// cl l.c /GL /O1 /Gy /MD /DNDEBUG /link /LTCG /OPT:REF /OPT:ICF
// cc -fsanitize=address l.c -o l_lin
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef unsigned long long Q;typedef unsigned int D;typedef unsigned short W;typedef unsigned char B;typedef char C;
typedef struct {B t;B s;B z;D r;D n;Q pad;} AH;                               // header for all heap allocated objects. type,shape,eltsize,refcount,length. MUST be at least 8 byte aligned or the allocator and pointer tagging scheme don't work
typedef Q(*DV)(Q,Q);                                                          // function pointer for dyadic verb
typedef Q(*MV)(Q);                                                            // function pointer for monadic verb

Q* TH;D THI=0;D THC=0;
Q SF[1024];

AH* ah(Q q){return (AH*)q;}                                                   // all pointer allocations have AH behind the pointer. legal regardless of underlying shape

B ip(Q q){return q&&!(7&q);}                                                  // Is this Q a pointer? nonzero in low 3 bits means atom
B itp(Q q){Q* ptr=(Q*)ah(q); return ip(q) && TH<=ptr && ptr<TH+THC; }         // Is this Q a pointer to the bump allocated region?
Q d(Q q){return q>>3;}                                                        // shift out the flags. decodes small integers
B*p(Q q){return (B*)(ah(q)+1);}                                               // pointers need no manipulation, low bits==0 is the signal for a pointer.
B v(Q q){return q>>5;}                                                        // verbs are grammatical type, subtype 0. payload in high 59 bits
B a(Q q){return q>>5;}
B c(Q q){return q>>5;}                                                        // controls are grammatical type, subtype 2. payload in high 59 bits

Q ar(Q r){return (r<<3)|1;}                                                   // create an atom of type 1 (reference)
Q av(Q v){return (v<<5)|2;}                                                   // create a verb atom (grammatical type 2, subtype 0)
Q an(Q n){return (n<(1ULL<<61))?((n<<3)|3):(0|3);}                            // create an atom of type 3 (integer) TODO: heap allocated 64 bit int. return 3 as a tagged 0 for stuff that should really be allocated on heap. 
Q ap(Q v){return (v<<3)|4;}                                                   // create an atom of type 4 (partial eval) - HEAP ONLY
Q aa(Q a){return (a<<5)|(1<<3)|2;}                                            // create an adverb atom (grammatical type 2, subtype 1)
Q ac(Q c){return (c<<5)|(2<<3)|2;}                                            // create a control atom (grammatical type 2, subtype 2)
Q as(Q s){return (s<<3)|7;}                                                   // create an atom of type 7 (symbol)
Q et(Q q,B t){return 0==t?q:1==t?ar(q):2==t?av(q):3==t?an(q):4==t?ap(q):ac(q);} // encode data of an atom based on the type

B ia(Q q){return !ip(q);}                                                     // is atom  from pointer
B t(Q q){
  if(!ia(q))return ah(q)->t;
  B tag=q&7;
  if(tag==2)return q&31;
  return tag;
}
B sh(Q q){return ia(q)?0:ah(q)->s;}                                           // shape    from header
B ls(Q q){return ia(q)?3:ah(q)->z;}                                           // logeltsz from header EDGE CASE: should type 0 automatically return 3 here????
B sz(Q q){return 1<<ls(q);}                                                   // bytesz   from logeltsz
D rc(Q q){return !q?0:ia(q)?1:ah(q)->r;}                                      // refcnt   from header
D n(Q a){B s=sh(a);return 0==s?1:1==s?ah(a)->n:0;}                            // length   from header

void ir(Q q);void dr(Q q);                                                          // forward declare refcount helpers

Q tsng(B t,B s,B z,D n){AH h={t,s,z,0,n,0};AH*o=malloc(sizeof(AH)+(1<<z)*n);*o=h;memset((void*)(o+1), 0, (1<<z)*n);return (Q)o;}  // LATER: custom allocator. Q points at data not header 
Q tsn(B t,B s,B z,D n){AH h={t,s,z,0,n,0};D bz=sizeof(AH)+(1<<z)*n;D qz=(bz+sizeof(Q)-1)/sizeof(Q);if(THC < THI+qz){printf("oom\n");exit(0);}AH*o=(AH*)(TH+THI);*o=h;memset((void*)(o+1), 0, (1<<z)*n);THI+=qz;return (Q)o;}  // LATER: custom allocator. Q points at data not header 
Q tn(B t,B z,D n){return tsn(t,1,z,n);}


// varwidth getters
Q Bi(B* b,B z,D i){Q r=0;memcpy(&r,b+z*i,z);return r;}                        // mask this by the size of z then cast to Q. NO SIGN EXTENSION FLOATS MAY LIVE IN HERE TOO.
Q pi(Q q,D i){return Bi(p(q),sz(q),i);}
Q ri(Q q,D i){
  if(1==sh(q)){return pi(q,i);}
  switch(t(q)){
    case 1:  return d(q);
    case 2:  return v(q);
    case 3:  return d(q);
    case 7:  return d(q);
    case 10: return q>>5;
    case 18: return c(q);
  }
  return 0;
}

Q qi(Q q,D i){B s=sh(q),tq=t(q);return 0==s?q:1==s?et(pi(q,i),tq):0;}         // get at index, return tagged Q
// varwidth setters
void Bid(B* b,B z,D i,Q d){memcpy(b+z*i,&d,z);}
void pid(Q q,D i,Q d){Bid(p(q),sz(q),i,d);}
void zid(Q q,D i,Q d){Q o=pi(q,i);ir(d);pid(q,i,d);dr(o);}
void qid(Q q,D i,Q d){if(!t(q)){zid(q,i,d);}else{pid(q,i,d);}}

void ir(Q q){ if(ip(q)&&!itp(q)){ah(q)->r++;} return;}
void dr(Q q){ 
  if(!q || ia(q) || itp(q)){return;}                                          // if null or atom just return
  if(0< --(ah(q)->r)){return;}                                                // if there is a nonzero refcount return
  if(!t(q)){for(D i=0;i<n(q);i++){dr(qi(q,i));}}                              // this object has refcount==0. if type 0, recurse on children
  free((void*)q);                                                             // then free this q
  return;                                                                     // should I consider returning a control sentinel here (type)
}
Q t2g(Q q){
  if(!itp(q)){return q;};
  AH *h=ah(q);Q g=tsng(h->t,h->s,h->z,h->n);
  if(t(q)){memcpy(p(g),p(q),(1<<h->z)*h->n);return g;}
  for(D i=0;i<n(g);i++){Q v=qi(q,i);if(itp(v)){v=t2g(v);};pid(g,i,v);}
  return g;
}

Q* OK; Q* OV; D OS; D OLOG; // Hash table for variables
C* VT;
C* MAP="0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";

void pr_b(Q q,D b){if(q<b){printf("%c",MAP[q]);return;}pr_b(q/b,b);printf("%c",MAP[q%b]);}

#define HASH_CONST 0x9E3779B97F4A7C15ULL                        // ~2^64/phi
D hash(Q k){ return (k*HASH_CONST)>>(64-OLOG); }
Q get(Q k){
  D i = hash(k);
  while(OK[i]&&OK[i]!=k){ i=(i+1)&(OS-1); } // linear probe
  return OK[i]?OV[i]:0;
}
Q hset(Q k, Q v){
  D i = hash(k);
  while(OK[i]&&OK[i]!=k){ i=(i+1)&(OS-1); }
  OK[i]=k; return OV[i]=v;
}

void pr(Q q){
  if(0==q){return;}
  if(0==t(q)){
    if(!sh(q)){printf("atom type 0?%lld ",q);}
    if(1==sh(q)){for(D i=0;i<n(q);i++){pr(pi(q,i));}}}
  if(1==t(q)){pr_b(d(q),62); printf(" "); pr(get(d(q)));}
  if(2==t(q)){printf("%c",VT[v(q)]);}
  if(10==t(q)){printf("adverb: %c\n",q>>5);}
  if(18==t(q)){printf("control: %d\n",c(q));}
  if(3==t(q)){
    if(0==sh(q)){printf("%lld",d(q));}
    if(1==sh(q)){if(n(q)){for(D i=0;i<n(q);i++){printf("%lld ",pi(q,i));}} else {printf("!0 ");}}
  }
  if(4==t(q)){for(D i=0;i<n(q);i++){pr(pi(q,i));}}
  if(7==t(q)){printf("`");pr_b(d(q),62);}
  printf("\n");
}
DV VD[9];
MV VM[9];

Q id(Q w){return w;}
Q en(Q w){B aw=ia(w);Q z=tn(aw?t(w):0,ls(w),1);if(aw){pid(z,0,d(w));}else{zid(z,0,w);};return z;}
Q tp(Q w){return an(t(w));}
Q ct(Q w){return an(n(w));}

typedef enum {DB,LB,RB,MB} BM; // broadcast mode
Q vb(Q a,Q w,MV mv,DV dv,BM m){B ta=t(a),tw=t(w),sa=sh(a),sw=sh(w);D na=n(a),nw=n(w);
  if(DB==m && na!=nw && sa && sw){return ac(2);}
  B ib=DB==m?((!ta)||(!tw)):RB==m?!tw:LB==m?!ta:/*MB==m*/!tw;
  if(ib){
    D nz=DB==m?(sa?na:nw):RB==m?nw:LB==m?na:nw;
    Q z=tn(0,3,nz);
    for(D i=0;i<nz;i++){
      Q zi=DB==m?dv(qi(a,i),qi(w,i)):RB==m?dv(a,qi(w,i)):LB==m?dv(qi(a,i),w):/*MB==m*/mv(qi(w,i));
      if(18==t(zi)){return zi;} // sentinel bubbled up. later: add cleanup
      zid(z,i,zi);
    }
    return z;
  }
  return ac(0);
}

Q car(Q w){return qi(w,0);}

Q nt(Q w){
  Q z=vb(0,w,nt,0,MB);
  if(18==t(z)){return z;}if(c(z)){return z;} // if data is returned, return the data. if a control sentinel is returned and its payload is nonzero then return, otherwise listen to theh control signal to do the proper work.
  if(ia(w)){return an(!d(w));}
  if(1==sh(w)){z=tn(3,ls(w),n(w));for(D i=0;i<n(w);i++){pid(z,i,!pi(w,i));};return z;}
  return ac(1); // return shape error
}

Q tl(Q w){
  B aw=ia(w);if(aw){w=en(w);};D nw=n(w);Q z=tn(0,3,nw);
  for(D i=0;i<nw;i++){
    Q ni=pi(w,i);Q zi=tn(3,ls(w),ni);for(D j=0;j<ni;j++){pid(zi,j,j);}
    zid(z,i,zi);
  }
  return aw?car(z):z;
}

Q at(Q a,Q w){
  Q z=vb(a,w,0,at,RB);
  if(18==t(z)){return z;}if(c(z)){return z;}
  B aa=ia(w);B tz=t(a);B nz=n(w);B shz=sh(w);z=tn(t(a),ls(a),nz);
  for(D i=0;i<nz;i++){
    Q wi=ri(w,i);Q zi=ri(a,wi);
    qid(z,i,zi);
  }
  return aa?car(z):z;
}

Q math(Q a,Q w,DV op){ // anything that gets here has been broadcasted. we can use the universal getter on both a and w
  D na=n(a),nw=n(w);D nz=na<nw?nw:na;B shz=sh(a)<sh(w)?sh(w):sh(a);B lz=ls(a)<ls(w)?ls(w):ls(a);
  if(0==shz){return an(op(d(a),d(w)));}
  Q z=tn(t(a),lz,nz);
  for(D i=0;i<nz;i++){Q ai=ri(a,i);Q wi=ri(w,i);
    Q zi=op(ai,wi);
    pid(z,i,zi);
  }
  return z;
}
Q pl_aa(Q a,Q w){ return a+w;}
Q ml_aa(Q a,Q w){ return a*w;}
Q pl(Q a,Q w){Q z=vb(a,w,0,pl,DB);if(t(z)!=18){return z;}if(c(z)){return z;}; return math(a,w,pl_aa);} // later: float support and type promotion. 
Q ml(Q a,Q w){Q z=vb(a,w,0,ml,DB);if(t(z)!=18){return z;}if(c(z)){return z;}; return math(a,w,ml_aa);}

Q set(Q a,Q w){
  w=t2g(w); Q k=d(a);
  Q o=get(k); ir(w); hset(k,w);
  if(o&&ip(o)){dr(o);}
  return w;
}

Q ca(Q a,Q w){
  B tz=(t(a)==t(w))?t(a):0;
  D j=0;D ca=d(ct(a));D cw=d(ct(w));Q z=tn(tz,3,ca+cw);
  for(D i=0;i<ca;i++,j++){Q ai=at(a,an(i));qid(z,j,tz?d(ai):ai);} // decode if not type 0
  for(D i=0;i<cw;i++,j++){Q wi=at(w,an(i));qid(z,j,tz?d(wi):wi);} // decode if atom or somethig
  return z;
}

DV VD[9]={0,0,0,at,0,pl,ml,set,ca};
MV VM[9]={0,nt,tl,tp,ct,0,car,id,en};
C* VT=" ~!@#+*:,";

Q Ap(Q a){Q p=tsn(4,1,3,1);pid(p,0,a);return p;}
Q e(Q* q);
Q emv(Q*q){
  Q w=e(q+1);
  if(4==t(w)){Q p=tsn(4,1,3,1);pid(p,0,*q);return ca(p,w);}
  return VM[v(*q)](w);
}
Q edv(Q a,Q*q){
  Q w=e(q+1);B i=v(*q);
  if(4==t(w)&&(7!=i)){Q p=tsn(4,1,3,2);pid(p,0,a);pid(p,1,*q);return ca(p,w);}  // handle partial evaluations but allow assignment of them instantly. 
  a=((1==t(a))&&(7!=i))?get(d(a)):a;
  DV dv=VD[i];
  return dv(a,w);
}
Q E(Q* q){
  Q r = 0;
  while(*q){
    r = e(q);
    // Find the end of the evaluated expression
    while(*q && !(18==t(*q) && ';'==c(*q))) q++;
    // If we found a semicolon, skip it to start the next expression
    if(*q) q++;
  }
  return r;
}
Q e(Q* q){
  Q a=*q;
  if(!a){return tsn(4,1,3,0);}                                 // If a is the end of the stream then we must have missing data. return type 4
  if(18==t(a) && ';'==c(a)){return tsn(4,1,3,0);}              // Semicolon is a statement terminator, acts as end-of-stream for this expression.
  Q w=q[1];                                                    // we know a is non zero, so we can read q[1] but it may be end of stream, or a semicolon
  B end = !w || (18==t(w) && ';'==c(w));                        // end of expression is null or semicolon
  return (2==t(a)&&!end)  ?                                // if a is a verb and w isn't the end of the stream
         emv(q)        :                                       //  then evaluate a monadic verb
         (2==t(a)&&end) ?                                   // if a is a verb and we have hit the end of the stream
         Ap(a)         :                                       //  then create a dyadic partial evaluation
         (!end&&2==t(w))  ?                                   // if w is non-zero and is a verb
         edv(a,q+1)    :                                       //  then eval dyadic verb
         (4==t(a)&&end) ?                                   // if a is a partial evaluation and we don't have a w 
         a             :                                       //  then just return the partial up the stack. 
         (1==t(a))     ?                                       // if a is a reference (and not being assigned to)
         get(d(a))     :                                       //  then return the value of the reference
         a             ;                                       //  otherwise this must be data, return the data.
}

Q R(C a){return ('a'<=a&&a<='z')?ar(a-'a'):0;} 
Q V(C a){for(D i=0;i<strlen(VT);i++){if(VT[i]==a){return av(i);}}return 0;}
Q parse_b(C* s, D len, D base){
  Q r=0,p=1;
  for(D i=len-1;i<len;i--){
    C* f=strchr(MAP,s[i]);if(!f)return -1; // invalid char
    r+=(f-MAP)*p;p*=base;
  }
  return r;
}
// State(st): 0-start,1-neg,2-int,3-flt,4-name,5-str,6-sym,7-done
// CClass(cc):0-nul,1-spc,2-alp,3-dig,4-dot,5-qot,6-bqt,7-ver,8-ctl,9-adv,10-oth,11-neg
// Character class lookup table. Maps ASCII chars ' ' (32) to '~' (126) to a class index.
//              !"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~
static C* CST="1757AAA988777B49333333333378AAAA722222222222222222222222222898AA62222222222222222222222222228A87";
D cl(C c){B uc=(B)c;if(!uc)return 0;if(uc<' '||uc>126)return 10;C r=CST[uc-' '];return(r>='0'&&r<='9')?r-'0':r-'A'+10;}
Q* lx(C*b){D l=strlen(b);Q*q=malloc(sizeof(Q)*(l+1));D qi=0;C*p=b;D st=0; // st:state
  D TT[7][12]={ // Transition Table
  // NUL SPC ALP DIG DOT QOT BQT VER CTL ADV OTH NEG
    {7,  0,  4,  2,  4,  5,  6,  7,  7,  7,  7,  1}, // 0 S_START
    {7,  7,  7,  2,  7,  7,  7,  7,  7,  7,  7,  7}, // 1 S_NEG
    {7,  7,  7,  2,  3,  7,  7,  7,  7,  7,  7,  7}, // 2 S_INT
    {7,  7,  7,  3,  7,  7,  7,  7,  7,  7,  7,  7}, // 3 S_FLT
    {7,  7,  4,  4,  4,  7,  7,  7,  7,  7,  7,  7}, // 4 S_NAME
    {7,  7,  7,  7,  7,  7,  7,  7,  7,  7,  7,  7}, // 5 S_STR (TODO)
    {7,  7,  6,  6,  6,  7,  0,  7,  7,  7,  7,  7}, // 6 S_SYM
  };
  while(st!=7){
    C*s=p;D cc=cl(*p);st=TT[0][cc]; // s:token start
    if(st==0){p++;continue;} // whitespace
    if(cc>=7&&cc<=9){q[qi++]=cc==7?V(*p):cc==8?ac(*p):aa(*p);p++;st=0;continue;} // verbs, controls, adverbs
    while(st!=7){
      p++;cc=cl(*p);D next_st=TT[st][cc];
      if(st==1&&next_st!=2){q[qi++]=V(*s);p=s+1;st=0;break;} // not a number, treat '-' as a verb
      if(next_st==7){ // End of token.
        D len=p-s;C t[100];strncpy(t,s,len);t[len]='\0';
        if(st==1||st==2) q[qi++]=an(parse_b(t,len,10));
        else if(st==3)  q[qi++]=an(parse_b(t,len,10)); // TODO: float support
        else if(st==4)  q[qi++]=ar(parse_b(t,len,62));
        else if(st==6){ s++; len--; strncpy(t,s,len);t[len]='\0'; q[qi++]=as(parse_b(t,len,62));}
        // TODO: S_STR, S_FLT
        st=0;break;
      }
      st=next_st;
    }
  }
  q[qi]=0;return q;
}

C buffer[100];
D main(void){
  TH=(Q*)malloc(1<<16);THC=(1<<16)/sizeof(Q);
  OLOG=10;OS=1<<OLOG;OK=calloc(OS,sizeof(Q));OV=calloc(OS,sizeof(Q));
  while (1) {
    printf(" "); if (!fgets(buffer, 100, stdin)){break;}
    buffer[strcspn(buffer, "\r")] = '\0'; buffer[strcspn(buffer, "\n")] = '\0';
    if (strcmp(buffer, "\\\\") == 0){break;}
    THI=0;
    Q r=E(lx(buffer));
    pr(r);
  }
  return 0;
}