// cl l.c /GL /O1 /Gy /MD /DNDEBUG /link /LTCG /OPT:REF /OPT:ICF
// cc -fsanitize=address l.c -o l_lin
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef unsigned long long Q;typedef unsigned int D;typedef unsigned short W;typedef unsigned char B;typedef char C;
typedef struct {B t;B s;B z;D r;D n;Q pad;} AH;                               // header for all heap allocated objects. type,shape,eltsize,refcount,length. MUST be at least 8 byte aligned or the allocator and pointer tagging scheme don't work
typedef Q(*DV)(Q,Q);                                                          // function pointer for dyadic verb
typedef Q(*MV)(Q);                                                            // function pointer for monadic verb

AH* ah(Q q){return (AH*)q;}                                                   // all pointer allocations have AH behind the pointer. legal regardless of underlying shape

B ip(Q q){return q&&!(7&q);}                                                  // Is this Q a pointer? nonzero in low 3 bits means atom
Q d(Q q){return q>>3;}                                                        // shift out the flags. decodes small integers
B*p(Q q){return (B*)(ah(q)+1);}                                               // pointers need no manipulation, low bits==0 is the signal for a pointer.
B r(Q r){return d(r)+'a';}                                                    // transform an atom of type 1 into ascii. This is how we do variables for now. 
B v(Q v){return d(v);}                                                        // transform an atom of type 2 into its verb index.
B c(Q c){return d(c);}                                                        // transform an atom of type 5 into its control sentinel

Q ar(Q r){return (r<<3)|1;}                                                   // create an atom of type 1 (reference)
Q av(Q v){return (v<<3)|2;}                                                   // create an atom of type 2 (verb)      
Q an(Q n){return (n<(1ULL<<61))?((n<<3)|3):(0|3);}                            // create an atom of type 3 (integer) TODO: heap allocated 64 bit int. return 3 as a tagged 0 for stuff that should really be allocated on heap. 
Q ap(Q v){return (v<<3)|4;}                                                   // create an atom of type 4 (partial eval)
Q ac(Q c){return (c<<3)|5;}                                                   // create an atom of type 5 (control sentinel)
Q et(Q q,B t){return 0==t?q:1==t?ar(q):2==t?av(q):3==t?an(q):4==t?ap(q):0;}   // encode data of an atom based on the type

B ia(Q q){return !ip(q);}                                                     // is atom  from pointer
B t(Q q){return ia(q)?(7&q):ah(q)->t;}                                        // type     from header
B sh(Q q){return ia(q)?0:ah(q)->s;}                                           // shape    from header
B ls(Q q){return ia(q)?3:ah(q)->z;}                                           // logeltsz from header EDGE CASE: should type 0 automatically return 3 here????
B sz(Q q){return 1<<ls(q);}                                                   // bytesz   from logeltsz
D rc(Q q){return !q?0:ia(q)?1:ah(q)->r;}                                      // refcnt   from header
D n(Q a){B s=sh(a);return 0==s?1:1==s?ah(a)->n:0;}                            // length   from header

void ir(Q q);void dr(Q q);                                                          // forward declare refcount helpers

Q tsn(B t,B s,B z,D n){AH h={t,s,z,1,n,0};AH*o=malloc(sizeof(AH)+(1<<z)*n);*o=h;memset((void*)(o+1), 0, (1<<z)*n);return (Q)o;}  // LATER: custom allocator. Q points at data not header 
Q tn(B t,B z,D n){return tsn(t,1,z,n);}

// varwidth getters
Q Bi(B* b,B z,D i){Q r=0;memcpy(&r,b+z*i,z);return r;}                        // mask this by the size of z then cast to Q. NO SIGN EXTENSION FLOATS MAY LIVE IN HERE TOO.
Q pi(Q q,D i){return Bi(p(q),sz(q),i);}
Q ri(Q q,D i){B s=sh(q);return 0==s?d(q):(1==s)?pi(q,i):0;}                   // raw data at i. later: add support for heap allocated atoms
Q qi(Q q,D i){B s=sh(q),tq=t(q);return 0==s?q:1==s?et(pi(q,i),tq):0;}       // get at index, return tagged Q
// varwidth setters
void Bid(B* b,B z,D i,Q d){memcpy(b+z*i,&d,z);}
void pid(Q q,D i,Q d){Bid(p(q),sz(q),i,d);}
void zid(Q q,D i,Q d){Q o=pi(q,i);ir(d);pid(q,i,d);dr(o);}
void qid(Q q,D i,Q d){if(!t(q)){zid(q,i,d);}else{pid(q,i,d);}}

void ir(Q q){ if(ip(q)){ah(q)->r++;} return;}
void dr(Q q){ 
  if(!q || ia(q)){return;}                                                    // if null or atom just return
  if(0< --(ah(q)->r)){return;}                                                // if there is a nonzero refcount return
  if(!t(q)){for(D i=0;i<n(q);i++){dr(qi(q,i));}}                              // this object has refcount==0. if type 0, recurse on children
  free((void*)q);                                                             // then free this q
  return;                                                                     // should I consider returning a control sentinel here (type)
}

Q O[26];
C* VT;

void pr(Q q){
  if(0==q){return;}
  if(0==t(q)){
    if(!sh(q)){printf("atom type 0?%lld ",q);}
    if(1==sh(q)){for(D i=0;i<n(q);i++){pr(pi(q,i));}}}
  if(1==t(q)){printf("%c ",r(q));pr(O[d(q)]);}
  if(2==t(q)){printf("%c",VT[v(q)]);}
  if(3==t(q)){
    if(0==sh(q)){printf("%lld",d(q));}
    if(1==sh(q)){if(n(q)){for(D i=0;i<n(q);i++){printf("%lld ",pi(q,i));}} else {printf("!0 ");}}
  }
  if(4==t(q)){for(D i=0;i<n(q);i++){pr(pi(q,i));}}
  if(5==t(q)){printf("control: %d\n",c(q));}
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
      if(5==t(zi)){return zi;} // sentinel bubbled up. later: add cleanup
      zid(z,i,zi);
    }
    return z;
  }
  return ac(0);
}

Q car(Q w){return qi(w,0);}

Q nt(Q w){
  Q z=vb(0,w,nt,0,MB);
  if(5!=t(z)){return z;}if(c(z)){return z;} // if data is returned, return the data. if a control sentinel is returned and its payload is nonzero then return, otherwise listen to theh control signal to do the proper work.
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
  if(5!=t(z)){return z;}if(c(z)){return z;}
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
Q pl(Q a,Q w){Q z=vb(a,w,0,pl,DB);if(5!=t(z)){return z;}if(c(z)){return z;}; return math(a,w,pl_aa);} // later: float support and type promotion. 
Q ml(Q a,Q w){Q z=vb(a,w,0,ml,DB);if(5!=t(z)){return z;}if(c(z)){return z;}; return math(a,w,ml_aa);}

Q as(Q a,Q w){Q o=O[d(a)];ir(w);O[d(a)]=w;if(o&&ip(o)){dr(o);};return w;}

Q ca(Q a,Q w){
  B tz=(t(a)==t(w))?t(a):0;
  D j=0;D ca=d(ct(a));D cw=d(ct(w));Q z=tn(tz,3,ca+cw);
  for(D i=0;i<ca;i++,j++){Q ai=at(a,an(i));qid(z,j,tz?d(ai):ai);} // decode if not type 0
  for(D i=0;i<cw;i++,j++){Q wi=at(w,an(i));qid(z,j,tz?d(wi):wi);} // decode if atom or somethig
  return z;
}

DV VD[9]={0,0,0,at,0,pl,ml,as,ca};
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
  a=((1==t(a))&&(7!=i))?O[d(a)]:a;
  DV dv=VD[i];
  return dv(a,w);
}
Q e(Q* q){
  Q a=*q;
  if(!a){return tsn(4,1,3,0);}                                 // If a is the end of the stream then we must have missing data. return type 4
  Q w=q[1];                                                    // we know a is non zero, so we can read q[1] but it may be end of stream, need to check if it is 0
  return (2==t(a)&&w)  ?                                       // if a is a verb and w isn't the end of the stream
         emv(q)        :                                       //  then evaluate a monadic verb
         (2==t(a)&&!w) ?                                       // if a is a verb and we have hit the end of the stream
         Ap(a)         :                                       //  then create a dyadic partial evaluation
         (w&&2==t(w))  ?                                       // if w is non-zero and is a verb
         edv(a,q+1)    :                                       //  then eval dyadic verb
         (4==t(a)&&!w) ?                                       // if a is a partial evaluation and we don't have a w 
         a             :                                       //  then just return the partial up the stack. 
         (1==t(a))     ?                                       // if a is a reference
         O[d(a)]       :                                       //  then return the value of the reference
         a             ;                                       //  otherwise this must be data, return the data.
}

Q R(C a){return ('a'<=a&&a<='z')?ar(a-'a'):0;} 
Q N(C a){return ('0'<=a&&a<='9')?an(a-'0'):0;}
Q V(C a){for(D i=0;i<9;i++){if(VT[i]==a){return av(i);}}return 0;} 
Q* pe(C*b){D l=strlen(b);Q* q=malloc(sizeof(Q)*(l+1));D i=0;
  for(;i<l;i++){
    Q a;q[i]=(a=R(b[i]))?a:(a=V(b[i]))?a:(a=N(b[i]))?a:0;
  }
  q[i]=0;
  return q;
}

C buffer[100];
D main(void){
  while (1) {
    printf(" "); if (!fgets(buffer, 100, stdin)){break;}
    buffer[strcspn(buffer, "\r")] = '\0'; buffer[strcspn(buffer, "\n")] = '\0';
    if (strcmp(buffer, "\\\\") == 0){break;}
    Q r=e(pe(buffer));pr(r);
    dr(r);
  }
  return 0;
}