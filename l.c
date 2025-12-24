// cl l.c /GL /O1 /Gy /MD /DNDEBUG /link /LTCG /OPT:REF /OPT:ICF
// cc -fsanitize=address l.c -o l_lin
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#if defined(_MSC_VER)
  #include <intrin.h>
  #include <malloc.h>
  #include <windows.h>
#else
  #include <sys/mman.h>
#endif

typedef unsigned long long Q;typedef unsigned int D;typedef unsigned short W;typedef unsigned char B;typedef char C;
typedef long long J; typedef int I; typedef short H;
typedef Q(*DV)(Q,Q);                                                          // function pointer for dyadic verb
typedef Q(*MV)(Q);                                                            // function pointer for monadic verb

#define BUMP_UNIT_BYTES   16
#define BUDDY_UNIT_BYTES  4096

#define BUMP_UNIT_QS   (BUMP_UNIT_BYTES / sizeof(Q))
#define BUDDY_UNIT_QS  (BUDDY_UNIT_BYTES / sizeof(Q))

#define ARENA_SZ       (1ULL<<32)
Q* AB[8];Q AI[8];Q AC[8];
Q AM[8];
Q AQ[8]={BUMP_UNIT_QS,BUDDY_UNIT_QS,0,0,0,0,0,0};
Q BF[32];
B ha(Q q){return (q>>8)&7;}
Q hp(Q q){return q>>11;}
Q* ptr(Q q){return AB[ha(q)]+(hp(q)*AQ[ha(q)]);}

B ip(Q q){return q&&!(7&q);}                                                  // Is this Q a pointer? nonzero in low 3 bits means atom
B itp(Q q){return ip(q) && ha(q)==0;}                                         // Is this Q a pointer to the bump allocated region?
Q d(Q q){return q>>3;}                                                        // shift out the flags. decodes small integers
B*p(Q q){return (B*)(ptr(q)+6);}                                              // pointers point at header after decoding and need to be adjusted to point at the data
B v(Q q){return q>>5;}                                                        // verbs are grammatical type, subtype 0. payload in high 59 bits
B a(Q q){return q>>5;}
B c(Q q){return q>>5;}                                                        // controls are grammatical type, subtype 2. payload in high 59 bits

Q ar(Q r){return (r<<3)|1;}                                                   // create an atom of type 1 (reference)
Q av(Q v){return (v<<5)|2;}                                                   // create a verb atom (grammatical type 2, subtype 0)
Q aa(Q a){return (a<<5)|(1<<3)|2;}                                            // create an adverb atom (grammatical type 2, subtype 1)
Q ac(Q c){return (c<<5)|(2<<3)|2;}                                            // create a control atom (grammatical type 2, subtype 2)
Q an(Q n){return (n<(1ULL<<61))?((n<<3)|3):(0|3);}                            // create an atom of type 3 (integer) TODO: heap allocated 64 bit int. return 3 as a tagged 0 for stuff that should really be allocated on heap. 
Q ap(Q v){return (v<<3)|4;}                                                   // create an atom of type 4 (partial eval) - HEAP ONLY
                                                                              // type 5 is hash
Q as(Q s){return (s<<3)|7;}                                                   // create an atom of type 7 (symbol)
Q et(Q q,B t){return 0==t?q:1==t?ar(q):2==t?av(q):3==t?an(q):4==t?ap(q):ac(q);} // encode data of an atom based on the type

B ia(Q q){return !ip(q);}                                                     // is atom  from pointer
B t(Q q){
  if(!ia(q))return ptr(q)[0];
  B tag=q&7;
  if(tag==2)return q&31;
  return tag;
}
B sh(Q q){return ia(q)?0:ptr(q)[1];}                                           // shape    from header
B ls(Q q){return ia(q)?3:ptr(q)[2];}                                           // logeltsz from header EDGE CASE: should type 0 automatically return 3 here????
B sz(Q q){return 1<<ls(q);}                                                     // bytesz   from logeltsz
D rc(Q q){return !q?0:ia(q)?1:ptr(q)[3];}                                      // refcnt   from header
D n(Q a){B s=sh(a);return 0==s?1:ptr(a)[4];}                                   // length   from header
D cp(Q a){B s=sh(a);return 0==s?1:ptr(a)[5];}                                  // capacity from header

void ir(Q q);void dr(Q q); 

Q qbz(Q bz){return ((bz+15)/16)*2;}                                             // forward declare refcount helpers
Q hz(){return sizeof(Q)*6;}                                                     // header size
D cn(B t,B s,D n){                                                              // capacity from type,shape,n
  if(0==s){return 1;}                                                           // heap allocated atom. there is only one element.
  if(2==s){return 3;}                                                           // we know that there are only ever 3 elements in a dictionary allocation.
  // otherwise, shape 1. 
  if(5==t){return 1<<6;};                                                       // capacity starts at 64 and must be power of two
  if(0==n){return 1;}
  return n+(n>>1)+(n>>3);                                                       // n+n/2+n/8 to approximate 1.618 LATER: overflow fix
} 
Q pz(B z,D c){ return (1<<z)*c;}                                           // payload size in bytes by shape, log elt size, and capacity
Q az(B z,D c){ return hz()+pz(z,c);}                                       // allocation size
void ah(Q* h,B t,B s,B z,D r,D n,D c){h[0]=t;h[1]=s;h[2]=z;h[3]=r;h[4]=n;h[5]=c;} // allocate the header. 
D lsz(Q x){
#if defined(_MSC_VER)
  unsigned long i; _BitScanReverse64(&i,x-1); return i+1;
#else
  return 64-__builtin_clzll(x-1);
#endif
}
static inline B floor_ord(Q x){
  // x >= 1
#if defined(_MSC_VER)
  unsigned long i;
  _BitScanReverse64(&i, x);
  return (B)i;
#else
  return (B)(63 - __builtin_clzll(x));
#endif
}
static inline Q bump_units(B z, D c){
  Q bytes = hz() + pz(z,c);
  return (bytes + BUMP_UNIT_BYTES - 1) / BUMP_UNIT_BYTES;
}
static inline Q buddy_units(B z, D c){
  Q bytes = hz() + pz(z,c);
  return (bytes + BUDDY_UNIT_BYTES - 1) / BUDDY_UNIT_BYTES;
}
static inline B buddy_order_from_units(Q units){
  // monotone mapping, not semantically log2
  return floor_ord(units);
}

static inline Q buddy_units_from_order(B ord){
  return 1ULL << ord;
}
static inline void commit_range(void* p, Q bytes){
#if defined(_MSC_VER)
  VirtualAlloc(p, bytes, MEM_COMMIT, PAGE_READWRITE);
#else
  Q a=(Q)p, m=4095;
  Q s=a&~m;
  Q e=(a+bytes+m)&~m;
  mprotect((void*)s, e-s, PROT_READ|PROT_WRITE);
#endif
}
Q bumpalloc(B t,B s,B z,D n,D c,B a){                                                    // LATER: custom allocator. Q points at header
  Q units=bump_units(z,c);
  if(AI[0]+units>AC[0]){printf("oom\n");exit(0);}
  if(AI[0]+units>AM[0]){
    Q req=AI[0]+units;
    commit_range(AB[0]+AM[0]*BUMP_UNIT_QS, (req-AM[0])*BUMP_UNIT_BYTES);
    AM[0]=req;
  }
  Q off=AI[0];
  Q* o=AB[0]+off*BUMP_UNIT_QS;
  AI[0]+=units;
  ah(o,t,s,z,0,n,c);
  memset(o+6,0,pz(z,c));
  return (off<<11)|(0<<8);
}
void bumpfree(B a){AI[a]=0;}
void buddyinit(B a){
  for(D i=0;i<32;i++) BF[i]=~0ULL;

  Q off=0;
  Q rem=AC[a];               // units remaining
  while(rem){
    B ord = floor_ord(rem);
    if(ord>=32) ord=31;

    Q u = buddy_units_from_order(ord);
    printf("rem ord u %lld %d %lld\n",rem,ord,u);
    commit_range(AB[a] + off * BUDDY_UNIT_QS, sizeof(Q));
    *(Q*)(AB[a] + off * BUDDY_UNIT_QS) = BF[ord];
    BF[ord] = off;

    off += u;
    rem -= u;
  }
}
Q buddyalloc(B t,B s,B z,D n,D c,B a){
  Q units = buddy_units(z,c);
  B ord   = buddy_order_from_units(units);

  B i = ord;
  while(i<32 && BF[i]==~0ULL) i++;
  if(i==32){ printf("oom buddy\n"); exit(0); }

  Q off = BF[i];
  BF[i] = *(Q*)(AB[1] + off * BUDDY_UNIT_QS);

  while(i>ord){
    i--;
    Q u = buddy_units_from_order(i);
    Q b = off + u;

    commit_range(AB[1] + b * BUDDY_UNIT_QS, sizeof(Q));
    *(Q*)(AB[1] + b * BUDDY_UNIT_QS) = BF[i];
    BF[i] = b;
  }

  Q* o = AB[1] + off * BUDDY_UNIT_QS;
  commit_range(o, az(z,c));
  ah(o,t,s,z,0,n,c);
  memset(o+6, 0, pz(z,c));

  return (off << 11) | (1 << 8) | (ord << 3);
}
void buddyfree(Q q){
  B a   = ha(q);
  Q off = hp(q);
  B ord = (q>>3)&31;
  while(ord<31){
    Q u = buddy_units_from_order(ord);
    Q b = off ^ u;
    Q* prev = &BF[ord];
    Q cur = *prev;
    while(cur!=~0ULL && cur!=b){
      prev = (Q*)(AB[a] + cur * BUDDY_UNIT_QS);
      cur = *prev;
    }
    if(cur!=b) break;
    *prev = *(Q*)(AB[a] + cur * BUDDY_UNIT_QS);
    if(b<off) off=b;
    ord++;
  }
  *(Q*)(AB[a] + off * BUDDY_UNIT_QS) = BF[ord];
  BF[ord] = off;
}
Q tsng(B t,B s,B z,D n){return buddyalloc(t,s,z,n,cn(t,s,n),1);}
Q tsn(B t,B s,B z,D n){return bumpalloc(t,s,z,n,cn(t,s,n),0);}
Q vn(B t,B z,D n){return tsn(t,1,z,n);}
Q ln(D n){return vn(0,3,n);}
Q vc(B t,B z,D c,B a){return (a==1?buddyalloc:bumpalloc)(t,1,z,0,c,a);}
Q lc(D c,B a){return vc(0,3,c,a);}

void pr(Q q);
void zid(Q q,D i,Q d);
Q dni(B t,B z,D n,B a){                                                              // alloc a dictionary of a certain type and element size with hash table capacity n. 
  D c=cn(5,1,n);
  Q h=vc(5,2,c,a);                                                                    // n means keycount for hash.
  Q k=lc(c,a);
  Q v=vc(t,z,c,a);
  Q d=(a==1?buddyalloc:bumpalloc)(0,2,3,3,3,a);
  zid(d,0,h);zid(d,1,k);zid(d,2,v);
  return d;
}
Q dn(B t,B z,D n){return dni(t,z,n,0);}

// varwidth getters
Q Bi(B* b,B z,D i){Q r=0;memcpy(&r,b+z*i,z);return r;}                                // mask this by the size of z then cast to Q. NO SIGN EXTENSION FLOATS MAY LIVE IN HERE TOO.
Q pi(Q q,D i){return Bi(p(q),sz(q),i);}              
Q ri(Q q,D i){
  if(1==sh(q)){return pi(q,i);}
  printf("non shape 1 ri call\n");
  return ac(1);                                                                 // shape error
}
Q vi(D n,D i){if(i>=n){return ac(2);};return an(i);}
Q qi(Q q,D i){B s=sh(q),tq=t(q);
  if(1==s){Q qi=vi(n(q),i);return 18==t(qi)?(printf("qi badidx\n"),qi):et(pi(q,d(qi)),tq);};
  return (printf("non shape 1 qi call\n"),ac(1));
}              // get at index, return tagged Q
Q ra(Q q){                                                                      // read atom
  if(sh(q)){printf("ra: not an atom\n");return ac(1);}
  switch(t(q)){
    case 1:  return d(q);
    case 2:  return v(q);
    case 3:  return d(q);                                                       // enhance for heap allocated 64 bit num.
    case 7:  return d(q);
    case 10: return a(q);
    case 18: return c(q);
    default: return ac(5);                                                      // not yet implemented
  }
}
Q grow(Q q,D n,D c,D m){printf("growing\n");return ac(5);}                                          // not yet implemented but, given a q, old length n, old capacity c, and amount of new items to add, extend the allocation to a new c, set the proper n.
D xn(Q q,D m){                                                                  // if n(q)+m<c then set n to n+m otherwise grow
  D nq=n(q);D c=cp(q);
  printf("q t(q) nq m c %lld %d %d %d %d\n",q,t(q),nq,m,c);
  if(nq+m<c){ptr(q)[4]=nq+m;}else{grow(q,nq,c,m);}
  return nq+m;
}
// varwidth setters
void Bid(B* b,B z,D i,Q d){memcpy(b+z*i,&d,z);}
void pid(Q q,D i,Q d){if(n(q)<=i){printf("length error\n");return;};Bid(p(q),sz(q),i,d);}          // throw length error when i outside of n
void zid(Q q,D i,Q d){Q o=pi(q,i);ir(d);pid(q,i,d);dr(o);}
void qid(Q q,D i,Q d){if(!t(q)){zid(q,i,d);}else{pid(q,i,d);}}

// dict get/set
static inline D lg2(D c){
#if defined(_MSC_VER)
  unsigned long idx;
  _BitScanForward64(&idx, (unsigned long long)c);
  return (D)idx;
#else
  return __builtin_ctzll(c);
#endif
}
#define HASH_CONST 0x9E3779B97F4A7C15ULL                                        // ~2^64/phi
D hash(Q k,D lc){ return (k*HASH_CONST)>>(64-lc); }
Q fk(D* ht,Q k,D c,Q keys){                                                     // hash goes from pointer to bucket but the hash needs to be based on structural equality. 
  D mask = c - 1, i = hash(k,lg2(c)) & mask;
  for(D j=0; j<c; ++j){
    D e = ht[i];
    if(!e) return i;                                                            // empty slot
    if(pi(keys, e-1) == k) return i;                                            // key match
    i = (i + 1) & mask;
  }
  return c;                                                                     // Sentinel for "table is full and key not found"
} 
Q SC[1024]; D SP=0;Q G;

Q dki(Q d, Q k){                                                                // inner "dictionary key" lookup for a single dictionary
  if(!ip(d)||2!=sh(d)) return 0;                                                // Not a dictionary
  Q htq=pi(d,0),kq=pi(d,1),vq=pi(d,2);
  D* ht=(D*)p(htq); D c=cp(htq);
  D i=fk(ht,k,c,kq);
  if(i==c){return 0;}                                                           // Not found
  D e=ht[i];
  return e?qi(vq,e-1):0;                                                        // Found, or empty slot
}

Q dk(Q d, Q k){                                                                 // outer "dictionary key" lookup with scope traversal
  Q r=dki(d,k);if(r){return r;}
  for (I j=SP; j>=0; j--) {                                                     // Search from the current scope (SP) down to scope 0
    Q r = dki(SC[j], k);
    if(r){return r;}
  }
  r=dki(G, k);                                                                  // If not found in scopes, try the global dictionary G
  if(r){return r;}
  return ac(4);                                                                 // Return result from G or "not found"
}
Q dkv(Q d,Q k,Q v){
  Q htq=pi(d,0),kq=pi(d,1),vq=pi(d,2);
  D* ht=(D*)p(htq);
  D c=cp(htq);
  D i=fk(ht,k,c,kq);
  if(i==c){return ac(6);}
  D e=ht[i];
  if(e){ // overwrite existing value
    D idx=e-1;
    Q old=pi(vq, idx);
    ir(v);
    pid(vq, idx, v);
    dr(old);
    return v;
  }
  D idx = n(kq);                                                              // insert new key/value
  xn(kq,1);zid(kq, idx, k);                                                   // append key
  xn(vq,1);qid(vq, idx, v);                                                   // append value
  ht[i] = idx + 1;                                                            // write hash entry
  xn(htq,1);                                                                  // n means element count for hash                          
  return v;
}
void ir(Q q){ if(ip(q)){ptr(q)[3]++;}return;}
void dr(Q q){ 
  if(!q || ia(q)){return;}                                                    // if null or atom just return
  if(0< --ptr(q)[3]){return;}                                                 // if there is a nonzero refcount return
  if(!t(q)){for(D i=0;i<n(q);i++){dr(qi(q,i));}}                              // this object has refcount==0. if type 0, recurse on children
  if(1==ha(q))buddyfree(q);                                                   // then free this q
  return;                                                                     // should I consider returning a control sentinel here (type)
}
Q t2g(Q q){
  if(!itp(q)){return q;};
  Q *h=ptr(q);Q g=tsng(h[0],h[1],h[2],h[4]); // copy header, ignore refcount and capacity
  if(1==sh(q)){
    if(t(q)){memcpy(p(g),p(q),(1<<h[2])*h[4]);return g;}
    for(D i=0;i<n(g);i++){Q v=qi(q,i);if(itp(v)){v=t2g(v);};zid(g,i,v);}
  }
  if(2==sh(q)){
    zid(g,0,t2g(pi(q,0))); // copy hash
    zid(g,1,t2g(pi(q,1))); // copy keys
    zid(g,2,t2g(pi(q,2))); // copy values
  }
  
  return g;
}

C* VT;
C* MAP="0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";

void pr_b(Q q,D b){if(q<b){printf("%c",MAP[q]);return;}pr_b(q/b,b);printf("%c",MAP[q%b]);}

void pr(Q q){
  if(0==q){return;}
  if(0==t(q)){
    
    if(!sh(q)){printf("atom type 0?%lld ",q);}
    if(1==sh(q)){printf("(");D nq=n(q);for(D i=0;i<nq;i++){pr(pi(q,i));if(i<nq-1){printf(";");}}; printf(")");}
    if(2==sh(q)){
      //pr(pi(q,0)); // print hash
      printf("{");
      Q kq = pi(q,1);Q nkq=n(kq);
      for(D i=0; i<n(kq); ++i){
        pr(pi(kq,i)); printf(":");
        pr(qi(pi(q,2),i));printf(i==nkq-1?"}":";");
      }
    }
   
  }
  if(1==t(q)){pr_b(d(q),62);}
  if(2==t(q)){printf("%c",VT[v(q)]);}
  if(10==t(q)){printf("adverb: %c\n",a(q));}
  if(18==t(q)){printf("control: %d\n",c(q));}
  if(3==t(q)){
    if(0==sh(q)){printf("%lld",d(q));}
    if(1==sh(q)){if(n(q)){for(D i=0;i<n(q);i++){printf("%lld",pi(q,i));if(i<n(q)-1){printf(" ");}}} else {printf("!0");}}
  }
  if(4==t(q)){for(D i=0;i<n(q);i++){pr(pi(q,i));}}
  if(5==t(q)){printf("hash table: ");for(D i=0;i<cp(q);i++){printf("%d:%lld ",i,pi(q,i));}printf("\n");}
  if(7==t(q)){printf("`");pr_b(d(q),62);}
}
DV VD[9];
MV VM[9];

Q id(Q w){return w;}
Q en(Q w){B aw=ia(w);Q z=vn(aw?t(w):0,ls(w),1);if(aw){pid(z,0,d(w));}else{zid(z,0,w);};return z;}
Q tp(Q w){return an(t(w));}
Q ct(Q w){return an(n(w));}

typedef enum {DB,LB,RB,MB} BM; // broadcast mode
Q vb(Q a,Q w,MV mv,DV dv,BM m){B ta=t(a),tw=t(w),sa=sh(a),sw=sh(w);D na=n(a),nw=n(w);
  if(DB==m && na!=nw && sa && sw){return ac(2);}
  B ib=DB==m?((!ta)||(!tw)):RB==m?!tw:LB==m?!ta:/*MB==m*/!tw;
  if(ib){
    D nz=DB==m?(sa?na:nw):RB==m?nw:LB==m?na:nw;
    Q z=ln(nz);
    for(D i=0;i<nz;i++){
      Q ai=sa?qi(a,i):a;Q wi=sw?qi(w,i):w;
      Q zi=DB==m?dv(ai,wi):RB==m?dv(a,wi):LB==m?dv(ai,w):/*MB==m*/mv(wi);
      if(18==t(zi)){return zi;} // sentinel bubbled up. later: add cleanup
      zid(z,i,zi);
    }
    return z;
  }
  return ac(0);
}

Q car(Q w){return 0==sh(w)?w:qi(w,0);}

Q nt(Q w){
  Q z=vb(0,w,nt,0,MB);
  if(18!=t(z)){return z;}if(c(z)){return z;} // if data is returned, return the data. if a control sentinel is returned and its payload is nonzero then return, otherwise listen to theh control signal to do the proper work.
  if(ia(w)){return an(!d(w));}
  if(1==sh(w)){z=vn(3,ls(w),n(w));for(D i=0;i<n(w);i++){pid(z,i,!pi(w,i));};return z;}
  return ac(1); // return shape error
}

Q tl(Q w){
  B aw=ia(w);if(aw){w=en(w);};D nw=n(w);Q z=ln(nw);
  for(D i=0;i<nw;i++){
    Q ni=pi(w,i);Q zi=vn(3,ls(w),ni);for(D j=0;j<ni;j++){pid(zi,j,j);}
    zid(z,i,zi);
  }
  return aw?car(z):z;
}

Q at(Q a,Q w){
  Q z=vb(a,w,0,at,RB);
  if(18!=t(z)){return z;}if(c(z)){return z;}
  B aa=ia(a),aw=ia(w);B tz=t(a);B nz=n(w);B shz=sh(w);
  if(aw){return aa?a:qi(a,ra(w));}
  z=vn(t(a),ls(a),nz);
  for(D i=0;i<nz;i++){ // unmerge this. use shape of w to dispatch. 
    Q zi=ri(a,aw?ra(w):ri(w,i));
    qid(z,i,zi);
  }
  return z;
}

Q math(Q a,Q w,DV op){ // anything that gets here has been broadcasted. we can use the universal getter on both a and w
  D na=n(a),nw=n(w);D nz=na<nw?nw:na;B sa=sh(a),sw=sh(w);B shz=sh(a)<sh(w)?sh(w):sh(a);B lz=ls(a)<ls(w)?ls(w):ls(a);
  if(0==shz){return an(op(d(a),d(w)));}
  Q z=vn(t(a),lz,nz);
  for(D i=0;i<nz;i++){Q ai=sa?ri(a,i):ra(a);Q wi=sw?ri(w,i):ra(w);
    Q zi=op(ai,wi);
    pid(z,i,zi);
  }
  return z;
}
Q pl_aa(Q a,Q w){ return a+w;}
Q ml_aa(Q a,Q w){ return a*w;}
Q pl(Q a,Q w){Q z=vb(a,w,0,pl,DB);if(18!=t(z)){return z;}if(c(z)){return z;}; return math(a,w,pl_aa);} // later: float support and type promotion. 
Q ml(Q a,Q w){Q z=vb(a,w,0,ml,DB);if(18!=t(z)){return z;}if(c(z)){return z;}; return math(a,w,ml_aa);}

Q set(Q a,Q w,D sp){
  dkv(SC[sp],a,w);
  return w;
}

Q ca(Q a,Q w){
  B tz=(t(a)==t(w))?t(a):0;
  D j=0;D na=n(a),nw=n(w);Q z=vn(tz,tz?ls(a):3,na+nw);
  for(D i=0;i<na;i++,j++){Q ai=at(a,an(i));qid(z,j,tz?ra(ai):ai);} // decode if not type 0
  for(D i=0;i<nw;i++,j++){Q wi=at(w,an(i));qid(z,j,tz?ra(wi):wi);} // decode if atom or somethig
  return z;
}

DV VD[9]={0,0,0,at,0,pl,ml,0,ca};
MV VM[9]={0,nt,tl,tp,ct,0,car,id,en};
C* VT=" ~!@#+*:,";  // later: (logical:min,max,equal,lesser,greater,not),(bitwise:and,or,xor,bnot)

Q Ap(Q a){Q p=tsn(4,1,3,1);pid(p,0,a);return p;}
Q e(Q* q);
Q E(Q* q,C tc);
Q eoc(Q* q){
  if(SP+1 >= 1024) return ac(6); // scope depth overflow
  SP++;D csp=SP; // cache the SP of this new allocation, return that.
  SC[SP] = dn(0,3,0); // Allocate new dictionary for the new scope
  E(q+1,'}'); // Evaluate the inner expression
  return SC[csp]; // Return the created dictionary
}

Q ecc(Q* q){
  if(SP > 0) SP--;
  return tsn(4,1,3,0); // Behave like a semicolon, terminating the expression
}

Q emv(Q*q){
  Q w=e(q+1);
  if(4==t(w)){Q p=tsn(4,1,3,1);pid(p,0,*q);return ca(p,w);}
  return VM[v(*q)](w);
}

Q edv(Q a,Q*q){
  D current_sp = SP; // Cache the scope pointer before evaluating the right-hand side.
  Q w=e(q+1);B i=v(*q);
  if(4==t(w)&&(7!=i)){Q p=tsn(4,1,3,2);pid(p,0,a);pid(p,1,*q);return ca(p,w);}  // handle partial evaluations but allow assignment of them instantly. 
  a=((1==t(a))&&(7!=i))?dk(SC[current_sp],a):a;
  // If this is an assignment, use the cached scope pointer to write into the correct scope.
  if(7==i){return set(a,w,current_sp);}
  DV dv=VD[i];
  return dv(a,w);
}

Q E(Q* q, C tc){
  Q r = 0;
  while(*q && !(18==t(*q)&&tc==c(*q))){
    r = e(q);
    // Find the end of the evaluated expression
    while(*q && !(18==t(*q) && c(*q)==';')) q++;
    // If we found a semicolon, skip it to start the next expression
    if(*q) q++;
  }
  return r;
}

Q e(Q* q){
  Q a=*q;
  if(!a){return tsn(4,1,3,0);}                                 // If a is the end of the stream then we must have missing data. return type 4
  if(18==t(a) && ';'==c(a)){return tsn(4,1,3,0);}              
  if(18==t(a)){
    if('{'==c(a)) return eoc(q);                                // this creates a scope dictionary and returns it.
    if('}'==c(a)) return ecc(q);                                // this terminates a scope dictionary and behaves like a semicolon
    if(';'==c(a)) return tsn(4,1,3,0);                          // Semicolon is a statement terminator, acts as end-of-stream for this expression.
  }
  Q w=q[1];                                                    // we know a is non zero, so we can read q[1] but it may be end of stream, or a semicolon
  B endexpr = !w || (18==t(w) && c(w)==';');         // end of expression is null or semicolon or }
  B endscope = w && (18==t(w) && c(w)=='}');                 // end of scope is }
  B end = endexpr || endscope;
  if(endscope){ecc(q);}
  return (2==t(a)&&!end)  ?                                // if a is a verb and w isn't the end of the stream
         emv(q)        :                                       //  then evaluate a monadic verb
         (2==t(a)&&end) ?                                   // if a is a verb and we have hit the end of the stream
         Ap(a)         :                                       //  then create a dyadic partial evaluation
         (!end&&2==t(w))  ?                                   // if w is non-zero and is a verb
         edv(a,q+1)    :                                       //  then eval dyadic verb
         (4==t(a)&&end) ?                                   // if a is a partial evaluation and we don't have a w 
         a             :                                       //  then just return the partial up the stack. 
         (1==t(a))     ?                                       // if a is a reference (and not being assigned to)
         dk(SC[SP],a)  :                                       //  then return the value of the reference
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
static C* CST="1757AAA988777B49333333333378AAAA722222222222222222222222222898AA6222222222222222222222222228A87";
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
#if defined(_MSC_VER)
  AB[0]=(Q*)VirtualAlloc(0, ARENA_SZ, MEM_RESERVE, PAGE_READWRITE);if(!AB[0]){printf("VA 0 failed\n");exit(1);}AC[0]=ARENA_SZ/BUMP_UNIT_BYTES;AI[0]=0;
  AB[1]=(Q*)VirtualAlloc(0, ARENA_SZ, MEM_RESERVE, PAGE_READWRITE);if(!AB[1]){printf("VA 1 failed\n");exit(1);}AC[1]=ARENA_SZ/BUDDY_UNIT_BYTES;AI[1]=0;
#else
  AB[0]=(Q*)mmap(0, ARENA_SZ, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);if(AB[0]==MAP_FAILED){printf("mmap 0 failed\n");exit(1);}AC[0]=ARENA_SZ/BUMP_UNIT_BYTES;AI[0]=0;
  AB[1]=(Q*)mmap(0, ARENA_SZ, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);if(AB[1]==MAP_FAILED){printf("mmap 1 failed\n");exit(1);}AC[1]=ARENA_SZ/BUDDY_UNIT_BYTES;AI[1]=0;
#endif
  printf("AB[0] AC[0] AI[0] %lld %lld %lld\n",AB[0],AC[0],AI[0]);
  printf("AB[1] AC[1] AI[1] %lld %lld %lld\n",AB[1],AC[1],AI[1]);
  buddyinit(1);
  G=dni(0,3,0,1); // global dictionary
  SC[0]=dni(0,3,0,0); SP=0;
  while (1) {
    printf(" "); if (!fgets(buffer, 100, stdin)){break;}
    buffer[strcspn(buffer, "\r")] = '\0'; buffer[strcspn(buffer, "\n")] = '\0';
    if (strcmp(buffer, "\\\\") == 0){break;}
    if(0==SP){
      for(D i=0;i<n(pi(SC[0],1));i++){
        Q gk=pi(pi(SC[0],1),i);Q gv=pi(pi(SC[0],2),i);
        dkv(G,t2g(gk),t2g(gv));
      }
      AI[0]=0;SC[0]=dni(0,3,0,0); SP=0; 
     } // reset THI only if evaluation takes us back to the global scope. 
    Q r=E(lx(buffer),'\0');
    pr(r);printf("\n");
  }
  return 0;
}