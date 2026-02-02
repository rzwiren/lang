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
  #include <fcntl.h>
  #include <unistd.h>
  #include <sys/stat.h>
#endif

typedef unsigned long long Q;typedef unsigned int D;typedef unsigned short W;typedef unsigned char B;typedef char C;
typedef long long J; typedef int I; typedef short H;
typedef Q(*RDO)(Q,Q);                                                           // function pointer for raw dyadic operation
typedef Q(*RMO)(Q);                                                             // function pointer for raw monadic operation
typedef Q(*DV)(B,Q,Q,Q);                                                        // function pointer for dyadic verb (arena;verb;alpha;omega)
typedef Q(*MV)(B,Q,Q);                                                          // function pointer for monadic verb (arena;verb;omega)
typedef Q(*ADV)(B,Q,Q,Q);                                                       // function pointer for adverb (arena;verb;alpha;omega)

#define BUMP_UNIT_BYTES   16
#define BUDDY_UNIT_BYTES  4096

#define BUMP_UNIT_QS   (BUMP_UNIT_BYTES / sizeof(Q))
#define BUDDY_UNIT_QS  (BUDDY_UNIT_BYTES / sizeof(Q))

#define ARENA_SZ       (1ULL<<32)
Q* AB[4];Q AI[4];Q AC[4];
Q AM[4];
Q AQ[4]={BUMP_UNIT_QS,BUDDY_UNIT_QS,BUMP_UNIT_QS,0};
Q BF[32];
B ha(Q q){return (q>>4)&3;}
Q FT_addr=0, FT_sz=0, FT_cap=0, FT_h=0, FT_fn=0;
Q hp(B a,Q q){return q>>(0==a?6:1==a?11:6);}
Q pi(Q q,D i);
Q* ptr(Q q){
  B a=ha(q);
  if(a==2){
    Q off = (q>>6) & 0x3FFFFFFFFF;
    D fid = q>>44;
    return ((Q*)pi(FT_addr,fid)) + (off*AQ[a]);
  }
  return AB[a]+(hp(a,q)*AQ[a]);
}

B ip(Q q){return q&&!(15&q);}                                                  // Is this Q a pointer? nonzero in low 3 bits means atom
B itp(Q q){return ip(q) && ha(q)==0;}                                         // Is this Q a pointer to the bump allocated region?
B*p(Q q){return (B*)(ptr(q)+6);}                                              // pointers point at header after decoding and need to be adjusted to point at the data
Q di(Q q){return q>>4;}                                                        // shift out the flags. decodes small integers
Q dv(Q q){return q>>6;}                                                        // verbs are grammatical type, subtype 0. payload in high 59 bits
Q da(Q q){return q>>6;}
Q dc(Q q){return q>>6;}                                                        // controls are grammatical type, subtype 2. payload in high 59 bits

Q ar(Q r){return (r<<4)|1;}                                                   // create an atom of type 1 (reference)
Q av(Q v){return (v<<6)|2;}                                                   // create a verb atom (grammatical type 2, subtype 0)
Q aa(Q a){return (a<<6)|(1<<4)|2;}                                            // create an adverb atom (grammatical type 2, subtype 1)
Q ac(Q c){return (c<<6)|(2<<4)|2;}                                            // create a control atom (grammatical type 2, subtype 2)
Q an(Q n){return (n<(1ULL<<60))?((n<<4)|3):(0|3);}                            // create an atom of type 3 (integer) TODO: heap allocated 64 bit int. return 3 as a tagged 0 for stuff that should really be allocated on heap. bitnot is broken on atoms due to this. 
Q ap(Q v){return (v<<4)|4;}                                                   // create an atom of type 4 (partial eval) - HEAP ONLY
                                                                              // type 5 is hash
Q ach(C c){return ((Q)(B)c<<4)|6;}                                            // create an atom of type 6 (char)
Q as(Q s){return (s<<4)|7;}                                                   // create an atom of type 7 (symbol)
Q aA(B a, D f){return (((Q)f<<8)|a)<<4|9;}                                    // create an atom of type 9 (arena/file)
Q et(Q q,B t){return 0==t?q:1==t?ar(q):2==t?av(q):3==t?an(q):4==t?ap(q):6==t?ach(q):ac(q);} // encode data of an atom based on the type. TODO: handle 9

#define AR_ID(x) ((x)&0xFF)
#define AR_FID(x) ((x)>>8)
#define MK_AR(a, f) (((Q)(f)<<8)|(a))

B ia(Q q){return !ip(q);}                                                     // is atom  from pointer
B t(Q q){
  if(!ia(q))return ptr(q)[0];
  B tag=q&15;
  if(tag==2)return q&63;
  return tag;
}
B sh(Q q){return ia(q)?0:ptr(q)[1];}                                           // shape    from header
B ls(Q q){return ia(q)?3:ptr(q)[2];}                                           // logeltsz from header EDGE CASE: should type 0 automatically return 3 here????
B sz(Q q){return 1<<ls(q);}                                                    // bytesz   from logeltsz
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
Q pz(B z,D c){ return (1<<z)*c;}                                                // payload size in bytes by shape, log elt size, and capacity
Q az(B z,D c){ return hz()+pz(z,c);}                                            // allocation size
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
  if (units <= 1) return 0;
  return floor_ord(units - 1) + 1;
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
Q bumpalloc(B t,B s,B z,D n,D c,Q ar){                                                    
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
  return (off<<6)|(0<<4);
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
Q buddyalloc(B t,B s,B z,D n,D c,Q ar){
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

  return (off << 11) | (ord << 6) | (1 << 4) ;
}
void buddyfree(Q q){
  B a   = ha(q);
  Q off = hp(a,q);
  B ord = (q>>6)&31;
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
void os_truncate(Q h, Q sz);
void* os_remap(void* addr, Q old_cap, Q new_cap, Q h);
Q filebumpalloc(B t, B s, B z, D n, D c, Q ar) {
    D fid = AR_FID(ar);
    Q* addrs = (Q*)p(FT_addr);
    Q* szs   = (Q*)p(FT_sz);
    Q* caps  = (Q*)p(FT_cap);
    Q* hs    = (Q*)p(FT_h);

    Q bytes_needed = az(z, c);
    bytes_needed = (bytes_needed + 15) & ~15; // align to 16 bytes

    Q current_sz_bytes = szs[fid];
    Q current_cap_bytes = caps[fid];
    Q new_sz = current_sz_bytes + bytes_needed;

    if (new_sz > current_cap_bytes) {
        Q new_cap = current_cap_bytes ? current_cap_bytes : (1ULL<<16);
        while (new_cap < new_sz) new_cap *= 2;
        void* new_addr = os_remap((void*)addrs[fid], current_cap_bytes, new_cap, hs[fid]);
        if (!new_addr) { printf("file: grow failed\n"); return ac(2); }
        addrs[fid] = (Q)new_addr;
        caps[fid] = new_cap;
    }

    os_truncate(hs[fid], new_sz);

    Q off_bytes = current_sz_bytes;
    Q* o = (Q*)((B*)addrs[fid] + off_bytes);
    ah(o, t, s, z, 0, n, c);
    memset(o+6, 0, pz(z, c));

    szs[fid] = new_sz; // update used size
    *((Q*)addrs[fid] + 1) = szs[fid]; // Persist size in file header

    Q off_units = off_bytes / 16;

    B ptr_tag = 0;

    return ((Q)fid << 44) | (off_units << 6) | (2 << 4) | ptr_tag;
}

Q tsna(Q ar, B t, B s, B z, D n, D c){
  B a = AR_ID(ar);
  if(a==2) return filebumpalloc(t,s,z,n,c,ar);
  if(a==1) return buddyalloc(t,s,z,n,c,ar);
  return bumpalloc(t,s,z,n,c,ar);
}
Q vna(Q ar, B t, B z, D n){ return tsna(ar, t, 1, z, n, cn(t,1,n)); }
Q lna(Q ar, D n){ return vna(ar, 0, 3, n); }
Q vca(Q ar, B t, B z, D c){ return tsna(ar, t, 1, z, 0, c); }
Q lca(Q ar, D c){ return vca(ar, 0, 3, c); }
Q ln(D n){return vna(0,0,3,n);}

void pr(Q q);
void zid(Q q,D i,Q d);
Q dni(B t,B z,D n,Q ar){                                                              // alloc a dictionary of a certain type and element size with hash table capacity n. 
  D c=cn(5,1,n);
  Q h=vca(ar, 5, 2, c);                                                                   // n means keycount for hash.
  Q k=lca(ar, c);
  Q v=vca(ar, t, z, c);
  Q d=tsna(ar, 0, 2, 3, 3, 3);
  zid(d,0,h);zid(d,1,k);zid(d,2,v);
  return d;
}
Q dn(B t,B z,D n,Q ar){return dni(t,z,n,ar);}
Q dnu(B t,B z,D n,B a){return tsna(a,0,2,3,3,3);}
// varwidth getters
Q Bi(B* b,B z,D i){Q r=0;memcpy(&r,b+z*i,z);return r;}                               // mask this by the size of z then cast to Q. NO SIGN EXTENSION FLOATS MAY LIVE IN HERE TOO.
Q pi(Q q,D i){return Bi(p(q),sz(q),i);}              
Q ri(Q q,D i){
  if(1==sh(q)){return pi(q,i);}
  printf("non shape 1 ri call\n");
  return ac(1);                                                                       // shape error
}
Q vi(D n,D i){if(i>=n){return ac(2);};return an(i);}
Q qi(Q q,D i){B s=sh(q),tq=t(q);
  if(1==s){Q qi=vi(n(q),i);return 34==t(qi)?(printf("qi badidx\n"),qi):et(pi(q,di(qi)),tq);};
  return (printf("non shape 1 qi call\n"),ac(1));
}              // get at index, return tagged Q
Q ra(Q q){                                                                      // read atom
  if(sh(q)){printf("ra: not an atom\n");return ac(1);}
  // Heap atoms store their payload in element 0; tagged atoms store it in the tag bits.
  Q payload = ip(q) ? pi(q,0) : di(q);
  switch(t(q)){
    case 1:  return payload;
    case 2:  return payload;                                                     // verbs are atoms; payload is the verb id
    case 3:  return payload;
    case 7:  return payload;
    case 6:  return payload;
    case 18: return payload;
    case 34: return payload;
    case 8:  return payload;                                                     // needs type 9 here
    default: return ac(5);                                                      // not yet implemented
  }
}
Q grow(Q q,D n,D c,D m){printf("growing\n");exit(1);return ac(5);}                      // not yet implemented but, given a q, old length n, old capacity c, and amount of new items to add, extend the allocation to a new c, set the proper n.
D xn(Q q,D m){                                                                  // if n(q)+m<c then set n to n+m otherwise grow
  D nq=n(q);D c=cp(q);
  printf("q t(q) nq m c %lld %d %d %d %d\n",q,t(q),nq,m,c);
  if(nq+m<=c){ptr(q)[4]=nq+m;}else{grow(q,nq,c,m);}
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
Q NL[1024]; D LP=0;

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
  if(e){                                                                      // overwrite existing value
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
  Q q2a(Q dest_ar, Q q);
  return q2a(1, q);
}

Q q2a(Q dest_ar, Q q); // Forward declare

static inline Q strip_fid(Q q){
    if (ip(q) && ha(q) == 2) return q & ((1ULL << 44) - 1);
    return q;
}

static inline Q atom_payload(Q q){
    return ip(q) ? pi(q, 0) : di(q);
}

static inline Q heap_atom_from(Q dest_ar, Q q){
    B tq = t(q);
    B z = ip(q) ? ls(q) : (tq == 6 ? 0 : 3);
    Q res = tsna(dest_ar, tq, 0, z, 1, 1);
    pid(res, 0, atom_payload(q));
    return res;
}

Q q2a_dict(Q dest_ar, Q q) {
    // A dictionary is a list of 3 pointers: hash, keys, values
    Q res = tsna(dest_ar, 0, 2, 3, 3, 3);

    // Recursively materialize components
    Q h = q2a(dest_ar, pi(q, 0));
    Q k = q2a(dest_ar, pi(q, 1));
    Q v = q2a(dest_ar, pi(q, 2));
    if (AR_ID(dest_ar) == 2) { h = strip_fid(h); k = strip_fid(k); v = strip_fid(v); }
    zid(res, 0, h); // hash
    zid(res, 1, k); // keys
    zid(res, 2, v); // values
    return res;
}

Q q2a_list(Q dest_ar, Q q){
    Q* h = ptr(q);
    B t_q = h[0], s_q = h[1], l_q = h[2];
    D n_q = h[4], c_q = h[5];
    Q res = tsna(dest_ar, t_q, s_q, l_q, n_q, c_q);

    if (t_q == 0) { // List of pointers
        for (D i = 0; i < n_q; i++) {
            // Recursively materialize each element
            Q e = q2a(dest_ar, pi(q, i));
            if (AR_ID(dest_ar) == 2) e = strip_fid(e);
            zid(res, i, e);
        }
    } else { // List of values
        memcpy(p(res), p(q), (1ULL << l_q) * n_q);
    }
    return res;
}

Q q2a(Q dest_ar, Q q) {
    B dest_a = AR_ID(dest_ar);
    D dest_fid = AR_FID(dest_ar);

    if (!ip(q)) {
        return (dest_a == 2) ? heap_atom_from(dest_ar, q) : q;
    }

    if (ha(q) == dest_a) {
        if (dest_a != 2 || (q >> 44) == dest_fid) return q;
    }

    if (sh(q) == 0) return heap_atom_from(dest_ar, q);
    if (sh(q) == 1) return q2a_list(dest_ar, q);
    if (sh(q) == 2) return q2a_dict(dest_ar, q);
    return q;
} 


void* os_map(char* fn, Q* sz, Q* h_out){
  void* addr = 0;
  int is_new = 0;
#if defined(_MSC_VER)
  HANDLE hf = CreateFileA(fn, GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
  if(hf == INVALID_HANDLE_VALUE) {
    hf = CreateFileA(fn, GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, CREATE_NEW, FILE_ATTRIBUTE_NORMAL, NULL);
    if(hf != INVALID_HANDLE_VALUE){
      is_new = 1;
    }
    if(hf == INVALID_HANDLE_VALUE) return 0;
  } else { is_new = 0; }
  LARGE_INTEGER li; GetFileSizeEx(hf, &li); *sz = li.QuadPart;
  if(!*sz && is_new){ *sz=16; li.QuadPart=*sz; SetFilePointerEx(hf, li, NULL, FILE_BEGIN); SetEndOfFile(hf); }
  HANDLE hmap = CreateFileMapping(hf, NULL, PAGE_READWRITE, 0, 0, NULL);
  if(!hmap) { CloseHandle(hf); return 0; }
  addr = MapViewOfFile(hmap, FILE_MAP_ALL_ACCESS, 0, 0, 0);
  CloseHandle(hmap);
  *h_out = (Q)hf;
#else
  int fd = open(fn, O_RDWR | O_CREAT, 0644);
  if(fd < 0) return 0;
  struct stat st; fstat(fd, &st); *sz = st.st_size;
  if(!*sz){ is_new=1; *sz=16; ftruncate(fd, 16); } else { is_new = 0; }
  addr = mmap(0, *sz, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  if(addr == MAP_FAILED) { close(fd); return 0; }
  *h_out = (Q)fd;
#endif
  if(is_new && addr && *sz >= 16) memset(addr, 0, 16);
  return addr;
}

void os_unmap(D fid){
  Q* addrs = (Q*)p(FT_addr);
  Q* caps  = (Q*)p(FT_cap);
  Q* hs    = (Q*)p(FT_h);
  Q* szs   = (Q*)p(FT_sz);

  if(!addrs[fid]) return;

#if defined(_MSC_VER)
  UnmapViewOfFile((void*)addrs[fid]);
  CloseHandle((HANDLE)hs[fid]);
#else
  munmap((void*)addrs[fid], caps[fid]);
  close((int)hs[fid]);
#endif

  addrs[fid] = 0;
  hs[fid] = 0;
  caps[fid] = 0;
  szs[fid] = 0;
  zid(FT_fn, fid, 0);
}

D find_empty_ft_slot(){
  D idx = n(FT_addr);
  for(D i=0; i<idx; i++){
    if(pi(FT_addr, i) == 0) return i;
  }
  xn(FT_addr, 1);
  xn(FT_sz, 1);
  xn(FT_cap, 1);
  xn(FT_h, 1);
  xn(FT_fn, 1);
  return idx;
}

void os_truncate(Q h, Q sz){
#if defined(_MSC_VER)
  HANDLE hf = (HANDLE)h;
  LARGE_INTEGER li; li.QuadPart = sz;
  SetFilePointerEx(hf, li, NULL, FILE_BEGIN); SetEndOfFile(hf);
#else
  ftruncate((int)h, sz);
#endif
}

void* os_remap(void* addr, Q old_cap, Q new_cap, Q h){
#if defined(_MSC_VER)
  UnmapViewOfFile(addr);
  HANDLE hf = (HANDLE)h;
  HANDLE hmap = CreateFileMapping(hf, NULL, PAGE_READWRITE, (DWORD)(new_cap >> 32), (DWORD)new_cap, NULL);
  if(!hmap) return 0;
  addr = MapViewOfFile(hmap, FILE_MAP_ALL_ACCESS, 0, 0, 0);
  CloseHandle(hmap);
#else
  munmap(addr, old_cap);
  int fd = (int)h;
  addr = mmap(0, new_cap, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
#endif
  return addr;
}

Q ca(B A,Q v,Q a,Q w);

Q file_append(Q a, Q w);
Q file_log(Q a, Q w);
Q file_read_log(Q f);

Q fl(B A, Q v, Q w){
  if(t(w)!=6){printf("file: filename must be string\n"); return ac(2);}
  char fn[256]; D fn_len = n(w); if(fn_len > 255) fn_len = 255;
  for(D i=0; i<fn_len; i++) fn[i] = (char)pi(w,i); fn[fn_len] = 0;

  D idx = n(FT_addr);
  D target_idx = -1;

  // Find if file exists in table. If so, unmap it for reloading.
  for(D i=0; i<idx; i++){
    Q s = pi(FT_fn, i);
    if(s != 0 && n(s) == fn_len && memcmp(p(s), fn, fn_len)==0) {
      os_unmap(i);
      target_idx = i;
      break;
    }
  }

  // If not found, find an empty slot.
  if(target_idx == -1){
    target_idx = find_empty_ft_slot();
  }

  // Map the file.
  Q sz=0, h=0;
  void* map_base = os_map(fn, &sz, &h);
  if(!map_base) { printf("file: map failed\n"); return ac(2); }

  // Populate the slot.
  Q used = *((Q*)map_base + 1);
  if(used < 16) used = sz;
  if(used < 16) used = 16; // Minimum header size

  Q fn_q = vca(1, 6, 0, fn_len);
  memcpy(p(fn_q), fn, fn_len);
  ((Q*)p(FT_addr))[target_idx] = (Q)map_base;
  ((Q*)p(FT_sz))[target_idx]   = used;
  ((Q*)p(FT_cap))[target_idx]  = sz;
  ((Q*)p(FT_h))[target_idx]    = h;
  zid(FT_fn, target_idx, fn_q);

  return aA(2, target_idx);
}

Q sv(B A, Q v, Q a, Q w){
  if(t(a)!=6){printf("save: filename must be string\n"); return ac(2);}
  char fn[256]; D fn_len = n(a); if(fn_len > 255) fn_len = 255;
  for(D i=0; i<fn_len; i++) fn[i] = (char)pi(a,i); fn[fn_len] = 0;

  remove(fn); // Overwrite by removing first.

  D fid = find_empty_ft_slot();

  Q sz=0, h=0;
  void* map_base = os_map(fn, &sz, &h);
  if(!map_base) { printf("file: save failed to map\n"); return ac(2); }

  // Temporarily populate FT to use materialize
  ((Q*)p(FT_addr))[fid] = (Q)map_base;
  ((Q*)p(FT_sz))[fid]   = 16;
  ((Q*)p(FT_cap))[fid]  = sz;
  ((Q*)p(FT_h))[fid]    = h;

  Q f_handle = aA(2, fid);
  Q root_ptr = q2a(di(f_handle), w);
  *(Q*)map_base = strip_fid(root_ptr);

  os_unmap(fid);

  return w;
}

Q file_read(Q f){
  D fid = AR_FID(di(f));
  Q root = *(Q*)((Q*)p(FT_addr))[fid];
  if(ip(root) && ha(root)==2){
    root |= ((Q)fid << 44); // Inject file index into root pointer
  }
  return root;
}
Q ld(B A, Q v, Q w){
  Q f = fl(A,v,w);
  if(t(f)==2 && dc(f)==2) return f;
  return file_read(f);
}
Q file_append(Q a, Q w){
  D fid = AR_FID(di(a));
  Q* addrs = (Q*)p(FT_addr);

  // 1. Read the old root object's pointer.
  Q old_root_ptr = file_read(a);

  Q new_root_ptr;
  if (old_root_ptr) {
    // 2. Materialize the old root into a temporary arena (arena 0).
    Q old_root_ram = q2a(0, old_root_ptr);
    // 3. Concatenate the new data 'w' in the temporary arena.
    Q new_root_ram = ca(0, av(8), old_root_ram, w);
    // 4. Materialize the combined result back into the file arena.
    new_root_ptr = q2a(di(a), new_root_ram);
  } else {
    new_root_ptr = q2a(di(a), w);
  }

  // 5. Update the file header to point to the new root.
  *(Q*)addrs[fid] = strip_fid(new_root_ptr);

  return a;
}

Q file_log(Q a, Q w){
  q2a(di(a), w);
  return a;
}

Q file_read_log(Q f){
  D fid = AR_FID(di(f));
  Q* addrs = (Q*)p(FT_addr);
  Q* szs = (Q*)p(FT_sz);
  Q* base_addr = (Q*)addrs[fid];
  Q used_size = szs[fid];

  // Preallocate enough capacity so we never hit grow() (currently unimplemented).
  // Smallest on-disk object is at least 64 bytes: 48-byte header + payload, aligned to 16.
  Q max_entries = 1;
  if (used_size > 16) max_entries = ((used_size - 16) / 64) + 1;
  Q result_list = lca(0, (D)max_entries);
  
  // Log data starts after the 16-byte file header reservation
  Q offset = 16; 

  while(offset < used_size){
    Q* obj_header = (Q*)( (B*)base_addr + offset );
    
    B type = obj_header[0];
    B ls = obj_header[2];
    D c = obj_header[5];

    // Reconstruct the Arena 2 pointer for the object at the current offset
    // NOTE: Pointer low-nibble must be 0. Type lives in the heap header, not in the pointer tag.
    Q obj_ptr = ((offset >> 4) << 6) | (2 << 4);
    obj_ptr |= ((Q)fid << 44); // Inject file ID

    // Append the discovered object's pointer to our result list
    xn(result_list, 1);
    zid(result_list, n(result_list)-1, obj_ptr);

    // Calculate the space this object took on disk to find the next one
    Q disk_size = az(ls, c);
    disk_size = (disk_size + 15) & ~15;
    
    if (disk_size == 0) break; // Safeguard against corrupted data

    offset += disk_size;
  }

  return result_list;
}

#define VTZ 25
#define ATZ 15
C* VT[];C* AT[];
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
  if(1==t(q)){pr_b(ip(q)?pi(q,0):di(q),62);}
  if(2==t(q)){printf("%s",VT[dv(q)]);}
  if(18==t(q)){printf("%s",AT[da(q)]);}
  if(34==t(q)){printf("control: %c\n",(char)dc(q));}
  if(9==t(q)){printf("file:%d", (int)AR_FID(di(q)));}
  if(6==t(q)){
    if(0==sh(q)){printf("\"%c\"",(char)(ip(q)?pi(q,0):di(q)));}
    if(1==sh(q)){printf("\"");for(D i=0;i<n(q);i++)printf("%c",(char)pi(q,i));printf("\"");}
  }
  if(3==t(q)){
    if(0==sh(q)){printf("%lld",(long long)(ip(q)?pi(q,0):di(q)));}
    if(1==sh(q)){if(n(q)){for(D i=0;i<n(q);i++){printf("%lld",pi(q,i));if(i<n(q)-1){printf(" ");}}} else {printf("!0");}}
  }
  if(4==t(q)){for(D i=0;i<n(q);i++){pr(pi(q,i));}}
  if(5==t(q)){printf("hash table: ");for(D i=0;i<cp(q);i++){printf("%d:%lld ",i,pi(q,i));}printf("\n");}
  if(7==t(q)){printf("`");pr_b(ip(q)?pi(q,0):di(q),62);}
}
DV VD[VTZ];
MV VM[VTZ];

Q id(B A,Q v,Q w){return w;}
Q en(B A,Q v,Q w){B aw=ia(w);Q z=vna(0,aw?t(w):0,ls(w),1);if(aw){pid(z,0,di(w));}else{zid(z,0,w);};return z;}
Q tp(B A,Q v,Q w){return an(t(w));}
Q ct(B A,Q v,Q w){return an(n(w));}

Q dispatch_monad(Q v,Q w);
Q dispatch_dyad(Q v,Q a,Q w);

typedef enum {DB,LB,RB,MB} BM;                                                          // broadcast mode
Q vb(B A,Q v,Q a,Q w,BM m,I d){ // arena verb alpha omega broadcast mode depth
  if(0==d)return ac(0);
  B ta=t(a),tw=t(w),sa=sh(a),sw=sh(w);D na=2==sa?n(pi(a,1)):n(a),nw=2==sw?n(pi(w,1)):n(w);
  if(DB==m && na!=nw && sa && sw){printf("vb length\n");return ac(2);}
  B ib=d>0?1:(DB==m?((!ta)||(!tw)):RB==m?!tw:LB==m?!ta:/*MB==m*/!tw);
  if(ib){
    D nz=DB==m?(sa?na:nw):RB==m?nw:LB==m?na:nw;
    Q z=ln(nz);
    for(D i=0;i<nz;i++){
      Q ai=(m!=RB && 1==sa)?qi(a,i):(m!=RB && 2==sa)?qi(pi(a,2),i):a;Q wi=(m!=LB && 1==sw)?qi(w,i):(m!=LB && 2==sw)?qi(pi(w,2),i):w;
      //Q zi=DB==m?dv(ai,wi):RB==m?dv(a,wi):LB==m?dv(ai,w):/*MB==m*/mv(wi);
      Q zi=0;
      if(MB==m)zi=dispatch_monad(v,wi);
      else zi=dispatch_dyad(v,ai,wi);
      if(34==t(zi)){return zi;}                                                         // sentinel bubbled up. later: add cleanup
      zid(z,i,zi);
    }
    if(2==sa){ // TODO: arena awareness
      Q zd=dnu(0,3,0,A);
      Q *hh=ptr(pi(a,0));Q hc=tsna(A,hh[0],hh[1],hh[2],hh[4],hh[5]);
      memcpy(p(hc),p(pi(a,0)),(1<<hh[2])*hh[4]);
      Q *hk=ptr(pi(a,1));Q kc=tsna(A,hk[0],hk[1],hk[2],hk[4],hk[5]);
      memcpy(p(kc),p(pi(a,1)),(1<<hk[2])*hk[4]);
      zid(zd,0,hc);zid(zd,1,kc);zid(zd,2,z);
      return zd;
    }
    if(2==sw){ // TODO: arena awareness
      Q zd=dnu(0,3,0,A);
      Q *hh=ptr(pi(w,0));Q hc=tsna(A,hh[0],hh[1],hh[2],hh[4],hh[5]);
      memcpy(p(hc),p(pi(w,0)),(1<<hh[2])*hh[4]);
      Q *hk=ptr(pi(w,1));Q kc=tsna(A,hk[0],hk[1],hk[2],hk[4],hk[5]);
      memcpy(p(kc),p(pi(w,1)),(1<<hk[2])*hk[4]);
      zid(zd,0,hc);zid(zd,1,kc);zid(zd,2,z);
      return zd;
    }
    return z;
  }
  return ac(0);
}

Q car(B A,Q v,Q w){return 0==sh(w)?w:qi(w,0);}

Q math_m(Q w,RMO op){ // TODO: arena awareness
  if(0==sh(w)){return an(op(di(w)));}
  Q z=vna(0,t(w),ls(w),n(w));
  for(D i=0;i<n(w);i++){pid(z,i,op(ri(w,i)));}
  return z;
}
Q nt_aa(Q w){return !w;}
Q nt(B A,Q v,Q w){Q z=vb(A,v,0,w,MB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}return math_m(w,nt_aa);}

Q tl(B A,Q v,Q w){
  B aw=ia(w);if(aw){w=en(A,av(8),w);};D nw=n(w);Q z=lna(A,nw);
  for(D i=0;i<nw;i++){
    Q ni=pi(w,i);Q zi=vna(0,3,ls(w),ni);for(D j=0;j<ni;j++){pid(zi,j,j);}
    zid(z,i,zi);
  }
  return aw?car(A,av(6),z):z;
}

Q at(B A,Q v,Q a,Q w){
  Q z=vb(A,v,a,w,RB,-1);
  if(34!=t(z)){return z;}if(dc(z)){return z;}
  B aa=ia(a),aw=ia(w);B tz=t(a);B nz=n(w);B shz=sh(w);
  if(aw){return aa?a:qi(a,ra(w));} // TODO: arena awareness
  z=vna(0,t(a),ls(a),nz);
  for(D i=0;i<nz;i++){ // unmerge this. use shape of w to dispatch. 
    Q zi=ri(a,aw?ra(w):ri(w,i));
    qid(z,i,zi);
  }
  return z;
}

Q math(Q a,Q w,RDO op){ // anything that gets here has been broadcasted. we can use the universal getter on both a and w
  D na=n(a),nw=n(w);D nz=na<nw?nw:na;B sa=sh(a),sw=sh(w);B shz=sh(a)<sh(w)?sh(w):sh(a);B lz=ls(a)<ls(w)?ls(w):ls(a);
  if(0==shz){return an(op(di(a),di(w)));}
  Q z=vna(0,t(a),lz,nz); // TODO: arena awareness
  for(D i=0;i<nz;i++){Q ai=sa?ri(a,i):ra(a);Q wi=sw?ri(w,i):ra(w);
    Q zi=op(ai,wi);
    pid(z,i,zi);
  }
  return z;
}
Q pl_aa(Q a,Q w){ return a+w;}
Q ml_aa(Q a,Q w){ return a*w;}
Q mn_aa(Q a,Q w){return a<w?a:w;}
Q mx_aa(Q a,Q w){return a>w?a:w;}
Q eq_aa(Q a,Q w){return a==w;}
Q lt_aa(Q a,Q w){return a<w;}
Q gt_aa(Q a,Q w){return a>w;}
Q an_aa(Q a,Q w){return a&w;}
Q or_aa(Q a,Q w){return a|w;}
Q xr_aa(Q a,Q w){return a^w;}
Q sb_aa(Q a,Q w){return a-w;}

Q bn_aa(Q w){return ~w;}
Q ng_aa(Q w){return -w;}

Q pl(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,pl_aa);} // later: float support and type promotion. 
Q ml(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,ml_aa);}
Q mn(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,mn_aa);}
Q mx(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,mx_aa);}
Q eq(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,eq_aa);}
Q lt(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,lt_aa);}
Q gt(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,gt_aa);}
Q nd(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,an_aa);}
Q or(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,or_aa);}
Q xr(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,xr_aa);}
Q sb(B A,Q v,Q a,Q w){Q z=vb(A,v,a,w,DB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math(a,w,sb_aa);}

Q bn(B A,Q v,Q w){Q z=vb(A,v,0,w,MB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math_m(w,bn_aa);}
Q ng(B A,Q v,Q w){Q z=vb(A,v,0,w,MB,-1);if(34!=t(z)){return z;}if(dc(z)){return z;}; return math_m(w,ng_aa);}

Q set(Q a,Q w,D sp){
  dkv(SC[sp],a,w);
  return w;
}

Q ca(B A,Q v,Q a,Q w){
  if(t(a)==9) return file_append(a,w);
  // Arena-aware concatenation
  Q dest_ar = 0; // Default to temporary arena
  if (!ia(a)) {
    B ha_a = ha(a);
    if (ha_a == 2) dest_ar = MK_AR(2, a >> 44);
    else dest_ar = ha_a;
  }
  if (!ia(w)) {
    B ha_w = ha(w);
    if (ha_w == 2) {
      if (AR_ID(dest_ar) != 2) dest_ar = MK_AR(2, w >> 44);
    } else if (ha_w > AR_ID(dest_ar) && AR_ID(dest_ar) != 2) {
      dest_ar = ha_w;
    }
  }

  if (t(w)==9) w = file_read(w); // If w is a file, read its root

  B tz = (t(a)==t(w)) ? t(a) : 0;
  D j=0; D na=n(a), nw=n(w);
  Q z = vna(dest_ar, tz, tz ? ls(a) : 3, na+nw);
  for(D i=0;i<na;i++,j++){Q ai=at(A,av(3),a,an(i));qid(z,j,tz?ra(ai):ai);} // decode if not type 0
  for(D i=0;i<nw;i++,j++){Q wi=at(A,av(3),w,an(i));qid(z,j,tz?ra(wi):wi);} // decode if atom or somethig
  return z;
}

Q el(B A,Q v,Q a,Q w){return vb(A,v,a,w,LB,1);}
Q er(B A,Q v,Q a,Q w){return vb(A,v,a,w,RB,1);}
Q ed(B A,Q v,Q a,Q w){return vb(A,v,a,w,DB,1);}
Q em(B A,Q v,Q a,Q w){return vb(A,v,0,w,MB,1);}
Q ov(B A,Q v,Q a,Q w){
  if(0==sh(w))return dispatch_monad(v,w);
  D nw=n(w);if(0==nw){if(a)return a;printf("ov empty\n");return ac(2);}
  Q acc;D i=0;
  if(a){acc=a;}else{acc=qi(w,0);i=1;} // TODO: arena awareness
  for(;i<nw;i++){acc=dispatch_dyad(v,acc,qi(w,i));}
  return acc;
}
Q sc(B A,Q v,Q a,Q w){
  if(0==sh(w))return dispatch_monad(v,w);
  D nw=n(w);D zn=a?nw+1:nw;Q z=ln(zn);
  Q acc;D i=0;D j=0;
  if(a){acc=a;zid(z,j++,acc);}else{acc=qi(w,0);zid(z,j++,acc);i=1;} // TODO: arena awareness
  for(;i<nw;i++){acc=dispatch_dyad(v,acc,qi(w,i));zid(z,j++,acc);}
  return z;
}
Q lfa(B A,Q v,Q a,Q w){
  if(ia(w))return a?dispatch_dyad(v,a,w):dispatch_monad(v,w);
  D nw=n(w);Q z=ln(nw);
  for(D i=0;i<nw;i++){
    Q wi=qi(w,i);
    Q r=lfa(A,v,a,wi);
    zid(z,i,r);
  }
  return z;
}
Q lvs(B A,Q v,Q a,Q w){
  if(a)return ac(2);
  Q h=dispatch_monad(v,w);
  if(ia(w)){Q z=ln(1);zid(z,0,h);return z;}
  D nw=n(w);
  Q s=ln(nw);
  D md=0;
  for(D i=0;i<nw;i++){
    pid(s,i,lvs(A,v,0,qi(w,i)));
    D d=n(pi(s,i));
    if(d>md)md=d;
  }
  Q z=ln(1+md);
  zid(z,0,h);
  for(D d=0;d<md;d++){
    Q r=ln(nw);
    for(D i=0;i<nw;i++){
      Q si=pi(s,i);D sn=n(si);
      Q val=qi(si,d<sn?d:sn-1);
      zid(r,i,val);
    }
    zid(z,d+1,r);
  }
  for(D i=0;i<nw;i++)dr(pi(s,i));
  return z;
}
Q lvl(B A,Q v,Q a,Q w){
  if(!a)return dispatch_monad(v,w);
  D d=di(a);
  if(0==d)return dispatch_monad(v,w);
  if(ia(w))return dispatch_monad(v,w);
  D nw=n(w);Q z=ln(nw);
  for(D i=0;i<nw;i++){
    Q r=lvl(A,v,an(d-1),qi(w,i));
    zid(z,i,r);
  }
  return z;
}
Q lsl(B A,Q v,Q a,Q w){
  D limit=a?di(a):0;
  Q h=dispatch_monad(v,w);
  if(0==limit||ia(w)){Q z=ln(1);zid(z,0,h);return z;}
  D nw=n(w);
  Q s=ln(nw);
  D md=0;
  for(D i=0;i<nw;i++){
    pid(s,i,lsl(A,v,an(limit-1),qi(w,i)));
    D d=n(pi(s,i));
    if(d>md)md=d;
  }
  Q z=ln(1+md);
  zid(z,0,h);
  for(D d=0;d<md;d++){
    Q r=ln(nw);
    for(D i=0;i<nw;i++){
      Q si=pi(s,i);D sn=n(si);
      Q val=qi(si,d<sn?d:sn-1);
      zid(r,i,val);
    }
    zid(z,d+1,r);
  }
  for(D i=0;i<nw;i++)dr(pi(s,i));
  return z;
}
Q itr(B A,Q v,Q a,Q w){
  if(!a)return ac(2);
  D n=di(a);
  Q r=w;
  for(D i=0;i<n;i++){
    Q next=dispatch_monad(v,r);
    if(r!=w && r!=next)dr(r);
    r=next;
  }
  return r;
}
Q its(B A,Q v,Q a,Q w){
  if(!a)return ac(2);
  D n=di(a);
  Q z=ln(n+1);
  Q r=w;
  zid(z,0,r);
  for(D i=0;i<n;i++){
    r=dispatch_monad(v,r);
    zid(z,i+1,r);
  }
  return z;
}

Q lg(B A, Q v, Q a, Q w);
Q rl(B A, Q v, Q w);
DV VD[VTZ]={0,0,0,at,0,pl,ml,0,ca,mn,mx,eq,lt,gt,xr,nd,or,0,sb,sv,0,0,0,lg,0};
MV VM[VTZ]={0,nt,tl,tp,ct,0,car,id,en,0,0,0,0,0,0,0,0,bn,ng,0,ld,fl,0,0,rl};
C* VT[VTZ]={" ","~","!","@","#","+","*",":",",","&","|","=","<",">","^","and","or","bnot","-","save","load","file","root","log","readlog"}; // LATER: (grow width:sign/zero extend sx sx) (shift sl sar sr) WAY LATER: Expose comparison flags directly instead of hiding them. 
ADV AVD[ATZ]={0,0 ,ed,0 ,0 ,el,er,0  ,0  ,0,0,lvl,lsl,itr,its};
ADV AVM[ATZ]={0,em,0 ,sc,ov,0 ,0 ,lvs,lfa,0,0,0  ,0  ,0  ,0  };
C* AT[ATZ]={" ","'","T","→","←","↰","↱","↓","↑","↺","↻","↿","⇃","↫","↬"};

Q dispatch_monad(Q v,Q w){
  Q r=dv(v);
  if(r<32)return VM[r](0,v,w);
  D c=(r-32)%15;Q b=av((r-32)/15);
  D idx=c+1;
  if(AVM[idx])return AVM[idx](0,b,0,w);
  if(AVD[idx])return ac(2); // projection not implemented
  return ac(2);
}
Q dispatch_dyad(Q v,Q a,Q w){
  Q r=dv(v);
  if(r<32)return VD[r](0,v,a,w);
  D c=(r-32)%15;Q b=av((r-32)/15);
  D idx=c+1;
  if(AVD[idx])return AVD[idx](0,b,a,w);
  if(AVM[idx])return AVM[idx](0,b,a,w);
  return ac(2);
}

Q lg(B A, Q v, Q a, Q w){
  Q f = fl(0, 0, a);
  if(t(f) == 34) return f;   // propagate file open error sentinel
  if(t(f) != 9) return ac(2);
  return file_log(f, w);
}
Q rl(B A, Q v, Q w){
  Q f = fl(A, v, w);
  if(t(f) == 34) return f;
  if(t(f) != 9) return ac(2);
  return file_read_log(f);
}

Q Ap(Q a){Q p=tsna(0,4,1,3,1,1);pid(p,0,a);return p;}
Q e(Q** q);
Q E(Q** q,C tc);
Q eoc(Q** q){
  (*q)++;
  if(SP+1 >= 1024) return ac(99);                                            // scope depth overflow
  SP++;D csp=SP;                                                            // cache the SP of this new allocation, return that.
  SC[SP] = dn(0,3,0,0);                                                       // Allocate new dictionary for the new scope
  E(q,'}');                                                               // Evaluate the inner expression
  //if(**q && 34==t(**q) && dc(**q)=='}'){ printf("eoc advanced past }\n");(*q)++;}
  return SC[csp];                                                           // Return the created dictionary
}

Q ecc(Q** q){printf("ecc\n");Q d=SC[SP];if(SP > 0) SP--;return d;}                           // Behave like a semicolon, terminating the expression

Q eol(Q** q){
  (*q)++;
  if(LP+1 >= 1024) return ac(99);
  LP++;D clp=LP;
  NL[LP] = vca(0, 0, 3, 64);
  E(q,')');
  //if(**q && 34==t(**q) && dc(**q)==')'){printf("eol advanced past )\n"); (*q)++; }// if we landed on ')' advance theh pointer by 1 at the end.
  return NL[clp];
}
Q ecl(Q** q){Q l=NL[LP];if(LP > 0) LP--;return l;}

Q emv(Q** q){
  Q v=*(*q)++;
  while(18==t(**q)){v=av(dv(v)*15+(da(*(*q)++)-1)+32);}
  Q w=e(q);
  if(4==t(w)){Q p=tsna(0,4,1,3,1,1);pid(p,0,v);return ca(0,av(8),p,w);}
  Q r=dispatch_monad(v,w);
  return r;
}

Q edv(Q a,Q** q){
  D current_sp = SP;Q v=*(*q)++;
  while(18==t(**q)){v=av(dv(v)*15+(da(*(*q)++)-1)+32);}                                                        // Cache the scope pointer before evaluating the right-hand side.
  Q w=e(q);
  if(4==t(w)&&(7!=dv(v))){Q p=tsna(0,4,1,3,2,2);pid(p,0,a);pid(p,1,v);return ca(0,av(8),p,w);}  // handle partial evaluations but allow assignment of them instantly. 
  a=((1==t(a))&&(7!=dv(v)))?dk(SC[current_sp],a):a;
  if(7==dv(v)){return set(a,w,current_sp);}                                     // If this is an assignment, use the cached scope pointer to write into the correct scope.
  Q r=dispatch_dyad(v,a,w);
  return r;
}

Q E(Q** q, C tc){
  Q r = 0;D clp=LP;
  while(**q && !(34==t(**q)&&tc==dc(**q))){
    r=e(q);
    if(tc==')'){Q l=NL[clp];D idx=n(l);xn(l,1);zid(l,idx,r);}
    while(**q && !(34==t(**q) && dc(**q)==';')) { // Find the end of the evaluated expression
      if(34==t(**q) && tc==dc(**q)){printf("early return found %c %d\n",tc,clp);(*q)++;return r;}    // if we find the ending character then break from the loop without advancing past that character
      (*q)++; 
    }                           
    if(**q && 34==t(**q) && ';'==dc(**q)){(*q)++;}  // advance past ; if it was encountered                                                             // If we found a semicolon, skip it to start the next expression
  }
  return r;
}

Q e(Q** q){
  Q a=**q;
  if(!a){return tsna(0,4,1,3,0,0);}                                  // If a is the end of the stream then we must have missing data. return type 4
  if(34==t(a)){
    if('{'==dc(a)){a=eoc(q);}
    if('}'==dc(a)){a=ecc(q);}
    if('('==dc(a)){a=eol(q);}
    if(')'==dc(a)){a=ecl(q);}
    if(';'==dc(a)) return tsna(0,4,1,3,0,0);                          // Semicolon is a statement terminator, acts as end-of-stream for this expression.
  }
  Q w=(*q)[1];                                                     // we know a is non zero, so we can read q[1] but it may be end of stream, or a semicolon
  B endexpr = !w || (34==t(w) && dc(w)==';');                    // end of expression is null or semicolon or }
  B endscope = w && (34==t(w) && dc(w)=='}');                    // end of scope is }
  B endlist = w && (34==t(w) && dc(w)==')');                    // end of list is )
  B end = endexpr || endscope || endlist;
  if(endscope){ecc(q);}
  if(endlist){ecl(q);}
  return (2==t(a)&&!end)  ?                                // if a is a verb and w isn't the end of the stream
         emv(q)        :                                       //  then evaluate a monadic verb // TODO: arena awareness
         (2==t(a)&&end) ?                                   // if a is a verb and we have hit the end of the stream
         Ap(a)         :                                       //  then create a dyadic partial evaluation
         (!end&&2==t(w))  ?                                   // if w is non-zero and is a verb
         edv(a,(((*q)++),q))    :                                       //  then eval dyadic verb
         (4==t(a)&&end) ?                                   // if a is a partial evaluation and we don't have a w 
         a             :                                       //  then just return the partial up the stack. 
         (1==t(a))     ?                                       // if a is a reference (and not being assigned to)
         dk(SC[SP],a)  :                                       //  then return the value of the reference
         a             ;                                       //  otherwise this must be data, return the data.
}

Q R(C a){return ('a'<=a&&a<='z')?ar(a-'a'):0;}
D FG(C* T[],B n,C* s){
  for(D i=0;i<n;i++){
    if(strcmp(T[i],s)==0) return i;
  }
  return 0;
}
D FV(C* s){return FG(VT,VTZ,s);}
D FA(C* s){return FG(AT,ATZ,s);}
Q V(C c){C s[2]={c,0};D i=FV(s);return i?av(i):0;}
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
// static C* CST="1757AA7988777B49333333333378777A7222222222222222222222222228987A6222222222222222222222222228787";
// D cl(C c){B uc=(B)c;if(!uc)return 0;if(uc<' '||uc>126)return 10;C r=CST[uc-' '];return(r>='0'&&r<='9')?r-'0':r-'A'+10;}
static C* CST="1757AA7988777B49333333333378777A7222222222222222222222222228987A6222222222222222222222222228787";
D cl(C c){B uc=(B)c;if(!uc)return 0;if(uc>=128)return 4;if(uc<' '||uc>126)return 10;C r=CST[uc-' '];return(r>='0'&&r<='9')?r-'0':r-'A'+10;}
D TT[9][12]={ // Transition Table
  // NUL SPC ALP DIG DOT QOT BQT VER CTL ADV OTH NEG
    {7,  0,  4,  2,  4,  5,  6,  7,  7,  7,  7,  1}, // 0 S_START
    {7,  7,  7,  2,  7,  7,  7,  7,  7,  7,  7,  7}, // 1 S_NEG
    {7,  8,  7,  2,  3,  7,  7,  7,  7,  7,  7,  7}, // 2 S_INT
    {7,  8,  7,  3,  7,  7,  7,  7,  7,  7,  7,  7}, // 3 S_FLT
    {7,  7,  4,  4,  4,  7,  7,  7,  7,  7,  7,  7}, // 4 S_NAME
    {7,  5,  5,  5,  5,  7,  5,  5,  5,  5,  5,  5}, // 5 S_STR
    {7,  7,  6,  6,  6,  7,  0,  7,  7,  7,  7,  7}, // 6 S_SYM
    {7,  7,  7,  7,  7,  7,  7,  7,  7,  7,  7,  7}, // 7 S_DONE
    {7,  8,  7,  2,  3,  7,  7,  7,  7,  7,  7,  7}, // 8 S_VEC
  };
Q pn(C* s, D len){
  D c=0;C* p=s;
  while(*p){while(*p==' ')p++;if(!*p)break;c++;while(*p&&*p!=' ')p++;}
  if(c==1){p=s;while(*p==' ')p++;C* t=p;while(*p&&*p!=' ')p++;return an(parse_b(t,p-t,10));} // TODO: arena awareness
  Q z=vna(0,3,3,c);p=s;
  for(D i=0;i<c;i++){while(*p==' ')p++;C* t=p;while(*p&&*p!=' ')p++;pid(z,i,parse_b(t,p-t,10));}
  return z;
}
Q* lx(C*b){D l=strlen(b);Q*q=malloc(sizeof(Q)*(l+1));D qi=0;C*p=b;D st=0; // st:state
  while(st!=7){
    if((B)*p==0xE2){
      C t[4];t[0]=p[0];t[1]=p[1];t[2]=p[2];t[3]=0;
      D ai=FA(t);
      if(ai){q[qi++]=aa(ai);p+=3;st=0;continue;}
    }
    C*s=p;D cc=cl(*p);st=TT[0][cc]; // s:token start
    if(st==0){p++;continue;} // whitespace
    if(cc>=7&&cc<=9){C ts[2]={*p,0};q[qi++]=cc==7?av(FV(ts)):cc==8?ac(*p):aa(FA(ts));p++;st=0;continue;} // verbs, controls, adverbs
    while(st!=7){
      p++;cc=cl(*p);D next_st=TT[st][cc];
      if(st==1&&next_st!=2){q[qi++]=V(*s);p=s+1;st=0;break;} // not a number, treat '-' as a verb
      if(next_st==7){ // End of token.
        D len=p-s;C t[100];strncpy(t,s,len);t[len]='\0';
        if(st==1||st==2||st==3||st==8) q[qi++]=pn(t,len);
        else if(st==4){
          D vi=FV(t);
          D ai=FA(t);
          if(vi) q[qi++]=av(vi); else if(ai) q[qi++]=aa(ai);
          else q[qi++]=ar(parse_b(t,len,62));
        }
        else if(st==6){ s++; len--; strncpy(t,s,len);t[len]='\0'; q[qi++]=as(parse_b(t,len,62));}
        else if(st==5){ s++; len--; Q z=vna(0,6,0,len); for(D i=0;i<len;i++)pid(z,i,s[i]); q[qi++]=z; if(*p)p++;}
        // TODO: S_FLT
        st=0;break;
      }
      st=next_st;
    }
  }
  q[qi]=0;return q;
}

C* sub(C* s){
  static C b[256];
  C* d=b; C* p=s;
  while(*p){
    if(p[0]=='-'&&p[1]=='>'){strcpy(d,"→");d+=3;p+=2;}
    else if(p[0]=='<'&&p[1]=='-'){strcpy(d,"←");d+=3;p+=2;}
    else if(p[0]=='<'&&p[1]=='o'){strcpy(d,"↺");d+=3;p+=2;}
    else if(p[0]=='o'&&p[1]=='>'){strcpy(d,"↻");d+=3;p+=2;}
    else if(p[0]=='<'&&p[1]=='\''){strcpy(d,"↰");d+=3;p+=2;}
    else if(p[0]=='\''&&p[1]=='>'){strcpy(d,"↱");d+=3;p+=2;}
    else if(p[0]=='\''&&p[1]=='v'){strcpy(d,"↓");d+=3;p+=2;}
    else if(p[0]=='\''&&p[1]=='^'){strcpy(d,"↑");d+=3;p+=2;}
    else if(p[0]=='/'&&p[1]=='\''){strcpy(d,"↿");d+=3;p+=2;}
    else if(p[0]=='\\'&&p[1]=='\''){strcpy(d,"⇃");d+=3;p+=2;}
    else if(p[0]=='<'&&p[1]=='p'){strcpy(d,"↫");d+=3;p+=2;}
    else if(p[0]=='p'&&p[1]=='>'){strcpy(d,"↬");d+=3;p+=2;}
    else {*d++=*p++;}
  }
  *d=0;
  return b;
}

C buffer[100];
D main(void){
#if defined(_MSC_VER)
  SetConsoleOutputCP(65001);
  AB[0]=(Q*)VirtualAlloc(0, ARENA_SZ, MEM_RESERVE, PAGE_READWRITE);if(!AB[0]){printf("VA 0 failed\n");exit(1);}AC[0]=ARENA_SZ/BUMP_UNIT_BYTES;AI[0]=1;
  AB[1]=(Q*)VirtualAlloc(0, ARENA_SZ, MEM_RESERVE, PAGE_READWRITE);if(!AB[1]){printf("VA 1 failed\n");exit(1);}AC[1]=ARENA_SZ/BUDDY_UNIT_BYTES;AI[1]=0;
#else
  AB[0]=(Q*)mmap(0, ARENA_SZ, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);if(AB[0]==MAP_FAILED){printf("mmap 0 failed\n");exit(1);}AC[0]=ARENA_SZ/BUMP_UNIT_BYTES;AI[0]=1;
  AB[1]=(Q*)mmap(0, ARENA_SZ, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);if(AB[1]==MAP_FAILED){printf("mmap 1 failed\n");exit(1);}AC[1]=ARENA_SZ/BUDDY_UNIT_BYTES;AI[1]=0;
#endif
  printf("AB[0] AC[0] AI[0] %lld %lld %lld\n",(long long)AB[0],AC[0],AI[0]);
  printf("AB[1] AC[1] AI[1] %lld %lld %lld\n",(long long)AB[1],AC[1],AI[1]);
  buddyinit(1);
  FT_addr = vca(1, 3, 3, 4096);
  FT_sz   = vca(1, 3, 3, 4096);
  FT_cap  = vca(1, 3, 3, 4096);
  FT_h    = vca(1, 3, 3, 4096);
  FT_fn   = vca(1, 0, 3, 4096);
  G=dni(0,3,0,1); // global dictionary in buddy allocator
  Q ft = dni(0,3,0,1); // file table dict in buddy allocator
  dkv(ft, ar(parse_b("addr",4,62)), FT_addr);
  dkv(ft, ar(parse_b("sz",2,62)),   FT_sz);
  dkv(ft, ar(parse_b("cap",3,62)),  FT_cap);
  dkv(ft, ar(parse_b("h",1,62)),    FT_h);
  dkv(ft, ar(parse_b("fn",2,62)),   FT_fn);
  dkv(G, ar(parse_b("FT",2,62)),    ft);
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
      AI[0]=1;SC[0]=dni(0,3,0,0); SP=0; 
     } // reset THI only if evaluation takes us back to the global scope. 
    C* s=sub(buffer);
    printf("\033[A\033[2K %s\n",s);
    Q* tokens = lx(s);
    Q r=E(&tokens,'\0');
    pr(r);printf("\n");
  }
  return 0;
}
