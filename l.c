// Build notes (canonical commands): see BUILDING.md
// windows: cl l.c /GL /O1 /Gy /MD /DNDEBUG /link /LTCG /OPT:REF /OPT:ICF
// linux_asan: cc -fsanitize=address l.c -o l_lin_asan
// linux: cc -Os l.c -o l_lin
// -----------------------------------------------------------------------------
// Compiler selection
// -----------------------------------------------------------------------------
#if defined(_MSC_VER)
  #define L_CC_MSVC 1
  #define _CRT_SECURE_NO_WARNINGS
#else
  #define L_CC_MSVC 0
#endif
#if defined(__clang__)
  #define L_CC_CLANG 1
#else
  #define L_CC_CLANG 0
#endif
#if defined(__GNUC__) && !defined(__clang__)
  #define L_CC_GCC 1
#else
  #define L_CC_GCC 0
#endif

// -----------------------------------------------------------------------------
// Platform selection (keep preprocessor conditionals out of the core runtime).
// -----------------------------------------------------------------------------
#if defined(__EMSCRIPTEN__) || defined(__wasm__) || defined(__wasm32__) || defined(__wasm64__)
  #define L_OS_WASM 1
#else
  #define L_OS_WASM 0
#endif

#if defined(_WIN32) && !L_OS_WASM
  #define L_OS_WIN32 1
#else
  #define L_OS_WIN32 0
#endif

#if !L_OS_WIN32 && !L_OS_WASM
  #define L_OS_POSIX 1
#else
  #define L_OS_POSIX 0
#endif

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <math.h>
#include <time.h>
#if L_OS_WIN32
  #include <windows.h>
  #if L_CC_MSVC
    #include <intrin.h>
  #endif
#elif L_OS_POSIX
  #include <sys/mman.h>
  #include <fcntl.h>
  #include <unistd.h>
  #include <sys/stat.h>
#elif L_OS_WASM
  // WASM platform layer TBD (intentionally no OS headers here).
#else
  #error "Unsupported platform (no headers selected)"
#endif

// ---------------------------------------------------------------------------
// l.c memory rule: C standard library heap allocation APIs are illegal here.
// Do not call malloc/free/realloc/calloc. Use arena allocators (tsna/vna/etc.)
// for Lang objects, and os_heap_alloc/os_heap_free for temporary C buffers.
// ---------------------------------------------------------------------------
struct LANG_MALLOC_IS_ILLEGAL;
struct LANG_CALLOC_IS_ILLEGAL;
struct LANG_REALLOC_IS_ILLEGAL;
struct LANG_FREE_IS_ILLEGAL;
#define malloc(...)  ((void*)sizeof(struct LANG_MALLOC_IS_ILLEGAL))
#define calloc(...)  ((void*)sizeof(struct LANG_CALLOC_IS_ILLEGAL))
#define realloc(...) ((void*)sizeof(struct LANG_REALLOC_IS_ILLEGAL))
#define free(...)    do{ (void)sizeof(struct LANG_FREE_IS_ILLEGAL); }while(0)

typedef unsigned long long Q;typedef unsigned int D;typedef unsigned short W;typedef unsigned char B;typedef char C;
typedef long long J; typedef int I; typedef short H;
typedef Q(*VF)(B,Q,Q,Q);                                                        // function pointer for verb/adverb (arena;verb;alpha;omega)

// -----------------------------------------------------------------------------
// Platform API (implemented once per platform in the platform layer section).
// -----------------------------------------------------------------------------
static void platform_arena_reserve_init(void);
static void platform_commit_range(void* p, Q bytes);
static void* platform_vm_alloc(Q bytes);
static void platform_vm_free(void* base, Q bytes);
static void platform_init_stdout_utf8_if_console(void);
static B platform_stdin_is_console(void);
static void platform_write_stderr_bytes(const char* s, size_t n);
static Q platform_now_ns_u64(void);

// -----------------------------------------------------------------------------
// Compiler helpers (hide compiler/arch intrinsics behind a tiny API).
// -----------------------------------------------------------------------------
static inline D compiler_bsr64(Q x){
#if L_CC_MSVC
  unsigned long i = 0;
  #if defined(_M_X64) || defined(_M_ARM64)
    _BitScanReverse64(&i, (unsigned long long)x);
    return (D)i;
  #else
    unsigned long hi = (unsigned long)(x >> 32);
    unsigned long lo = (unsigned long)(x & 0xFFFFFFFFULL);
    if(hi){
      _BitScanReverse(&i, hi);
      return (D)(i + 32);
    }
    _BitScanReverse(&i, lo);
    return (D)i;
  #endif
#else
  return (D)(63 - __builtin_clzll((unsigned long long)x));
#endif
}

static inline D compiler_bsf64(Q x){
#if L_CC_MSVC
  unsigned long i = 0;
  #if defined(_M_X64) || defined(_M_ARM64)
    _BitScanForward64(&i, (unsigned long long)x);
    return (D)i;
  #else
    unsigned long hi = (unsigned long)(x >> 32);
    unsigned long lo = (unsigned long)(x & 0xFFFFFFFFULL);
    if(lo){
      _BitScanForward(&i, lo);
      return (D)i;
    }
    _BitScanForward(&i, hi);
    return (D)(i + 32);
  #endif
#else
  return (D)__builtin_ctzll((unsigned long long)x);
#endif
}

static inline int compiler_snprintf17g(C* buf, size_t buf_cap, double x){
#if L_CC_MSVC
  return _snprintf(buf, buf_cap, "%.17g", x);
#else
  return snprintf(buf, buf_cap, "%.17g", x);
#endif
}

#define T_INT   3
#define T_CHAR  6
#define T_SYM   7
#define T_FLT   8
#define T_TAG   10
#define T_LAMBDA 11
// Grammatical immediates (low 4 bits == 2; t() returns low 6 bits):
#define T_VERB  2
#define T_ADV   18
#define T_CTL   34
#define T_ERR   50

// Symbol payload tagging (within the 60-bit immediate payload or 64-bit vector element):
// - LSB==1 => interned symbol id (payload>>1 is the id/index into symtab)
// - LSB==0 => "small" base62 symbol payload (payload>>1 is the base62 value; printing may be lossy for leading zeros)
#define SYM_PAYLOAD_IS_INTERN(p) ((p) & 1ULL)
#define SYM_PAYLOAD_VAL(p)       ((p) >> 1)
#define SYM_PAYLOAD_INTERN(id)   ((((Q)(id)) << 1) | 1ULL)
#define SYM_PAYLOAD_SMALL(v)     (((Q)(v)) << 1)

#if L_CC_MSVC && (defined(_M_IX86) || defined(_M_X64))
  #include <xmmintrin.h>
  #define HAVE_MXCSR 1
#elif (defined(__i386__) || defined(__x86_64__)) && defined(__SSE__)
  #include <xmmintrin.h>
  #define HAVE_MXCSR 1
#else
  #define HAVE_MXCSR 0
#endif

static inline Q f64_bits(double x){ Q b=0; memcpy(&b, &x, sizeof(b)); return b; }
static inline double f64_from_bits(Q b){ double x=0; memcpy(&x, &b, sizeof(x)); return x; }
static inline Q af_bits(Q ar, Q bits); // forward decl

// Signed 60-bit immediate integers (type tag == 3). Other immediate tags use unsigned payloads.
static inline Q di_int(Q q){
  Q x = q >> 4; // 60-bit payload
  if(x & (1ULL<<59)) x |= 0xF000000000000000ULL; // sign extend into top 4 bits
  return x;
}

#define BUMP_UNIT_BYTES   16
#define BUDDY_UNIT_BYTES  4096

#define BUMP_UNIT_QS   (BUMP_UNIT_BYTES / sizeof(Q))
#define BUDDY_UNIT_QS  (BUDDY_UNIT_BYTES / sizeof(Q))

#define ARENA_SZ       (1ULL<<32)
Q* AB[4];Q AI[4];Q AC[4];
Q AM[4];
Q AQ[4]={BUMP_UNIT_QS,BUDDY_UNIT_QS,BUMP_UNIT_QS,0};
Q BF[32];

typedef struct {
  B dbg_startup;
  B dump_tokens;
  B no_inplace;
} L_Opts;
static L_Opts L_opts = {0,0,0};

B ha(Q q){return (q>>4)&3;}
Q FT_addr=0, FT_sz=0, FT_cap=0, FT_h=0, FT_fn=0;
Q hp(B a,Q q){return q>>(0==a?6:1==a?11:6);}
Q pi(Q q,D i);
static inline Q af(Q ar, double x);
Q* ptr(Q q){
  B a=ha(q);
  if(a==2){
    Q off = (q>>6) & 0x3FFFFFFFFF;
    D fid = q>>44;
    return ((Q*)pi(FT_addr,fid)) + (off*AQ[a]);
  }
  return AB[a]+(hp(a,q)*AQ[a]);
}

B ip(Q q){return q&&!(15&q);}                                                 // Is this Q a pointer? nonzero in low 4 bits means atom
B itp(Q q){return ip(q) && ha(q)==0;}                                         // Is this Q a pointer to the bump allocated region?
B*p(Q q){return (B*)(ptr(q)+6);}                                              // pointers point at header after decoding and need to be adjusted to point at the data
Q di(Q q){return q>>4;}                                                       // shift out the flags. decodes small integers
Q dv(Q q){return q>>6;}                                                       // verbs are grammatical type, subtype 0. payload in high 59 bits
Q da(Q q){return q>>6;}
Q dc(Q q){return q>>6;}                                                       // controls are grammatical type, subtype 2. payload in high 59 bits
Q de(Q q){return q>>6;}                                                       // errors are grammatical type, subtype 3. payload in high 59 bits

Q tsna(Q ar, B t, B s, B z, D n, D c);                                         // forward decl (needed by an)

Q ar(Q r){return (r<<4)|1;}                                                   // create an atom of type 1 (reference)
Q av(Q v){return (v<<6)|2;}                                                   // create a verb atom (grammatical type 2, subtype 0)
Q aa(Q a){return (a<<6)|(1<<4)|2;}                                            // create an adverb atom (grammatical type 2, subtype 1)
Q ac(Q c){return (c<<6)|(2<<4)|2;}                                            // create a control atom (grammatical type 2, subtype 2)
Q ae(Q e){return (e<<6)|(3<<4)|2;}                                            // create an error atom (grammatical type 2, subtype 3)
Q an(J n){                                                                    // create an int atom (signed 60-bit immediate when possible; otherwise heap int64 atom)
  if(n >= -(1LL<<59) && n < (1LL<<59)){
    Q payload = ((Q)n) & ((1ULL<<60)-1ULL);
    return (payload<<4) | T_INT;
  }
  Q q = tsna(0, T_INT, 0, 3, 1, 1);
  Q bits = (Q)n;
  memcpy(p(q), &bits, sizeof(bits));
  return q;
}
Q ap(Q v){return (v<<4)|4;}                                                   // create an atom of type 4 (partial eval) - HEAP ONLY
                                                                              // type 5 is hash
Q ach(C c){return ((Q)(B)c<<4)|6;}                                            // create an atom of type 6 (char)
Q as(Q s){return (s<<4)|7;}                                                   // create an atom of type 7 (symbol)
Q atg(Q x){return (x<<4)|T_TAG;}                                              // create an atom of type 10 (tag64)
Q aA(B a, D f){return (((Q)f<<8)|a)<<4|9;}                                    // create an atom of type 9 (arena/file)
Q et(Q q,B t){return 0==t?q:1==t?ar(q):2==t?av(q):3==t?an(q):4==t?ap(q):6==t?ach(q):7==t?as(q):8==t?af_bits(0,q):T_TAG==t?atg(q):T_ERR==t?ae(q):ac(q);} // encode data of an atom based on the type. TODO: handle 9

#define AR_ID(x) ((x)&0xFF)
#define AR_FID(x) ((x)>>8)
#define MK_AR(a, f) (((Q)(f)<<8)|(a))

B ii(Q q){return !ip(q);}                                                     // is immediate  from pointer
B t(Q q){                                                                     // type      from pointer or header
  if(ip(q))return ptr(q)[0];
  B tag=q&15;
  if(tag==2)return q&63;
  return tag;
}
static inline B is_err(Q q){ return q && t(q)==T_ERR; }
B sh(Q q){return ii(q)?0:ptr(q)[1];}                                           // shape    from header
B ls(Q q){return ii(q)?3:ptr(q)[2];}                                           // logeltsz from header EDGE CASE: should type 0 automatically return 3 here????
B sz(Q q){return 1<<ls(q);}                                                    // bytesz   from logeltsz
D rc(Q q){return !q?0:ii(q)?1:ptr(q)[3];}                                      // refcnt   from header
D n(Q a){B s=sh(a);return 0==s?1:ptr(a)[4];}                                   // length   from header
D cp(Q a){B s=sh(a);return 0==s?1:ptr(a)[5];}                                  // capacity from header

B is(Q q){return 0==sh(q);}
B iv(Q q){return 1==sh(q);}
B iD(Q q){return 2==sh(q);}

void ir(Q q);void dr(Q q); 

static inline B ends_with_dot_l(const char* s);
static inline B qstr_to_c(Q w, C* out, D out_cap);
static Q eval_code_file(const char* fn);
static Q eval_code_tape(const C* src, D len);

Q qbz(Q bz){return ((bz+15)/16)*2;}                                             // forward declare refcount helpers
Q hz(void){return sizeof(Q)*6;}                                                 // header size
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
  return compiler_bsr64(x-1) + 1;
}
static inline B floor_ord(Q x){
  // x >= 1
  return (B)compiler_bsr64(x);
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
  platform_commit_range(p, bytes);
}

static inline Q bumpalloc_impl(B t, B s, B z, D n, D c, Q ar, B zero_payload){
  (void)ar;
  Q units = bump_units(z, c);
  if(AI[0] + units > AC[0]) exit(1);
  if(AI[0] + units > AM[0]){
    Q req = AI[0] + units;
    commit_range(AB[0] + AM[0] * BUMP_UNIT_QS, (req - AM[0]) * BUMP_UNIT_BYTES);
    AM[0] = req;
  }
  Q off = AI[0];
  Q* o = AB[0] + off * BUMP_UNIT_QS;
  AI[0] += units;
  ah(o, t, s, z, 0, n, c);
  if(zero_payload) memset(o + 6, 0, pz(z, c));
  return (off << 6) | (0 << 4);
}

Q bumpalloc(B t,B s,B z,D n,D c,Q ar){
  return bumpalloc_impl(t, s, z, n, c, ar, 1);
}

Q bumpalloc_u(B t,B s,B z,D n,D c,Q ar){
  // Uninitialized payload allocation (header set, payload not zeroed).
  // Only use when the caller will fully initialize all n elements before any read.
  return bumpalloc_impl(t, s, z, n, c, ar, 0);
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
    commit_range(AB[a] + off * BUDDY_UNIT_QS, sizeof(Q));
    *(Q*)(AB[a] + off * BUDDY_UNIT_QS) = BF[ord];
    BF[ord] = off;

    off += u;
    rem -= u;
  }
}

static inline Q buddyalloc_impl(B t, B s, B z, D n, D c, Q ar, B zero_payload){
  (void)ar;
  Q units = buddy_units(z, c);
  B ord   = buddy_order_from_units(units);

  B i = ord;
  while(i < 32 && BF[i] == ~0ULL) i++;
  if(i == 32) exit(1);

  Q off = BF[i];
  BF[i] = *(Q*)(AB[1] + off * BUDDY_UNIT_QS);

  while(i > ord){
    i--;
    Q u = buddy_units_from_order(i);
    Q b = off + u;

    commit_range(AB[1] + b * BUDDY_UNIT_QS, sizeof(Q));
    *(Q*)(AB[1] + b * BUDDY_UNIT_QS) = BF[i];
    BF[i] = b;
  }

  Q* o = AB[1] + off * BUDDY_UNIT_QS;
  commit_range(o, az(z, c));
  ah(o, t, s, z, 0, n, c);
  if(zero_payload) memset(o + 6, 0, pz(z, c));

  return (off << 11) | (ord << 6) | (1 << 4);
}

Q buddyalloc(B t,B s,B z,D n,D c,Q ar){
  return buddyalloc_impl(t, s, z, n, c, ar, 1);
}

Q buddyalloc_u(B t,B s,B z,D n,D c,Q ar){
  // Uninitialized payload allocation (header set, payload not zeroed).
  // Only use when the caller will fully initialize all n elements before any read.
  return buddyalloc_impl(t, s, z, n, c, ar, 0);
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
        if (!new_addr) { return ae(2); }
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

    return ((Q)fid << 44) | (off_units << 6) | (2 << 4) | 0;
}

Q tsna(Q ar, B t, B s, B z, D n, D c){
  B a = AR_ID(ar);
  if(a==2) return filebumpalloc(t,s,z,n,c,ar);
  if(a==1) return buddyalloc(t,s,z,n,c,ar);
  return bumpalloc(t,s,z,n,c,ar); // TODO: return fatal error for unknown arena instead of temp arena fallback
}

// Uninitialized allocation variant: does not zero payload for arena 0 (temp bump) or arena 1 (buddy).
// For file-backed arena (2), always use the initialized allocator to avoid persisting garbage bytes.
Q tsna_u(Q ar, B t, B s, B z, D n, D c){
  B a = AR_ID(ar);
  if(a==2) return filebumpalloc(t,s,z,n,c,ar);
  if(a==1) return buddyalloc_u(t,s,z,n,c,ar);
  return bumpalloc_u(t,s,z,n,c,ar);
}
Q vna(Q ar, B t, B z, D n){ return tsna(ar, t, 1, z, n, cn(t,1,n)); }
Q lna(Q ar, D n){ return vna(ar, 0, 3, n); }
Q vca(Q ar, B t, B z, D c){ return tsna(ar, t, 1, z, 0, c); }
Q lca(Q ar, D c){ return vca(ar, 0, 3, c); }
Q ln(D n){return vna(0,0,3,n);}

void pr(Q q);
void zid(Q q,D i,Q d);

static inline D pow2_ceil_u32(D x){
  if(x<=1) return 1;
  x--;
  x |= x>>1;
  x |= x>>2;
  x |= x>>4;
  x |= x>>8;
  x |= x>>16;
  return x+1;
}

static inline D dict_hash_cap_for_keys(D key_count){
  // Keep load factor <= 0.75 and minimum size 64.
  // need ~= ceil((key_count+1) / 0.75) => (4*(key_count+1))/3
  Q want = (Q)key_count + 1ULL;
  Q need = (4ULL*want + 2ULL) / 3ULL; // ceil(4*want/3)
  if(need < 64ULL) need = 64ULL;
  if(need > 0x7FFFFFFFULL) need = 0x7FFFFFFFULL; // keep in signed 32-bit range
  D cap = pow2_ceil_u32((D)need);
  if(cap < 64) cap = 64;
  return cap;
}
Q dni(B t,B z,D n,Q ar){                                                              // alloc a dictionary of a certain type and element size with hash table capacity n. 
  D cap = dict_hash_cap_for_keys(n);
  Q h=vca(ar, 5, 3, cap);                                                            // hash table (packed: fp32|idx32)
  Q k=lca(ar, cap);                                                                  // key list
  Q v=vca(ar, t, z, cap);                                                            // value list
  Q d=tsna(ar, 0, 2, 3, 3, 3);
  zid(d,0,h);zid(d,1,k);zid(d,2,v);
  return d;
}
Q dn(B t,B z,D n,Q ar){return dni(t,z,n,ar);}
Q dnu(B t,B z,D n,B a){return tsna(a,0,2,3,3,3);}
// varwidth getters
Q Bi(B* b,B z,D i){                                                                // no sign-extension; floats may live in here too
  switch(z){
    case 1: return (Q)((B*)b)[i];
    case 2: return (Q)((W*)b)[i];
    case 4: return (Q)((D*)b)[i];
    case 8: return ((Q*)b)[i];
    default: { Q r=0; memcpy(&r, b+z*i, z); return r; }
  }
}
Q pi(Q q,D i){return Bi(p(q),sz(q),i);}              
Q ri(Q q,D i){
  if(1==sh(q)){return pi(q,i);}
  return ae(1);                                                                       // shape error
}
Q vi(D n,D i){if(i>=n){return ae(2);};return an(i);}
Q qi(Q q,D i){B s=sh(q),tq=t(q);
  if(1==s){Q qi=vi(n(q),i);return is_err(qi)?qi:et(pi(q,di(qi)),tq);};
  return ae(1);
}              // get at index, return tagged Q
Q ra(Q q){                                                                      // read atom
  if(sh(q)) return ae(1);
  switch(t(q)){
    case 1:  return ip(q) ? pi(q,0) : di(q);
    case 2:  return ip(q) ? pi(q,0) : (q>>6);                                    // verbs are atoms; payload is the verb id
    case 3:  return ip(q) ? pi(q,0) : di_int(q);
    case 6:  return ip(q) ? pi(q,0) : di(q);
    case 7:  return ip(q) ? pi(q,0) : di(q);
    case 8:  return ip(q) ? pi(q,0) : di(q);                                     // float payload bits (heap atoms only today)
    case T_TAG: return ip(q) ? pi(q,0) : di(q);
    case T_ADV: return ip(q) ? pi(q,0) : (q>>6);
    case T_CTL: return ip(q) ? pi(q,0) : (q>>6);
    case T_ERR: return ip(q) ? pi(q,0) : (q>>6);
    default: return ae(5);                                                      // not yet implemented
  }
}
static inline D grow_cap_default(D old_cap, D need){
  D cap = old_cap ? old_cap : 1;
  while(cap < need){
    D next = cap + (cap>>1) + (cap>>3);
    if(next <= cap){ cap = need; break; }
    cap = next;
  }
  return cap;
}

Q grow(Q q, D need_n){
  if(!ip(q) || sh(q)!=1) return ae(1);

  Q* h = ptr(q);
  B tq = (B)h[0], sq = (B)h[1], zq = (B)h[2];
  D old_n = (D)h[4], old_c = (D)h[5];

  if(tq==5){
    // Hash tables depend on the probe mask (capacity). Growing requires rehashing with the keys.
    // Do not attempt to resize here; dict-level code should rebuild ht+rehash.
    return ae(6);
  }

  D new_c = grow_cap_default(old_c, need_n);
  Q ar = (ha(q)==2) ? MK_AR(2, (D)(q>>44)) : (Q)ha(q);
  Q nq = tsna(ar, tq, sq, zq, need_n, new_c);

  // Copy old payload; new region is already zeroed by allocators.
  memcpy(p(nq), p(q), (1ULL<<zq) * (Q)old_n);

  // Classic COW: if this is a pointer list, bump child refcounts so old and new can be independently freed.
  if(tq==0){
    for(D i=0;i<old_n;i++) ir(pi(nq, i));
  }

  return nq;
}

Q xn(Q q, D add){
  if(!ip(q) || sh(q)!=1) return ae(1);
  D old_n = n(q);
  D need_n = old_n + add;
  D c = cp(q);
  if(need_n <= c){ ptr(q)[4] = need_n; return q; }
  return grow(q, need_n);
}
// varwidth setters
void Bid(B* b,B z,D i,Q d){
  switch(z){
    case 1: ((B*)b)[i] = (B)d; return;
    case 2: ((W*)b)[i] = (W)d; return;
    case 4: ((D*)b)[i] = (D)d; return;
    case 8: ((Q*)b)[i] = (Q)d; return;
    default: memcpy(b+z*i, &d, z); return;
  }
}
void pid(Q q,D i,Q d){if(n(q)<=i){exit(1);return;};Bid(p(q),sz(q),i,d);}          // throw length error when i outside of n
void zid(Q q,D i,Q d){Q o=pi(q,i);ir(d);pid(q,i,d);dr(o);}
void qid(Q q,D i,Q d){if(!t(q)){zid(q,i,d);}else{pid(q,i,d);}}

static inline Q obj_ar(Q q){
  if(!ip(q)) return 0;
  B a = ha(q);
  if(a==2) return MK_AR(2, (D)(q>>44));
  return (Q)a;
}

// dict get/set
static inline D lg2(D c){
  return compiler_bsf64((Q)c);
}
static B match_struct(Q a, Q w, D depth);

static inline Q mix64(Q x){
  x += 0x9E3779B97F4A7C15ULL;
  x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
  x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
  return x ^ (x >> 31);
}
static inline Q hash_bytes64(const void* data, Q bytes){
  const B* p0 = (const B*)data;
  Q h = 0xD6E8FEB86659FD93ULL ^ mix64(bytes);
  for(Q i=0;i<bytes;i+=8){
    Q chunk = 0;
    Q rem = bytes - i;
    if(rem > 8) rem = 8;
    memcpy(&chunk, p0 + i, (size_t)rem);
    h = mix64(h ^ mix64(chunk + i));
  }
  return h;
}
static inline Q atom_payload_for_hash(Q q){
  if(ip(q)) return pi(q, 0);
  B tq = t(q);
  if(tq==2 || tq==18 || tq==34) return q>>6;
  if(tq==3) return di_int(q);
  return di(q);
}
static Q qhash_struct(Q q, Q* stack, D depth){
  if(!q) return 0;
  if(depth > 1024) return 0x243F6A8885A308D3ULL;

  if(ip(q)){
    for(D i=0;i<depth && i<64;i++) if(stack[i]==q) return mix64(q);
    if(depth < 64) stack[depth] = q;
  }

  B tq=t(q), sq=sh(q);
  Q h = mix64(((Q)tq<<56) ^ ((Q)sq<<48) ^ ((Q)ls(q)<<40) ^ (Q)n(q));

  if(sq==0){
    return mix64(h ^ mix64(atom_payload_for_hash(q)));
  }

  // Structural dictionary: ignore internal hash table.
  if(sq==2 && tq==0){
    Q kq = pi(q, 1);
    Q vq = pi(q, 2);
    h = mix64(h ^ qhash_struct(kq, stack, depth+1));
    h = mix64(h ^ qhash_struct(vq, stack, depth+1));
    return h;
  }

  // Pointer lists and partial eval chains are structural.
  if(tq==0 || tq==4){
    D nq = n(q);
    for(D i=0;i<nq;i++){
      h = mix64(h ^ qhash_struct(pi(q,i), stack, depth+1));
    }
    return h;
  }

  // Homogeneous value vectors.
  return mix64(h ^ hash_bytes64(p(q), (Q)n(q) * (Q)sz(q)));
}
static inline Q qhash64(Q q){
  Q stack[64];
  return qhash_struct(q, stack, 0);
}
static inline D bucket_from_hash(Q h, D lc){
  return (D)(h >> (64 - lc));
}

static Q dict_rehash(Q d, D new_cap);
static inline Q dict_ensure_ht(Q d, D want_keys){
  if(!ip(d) || 2!=sh(d)) return ae(1);
  Q htq = pi(d,0), kq = pi(d,1);
  D key_n = n(kq);
  if(want_keys < key_n) want_keys = key_n;

  // Rebuild if counts drift (e.g., after load/clone) or if we'd exceed the load factor.
  D used = (D)n(htq);
  D cap  = (D)cp(htq);
  D need = dict_hash_cap_for_keys(want_keys);

  if(used != key_n || cap < need) return dict_rehash(d, need);
  return d;
}

static inline D fp32_from_hash(Q h){
  return (D)(h >> 32);
}
static inline D idx32_from_entry(Q entry){
  return (D)(entry & 0xFFFFFFFFULL);
}
static inline D fp32_from_entry(Q entry){
  return (D)(entry >> 32);
}

static inline D fk_h(Q* ht, Q k, Q h, D c, Q keys){
  D mask = c - 1;
  D fp = fp32_from_hash(h);
  D i = bucket_from_hash(h, lg2(c)) & mask;
  for(D j=0; j<c; ++j){
    Q e = ht[i];
    if(!e) return i;                                                            // empty slot
    if(fp32_from_entry(e) == fp){
      D idx1 = idx32_from_entry(e);
      if(idx1 && match_struct(pi(keys, idx1-1), k, 0)) return i;                 // key match
    }
    i = (i + 1) & mask;
  }
  return c;                                                                     // Sentinel for "table is full and key not found"
}
Q fk(Q* ht,Q k,D c,Q keys){                                                     // find slot for key in ht; uses structural hashing/equality
  return fk_h(ht, k, qhash64(k), c, keys);
}
Q SC[1024]; D SP=0;Q G;
// Open list builders (for both (...) list literals and postfix [...] indexing lists).
Q NL[1024]; D LP=0;
// For each open list builder depth LP: expected closing token (')' or ']'), and kind:
// - 0: list literal / grouping
// - 1: postfix index apply (base[...])
// - 2: postfix index capture (base[...]:v lvalue parsing)
C LC[1024];
B LK[1024];
// For LK==1 (postfix index), the base value being indexed (kept alive across unbalanced input).
Q LBASE[1024];
// For LK==0 (list literal), track whether any list separators (';' or '\n') occurred while building.
B LSEP[1024];

Q dki(Q d, Q k){                                                                // inner "dictionary key" lookup for a single dictionary
  if(!ip(d)||2!=sh(d)) return 0;                                                // Not a dictionary
  Q ok = dict_ensure_ht(d, n(pi(d,1)));
  if(is_err(ok)) return ok;
  Q htq=pi(d,0),kq=pi(d,1),vq=pi(d,2);
  Q* ht=(Q*)p(htq); D c=cp(htq);
  Q h = qhash64(k);
  D i=fk_h(ht,k,h,c,kq);
  if(i==c){return 0;}                                                           // Not found
  Q e=ht[i];
  D idx1 = idx32_from_entry(e);
  return idx1?qi(vq,idx1-1):0;                                                   // Found, or empty slot
}

Q dk(Q d, Q k){                                                                 // outer "dictionary key" lookup with scope traversal
  // References are grammatical name tokens. Environments store bindings under symbol keys,
  // so resolve lookup keys by converting references to symbols.
  if(1==t(k)) k = as(ra(k));
  Q r=dki(d,k);if(r){return r;}
  for (I j=SP; j>=0; j--) {                                                     // Search from the current scope (SP) down to scope 0
    Q r = dki(SC[j], k);
    if(r){return r;}
  }
  r=dki(G, k);                                                                  // If not found in scopes, try the global dictionary G
  if(r){return r;}
  return ac(4);                                                                 // Return result from G or "not found"
}

static Q clone0_for_embed(Q q, Q dest_ar, Q* stack, D depth);

static inline B is_nf(Q q){ return 34==t(q) && dc(q)==4; }
static inline B is_fatal_clone_control(Q q){
  if(is_err(q)) return 1;
  if(34!=t(q)) return 0;
  Q code = dc(q);
  // Controls are grammar tokens (e.g. '[', ';', '\n') plus a few runtime sentinels like nf.
  if(code==4) return 0;                 // nf is a normal value
  if(code=='\n' || code==';') return 0; // statement separators are safe to embed (e.g. in lambda bodies)
  if(code>=32 && code<=126) return 0;   // printable ASCII controls are grammar tokens
  return 1;                             // non-printable / out-of-band controls => fatal
}

static inline Q clone_lambda_for_embed(Q q, Q dest_ar, Q* stack, D depth);

static inline Q clone0_for_embed0(Q q, Q dest_ar, Q* stack, D depth){
  if(!ip(q)) return q;
  B tq = t(q);
  if(tq!=0 && tq!=T_LAMBDA) return q;
  if(depth >= 64) return ae(99);
  for(D i=0;i<depth;i++) if(stack[i]==q) return ae(2);                           // cycle detected
  stack[depth]=q;
  if(tq==T_LAMBDA) return clone_lambda_for_embed(q, dest_ar, stack, depth+1);
  return clone0_for_embed(q, dest_ar, stack, depth+1);
}

static Q clone0_for_embed(Q q, Q dest_ar, Q* stack, D depth){
  if(!ip(q) || t(q)!=0) return q;

  B s = sh(q);
  if(s==2){
    Q kq=pi(q,1),vq=pi(q,2);

    Q k2 = tsna(dest_ar, 0, 1, ls(kq), n(kq), cp(kq));
    for(D i=0;i<n(kq);i++){
      Q ki = pi(kq, i);
      Q kc = clone0_for_embed0(ki, dest_ar, stack, depth);
      if(is_fatal_clone_control(kc)) return kc;
      zid(k2, i, kc);
    }

    Q v2 = tsna(dest_ar, t(vq), 1, ls(vq), n(vq), cp(vq));
    if(0==t(vq)){
      for(D i=0;i<n(vq);i++){
        Q vi = pi(vq, i);
        Q vc = clone0_for_embed0(vi, dest_ar, stack, depth);
        if(is_fatal_clone_control(vc)) return vc;
        zid(v2, i, vc);
      }
    }else{
      memcpy(p(v2), p(vq), (size_t)sz(vq) * (size_t)n(vq));
    }

    Q d2 = tsna(dest_ar, 0, 2, 3, 3, 3);
    zid(d2, 1, k2);
    zid(d2, 2, v2);
    Q r = dict_rehash(d2, dict_hash_cap_for_keys(n(k2)));
    if(is_err(r)) return r;
    return d2;
  }

  if(s==1 || s==0){
    Q* h = ptr(q);
    B z = (B)h[2];
    D nq = (D)h[4], cq = (D)h[5];
    Q r = tsna(dest_ar, 0, s, z, nq, cq);
    for(D i=0;i<nq;i++){
      Q ei = pi(q, i);
      Q ec = clone0_for_embed0(ei, dest_ar, stack, depth);
      if(is_fatal_clone_control(ec)) return ec;
      zid(r, i, ec);
    }
    return r;
  }

  return ae(1);                                                                   // unsupported shape
}

static inline Q clone_lambda_for_embed(Q q, Q dest_ar, Q* stack, D depth){
  if(!ip(q) || t(q)!=T_LAMBDA || sh(q)!=1 || n(q)!=2) return ae(1);
  Q params = pi(q, 0);
  Q body = pi(q, 1);

  Q params2 = clone0_for_embed0(params, dest_ar, stack, depth);
  if(is_fatal_clone_control(params2)) return params2;
  Q body2 = clone0_for_embed0(body, dest_ar, stack, depth);
  if(is_fatal_clone_control(body2)) return body2;

  Q r = tsna(dest_ar, T_LAMBDA, 1, 3, 2, 2);
  zid(r, 0, params2);
  zid(r, 1, body2);
  return r;
}

Q dkv(Q d,Q k,Q v){
  Q htq=pi(d,0),kq=pi(d,1),vq=pi(d,2);
  Q ok = dict_ensure_ht(d, n(kq) + 1);
  if(is_err(ok)) return ok;
  htq=pi(d,0);kq=pi(d,1);vq=pi(d,2);
  Q* ht=(Q*)p(htq);
  D c=cp(htq);
  Q h = qhash64(k);
  D i=fk_h(ht,k,h,c,kq);
  if(i==c){return ae(6);}
  Q e=ht[i];
  if(e){                                                                      // overwrite existing value
    D idx=idx32_from_entry(e)-1;
    Q old=pi(vq, idx);
    ir(v);
    qid(vq, idx, v);
    dr(old);
    return v;
  }
  D idx = n(kq);                                                              // insert new key/value
  Q kq2 = xn(kq,1); if(is_err(kq2)) return kq2; if(kq2!=kq){ zid(d,1,kq2); kq=kq2; }
  zid(kq, idx, k);                                                            // append key
  Q vq2 = xn(vq,1); if(is_err(vq2)) return vq2; if(vq2!=vq){ zid(d,2,vq2); vq=vq2; }
  qid(vq, idx, v);                                                            // append value
  ht[i] = ((Q)fp32_from_hash(h) << 32) | (Q)(idx + 1);                        // write hash entry (fp32|idx32+1)
  // Track number of active hash entries in the ht header (capacity remains fixed).
  ptr(htq)[4] = (Q)(n(htq) + 1);
  return v;
}

static Q dict_rehash(Q d, D new_cap){
  if(!ip(d) || 2!=sh(d)) return ae(1);
  Q kq = pi(d,1);
  D key_n = n(kq);
  D need = dict_hash_cap_for_keys(key_n);
  if(new_cap < need) new_cap = need;
  new_cap = pow2_ceil_u32(new_cap);
  if(new_cap < 64) new_cap = 64;

  Q ht_new = vca(obj_ar(d), 5, 3, new_cap);
  Q* ht = (Q*)p(ht_new);

  for(D idx=0; idx<key_n; ++idx){
    Q key = pi(kq, idx);
    Q h = qhash64(key);
    D fp = fp32_from_hash(h);
    D slot = (D)fk_h(ht, key, h, new_cap, kq);
    if(slot == new_cap) return ae(6);
    ht[slot] = ((Q)fp << 32) | (Q)(idx + 1);
  }
  ptr(ht_new)[4] = (Q)key_n;
  zid(d, 0, ht_new);
  return d;
}
Q parse_b(C* s, D len, D base);
static inline Q sym_intern_bytes(const C* bytes, D len);
static void ft_refresh_dict(void){
  if(!G) return;
  Q ft = dk(G, sym_intern_bytes("FT", 2));
  if(is_err(ft) || is_nf(ft)) return;
  dkv(ft, sym_intern_bytes("addr", 4), FT_addr);
  dkv(ft, sym_intern_bytes("sz",   2), FT_sz);
  dkv(ft, sym_intern_bytes("cap",  3), FT_cap);
  dkv(ft, sym_intern_bytes("h",    1), FT_h);
  dkv(ft, sym_intern_bytes("fn",   2), FT_fn);
}
void ir(Q q){ if(ip(q)){ptr(q)[3]++;}return;}
void dr(Q q){ 
  if(!q || ii(q)){return;}                                                    // if null or atom just return
  if(0< --ptr(q)[3]){return;}                                                 // if there is a nonzero refcount return
  if(!t(q)){for(D i=0;i<n(q);i++){dr(qi(q,i));}}                              // this object has refcount==0. if type 0, recurse on children
  if(T_LAMBDA==t(q)){
    // Lambda is a small pointer container: (params_symvec; body_token_list)
    dr(pi(q, 0));
    dr(pi(q, 1));
  }
  if(1==ha(q))buddyfree(q);                                                   // then free this q
  return;                                                                     // should I consider returning a control sentinel here (type)
}

Q q2a(Q dest_ar, Q q); // Forward declare
Q t2g(Q q){
  return q2a(1, q);
}

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

    Q k = q2a(dest_ar, pi(q, 1));
    Q v = q2a(dest_ar, pi(q, 2));
    if (AR_ID(dest_ar) == 2) { k = strip_fid(k); v = strip_fid(v); }
    zid(res, 1, k); // keys
    zid(res, 2, v); // values
    Q r = dict_rehash(res, dict_hash_cap_for_keys(n(k)));
    if(is_err(r)) return r;
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
        if(dest_a == 2){
          // Keep control/errors as immediates even when materializing into file arena.
          // (They are sentinel values; persisting them as heap atoms just adds ambiguity.)
          B tq = t(q);
          if(tq==T_CTL || tq==T_ERR) return q;
          return heap_atom_from(dest_ar, q);
        }
        return q;
    }

    if (ha(q) == dest_a) {
        if (dest_a != 2 || (q >> 44) == dest_fid) return q;
    }

    if(t(q)==T_LAMBDA){
        Q params = q2a(dest_ar, pi(q, 0));
        Q body = q2a(dest_ar, pi(q, 1));
        if (AR_ID(dest_ar) == 2) { params = strip_fid(params); body = strip_fid(body); }
        Q res = tsna(dest_ar, T_LAMBDA, 1, 3, 2, 2);
        zid(res, 0, params);
        zid(res, 1, body);
        return res;
    }

    if (sh(q) == 0) return heap_atom_from(dest_ar, q);
    if (sh(q) == 1) return q2a_list(dest_ar, q);
    if (sh(q) == 2) return q2a_dict(dest_ar, q);
    return q;
}

// -----------------------------------------------------------------------------
// Symbol interning
//
// Symbols (`name) are interned into a global table so:
// - equality/hashing can use the symbol id payload
// - printing can recover the original name
// - users can inspect the symbol table via the exposed globals:
//   - symtab: list of symbol names (id -> "name")
//   - symmap: dict mapping "name" -> id
// -----------------------------------------------------------------------------

static Q SYM_TAB = 0;   // list of charvecs, in buddy arena; exposed as `symtab`
static Q SYM_MAP = 0;   // dict: charvec -> int (id), in buddy arena; exposed as `symmap`
static Q SYM_K_TAB = 0; // symbol key for global dict
static Q SYM_K_MAP = 0;
static Q SYM_PAY_IF = 0; // reference payload for keyword `if` (interned symbol payload)
// Lambdas are heap objects of type T_LAMBDA (not marker-tagged lists).

static inline Q qhash_charvec_bytes(const C* bytes, D len){
  Q h0 = mix64(((Q)T_CHAR<<56) ^ ((Q)1<<48) ^ ((Q)0<<40) ^ (Q)len);
  return mix64(h0 ^ hash_bytes64(bytes, (Q)len));
}

static inline int tag64_digit(C c){
  if(c=='_') return 0;
  if(c>='A' && c<='Z') return 1 + (c - 'A');
  if(c>='a' && c<='z') return 27 + (c - 'a');
  if(c>='0' && c<='9') return 53 + (c - '0');
  if(c=='.') return 63;
  return -1;
}

static const Q TAG64_ERR = ~0ULL;

static inline Q tag64_parse_payload(const C* s, D len){
  // No stored length: leading '_' digits are treated as leading zeros and thus are not round-trippable.
  if(!s || len < 0) return TAG64_ERR;
  if(len > 10) return TAG64_ERR; // >60 bits
  Q v=0;
  for(D i=0;i<len;i++){
    int d = tag64_digit(s[i]);
    if(d < 0) return TAG64_ERR;
    v = (v << 6) | (Q)(D)d;
  }
  return v;
}

static B symmap_lookup_id(Q symmap, const C* bytes, D len, D* out_id){
  if(!out_id) return 0;
  if(!symmap || !ip(symmap) || sh(symmap)!=2) return 0;
  Q ok = dict_ensure_ht(symmap, n(pi(symmap,1)));
  if(is_err(ok)) return 0;

  Q htq=pi(symmap,0), kq=pi(symmap,1), vq=pi(symmap,2);
  Q* ht=(Q*)p(htq);
  D c=cp(htq);
  if(!c) return 0;
  D mask = c - 1;

  Q h = qhash_charvec_bytes(bytes, len);
  D fp = fp32_from_hash(h);
  D i = bucket_from_hash(h, lg2(c)) & mask;
  for(D j=0; j<c; ++j){
    Q e = ht[i];
    if(!e) return 0;
    if(fp32_from_entry(e) == fp){
      D idx1 = idx32_from_entry(e);
      if(idx1){
        Q key = pi(kq, idx1-1);
        if(t(key)==T_CHAR && sh(key)==1 && n(key)==len && 0==memcmp(p(key), bytes, (size_t)len)){
          Q val = pi(vq, idx1-1);
          if(t(val)!=T_INT || sh(val)!=0) return 0;
          J idj = (J)ra(val);
          if(idj < 0 || idj > 0x7FFFFFFF) return 0;
          *out_id = (D)idj;
          return 1;
        }
      }
    }
    i = (i + 1) & mask;
  }
  return 0;
}

static void sym_init(void){
  if(SYM_TAB && SYM_MAP) return;
  if(!G) return;

  if(!SYM_TAB){
    SYM_TAB = lca(1, 64);
  }
  if(!SYM_MAP){
    // Values are pointer-list ints (an(id)) so dkv's ir/dr remains safe.
    SYM_MAP = dni(0, 3, 0, 1);
  }

  // Bootstrap the interned ids for the exposed globals "symtab" and "symmap" without
  // recursing back into sym_intern_bytes(). These keys must be interned so that
  // identifier references (which are interned at lex time) can resolve them.
  D id_tab=0, id_map=0;
  if(!symmap_lookup_id(SYM_MAP, "symtab", 6, &id_tab)){
    Q name = tsna_u(1, T_CHAR, 1, 0, 6, 6);
    memcpy(p(name), "symtab", 6);
    D idx = n(SYM_TAB);
    Q tab2 = xn(SYM_TAB, 1);
    if(!is_err(tab2)){
      if(tab2!=SYM_TAB) SYM_TAB = tab2;
      zid(SYM_TAB, idx, name);
      dkv(SYM_MAP, name, an((J)idx));
      id_tab = idx;
    }
  }
  if(!symmap_lookup_id(SYM_MAP, "symmap", 6, &id_map)){
    Q name = tsna_u(1, T_CHAR, 1, 0, 6, 6);
    memcpy(p(name), "symmap", 6);
    D idx = n(SYM_TAB);
    Q tab2 = xn(SYM_TAB, 1);
    if(!is_err(tab2)){
      if(tab2!=SYM_TAB) SYM_TAB = tab2;
      zid(SYM_TAB, idx, name);
      dkv(SYM_MAP, name, an((J)idx));
      id_map = idx;
    }
  }

  // Bootstrap keyword payloads (like symtab/symmap) to guarantee they resolve as identifiers.
  D id_if = 0;
  B ok_if = symmap_lookup_id(SYM_MAP, "if", 2, &id_if);
  if(!ok_if){
    Q name = tsna_u(1, T_CHAR, 1, 0, 2, 2);
    memcpy(p(name), "if", 2);
    D idx = n(SYM_TAB);
    Q tab2 = xn(SYM_TAB, 1);
    if(!is_err(tab2)){
      if(tab2!=SYM_TAB) SYM_TAB = tab2;
      zid(SYM_TAB, idx, name);
      dkv(SYM_MAP, name, an((J)idx));
      id_if = idx;
      ok_if = 1;
    }
  }

  SYM_K_TAB = as(SYM_PAYLOAD_INTERN(id_tab));
  SYM_K_MAP = as(SYM_PAYLOAD_INTERN(id_map));
  if(ok_if) SYM_PAY_IF = SYM_PAYLOAD_INTERN(id_if);
  dkv(G, SYM_K_TAB, SYM_TAB);
  dkv(G, SYM_K_MAP, SYM_MAP);
}

static inline Q sym_intern_bytes(const C* bytes, D len){
  sym_init();
  if(!SYM_TAB || !SYM_MAP) return as(SYM_PAYLOAD_SMALL(parse_b((C*)bytes, len, 62))); // fallback

  D id=0;
  if(symmap_lookup_id(SYM_MAP, bytes, len, &id)){
    return as(SYM_PAYLOAD_INTERN(id));
  }

  // Allocate name string (buddy) and append to symtab.
  Q name = tsna_u(1, T_CHAR, 1, 0, len, len ? len : 1);
  if(len) memcpy(p(name), bytes, (size_t)len);

  D idx = n(SYM_TAB);
  Q tab2 = xn(SYM_TAB, 1);
  if(is_err(tab2)) return tab2;
  if(tab2 != SYM_TAB){
    SYM_TAB = tab2;
    dkv(G, SYM_K_TAB, SYM_TAB);
  }
  zid(SYM_TAB, idx, name);

  // Insert into map (name -> id).
  dkv(SYM_MAP, name, an((J)idx));
  return as(SYM_PAYLOAD_INTERN(idx));
}

// -----------------------------------------------------------------------------
// Platform layer
//
// Goal: keep preprocessor platform conditionals localized to a single section,
// so the rest of the interpreter reads like a platform-agnostic runtime calling
// a small OS API.
// -----------------------------------------------------------------------------

#if L_OS_WIN32

static void platform_arena_reserve_init(void){
  AB[0]=(Q*)VirtualAlloc(0, ARENA_SZ, MEM_RESERVE, PAGE_READWRITE);if(!AB[0]){exit(1);}AC[0]=ARENA_SZ/BUMP_UNIT_BYTES;AI[0]=1;
  AB[1]=(Q*)VirtualAlloc(0, ARENA_SZ, MEM_RESERVE, PAGE_READWRITE);if(!AB[1]){exit(1);}AC[1]=ARENA_SZ/BUDDY_UNIT_BYTES;AI[1]=0;
}

static void platform_commit_range(void* p, Q bytes){
  VirtualAlloc(p, (SIZE_T)bytes, MEM_COMMIT, PAGE_READWRITE);
}

static void* platform_vm_alloc(Q bytes){
  return VirtualAlloc(0, (SIZE_T)bytes, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
}

static void platform_vm_free(void* base, Q bytes){
  (void)bytes;
  VirtualFree(base, 0, MEM_RELEASE);
}

static void platform_init_stdout_utf8_if_console(void){
  // Only attempt to change the console code page when stdout is an actual console.
  // When stdout is redirected (e.g. piped from PowerShell), there may be no console attached.
  HANDLE hout = GetStdHandle(STD_OUTPUT_HANDLE);
  DWORD mode = 0;
  if(hout && hout != INVALID_HANDLE_VALUE && GetConsoleMode(hout, &mode)){
    SetConsoleOutputCP(65001);
  }
}

static B platform_stdin_is_console(void){
  HANDLE hin = GetStdHandle(STD_INPUT_HANDLE);
  DWORD mode = 0;
  return (hin && hin != INVALID_HANDLE_VALUE && GetConsoleMode(hin, &mode)) ? 1 : 0;
}

static void platform_write_stderr_bytes(const char* s, size_t n){
  if(!s || !n) return;
  HANDLE h = GetStdHandle(STD_ERROR_HANDLE);
  if(!h || h==INVALID_HANDLE_VALUE) return;
  DWORD wrote = 0;
  WriteFile(h, s, (DWORD)n, &wrote, NULL);
}

static Q platform_now_ns_u64(void){
  static Q qpc_freq = 0;
  if(!qpc_freq){
    LARGE_INTEGER f;
    QueryPerformanceFrequency(&f);
    qpc_freq = (Q)f.QuadPart;
    if(!qpc_freq) qpc_freq = 1;
  }
  LARGE_INTEGER c;
  QueryPerformanceCounter(&c);
  Q ticks = (Q)c.QuadPart;
  Q sec = ticks / qpc_freq;
  Q rem = ticks % qpc_freq;
  return sec*1000000000ULL + (rem*1000000000ULL)/qpc_freq;
}

void* os_map(char* fn, Q* sz, Q* h_out){
  void* addr = 0;
  int is_new = 0;
  HANDLE hf = CreateFileA(fn, GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
  if(hf == INVALID_HANDLE_VALUE) {
    hf = CreateFileA(fn, GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, CREATE_NEW, FILE_ATTRIBUTE_NORMAL, NULL);
    if(hf != INVALID_HANDLE_VALUE){
      is_new = 1;
    }
    if(hf == INVALID_HANDLE_VALUE) return 0;
  } else { is_new = 0; }
  LARGE_INTEGER li; GetFileSizeEx(hf, &li); *sz = (Q)li.QuadPart;
  if(!*sz && is_new){ *sz=16; li.QuadPart=(LONGLONG)*sz; SetFilePointerEx(hf, li, NULL, FILE_BEGIN); SetEndOfFile(hf); }
  HANDLE hmap = CreateFileMapping(hf, NULL, PAGE_READWRITE, 0, 0, NULL);
  if(!hmap) { CloseHandle(hf); return 0; }
  addr = MapViewOfFile(hmap, FILE_MAP_ALL_ACCESS, 0, 0, 0);
  CloseHandle(hmap);
  *h_out = (Q)hf;
  if(is_new && addr && *sz >= 16) memset(addr, 0, 16);
  return addr;
}

void* os_map_ro(char* fn, Q* sz, Q* h_out){
  void* addr = 0;
  HANDLE hf = CreateFileA(fn, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
  if(hf == INVALID_HANDLE_VALUE) return 0;
  LARGE_INTEGER li;
  if(!GetFileSizeEx(hf, &li)) { CloseHandle(hf); return 0; }
  *sz = (Q)li.QuadPart;
  if(*sz == 0) { CloseHandle(hf); *h_out = 0; return (void*)1; } // sentinel for empty file
  HANDLE hmap = CreateFileMapping(hf, NULL, PAGE_READONLY, 0, 0, NULL);
  if(!hmap) { CloseHandle(hf); return 0; }
  addr = MapViewOfFile(hmap, FILE_MAP_READ, 0, 0, 0);
  CloseHandle(hmap);
  if(!addr) { CloseHandle(hf); return 0; }
  *h_out = (Q)hf;
  return addr;
}

void os_unmap_ro(void* addr, Q sz, Q h){
  (void)sz;
  if(!addr || addr==(void*)1) return;
  UnmapViewOfFile(addr);
  CloseHandle((HANDLE)h);
}

void os_unmap(D fid){
  Q* addrs = (Q*)p(FT_addr);
  Q* caps  = (Q*)p(FT_cap);
  Q* hs    = (Q*)p(FT_h);
  Q* szs   = (Q*)p(FT_sz);

  if(!addrs[fid]) return;

  UnmapViewOfFile((void*)addrs[fid]);
  CloseHandle((HANDLE)hs[fid]);

  addrs[fid] = 0;
  hs[fid] = 0;
  caps[fid] = 0;
  szs[fid] = 0;
  zid(FT_fn, fid, 0);
}

void os_truncate(Q h, Q sz){
  HANDLE hf = (HANDLE)h;
  LARGE_INTEGER li; li.QuadPart = (LONGLONG)sz;
  SetFilePointerEx(hf, li, NULL, FILE_BEGIN); SetEndOfFile(hf);
}

void* os_remap(void* addr, Q old_cap, Q new_cap, Q h){
  (void)old_cap;
  UnmapViewOfFile(addr);
  HANDLE hf = (HANDLE)h;
  HANDLE hmap = CreateFileMapping(hf, NULL, PAGE_READWRITE, (DWORD)(new_cap >> 32), (DWORD)new_cap, NULL);
  if(!hmap) return 0;
  addr = MapViewOfFile(hmap, FILE_MAP_ALL_ACCESS, 0, 0, 0);
  CloseHandle(hmap);
  return addr;
}

#elif L_OS_POSIX

static void platform_arena_reserve_init(void){
  AB[0]=(Q*)mmap(0, ARENA_SZ, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);if(AB[0]==MAP_FAILED){exit(1);}AC[0]=ARENA_SZ/BUMP_UNIT_BYTES;AI[0]=1;
  AB[1]=(Q*)mmap(0, ARENA_SZ, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);if(AB[1]==MAP_FAILED){exit(1);}AC[1]=ARENA_SZ/BUDDY_UNIT_BYTES;AI[1]=0;
}

static void platform_commit_range(void* p, Q bytes){
  Q a=(Q)p, m=4095;
  Q s=a&~m;
  Q e=(a+bytes+m)&~m;
  mprotect((void*)s, (size_t)(e-s), PROT_READ|PROT_WRITE);
}

static void* platform_vm_alloc(Q bytes){
  void* base = mmap(0, (size_t)bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  return (base == MAP_FAILED) ? 0 : base;
}

static void platform_vm_free(void* base, Q bytes){
  munmap(base, (size_t)bytes);
}

static void platform_init_stdout_utf8_if_console(void){
  // no-op
}

static B platform_stdin_is_console(void){
  return isatty(fileno(stdin)) ? 1 : 0;
}

static void platform_write_stderr_bytes(const char* s, size_t n){
  if(!s || !n) return;
  (void)write(2, s, n);
}

static Q platform_now_ns_u64(void){
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (Q)ts.tv_sec*1000000000ULL + (Q)ts.tv_nsec;
}

void* os_map(char* fn, Q* sz, Q* h_out){
  void* addr = 0;
  int is_new = 0;
  int fd = open(fn, O_RDWR | O_CREAT, 0644);
  if(fd < 0) return 0;
  struct stat st; fstat(fd, &st); *sz = (Q)st.st_size;
  if(!*sz){ is_new=1; *sz=16; ftruncate(fd, 16); } else { is_new = 0; }
  addr = mmap(0, (size_t)*sz, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  if(addr == MAP_FAILED) { close(fd); return 0; }
  *h_out = (Q)fd;
  if(is_new && addr && *sz >= 16) memset(addr, 0, 16);
  return addr;
}

void* os_map_ro(char* fn, Q* sz, Q* h_out){
  void* addr = 0;
  int fd = open(fn, O_RDONLY);
  if(fd < 0) return 0;
  struct stat st;
  if(fstat(fd, &st) < 0) { close(fd); return 0; }
  *sz = (Q)st.st_size;
  if(*sz == 0) { close(fd); *h_out = 0; return (void*)1; } // sentinel for empty file
  addr = mmap(0, (size_t)*sz, PROT_READ, MAP_PRIVATE, fd, 0);
  if(addr == MAP_FAILED) { close(fd); return 0; }
  *h_out = (Q)fd;
  return addr;
}

void os_unmap_ro(void* addr, Q sz, Q h){
  if(!addr || addr==(void*)1) return;
  munmap(addr, (size_t)sz);
  close((int)h);
}

void os_unmap(D fid){
  Q* addrs = (Q*)p(FT_addr);
  Q* caps  = (Q*)p(FT_cap);
  Q* hs    = (Q*)p(FT_h);
  Q* szs   = (Q*)p(FT_sz);

  if(!addrs[fid]) return;

  munmap((void*)addrs[fid], (size_t)caps[fid]);
  close((int)hs[fid]);

  addrs[fid] = 0;
  hs[fid] = 0;
  caps[fid] = 0;
  szs[fid] = 0;
  zid(FT_fn, fid, 0);
}

void os_truncate(Q h, Q sz){
  ftruncate((int)h, sz);
}

void* os_remap(void* addr, Q old_cap, Q new_cap, Q h){
  munmap(addr, (size_t)old_cap);
  int fd = (int)h;
  addr = mmap(0, (size_t)new_cap, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  return (addr == MAP_FAILED) ? 0 : addr;
}

#else
  #error "Unsupported platform (no platform layer implementation)"
#endif

D find_empty_ft_slot(void){
  D idx = n(FT_addr);
  for(D i=0; i<idx; i++){
    if(pi(FT_addr, i) == 0) return i;
  }
  Q old_addr = FT_addr, old_sz = FT_sz, old_cap = FT_cap, old_h = FT_h, old_fn = FT_fn;
  FT_addr = xn(FT_addr, 1);
  FT_sz   = xn(FT_sz, 1);
  FT_cap  = xn(FT_cap, 1);
  FT_h    = xn(FT_h, 1);
  FT_fn   = xn(FT_fn, 1);
  if(FT_addr!=old_addr || FT_sz!=old_sz || FT_cap!=old_cap || FT_h!=old_h || FT_fn!=old_fn){
    ft_refresh_dict();
  }
  return idx;
}

// -----------------------------------------------------------------------------
// OS heap allocation (no libc malloc/free/realloc/calloc)
//
// This is for temporary C-side buffers (lexer token buffers, input lines, etc.).
// Lang objects must still be allocated via arenas (tsna/vna/etc.).
//
// NOTE: We intentionally avoid the C standard library allocators in l.c.
// -----------------------------------------------------------------------------

typedef struct { Q magic; Q payload_bytes; Q total_bytes; } OsHeapHdr;
static const Q OSHEAP_MAGIC = 0x4C414E472D4F5341ULL; // "LANG-OSA" (arbitrary tag)

static inline Q os_align16(Q x){ return (x + 15ULL) & ~15ULL; }

static void* os_heap_alloc(Q payload_bytes){
  Q total = os_align16((Q)sizeof(OsHeapHdr) + payload_bytes);
  void* base = platform_vm_alloc(total);
  if(!base) return 0;
  OsHeapHdr* h = (OsHeapHdr*)base;
  h->magic = OSHEAP_MAGIC;
  h->payload_bytes = payload_bytes;
  h->total_bytes = total;
  return (void*)(h + 1);
}

static inline Q os_heap_payload_bytes(void* p){
  if(!p) return 0;
  OsHeapHdr* h = ((OsHeapHdr*)p) - 1;
  if(h->magic != OSHEAP_MAGIC) return 0;
  return h->payload_bytes;
}

static void os_heap_free(void* p){
  if(!p) return;
  OsHeapHdr* h = ((OsHeapHdr*)p) - 1;
  if(h->magic != OSHEAP_MAGIC) return;
  Q total = h->total_bytes;
  platform_vm_free((void*)h, total);
}

static void* os_heap_realloc(void* p, Q new_payload_bytes){
  if(!p) return os_heap_alloc(new_payload_bytes);
  if(new_payload_bytes == 0){ os_heap_free(p); return 0; }
  Q old_payload_bytes = os_heap_payload_bytes(p);
  void* np = os_heap_alloc(new_payload_bytes);
  if(!np) return 0;
  Q copy_bytes = old_payload_bytes < new_payload_bytes ? old_payload_bytes : new_payload_bytes;
  if(copy_bytes) memcpy(np, p, (size_t)copy_bytes);
  os_heap_free(p);
  return np;
}

Q ca(B A,Q v,Q a,Q w);

Q file_append(Q a, Q w);
Q file_log(Q a, Q w);
Q file_read_log(Q f);

Q fl(B A, Q v, Q a, Q w){
  if(t(w)!=6) return ae(2);
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
  if(!map_base) return ae(2);

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
  if(t(a)!=6) return ae(2);
  char fn[256]; D fn_len = n(a); if(fn_len > 255) fn_len = 255;
  for(D i=0; i<fn_len; i++) fn[i] = (char)pi(a,i); fn[fn_len] = 0;

  remove(fn); // Overwrite by removing first.

  D fid = find_empty_ft_slot();

  Q sz=0, h=0;
  void* map_base = os_map(fn, &sz, &h);
  if(!map_base) return ae(2);

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

static Q text_read(Q w){
#if L_OS_WASM
  (void)w;
  return ae(2);
#else
  if(t(w)!=T_CHAR) return ae(2);
  C fn[1024];
  if(!qstr_to_c(w, fn, (D)sizeof(fn))) return ae(2);

  Q sz = 0, h = 0;
  void* addr = os_map_ro(fn, &sz, &h);
  if(!addr) return ae(2);
  if(addr==(void*)1) return vna(0, T_CHAR, 0, 0);
  if(sz > 0xFFFFFFFFULL){ os_unmap_ro(addr, sz, h); return ae(2); }

  Q z = vna(0, T_CHAR, 0, (D)sz);
  if(sz) memcpy(p(z), addr, (size_t)sz);
  os_unmap_ro(addr, sz, h);
  return z;
#endif
}

static Q text_write(Q a, Q w){
#if L_OS_WASM
  (void)a; (void)w;
  return ae(2);
#else
  if(t(a)!=T_CHAR) return ae(2);
  C fn[1024];
  if(!qstr_to_c(a, fn, (D)sizeof(fn))) return ae(2);

  if(t(w)!=T_CHAR) return ae(2);

  FILE* f = fopen(fn, "wb");
  if(!f) return ae(2);

  if(sh(w)==0){
    C c = (C)(ip(w) ? pi(w, 0) : di(w));
    if(1 != fwrite(&c, 1, 1, f)){ fclose(f); return ae(2); }
  }else if(sh(w)==1){
    size_t nw = (size_t)n(w);
    if(nw && nw != fwrite(p(w), 1, nw, f)){ fclose(f); return ae(2); }
  }else{
    fclose(f);
    return ae(2);
  }

  fclose(f);
  return w;
#endif
}

Q textm(B A, Q v, Q a, Q w){
  (void)A; (void)v; (void)a;
  return text_read(w);
}
Q textd(B A, Q v, Q a, Q w){
  (void)A; (void)v;
  return text_write(a, w);
}

Q file_read(Q f){
  D fid = AR_FID(di(f));
  Q root = *(Q*)((Q*)p(FT_addr))[fid];
  if(ip(root) && ha(root)==2){
    root |= ((Q)fid << 44); // Inject file index into root pointer
  }
  return root;
}
Q ld(B A, Q v, Q a, Q w){
  if(t(w)!=6) return ae(2);
  C fn[1024];
  if(!qstr_to_c(w, fn, (D)sizeof(fn))) return ae(2);
  if(ends_with_dot_l(fn)){
    return eval_code_file(fn);
  }
  Q f = fl(A,v,0,w);
  if(is_err(f)) return f;
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
    
    B ls = obj_header[2];
    D c = obj_header[5];

    // Reconstruct the Arena 2 pointer for the object at the current offset
    // NOTE: Pointer low-nibble must be 0. Type lives in the heap header, not in the pointer tag.
    Q obj_ptr = ((offset >> 4) << 6) | (2 << 4);
    obj_ptr |= ((Q)fid << 44); // Inject file ID

    // Append the discovered object's pointer to our result list
    result_list = xn(result_list, 1);
    zid(result_list, n(result_list)-1, obj_ptr);

    // Calculate the space this object took on disk to find the next one
    Q disk_size = az(ls, c);
    disk_size = (disk_size + 15) & ~15;
    
    if (disk_size == 0) break; // Safeguard against corrupted data

    offset += disk_size;
  }

  return result_list;
}

#define VTZ 39
#define ATZ 14
C* VT[];C* AT[];
C* MAP="0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";

typedef struct {
  char buf[4096];
  size_t len;
} StdoutBuf;

static void stdoutbuf_flush(StdoutBuf* b){
  if(!b || !b->len) return;
  fwrite(b->buf, 1, b->len, stdout);
  b->len = 0;
}

static void stdoutbuf_write(StdoutBuf* b, const char* s, size_t n){
  if(!b || !s || !n) return;
  while(n){
    size_t cap = sizeof(b->buf);
    size_t rem = cap - b->len;
    if(!rem){ stdoutbuf_flush(b); rem = cap; }
    size_t take = (n < rem) ? n : rem;
    memcpy(b->buf + b->len, s, take);
    b->len += take;
    s += take;
    n -= take;
  }
}

typedef struct {
  Q q;
  D len;
  Q err;
} QStrBuf;

typedef struct {
  void* ctx;
  void (*write)(void* ctx, const char* s, size_t n);
} L_Out;

static inline void out_write(L_Out* out, const char* s, size_t n){
  if(!out || !out->write) return;
  out->write(out->ctx, s, n);
}

static inline void out_putc(L_Out* out, C c){
  out_write(out, &c, 1);
}

static inline void out_puts(L_Out* out, const char* s){
  if(!s) return;
  out_write(out, s, strlen(s));
}

static void out_put_u64_dec(L_Out* out, Q x){
  C buf[32];
  int i = 0;
  do{
    Q q = x / 10ULL;
    Q r = x - q*10ULL;
    buf[i++] = (C)('0' + (C)r);
    x = q;
  }while(x && i < (int)sizeof(buf));
  for(int j=i-1;j>=0;--j) out_putc(out, buf[j]);
}

static void out_put_i64_dec(L_Out* out, J x){
  if(x < 0){
    out_putc(out, '-');
    Q ux = (Q)(-(x+1)) + 1ULL;
    out_put_u64_dec(out, ux);
    return;
  }
  out_put_u64_dec(out, (Q)x);
}

static void out_pr_b(L_Out* out, Q q, D b){
  if(q < (Q)b){ out_putc(out, MAP[q]); return; }
  out_pr_b(out, q / (Q)b, b);
  out_putc(out, MAP[q % (Q)b]);
}

static inline B int_vec_is_til(Q q){
  if(!ip(q) || t(q)!=T_INT || sh(q)!=1) return 0;
  D nq = n(q);
  const Q* bits = (const Q*)p(q);
  for(D i=0;i<nq;i++){
    if((J)bits[i] != (J)i) return 0;
  }
  return 1;
}

static void out_print_q(L_Out* out, Q q); // forward

static void out_pr_sym_payload(L_Out* out, Q idq){
  Q payload = idq;
  if(SYM_PAYLOAD_IS_INTERN(payload)){
    D id = (D)SYM_PAYLOAD_VAL(payload);
    if(SYM_TAB && ip(SYM_TAB) && sh(SYM_TAB)==1 && id < n(SYM_TAB)){
      Q name = pi(SYM_TAB, id);
      if(t(name)==T_CHAR && sh(name)==1){
        out_write(out, (const char*)p(name), (size_t)n(name));
        return;
      }
    }
  }else{
    out_pr_b(out, SYM_PAYLOAD_VAL(payload), 62);
    return;
  }
  out_pr_b(out, payload, 62);
}

// Tag64 printing: `$` prefix + base64 digits (alphabet is: _ A-Z a-z 0-9 .)
static inline C tag64_digit_char(D v){
  if(v==0) return '_';
  if(v>=1 && v<=26) return (C)('A' + (v-1));
  if(v>=27 && v<=52) return (C)('a' + (v-27));
  if(v>=53 && v<=62) return (C)('0' + (v-53));
  return '.';
}

static void out_pr_tag64_payload(L_Out* out, Q payload){
  // Canonical minimal digit form; leading '_' digits (zeros) are omitted. payload==0 prints as just "$".
  out_putc(out, '$');
  if(payload==0) return;
  C buf[16];
  D nbuf=0;
  while(payload && nbuf < (D)sizeof(buf)){
    D d = (D)(payload & 63ULL);
    buf[nbuf++] = tag64_digit_char(d);
    payload >>= 6;
  }
  for(D i=0;i<nbuf;i++){
    out_putc(out, buf[nbuf-1-i]);
  }
}

static inline void out_pr_f64(L_Out* out, double x){
  if(isnan(x)){ out_puts(out, "nan"); return; }
  if(isinf(x)){ if(x<0) out_putc(out, '-'); out_puts(out, "inf"); return; }
  C buf[80];
  int n = compiler_snprintf17g(buf, sizeof(buf), x);
  if(n <= 0){ out_puts(out, "nan"); return; }
  B has_dot=0, has_exp=0;
  for(int i=0;i<n;i++){ if(buf[i]=='.') has_dot=1; else if(buf[i]=='e' || buf[i]=='E') has_exp=1; }
  if(!has_dot && !has_exp){
    out_write(out, buf, (size_t)n);
    out_puts(out, ".0");
  }else{
    out_write(out, buf, (size_t)n);
  }
}

static inline void out_pr_adv_ascii(L_Out* out, D ai){
  switch(ai){
    case 0: return;
    case 1: out_putc(out, '\''); return;
    case 2: out_puts(out, "->"); return;
    case 3: out_puts(out, "<-"); return;
    case 4: out_puts(out, "<'"); return;
    case 5: out_puts(out, "'>"); return;
    case 6: out_puts(out, "'v"); return;
    case 7: out_puts(out, "'^"); return;
    case 8: out_puts(out, "<o"); return;
    case 9: out_puts(out, "o>"); return;
    case 10: out_puts(out, "/'"); return;
    case 11: out_puts(out, "\\'"); return;
    case 12: out_puts(out, "<p"); return;
    case 13: out_puts(out, "p>"); return;
    default: out_puts(out, (ai < (D)ATZ) ? AT[ai] : "?"); return;
  }
}

static inline void out_pr_control_ascii(L_Out* out, Q q){
  Q code = dc(q);
  if(code=='\n'){ out_putc(out, '\n'); return; }
  if(code>=32 && code<=126){ out_putc(out, (C)code); return; }
  out_print_q(out, q);
}

static inline const char* err_name(Q code){
  switch(code){
    case 1:  return "shape";
    case 2:  return "type";
    case 5:  return "nyi";
    case 6:  return "hash";
    case 99: return "limit";
    default: return 0;
  }
}

static void out_pr_lambda_roundtrip(L_Out* out, Q lam);

static inline void out_pr_verb_roundtrip(L_Out* out, Q v){
  Q vv=v;
  D advs[32];D nadv=0;
  while(dv(vv)>=(Q)VTZ && nadv<32){
    Q x=dv(vv)-(Q)VTZ;
    advs[nadv++]=(D)(x%(Q)ATZ)+1;
    vv=av(x/(Q)ATZ);
  }
  Q base=dv(vv);
  out_puts(out, base<(Q)VTZ ? VT[base] : "?");
  for(D i=nadv;i>0;--i) out_pr_adv_ascii(out, advs[i-1]);
}

static inline void out_pr_token_roundtrip(L_Out* out, Q tok){
  if(!tok) return;
  if(34==t(tok) && sh(tok)==0){ out_pr_control_ascii(out, tok); return; }
  if(18==t(tok) && sh(tok)==0){ out_pr_adv_ascii(out, (D)da(tok)); return; }
  if(2==t(tok) && sh(tok)==0){ out_pr_verb_roundtrip(out, tok); return; }
  if(T_LAMBDA==t(tok)){ out_pr_lambda_roundtrip(out, tok); return; }
  out_print_q(out, tok);
}

static void out_pr_lambda_roundtrip(L_Out* out, Q lam){
  if(!ip(lam) || t(lam)!=T_LAMBDA || sh(lam)!=1 || n(lam)!=2){ out_print_q(out, lam); return; }
  Q params = pi(lam, 0);
  Q body = pi(lam, 1);
  if(!ip(params) || t(params)!=T_SYM || sh(params)!=1){ out_print_q(out, lam); return; }
  if(!ip(body) || t(body)!=0 || sh(body)!=1){ out_print_q(out, lam); return; }

  out_puts(out, "{[");
  D np = n(params);
  for(D i=0;i<np;i++){
    if(i) out_putc(out, ';');
    out_pr_sym_payload(out, pi(params, i));
  }
  out_putc(out, ']');

  D nt = n(body);
  if(nt){
    // Add a single space before the body unless it starts with a statement terminator/newline.
    Q t0 = pi(body, 0);
    if(!(34==t(t0) && sh(t0)==0 && (';'==(C)dc(t0) || '\n'==(C)dc(t0)))) out_putc(out, ' ');

    for(D i=0;i<nt;i++){
      Q cur = pi(body, i);
      if(i){
        Q prev = pi(body, i-1);
        B prev_is_ctl = (34==t(prev) && sh(prev)==0);
        B cur_is_ctl = (34==t(cur) && sh(cur)==0);
        if(!prev_is_ctl && !cur_is_ctl) out_putc(out, ' ');
      }
      out_pr_token_roundtrip(out, cur);
    }
  }

  out_putc(out, '}');
}

static void out_print_q(L_Out* out, Q q){
  if(!q) return;
  B tq = t(q);
  B sq = sh(q);

  if(tq==0){
    if(!sq){
      out_puts(out, "atom type 0?");
      out_put_i64_dec(out, (J)q);
      out_putc(out, ' ');
      return;
    }
    if(sq==1){
      out_putc(out, '(');
      D nq = n(q);
      for(D i=0;i<nq;i++){
        out_print_q(out, pi(q,i));
        if(i+1 < nq) out_putc(out, ';');
      }
      out_putc(out, ')');
      return;
    }
    if(sq==2){
      out_putc(out, '{');
      Q kq = pi(q,1);
      Q vq = pi(q,2);
      D nk = n(kq);
      for(D i=0;i<nk;i++){
        out_print_q(out, pi(kq,i));
        out_putc(out, ':');
        out_print_q(out, qi(vq,i));
        out_putc(out, (i+1==nk) ? '}' : ';');
      }
      return;
    }
  }

  if(tq==1){
    if(sq==0){
      out_pr_sym_payload(out, ip(q) ? pi(q,0) : di(q));
      return;
    }
    if(sq==1){
      D nq=n(q);
      for(D i=0;i<nq;i++){
        if(i) out_putc(out, '.');
        out_pr_sym_payload(out, pi(q,i));
      }
      return;
    }
    out_pr_sym_payload(out, ip(q) ? pi(q,0) : di(q));
    return;
  }

  if(tq==2){
    out_pr_verb_roundtrip(out, q);
    return;
  }

  if(tq==T_ADV){
    out_pr_adv_ascii(out, (D)da(q));
    return;
  }

  if(tq==T_LAMBDA){
    out_pr_lambda_roundtrip(out, q);
    return;
  }

  if(tq==T_ERR){
    Q code = de(q);
    const char* name = err_name(code);
    if(name){ out_puts(out, "err:"); out_puts(out, name); }
    else{ out_puts(out, "err:"); out_put_u64_dec(out, code); }
    return;
  }

  if(tq==T_CTL){
    Q code = dc(q);
    if(code==4){ out_puts(out, "nf"); return; }                                 // not found
    if(code=='\n'){ out_puts(out, "ctl:\\n"); return; }
    if(code==';'){ out_puts(out, "ctl:;"); return; }
    if(code>=32 && code<=126){ out_puts(out, "ctl:"); out_putc(out, (C)code); return; }
    out_puts(out, "ctl:");
    out_put_u64_dec(out, code);
    return;
  }

  if(tq==9){
    out_puts(out, "file:");
    out_put_u64_dec(out, (Q)AR_FID(di(q)));
    return;
  }

  if(tq==T_CHAR){
    if(sq==0){
      out_putc(out, '"');
      out_putc(out, (C)(ip(q)?pi(q,0):di(q)));
      out_putc(out, '"');
      return;
    }
    if(sq==1){
      out_putc(out, '"');
      D nq=n(q);
      for(D i=0;i<nq;i++) out_putc(out, (C)pi(q,i));
      out_putc(out, '"');
      return;
    }
  }

  if(tq==T_INT){
    if(sq==0){
      out_put_i64_dec(out, (J)(ip(q)?pi(q,0):di_int(q)));
      return;
    }
    if(sq==1){
      D nq = n(q);
      if(!nq){ out_puts(out, "!0"); return; }
      if(nq >= 1024 && int_vec_is_til(q)){
        out_putc(out, '!');
        out_put_u64_dec(out, (Q)nq);
        return;
      }
      for(D i=0;i<nq;i++){
        out_put_i64_dec(out, (J)pi(q,i));
        if(i+1 < nq) out_putc(out, ' ');
      }
      return;
    }
  }

  if(tq==T_FLT){
    if(sq==0){
      out_pr_f64(out, f64_from_bits(pi(q,0)));
      return;
    }
    if(sq==1){
      D nq = n(q);
      if(!nq){ out_puts(out, "!0"); return; }
      for(D i=0;i<nq;i++){
        out_pr_f64(out, f64_from_bits(pi(q,i)));
        if(i+1 < nq) out_putc(out, ' ');
      }
      return;
    }
  }

  if(tq==T_TAG){
    if(sq==0){
      out_pr_tag64_payload(out, ip(q)?pi(q,0):di(q));
      return;
    }
    if(sq==1){
      D nq=n(q);
      for(D i=0;i<nq;i++){
        if(i) out_putc(out, ' ');
        out_pr_tag64_payload(out, pi(q,i));
      }
      return;
    }
  }

  if(tq==4){
    D nq=n(q);
    for(D i=0;i<nq;i++) out_print_q(out, pi(q,i));
    return;
  }

  if(tq==5){
    out_puts(out, "hash table: ");
    D c = cp(q);
    for(D i=0;i<c;i++){
      out_put_u64_dec(out, (Q)i);
      out_putc(out, ':');
      out_put_i64_dec(out, (J)pi(q,i));
      out_putc(out, ' ');
    }
    out_putc(out, '\n');
    return;
  }

  if(tq==T_SYM){
    // Interned symbol printing: show original bytes if present in symtab, else base62 payload.
    if(sq==0){
      out_putc(out, '`');
      out_pr_sym_payload(out, ip(q)?pi(q,0):di(q));
      return;
    }
    if(sq==1){
      D nq=n(q);
      for(D i=0;i<nq;i++){
        if(i) out_putc(out, ' ');
        out_putc(out, '`');
        out_pr_sym_payload(out, pi(q,i));
      }
      return;
    }
    out_putc(out, '`');
    out_pr_b(out, ip(q)?pi(q,0):di(q), 62);
    return;
  }
}

static void out_write_stdout(void* ctx, const char* s, size_t n){
  stdoutbuf_write((StdoutBuf*)ctx, s, n);
}

static void out_write_qstr(void* ctx, const char* s, size_t n){
  QStrBuf* b = (QStrBuf*)ctx;
  if(!b || b->err || !s || !n) return;
  if(n > 0x7FFFFFFFULL){ b->err = ae(99); return; }
  D add = (D)n;
  D need = b->len + add;
  if(need > cp(b->q)){
    Q nq = grow(b->q, need);
    if(is_err(nq)){ b->err = nq; return; }
    if(nq != b->q) dr(b->q);
    b->q = nq;
  }
  memcpy((C*)p(b->q) + b->len, s, n);
  b->len = need;
  ptr(b->q)[4] = b->len;
}

void pr(Q q){
  StdoutBuf sb;
  sb.len = 0;
  L_Out out;
  out.ctx = &sb;
  out.write = out_write_stdout;
  out_print_q(&out, q);
  stdoutbuf_flush(&sb);
}

Q reprm(B A, Q v, Q a, Q w){
  (void)A; (void)v; (void)a;
  QStrBuf b;
  b.q = vca(0, T_CHAR, 0, 64);
  if(is_err(b.q)) return b.q;
  b.len = 0;
  b.err = 0;
  L_Out out;
  out.ctx = &b;
  out.write = out_write_qstr;
  out_print_q(&out, w);
  if(b.err){ dr(b.q); return b.err; }
  return b.q;
}
VF VD[VTZ];
VF VM[VTZ];
extern VF AV[ATZ];

Q id(B A,Q v,Q a,Q w){return w;}
Q en(B A,Q v,Q a,Q w){
  (void)A; (void)v; (void)a;

  // Enlist:
  // - atoms => homogeneous vector of that atom type (shape 1)
  // - non-atoms => pointer list (type 0) containing the object
  if(ii(w) || (ip(w) && sh(w)==0)){
    B tw = t(w);
    if(tw==T_CHAR){
      Q z = vna(0, T_CHAR, 0, 1);
      pid(z, 0, ra(w));
      return z;
    }
    Q z = vna(0, tw, ls(w), 1);
    pid(z, 0, ra(w));
    return z;
  }

  Q z = vna(0, 0, 3, 1);
  zid(z, 0, w);
  return z;
}
Q tp(B A,Q v,Q a,Q w){return an(t(w));}
Q ct(B A,Q v,Q a,Q w){return an(n(w));}

typedef enum {NB,DB,LB,RB,MB} BM;                                                       // broadcast mode (NB = no implicit lift)
static const BM VBM[VTZ];
static const BM VBD[VTZ];

Q dispatch(VF* Vtab, const BM* Btab, Q v, Q a, Q w);

static inline Q vb_rebuild_dict(B A, Q d, Q new_vals){
  Q zd=dnu(0,3,0,A);
  Q kq = pi(d,1);
  Q *hk=ptr(kq);
  Q kc=tsna(A,hk[0],hk[1],hk[2],hk[4],hk[5]);
  memcpy(p(kc), p(kq), (size_t)sz(kq) * (size_t)n(kq));
  for(D i=0;i<n(kc);i++) ir(pi(kc,i)); // preserve referenced key objects if any

  zid(zd,1,kc);
  zid(zd,2,new_vals);
  Q r = dict_rehash(zd, dict_hash_cap_for_keys(n(kc)));
  if(is_err(r)) return r;
  return zd;
}

static inline B vb_implicit_needed(Q q){ return q && !ii(q) && t(q)==0; }

static inline B vb_need_for(BM m, Q a, Q w){
  switch(m){
    case DB: return vb_implicit_needed(a) || vb_implicit_needed(w);
    case RB: return vb_implicit_needed(w);
    case LB: return vb_implicit_needed(a);
    case MB: return vb_implicit_needed(w);
    case NB: return 0;
    default: return 0;
  }
}

// Derived verbs (verb+adverb chains) are encoded as a base-ATZ digit stream with an offset of VTZ.
// This avoids hard-coding magic numbers and keeps encode/decode consistent when VTZ/ATZ change.
static inline Q derive_verb(Q v, Q adv_atom){
  D ai = (D)da(adv_atom);
  // adverb ids start at 1; 0 is reserved/unused
  if(!ai) return v;
  return av(dv(v) * (Q)ATZ + (Q)(ai - 1) + (Q)VTZ);
}

static inline void decode_derived_verb(Q v, Q* base_out, D* adv_idx_out){
  Q r = dv(v);
  Q x = r - (Q)VTZ;
  *base_out = av(x / (Q)ATZ);
  *adv_idx_out = (D)(x % (Q)ATZ) + 1; // maps digit back to adverb id (1..ATZ-1)
}

static inline Q apply_raw(VF* Vtab, Q v, Q a, Q w){
  if(is_err(a)) return a;
  if(is_err(w)) return w;
  Q r=dv(v);
  if(r<(Q)VTZ) return Vtab && Vtab[r] ? Vtab[r](0, v, a, w) : ae(2);
  Q b=0; D idx=0;
  decode_derived_verb(v, &b, &idx);
  return AV[idx] ? AV[idx](0, b, a, w) : ae(2);
}

Q vb(B A,Q v,Q a,Q w,BM m,I d){ // arena verb alpha omega broadcast mode depth
  B sa=sh(a),sw=sh(w);
  D na=2==sa?n(pi(a,1)):n(a), nw=2==sw?n(pi(w,1)):n(w);
  if(DB==m && na!=nw && sa && sw) return ae(2);

  // Force broadcast for explicit adverbs (d>0). For implicit lifting (d<0), only lift on boxed args.
  B ib = d>0 ? 1 : vb_need_for(m, a, w);
  if(!ib){
    // No lift: behave like normal application (useful for explicit each on atoms).
    return (MB==m) ? apply_raw(VM, v, 0, w) : apply_raw(VD, v, a, w);
  }

  D nz=DB==m?(sa?na:nw):RB==m?nw:LB==m?na:nw;
  Q z=ln(nz);
  for(D i=0;i<nz;i++){
    Q ai=(m!=RB && 1==sa)?qi(a,i):(m!=RB && 2==sa)?qi(pi(a,2),i):a;
    Q wi=(m!=LB && 1==sw)?qi(w,i):(m!=LB && 2==sw)?qi(pi(w,2),i):w;
    Q zi;
    if(d<0 && m!=NB && vb_need_for(m, ai, wi)){
      zi = vb(0, v, ai, wi, m, -1);
    }else{
      zi = (MB==m) ? apply_raw(VM, v, 0, wi) : apply_raw(VD, v, ai, wi);
    }    
    if(is_err(zi)) return zi;
    zid(z,i,zi);
  }
  if(2==sa) return vb_rebuild_dict(A, a, z);
  if(2==sw) return vb_rebuild_dict(A, w, z);
  return z;
}

Q car(B A,Q v,Q a,Q w){return 0==sh(w)?w:qi(w,0);}

static inline B is_num_type(B tq){ return tq==T_INT || tq==T_FLT; }
static inline Q num_int_bits_atom(Q q){ return ip(q) ? pi(q,0) : di_int(q); }
static inline Q num_int_bits_elem(Q q, D i){ return sh(q) ? pi(q,i) : num_int_bits_atom(q); }
static inline double num_f64_atom(Q q){
  B tq=t(q);
  if(tq==T_FLT) return f64_from_bits(pi(q,0));
  return (double)(J)(ip(q) ? pi(q,0) : di_int(q));
}
static inline double num_f64_elem(Q q, D i){
  B tq=t(q);
  if(sh(q)){
    Q bits = pi(q,i);
    return tq==T_FLT ? f64_from_bits(bits) : (double)(J)bits;
  }
  return num_f64_atom(q);
}

static inline Q vne_u(Q ar, B t, B z, D n){
  // Allocate an exact-capacity value vector without zeroing payload.
  // Only use when the caller will fully initialize all n elements.
  D c = n ? n : 1;
  return tsna_u(ar, t, 1, z, n, c);
}

static inline B num_can_inplace_w_vec(Q w, B out_t, D nz){
  // Reuse omega's payload for elementwise numeric kernels when omega is:
  // - bump arena (0) allocated
  // - an unreffed (rc==0) vector
  // - same element type/size as the output
  // This reduces arena 0 bump pressure for chains like: 2 + 1 + !n
  if(L_opts.no_inplace) return 0;
  if(!itp(w)) return 0;
  Q* hw = ptr(w);
  if((B)hw[0] != out_t) return 0;
  if((B)hw[1] != 1) return 0;
  if((B)hw[2] != 3) return 0;  // 8-byte elements (int64/float64 bits)
  if((D)hw[4] != nz) return 0; // exact length match
  if(hw[3] != 0) return 0;     // unreffed in object graph => safe to mutate
  return 1;
}

static inline B num_can_inplace_vec_bytes(Q q, B out_ls, D nz){
  // Like num_can_inplace_w_vec but only requires matching element *size* (ls),
  // not matching element *type*. Useful for comparisons, which produce int
  // vectors even when the input vector is float.
  if(L_opts.no_inplace) return 0;
  if(!itp(q)) return 0;
  Q* h = ptr(q);
  if((B)h[1] != 1) return 0;
  if((B)h[2] != out_ls) return 0;
  if((D)h[4] != nz) return 0;
  if(h[3] != 0) return 0;
  return 1;
}

static inline Q now_ns_u64(void){
  return platform_now_ns_u64();
}

static inline J floordiv_j(J a, J b){
  // Requires b != 0. Floors toward -inf (Python-style).
  J q = a / b;
  J r = a % b;
  if(r && ((r > 0) != (b > 0))) q -= 1;
  return q;
}
static inline J floormod_j(J a, J b){
  // Requires b != 0. Remainder has sign of b and magnitude < |b|.
  J r = a % b;
  if(r && ((r > 0) != (b > 0))) r += b;
  return r;
}

typedef enum {
  NOP_ADD,
  NOP_MUL,
  NOP_SUB,
  NOP_MIN,
  NOP_MAX,
  NOP_EQ,
  NOP_LT,
  NOP_GT,
  NOP_DIV,      // always float
  NOP_MOD,      // int: floored mod; float: fmod
  NOP_FLOORDIV, // int-only
  NOP_BAND,     // int-only bitwise and
  NOP_BOR,      // int-only bitwise or
  NOP_BXOR      // int-only bitwise xor
  ,NOP__N
} NOP;

typedef enum {NOUT_PROMOTE, NOUT_BOOL, NOUT_FLOAT, NOUT_INT} NOUT;
typedef struct { B require_int; NOUT out; } NumOpSpec;

static const NumOpSpec NUMOPS[] = {
  /* NOP_ADD      */ {0, NOUT_PROMOTE},
  /* NOP_MUL      */ {0, NOUT_PROMOTE},
  /* NOP_SUB      */ {0, NOUT_PROMOTE},
  /* NOP_MIN      */ {0, NOUT_PROMOTE},
  /* NOP_MAX      */ {0, NOUT_PROMOTE},
  /* NOP_EQ       */ {0, NOUT_BOOL},
  /* NOP_LT       */ {0, NOUT_BOOL},
  /* NOP_GT       */ {0, NOUT_BOOL},
  /* NOP_DIV      */ {0, NOUT_FLOAT},
  /* NOP_MOD      */ {0, NOUT_PROMOTE},
  /* NOP_FLOORDIV */ {1, NOUT_INT},
  /* NOP_BAND     */ {1, NOUT_INT},
  /* NOP_BOR      */ {1, NOUT_INT},
  /* NOP_BXOR     */ {1, NOUT_INT},
};

static inline const NumOpSpec* numop_spec(NOP op){
  if((D)op >= (D)(sizeof(NUMOPS)/sizeof(NUMOPS[0]))) return 0;
  return &NUMOPS[(D)op];
}

typedef Q(*NumKernel)(Q a, Q w, B sa, B sw, D nz);

typedef struct {
  B is_vec;
  B is_flt;
  const Q* vec_bits;
  double scalar;
} NumInF64;

static inline NumInF64 numin_f64(Q q, B is_vec){
  NumInF64 in;
  in.is_vec = is_vec;
  in.is_flt = (t(q) == T_FLT);
  in.vec_bits = is_vec ? (const Q*)p(q) : 0;
  in.scalar = is_vec ? 0.0 : num_f64_atom(q);
  return in;
}

static inline double numin_f64_at(const NumInF64* in, D i){
  if(!in->is_vec) return in->scalar;
  Q bits = in->vec_bits[i];
  return in->is_flt ? f64_from_bits(bits) : (double)(J)bits;
}

typedef struct {
  B is_vec;
  const Q* vec_bits;
  Q scalar_bits;
} NumInI64;

static inline NumInI64 numin_i64(Q q, B is_vec){
  NumInI64 in;
  in.is_vec = is_vec;
  in.vec_bits = is_vec ? (const Q*)p(q) : 0;
  in.scalar_bits = is_vec ? 0 : num_int_bits_atom(q);
  return in;
}

static inline Q numin_i64_bits_at(const NumInI64* in, D i){
  return in->is_vec ? in->vec_bits[i] : in->scalar_bits;
}

static Q k_add_f(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return af(0, num_f64_atom(a) + num_f64_atom(w));
  Q z=num_can_inplace_w_vec(w, T_FLT, nz) ? w : vne_u(0, T_FLT, 3, nz);
  Q* out = (Q*)p(z);
  NumInF64 av = numin_f64(a, sa);
  NumInF64 wv = numin_f64(w, sw);
  for(D i=0;i<nz;i++){
    double x = numin_f64_at(&av, i);
    double y = numin_f64_at(&wv, i);
    out[i] = f64_bits(x + y);
  }
  return z;
}
static Q k_mul_f(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return af(0, num_f64_atom(a) * num_f64_atom(w));
  Q z=num_can_inplace_w_vec(w, T_FLT, nz) ? w : vne_u(0, T_FLT, 3, nz);
  Q* out = (Q*)p(z);
  NumInF64 av = numin_f64(a, sa);
  NumInF64 wv = numin_f64(w, sw);
  for(D i=0;i<nz;i++){
    double x = numin_f64_at(&av, i);
    double y = numin_f64_at(&wv, i);
    out[i] = f64_bits(x * y);
  }
  return z;
}
static Q k_sub_f(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return af(0, num_f64_atom(a) - num_f64_atom(w));
  Q z=num_can_inplace_w_vec(w, T_FLT, nz) ? w : vne_u(0, T_FLT, 3, nz);
  Q* out = (Q*)p(z);
  NumInF64 av = numin_f64(a, sa);
  NumInF64 wv = numin_f64(w, sw);
  for(D i=0;i<nz;i++){
    double x = numin_f64_at(&av, i);
    double y = numin_f64_at(&wv, i);
    out[i] = f64_bits(x - y);
  }
  return z;
}
static Q k_min_f(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0){ double x=num_f64_atom(a), y=num_f64_atom(w); return af(0, x<y?x:y); }
  Q z=num_can_inplace_w_vec(w, T_FLT, nz) ? w : vne_u(0, T_FLT, 3, nz);
  Q* out = (Q*)p(z);
  NumInF64 av = numin_f64(a, sa);
  NumInF64 wv = numin_f64(w, sw);
  for(D i=0;i<nz;i++){
    double x = numin_f64_at(&av, i);
    double y = numin_f64_at(&wv, i);
    out[i] = f64_bits(x<y?x:y);
  }
  return z;
}
static Q k_max_f(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0){ double x=num_f64_atom(a), y=num_f64_atom(w); return af(0, x>y?x:y); }
  Q z=num_can_inplace_w_vec(w, T_FLT, nz) ? w : vne_u(0, T_FLT, 3, nz);
  Q* out = (Q*)p(z);
  NumInF64 av = numin_f64(a, sa);
  NumInF64 wv = numin_f64(w, sw);
  for(D i=0;i<nz;i++){
    double x = numin_f64_at(&av, i);
    double y = numin_f64_at(&wv, i);
    out[i] = f64_bits(x>y?x:y);
  }
  return z;
}
static Q k_div_f(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return af(0, num_f64_atom(a) / num_f64_atom(w));
  Q z=num_can_inplace_w_vec(w, T_FLT, nz) ? w : vne_u(0, T_FLT, 3, nz);
  Q* out = (Q*)p(z);
  NumInF64 av = numin_f64(a, sa);
  NumInF64 wv = numin_f64(w, sw);
  for(D i=0;i<nz;i++){
    double x = numin_f64_at(&av, i);
    double y = numin_f64_at(&wv, i);
    out[i] = f64_bits(x / y);
  }
  return z;
}
static Q k_mod_f(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return af(0, fmod(num_f64_atom(a), num_f64_atom(w)));
  Q z=num_can_inplace_w_vec(w, T_FLT, nz) ? w : vne_u(0, T_FLT, 3, nz);
  Q* out = (Q*)p(z);
  NumInF64 av = numin_f64(a, sa);
  NumInF64 wv = numin_f64(w, sw);
  for(D i=0;i<nz;i++){
    double x = numin_f64_at(&av, i);
    double y = numin_f64_at(&wv, i);
    out[i] = f64_bits(fmod(x, y));
  }
  return z;
}

static Q k_add_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)(num_int_bits_atom(a) + num_int_bits_atom(w)));
  Q z=num_can_inplace_w_vec(w, T_INT, nz) ? w : vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    out[i] = numin_i64_bits_at(&av, i) + numin_i64_bits_at(&wv, i);
  }
  return z;
}
static Q k_mul_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)(num_int_bits_atom(a) * num_int_bits_atom(w)));
  Q z=num_can_inplace_w_vec(w, T_INT, nz) ? w : vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    out[i] = numin_i64_bits_at(&av, i) * numin_i64_bits_at(&wv, i);
  }
  return z;
}
static Q k_sub_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)(num_int_bits_atom(a) - num_int_bits_atom(w)));
  Q z=num_can_inplace_w_vec(w, T_INT, nz) ? w : vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    out[i] = numin_i64_bits_at(&av, i) - numin_i64_bits_at(&wv, i);
  }
  return z;
}
static Q k_min_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0){
    Q x=num_int_bits_atom(a), y=num_int_bits_atom(w);
    return an((J)(((J)x < (J)y) ? x : y));
  }
  Q z=num_can_inplace_w_vec(w, T_INT, nz) ? w : vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    Q x = numin_i64_bits_at(&av, i);
    Q y = numin_i64_bits_at(&wv, i);
    out[i] = ((J)x < (J)y) ? x : y;
  }
  return z;
}
static Q k_max_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0){
    Q x=num_int_bits_atom(a), y=num_int_bits_atom(w);
    return an((J)(((J)x > (J)y) ? x : y));
  }
  Q z=num_can_inplace_w_vec(w, T_INT, nz) ? w : vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    Q x = numin_i64_bits_at(&av, i);
    Q y = numin_i64_bits_at(&wv, i);
    out[i] = ((J)x > (J)y) ? x : y;
  }
  return z;
}
static Q k_band_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)(num_int_bits_atom(a) & num_int_bits_atom(w)));
  Q z=num_can_inplace_w_vec(w, T_INT, nz) ? w : vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    out[i] = numin_i64_bits_at(&av, i) & numin_i64_bits_at(&wv, i);
  }
  return z;
}
static Q k_bor_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)(num_int_bits_atom(a) | num_int_bits_atom(w)));
  Q z=num_can_inplace_w_vec(w, T_INT, nz) ? w : vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    out[i] = numin_i64_bits_at(&av, i) | numin_i64_bits_at(&wv, i);
  }
  return z;
}
static Q k_bxor_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)(num_int_bits_atom(a) ^ num_int_bits_atom(w)));
  Q z=num_can_inplace_w_vec(w, T_INT, nz) ? w : vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    out[i] = numin_i64_bits_at(&av, i) ^ numin_i64_bits_at(&wv, i);
  }
  return z;
}
static Q k_mod_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0){
    J y=(J)num_int_bits_atom(w); if(!y) return ae(2);
    return an(floormod_j((J)num_int_bits_atom(a), y));
  }
  Q z=num_can_inplace_w_vec(w, T_INT, nz) ? w : vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    J y = (J)numin_i64_bits_at(&wv, i);
    if(!y) return ae(2);
    J x = (J)numin_i64_bits_at(&av, i);
    out[i] = (Q)floormod_j(x, y);
  }
  return z;
}
static Q k_floordiv_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0){
    J y=(J)num_int_bits_atom(w); if(!y) return ae(2);
    return an(floordiv_j((J)num_int_bits_atom(a), y));
  }
  Q z=num_can_inplace_w_vec(w, T_INT, nz) ? w : vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    J y = (J)numin_i64_bits_at(&wv, i);
    if(!y) return ae(2);
    J x = (J)numin_i64_bits_at(&av, i);
    out[i] = (Q)floordiv_j(x, y);
  }
  return z;
}

static Q k_eq_f(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)(num_f64_atom(a) == num_f64_atom(w)));
  Q z = (sw==1 && num_can_inplace_vec_bytes(w, 3, nz)) ? w :
        (sa==1 && num_can_inplace_vec_bytes(a, 3, nz)) ? a :
        vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInF64 av = numin_f64(a, sa);
  NumInF64 wv = numin_f64(w, sw);
  for(D i=0;i<nz;i++){
    out[i] = (Q)(numin_f64_at(&av, i) == numin_f64_at(&wv, i));
  }
  if(z==a || z==w){ ptr(z)[0] = T_INT; ptr(z)[2] = 3; }
  return z;
}
static Q k_lt_f(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)(num_f64_atom(a) < num_f64_atom(w)));
  Q z = (sw==1 && num_can_inplace_vec_bytes(w, 3, nz)) ? w :
        (sa==1 && num_can_inplace_vec_bytes(a, 3, nz)) ? a :
        vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInF64 av = numin_f64(a, sa);
  NumInF64 wv = numin_f64(w, sw);
  for(D i=0;i<nz;i++){
    out[i] = (Q)(numin_f64_at(&av, i) < numin_f64_at(&wv, i));
  }
  if(z==a || z==w){ ptr(z)[0] = T_INT; ptr(z)[2] = 3; }
  return z;
}
static Q k_gt_f(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)(num_f64_atom(a) > num_f64_atom(w)));
  Q z = (sw==1 && num_can_inplace_vec_bytes(w, 3, nz)) ? w :
        (sa==1 && num_can_inplace_vec_bytes(a, 3, nz)) ? a :
        vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInF64 av = numin_f64(a, sa);
  NumInF64 wv = numin_f64(w, sw);
  for(D i=0;i<nz;i++){
    out[i] = (Q)(numin_f64_at(&av, i) > numin_f64_at(&wv, i));
  }
  if(z==a || z==w){ ptr(z)[0] = T_INT; ptr(z)[2] = 3; }
  return z;
}
static Q k_eq_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)((J)num_int_bits_atom(a) == (J)num_int_bits_atom(w)));
  Q z = (sw==1 && num_can_inplace_w_vec(w, T_INT, nz)) ? w :
        (sa==1 && num_can_inplace_w_vec(a, T_INT, nz)) ? a :
        vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    J x = (J)numin_i64_bits_at(&av, i);
    J y = (J)numin_i64_bits_at(&wv, i);
    out[i] = (Q)(x == y);
  }
  return z;
}
static Q k_lt_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)((J)num_int_bits_atom(a) < (J)num_int_bits_atom(w)));
  Q z = (sw==1 && num_can_inplace_w_vec(w, T_INT, nz)) ? w :
        (sa==1 && num_can_inplace_w_vec(a, T_INT, nz)) ? a :
        vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    J x = (J)numin_i64_bits_at(&av, i);
    J y = (J)numin_i64_bits_at(&wv, i);
    out[i] = (Q)(x < y);
  }
  return z;
}
static Q k_gt_i(Q a,Q w,B sa,B sw,D nz){
  if(sa==0 && sw==0) return an((J)((J)num_int_bits_atom(a) > (J)num_int_bits_atom(w)));
  Q z = (sw==1 && num_can_inplace_w_vec(w, T_INT, nz)) ? w :
        (sa==1 && num_can_inplace_w_vec(a, T_INT, nz)) ? a :
        vne_u(0, T_INT, 3, nz);
  Q* out = (Q*)p(z);
  NumInI64 av = numin_i64(a, sa);
  NumInI64 wv = numin_i64(w, sw);
  for(D i=0;i<nz;i++){
    J x = (J)numin_i64_bits_at(&av, i);
    J y = (J)numin_i64_bits_at(&wv, i);
    out[i] = (Q)(x > y);
  }
  return z;
}

static const NumKernel K_F64[NOP__N] = {
  /* NOP_ADD      */ k_add_f,
  /* NOP_MUL      */ k_mul_f,
  /* NOP_SUB      */ k_sub_f,
  /* NOP_MIN      */ k_min_f,
  /* NOP_MAX      */ k_max_f,
  /* NOP_EQ       */ 0,
  /* NOP_LT       */ 0,
  /* NOP_GT       */ 0,
  /* NOP_DIV      */ k_div_f,
  /* NOP_MOD      */ k_mod_f,
  /* NOP_FLOORDIV */ 0,
  /* NOP_BAND     */ 0,
  /* NOP_BOR      */ 0,
  /* NOP_BXOR     */ 0,
};
static const NumKernel K_I64[NOP__N] = {
  /* NOP_ADD      */ k_add_i,
  /* NOP_MUL      */ k_mul_i,
  /* NOP_SUB      */ k_sub_i,
  /* NOP_MIN      */ k_min_i,
  /* NOP_MAX      */ k_max_i,
  /* NOP_EQ       */ 0,
  /* NOP_LT       */ 0,
  /* NOP_GT       */ 0,
  /* NOP_DIV      */ 0,
  /* NOP_MOD      */ k_mod_i,
  /* NOP_FLOORDIV */ k_floordiv_i,
  /* NOP_BAND     */ k_band_i,
  /* NOP_BOR      */ k_bor_i,
  /* NOP_BXOR     */ k_bxor_i,
};
static const NumKernel K_CMP_F64[NOP__N] = {
  /* NOP_ADD      */ 0,
  /* NOP_MUL      */ 0,
  /* NOP_SUB      */ 0,
  /* NOP_MIN      */ 0,
  /* NOP_MAX      */ 0,
  /* NOP_EQ       */ k_eq_f,
  /* NOP_LT       */ k_lt_f,
  /* NOP_GT       */ k_gt_f,
  /* NOP_DIV      */ 0,
  /* NOP_MOD      */ 0,
  /* NOP_FLOORDIV */ 0,
  /* NOP_BAND     */ 0,
  /* NOP_BOR      */ 0,
  /* NOP_BXOR     */ 0,
};
static const NumKernel K_CMP_I64[NOP__N] = {
  /* NOP_ADD      */ 0,
  /* NOP_MUL      */ 0,
  /* NOP_SUB      */ 0,
  /* NOP_MIN      */ 0,
  /* NOP_MAX      */ 0,
  /* NOP_EQ       */ k_eq_i,
  /* NOP_LT       */ k_lt_i,
  /* NOP_GT       */ k_gt_i,
  /* NOP_DIV      */ 0,
  /* NOP_MOD      */ 0,
  /* NOP_FLOORDIV */ 0,
  /* NOP_BAND     */ 0,
  /* NOP_BOR      */ 0,
  /* NOP_BXOR     */ 0,
};

static inline NumKernel kernel_f64(NOP op){ return (op>=0 && op<NOP__N) ? K_F64[op] : 0; }
static inline NumKernel kernel_i64(NOP op){ return (op>=0 && op<NOP__N) ? K_I64[op] : 0; }
static inline NumKernel kernel_cmp_f64(NOP op){ return (op>=0 && op<NOP__N) ? K_CMP_F64[op] : 0; }
static inline NumKernel kernel_cmp_i64(NOP op){ return (op>=0 && op<NOP__N) ? K_CMP_I64[op] : 0; }

static Q num_binop(NOP op, Q a, Q w){
  const NumOpSpec* sp = numop_spec(op);
  if(!sp) return ae(2);

  B ta=t(a), tw=t(w);
  if(sp->require_int){
    if(ta!=T_INT || tw!=T_INT) return ae(2);
  }else{
    if(!is_num_type(ta) || !is_num_type(tw)) return ae(2);
  }

  B sa=sh(a), sw=sh(w);
  if(sa>1 || sw>1) return ae(1);
  D na=n(a), nw=n(w);
  if(sa==1 && sw==1 && na!=nw) return ae(2);

  D nz = (sa==1) ? na : (sw==1) ? nw : 1;

  B use_f_in = (ta==T_FLT) || (tw==T_FLT);
  B out_f = (sp->out==NOUT_FLOAT) ? 1 : (sp->out==NOUT_PROMOTE ? use_f_in : 0);
  B out_bool = (sp->out==NOUT_BOOL);

  NumKernel k = 0;
  if(out_bool){
    k = use_f_in ? kernel_cmp_f64(op) : kernel_cmp_i64(op);
  }else if(out_f){
    k = kernel_f64(op);
  }else{
    k = kernel_i64(op);
  }
  return k ? k(a, w, sa, sw, nz) : ae(2);
}

static Q int_bit_not(Q w){
  if(t(w)!=T_INT) return ae(2);
  B sw=sh(w);
  if(sw==0) return an((J)(~num_int_bits_atom(w)));
  if(sw!=1) return ae(1);
  D nw=n(w);
  Q z=num_can_inplace_w_vec(w, T_INT, nw) ? w : vne_u(0, T_INT, 3, nw);
  Q* out = (Q*)p(z);
  for(D i=0;i<nw;i++) out[i] = ~num_int_bits_elem(w, i);
  return z;
}

Q nt(B A,Q v,Q a,Q w){
  (void)A; (void)v; (void)a;
  if(!is_num_type(t(w))) return ae(2);
  B sw=sh(w);
  if(sw==0){
    if(t(w)==T_FLT) return an(num_f64_atom(w)==0.0);
    return an((J)(num_int_bits_atom(w)==0));
  }
  if(sw!=1) return ae(1);
  D nw=n(w);
  Q z=(t(w)==T_INT && num_can_inplace_w_vec(w, T_INT, nw)) ? w : vne_u(0, T_INT, 3, nw);
  Q* out = (Q*)p(z);
  if(t(w)==T_FLT){
    for(D i=0;i<nw;i++) out[i] = (Q)(num_f64_elem(w,i)==0.0);
  }else{
    for(D i=0;i<nw;i++) out[i] = (Q)(num_int_bits_elem(w,i)==0);
  }
  return z;
}

Q tl(B A,Q v,Q a,Q w){
  (void)v; (void)a;
  if(t(w)!=T_INT) return ae(2);

  // Scalar til: return the value vector directly (avoid transient container refs so rc stays 0).
  if(sh(w)==0){
    J nij = (J)ra(w);
    if(nij < 0) return ae(2);
    D ni = (D)nij;
    Q zi = vne_u(0, T_INT, 3, ni);
    Q* out = (Q*)p(zi);
    for(D j=0;j<ni;j++) out[j] = (Q)j;
    return zi;
  }

  // Vector til: return a list of value vectors.
  if(sh(w)!=1) return ae(1);
  D nw=n(w);
  Q z=lna(A,nw);
  for(D i=0;i<nw;i++){
    J nij = (J)pi(w,i);
    if(nij < 0) return ae(2);
    D ni = (D)nij;
    Q zi=vne_u(0, T_INT, 3, ni);
    Q* out = (Q*)p(zi);
    for(D j=0;j<ni;j++) out[j] = (Q)j;
    zid(z,i,zi);
  }
  return z;
}

Q at(B A,Q v,Q a,Q w){
  // Dictionary lookup: d@k
  if(ip(a) && t(a)==0 && sh(a)==2){
    if(ii(w)){
      Q r = dki(a, w);
      if(is_err(r)) return r;
      return r ? r : ac(4);
    }
    if(sh(w)==1){
      D nw=n(w);
      Q z = ln(nw);
      for(D i=0;i<nw;i++){
        Q ki = qi(w, i);
        Q r = dki(a, ki);
        if(is_err(r)) return r;
        zid(z, i, r ? r : ac(4));
      }
      return z;
    }
    return ae(1);
  }

  // Lambda introspection: lam@0 => params, lam@1 => body
  if(ip(a) && t(a)==T_LAMBDA && sh(a)==1 && n(a)==2){
    if(ii(w)){
      if(t(w)!=T_INT) return ae(2);
      J idx = (J)ra(w);
      if(idx<0 || idx>1) return ae(2);
      return pi(a, (D)idx);
    }
    if(sh(w)==1){
      D nw=n(w);
      Q z = ln(nw);
      for(D i=0;i<nw;i++){
        Q wi = qi(w, i);
        if(t(wi)!=T_INT) return ae(2);
        J idx = (J)ra(wi);
        if(idx<0 || idx>1) return ae(2);
        zid(z, i, pi(a, (D)idx));
      }
      return z;
    }
    return ae(1);
  }

  B aa=ii(a),aw=ii(w);B nz=n(w);
  if(aw){return aa?a:qi(a,ra(w));} // TODO: arena awareness
  Q z=vna(0,t(a),ls(a),nz);
  for(D i=0;i<nz;i++){ // unmerge this. use shape of w to dispatch. 
    Q zi=ri(a,aw?ra(w):ri(w,i));
    qid(z,i,zi);
  }
  return z;
}

Q pl(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_ADD, a, w); }
Q ml(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_MUL, a, w); }
Q mn(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_MIN, a, w); }
Q mx(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_MAX, a, w); }
Q eq(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_EQ, a, w); }
Q lt(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_LT, a, w); }
Q gt(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_GT, a, w); }
Q nd(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_BAND, a, w); }
Q or(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_BOR, a, w); }
Q xr(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_BXOR, a, w); }
Q sb(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_SUB, a, w); }
Q dvv(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_DIV, a, w); }   // /
Q md(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_MOD, a, w); }    // %
Q idv(B A,Q v,Q a,Q w){ (void)A; (void)v; return num_binop(NOP_FLOORDIV, a, w); } // div

static inline Q atom_payload_for_match(Q q){
  if(ip(q)) return pi(q, 0);
  B tq = t(q);
  if(tq==2 || tq==18 || tq==34 || tq==T_ERR) return q>>6; // grammatical atoms store payload above bit 6
  if(tq==3) return di_int(q);
  return di(q);
}

static B match_struct(Q a, Q w, D depth){
  if(a==w) return 1;
  if(!a || !w) return 0;
  if(depth > 1024) return 0;

  B ta=t(a), tw=t(w);
  if(ta!=tw) return 0;
  B sa=sh(a), sw=sh(w);
  if(sa!=sw) return 0;

  if(sa==0){
    return atom_payload_for_match(a) == atom_payload_for_match(w);
  }

  if(ls(a)!=ls(w)) return 0;
  D na=n(a), nw=n(w);
  if(na!=nw) return 0;

  // Dictionaries are structural: ignore internal hash table contents.
  if(sa==2 && ta==0){
    return match_struct(pi(a,1), pi(w,1), depth+1) && match_struct(pi(a,2), pi(w,2), depth+1);
  }

  // Lambdas are structural: compare fields.
  if(ta==T_LAMBDA){
    return match_struct(pi(a,0), pi(w,0), depth+1) && match_struct(pi(a,1), pi(w,1), depth+1);
  }

  // Pointer lists (and partial-eval sequences) compare recursively.
  if(ta==0 || ta==4){
    for(D i=0;i<na;i++){
      if(!match_struct(pi(a,i), pi(w,i), depth+1)) return 0;
    }
    return 1;
  }

  // Homogeneous value vectors: compare bytes (ignores capacity).
  return 0==memcmp(p(a), p(w), (size_t)na * (size_t)sz(a));
}

Q mt(B A,Q v,Q a,Q w){
  (void)A; (void)v;
  return an(match_struct(a, w, 0) ? 1 : 0);
}

Q bn(B A,Q v,Q a,Q w){
  (void)A; (void)v; (void)a;
  return int_bit_not(w);
}
Q ng(B A,Q v,Q a,Q w){
  (void)A; (void)v; (void)a;
  if(!is_num_type(t(w))) return ae(2);
  B sw=sh(w);
  if(sw==0){
    if(t(w)==T_FLT) return af(0, -num_f64_atom(w));
    Q bits = num_int_bits_atom(w);
    return an((J)(0 - bits));
  }
  if(sw!=1) return ae(1);
  D nw=n(w);
  if(t(w)==T_FLT){
    Q z=num_can_inplace_w_vec(w, T_FLT, nw) ? w : vne_u(0, T_FLT, 3, nw);
    Q* out = (Q*)p(z);
    for(D i=0;i<nw;i++) out[i] = f64_bits(-num_f64_elem(w,i));
    return z;
  }
  Q z=num_can_inplace_w_vec(w, T_INT, nw) ? w : vne_u(0, T_INT, 3, nw);
  Q* out = (Q*)p(z);
  for(D i=0;i<nw;i++) out[i] = 0 - num_int_bits_elem(w,i);
  return z;
}

static inline B is_dict(Q q){ return ip(q) && t(q)==0 && sh(q)==2; }
static inline B is_ptr_list(Q q){ return ip(q) && t(q)==0 && sh(q)==1; }
static inline B is_val_vec(Q q){ return ip(q) && sh(q)==1 && t(q)!=0 && t(q)!=4; }

static inline Q set_embed_kv(Q dest_dict, Q key, Q w, D sp){
  if(ip(w) && 0==t(w)){
    // Preserve identity for open-scope/list builders so later input continues mutating the same object.
    // Only do this when the destination lives in the same arena as the builder to avoid storing pointers
    // into an arena that may be reset.
    if(obj_ar(dest_dict) == obj_ar(w)){
      if(2==sh(w) && SP==sp+1 && SC[SP]==w){ dkv(dest_dict, key, w); return w; }
      if(1==sh(w) && LP>0 && NL[LP]==w){ dkv(dest_dict, key, w); return w; }
    }

    Q stack[64];
    Q wc = clone0_for_embed0(w, obj_ar(dest_dict), stack, 0);
    if(is_err(wc)) return wc;
    dkv(dest_dict, key, wc);
    return wc;
  }
  dkv(dest_dict, key, w);
  return w;
}

static Q container_set_scalar(Q container, Q idx, Q val){
  if(is_dict(container)){
    Q r = dkv(container, idx, val);
    if(is_err(r)) return r;
    return container;
  }

  if(is_ptr_list(container)){
    if(t(idx)!=T_INT || sh(idx)!=0) return ae(2);
    J ij = (J)ra(idx);
    if(ij < 0) return ae(2);
    D i = (D)ij;
    if(i >= n(container)) return ae(2);
    Q old = pi(container, i);
    ir(val);
    pid(container, i, val);
    dr(old);
    return container;
  }

  if(is_val_vec(container)){
    if(t(idx)!=T_INT || sh(idx)!=0) return ae(2);
    J ij = (J)ra(idx);
    if(ij < 0) return ae(2);
    D i = (D)ij;
    if(i >= n(container)) return ae(2);

    B tc = t(container);
    if(tc==T_INT){
      if(t(val)!=T_INT || sh(val)!=0) return ae(2);
      pid(container, i, ra(val));
      return container;
    }
    if(tc==T_FLT){
      if(t(val)!=T_FLT || sh(val)!=0) return ae(2);
      pid(container, i, ra(val));
      return container;
    }
    if(tc==T_CHAR){
      if(t(val)!=T_CHAR || sh(val)!=0) return ae(2);
      pid(container, i, ra(val));
      return container;
    }
    if(tc==T_SYM){
      if(t(val)!=T_SYM || sh(val)!=0) return ae(2);
      pid(container, i, ra(val));
      return container;
    }
    if(tc==T_TAG){
      if(t(val)!=T_TAG || sh(val)!=0) return ae(2);
      pid(container, i, ra(val));
      return container;
    }

    return ae(2);
  }

  return ae(2);
}

static Q container_set_in(Q container, Q idxs, D pos, D nidx, Q val){
  if(pos >= nidx) return val;
  Q idx = qi(idxs, pos);

  if(pos + 1 == nidx){
    return container_set_scalar(container, idx, val);
  }

  // Descend one level (create intermediate dicts on demand for dict containers).
  Q child = at(0, av(3), container, idx);
  if(is_err(child)) return child;
  if(is_nf(child)){
    if(is_dict(container)){
      Q nd = dni(0, 3, 0, obj_ar(container));
      Q r = dkv(container, idx, nd);
      if(is_err(r)) return r;
      child = nd;
    }else{
      return ae(2);
    }
  }

  Q updated_child = container_set_in(child, idxs, pos+1, nidx, val);
  if(is_err(updated_child)) return updated_child;

  Q updated_container = container_set_scalar(container, idx, updated_child);
  if(is_err(updated_container)) return updated_container;
  return updated_container;
}

static inline Q container_set_path(Q container, Q idxs, Q val){
  if(!idxs) return ae(2);
  if(ii(idxs)) return container_set_scalar(container, idxs, val);
  if(!is_ptr_list(idxs)) return ae(2);
  D nidx = n(idxs);
  if(nidx==0) return val; // x[]:v => replace x with v
  return container_set_in(container, idxs, 0, nidx, val);
}

Q set(Q a,Q w,D sp){
  Q d = SC[sp];

  // Indexed assignment: (ref; idxs) : w   where ref is a reference token and idxs is a flattened index list.
  if(is_ptr_list(a) && n(a)==2){
    Q ref = pi(a, 0);
    Q idxs = pi(a, 1);
    if(ref && t(ref)==1){

      // Resolve the parent dictionary + final key to update (creating dotref intermediate dicts if needed).
      Q parent = d;
      Q key = 0;

      if(sh(ref)==0){
        key = as(ra(ref));
      }else if(sh(ref)==1){
        D segc = n(ref);
        if(segc <= 0) return ae(2);

        Q base_key = as(pi(ref, 0));
        if(segc == 1){
          key = base_key;
        }else{
          Q cur = dki(d, base_key);
          if(is_err(cur)) return cur;
          if(!cur){
            Q nd = dni(0, 3, 0, obj_ar(d));
            dkv(d, base_key, nd);
            cur = nd;
          }
          if(!is_dict(cur)) return ae(2);

          for(D i=1;i<segc-1;i++){
            Q k = as(pi(ref, i));
            Q next = dki(cur, k);
            if(is_err(next)) return next;
            if(!next){
              Q nd = dni(0, 3, 0, obj_ar(cur));
              dkv(cur, k, nd);
              next = nd;
            }
            if(!is_dict(next)) return ae(2);
            cur = next;
          }

          parent = cur;
          key = as(pi(ref, segc-1));
        }
      }else{
        return ae(1);
      }

      Q base = dki(parent, key);
      if(is_err(base)) return base;
      if(!base) return ae(2);

      Q updated = container_set_path(base, idxs, w);
      if(is_err(updated)) return updated;
      Q r2 = dkv(parent, key, updated);
      if(is_err(r2)) return r2;
      return w;
    }
  }

  // Dotted reference assignment: a.b.c : w
  if(a && t(a)==1 && sh(a)==1){
    D segc = n(a);
    if(segc <= 0) return ae(2);

    Q base_key = as(pi(a, 0));
    if(segc == 1){
      return set_embed_kv(d, base_key, w, sp);
    }

    // Ensure base container exists in the current scope dict.
    Q cur = dki(d, base_key);
    if(is_err(cur)) return cur;
    if(!cur){
      Q nd = dni(0, 3, 0, obj_ar(d));
      dkv(d, base_key, nd);
      cur = nd;
    }
    if(!(ip(cur) && t(cur)==0 && sh(cur)==2)) return ae(2);

    // Create intermediate dicts as needed.
    for(D i=1;i<segc-1;i++){
      Q k = as(pi(a, i));
      Q next = dki(cur, k);
      if(is_err(next)) return next;
      if(!next){
        Q nd = dni(0, 3, 0, obj_ar(cur));
        dkv(cur, k, nd);
        next = nd;
      }
      if(!(ip(next) && t(next)==0 && sh(next)==2)) return ae(2);
      cur = next;
    }

    Q last_key = as(pi(a, segc-1));
    return set_embed_kv(cur, last_key, w, sp);
  }

  // Store bindings under symbol keys (not reference keys).
  if(1==t(a)) a = as(ra(a));
  return set_embed_kv(d, a, w, sp);
}

Q ca(B A,Q v,Q a,Q w){
  if(t(a)==9) return file_append(a,w);
  if (t(w)==9) w = file_read(w); // If w is a file, read its root

  B tz = (t(a)==t(w)) ? t(a) : 0;
  D j=0; D na=n(a), nw=n(w);
  Q z = vna(A, tz, tz ? ls(a) : 3, na+nw);
  for(D i=0;i<na;i++,j++){Q ai=at(A,av(3),a,an(i));qid(z,j,tz?ra(ai):ai);} // decode if not type 0
  for(D i=0;i<nw;i++,j++){Q wi=at(A,av(3),w,an(i));qid(z,j,tz?ra(wi):wi);} // decode if atom or somethig
  return z;
}

Q el(B A,Q v,Q a,Q w){return vb(A,v,a,w,LB,1);}
Q er(B A,Q v,Q a,Q w){return vb(A,v,a,w,RB,1);}
Q ed(B A,Q v,Q a,Q w){return vb(A,v,a,w,a?DB:MB,1);}
Q ov(B A,Q v,Q a,Q w){
  D nw=n(w),sw=sh(w);
  if(0==nw){return a?a:w;}
  if(0==sw && !a){return w;} 
  Q acc;D i=0;
  if(a){acc=a;}else{acc=qi(w,0);i=1;}
  for(;i<nw;i++){acc=dispatch(VD, VBD, v, acc, qi(w,i));}
  return acc;
}
Q sc(B A,Q v,Q a,Q w){
  D nw=n(w),sw=sh(w);
  if(0==nw){return a?a:w;}
  if(0==sw && !a){return w;} 
  D zn=a?nw+1:nw;Q z=ln(zn);
  Q acc;D i=0;D j=0;
  if(a){acc=a;zid(z,j++,acc);}else{acc=qi(w,0);zid(z,j++,acc);i=1;}
  for(;i<nw;i++){acc=dispatch(VD, VBD, v, acc, qi(w,i));zid(z,j++,acc);}
  return z;
}
Q lfa(B A,Q v,Q a,Q w){
  if(ii(w))return a?dispatch(VD, VBD, v, a, w):dispatch(VM, VBM, v, 0, w);
  D nw=n(w);Q z=ln(nw);
  for(D i=0;i<nw;i++){
    Q wi=qi(w,i);
    Q r=lfa(A,v,a,wi);
    zid(z,i,r);
  }
  return z;
}
Q lvs(B A,Q v,Q a,Q w){
  if(a)return ae(2);
  Q h=dispatch(VM, VBM, v, 0, w);
  if(ii(w)){Q z=ln(1);zid(z,0,h);return z;}
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
  if(!a)return dispatch(VM, VBM, v, 0, w);
  D d=di(a);
  if(0==d)return dispatch(VM, VBM, v, 0, w);
  if(ii(w))return dispatch(VM, VBM, v, 0, w);
  D nw=n(w);Q z=ln(nw);
  for(D i=0;i<nw;i++){
    Q r=lvl(A,v,an(d-1),qi(w,i));
    zid(z,i,r);
  }
  return z;
}
Q lsl(B A,Q v,Q a,Q w){
  D limit=a?di(a):0;
  Q h=dispatch(VM, VBM, v, 0, w);
  if(0==limit||ii(w)){Q z=ln(1);zid(z,0,h);return z;}
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
  if(!a)return ae(2);
  D n=di(a);
  Q r=w;
  for(D i=0;i<n;i++){
    Q next=dispatch(VM, VBM, v, 0, r);
    if(r!=w && r!=next)dr(r);
    r=next;
  }
  return r;
}
Q its(B A,Q v,Q a,Q w){
  if(!a)return ae(2);
  D n=di(a);
  Q z=ln(n+1);
  Q r=w;
  zid(z,0,r);
  for(D i=0;i<n;i++){
    r=dispatch(VM, VBM, v, 0, r);
    zid(z,i+1,r);
  }
  return z;
}

Q lg(B A, Q v, Q a, Q w);
Q rl(B A, Q v, Q a, Q w);
Q mt(B A, Q v, Q a, Q w);
Q arena(B A, Q v, Q a, Q w);
Q lex(B A, Q v, Q a, Q w);
Q lex2(B A, Q v, Q a, Q w);
Q mxcsr(B A, Q v, Q a, Q w);
Q setmxcsr(B A, Q v, Q a, Q w);
Q ticks(B A, Q v, Q a, Q w);
Q ev(B A, Q v, Q a, Q w);
Q bench(B A, Q v, Q a, Q w);
Q aply(B A, Q v, Q a, Q w);
VF VD[VTZ]={0,mt,0,at,0,pl,ml,0,ca,mn,mx,eq,lt,gt,xr,nd,or,0,sb,sv,0,0,0,lg,0,dvv,md,idv,0,0,0,0,0,aply,0,0,0,textd,0};
VF VM[VTZ]={0,nt,tl,tp,ct,0,car,id,en,0,0,0,0,0,0,0,0,bn,ng,0,ld,fl,0,0,rl,0,0,0,mxcsr,setmxcsr,ticks,bench,ev,0,arena,lex,lex2,textm,reprm};

static const BM VBM[VTZ]={
  /*  0 */ NB,
  /*  1 */ MB, // ~
  /*  2 */ NB, // !
  /*  3 */ NB, // @
  /*  4 */ NB, // #
  /*  5 */ NB, // +
  /*  6 */ NB, // *
  /*  7 */ NB, // :
  /*  8 */ NB, // ,
  /*  9 */ NB, // &
  /* 10 */ NB, // |
  /* 11 */ NB, // =
  /* 12 */ NB, // <
  /* 13 */ NB, // >
  /* 14 */ NB, // ^
  /* 15 */ NB, // and
  /* 16 */ NB, // or
  /* 17 */ MB, // bnot
  /* 18 */ MB, // - (negate)
  /* 19 */ NB, // save
  /* 20 */ NB, // load
  /* 21 */ NB, // file
  /* 22 */ NB, // root
  /* 23 */ NB, // log
  /* 24 */ NB, // readlog
  /* 25 */ NB, // / (unimplemented monad)
  /* 26 */ NB, // % (unimplemented monad)
  /* 27 */ NB, // div (unimplemented monad)
  /* 28 */ NB, // mxcsr
  /* 29 */ NB, // setmxcsr
  /* 30 */ NB, // ticks
  /* 31 */ NB, // bench
  /* 32 */ NB, // eval
  /* 33 */ NB, // apply
  /* 34 */ NB, // arena
  /* 35 */ NB, // lex
  /* 36 */ NB, // lex2
  /* 37 */ NB, // text
  /* 38 */ NB, // repr
};

static const BM VBD[VTZ]={
  /*  0 */ NB,
  /*  1 */ NB, // ~
  /*  2 */ NB, // !
  /*  3 */ NB, // @ (handled explicitly in at(); do not implicitly lift boxed keys/indices)
  /*  4 */ NB, // #
  /*  5 */ DB, // +
  /*  6 */ DB, // *
  /*  7 */ NB, // :
  /*  8 */ NB, // ,
  /*  9 */ DB, // &
  /* 10 */ DB, // |
  /* 11 */ DB, // =
  /* 12 */ DB, // <
  /* 13 */ DB, // >
  /* 14 */ DB, // ^
  /* 15 */ DB, // and
  /* 16 */ DB, // or
  /* 17 */ NB, // bnot
  /* 18 */ DB, // -
  /* 19 */ NB, // save
  /* 20 */ NB, // load
  /* 21 */ NB, // file
  /* 22 */ NB, // root
  /* 23 */ NB, // log
  /* 24 */ NB, // readlog
  /* 25 */ DB, // /
  /* 26 */ DB, // %
  /* 27 */ DB, // div
  /* 28 */ NB, // mxcsr
  /* 29 */ NB, // setmxcsr
  /* 30 */ NB, // ticks
  /* 31 */ NB, // bench
  /* 32 */ NB, // eval
  /* 33 */ NB, // apply
  /* 34 */ NB, // arena
  /* 35 */ NB, // lex
  /* 36 */ NB, // lex2
  /* 37 */ NB, // text
  /* 38 */ NB, // repr
};
C* VT[VTZ]={" ","~","!","@","#","+","*",":",",","&","|","=","<",">","^","and","or","bnot","-","save","load","file","root","log","readlog","/","%","div","mxcsr","setmxcsr","ticks","bench","eval","apply","arena","lex","lex2","text","repr"}; // LATER: (grow width:sign/zero extend sx sx) (shift sl sar sr) WAY LATER: Expose comparison flags directly instead of hiding them. 

VF AV[ATZ]={0  ,ed ,sc ,ov ,el ,er ,lvs,lfa,0  ,0  ,lvl,lsl,itr,its};
C* AT[ATZ]={" ","'","→","←","↰","↱","↓","↑","↺","↻","↿","⇃","↫","↬"};

Q dispatch(VF* Vtab, const BM* Btab, Q v, Q a, Q w){
  Q r=dv(v);
  if(r<VTZ){
    BM m = Btab ? Btab[r] : NB;
    if(m!=NB && vb_need_for(m, a, w)) return vb(0, v, a, w, m, -1);
    return apply_raw(Vtab, v, a, w);
  }
  return apply_raw(Vtab, v, a, w);
}

Q lg(B A, Q v, Q a, Q w){
  Q f = fl(0, 0, 0, a);
  if(is_err(f)) return f;
  if(t(f) != 9) return ae(2);
  return file_log(f, w);
}
Q rl(B A, Q v, Q a, Q w){
  Q f = fl(A, v, 0, w);
  if(is_err(f)) return f;
  if(t(f) != 9) return ae(2);
  return file_read_log(f);
}

Q mxcsr(B A, Q v, Q a, Q w){
  (void)A; (void)v; (void)a; (void)w;
#if HAVE_MXCSR
  return an((J)(D)_mm_getcsr());
#else
  return ae(2);
#endif
}

Q setmxcsr(B A, Q v, Q a, Q w){
  (void)A; (void)v; (void)a;
#if HAVE_MXCSR
  if(t(w)!=T_INT || sh(w)!=0) return ae(2);
  J val = (J)ra(w);
  if(val < 0 || (Q)val > 0xFFFFFFFFULL) return ae(2);
  D old = (D)_mm_getcsr();
  _mm_setcsr((D)val);
  return an((J)old);
#else
  (void)w;
  return ae(2);
#endif
}

Q ticks(B A, Q v, Q a, Q w){
  (void)A; (void)v; (void)a; (void)w;
  return an((J)now_ns_u64());
}

Q arena(B A, Q v, Q a, Q w){
  (void)A; (void)v; (void)a; (void)w;
  printf("AB[0] AC[0] AI[0] %lld %lld %lld\n", (long long)AB[0], (long long)AC[0], (long long)AI[0]);
  printf("AB[1] AC[1] AI[1] %lld %lld %lld\n", (long long)AB[1], (long long)AC[1], (long long)AI[1]);
  return tsna(0,4,1,3,0,0); // missing (print-only)
}


Q* lx_len(const C* b, D l);
Q* lx2_len(const C* b, D l);

static Q toks_tape_to_list(Q* toks){
  if(!toks) return ae(2);
  D nt=0;
  while(toks[nt]) nt++;
  Q z = ln(nt);
  for(D i=0;i<nt;i++) zid(z, i, toks[i]);
  os_heap_free(toks);
  return z;
}

static Q lex_from_src(const C* src, D len, B use_new_lexer){
  if(!src) return ae(2);
  Q* toks = use_new_lexer ? lx2_len(src, len) : lx_len(src, len);
  return toks_tape_to_list(toks);
}

static inline Q qchar_src(Q w, const C** src_out, D* len_out, C* one_out){
  if(!src_out || !len_out || !one_out) return ae(2);
  if(t(w)!=6) return ae(2);
  if(sh(w)==0){
    *one_out = (C)ra(w);
    *src_out = one_out;
    *len_out = 1;
    return 0;
  }
  if(sh(w)!=1) return ae(1);
  *src_out = (const C*)p(w);
  *len_out = n(w);
  return 0;
}

Q lex(B A, Q v, Q a, Q w){
  (void)A; (void)v; (void)a;
  const C* src = 0; D len = 0; C one = 0;
  Q err = qchar_src(w, &src, &len, &one);
  if(err) return err;
  return lex_from_src(src, len, 0);
}

Q lex2(B A, Q v, Q a, Q w){
  (void)A; (void)v; (void)a;
  const C* src = 0; D len = 0; C one = 0;
  Q err = qchar_src(w, &src, &len, &one);
  if(err) return err;
  return lex_from_src(src, len, 1);
}

Q ev(B A, Q v, Q a, Q w){
  (void)A; (void)v; (void)a;
  const C* src = 0; D len = 0; C one = 0;
  Q err = qchar_src(w, &src, &len, &one);
  if(err) return err;
  return eval_code_tape(src, len);
}

Q bench(B A, Q v, Q a, Q w){
  (void)A; (void)v; (void)a;
  if(!ip(w) || t(w)!=0 || sh(w)!=1) return ae(2);
  D nw = n(w);
  enum { BENCH_F_ARENA0_PEAK = 1 };
  if(nw<2 || nw>4) return ae(2);

  Q qn = qi(w, 0);
  if(t(qn)!=T_INT || sh(qn)!=0) return ae(2);
  J iters_j = (J)ra(qn);
  if(iters_j < 0 || iters_j > 0x7FFFFFFF) return ae(2);
  D iters = (D)iters_j;

  Q verb = 0;
  Q code = 0;
  Q w1 = qi(w, 1);
  B eval_mode = (t(w1)==6);
  Q flags = 0;
  if(eval_mode){
    code = w1;
    if(!(sh(code)==0 || sh(code)==1)) return ae(1);
    if(nw==3){
      flags = qi(w, 2);
      if(t(flags)!=T_INT || sh(flags)!=0) return ae(2);
      flags = ra(flags);
    }else{
      flags = 0;
    }
  }else{
    if(nw!=3 && nw!=4) return ae(2);
    verb = w1;
    if(t(verb)==4){
      if(!ip(verb) || sh(verb)!=1 || n(verb)!=1) return ae(2);
      verb = pi(verb, 0);
    }
    if(t(verb)!=2) return ae(2);
  }

  B is_dyad = (!eval_mode && nw==4);
  Q alpha = 0;
  Q omega = 0;
  if(!eval_mode){
    if(is_dyad){
      alpha = qi(w, 2);
      omega = qi(w, 3);
    }else{
      omega = qi(w, 2);
    }
  }

  Q start = now_ns_u64();
  Q last = tsna(0,4,1,3,0,0); // missing
  Q ai0_peak_units = 0;
  for(D i=0;i<iters;i++){
    // Rewind temp arena allocations each iteration (except the last) so benchmarks
    // don't measure unbounded bump growth / page commits.
    Q ai0_before = AI[0];
    Q r;
    if(eval_mode){
      if(sh(code)==0){
        C c = (C)ra(code);
        r = eval_code_tape(&c, 1);
      }else{
        r = eval_code_tape((const C*)p(code), n(code));
      }
    }else{
      r = is_dyad ? dispatch(VD, VBD, verb, alpha, omega) : dispatch(VM, VBM, verb, 0, omega);
    }
    Q ai0_used = AI[0] - ai0_before;
    if(ai0_used > ai0_peak_units) ai0_peak_units = ai0_used;
    if(i+1 < iters){
      ir(r);
      dr(r);
      AI[0] = ai0_before;
    }else{
      last = r;
    }
  }
  Q end = now_ns_u64();

  if(eval_mode && (flags & (Q)BENCH_F_ARENA0_PEAK)){
    Q z = ln(4);
    zid(z, 0, an((J)(end - start)));
    zid(z, 1, last);
    zid(z, 2, an((J)ai0_peak_units));
    zid(z, 3, an((J)(ai0_peak_units * (Q)BUMP_UNIT_BYTES)));
    return z;
  }else{
    Q z = ln(2);
    zid(z, 0, an((J)(end - start)));
    zid(z, 1, last);
    return z;
  }
}

static inline B is_lambda_obj(Q q);
Q E(Q** q, C tc, B capture);

Q aply(B A, Q v, Q a, Q w){
  (void)A; (void)v;

  // Allow applying partial-wrapped verbs (e.g. p:+; p apply (2;3)).
  if(t(a)==4){
    if(!ip(a) || sh(a)!=1 || n(a)!=1) return ae(2);
    a = pi(a, 0);
  }

  B w_is_list = ip(w) && t(w)==0 && sh(w)==1;
  D nw = w_is_list ? n(w) : 1;

  // Apply a verb.
  if(t(a)==2){
    if(nw==1){
      Q omega = w_is_list ? qi(w, 0) : w;
      return dispatch(VM, VBM, a, 0, omega);
    }
    if(nw==2){
      Q alpha = qi(w, 0);
      Q omega = qi(w, 1);
      return dispatch(VD, VBD, a, alpha, omega);
    }
    return ae(2);
  }

  // Apply a lambda.
  if(is_lambda_obj(a)){
    Q params = pi(a, 0);
    Q body = pi(a, 1);
    if(!ip(params) || t(params)!=T_SYM || sh(params)!=1){
      return ae(2);
    }
    if(!ip(body) || t(body)!=0 || sh(body)!=1){
      return ae(2);
    }
    D np = n(params);

    if(!w_is_list){
      if(np!=1){
        return ae(2);
      }
    }else{
      if((D)nw!=np){
        return ae(2);
      }
    }

    if(SP+1 >= 1024) return ae(99);
    SP++;
    SC[SP] = dn(0,3,0,0);

    for(D i=0;i<np;i++){
      Q key = as(pi(params, i));
      Q val = w_is_list ? qi(w, i) : w;
      dkv(SC[SP], key, val);
    }

    D nt = n(body);
    Q tape_small[256];
    Q* tape = tape_small;
    if(nt + 1ULL > (D)(sizeof(tape_small)/sizeof(tape_small[0]))){
      tape = (Q*)os_heap_alloc((Q)(nt + 1ULL) * (Q)sizeof(Q));
      if(!tape){ if(SP>0) SP--; return ae(2); }
    }
    for(D i=0;i<nt;i++) tape[i] = pi(body, i);
    tape[nt] = 0;
    Q* tp = tape;
    Q r = E(&tp, '\0', 0);
    if(tape != tape_small) os_heap_free(tape);

    if(SP>0) SP--;
    return r;
  }

  return ae(2);
}

Q Ap(Q a){Q p=tsna(0,4,1,3,1,1);pid(p,0,a);return p;}
Q e(Q** q);
Q E(Q** q,C tc, B capture);
Q ecl(Q** q);

static inline Q apply_index_over(Q base, Q idxs){
  // Syntax sugar for: @<-(base; idx0; idx1; ...)
  // (Derived verb: '@' with adverb id 3 ('←') => fold/over.)
  D ni = ii(idxs) ? 1 : n(idxs);
  Q args = ln(ni + 1);
  zid(args, 0, base);
  if(ii(idxs)){
    zid(args, 1, idxs);
  }else{
    for(D i=0;i<ni;i++) zid(args, i+1, qi(idxs, i));
  }
  Q v = derive_verb(av(3), aa(3)); // '@' is VT[3], '←' is AT[3]
  return dispatch(VM, VBM, v, 0, args);
}

static inline B is_bracket_call_target(Q base){
  // Allow f[...] to call when f is callable.
  // - lambdas (T_LAMBDA)
  // - verbs (t==2)
  // - partial-wrapped verbs (t==4) (aply unwraps)
  B tb = t(base);
  return (tb==T_LAMBDA) || (tb==2) || (tb==4);
}

static inline Q apply_brackets(Q base, Q args){
  // If base is callable, treat postfix [...] as a call: base apply args.
  // Otherwise treat it as indexing sugar: @<-(base; args...).
  if(is_bracket_call_target(base)) return aply(0, 0, base, args);
  return apply_index_over(base, args);
}

Q eoc(Q** q){
  (*q)++;                                                                      // consume '{'
  if(SP+1 >= 1024) return ae(99);                                              // scope depth overflow
  SP++;D csp=SP;                                                               // cache the SP of this new allocation, return that.
  SC[SP] = dn(0,3,0,0);                                                        // Allocate new dictionary for the new scope
  (void)E(q,'}',0);                                                            // Evaluate until '}' or end-of-stream
  if(**q && 34==t(**q) && '}'==dc(**q)){                                       // If '}' is present, consume it and close the scope.
    (*q)++;
    Q d = SC[csp];
    if(SP>0) SP--;
    return d;
  }
  return SC[csp];                                                              // Leave the scope open across end-of-stream.
}

Q ecc(Q** q){
  (*q)++;                                                                      // consume '}'
  if(SP==0) return ae(2);
  Q d=SC[SP];
  SP--;
  return d;
}

Q eol(Q** q){
  (*q)++;                                                                      // consume '('
  if(LP+1 >= 1024) return ae(99);
  LP++;D clp=LP;
  NL[LP] = vca(0, 0, 3, 64);
  LC[LP] = ')';
  LK[LP] = 0;
  LBASE[LP] = 0;
  LSEP[LP] = 0;
  (void)E(q,')',1);                                                            // Evaluate until ')' or end-of-stream, appending values.
  if(**q && 34==t(**q) && ')'==dc(**q)){                                       // If ')' is present, consume it and close the list.
    return ecl(q);
  }
  return NL[clp];                                                              // Leave the list open across end-of-stream.
}

Q eob(Q** q){
  // Bracket block: evaluate in the current scope and return the last statement value.
  (*q)++;                                                                      // consume '['
  Q r = E(q,']',0);                                                            // Evaluate until ']' or end-of-stream (no capture).
  if(**q && 34==t(**q) && ']'==dc(**q)) (*q)++;                                // consume ']'
  return r;
}

Q eib(Q base, Q** q){
  (*q)++;                                                                      // consume '[' (postfix indexing)
  if(LP+1 >= 1024) return ae(99);
  LP++;
  NL[LP] = vca(0, 0, 3, 64);
  LC[LP] = ']';
  LK[LP] = 1;
  LBASE[LP] = base; ir(base);
  LSEP[LP] = 0;
  (void)E(q,']',1);                                                            // Evaluate until ']' or end-of-stream, appending indices.
  if(**q && 34==t(**q) && ']'==dc(**q)){
    return ecl(q);                                                             // close + apply index
  }
  // Unbalanced '[': keep builder open for future input.
  return apply_brackets(LBASE[LP], NL[LP]);
}

static Q eix(Q** q){
  // Capture-only postfix indexing list: parse `[...]` into a list of evaluated indices without applying.
  (*q)++;                                                                      // consume '['
  if(LP+1 >= 1024) return ae(99);
  LP++;
  NL[LP] = vca(0, 0, 3, 64);
  LC[LP] = ']';
  LK[LP] = 2;
  LBASE[LP] = 0;
  LSEP[LP] = 0;
  (void)E(q,']',1);
  if(**q && 34==t(**q) && ']'==dc(**q)){
    return ecl(q);
  }
  // Unbalanced '[': keep builder open; return current captured indices.
  return NL[LP];
}

Q ecl(Q** q){
  // Close the most recent open list builder, or postfix index builder.
  Q a = **q;
  if(!a || 34!=t(a)) return ae(2);
  C close_tc = (C)dc(a);
  (*q)++;                                                                      // consume the close token
  if(LP==0) return ae(2);
  if(LC[LP] && close_tc != LC[LP]) return ae(2);

  Q l = NL[LP];
  B kind = LK[LP];
  Q base = LBASE[LP];
  B saw_sep = LSEP[LP];

  LC[LP] = 0;
  LK[LP] = 0;
  LBASE[LP] = 0;
  LSEP[LP] = 0;
  LP--;

  if(kind==0){
    // Delistify: treat `(expr)` as grouping if it contains no list separators on this line.
    // Singleton lists can still be created via enlist: `,expr`.
    if(close_tc==')' && !saw_sep && n(l)==1){
      // The list builder stores the single element via `zid`, which bumps its refcount.
      // Grouping parentheses are not a semantic container, so detach the element from the
      // temporary list and undo that refcount bump.
      Q r0 = pi(l, 0);
      pid(l, 0, 0);
      if(ip(r0)){
        Q* hr0 = ptr(r0);
        if(hr0[3]) hr0[3]--;
      }
      return r0;
    }
    return l;
  }
  if(kind==1){
    Q r = apply_brackets(base, l);
    dr(base);
    return r;
  }
  // kind==2: capture-only indexing list
  return l;
}

static inline B is_missing(Q q){ return q && 4==t(q) && 0==n(q); }
static inline B truthy(Q q){
  if(!q) return 0;
  if(is_missing(q)) return 0;
  if(t(q)==T_INT && sh(q)==0) return ra(q)!=0;
  if(t(q)==T_FLT && sh(q)==0){
    double x = f64_from_bits(ra(q));
    return x!=0.0;
  }
  return 1;
}

static inline B is_if_ref(Q q){
  return q && t(q)==1 && sh(q)==0 && SYM_PAY_IF && ra(q)==SYM_PAY_IF;
}

static inline Q eval_slice(Q* start, Q* end){
  Q saved = *end;
  *end = 0;
  Q* tp = start;
  Q r = E(&tp, '\0', 0);
  *end = saved;
  return r;
}

static Q eif(Q** q){
  // Special-form: if[cond;then;cond;then;...;else]
  // - Lazy: only the selected branch is evaluated.
  // - Branch expressions may be blocks via `[...]` (same scope) or `{...}` (new scope).
  (*q)++; // consume `if`
  if(!(**q && 34==t(**q) && '['==(C)dc(**q))) return ae(2);
  (*q)++; // consume '['

  enum { IF_MAX_SEGS = 256 };
  Q* seg_s[IF_MAX_SEGS];
  Q* seg_e[IF_MAX_SEGS];
  D segc = 0;

  Q* start = *q;
  D depth = 0;
  for(;;){
    Q tok = **q;
    if(!tok) return ae(2); // missing closing ']'

    if(34==t(tok)){
      C c = (C)dc(tok);

      // Top-level separators split segments.
      if(depth==0 && (c==';' || c=='\n')){
        if(segc >= IF_MAX_SEGS) return ae(99);
        seg_s[segc] = start;
        seg_e[segc] = *q;
        segc++;
        (*q)++; // consume separator
        while(**q && 34==t(**q) && (((C)dc(**q))==';' || ((C)dc(**q))=='\n')) (*q)++;
        start = *q;
        continue;
      }

      // Track nesting so we don't split inside nested blocks/lists.
      if(c=='{' || c=='(' || c=='['){ depth++; (*q)++; continue; }
      if(c=='}' || c==')' || c==']'){
        if(c==']' && depth==0){
          if(segc >= IF_MAX_SEGS) return ae(99);
          seg_s[segc] = start;
          seg_e[segc] = *q;
          segc++;
          (*q)++; // consume ']'
          break;
        }
        if(depth>0) depth--;
        (*q)++;
        continue;
      }
    }

    (*q)++;
  }

  if(segc < 2) return ae(2);

  D pair_count = segc / 2;
  B has_else = (segc & 1) ? 1 : 0;

  for(D i=0;i<pair_count;i++){
    Q cond = eval_slice(seg_s[i*2], seg_e[i*2]);
    if(is_err(cond)) return cond;
    if(truthy(cond)){
      Q thenv = eval_slice(seg_s[i*2+1], seg_e[i*2+1]);
      return thenv;
    }
  }

  if(has_else){
    Q elsev = eval_slice(seg_s[segc-1], seg_e[segc-1]);
    return elsev;
  }

  return tsna(0,4,1,3,0,0); // missing
}

static inline B is_lambda_obj(Q q){
  return ip(q) && t(q)==T_LAMBDA && sh(q)==1 && n(q)==2;
}

static Q elam(Q** q){
  // Lambda: {[a;b;...] body}
  // Stores (heap type T_LAMBDA): (params_symvec; body_token_list)
  if(!(**q && 34==t(**q) && '{'==(C)dc(**q))) return ae(2);
  (*q)++; // consume '{'

  if(!(**q && 34==t(**q) && '['==(C)dc(**q))) return ae(2);
  (*q)++; // consume '['

  // Parse parameter list: refs/symbols separated by ';' or newlines.
  Q tmp_params[64];
  Q* params = tmp_params;
  D nparams = 0;
  D cap = (D)(sizeof(tmp_params)/sizeof(tmp_params[0]));
  for(;;){
    Q tok = **q;
    if(!tok) return ae(2);
    if(34==t(tok)){
      C c = (C)dc(tok);
      if(c==';' || c=='\n'){ (*q)++; continue; }
      if(c==']'){ (*q)++; break; }
      return ae(2);
    }
    if(t(tok)==1){
      Q payload = ra(tok);
      if(nparams >= cap){
        D new_cap = cap + (cap>>1) + 8;
        Q* np = (Q*)os_heap_alloc((Q)new_cap * (Q)sizeof(Q));
        if(!np) return ae(2);
        memcpy(np, params, (size_t)cap * sizeof(Q));
        if(params != tmp_params) os_heap_free(params);
        params = np;
        cap = new_cap;
      }
      params[nparams++] = payload;
      (*q)++;
      continue;
    }
    if(t(tok)==T_SYM){
      Q payload = ra(tok);
      if(nparams >= cap){
        D new_cap = cap + (cap>>1) + 8;
        Q* np = (Q*)os_heap_alloc((Q)new_cap * (Q)sizeof(Q));
        if(!np) return ae(2);
        memcpy(np, params, (size_t)cap * sizeof(Q));
        if(params != tmp_params) os_heap_free(params);
        params = np;
        cap = new_cap;
      }
      params[nparams++] = payload;
      (*q)++;
      continue;
    }
    return ae(2);
  }

  Q params_vec = vna(0, T_SYM, 3, nparams);
  for(D i=0;i<nparams;i++) pid(params_vec, i, params[i]);
  if(params != tmp_params) os_heap_free(params);

  // Capture body tokens until matching '}' (no unbalanced support).
  Q* body_start = *q;
  D depth = 0;
  for(;;){
    Q tok = **q;
    if(!tok) return ae(2);
    if(34==t(tok)){
      C c = (C)dc(tok);
      if(c=='{' || c=='(' || c=='['){ depth++; (*q)++; continue; }
      if(c=='}' || c==')' || c==']'){
        if(c=='}' && depth==0) break;
        if(depth>0) depth--;
        (*q)++; continue;
      }
    }
    (*q)++;
  }
  Q* body_end = *q; // points at closing '}'

  D ntok = (D)(body_end - body_start);
  Q body = ln(ntok);
  for(D i=0;i<ntok;i++) zid(body, i, body_start[i]);

  if(!(**q && 34==t(**q) && '}'==(C)dc(**q))) return ae(2);
  (*q)++; // consume '}'

  Q lam = tsna(0, T_LAMBDA, 1, 3, 2, 2);
  zid(lam, 0, params_vec);
  zid(lam, 1, body);
  return lam;
}

Q emv(Q** q){
  Q v=*(*q)++;
  while(18==t(**q)){v=derive_verb(v,*(*q)++);}
  Q w=e(q);
  if(is_err(w)) return w;
  if(4==t(w)){Q p=tsna(0,4,1,3,1,1);pid(p,0,v);return ca(0,av(8),p,w);}
  Q r=dispatch(VM, VBM, v, 0, w);
  return r;
}

static inline Q resolve_ref(Q env, Q ref);

Q edv(Q a,Q** q){
  D current_sp = SP;Q v=*(*q)++;
  while(18==t(**q)){v=derive_verb(v,*(*q)++);}                                                         // Cache the scope pointer before evaluating the right-hand side.
  Q w=e(q);
  if(is_err(w)) return w;
  if(4==t(w)&&(7!=dv(v))){Q p=tsna(0,4,1,3,2,2);pid(p,0,a);pid(p,1,v);return ca(0,av(8),p,w);}  // handle partial evaluations but allow assignment of them instantly. 
  if((1==t(a)) && (7!=dv(v))) a = resolve_ref(SC[current_sp], a);
  if(is_err(a)) return a;
  if(7==dv(v)){return set(a,w,current_sp);}                                     // If this is an assignment, use the cached scope pointer to write into the correct scope.
  Q r=dispatch(VD, VBD, v, a, w);
  return r;
}

static inline Q resolve_dotref(Q env, Q dotref){
  if(!dotref || t(dotref)!=1 || sh(dotref)!=1) return ae(2);
  D segc = n(dotref);
  if(segc <= 0) return ae(2);

  // First segment is an environment lookup; the rest are literal symbol keys applied via dyadic '@'.
  Q base_ref = ar(pi(dotref, 0));
  Q cur = dk(env, base_ref);
  if(is_err(cur) || is_nf(cur)) return cur;

  for(D i=1;i<segc;i++){
    Q key = as(pi(dotref, i));
    cur = at(0, av(3), cur, key);
    if(is_err(cur) || is_nf(cur)) return cur;
  }
  return cur;
}

static inline Q resolve_ref(Q env, Q ref){
  if(!ref || t(ref)!=1) return ref;
  if(sh(ref)==0) return dk(env, ref);
  if(sh(ref)==1) return resolve_dotref(env, ref);
  return ae(1);
}

Q E(Q** q, C tc, B capture){
  Q missing = tsna(0,4,1,3,0,0);                                                  // "missing" sentinel
  Q r = missing;                                                                  // last statement result (or missing)
  D clp=LP;                                                                       // capture the list builder index for this call
  for(;;){
    Q a = **q;
    if(!a) break;
    if(tc && 34==t(a) && tc==dc(a)) break;
    if(34==t(a) && (';'==dc(a) || '\n'==dc(a))){
      if(capture && LP>0 && LK[LP]==0) LSEP[LP]=1;
      (*q)++;
      continue;
    }                                                                              // ignore empty statements
    r=e(q);                                                                        // e() consumes exactly one expression
    if(is_err(r)) return r;
    if(capture && !(4==t(r) && 0==n(r))){                                          // capture (skip "missing")
      Q v = r;
      if(ip(r) && 0==t(r)){
        Q stack[64];
        Q vc = clone0_for_embed0(r, obj_ar(NL[clp]), stack, 0);
        if(is_err(vc)) return vc;
        v = vc;
      }

      Q l=NL[clp];D idx=n(l);
      Q l2=xn(l,1); if(is_err(l2)) return l2; if(l2!=l) NL[clp]=l2;
      zid(NL[clp],idx,v);
    }
    if(**q && 34==t(**q) && (';'==dc(**q) || '\n'==dc(**q))){                      // consume statement terminator if present
      C sep = (C)dc(**q);
      if(capture && LP>0 && LK[LP]==0) LSEP[LP]=1;
      (*q)++;
      if(sep==';') r = missing;                                                   // trailing ';' suppresses the statement result
    }
  }
  return r;
}

Q e(Q** q){
  Q a=**q;
  if(!a) return tsna(0,4,1,3,0,0);                                              // missing
  if(is_err(a)){ (*q)++; return a; }
  if(34==t(a)){
    C c = (C)dc(a);
    if(';'==c || '\n'==c){(*q)++; return tsna(0,4,1,3,0,0);}                     // terminator => missing
    if('{'==c){
      Q next = (*q)[1];
      Q noun = (next && 34==t(next) && '['==(C)dc(next)) ? elam(q) : eoc(q);
      while(**q && 34==t(**q) && '['==(C)dc(**q)) noun = eib(noun, q);          // postfix indexing
      Q w = **q;
      B end = !w || (34==t(w) && (';'==dc(w) || '\n'==dc(w) || '}'==dc(w) || ')'==dc(w) || ']'==dc(w)));
      if(!end && w && 2==t(w)) return edv(noun, q);                              // allow `{...}v w`
      return noun;
    }
    if('('==c){
      Q noun = eol(q);
      while(**q && 34==t(**q) && '['==(C)dc(**q)) noun = eib(noun, q);          // postfix indexing
      Q w = **q;
      B end = !w || (34==t(w) && (';'==dc(w) || '\n'==dc(w) || '}'==dc(w) || ')'==dc(w) || ']'==dc(w)));
      if(!end && w && 2==t(w)) return edv(noun, q);                              // allow `(a;b)v w`
      return noun;
    }
    if('['==c){
      Q noun = eob(q);
      while(**q && 34==t(**q) && '['==(C)dc(**q)) noun = eib(noun, q);          // postfix indexing
      Q w = **q;
      B end = !w || (34==t(w) && (';'==dc(w) || '\n'==dc(w) || '}'==dc(w) || ')'==dc(w) || ']'==dc(w)));
      if(!end && w && 2==t(w)) return edv(noun, q);
      return noun;
    }
    if('}'==c) return ecc(q);
    if(')'==c) return ecl(q);
    if(']'==c) return ecl(q);
  }

  // Special form: if[cond;then;...;else]
  if(is_if_ref(a)){
    Q w0 = (*q)[1];
    if(w0 && 34==t(w0) && '['==(C)dc(w0)){
      Q noun = eif(q);
      if(is_err(noun)) return noun;
      while(**q && 34==t(**q) && '['==(C)dc(**q)) noun = eib(noun, q);          // postfix indexing
 
      Q v = **q;
      Q w2 = v ? (*q)[1] : 0;
      B end2 = !w2 || (34==t(w2) && (';'==dc(w2) || '\n'==dc(w2) || '}'==dc(w2) || ')'==dc(w2) || ']'==dc(w2)));
      if(v && 2==t(v) && !end2) return edv(noun, q);
      return noun;
    }
  }

  Q w=(*q)[1];                                                                   // safe: token streams are 0-terminated
  B end = !w || (34==t(w) && (';'==dc(w) || '\n'==dc(w) || '}'==dc(w) || ')'==dc(w) || ']'==dc(w)));

  if(2==t(a) && !end) return emv(q);                                             // monadic verb chain
  if(2==t(a) && end){(*q)++; return Ap(a);}                                      // partial at end-of-expression

  if(!end && w && 2==t(w)){(*q)++; return edv(a, q);}                            // dyadic a v w...

  (*q)++;                                                                        // consume noun/reference

  // Lvalue support: x[...]:v and a.b.c[...]:v
  // If we see postfix brackets after a reference, we may need to avoid applying them eagerly so
  // assignment can interpret them as a set-at-depth operation.
  if(1==t(a) && **q && 34==t(**q) && '['==(C)dc(**q)){
    Q bracks = ln(0);
    while(**q && 34==t(**q) && '['==(C)dc(**q)){
      Q args = eix(q);
      if(is_err(args)) return args;
      D bi = n(bracks);
      Q br2 = xn(bracks, 1);
      if(is_err(br2)) return br2;
      if(br2!=bracks) bracks = br2;
      zid(bracks, bi, args);
    }

    Q v0 = **q;
    Q w0 = v0 ? (*q)[1] : 0;
    B end0 = !w0 || (34==t(w0) && (';'==dc(w0) || '\n'==dc(w0) || '}'==dc(w0) || ')'==dc(w0) || ']'==dc(w0)));
    if(v0 && 2==t(v0) && dv(v0)==7 && !end0){
      // Flatten bracket groups into a single index path (x[i][j] => (i;j), x[i;j] => (i;j)).
      Q idxs = ln(0);
      D nb = n(bracks);
      for(D i=0;i<nb;i++){
        Q args = qi(bracks, i);
        if(is_ptr_list(args)){
          D na = n(args);
          if(na){
            D old = n(idxs);
            Q idxs2 = xn(idxs, na);
            if(is_err(idxs2)) return idxs2;
            if(idxs2!=idxs) idxs = idxs2;
            for(D j=0;j<na;j++) zid(idxs, old+j, qi(args, j));
          }
        }else if(args){
          D old = n(idxs);
          Q idxs2 = xn(idxs, 1);
          if(is_err(idxs2)) return idxs2;
          if(idxs2!=idxs) idxs = idxs2;
          zid(idxs, old, args);
        }
      }

      Q lv = ln(2);
      zid(lv, 0, a);
      zid(lv, 1, idxs);
      return edv(lv, q);
    }

    Q noun = resolve_ref(SC[SP], a);
    if(is_err(noun)) return noun;
    D nb = n(bracks);
    for(D i=0;i<nb;i++){
      noun = apply_brackets(noun, qi(bracks, i));
      if(is_err(noun)) return noun;
    }

    Q v = **q;
    Q w2 = v ? (*q)[1] : 0;
    B end2 = !w2 || (34==t(w2) && (';'==dc(w2) || '\n'==dc(w2) || '}'==dc(w2) || ')'==dc(w2) || ']'==dc(w2)));
    if(v && 2==t(v) && !end2) return edv(noun, q);                                 // dyadic (after postfix indexing)
    return noun;
  }

  Q noun = (1==t(a)) ? resolve_ref(SC[SP], a) : a;
  if(is_err(noun)) return noun;
  while(**q && 34==t(**q) && '['==(C)dc(**q)) noun = eib(noun, q);              // postfix indexing
  
  Q v = **q;
  Q w2 = v ? (*q)[1] : 0;
  B end2 = !w2 || (34==t(w2) && (';'==dc(w2) || '\n'==dc(w2) || '}'==dc(w2) || ')'==dc(w2) || ']'==dc(w2)));
  if(v && 2==t(v) && !end2) return edv(noun, q);                                 // dyadic (after postfix indexing)
  return noun;
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
static C* CST="1757A77988777B47333333333378777A7222222222222222222222222228987A6222222222222222222222222228787";
D cl(C c){
  B uc=(B)c;if(!uc)return 0;if(uc>=128)return 4;if(uc<' '||uc>126)return 10;C r=CST[uc-' '];return(r>='0'&&r<='9')?r-'0':r-'A'+10;
}
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
    {7,  8,  7,  2,  3,  7,  7,  7,  7,  7,  7,  1}, // 8 S_VEC (allow negative elements after spaces)
  };
static inline J parse_i10(const C* s, D len){
  if(len<=0) return 0;
  D i=0;
  J sign=1;
  if(s[0]=='-'){ sign=-1; i=1; }
  Q r=0;
  for(; i<len; i++){
    C c=s[i];
    if(c<'0' || c>'9') break;
    r = r*10ULL + (Q)(c - '0');
  }
  return (J)r * sign;
}
static inline double parse_f10(const C* s, D len){
  C tmp_small[128];
  C* tmp = tmp_small;
  if(len >= (D)sizeof(tmp_small)){
    tmp = (C*)os_heap_alloc((Q)len + 1ULL);
    if(!tmp) return 0.0;
  }
  memcpy(tmp, s, (size_t)len);
  tmp[len]=0;
  errno = 0;
  C* endp = 0;
  double x = strtod(tmp, &endp);
  if(tmp != tmp_small) os_heap_free(tmp);
  // The lexer guarantees a numeric-ish token, but keep this strict anyway.
  if(errno || !endp || *endp) return 0.0;
  return x;
}
static inline Q af(Q ar, double x){
  Q q = tsna(ar, T_FLT, 0, 3, 1, 1);
  pid(q, 0, f64_bits(x));
  return q;
}
static inline Q af_bits(Q ar, Q bits){
  Q q = tsna(ar, T_FLT, 0, 3, 1, 1);
  pid(q, 0, bits);
  return q;
}
Q pn(C* s, D len){
  (void)len;
  B is_flt=0;
  for(C* p=s; *p; p++){ if(*p=='.') { is_flt=1; break; } }

  D c=0; C* p=s;
  while(*p){ while(*p==' ') p++; if(!*p) break; c++; while(*p && *p!=' ') p++; }

  if(c==1){
    p=s; while(*p==' ') p++; C* t0=p; while(*p && *p!=' ') p++; D l0=(D)(p-t0);
    if(is_flt) return af(0, parse_f10(t0, l0));
    return an(parse_i10(t0, l0));
  }

  if(is_flt){
    Q z=vna(0, T_FLT, 3, c); p=s;
    for(D i=0;i<c;i++){
      while(*p==' ') p++; C* t0=p; while(*p && *p!=' ') p++; D l0=(D)(p-t0);
      pid(z, i, f64_bits(parse_f10(t0, l0)));
    }
    return z;
  }

  Q z=vna(0, T_INT, 3, c); p=s;
  for(D i=0;i<c;i++){
    while(*p==' ') p++; C* t0=p; while(*p && *p!=' ') p++; D l0=(D)(p-t0);
    pid(z, i, (Q)parse_i10(t0, l0));
  }
  return z;
}
static inline B ends_with_dot_l(const char* s){
  if(!s) return 0;
  size_t n = strlen(s);
  if(n < 2) return 0;
  C c0 = s[n-2], c1 = s[n-1];
  if(c0 != '.') return 0;
  if(c1 >= 'A' && c1 <= 'Z') c1 = (C)(c1 - 'A' + 'a');
  return c1 == 'l';
}

static inline B qstr_to_c(Q w, C* out, D out_cap){
  if(!out || !out_cap) return 0;
  if(t(w)!=6) return 0;
  D n_w = n(w);
  if(n_w >= out_cap) n_w = out_cap - 1;
  for(D i=0;i<n_w;i++) out[i] = (C)pi(w,i);
  out[n_w] = 0;
  return 1;
}

static inline D ascii_adv_id(const C* p){
  C a=p[0], b=p[1];
  if(a=='-' && b=='>') return 2;   // →
  if(a=='<' && b=='-') return 3;   // ←
  if(a=='<' && b=='\'') return 4;  // ↰
  if(a=='\''&& b=='>') return 5;   // ↱
  if(a=='\''&& b=='v') return 6;   // ↓
  if(a=='\''&& b=='^') return 7;   // ↑
  if(a=='<' && b=='o') return 8;   // ↺
  if(a=='o' && b=='>') return 9;   // ↻
  if(a=='/' && b=='\'') return 10; // ↿
  if(a=='\\'&& b=='\'') return 11; // ⇃
  if(a=='<' && b=='p') return 12;  // ↫
  if((a=='p' || a=='q') && b=='>') return 13;  // ↬ (support both p> and q>)
  return 0;
}

static void print_usage(void){
  printf("usage: l [--dbg-startup] [--dump-tokens] [--no-inplace] [script.l]\n");
}

static void parse_args(I argc, C** argv, const C** script_out, B* usage_out){
  if(script_out) *script_out = 0;
  if(usage_out) *usage_out = 0;
  for(I i=1;i<argc;i++){
    const C* a = argv[i];
    if(!a || !*a) continue;
    if(0==strcmp(a, "--dbg-startup")){ L_opts.dbg_startup = 1; continue; }
    if(0==strcmp(a, "--dump-tokens")){ L_opts.dump_tokens = 1; continue; }
    if(0==strcmp(a, "--no-inplace")){ L_opts.no_inplace = 1; continue; }
    if(0==strcmp(a, "-h") || 0==strcmp(a, "--help")){ if(usage_out) *usage_out = 1; continue; }
    if(a[0]=='-'){ if(usage_out) *usage_out = 1; continue; }
    if(script_out && !*script_out){ *script_out = a; continue; }
    if(usage_out) *usage_out = 1;
  }
}

static inline void dbg_write_startup(const char* s){
  if(!L_opts.dbg_startup || !s) return;
  platform_write_stderr_bytes(s, strlen(s));
}
static void dump_token_tape(Q* toks){
  if(!toks) return;
  for(D i=0; toks[i]; ++i){
    Q x = toks[i];
    printf("tok[%u] t=%u sh=%u ", (unsigned)i, (unsigned)t(x), (unsigned)sh(x));
    pr(x);
    printf("\n");
  }
}
static inline B dump_tokens_enabled(void){
  return L_opts.dump_tokens;
}

static Q eval_lexed_tokens(Q* tokens_base){
  Q* tokens = tokens_base;
  Q r = tsna(0,4,1,3,0,0); // missing
  for(;;){
    if(LP>0){
      C tc = LC[LP] ? LC[LP] : ')';
      r = E(&tokens, tc, 1);
      if(LP>0 && LK[LP]==1 && !(*tokens && 34==t(*tokens) && tc==dc(*tokens))){
        r = apply_brackets(LBASE[LP], NL[LP]);
      }
      if(*tokens && 34==t(*tokens) && tc==dc(*tokens)){
        r = ecl(&tokens);
        if(*tokens) continue;
      }
      break;
    }else{
      Q r2 = E(&tokens, '\0', 0);
      if(!(4==t(r2) && 0==n(r2))) r = r2;
      break;
    }
  }
  return r;
}

static Q eval_code_tape(const C* src, D len){
  if(!src || !len) return 0;
  dbg_write_startup("dbg: eval_code_tape enter\n");
  if(len >= 3 && (B)src[0]==0xEF && (B)src[1]==0xBB && (B)src[2]==0xBF){ src += 3; len -= 3; } // skip UTF-8 BOM
  Q* tokens_base = lx_len(src, len);
  dbg_write_startup("dbg: eval_code_tape lexed\n");
  if(!tokens_base) return ae(2);
  if(dump_tokens_enabled()) dump_token_tape(tokens_base);
  Q r = eval_lexed_tokens(tokens_base);
  os_heap_free(tokens_base);
  return r;
}

static Q eval_code_file(const char* fn){
  if(!fn) return ae(2);
  Q sz=0, h=0;
  void* addr = os_map_ro((char*)fn, &sz, &h);
  if(!addr) return ae(2);
  dbg_write_startup("dbg: eval_code_file mapped\n");
  Q r = (addr==(void*)1) ? 0 : eval_code_tape((const C*)addr, (D)sz);
  dbg_write_startup("dbg: eval_code_file tape done\n");
  os_unmap_ro(addr, sz, h);
  dbg_write_startup("dbg: eval_code_file unmapped\n");
  return r;
}

Q* lx_len(const C* b, D l){
  Q* q=(Q*)os_heap_alloc((Q)sizeof(Q) * (Q)(l+1)); if(!q) return 0;
  D qi=0;const C*p=b;const C* end=b+l;D st=0; // st:state
  while(st!=7){
    if(p>=end){st=7;break;}

    // Line comment: `// ...` until end-of-line (newline is still a statement separator).
    if(*p=='/' && (p+1)<end && p[1]=='/'){
      p += 2;
      while(p<end && *p!='\n' && *p!='\r') p++;
      continue;
    }

    // Statement separators:
    // - Newlines separate statements but do not suppress the last value.
    // - ';' separates statements AND suppresses the value of the preceding statement.
    if(*p=='\n'){q[qi++]=ac('\n');p++;st=0;continue;}
    if(*p=='\r'){q[qi++]=ac('\n');p++;if(p<end && *p=='\n')p++;st=0;continue;}
    if(*p==';'){q[qi++]=ac(';');p++;st=0;continue;}
    if(*p=='\t'){p++;continue;}
    if(*p=='[' || *p==']'){q[qi++]=ac(*p);p++;st=0;continue;}

    // Tag literal: `$...` (tag64). Uses '$' as a delimiter like '`' for symbols.
    // Allowed digits: _ A-Z a-z 0-9 .  (max 10 digits => 60 bits)
    // Vector literal: multiple tag literals (e.g. "$a$b" or "$a $b $c") lex as a single T_TAG vector (like "1 2 3").
    if(*p=='$'){
      Q tmp[32]; Q* vals = tmp; D nvals = 0, cap = (D)(sizeof(tmp)/sizeof(tmp[0]));
      Q scalar_payload = 0; B scalar_ok = 0;
      B err = 0;
      for(;;){
        const C* s = p;
        p++; // '$'
        while(p<end && tag64_digit(*p) >= 0) p++;

        D len_tok = (D)(p - s);
        Q payload = tag64_parse_payload(s+1, len_tok-1);
        if(payload==TAG64_ERR){
          err = 1;
          break;
        }

        if(nvals==0){ scalar_payload = payload; scalar_ok = 1; }
        if(nvals < cap){
          vals[nvals++] = payload;
        }else{
          D new_cap = cap + (cap>>1) + 8;
          Q* nv = (Q*)os_heap_alloc((Q)(new_cap * (D)sizeof(Q)));
          if(!nv){
            err = 1;
            break;
          }
          memcpy(nv, vals, (size_t)(cap * (D)sizeof(Q)));
          if(vals!=tmp) os_heap_free(vals);
          vals = nv;
          cap = new_cap;
          vals[nvals++] = payload;
        }

        // Next element?
        if(p<end && *p=='$') continue;
        const C* p2 = p;
        while(p2<end && (*p2==' ' || *p2=='\t')) p2++;
        if(p2<end && *p2=='$'){ p = p2; continue; }
        break;
      }

      if(err){
        if(vals!=tmp) os_heap_free(vals);
        q[qi++]=ae(2);
        st=0;continue;
      }

      if(nvals<=1 && scalar_ok){
        if(vals!=tmp) os_heap_free(vals);
        q[qi++] = atg(scalar_payload);
      }else{
        Q z = vna(0, T_TAG, 3, nvals);
        for(D i=0;i<nvals;i++) pid(z, i, vals[i]);
        if(vals!=tmp) os_heap_free(vals);
        q[qi++] = z;
      }
      st=0;continue;
    }

    // Symbol literal: '`name' (interned). Vector literal: `a`b`c (or `a `b `c) lex as a single T_SYM vector.
    if(*p=='`'){
      Q tmp[32]; Q* vals = tmp; D nvals = 0, cap = (D)(sizeof(tmp)/sizeof(tmp[0]));
      Q scalar_atom = 0; B scalar_ok = 0;
      Q errtok = 0;
      for(;;){
        p++; // '`'
        const C* s = p;
        while(p<end){
          C c=*p;
          if((c>='A'&&c<='Z')||(c>='a'&&c<='z')||(c>='0'&&c<='9')||c=='.'||c=='_'){ p++; continue; }
          break;
        }
        D len_tok = (D)(p - s);
        Q atom = sym_intern_bytes(s, len_tok);
        if(is_err(atom)){
          errtok = atom;
          break;
        }
        if(nvals==0){ scalar_atom = atom; scalar_ok = 1; }
        Q payload = ip(atom) ? pi(atom,0) : di(atom);

        if(nvals < cap){
          vals[nvals++] = payload;
        }else{
          D new_cap = cap + (cap>>1) + 8;
          Q* nv = (Q*)os_heap_alloc((Q)(new_cap * (D)sizeof(Q)));
          if(!nv){
            errtok = ae(2);
            break;
          }
          memcpy(nv, vals, (size_t)(cap * (D)sizeof(Q)));
          if(vals!=tmp) os_heap_free(vals);
          vals = nv;
          cap = new_cap;
          vals[nvals++] = payload;
        }

        // Next element?
        if(p<end && *p=='`') continue;
        const C* p2 = p;
        while(p2<end && (*p2==' ' || *p2=='\t')) p2++;
        if(p2<end && *p2=='`'){ p = p2; continue; }
        break;
      }

      if(errtok){
        if(vals!=tmp) os_heap_free(vals);
        q[qi++] = errtok;
        st=0;continue;
      }

      if(nvals<=1 && scalar_ok){
        if(vals!=tmp) os_heap_free(vals);
        q[qi++] = scalar_atom;
      }else{
        Q z = vna(0, T_SYM, 3, nvals);
        for(D i=0;i<nvals;i++) pid(z, i, vals[i]);
        if(vals!=tmp) os_heap_free(vals);
        q[qi++] = z;
      }
      st=0;continue;
    }

    if((end-p)>=2){
      D ai2=ascii_adv_id(p);
      if(ai2){q[qi++]=aa(ai2);p+=2;st=0;continue;}
    }

    if((B)*p==0xE2 && (end-p)>=3){
      C t[4];t[0]=p[0];t[1]=p[1];t[2]=p[2];t[3]=0;
      D ai=FA(t);
      if(ai){q[qi++]=aa(ai);p+=3;st=0;continue;}
    }

    // Make '-' subtract when adjacent (e.g. "1-2" or "1- 2"), but keep negative literals in numeric vectors ("1 -2").
    if(*p=='-'){
      C next = (p+1<end) ? p[1] : 0;
      if(next && ((next>='0' && next<='9') || next=='.')){
        C prev = (p>b) ? p[-1] : 0;
        B prev_can_end =
          (prev>='0' && prev<='9') ||
          (prev>='A' && prev<='Z') ||
          (prev>='a' && prev<='z') ||
          prev==')' || prev=='}' || prev=='\"' || prev=='`' || prev=='.';
        if(prev_can_end){
          q[qi++]=V('-');p++;st=0;continue;
        }
      }else{
        q[qi++]=V('-');p++;st=0;continue;
      }
    }
    C*s=(C*)p;D cc=cl(*p);st=TT[0][cc]; // s:token start
    if(st==0){p++;continue;} // whitespace
    if(cc>=7&&cc<=9){C ts[2]={*p,0};q[qi++]=cc==7?av(FV(ts)):cc==8?ac(*p):aa(FA(ts));p++;st=0;continue;} // verbs, controls, adverbs
    if(st==7){
      if(cc==0){st=7;break;} // embedded NUL: treat as end-of-input
      q[qi++]=ae(2);p++;st=0;continue; // unknown/illegal char
    }
    while(st!=7){
      p++;
      C c = (p<end) ? *p : 0;
      if(st!=5 && (c=='\n' || c=='\r' || c=='\t' || c==';')) c=0; // token boundary at separators (except strings)
      cc=cl(c);
      D next_st=TT[st][cc];
      // Disambiguate dyadic '-' written with spaces ("1 - 2") from a negative element in a numeric vector ("1 -2 3").
      // If we're in a numeric vector and see '-' followed by whitespace/separator, end the current numeric token before '-'
      // so the outer loop can re-lex '-' as a verb.
      if(st==8 && c=='-' && next_st==1){
        C la = (p+1<end) ? p[1] : 0;
        if(!la || la==' ' || la=='\t' || la=='\n' || la=='\r' || la==';') next_st=7;
      }
      if(st==1&&next_st!=2){q[qi++]=V(*s);p=s+1;st=0;break;} // not a number, treat '-' as a verb
      if(next_st==7){ // End of token.
        D len=(D)(p-s);
        if(st==1||st==2||st==3||st==8 || st==4){
          C tmp_small[100];C* tok=tmp_small;
          if(len >= (D)sizeof(tmp_small)){
            tok=(C*)os_heap_alloc((Q)len + 1ULL);
            if(!tok){q[qi]=0;return q;}
          }
          memcpy(tok,s,(size_t)len);tok[len]=0;
          if(st==1||st==2||st==3||st==8) q[qi++]=pn(tok,len);
          else { // st==4 name
            D vi=FV(tok);
            D ai=FA(tok);
            if(vi) q[qi++]=av(vi);
            else if(ai) q[qi++]=aa(ai);
            else {
              // Dotted reference sugar: a.b.c
              // Lex as a single reference token with shape 1 (vector of symbol payloads).
              // Evaluation interprets this as: (((a@`b)@`c)...).
              B has_dot = 0;
              for(D i=0;i<len;i++){ if(tok[i]=='.'){ has_dot = 1; break; } }

              if(!has_dot){
                Q sym = sym_intern_bytes(tok, len);
                if(is_err(sym)) q[qi++]=sym;
                else q[qi++]=ar(ra(sym)); // reference payload is the symbol payload (interned or small)
              }else{
                // Validate + count segments.
                if(len<=0 || tok[0]=='.' || tok[len-1]=='.'){ q[qi++]=ae(2); }
                else{
                  D segc = 1;
                  B bad = 0;
                  for(D i=1;i<len;i++){
                    if(tok[i]=='.'){
                      segc++;
                      if(tok[i-1]=='.'){ bad = 1; break; }
                    }
                  }
                  if(bad){ q[qi++]=ae(2); }
                  else{
                    Q tmp_payloads[32];
                    Q* payloads = tmp_payloads;
                    if(segc > (D)(sizeof(tmp_payloads)/sizeof(tmp_payloads[0]))){
                      payloads = (Q*)os_heap_alloc((Q)segc * (Q)sizeof(Q));
                      if(!payloads){ q[qi++]=ae(2); goto lx_name_done; }
                    }

                    D segi = 0;
                    D start = 0;
                    Q errtok = 0;
                    for(D i=0;i<=len;i++){
                      if(i==len || tok[i]=='.'){
                        D slen = i - start;
                        if(slen <= 0){ errtok = ae(2); break; }
                        Q sym = sym_intern_bytes(tok + start, slen);
                        if(is_err(sym)){ errtok = sym; break; }
                        payloads[segi++] = ra(sym);
                        start = i + 1;
                      }
                    }

                    if(!errtok){
                      Q rv = vna(0, 1, 3, segi);
                      for(D i=0;i<segi;i++) pid(rv, i, payloads[i]);
                      q[qi++] = rv;
                    }else{
                      q[qi++] = errtok;
                    }

                    if(payloads != tmp_payloads) os_heap_free(payloads);
lx_name_done:;
                  }
                }
              }
            }
          }
          if(tok!=tmp_small) os_heap_free(tok);
        }
        else if(st==6){ q[qi++]=sym_intern_bytes(s+1, len-1); }
        else if(st==5){ s++; len--; Q z=vna(0,6,0,len); for(D i=0;i<len;i++)pid(z,i,s[i]); q[qi++]=z; if(p<end)p++;}
        // TODO: S_FLT
        st=0;break;
      }
      st=next_st;
    }
  }
  q[qi]=0;return q;
}

// New lexer implementation placeholder (state-machine rewrite will live here).
// For now, keep lex2 behavior identical for parity testing.
Q* lx2_len(const C* b, D l){
  return lx_len(b, l);
}
static C* read_line(FILE* in){
  if(!in) return 0;
  size_t cap = 256;
  size_t len = 0;
  C* buf = (C*)os_heap_alloc((Q)cap);
  if(!buf) return 0;
  for(;;){
    int ch = fgetc(in);
    if(ch == EOF){
      if(len == 0){ os_heap_free(buf); return 0; }
      break;
    }
    if(ch == '\n') break;
    if(ch == '\r') continue;
    if(len + 1 >= cap){
      cap *= 2;
      C* nb = (C*)os_heap_realloc(buf, (Q)cap);
      if(!nb){ os_heap_free(buf); return 0; }
      buf = nb;
    }
    buf[len++] = (C)ch;
  }
  buf[len] = 0;
  return buf;
}

static B repl_buf_in_open_string(const C* buf, size_t len){
  if(!buf || !len) return 0;
  B in_str = 0;
  for(size_t i=0;i<len;i++){
    C c = buf[i];
    if(!in_str){
      if(c=='/' && (i+1)<len && buf[i+1]=='/'){
        i += 2;
        while(i<len && buf[i] != '\n') i++;
        continue;
      }
      if(c=='\"'){ in_str = 1; continue; }
    }else{
      if(c=='\"'){ in_str = 0; continue; }
    }
  }
  return in_str;
}

static C* read_repl_stmt(FILE* in, B* exit_repl){
  if(exit_repl) *exit_repl = 0;
  C* buf = read_line(in);
  if(!buf) return 0;

  if(exit_repl && strcmp(buf, "\\\\") == 0){
    *exit_repl = 1;
    return buf;
  }

  size_t len = strlen(buf);
  while(repl_buf_in_open_string(buf, len)){
    printf(" |");
    C* next = read_line(in);
    if(!next) break;
    size_t next_len = strlen(next);

    Q need = (Q)(len + 1 + next_len + 1);
    C* nb = (C*)os_heap_realloc(buf, need);
    if(!nb){ os_heap_free(buf); os_heap_free(next); return 0; }
    buf = nb;
    buf[len] = '\n';
    if(next_len) memcpy(buf + len + 1, next, next_len);
    len += 1 + next_len;
    buf[len] = 0;
    os_heap_free(next);
  }

  return buf;
}

I main(I argc, C** argv){
  const C* script = 0;
  B usage = 0;
  parse_args(argc, argv, &script, &usage);
  if(usage) print_usage();
  dbg_write_startup("dbg: main start\n");
  platform_init_stdout_utf8_if_console();
  platform_arena_reserve_init();
  dbg_write_startup("dbg: arenas reserved\n");
  buddyinit(1);
  dbg_write_startup("dbg: buddyinit done\n");
  FT_addr = vca(1, 3, 3, 4096);
  FT_sz   = vca(1, 3, 3, 4096);
  FT_cap  = vca(1, 3, 3, 4096);
  FT_h    = vca(1, 3, 3, 4096);
  FT_fn   = vca(1, 0, 3, 4096);
  G=dni(0,3,0,1); // global dictionary in buddy allocator
  sym_init();
  dbg_write_startup("dbg: sym_init done\n");
  Q ft = dni(0,3,0,1); // file table dict in buddy allocator
  dkv(ft, sym_intern_bytes("addr", 4), FT_addr);
  dkv(ft, sym_intern_bytes("sz",   2), FT_sz);
  dkv(ft, sym_intern_bytes("cap",  3), FT_cap);
  dkv(ft, sym_intern_bytes("h",    1), FT_h);
  dkv(ft, sym_intern_bytes("fn",   2), FT_fn);
  dkv(G,  sym_intern_bytes("FT",   2), ft);
  SC[0]=dni(0,3,0,0); SP=0;
  dbg_write_startup("dbg: globals ready\n");

  // In non-interactive/scripted usage (e.g. tests), stdin may not be a real console.
  // Avoid entering the REPL in that case to prevent stdio/handle edge-case crashes.
  B stdin_is_console = platform_stdin_is_console();

  if(script){
    if(!ends_with_dot_l(script)){
      print_usage();
    }else{
      dbg_write_startup("dbg: eval_code_file start\n");
      Q r = eval_code_file(script);
      dbg_write_startup("dbg: eval_code_file done\n");
      pr(r);printf("\n");
    }
    if(!stdin_is_console) return 0;
  }

  while (1) {
    printf(" ");
    B exit_repl = 0;
    C* line = read_repl_stmt(stdin, &exit_repl);
    if(!line) break;
    if(exit_repl){ os_heap_free(line); break; }
    if(!*line){ os_heap_free(line); continue; }
    if(0==SP && 0==LP){
      for(D i=0;i<n(pi(SC[0],1));i++){
        Q gk=pi(pi(SC[0],1),i);Q gv=pi(pi(SC[0],2),i);
        dkv(G,t2g(gk),t2g(gv));
      }
      AI[0]=1;SC[0]=dni(0,3,0,0); SP=0; 
     } // reset THI only if evaluation takes us back to the global scope. 
    Q* tokens_base = lx_len(line, (D)strlen(line));
    if(!tokens_base){ os_heap_free(line); pr(ae(2)); printf("\n"); continue; }
    Q r = eval_lexed_tokens(tokens_base);
    os_heap_free(tokens_base);
    pr(r);printf("\n");
    os_heap_free(line);
  }
  return 0;
}
