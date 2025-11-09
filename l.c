// cl l.c /GL /O1 /Gy /MD /DNDEBUG /link /LTCG /OPT:REF /OPT:ICF
// cc -fsanitize=address l.c -o l_lin
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef unsigned long long Q;typedef unsigned int D;typedef unsigned short W;typedef unsigned char B;typedef char C;
typedef struct {Q n;} AH;                                                     // header for shape 0 and 2. n is Q for alignment.
typedef struct {B t;D m;D n;} Z;                                              // header for shape 3 which is contiguous type 0+metadata.t type; m metadata len;n data len
typedef Q(*DV)(Q,Q);                                                          // function pointer for dyadic verb
typedef Q(*MV)(Q);                                                            // function pointer for monadic verb

Q d(Q q){return q&0x0000ffffffffffffULL;}                                     // hi bits of pointer hold a header. 4 bit type 2 bit element size 2 bit shape. FUTURE: page size min allocation and page alignment (12 low bits free with 4kb pages, eliminate need for shift to get header)
B*p(Q q){return (B*)d(q);}                                                    // util to mask out header and rebuild absolute pointer
B r(Q r){return d(r)+'a';}                                                    // transform an atom of type 1 into ascii. This is how we do variables for now. 
B v(Q v){return d(v);}                                                        // transform an atom of type 2 into its verb index.

AH* ah(Q q){return (AH*)d(q);}                                                // mask header bits and cast to vector type
Z*  zh(Q q){return (Z*)d(q);}                                                 // mask header bits and cast to bulk vector type

Q wh(B t,B z,B s,Q q){return (((Q)((t<<4)|((3&z)<<2)|(3&s)))<<48)|q;}         // write a header into an absolute pointer q

Q ar(Q r){return wh(1,3,1,r);}                                                // create an atom of type 1 (reference) whose element size is 8 bytes
Q av(Q v){return wh(2,0,1,v);}                                                // create an atom of type 2 (verb)      whose element size is 1 byte
Q an(Q n){return wh(3,3,1,n);}                                                // create an atom of type 3 (integer)   whose element size is 8 bytes
Q ap(Q v){return wh(4,3,1,v);}                                                // create an atom of type 4 (partial eval) whose element size is 8 bytes

B  h(Q q){return q>>48;}                                                      // header   from pointer
B th(Q q){return h(q)>>4;}                                                    // type     from header
B sh(Q q){return 3&h(q);}                                                     // shape    from header
B ia(Q q){return 1==sh(q);}                                                   // is atom  from shape
B ls(Q q){return 3&(h(q)>>2);}                                                // logeltsz from header EDGE CASE: should type 0 automatically return 3 here????
B sz(Q q){return 1<<ls(q);}                                                   // bytesz   from logeltsz

Q tsn(B t,B s,B z,D n){AH h={n};AH*o=malloc(sizeof(AH)+(1<<z)*n);*o=h;return wh(t,z,s,(Q)(o+1));}  // LATER: custom allocator. 
Q tn(B t,B z,D n){return tsn(t,2*!!t,z,n);}
Q zn(B t,B z,D m,D n){                                                        // contiguous allocation of data with same type and width, m metdata elements. n total data elements
  Z*o=malloc(sizeof(Z)+(2*sizeof(D)*m)+((1<<z)*n));                           // there are two metadata vectors of length m. all metadata is dword
  Z h={t,m,n};*o=h;
  return wh(0,z,3,(Q)o);
}
D  mz(Q a){return zh(a)->m;}                                                  // length of each Nz and Oz metadata array
D  nz(Q a){return zh(a)->n;}                                                  // length of data pointed to by Dz
D* Nz(Q a){return (D*)(1+zh(a));}                                             // pointer to vector of lengths of each child
D* Oz(Q a){return mz(a)+Nz(a);}                                               // pointer to offset of first child. may point to an offset with Oz(a)+m or beyond into Dz(a). 
                                                                              //  We use this to figure out if a certain metadata item points to aother lower layer of a list or actual data
B* Dz(Q a){return (B*)((mz(a)*2)+Nz(a));}                                     // pointer to data for a bulk allocated type 0
D  fz(Q a,D o){D m=mz(a);D z=o;while(z<m){z=Oz(a)[z];};return z;}             // dist from Oz(a) to first data item 
D  no(Q a,D o,D n){                                                           // number of children under this offset
  D nzo=Nz(a)[o];D oo=Oz(a)[o];
  if(oo>=mz(a)){return Nz(a)[o];}
  for(D i=0;i<nzo;i++){n+=no(a,o+i,n);}
  return n;
}

// varwidth getters
Q Bi(B* b,B z,D i){Q r=0;memcpy(&r,b+z*i,z);return r;}                        // mask this by the size of z then cast to Q. NO SIGN EXTENSION FLOATS MAY LIVE IN HERE TOO.
Q pi(Q q,D i){return Bi(p(q),sz(q),i);}
Q Dzi(Q q,D i){return Bi(Dz(q),sz(q),i);}
Q Gi(Q q,B z,B s,D i){return 1==s?d(q):(2==s||0==s)?Bi(p(q),z,i):Bi(Dz(q),z,i);}   // universal getter, checks shape.
//TODO varwidth setters
void Bid(B* b,B z,D i,Q d){memcpy(b+z*i,&d,z);}
void pid(Q q,D i,Q d){Bid(p(q),sz(q),i,d);}
void Dzid(Q q,D i,Q d){Bid(Dz(q),sz(q),i,d);}
void Si(Q q,B z,B s,D i,Q d){1==s?((h(q)<<48)|d):(2==s||0==s)?Bid(p(q),z,i,d):Bid(Dz(q),z,i,d);}   // universal setter

D n(Q a){B s=sh(a);return 1==s?1:(0==s||2==s)?ah(a)[-1].n:3==sh(a)?nz(a):0;} 
B t(Q a){B t;return th(a);}

Q O[26];
C* VT;

void pr(Q q){
  if(0==q){return;}
  if(0==t(q)){
    if(3==sh(q)){for(D i=0;i<n(q);i++){printf("%lld ",Dzi(q,i));}}
    if(!sh(q)){for(D i=0;i<n(q);i++){pr(pi(q,i));}}}
  if(1==t(q)){printf("%c ",r(q));pr(O[d(q)]);}
  if(2==t(q)){printf("%c",VT[v(q)]);}
  if(3==t(q)){
    if(0==sh(q)){printf("?num\n");}
    if(1==sh(q)){printf("%lld\n",d(q));}
    if(2==sh(q)){
      for(D i=0;i<n(q);i++){printf("%lld ",pi(q,i));}}
    }
  if(4==t(q)){for(D i=0;i<n(q);i++){pr(pi(q,i));}}
  printf("\n");
}
DV VD[8][4][4];
MV VM[8][4];

Q noP(Q w){Q z=tn(0,ls(w),n(w));for(D i=0;i<n(w);i++){pid(z,i,VM[1][sh(pi(w,i))](pi(w,i)));};return z;}
Q noA(Q w){return an(!d(w));}
Q noV(Q w){Q z=tn(3,ls(w),n(w));for(D i=0;i<n(w);i++){pid(z,i,!pi(w,i));};return z;}
Q noZ(Q w){Q z=zn(3,ls(w),mz(w),n(w));for(D i=0;i<2*mz(w);i++){Nz(z)[i]=Nz(w)[i];}for(D i=0;i<n(w);i++){Dzid(z,i,!Dzi(w,i));};return z;}

Q tlA(Q w){Q z=tn(3,ls(w),d(w));for(D i=0;i<d(w);i++){pid(z,i,i);}return z;} // this will force everything to be size of whatever atom literals are.
//Q tlV(Q v){Q z=tn(0,n(v));for(D i=0;i<n(v);i++){p(z)[i]=tlA(p(v)[i]);};return z;}
Q tlV(Q w){
  D nw=n(w);D mzz=1+nw;D zz=0;for(D i=0;i<nw;i++){zz+=pi(w,i);};Q z=zn(3,ls(w),mzz,zz);
  Nz(z)[0]=nw;Oz(z)[0]=1;D l=0;
  for(D i=0;i<nw;i++){Oz(z)[i+1]=((D*)(Dz(z)+l))-Oz(z);l+=Nz(z)[i+1]=pi(w,i);}
  D k=0;for(D i=0;i<nw;i++){for(D j=0;j<pi(w,i);j++){Dzid(z,k++,j);}};
  return z;
}
Q tlZ(Q z){return z;}


Q at(Q a,Q w){Q z=tn(t(a),ls(a),n(w));for(D i=0;i<n(w);i++){pid(z,i,pi(a,pi(w,i)));};return z;}

Q tp(Q a){return an(t(a));}
Q ct(Q a){return an(3==sh(a)?*Nz(a):n(a));}

Q plVV(Q a,Q w){Q z=tn(3,ls(w),n(w));for(D i=0;i<n(w);i++){pid(z,i,pi(a,i)+pi(w,i));};return z;}
Q plAV(Q a,Q w){Q z=tn(3,ls(w),n(w));for(D i=0;i<n(w);i++){pid(z,i,d(a)+pi(w,i));};return z;} 
Q plVA(Q a,Q w){return plAV(w,a);}
Q plAA(Q a,Q w){return an(d(a)+d(w));}
Q plAP(Q a,Q w){Q z=tn(0,ls(w),n(w));for(D i=0;i<n(w);i++){pid(z,i,VD[5][1][sh(pi(w,i))](a,pi(w,i)));};return z;} 
Q plPA(Q a,Q w){return plAP(w,a);}
Q plPP(Q a,Q w){Q z=tn(0,ls(w),n(w));for(D i=0;i<n(w);i++){pid(z,i,VD[5][sh(pi(a,i))][sh(pi(w,i))](pi(a,i),pi(w,i)));}return z;}
Q plPV(Q a,Q w){Q z=tn(0,ls(w),n(w));for(D i=0;i<n(w);i++){pid(z,i,VD[5][sh(pi(a,i))][1](pi(a,i),an(pi(w,i))));}return z;}
Q plVP(Q a,Q w){return plPV(w,a);}
Q plAZ(Q a,Q w){  // this case is simple because we don't need to examine metadata, just need to copy.
  Q z=zn(3,ls(w),mz(w),n(w));
  for(D i=0;i<2*mz(w);i++){Nz(z)[i]=Nz(w)[i];} // counts and offsets are same size
  for(D i=0;i<n(w);i++){Dzid(z,i,d(a)+Dzi(w,i));}
  return z;
} 
Q plZA(Q a,Q w){return plAZ(w,a);}
Q plVZ(Q a,Q w){  // this case is medium hard, metadata still the ssame but need to examine metadata to know which vector index conforms to while data index in the z list
  Q z=zn(3,ls(w),mz(w),n(w));
  for(D i=0;i<2*mz(w);i++){Nz(z)[i]=Nz(w)[i];} // counts and offsets are same size
  Q o=*Oz(w); // o is the distance from Oz(w) to the next offset. 
  for(D i=0;i<*Nz(w);i++){
    D d=fz(w,o+i);
    for(D j=0;j<no(w,o+i,0);j++){
      ((Q*)(Oz(z)+d))[j]=((Q*)(Oz(w)+d))[j]+pi(a,i);
    }
  }
  return z;
}
Q plZV(Q a,Q w){return plVZ(w,a);}
Q plZZ(Q a,Q w){ // not atomic in the usual sense of a k implementation. 
  Q z=zn(3,ls(w),mz(w),n(w));
  for(D i=0;i<2*mz(w);i++){Nz(z)[i]=Nz(w)[i];}
  for(D i=0;i<n(w);i++){Dzid(z,i,Dzi(a,i)+Dzi(w,i));}
  return z;
}

Q as(Q a,Q w){O[d(a)]=w;return w;}

// LATER: finish caPA caPV caPZ
Q caPA(Q a,Q w){Q z=tn(t(a)==t(w)?t(a):0,3,1+n(a));for(D i=0;i<n(a);i++){pid(z,i,pi(a,i));}pid(z,n(a),d(a));return z;}
Q caPV(Q a,Q w){Q z=tn(t(a)==t(w)?t(a):0,3,n(a)+n(w));D j=0;for(D i=0;i<n(a);i++,j++){pid(z,j,pi(a,i));};for(D i=0;i<n(w);i++,j++){pid(z,j,pi(w,i));}return z;}
Q caPZ(Q a,Q w){Q z=tn(t(a)==t(w)?t(a):0,3,n(a)+1);
  for(D i=0;i<n(a);i++){pid(z,i,pi(a,i));};pid(z,n(a),w);
  return z;
}
Q caAA(Q a,Q w){Q z=tn(t(w),ls(w),2);pid(z,0,d(a));pid(z,1,d(w));return z;}
Q caAV(Q a,Q w){Q z=tn(t(w),ls(w),1+n(w));pid(z,0,d(a));for(D i=0;i<n(w);i++){pid(z,i+1,pi(w,i));}return z;}
Q caAZ(Q a,Q w){Q z=zn(t(w),ls(w),1+mz(w),1+n(w));
  Oz(z)[0]=1;Oz(z)[1]=((D*)Dz(z))-Oz(z);
  *Nz(z)=1+*Nz(w);
  for(D i=1;i<mz(w);i++){Oz(z)[i+1]=Oz(w)[i]+((Oz(w)[i]>=mz(w))?2:1);Nz(z)[i+1]=Nz(w)[i];}
  *Dz(z)=d(a);
  for(D i=0;i<n(w);i++){Dzid(z,i+1,Dzi(w,i));}
  return z;
}
Q caVA(Q a,Q w){Q z=tn(t(w),ls(w),1+n(a));for(D i=0;i<n(a);i++){pid(z,i,pi(a,i));}pid(z,n(a),d(a));return z;}
Q caVV(Q a,Q w){Q z=tn(t(w),ls(w),n(a)+n(w));D j=0;for(D i=0;i<n(a);i++,j++){pid(z,j,pi(a,i));};for(D i=0;i<n(w);i++,j++){pid(z,j,pi(w,i));}return z;}
Q caVZ(Q a,Q w){Q z=zn(t(w),ls(w),1+mz(w),n(a)+n(w));
  Oz(z)[0]=1;Oz(z)[1]=((D*)Dz(z))-Oz(z);
  *Nz(z)=1+*Nz(w);Nz(z)[1]=n(a);
  for(D i=1;i<mz(w);i++){Oz(z)[i+1]=Oz(w)[i]+((Oz(w)[i]>=mz(w))?1+n(a)*2:1);Nz(z)[i+1]=Nz(w)[i];} //ls(w) missing
  for(D i=0;i<n(a);i++){Dzid(z,i,pi(a,i));}
  for(D i=0;i<n(w);i++){Dzid(z,i+n(a),Dzi(w,i));}
  return z;
}
Q caZA(Q a,Q w){Q z=zn(t(w),ls(w),1+mz(a),1+n(a));
  Oz(z)[0]=1;*Nz(z)=1+*Nz(a);
  for(D i=1;i<2*mz(a);i++){Nz(z)[i]=Nz(a)[i];}
  for(D i=0;i<n(a);i++){Dzid(z,i,Dzi(a,i));}
  Nz(z)[mz(a)]=1;Oz(z)[mz(a)]=((D*)(Dz(z)+n(a)))-Oz(z);Dzid(z,n(a),d(w));
  return z;
}
Q caZV(Q a,Q w){Q z=zn(t(w),ls(w),1+mz(a),n(w)+n(a));
  Oz(z)[0]=1;*Nz(z)=1+*Nz(a);
  for(D i=1;i<2*mz(a);i++){Nz(z)[i]=Nz(a)[i];}
  for(D i=0;i<n(a);i++){Dzid(z,i,Dzi(a,i));}
  Nz(z)[mz(a)]=1;Oz(z)[mz(a)]=((D*)(Dz(z)+n(a)))-Oz(z);
  for(D i=0;i<n(w);i++){Dzid(z,n(a)+i,pi(w,i));}

  return z;
}
Q caZZ(Q a,Q w){Q z=zn(t(w),ls(w),mz(a)+mz(w),n(a)+n(w));
  D i=1,j=0;
  Oz(z)[0]=1;*Nz(z)=(*Nz(a))+(*Nz(w));
  for(j=1;j<*Nz(a);j++,i++){Oz(z)[i]=Oz(a)[j];Nz(z)[i]=Nz(a)[j];}
  for(j=1;j<*Nz(w);j++,i++){Oz(z)[i]=Oz(z)[*Nz(a)]+Oz(w)[j]; Nz(z)[i]=Nz(w)[j];}
  for(j=*Nz(a);j<mz(a);j++,i++){Oz(z)[i]=Oz(z)[*Nz(a)+*Nz(w)-1]+Oz(a)[j];Nz(z)[i]=Nz(a)[j];}
  for(j=*Nz(w);j<mz(w);j++,i++){Oz(z)[i]=Oz(z)[ mz(a)+*Nz(w)-1]+Oz(w)[j];Nz(z)[i]=Nz(w)[j];}
  for(i=0,j=0;i<n(a);i++,j++){Dzid(z,i,Dzi(a,j));}
  for(j=0;j<n(w);i++,j++){Dzid(z,i,Dzi(w,j));}
  return z;
}

Q id(Q a){return a;}
Q en(Q a){Q z=tn(0,3,1);pid(z,0,a);return z;}
Q enA(Q a){Q z=tn(t(a),ls(a),1);pid(z,0,d(a));return z;}

DV VD[8][4][4]={
  {{0,0,0,0},{0,0,0,0},{0,0,0,0},{0,0,0,0}},
  {{0,0,0,0},{0,0,0,0},{0,0,0,0},{0,0,0,0}},
  {{0,0,0,0},{0,0,0,0},{0,0,0,0},{0,0,0,0}},
  {{0,0,0,0},{0,0,0,0},{0,at,0,0},{0,0,0,0}}, //at
  {{0,0,0,0},{0,0,0,0},{0,0,0,0},{0,0,0,0}},
  {{plPP,plPA,plPV,0},{plAP,plAA,plAV,plAZ},{plVP,plVA,plVV,plVZ},{0,plZA,plZV,plZZ}}, //pl,
  {{0,0,0,0},{as,as,as,as},{0,0,0,0},{0,0,0,0}}, // as
  {{caVV,caVA,caVV,caVZ},{0,caAA,caAV,caAZ},{caVV,caVA,caVV,caVZ},{0,caZA,caZV,caZZ}}}; // ca
MV VM[8][4]={
  {0,0,0,0},
  {noP,noA,noV,noZ},
  {0,tlA,tlV,0},
  {tp,tp,tp,tp},
  {ct,ct,ct,ct},
  {0,0,0,0}, // consider making this x<<1
  {id,id,id,id},
  {en,enA,en,en}};
C* VT=" ~!@#+:,";

Q Ap(Q a){Q p=tsn(4,0,3,1);pid(p,0,a);return p;}
Q e(Q* q);
Q emv(Q*q){
  Q w=e(q+1);
  if(4==t(w)){Q p=tsn(4,0,3,1);pid(p,0,*q);return caVV(p,w);}
  return VM[v(*q)][sh(w)](w);
}
Q edv(Q a,Q*q){
  Q w=e(q+1);
  if(4==t(w)&&(6!=v(*q))){Q p=tsn(4,0,3,2);pid(p,0,a);pid(p,1,*q);return caVV(p,w);}  // handle partial evaluations but allow assignment of them instantly. 
  a=((1==t(a))&&(6!=v(*q)))?O[d(a)]:a;
  DV dv=VD[v(*q)][sh(a)][sh(w)];
  return dv(a,w);
}
Q e(Q* q){
  Q a=*q;
  if(!a){return tsn(4,0,3,0);}                                 // If a is the end of the stream then we must have missing data. return type 4
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
Q V(C a){for(D i=0;i<8;i++){if(VT[i]==a){return av(i);}}return 0;} 
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
    pr(e(pe(buffer)));
  }
  return 0;
}