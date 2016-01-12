#ifndef __Encodings_MW_h
#define __Encodings_MW_h

#include <assert.h>
#include <map>
#include <vector>
#include <iostream>
#include "core/SolverTypes.h"

using namespace std;

template <class Solver>
class Encoding_MW {
 private:
  bool make3wiseSel(vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);
  void _3wiseSplit(vector<Lit> const& in, vector<Lit>& out1, vector<Lit>& out2, vector<Lit>& out3);

  void make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3);
  inline void make2Comparator(Lit const& a, Lit const& b, Lit& c1, Lit& c2);

  bool makeDirectNetwork(vector<Lit>& invars, vector<Lit>& outvars, unsigned k);
  void DirectCardClauses(vector<Lit>& invars, unsigned start, unsigned pos, unsigned j, vec<Lit>& args);

  Solver* S;

 public:
  bool make3wiseSelConstr(const vector<Lit>& lits, unsigned const k, vector<Lit>* outvars);

  Encoding_MW(Solver* _S) : S(_S) { }
  ~Encoding_MW() { }
};

template<class Solver>
bool Encoding_MW<Solver>::make3wiseSelConstr(const vector<Lit>& lits, unsigned const k, vector<Lit>* p_outvars) {
  // input vars
  vector<Lit> invars;
  for (unsigned i = 0 ; i < lits.size() ; i++) {
    invars.push_back(lits[i]);
  }

  //output vars
  vector<Lit> outvars;

  make3wiseSel(invars, outvars, k);

  for (unsigned i = 0 ; i < outvars.size() ; i++) {
    if (outvars[i] == lit_Undef)  continue;
    if (p_outvars) {
      p_outvars->push_back(outvars[i]);
    }
  }

  for (unsigned i = k ; i < outvars.size() ; i++) {
    if(outvars[i] == lit_Undef) continue;
    S->addClause(~outvars[i]);
  }
    
  return true;
}

template<class Solver>
bool Encoding_MW<Solver>::make3wiseSel(vector<Lit>& invars, vector<Lit>& outvars, unsigned const k) {
  assert(outvars.empty());

  unsigned int n = invars.size();

  if((k==1) || (k==2 && n <= 9) || (k==3 && n <= 6) || (k==4 && n <= 5) || (k==5 && n==5)) {
    makeDirectNetwork(invars, outvars, k);
    return true;
  }

  if (k >= n) {
    //makeSortNet(invars, outvars); // temporary use of existing odd-even sorting network
    return true;
  }

  // split
  vector<Lit> out1, out2, out3;
  _3wiseSplit(invars, out1, out2, out3);

  // recursive calls
  vector<Lit> sorted1, sorted2, sorted3;
  make3wiseSel(out1, sorted1, k);
  make3wiseSel(out2, sorted2, k/2);
  make3wiseSel(out3, sorted3, k/3);

  // merging

  return true;
}

// Pairwise Splitting
template<class Solver>
void Encoding_MW<Solver>::_3wiseSplit(vector<Lit> const& in, vector<Lit>& out1, vector<Lit>& out2, vector<Lit>& out3) {
  // out1/2/3 should be created in this function
  assert(out1.empty());
  assert(out2.empty());
  assert(out3.empty());
}
  
template<class Solver>
void Encoding_MW<Solver>::make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3) {
  // if one of our inputs is a constant false, we use normal comparator on the other two
  if (x1 == lit_Undef) {
    y3 = x1;
    make2Comparator(x2, x3, y1, y2);
    return;
  }
  if (x2 == lit_Undef) {
    y3 = x2;
    make2Comparator(x1, x3, y1, y2);
    return;
  }
  if (x3 == lit_Undef) {
    y3 = x3;
    make2Comparator(x1, x2, y1, y2);
    return;
  }

  // otherwise we create new variables
  S->newVar();
  y1 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  y2 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  y3 = mkLit((unsigned int)S->nVars()-1);
  
  // 7-clause 3-comparator for AtMost constraint

  vec<Lit> args; // reused
  
  // x1 -> y1
  args.push(~x1);
  args.push(y1);
  S->addClause(args);
  
  // x2 -> y1
  args[0] = ~x2;
  // Already there: args[1] = y1;
  S->addClause(args);
  
  // x3 -> y1
  args[0] = ~x3;
  // Already there: args[1] = y1;
  S->addClause(args);
  
  // x1 ^ x2 -> y2
  args[0] = ~x1;
  args[1] = ~x2;
  args.push(y2);
  S->addClause(args);
  
  // x1 ^ x3 -> y2
  // Already there: args[0] = ~x1;
  args[1] = ~x3;
  // Already there: args[2] = y2;
  S->addClause(args);
  
  // x2 ^ x3 -> y2
  args[0] = ~x2;
  // Already there: args[1] = ~x3;
  // Already there: args[2] = y2;
  S->addClause(args);
  
  // x1 ^ x2 ^ x3 -> y3
  args[0] = ~x1;
  args[1] = ~x2;
  args[2] = ~x3;
  args.push(y3);
  S->addClause(args);
}

template<class Solver>
inline void Encoding_MW<Solver>::make2Comparator(Lit const& a, Lit const& b, Lit& c1, Lit& c2) {
  // if one of our inputs is a constant false, we can simplify greatly
  if (a == lit_Undef) {
    c1 = b;
    c2 = a;
    return;
  }
  if (b == lit_Undef) {
    c1 = a;
    c2 = b;
    return;
  } 

  // otherwise, we need new variables
  S->newVar();
  c1 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  c2 = mkLit((unsigned int)S->nVars()-1);

  vec<Lit> args; // reused

  // 3-clause comparator,
  // because AtMosts only need implications from 0 on the outputs to 0 on the inputs

  // a -> c1
  args.push(~a);
  args.push(c1);
  S->addClause(args);

  // b -> c1
  args[0] = ~b;
  // Already there: args[1] = c1;
  S->addClause(args);

  // !c2 -> !a v !b'
  args[0] = ~a;
  args[1] = ~b;
  args.push(c2);
  S->addClause(args);
}

// Direct Sorting and Direct m-Cardinality Natwork
template<class Solver>
bool Encoding_MW<Solver>::makeDirectNetwork(vector<Lit>& invars, vector<Lit>& outvars, unsigned k) {
  // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell:
  // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints", page 11
  // k is the desired size of sorted output

  // outvars should be created in this function
  assert(outvars.empty());
  unsigned n = invars.size();
  
  if (k == 0 || k > n) k = n;

  for (unsigned i=0 ; i < k ; i++) {
    S->newVar();
    Lit ret = mkLit((unsigned)S->nVars()-1);
    outvars.push_back(ret);
  }
  for (unsigned j=1 ; j <= k ; j++) {
    vec<Lit> args;
    for (unsigned i=0 ; i < j; i++)
      args.push(lit_Error);
    args.push(outvars[j-1]);
    DirectCardClauses(invars, 0, 0, j, args);
  }
  return true;
}
  
template<class Solver>
void Encoding_MW<Solver>::DirectCardClauses(vector<Lit>& invars, unsigned start, unsigned pos, unsigned j, vec<Lit>& args) {
  unsigned n = invars.size();
  if (pos == j) {
    S->addClause(args);
  } else {
    for (unsigned i = start ; i <= n - (j - pos) ; i++) {
      args[pos] = ~invars[i];
      DirectCardClauses(invars, i+1, pos+1, j, args);
    }
  }  
}

#endif // __Encodings_MW_h
