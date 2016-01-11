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
  bool make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3);
  void _3wiseSplit(vector<Lit> const& in, vector<Lit>& out1, vector<Lit>& out2, vector<Lit>& out3);
  
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
  make3wiseSel(out2, sorted2, k>>1);
  make3wiseSel(out3, sorted3, k>>2);

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
bool Encoding_MW<Solver>::make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3) {
  return true;
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
