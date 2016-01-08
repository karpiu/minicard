/* MiniCARD  Copyright 2012, Mark Liffiton, Jordyn Maglalang
 * See LICENSE file for license details
 *
 * Encodings.h - Helper class for creating cardinality constraints
 *
 */

#ifndef __Encodings_h
#define __Encodings_h

#include <assert.h>
#include <map>
#include <vector>
#include <iostream>
#include "core/SolverTypes.h"

using namespace std;

namespace Minisat {

template<class S, class D>
int writeMapToFile(const char *fileName, map<S,D>& myMap); // used in 
template<class S, class D>
int readMapFromFile(const char *fileName, map<S,D>& myMap);

enum EncodingType {
    ITE = 1,
    PSN = 2,
    PCN = 3,
    PSN3 = 4,
    PCN3 = 5,
    PAIRWISE = 6,
    CODISH = 7,
    PW_BIT = 8,
    PW_SEL = 9,
    CP13a = 11,
    CP13b = 12,
    SORT_3C = 13
};

template <class Solver>
class Encoding {
private:
    // Different types of cardinality constraint encodings
    // These should not be called other than from makeAtMost()
    Lit makeAtMostITE(vector<Lit> lits, unsigned k, map<pair<int,int>, Lit>& subexprs);
    bool makeAtMostPairNet(const vector<Lit>& lits, unsigned const k, bool cardnet, vector<Lit>* outvars);
    bool makeAtMostPairwise(const vector<Lit>& lits, const int k);
    bool makeCodishConstr(const vector<Lit>& lits, unsigned const k, vector<Lit>* outvars);
    bool makePwbitConstr(const vector<Lit>& lits, unsigned const k, vector<Lit>* outvars);

    // Produce a sorting network, filling in outvars and constraints with the created output variables and network constraints
    void makeSortNet(vector<Lit>& invars, vector<Lit>& outvars);
    
    // Produce a cardinality network, filling in outvars and constraints with the created output variables and network constraints
    // Returns true if "all false" condition triggered (k=0)
    bool makeCardNet(vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);

    // Siec selekcji Codisha
    bool makeCodish(vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);
    
    // Nasza siec selekcji
    bool makePwbit(vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);

    // Pairwise Splitting
    void pwSplit(vector<Lit> const& in, vector<Lit>& out1, vector<Lit>& out2);
    // Pairwise Merging
    void pwMerge(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars);

    // merger Codisha
    void pwCodishMerge(vector<Lit> const& in1, vector<Lit> const& in2, unsigned const k, vector<Lit>& outvars);
    
    // our mergers
    void pwBitMerge(vector<Lit> & in1, vector<Lit> const& in2, unsigned const k, vector<Lit>& outvars);
    void pwHalfBitMerge(vector<Lit> const& invars,  unsigned const k, vector<Lit>& outvars, bool const half);
    void selectFromSorted(vector<Lit> const& in1, vector<Lit> const& in2, unsigned const k, vector<Lit>& outvars);

    // Produce a comparator, following the "half merging network" construction
    // from Asin, et al. in "Cardinality Network and their Applications"
    // -or- a full 6-clause comparator, depending on encoding type selected.
    inline void makeComparator(Lit const& a, Lit const& b, Lit& c1, Lit& c2);

    // Recursively build all clauses required for the "pairwise encoding."
    //  i.e., create all (n choose k+1) subsets of size k+1 from the n literals in the AtMost,
    //        and make a clause stating at least one must be false from each set.
    void buildPairwise(const vector<Lit>& lits, vec<Lit>& clause, int highest, const int k);
    
    // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell:
    // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints"
    pair<int,int> ANORC13_Merge(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, bool gen = true);
    pair<int,int> ANORC13_Sorting(vector<Lit>& invars, vector<Lit>& outvars, bool gen = true);
    pair<int,int> ANORC13_SMerge(vector<Lit> const& in1, vector<Lit> const& in2, unsigned c, vector<Lit>& outvars, bool gen = true);
    pair<int,int> ANORC13_Card(vector<Lit>& invars, unsigned m, vector<Lit>& outvars, bool gen = true);
    bool makeANORC13_Card(const vector<Lit>& lits, unsigned const k, vector<Lit>* p_outvars);
    pair<int,int> ANORC13_DirectMerge(vector<Lit> const& in1, vector<Lit> const& in2, unsigned c, vector<Lit>& outvars, bool gen);
    pair<int,int> ANORC13_DirectCard(vector<Lit>& invars, unsigned m, vector<Lit>& outvars, bool gen);
    unsigned ANORC13_DirectCardClauses(vector<Lit>& invars, unsigned start, unsigned pos, unsigned k, vec<Lit>& args);
    static const long long int lambda = 5; // used to optimize expression: lambda * #vars + #claues
    map<unsigned,unsigned> sort_optimal_split_point;
    map<pair<unsigned,unsigned>,unsigned> card_optimal_split_point;

    // functions for 3-sorter based selection networks
    void build3sort(vector<Lit> const& invars, vector<Lit>& outvars);
    
    // MiniSAT Solver
    Solver* S;

    // The constraint type (set for every constraint made by this Encoding object)
    EncodingType ctype;
    
    // The type of 3-clause to use for a single comparator.
    // if true then: (a => c) ^ (b => c) ^ (a ^ b => d)
    // if false then: (d => a) ^ (d => b) ^ (c => a v b)
    bool propagate_ones;

    inline unsigned pow2roundup (unsigned x) {
      if(x == 0) return 0;
      --x;
      x |= x >> 1;
      x |= x >> 2;
      x |= x >> 4;
      x |= x >> 8;
      x |= x >> 16;
      return x+1;
    }
    
public:
    
    Encoding(Solver* _S, EncodingType const _ctype) : S(_S), ctype(_ctype), propagate_ones(true) {
        if (ctype == CP13a || ctype == CP13b) {
           readMapFromFile(ctype==CP13a?"/var/tmp/sortmap13a.dat":"/var/tmp/sortmap13b.dat",sort_optimal_split_point);
           readMapFromFile(ctype==CP13a?"/var/tmp/cardmap13a.dat":"/var/tmp/cardmap13b.dat",card_optimal_split_point);
        }
    }
    ~Encoding() {
    }

    void writeMaps(void) {
        if (ctype == CP13a || ctype == CP13b) {
            writeMapToFile(ctype==CP13a?"/var/tmp/sortmap13a.dat":"/var/tmp/sortmap13b.dat",sort_optimal_split_point);
            writeMapToFile(ctype==CP13a?"/var/tmp/cardmap13a.dat":"/var/tmp/cardmap13b.dat",card_optimal_split_point);
        }
    }

    
    // build an AtMost or AtLeast constraint following the specified type
    // outvars, if not NULL and if ctype is cardinality or sorting network,
    //  will contain the network's "output" variables, which can be used to tighten the constraint later.
    bool makeAtMost(vector<Lit>& lits, unsigned const k, vector<Lit>* outvars = NULL);
    bool makeAtLeast(vector<Lit>& lits, unsigned const k, vector<Lit>* outvars = NULL);
};



// Function implementations follow

template<class Solver>
void Encoding<Solver>::build3sort(vector<Lit> const& invars, vector<Lit>& outvars) {
  assert(invars.size()==3);
  assert(outvars.size()==3);

  S->newVar();
  outvars[0] = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  outvars[1] = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  outvars[2] = mkLit((unsigned int)S->nVars()-1);

  // direct 3 sorter requiers 7 clauses
  vec<Lit> c1, c2, c3, c4, c5, c6, c7;
  c1.push(~invars[0]);
  c1.push(outvars[0]);

  c2.push(~invars[1]);
  c2.push(outvars[0]);

  c3.push(~invars[2]);
  c3.push(outvars[0]);

  c4.push(~invars[0]);
  c4.push(~invars[1]);
  c4.push(outvars[1]);

  c5.push(~invars[0]);
  c5.push(~invars[2]);
  c5.push(outvars[1]);

  c6.push(~invars[1]);
  c6.push(~invars[2]);
  c6.push(outvars[1]);

  c7.push(~invars[0]);
  c7.push(~invars[1]);
  c7.push(~invars[2]);
  c7.push(outvars[2]);

  S->addClause(c1);
  S->addClause(c2);
  S->addClause(c3);
  S->addClause(c4);
  S->addClause(c5);
  S->addClause(c6);
  S->addClause(c7);
}

template<class Solver>
bool Encoding<Solver>::makeAtLeast(vector<Lit>& lits, unsigned const k, vector<Lit>* outvars) {
    // maintain invariant that k<=|lits|/2
    if( k > lits.size()/2 ) {
      for ( unsigned i=0 ; i < lits.size() ; i++ ) {
        lits[i] = ~lits[i];
      }
      return makeAtMost(lits, lits.size() - k, outvars);
    }

    // for encodings other than CODISH and PW_BIT use AtMost constraint no mather the invariant k<=|lits|/2
    if(ctype != CODISH && ctype != PW_BIT && ctype != PW_SEL) {
      for ( unsigned i=0 ; i < lits.size() ; i++ ) {
        lits[i] = ~lits[i];
      }
      return makeAtMost(lits, lits.size() - k, outvars);
    }

    // propagate zeros forward for AtLeast constraint
    propagate_ones=false;

    switch(ctype) {
    case CODISH:
      return makeCodishConstr(lits, k, outvars);
    case PW_BIT:
    case PW_SEL:
      return makePwbitConstr(lits, k, outvars); 
    default:
        assert(0);
        return false;
    }
}

template<class Solver>
bool Encoding<Solver>::makeAtMost(vector<Lit>& lits, unsigned const k, vector<Lit>* outvars) {
    // maintain invariant that k<=|lits|/2 if type is CODISH or PW_BIT or PW_SEL
    if(ctype == CODISH || ctype == PW_BIT || ctype == PW_SEL) {
      if( k > lits.size()/2 ) {
	for ( unsigned i=0 ; i < lits.size() ; i++ ) {
	  lits[i] = ~lits[i];
	}
	return makeAtLeast(lits, lits.size() - k, outvars);
      }
    }

    // propagate ones forward for AtMost constraint
    propagate_ones=true;

    switch(ctype) {
    case ITE:
        {
            // Cache of subexpressions for the ITE formulation.
            // Needed in order to make a DAG instead of an exponentially large tree.
            map<pair<int,int>, Lit> subexprs;
            Lit ret = makeAtMostITE(lits, k, subexprs);
            if(ret != lit_Undef)S->addClause(ret);
            return true;
        }
    case PSN:
    case PSN3:
        return makeAtMostPairNet(lits, k, false,outvars);
    case PCN:
    case PCN3:
        return makeAtMostPairNet(lits, k, true,outvars);
    case PAIRWISE:
        return makeAtMostPairwise(lits, k);
    case CODISH:
      return makeCodishConstr(lits, k, outvars);
    case PW_BIT:
    case PW_SEL:
      return makePwbitConstr(lits, k, outvars);
    case CP13a:
    case CP13b:
      return makeANORC13_Card(lits, k, outvars);
    default:
        assert(0);
        return false;
    }
}


template<class Solver>
Lit Encoding<Solver>::makeAtMostITE(vector<Lit> lits, unsigned k, map<pair<int,int>, Lit>& subexprs) {
    // Inspired by "Evaluation of Cardinality Constraints on SMT-based Debugging" - though slightly improved?
    // This is a recursive construction.
    //  AtMost(lits, k) == ITE(lits[0], AtMost(lits[1:], k-1), AtMost(lits[1:], k))
    //  Easy base case: k==-1, return FALSE ; lits.size()<=k, return TRUE
    //   (doesn't work w/ unsigned k, and doesn't propagate as quickly as below, either)
    //  Better base case: k==0, all lits are FALSE ; lits.size()<=k, return TRUE
    //
    //  It is crucial to make it a DAG (reuse subexpressions) to avoid exponential size.

    // No constraint required. Return a trivial literal
    if (lits.size() <= k) {
        return lit_Undef;
    }

    // Create a new literal that will imply this particular constraint.
    S->newVar();
    Lit ret = mkLit((unsigned int)S->nVars()-1);

    // All remaining literals must be negated
    if (k == 0) {
        vec<Lit> args;
        args.push(~ret);
        
        for (unsigned i = 0 ; i < lits.size(); i++) {
            args.push(~lits[i]);
            S->addClause(args);
            args.pop();
            
            /*Print out new clauses
            std::cout << "( -" << var(ret) << " ";
            std::cout << ((sign(~lits[i])) ? "-" : "");
            std::cout << var(lits[i]) << " " << ") " << endl;*/
        }
        return ret;
    }

    // look for an existing ITE subexpression for this size and bound
    pair<int,int> cur(lits.size(), k);
    map<pair<int,int>, Lit>::iterator it = subexprs.find(cur);

    // if we have one, use it
    if (it != subexprs.end()) {
        return (*it).second;
    }
    // otherwise, build it
    
    // using last element (back) to make removal O(1)
    Lit lit0 = lits.back();
    lits.pop_back();
    
    // build the ITE recursively
    
    //Create and add each clause to the solver
    vec<Lit> newClauseA;
    vec<Lit> newClauseB;
    
    //First Clause
    Lit trueBranch = makeAtMostITE(lits,k-1,subexprs);
    if (trueBranch != lit_Undef) {
        newClauseA.push(~ret);
        newClauseA.push(~lit0);
        newClauseA.push(trueBranch);
        S->addClause(newClauseA);
        
        /*Print out the new clause
        std::cout << "( ";
        for (int j=0;j<newClauseA.size();j++) { 
            if (sign(newClauseA[j])) std::cout << "-";
            std::cout << var(newClauseA[j]) << " ";
        }
        std::cout << ") " << endl;*/
    }
    
    //Second Clause
    Lit falseBranch = makeAtMostITE(lits,k,subexprs);
    if (falseBranch != lit_Undef) {
        newClauseB.push(~ret);
        newClauseB.push(lit0);
        newClauseB.push(falseBranch);
        S->addClause(newClauseB);
        
        /*Print out the new clause
        std::cout << "( ";
        for (int k=0;k<newClauseB.size();k++) {
            if (sign(newClauseB[k])) std::cout << "-";
            std::cout << var(newClauseB[k]) << " ";
        }
        std::cout << ")" << endl;*/
    }

    // third (redundant, but helps unit propagation)
    // only needed if neither branch is trivially satisfied
    if (falseBranch != lit_Undef && trueBranch != lit_Undef) {
        vec<Lit> newClauseC;
        newClauseC.push(~ret);
        newClauseC.push(falseBranch);
        newClauseC.push(trueBranch);
        S->addClause(newClauseC);
    }
    
    // store reference literal for later use
    subexprs[cur] = ret;

    return ret;
}

template<class Solver>
bool Encoding<Solver>::makePwbitConstr(const vector<Lit>& lits, unsigned const k, vector<Lit>* p_outvars) {
    // input vars
    vector<Lit> invars;
    for (unsigned i = 0 ; i < lits.size() ; i++) {
        invars.push_back(lits[i]);
    }

    for (unsigned i = lits.size() ; i < pow2roundup(lits.size()) ; i++) {
      invars.push_back(lit_Undef);
    }
    
    //output vars
    vector<Lit> outvars;
    
    makePwbit(invars, outvars, k);
    
    for (unsigned i = 0 ; i < outvars.size() ; i++) {
        if (outvars[i] == lit_Undef)  continue;
	if (p_outvars) {
            p_outvars->push_back(outvars[i]);
        }
    }

    if ( propagate_ones ) {
      // at most
      for (unsigned i = k ; i < outvars.size() ; i++) {
	if(outvars[i] == lit_Undef) continue;
        S->addClause(~outvars[i]);
      }
    } else {
      // at least
      for (unsigned i = 0 ; i < k ; i++) { // assuming that k <= |outvars|
	if(outvars[i] == lit_Undef) continue;
        S->addClause(outvars[i]);
      }
    }

    return true;
}

template<class Solver>
bool Encoding<Solver>::makeCodishConstr(const vector<Lit>& lits, unsigned const k, vector<Lit>* p_outvars) {
    // input vars
    vector<Lit> invars;
    for (unsigned i = 0 ; i < lits.size() ; i++) {
        invars.push_back(lits[i]);
    }
    
    //output vars
    vector<Lit> outvars;

    makeCodish(invars, outvars, k);
    
    for (unsigned i = 0 ; i < outvars.size() ; i++) {
        if (outvars[i] == lit_Undef)  continue;
	if (p_outvars) {
            p_outvars->push_back(outvars[i]);
        }
    }

    if ( propagate_ones ) {
      // at most
      for (unsigned i = k ; i < outvars.size() ; i++) {
	if(outvars[i] == lit_Undef) continue;
        S->addClause(~outvars[i]);
      }
    } else {
      // at least
      for (unsigned i = 0 ; i < k ; i++) { // assuming that k <= |outvars|
	if(outvars[i] == lit_Undef) continue;
        S->addClause(outvars[i]);
      }
    }

    return true;
}

template<class Solver>
bool Encoding<Solver>::makeAtMostPairNet(const vector<Lit>& lits, unsigned const k, bool const cardnet, vector<Lit>* p_outvars) {
    //  AtMost(lits, k) :=
    //    (Out = Sort(lits)) ^ (Out[k+1] = 0)
    //
    //  Use pairwise sorting networks
    //  If cardnet true, then make it a cardinality network (simplified/reduced sorting network)

    // setup the input literals
    vector<Lit> invars;
    for (unsigned i = 0 ; i < lits.size() ; i++) {
        invars.push_back(lits[i]);
    }
    // make a place to get the "output" variables for the sorting network
    vector<Lit> outvars;
    
    // build the network
    if (cardnet) {
        makeCardNet(invars, outvars, k);
    }
    else {
        makeSortNet(invars, outvars);
    }

    // populate p_outvars, if not NULL,
    // and enforce AtMost k ("out" indexes k and above == 0)
    for (unsigned i = 0 ; i < outvars.size() ; i++) {
        if (outvars[i] == lit_Undef)  continue;

        if (p_outvars) {
            p_outvars->push_back(outvars[i]);
        }
        // make these constraints here
        if (i >= k) {
            S->addClause(~outvars[i]);
        }
    }
    return true;
}


template<class Solver>
inline void Encoding<Solver>::makeComparator(Lit const& a, Lit const& b, Lit& c1, Lit& c2) {
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

    if (ctype == PSN3 || ctype == PCN3 || ctype == CODISH || ctype == PW_BIT || ctype >= PW_SEL) {
        // 3-clause comparator,
        // because AtMosts only need implications from 0 on the outputs to 0 on the inputs
        // and AtLeasts other way around

      if( propagate_ones ) {
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
      } else {
	// c2 -> a
	args.push(~c2);
        args.push(a);
        S->addClause(args);

	// c2 -> b
	// Already there: args[0] = ~c2;
	args[1] = b;
	S->addClause(args);

	// c1 -> a v b
	args[0] = a;
        args[1] = b;
        args.push(~c1);
        S->addClause(args);
      }
    }
    else {
        // full 6-clause comparator

        // !c2 -> !a v !b
        args.push(~a);
        args.push(~b);
        args.push(c2);
        S->addClause(args);
        
        //  a -> c1
        args.pop();
        // Already there: args[0] = ~a;
        args[1] = c1;
        S->addClause(args);

        // b -> c1
        args[0] = ~b;
        // Already there: args[1] = c1;
        S->addClause(args);

        // c1 -> a v b
        args[0] = a;
        args[1] = b;
        args.push(~c1);
        S->addClause(args);

        // !a -> !c2
        args.pop();
        // Already there: args[0] = a;
        args[1] = ~c2;
        S->addClause(args);

        // !b -> !c2
        args[0] = b;
        // Already there: args[1] = ~c2;
        S->addClause(args);
   }
}

template<class Solver>
bool Encoding<Solver>::makePwbit(vector<Lit>& invars, vector<Lit>& outvars, unsigned const k) {
    assert(outvars.empty());
    if (k == 0) {
        for (unsigned i = 0 ; i < invars.size() ; i++) {
	  if ((invars[i] != lit_Undef) && propagate_ones) {
                S->addClause(~invars[i]);
            }
        }
        return true;
    }

    if (k >= invars.size()) {
        makeSortNet(invars, outvars);
        return false;
    }
    
    if (invars.size() == 1) {
        outvars.push_back(invars[0]);
        return false;
    }
    
    if (invars.size() == 2) {
        // make a simple comparator
        outvars.push_back(lit_Error);
        outvars.push_back(lit_Error);
        makeComparator(invars[0], invars[1], outvars[0], outvars[1]);
        return false;
    }

    // split
    vector<Lit> out1, out2;
    pwSplit(invars, out1, out2);

    // recursive calls
    vector<Lit> sorted1, sorted2;
    makePwbit(out1, sorted1, k);
    makePwbit(out2, sorted2, k>>1);

    // maintaining invariant |outvars| >= min(k, |invars|)
    while (sorted1.size() < k) sorted1.push_back(lit_Undef);
    
    // merge
    if (k>1) {

      // making |sorted1| = k
      // and |sorted2| = k>>1
      while (sorted1.size() > k) {
	if ((sorted1.back() != lit_Undef) && propagate_ones) {
	  S->addClause(~sorted1.back());
	}
	sorted1.pop_back();
      }
      
      while (sorted2.size() > (k>>1)) {
	if ((sorted2.back() != lit_Undef) && propagate_ones) {
	  S->addClause(~sorted2.back());
	}
	sorted2.pop_back();
      }
      
      while (sorted2.size() < (k>>1)) sorted2.push_back(lit_Undef);

      // merge
      if (ctype == PW_BIT)
        pwBitMerge(sorted1, sorted2, k, outvars);
      else //ctype == PW_SEL
        selectFromSorted(sorted1, sorted2, k, outvars);
    }
    else {
        outvars = sorted1;
    }
    return false;
}

template<class Solver>
void Encoding<Solver>::selectFromSorted(vector<Lit> const& in1, vector<Lit> const& in2, unsigned const k, vector<Lit>& outvars) {
    assert(in1.size()==k);
    assert(in2.size()==k/2);
    assert(k > 1);
    // both in1 and in2 are sorted and in1 dominates in2 (in1[i] >= in2[i], i=0,...,k/2)
    // on exit outvars.size() = k+k/2, elements of outvars[0..k-1] are sorted and are >= all other elements 

    vector<Lit> stageIn1 = in1, stageIn2 = in2;
    int K, logK;

    for (K = 1, logK=0; K < k; K*=2, ++logK);
    
    K/=2;
    for (int stage=1; stage <= logK; ++stage, K/=2) {
      vector<Lit> out1, out2;
      int top;
      
      for (int i = 0 ; i < K ; i++) 
	out1.push_back(stageIn1[i]);
      for (top = 0 ; top < k/2 && top+K < k; top++) {
        out1.push_back(lit_Error);
        out2.push_back(lit_Error);
        makeComparator(stageIn2[top], stageIn1[top+K], out2[top], out1[top+K]);
      }
      for (int i = top+K ; i < k ; i++) 
	out1.push_back(stageIn1[i]);
      while (top < k/2) 
	out2.push_back(stageIn2[top++]);
      stageIn1 = out1; stageIn2 = out2;
    }
    for (int i=0; i < k/2; ++i) {
      outvars.push_back(stageIn1[i]);
      outvars.push_back(stageIn2[i]);
    }
    for (int i=k/2; i < k; ++i)
      outvars.push_back(stageIn1[i]);
}

template<class Solver>
void Encoding<Solver>::pwBitMerge(vector<Lit> & in1, vector<Lit> const& in2, unsigned const k, vector<Lit>& outvars) {
    assert(in1.size()==k);
    assert(in2.size()==(k>>1));

    for (unsigned i = k ; i < pow2roundup(k) ; i++) {
      in1.push_back(lit_Undef);
    }

    vector<Lit> out1, out2;

    int K = in1.size();
    
    // bit_split
    for (unsigned i = 0 ; i < (k>>1) ; i++) {
      out1.push_back(lit_Error);
      out2.push_back(lit_Error);
      makeComparator(in1[K-(k>>1)+i], in2[(k>>1)-i-1], out1[i], out2[i]);
    }
    
    // to pewnie mozna zapisac ladniej korzystajac z operacji konkatenacji
    vector<Lit> hbit_in;
    
    for(unsigned i = 0 ; i < K-out1.size() ; i++) {
      hbit_in.push_back(in1[i]);
    }
    for(unsigned i = 0 ; i < out1.size() ; i++) {
      hbit_in.push_back(out1[i]);
    }

    if(propagate_ones) {
      for(unsigned i=0 ; i < out2.size() ; i++) {
	if(out2[i] == lit_Undef) continue;
	S->addClause(~out2[i]);
      }
    }
      
    // pw_hbit_merger
    pwHalfBitMerge(hbit_in, K, outvars, true); 
}

template<class Solver>
void Encoding<Solver>::pwHalfBitMerge(vector<Lit> const& invars,  unsigned const k, vector<Lit>& outvars, bool const half) {
    assert(invars.size()==k);
    // invariant: k is a power of 2

    if (k == 1) {
      outvars.push_back(invars[0]);
      return;
    }

    vector<Lit> out1, out2;
    
    if ( half ) { // use half splitter
      if ( k==2 ) {
	outvars.push_back(invars[0]);
        outvars.push_back(invars[1]);
        return;
      }

      vector<Lit> hout1, hout2, in1, in2;

      // half split
      for (unsigned i = 0 ; i < k/4 ; i++) {
	hout1.push_back(lit_Error);
	hout2.push_back(lit_Error);
	makeComparator(invars[k/2-i-1], invars[k-i-1], hout1[i], hout2[i]);
      }

      // inputs for recursive calls
      for (unsigned i = 0 ; i < k/4 ; i++ ) {
	in1.push_back(invars[i]);
      }

      for (int i = hout1.size()-1 ; i>=0 ; i-- ) {
	in1.push_back(hout1[i]);
      }

      for (unsigned i = k/2 ; i < k-hout2.size() ; i++ ) {
	in2.push_back(invars[i]);
      }
      for (int i = hout2.size()-1 ; i>=0 ; i-- ) {
	in2.push_back(hout2[i]);
      }
      
      // recursive calls
      pwHalfBitMerge(in1, in1.size(), out1, true);
      pwHalfBitMerge(in2, in2.size(), out2, false);

    } else { // use normal splitter
      if ( k==2 ) {
	outvars.push_back(lit_Error);
        outvars.push_back(lit_Error);
        makeComparator(invars[0], invars[1], outvars[0], outvars[1]);
	return;
      }

      vector<Lit> sout1, sout2, in1, in2;
      
      // normal split
      for (unsigned i = 0 ; i < k/2 ; i++) {
	sout1.push_back(lit_Error);
	sout2.push_back(lit_Error);
	makeComparator(invars[i], invars[k/2+i], sout1[i], sout2[i]);
      }
      
      // recursive calls
      pwHalfBitMerge(sout1, sout1.size(), out1, false);
      pwHalfBitMerge(sout2, sout2.size(), out2, false);
    }

    // concatenating the results
    for (unsigned i = 0; i < out1.size(); i++) { outvars.push_back(out1[i]); }
    for (unsigned i = 0; i < out2.size(); i++) { outvars.push_back(out2[i]); }
}

template<class Solver>
bool Encoding<Solver>::makeCodish(vector<Lit>& invars, vector<Lit>& outvars, unsigned const k) {
    assert(outvars.empty());
    if (k == 0) {
        for (unsigned i = 0 ; i < invars.size() ; i++) {
	  if ((invars[i] != lit_Undef) && propagate_ones) {
                S->addClause(~invars[i]);
            }
        }
        return true;
    }

    if (k >= invars.size()) {
        makeSortNet(invars, outvars);
        return false;
    }
    
    if (invars.size() == 1) {
        outvars.push_back(invars[0]);
        return false;
    }
    
    if (invars.size() == 2) {
        // make a simple comparator
        outvars.push_back(lit_Error);
        outvars.push_back(lit_Error);
        makeComparator(invars[0], invars[1], outvars[0], outvars[1]);
        return false;
    }

    // pad invars to have an even number of literals
    if (invars.size() % 2 != 0) {
        invars.push_back(lit_Undef);
    }

    // split
    vector<Lit> out1, out2;
    pwSplit(invars, out1, out2);

    // recursive calls
    vector<Lit> sorted1, sorted2;
    makeCodish(out1, sorted1, k);
    bool allFalse = makeCodish(out2, sorted2, k>>1);

    //maintaining invariant |outvars| >= min(k, |invars|)
    while (sorted1.size() < k) sorted1.push_back(lit_Undef);
    
    // merge
    if (!allFalse) {

      // making |sorted1|=|sorted2|=k
      while (sorted1.size() > k) {
	if ((sorted1.back() != lit_Undef) && propagate_ones) {
	  S->addClause(~sorted1.back());
	}
	sorted1.pop_back();
      }
      
      while (sorted2.size() > k) {
	if (sorted2.back() != lit_Undef && propagate_ones) {
	  S->addClause(~sorted2.back());
	}
	sorted2.pop_back();
      }
      
      while (sorted2.size() < k) sorted2.push_back(lit_Undef);

      // merge
      pwMerge(sorted1, sorted2, outvars);
    }
    else {
        outvars = sorted1;
    }
    return false;
}
 
template<class Solver>
void Encoding<Solver>::makeSortNet(vector<Lit>& invars, vector<Lit>& outvars) {
    // Pairwise Sorting Network, as described in "pairwise cardinality networks"
    //  by Codish and Zazon-Ivry
    //
    // This is a recursive construction.
    //
    //  Sort(invars) :=
    //    if invars.size <= 2: simple comparator [produces Out from invars]
    //    else:
    //      (<A1,A2> = PairwiseSplit(invars)) ^ (B1 = Sort(A1)) ^ (B2 = Sort(A2)) ^ (Out = Merge(B1,B2))

    // outvars should be created in this function
    assert(outvars.empty());

    if (invars.size() == 1) {
        // nothing to sort, thus already sorted
        outvars.push_back(invars[0]);
        return;
    }

    if (invars.size() == 2) {
        // make a simple comparator
        outvars.push_back(lit_Error);
        outvars.push_back(lit_Error);
        makeComparator(invars[0], invars[1], outvars[0], outvars[1]);
        return;
    }

    // pad invars to have an even number of literals
    if (invars.size() % 2 != 0) {
        invars.push_back(lit_Undef);
    }

    // do the complicated stuff
    vector<Lit> out1, out2;
    pwSplit(invars, out1, out2);
    vector<Lit> sorted1, sorted2;
    makeSortNet(out1, sorted1);
    makeSortNet(out2, sorted2);
    pwMerge(sorted1, sorted2, outvars);
}

template<class Solver>
bool Encoding<Solver>::makeCardNet(vector<Lit>& invars, vector<Lit>& outvars, unsigned const k) {
    // Pairwise Cardinality Network, as described in "pairwise cardinality networks"
    //  by Codish and Zazon-Ivry
    //
    // This is a recursive construction.
    //
    //  Sort(invars) :=
    //    if invars.size <= 2: simple comparator [produces Out from invars]
    //    else:
    //      (<A1,A2> = PairwiseSplit(invars)) ^ (B1 = Sort(A1)) ^ (B2 = Sort(A2)) ^ (Out = Merge(B1,B2))
    //   Plus simplifications based on bound k

    // outvars should be created in this function
    assert(outvars.empty());
    if (k == 0) {
        for (unsigned i = 0 ; i < invars.size() ; i++) {
            outvars.push_back(lit_Undef);
            // May be receiving lit_Undef, indicating a FALSE already.
            // In that case, no constraint to add.
            if (invars[i] != lit_Undef) {
                S->addClause(~invars[i]);
            }
        }
        return true;
    }

    if (invars.size() == 1) {
        // nothing to sort, thus already sorted
        outvars.push_back(invars[0]);
        return false;
    }

    if (invars.size() == 2) {
        // make a simple comparator
        outvars.push_back(lit_Error);
        outvars.push_back(lit_Error);
        makeComparator(invars[0], invars[1], outvars[0], outvars[1]);
        return false;
    }

    // pad invars to have an even number of literals
    if (invars.size() % 2 != 0) {
        invars.push_back(lit_Undef);
    }

    // do the complicated stuff
    vector<Lit> out1, out2;
    pwSplit(invars, out1, out2);

    vector<Lit> sorted1, sorted2;
    makeCardNet(out1, sorted1, k);
    bool allFalse = makeCardNet(out2, sorted2, k>>1);

    if (!allFalse) {
        // not the most elegant, but this makes the sizes match for pwMerge, and the extra Falses shouldn't
        // have much/any impact on the resulting constraints.
        while (sorted2.size() < sorted1.size()) {
            sorted2.push_back(lit_Undef);
        }
        pwMerge(sorted1, sorted2, outvars);
    }
    else {
        outvars = sorted1;
    }
    return false;
}

// Pairwise Splitting
template<class Solver>
void Encoding<Solver>::pwSplit(vector<Lit> const& in, vector<Lit>& out1, vector<Lit>& out2) {
    // out1/2 should be created in this function
    assert(out1.empty());
    assert(out2.empty());

    // in should have an even number of elements
    assert(in.size() % 2 == 0);

    for (unsigned i = 0 ; i < in.size()/2 ; i++) {
        out1.push_back(lit_Error);
        out2.push_back(lit_Error);
        makeComparator(in[i*2], in[i*2+1], out1[i], out2[i]);
    }
}

template<class Solver>
void Encoding<Solver>::pwCodishMerge(vector<Lit> const& in1, vector<Lit> const& in2, unsigned const k, vector<Lit>& outvars) {
  // we use normal pwMerge at the moment
}
 
// Pairwise Merging
template<class Solver>
void Encoding<Solver>::pwMerge(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars) {
    // require an equal number of elements in both in1 and in2
    assert(in1.size() == in2.size());

    unsigned n = in1.size();

    if (n == 1) {
        // we can assume that we have done pairwise sorting earlier, so in1[0] > in2[0]
        outvars.push_back(in1[0]);
        outvars.push_back(in2[0]);
        return;
    }

    // in paper, indexes start from 1, here, from 0, so evens/odds nomenclature is switched
    vector<Lit> in1odds, in2odds, in1evens, in2evens, tmp1, tmp2;
    // in1evens = in1[0,2,4,...], in2evens same
    // in1odds  = in1[1,3,5,...], in2odds same
    for (unsigned i = 0 ; i < (n+1) / 2 ; i++) {
        in1evens.push_back(in1[i*2]);
        in2evens.push_back(in2[i*2]);
        if (i*2 + 1 < n) {
            in1odds.push_back(in1[i*2+1]);
            in2odds.push_back(in2[i*2+1]);
        }
        else {
            in1odds.push_back(lit_Undef);
            in2odds.push_back(lit_Undef);
        }
    }

    pwMerge(in1evens, in2evens, tmp1);
    pwMerge(in1odds, in2odds, tmp2);

    // set outvars[0] = tmp1[0];
    outvars.push_back(tmp1[0]);

    for (unsigned i = 0 ; i < n-1 ; i++) {
        outvars.push_back(lit_Error);
        outvars.push_back(lit_Error);
        makeComparator(tmp2[i], tmp1[i+1], outvars[i*2+1], outvars[i*2+2]);
    }

    // set outvars[2n-1] = tmp2[n-1];
    outvars.push_back(tmp2[n-1]);
}

 
// lits: set of literals in AtMost (set of elements from which subsets are drawn)
// clause: growing clause (subset of lits)
// highest: highest index in lits currently added to clause
// k: AtMost bound, so k+1 = target subset size
//
// Generates all (lits.size() choose k+1) subsets of size k+1 from lits.
template<class Solver>
void Encoding<Solver>::buildPairwise(const vector<Lit>& lits, vec<Lit>& clause, int highest, const int k) {
    // Base case: fully populated subset, add to solver and backtrack
    if (clause.size() == k+1) {
        S->addClause(clause);
        return;
    }

    // Start at next highest index,
    // continue as long as there are enough remaining indexes to fill the required subset size.
    for (int i = highest+1 ; ((int)lits.size()-i) >= ((k+1) - clause.size()) ; i++) {
        // build a clause using this index
        clause.push(~lits[i]);
        buildPairwise(lits, clause, i, k);

        // backtrack
        clause.pop();
    }
}

template<class Solver>
bool Encoding<Solver>::makeAtMostPairwise(const vector<Lit>& lits, const int k) {
    //  AtMost(lits, k) :=
    //    PRODUCT[ one clause for every invalid assignment ]
    //
    //  NOT a pairwise sorting network.  This is the encoding Marques-Silva refers to as the "pairwise encoding."
    //  It's pairwise for AtMost1 (for which it is claimed to perform well), but for k>1, we must
    //  create one clause per subset of size k+1.

    vec<Lit> clause;
    buildPairwise(lits, clause, -1, k);

    return true;
}

// Odd-Even Merging
template<class Solver>
pair<int,int> Encoding<Solver>::ANORC13_Merge(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, bool gen) {
    // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell:
    // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints", pages 4-6

    unsigned a = in1.size(), b = in2.size();

    if (a == 1 && b == 1) {
        outvars.push_back(lit_Error);
        outvars.push_back(lit_Error);
        if (gen) makeComparator(in1[0], in2[0], outvars[0], outvars[1]);
        return make_pair(2,3);
    }
    if (a == 0) {
        for (unsigned i = 0 ; i < b ; i++)   
            outvars.push_back(in2[i]);
	return make_pair(0,0);
   }
     if (b == 0) {
        for (unsigned i = 0 ; i < a ; i++)   
            outvars.push_back(in1[i]);
	return make_pair(0,0);
   }
    // from now on: a > 0 && b > 0 && (a > 1 || b > 1)  
    
    // in paper, indexes start from 1, here, from 0, so evens/odds nomenclature is switched
    vector<Lit> in1odds, in2odds, in1evens, in2evens, tmp1, tmp2;
    // in1evens = in1[0,2,4,...], in2evens same
    // in1odds  = in1[1,3,5,...], in2odds same
    for (unsigned i = 0 ; i < a; i+=2) {
        in1evens.push_back(in1[i]);
        if (i + 1 < a) 
            in1odds.push_back(in1[i+1]);
    }
    for (unsigned i = 0 ; i < b; i+=2) {
        in2evens.push_back(in2[i]);
        if (i + 1 < b)
            in2odds.push_back(in2[i+1]);
    }

    if (ctype == CP13b) {
        vector<Lit> out, out1, out2;
        pair<int,int> evens = ANORC13_Merge(in1evens, in2evens, out1, false);
        pair<int,int> odds  = ANORC13_Merge(in1odds, in2odds, out2, false);
	pair<int,int> recursive = make_pair(evens.first+odds.first+(a+b-1)/2*2 , evens.second+odds.second+(a+b-1)/2*3);
	pair<int,int> direct = ANORC13_DirectMerge(in1, in2, 0, out, false);
	bool selectDirect = lambda * direct.first + direct.second < lambda * recursive.first + recursive.second;
	if (selectDirect && gen)
	    return ANORC13_DirectMerge(in1, in2, 0, outvars, true);
	if (! gen) {
            for (unsigned i = 0 ; i < a + b ; i++)
                outvars.push_back(lit_Error);
	    return (selectDirect ? direct : recursive);
	}
    }
    pair<int,int> evens = ANORC13_Merge(in1evens, in2evens, tmp1, gen);
    pair<int,int> odds  = ANORC13_Merge(in1odds, in2odds, tmp2, gen);

    // set outvars[0] = tmp1[0];
    outvars.push_back(tmp1[0]);

    for (unsigned i = 0 ; i < (a+b-1)/2 ; i++) {
        outvars.push_back(lit_Error);
        outvars.push_back(lit_Error);
        if (gen) makeComparator(tmp2[i], tmp1[i+1], outvars[i*2+1], outvars[i*2+2]);
    }

    // set outvars[a+b-1] if needed
    if ((a+b) % 2 == 0) // both even or both odd
        outvars.push_back(a % 2 == 0 ? tmp2[tmp2.size()-1] : tmp1[tmp1.size()-1]);
    return make_pair(evens.first+odds.first+(a+b-1)/2*2 , evens.second+odds.second+(a+b-1)/2*3);
}

// Odd-Even Sorting
template<class Solver>
pair<int,int> Encoding<Solver>::ANORC13_Sorting(vector<Lit>& invars, vector<Lit>& outvars, bool gen) {
    // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell:
    // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints", pages 6-7

    // outvars should be created in this function
    assert(outvars.empty());

    if (invars.size() == 1) {
        // nothing to sort, thus already sorted
        outvars.push_back(invars[0]);
        return make_pair(0,0);
    }

    if (invars.size() == 2) {
        // make a simple comparator
        outvars.push_back(lit_Error);
        outvars.push_back(lit_Error);
        if (gen) makeComparator(invars[0], invars[1], outvars[0], outvars[1]);
        return make_pair(2,3);
    }

    unsigned split_point;
    map<unsigned,unsigned>::iterator it = sort_optimal_split_point.find(invars.size());
    if (it == sort_optimal_split_point.end()) {
        unsigned minj = invars.size()/2;
	long long int min = LLONG_MAX;
	for (unsigned j = 1; j < invars.size() ; j++) {
            vector<Lit> in1, in2;
            for (unsigned i = 0 ; i < j ; i++)
	        in1.push_back(invars[i]);
            for (unsigned i = j ; i < invars.size() ; i++)
                in2.push_back(invars[i]);
            vector<Lit> sorted1, sorted2, out;
            pair<int,int> sort1 = ANORC13_Sorting(in1, sorted1, false);
            pair<int,int> sort2 = ANORC13_Sorting(in2, sorted2, false);
            pair<int,int> merge = ANORC13_Merge(sorted1, sorted2, out, false);
            long long int res = lambda*(sort1.first+sort2.first+merge.first) + sort1.second+sort2.second+merge.second;
	    if (res < min) { minj = j; min = res; }
	}
	if (ctype == CP13b) {
	    vector<Lit> out;
	    pair<int,int> direct = ANORC13_DirectCard(invars, invars.size(), out, false);
	    bool selectDirect = lambda * direct.first + direct.second < min;
	    sort_optimal_split_point[invars.size()] = split_point =  (selectDirect ? 0 : minj);
	} else
            sort_optimal_split_point[invars.size()] = split_point =  minj;
    } else
        split_point = it->second;

    if (ctype == CP13b && split_point == 0)
        return ANORC13_DirectCard(invars, invars.size(), outvars, gen);
    
    vector<Lit> in1, in2;
    for (unsigned i = 0 ; i < split_point ; i++)
        in1.push_back(invars[i]);
    for (unsigned i = split_point ; i < invars.size() ; i++)
       in2.push_back(invars[i]);
     
    vector<Lit> sorted1, sorted2;
    pair<int,int> sort1 = ANORC13_Sorting(in1, sorted1, gen);
    pair<int,int> sort2 = ANORC13_Sorting(in2, sorted2, gen);
    pair<int,int> merge = ANORC13_Merge(sorted1, sorted2, outvars, gen);
    return make_pair(sort1.first+sort2.first+merge.first , sort1.second+sort2.second+merge.second);
}

// Simplified Odd-Even Merging
template<class Solver>
pair<int,int> Encoding<Solver>::ANORC13_SMerge(vector<Lit> const& in1, vector<Lit> const& in2, unsigned c, 
					       vector<Lit>& outvars, bool gen) {
    // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell:
    // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints", pages 7-8
    // c is the desired size of sorted output

    unsigned a = in1.size(), b = in2.size();
    
    if (a+b <= c)
        return ANORC13_Merge(in1, in2, outvars, gen);

    if (a > c) a = c;
    if (b > c) b = c;
    if (a == 0) {
        for (unsigned i = 0 ; i < b ; i++)   
            outvars.push_back(in2[i]);
	return make_pair(0,0);
    }
    if (b == 0) {
        for (unsigned i = 0 ; i < a ; i++)   
            outvars.push_back(in1[i]);
	return make_pair(0,0);
    }
    if (a == 1 && b == 1 && c == 1) {
        if (gen) {
	    S->newVar();
	    Lit ret = mkLit((unsigned)S->nVars()-1);
            outvars.push_back(ret);
	    vec<Lit> args;
	    // in1[0] -> ret
	    args.push(~in1[0]);
	    args.push(ret);
	    S->addClause(args);
	    // in2[0] -> ret
	    args[0] = ~in2[0];
	    S->addClause(args);
	} else
            outvars.push_back(lit_Error);
        return make_pair(1,2);
    }
    // from now on: a > 0 && b > 0 && && a,b <= c && 1 < c < a + b 
    
    // in paper, indexes start from 1, here, from 0, so evens/odds nomenclature is switched
    vector<Lit> in1odds, in2odds, in1evens, in2evens, tmp1, tmp2;
    // in1evens = in1[0,2,4,...], in2evens same
    // in1odds  = in1[1,3,5,...], in2odds same
    for (unsigned i = 0 ; i < a; i+=2) {
        in1evens.push_back(in1[i]);
        if (i + 1 < a) 
            in1odds.push_back(in1[i+1]);
    }
    for (unsigned i = 0 ; i < b; i+=2) {
        in2evens.push_back(in2[i]);
        if (i + 1 < b)
            in2odds.push_back(in2[i+1]);
    }
    if (ctype == CP13b) {
        vector<Lit> out, out1, out2;
        pair<int,int> evens = ANORC13_SMerge(in1evens, in2evens, c/2+1, out1, false);
        pair<int,int> odds  = ANORC13_SMerge(in1odds, in2odds, c/2, out2, false);
	pair<int,int> recursive = make_pair(evens.first+odds.first + c-1 , evens.second+odds.second + (c%2 ? (3*c-3)/2 : (c-1)/2*3+2));
	pair<int,int> direct = ANORC13_DirectMerge(in1, in2, c, out, false);
	bool selectDirect = lambda * direct.first + direct.second < lambda * recursive.first + recursive.second;
	if (selectDirect && gen)
	    return ANORC13_DirectMerge(in1, in2, c, outvars, true);
	if (! gen) {
            for (unsigned i = 0 ; i < c ; i++)
                outvars.push_back(lit_Error);
	    return (selectDirect ? direct : recursive);
	}
    }
    pair<int,int> evens = ANORC13_SMerge(in1evens, in2evens, c/2+1, tmp1, gen);
    pair<int,int> odds  = ANORC13_SMerge(in1odds, in2odds, c/2, tmp2, gen);

    // set outvars[0] = tmp1[0];
    outvars.push_back(tmp1[0]);

    for (unsigned i = 0 ; i < (c-1)/2 ; i++) {
        outvars.push_back(lit_Error);
        outvars.push_back(lit_Error);
        if (gen) makeComparator(tmp2[i], tmp1[i+1], outvars[i*2+1], outvars[i*2+2]);
    }

    // set outvars[c-1] if needed
    if (c % 2 == 0) { // c is even
        if (gen) {
	    S->newVar();
	    Lit ret = mkLit((unsigned)S->nVars()-1);
            outvars.push_back(ret);
	    vec<Lit> args;
	    // tmp2[c/2-1] -> ret
	    args.push(~tmp2[c/2-1]);
	    args.push(ret);
	    S->addClause(args);
	    // tmp1[c/2] -> ret
	    args[0] = ~tmp1[c/2];
	    S->addClause(args);
	} else
            outvars.push_back(lit_Error);
    }
    return make_pair(evens.first+odds.first + c-1 , evens.second+odds.second + (c%2 ? (3*c-3)/2 : (c-1)/2*3+2));
}

// m-Cardinality Natwork, that is, Simplified Odd-Even Sorting
template<class Solver>
pair<int,int> Encoding<Solver>::ANORC13_Card(vector<Lit>& invars, unsigned m, vector<Lit>& outvars, bool gen) {
    // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell:
    // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints", page 9
    // m is the desired size of sorted output
    
    // outvars should be created in this function
    assert(outvars.empty());
    if (invars.size() <= m)
        return ANORC13_Sorting(invars, outvars, gen);

    unsigned split_point;
    map<pair<unsigned,unsigned>,unsigned>::iterator it = card_optimal_split_point.find(make_pair(invars.size(),m));
    if (it == card_optimal_split_point.end()) {
        unsigned minj = invars.size()/2;
        long long int min = LLONG_MAX;
        pair<int,int> minpair = make_pair(INT_MAX,INT_MAX);
	for (unsigned j = 1; j < invars.size() ; j++) {
            vector<Lit> in1, in2;
            for (unsigned i = 0 ; i < j ; i++)
	        in1.push_back(invars[i]);
            for (unsigned i = j ; i < invars.size() ; i++)
                in2.push_back(invars[i]);
            vector<Lit> sorted1, sorted2, out;
            pair<int,int> sort1 = ANORC13_Card(in1, m, sorted1, false);
            pair<int,int> sort2 = ANORC13_Card(in2, m, sorted2, false);
            pair<int,int> merge = ANORC13_SMerge(sorted1, sorted2, m, out, false);
            pair<int,int> result = make_pair(sort1.first+sort2.first+merge.first, 
                                             sort1.second+sort2.second+merge.second);
            long long int res = lambda*result.first + result.second;
	    if (res < min) { minj = j; min = res; minpair = result; }
	}
	if (ctype == CP13b) {
	    vector<Lit> out;
	    pair<int,int> direct = ANORC13_DirectCard(invars, m, out, false);
	    bool selectDirect = lambda * direct.first + direct.second < min;
	    card_optimal_split_point[make_pair(invars.size(),m)] = split_point =  (selectDirect ? 0 : minj);
            if (! gen) {
	        for (unsigned i=0 ; i < m; i++) outvars.push_back(lit_Error);
	        return (selectDirect ? direct : minpair);
	    }
	} else {
            card_optimal_split_point[make_pair(invars.size(),m)] = split_point =  minj;
            if (! gen) {
	        for (unsigned i=0 ; i < m; i++) outvars.push_back(lit_Error);
	        return minpair;
	    }
        }
    } else
        split_point = it->second;
    
    if (ctype == CP13b && split_point == 0)
        return ANORC13_DirectCard(invars, m, outvars, gen);
    
    vector<Lit> in1, in2;
    for (unsigned i = 0 ; i < split_point ; i++)
        in1.push_back(invars[i]);
    for (unsigned i = split_point ; i < invars.size() ; i++)
       in2.push_back(invars[i]);
     
    vector<Lit> sorted1, sorted2;
    pair<int,int> sort1 = ANORC13_Card(in1, m, sorted1, gen);
    pair<int,int> sort2 = ANORC13_Card(in2, m, sorted2, gen);
    pair<int,int> merge = ANORC13_SMerge(sorted1, sorted2, m, outvars, gen);
    return make_pair(sort1.first+sort2.first+merge.first , sort1.second+sort2.second+merge.second);
}

template<class Solver>
bool Encoding<Solver>::makeANORC13_Card(const vector<Lit>& lits, unsigned const k, vector<Lit>* p_outvars) {
    // input vars
    vector<Lit> invars;
    for (unsigned i = 0 ; i < lits.size() ; i++) {
        invars.push_back(lits[i]);
    }

    //output vars
    vector<Lit> outvars;
    
    ANORC13_Card(invars, k+1, outvars, true);
    
    for (unsigned i = 0 ; i < outvars.size() ; i++) {
        if (outvars[i] == lit_Undef)  continue;
	if (p_outvars) {
            p_outvars->push_back(outvars[i]);
        }
    }
    
    S->addClause(~outvars[k]);

    return true;
}

// Direct Merging and Simplified Direct Merging
template<class Solver>
pair<int,int> Encoding<Solver>::ANORC13_DirectMerge(vector<Lit> const& in1, vector<Lit> const& in2, unsigned c,
						    vector<Lit>& outvars, bool gen) {
    // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell:
    // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints", page 11

    unsigned a = in1.size(), b = in2.size();
    assert( a > 0 && b > 0);
    if (c == 0 || c > a + b) c = a + b;
    if (a > c) a = c;
    if (b > c) b = c;
    
    if (gen) {
        for (unsigned i=0 ; i < c ; i++) {
	    S->newVar();
	    Lit ret = mkLit((unsigned)S->nVars()-1);
            outvars.push_back(ret);
	}
        for (unsigned i=0 ; i < a ; i++) {
	    vec<Lit> args;
	    // in1[i] -> outvars[i]
	    args.push(~in1[i]);
	    args.push(outvars[i]);
	    S->addClause(args);
            args.push(lit_Error);
           for (unsigned j=0 ; j < b && i + j + 1 < c ; j++) {
	        // in1[i] & in2[j] -> outvars[i+j+1]
	        args[1] = ~in2[j];
	        args[2] = outvars[i+j+1];
	        S->addClause(args);
            }
	}
        for (unsigned j=0 ; j < b ; j++) {
	    vec<Lit> args;
	    // in2[i] -> outvars[i]
	    args.push(~in2[j]);
	    args.push(outvars[j]);
	    S->addClause(args);
	}
    } else {
        for (unsigned i=0 ; i < c; i++)
            outvars.push_back(lit_Error);
    }
    return make_pair(c,(a+b)*c - (c*(c-1) + b*(b-1) + a*(a-1))/2); 
    
}
  
// Direct Sorting and Direct m-Cardinality Natwork
template<class Solver>
pair<int,int> Encoding<Solver>::ANORC13_DirectCard(vector<Lit>& invars, unsigned m, vector<Lit>& outvars, bool gen) {
    // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell:
    // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints", page 11
    // m is the desired size of sorted output

    // outvars should be created in this function
    assert(outvars.empty());
    unsigned n = invars.size(), sum = 0;
    
    if (m == 0 || m > n) m = n;

    if (gen) {
        for (unsigned i=0 ; i < m ; i++) {
	    S->newVar();
	    Lit ret = mkLit((unsigned)S->nVars()-1);
            outvars.push_back(ret);
	}
        for (unsigned k=1 ; k <= m ; k++) {
	    vec<Lit> args;
            for (unsigned i=0 ; i < k; i++)
                args.push(lit_Error);
            args.push(outvars[k-1]);
	    sum += ANORC13_DirectCardClauses(invars, 0, 0, k, args);
	}
    } else {
        for (unsigned i=0 ; i < m; i++)
            outvars.push_back(lit_Error);
	unsigned newton = 1;
        for (unsigned k=1 ; k <= m ; k++) { // compute (n over 1) + (n over 2) + ... + (n over m)
	    if (newton <= INT_MAX / (n-k+1))
	        newton = newton*(n-k+1)/k; // compute Newton symbol (n over k)
	    else {
	        sum = INT_MAX;
		break;
	    }
	    if (sum <= INT_MAX - newton)
	        sum += newton;
	    else {
	        sum = INT_MAX;
		break;
	    }
	}
    }
    return make_pair(m , sum);
}
  
template<class Solver>
unsigned Encoding<Solver>::ANORC13_DirectCardClauses(vector<Lit>& invars, unsigned start, unsigned pos, unsigned k, vec<Lit>& args) {
    unsigned n = invars.size(), sum = 0;
    if (pos == k) {
	S->addClause(args);
	return 1;
    } else {
        for (unsigned i = start ; i <= n - (k - pos) ; i++) {
	    args[pos] = ~invars[i];
	    sum += ANORC13_DirectCardClauses(invars, i+1, pos+1, k, args);
        }
	return sum;
    }  
}

template<class S, class D>
int writeMapToFile(const char *fileName, map<S,D>& myMap) {
    FILE *out = fopen(fileName,"wb");
    int count = 0;

    if (out == NULL) return -1;
    for (typename map<S,D>::iterator it = myMap.begin() ; it != myMap.end() ; it++) {
        fwrite(&(it->first),sizeof(it->first),1,out);
        fwrite(&(it->second),sizeof(it->second),1,out);
        count++;
    }
    fclose(out);
    return count;
}

template<class S, class D>
int readMapFromFile(const char *fileName, map<S,D>& myMap) {
    FILE *in = fopen(fileName,"rb");
    int count = 0;

    if (in == NULL) return -1;
    while (! feof(in)) {
        S key;
        D value;
        if (fread(&key,sizeof(key),1,in) != 1) break;
        if (fread(&value,sizeof(value),1,in) != 1) break;
        myMap.insert(make_pair(key,value));
        count++;
    }
    fclose(in);
    return count;
}

} // end namespace Minisat

#endif // __Encodings_h
