/*
 * All of the documentation and software included in the
 * Alchemy Software is copyrighted by Stanley Kok, Parag
 * Singla, Matthew Richardson, Pedro Domingos, Marc
 * Sumner, Hoifung Poon, and Daniel Lowd.
 * 
 * Copyright [2004-07] Stanley Kok, Parag Singla, Matthew
 * Richardson, Pedro Domingos, Marc Sumner, Hoifung
 * Poon, and Daniel Lowd. All rights reserved.
 * 
 * Contact: Pedro Domingos, University of Washington
 * (pedrod@cs.washington.edu).
 * 
 * Redistribution and use in source and binary forms, with
 * or without modification, are permitted provided that
 * the following conditions are met:
 * 
 * 1. Redistributions of source code must retain the above
 * copyright notice, this list of conditions and the
 * following disclaimer.
 * 
 * 2. Redistributions in binary form must reproduce the
 * above copyright notice, this list of conditions and the
 * following disclaimer in the documentation and/or other
 * materials provided with the distribution.
 * 
 * 3. All advertising materials mentioning features or use
 * of this software must display the following
 * acknowledgment: "This product includes software
 * developed by Stanley Kok, Parag Singla, Matthew
 * Richardson, Pedro Domingos, Marc Sumner, Hoifung
 * Poon, and Daniel Lowd in the Department of Computer Science and
 * Engineering at the University of Washington".
 * 
 * 4. Your publications acknowledge the use or
 * contribution made by the Software to your research
 * using the following citation(s): 
 * Stanley Kok, Parag Singla, Matthew Richardson and
 * Pedro Domingos (2005). "The Alchemy System for
 * Statistical Relational AI", Technical Report,
 * Department of Computer Science and Engineering,
 * University of Washington, Seattle, WA.
 * http://www.cs.washington.edu/ai/alchemy.
 * 
 * 5. Neither the name of the University of Washington nor
 * the names of its contributors may be used to endorse or
 * promote products derived from this software without
 * specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY OF WASHINGTON
 * AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE UNIVERSITY
 * OF WASHINGTON OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN
 * IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 */
#ifndef MRF_H_SEP_23_2005
#define MRF_H_SEP_23_2005

#include <sys/times.h>
#include <sys/time.h>
#include <cstdlib>
#include <cfloat>
#include <fstream>
#include "timer.h"
#include "mln.h"
#include "groundpredicate.h"

const bool mrfdebug = true;

///////////////////////////////////////////////////////////////////////////

  // used as parameter of addGndClause()
struct AddGroundClauseStruct
{
  AddGroundClauseStruct(const GroundPredicateSet* const & sseenPreds,
                        GroundPredicateSet* const & uunseenPreds,
                        GroundPredicateHashArray* const & ggndPreds,
                        const Array<int>* const & aallPredGndingsAreQueries,
                        GroundClauseSet* const & ggndClausesSet, GroundClauseSet* const & rrealGndClausesSet,
                        Array<GroundClause*>* const & ggndClauses,
                        const bool& mmarkHardGndClauses,
                        const double* const & pparentWtPtr,
                        const int & cclauseId, const bool &wwithEM)
    : seenPreds(sseenPreds), unseenPreds(uunseenPreds), gndPreds(ggndPreds),
      allPredGndingsAreQueries(aallPredGndingsAreQueries),
      gndClausesSet(ggndClausesSet), realGndClausesSet(rrealGndClausesSet),
      gndClauses(ggndClauses), markHardGndClauses(mmarkHardGndClauses),
      parentWtPtr(pparentWtPtr), clauseId(cclauseId), withEM(wwithEM) {}
  
  ~AddGroundClauseStruct() {}
  
  const GroundPredicateSet* seenPreds;
  GroundPredicateSet* unseenPreds;
  GroundPredicateHashArray* gndPreds;
  const Array<int>* allPredGndingsAreQueries;
  GroundClauseSet* gndClausesSet;
  GroundClauseSet* realGndClausesSet;
  Array<GroundClause*>* gndClauses;
  const bool markHardGndClauses;
  const double* parentWtPtr;
  const int clauseId;
  bool withEM;
};

///////////////////////////////////////////////////////////////////////////


class MRF
{
 public:
    //allPredGndingsAreQueries[p] is 1 (true) if all groundings of predicate p 
    //are in queries, otherwise it is 0 (false). 
    //allPredGndingsAreQueries can be
    //NULL if none of the predicates have all their groundings as queries.
  MRF(const GroundPredicateHashArray* const& queries, 
      const Array<int>* const & allPredGndingsAreQueries,
      const Domain* const & domain,  const Database * const & db, 
      const MLN* const & mln, const bool& markHardGndClauses,
      const bool& trackParentClauseWts, const int& memLimit)
  {
    cout << "creating mrf..." << endl; 
    Timer timer;
    GroundPredicateSet unseenPreds, seenPreds;
    GroundPredicateToIntMap gndPredsMap;
    GroundClauseSet gndClausesSet;
    GroundClauseSet realGndClausesSet;  
    gndPreds_ = new GroundPredicateHashArray;
    gndClauses_ = new Array<GroundClause*>;
    flatRealGndClauses_ = new Array<GroundClause*>;
    withEM_ = false;

    int numFirstOrderClauses = mln->getNumClauses();
    
    //reverseMap = new Array<Array<Array<int>*>*>();
    long double memNeeded = 0;

    if(mrfdebug)
      cout<<"initialization done..."<<endl;
	
      //add GroundPredicates in queries to unseenPreds
    
    for (int i = 0; i < queries->size(); i++)
    {
      GroundPredicate* gp = (*queries)[i];
      unseenPreds.insert(gp);
      int gndPredIdx = gndPreds_->append(gp);
      assert(gndPredsMap.find(gp) == gndPredsMap.end());
      gndPredsMap[gp] = gndPredIdx;
    }

      // If too much memory to build MRF then destroy it
    if (memLimit > 0)
    {
      memNeeded = sizeKB();
      if (memNeeded > memLimit)
      {
        for (int i = 0; i < gndClauses_->size(); i++)
          delete (*gndClauses_)[i];
        delete gndClauses_;    

        for (int i = 0; i < gndPreds_->size(); i++)
          if ((*gndPreds_)[i]) delete (*gndPreds_)[i];
        delete gndPreds_;
                    
        throw 1;
      }
    }
	
      //while there are still unknown preds we have not looked at
    while (!unseenPreds.empty())   
    {
      GroundPredicateSet::iterator predIt = unseenPreds.begin();
      GroundPredicate* pred = *predIt;
      unsigned int predId = pred->getId();
      //cout << "\tlooking at pred: ";  pred->print(cout, domain); cout << " with predId : "<<predId<<endl; //added by Happy
//      cout << "(*allPredGndingsAreQueries)[predId] : "<<(*allPredGndingsAreQueries)[predId]<<endl; //added by Happy
      bool genClausesForAllPredGndings = false;
        // if all groundings of predicate with predId are queries
      if (allPredGndingsAreQueries && (*allPredGndingsAreQueries)[predId] >= 1)
      {
          // if we have not generated gnd clauses containing the queries before
        if ((*allPredGndingsAreQueries)[predId] == 1){
          genClausesForAllPredGndings = true;
          // cout<<"inside IF : Added By Noman"<<endl;
        } 
        else
        {   //we have dealt with predicate predId already          
          //cout << "\terasing at pred: ";  pred->print(cout, domain);  //added by Happy
          //cout<< endl; //added by Happy
          unseenPreds.erase(predIt);
          // cout<<"inside ELSE : Added By Noman"<<endl;
          seenPreds.insert(pred);
          continue;
        }
      }
        //get all clauses that contains pred with predId
        // We have recieved all the clauses that contains predicate "Smokes"  (Added By Noman)
      const Array<IndexClause*>* clauses
        = mln->getClausesContainingPred(predId);

        //for each clause, ground it and find those with unknown truth values,
        //dropping ground preds which do not matter to the clause's truth value
      //cout<<"\tclauses->size : "<<clauses->size()<<endl; //added by Happy
      for (int i = 0; clauses && i < clauses->size(); i++)
      {
        Clause* c = (*clauses)[i]->clause;
        //cout << "\tIn clause c: ";  c->printWithWtAndStrVar(cout, domain); cout << endl; //added by Happy
        //const int formulaId = c->parentFormulaId_;
//        cout<<"In formula : "<<((*(mln->getFormulaAndClausesArray()))[formulaId])->formula<<endl; //added by Happy
		    const int clauseId = mln->findClauseIdx(c);  
		    assert(clauseId >= 0);
		    //cout<<"\tclause id : " << clauseId <<endl; //added by Happy
		    //ignore clause with zero weight
        if (c->getWt() == 0) continue;

          //add gnd clauses with unknown truth values to gndClauses_
        const double* parentWtPtr =
          (trackParentClauseWts) ? c->getWtPtr() : NULL;
        AddGroundClauseStruct agc(&seenPreds, &unseenPreds, gndPreds_,
                                  allPredGndingsAreQueries,
                                  &gndClausesSet, &realGndClausesSet, gndClauses_,
                                  markHardGndClauses, parentWtPtr,
                                  clauseId, withEM_);
        //cout << "Happy number of grounded clauses = " << gndClauses_->size() << endl; //added by Happy
    	try
        {
          //pred = Smokes(A), c=!Smokes(a1)v Cancer(a1), genClausesForAllPredGndings=False      //added by Noman
          if(mrfdebug)
            cout<<"calling addUnknownGndClauses..."<<endl;
          
          addUnknownGndClauses(pred, c, domain, db, genClausesForAllPredGndings,
                               &agc);
          
          if(mrfdebug)
            cout<<"called addUnknownGndClauses..."<<endl;
        }
        catch (bad_alloc&)
        {
          cout << "Bad alloc when adding unknown ground clauses to MRF!\n";
          cerr << "Bad alloc when adding unknown ground clauses to MRF!\n";
          throw 1;
        }
        //cout<<"\tCalled addUnknownGndClauses..."<<endl; //added by Happy
        //cout << "number of grounded clauses = " << gndClauses_->size() << endl; //added by Happy
          // If too much memory to build MRF then destroy it
        if (memLimit > 0)
        {
          memNeeded = sizeKB();
            //cout << "preds " << gndPreds_->size() << endl;
            //cout << "clauses " << gndClauses_->size() << endl;
            //cout << "memory " << memNeeded << endl;
            //cout << "limit " << memLimit << endl;
          if (memNeeded > memLimit)
          {
            for (int i = 0; i < gndClauses_->size(); i++)
              delete (*gndClauses_)[i];
            delete gndClauses_;    

            for (int i = 0; i < gndPreds_->size(); i++)
              if ((*gndPreds_)[i]) delete (*gndPreds_)[i];
            delete gndPreds_;
    
            throw 1;
          }
        }
      } // clause loop ended
      //cout<<"all clauses done..."<<endl; //added by Happy
      //clauses with negative wts are handled by the inference algorithms

      //if all the gnd clauses that pred appears in have known truth value,
      //it is not added to gndPreds_ and excluded from the MCMC network

      //cout << "\terasing pred: ";  pred->print(cout, domain); cout << endl;//added by Happy
      unseenPreds.erase(predIt);
      seenPreds.insert(pred);
      if (genClausesForAllPredGndings)
      {
        assert(allPredGndingsAreQueries && 
               (*allPredGndingsAreQueries)[predId]==1);
          //indicate we have seen all groundings of pred predId
        (*allPredGndingsAreQueries)[predId]++;
      }
    }//while (!unseenPreds.empty())

    /*
    for(int i = 0 ; i < gndPreds_->size() ; i++)
    {
      delete (*gndPreds_)[i];
    }
    gndPreds_ = realGndPreds_;
    */
    cout << "number of grounded predicates = " << gndPreds_->size() << endl;
    cout << "number of grounded clauses = " << gndClauses_->size() << endl;
    if (gndClauses_->size() == 0)
      cout<< "Markov blankets of query ground predicates are empty" << endl;

    for(GroundClauseSet::iterator iter = realGndClausesSet.begin() ; iter != realGndClausesSet.end() ; iter++)
    {
      flatRealGndClauses_->append(*iter);
    }

    if (mrfdebug)
    {
      cout << "Clauses in MRF: " << endl;
      for (int i = 0; i < gndClauses_->size(); i++)
      {
        (*gndClauses_)[i]->print(cout, domain, gndPreds_);
        cout << endl;
      }
      cout << "Flat Real Ground Clauses in MRF: " << endl;
      for (int i = 0; i < flatRealGndClauses_->size(); i++)
      {
        (*flatRealGndClauses_)[i]->print(cout, domain, gndPreds_);
        cout << endl;
      }
    }

    
      // Compress preds
    for (int i = 0; i < gndPreds_->size(); i++)
      (*gndPreds_)[i]->compress();

    gndPreds_->compress();
    gndClauses_->compress();
    flatRealGndClauses_->compress();

    cout <<"Time taken to construct MRF = ";
    Timer::printTime(cout,timer.time());
    cout << endl;
  }

  /**
   * Computes and returns size of the mrf in kilobytes
   */
  long double sizeKB()
  {
      // # of ground clauses times memory for a ground clause +
      // # of ground predicates times memory for a ground predicate
    long double size = 0;
    for (int i = 0; i < gndClauses_->size(); i++)
      size += (*gndClauses_)[i]->sizeKB();
    for (int i = 0; i < gndPreds_->size(); i++)
      size += (*gndPreds_)[i]->sizeKB();

    return size;    
  }
  /*
  static bool appendToRealGndClauses(GroundClause *gc, const AddGroundClauseStruct* const & agcs, Array<GroundClause*> &groundClausesAppended)
  {
    Array<Array<Array<GroundClause*>*>*>* realGndClauses = agcs->realGndClauses;
    GroundPredicateHashArray* gndPreds = agcs->gndPreds;
    int i = agcs->clauseId;
    int j = (*realGndClauses)[i]->size();
    GroundClauseSet* realGndClausesSet = agcs->realGndClausesSet;
    GroundClauseSet::iterator iter = realGndClausesSet->find(gc);
    int clauseno = agcs->clauseId;        
    if (iter == realGndClausesSet->end())
    {
      realGndClausesSet->insert(gc);
      if(mrfdebug)
        cout<<"piece newgc is created..."<<endl;
      gc->appendToRealGndPreds(gndPreds);
      if(mrfdebug)
        cout<<"appendtogndpreds done..."<<endl;
      (*realGndClauses)[i]->append(new Array<GroundClause*>());
      if(mrfdebug)
        cout<<"empty append done..."<<endl;
      int k = (*((*realGndClauses)[i]))[j]->size();
      (*((*realGndClauses)[i]))[j]->append(gc);
      groundClausesAppended.append(gc);
      if(mrfdebug)
        cout<<"gc added done..."<<endl;
      
      return true;
    }
    else
    {
      const pair<int,bool>* clauseFrequencyPair = (*iter)->getClauseFrequencyPair(clauseno);
      int freq = clauseFrequencyPair->first;
      bool invertWt = clauseFrequencyPair->second;
      if(freq != 0)
        (*iter)->incrementClauseFrequency(clauseno, 1, invertWt);
      else
        delete clauseFrequencyPair;
      groundClausesAppended.append((GroundClause*)NULL);
      
      return false;
    }

  }
  */
  static void addToRealGndClauses(const GroundClause* const & gcArg, const bool &isHardClause, const AddGroundClauseStruct* const & agcs, const Database *db )
  {
    int numRealGndClauses = 0;
    GroundClauseSet *realGndClausesSet = agcs->realGndClausesSet;
    Array<GroundClause*> groundClausesAppended;
    GroundPredicateHashArray* gndPreds = agcs->gndPreds;
    if(mrfdebug)
      cout<<"In MRF::addToRealGndClauses"<<endl;

    Array<int> subTypeIndices(1,-1);
    Array<int> normalIndices;
    const double* parentWtPtr = agcs->parentWtPtr;
    int clauseno = agcs->clauseId;
    int numGroundPredicates = gcArg->getNumGroundPredicates();
    for(int n = 0 ; n < numGroundPredicates ; n++)
    {
      const GroundPredicate* gndPred = gcArg->getGroundPredicate(n,gndPreds);
      
      if((gndPred->getPredName(db->getDomain()) == "subtype") && !isHardClause)
      {
        subTypeIndices[0] = n;
        //if(mrfdebug)cout<<"subtype size is : "<<subTypeIndices.size()<<endl;
        GroundClause *newgc = new GroundClause(gcArg, gndPreds, subTypeIndices);
        if(mrfdebug)
        {
          cout<<"subtype found, printing newgc : "<<endl;
          newgc->print(cout);
          cout<<endl;
        }
        GroundClauseSet::iterator iter = realGndClausesSet->find(newgc);
        if(iter == realGndClausesSet->end())
        {
          if(mrfdebug)cout<<"This piece comes first time..."<<endl;
          groundClausesAppended.append(newgc);
          realGndClausesSet->insert(newgc);
        }
        else
        {
          if(mrfdebug)cout<<"This piece has already come..."<<endl;
          groundClausesAppended.append(*iter); 
          //if(mrfdebug)cout<<"This piece has been appended.."<<endl;
          delete newgc;
        }
        numRealGndClauses++;
      }
      else
      {
        normalIndices.append(n);
      }
    }
    
    if(mrfdebug)cout<<"normalIndices created succesfully..."<<endl;
    GroundClause *newgc = new GroundClause(gcArg, gndPreds, normalIndices);
    GroundClauseSet::iterator iter = realGndClausesSet->find(newgc);
    if(iter == realGndClausesSet->end())
    {
      if(mrfdebug)cout<<"nonsubtype clause, piece comes first time..."<<endl;
      groundClausesAppended.append(newgc);
      realGndClausesSet->insert(newgc);
    }
    else
    {
      if(mrfdebug)cout<<"non subtype clause, piece has already come..."<<endl;
      groundClausesAppended.append(*iter);
      delete newgc; 
    }
    numRealGndClauses++;
    if(mrfdebug)
    {
      cout<<"printing realGndClauses set after adding new pieces : "<<endl;
      for(GroundClauseSet::iterator iter = realGndClausesSet->begin() ; iter != realGndClausesSet->end() ; iter++)
      {
        (*iter)->print(cout);
        cout<<endl;
      }
    }
    if(mrfdebug){cout<<"numRealGndClauses : "<<numRealGndClauses<<", now updating wts, freq and divide factors..."<<endl;}
    for(int k = 0 ; k < numRealGndClauses; k++)
    {
      groundClausesAppended[k]->addWt((gcArg->getWt())/numRealGndClauses);
      if(mrfdebug)
      {
        cout<<"k : "<<k<<endl;
        cout<<"wt : "<<groundClausesAppended[k]->getWt()<<endl;
      }
      if(parentWtPtr)
      {
        const pair<int,bool>* clauseFrequencyPair = gcArg->getClauseFrequencyPair(clauseno);
        bool invertWt = clauseFrequencyPair->second;
        if(clauseFrequencyPair->first == 0)
          delete clauseFrequencyPair;
        groundClausesAppended[k]->incrementClauseFrequency(clauseno, 1, invertWt);
        groundClausesAppended[k]->updateDivideFactor(clauseno, numRealGndClauses);
      }
    }
  }

    // Do not delete the clause and truncClause argument.
    // This function is tightly bound to Clause::createAndAddUnknownClause().
  static void addUnknownGndClause(const AddGroundClauseStruct* const & agcs, 
                                  const Clause* const & clause,
                                  const Clause* const & truncClause,
                                  const bool& isHardClause, const Database *db)
  {
    const GroundPredicateSet* seenPreds     = agcs->seenPreds;
    GroundPredicateSet*       unseenPreds   = agcs->unseenPreds;
    GroundPredicateHashArray* gndPreds      = agcs->gndPreds;
    const Array<int>* allGndingsAreQueries  = agcs->allPredGndingsAreQueries;
    GroundClauseSet*          gndClausesSet = agcs->gndClausesSet;
    Array<GroundClause*>*     gndClauses    = agcs->gndClauses;
    GroundClauseSet* realGndClausesSet      = agcs->realGndClausesSet;
    const bool markHardGndClauses           = agcs->markHardGndClauses;
    const double* parentWtPtr               = agcs->parentWtPtr;
    const int clauseId                      = agcs->clauseId;
    const bool withEM = agcs->withEM;

    // Check none of the grounded clause's predicates have been seen before.
    // If any of them have been seen before, this clause has been created 
    // before (for that seen predicate), and can be ignored

      // Check the untruncated ground clause whether any of its predicates
      // have been seen before
    bool seenBefore = false;
    //cout<<"seenPredsSize : "<<seenPreds->size()<<endl; //added by Happy
    for (int j = 0; j < clause->getNumPredicates(); j++)
    {
      Predicate* p = clause->getPredicate(j);
      GroundPredicate* gp = new GroundPredicate(p);
      if (seenPreds->find(gp) !=  seenPreds->end() ||
          (allGndingsAreQueries && (*allGndingsAreQueries)[gp->getId()] > 1) )
      { 
        seenBefore = true;
        delete gp;
        break;
      }
      delete gp;
    }
    //cout<<"seenBefore : "<<seenBefore<<endl; //added by Happy
    if (seenBefore) return;

    GroundClause* gndClause = new GroundClause(truncClause, gndPreds);
    if(mrfdebug)
    {
      cout<<"gndPreds size : "<<gndPreds->size()<<endl;
      cout<<"gndClause created..."<<endl;
    }
    // we don't want to add ground clause which only contains subtype predicates because that means rest of the formula was false.
    bool allPredsSubtype = true;
    for(int i = 0 ; i < gndClause->getNumGroundPredicates() ; i++)
    {
      const GroundPredicate* gp = gndClause->getGroundPredicate(i, gndPreds);
      if(gp->getPredName(db->getDomain()) != "subtype" || isHardClause || withEM)
      {
        allPredsSubtype = false;
        break;
      }
    }
    if(allPredsSubtype)
    {
      delete gndClause;
      return;
    }

    if(mrfdebug)
    {
      cout<<"checking for all subtype done..."<<endl;
    }
    if (markHardGndClauses && isHardClause) gndClause->setWtToHardWt();
    assert(gndClause->getWt() != 0);

    bool invertWt = false;
      // We want to normalize soft unit clauses to all be positives
    if (!isHardClause && gndClause->getNumGroundPredicates() == 1 &&
        !gndClause->getGroundPredicateSense(0))
    {
      gndClause->setGroundPredicateSense(0, true);
      gndClause->setWt(-gndClause->getWt());
      invertWt = true;
    }
    
    GroundClauseSet::iterator iter = gndClausesSet->find(gndClause);
    if(mrfdebug)
    {
      cout<<"printing current big gnd clause : "<<endl;
      gndClause->print(cout);
      cout<<endl;
      cout<<"printing big gnd clausesSet :"<<endl;
      for(GroundClauseSet::iterator iter = gndClausesSet->begin() ; iter != gndClausesSet->end() ; iter++)
      {
        (*iter)->print(cout);
        cout<<endl;
      }
    }
      // If the unknown clause is not in gndClauses
    if (iter == gndClausesSet->end())
    {
      gndClausesSet->insert(gndClause);
      gndClauses->append(gndClause);
      gndClause->appendToGndPreds(gndPreds);
      if(mrfdebug) cout<<"parentWtPtr : "<<parentWtPtr<<endl;
        // gndClause's wt is set when it was constructed
      if (parentWtPtr)
        gndClause->incrementClauseFrequency(clauseId, 1, invertWt);

        // Add the unknown predicates of the clause to unseenPreds if 
        // the predicates are already not in it
      for (int j = 0; j < gndClause->getNumGroundPredicates(); j++)
      {
        GroundPredicate* gp =
          (GroundPredicate*)gndClause->getGroundPredicate(j, gndPreds);
        assert(seenPreds->find(gp) == seenPreds->end());
          // if the ground predicate is not in unseenPreds
        GroundPredicateSet::iterator it = unseenPreds->find(gp);
        if (it == unseenPreds->end())
        {
          //cout << "\tinserting into unseen pred: ";  
          //pred->print(cout, domain); cout << endl;
          unseenPreds->insert(gp);
        }
      }
      addToRealGndClauses(gndClause, isHardClause, agcs, db);
      //gndClause->jGivenI = ((*realGndClauses)[agcs->clauseId])->size()-1;
    }
    else
    {
      if(mrfdebug)cout<<"Big ground clause already havs appeared..."<<endl;
      (*iter)->addWt(gndClause->getWt());
      if (parentWtPtr)
        gndClause->incrementClauseFrequency(clauseId, 1, invertWt);
      addToRealGndClauses(gndClause, isHardClause, agcs, db);
      delete gndClause;
    }
  } //addUnknownGndClause()



  ~MRF()
  {
    for (int i = 0; i < gndClauses_->size(); i++)
      if ((*gndClauses_)[i]) delete (*gndClauses_)[i];
    delete gndClauses_;    

    for (int i = 0; i < gndPreds_->size(); i++)
      if ((*gndPreds_)[i]) delete (*gndPreds_)[i];
    delete gndPreds_;
  }

  void deleteGndPredsGndClauseSets()
  {
    for (int i = 0; i < gndPreds_->size(); i++)
      (*gndPreds_)[i]->deleteGndClauseSet();
  }  

  const GroundPredicateHashArray* getGndPreds() const { return gndPreds_; }

  const Array<GroundClause*>* getGndClauses() const { return gndClauses_; }

  const Array<GroundClause*>* getFlatRealGndClauses() const { return flatRealGndClauses_; }

 private:

  void addUnknownGndClauses(const GroundPredicate* const& queryGndPred,
                            Clause* const & c, const Domain* const & domain, 
                            const Database* const & db, 
                            const bool& genClauseForAllPredGndings,
                            const AddGroundClauseStruct* const & agcs)
  {

    //cout<<"genClauseForAllPredGndings: "<<genClauseForAllPredGndings<<endl; //added by Happy
    
    if (genClauseForAllPredGndings)
      c->addUnknownClauses(domain, db, -1, NULL, agcs);
    else
    {
      for (int i = 0; i < c->getNumPredicates(); i++)
      {
        
        //pred is Smoke and All Terms are different Variables. hence this if conditon is satisfied //added by Noman
        if (c->getPredicate(i)->canBeGroundedAs(queryGndPred))
        {
          c->addUnknownClauses(domain, db, i, queryGndPred, agcs);
        
        }
      }
    }
  } 

 public:

  const int getNumGndPreds()
  {
    return gndPreds_->size();
  }

  const int getNumGndClauses()
  {
    return gndClauses_->size();
  }

  bool withEM_;
 private:
  GroundPredicateHashArray* gndPreds_;
  //GroundPredicateHashArray* realGndPreds_;
  Array<GroundClause*>* gndClauses_;
  Array<GroundClause*>* flatRealGndClauses_;
  
};


#endif

