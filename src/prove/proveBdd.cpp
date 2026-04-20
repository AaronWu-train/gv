/****************************************************************************
  FileName     [ proveBdd.cpp ]
  PackageName  [ prove ]
  Synopsis     [ For BDD-based verification ]
  Author       [ ]
  Copyright    [ Copyright(c) 2023-present DVLab, GIEE, NTU, Taiwan ]
****************************************************************************/

#include "bddMgrV.h"
#include "gvMsg.h"
// #include "gvNtk.h"
#include <iomanip>
#include <iostream>
#include <vector>

#include "cirGate.h"
#include "cirMgr.h"
#include "util.h"

void BddMgrV::buildPInitialState() {
    // set initial state: all latches (CS) = 0
    _isFixed = false;
    _reachStates.clear();

    const unsigned nPi    = cirMgr->getNumPIs();
    const unsigned nLatch = cirMgr->getNumLATCHs();

    BddNodeV init = BddNodeV::_one;
    for (unsigned i = 0; i < nLatch; ++i) {
        const unsigned csLevel = nPi + 1 + i;
        init &= ~getSupport(csLevel);
    }
    _initState = init;
}

void BddMgrV::buildPTransRelation() {
    const unsigned nPi    = cirMgr->getNumPIs();
    const unsigned nLatch = cirMgr->getNumLATCHs();

    // TR(CS, PI, NS) = ∧_i (NS_i <-> f_i(CS, PI))
    BddNodeV tr = BddNodeV::_one;
    for (unsigned i = 0; i < nLatch; ++i) {
        gv::cir::CirRiGate* ri = cirMgr->getRi(i);
        const unsigned nsLevel = nPi + nLatch + 1 + i;
        const BddNodeV nsVar   = getSupport(nsLevel);
        const BddNodeV nsFunc  = getBddNodeV(ri->getGid());
        assert(nsFunc() != 0);

        const BddNodeV eq = ~(nsVar ^ nsFunc);  // XNOR means <->
        tr &= eq;
    }
    _tr = tr;

    // TRI(CS, NS) = ∃ PI . TR(CS, PI, NS)
    BddNodeV tri = tr;
    for (unsigned l = 1; l <= nPi; ++l) {
        tri = tri.exist(l);
    }
    _tri = tri;
}

BddNodeV BddMgrV::restrict(const BddNodeV& f, const BddNodeV& g) {
    if (g == BddNodeV::_zero) {
        cout << "Error in restrict!!" << endl;
    }
    if (g == BddNodeV::_one) {
        return f;
    }
    if (f == BddNodeV::_zero || f == BddNodeV::_one) {
        return f;
    }
    unsigned a = g.getLevel();
    if (g.getLeftCofactor(a) == BddNodeV::_zero) {
        return restrict(f.getRightCofactor(a), g.getRightCofactor(a));
    }
    if (g.getRightCofactor(a) == BddNodeV::_zero) {
        return restrict(f.getLeftCofactor(a), g.getLeftCofactor(a));
    }
    if (f.getLeftCofactor(a) == f.getRightCofactor(a)) {
        return restrict(f, g.getLeftCofactor(a) | g.getRightCofactor(a));
    }
    BddNodeV newNode =
        (~getSupport(a)& restrict(f.getRightCofactor(a),
                                  g.getRightCofactor(a))) |
        (getSupport(a)& restrict(f.getLeftCofactor(a), g.getLeftCofactor(a)));
    return newNode;
}

void BddMgrV::buildPImage(int level) {
    // note:: _reachStates records the set of reachable states (monotonically)
    if (_initState() == 0 || _tri() == 0) return;

    if (_reachStates.empty()) {
        _isFixed = false;
        _reachStates.push_back(_initState);
    }

    for (int k = 0; k < level && !_isFixed; ++k) {
        BddNodeV nsImg   = find_ns(_reachStates.back());
        BddNodeV csImg   = ns_to_cs(nsImg);
        BddNodeV newReach = _reachStates.back() | csImg;

        if (newReach == _reachStates.back()) {
            _isFixed = true;
            break;
        }
        _reachStates.push_back(newReach);
    }
}

void BddMgrV::runPCheckProperty(const string& name, BddNodeV monitor) {
    // Prove AG(~monitor):
    // If monitor depends on PI, treat PI as nondeterministic:
    // counterexample exists if ∃ CS ∈ Reach, ∃ PI : monitor(CS, PI) == 1
    const BddNodeV reach = getPReachState();
    if (reach() == 0) return;

    BddNodeV bad = reach & monitor;
    if (bad == BddNodeV::_zero) {
        gvMsg(GV_MSG_IFO) << "[PCHECKProperty] PASS: AG(~" << name << ") holds."
                          << endl;
        return;
    }

    gvMsg(GV_MSG_ERR) << "[PCHECKProperty] FAIL: property violated for \"" << name
                      << "\"." << endl;
    BddNodeV cube = bad.getCube(0);
    gvMsg(GV_MSG_ERR) << "  witness cube: " << cube.toString() << endl;
}

BddNodeV
BddMgrV::find_ns(BddNodeV cs) {
    // Compute next-state image over NS variables:
    // ns = ∃ CS . ( cs(CS) ∧ TRI(CS, NS) )
    const unsigned nPi    = cirMgr->getNumPIs();
    const unsigned nLatch = cirMgr->getNumLATCHs();

    BddNodeV tmp = cs & _tri;
    for (unsigned i = 0; i < nLatch; ++i) {
        const unsigned csLevel = nPi + 1 + i;
        tmp = tmp.exist(csLevel);
    }
    return tmp;
}

BddNodeV
BddMgrV::ns_to_cs(BddNodeV ns) {
    // Rename NS vars (Y) to CS vars (X) by moving levels down by nLatch.
    const unsigned nPi    = cirMgr->getNumPIs();
    const unsigned nLatch = cirMgr->getNumLATCHs();
    if (ns() == 0) return ns;

    bool isMoved = false;
    const unsigned fromLevel = nPi + nLatch + 1;
    const unsigned toLevel   = nPi + 1;
    BddNodeV cs = ns.nodeMove(fromLevel, toLevel, isMoved);
    assert(isMoved);
    return cs;
}
