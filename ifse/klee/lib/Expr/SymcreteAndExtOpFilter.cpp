#include "klee/Expr/ExprVisitor.h"

#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprPPrinter.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "klee/Expr/SymcreteAndExtOpFilter.h"

using namespace klee;

ExprVisitor::Action SymcreteAndExtOpFilter::visitExpr(const Expr& e) {
    Expr::Kind kind = e.getKind();
    #define RIGHT_HAND_SIDE 1
    if (kind == Expr::Eq) {
        ref<Expr> right = e.getKid(RIGHT_HAND_SIDE);
        if (right->getKind() == Expr::ExtOp) {
        return Action::changeTo(EqExpr::create(klee::ConstantExpr::create(1, Expr::Bool), 
                                                klee::ConstantExpr::create(1, Expr::Bool)));
        }
    }
    return Action::doChildren();
}
