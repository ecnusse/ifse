#include "klee/Expr/ExprVisitor.h"

#include "klee/Expr/Expr.h"

#include "llvm/Support/raw_ostream.h"
#include "/home/user/ifse/klee/lib/Core/ExecutionState.h"
#include "klee/Expr/SymcreteReplacer.h"

using namespace klee;

/** Replace all occurrences of symcrete with its corresponding constant 
    in a complex expression.
*/ 
ExprVisitor::Action SymcreteReplacer::visitExpr(const Expr& expr) {
    Expr::Kind kind = expr.getKind();
    if (kind == Expr::ZExt || kind == Expr::Read || kind == Expr::Concat) {
        const ReadExpr* readExpr = NULL;
        switch (kind) {
            case Expr::Read: { readExpr = &cast<ReadExpr>(expr); break; }
            case Expr::ZExt: case Expr::Concat: {
                auto left = expr.getKid(0);
                if (left->getKind() != klee::Expr::Read) {
                    assert(0 && "Something weird may have happened\n");
                }
                readExpr = dyn_cast<ReadExpr>(left);
                break;
            }
            default: assert(0 && "Invalid symcrete kind\n");
        }
        // Parse the symcrete
        if (!readExpr->updates.head.isNull()) { assert(0 && "Something weird may have happened\n"); }

        auto array = readExpr->updates.root;
        auto find = state->findSymcreteMap(array);
        // Indeed kind of symcrete
        if (find.hasValue()) {
            auto v = find.getValue();
            uint64_t r = 0;
            for (size_t i = 0; i < 8; ++i) {
                r |= static_cast<uint64_t>(v[i]) << (i * 8);
            }
            switch (expr.getWidth()) {
            case 1:
                r &=0x01;
                break;
            case 8:
                r &= 0xFF;
                break;
            case 16:
                r &= 0xFFFF;
                break;
            case 32:
                r &= 0xFFFFFFFF;
                break;
            default:
                break;
            }
            return Action::changeTo(ConstantExpr::create(r, expr.getWidth()));
        }
    }
    return Action::doChildren();
}
