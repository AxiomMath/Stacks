module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalQCEquivalence
public import StacksFrontier.Homology.DerivedComplete.RingEquivTransport

/-!
# Quasi-coherent objects on a site with a final object and derived completeness

Let `C` be a category with a final object `X`, viewed as a site with the chaotic topology, and
`O` a presheaf of commutative rings on it, with `O(X)` identified with a ring `A`. If `I ⊆ A` is a
nilpotent ideal, every object of `D(A)` is derived complete with respect to `I`, so the
equivalence `QC(O) ≌ D(O(X))` of Stacks 0H0R reads `QC(O) ≌ D_comp(A, I)`.

## Main definitions

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.qcEquivalenceDerivedCompleteOfTerminal`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)

universe w w' u v r s

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}} {X : C} (hX : IsTerminal X)
  (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x)
  {A : Type s} [CommRing A] [HasDerivedCategory.{w'} (ModuleCat.{max u v r w} A)]

/-- **`QC(O) ≌ D_comp(A, I)` on a site with a final object `X`, for `O(X) ≅ A` and `I` nilpotent**:
the equivalence `QC(O) ≌ D(O(X))` of Stacks 0H0R, transported along `O(X) ≅ A`, followed by the
identification of `D(A)` with its derived complete objects. -/
def qcEquivalenceDerivedCompleteOfTerminal (eA : O.obj (Opposite.op X) ≃+* A) {I : Ideal A}
    (hI : IsNilpotent I) :
    QC.{w} (baseChangeDataOfComm.{r, v, u, w} O hO) ≌
      ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (ModuleCat.{max u v r w} A) => IsDerivedComplete I K) :=
  letI : CommRing (O.obj (Opposite.op X)) :=
    @CommRing.mk _ (inferInstance : Ring (O.obj (Opposite.op X))) (hO _)
  (qcEquivalenceOfTerminalStandard.{w} hX hO).trans
    ((@Stacks.DerivedCompleteTransport.derivedEquivalenceOfRingEquiv (O.obj (Opposite.op X)) _
        A _ eA (HasDerivedCategory.standard _) inferInstance).trans
      (Stacks.DerivedCompleteTransport.derivedCompleteEquivalenceOfIsNilpotent hI).symm)

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
