module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Unconditional

/-!
# Complements to `StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Unconditional`

Declarations used alongside `StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Unconditional`:
`derivedCategoryBBounded_derivedPushforward`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

-- The statements below have to spell out `R ᵖ f_* F`, so they have to be elaborated at the same
-- derived category as the reduction in
-- `StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/Basic.lean`, namely
-- `CategoryTheory.HasDerivedCategory.standard`. The import cone of Chow's lemma contributes a
-- competing `HasDerivedCategory` instance, so the precedence is raised here.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
  (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

omit [IsLocallyNoetherian S] in
/-- **[Stacks, Tag 08E2].** Let `S` be a Noetherian scheme, `f : X ⟶ S` locally of finite type
and `E` an object of `D^b_Coh(𝒪_X)` such that the support of `H^i(E)` is proper over `S` for all
`i`. Then `Rf_*E` is an object of `D^b_Coh(𝒪_S)`. -/
@[stacks 08E2]
theorem derivedCategoryBBounded_derivedPushforward [IsNoetherian S]
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) :=
  derivedCategoryBBounded_derivedPushforward_of_isProperOver_supp f E hcoh hsupp
    _root_.AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase
    a b hGE hLE

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
