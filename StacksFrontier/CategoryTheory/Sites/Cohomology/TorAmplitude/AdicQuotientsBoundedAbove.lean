module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.AdicQuotients
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IdealKilledBoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealTensorVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# A uniform upper bound on the derived tensor products with the adic quotients

Let `(C, O)` be a ringed site, `I ⊆ O` a sheaf of ideals and `K` an object of `D(O)`. If
`K ⊗^L_O O/I` is bounded above, then the family `K ⊗^L_O O/Iⁿ` is bounded above by one integer
for every `n` at once.

## Main definitions

* `Stacks.Sites.adicQuotientModuleOneIso`: the first quotient `O/I¹` of the tower is the
  quotient of the structure sheaf by the sheaf of ideals.

## Main results

* `Stacks.Sites.isUniformlyBoundedAbove_tensor_adicQuotientModule_of_isBoundedAbove`: if
  `K ⊗^L_O O/I` is bounded above then `K ⊗^L_O O/Iⁿ` is uniformly bounded above.

## Implementation notes

The graded pieces `Iⁿ/Iⁿ⁺¹` of the filtration of the structure sheaf by the powers of `I` are
killed by `I`, so each `K ⊗^L_O Iⁿ/Iⁿ⁺¹` inherits the bound of `K ⊗^L_O O/I` by
`Stacks.Sites.isBoundedAboveBy_tensor_single_of_idealι_app_eq_zero`; the tower of short exact
sequences `0 → Iⁿ/Iⁿ⁺¹ → O/Iⁿ⁺¹ → O/Iⁿ → 0`, whose zeroth stage `O/I⁰` vanishes, then carries
that single bound to every `O/Iⁿ` by induction.

That the graded pieces are killed by `I` is the hypothesis `hG` below: the ordinary map
`I ⊗_O Iⁿ/Iⁿ⁺¹ ⟶ O ⊗_O Iⁿ/Iⁿ⁺¹` vanishes, which under `O ⊗_O G ≅ G` is the statement that
`I · Iⁿ ⊆ Iⁿ⁺¹`.

All the site universes are equal, as they are for the associativity of the derived tensor product
and for its right t-exactness; the universe of the derived category stays independent.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.Sites

attribute [local instance] instHasSheafComposeForget₂RingCat

variable {X : RingedSite.{u, u, u}} [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (I : IdealSubsheaf.{u, u, u} X.O)

/-- The first power of a sheaf of ideals is the ideal itself. -/
lemma adicQuotientModule_one_eq : adicQuotientModule I 1 = cokernel I.ι :=
  congrArg (fun N : IdealSubsheaf.{u, u, u} X.O => cokernel N.ι) (idealPow_one I)

/-- **The first quotient of the tower is the quotient by the sheaf of ideals**: `O/I¹ = O/I`. -/
def adicQuotientModuleOneIso : adicQuotientModule I 1 ≅ cokernel I.ι :=
  eqToIso (adicQuotientModule_one_eq I)

section Derived

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)
  (K : RingedSite.DerivedModules.{u, u, u, d} X)

/-- **If `K ⊗^L_O O/I` is bounded above then `K ⊗^L_O O/Iⁿ` is uniformly bounded above**: one
integer bounds the cohomology of every `K ⊗^L_O O/Iⁿ` from above. The graded pieces `Iⁿ/Iⁿ⁺¹`
are killed by `I`, hence all bounded above by the bound of `K ⊗^L_O O/I` after tensoring with
`K`, and the tower `0 → Iⁿ/Iⁿ⁺¹ → O/Iⁿ⁺¹ → O/Iⁿ → 0` carries that bound to every quotient. -/
@[stacks 0942 "uniformly bounded above"]
theorem isUniformlyBoundedAbove_tensor_adicQuotientModule_of_isBoundedAbove
    (hQ : Stacks.DerivedCategory.IsBoundedAbove
      ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj
          (adicQuotientModule I 1))))
    :
    Stacks.DerivedCategory.IsUniformlyBoundedAbove
      (fun n : ℕ => (T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj
          (adicQuotientModule I n))) := by
  obtain ⟨b, hb⟩ := hQ
  refine isUniformlyBoundedAbove_tensor_adicQuotientModule I T K b fun n => ?_
  exact isBoundedAboveBy_tensor_single_of_idealι_app_eq_zero I T K (adicGradedPiece I n) b
    (hb.of_iso ((T.tensor.obj K).mapIso
      ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).mapIso
        (adicQuotientModuleOneIso I)))) (sheafTensor_map_idealι_app_adicGradedPiece_eq_zero I n)

end Derived

end Stacks.Sites

end
