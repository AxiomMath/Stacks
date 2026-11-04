module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperExtFiniteComplexes
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardCoherentProperSupport

/-!
# Ext between coherent modules on a proper algebraic space

Let `k` be a field and `X` an algebraic space proper over `Spec k`. For coherent `𝒪_X`-modules
`G` and `H` the `k`-vector spaces `Ext^n_X(G, H)` are finite-dimensional: this is Stacks 0D0T
for the objects `G` and `H` of `D_Coh(𝒪_X)` placed in degree `0`, read through the identification
of `Ext^n` with morphisms `G ⟶ H[n]` of the derived category.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_ext_of_isProper`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] modulesLinear

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- **`Ext^n(G, H)` is a finite `A`-module for coherent `G` and `H` on an algebraic space proper
over a Noetherian ring `A`** (Stacks 0D0T for objects placed in degree `0`). -/
theorem moduleFinite_ext_of_isProper [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f)
    (G H : Modules.{u, u} B (Spec (.of A)) hA X hX) (hG : IsCoherent B (Spec (.of A)) hA X hX G)
    (hH : IsCoherent B (Spec (.of A)) hA X hX H) (n : ℕ) :
    letI : HasExt.{u + 1} (Modules.{u, u} B (Spec (.of A)) hA X hX) := HasExt.standard _
    Module.Finite A (Ext G H n) := by
  let : HasExt.{u + 1} (Modules.{u, u} B (Spec (.of A)) hA X hX) := HasExt.standard _
  -- the model of the derived category in which Stacks 0D0T is stated
  let : HasDerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
    HasDerivedCategory.standard _
  have hS := isWeakSerre_isCoherent B (Spec (.of A)) hA X hX
  have hL := DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _ hS H hH
  have hK : DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX)
      ((DerivedCategory.singleFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) 0).obj G) :=
    ⟨⟨0, fun m hm => DerivedCategory.isZero_of_isLE _ 0 m hm⟩,
      (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _ hS G hG).2⟩
  have hfin := moduleFinite_hom_shift_of_isProper A B hA X hX f hf _ _ hK hL n
  exact Module.Finite.equiv (Ext.homLinearEquiv (R := A) (X := G) (Y := H) (n := n)).symm

end AlgebraicGeometry.Space

end
