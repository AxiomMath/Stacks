module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsGeometricFactor

/-!
# Eilenberg-Watts in a top-degree base-change situation over an affine base

For a `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` whose base `Y'` is affine, `Y'` is
`Spec Γ(Y', ⊤)` through `AlgebraicGeometry.Scheme.isoSpec`, so `X'` is a scheme over
`Spec Γ(Y', ⊤)` with `X'` itself as its underlying scheme. For a quasi-coherent module `F` on
`X'`, the endofunctor

> `Φ(M) = H^d(X', F ⊗_{𝒪_{X'}} (f')^* M~)`

of `Γ(Y', ⊤)`-modules is additive, linear, right exact and commutes with direct sums, so by the
Eilenberg-Watts theorem it is tensoring with `Φ(Γ(Y', ⊤))`. This is the affine case of
[Stacks, Tag 0EX3] (b).

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.affineBaseRing`: the ring `Γ(Y', ⊤)` of
  the affine base.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.affineBaseOver`: `X'` as a scheme over
  `Spec Γ(Y', ⊤)`, through `f'` followed by `Y' ≅ Spec Γ(Y', ⊤)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeFunctor`: the endofunctor `Φ`
  of `Γ(Y', ⊤)`-modules, for a quasi-coherent module `F` on `X'`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.isZero_cohomology_succ_d`: the
  vanishing of `H^{d+1}(X', -)` on quasi-coherent modules.
* `additive_topDegreeFunctor`, `linear_topDegreeFunctor`,
  `preservesFiniteColimits_topDegreeFunctor` and
  `preservesColimitsOfShape_discrete_topDegreeFunctor`, all in the same namespace: the four
  hypotheses of `Stacks.EilenbergWatts.iso` for `Φ`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeTensorIso`: `Φ` is
  tensoring with the `Γ(Y', ⊤)`-module `H^d(X', F ⊗ (f')^* Γ(Y', ⊤)~)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeTensorLinearEquiv`: the same
  conclusion module by module, as a `Γ(Y', ⊤)`-linear equivalence `Φ(Γ(Y', ⊤)) ⊗ M ≃ₗ Φ(M)`.
* `isLinearRightExactAndPreservesDirectSums_topDegreeFunctor`, in the same namespace: `Φ` lies in
  the full subcategory of [Stacks, Tag 0GNV].

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0GNV](https://stacks.math.columbia.edu/tag/0GNV)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.Cohomology.AffineBase
open scoped ModuleCat.Algebra

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable (S : TopDegreeBaseChangeSituation.{u}) [IsAffine S.Y']

/-- The ring `Γ(Y', ⊤)` of the affine base `Y'`, of which `Y'` is the spectrum. -/
abbrev affineBaseRing : Type u := Γ(S.Y', ⊤)

/-- **`X'` as a scheme over `Spec Γ(Y', ⊤)`**, through the base-changed morphism `f'` followed by
the canonical isomorphism `Y' ≅ Spec Γ(Y', ⊤)`. Its underlying scheme is `S.X'` itself. -/
abbrev affineBaseOver : Over (Spec (CommRingCat.of S.affineBaseRing)) :=
  Over.mk (S.f' ≫ S.Y'.isoSpec.hom)

/-- The scheme over the affine base is `X'` on the nose. -/
lemma affineBaseOver_left : (S.affineBaseOver).left = S.X' := rfl

/-- The structure morphism over the affine base is `f'` followed by `Y' ≅ Spec Γ(Y', ⊤)`. -/
lemma affineBaseOver_hom : (S.affineBaseOver).hom = S.f' ≫ S.Y'.isoSpec.hom := rfl

/-- The structure morphism over the affine base is quasi-compact. -/
instance quasiCompact_affineBaseOver_hom : QuasiCompact (S.affineBaseOver).hom :=
  have := S.quasiCompact_f'
  inferInstanceAs (QuasiCompact (S.f' ≫ S.Y'.isoSpec.hom))

/-- The structure morphism over the affine base is quasi-separated. -/
instance quasiSeparated_affineBaseOver_hom : QuasiSeparated (S.affineBaseOver).hom :=
  have := S.quasiSeparated_f'
  inferInstanceAs (QuasiSeparated (S.f' ≫ S.Y'.isoSpec.hom))

/-- The cohomology `H^{d+1}(X', G)` of a quasi-coherent module `G` on `X'` vanishes. -/
theorem isZero_cohomology_succ_d (G : (S.affineBaseOver).left.Modules)
    (hG : G.IsQuasicoherent) :
    IsZero (((moduleGlobalSections (S.affineBaseOver).left).rightDerivedPlus
      ((S.d : ℤ) + 1)).obj G) :=
  have := hG
  S.isZero_cohomology_of_lt ((S.d : ℤ) + 1) (lt_add_one _) G

variable (F : (SheafOfModules.isQuasicoherent (S.affineBaseOver).left.ringCatSheaf).FullSubcategory)

/-- The endofunctor `Φ : M ↦ H^d(X', F ⊗ (f')^* M~)` of `Γ(Y', ⊤)`-modules. -/
abbrev topDegreeFunctor : ModuleCat.{u} S.affineBaseRing ⥤ ModuleCat.{u} S.affineBaseRing :=
  affineTopDegreeFunctor S.affineBaseRing S.affineBaseOver S.d
    (geometricFactor S.affineBaseRing S.affineBaseOver F)

/-- The functor `Φ` is additive. -/
theorem additive_topDegreeFunctor : (S.topDegreeFunctor F).Additive :=
  additive_affineTopDegreeFunctor S.affineBaseRing S.affineBaseOver S.d _

/-- The functor `Φ` is `Γ(Y', ⊤)`-linear. -/
theorem linear_topDegreeFunctor : Functor.Linear S.affineBaseRing (S.topDegreeFunctor F) :=
  linear_affineTopDegreeFunctor S.affineBaseRing S.affineBaseOver S.d _
    (linear_geometricFactor S.affineBaseRing S.affineBaseOver F)

/-- The functor `Φ` is right exact: it preserves finite colimits. -/
theorem preservesFiniteColimits_topDegreeFunctor :
    PreservesFiniteColimits (S.topDegreeFunctor F) :=
  preservesFiniteColimits_affineTopDegreeFunctor S.affineBaseRing S.affineBaseOver S.d _
    S.isZero_cohomology_succ_d

/-- The functor `Φ` commutes with arbitrary direct sums. -/
theorem preservesColimitsOfShape_discrete_topDegreeFunctor (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (S.topDegreeFunctor F) :=
  have : CompactSpace ((S.affineBaseOver).left : Type u) :=
    QuasiCompact.compactSpace_of_compactSpace (S.affineBaseOver).hom
  have : QuasiSeparatedSpace ((S.affineBaseOver).left : Type u) :=
    quasiSeparatedSpace_of_quasiSeparated (S.affineBaseOver).hom
  preservesColimitsOfShape_discrete_affineTopDegreeFunctor S.affineBaseRing S.affineBaseOver S.d _
    (preservesColimitsOfShape_discrete_geometricFactor S.affineBaseRing S.affineBaseOver F) J

/-- **The affine case of [Stacks, Tag 0EX3] (b).** For a top-degree base-change situation whose
base `Y'` is affine and a quasi-coherent module `F` on `X'`, the endofunctor
`M ↦ H^d(X', F ⊗ (f')^* M~)` of `Γ(Y', ⊤)`-modules is tensoring with the `Γ(Y', ⊤)`-module
`H^d(X', F ⊗ (f')^* Γ(Y', ⊤)~)`. -/
def topDegreeTensorIso :
    MonoidalCategory.tensorLeft
        ((S.topDegreeFunctor F).obj (ModuleCat.of S.affineBaseRing S.affineBaseRing)) ≅
      S.topDegreeFunctor F :=
  affineTopDegreeTensorIso S.affineBaseRing S.affineBaseOver F S.d S.isZero_cohomology_succ_d

/-- **The affine case of [Stacks, Tag 0EX3] (b), module by module.** For every
`Γ(Y', ⊤)`-module `M`, a `Γ(Y', ⊤)`-linear equivalence `Φ(Γ(Y', ⊤)) ⊗ M ≃ₗ Φ(M)`. -/
def topDegreeTensorLinearEquiv (M : ModuleCat.{u} S.affineBaseRing) :
    ((S.topDegreeFunctor F).obj (ModuleCat.of S.affineBaseRing S.affineBaseRing)) ⊗[
        S.affineBaseRing] M ≃ₗ[S.affineBaseRing] (S.topDegreeFunctor F).obj M :=
  haveI := S.additive_topDegreeFunctor F
  haveI := S.linear_topDegreeFunctor F
  haveI := S.preservesFiniteColimits_topDegreeFunctor F
  haveI := fun J : Type u => S.preservesColimitsOfShape_discrete_topDegreeFunctor F J
  Stacks.EilenbergWatts.linearEquiv (S.topDegreeFunctor F) M

/-- The functor `Φ` is linear, right exact and commutes with direct sums: it lies in the full
subcategory classified by [Stacks, Tag 0GNV]. -/
theorem isLinearRightExactAndPreservesDirectSums_topDegreeFunctor :
    ModuleCat.IsLinearRightExactAndPreservesDirectSums S.affineBaseRing S.affineBaseRing
      S.affineBaseRing (S.topDegreeFunctor F) :=
  isLinearRightExactAndPreservesDirectSums_affineTopDegreeFunctor_geometricFactor
    S.affineBaseRing S.affineBaseOver F S.d S.isZero_cohomology_succ_d

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

end
