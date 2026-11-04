module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.AlgebraicGeometry.DenominatorIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.DenominatorIdealResidue.LocallyInjective
public import StacksFrontier.CategoryTheory.Adjunction.AdjunctionUnit

/-!
# The denominator ideal embeds in the structure sheaf

Let `X` be a scheme, `L` a sheaf of `𝒪_X`-modules and `s` a meromorphic section of `L`.  The
denominator ideal of `s` is the fibre product of multiplication by `s` and of the canonical map
`L ⟶ K_X(L)`, and its inclusion in the structure sheaf is the first projection.  In the abelian
category of sheaves of modules the kernel of that projection is the kernel of `L ⟶ K_X(L)`, so
the inclusion is a monomorphism exactly when `L ⟶ K_X(L)` is one.

This file reduces that question to a single elementary local statement: the map
`x ↦ 1 ⊗ x` from `L` to the *presheaf* tensor product `K_X ⊗_{𝒪_X} L` is injective on the
sections over the members of a neighbourhood basis.

## Main definitions

* `Stacks.DenominatorIdealResidue.tmulOne`: the presheaf-level map `x ↦ 1 ⊗ x`.
* `Stacks.DenominatorIdealResidue.toSheafifyMeromorphic`: the sheafification map from the
  presheaf tensor product to `K_X(L)`.
* `Stacks.DenominatorIdealResidue.toKExplicit`: their composite, an explicit morphism
  `L ⟶ K_X(L)` read as a morphism of `𝒪_X`-modules.

## Main results

* `Stacks.DenominatorIdealResidue.isLocallyInjective_tmulOne`: local injectivity of
  `x ↦ 1 ⊗ x` on a neighbourhood basis gives local injectivity on the whole site.
* `Stacks.DenominatorIdealResidue.mono_toKExplicit`, and then
  `Stacks.DenominatorIdealResidue.mono_toK`: the canonical map `L ⟶ K_X(L)` is a
  monomorphism.
* `Stacks.DenominatorIdealResidue.mono_denominatorIdealIncl`: hence so is the inclusion of
  the denominator ideal in the structure sheaf.

## Implementation notes

`Stacks.DenominatorIdeal.toK` is the unit of
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`, which is assembled from
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, the **data** form of Tag 03CU.
So `toK` *is* `toKExplicit`, by `rfl`: the presheaf-level unit of
`Stacks.PresheafOfModules.ChangeOfRings`, whose formula on sections is
`Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply`, followed by the sheafification map of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction`, whose underlying morphism of
presheaves of abelian groups is `CategoryTheory.toSheafify` by definition.  That equation is
recorded as `Stacks.DenominatorIdealUnit.toK_eq_toKExplicit`, and `mono_toK` below is
`mono_toKExplicit` for the same reason.

Monicity of `toKExplicit` is local rather than objectwise, which is the point: the
sheafification map is never injective on sections, only *locally* injective, and
`Stacks.SheafOfModules.mono_of_isLocallyInjective` turns local injectivity into monicity
because the source is a sheaf.

What remains open is `isLocallyInjective_tmulOne`'s hypothesis.  It holds for an invertible
`L`: on an open set over which `L` is isomorphic to `𝒪_X` the map `x ↦ 1 ⊗ x` becomes
`𝒪_X(V) ⟶ K_X(V)`, which is injective by
`AlgebraicGeometry.toTotalQuotientSheaf_app_injective`.  Discharging it needs the sections of
a trivialisation `L.over W ≅ 𝒪_W`, and that is the only mathematics still missing.
Consequently **no tag attribute for 02P0 is attached in this file**: the results below
carry a hypothesis that the tagged statement of "inclusion is injective" does not have, so
there is no covering set for that label.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DenominatorIdeal

universe u

namespace Stacks.DenominatorIdealResidue

variable (X : Scheme.{u}) (L : SheafOfModules.{u} (O X))

/-- The ring map `𝒪_X ⟶ K_X` to the sheaf of total quotient rings, as a morphism of presheaves
of commutative rings. -/
abbrev toK₀ : X.sheaf.obj ⟶ (totalQuotientSheaf X.sheaf).obj :=
  (toTotalQuotientSheaf X.sheaf).hom

/-- The map `x ↦ 1 ⊗ x` from `L` to the presheaf tensor product `K_X ⊗_{𝒪_X} L`, as a morphism
of presheaves of `𝒪_X`-modules.  This is the unit of the presheaf-level extension-restriction
adjunction of Tag 03CU, whose value on sections is
`Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply`. -/
def tmulOne :
    L.val ⟶ (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toK₀ X)).obj
      ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (toK₀ X)).obj L.val) :=
  Stacks.PresheafOfModules.ChangeOfRings.unitHom (toK₀ X) (𝟙 _)

/-- The sheafification map from the presheaf tensor product `K_X ⊗_{𝒪_X} L` to the sheaf
`K_X(L)` of meromorphic sections of `L`. -/
def toSheafifyMeromorphic :
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (toK₀ X)).obj L.val ⟶ (K X L).val :=
  (PresheafOfModules.sheafificationAdjunction (R := KRing X) (𝟙 _)).unit.app _

/-- An explicit morphism from `L` to its sheaf of meromorphic sections, read as a morphism of
`𝒪_X`-modules: `x ↦ 1 ⊗ x`, followed by sheafification. -/
def toKExplicit : L ⟶ kAsOModule X L :=
  ⟨Stacks.PresheafOfModules.ChangeOfRings.unitHom (toK₀ X) (toSheafifyMeromorphic X L)⟩

/-- `toKExplicit` factors as `x ↦ 1 ⊗ x` followed by sheafification. -/
lemma toKExplicit_val :
    (toKExplicit X L).val =
      tmulOne X L ≫ (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toK₀ X)).map
        (toSheafifyMeromorphic X L) := by
  refine PresheafOfModules.hom_ext ?_
  intro U
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  rfl

/-- The same factorisation, read on the underlying presheaves of abelian groups. -/
lemma toPresheaf_map_toKExplicit_val :
    (PresheafOfModules.toPresheaf (O X).obj).map (toKExplicit X L).val =
      (PresheafOfModules.toPresheaf (O X).obj).map (tmulOne X L) ≫
        (PresheafOfModules.toPresheaf (O X).obj).map
          ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toK₀ X)).map
            (toSheafifyMeromorphic X L)) := by
  rw [toKExplicit_val]
  exact (PresheafOfModules.toPresheaf (O X).obj).map_comp _ _

/-- Sheafification is locally injective.  Its underlying morphism of presheaves of abelian
groups is `CategoryTheory.toSheafify`, for which this is a Mathlib instance. -/
instance isLocallyInjective_toSheafifyMeromorphic :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (O X).obj).map
        ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toK₀ X)).map
          (toSheafifyMeromorphic X L))) := by
  change CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (toK₀ X)).obj L.val).presheaf))
  infer_instance

/-- If `x ↦ 1 ⊗ x` is injective on the sections over the members of a neighbourhood basis, it is
locally injective for the topology of `X`. -/
lemma isLocallyInjective_tmulOne
    (hloc : ∀ (U : Opens X) (p : X), p ∈ U → ∃ V : Opens X, ∃ _ : V ≤ U, p ∈ V ∧
      Function.Injective
        (((PresheafOfModules.toPresheaf (O X).obj).map (tmulOne X L)).app (op V))) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (O X).obj).map (tmulOne X L)) where
  equalizerSieve_mem {U} x y h := by
    intro p hp
    obtain ⟨V, hVU, hpV, hinj⟩ := hloc U.unop p hp
    refine ⟨V, homOfLE hVU, hinj ?_, hpV⟩
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]

/-- The explicit morphism `L ⟶ K_X(L)` is a monomorphism. -/
lemma mono_toKExplicit
    (hloc : ∀ (U : Opens X) (p : X), p ∈ U → ∃ V : Opens X, ∃ _ : V ≤ U, p ∈ V ∧
      Function.Injective
        (((PresheafOfModules.toPresheaf (O X).obj).map (tmulOne X L)).app (op V))) :
    Mono (toKExplicit X L) :=
  Stacks.SheafOfModules.mono_of_isLocallyInjective (toKExplicit X L)
    ((toPresheaf_map_toKExplicit_val X L) ▸
      (@CategoryTheory.Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (isLocallyInjective_tmulOne X L hloc) (isLocallyInjective_toSheafifyMeromorphic X L)))

/-- The canonical morphism `L ⟶ K_X(L)`, the unit of extension of scalars along `𝒪_X ⟶ K_X`,
is a monomorphism.  It *is* `toKExplicit`, the adjunction being assembled from the data form of
Tag 03CU, so this is `mono_toKExplicit`. -/
lemma mono_toK
    (hloc : ∀ (U : Opens X) (p : X), p ∈ U → ∃ V : Opens X, ∃ _ : V ≤ U, p ∈ V ∧
      Function.Injective
        (((PresheafOfModules.toPresheaf (O X).obj).map (tmulOne X L)).app (op V))) :
    Mono (toK X L) :=
  mono_toKExplicit X L hloc

/-- The inclusion of the denominator ideal of a meromorphic section in the structure sheaf is a
monomorphism.  In the abelian category of sheaves of `𝒪_X`-modules the kernel of the first
projection of a fibre product is the kernel of the opposite leg, so this is exactly
`Stacks.DenominatorIdealResidue.mono_toK`. -/
lemma mono_denominatorIdealIncl (s : MeromorphicSection.{u, u} X.sheaf L)
    (hloc : ∀ (U : Opens X) (p : X), p ∈ U → ∃ V : Opens X, ∃ _ : V ≤ U, p ∈ V ∧
      Function.Injective
        (((PresheafOfModules.toPresheaf (O X).obj).map (tmulOne X L)).app (op V))) :
    Mono (denominatorIdealι X L s) :=
  @pullback.fst_of_mono _ _ _ _ _ _ _ _ (mono_toK X L hloc)

end Stacks.DenominatorIdealResidue
