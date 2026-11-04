module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticPresheafBridge
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensZariskiDescent
import StacksCore.Tactic.StacksAttribute

/-!
# Item (4) of [Stacks, Tag 0GZZ] as the quasi-coherent modules for the chaotic topology

`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensChaoticPresheafBridge.lean` leaves one
statement between this development and [Stacks, Tag 0A9E]: the equality of object properties on
`SheafOfModules.{u} 𝒪_⊥` for `𝒪` the structure sheaf of the affine Zariski site of a scheme `X`,

```
Stacks.Cohomology.CompareTopologies.imageOfLE bot_le 𝒪 (quasi-coherent modules on X_{affine,Zar})
  = SheafOfModules.isQuasicoherentOnSite 𝒪_⊥
```

between the class in which the second conclusion of [Stacks, Tag 07A8] delivers item (4) of
[Stacks, Tag 0GZZ] — the image of the quasi-coherent modules under `ε_*` — and the class of
modules which are quasi-coherent for the chaotic topology. This file proves it, and draws the
consequences.

## Main results

* `AlgebraicGeometry.Scheme.isQuasicoherentOnSite_le_imageOfLE_affineChaotic` — the inclusion
  that was missing: **a quasi-coherent module for the chaotic topology on the affine opens of a
  scheme is the coarsening of a quasi-coherent module for the Zariski topology.**
* `AlgebraicGeometry.Scheme.imageOfLE_eq_isQuasicoherentOnSite_affineChaotic` — **the equality**,
  together with `…imageOfLE_le_isQuasicoherentOnSite_affineChaotic`.
* `AlgebraicGeometry.exists_generating_family_quasiCoherentDerivedCategory` — **a generating
  family in the sense of [Stacks, Tag 0GYG] for `D_QCoh(𝒪_X)`, indexed by a `Type u`, for an
  arbitrary scheme and with no hypothesis.**
* `AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward` — **[Stacks, Tag 0A9E]**:
  for a quasi-compact quasi-separated morphism of schemes with quasi-compact target,
  `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint. No hypothesis is carried.

## Main definitions

* `AlgebraicGeometry.Scheme.imageOfLEQcohCohomologyEquivalence` and
  `AlgebraicGeometry.Scheme.quasicoherentDerivedQcohCohomologyEquivalence` — the chain
  (1) ≃ (2) ≃ (3) ≃ (4) of [Stacks, Tag 0GZZ] with item (4) read as
  `Stacks.ModulesOnACategory.QuasiCoherentCohomology.qcohCohomologyProperty`, the spelling in
  which the generating family of [Stacks, Tag 0GYG] is produced.

## The missing inclusion

Unwound through [Stacks, Tag 0GZN],
`Stacks.SheafOfModules.isQuasicoherent_iff_canonicalMap_isIso`, a quasi-coherent module `N` for
the chaotic topology is exactly a *cartesian* presheaf of modules on the affine opens: all its
base-change comparisons `N(U) ⊗_{Γ(X, U)} Γ(X, V) ⟶ N(V)` are isomorphisms. Two things then have
to be said, and both are about the Zariski topology.

* `N` is a **Zariski sheaf**, so that it is the coarsening of a sheaf of modules on
  `(X_{affine, Zar}, 𝒪)` at all. This is Zariski descent for modules,
  `AlgebraicGeometry.Scheme.isSheaf_affineOpensTopology_of_cartesian`.
* That sheaf is **quasi-coherent for the Zariski topology**. This is
  `Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso`, which produces a global
  presentation over the chaotic covering of each object and transports it to the finer topology
  by `SheafOfModules.IsQuasicoherentOnSite.of_coarser`; the cartesian condition is the same one.

Coarsening changes neither the underlying presheaf of modules nor the morphisms,
`SheafOfModules.ofLE_obj_val`, and the sheaf condition is a proposition, so the witnessing
isomorphism `ε_*M ≅ N` is the identity.

## From the equality to [Stacks, Tag 0A9E]

The equality turns the chain
`AlgebraicGeometry.Scheme.quasicoherentDerivedAffineChaoticEquivalenceLocallySmall`, whose target
is the derived subcategory of the image class, into one whose target is the derived subcategory of
the quasi-coherent modules for the chaotic topology; composed with
`AlgebraicGeometry.Scheme.affineChaoticQcohCohomologyEquivalence`'s passage from sheaves to
presheaves this is an equivalence

`D_QCoh(𝒪_X) ≌ D_QCoh(X_affine, 𝒪)`

onto the subcategory cut out by
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.qcohCohomologyProperty`. That is the category
on which `AlgebraicGeometry.exists_generating_family_qcohCohomology_affineChaotic` produces a
generating family indexed by a `Type u` with no hypothesis, so
`CategoryTheory.exists_generating_family_of_equivalence` carries the family to `D_QCoh(𝒪_X)`, and
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_generating`
— which has [Stacks, Tag 08DZ] and part (1) of [Stacks, Tag 08D5] already discharged — turns it
into the right adjoint of `Rf_*`.

Tag 0A9E assumes `X` and `Y` quasi-compact and quasi-separated; the statement below assumes `f`
quasi-compact and quasi-separated and `Y` quasi-compact, which those hypotheses imply, so it is
the tag and a little more.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0GZN](https://stacks.math.columbia.edu/tag/0GZN)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ModulesOnACategory.QuasiCoherentCohomology

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-! ### The missing inclusion, and the equality -/

/-- **A quasi-coherent module for the chaotic topology on the affine opens of a scheme lies in
the image of `ε_*`.** This is the inclusion of object properties on `SheafOfModules.{u} 𝒪_⊥`
converse to `AlgebraicGeometry.Scheme.imageOfLE_le_isQuasicoherentOnSite_affineChaotic`.

By [Stacks, Tag 0GZN] the hypothesis says that `N` is cartesian; it is then a Zariski sheaf by
`AlgebraicGeometry.Scheme.isSheaf_affineOpensTopology_of_cartesian`, hence the coarsening of a
sheaf of modules `M` on `(X_{affine, Zar}, 𝒪)` with the same underlying presheaf, and `M` is
quasi-coherent for the Zariski topology by
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso` applied to the same cartesian
condition. -/
theorem Scheme.isQuasicoherentOnSite_le_imageOfLE_affineChaotic :
    SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O) ≤
      Stacks.Cohomology.CompareTopologies.imageOfLE
        (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
          X.affineZariskiRingedSite.J)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)
        (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)) := by
  intro N hN
  have hcan := (Stacks.SheafOfModules.isQuasicoherent_iff_canonicalMap_isIso
    X.affineChaoticRingedSite N rfl).1 hN
  have hM : ∀ {A B : (X.affineOpens)ᵒᵖ} (k : A ⟶ B),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := X.affineOpensToOpens.op ⋙ X.presheaf) N.val k) :=
    fun {_ _} k ↦ hcan k.unop
  refine ⟨⟨N.val, X.isSheaf_affineOpensTopology_of_cartesian N.val hM⟩, ?_, ⟨Iso.refl _⟩⟩
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso
    X.affineZariskiRingedSite _ (fun {_ _} f ↦ hcan f)

/-- **Item (4) of [Stacks, Tag 0GZZ] in its two spellings on modules.** The image under `ε_*` of
the quasi-coherent modules on the affine Zariski site of a scheme is exactly the class of
quasi-coherent modules for the chaotic topology.

The two inclusions are
`AlgebraicGeometry.Scheme.imageOfLE_le_isQuasicoherentOnSite_affineChaotic`, which is the
cartesian property of a quasi-coherent module, and
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_le_imageOfLE_affineChaotic`, which is Zariski
descent.

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): item (4) as
the image class of Tag 07A8 is item (4) as quasi-coherence
-/
theorem Scheme.imageOfLE_eq_isQuasicoherentOnSite_affineChaotic :
    Stacks.Cohomology.CompareTopologies.imageOfLE
        (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
          X.affineZariskiRingedSite.J)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)
        (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)) =
      SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O) :=
  le_antisymm X.imageOfLE_le_isQuasicoherentOnSite_affineChaotic
    X.isQuasicoherentOnSite_le_imageOfLE_affineChaotic

/-! ### Item (4) in the spelling of the generating family -/

/-- **The derived subcategory of the image class of [Stacks, Tag 07A8] is item (4) of
[Stacks, Tag 0GZZ] as `qcohCohomologyProperty`.** This is
`AlgebraicGeometry.Scheme.affineChaoticQcohCohomologyEquivalence` with its source rewritten
along `AlgebraicGeometry.Scheme.imageOfLE_eq_isQuasicoherentOnSite_affineChaotic`. -/
def Scheme.imageOfLEQcohCohomologyEquivalence :
    (DerivedCategoryB.derivedCategoryB
        (Stacks.Cohomology.CompareTopologies.imageOfLE
          (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
            X.affineZariskiRingedSite.J)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)
          (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              X.affineZariskiRingedSite.O)))).FullSubcategory ≌
      (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory :=
  X.imageOfLE_eq_isQuasicoherentOnSite_affineChaotic ▸ X.affineChaoticQcohCohomologyEquivalence

/-- **The chain (1) ≃ (2) ≃ (3) ≃ (4) of [Stacks, Tag 0GZZ] at the locally small model, with item
(4) read as `qcohCohomologyProperty`.** The derived category of `𝒪_X`-modules with quasi-coherent
cohomology, in the spelling `Stacks.Duality.quasiCoherentDerivedCategory X` the duality
development uses, is equivalent to `D_QCoh(X_affine, 𝒪)` in the spelling in which the generating
family of [Stacks, Tag 0GYG] is produced. No hypothesis is carried.

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): the chain
(1) = (2) = (3) = (4), locally small model, (4) on presheaves
-/
def Scheme.quasicoherentDerivedQcohCohomologyEquivalence :
    Stacks.Duality.quasiCoherentDerivedCategory X ≌
      (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory :=
  X.quasicoherentDerivedAffineChaoticEquivalenceLocallySmall.trans
    X.imageOfLEQcohCohomologyEquivalence

/-! ### [Stacks, Tag 0A9E] -/

/-- **A generating family in the sense of [Stacks, Tag 0GYG] for `D_QCoh(𝒪_X)`, indexed by a
`Type u`.** For an arbitrary scheme `X : Scheme.{u}`, with no hypothesis, there is a family
`E : ι → D_QCoh(𝒪_X)` with `ι : Type u` which detects nonzero objects and through which every
morphism into a countable direct sum factors.

This is `AlgebraicGeometry.exists_generating_family_qcohCohomology_affineChaotic`, which produces
such a family on the affine site, transported along
`AlgebraicGeometry.Scheme.quasicoherentDerivedQcohCohomologyEquivalence` by
`CategoryTheory.exists_generating_family_of_equivalence`. -/
theorem exists_generating_family_quasiCoherentDerivedCategory :
    ∃ (ι : Type u) (E : ι → Stacks.Duality.quasiCoherentDerivedCategory X),
      (∀ K : Stacks.Duality.quasiCoherentDerivedCategory X, ¬ IsZero K →
          ∃ (i : ι) (g : E i ⟶ K), g ≠ 0) ∧
        ∀ (K : ℕ → Stacks.Duality.quasiCoherentDerivedCategory X) (i : ι) (α : E i ⟶ ∐ K),
          ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ K n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
            α = γ ≫ Limits.Sigma.map β := by
  obtain ⟨ι, E, hE, hE'⟩ := exists_generating_family_qcohCohomology_affineChaotic X
  obtain ⟨h1, h2⟩ := CategoryTheory.exists_generating_family_of_equivalence
    X.quasicoherentDerivedQcohCohomologyEquivalence.symm E hE hE'
  exact ⟨ι, _, h1, h2⟩

open Stacks.Duality.DerivedPushforward in
/-- **[Stacks, Tag 0A9E].** Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of
schemes with `Y` quasi-compact. Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint, the
twisted inverse image `f^×`.

The source assumes `X` and `Y` quasi-compact and quasi-separated, which gives these hypotheses:
`Y` is quasi-compact; `f` is quasi-compact because `X` is and `Y` is quasi-separated; and `f` is
quasi-separated because `X` is.

The generating family of [Stacks, Tag 0GYG] is
`AlgebraicGeometry.exists_generating_family_quasiCoherentDerivedCategory`, and
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_generating`
supplies the rest of the source's argument: part (1) of [Stacks, Tag 08D5], that `Rf_*` preserves
quasi-coherence of cohomology, and [Stacks, Tag 08DZ], that the restricted functor commutes with
direct sums. -/
@[stacks 0A9E "for a quasi-compact quasi-separated morphism with quasi-compact target"]
theorem isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] :
    (Stacks.Duality.quasiCoherentDerivedPushforward f
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).IsLeftAdjoint := by
  obtain ⟨ι, E, hE, hE'⟩ := exists_generating_family_quasiCoherentDerivedCategory X
  exact isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_generating f E hE hE'

end AlgebraicGeometry

end
