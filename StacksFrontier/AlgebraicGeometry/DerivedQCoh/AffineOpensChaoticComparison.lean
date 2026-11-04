module

public import StacksFrontier.AlgebraicGeometry.Cohomology.TruncationTowerInput
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedTransport
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningDerivedEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# The change of topology on the affine opens of a scheme

Let `X` be a scheme. [Stacks, Tag 0GZZ] compares the derived category of quasi-coherent modules
on the affine opens of `X` read with the Zariski topology, its item (3), with the same category
read with the **chaotic** topology, its item (4). The comparison is the second conclusion of
[Stacks, Tag 07A8] for the coarsening `ε : (X_{affine, Zar}, 𝒪) ⟶ (X_affine, 𝒪)`, which is
available for an arbitrary ringed site as
`Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfBot`. That statement asks
for exactly two things of the weak Serre subcategory `A` it is applied to: that it *is* a weak
Serre subcategory, and that `H^p_Zar(U, F)` vanish for every object `U` of the site, every
`p > 0` and every `F` of `A`. This file supplies both for `A` the quasi-coherent modules on the
affine Zariski site, and instantiates the equivalence.

## Main results

* `AlgebraicGeometry.Scheme.isZero_moduleCohomology_affineZariskiRingedSite` — **Serre vanishing
  on the affine site**: the positive-degree cohomology of a quasi-coherent module on
  `(X_{affine, Zar}, 𝒪)` over an object of that site vanishes.
* `AlgebraicGeometry.Scheme.isWeakSerreClass_isQuasicoherentOnSite_affineZariski` — **the
  quasi-coherent modules on the affine site form a weak Serre subcategory.**
* `AlgebraicGeometry.Scheme.affineOpensChaoticDerivedEquivalence` — **the comparison (3) ≃ (4) of
  [Stacks, Tag 0GZZ] for a scheme**, as the instance of [Stacks, Tag 07A8] at the affine site.
* `AlgebraicGeometry.Scheme.quasicoherentDerivedAffineChaoticEquivalence` and
  `…OfIsQuasicoherent` — its composite with the comparison (1) ≃ (3) of
  `StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensDerivedComparison.lean`, so **the chain
  (1) ≃ (2) ≃ (3) ≃ (4)**.

## Main definitions

* `AlgebraicGeometry.Scheme.affineOpensModuleCohomologyIso` — restriction to the affine opens
  does not change the cohomology of a sheaf of modules over an affine open.
* `AlgebraicGeometry.Scheme.affineOpensChaoticQuasicoherentDerivedCategory` — the category (4),
  in the spelling [Stacks, Tag 07A8] delivers it: the derived category of modules for the chaotic
  topology whose cohomology lies in the image class `ε_*A` of the first conclusion of that tag.

## The two inputs, and how they are obtained

Both come from the **dense subsite** `AlgebraicGeometry.Scheme.affineOpensToOpens`, along which
restriction of sheaves of modules is an equivalence
`AlgebraicGeometry.Scheme.affineOpensModuleRestrictionEquivalence` matching up the quasi-coherent
objects in both directions, by
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction_iff`.

* **Vanishing.** `Stacks.Cohomology.isZero_moduleCohomology_of_isAffineOpen` is Serre vanishing on
  the site of *all* opens of `X`. Cohomology over an object is the right derived functor of
  evaluation there, and evaluation at an affine open of `X.Opens` is literally restriction to the
  affine opens followed by evaluation at that object of the affine site. So the comparison is the
  transport of a right derived functor along an equivalence of its source,
  `CategoryTheory.Equivalence.compRightDerivedIso` of
  `StacksFrontier/CategoryTheory/Abelian/RightDerivedTransport.lean`.
* **The weak Serre condition.** On `X.Opens` it is Mathlib's quasi-coherence, which is a weak
  Serre class by `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass`
  and agrees with the quasi-coherence of [Stacks, Tag 03DL] (6) there, by
  `AlgebraicGeometry.Scheme.isQuasicoherent_eq_isQuasicoherentOnSite_ringCatSheaf`. Transporting
  it across the equivalence is
  `CategoryTheory.ObjectProperty.isWeakSerreClass_of_iff`.

Neither input is hypothesised and neither carries a hypothesis on `X`: no quasi-compactness, no
quasi-separatedness, no Noetherian hypothesis. The chaotic analogue
`Stacks.Sheaves.ChaoticFlatQuasicoherent.isQuasicoherentOnSite_isWeakSerreClass` needs
`Fact (X.J = ⊥)` and so does not serve the Zariski side; the statement below is proved on the
Zariski side directly.

## What is still missing for [Stacks, Tag 0A9E]

The spelling of item (4). What `derivedPullbackEquivalenceImageOfBot` produces is the subcategory
of `D(X_affine, 𝒪)` cut out by `Stacks.Cohomology.CompareTopologies.imageOfLE`, the image of the
quasi-coherent modules under `ε_*`, inside
`CategoryTheory.DerivedCategory (SheafOfModules.{u} (𝒪.ofLE bot_le))`. The downstream consumer
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_affineSiteAdjunction`
needs it in the spelling
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.qcohCohomologyProperty`, which lives over
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod`, i.e. over
`CategoryTheory.DerivedCategory (PresheafOfModules.{u} 𝒪.obj)`. Those are different ambient
categories — sheaves for the chaotic topology versus presheaves — and the comparison of the two
is not made in this file, so Tag 0A9E does **not** follow from it and no `stacks 0A9E`
attribute appears below.

The two *ambient* categories are bridged in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensChaoticPresheafBridge.lean`, which also
restates the chain below at the locally small derived-category model the consumer uses. What
remains after that is one equality of object properties on `SheafOfModules.{u} 𝒪_⊥`, namely that
`Stacks.Cohomology.CompareTopologies.imageOfLE bot_le 𝒪` of the quasi-coherent modules is
`SheafOfModules.isQuasicoherentOnSite 𝒪_⊥`; the coverage note of that file says what the two
directions of it are.

## References

* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-! ### Cohomology over an affine open is computed on the affine site -/

/-- **Restriction to the affine opens does not change cohomology over an affine open.** For an
affine open `U` of `X` and a sheaf of `𝒪_X`-modules `M`, the `p`-th cohomology of `M` over `U`
on the site of all opens is the `p`-th cohomology of its restriction over `U` on the affine
site.

Cohomology over an object is the right derived functor of evaluation, and evaluation at `U` on
`X.Opens` *is* restriction to the affine opens followed by evaluation at `U` on the affine site —
the two functors are equal, restriction being precomposition with
`AlgebraicGeometry.Scheme.affineOpensToOpens`. So the comparison is the transport of a right
derived functor along an equivalence of its source. -/
def Scheme.affineOpensModuleCohomologyIso (U : X.affineOpens) (p : ℕ)
    (M : SheafOfModules.{u} X.ringCatSheaf) :
    Stacks.Cohomology.moduleCohomology X.ringCatSheaf (U : X.Opens) p M ≅
      Stacks.Cohomology.moduleCohomology
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O) U p
        (X.affineOpensModuleRestriction.obj M) :=
  have := X.isEquivalence_affineOpensModuleRestriction
  (X.affineOpensModuleRestriction.compRightDerivedIso
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)
      (.op U)) p).app M

/-! ### Serre vanishing on the affine site -/

/-- Quasi-coherence of a module on the affine site is quasi-coherence of its image under the
inverse of the restriction equivalence. -/
private theorem isQuasicoherentOnSite_affineZariski_iff_aux
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)) :
    SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O) N ↔
      SheafOfModules.isQuasicoherentOnSite.{u, u, u, u} X.ringCatSheaf
        (X.affineOpensModuleRestrictionEquivalence.inverse.obj N) := by
  have hiso : X.affineOpensModuleRestriction.obj
      (X.affineOpensModuleRestrictionEquivalence.inverse.obj N) ≅ N :=
    X.affineOpensModuleRestrictionEquivalence.counitIso.app N
  have hcl : (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      X.affineZariskiRingedSite.O)).IsClosedUnderIsomorphisms := inferInstance
  exact ⟨fun h ↦ (X.isQuasicoherentOnSite_affineOpensModuleRestriction_iff _).1
      (hcl.of_iso hiso.symm h),
    fun h ↦ hcl.of_iso hiso
      ((X.isQuasicoherentOnSite_affineOpensModuleRestriction_iff _).2 h)⟩

/-- **Serre vanishing on the affine Zariski site of a scheme.** The positive-degree cohomology of
a quasi-coherent module on the ringed site `(X_{affine, Zar}, 𝒪)`, over an object `U` of that
site, vanishes.

Every object of the affine site is an affine open of `X`, so this is [Stacks, Tag 01XB] —
available on the site of all opens as
`Stacks.Cohomology.isZero_moduleCohomology_of_isAffineOpen` — carried across the dense subsite by
`AlgebraicGeometry.Scheme.affineOpensModuleCohomologyIso`. The module is written as the
restriction of one on `X.Opens` using that restriction is an equivalence, and its
quasi-coherence there is the reflection
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_of_affineOpensModuleRestriction`.

[Stacks, Tag 01XB] (not registered here: this is not the whole statement of the tag): Serre
vanishing over an object of the affine Zariski site of a scheme, for a quasi-coherent module on
that site
-/
theorem Scheme.isZero_moduleCohomology_affineZariskiRingedSite
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O))
    (hF : SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O) F)
    (U : X.affineOpens) (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.Cohomology.moduleCohomology
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O) U p F) := by
  have hiso : X.affineOpensModuleRestriction.obj
      (X.affineOpensModuleRestrictionEquivalence.inverse.obj F) ≅ F :=
    X.affineOpensModuleRestrictionEquivalence.counitIso.app F
  have hM := (isQuasicoherentOnSite_affineZariski_iff_aux X F).1 hF
  have hMq : SheafOfModules.isQuasicoherent X.ringCatSheaf
      (X.affineOpensModuleRestrictionEquivalence.inverse.obj F) :=
    X.isQuasicoherent_eq_isQuasicoherentOnSite_ringCatSheaf ▸ hM
  have h01XB := Stacks.Cohomology.isZero_moduleCohomology_of_isAffineOpen X
    (X.affineOpensModuleRestrictionEquivalence.inverse.obj F) hMq (U : X.Opens) U.2 p hp
  have h2 := h01XB.of_iso
    (X.affineOpensModuleCohomologyIso U p
      (X.affineOpensModuleRestrictionEquivalence.inverse.obj F)).symm
  exact h2.of_iso (((SheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O) (.op U)).rightDerived
      p).mapIso hiso.symm)

/-! ### The quasi-coherent modules on the affine site form a weak Serre subcategory -/

/-- **Quasi-coherence on the affine site is the inverse image of quasi-coherence on `X.Opens`.**
A sheaf of modules on `(X_{affine, Zar}, 𝒪)` is quasi-coherent if and only if the corresponding
sheaf of `𝒪_X`-modules is, the correspondence being
`AlgebraicGeometry.Scheme.affineOpensModuleRestrictionEquivalence`. -/
theorem Scheme.isQuasicoherentOnSite_affineZariski_iff
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)) :
    SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O) N ↔
      SheafOfModules.isQuasicoherentOnSite.{u, u, u, u} X.ringCatSheaf
        (X.affineOpensModuleRestrictionEquivalence.inverse.obj N) :=
  isQuasicoherentOnSite_affineZariski_iff_aux X N

/-- **The quasi-coherent modules on the affine Zariski site of a scheme form a weak Serre
subcategory** of all modules on that site, in the sense of [Stacks, Tag 0754].

On `X.Opens` this is [Stacks, Tag 01LA], available as
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass` for Mathlib's
quasi-coherence, which agrees there with the quasi-coherence of [Stacks, Tag 03DL] (6). The
affine site's class corresponds to it across the equivalence of module categories, by
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_affineZariski_iff`,
and a weak Serre class pulls back along an exact functor. -/
instance Scheme.isWeakSerreClass_isQuasicoherentOnSite_affineZariski :
    (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)).IsWeakSerreClass :=
  have : (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u} X.ringCatSheaf).IsWeakSerreClass :=
    X.isQuasicoherent_eq_isQuasicoherentOnSite_ringCatSheaf ▸
      (inferInstance : (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsWeakSerreClass)
  CategoryTheory.ObjectProperty.isWeakSerreClass_of_iff
    (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u} X.ringCatSheaf)
    X.affineOpensModuleRestrictionEquivalence.inverse
    (X.isQuasicoherentOnSite_affineZariski_iff)

/-! ### The comparison (3) ≃ (4) of [Stacks, Tag 0GZZ] -/

section Chaotic

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Category (4) of [Stacks, Tag 0GZZ] for a scheme**, in the spelling the second conclusion of
[Stacks, Tag 07A8] delivers it: the full subcategory of the derived category of modules on the
affine opens of `X` *with the chaotic topology* whose cohomology sheaves lie in the image class
`ε_*A` of the first conclusion of that tag, for `A` the quasi-coherent modules on the affine
Zariski site. -/
abbrev Scheme.affineOpensChaoticQuasicoherentDerivedCategory :=
  (DerivedCategoryB.derivedCategoryB
    (Stacks.Cohomology.CompareTopologies.imageOfLE
      (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
        X.affineZariskiRingedSite.J)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)
      (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)))).FullSubcategory

/-- **The comparison (3) ≃ (4) of [Stacks, Tag 0GZZ] for a scheme.** Reading the affine opens of
`X` with the chaotic topology instead of the Zariski topology does not change the derived
category of complexes with quasi-coherent cohomology: derived pullback and derived pushforward
along the coarsening `ε` are quasi-inverse equivalences

`D_{ε_*QCoh}(X_affine, 𝒪) ≌ D_QCoh(X_{affine, Zar}, 𝒪)`.

This is `Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfBot`, the chaotic
case of the second conclusion of [Stacks, Tag 07A8], instantiated at the affine site of `X` and
at the quasi-coherent modules on it. Its two inputs are
`AlgebraicGeometry.Scheme.isWeakSerreClass_isQuasicoherentOnSite_affineZariski` and
`AlgebraicGeometry.Scheme.isZero_moduleCohomology_affineZariskiRingedSite`; no hypothesis is
carried. The two functors are `Lε^*` and `Rε_*`, by
`Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfLE_functor_comp_ι` and
`…_inverse_comp_ι`.

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): the
comparison (3) ≃ (4) for a scheme, with the quasi-coherent modules on the affine Zariski site as
the weak Serre subcategory and no hypothesis carried
-/
def Scheme.affineOpensChaoticDerivedEquivalence :
    X.affineOpensChaoticQuasicoherentDerivedCategory ≌
      X.affineOpensQuasicoherentDerivedCategory :=
  Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfBot
    X.affineZariskiRingedSite
    (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O))
    fun U p hp F hF ↦ X.isZero_moduleCohomology_affineZariskiRingedSite F hF U p hp

/-- **The chain (1) ≃ (2) ≃ (3) ≃ (4) of [Stacks, Tag 0GZZ] for a scheme.** The derived category
of `𝒪_X`-modules with quasi-coherent cohomology is equivalent to the derived category of modules
on the affine opens of `X` **with the chaotic topology** whose cohomology lies in `ε_*QCoh`.

This is `AlgebraicGeometry.Scheme.quasicoherentDerivedAffineOpensEquivalence`, the comparison
(1) ≃ (3) induced by derived restriction to the affine opens, followed by the change of topology
`AlgebraicGeometry.Scheme.affineOpensChaoticDerivedEquivalence`. Categories (1) and (2) of 0GZZ
are the same category of modules here, so this is the whole chain up to (4). No hypothesis is
carried.

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): the chain
(1) = (2) ≃ (3) ≃ (4) for a scheme, with (4) read as the image class of [Stacks, Tag 07A8]
-/
def Scheme.quasicoherentDerivedAffineChaoticEquivalence :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite X.ringCatSheaf)).FullSubcategory ≌
      X.affineOpensChaoticQuasicoherentDerivedCategory :=
  X.quasicoherentDerivedAffineOpensEquivalence.trans
    X.affineOpensChaoticDerivedEquivalence.symm

/-- **The chain (1) ≃ (2) ≃ (3) ≃ (4) of [Stacks, Tag 0GZZ], with (1) read over Mathlib's
quasi-coherence.** The same statement as
`AlgebraicGeometry.Scheme.quasicoherentDerivedAffineChaoticEquivalence` with the source written
in the spelling of `Stacks.Duality.quasiCoherentDerivedCategory`.

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): the chain
(1) = (2) ≃ (3) ≃ (4) for a scheme, with (1) read over Mathlib's quasi-coherence predicate
-/
def Scheme.quasicoherentDerivedAffineChaoticEquivalenceOfIsQuasicoherent :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory ≌
      X.affineOpensChaoticQuasicoherentDerivedCategory :=
  X.quasicoherentDerivedAffineOpensEquivalenceOfIsQuasicoherent.trans
    X.affineOpensChaoticDerivedEquivalence.symm

end Chaotic

end AlgebraicGeometry

end
