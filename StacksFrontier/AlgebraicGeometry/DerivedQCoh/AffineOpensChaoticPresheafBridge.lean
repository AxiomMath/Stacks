module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticComparison
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineSiteQuasiCoherentObjects
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.AffineSiteGeneratingFamily
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentCartesian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.SmallRepresentatives
import StacksCore.Tactic.StacksAttribute

/-!
# Item (4) of [Stacks, Tag 0GZZ]: sheaves for the chaotic topology versus presheaves

Item (4) of [Stacks, Tag 0GZZ] — the derived category of modules with quasi-coherent cohomology
on the affine opens of a scheme `X` read with the **chaotic** topology — is spelled two
incompatible ways in this library.

* `AlgebraicGeometry.Scheme.affineOpensChaoticQuasicoherentDerivedCategory` of
  `StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensChaoticComparison.lean` lives over
  `CategoryTheory.DerivedCategory (SheafOfModules.{u} 𝒪_⊥)` — the shape in which the second
  conclusion of [Stacks, Tag 07A8] delivers the change of topology.
* `Stacks.ModulesOnACategory.QuasiCoherentCohomology.qcohCohomologyProperty` of
  `AlgebraicGeometry.Scheme.affineChaoticRingedSite` lives over
  `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod`, which is
  `CategoryTheory.DerivedCategory (PresheafOfModules.{u} 𝒪.obj)` — the shape in which the
  generating family of [Stacks, Tag 0GYG] is produced, and the one the consumer
  `AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_affineSiteAdjunction`
  binds.

This file bridges the two **ambient** categories, and reduces the comparison of the two
subcategories to a single statement about modules.

## Main definitions

* `AlgebraicGeometry.Scheme.affineChaoticSheafPresheafEquivalence` — on the chaotic site a
  sheaf of modules is a presheaf of modules; this is
  `Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence` at the affine site of a scheme.
* `AlgebraicGeometry.Scheme.affineChaoticDerivedSheafPresheafEquivalence` — the induced
  equivalence of the two ambient unbounded derived categories.
* `AlgebraicGeometry.Scheme.affineChaoticQcohCohomologyEquivalence` — **the two spellings of
  "quasi-coherent cohomology on the chaotic affine site" cut out equivalent subcategories.**

## Main results

* `AlgebraicGeometry.Scheme.qcohCohomologyProperty_affineChaotic_iff` — an object of
  `D(X_affine, 𝒪)` read as sheaves has all of its cohomology sheaves quasi-coherent if and only
  if its image read as presheaves does.
* `AlgebraicGeometry.Scheme.quasicoherentDerivedAffineChaoticEquivalenceLocallySmall` — the chain
  (1) ≃ (2) ≃ (3) ≃ (4) of `AffineOpensChaoticComparison.lean`, restated at the **locally small**
  derived-category model, so that its source is literally
  `Stacks.Duality.quasiCoherentDerivedCategory X` as the consumer spells it.
* `AlgebraicGeometry.Scheme.isIso_canonicalMap_affineChaotic_of_isQuasicoherent` and
  `AlgebraicGeometry.Scheme.imageOfLE_le_isQuasicoherentOnSite_affineChaotic` — **one of the two
  inclusions of the equality of the two spellings of item (4)**: the image under `ε_*` of the
  quasi-coherent modules on the affine Zariski site is contained in the quasi-coherent modules
  for the chaotic topology.

## The equality of the two spellings of item (4)

The two readings of item (4) on modules are the two object properties on
`SheafOfModules.{u} 𝒪_⊥`

```
Stacks.Cohomology.CompareTopologies.imageOfLE bot_le 𝒪 (quasi-coherent modules on X_{affine,Zar})
  = SheafOfModules.isQuasicoherentOnSite 𝒪_⊥
```

`AlgebraicGeometry.Scheme.affineOpensChaoticDerivedEquivalence` produces item (4) over the left
class — the image of the quasi-coherent modules under `ε_*` — and this file connects the right
class to `qcohCohomologyProperty`. That equality is
`AlgebraicGeometry.Scheme.imageOfLE_eq_isQuasicoherentOnSite_affineChaotic` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensChaoticQuasicoherentEquality.lean`, where
it
is combined with the chain (1) ≃ (2) ≃ (3) ≃ (4) proved here to discharge the hypothesis of
`AlgebraicGeometry.exists_generating_family_quasiCoherentDerivedCategory_of_adjunction` and hence
[Stacks, Tag 0A9E]. One of its two inclusions is proved below.

Unwound through `Stacks.SheafOfModules.isQuasicoherent_iff_canonicalMap_isIso`, which
characterises the right-hand class by invertibility of the base-change maps
`N(V) ⊗_{𝒪(V)} 𝒪(U) ⟶ N(U)`, that equality is the following pair of statements about a presheaf
of modules on the affine opens of a scheme.

* **Left to right.** A quasi-coherent module on the affine Zariski site is cartesian: for affine
  opens `V ≤ U` the map `M(U) ⊗_{Γ(X,U)} Γ(X,V) ⟶ M(V)` is an isomorphism. This is proved here,
  as `AlgebraicGeometry.Scheme.imageOfLE_le_isQuasicoherentOnSite_affineChaotic`, out of
  `Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_restrictₗ` — which is Descent,
  Proposition 03DX for a scheme — through
  `StacksFrontier/AlgebraicGeometry/Modules/QuasicoherentCartesian.lean`. The coverage note of
  `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentModulesAndAffines.lean` records it as one
  of the "converse implications" of [Stacks, Tag 0GZX] that the development does not have; for a
  plain scheme it does.
* **Right to left.** A cartesian presheaf of modules on the affine opens satisfies the Zariski
  sheaf condition, so that it is in the image of `ε_*` at all. This is Zariski descent for
  modules, the other half of the same coverage note, and it is
  `AlgebraicGeometry.Scheme.isSheaf_affineOpensTopology_of_cartesian` of
  `StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensZariskiDescent.lean`. The machinery is
  `Stacks.Sites.isSheafFor_of_cartesian` of
  `StacksFrontier/CategoryTheory/Sites/Modules/CartesianSheafCondition.lean`, whose `IsPushout`
  hypothesis asks for `Γ(X, V ⊓ V') = Γ(X, V) ⊗_{Γ(X, U)} Γ(X, V')`; the companion
  `StacksFrontier/AlgebraicGeometry/Topologies/CartesianModulesOnAffineSite.lean` runs that argument
  for a site of affine *schemes* with pullbacks, which the poset of affine opens is not, so the
  covering families are instead refined to **basic opens**, for which the pushout is a base
  change of a localization away from one element.

## Implementation notes

Three definitional coincidences carry the whole file and each is checked by a `rfl` below or in
`AffineOpensChaoticComparison.lean`: `AlgebraicGeometry.Scheme.affineChaoticRingedSite.J` is
`⊥`; the structure sheaf of the chaotic reading of the affine site is the coarsening
`𝒪.ofLE bot_le` of the Zariski one, so the two namings of `𝒪_⊥` agree — this is the hazard the
explicit ascription in
`Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfLE` guards against; and
`Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence` is `SheafOfModules.forget` with
`CategoryTheory.Presheaf.isSheaf_bot` for its inverse and `Iso.refl` for its unit and counit, so
it is additive by `⟨rfl⟩` and no coherence is needed to derive it on complexes.

The passage from modules to complexes is
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, exactly as in
`AlgebraicGeometry.Scheme.derivedCategoryB_isQuasicoherentOnSite_affineOpensRestriction_iff`. The
sheaf condition appearing in `Stacks.ModulesOnACategory.QuasiCoherentCohomology`'s
`hasQuasicoherentCohomology` is discharged by `Presheaf.isSheaf_bot`, and the two proofs of it
that then occur are interchangeable by proof irrelevance, so the two sheaves of modules they
produce are the same term.

The locally small restatement names both derived-category models explicitly —
`SheafOfModules.hasDerivedCategory` and `CategoryTheory.HasDerivedCategory.standard` — as the
implementation notes of
`StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean` require, and the transport
is `StacksDraft.DerivedModel.derivedCategoryBModelEquiv`.

## References

* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 0GZN](https://stacks.math.columbia.edu/tag/0GZN)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.CartesianQuasicoherent

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-! ### Sheaves for the chaotic topology are presheaves -/

/-- **The structure sheaf of the chaotic affine site is the coarsening of the Zariski one.** The
two namings of `𝒪_⊥` that the change-of-topology statements and the quasi-coherence statements
use are the same term. -/
theorem Scheme.affineChaoticRingedSite_ringSheaf_eq_ofLE :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O) =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O).ofLE
        (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
          X.affineZariskiRingedSite.J) :=
  rfl

/-- **On the chaotic affine site of a scheme, sheaves of modules are presheaves of modules.** The
topology is `⊥`, for which every presheaf is a sheaf, so the forgetful functor is an
equivalence. -/
def Scheme.affineChaoticSheafPresheafEquivalence :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O) ≌
      _root_.PresheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O).obj :=
  Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence _

/-- The equivalence `AlgebraicGeometry.Scheme.affineChaoticSheafPresheafEquivalence` is
`SheafOfModules.forget`, so it is additive on the nose. -/
instance Scheme.additive_affineChaoticSheafPresheafEquivalence_functor :
    X.affineChaoticSheafPresheafEquivalence.functor.Additive :=
  ⟨rfl⟩

/-- **The two ambient derived categories of item (4) of [Stacks, Tag 0GZZ] are equivalent**:
`D(X_affine, 𝒪)` read as sheaves of modules for the chaotic topology and read as presheaves of
modules. -/
def Scheme.affineChaoticDerivedSheafPresheafEquivalence :
    DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O)) ≌
      Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O).obj :=
  Stacks.DerivedQCoh.Equivalence.mapDerivedCategory X.affineChaoticSheafPresheafEquivalence

/-- Quasi-coherence on the chaotic affine site of the sheaf corresponding to a presheaf of modules
is invariant under isomorphism of presheaves. -/
private theorem isQuasicoherentOnSite_inverse_iff_of_iso
    {A B : _root_.PresheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O).obj} (e : A ≅ B) :
    SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O)
        (X.affineChaoticSheafPresheafEquivalence.inverse.obj A) ↔
      SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O)
        (X.affineChaoticSheafPresheafEquivalence.inverse.obj B) :=
  ObjectProperty.prop_iff_of_iso _ (X.affineChaoticSheafPresheafEquivalence.inverse.mapIso e)

open Stacks.ModulesOnACategory.QuasiCoherentCohomology in
/-- **Quasi-coherent cohomology on the chaotic affine site means the same thing on sheaves and on
presheaves.** A complex of sheaves of modules for the chaotic topology has quasi-coherent
cohomology in every degree if and only if the corresponding complex of presheaves of modules
satisfies `Stacks.ModulesOnACategory.QuasiCoherentCohomology.qcohCohomologyProperty`.

The sheaf condition that the latter asks for in each degree is automatic at the chaotic topology,
by `CategoryTheory.Presheaf.isSheaf_bot`; what is left is the comparison of the cohomology of the
transported complex with the transport of its cohomology,
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`. -/
theorem Scheme.qcohCohomologyProperty_affineChaotic_iff
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O))) :
    qcohCohomologyProperty.{u} X.affineChaoticRingedSite
        (X.affineChaoticDerivedSheafPresheafEquivalence.functor.obj K) ↔
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O)) K := by
  have hcomp := fun n : ℤ ↦
    (CategoryTheory.Functor.mapDerivedCategoryHomologyIso
      X.affineChaoticSheafPresheafEquivalence.functor n).app K
  exact forall_congr' fun n ↦
    ⟨fun ⟨_, hQC⟩ ↦ ObjectProperty.prop_of_iso _
        (X.affineChaoticSheafPresheafEquivalence.unitIso.symm.app _)
        ((isQuasicoherentOnSite_inverse_iff_of_iso X (hcomp n)).1 hQC),
      fun h ↦ ⟨Presheaf.isSheaf_bot _, (isQuasicoherentOnSite_inverse_iff_of_iso X (hcomp n)).2
        (ObjectProperty.prop_of_iso _ (X.affineChaoticSheafPresheafEquivalence.unitIso.app _) h)⟩⟩

/-- **The two spellings of item (4) of [Stacks, Tag 0GZZ] cut out equivalent subcategories.** The
full subcategory of `D(X_affine, 𝒪)` on sheaves of modules whose cohomology is quasi-coherent is
equivalent to the one cut out by
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.qcohCohomologyProperty` on presheaves of
modules, by the restriction of
`AlgebraicGeometry.Scheme.affineChaoticDerivedSheafPresheafEquivalence`. -/
def Scheme.affineChaoticQcohCohomologyEquivalence :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O))).FullSubcategory ≌
      (Stacks.ModulesOnACategory.QuasiCoherentCohomology.qcohCohomologyProperty.{u}
        X.affineChaoticRingedSite).FullSubcategory :=
  haveI : (Stacks.ModulesOnACategory.QuasiCoherentCohomology.qcohCohomologyProperty.{u}
      X.affineChaoticRingedSite).IsClosedUnderIsomorphisms :=
    ⟨fun {_ _} e hK n ↦ by
      obtain ⟨_, hQC⟩ := hK n
      refine ⟨Presheaf.isSheaf_bot _, ?_⟩
      exact (inferInstance : (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          X.affineChaoticRingedSite.O)).IsClosedUnderIsomorphisms).of_iso
        (X.affineChaoticSheafPresheafEquivalence.inverse.mapIso
          ((DerivedCategory.homologyFunctor _ n).mapIso e)) hQC⟩
  X.affineChaoticDerivedSheafPresheafEquivalence.congrFullSubcategory
    (funext fun K ↦ propext (X.qcohCohomologyProperty_affineChaotic_iff K))

/-! ### The chain (1) ≃ (2) ≃ (3) ≃ (4) at the locally small model -/

/-- **The chain (1) ≃ (2) ≃ (3) ≃ (4) of [Stacks, Tag 0GZZ], at the locally small model of the
derived category.** `AlgebraicGeometry.Scheme.quasicoherentDerivedAffineChaoticEquivalence` is
proved at `CategoryTheory.HasDerivedCategory.standard`, because the second conclusion of
[Stacks, Tag 07A8] is; its source there is not the category
`Stacks.Duality.quasiCoherentDerivedCategory X` that the rest of the duality development and the
[Stacks, Tag 0A9E] statement use, which is at the locally small model with morphisms in
`Type u`. This restates it there, by
`StacksDraft.DerivedModel.derivedCategoryBModelEquiv` at both ends.

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): the chain
(1) = (2) ≃ (3) ≃ (4) for a scheme, at the locally small model of the derived category, with (4)
read as the image class of [Stacks, Tag 07A8]
-/
def Scheme.quasicoherentDerivedAffineChaoticEquivalenceLocallySmall :
    Stacks.Duality.quasiCoherentDerivedCategory X ≌
      (DerivedCategoryB.derivedCategoryB
        (Stacks.Cohomology.CompareTopologies.imageOfLE
          (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
            X.affineZariskiRingedSite.J)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)
          (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              X.affineZariskiRingedSite.O)))).FullSubcategory :=
  (StacksDraft.DerivedModel.derivedCategoryBModelEquiv
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (SheafOfModules.hasDerivedCategory _) (HasDerivedCategory.standard _)).trans
    (X.quasicoherentDerivedAffineChaoticEquivalenceOfIsQuasicoherent.trans
      (StacksDraft.DerivedModel.derivedCategoryBModelEquiv _
        (HasDerivedCategory.standard _) (SheafOfModules.hasDerivedCategory _)))

/-! ### One of the two inclusions of the remaining equality -/

/-- **A quasi-coherent module on the affine site of a scheme is cartesian.** For a quasi-coherent
`𝒪_X`-module `M'` and a morphism `f : U ⟶ V` of affine opens, the base-change comparison of the
restriction of `M'` to the affine site, read with the chaotic topology, is an isomorphism.

This is `isIso_restrictionBaseChange_of_isQuasicoherent` of
`Stacks.AlgebraicGeometry.CartesianQuasicoherent`, read on the affine site: restriction along
`AlgebraicGeometry.Scheme.affineOpensToOpens` is precomposition, so the base-change comparison of
the restricted module at `f` *is* that of `M'` at the inclusion `U ≤ V` of opens of `X`. -/
theorem Scheme.isIso_canonicalMap_affineChaotic_of_isQuasicoherent
    (M' : SheafOfModules.{u} X.ringCatSheaf)
    (hM' : SheafOfModules.isQuasicoherent X.ringCatSheaf M')
    {U V : X.affineOpens} (f : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap X.affineChaoticRingedSite
      ((_root_.SheafOfModules.ofLE
        (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
          X.affineZariskiRingedSite.J)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)).obj
        (X.affineOpensModuleRestriction.obj M')) f) := by
  have : M'.IsQuasicoherent := hM'
  have hle : (U : X.Opens) ≤ (V : X.Opens) := leOfHom f
  exact isIso_restrictionBaseChange_of_isQuasicoherent M' U.2 V.2 hle

/-- **One of the two inclusions of the remaining equality.** The image under `ε_*` of the
quasi-coherent modules on the affine Zariski site of a scheme consists of quasi-coherent modules
for the chaotic topology.

A quasi-coherent module on the affine Zariski site is the restriction of a quasi-coherent
`𝒪_X`-module, by
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction_iff` and
`AlgebraicGeometry.Scheme.isQuasicoherent_eq_isQuasicoherentOnSite_ringCatSheaf`; such a module is
cartesian on affine opens, by
`AlgebraicGeometry.Scheme.isIso_canonicalMap_affineChaotic_of_isQuasicoherent`; and on a chaotic
site cartesian means quasi-coherent, by [Stacks, Tag 0GZN],
`Stacks.SheafOfModules.isQuasicoherent_iff_canonicalMap_isIso`.

The reverse inclusion asks that a cartesian module for the chaotic topology be a Zariski sheaf,
hence in the image of `ε_*` at all; it is
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_le_imageOfLE_affineChaotic` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensChaoticQuasicoherentEquality.lean`. -/
theorem Scheme.imageOfLE_le_isQuasicoherentOnSite_affineChaotic :
    Stacks.Cohomology.CompareTopologies.imageOfLE
        (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
          X.affineZariskiRingedSite.J)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)
        (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)) ≤
      SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O) := by
  rintro N ⟨M, hM, ⟨eN⟩⟩
  have hiso : X.affineOpensModuleRestriction.obj
      (X.affineOpensModuleRestrictionEquivalence.inverse.obj M) ≅ M :=
    X.affineOpensModuleRestrictionEquivalence.counitIso.app M
  have hres : SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)
      (X.affineOpensModuleRestriction.obj
        (X.affineOpensModuleRestrictionEquivalence.inverse.obj M)) :=
    ObjectProperty.prop_of_iso _ hiso.symm hM
  have hM'q : SheafOfModules.isQuasicoherent X.ringCatSheaf
      (X.affineOpensModuleRestrictionEquivalence.inverse.obj M) :=
    X.isQuasicoherent_eq_isQuasicoherentOnSite_ringCatSheaf ▸
      (X.isQuasicoherentOnSite_affineOpensModuleRestriction_iff _).1 hres
  have hqc : ((Stacks.Cohomology.CompareTopologies.pushforward
      (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
        X.affineZariskiRingedSite.J)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)).obj
        (X.affineOpensModuleRestriction.obj
          (X.affineOpensModuleRestrictionEquivalence.inverse.obj M))).IsQuasicoherentOnSite :=
    (Stacks.SheafOfModules.isQuasicoherent_iff_canonicalMap_isIso X.affineChaoticRingedSite
      _ rfl).2 fun {_ _} f ↦
        X.isIso_canonicalMap_affineChaotic_of_isQuasicoherent _ hM'q f
  exact (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O)).prop_of_iso
    (((Stacks.Cohomology.CompareTopologies.pushforward _ _).mapIso hiso).trans eN) hqc

end AlgebraicGeometry

end
