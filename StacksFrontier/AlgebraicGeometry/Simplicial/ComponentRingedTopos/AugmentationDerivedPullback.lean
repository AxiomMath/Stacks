module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Augmentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback of modules along a ringed augmentation

Let `S` be a simplicial-site situation, `a` an augmentation of `S` towards a site `(D, K)` and
`A` a ringed augmentation of Stacks 0D9D, with total morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)`. This module records the derived pullback
`La^* : D(O_D) ⥤ D(O)` of Stacks 06YY along it, and that the canonical comparison `La^* ⟶ a^*`
is invertible on the K-flat complexes with flat terms.

Nothing here is specific to the augmentation: the derived pullback exists along *every* morphism
of ringed topoi whose two topoi live at the site universe, by
`Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy`, whose two
inputs — Stacks 06YS and the exactness clause of Stacks 06YY at the K-flat complexes with flat
terms — hold for an arbitrary such morphism. What this module supplies is the two sheafification
facts for the *augmentation* site, which no other module in the development declares (the two for
the total site are the boilerplate every consumer repeats), and the resulting named functor.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.augmentationKFlat`: the K-flat
  complexes of `O_D`-modules with flat terms, the resolving class the derived pullback is
  computed by.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.derivedPullbackModules`:
  **`La^* : D(O_D) ⥤ D(O)`**, with its canonical comparison
  `.derivedPullbackModulesComparison`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation`
  `.hasLeftDerivedFunctor_pullbackOnHomotopy_totalRingedHom`: the derived pullback along the
  ringed augmentation exists, as an instance.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.hasResolutions_augmentationKFlat`:
  Stacks 06YS on the augmentation site.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation`
  `.isIso_derivedPullbackModulesComparison_app`: the computation assertion of Stacks 06YY —
  `La^*P = a^*P` for `P` K-flat with flat terms.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.augmentationKFlat_pullback`: Stacks
  0G7E along the ringed augmentation — the degreewise pullback of a K-flat complex with flat
  terms is again one.

## Implementation notes

**Why the sheafification facts are `local instance`s here.** Sheafification of
`AddCommGrpCat`-valued presheaves on the augmentation site, and the identification of the maps it
inverts with the locally bijective ones, are theorems in this development
(`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat`) rather than global
instances: making them global would change instance synthesis for every site in the library.
Every consumer therefore declares them locally, and this file is the first one to need them for
an augmentation site.

## References

* [Stacks Project, Section 85.10 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation.RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

/-- Sheafification of abelian presheaves on the augmentation site exists: the site's objects and
morphisms both lie in `Type u`. -/
local instance hasSheafifyAugmentation : HasSheafify K AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} K

/-- On the augmentation site the maps inverted by sheafification of abelian presheaves are
exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveAugmentation :
    K.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} K

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- The K-flat complexes of `O_D`-modules **with flat terms** on the augmentation ringed topos,
as a property of objects of the unbounded homotopy category. This is the class Stacks 06YS
resolves by and the class Stacks 0G7E is stable under. -/
abbrev augmentationKFlat :=
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
    (Y := A.augmentationRingedTopos)

/-- **Stacks 06YS on the augmentation ringed topos.** Every complex of `O_D`-modules receives a
quasi-isomorphism from a K-flat complex with flat terms. -/
theorem hasResolutions_augmentationKFlat
    (M : HomotopyCategory A.augmentationRingedTopos.Modules (ComplexShape.up ℤ)) :
    ∃ (P : HomotopyCategory A.augmentationRingedTopos.Modules (ComplexShape.up ℤ))
      (_ : A.augmentationKFlat P) (s : P ⟶ M),
      quasiIsoTarget (Y := A.augmentationRingedTopos) s := by
  obtain ⟨P, hP, s, hs⟩ :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
      (Y := A.augmentationRingedTopos) M
  exact ⟨P, hP, s, hs⟩

/-- **The derived pullback along the ringed augmentation exists.** Degreewise pullback of
complexes of modules followed by localization has an everywhere-defined left derived functor,
because the K-flat complexes with flat terms resolve every complex and their quasi-isomorphisms
are inverted. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_totalRingedHom :
    (pullbackOnHomotopy A.totalRingedHom).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := A.augmentationRingedTopos)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy A.totalRingedHom

/-- **Stacks 06YY for a ringed augmentation.** The derived pullback
`La^* : D(O_D) ⥤ D(O)` along the total morphism of ringed topoi of a ringed augmentation of
Stacks 0D9D.

This is `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback`, which carries the 06YY
registration, at the ringed augmentation; it is named only so that the statements below and
Stacks 0D7H (4) can refer to it. -/
noncomputable abbrev derivedPullbackModules :
    DerivedCategory A.augmentationRingedTopos.Modules ⥤
      DerivedCategory (S.totalRingedTopos A.O).Modules :=
  derivedPullback (X := S.totalRingedTopos A.O) (Y := A.augmentationRingedTopos)
    A.totalRingedHom

/-- The canonical comparison `La^* ⟶ a^*` from the derived pullback along the ringed
augmentation to degreewise pullback. -/
noncomputable abbrev derivedPullbackModulesComparison :
    DerivedCategory.Qh ⋙ A.derivedPullbackModules ⟶
      pullbackOnHomotopy (X := S.totalRingedTopos A.O) (Y := A.augmentationRingedTopos)
        A.totalRingedHom :=
  derivedPullbackComparison (X := S.totalRingedTopos A.O) (Y := A.augmentationRingedTopos)
    A.totalRingedHom

/-- **The computation assertion of Stacks 06YY for a ringed augmentation.** The canonical
comparison `La^*P ⟶ a^*P` is invertible at a K-flat complex with flat terms: the derived
pullback of such a complex is computed by degreewise pullback. -/
theorem isIso_derivedPullbackModulesComparison_app
    (P : HomotopyCategory A.augmentationRingedTopos.Modules (ComplexShape.up ℤ))
    (hP : A.augmentationKFlat P) :
    IsIso (A.derivedPullbackModulesComparison.app P) :=
  isIso_derivedPullbackComparison_app A.totalRingedHom (A.augmentationKFlat)
    A.hasResolutions_augmentationKFlat
    (pullbackInvertsQuasiIso_isKFlat A.totalRingedHom) P hP

/-- **Stacks 0G7E along a ringed augmentation.** Degreewise pullback along `a` carries a K-flat
complex of `O_D`-modules with flat terms to a K-flat complex of `O`-modules with flat terms. -/
theorem augmentationKFlat_pullback
    (P : HomotopyCategory A.augmentationRingedTopos.Modules (ComplexShape.up ℤ))
    (hP : A.augmentationKFlat P) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := S.totalRingedTopos A.O)
      (((A.totalRingedHom.toModulesHom.pullbackModules).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj P) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
    A.totalRingedHom P hP

end CategoryTheory.SimplicialSiteSituation.RingedAugmentation

end
