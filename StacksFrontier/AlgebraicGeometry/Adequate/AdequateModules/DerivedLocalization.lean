module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightResolvingSubcategoryPlus
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Comparison

/-!
# The bounded below derived category of adequate modules on an affine scheme

A map of complexes of quasi-coherent `𝒪_S`-modules is a *universal quasi-isomorphism* when its
pullback along every morphism of schemes `T ⟶ S` is a quasi-isomorphism. Over an affine base
`U = Spec A` the bounded below derived category `D⁺(Adeq(𝒪))` is the localization of
`K⁺(QCoh(𝒪_U))` at the universal quasi-isomorphisms, which is [Stacks, Tag 06ZR].

## Main definitions

* `Stacks.Adequate.qcohPullback` — pullback of quasi-coherent `𝒪_S`-modules along a morphism of
  schemes, with values in all modules on the target.
* `Stacks.Adequate.universalQuasiIso` — the universal quasi-isomorphisms, as a class of
  morphisms of `K⁺(QCoh(𝒪_S))`.

## Main results

The general form of [Stacks, Tag 06ZR],
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq`, needs the
functor `u` of [Stacks, Tag 06VN], whose imports change the preadditive structure instance search
finds for the quasi-coherent modules (see below); it is stated in
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdequacy`.

## Implementation notes

A universal quasi-isomorphism is tested in all `𝒪_T`-modules rather than in the quasi-coherent
ones: the pullback of a quasi-coherent module is quasi-coherent ([Stacks, Tag 01BG]) and
quasi-coherence is an exact condition, so this is the condition of the source, and it needs no
abelian structure on `QCoh(𝒪_T)`.

The abelian structures of `QCoh(𝒪_U)` and of `Adeq(𝒪)` are hypotheses, and the preadditive
structure induced on a full subcategory by its ambient category is removed from instance search
for the statement, so that the one underlying those hypotheses is used throughout.

The bounded below derived category `D⁺(Adeq(𝒪))` is taken in the source's own sense, as the
localization of `K⁺(Adeq(𝒪))` at the quasi-isomorphisms; the statement holds for every model of
it, `CategoryTheory.Functor.isLocalization_mapHomotopyCategoryPlus_comp` being stated for an
arbitrary localization functor, in particular for Mathlib's `DerivedCategory.Plus.Qh`.

The mathematical content of the source's proof — the essential surjectivity and the full
faithfulness of the canonical functor out of the localization — is
`CategoryTheory.Functor.isLocalization_mapHomotopyCategoryPlus_comp`, proved for an arbitrary
fully faithful exact functor of abelian categories along which every object of the target admits
a monomorphism into an object of the image. Two inputs of the source are named as hypotheses:
that every adequate module admits a monomorphism into the associated module of a quasi-coherent
one, which is the implication (1) ⇒ (2) of [Stacks, Tag 06VK]; and the source's opening sentence
that `uφ` is a quasi-isomorphism exactly when `φ` is a universal quasi-isomorphism, which the
source reads off [Stacks, Tags 06VI and 06VM].

The first of the two is `Stacks.Adequate.BigSite.exists_mono_associatedModuleAdeq` in
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdequacy`, which also
carries the general statement and the one with it supplied; the adequacy of the associated
module that `u` needs to exist at all is
`Stacks.Adequate.BigSite.isAdequate_associatedModuleFunctor_obj`, which
`Stacks.Adequate.BigSite.associatedModuleAdeq` uses.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06VN](https://stacks.math.columbia.edu/tag/06VN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Adequate

/-! ### Universal quasi-isomorphisms -/

section UniversalQuasiIso

variable {S : Scheme.{u}}
  [Preadditive (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory]
  [(SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.Additive]

/-- Pullback of quasi-coherent `𝒪_S`-modules along a morphism of schemes `f : T ⟶ S`, read in
all `𝒪_T`-modules. -/
public noncomputable abbrev qcohPullback {T : Scheme.{u}} (f : T ⟶ S) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤ T.Modules :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙ Scheme.Modules.pullback f

/-- Pullback of quasi-coherent modules is additive, the inclusion of the quasi-coherent modules
and the pullback of all modules both being additive. -/
public noncomputable instance qcohPullback_additive {T : Scheme.{u}} (f : T ⟶ S) :
    (qcohPullback f).Additive where
  map_add := by
    intro X Y a b
    have h : (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map (a + b) =
        (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map a +
          (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map b := Functor.map_add _
    exact (congrArg (Scheme.Modules.pullback f).map h).trans
      (Scheme.Modules.pullback f).map_add

variable (S) in
/-- A morphism of bounded below complexes of quasi-coherent `𝒪_S`-modules is a **universal
quasi-isomorphism** when its pullback along every morphism of schemes `T ⟶ S` is a
quasi-isomorphism of complexes of `𝒪_T`-modules. -/
public noncomputable def universalQuasiIso :
    MorphismProperty
      (HomotopyCategory.Plus (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :=
  fun _ _ φ ↦ ∀ (T : Scheme.{u}) (f : T ⟶ S),
    HomotopyCategory.Plus.quasiIso T.Modules ((qcohPullback f).mapHomotopyCategoryPlus.map φ)

end UniversalQuasiIso

end Stacks.Adequate

end
