module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtaleAssociatedModulePicard
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent

/-!
# The Picard homomorphism of the associated module is an isomorphism

Let `S` be a scheme of a big étale site `B`.  The declaration
`AlgebraicGeometry.SmallEtale.associatedModulePicardHom` is the homomorphism of Picard groups of
Tag 01CX

`Pic(𝒪_S) ⟶ Pic(𝒪_{S_étale})`

induced by the associated-module functor `𝓕 ↦ 𝓕^a` of Stacks 03DU (4).  This file proves that it
is **bijective**, with no hypothesis on `S`, so that `Pic(𝒪_S) ≅ Pic(𝒪_{S_étale})`.  That is the
content of Descent, Proposition 03DX (2) at the level of Picard groups.

## The shape of the argument

Both halves are read off the associated-module adjunction
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction` rather than off the equivalence of
categories `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`: the unit and
the counit are isomorphisms at the modules in play, and that is all that is used.

* *Injectivity.*  An invertible `𝒪_S`-module `𝓛` is quasi-coherent, so the unit of the adjunction
  at `𝓛` is an isomorphism, `𝓛 ≅ (𝓛^a)|_{S_Zar}`
  (`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, Stacks 0GN7).  Two invertible modules
  with the same image class have isomorphic associated modules, hence isomorphic restrictions,
  hence are isomorphic; `Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff` turns that back into
  an equality of classes.
* *Surjectivity.*  An invertible `𝒪`-module `𝓐` on the small étale site is quasi-coherent on that
  site, so its Zariski restriction `𝓐|_{S_Zar}` is quasi-coherent
  (`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`) and the counit at `𝓐` is an
  isomorphism `(𝓐|_{S_Zar})^a ≅ 𝓐` (`AlgebraicGeometry.SmallEtale.isIso_counit`).  The class of
  `𝓐` is therefore the image of the class of `𝓐|_{S_Zar}` — once that restriction is known to be
  *invertible*, which is the reflection statement below.

## Reflection of invertibility

`AlgebraicGeometry.SmallEtale.isInvertible_restrictModule` is the one input the library did not
have: the Zariski restriction of an invertible `𝒪`-module on `S_étale` is invertible.  The generic
transport `Stacks.SheafOfModules.Picard.isInvertible_map_obj` cannot supply it, because the tensor
comparison of the restriction functor,
`AlgebraicGeometry.SmallEtale.restrictModuleTensorIso`, exists only at *quasi-coherent*
arguments — restriction is a right adjoint and is only laxly monoidal in general — while that
lemma asks for a comparison at all arguments.  What closes the gap is
`Stacks.SheafOfModules.Picard.isInvertible_map_obj_of_tensorIsoOn`, the same transport with the
tensor comparison asked for only on a full subcategory containing the invertible modules, and the
two statements that an invertible module *is* quasi-coherent, on each of the two sites.

## Main results

* `AlgebraicGeometry.SmallEtale.zariskiIsQuasicoherent_of_isInvertible`: an invertible
  `𝒪_S`-module is quasi-coherent on the small Zariski site, in the quasi-coherence predicate the
  adjunction is stated with.
* `AlgebraicGeometry.SmallEtale.isInvertible_restrictModule`: **the Zariski restriction of an
  invertible `𝒪`-module on `S_étale` is an invertible `𝒪_S`-module.**
* `AlgebraicGeometry.SmallEtale.injective_associatedModulePicardHom`,
  `AlgebraicGeometry.SmallEtale.surjective_associatedModulePicardHom` and
  `AlgebraicGeometry.SmallEtale.bijective_associatedModulePicardHom`.
* `AlgebraicGeometry.SmallEtale.associatedModulePicardAddEquiv`: **the isomorphism of abelian
  groups `Pic(𝒪_S) ≅ Pic(𝒪_{S_étale})`**, with no hypothesis, sending the class of `𝓛` to the
  class of `𝓛^a` by `AlgebraicGeometry.SmallEtale.associatedModulePicardAddEquiv_classOf`.

## Implementation notes

Rank one on the small étale site is the converse clause of Tag 0B8Q,
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'`, fed the local
ringedness of the small étale site of a scheme, Stacks 04HZ
(`AlgebraicGeometry.smallEtaleRingedSite_isLocallyRinged`); quasi-coherence then goes through
finite presentation, exactly as `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertible`
does for an algebraic space.  On the Zariski side the corresponding statement is the instance
`Stacks.SheafOfModules.isQuasicoherent_of_isInvertible` of the ringed space of `S`.

No monoidal structure on either category of modules is used, and no coherence condition is
assumed; see the discussion in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PicardTransport.lean`.

The three spellings of each of the two structure sheaves — `AlgebraicGeometry.RingedSite.ringSheaf`
of the two ringed sites, `AlgebraicGeometry.SmallEtale.structureSheaf`, and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of the presheaf of commutative rings —
agree by `rfl`, so nothing below has to be transported.

No `@[stacks]` attribute is claimed here.  Clause (2) of Stacks 03DX at `τ = étale` is registered
on `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`; this file is that
clause read on Picard groups, and the identification of first cohomology it feeds is registered in
`StacksFrontier/AlgebraicGeometry/Picard/SmallEtaleFirstCohomologyComparison.lean`.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04HZ](https://stacks.math.columbia.edu/tag/04HZ)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### An invertible module is quasi-coherent, on each of the two sites -/

/-- **An invertible `𝒪_S`-module is quasi-coherent**, in the predicate
`SheafOfModules.IsQuasicoherent` over `AlgebraicGeometry.Scheme.ringCatSheaf` that the
associated-module adjunction is stated with.  This is the instance
`Stacks.SheafOfModules.isQuasicoherent_of_isInvertible` of the ringed space of `S`, restated at
the sheaf condition `AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf` the Picard group of `S`
is packaged with; the two are the same proposition, the two sheaves of rings being equal. -/
theorem zariskiIsQuasicoherent_of_isInvertible (L : S.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.presheaf (zariskiStructureIsSheaf S) L) :
    SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) L :=
  have := hL
  Stacks.SheafOfModules.isQuasicoherent_of_isInvertible (X := S.toRingedSpace) L

/-! ### Reflection of invertibility by the associated module -/

/-- **The Zariski restriction of the unit object is the unit object.**  The associated module of
`𝒪_S` is `𝒪_{S_étale}` (`AlgebraicGeometry.SmallEtale.associatedModulePicardUnitIso`) and the unit
of the adjunction is an isomorphism at the quasi-coherent module `𝒪_S`, so

`(𝒪_{S_étale})|_{S_Zar} ≅ (𝒪_S^a)|_{S_Zar} ≅ 𝒪_S`. -/
def restrictModulePicardUnitIso :
    Stacks.SheafOfModules.Picard.UnitIso (commRingStructureSheaf B S hS).obj
      (structure_isSheaf B S hS) S.presheaf (zariskiStructureIsSheaf S)
      (restrictModule B S hS) :=
  (restrictModule B S hS).mapIso (associatedModulePicardUnitIso B S hS).symm ≪≫
    (@asIso _ _ _ _ _ (unitIsoOnQuasicoherent B S hS
      ⟨SheafOfModules.unit S.ringCatSheaf, inferInstance⟩)).symm

/-- **The Zariski restriction has an object-level tensor comparison on the quasi-coherent
modules**: this is `AlgebraicGeometry.SmallEtale.restrictModuleTensorIso` in the packaging of
`Stacks.SheafOfModules.Picard.isInvertible_map_obj_of_tensorIsoOn`.  The two tensor products it is
stated with are the two here by `rfl`, as `tensorSheafBifunctorZariski_obj` and
`tensorSheafBifunctorEtale_obj` record. -/
def restrictModuleTensorIsoOn :
    Stacks.SheafOfModules.Picard.TensorIsoOn (commRingStructureSheaf B S hS).obj
      (structure_isSheaf B S hS) S.presheaf (zariskiStructureIsSheaf S)
      (restrictModule B S hS) (fun M => M.IsQuasicoherentOnSite) := fun M N hM hN =>
  restrictModuleTensorIso B S hS M N hM hN

/-- **Invertibility is reflected by `𝓕 ↦ 𝓕^a`**: the Zariski restriction of an invertible
`𝒪`-module on the small étale site of `S` is an invertible `𝒪_S`-module, with no hypothesis.

`Stacks.SheafOfModules.Picard.isInvertible_map_obj_of_tensorIsoOn` at the restriction functor,
with the quasi-coherent modules on the small étale site as the subcategory on which its tensor
comparison lives. The invertible modules lie in it: by the converse clause of Tag 0B8Q,
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'`, fed the local
ringedness of the small étale site (Stacks 04HZ), they are finite locally free of rank one, hence
of finite presentation, hence quasi-coherent. -/
theorem isInvertible_restrictModule (M : SheafOfModules.{u} (structureSheaf B S hS))
    (hM : Stacks.SheafOfModules.IsInvertible (commRingStructureSheaf B S hS).obj
      (structure_isSheaf B S hS) M) :
    Stacks.SheafOfModules.IsInvertible S.presheaf (zariskiStructureIsSheaf S)
      ((restrictModule B S hS).obj M) :=
  Stacks.SheafOfModules.Picard.isInvertible_map_obj_of_tensorIsoOn
    (commRingStructureSheaf B S hS).obj (structure_isSheaf B S hS) S.presheaf
    (zariskiStructureIsSheaf S) (restrictModule B S hS)
    (P := fun M => M.IsQuasicoherentOnSite)
    (fun L hL =>
      have := hL
      have : L.IsFinitePresentationOnSite :=
        SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
          (RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible' (smallEtaleRingedSite B S hS)
            L (smallEtaleRingedSite_isLocallyRinged B S hS)).isFiniteLocallyFreeOnSite
      show L.IsQuasicoherentOnSite from inferInstance)
    (restrictModulePicardUnitIso B S hS)
    (restrictModuleTensorIsoOn B S hS) M hM

/-! ### The homomorphism of Picard groups is bijective -/

attribute [local instance] zariskiPicardAddCommGroup etalePicardAddCommGroup

/-- **The Picard homomorphism of `𝓕 ↦ 𝓕^a` is injective.**  Two invertible `𝒪_S`-modules whose
associated modules have the same class are isomorphic: their associated modules are isomorphic,
hence so are the Zariski restrictions of those, and each module is the restriction of its own
associated module because the unit of the adjunction is an isomorphism at a quasi-coherent
module. -/
theorem injective_associatedModulePicardHom :
    Function.Injective (associatedModulePicardHom B S hS) := by
  intro x y hxy
  obtain ⟨L, hL, rfl⟩ := Stacks.SheafOfModules.Picard.exists_classOf_eq _ _ x
  obtain ⟨N, hN, rfl⟩ := Stacks.SheafOfModules.Picard.exists_classOf_eq _ _ y
  rw [associatedModulePicardHom_classOf, associatedModulePicardHom_classOf] at hxy
  obtain ⟨e⟩ := (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ _ _ _ _).1 hxy
  refine (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ L N hL hN).2 ⟨?_⟩
  exact (@asIso _ _ _ _ _ (unitIsoOnQuasicoherent B S hS
      ⟨L, zariskiIsQuasicoherent_of_isInvertible S L hL⟩)) ≪≫
    (restrictModule B S hS).mapIso e ≪≫
    (@asIso _ _ _ _ _ (unitIsoOnQuasicoherent B S hS
      ⟨N, zariskiIsQuasicoherent_of_isInvertible S N hN⟩)).symm

/-- **The Picard homomorphism of `𝓕 ↦ 𝓕^a` is surjective.**  An invertible `𝒪`-module `𝓐` on the
small étale site is quasi-coherent on the site, so its Zariski restriction is quasi-coherent and
invertible and the counit of the adjunction exhibits `𝓐` as the associated module of it. -/
theorem surjective_associatedModulePicardHom :
    Function.Surjective (associatedModulePicardHom B S hS) := by
  intro y
  obtain ⟨A, hA, rfl⟩ := Stacks.SheafOfModules.Picard.exists_classOf_eq _ _ y
  have hAq : A.IsQuasicoherentOnSite := by
    have := hA
    have : A.IsFinitePresentationOnSite :=
      SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
        (RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible' (smallEtaleRingedSite B S hS)
          A (smallEtaleRingedSite_isLocallyRinged B S hS)).isFiniteLocallyFreeOnSite
    infer_instance
  have hFq : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj A) := isQuasicoherent_restrictModule B S hS A hAq
  refine ⟨Stacks.SheafOfModules.Picard.classOf S.presheaf (zariskiStructureIsSheaf S)
    ((restrictModule B S hS).obj A) (isInvertible_restrictModule B S hS A hA), ?_⟩
  refine (associatedModulePicardHom_classOf B S hS _ _).trans ?_
  exact (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ _ _ _ hA).2
    ⟨@asIso _ _ _ _ _ (isIso_counit B S hS A hAq hFq)⟩

/-- **The Picard homomorphism of `𝓕 ↦ 𝓕^a` is bijective**, with no hypothesis on `S`. -/
theorem bijective_associatedModulePicardHom :
    Function.Bijective (associatedModulePicardHom B S hS) :=
  ⟨injective_associatedModulePicardHom B S hS, surjective_associatedModulePicardHom B S hS⟩

/-- **`Pic(𝒪_S) ≅ Pic(𝒪_{S_étale})`**, with no hypothesis on `S`: the homomorphism induced by the
associated-module functor of Stacks 03DU (4) is an isomorphism of abelian groups.  Both groups are
`Stacks.SheafOfModules.Picard.PicardGroup`, the group Tag 040E produces. -/
def associatedModulePicardAddEquiv :
    Stacks.SheafOfModules.Picard.PicardGroup S.presheaf (zariskiStructureIsSheaf S) ≃+
      Stacks.SheafOfModules.Picard.PicardGroup (commRingStructureSheaf B S hS).obj
        (structure_isSheaf B S hS) :=
  AddEquiv.ofBijective (associatedModulePicardHom B S hS)
    (bijective_associatedModulePicardHom B S hS)

/-- **The isomorphism sends the class of `𝓛` to the class of `𝓛^a`.**  This fixes it, rather than
only asserting that some isomorphism exists. -/
theorem associatedModulePicardAddEquiv_classOf
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S)))
    (hL : Stacks.SheafOfModules.IsInvertible S.presheaf (zariskiStructureIsSheaf S) L) :
    associatedModulePicardAddEquiv B S hS
        (Stacks.SheafOfModules.Picard.classOf S.presheaf (zariskiStructureIsSheaf S) L hL) =
      Stacks.SheafOfModules.Picard.classOf (commRingStructureSheaf B S hS).obj
        (structure_isSheaf B S hS) ((associatedModule B S hS).obj L)
        (isInvertible_associatedModule B S hS L hL) :=
  associatedModulePicardHom_classOf B S hS L hL

end AlgebraicGeometry.SmallEtale

end
