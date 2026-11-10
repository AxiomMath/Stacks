module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import StacksFrontier.CategoryTheory.Limits.PresentationOpposite
public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianGRing

/-!
# The spectrum of an ind-smooth algebra as an inverse limit of smooth affine schemes

Popescu's theorem is a statement about rings: it presents a ring map with suitable regularity as
a filtered colimit of smooth algebras.  This file transports such a presentation to schemes, so
that `Spec` of the colimit is exhibited as the *inverse* limit of the spectra of the stages,
each of which is affine and smooth over the base.

## Main definitions

* `AlgebraicGeometry.specUnderDiagram`: the cofiltered diagram of spectra attached to a diagram
  of algebras over a fixed base ring.
* `AlgebraicGeometry.specUnderStructureMap`: its structure morphisms to the spectrum of the
  base, as a natural transformation to a constant functor.
* `AlgebraicGeometry.specUnderLimitPresentation`: the limit presentation of `Spec` of the
  colimit object, obtained from a colimit presentation in the under category.

## Main results

* `AlgebraicGeometry.exists_limitPresentation_spec_of_ind`: for a property `P` of morphisms of
  schemes governed by a property `Q` of ring maps, an ind-`Q` algebra has a spectrum which is a
  cofiltered inverse limit of affine schemes whose structure morphisms to the base satisfy `P`.
* `AlgebraicGeometry.exists_limitPresentation_spec_of_indSmooth`: the case `P = `
  `AlgebraicGeometry.Smooth`, stated for `Stacks.Smoothing.IndSmooth`.
* `AlgebraicGeometry.exists_limitPresentation_spec_adicCompletion_of_isGRing`: for a G-ring `R`
  and an ideal `I`, `Spec (R^∧_I)` is a cofiltered inverse limit of affine schemes smooth
  over `Spec R`.
* `AlgebraicGeometry.exists_limitPresentation_spec_completedStalk`: the same for the completion
  of a local ring of a scheme at a point, which is the presentation of
  `Spec 𝒪^∧_{S,s}` as an inverse limit of smooth `Spec 𝒪_{S,s}`-schemes.
* `AlgebraicGeometry.exists_limitPresentation_spec_completedStalk_of_isAffineOpen`: the
  presentation of `Spec 𝒪^∧_{S,s}` as an inverse limit of smooth `S`-schemes, the base being
  `Spec Γ(S, U)` for an affine open `U ∋ s`.  This is the form with content about `S`: over
  `Spec 𝒪_{S,s}` the stages say nothing about `S`, because `Spec 𝒪_{S,s} ⟶ S` is not of finite
  type.

## Implementation notes

The one piece of plumbing the transport needs is that a colimit in `CategoryTheory.Under A` may
be computed after forgetting the structure map.  Mathlib has this: the instance
`CategoryTheory.Limits.instPreservesFilteredColimitsOfSizeUnderForget` in
`Mathlib/CategoryTheory/Limits/Preserves/Over.lean` gives it for filtered shapes, and
`CategoryTheory.Limits.CreatesConnected` in
`Mathlib/CategoryTheory/Limits/Constructions/Over/Connected.lean` gives it for merely connected
shapes.  Nothing here reproves it: the hypothesis is taken in the weakest form
`CategoryTheory.Limits.PreservesColimitsOfShape J (CategoryTheory.Under.forget A)`, which either
instance discharges.

## References

* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 0CB1](https://stacks.math.columbia.edu/tag/0CB1)
* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

variable {A : CommRingCat.{u}} {J : Type u} [SmallCategory J]

/-- The diagram of spectra attached to a diagram `F` of `A`-algebras: its value at `j` is the
spectrum of the underlying ring of `F.obj j`, and it is indexed by `Jᵒᵖ` because `Spec` is
contravariant. -/
noncomputable abbrev specUnderDiagram (F : J ⥤ Under A) : Jᵒᵖ ⥤ Scheme.{u} :=
  (F ⋙ Under.forget A).op ⋙ Scheme.Spec

/-- The structure morphisms `Spec (F.obj j).right ⟶ Spec A` of the spectra of a diagram `F` of
`A`-algebras, as a natural transformation to the constant functor at `Spec A`. -/
noncomputable def specUnderStructureMap (F : J ⥤ Under A) :
    specUnderDiagram F ⟶ (Functor.const Jᵒᵖ).obj (Spec A) where
  app j := Spec.map (F.obj j.unop).hom
  naturality i j f := by
    dsimp
    rw [Category.comp_id, ← Spec.map_comp]
    exact congrArg Spec.map (Under.w (F.map f.unop))

/-- The component of `specUnderStructureMap F` at `j` is the spectrum of the structure map of
`F.obj j.unop`. -/
@[simp]
lemma specUnderStructureMap_app (F : J ⥤ Under A) (j : Jᵒᵖ) :
    (specUnderStructureMap F).app j = Spec.map (F.obj j.unop).hom :=
  rfl

variable {X : Under A}

/-- **The spectrum of a colimit of `A`-algebras, as an inverse limit of their spectra.**  A
colimit presentation of an object `X` of `CategoryTheory.Under A` over an index category `J`
along which `CategoryTheory.Under.forget A` preserves colimits — in particular over any filtered
or merely connected `J` — presents `Spec X.right` as the limit of the spectra of the stages. -/
noncomputable def specUnderLimitPresentation [PreservesColimitsOfShape J (Under.forget A)]
    (pres : ColimitPresentation J X) : LimitPresentation Jᵒᵖ (Spec X.right) where
  diag := specUnderDiagram pres.diag
  π :=
    { app j := Spec.map (pres.leg j.unop).right
      naturality i j f := by
        dsimp
        rw [Category.id_comp, ← Spec.map_comp, ColimitPresentation.right_diag_map_comp_leg] }
  isLimit :=
    isLimitOfPreserves Scheme.Spec (isColimitOfPreserves (Under.forget A) pres.isColimit).op

/-- The diagram of `specUnderLimitPresentation pres` is the diagram of spectra of `pres.diag`.
-/
@[simp]
lemma specUnderLimitPresentation_diag [PreservesColimitsOfShape J (Under.forget A)]
    (pres : ColimitPresentation J X) :
    (specUnderLimitPresentation pres).diag = specUnderDiagram pres.diag :=
  rfl

/-- The leg of `specUnderLimitPresentation pres` at `j` is the spectrum of the colimit leg
`pres.leg j.unop`. -/
@[simp]
lemma specUnderLimitPresentation_π_app [PreservesColimitsOfShape J (Under.forget A)]
    (pres : ColimitPresentation J X) (j : Jᵒᵖ) :
    (specUnderLimitPresentation pres).π.app j = Spec.map (pres.leg j.unop).right :=
  rfl

/-- Every stage of the diagram of spectra is affine. -/
lemma isAffine_specUnderDiagram_obj (F : J ⥤ Under A) (j : Jᵒᵖ) :
    IsAffine ((specUnderDiagram F).obj j) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The legs of the limit cone are compatible with the structure morphisms to `Spec A`. -/
lemma specUnderLimitPresentation_π_comp_structureMap
    [PreservesColimitsOfShape J (Under.forget A)] (pres : ColimitPresentation J X) (j : Jᵒᵖ) :
    (specUnderLimitPresentation pres).π.app j ≫ (specUnderStructureMap pres.diag).app j =
      Spec.map X.hom := by
  change Spec.map (pres.leg j.unop).right ≫ Spec.map (pres.diag.obj j.unop).hom = Spec.map X.hom
  rw [← Spec.map_comp]
  exact congrArg Spec.map (Under.w (pres.leg j.unop))

/-- A property of morphisms of schemes which is governed by a property of ring maps holds for a
structure morphism of the diagram of spectra as soon as the corresponding ring map has it. -/
lemma prop_specUnderStructureMap_app (P : MorphismProperty Scheme.{u}) {Q}
    [HasRingHomProperty P Q] (F : J ⥤ Under A) (j : Jᵒᵖ) (h : Q (F.obj j.unop).hom.hom) :
    P ((specUnderStructureMap F).app j) :=
  (HasRingHomProperty.Spec_iff (P := P)).mpr h

/-- **The spectrum of an ind-`Q` algebra is a cofiltered inverse limit of affine schemes whose
structure morphisms satisfy `P`.**  Here `Q` is a property of ring maps and `P` the property of
morphisms of schemes it governs, in the sense of
`AlgebraicGeometry.HasRingHomProperty`. -/
theorem exists_limitPresentation_spec_of_ind (P : MorphismProperty Scheme.{u}) {Q}
    [HasRingHomProperty P Q] {A : CommRingCat.{u}} {X : Under A}
    (h : ObjectProperty.ind.{u} (fun Y : Under A ↦ Q Y.hom.hom) X) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (pres : LimitPresentation I (Spec X.right))
      (f : pres.diag ⟶ (Functor.const I).obj (Spec A)),
      (∀ i, IsAffine (pres.diag.obj i)) ∧ (∀ i, P (f.app i)) ∧
        (∀ i, pres.π.app i ≫ f.app i = Spec.map X.hom) := by
  obtain ⟨J, _, _, pres, hQ⟩ := h
  exact ⟨Jᵒᵖ, inferInstance, inferInstance, specUnderLimitPresentation pres,
    specUnderStructureMap pres.diag, isAffine_specUnderDiagram_obj pres.diag,
    fun j ↦ prop_specUnderStructureMap_app P pres.diag j (hQ j.unop),
    specUnderLimitPresentation_π_comp_structureMap pres⟩

/-- **The spectrum of an ind-smooth algebra is a cofiltered inverse limit of affine schemes
smooth over the base.**  This is the scheme-level form of the ring-level statement of Lemma
`07C3`: the colimit presentation by smooth algebras of `Stacks.Smoothing.IndSmooth` becomes a
presentation of `Spec B` as an inverse limit of smooth affine `Spec A`-schemes. -/
theorem exists_limitPresentation_spec_of_indSmooth (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (h : Stacks.Smoothing.IndSmooth A B) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (pres : LimitPresentation I (Spec (.of B)))
      (f : pres.diag ⟶ (Functor.const I).obj (Spec (.of A))),
      (∀ i, IsAffine (pres.diag.obj i)) ∧ (∀ i, Smooth (f.app i)) ∧
        (∀ i, pres.π.app i ≫ f.app i = Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  exists_limitPresentation_spec_of_ind (P := @Smooth) h

/-- **The spectrum of the adic completion of a G-ring is a cofiltered inverse limit of affine
schemes smooth over the ring.**  This is the scheme-level form of
`Stacks.Smoothing.indSmooth_adicCompletion_of_isGRing`, which is Popescu's theorem (Tag `07GC`)
applied to the completion map of a G-ring. -/
theorem exists_limitPresentation_spec_adicCompletion_of_isGRing {R : Type u} [CommRing R]
    (hG : IsGRing R) (I : Ideal R) :
    ∃ (K : Type u) (_ : SmallCategory K) (_ : IsCofiltered K)
      (pres : LimitPresentation K (Spec (.of (AdicCompletion I R))))
      (f : pres.diag ⟶ (Functor.const K).obj (Spec (.of R))),
      (∀ k, IsAffine (pres.diag.obj k)) ∧ (∀ k, Smooth (f.app k)) ∧
        (∀ k, pres.π.app k ≫ f.app k =
          Spec.map (CommRingCat.ofHom (algebraMap R (AdicCompletion I R)))) :=
  exists_limitPresentation_spec_of_indSmooth R (AdicCompletion I R)
    (Stacks.Smoothing.indSmooth_adicCompletion_of_isGRing hG I)

/-- **`Spec 𝒪^∧_{S,s}` is a cofiltered inverse limit of affine schemes smooth over
`Spec 𝒪_{S,s}`.**  The completion is taken at the maximal ideal of the local ring of `S` at `s`,
and the hypothesis is that this local ring is a G-ring — which holds, for instance, when `S` is
excellent. -/
theorem exists_limitPresentation_spec_completedStalk (S : Scheme.{u}) (s : S)
    (hG : IsGRing (S.presheaf.stalk s)) :
    ∃ (K : Type u) (_ : SmallCategory K) (_ : IsCofiltered K)
      (pres : LimitPresentation K
        (Spec (.of (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s)))))
      (f : pres.diag ⟶ (Functor.const K).obj (Spec (.of (S.presheaf.stalk s)))),
      (∀ k, IsAffine (pres.diag.obj k)) ∧ (∀ k, Smooth (f.app k)) ∧
        (∀ k, pres.π.app k ≫ f.app k = Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk s)
            (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))) :=
  exists_limitPresentation_spec_adicCompletion_of_isGRing hG _

/-- **`Spec 𝒪^∧_{S,s}` is a cofiltered inverse limit of affine schemes smooth over an affine
open neighbourhood of `s` in `S`.**  This is the presentation by smooth `S`-schemes: the base is
`Spec Γ(S, U)` for an affine open `U ∋ s`, so each stage is a smooth scheme over an open
subscheme of `S`, and the map `Spec 𝒪^∧_{S,s} ⟶ Spec Γ(S, U)` whose cone this is is the one
induced by the germ map `Γ(S, U) ⟶ 𝒪_{S,s}` followed by the completion map.

Over `Spec 𝒪_{S,s}` instead, as in
`AlgebraicGeometry.exists_limitPresentation_spec_completedStalk`, the stages carry no
information about `S`, because `Spec 𝒪_{S,s} ⟶ S` is not of finite type. -/
theorem exists_limitPresentation_spec_completedStalk_of_isAffineOpen {S : Scheme.{u}}
    {U : S.Opens} (hU : IsAffineOpen U) {s : S} (hs : s ∈ U) [IsNoetherianRing Γ(S, U)]
    (hG : IsGRing (S.presheaf.stalk s)) :
    ∃ (K : Type u) (_ : SmallCategory K) (_ : IsCofiltered K)
      (pres : LimitPresentation K (Spec (.of (AdicCompletion
        (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))))
      (f : pres.diag ⟶ (Functor.const K).obj (Spec Γ(S, U))),
      (∀ k, IsAffine (pres.diag.obj k)) ∧ (∀ k, Smooth (f.app k)) ∧
        (∀ k, pres.π.app k ≫ f.app k =
          Spec.map (S.presheaf.germ U s hs ≫ CommRingCat.ofHom
            (algebraMap (S.presheaf.stalk s) (AdicCompletion
              (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))) := by
  let : Algebra Γ(S, U) (S.presheaf.stalk s) := S.presheaf.algebra_section_stalk ⟨s, hs⟩
  have : IsLocalization (hU.primeIdealOf ⟨s, hs⟩).asIdeal.primeCompl (S.presheaf.stalk s) :=
    hU.isLocalization_stalk ⟨s, hs⟩
  have hind := Stacks.Smoothing.indSmooth_adicCompletion_maximalIdeal_of_isLocalization
    (A := Γ(S, U)) (R := S.presheaf.stalk s)
    (hU.primeIdealOf ⟨s, hs⟩).asIdeal.primeCompl hG
  -- `CommRingCat.ofHom (algebraMap Γ(S, U) 𝒪_{S,s})` is the germ map, so the composite
  -- structure map of `hind` is the one in the statement.
  exact exists_limitPresentation_spec_of_ind (P := @Smooth)
    (X := Under.mk (S.presheaf.germ U s hs ≫ CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) (AdicCompletion
        (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))) hind

end AlgebraicGeometry

end
