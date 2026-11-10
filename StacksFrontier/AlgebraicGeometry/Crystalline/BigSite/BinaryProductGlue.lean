module

public import Mathlib.AlgebraicGeometry.Gluing
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerGluing

/-!
# Gluing objects of the big crystalline category along a locally directed diagram

Fix a global crystalline situation `(p, (S, I, γ), X)`.  This file glues a diagram of objects of
`CRIS(X/S)` into a single object.  The data glued over is a
`Crystalline.GlobalCrystallineSituation.ThickeningPresentation`: a diagram `J ⥤ Thickening S`
whose transition maps are open immersions on the thickened schemes and *induced* open immersions
on the ambient divided power schemes, and whose diagram of ambient schemes is locally directed in
the sense of `CategoryTheory.Functor.IsLocallyDirected`.

Both halves of the glued object are Mathlib colimits: the thickened scheme is `colimit` of the
thickened schemes of the charts, and the ambient scheme is `colimit` of the ambient schemes, which
carries a divided power structure because the diagram of ambient divided power schemes is a
`Crystalline.DividedPowerScheme.DividedPowerOpenPresentation` of that colimit.  The glued immersion
is the descent of the chart immersions.

Two things have to be checked.  First, that the glued immersion is again a thickening: each chart
square is cartesian (`isPullback_chart`, from the computation `preimage_opensRange_ι` of the
preimage of a chart), so being a closed immersion is Zariski-local on the chart cover, and
surjectivity is pointwise through the joint surjectivity of the charts.  Second, that the glued
divided power ideal is the defining ideal of the glued immersion.  On the images of the affine
opens of the charts this is `Mathlib`'s computation of the ideal of a closed immersion across a
cartesian square (`AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion`) together
with the corresponding property of the chart; those images form a basis of the glued ambient
scheme, and both sides of the identity may be checked on a basis.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.ThickeningPresentation` — a locally directed open
  presentation of an object of `CRIS(X/S)` by objects of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.ThickeningPresentation.ambient`,
  `.ambientDP` and `.sourceDiagram` — the diagrams of ambient schemes, of ambient divided power
  schemes, and of thickened schemes.
* `Crystalline.GlobalCrystallineSituation.ThickeningPresentation.ambientPresentation` — the induced
  divided power open presentation of the glued ambient scheme.
* `Crystalline.GlobalCrystallineSituation.ThickeningPresentation.gluedImmersion` — the glued
  immersion, and `.gluedThickening` the glued divided power thickening of schemes.
* **`Crystalline.GlobalCrystallineSituation.ThickeningPresentation.glued`** — the glued object of
  `CRIS(X/S)`, with `.gluedι` the chart morphisms.
* `Crystalline.GlobalCrystallineSituation.ThickeningPresentation.gluedHom` — the descent of a
  compatible family of morphisms out of the charts.

## Main results

* `Crystalline.GlobalCrystallineSituation.ThickeningPresentation.isPullback_chart` — each chart
  square is cartesian: the thickened scheme of a chart is the part of the glued thickened scheme
  lying over the chart.
* `Crystalline.GlobalCrystallineSituation.ThickeningPresentation.isClosedImmersion_gluedImmersion`
  and `.surjective_gluedImmersion` — the glued immersion is a thickening.
* `Crystalline.GlobalCrystallineSituation.ThickeningPresentation.gluedImmersion_ideal_eq_ker` — the
  glued divided power ideal is the defining ideal of the glued immersion.
* `Crystalline.GlobalCrystallineSituation.ThickeningPresentation.isInducedOpen_gluedι` and
  `.isOpenImmersion_gluedι_targetHom` — each chart is an induced open of the glued object, and
  `.gluedι_jointly_surjective` — the charts cover the glued ambient scheme.
* `Crystalline.GlobalCrystallineSituation.ThickeningPresentation.gluedι_gluedHom` and
  `.gluedHom_ext` — the descended morphism restricts to the given ones, and a morphism out of the
  glued object is determined by its restrictions to the charts.

## What is and is not proved

No tag attribute is placed in this file.  **This is not [Stacks, Tag 07I9]**: nothing here asserts
that any limit exists in `CRIS(X/S)`.  What is proved is the descent statement that
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/FibreProduct.lean` and
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/AffineSections.lean` both record as missing:
the
counterpart, for `Crystalline.SchemeThickening` and
`Crystalline.GlobalCrystallineSituation.Thickening`, of the divided power *scheme* level gluing
`Crystalline.DividedPowerScheme.DividedPowerOpenPresentation`.  It is infrastructure for
[Stacks, Tag 07I9], whose binary product half is to be glued from affine patches; the patches
themselves, and the verification that the glued object has the universal property of a product,
are not here.

The universal property proved here is only the descent of morphisms *out of* the glued object
(`gluedHom`, `gluedι_gluedHom`, `gluedHom_ext`), which is what the glued object being a colimit of
the charts amounts to.  Nothing is claimed about morphisms *into* it.

## References

* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07I4](https://stacks.math.columbia.edu/tag/07I4)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
open Stacks.Thickenings

universe u

namespace Crystalline.GlobalCrystallineSituation

attribute [local implicit_reducible] DividedPowerScheme.dividedPowerSchemeForget
  DividedPowerScheme.DividedPowerOpenPresentation.ideal
  DividedPowerScheme.DividedPowerOpenPresentation.gluedMap
  DividedPowerScheme.DividedPowerOpenPresentation.glued
  DividedPowerScheme.DividedPowerOpenPresentation.gluedι

/-- Restriction to a smaller open commutes with the action of a morphism on sections. -/
private theorem app_map_comm {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U)
    (h' : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) :
    Y.presheaf.map (homOfLE h).op ≫ f.app V = f.app U ≫ X.presheaf.map (homOfLE h').op := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- `Crystalline.GlobalCrystallineSituation.app_map_comm`, read on a section. -/
private theorem app_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U)
    (h' : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (f.app V).hom ((Y.presheaf.map (homOfLE h).op).hom x) =
      (X.presheaf.map (homOfLE h').op).hom ((f.app U).hom x) := by
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using
    congrArg (fun k : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ V) ↦ k.hom x) (app_map_comm f h h')

/-- Two ideals with the same image under a ring equivalence are equal. -/
private theorem ideal_eq_of_map_eq {R T : Type*} [CommRing R] [CommRing T] (e : R ≃+* T)
    {I K : Ideal R} (h : I.map (e : R →+* T) = K.map (e : R →+* T)) : I = K := by
  have key (A : Ideal R) : (A.map (e : R →+* T)).map (e.symm : T →+* R) = A := by
    have he : (e.symm : T →+* R).comp (e : R →+* T) = RingHom.id R :=
      RingHom.ext fun x ↦ e.symm_apply_apply x
    rw [Ideal.map_map, he, Ideal.map_id]
  rw [← key I, ← key K, h]

/-- **A locally directed open presentation of an object of `CRIS(X/S)` by objects of
`CRIS(X/S)`.**  The transition maps are open immersions on the thickened schemes and induced open
immersions on the ambient divided power schemes, and the diagram of ambient schemes is locally
directed, so that it may be glued by Mathlib's colimit construction for locally directed diagrams
of open immersions. -/
structure ThickeningPresentation (S : GlobalCrystallineSituation.{u}) (J : Type u)
    [Category.{u} J] where
  /-- The diagram of charts. -/
  functor : J ⥤ Thickening S
  /-- Every transition map is an open immersion on ambient schemes, with induced divided power
  ideal. -/
  induced {i j : J} (h : i ⟶ j) :
    Crystalline.DividedPowerScheme.IsInducedOpen (functor.map h).targetHom
  /-- Every transition map is an open immersion on thickened schemes. -/
  isOpenImmersion_sourceHom {i j : J} (h : i ⟶ j) : IsOpenImmersion (functor.map h).sourceHom
  /-- The diagram of ambient schemes is locally directed. -/
  directed {i j k : J} (fi : i ⟶ k) (fj : j ⟶ k)
      (xi : (functor.obj i).thickening.target.scheme)
      (xj : (functor.obj j).thickening.target.scheme)
      (h : (functor.map fi).targetHom.hom xi = (functor.map fj).targetHom.hom xj) :
    ∃ (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : (functor.obj l).thickening.target.scheme),
      (functor.map fli).targetHom.hom x = xi ∧ (functor.map flj).targetHom.hom x = xj

namespace ThickeningPresentation

variable {S : GlobalCrystallineSituation.{u}} {J : Type u} [Category.{u} J]
  (P : ThickeningPresentation S J)

/-- The diagram of ambient divided power schemes of a presentation. -/
@[implicit_reducible]
def ambientDP : J ⥤ DividedPowerScheme.{u} where
  obj i := (P.functor.obj i).thickening.target
  map h := (P.functor.map h).targetHom
  map_id i := by
    rw [P.functor.map_id]
    exact Thickening.id_targetHom _
  map_comp f g := by
    rw [P.functor.map_comp]
    exact Thickening.comp_targetHom _ _

/-- The diagram of ambient schemes of a presentation. -/
@[implicit_reducible]
def ambient : J ⥤ Scheme.{u} :=
  P.ambientDP ⋙ DividedPowerScheme.dividedPowerSchemeForget

/-- The diagram of thickened schemes of a presentation. -/
@[implicit_reducible]
def sourceDiagram : J ⥤ Scheme.{u} where
  obj i := (P.functor.obj i).thickening.source
  map h := (P.functor.map h).sourceHom
  map_id i := by
    rw [P.functor.map_id]
    exact Thickening.id_sourceHom _
  map_comp f g := by
    rw [P.functor.map_comp]
    exact Thickening.comp_sourceHom _ _

/-- The ambient scheme of a chart. -/
theorem ambient_obj (i : J) :
    P.ambient.obj i = (P.functor.obj i).thickening.target.scheme := rfl

/-- A transition map of the diagram of ambient schemes. -/
theorem ambient_map {i j : J} (h : i ⟶ j) :
    P.ambient.map h = (P.functor.map h).targetHom.hom := rfl

/-- The thickened scheme of a chart. -/
theorem sourceDiagram_obj (i : J) :
    P.sourceDiagram.obj i = (P.functor.obj i).thickening.source := rfl

/-- A transition map of the diagram of thickened schemes. -/
theorem sourceDiagram_map {i j : J} (h : i ⟶ j) :
    P.sourceDiagram.map h = (P.functor.map h).sourceHom := rfl

/-- The transition maps of the diagram of ambient schemes are open immersions. -/
instance isOpenImmersion_ambient_map :
    ∀ {i j : J} (h : i ⟶ j), IsOpenImmersion (P.ambient.map h) :=
  fun h ↦ (P.induced h).isOpenImmersion

/-- The transition maps of the diagram of thickened schemes are open immersions. -/
instance isOpenImmersion_sourceDiagram_map :
    ∀ {i j : J} (h : i ⟶ j), IsOpenImmersion (P.sourceDiagram.map h) :=
  fun h ↦ P.isOpenImmersion_sourceHom h

/-- A transition map of a presentation is compatible with the immersions of its charts. -/
theorem immersion_comm {i j : J} (h : i ⟶ j) (y : (P.functor.obj i).thickening.source) :
    (P.functor.obj j).thickening.immersion (P.sourceDiagram.map h y) =
      P.ambient.map h ((P.functor.obj i).thickening.immersion y) := by
  have e : (P.functor.obj i).thickening.immersion ≫ P.ambient.map h =
      P.sourceDiagram.map h ≫ (P.functor.obj j).thickening.immersion :=
    (P.functor.map h).immersion_naturality
  rw [← Scheme.Hom.comp_apply, ← e, Scheme.Hom.comp_apply]

/-- A point of a chart is determined by the image of its immersion under a transition map. -/
private theorem sourceDiagram_map_eq_of_immersion {i j : J} (h : i ⟶ j)
    (u : (P.functor.obj i).thickening.source) (y : (P.functor.obj j).thickening.source)
    (hy : P.ambient.map h ((P.functor.obj i).thickening.immersion u) =
      (P.functor.obj j).thickening.immersion y) :
    P.sourceDiagram.map h u = y :=
  (P.functor.obj j).thickening.immersion.isClosedEmbedding.injective
    ((P.immersion_comm h u).trans hy)

/-- The diagram of ambient schemes of a presentation is locally directed. -/
instance isLocallyDirected_ambient : (P.ambient ⋙ Scheme.forget).IsLocallyDirected :=
  ⟨fun fi fj xi xj h ↦ P.directed fi fj xi xj h⟩

/-- **The diagram of thickened schemes of a presentation is locally directed.**  A thickening is
surjective and injective on points, so the condition transports from the diagram of ambient
schemes. -/
instance isLocallyDirected_sourceDiagram :
    (P.sourceDiagram ⋙ Scheme.forget).IsLocallyDirected := by
  refine ⟨fun {i j k} fi fj yi yj h ↦ ?_⟩
  have h' : P.sourceDiagram.map fi yi = P.sourceDiagram.map fj yj := h
  have hij : P.ambient.map fi ((P.functor.obj i).thickening.immersion yi) =
      P.ambient.map fj ((P.functor.obj j).thickening.immersion yj) :=
    (P.immersion_comm fi yi).symm.trans
      ((congrArg (fun z ↦ (P.functor.obj k).thickening.immersion z) h').trans
        (P.immersion_comm fj yj))
  obtain ⟨l, fli, flj, x, hxi, hxj⟩ := P.directed fi fj
    ((P.functor.obj i).thickening.immersion yi) ((P.functor.obj j).thickening.immersion yj) hij
  obtain ⟨y, hy⟩ := (P.functor.obj l).thickening.isThickening.2 x
  exact ⟨l, fli, flj, y, P.sourceDiagram_map_eq_of_immersion fli y yi (by rwa [hy]),
    P.sourceDiagram_map_eq_of_immersion flj y yj (by rwa [hy])⟩

section Thin

variable [Quiver.IsThin J]

/-- **The divided power open presentation of the glued ambient scheme.**  The colimit of the
diagram of ambient schemes is presented by the ambient divided power schemes of the charts. -/
@[implicit_reducible]
def ambientPresentation :
    DividedPowerScheme.DividedPowerOpenPresentation J (colimit P.ambient) where
  functor := P.ambientDP
  ι := (colimit.cocone P.ambient).ι
  isOpen i := inferInstanceAs (IsOpenImmersion (colimit.ι P.ambient i))
  surjective x := Scheme.IsLocallyDirected.ι_jointly_surjective P.ambient x
  induced h := P.induced h
  directed _ _ h := (Scheme.IsLocallyDirected.ι_eq_ι_iff P.ambient).mp h

/-- The chart inclusions of the glued ambient scheme are the colimit inclusions. -/
theorem ambientPresentation_ι_app (i : J) :
    P.ambientPresentation.ι.app i = colimit.ι P.ambient i := rfl

/-- **The glued ambient divided power scheme.** -/
abbrev gluedTarget : DividedPowerScheme.{u} := P.ambientPresentation.glued

/-- The cocone of the chart immersions over the diagram of thickened schemes. -/
@[implicit_reducible]
def immersionCocone : Cocone P.sourceDiagram where
  pt := colimit P.ambient
  ι :=
    { app i := (P.functor.obj i).thickening.immersion ≫ colimit.ι P.ambient i
      naturality {i j} h := by
        have e : (P.functor.obj i).thickening.immersion ≫ P.ambient.map h =
            P.sourceDiagram.map h ≫ (P.functor.obj j).thickening.immersion :=
          (P.functor.map h).immersion_naturality
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        rw [← Category.assoc, ← e, Category.assoc, colimit.w] }

/-- **The glued immersion**: the descent of the chart immersions to the colimit of the thickened
schemes. -/
@[implicit_reducible]
def gluedImmersion : colimit P.sourceDiagram ⟶ colimit P.ambient :=
  colimit.desc P.sourceDiagram P.immersionCocone

/-- The glued immersion restricts to the immersion of each chart. -/
@[reassoc]
theorem ι_gluedImmersion (i : J) :
    colimit.ι P.sourceDiagram i ≫ P.gluedImmersion =
      (P.functor.obj i).thickening.immersion ≫ colimit.ι P.ambient i :=
  colimit.ι_desc P.immersionCocone i

/-- The glued immersion, read on a point of a chart. -/
theorem gluedImmersion_ι_apply (i : J) (y : (P.functor.obj i).thickening.source) :
    P.gluedImmersion (colimit.ι P.sourceDiagram i y) =
      colimit.ι P.ambient i ((P.functor.obj i).thickening.immersion y) := by
  rw [← Scheme.Hom.comp_apply, P.ι_gluedImmersion i, Scheme.Hom.comp_apply]

/-- **The part of the glued thickened scheme lying over a chart is the thickened scheme of that
chart.**  A point of the glued thickened scheme lying over the chart `i` comes from a chart `j`,
and local directedness refines the two to a common chart `k`, over which the point lifts through
the surjective immersion of `k`. -/
theorem preimage_opensRange_ι (i : J) :
    P.gluedImmersion ⁻¹ᵁ (colimit.ι P.ambient i).opensRange =
      (colimit.ι P.sourceDiagram i).opensRange := by
  ext z
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨j, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective P.sourceDiagram z
    have hz : colimit.ι P.ambient j ((P.functor.obj j).thickening.immersion y) =
        colimit.ι P.ambient i w :=
      (P.gluedImmersion_ι_apply j y).symm.trans hw.symm
    obtain ⟨k, fj, fi, v, hvj, hvi⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff P.ambient).mp hz
    obtain ⟨u, hu⟩ := (P.functor.obj k).thickening.isThickening.2 v
    have hkj := P.sourceDiagram_map_eq_of_immersion fj u y (by rwa [hu])
    refine ⟨P.sourceDiagram.map fi u, ?_⟩
    rw [← Scheme.Hom.comp_apply, colimit.w P.sourceDiagram fi, ← hkj, ← Scheme.Hom.comp_apply,
      colimit.w P.sourceDiagram fj]
  · rintro ⟨y, rfl⟩
    exact ⟨_, (P.gluedImmersion_ι_apply i y).symm⟩

/-- **Each chart square is cartesian.**  The thickened scheme of a chart is the fibre product of
the glued thickened scheme with the ambient scheme of the chart, by
`Crystalline.GlobalCrystallineSituation.ThickeningPresentation.preimage_opensRange_ι`. -/
theorem isPullback_chart (i : J) :
    IsPullback (P.functor.obj i).thickening.immersion (colimit.ι P.sourceDiagram i)
      (colimit.ι P.ambient i) P.gluedImmersion :=
  IsOpenImmersion.isPullback _ _ _ _ (P.ι_gluedImmersion i) (P.preimage_opensRange_ι i)

/-- **Over a chart, the glued immersion is a closed immersion**: it is the immersion of that
chart, up to the isomorphism coming from the cartesian chart square. -/
theorem isClosedImmersion_pullbackHom (i : J) :
    IsClosedImmersion
      ((Scheme.IsLocallyDirected.openCover P.ambient).pullbackHom P.gluedImmersion i) := by
  have h1 : (P.isPullback_chart i).flip.isoPullback.hom ≫
      (Scheme.IsLocallyDirected.openCover P.ambient).pullbackHom P.gluedImmersion i =
      (P.functor.obj i).thickening.immersion :=
    (P.isPullback_chart i).flip.isoPullback_hom_snd
  refine (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (P.isPullback_chart i).flip.isoPullback.hom _).mp ?_
  rw [h1]
  exact (P.functor.obj i).thickening.isThickening.1

/-- **The glued immersion is a closed immersion.**  Being a closed immersion is Zariski-local on
the target, and over each chart the glued immersion is the immersion of that chart by
`Crystalline.GlobalCrystallineSituation.ThickeningPresentation.isPullback_chart`. -/
theorem isClosedImmersion_gluedImmersion : IsClosedImmersion P.gluedImmersion :=
  IsZariskiLocalAtTarget.of_openCover (Scheme.IsLocallyDirected.openCover P.ambient)
    fun i ↦ P.isClosedImmersion_pullbackHom i

/-- **The glued immersion is surjective.**  The charts cover the glued ambient scheme and each
chart immersion is surjective. -/
theorem surjective_gluedImmersion : Function.Surjective P.gluedImmersion := by
  intro x
  obtain ⟨i, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective P.ambient x
  obtain ⟨z, hz⟩ := (P.functor.obj i).thickening.isThickening.2 y
  exact ⟨colimit.ι P.sourceDiagram i z, by rw [P.gluedImmersion_ι_apply i z, hz]⟩

/-- **The glued immersion is a thickening.** -/
theorem isThickening_gluedImmersion : IsThickening P.gluedImmersion :=
  ⟨P.isClosedImmersion_gluedImmersion, P.surjective_gluedImmersion⟩

/-- **Over the image of an affine open of a chart, the glued divided power ideal is the defining
ideal of the glued immersion.**  The ideal of the glued immersion over that image is computed from
the cartesian chart square, and comes out as the divided power ideal of the chart transported
along the identification of sections; the glued divided power ideal does the same, by
`Crystalline.DividedPowerScheme.DividedPowerOpenPresentation.ideal_map_appIso`. -/
theorem ker_ideal_basisOpen (i : J)
    (W : (P.functor.obj i).thickening.target.scheme.affineOpens) :
    P.gluedImmersion.ker.ideal ⟨P.ambientPresentation.basisOpen ⟨i, W⟩,
        W.2.image_of_isOpenImmersion (colimit.ι P.ambient i)⟩ =
      P.ambientPresentation.ideal.obj (op (P.ambientPresentation.basisOpen ⟨i, W⟩)) := by
  have := P.isClosedImmersion_gluedImmersion
  refine ideal_eq_of_map_eq
    ((colimit.ι P.ambient i).appIso W.1).commRingCatIsoToRingEquiv ?_
  have h1 : (P.functor.obj i).thickening.immersion.ker.ideal W =
      (P.gluedImmersion.ker.ideal ⟨P.ambientPresentation.basisOpen ⟨i, W⟩,
          W.2.image_of_isOpenImmersion (colimit.ι P.ambient i)⟩).comap
        ((colimit.ι P.ambient i).appIso W.1).inv.hom :=
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion P.gluedImmersion
      (P.functor.obj i).thickening.immersion (colimit.ι P.sourceDiagram i)
      (colimit.ι P.ambient i) (P.isPullback_chart i) W
  have e1 : (P.gluedImmersion.ker.ideal ⟨P.ambientPresentation.basisOpen ⟨i, W⟩,
        W.2.image_of_isOpenImmersion (colimit.ι P.ambient i)⟩).map
        ((colimit.ι P.ambient i).appIso W.1).hom.hom =
      Crystalline.sectionIdeal (P.functor.obj i).thickening.target.scheme.sheaf
        (P.functor.obj i).thickening.target.ideal (op (W : _)) := by
    rw [DividedPowerScheme.map_hom_eq_comap_inv, ← h1,
      ← (P.functor.obj i).thickening.ideal_eq_ker W]
  exact e1.trans (P.ambientPresentation.ideal_map_appIso i W).symm

/-- **A section of the glued ambient scheme over an affine open lies in the defining ideal of the
glued immersion exactly when the glued immersion kills it.** -/
theorem mem_ker_ideal_iff (V : (colimit P.ambient).affineOpens)
    (y : Γ(colimit P.ambient, (V : (colimit P.ambient).Opens))) :
    y ∈ P.gluedImmersion.ker.ideal V ↔ (P.gluedImmersion.app (V : _)).hom y = 0 := by
  have := P.isClosedImmersion_gluedImmersion
  rw [Scheme.Hom.ker_apply]
  exact RingHom.mem_ker

/-- **Over the image of an affine open of a chart, a section lies in the glued divided power ideal
exactly when the glued immersion kills it.** -/
theorem mem_ideal_basisOpen_iff (a : P.ambientPresentation.basisIndex)
    (y : Γ(colimit P.ambient, P.ambientPresentation.basisOpen a)) :
    y ∈ P.ambientPresentation.ideal.obj (op (P.ambientPresentation.basisOpen a)) ↔
      (P.gluedImmersion.app (P.ambientPresentation.basisOpen a)).hom y = 0 := by
  have h := P.mem_ker_ideal_iff ⟨P.ambientPresentation.basisOpen ⟨a.1, a.2⟩,
    a.2.2.image_of_isOpenImmersion (colimit.ι P.ambient a.1)⟩ y
  rwa [P.ker_ideal_basisOpen a.1 a.2] at h

/-- **The glued divided power ideal is the defining ideal of the glued immersion.**  The images of
the affine opens of the charts form a basis of the glued ambient scheme, membership in the glued
ideal may be checked on that basis
(`Crystalline.DividedPowerScheme.mem_ideal_basis`), and a section of the glued thickened scheme
vanishes as soon as it vanishes over each of those opens. -/
theorem gluedImmersion_ideal_eq_ker (V : (colimit P.ambient).affineOpens) :
    P.ambientPresentation.ideal.obj (op (V : (colimit P.ambient).Opens)) =
      P.gluedImmersion.ker.ideal V := by
  have hbasis := fun x ↦ DividedPowerScheme.mem_ideal_basis (colimit P.ambient)
    P.ambientPresentation.ideal P.ambientPresentation.basisOpen P.ambientPresentation.isBasis
    (U := (V : (colimit P.ambient).Opens)) x
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · refine (P.mem_ker_ideal_iff V x).mpr ?_
    refine TopCat.Presheaf.IsSheaf.section_ext (colimit P.sourceDiagram).sheaf.property
      fun z hz ↦ ?_
    obtain ⟨O, ⟨a, rfl⟩, hzO, hOV⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.ambientPresentation.isBasis
        (show P.gluedImmersion z ∈ (V : (colimit P.ambient).Opens) from hz)
    refine ⟨P.gluedImmersion ⁻¹ᵁ P.ambientPresentation.basisOpen a,
      fun y hy ↦ hOV hy, hzO, ?_⟩
    exact ((app_map_apply P.gluedImmersion hOV (fun y hy ↦ hOV hy) x).symm.trans
      ((P.mem_ideal_basisOpen_iff a _).mp ((hbasis x).mp hx a hOV))).trans (map_zero _).symm
  · refine (hbasis x).mpr fun a ha ↦ (P.mem_ideal_basisOpen_iff a _).mpr ?_
    rw [app_map_apply P.gluedImmersion ha (fun y hy ↦ ha hy) x, (P.mem_ker_ideal_iff V x).mp hx,
      map_zero]

/-- **The glued divided power thickening of schemes.** -/
@[implicit_reducible]
def gluedThickening : SchemeThickening.{u} where
  source := colimit P.sourceDiagram
  target := P.gluedTarget
  immersion := P.gluedImmersion
  isThickening := P.isThickening_gluedImmersion
  ideal_eq_ker := P.gluedImmersion_ideal_eq_ker

/-- The cocone of the structure morphisms of the charts to the divided power base. -/
@[implicit_reducible]
def baseCocone : Cocone P.ambient where
  pt := S.S.scheme
  ι :=
    { app i := (P.functor.obj i).toBase.hom
      naturality {i j} h := by
        have e : ((P.functor.map h).targetHom ≫ (P.functor.obj j).toBase).hom =
            (P.functor.obj i).toBase.hom :=
          congrArg DividedPowerScheme.Hom.hom (P.functor.map h).base_naturality
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact e }

/-- The cocone of the structure morphisms of the charts to `X`. -/
@[implicit_reducible]
def toXCocone : Cocone P.sourceDiagram where
  pt := S.X
  ι :=
    { app i := (P.functor.obj i).toX
      naturality {i j} h := by
        have e : (P.functor.map h).sourceHom ≫ (P.functor.obj j).toX =
            (P.functor.obj i).toX := (P.functor.map h).toX_naturality
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact e }

/-- The structure morphism of the glued object to the divided power base, on ambient schemes. -/
@[implicit_reducible]
def gluedToBaseHom : colimit P.ambient ⟶ S.S.scheme := colimit.desc P.ambient P.baseCocone

/-- The structure morphism of the glued object to the divided power base, on ambient schemes,
restricts to that of each chart. -/
@[reassoc]
theorem ι_gluedToBaseHom (i : J) :
    colimit.ι P.ambient i ≫ P.gluedToBaseHom = (P.functor.obj i).toBase.hom :=
  colimit.ι_desc P.baseCocone i

/-- **The structure morphism of the glued object to the divided power base.**  Compatibility with
the divided powers is checked chart by chart, by
`Crystalline.DividedPowerScheme.DividedPowerOpenPresentation.gluedMap`. -/
@[implicit_reducible]
def gluedToBase : P.gluedTarget ⟶ S.S :=
  P.ambientPresentation.gluedMap S.S P.gluedToBaseHom (fun i ↦ (P.functor.obj i).toBase)
    (fun i ↦ P.ι_gluedToBaseHom i)

/-- The structure morphism of the glued object to the divided power base has the expected
underlying morphism of schemes. -/
theorem gluedToBase_hom : P.gluedToBase.hom = P.gluedToBaseHom := rfl

/-- The structure morphism of the glued object to the divided power base restricts to that of each
chart. -/
theorem gluedι_gluedToBase (i : J) :
    P.ambientPresentation.gluedι i ≫ P.gluedToBase = (P.functor.obj i).toBase :=
  DividedPowerScheme.Hom.ext (P.ι_gluedToBaseHom i)

/-- **The structure morphism of the glued object to `X`.** -/
@[implicit_reducible]
def gluedToX : colimit P.sourceDiagram ⟶ S.X := colimit.desc P.sourceDiagram P.toXCocone

/-- The structure morphism of the glued object to `X` restricts to that of each chart. -/
@[reassoc]
theorem ι_gluedToX (i : J) :
    colimit.ι P.sourceDiagram i ≫ P.gluedToX = (P.functor.obj i).toX :=
  colimit.ι_desc P.toXCocone i

/-- **The object of `CRIS(X/S)` glued from a locally directed presentation.** -/
@[implicit_reducible]
def glued : Thickening S where
  thickening := P.gluedThickening
  toBase := P.gluedToBase
  toX := P.gluedToX
  over_base := by
    change P.gluedImmersion ≫ P.gluedToBase.hom = P.gluedToX ≫ sourceToBase S
    rw [P.gluedToBase_hom]
    refine colimit.hom_ext fun i ↦ ?_
    rw [← Category.assoc, ← Category.assoc, P.ι_gluedImmersion i, P.ι_gluedToX i,
      Category.assoc, P.ι_gluedToBaseHom i]
    exact (P.functor.obj i).over_base

/-- **The chart morphisms into the glued object.** -/
@[implicit_reducible]
def gluedι (i : J) : P.functor.obj i ⟶ P.glued where
  sourceHom := colimit.ι P.sourceDiagram i
  targetHom := P.ambientPresentation.gluedι i
  immersion_naturality := (P.ι_gluedImmersion i).symm
  base_naturality := P.gluedι_gluedToBase i
  toX_naturality := P.ι_gluedToX i

/-- The chart morphisms are natural in the index. -/
theorem map_gluedι {i j : J} (h : i ⟶ j) : P.functor.map h ≫ P.gluedι j = P.gluedι i :=
  Thickening.Hom.ext (colimit.w P.sourceDiagram h)
    (DividedPowerScheme.Hom.ext (P.ambientPresentation.map_ι h))

/-- Each chart morphism is an open immersion on ambient schemes. -/
instance isOpenImmersion_gluedι_targetHom (i : J) :
    IsOpenImmersion (P.gluedι i).targetHom.hom :=
  inferInstanceAs (IsOpenImmersion (colimit.ι P.ambient i))

/-- Each chart morphism is an open immersion on thickened schemes. -/
instance isOpenImmersion_gluedι_sourceHom (i : J) :
    IsOpenImmersion (P.gluedι i).sourceHom :=
  inferInstanceAs (IsOpenImmersion (colimit.ι P.sourceDiagram i))

/-- **Each chart is an induced open of the glued object**: the divided power ideal of the chart is
induced from the glued one. -/
theorem isInducedOpen_gluedι (i : J) :
    Crystalline.DividedPowerScheme.IsInducedOpen (P.gluedι i).targetHom :=
  P.ambientPresentation.gluedι_isInducedOpen i

/-- **The charts cover the ambient scheme of the glued object.** -/
theorem gluedι_jointly_surjective (x : P.glued.thickening.target.scheme) :
    ∃ (i : J) (y : (P.functor.obj i).thickening.target.scheme),
      (P.gluedι i).targetHom.hom y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective P.ambient x

/-- **The charts cover the thickened scheme of the glued object.** -/
theorem gluedι_sourceHom_jointly_surjective (x : P.glued.thickening.source) :
    ∃ (i : J) (y : (P.functor.obj i).thickening.source), (P.gluedι i).sourceHom y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective P.sourceDiagram x

section Descent

variable (C : Thickening S) (m : ∀ i, P.functor.obj i ⟶ C)
  (hm : ∀ {i j : J} (h : i ⟶ j), P.functor.map h ≫ m j = m i)

/-- The cocone on the diagram of thickened schemes given by a compatible family of morphisms out
of the charts. -/
@[implicit_reducible]
def descSourceCocone : Cocone P.sourceDiagram where
  pt := C.thickening.source
  ι :=
    { app i := (m i).sourceHom
      naturality {i j} h := by
        have e : ((P.functor.map h) ≫ m j).sourceHom = (m i).sourceHom :=
          congrArg Thickening.Hom.sourceHom (hm h)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact e }

/-- The cocone on the diagram of ambient schemes given by a compatible family of morphisms out of
the charts. -/
@[implicit_reducible]
def descTargetCocone : Cocone P.ambient where
  pt := C.thickening.target.scheme
  ι :=
    { app i := (m i).targetHom.hom
      naturality {i j} h := by
        have e : ((P.functor.map h) ≫ m j).targetHom.hom = (m i).targetHom.hom :=
          congrArg (fun k : P.functor.obj i ⟶ C ↦ k.targetHom.hom) (hm h)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact e }

/-- **The descent of a compatible family of morphisms out of the charts to the glued object.** -/
@[implicit_reducible]
def gluedHom : P.glued ⟶ C where
  sourceHom := colimit.desc P.sourceDiagram (P.descSourceCocone C m hm)
  targetHom := P.ambientPresentation.gluedMap C.thickening.target
    (colimit.desc P.ambient (P.descTargetCocone C m hm)) (fun i ↦ (m i).targetHom)
    (fun i ↦ colimit.ι_desc (P.descTargetCocone C m hm) i)
  immersion_naturality := by
    change P.gluedImmersion ≫ colimit.desc P.ambient (P.descTargetCocone C m hm) =
      colimit.desc P.sourceDiagram (P.descSourceCocone C m hm) ≫ C.thickening.immersion
    refine colimit.hom_ext fun i ↦ ?_
    rw [← Category.assoc, ← Category.assoc, P.ι_gluedImmersion i, colimit.ι_desc,
      Category.assoc, colimit.ι_desc]
    exact (m i).immersion_naturality
  base_naturality := by
    refine DividedPowerScheme.Hom.ext ?_
    change colimit.desc P.ambient (P.descTargetCocone C m hm) ≫ C.toBase.hom = P.gluedToBaseHom
    refine colimit.hom_ext fun i ↦ ?_
    rw [← Category.assoc, colimit.ι_desc, P.ι_gluedToBaseHom i]
    exact congrArg DividedPowerScheme.Hom.hom (m i).base_naturality
  toX_naturality := by
    change colimit.desc P.sourceDiagram (P.descSourceCocone C m hm) ≫ C.toX = P.gluedToX
    refine colimit.hom_ext fun i ↦ ?_
    rw [← Category.assoc, colimit.ι_desc, P.ι_gluedToX i]
    exact (m i).toX_naturality

/-- The descended morphism restricts to the given morphism on each chart. -/
theorem gluedι_gluedHom (i : J) : P.gluedι i ≫ P.gluedHom C m hm = m i :=
  Thickening.Hom.ext (colimit.ι_desc (P.descSourceCocone C m hm) i)
    (DividedPowerScheme.Hom.ext (colimit.ι_desc (P.descTargetCocone C m hm) i))

end Descent

/-- **A morphism out of the glued object is determined by its restrictions to the charts.** -/
theorem gluedHom_ext {C : Thickening S} {f g : P.glued ⟶ C}
    (h : ∀ i, P.gluedι i ≫ f = P.gluedι i ≫ g) : f = g := by
  refine Thickening.Hom.ext (colimit.hom_ext fun i ↦ ?_)
    (DividedPowerScheme.Hom.ext (colimit.hom_ext fun i ↦ ?_))
  · exact congrArg Thickening.Hom.sourceHom (h i)
  · exact congrArg (fun k : P.functor.obj i ⟶ C ↦ k.targetHom.hom) (h i)

end Thin

end ThickeningPresentation

end Crystalline.GlobalCrystallineSituation

end
