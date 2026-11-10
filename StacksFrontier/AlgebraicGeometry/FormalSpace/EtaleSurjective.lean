module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Etale.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningClassification
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.Topology.Algebra.AdicTopology.FaithfullyFlatModWeakIdeal

/-!
# Surjectivity of an étale morphism of affine formal algebraic spaces

Let `R` be a weakly admissible topological ring, let `A` be an étale `R`-algebra and let `A^∧` be
the completion of `A` over `R`. The induced morphism `Spf A^∧ ⟶ Spf R` of affine formal algebraic
spaces over a base scheme `S` of a big fppf site is surjective exactly when `R → A` is faithfully
flat, and that can be tested on every, or on a single, weak ideal of definition of `R`.

## Main results

* `AlgebraicGeometry.FormalSpace.etaleFormalSpectrumMap_surjective_tfae`: surjectivity of
  `Spf A^∧ ⟶ Spf R` is equivalent to faithful flatness of `R → A`, and to faithful flatness of
  `R ⧸ J → A ⧸ JA` for every, or for some, weak ideal of definition `J` of `R`.
* `AlgebraicGeometry.FormalSpace.bijective_pointsMapULift_formalSpectrumInclusion`: the inclusion
  of a quotient stage into a formal spectrum is bijective on points.
* `AlgebraicGeometry.FormalSpace.surjective_pointsMapULift_sheafifiedYoneda_iff`: a morphism of
  objects of the site is surjective on the points of the sheaves it represents exactly when the
  underlying morphism of schemes is surjective.

## Implementation notes

The morphism of formal spectra is presented as in Tag 0AIF, by quotient systems for `R` and for
`A^∧` over `S` together with a continuous homomorphism between them realising the canonical map
`R → A^∧`. Surjectivity is `AlgebraicGeometry.FormalSpace.IsSurjective`, surjectivity of the
induced map on points, so no reduction of the source or of the target has to be chosen and neither
has to be known to be a formal algebraic space.

## References

* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### Points of a representable thickening -/

/-- The field-valued point of a presheaf of `Type (u + 1)` specified by a section over the spectrum
of a field of the site. -/
private def fieldPointOfValue (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ S)
    (x : F.obj (Opposite.op (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS)))) :
    Space.FieldValuedPointULift.{u + 1} B S hS F where
  carrier := K
  contained := hK
  toBase := b
  value := x

/-- A commuting square of fppf sheaves induces a commuting square of the maps on points. -/
public theorem pointsMapULift_square {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {W X Y Z : FppfSheaf B S hS} {a : W ⟶ X} {b : X ⟶ Z} {c : W ⟶ Y}
    {d : Y ⟶ Z} (h : a ≫ b = c ≫ d) (p : Space.pointsULift.{u + 1} B S hS W.obj) :
    Space.pointsMapULift.{u + 1} B S hS X.obj b.hom
        (Space.pointsMapULift.{u + 1} B S hS W.obj a.hom p)
      = Space.pointsMapULift.{u + 1} B S hS Y.obj d.hom
        (Space.pointsMapULift.{u + 1} B S hS W.obj c.hom p) := by
  have h' : a.hom ≫ b.hom = c.hom ≫ d.hom := congrArg (fun k : W ⟶ Z => k.hom) h
  have h₁ := congrArg (fun α => Space.pointsMapULift.{u + 1} B S hS W.obj α p) h'
  simpa only [Space.pointsMapULift_comp, Function.comp_apply] using h₁

/-- A morphism of fppf sheaves whose base change along every represented sheaf is a thickening of
schemes is bijective on the sections over the spectrum of a field of the site. -/
public theorem bijective_app_of_relativeThickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f)
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ S) :
    Function.Bijective (f.hom.app (Opposite.op (Over.mk
      (⟨b⟩ : B.obj hK ⟶ B.obj hS)))) := by
  let topology := BigFppfOver.topology B S hS
  let : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let : topology.Subcanonical := inferInstance
  let object : BigFppfOver B S hS := Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS)
  let embedding := Sheaf.sheafifiedYoneda topology
  let iso := Sheaf.sheafifiedYonedaIsoUliftYoneda' topology
  let sections (Z : Sheaf topology (Type (u + 1))) :
      (embedding.obj object ⟶ Z) ≃ Z.obj.obj (Opposite.op object) :=
    (Iso.homCongr (iso.app object) (Iso.refl Z)).trans (topology.uliftYonedaEquiv.{u + 1})
  have hiso (map : embedding.obj object ⟶ Y) : IsIso (hf.rep.snd map) := by
    have : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hf.rep.snd map)) := (hf.property_snd map).1
    have : Surjective ((BigFppfOver.toScheme B S hS).map (hf.rep.snd map)) :=
      ⟨(hf.property_snd map).2⟩
    have : IsReduced ((BigFppfOver.toScheme B S hS).obj object) := by
      change IsReduced (Spec (.of K))
      infer_instance
    have : IsIso ((BigFppfOver.toScheme B S hS).map (hf.rep.snd map)) :=
      isIso_of_isClosedImmersion_of_surjective _
    exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  have hhom : Function.Bijective (fun map : embedding.obj object ⟶ X => map ≫ f) := by
    constructor
    · intro left right heq
      have := hiso (left ≫ f)
      let square := hf.rep.isPullback (left ≫ f)
      have hleft := square.lift_fst left (𝟙 _) (by simp only [Category.id_comp])
      have hright := square.lift_fst right (𝟙 _)
        (by simpa only [Category.id_comp] using heq.symm)
      have hequal : square.lift left (𝟙 _) (by simp only [Category.id_comp]) =
          square.lift right (𝟙 _) (by simpa only [Category.id_comp] using heq.symm) := by
        apply (cancel_mono (embedding.map (hf.rep.snd (left ≫ f)))).mp
        rw [square.lift_snd, square.lift_snd]
      exact hleft.symm.trans
        ((congrArg (fun map => map ≫ hf.rep.fst (left ≫ f)) hequal).trans hright)
    · intro map
      have := hiso map
      refine ⟨embedding.map (inv (hf.rep.snd map)) ≫ hf.rep.fst map, ?_⟩
      change (embedding.map (inv (hf.rep.snd map)) ≫ hf.rep.fst map) ≫ f = map
      rw [Category.assoc, hf.rep.w, ← Category.assoc, ← embedding.map_comp, IsIso.inv_hom_id,
        embedding.map_id, Category.id_comp]
  have hcomp (map : embedding.obj object ⟶ X) :
      sections Y (map ≫ f) = f.hom.app _ (sections X map) := rfl
  constructor
  · intro left right heq
    apply (sections X).symm.injective
    apply hhom.1
    apply (sections Y).injective
    simpa only [hcomp, Equiv.apply_symm_apply] using heq
  · intro element
    obtain ⟨map, hmap⟩ := hhom.2 ((sections Y).symm element)
    exact ⟨sections X map, (hcomp map).symm.trans
      ((congrArg (sections Y) hmap).trans ((sections Y).apply_symm_apply element))⟩

/-- A morphism of presheaves of `Type (u + 1)` which is bijective on the sections over the spectrum
of every field of the site is bijective on points. -/
public theorem bijective_pointsMapULift_of_bijective_app
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : F ⟶ G)
    (hf : ∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
      (b : Spec (.of K) ⟶ S), Function.Bijective
        (f.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS))))) :
    Function.Bijective (Space.pointsMapULift.{u + 1} B S hS F f) := by
  classical
  let liftPoint (p : Space.FieldValuedPointULift.{u + 1} B S hS G) :
      Space.FieldValuedPointULift.{u + 1} B S hS F :=
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := ((hf p.carrier p.contained p.toBase).2 p.value).choose }
  have hlift (p : Space.FieldValuedPointULift.{u + 1} B S hS G) :
      f.app (Opposite.op (p.siteObject B S hS G)) (liftPoint p).value = p.value :=
    ((hf p.carrier p.contained p.toBase).2 p.value).choose_spec
  let inverse : Space.pointsULift.{u + 1} B S hS G → Space.pointsULift.{u + 1} B S hS F :=
    Quot.map liftPoint (by
      intro left right hcommon
      obtain ⟨extension, ⟨leftMap, hleft⟩, ⟨rightMap, hright⟩⟩ := hcommon
      have step {q : Space.FieldValuedPointULift.{u + 1} B S hS G}
          (m : extension.siteObject B S hS G ⟶ q.siteObject B S hS G)
          (h : G.map m.op q.value = extension.value) :
          F.map m.op (liftPoint q).value = (liftPoint extension).value := by
        apply (hf extension.carrier extension.contained extension.toBase).1
        change f.app (Opposite.op (extension.siteObject B S hS G))
            (F.map m.op (liftPoint q).value) =
          f.app (Opposite.op (extension.siteObject B S hS G)) (liftPoint extension).value
        rw [NatTrans.naturality_apply f m.op, hlift, hlift]
        exact h
      exact ⟨liftPoint extension, ⟨leftMap, step leftMap hleft⟩, ⟨rightMap, step rightMap hright⟩⟩)
  have hleft : Function.LeftInverse inverse (Space.pointsMapULift.{u + 1} B S hS F f) := by
    intro point
    induction point using Quot.ind with
    | _ point =>
      change Quot.mk _ (liftPoint (Space.FieldValuedPointULift.map B S hS F f point)) =
        Quot.mk _ point
      refine congrArg (Quot.mk _) ?_
      have hvalue : (liftPoint (Space.FieldValuedPointULift.map B S hS F f point)).value =
          point.value := (hf point.carrier point.contained point.toBase).1
        (hlift (Space.FieldValuedPointULift.map B S hS F f point))
      exact congrArg (fun value => fieldPointOfValue B S hS F point.carrier point.contained
        point.toBase value) hvalue
  have hright : Function.RightInverse inverse (Space.pointsMapULift.{u + 1} B S hS F f) := by
    intro point
    induction point using Quot.ind with
    | _ point =>
      change Quot.mk _ (Space.FieldValuedPointULift.map B S hS F f (liftPoint point)) =
        Quot.mk _ point
      refine congrArg (Quot.mk _) ?_
      exact congrArg (fun value => fieldPointOfValue B S hS G point.carrier point.contained
        point.toBase value) (hlift point)
  exact ⟨hleft.injective, hright.surjective⟩

/-- The inclusion of a quotient stage into a formal spectrum is bijective on points. -/
public theorem bijective_pointsMapULift_formalSpectrumInclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (J : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    Function.Bijective (Space.pointsMapULift.{u + 1} B S hS
      ((formalSpectrumDiagram D).obj (OrderDual.toDual J)).obj
      (formalSpectrumInclusion D (OrderDual.toDual J)).hom) := by
  let presentation : WeakIdealColimitPresentation B S hS A (formalSpectrum D) :=
    { diagram := D.diagram
      quotientIso := fun _ => Iso.refl _
      quotientIso_natural := by intro first second arrow; rfl
      colimitIso := Iso.refl _ }
  have hthick := isThickening_quotient B S hS A (formalSpectrum D) presentation hA
    (OrderDual.toDual J)
  have hthick' : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (formalSpectrumInclusion D (OrderDual.toDual J)) := by
    simpa only [quotientMap, presentation, Iso.refl_inv, Category.comp_id, formalSpectrum,
      formalSpectrumDiagram, formalSpectrumInclusion, Functor.comp_obj] using hthick
  exact bijective_pointsMapULift_of_bijective_app B S hS _
    (bijective_app_of_relativeThickening B S hS _ hthick')

/-! ### Points in the two value universes -/

/-- A field-valued point of a presheaf of `Type u` is a field-valued point of its universe lift. -/
private def uliftFieldPointEquiv (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Space.FieldValuedPoint B S hS F ≃
      Space.FieldValuedPointULift.{u + 1} B S hS (F ⋙ uliftFunctor.{u + 1}) where
  toFun p :=
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := ⟨p.value⟩ }
  invFun p :=
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := p.value.down }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The points of a presheaf of `Type u` are the points of its universe lift. -/
private def uliftPointsEquiv (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Space.points B S hS F ≃
      Space.pointsULift.{u + 1} B S hS (F ⋙ uliftFunctor.{u + 1}) := by
  refine Quot.congr (uliftFieldPointEquiv B S hS F) ?_
  intro first second
  constructor
  · rintro ⟨p, ⟨left, hleft⟩, ⟨right, hright⟩⟩
    exact ⟨uliftFieldPointEquiv B S hS F p, ⟨left, congrArg ULift.up hleft⟩,
      ⟨right, congrArg ULift.up hright⟩⟩
  · rintro ⟨p, ⟨left, hleft⟩, ⟨right, hright⟩⟩
    exact ⟨(uliftFieldPointEquiv B S hS F).symm p, ⟨left, congrArg ULift.down hleft⟩,
      ⟨right, congrArg ULift.down hright⟩⟩

/-- The identification of the points of a presheaf of `Type u` with those of its universe lift is
natural. -/
private theorem uliftPointsEquiv_naturality (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (p : Space.points B S hS F) :
    uliftPointsEquiv B S hS G (Space.pointsMap B S hS F f p) =
      Space.pointsMapULift.{u + 1} B S hS (F ⋙ uliftFunctor.{u + 1})
        (Functor.whiskerRight f uliftFunctor.{u + 1}) (uliftPointsEquiv B S hS F p) := by
  induction p using Quot.ind with
  | _ p => rfl

/-- A morphism of presheaves of `Type u` is surjective on points exactly when its universe lift
is. -/
private theorem surjective_pointsMapULift_whiskerRight_iff (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    Function.Surjective (Space.pointsMapULift.{u + 1} B S hS (F ⋙ uliftFunctor.{u + 1})
        (Functor.whiskerRight f uliftFunctor.{u + 1})) ↔
      Function.Surjective (Space.pointsMap B S hS F f) := by
  constructor
  · intro hsurjective p
    obtain ⟨pre, hpre⟩ := hsurjective (uliftPointsEquiv B S hS G p)
    obtain ⟨lift, rfl⟩ := (uliftPointsEquiv B S hS F).surjective pre
    exact ⟨lift, (uliftPointsEquiv B S hS G).injective
      ((uliftPointsEquiv_naturality B S hS f lift).trans hpre)⟩
  · intro hsurjective p
    obtain ⟨pre, rfl⟩ := (uliftPointsEquiv B S hS G).surjective p
    obtain ⟨lift, rfl⟩ := hsurjective pre
    exact ⟨uliftPointsEquiv B S hS F lift,
      (uliftPointsEquiv_naturality B S hS f lift).symm⟩

/-! ### Surjectivity through a commuting square -/

/-- In a commuting square whose two vertical maps are bijections, the top map is surjective exactly
when the bottom map is. -/
public theorem surjective_iff_of_commutes {X X' Y Y' : Type*} (left : X → X')
    (right : Y → Y') (top : X → Y) (bottom : X' → Y') (hleft : Function.Bijective left)
    (hright : Function.Bijective right) (hcomm : ∀ p, right (top p) = bottom (left p)) :
    Function.Surjective top ↔ Function.Surjective bottom := by
  constructor
  · intro hsurjective p
    obtain ⟨pre, rfl⟩ := hright.2 p
    obtain ⟨lift, rfl⟩ := hsurjective pre
    exact ⟨left lift, (hcomm lift).symm⟩
  · intro hsurjective p
    obtain ⟨pre, hpre⟩ := hsurjective (right p)
    obtain ⟨lift, rfl⟩ := hleft.2 pre
    exact ⟨lift, hright.1 ((hcomm lift).trans hpre)⟩

/-- A morphism of objects of the big fppf site of `S` is surjective on the points of the sheaves it
represents exactly when the underlying morphism of schemes is surjective. -/
public theorem surjective_pointsMapULift_sheafifiedYoneda_iff (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {source target : BigFppfOver B S hS}
    (f : source ⟶ target) :
    Function.Surjective (Space.pointsMapULift.{u + 1} B S hS
        (((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj source).obj)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map f).hom) ↔
      Surjective ((BigFppfOver.toScheme B S hS).map f) := by
  let topology := BigFppfOver.topology B S hS
  let : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let : topology.Subcanonical := inferInstance
  let iso := Sheaf.sheafifiedYonedaIsoUliftYoneda' topology
  have hbij (object : BigFppfOver B S hS) :=
    bijective_pointsMapULift_of_bijective_app B S hS (iso.hom.app object).hom
      (fun K _ hK b => ConcreteCategory.bijective_of_isIso ((iso.hom.app object).hom.app _))
  rw [surjective_iff_of_commutes
    (Space.pointsMapULift.{u + 1} B S hS _ (iso.hom.app source).hom)
    (Space.pointsMapULift.{u + 1} B S hS _ (iso.hom.app target).hom)
    (Space.pointsMapULift.{u + 1} B S hS _ ((Sheaf.sheafifiedYoneda topology).map f).hom)
    (Space.pointsMapULift.{u + 1} B S hS _ ((topology.uliftYoneda.{u + 1}).map f).hom)
    (hbij source) (hbij target) (fun p => pointsMapULift_square (iso.hom.naturality f) p)]
  change Function.Surjective (Space.pointsMapULift.{u + 1} B S hS _
    (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1})) ↔ _
  rw [surjective_pointsMapULift_whiskerRight_iff]
  refine (Space.presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj target)
    (isAlgebraicSpace_yoneda B S hS target) source (yoneda.map f)).symm.trans ?_
  let : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨by
      intro first second third fourth top left right bottom square hsurjective
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := (@Surjective.{u} : MorphismProperty Scheme.{u}))
        (square.map (BigFppfOver.toScheme B S hS)) hsurjective⟩
  exact MorphismProperty.relative_map_iff

/-! ### Stacks 0AN9 -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {R A : Type u}
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] [CommRing A]

/-- Let `R` be a weakly admissible topological ring, let `A` be an étale `R`-algebra and let
`R → A^∧` be the canonical map to the completion of `A` over `R`, presented by quotient systems
over a base scheme `S` of a big fppf site. The following are equivalent:

1. the induced morphism `Spf A^∧ ⟶ Spf R` of formal spectra is surjective;
2. `R → A` is faithfully flat;
3. `R ⧸ J → A ⧸ JA` is faithfully flat for every weak ideal of definition `J` of `R`;
4. `R ⧸ J → A ⧸ JA` is faithfully flat for some weak ideal of definition `J` of `R`. -/
@[stacks 0AN9]
public theorem etaleFormalSpectrumMap_surjective_tfae (f : R →+* A)
    (hA : letI : Algebra R A := f.toAlgebra; Algebra.Etale R A)
    (hB : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem B S hS R)
    (E : QuotientSystem B S hS (TopologicalRing.CompletionOver f))
    (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f) :
    List.TFAE
      [ IsSurjective B S hS (formalSpectrumMap hB g),
        f.FaithfullyFlat,
        ∀ J : TopologicalRing.WeakIdealOfDefinitionIndex R,
          (Ideal.quotientMap (J.1.map f) f Ideal.le_comap_map).FaithfullyFlat,
        ∃ J : TopologicalRing.WeakIdealOfDefinitionIndex R,
          (Ideal.quotientMap (J.1.map f) f Ideal.le_comap_map).FaithfullyFlat ] := by
  let : Algebra R A := f.toAlgebra
  let : Algebra.Etale R A := hA
  have hflat : f.Flat := inferInstanceAs (Module.Flat R A)
  tfae_have 2 → 3 := fun h J => RingHom.faithfullyFlat_quotientMap f h J.1
  tfae_have 3 → 4 := fun h => hB.1.elim fun J hJ => ⟨⟨J, hJ⟩, h _⟩
  tfae_have 4 → 2 := fun ⟨J, hJ⟩ =>
    (RingHom.faithfullyFlat_iff_quotientMap f hflat J.1
      (TopologicalRing.le_ringJacobson_of_isWeakIdealOfDefinition hB J.2)).mpr hJ
  tfae_have 1 ↔ 3 := by
    have hstage (J : TopologicalRing.WeakIdealOfDefinitionIndex R) :
        IsSurjective B S hS (formalSpectrumMap hB g) ↔
          (Ideal.quotientMap (J.1.map f) f Ideal.le_comap_map).FaithfullyFlat := by
      let projection := TopologicalRing.CompletionOver.projection f J
      let kernel : TopologicalRing.WeakIdealOfDefinitionIndex
          (TopologicalRing.CompletionOver f) :=
        ⟨RingHom.ker projection, TopologicalRing.projection_ker_isWeakIdealOfDefinition f J⟩
      have hle : J.1 ≤ Ideal.comap g.toRingHom kernel.1 := by
        rw [hg]
        intro element helement
        change Ideal.Quotient.mk (TopologicalRing.extendedIdeal f J) (f element) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f helement)
      let stage := g.stageMap J kernel hle
      have hsource := bijective_pointsMapULift_formalSpectrumInclusion B S hS
        (TopologicalRing.completionOver_isWeaklyAdmissible f hB) E kernel
      have htarget := bijective_pointsMapULift_formalSpectrumInclusion B S hS hB D J
      have hspec := formalSpectrumMap_spec hB g J kernel hle
      refine (surjective_iff_of_commutes
        (Space.pointsMapULift.{u + 1} B S hS _
          (formalSpectrumInclusion E (OrderDual.toDual kernel)).hom)
        (Space.pointsMapULift.{u + 1} B S hS _
          (formalSpectrumInclusion D (OrderDual.toDual J)).hom)
        (Space.pointsMapULift.{u + 1} B S hS _
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            ((BigAffineFppf.inclusion B S hS).map stage)).hom)
        (Space.pointsMapULift.{u + 1} B S hS _ (formalSpectrumMap hB g).hom)
        hsource htarget (fun p => (pointsMapULift_square hspec p).symm)).symm.trans
        ((surjective_pointsMapULift_sheafifiedYoneda_iff B S hS
          ((BigAffineFppf.inclusion B S hS).map stage)).trans ?_)
      change Surjective (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap kernel.1 g.toRingHom hle))) ↔ _
      let equivalence := projection.quotientKerEquivOfSurjective
        (TopologicalRing.CompletionOver.projection_surjective f J)
      let : IsIso (CommRingCat.ofHom equivalence.toRingHom) :=
        equivalence.toCommRingCatIso.isIso_hom
      have heq : equivalence.toRingHom.comp (Ideal.quotientMap kernel.1 g.toRingHom hle) =
          Ideal.quotientMap (J.1.map f) f Ideal.le_comap_map := by
        refine Ideal.Quotient.ringHom_ext ?_
        ext element
        change equivalence (Ideal.Quotient.mk (RingHom.ker projection) (g.toRingHom element)) =
          Ideal.Quotient.mk (J.1.map f) (f element)
        rw [RingHom.quotientKerEquivOfSurjective_apply_mk, hg]
        rfl
      have hfaithful : (Ideal.quotientMap kernel.1 g.toRingHom hle).FaithfullyFlat ↔
          (Ideal.quotientMap (J.1.map f) f Ideal.le_comap_map).FaithfullyFlat := by
        rw [← heq]
        exact (RingHom.FaithfullyFlat.respectsIso.cancel_right_isIso
          (CommRingCat.ofHom (Ideal.quotientMap kernel.1 g.toRingHom hle))
          (CommRingCat.ofHom equivalence.toRingHom)).symm
      have hflatStage : (Ideal.quotientMap kernel.1 g.toRingHom hle).Flat := by
        have hcomposed := RingHom.flat_quotientMap f hflat J.1
        rw [← heq] at hcomposed
        exact (RingHom.Flat.respectsIso.cancel_right_isIso
          (CommRingCat.ofHom (Ideal.quotientMap kernel.1 g.toRingHom hle))
          (CommRingCat.ofHom equivalence.toRingHom)).mp hcomposed
      rw [← hfaithful]
      have hflatSpec : Flat (Spec.map (CommRingCat.ofHom
          (Ideal.quotientMap kernel.1 g.toRingHom hle))) :=
        (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hflatStage
      exact ⟨fun hsurjective => (flat_and_surjective_SpecMap_iff _).mp ⟨hflatSpec, hsurjective⟩,
        fun hfaithful => ((flat_and_surjective_SpecMap_iff _).mpr hfaithful).2⟩
    exact ⟨fun hsurjective J => (hstage J).mp hsurjective,
      fun hfaithful => hB.1.elim fun J hJ => (hstage ⟨J, hJ⟩).mpr (hfaithful _)⟩
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
