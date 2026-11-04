module

public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite

/-!
# Presentations of a quotient sheaf in an arbitrary universe

The quotient sheaf of a pre-relation on the big fppf site of `S` takes its values in `Type u`,
the universe of morphisms of `S`-schemes. This file lifts the quotient construction to
`Type (max u v)`: the quotient presheaf is composed with `ULift` before sheafification, and the
relation is the kernel pair of the canonical map from the lifted functor of points.

## Main definitions

* `AlgebraicGeometry.Space.EtalePresentation` is a presentation of a sheaf with values in an
  arbitrary universe by an étale equivalence relation, with representability measured against
  `CategoryTheory.uliftYoneda`.
* `AlgebraicGeometry.Space.uliftQuotientSheaf` is the sheafification of the lifted quotient
  presheaf, and `AlgebraicGeometry.Space.uliftQuotientMap` the canonical map onto it.

## Main results

* `AlgebraicGeometry.Space.isPullback_uliftQuotientMap`: the given relation is the kernel
  pair of the lifted quotient map.
* `AlgebraicGeometry.Space.relative_ulift_sheafify` transports a representable morphism
  property from a map into a `Type u`-valued sheafification to the corresponding map into the
  lifted one.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u v w

namespace AlgebraicGeometry.Space

/-- For a fully faithful functor `F` presenting a site of `S`-schemes, the restricted functor
of points of `F.obj U` is the presheaf represented by `U`. -/
def pointsYonedaIso {C : Type v} [Category.{u} C] {S : Scheme.{u}} (F : C ⥤ Over S)
    [F.Full] [F.Faithful] (U : C) : points F (F.obj U) ≅ yoneda.obj U := by
  let hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  refine NatIso.ofComponents (fun X ↦ Equiv.toIso hF.homEquiv.symm) ?_
  intro X Y f
  ext g
  simp [points, hF, Functor.FullyFaithful.homEquiv, Functor.FullyFaithful.ofFullyFaithful]

/-! ### Lifting representability along `ULift` -/

/-- A morphism of `Type u`-valued presheaves which is representable by a morphism property
stays so after its values are lifted to `Type (max u v)`. -/
theorem relative_ulift_of_presheaf {C : Type w} [Category.{u} C] (P : MorphismProperty C)
    {X Y : Cᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hf : P.presheaf f) :
    P.relative uliftYoneda.{v} (Functor.whiskerRight f uliftFunctor.{v}) := by
  let H : (Cᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ Type (max u v)) :=
    (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max u v))).obj uliftFunctor.{v}
  have : H.Full := inferInstance
  have : H.Faithful := inferInstance
  show P.relative (yoneda ⋙ H) (H.map f)
  refine ⟨?_, ?_⟩
  · intro a g
    obtain ⟨g₀, rfl⟩ := H.map_surjective g
    obtain ⟨b, snd, fst, hpb⟩ := hf.1 g₀
    refine ⟨b, snd, H.map fst, ?_⟩
    simpa using hpb.map H
  · intro a b g fst snd hpb
    obtain ⟨g₀, hg₀⟩ := H.map_surjective g
    obtain ⟨fst₀, hfst₀⟩ := H.map_surjective fst
    have hpbMap : IsPullback (H.map fst₀) (H.map (yoneda.map snd)) (H.map f) (H.map g₀) := by
      convert hpb using 1 <;> simp
    have hcomm : fst₀ ≫ f = yoneda.map snd ≫ g₀ := by
      apply H.map_injective
      simpa only [Functor.map_comp] using hpbMap.w
    exact hf.2 g₀ fst₀ snd (hpbMap.of_map H hcomm)

/-- A map from a representable presheaf into a `Type u`-valued sheafification which is
representable by a morphism property induces a representable map into the sheafification of
the lifted presheaf. -/
theorem relative_ulift_sheafify {C : Type w} [Category.{u} C] [EssentiallySmall.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    [HasSheafify J (Type (max u v))] (P : MorphismProperty C) (F : Cᵒᵖ ⥤ Type u) {U : C}
    (f : yoneda.obj U ⟶ F) (hf : P.presheaf (f ≫ toSheafify J F)) :
    P.relative uliftYoneda.{v}
      (Functor.whiskerRight f uliftFunctor.{v} ≫
        toSheafify J (F ⋙ uliftFunctor.{v})) := by
  let _ : ((equivSmallModel.{u} C).inverse.inducedTopology J).PreservesSheafification
      uliftFunctor.{v, u} :=
    GrothendieckTopology.instPreservesSheafification _ _
  let _ : J.PreservesSheafification uliftFunctor.{v, u} :=
    GrothendieckTopology.PreservesSheafification.transport J
      ((equivSmallModel.{u} C).inverse.inducedTopology J)
      (equivSmallModel.{u} C).inverse (Type (max u v)) uliftFunctor.{v, u}
  let e := sheafifyComposeIso J uliftFunctor.{v} F
  apply ((P.relative uliftYoneda.{v}).cancel_right_of_respectsIso _ e.hom).mp
  rw [Category.assoc, sheafComposeIso_hom_fac, ← Functor.whiskerRight_comp]
  exact relative_ulift_of_presheaf P (f ≫ toSheafify J F) hf

/-! ### The lifted quotient sheaf and its presentation -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presentation of a sheaf on the big fppf site of `S` by an étale equivalence relation,
with the sheaf allowed to take values in a universe independent of the universe of morphisms
of schemes. Representability of the atlas is measured against
`CategoryTheory.uliftYoneda`. -/
structure EtalePresentation (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max u v)) where
  /-- The fppf sheaf condition. -/
  isSheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F
  /-- The presenting scheme. -/
  U : BigFppfOver B S hS
  /-- The scheme of relations. -/
  R : BigFppfOver B S hS
  /-- The target projection. -/
  target : R ⟶ U
  /-- The source projection. -/
  source : R ⟶ U
  /-- The projections form an étale equivalence relation. -/
  isEtaleEquivalenceRelation :
    IsEtaleEquivalenceRelation (relation B S hS source target)
  /-- The atlas map. -/
  toSpace : uliftYoneda.{v}.obj U ⟶ F
  /-- The atlas is surjective after every representable base change. -/
  surjective : (MorphismProperty.relative uliftYoneda.{v} (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) toSpace
  /-- The atlas is étale after every representable base change. -/
  etale : (MorphismProperty.relative uliftYoneda.{v} (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) toSpace
  /-- The original relation is the kernel pair of the atlas. -/
  isPullback : IsPullback (uliftYoneda.{v}.map target) (uliftYoneda.{v}.map source)
    toSpace toSpace

variable {R U : BigFppfOver B S hS} (s t : R ⟶ U)

/-- The quotient sheaf of a relation on the big fppf site of `S`, formed by lifting the values
of the quotient presheaf to `Type (max u v)` before sheafifying. -/
abbrev uliftQuotientSheaf [HasSheafify (BigFppfOver.topology B S hS) (Type (max u v))] :
    Sheaf (BigFppfOver.topology B S hS) (Type (max u v)) :=
  (presheafToSheaf (BigFppfOver.topology B S hS) (Type (max u v))).obj
    (quotientPresheaf (Over.post B.inclusion) (relation B S hS s t) ⋙ uliftFunctor.{v})

/-- The canonical map from the lifted functor of points of the presenting
scheme to the lifted quotient sheaf of its relation. -/
@[stacks 02WW "canonical quotient map"]
def uliftQuotientMap [HasSheafify (BigFppfOver.topology B S hS) (Type (max u v))] :
    uliftYoneda.{v}.obj U ⟶ (uliftQuotientSheaf.{u, v} B S hS s t).obj :=
  Functor.whiskerRight
    ((yonedaEquiv (F := points (Over.post B.inclusion)
      ((Over.post B.inclusion).obj U))).symm (𝟙 ((Over.post B.inclusion).obj U)) ≫
      toQuotientPresheaf (Over.post B.inclusion) (relation B S hS s t))
    uliftFunctor.{v} ≫
    toSheafify (BigFppfOver.topology B S hS) _

/-- The given relation is the kernel pair of the lifted quotient map. -/
theorem isPullback_uliftQuotientMap
    [HasSheafify (BigFppfOver.topology B S hS) (Type (max u v))]
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    IsPullback (uliftYoneda.{v}.map t) (uliftYoneda.{v}.map s)
      (uliftQuotientMap.{u, v} B S hS s t) (uliftQuotientMap.{u, v} B S hS s t) := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let F : C ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let j := relation B S hS s t
  let _ : F.Full := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Full
  let _ : F.Faithful := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Faithful
  let H : (Cᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ Type (max u v)) :=
    (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max u v))).obj uliftFunctor.{v}
  have hp : IsPullback
      (Functor.whiskerRight (targetMap F j) uliftFunctor.{v})
      (Functor.whiskerRight (sourceMap F j) uliftFunctor.{v})
      (Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{v})
      (Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{v}) :=
    (quotientPresheaf_isPullback F j).map H
  have hPoints (X : C) : Presheaf.IsSheaf J (points F (F.obj X) ⋙ uliftFunctor.{v}) := by
    apply (isSheaf_iff_isSheaf_of_type J _).mpr
    rw [Presieve.isSheaf_comp_uliftFunctor_iff]
    exact (isSheaf_iff_isSheaf_of_type J _).mp
      (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS (F.obj X))
  let hf := hp.map (presheafToSheaf J (Type (max u v)))
  let hf' := hf.map (sheafToPresheaf J (Type (max u v)))
  let iR := isoSheafify J (hPoints R)
  let iU := isoSheafify J (hPoints U)
  have hpts : IsPullback
      (Functor.whiskerRight (targetMap F j) uliftFunctor.{v})
      (Functor.whiskerRight (sourceMap F j) uliftFunctor.{v})
      (Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{v} ≫
        toSheafify J (quotientPresheaf F j ⋙ uliftFunctor.{v}))
      (Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{v} ≫
        toSheafify J (quotientPresheaf F j ⋙ uliftFunctor.{v})) :=
    hf'.of_iso' iR iU iU (Iso.refl _) (toSheafify_naturality J _).symm
      (toSheafify_naturality J _).symm (toSheafify_naturality J _).symm
      (toSheafify_naturality J _).symm
  let eR : points F (F.obj R) ⋙ uliftFunctor.{v} ≅ uliftYoneda.{v}.obj R :=
    Functor.isoWhiskerRight (pointsYonedaIso F R) uliftFunctor.{v}
  let eU : points F (F.obj U) ⋙ uliftFunctor.{v} ≅ uliftYoneda.{v}.obj U :=
    Functor.isoWhiskerRight (pointsYonedaIso F U) uliftFunctor.{v}
  have htarget : j.target = F.map t := prod.lift_fst _ _
  have hsource : j.source = F.map s := prod.lift_snd _ _
  let q := Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{v} ≫
    toSheafify J (quotientPresheaf F j ⋙ uliftFunctor.{v})
  have hcan : uliftQuotientMap.{u, v} B S hS s t = eU.inv ≫ q := by
    let e := pointsYonedaIso F U
    have he0 : (yonedaEquiv (F := points F (F.obj U))).symm (𝟙 (F.obj U)) = e.inv := by
      apply (yonedaEquiv (F := points F (F.obj U))).injective
      simp [e, pointsYonedaIso, points, Functor.FullyFaithful.homEquiv,
        Functor.FullyFaithful.ofFullyFaithful, yonedaEquiv]
    show Functor.whiskerRight
        ((yonedaEquiv (F := points F (F.obj U))).symm (𝟙 (F.obj U)) ≫
          toQuotientPresheaf F j) uliftFunctor.{v} ≫ toSheafify J _ = _
    rw [he0]
    rfl
  have ht : eR.inv ≫ Functor.whiskerRight (targetMap F j) uliftFunctor.{v} =
      uliftYoneda.{v}.map t ≫ eU.inv := by
    ext X ⟨x⟩
    show ULift.up (F.map x ≫ j.target) = ULift.up (F.map (x ≫ t))
    rw [htarget, Functor.map_comp]
  have hs : eR.inv ≫ Functor.whiskerRight (sourceMap F j) uliftFunctor.{v} =
      uliftYoneda.{v}.map s ≫ eU.inv := by
    ext X ⟨x⟩
    show ULift.up (F.map x ≫ j.source) = ULift.up (F.map (x ≫ s))
    rw [hsource, Functor.map_comp]
  exact hpts.of_iso' eR.symm eU.symm eU.symm (Iso.refl _) ht hs hcan.symm hcan.symm

end AlgebraicGeometry.Space

end
