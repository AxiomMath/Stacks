module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Diagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Reduction
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction

/-!
# Flatness and universal openness of the composition of a groupoid in algebraic spaces

Composition in a groupoid in algebraic spaces is a base change of the target morphism, so it
is flat, respectively universally open, as soon as the target is. When the object space is the
spectrum of a field, the target morphism is automatically flat and universally open, and hence
so is the composition.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_comp_of_isFlat_target`: if the target
  morphism of a groupoid in algebraic spaces is flat, so is its composition.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.universallyOpen_comp_of_universallyOpen_target`:
  if the target morphism of a groupoid in algebraic spaces is universally open, so is its
  composition.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_comp_of_objects_eq_spec_field`:
  **Stacks 06E0**, first assertion: the composition of a groupoid in algebraic spaces whose
  object space is the spectrum of a field is flat and universally open.

## Implementation notes

The reduction of the composition to the target is
`AlgebraicGeometry.Space.isPullback_fst_comp`, which exhibits the
composition as the base change of the target along itself, together with stability of flatness
under base change (Stacks 03MO) and of universal openness under base change (Stacks 03Z3).

Flatness of the target over a field spectrum is checked on one surjective étale chart, which
is legitimate because flatness of morphisms of schemes is étale local on source and target
(Stacks 04R3). On a chart the target becomes a morphism of schemes whose codomain is an
integral scheme with one point, over which every morphism is flat. Universal openness of the
target over a field spectrum is Stacks 06DN,
`AlgebraicGeometry.Space.universallyOpen_to_field`.

The hypothesis is an *equality* of the object space with the algebraic space of the field
spectrum, not an isomorphism, because that is how the situation arises: the object space is
prescribed. Flatness is then transported along the induced equality of presheaves by
`isFlat_conjugate`, which is stability of flatness under pre- and post-composition with
isomorphisms of presheaves.

## References

* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03Z3](https://stacks.math.columbia.edu/tag/03Z3)
* [Stacks Project, Tag 04P9](https://stacks.math.columbia.edu/tag/04P9)
* [Stacks Project, Tag 06DN](https://stacks.math.columbia.edu/tag/06DN)
* [Stacks Project, Tag 06E0](https://stacks.math.columbia.edu/tag/06E0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

/-- Flatness of a morphism of presheaves is unchanged by composing with isomorphisms on either
side. -/
private theorem isFlat_conjugate {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {F F' G G' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (e : F' ≅ F) (i : G ≅ G') (f : F ⟶ G)
    (hf : Space.IsFlat C S hS f) :
    Space.IsFlat C S hS (e.hom ≫ f ≫ i.hom) := by
  intro U V a b h ha hb hh
  let Q : MorphismProperty (BigFppfOver C S hS) :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)
  have ha' : Q.presheaf (a ≫ e.hom) := (Q.presheaf.cancel_right_of_respectsIso a e.hom).2 ha
  have hb' : Q.presheaf (b ≫ i.inv) := (Q.presheaf.cancel_right_of_respectsIso b i.inv).2 hb
  have hh' : yoneda.map h ≫ (b ≫ i.inv) = (a ≫ e.hom) ≫ f := by
    calc yoneda.map h ≫ (b ≫ i.inv) = (yoneda.map h ≫ b) ≫ i.inv := by simp [Category.assoc]
      _ = (a ≫ (e.hom ≫ f ≫ i.hom)) ≫ i.inv := by rw [hh]
      _ = (a ≫ e.hom) ≫ f := by simp [Category.assoc]
  exact hf U V (a ≫ e.hom) (b ≫ i.inv) h ha' hb' hh'

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_FlatComposition :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_FlatComposition
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- If the target morphism of a groupoid in algebraic spaces is flat, so is its composition:
composition is a base change of the target along itself. -/
theorem isFlat_comp_of_isFlat_target (G : GroupoidInAlgebraicSpaces C S hS B)
    (ht : Space.IsFlat C S hS G.target.hom) : Space.IsFlat C S hS G.comp.hom :=
  (Space.isFlat_isStableUnderBaseChange C S hS).of_isPullback (Space.isPullback_fst_comp G) ht

/-- If the target morphism of a groupoid in algebraic spaces is universally open, so is its
composition: composition is a base change of the target along itself (Stacks 03Z3). -/
theorem universallyOpen_comp_of_universallyOpen_target (G : GroupoidInAlgebraicSpaces C S hS B)
    (ht : Space.UniversallyOpen C S hS G.target.hom) :
    Space.UniversallyOpen C S hS G.comp.hom := by
  have hsq := ((Space.isPullback_fst_comp G).map (ObjectProperty.ι _)).flip
  exact Space.universallyOpen_of_comp_isIso C S hS hsq.isoPullback.hom hsq.isoPullback_hom_fst
    (Space.universallyOpen_pullback C S hS G.arrows.property G.objects.property
      G.arrows.property G.target.hom G.target.hom ht)

/-- The target morphism of a groupoid in algebraic spaces whose object space is the spectrum
of a field is flat. -/
private theorem isFlat_target_of_objects_eq_spec_field {k : Type u} [Field k]
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (structureMap : Spec (.of k) ⟶ S) (hk : C.Contains (Spec (.of k)))
    (B : AlgebraicSpaces C S hS) (G : GroupoidInAlgebraicSpaces C S hS B)
    (objects_eq : G.objects =
      schemeSpace (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS))) :
    Space.IsFlat C S hS G.target.hom := by
  let T := BigFppfOver.toScheme C S hS
  let V : BigFppfOver C S hS := Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)
  let ei : G.objects.obj ≅ yoneda.obj V :=
    eqToIso (congrArg (fun X : AlgebraicSpaces C S hS => X.obj) objects_eq)
  let f : G.arrows.obj ⟶ yoneda.obj V := G.target.hom ≫ ei.hom
  let q : yoneda.obj V ⟶ yoneda.obj V := 𝟙 _
  let _ : HasPullbacks (BigFppfOver C S hS) := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan T := by
    show PreservesLimitsOfShape WalkingCospan ((Over.forget (C.obj hS)) ⋙ C.inclusion)
    exact comp_preservesLimitsOfShape _ _
  have hq : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange],
      P (T.map (𝟙 V)) → (MorphismProperty.inverseImage P T).presheaf q := by
    intro P _ h
    have : (MorphismProperty.inverseImage P T).IsStableUnderBaseChange :=
      ⟨fun sq hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P) (sq.map T) hg⟩
    simpa [q, T] using
      (MorphismProperty.relative_map_iff (F := yoneda)
        (P := MorphismProperty.inverseImage P T)).2 h
  have hq_surj := hq (@Surjective.{u}) (by infer_instance)
  have hq_etale := hq (@Etale.{u}) (by infer_instance)
  obtain ⟨U, p, α, hcomm, hp_surj, hp_etale⟩ :=
    Space.exists_surjective_etale_presentation_lift C S hS G.arrows.property
      (isAlgebraicSpace_yoneda C S hS V) f V q hq_surj hq_etale
  have hf : Space.IsFlat C S hS f := by
    apply (Space.holdsOnEveryEtaleChart_iff_surjectiveChart C S hS
      (@Flat : MorphismProperty Scheme.{u}) Flat.isEtaleLocalOnSourceAndTarget
      G.arrows.property (isAlgebraicSpace_yoneda C S hS V) f).2
    refine ⟨U, V, p, q, α, hp_etale, hq_etale, hp_surj, hcomm.symm, ?_⟩
    have : Subsingleton ((BigFppfOver.toScheme C S hS).obj V) := by
      show Subsingleton (Spec (.of k))
      infer_instance
    have : IsIntegral ((BigFppfOver.toScheme C S hS).obj V) := by
      show IsIntegral (Spec (.of k))
      infer_instance
    infer_instance
  have htarget := isFlat_conjugate (Iso.refl G.arrows.obj) ei.symm f hf
  simpa [f, ei, Category.assoc] using htarget

/-- The target morphism of a groupoid in algebraic spaces whose object space is the spectrum
of a field is universally open: every morphism of algebraic spaces to the spectrum of a field
is (Stacks 06DN). -/
private theorem universallyOpen_target_of_objects_eq_spec_field {k : Type u} [Field k]
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (structureMap : Spec (.of k) ⟶ S) (hk : C.Contains (Spec (.of k)))
    (B : AlgebraicSpaces C S hS) (G : GroupoidInAlgebraicSpaces C S hS B)
    (objects_eq : G.objects =
      schemeSpace (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS))) :
    Space.UniversallyOpen C S hS G.target.hom := by
  have key : ∀ {Y : AlgebraicSpaces C S hS},
      Y = schemeSpace (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)) →
      ∀ f : G.arrows ⟶ Y, Space.UniversallyOpen C S hS f.hom := by
    rintro Y rfl f
    exact Space.universallyOpen_to_field C S hS G.arrows.property (k := k) (Iso.refl _) f.hom
  exact key objects_eq G.target

/-- **Stacks 06E0**, first assertion. Composition in a groupoid in algebraic spaces whose
object space is the spectrum of a field is flat and universally open. -/
@[stacks 06E0 "first assertion: the composition of a groupoid over a field"]
theorem isFlat_comp_of_objects_eq_spec_field {k : Type u} [Field k]
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (structureMap : Spec (.of k) ⟶ S) (hk : C.Contains (Spec (.of k)))
    (B : AlgebraicSpaces C S hS) (G : GroupoidInAlgebraicSpaces C S hS B)
    (objects_eq : G.objects =
      schemeSpace (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS))) :
    Space.IsFlat C S hS G.comp.hom ∧ Space.UniversallyOpen C S hS G.comp.hom :=
  ⟨isFlat_comp_of_isFlat_target G
      (isFlat_target_of_objects_eq_spec_field C S hS structureMap hk B G objects_eq),
    universallyOpen_comp_of_universallyOpen_target G
      (universallyOpen_target_of_objects_eq_spec_field C S hS structureMap hk B G objects_eq)⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
