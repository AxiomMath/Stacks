module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingChartExistence
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The unit of the gluing adjunction of Tag 07VY (Tag 07W0) and the flat equivalence (Tag 07W3)

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`, `f : X ⟶ Y` an affine morphism
and `Y' = Y ⨿_X X'`.  [Stacks Project, Tag 07W0] says that the composite `F ∘ G` of the gluing
functor and the base change functor of [Stacks Project, Tag 07VY] is isomorphic to the identity.
This file proves it given that charts lift across thickenings, together with the final assertion
of [Stacks Project, Tag 07W3].

## Main results

* `CategoryTheory.PushoutGluing.isIso_adjunction_unit_app_of_isPullback`: in any category, the
  unit of the gluing adjunction is invertible at a triple whose two pieces are the base changes
  of its glued object.
* `AlgebraicGeometry.Space.isIso_pushoutGluingAdjunction_unit`: Tag 07W0, given that charts lift
  across thickenings.
* `AlgebraicGeometry.Space.pushoutFlatEquivalence`: the final assertion of
  [Stacks Project, Tag 07W3], the equivalence between flat triples and algebraic spaces flat
  over the pushout, given that charts lift across thickenings.

## References

* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07VY](https://stacks.math.columbia.edu/tag/07VY)
* [Stacks Project, Tag 07VZ](https://stacks.math.columbia.edu/tag/07VZ)
* [Stacks Project, Tag 07W0](https://stacks.math.columbia.edu/tag/07W0)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.PushoutGluing

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- **The unit of the gluing adjunction at a triple recovered by base change.**  If the two
pieces `V` and `U'` of a triple are the base changes of its glued object `G(V, U', φ)` along
`Y ⟶ Y'` and `X' ⟶ Y'`, then the unit `(V, U', φ) ⟶ F(G(V, U', φ))` is an isomorphism. -/
theorem isIso_adjunction_unit_app_of_isPullback {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    (T : GluingData i f)
    (hV : IsPullback (pushout.inr (pullback.fst T.obj.right.hom i) (sourceMap i f T))
      T.obj.left.hom ((gluingFunctor i f w hpo).obj T).hom b)
    (hU : IsPullback (pushout.inl (pullback.fst T.obj.right.hom i) (sourceMap i f T))
      T.obj.right.hom ((gluingFunctor i f w hpo).obj T).hom a) :
    IsIso ((adjunction i f w hpo).unit.app T) := by
  let := hpo T
  let η := (adjunction i f w hpo).unit.app T
  have : IsIso η.hom.left := by
    have e : (Over.forget _).map η.hom.left = hV.isoPullback.hom :=
      pullback.hom_ext
        (((gluingToPair_left_comp_fst i f w hpo (𝟙 _)).trans (Category.comp_id _)).trans
          hV.isoPullback_hom_fst.symm)
        ((gluingToPair_left_comp_snd i f w hpo (𝟙 _)).trans hV.isoPullback_hom_snd.symm)
    have : IsIso ((Over.forget _).map η.hom.left) := by rw [e]; exact Iso.isIso_hom _
    exact isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso η.hom.right := by
    have e : (Over.forget _).map η.hom.right = hU.isoPullback.hom :=
      pullback.hom_ext
        (((gluingToPair_right_comp_fst i f w hpo (𝟙 _)).trans (Category.comp_id _)).trans
          hU.isoPullback_hom_fst.symm)
        ((gluingToPair_right_comp_snd i f w hpo (𝟙 _)).trans hU.isoPullback_hom_snd.symm)
    have : IsIso ((Over.forget _).map η.hom.right) := by rw [e]; exact Iso.isIso_hom _
    exact isIso_of_reflects_iso _ (Over.forget _)
  exact (ObjectProperty.isIso_hom_iff η).1
    (Comma.isoMk (asIso η.hom.left) (asIso η.hom.right) η.hom.w).isIso_hom

end CategoryTheory.PushoutGluing

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (hlift : HasEtaleChartLifts B S hS) (hatlas : HasThickeningAffineAtlases B S hS)
  {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickeningHom B S hS i)
  (hf : IsAffineHom B S hS f.hom)

include hlift

/-- **[Stacks Project, Tag 07W0], given that charts lift across thickenings.**  Let
`i : X ⟶ X'` be a thickening of algebraic spaces over `S` and `f : X ⟶ Y` an affine morphism,
and let `G ⊣ F` be the gluing adjunction of [Stacks Project, Tag 07VY].  Its unit
`𝟭 ⟶ G ⋙ F` is an isomorphism: `F ∘ G` is isomorphic to the identity of the category of
triples. -/
theorem isIso_pushoutGluingAdjunction_unit :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    IsIso (pushoutGluingAdjunction B S hS hatlas i f hi hf).unit := by
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  suffices h : ∀ T, IsIso ((pushoutGluingAdjunction B S hS hatlas i f hi hf).unit.app T) from
    NatIso.isIso_of_isIso_app _
  intro T
  let := pushoutGluingHasPushout B S hS hatlas i f hi hf T
  have hinl := CategoryTheory.PushoutGluing.gluedObj_inl i f
    (pushout.condition (f := i) (g := f)) T
  have hinr := CategoryTheory.PushoutGluing.gluedObj_inr i f
    (pushout.condition (f := i) (g := f)) T
  obtain ⟨D, hV, hU, hY, hX⟩ := exists_thickeningAffineGluingChart_of_chartLift B S hS hlift hi
    hf (IsPushout.of_hasPushout i f) (IsPullback.of_hasPullback T.obj.right.hom i)
    (CategoryTheory.PushoutGluing.sourceMap_isPullback i f T)
    (IsPushout.of_hasPushout (pullback.fst T.obj.right.hom i)
      (CategoryTheory.PushoutGluing.sourceMap i f T)) hinl hinr
  exact CategoryTheory.PushoutGluing.isIso_adjunction_unit_app_of_isPullback i f
    (pushout.condition (f := i) (g := f))
    (pushoutGluingHasPushout B S hS hatlas i f hi hf) T
    (IsPullback.of_map_of_faithful (ObjectProperty.ι _) (D.isPullback_v hinr hV hY).flip)
    (IsPullback.of_map_of_faithful (ObjectProperty.ι _) (D.isPullback_u' hinl hU hX).flip)

/-- **The flat equivalence of [Stacks Project, Tag 07W3], given that charts lift across
thickenings.**  The gluing functor `G` and the base-change functor `F` of
[Stacks Project, Tag 07VY] restrict to mutually quasi-inverse functors between the triples
`(V, U', φ)` with `V ⟶ Y` and `U' ⟶ X'` flat and the algebraic spaces flat over
`Y' = Y ⨿_X X'`. -/
noncomputable def pushoutFlatEquivalence :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    ObjectProperty.FullSubcategory (fun T : pushoutGluingData B S hS i f =>
        IsFlat B S hS T.obj.left.hom.hom ∧ IsFlat B S hS T.obj.right.hom.hom) ≌
      ObjectProperty.FullSubcategory (fun Z : Over (pushout i f) => IsFlat B S hS Z.hom.hom) :=
  letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  haveI := isIso_pushoutGluingAdjunction_unit hlift hatlas i f hi hf
  CategoryTheory.Equivalence.mk
    (ObjectProperty.lift (fun Z : Over (pushout i f) => IsFlat B S hS Z.hom.hom)
      (ObjectProperty.ι _ ⋙ pushoutGluingFunctor B S hS hatlas i f hi hf)
      fun T => (isFlat_pushoutGluingFunctor_obj_iff hlift hatlas i f hi hf T.obj).2 T.property)
    (ObjectProperty.lift (fun T : pushoutGluingData B S hS i f =>
        IsFlat B S hS T.obj.left.hom.hom ∧ IsFlat B S hS T.obj.right.hom.hom)
      (ObjectProperty.ι _ ⋙ pushoutBaseChangeFunctor B S hS hatlas i f hi hf)
      fun Z => ⟨(isFlat_isStableUnderBaseChange B S hS).of_isPullback
          (IsPullback.of_hasPullback Z.obj.hom (pushout.inr i f)) Z.property,
        (isFlat_isStableUnderBaseChange B S hS).of_isPullback
          (IsPullback.of_hasPullback Z.obj.hom (pushout.inl i f)) Z.property⟩)
    (NatIso.ofComponents
      (fun T => ObjectProperty.isoMk _
        (asIso ((pushoutGluingAdjunction B S hS hatlas i f hi hf).unit.app T.obj)))
      fun g => ObjectProperty.hom_ext _
        ((pushoutGluingAdjunction B S hS hatlas i f hi hf).unit.naturality g.hom))
    (NatIso.ofComponents
      (fun Z => ObjectProperty.isoMk _
        (haveI := isIso_pushoutGluingAdjunction_counit_of_isFlat B S hS hatlas i f hi hf
          Z.obj Z.property
        asIso ((pushoutGluingAdjunction B S hS hatlas i f hi hf).counit.app Z.obj)))
      fun g => ObjectProperty.hom_ext _
        ((pushoutGluingAdjunction B S hS hatlas i f hi hf).counit.naturality g.hom))

end AlgebraicGeometry.Space

end
