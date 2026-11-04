module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Reduced
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ProperFlatGeomReduced

/-!
# The Stein image of a finite étale cover of a proper flat family

Let `f : X ⟶ S` be a proper, flat morphism of finite presentation with geometrically reduced
fibres and let `v : W ⟶ X` be finite étale. The composite `W ⟶ S` is again proper, flat and of
finite presentation, and it still has geometrically reduced fibres, so the second factor of its
Stein factorization is a finite étale cover `T ⟶ S` of the base. The first factor `W ⟶ T`
together with `v` gives a canonical morphism

```
W ⟶ T ×_S X
```

over `X`, and that morphism is itself finite étale. These are the data out of which a finite
étale cover of `X` is recognised as the base change of a finite étale cover of `S`.

## Main definitions

* `AlgebraicGeometry.steinImage`: the finite étale cover `T ⟶ S` of the base.
* `AlgebraicGeometry.steinComparison`: the canonical morphism `W ⟶ T ×_S X` over `X`.

## Main results

* `AlgebraicGeometry.isReduced_of_smooth_of_isReduced` and
  `AlgebraicGeometry.geometricallyReduced_comp_etale`: geometrically reduced fibres are inherited
  by the composite of an étale morphism with a morphism having geometrically reduced fibres.
* `AlgebraicGeometry.steinComparison_comp_snd` and `AlgebraicGeometry.steinComparison_comp_fst`:
  the two components of the comparison morphism.
* `AlgebraicGeometry.finiteEtale_steinComparison`: the comparison morphism is finite étale.

## References

* [Stacks Project, Tag 0BUN](https://stacks.math.columbia.edu/tag/0BUN)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 034E](https://stacks.math.columbia.edu/tag/034E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Geometrically reduced fibres along an étale morphism -/

/-- The source of a smooth morphism to a reduced scheme is reduced: reducedness is local for the
smooth topology, and a smooth morphism together with the identity of the target is a smooth cover
of the target. -/
theorem isReduced_of_smooth_of_isReduced {W Z : Scheme.{u}} (g : W ⟶ Z)
    [Smooth g] [IsReduced Z] : IsReduced W := by
  have : ObjectProperty.IsLocal (fun T : Scheme.{u} ↦ IsReduced T)
      (Scheme.precoverage @Smooth) := AlgebraicGeometry.isReduced_isLocal_smooth
  let V : Bool → Scheme.{u} := fun b ↦ match b with | true => W | false => Z
  let q : ∀ b, V b ⟶ Z := fun b ↦ match b with | true => g | false => 𝟙 Z
  have hq : Presieve.ofArrows V q ∈ Scheme.precoverage @Smooth Z := by
    rw [Scheme.ofArrows_mem_precoverage_iff (P := @Smooth)]
    refine ⟨fun z ↦ ⟨false, z, by simp [q, V]⟩, fun b ↦ ?_⟩
    cases b <;> infer_instance
  exact ObjectProperty.IsLocal.component (P := fun T : Scheme.{u} ↦ IsReduced T)
    hq g (Presieve.ofArrows.mk (Y := V) (f := q) true) inferInstance

/-- Composing an étale morphism with a morphism having geometrically reduced fibres again gives a
morphism with geometrically reduced fibres: a geometric fibre of the composite is the base change
along an étale morphism of the corresponding geometric fibre of the second morphism, hence is
reduced. -/
theorem geometricallyReduced_comp_etale {W X S : Scheme.{u}} (e : W ⟶ X) (f : X ⟶ S)
    [Etale e] [GeometricallyReduced f] : GeometricallyReduced (e ≫ f) := by
  rw [GeometricallyReduced.eq_geometrically, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  have : IsReduced (pullback f y) :=
    GeometricallyReduced.geometrically_isReduced (f := f) y
      (pullback.fst f y) (pullback.snd f y) (.of_hasPullback _ _)
  exact ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} ↦ IsReduced Z)
    (pullbackRightPullbackFstIso f y e)
    (isReduced_of_smooth_of_isReduced (pullback.snd e (pullback.fst f y)))

/-! ### The Stein image of a finite étale cover -/

variable {W X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyReduced f]
  (hfp : FinitePresentation f) (v : W ⟶ X) [IsFinite v] [Etale v]

omit [Flat f] [GeometricallyReduced f] in
include hfp in
/-- The composite of a finite étale morphism with a morphism of finite presentation is of finite
presentation. -/
theorem finitePresentation_comp_of_finiteEtale : FinitePresentation (v ≫ f) :=
  let : LocallyOfFinitePresentation f := hfp.1
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- **The Stein image of a finite étale cover.** For `f : X ⟶ S` proper, flat, of finite
presentation with geometrically reduced fibres and `v : W ⟶ X` finite étale, the second factor of
the Stein factorization of `v ≫ f` is a finite étale cover of `S`. -/
def steinImage : FiniteEtaleOver S :=
  letI : GeometricallyReduced (v ≫ f) := geometricallyReduced_comp_etale v f
  MorphismProperty.Over.mk ⊤ (v ≫ f).fromNormalization
    ⟨Stacks.SteinFactorization.isFinite_fromNormalization_of_properFlat (v ≫ f)
        (finitePresentation_comp_of_finiteEtale f hfp v),
      Stacks.SteinFactorization.etale_fromNormalization_of_properFlat (v ≫ f)
        (finitePresentation_comp_of_finiteEtale f hfp v)⟩

/-- The structure morphism `T ⟶ S` of the Stein image `T` is the second factor of the Stein
factorization of `v ≫ f`. -/
@[simp]
theorem steinImage_hom : (steinImage f hfp v).hom = (v ≫ f).fromNormalization := rfl

/-- **The comparison morphism to the base change of the Stein image.** The first factor of the
Stein factorization of `v ≫ f` together with `v` itself determines a morphism `W ⟶ T ×_S X`,
where `T` is the Stein image. -/
def steinComparison : W ⟶ pullback (steinImage f hfp v).hom f :=
  pullback.lift (v ≫ f).toNormalization v
    (Stacks.SteinFactorization.toNormalization_fromNormalization (v ≫ f))

/-- The comparison morphism `W ⟶ T ×_S X` followed by the projection `T ×_S X ⟶ X` is `v`. -/
@[reassoc (attr := simp)]
theorem steinComparison_comp_snd :
    steinComparison f hfp v ≫ pullback.snd (steinImage f hfp v).hom f = v :=
  pullback.lift_snd _ _ _

/-- The comparison morphism `W ⟶ T ×_S X` followed by the projection `T ×_S X ⟶ T` is the first
factor of the Stein factorization of `v ≫ f`. -/
@[reassoc (attr := simp)]
theorem steinComparison_comp_fst :
    steinComparison f hfp v ≫ pullback.fst (steinImage f hfp v).hom f =
      (v ≫ f).toNormalization :=
  pullback.lift_fst _ _ _

/-- **The comparison morphism is finite étale.** Both `v` and the base change `T ×_S X ⟶ X` of
the Stein image are finite étale, and a morphism whose composite with a finite étale morphism is
finite étale is itself finite étale. -/
theorem finiteEtale_steinComparison : finiteEtale (steinComparison f hfp v) := by
  have hs : finiteEtale (pullback.snd (steinImage f hfp v).hom f) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) (steinImage f hfp v).prop
  have hc : finiteEtale (steinComparison f hfp v ≫ pullback.snd (steinImage f hfp v).hom f) := by
    rw [steinComparison_comp_snd]
    exact ⟨inferInstance, inferInstance⟩
  have := hs.1
  have := hs.2
  have := hc.1
  have := hc.2
  exact ⟨IsFinite.of_comp _ (pullback.snd (steinImage f hfp v).hom f),
    Etale.of_comp _ (pullback.snd (steinImage f hfp v).hom f)⟩

end AlgebraicGeometry

end
