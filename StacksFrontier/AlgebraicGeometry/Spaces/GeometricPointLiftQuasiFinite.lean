module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange

/-!
# Lifting a geometric point along a morphism quasi-finite at a point

Let `p : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `ȳ` be a geometric point of `Y` and let `x` be a point of `|X|` over the image of `ȳ`
at which `p` is quasi-finite.  Then `ȳ` lifts to a geometric point `x̄` of `X` over `x`, over the
same algebraically closed field: `p ∘ x̄ = ȳ`.

## Main results

* `AlgebraicGeometry.isClosed_singleton_of_quasiFiniteAt`: a point of a scheme locally of
  finite type over a field at which the structure morphism is quasi-finite is closed.
* `AlgebraicGeometry.Space.exists_geometricPoint_lift_of_isQuasiFiniteAt`: the lift.

## References

* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 01TF](https://stacks.math.columbia.edu/tag/01TF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A quasi-finite point over a field is closed.** Let `π : W ⟶ Spec K` be locally of finite
type, with `K` a field, and let `w` be a point at which `π` is quasi-finite.  Then `w` is a
closed point of `W`. -/
theorem isClosed_singleton_of_quasiFiniteAt {W : Scheme.{u}} {K : Type u} [Field K]
    (π : W ⟶ Spec (.of K)) [LocallyOfFiniteType π] {w : W} (hw : π.QuasiFiniteAt w) :
    IsClosed ({w} : Set W) := by
  have h := (hw.isClopen_singleton_asFiber).1
  rw [← (π.fiberHomeo (π w)).isClosed_image, Set.image_singleton] at h
  have hfib : π ⁻¹' {π w} = Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hclosed : IsClosed (π ⁻¹' {π w}) := hfib ▸ isClosed_univ
  have e : π.fiberHomeo (π w) (π.asFiber w) = ⟨w, rfl⟩ := by
    simp only [Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
  have := hclosed.isClosedMap_subtype_val _ h
  rwa [e, Set.image_singleton] at this

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A geometric point lifts along a morphism quasi-finite at a point over it, without changing
its field.** Let `p : X ⟶ Y` be a morphism of algebraic spaces over `S`, locally of finite type,
let `ȳ` be a geometric point of `Y` and let `x` be a point of `|X|` over the image of `ȳ` at which
`p` is quasi-finite.  Then there is a geometric point `x̄` of `X` over `x` with `p ∘ x̄ = ȳ`. -/
theorem exists_geometricPoint_lift_of_isQuasiFiniteAt {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (p : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS p) (ybar : GeometricPoint B S hS Y)
    (x : points B S hS X) (hx : pointsMap B S hS X p x = ybar.image)
    (hqf : IsQuasiFiniteAt B S hS p x) :
    ∃ xbar : GeometricPoint B S hS X, xbar.image = x ∧ geometricPointMap p xbar = ybar := by
  have : IsAlgClosed ybar.val.carrier := ybar.property
  set O := ybar.val.siteObject
  set a : yoneda.obj O ⟶ Y := yonedaEquiv.symm ybar.val.value
  have haone : a.app (Opposite.op O) (𝟙 O) = ybar.val.value :=
    Equiv.apply_symm_apply yonedaEquiv _
  have hpb := IsPullback.of_hasPullback p a
  set pt0 : FieldValuedPoint B S hS (yoneda.obj O) :=
    { carrier := ybar.val.carrier
      contained := ybar.val.contained
      toBase := ybar.val.toBase
      value := 𝟙 O }
  have hpt0 : FieldValuedPoint.map B S hS _ a pt0 = ybar.val :=
    congrArg (fun v : Y.obj (Opposite.op O) => { ybar.val with value := v }) haone
  have hapt : pointsMap B S hS _ a (pt0.class B S hS _) = ybar.image := by
    rw [pointsMap_class, hpt0]
  obtain ⟨x', hx'1, hx'2⟩ := exists_points_of_isPullback B S hS hpb
    x (pt0.class B S hS _) (hx.trans hapt.symm)
  have hO' : IsAlgebraicSpace B S hS (yoneda.obj O) := isAlgebraicSpace_yoneda B S hS O
  have hP : IsAlgebraicSpace B S hS (pullback p a) := isAlgebraicSpace_pullback B S hS p a hX hO' hY
  have hsndlft : IsLocallyOfFiniteType B S hS (pullback.snd p a) :=
    IsLocallyOfFiniteType.of_isPullback B S hS hpb.flip hX hY hlft
  have hsndqf : IsQuasiFiniteAt B S hS (pullback.snd p a) x' :=
    (isQuasiFiniteAt_iff_of_isPullback B S hS hpb.flip hX hY hO' hlft
      x').2 (hx'1 ▸ hqf)
  obtain ⟨W, c, -, hcE, w, hw⟩ := exists_affine_etale_chart_at_point B S hS _ hP x'
  obtain ⟨τ, hτ⟩ : ∃ τ : W ⟶ O, yoneda.map τ = c ≫ pullback.snd p a :=
    ⟨Yoneda.fullyFaithful.preimage _, Yoneda.fullyFaithful.map_preimage _⟩
  set T := BigFppfOver.toScheme B S hS
  have hτlft : LocallyOfFiniteType (T.map τ) :=
    locallyOfFiniteType_toScheme_map_of_chart B S hS hsndlft c hcE hτ
  set w₀ := pointsToScheme B S hS W w
  have hww₀ : (pointsEquivScheme B S hS W).symm w₀ = w := (Equiv.symm_apply_eq _).2 rfl
  have hτqf : AlgebraicGeometry.quasiFiniteAt (T.map τ) w₀ :=
    (quasiFiniteAt_toScheme_map_of_chart B S hS hP hsndlft c hcE hτ w₀).1
      (by rw [hww₀, hw]; exact hsndqf)
  let π : T.obj W ⟶ Spec (.of ybar.val.carrier) := T.map τ
  have : LocallyOfFiniteType π := hτlft
  have hclosed := isClosed_singleton_of_quasiFiniteAt π hτqf.2
  set σ : Spec (.of ybar.val.carrier) ⟶ T.obj W := pointOfClosedPoint π w₀ hclosed
  have hσ : σ ≫ π = 𝟙 _ := pointOfClosedPoint_comp π w₀ hclosed
  have hσw : σ (IsLocalRing.closedPoint ybar.val.carrier) = w₀ :=
    pointOfClosedPoint_apply π w₀ hclosed _
  obtain ⟨σl, hσl⟩ : ∃ σl : O.left ⟶ W.left, B.inclusion.map σl = σ :=
    ⟨B.inclusion.preimage σ, B.inclusion.map_preimage (X := O.left) (Y := W.left) σ⟩
  have hover : σl ≫ W.hom = O.hom := by
    refine B.inclusion.map_injective ?_
    calc B.inclusion.map (σl ≫ W.hom) = σ ≫ B.inclusion.map W.hom := by
          rw [Functor.map_comp, hσl]
      _ = σ ≫ B.inclusion.map (τ.left ≫ O.hom) := by rw [Over.w τ]
      _ = (σ ≫ π) ≫ B.inclusion.map O.hom := by
          rw [Functor.map_comp, Category.assoc]
          rfl
      _ = B.inclusion.map O.hom := by rw [hσ, Category.id_comp]
  set σ' : O ⟶ W := Over.homMk σl hover
  have hTσ' : T.map σ' = σ := hσl
  have hστ : σ' ≫ τ = 𝟙 O := T.map_injective (by rw [T.map_comp, hTσ', T.map_id]; exact hσ)
  set q : FieldValuedPoint B S hS (yoneda.obj W) :=
    { carrier := ybar.val.carrier
      contained := ybar.val.contained
      toBase := ybar.val.toBase
      value := σ' }
  refine ⟨⟨FieldValuedPoint.map B S hS _ (c ≫ pullback.fst p a) q, ybar.property⟩, ?_, ?_⟩
  · show (FieldValuedPoint.map B S hS _ (c ≫ pullback.fst p a) q).class B S hS X = x
    rw [← pointsMap_class, pointsMap_comp_apply]
    have hq : q.class B S hS (yoneda.obj W) = w := by
      refine injective_pointsToScheme B S hS W ?_
      rw [pointsToScheme_class]
      show T.map σ' (IsLocalRing.closedPoint ybar.val.carrier) = w₀
      rw [hTσ', hσw]
    rw [hq, hw, hx'1]
  · apply Subtype.ext
    have hv : p.app _ ((c ≫ pullback.fst p a).app _ σ') = ybar.val.value := by
      have h1 : c ≫ pullback.fst p a ≫ p = c ≫ pullback.snd p a ≫ a := by
        rw [pullback.condition]
      show (c ≫ pullback.fst p a ≫ p).app _ σ' = _
      rw [h1, ← Category.assoc, ← hτ]
      show a.app _ (σ' ≫ τ) = _
      rw [hστ]
      exact haone
    exact congrArg (fun v : Y.obj (Opposite.op O) => { ybar.val with value := v }) hv

end AlgebraicGeometry.Space
