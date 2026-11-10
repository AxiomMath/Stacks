module

public import StacksFrontier.RingTheory.ChartedFunctor.Tangent
public import StacksFrontier.RingTheory.Derivation.TensorProjective

/-!
# Base change of the tangent of a charted functor

Let `F` be a functor on bounded `R`-algebras with an étale chart, let `f : P ⟶ P'` carry an
ideal `J` into an ideal `J'`, let `x` be a chart point of `F` over `P ⧸ J` and `x'` its image
over `P' ⧸ J'`, and let `g : N → P'` be an algebra map. The tangent maps along `f`, linearised
along `g`,
```
Tan(x) ⊗_R N ⟶ Tan(x'),   w ⊗ n ↦ g(n) · f_*(w),
```
form a bijection as soon as the corresponding map of conormal modules
`J/J² ⊗_R N ⟶ J'/J'²`, `m ⊗ n ↦ g(n) · f(m)`, is one. The chart identifies tangents with
derivations of the chart algebra `C` along the chart point, the derivations of a smooth algebra
commute with tensor products (`Derivation.bijective_alongRTensorHom`), and the tangent map is
composition with the map of conormal modules.

## Main definitions

* `Stacks.ChartedFunctor.Tan.linMap`: the linearised tangent map.
* `Stacks.ChartedFunctor.conormalLinMap`: the linearised map of conormal modules.

## Main results

* `Stacks.ChartedFunctor.Tan.bijective_linMap`: **base change of the tangent.**

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal TensorProduct

universe u

namespace Stacks.ChartedFunctor

variable {R : Type u} [CommRing R] {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
  {F : BoundedAlg R κ ⥤ Type u}

variable {P P' : BoundedAlg R κ} {J : Ideal P.obj} {J' : Ideal P'.obj} (f : P ⟶ P')
  (hJ : J ≤ J'.comap (BoundedAlg.toAlgHom f)) {x : F.obj (quot P J)} {x' : F.obj (quot P' J')}
  (hx : F.map (quotMap f hJ) x = x')

/-- The chart description of the image of a tangent vector is the image of its chart
description under the map of conormal modules. -/
lemma Tan.chartVec_map (c : EtaleChart F) {ρ₀ : c.C ⟶ (quot P J).obj}
    (h : c.α.app (quot P J) ρ₀ = x) (h' : c.α.app (quot P' J') (ρ₀ ≫ (quotMap f hJ).hom) = x')
    (w : Tan F P J x) (y : c.C) :
    Tan.chartVec c h' (Tan.map f hJ hx w) y =
      J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ (Tan.chartVec c h w y) := by
  have e : c.chartLift (isSqZeroExt_sqZeroFst P' J') h' (Tan.map f hJ hx w) =
      c.chartLift (isSqZeroExt_sqZeroFst P J) h w ≫ (sqZeroMap f hJ).hom := by
    refine c.chartLift_eq _ h' _ _ ?_ ?_
    · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, sqZeroMap_fst,
        ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, c.chartLift_comp]
    · rw [← c.map_α, c.α_chartLift]
      rfl
  simp only [Tan.chartVec, e]
  rfl

variable (N : Type u) [CommRing N] [Algebra R N] (g : N →ₐ[R] P'.obj)

/-- The linearised map of conormal modules, `m ⊗ n ↦ g(n) · f(m)`. -/
def conormalLinMap : J.Cotangent ⊗[R] N →ₗ[R] J'.Cotangent :=
  TensorProduct.lift
    { toFun := fun m =>
        { toFun := fun n => Ideal.Quotient.mkₐ R J' (g n) •
            J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ m
          map_add' := fun n n' => by rw [_root_.map_add, _root_.map_add, add_smul]
          map_smul' := fun r n => by
            rw [_root_.map_smul, _root_.map_smul, RingHom.id_apply, smul_assoc] }
      map_add' := fun m m' => by ext n; simp [smul_add]
      map_smul' := fun r m => by
        ext n
        simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul, LinearMap.smul_apply,
          RingHom.id_apply]
        rw [smul_comm] }

omit [Fact (ℵ₀ < κ)] in
/-- The linearised map of conormal modules sends `m ⊗ n` to `g(n) · f(m)`. -/
@[simp]
lemma conormalLinMap_tmul (m : J.Cotangent) (n : N) :
    conormalLinMap f hJ N g (m ⊗ₜ n) =
      Ideal.Quotient.mkₐ R J' (g n) • J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ m := rfl

variable [Fact (HasChartPoint F x)] [Fact (HasChartPoint F x')]

/-- **The linearised tangent map**, `w ⊗ n ↦ g(n) · f_*(w)`. -/
def Tan.linMap : Tan F P J x ⊗[R] N →ₗ[R] Tan F P' J' x' :=
  TensorProduct.lift
    { toFun := fun w =>
        { toFun := fun n => Ideal.Quotient.mkₐ R J' (g n) • Tan.map f hJ hx w
          map_add' := fun n n' => by rw [_root_.map_add, _root_.map_add, add_smul]
          map_smul' := fun r n => by
            rw [_root_.map_smul, _root_.map_smul, RingHom.id_apply, smul_assoc] }
      map_add' := fun w w' => by
        ext n
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
        rw [Tan.map_add f hJ hx Tan.someChart Tan.someChartPoint_spec, smul_add]
      map_smul' := fun r w => by
        ext n
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
        rw [← Tan.mapₗ_apply f hJ hx, _root_.map_smul, Tan.mapₗ_apply, smul_comm] }

/-- The linearised tangent map sends `w ⊗ n` to `g(n) · f_*(w)`. -/
@[simp]
lemma Tan.linMap_tmul (w : Tan F P J x) (n : N) :
    Tan.linMap f hJ hx N g (w ⊗ₜ n) = Ideal.Quotient.mkₐ R J' (g n) • Tan.map f hJ hx w := rfl

/-- The chart description of a tangent vector, as a derivation along the chart point. -/
def Tan.chartAlong (c : EtaleChart F) {ρ₀ : c.C ⟶ (quot P J).obj}
    (h : c.α.app (quot P J) ρ₀ = x) : Tan F P J x →ₗ[R] Derivation.along ρ₀.hom J.Cotangent where
  toFun w := ⟨⟨⟨Tan.chartVec c h w, Tan.chartVec_add_apply c h w⟩,
    Tan.chartVec_smul_apply c h w⟩, Tan.chartVec_mul_apply c h w⟩
  map_add' w w' := Subtype.ext (LinearMap.ext fun y => congrFun (Tan.chartVec_add c h w w') y)
  map_smul' r w := Subtype.ext (LinearMap.ext fun y => congrFun (Tan.chartVec_rsmul c h r w) y)

/-- The derivation `Tan.chartAlong c h w` is the chart description `Tan.chartVec c h w`. -/
@[simp]
lemma Tan.chartAlong_apply (c : EtaleChart F) {ρ₀ : c.C ⟶ (quot P J).obj}
    (h : c.α.app (quot P J) ρ₀ = x) (w : Tan F P J x) (y : c.C) :
    (Tan.chartAlong c h w).1 y = Tan.chartVec c h w y := rfl

/-- Two derivations along an algebra map are equal iff they agree at every point. -/
private lemma along_eq_iff {C A M : Type*} [CommRing C] [Algebra R C] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    {ρ : C →ₐ[R] A} {d d' : Derivation.along ρ M} : d = d' ↔ ∀ y, d.1 y = d'.1 y :=
  ⟨fun h _ => by rw [h], fun h => Subtype.ext (LinearMap.ext h)⟩

/-- The chart description `Tan.chartAlong c h` of tangent vectors as derivations along the
chart point is bijective. -/
lemma Tan.bijective_chartAlong (c : EtaleChart F) {ρ₀ : c.C ⟶ (quot P J).obj}
    (h : c.α.app (quot P J) ρ₀ = x) : Function.Bijective (Tan.chartAlong c h) := by
  refine ⟨fun w w' hw => Tan.chartVec_injective c h ?_, fun d => ?_⟩
  · exact funext fun y => along_eq_iff.1 hw y
  · obtain ⟨w, hw⟩ := Tan.exists_chartVec_eq c h d.1 d.2
    exact ⟨w, along_eq_iff.2 fun y => congrFun hw y⟩

/-- **Base change of the tangent.** If the linearised map of conormal modules is bijective, so
is the linearised tangent map. -/
theorem Tan.bijective_linMap (hμ : Function.Bijective (conormalLinMap f hJ N g)) :
    Function.Bijective (Tan.linMap f hJ hx N g) := by
  let c := Tan.someChart (x := x)
  let ρ₀ := Tan.someChartPoint (x := x)
  have h : c.α.app (quot P J) ρ₀ = x := Tan.someChartPoint_spec
  have h' : c.α.app (quot P' J') (ρ₀ ≫ (quotMap f hJ).hom) = x' := by rw [← c.map_α, h, hx]
  have := c.smooth
  let μ := LinearEquiv.ofBijective (conormalLinMap f hJ N g) hμ
  have hμs : ∀ (a : P.obj ⧸ J) (t : J.Cotangent ⊗[R] N),
      μ (a • t) = Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ a • μ t := fun a t => by
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => rw [smul_add, _root_.map_add, _root_.map_add, hs, ht, smul_add]
    | tmul m n =>
      change conormalLinMap f hJ N g ((a • m) ⊗ₜ n) = _ • conormalLinMap f hJ N g (m ⊗ₜ n)
      rw [conormalLinMap_tmul, conormalLinMap_tmul, mapCotangent_smul, smul_comm]
  let comp : Derivation.along ρ₀.hom (J.Cotangent ⊗[R] N) →ₗ[R]
      Derivation.along (ρ₀ ≫ (quotMap f hJ).hom).hom J'.Cotangent :=
    { toFun := fun d => ⟨μ.toLinearMap ∘ₗ d.1, fun y y' => by
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
        rw [d.2 y y', _root_.map_add, hμs, hμs]
        rfl⟩
      map_add' := fun d d' => by ext y; simp
      map_smul' := fun r d => by ext y; simp }
  have hcomp : Function.Bijective comp := by
    refine ⟨fun d d' hd => ?_, fun d => ?_⟩
    · exact along_eq_iff.2 fun y => μ.injective (along_eq_iff.1 hd y)
    · refine ⟨⟨μ.symm.toLinearMap ∘ₗ d.1, fun y y' => ?_⟩, ?_⟩
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
        apply μ.injective
        rw [μ.apply_symm_apply, _root_.map_add, hμs, hμs, μ.apply_symm_apply, μ.apply_symm_apply]
        exact d.2 y y'
      · exact along_eq_iff.2 fun y => μ.apply_symm_apply (d.1 y)
  have key : (Tan.chartAlong c h') ∘ₗ (Tan.linMap f hJ hx N g) =
      comp ∘ₗ (Derivation.alongRTensorHom ρ₀.hom J.Cotangent N) ∘ₗ
        (LinearMap.rTensor N (Tan.chartAlong c h)) := by
    refine TensorProduct.ext' fun w n => along_eq_iff.2 fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul]
    rw [Tan.chartAlong_apply, Tan.linMap_tmul, Tan.chartVec_smul, Pi.smul_apply,
      Tan.chartVec_map f hJ hx c h h']
    rfl
  rw [← Function.Bijective.of_comp_iff' (Tan.bijective_chartAlong c h'), ← LinearMap.coe_comp,
    key]
  exact hcomp.comp ((Derivation.bijective_alongRTensorHom ρ₀.hom J.Cotangent N).comp
    (LinearEquiv.rTensor N (LinearEquiv.ofBijective _ (Tan.bijective_chartAlong c h))).bijective)

end Stacks.ChartedFunctor

end
