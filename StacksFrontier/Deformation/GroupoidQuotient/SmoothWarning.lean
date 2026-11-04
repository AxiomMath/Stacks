module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.Basic
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# A smooth groupoid in functors with a non-smooth quotient category

Smoothness of a groupoid in functors is *not* the same as smoothness of its quotient category
over the base. This file exhibits a smooth groupoid in functors on the category of Artinian
local `ℚ`-algebras whose quotient category is not smooth over the base, which is the warning of
the source. What *is* equivalent to smoothness of the groupoid is smoothness of the quotient
*morphism* out of the category of elements of the object functor; that is already recorded by
`Deformation.isSmooth_iff_source` and `Deformation.source_isSmooth_iff_quotient`, and the tag is
claimed for them here rather than duplicated.

The counterexample is the groupoid with only identity arrows on the functor corepresented by
`ℚ[[x]]/(x²)`. Such a groupoid is smooth, because the source and target morphisms are the
identity. Its quotient category is the category of elements of that functor, and smoothness of
the projection to the base would produce, for the surjection `ℚ[[x]]/(x³) → ℚ[[x]]/(x²)`, a
section of that surjection — hence an element of `ℚ[[x]]/(x³)` squaring to zero and mapping to
the class of `x`, which does not exist.

## Main definitions

* `Deformation.quotientProjectionBasedFunctor`: the structure functor of a quotient category,
  regarded as a morphism to the identity category over the base.

## Main results

* `Deformation.smooth_groupoid_quotient_not_smooth`: a smooth groupoid in functors whose
  quotient category is not smooth over the base.

## Implementation notes

Smoothness of a category over the base means smoothness of its structure morphism, regarded as
a based functor to the identity category over the base; `quotientProjectionBasedFunctor` packages
the quotient projection in that form.

## References

* [Stacks Project, Tag 06KJ](https://stacks.math.columbia.edu/tag/06KJ)
-/

@[expose] public section

namespace Deformation

/-! ### The structure morphism of a quotient category -/

section
open CategoryTheory
universe u v w

/-- The structure morphism of a quotient category, as a based functor to the base. -/
public noncomputable def quotientProjectionBasedFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    BasedFunctor
      (BasedCategory.ofFunctor
        (Grothendieck.forget (evaluationFunctor G)))
      (BasedCategory.ofFunctor
        (𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k))) where
  toFunctor := Grothendieck.forget (evaluationFunctor G)
  w := Functor.comp_id _

end

/-! ### A smooth groupoid whose quotient category is not smooth -/

section
open CategoryTheory

universe z

private abbrev PowerSeriesQ := PowerSeries ℚ

private noncomputable def powerSeriesConstantCoeff : PowerSeriesQ →ₐ[ℚ] ℚ where
  toRingHom := PowerSeries.constantCoeff
  commutes' r := by simp

private noncomputable def powerSeriesComplete : CompleteLocalAlgCat.{0, 0, 0} ℚ ℚ where
  carrier := PowerSeriesQ
  completeLocal := {
    isNoetherian := inferInstance
    isLocal := inferInstance
    isComplete := by
      rw [PowerSeries.maximalIdeal_eq_span_X]
      infer_instance
  }
  residueEquiv := by
    let f := powerSeriesConstantCoeff
    have hf : Function.Surjective f := PowerSeries.constantCoeff_surj
    let _ : IsLocalHom f.toRingHom := IsLocalHom.of_surjective _ hf
    have hk : RingHom.ker f = IsLocalRing.maximalIdeal PowerSeriesQ :=
      IsLocalRing.ker_eq_maximalIdeal f.toRingHom hf
    exact (Ideal.quotientEquivAlgOfEq ℚ hk.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hf)

private noncomputable abbrev maximalIdealSq : Ideal PowerSeriesQ :=
  IsLocalRing.maximalIdeal PowerSeriesQ ^ 2
private noncomputable abbrev maximalIdealCube : Ideal PowerSeriesQ :=
  IsLocalRing.maximalIdeal PowerSeriesQ ^ 3
private abbrev TruncSq := PowerSeriesQ ⧸ maximalIdealSq
private abbrev TruncCube := PowerSeriesQ ⧸ maximalIdealCube

private lemma maximalIdealCube_le_sq : maximalIdealCube ≤ maximalIdealSq :=
  Ideal.pow_le_pow_right (by omega)

private lemma X_mem_maximalIdeal :
    (PowerSeries.X : PowerSeriesQ) ∈ IsLocalRing.maximalIdeal PowerSeriesQ := by
  rw [PowerSeries.maximalIdeal_eq_span_X]
  exact Ideal.subset_span (by simp)

private noncomputable def truncCubeToSq : TruncCube →ₐ[ℚ] TruncSq :=
  Ideal.Quotient.factorₐ ℚ maximalIdealCube_le_sq

private noncomputable def xClassSq : TruncSq :=
  Ideal.Quotient.mk maximalIdealSq (PowerSeries.X : PowerSeriesQ)

private lemma X_sq_not_mem_maximalIdealCube :
    (PowerSeries.X : PowerSeriesQ) ^ 2 ∉ maximalIdealCube := by
  rw [maximalIdealCube, PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  intro hdiv
  have hcoeff := (PowerSeries.X_pow_dvd_iff.mp hdiv) 2 (by omega)
  norm_num [PowerSeries.coeff_X_pow] at hcoeff

private lemma no_squarezero_lift (b : TruncCube) (hb : truncCubeToSq b = xClassSq) :
    b ^ 2 ≠ 0 := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hmk : Ideal.Quotient.mk maximalIdealSq r =
      Ideal.Quotient.mk maximalIdealSq (PowerSeries.X : PowerSeriesQ) := by
    simpa [xClassSq, truncCubeToSq, Ideal.Quotient.factorₐ_apply_mk] using hb
  have hz : r - (PowerSeries.X : PowerSeriesQ) ∈ maximalIdealSq := Ideal.Quotient.eq.mp hmk
  have hdiff : r ^ 2 - (PowerSeries.X : PowerSeriesQ) ^ 2 ∈ maximalIdealCube := by
    let m : Ideal PowerSeriesQ := IsLocalRing.maximalIdeal PowerSeriesQ
    have hx : (PowerSeries.X : PowerSeriesQ) ∈ m := X_mem_maximalIdeal
    have hrm : r ∈ m := by
      convert m.add_mem hx (Ideal.pow_le_self (by norm_num : 1 + 1 ≠ 0) hz) using 1
      ring
    change r ^ 2 - (PowerSeries.X : PowerSeriesQ) ^ 2 ∈ m ^ 3
    rw [show r ^ 2 - (PowerSeries.X : PowerSeriesQ) ^ 2 =
      (r - (PowerSeries.X : PowerSeriesQ)) * (r + (PowerSeries.X : PowerSeriesQ)) by ring]
    simpa [pow_succ, mul_comm] using
      (Ideal.mul_mem_mul hz (m.add_mem hrm hx))
  intro h
  have hXzero : Ideal.Quotient.mk maximalIdealCube
      ((PowerSeries.X : PowerSeriesQ) ^ 2) = 0 := by
    rw [← Ideal.Quotient.eq.mpr hdiff]
    simpa only [map_pow] using h
  exact X_sq_not_mem_maximalIdealCube (Ideal.Quotient.eq_zero_iff_mem.mp hXzero)

private lemma xClassSq_sq : xClassSq ^ 2 = 0 := by
  rw [xClassSq, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow X_mem_maximalIdeal 2

private abbrev ArtQ := ArtinianLocalAlgCat.{0, 0, 0} ℚ ℚ

private noncomputable def truncSqArt : ArtQ := AdicTruncation.obj powerSeriesComplete 1
private noncomputable def truncCubeArt : ArtQ := AdicTruncation.obj powerSeriesComplete 2
private noncomputable def truncCubeToSqArt : truncCubeArt ⟶ truncSqArt :=
  AdicTruncation.transition powerSeriesComplete 1
private noncomputable def xClassSqArt : truncSqArt :=
  Ideal.Quotient.mk maximalIdealSq (PowerSeries.X : PowerSeriesQ)

private lemma xClassSqArt_sq : xClassSqArt ^ 2 = 0 := xClassSq_sq

private theorem discreteHom_ext {α : Type*} {a b : α}
    (f g : Discrete.Hom a b) : f = g := by
  rcases f with ⟨hf⟩
  rcases g with ⟨hg⟩
  rfl

private noncomputable def corepresented (A₀ : ArtQ) : Functor.{0, z} ArtQ (Type z) where
  obj A := ULift.{z, 0} (A₀ ⟶ A)
  map {X Y} f := ↾ (fun (x : ULift.{z, 0} (A₀ ⟶ X)) => ULift.up (x.down ≫ f))
  map_id A := by ext x; simp
  map_comp f g := by ext x; simp [Category.assoc]

private noncomputable def discreteGroupoid (F : Functor.{0, z} ArtQ (Type z)) :
    GroupoidInFunctors.{1, 0, z} ArtQ where
  objects := F
  arrows := F
  source := 𝟙 F
  target := 𝟙 F
  comp := {
    app := fun A => ↾ (fun (p : (composableArrows F F (𝟙 F) (𝟙 F)).obj A) => p.1.2)
    naturality := by intro A B f; ext p; rfl
  }
  pointwiseGroupoid := by
    intro A
    let _ : Groupoid (F.obj A) := {
      Hom := fun x y => Discrete.Hom x y
      id _ := ⟨rfl⟩
      comp f g := ⟨f.eq.trans g.eq⟩
      id_comp := by cat_disch
      comp_id := by cat_disch
      assoc := by cat_disch
      inv f := ⟨f.eq.symm⟩
      inv_comp := by cat_disch
      comp_inv := by cat_disch
    }
    refine ⟨{
      groupoid := inferInstance
      arrowEquiv := fun x y => {
        toFun := fun f => ⟨x, rfl, f.eq⟩
        invFun := fun a => ⟨a.2.1.symm.trans a.2.2⟩
        left_inv := fun f => discreteHom_ext (a := x) (b := y) _ f
        right_inv := fun a => Subtype.ext a.2.1.symm
      }
      comp_eq := by intros; rfl
    }⟩

private theorem identityElementsBasedFunctor_isSmooth (F : Functor.{0, z} ArtQ (Type z)) :
    IsSmooth (elementsBasedFunctor (𝟙 F)) :=
  (isSmooth_elementsBasedFunctor_iff (𝟙 F)).2 fun _ _ _ _ _ yB hxy =>
    ⟨yB, by simpa using hxy.symm, rfl⟩

private noncomputable def corepresentedTruncSq : Functor.{0, z} ArtQ (Type z) :=
  corepresented truncSqArt

private noncomputable def nonsmoothQuotientGroupoid : GroupoidInFunctors ArtQ :=
  discreteGroupoid corepresentedTruncSq

private theorem nonsmoothQuotientGroupoid_isSmooth :
    GroupoidInFunctors.IsSmooth nonsmoothQuotientGroupoid :=
  ⟨identityElementsBasedFunctor_isSmooth corepresentedTruncSq,
    identityElementsBasedFunctor_isSmooth corepresentedTruncSq⟩

private theorem truncCubeToSqArt_surjective :
    Function.Surjective truncCubeToSqArt.hom := by
  change Function.Surjective (Ideal.Quotient.factorₐ ℚ _).toRingHom
  exact Ideal.Quotient.factor_surjective maximalIdealCube_le_sq

/-- A smooth groupoid in functors can have a quotient category that is not smooth
over the base. -/
@[stacks 06KJ "smooth groupoid with nonsmooth quotient category"]
public theorem smooth_groupoid_quotient_not_smooth :
    ∃ G : GroupoidInFunctors (ArtinianLocalAlgCat.{0, 0, 0} ℚ ℚ),
      GroupoidInFunctors.IsSmooth G ∧
        ¬ IsSmooth (quotientProjectionBasedFunctor G) := by
  refine ⟨nonsmoothQuotientGroupoid, nonsmoothQuotientGroupoid_isSmooth, ?_⟩
  intro hs
  let x : Grothendieck (evaluationFunctor nonsmoothQuotientGroupoid) :=
    ⟨truncSqArt, ULift.up (𝟙 truncSqArt)⟩
  obtain ⟨x', h, a, hh, ha, hcomm⟩ :=
    hs truncCubeToSqArt truncCubeToSqArt_surjective truncCubeArt x truncCubeToSqArt
      (IsHomLift.map (p := 𝟭 ArtQ) truncCubeToSqArt)
  rcases x' with ⟨B', z⟩
  have hh' : (Grothendieck.forget
      (evaluationFunctor nonsmoothQuotientGroupoid)).IsHomLift truncCubeToSqArt h := hh
  obtain rfl : B' = truncCubeArt := by
    let _ := hh'
    exact IsHomLift.domain_eq
      (p := Grothendieck.forget (evaluationFunctor nonsmoothQuotientGroupoid))
      truncCubeToSqArt h
  let a' : truncCubeArt ⟶ truncCubeArt := a
  have ha' : (𝟭 ArtQ).IsHomLift (𝟙 truncCubeArt) a' := ha
  have haId : a' = 𝟙 truncCubeArt :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (𝟭 ArtQ) _ _ (𝟙 truncCubeArt) a' ha').symm
  have hbase : h.base = truncCubeToSqArt := by
    rw [show h.base = a' ≫ truncCubeToSqArt from hcomm, haId, Category.id_comp]
  have hfiberTerm := h.fiber
  rw [hbase] at hfiberTerm
  let α := ((evaluationFunctor nonsmoothQuotientGroupoid).map truncCubeToSqArt).toFunctor
  change α.obj z ⟶ ULift.up (𝟙 truncSqArt) at hfiberTerm
  have hfiber := nonsmoothQuotientGroupoid.evaluationArrowEquiv truncSqArt
      (α.obj z) (ULift.up (𝟙 truncSqArt)) hfiberTerm
  have hred : (corepresentedTruncSq.map truncCubeToSqArt) z = ULift.up (𝟙 truncSqArt) := by
    have := hfiber.2.1.symm.trans hfiber.2.2
    change (evaluationMap nonsmoothQuotientGroupoid truncCubeToSqArt).obj z =
      ULift.up (𝟙 truncSqArt) at this
    rwa [evaluationMap_obj] at this
  have hsection : z.down ≫ truncCubeToSqArt = 𝟙 truncSqArt := congrArg ULift.down hred
  have hsectionHom : truncCubeToSqArt.hom.comp z.down.hom = AlgHom.id ℚ truncSqArt := by
    simpa [ArtinianLocalAlgCat.comp_hom, ArtinianLocalAlgCat.id_hom] using
      congrArg (fun g : truncSqArt ⟶ truncSqArt => g.hom) hsection
  have hsq : (z.down.hom xClassSqArt) ^ 2 = 0 := by
    simpa only [map_pow, map_zero] using congrArg z.down.hom xClassSqArt_sq
  exact no_squarezero_lift (z.down.hom xClassSqArt)
    (congrArg (fun f : truncSqArt →ₐ[ℚ] truncSqArt => f xClassSqArt) hsectionHom) hsq

add_to_stacks 06KJ "smooth groupoid iff smooth source" isSmooth_iff_source
add_to_stacks 06KJ "smooth source iff smooth quotient morphism" source_isSmooth_iff_quotient

end

end Deformation
