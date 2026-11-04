module

public import Mathlib.Algebra.Module.FinitePresentation
public import StacksFrontier.Algebra.Module.Adequate.SplittingLiftLarge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The weight-one calculus on symmetric algebras, at independent universes

The splitting argument of Stacks 06V7 lifts the tautological element of a linearly adequate
functor `L` to a weight-one element `θ` of the middle term `E` of an extension of `L`, and then
checks that evaluating `θ` is additive. The additivity check is a computation on the symmetric
algebra of two copies of a finitely presented module: this file carries that computation across
the single-universe diagonal.

Everything is stated for `AdequateFunctor.ModuleValuedFunctor.{max u v w, v} A`, with the
module `M` in `Type v`, so that `SymmetricAlgebra A M` is an object of
`CommAlgCat.{max u v} A`. `StacksFrontier.Algebra.Module.Adequate.Splitting` proves the same
statements at the diagonal `ModuleValuedFunctor.{u, u} A`; those are left untouched.

## Main definitions

* `AdequateFunctor.symmetricMapLarge`: the algebra map induced on symmetric algebras.
* `AdequateFunctor.laurentEvaluationLarge`: evaluation of a Laurent polynomial algebra at a
  unit of the target.

## Main results

* `AdequateFunctor.weightOne_unit_evaluation_large`: evaluating a weight-one element along a
  rescaled linear map rescales the value.
* `AdequateFunctor.weightOne_symmetricMap_large`: weight one is preserved by the maps induced
  on symmetric algebras.
* `AdequateFunctor.weightOne_eq_zero_of_projections_large`: a weight-one element over the
  symmetric algebra of two copies killed by both projections is zero.
* `AdequateFunctor.weightOne_lift_additive_large`: a weight-one lift whose image is additive
  is itself additive.
* `AdequateFunctor.evaluate_primitive_add_large`: evaluating an additive weight-one element at
  a sum of linear maps adds.

## Implementation notes

The weight spaces are those of `AdequateFunctor.LaurentLarge.weightSpace`, whose structural
maps agree definitionally with `AdequateFunctor.constantLaurentMapLarge` and
`AdequateFunctor.gradedLaurentMapLarge`. The grading used throughout is the symmetric-power
grading `AdequateFunctor.symmetricPower`, and
`AdequateFunctor.weightSpace_one_iff_symmetricPower_large` says that weight one does not
depend on which degree-one grading measures it.

Two inputs come from
`StacksFrontier.Algebra.Module.Adequate.SplittingWeightOneLarge`: the weight-one coproduct
`AdequateFunctor.HasWeightOneCoproductLarge` and the fact that an element with two distinct
weights vanishes. The exactness step of `weightOne_lift_additive_large` is
`AdequateFunctor.exact_component_preimage_large`, which replaces the
`ShortComplex.moduleCat_exact_iff` idiom of the diagonal proof: the latter tests exactness
through `MonoidalCategory`-free evaluation but is stated only where the module universe agrees
with the ring universe.

## References

* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace AdequateFunctor

/-! ### Maps induced on symmetric algebras -/

/-- The algebra map on symmetric algebras induced by a linear map. -/
@[ega "II 1.7.1" "partial"]
public noncomputable def symmetricMapLarge {A : Type u} {V W : Type v} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] (f : V →ₗ[A] W) :
    SymmetricAlgebra A V →ₐ[A] SymmetricAlgebra A W :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι A W).comp f)

/-- Precomposing a lift with an induced map lifts the precomposed linear map. -/
private lemma lift_comp_symmetricMapLarge {A : Type u} {V W : Type v} {B : Type*} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] [CommRing B] [Algebra A B]
    (g : W →ₗ[A] B) (f : V →ₗ[A] W) :
    (SymmetricAlgebra.lift g).comp (symmetricMapLarge f) = SymmetricAlgebra.lift (g.comp f) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp [symmetricMapLarge]

/-- The induced maps compose. -/
public lemma symmetricMapLarge_comp {A : Type u} {V W T : Type v} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [AddCommGroup T] [Module A T] (f : V →ₗ[A] W) (g : W →ₗ[A] T) :
    (symmetricMapLarge g).comp (symmetricMapLarge f) = symmetricMapLarge (g.comp f) :=
  lift_comp_symmetricMapLarge _ _

/-- The map induced by the identity is the identity. -/
public lemma symmetricMapLarge_id {A : Type u} {V : Type v} [CommRing A]
    [AddCommGroup V] [Module A V] :
    symmetricMapLarge (LinearMap.id : V →ₗ[A] V) = AlgHom.id A _ := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp [symmetricMapLarge]

/-- Evaluate a Laurent polynomial algebra along an algebra map and a unit of the target. -/
public noncomputable def laurentEvaluationLarge {A : Type u} {B C : Type (max u v)}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (t : Cˣ) : LaurentPolynomial B →ₐ[A] C where
  toRingHom := LaurentPolynomial.eval₂ f.toRingHom t
  commutes' a := by simp [LaurentPolynomial.algebraMap_apply]

/-! ### Weight one under evaluation -/

/-- Evaluating a weight-one element along a linear map rescaled by a unit rescales the value
by that unit. Independent-universe form. -/
public lemma weightOne_unit_evaluation_large {A : Type u} {M : Type v} {B : Type (max u v)}
    [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [Algebra A B]
    (F : ModuleValuedFunctor.{max u v w, v} A)
    (x : algebraValueLarge F (SymmetricAlgebra A M))
    (hx : x ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F
      (symmetricPower A M) 1) (f : M →ₗ[A] B) (t : Bˣ) :
    algebraMapValueLarge F (SymmetricAlgebra.lift ((t : B) • f)) x =
      (t : B) • algebraMapValueLarge F (SymmetricAlgebra.lift f) x := by
  let ev := laurentEvaluationLarge (SymmetricAlgebra.lift f) t
  have hC : ev.comp (constantLaurentMapLarge A (SymmetricAlgebra A M)) =
      SymmetricAlgebra.lift f := by
    apply AlgHom.ext
    intro b
    show LaurentPolynomial.eval₂ _ t (LaurentPolynomial.C b) = _
    exact LaurentPolynomial.eval₂_C _ _ _
  have hG : ev.comp (gradedLaurentMapLarge A (SymmetricAlgebra A M)
      (symmetricPower A M)) = SymmetricAlgebra.lift ((t : B) • f) := by
    rw [gradedLaurentMapLarge_symmetricAlgebra_eq_degreeOne A M (symmetricPower A M)
      (symmetricAlgebra_generator_mem_symmetricPower_one A M)]
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    show ev (symmetricAlgebraLaurentDegreeOneMapLarge A M (SymmetricAlgebra.ι A M m)) =
      SymmetricAlgebra.lift ((t : B) • f) (SymmetricAlgebra.ι A M m)
    rw [symmetricAlgebraLaurentDegreeOneMapLarge, SymmetricAlgebra.lift_ι_apply,
      SymmetricAlgebra.lift_ι_apply]
    show LaurentPolynomial.eval₂ (SymmetricAlgebra.lift f).toRingHom t
      (LaurentPolynomial.C (SymmetricAlgebra.ι A M m) * LaurentPolynomial.T 1) =
        (t : B) * f m
    simp only [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T,
      zpow_one, SymmetricAlgebra.lift_ι_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    exact mul_comm _ _
  have h := congrArg (algebraMapValueLarge F ev) hx
  change algebraMapValueLarge F ev
      ((LaurentPolynomial.T 1 : LaurentPolynomial (SymmetricAlgebra A M)) •
        algebraMapValueLarge F (constantLaurentMapLarge A (SymmetricAlgebra A M)) x) =
    algebraMapValueLarge F ev (algebraMapValueLarge F (gradedLaurentMapLarge A
      (SymmetricAlgebra A M) (symmetricPower A M)) x) at h
  rw [map_smulₛₗ, algebraMapValueLarge_comp, algebraMapValueLarge_comp, hC, hG] at h
  simpa [ev, laurentEvaluationLarge] using h.symm

/-- Weight one is preserved by the algebra maps induced on symmetric algebras.
Independent-universe form. -/
public lemma weightOne_symmetricMap_large {A : Type u} {V W : Type v} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (F : ModuleValuedFunctor.{max u v w, v} A) (f : V →ₗ[A] W)
    (x : algebraValueLarge F (SymmetricAlgebra A V))
    (hx : x ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A V) F
      (symmetricPower A V) 1) :
    algebraMapValueLarge F (symmetricMapLarge f) x ∈
      LaurentLarge.weightSpace A (SymmetricAlgebra A W) F (symmetricPower A W) 1 := by
  let t : (LaurentPolynomial (SymmetricAlgebra A W))ˣ :=
    ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by
      rw [← LaurentPolynomial.T_add]; norm_num, by
      rw [← LaurentPolynomial.T_add]; norm_num⟩
  let g := (constantLaurentMapLarge A (SymmetricAlgebra A W)).toLinearMap.comp
    ((SymmetricAlgebra.ι A W).comp f)
  have h := weightOne_unit_evaluation_large F x hx g t
  have hC : (constantLaurentMapLarge A (SymmetricAlgebra A W)).comp
      (symmetricMapLarge f) = SymmetricAlgebra.lift g := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    simp [symmetricMapLarge, g]
  have hG : (gradedLaurentMapLarge A (SymmetricAlgebra A W)
      (symmetricPower A W)).comp (symmetricMapLarge f) =
      SymmetricAlgebra.lift ((t : LaurentPolynomial (SymmetricAlgebra A W)) • g) := by
    rw [gradedLaurentMapLarge_symmetricAlgebra_eq_degreeOne A W (symmetricPower A W)
      (symmetricAlgebra_generator_mem_symmetricPower_one A W)]
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro v
    show symmetricAlgebraLaurentDegreeOneMapLarge A W
        (symmetricMapLarge f (SymmetricAlgebra.ι A V v)) =
      SymmetricAlgebra.lift ((t : LaurentPolynomial (SymmetricAlgebra A W)) • g)
        (SymmetricAlgebra.ι A V v)
    simp only [symmetricMapLarge, symmetricAlgebraLaurentDegreeOneMapLarge,
      SymmetricAlgebra.lift_ι_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, LinearMap.smul_apply]
    show LaurentPolynomial.C (SymmetricAlgebra.ι A W (f v)) * LaurentPolynomial.T 1 =
      LaurentPolynomial.T 1 * LaurentPolynomial.C (SymmetricAlgebra.ι A W (f v))
    exact mul_comm _ _
  show (LaurentPolynomial.T 1 : LaurentPolynomial (SymmetricAlgebra A W)) •
    algebraMapValueLarge F (constantLaurentMapLarge A (SymmetricAlgebra A W))
      (algebraMapValueLarge F (symmetricMapLarge f) x) =
    algebraMapValueLarge F (gradedLaurentMapLarge A (SymmetricAlgebra A W)
      (symmetricPower A W)) (algebraMapValueLarge F (symmetricMapLarge f) x)
  rw [algebraMapValueLarge_comp, algebraMapValueLarge_comp, hC, hG]
  exact h.symm

/-- Pushing a weight-one element along the zero map kills it. Independent-universe form. -/
public lemma weightOne_zeroMap_large {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] (F : ModuleValuedFunctor.{max u v w, v} A)
    (hF : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A F)
    (x : algebraValueLarge F (SymmetricAlgebra A M))
    (hx : x ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F
      (symmetricPower A M) 1) :
    algebraMapValueLarge F (symmetricMapLarge (0 : M →ₗ[A] M)) x = 0 := by
  apply weightSpace_eq_zero_of_mem_two_weights_large F hF (symmetricPower A M)
    (k := 1) (l := 0) (by decide)
  · exact weightOne_symmetricMap_large F 0 x hx
  · have heq : symmetricMapLarge (0 : M →ₗ[A] M) = symmetricAlgebraZeroMapLarge A M := by
      simp only [symmetricMapLarge, symmetricAlgebraZeroMapLarge, LinearMap.comp_zero]
    rw [heq]
    exact symmetricAlgebraZeroMapLarge_mem_weightSpace_zero A M F (symmetricPower A M) x

/-- A weight-one element over the symmetric algebra of two copies of a finitely presented
module which is killed by both projections is zero. Independent-universe form. -/
public lemma weightOne_eq_zero_of_projections_large {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (F : ModuleValuedFunctor.{max u v w, v} A)
    (hflat : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A F)
    (hweight : HasWeightOneCoproductLarge.{u, v, w} F)
    (z : algebraValueLarge F (SymmetricAlgebra A (M × M)))
    (hz : z ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A (M × M)) F
      (symmetricPower A (M × M)) 1)
    (h₁ : algebraMapValueLarge F (symmetricMapLarge (LinearMap.fst A M M)) z = 0)
    (h₂ : algebraMapValueLarge F (symmetricMapLarge (LinearMap.snd A M M)) z = 0) : z = 0 := by
  obtain ⟨⟨x, y⟩, ⟨hx, hy, z₁, z₂, rfl, rfl, rfl⟩, -⟩ :=
    (hweight M (symmetricPower A M) (symmetricPower A (M × M))
      (symmetricAlgebra_generator_mem_symmetricPower_one A M)
      (symmetricAlgebra_generator_mem_symmetricPower_one A (M × M)) z).mp hz
  change algebraMapValueLarge F (symmetricMapLarge (LinearMap.fst A M M))
    (algebraMapValueLarge F (symmetricMapLarge (LinearMap.inl A M M)) x +
      algebraMapValueLarge F (symmetricMapLarge (LinearMap.inr A M M)) y) = 0 at h₁
  change algebraMapValueLarge F (symmetricMapLarge (LinearMap.snd A M M))
    (algebraMapValueLarge F (symmetricMapLarge (LinearMap.inl A M M)) x +
      algebraMapValueLarge F (symmetricMapLarge (LinearMap.inr A M M)) y) = 0 at h₂
  rw [map_add, algebraMapValueLarge_comp, algebraMapValueLarge_comp, symmetricMapLarge_comp,
    symmetricMapLarge_comp, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, symmetricMapLarge_id,
    algebraMapValueLarge_id, weightOne_zeroMap_large F hflat y hy, add_zero] at h₁
  rw [map_add, algebraMapValueLarge_comp, algebraMapValueLarge_comp, symmetricMapLarge_comp,
    symmetricMapLarge_comp, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, symmetricMapLarge_id,
    algebraMapValueLarge_id, weightOne_zeroMap_large F hflat x hx, zero_add] at h₂
  subst x y
  show algebraMapValueLarge F (symmetricMapLarge (LinearMap.inl A M M)) 0 +
    algebraMapValueLarge F (symmetricMapLarge (LinearMap.inr A M M)) 0 = 0
  simp only [map_zero, add_zero]

/-- A weight-one lift of an element whose image is additive on the two factors is itself
additive. Independent-universe form. -/
public lemma weightOne_lift_additive_large {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    {F E L : ModuleValuedFunctor.{max u v w, v} A}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (hflat : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A F)
    (hweight : HasWeightOneCoproductLarge.{u, v, w} F)
    (hE : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A E)
    (x : algebraValueLarge E (SymmetricAlgebra A M))
    (hx : x ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) E
      (symmetricPower A M) 1)
    (hpx : algebraMapValueLarge L (symmetricMapLarge
        (LinearMap.inl A M M + LinearMap.inr A M M)) (p.app _ x) =
      algebraMapValueLarge L (symmetricMapLarge (LinearMap.inl A M M)) (p.app _ x) +
      algebraMapValueLarge L (symmetricMapLarge (LinearMap.inr A M M)) (p.app _ x)) :
    algebraMapValueLarge E (symmetricMapLarge
        (LinearMap.inl A M M + LinearMap.inr A M M)) x =
      algebraMapValueLarge E (symmetricMapLarge (LinearMap.inl A M M)) x +
      algebraMapValueLarge E (symmetricMapLarge (LinearMap.inr A M M)) x := by
  let d := algebraMapValueLarge E (symmetricMapLarge
        (LinearMap.inl A M M + LinearMap.inr A M M)) x -
      algebraMapValueLarge E (symmetricMapLarge (LinearMap.inl A M M)) x -
      algebraMapValueLarge E (symmetricMapLarge (LinearMap.inr A M M)) x
  have hd : p.app _ d = 0 := by
    dsimp [d]
    rw [map_sub, map_sub]
    refine Eq.trans (congrArg₂ (· - ·) (congrArg₂ (· - ·)
      (algebraMapValueLarge_naturality' p
        (symmetricMapLarge (LinearMap.inl A M M + LinearMap.inr A M M)) x)
      (algebraMapValueLarge_naturality' p (symmetricMapLarge (LinearMap.inl A M M)) x))
      (algebraMapValueLarge_naturality' p (symmetricMapLarge (LinearMap.inr A M M)) x)) ?_
    rw [hpx]; abel
  obtain ⟨z, hz⟩ := exact_component_preimage_large.{w, v, u} A (ShortComplex.mk i p hip)
    hS.exact (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A (M × M))))) d hd
  change i.app _ z = d at hz
  have hi : Mono i := hS.mono_f
  have hwz : z ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A (M × M)) F
      (symmetricPower A (M × M)) 1 := by
    apply (weightSpace_map_iff_of_mono_large i _ 1 z).mp
    rw [hz]
    have h (f : M →ₗ[A] M × M) := weightOne_symmetricMap_large E f x hx
    exact weightSpace_sub_mem_large E _ 1 (weightSpace_sub_mem_large E _ 1 (h _) (h _)) (h _)
  have hproj (q : M × M →ₗ[A] M)
      (hqa : q.comp (LinearMap.inl A M M + LinearMap.inr A M M) = LinearMap.id)
      (hq : (q.comp (LinearMap.inl A M M) = LinearMap.id ∧
          q.comp (LinearMap.inr A M M) = 0) ∨
        (q.comp (LinearMap.inl A M M) = 0 ∧
          q.comp (LinearMap.inr A M M) = LinearMap.id)) :
      algebraMapValueLarge F (symmetricMapLarge q) z = 0 := by
    apply (ModuleCat.mono_iff_injective (i.app
      (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M)))))).mp inferInstance
    rw [algebraMapValueLarge_naturality, (i.app _).hom.map_zero, hz]
    show algebraMapValueLarge E (symmetricMapLarge q) (_ - _ - _) = 0
    rw [map_sub, map_sub, algebraMapValueLarge_comp, algebraMapValueLarge_comp,
      algebraMapValueLarge_comp, symmetricMapLarge_comp, symmetricMapLarge_comp,
      symmetricMapLarge_comp, hqa]
    rcases hq with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rw [ha, hb, symmetricMapLarge_id, algebraMapValueLarge_id,
        weightOne_zeroMap_large E hE x hx] <;> abel
  have hz0 : z = 0 := weightOne_eq_zero_of_projections_large F hflat hweight z hwz
    (hproj (LinearMap.fst A M M) (by ext; simp) (Or.inl ⟨rfl, rfl⟩))
    (hproj (LinearMap.snd A M M) (by ext; simp) (Or.inr ⟨rfl, rfl⟩))
  rw [hz0, (i.app _).hom.map_zero] at hz
  exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans hz.symm)

/-- Evaluating an additive weight-one element at a sum of linear maps adds.
Independent-universe form. -/
public lemma evaluate_primitive_add_large {A : Type u} {M : Type v} {B : Type (max u v)}
    [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [Algebra A B]
    (E : ModuleValuedFunctor.{max u v w, v} A)
    (x : algebraValueLarge E (SymmetricAlgebra A M))
    (hx : algebraMapValueLarge E (symmetricMapLarge
        (LinearMap.inl A M M + LinearMap.inr A M M)) x =
      algebraMapValueLarge E (symmetricMapLarge (LinearMap.inl A M M)) x +
      algebraMapValueLarge E (symmetricMapLarge (LinearMap.inr A M M)) x)
    (f g : M →ₗ[A] B) :
    algebraMapValueLarge E (SymmetricAlgebra.lift (f + g)) x =
      algebraMapValueLarge E (SymmetricAlgebra.lift f) x +
      algebraMapValueLarge E (SymmetricAlgebra.lift g) x := by
  have he := congrArg
    (algebraMapValueLarge E (SymmetricAlgebra.lift (f.coprod g)))
    hx
  rwa [map_add, algebraMapValueLarge_comp, algebraMapValueLarge_comp,
    algebraMapValueLarge_comp, lift_comp_symmetricMapLarge,
    lift_comp_symmetricMapLarge, lift_comp_symmetricMapLarge, LinearMap.comp_add,
    LinearMap.coprod_inl, LinearMap.coprod_inr] at he

end AdequateFunctor

end
