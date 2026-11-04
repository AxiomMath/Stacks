module

public import Mathlib.Algebra.Module.FinitePresentation
public import StacksFrontier.Algebra.Module.Adequate.SplittingSymmetricLarge
public import StacksFrontier.Algebra.Module.Adequate.SplittingWeightOneDomain

/-!
# The weight-one calculus on symmetric algebras, on a restricted domain of algebras

The splitting argument of [Stacks, Tag 06V7] lifts the tautological element of a linearly
adequate functor `L` to a weight-one element `θ` of the middle term `E` of an extension of `L`,
and then checks that evaluating `θ` is additive. The additivity check is a computation on the
symmetric algebra of two copies of a finitely presented module: this file carries that
computation to a module-valued functor defined only on the full subcategory of commutative
`A`-algebras satisfying a property `Q`.

`StacksFrontier.Algebra.Module.Adequate.SplittingSymmetricLarge` proves the same statements for a
functor on all commutative `A`-algebras; that proof is left untouched, and nothing here depends
on its conclusions. Its domain-free ingredients — `AdequateFunctor.symmetricMapLarge` and its
composition laws, and `AdequateFunctor.laurentEvaluationLarge` — are `public` and are reused
verbatim.

## Main results

* `AdequateFunctor.LaurentDomain.weightOne_unit_evaluation` — evaluating a weight-one element
  along a rescaled linear map rescales the value.
* `AdequateFunctor.LaurentDomain.weightOne_symmetricMap` — weight one is preserved by the maps
  induced on symmetric algebras.
* `AdequateFunctor.LaurentDomain.weightOne_eq_zero_of_projections` — a weight-one element over
  the symmetric algebra of two copies killed by both projections is zero.
* `AdequateFunctor.LaurentDomain.weightOne_lift_additive` — a weight-one lift whose image is
  additive is itself additive.
* `AdequateFunctor.LaurentDomain.evaluate_primitive_add` — evaluating an additive weight-one
  element at a sum of linear maps adds.

## Implementation notes

Each statement carries the memberships of exactly the algebras it evaluates at. That is more
bookkeeping than the full-domain versions need, but it is the whole content of the restriction:
the two symmetric algebras, their Laurent polynomial algebras, and — where uniqueness of the
weight decomposition is used, i.e. in
`AdequateFunctor.LaurentDomain.weightOne_zeroMap` — the double Laurent polynomial algebra.

The transition maps are written with `AdequateFunctor.LaurentDomain.algebraMapValue`, the
semilinear spelling, because the evaluation step rescales by a unit and so has to go through
`map_smulₛₗ`. `algebraMapValue_comp`, `algebraMapValue_id` and `algebraMapValue_congr` are the
three facts about it the computations use; each is the corresponding `map_algMor_*` of
`StacksFrontier.Algebra.Module.Adequate.DomainValues` in that spelling, so that no `rw` is ever
asked to match across the two.

The exactness step of `weightOne_lift_additive` is
`AdequateFunctor.exact_component_preimage_on`, the restricted-domain exactness tool.

## References

* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AdequateFunctor.LaurentDomain

universe w v u

variable {A : Type u} [CommRing A] {Q : ObjectProperty (CommAlgCat.{max u v} A)}

/-! ### The three facts about the semilinear transition maps -/

/-- The semilinear transition maps compose. -/
public lemma algebraMapValue_comp (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    {B C D : Type (max u v)} [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] (f : B →ₐ[A] C) (g : C →ₐ[A] D)
    (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C)) (hD : Q (CommAlgCat.of A D))
    (x : F.obj (algObj Q B hB)) :
    algebraMapValue F g hC hD (algebraMapValue F f hB hC x) =
      algebraMapValue F (g.comp f) hB hD x :=
  map_algMor_comp F f g hB hC hD x

/-- The semilinear transition map along the identity is the identity. -/
public lemma algebraMapValue_id (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    {B : Type (max u v)} [CommRing B] [Algebra A B] (hB : Q (CommAlgCat.of A B))
    (x : F.obj (algObj Q B hB)) :
    algebraMapValue F (AlgHom.id A B) hB hB x = x :=
  map_algMor_id F hB x

/-- Semilinear transition maps carried by equal algebra maps agree. -/
public lemma algebraMapValue_congr (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {f g : B →ₐ[A] C} (h : f = g)
    (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C))
    (x : F.obj (algObj Q B hB)) :
    algebraMapValue F f hB hC x = algebraMapValue F g hB hC x :=
  map_algMor_congr F h hB hC x

/-- A morphism of module-valued functors on the domain commutes with the semilinear transition
maps. -/
public lemma algebraMapValue_naturality {F G : ModuleValuedFunctorOn.{max u v w} Q.ι}
    (η : F ⟶ G) {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C))
    (x : F.obj (algObj Q B hB)) :
    η.app (algObj Q C hC) (algebraMapValue F f hB hC x) =
      algebraMapValue G f hB hC (η.app (algObj Q B hB) x) :=
  PresheafOfModules.naturality_apply η (algMor Q f hB hC) x

/-! ### Weight one under evaluation -/

/-- Transition maps along two induced symmetric algebra maps compose to the one induced by the
composite. -/
private lemma algebraMapValue_symmetricMapLarge_comp
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι) {U V W : Type (max u v)}
    [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (hU : Q (CommAlgCat.of A (SymmetricAlgebra A U)))
    (hV : Q (CommAlgCat.of A (SymmetricAlgebra A V)))
    (hW : Q (CommAlgCat.of A (SymmetricAlgebra A W)))
    (j : U →ₗ[A] V) (q : V →ₗ[A] W) (x : F.obj (algObj Q (SymmetricAlgebra A U) hU)) :
    algebraMapValue F (symmetricMapLarge q) hV hW
        (algebraMapValue F (symmetricMapLarge j) hU hV x) =
      algebraMapValue F (symmetricMapLarge (q.comp j)) hU hW x := by
  rw [algebraMapValue_comp, algebraMapValue_congr F (symmetricMapLarge_comp j q)]

/-- Transition maps along the maps induced by `j` and a retraction `q` of it cancel. -/
private lemma algebraMapValue_symmetricMapLarge_comp_id
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι) {U V : Type (max u v)}
    [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    (hU : Q (CommAlgCat.of A (SymmetricAlgebra A U)))
    (hV : Q (CommAlgCat.of A (SymmetricAlgebra A V)))
    (j : U →ₗ[A] V) (q : V →ₗ[A] U) (hqj : q.comp j = LinearMap.id)
    (x : F.obj (algObj Q (SymmetricAlgebra A U) hU)) :
    algebraMapValue F (symmetricMapLarge q) hV hU
        (algebraMapValue F (symmetricMapLarge j) hU hV x) = x := by
  rw [algebraMapValue_symmetricMapLarge_comp, hqj, algebraMapValue_congr F symmetricMapLarge_id,
    algebraMapValue_id]

/-- Evaluating a weight-one element along a linear map rescaled by a unit rescales the value by
that unit. -/
public lemma weightOne_unit_evaluation {M : Type (max u v)} {B : Type (max u v)}
    [AddCommGroup M] [Module A M] [CommRing B] [Algebra A B]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M))))
    (hB : Q (CommAlgCat.of A B))
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    (x : F.obj (algObj Q (SymmetricAlgebra A M) hS))
    (hx : x ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F (symmetricPower A M) 1)
    (f : M →ₗ[A] B) (t : Bˣ) :
    algebraMapValue F (SymmetricAlgebra.lift ((t : B) • f)) hS hB x =
      (t : B) • algebraMapValue F (SymmetricAlgebra.lift f) hS hB x := by
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
  have h := congrArg (algebraMapValue F ev hSL hB) hx
  change algebraMapValue F ev hSL hB
      ((LaurentPolynomial.T 1 : LaurentPolynomial (SymmetricAlgebra A M)) •
        algebraMapValue F (constantLaurentMapLarge A (SymmetricAlgebra A M)) hS hSL x) =
    algebraMapValue F ev hSL hB (algebraMapValue F (gradedLaurentMapLarge A
      (SymmetricAlgebra A M) (symmetricPower A M)) hS hSL x) at h
  rw [map_smulₛₗ, algebraMapValue_comp F _ _ hS hSL hB,
    algebraMapValue_comp F _ _ hS hSL hB, algebraMapValue_congr F hC hS hB,
    algebraMapValue_congr F hG hS hB] at h
  simpa [ev, laurentEvaluationLarge] using h.symm

/-- Weight one is preserved by the algebra maps induced on symmetric algebras. -/
public lemma weightOne_symmetricMap {V W : Type (max u v)}
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (hSV : Q (CommAlgCat.of A (SymmetricAlgebra A V)))
    (hSVL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A V))))
    (hSW : Q (CommAlgCat.of A (SymmetricAlgebra A W)))
    (hSWL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A W))))
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι) (f : V →ₗ[A] W)
    (x : F.obj (algObj Q (SymmetricAlgebra A V) hSV))
    (hx : x ∈ weightSpace Q (SymmetricAlgebra A V) hSV hSVL F (symmetricPower A V) 1) :
    algebraMapValue F (symmetricMapLarge f) hSV hSW x ∈
      weightSpace Q (SymmetricAlgebra A W) hSW hSWL F (symmetricPower A W) 1 := by
  let t : (LaurentPolynomial (SymmetricAlgebra A W))ˣ :=
    ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
      by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero],
      by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]⟩
  let g := (constantLaurentMapLarge A (SymmetricAlgebra A W)).toLinearMap.comp
    ((SymmetricAlgebra.ι A W).comp f)
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
    algebraMapValue F (constantLaurentMapLarge A (SymmetricAlgebra A W)) hSW hSWL
      (algebraMapValue F (symmetricMapLarge f) hSV hSW x) =
    algebraMapValue F (gradedLaurentMapLarge A (SymmetricAlgebra A W)
      (symmetricPower A W)) hSW hSWL (algebraMapValue F (symmetricMapLarge f) hSV hSW x)
  rw [algebraMapValue_comp F _ _ hSV hSW hSWL, algebraMapValue_comp F _ _ hSV hSW hSWL,
    algebraMapValue_congr F hC hSV hSWL, algebraMapValue_congr F hG hSV hSWL]
  exact (weightOne_unit_evaluation hSV hSVL hSWL F x hx g t).symm

/-- Pushing a weight-one element along the zero map kills it. -/
public lemma weightOne_zeroMap {M : Type (max u v)} [AddCommGroup M] [Module A M]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M))))
    (hSLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial
      (SymmetricAlgebra A M)))))
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι) (hF : PreservesFlatBaseChange Q F)
    (x : F.obj (algObj Q (SymmetricAlgebra A M) hS))
    (hx : x ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F (symmetricPower A M) 1) :
    algebraMapValue F (symmetricMapLarge (0 : M →ₗ[A] M)) hS hS x = 0 := by
  have heq : symmetricMapLarge (0 : M →ₗ[A] M) = symmetricAlgebraZeroMapLarge A M := by
    simp only [symmetricMapLarge, symmetricAlgebraZeroMapLarge, LinearMap.comp_zero]
  refine weightSpace_eq_zero_of_mem_two_weights Q (SymmetricAlgebra A M) hS hSL hSLL F hF
    (symmetricPower A M) (k := 1) (l := 0) (by decide)
    (weightOne_symmetricMap hS hSL hS hSL F 0 x hx) ?_
  rw [algebraMapValue_congr F heq hS hS]
  exact symmetricAlgebraZeroMap_mem_weightSpace_zero M hS hSL F (symmetricPower A M) x

/-- A weight-one element over the symmetric algebra of two copies of a finitely presented
module which is killed by both projections is zero. -/
public lemma weightOne_eq_zero_of_projections {M : Type (max u v)}
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M))))
    (hSLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial
      (SymmetricAlgebra A M)))))
    (hT : Q (CommAlgCat.of A (SymmetricAlgebra A (M × M))))
    (hTL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A (M × M)))))
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι) (hflat : PreservesFlatBaseChange Q F)
    (hweight : HasWeightOneCoproduct.{w} Q F)
    (z : F.obj (algObj Q (SymmetricAlgebra A (M × M)) hT))
    (hz : z ∈ weightSpace Q (SymmetricAlgebra A (M × M)) hT hTL F
      (symmetricPower A (M × M)) 1)
    (h₁ : algebraMapValue F (symmetricMapLarge (LinearMap.fst A M M)) hT hS z = 0)
    (h₂ : algebraMapValue F (symmetricMapLarge (LinearMap.snd A M M)) hT hS z = 0) :
    z = 0 := by
  obtain ⟨⟨x, y⟩, ⟨hx, hy, z₁, z₂, rfl, rfl, rfl⟩, -⟩ :=
    (hweight M hS hSL hT hTL (symmetricPower A M) (symmetricPower A (M × M))
      (symmetricAlgebra_generator_mem_symmetricPower_one A M)
      (symmetricAlgebra_generator_mem_symmetricPower_one A (M × M)) z).mp hz
  change algebraMapValue F (symmetricMapLarge (LinearMap.fst A M M)) hT hS
    (algebraMapValue F (symmetricMapLarge (LinearMap.inl A M M)) hS hT x +
      algebraMapValue F (symmetricMapLarge (LinearMap.inr A M M)) hS hT y) = 0 at h₁
  change algebraMapValue F (symmetricMapLarge (LinearMap.snd A M M)) hT hS
    (algebraMapValue F (symmetricMapLarge (LinearMap.inl A M M)) hS hT x +
      algebraMapValue F (symmetricMapLarge (LinearMap.inr A M M)) hS hT y) = 0 at h₂
  have hfi : (LinearMap.fst A M M).comp (LinearMap.inl A M M) = LinearMap.id := rfl
  have hfj : (LinearMap.fst A M M).comp (LinearMap.inr A M M) = 0 := rfl
  have hsi : (LinearMap.snd A M M).comp (LinearMap.inl A M M) = 0 := rfl
  have hsj : (LinearMap.snd A M M).comp (LinearMap.inr A M M) = LinearMap.id := rfl
  rw [map_add, algebraMapValue_symmetricMapLarge_comp_id F hS hT _ _ hfi,
    algebraMapValue_symmetricMapLarge_comp, hfj, weightOne_zeroMap hS hSL hSLL F hflat y hy,
    add_zero] at h₁
  rw [map_add, algebraMapValue_symmetricMapLarge_comp_id F hS hT _ _ hsj,
    algebraMapValue_symmetricMapLarge_comp, hsi, weightOne_zeroMap hS hSL hSLL F hflat x hx,
    zero_add] at h₂
  subst x y
  show algebraMapValue F (symmetricMapLarge (LinearMap.inl A M M)) hS hT 0 +
    algebraMapValue F (symmetricMapLarge (LinearMap.inr A M M)) hS hT 0 = 0
  simp only [map_zero, add_zero]

/-- A weight-one lift of an element whose image is additive on the two factors is itself
additive. -/
public lemma weightOne_lift_additive {M : Type (max u v)}
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M))))
    (hSLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial
      (SymmetricAlgebra A M)))))
    (hT : Q (CommAlgCat.of A (SymmetricAlgebra A (M × M))))
    (hTL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A (M × M)))))
    {F E L : ModuleValuedFunctorOn.{max u v w} Q.ι}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hSE : (ShortComplex.mk i p hip).ShortExact)
    (hflat : PreservesFlatBaseChange Q F)
    (hweight : HasWeightOneCoproduct.{w} Q F)
    (hE : PreservesFlatBaseChange Q E)
    (x : E.obj (algObj Q (SymmetricAlgebra A M) hS))
    (hx : x ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL E (symmetricPower A M) 1)
    (hpx : algebraMapValue L (symmetricMapLarge
        (LinearMap.inl A M M + LinearMap.inr A M M)) hS hT
          (p.app (algObj Q (SymmetricAlgebra A M) hS) x) =
      algebraMapValue L (symmetricMapLarge (LinearMap.inl A M M)) hS hT
        (p.app (algObj Q (SymmetricAlgebra A M) hS) x) +
      algebraMapValue L (symmetricMapLarge (LinearMap.inr A M M)) hS hT
        (p.app (algObj Q (SymmetricAlgebra A M) hS) x)) :
    algebraMapValue E (symmetricMapLarge
        (LinearMap.inl A M M + LinearMap.inr A M M)) hS hT x =
      algebraMapValue E (symmetricMapLarge (LinearMap.inl A M M)) hS hT x +
      algebraMapValue E (symmetricMapLarge (LinearMap.inr A M M)) hS hT x := by
  let d : E.obj (algObj Q (SymmetricAlgebra A (M × M)) hT) :=
    algebraMapValue E (symmetricMapLarge (LinearMap.inl A M M + LinearMap.inr A M M)) hS hT x -
      algebraMapValue E (symmetricMapLarge (LinearMap.inl A M M)) hS hT x -
      algebraMapValue E (symmetricMapLarge (LinearMap.inr A M M)) hS hT x
  have hd : p.app (algObj Q (SymmetricAlgebra A (M × M)) hT) d = 0 := by
    dsimp only [d]
    rw [map_sub, map_sub]
    refine Eq.trans (congrArg₂ (· - ·) (congrArg₂ (· - ·)
      (algebraMapValue_naturality p
        (symmetricMapLarge (LinearMap.inl A M M + LinearMap.inr A M M)) hS hT x)
      (algebraMapValue_naturality p (symmetricMapLarge (LinearMap.inl A M M)) hS hT x))
      (algebraMapValue_naturality p (symmetricMapLarge (LinearMap.inr A M M)) hS hT x)) ?_
    rw [hpx]
    abel
  obtain ⟨z, hz⟩ := exact_component_preimage_on.{w} Q.ι (ShortComplex.mk i p hip)
    hSE.exact (algObj Q (SymmetricAlgebra A (M × M)) hT) d hd
  change i.app (algObj Q (SymmetricAlgebra A (M × M)) hT) z = d at hz
  have hi : Mono i := hSE.mono_f
  have hwz : z ∈ weightSpace Q (SymmetricAlgebra A (M × M)) hT hTL F
      (symmetricPower A (M × M)) 1 := by
    rw [← weightSpace_map_iff_of_mono hT hTL i (symmetricPower A (M × M)) 1 z, hz]
    exact weightSpace_sub_mem hT hTL E _ 1
      (weightSpace_sub_mem hT hTL E _ 1 (weightOne_symmetricMap hS hSL hT hTL E _ x hx)
        (weightOne_symmetricMap hS hSL hT hTL E _ x hx))
      (weightOne_symmetricMap hS hSL hT hTL E _ x hx)
  have hproj (q : M × M →ₗ[A] M)
      (hqa : q.comp (LinearMap.inl A M M + LinearMap.inr A M M) = LinearMap.id)
      (hq : (q.comp (LinearMap.inl A M M) = LinearMap.id ∧
          q.comp (LinearMap.inr A M M) = 0) ∨
        (q.comp (LinearMap.inl A M M) = 0 ∧
          q.comp (LinearMap.inr A M M) = LinearMap.id)) :
      algebraMapValue F (symmetricMapLarge q) hT hS z = 0 := by
    apply PresheafOfModules.injective_of_mono i (algObj Q (SymmetricAlgebra A M) hS)
    rw [algebraMapValue_naturality i (symmetricMapLarge q) hT hS z,
      (i.app (algObj Q (SymmetricAlgebra A M) hS)).hom.map_zero, hz]
    show algebraMapValue E (symmetricMapLarge q) hT hS (_ - _ - _) = 0
    rw [map_sub, map_sub, algebraMapValue_symmetricMapLarge_comp, hqa,
      algebraMapValue_symmetricMapLarge_comp, algebraMapValue_symmetricMapLarge_comp]
    rcases hq with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rw [ha, hb, weightOne_zeroMap hS hSL hSLL E hE x hx,
        algebraMapValue_congr E symmetricMapLarge_id, algebraMapValue_id] <;> abel
  have hz0 : z = 0 := weightOne_eq_zero_of_projections hS hSL hSLL hT hTL F hflat hweight
    z hwz
    (hproj (LinearMap.fst A M M) (by ext; simp) (Or.inl ⟨rfl, rfl⟩))
    (hproj (LinearMap.snd A M M) (by ext; simp) (Or.inr ⟨rfl, rfl⟩))
  rw [hz0, (i.app (algObj Q (SymmetricAlgebra A (M × M)) hT)).hom.map_zero] at hz
  exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans hz.symm)

/-- Evaluating an additive weight-one element at a sum of linear maps adds. -/
public lemma evaluate_primitive_add {M : Type (max u v)} {B : Type (max u v)}
    [AddCommGroup M] [Module A M] [CommRing B] [Algebra A B]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)))
    (hT : Q (CommAlgCat.of A (SymmetricAlgebra A (M × M))))
    (hB : Q (CommAlgCat.of A B))
    (E : ModuleValuedFunctorOn.{max u v w} Q.ι)
    (x : E.obj (algObj Q (SymmetricAlgebra A M) hS))
    (hx : algebraMapValue E (symmetricMapLarge
        (LinearMap.inl A M M + LinearMap.inr A M M)) hS hT x =
      algebraMapValue E (symmetricMapLarge (LinearMap.inl A M M)) hS hT x +
      algebraMapValue E (symmetricMapLarge (LinearMap.inr A M M)) hS hT x)
    (f g : M →ₗ[A] B) :
    algebraMapValue E (SymmetricAlgebra.lift (f + g)) hS hB x =
      algebraMapValue E (SymmetricAlgebra.lift f) hS hB x +
      algebraMapValue E (SymmetricAlgebra.lift g) hS hB x := by
  let h := SymmetricAlgebra.lift (f.coprod g)
  have hcomp (j : M →ₗ[A] M × M) :
      h.comp (symmetricMapLarge j) = SymmetricAlgebra.lift ((f.coprod g).comp j) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    show h (symmetricMapLarge j (SymmetricAlgebra.ι A M m)) =
      SymmetricAlgebra.lift ((f.coprod g).comp j) (SymmetricAlgebra.ι A M m)
    simp only [h, symmetricMapLarge, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
  have hsum : (f.coprod g).comp (LinearMap.inl A M M + LinearMap.inr A M M) = f + g := by
    ext m; simp
  have hfst : (f.coprod g).comp (LinearMap.inl A M M) = f := by ext; simp
  have hsnd : (f.coprod g).comp (LinearMap.inr A M M) = g := by ext; simp
  have he := congrArg (algebraMapValue E h hT hB) hx
  rwa [map_add, algebraMapValue_comp E _ h hS hT hB, algebraMapValue_comp E _ h hS hT hB,
    algebraMapValue_comp E _ h hS hT hB,
    algebraMapValue_congr E (hcomp (LinearMap.inl A M M + LinearMap.inr A M M)) hS hB,
    algebraMapValue_congr E (hcomp (LinearMap.inl A M M)) hS hB,
    algebraMapValue_congr E (hcomp (LinearMap.inr A M M)) hS hB,
    algebraMapValue_congr E (congrArg SymmetricAlgebra.lift hsum) hS hB,
    algebraMapValue_congr E (congrArg SymmetricAlgebra.lift hfst) hS hB,
    algebraMapValue_congr E (congrArg SymmetricAlgebra.lift hsnd) hS hB] at he

end AdequateFunctor.LaurentDomain

end
