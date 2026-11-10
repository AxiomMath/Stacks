module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.Algebra.Module.Adequate.LaurentLarge
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.BaseChange
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift

/-!
# The weight-one coproduct of Tag 06V7 at independent universes

Let `A` be a ring and `M` a finitely presented `A`-module. The weight-one part of an adequate
module-valued functor on the symmetric algebra of `M × M` is the direct sum of the images of
the weight-one parts coming from the two copies of `M`. This is the part of Stacks 06V7 that
the splitting argument consumes, and it is proved here with the algebra carriers and the
module values in universes independent of the base ring: the algebras are objects of
`CommAlgCat.{max u v} A` and the values lie in `Type (max u v w)`, which is the universe
discipline of `AdequateFunctor.ModuleValuedFunctor.{max u v w, v} A`.

`StacksFrontier.Algebra.Module.Adequate.Splitting` proves the same statements at the single
universe `u`; those are left untouched, and nothing here depends on them.

## Main definitions

* `AdequateFunctor.HasWeightOneCoproductLarge`: the weight-one direct-sum decomposition.

## Main results

* `AdequateFunctor.weightOne_eq_add_images_large`: the weight-one part over the symmetric
  algebra of two copies of a finitely presented module is the sum of the two factor images.
* `AdequateFunctor.weightOne_images_disjoint_large`: that sum is direct.
* `AdequateFunctor.adequate_hasWeightOneCoproduct_large`: an adequate functor has the
  weight-one coproduct.

## Implementation notes

The weight spaces are those of `AdequateFunctor.LaurentLarge.weightSpace`, whose two
structural maps agree definitionally with `AdequateFunctor.constantLaurentMapLarge` and
`AdequateFunctor.gradedLaurentMapLarge`; `laurentLarge_constantLaurentMap_eq` and
`laurentLarge_gradedLaurentMap_eq` record that, so the tensor-level descriptions of
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift` apply verbatim.

Two inputs carry the argument past the single-universe diagonal. The uniqueness of the weight
decomposition is `AdequateFunctor.LaurentLarge.existsUnique_finsupp_weightSpace_eq_large`
(Stacks 06UZ), which is what rules out an element having two distinct weights; the hypothesis
it needs, that an adequate functor commutes with flat base change, is
`adequate_preservesFlatBaseChange_large`, read off from Stacks 06UW, which is already stated
at these universes. No Ext vanishing is used.

## References

* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
* [Stacks Project, Tag 06UZ](https://stacks.math.columbia.edu/tag/06UZ)
* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct

universe u v w t

namespace AdequateFunctor

/-- The endomorphism of a symmetric algebra killing every generator. -/
public noncomputable def symmetricAlgebraZeroMapLarge (A : Type u) (M : Type v) [CommRing A]
    [AddCommGroup M] [Module A M] : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A M :=
  SymmetricAlgebra.lift (0 : M →ₗ[A] SymmetricAlgebra A M)

/-- The algebra map on a symmetric algebra sending each generator to itself times `T`. -/
public noncomputable def symmetricAlgebraLaurentDegreeOneMapLarge (A : Type u) (M : Type v)
    [CommRing A] [AddCommGroup M] [Module A M] :
    SymmetricAlgebra A M →ₐ[A] LaurentPolynomial (SymmetricAlgebra A M) :=
  SymmetricAlgebra.lift
    ((LinearMap.mulRight A (LaurentPolynomial.T (1 : ℤ))).comp
      ((constantLaurentMapLarge A (SymmetricAlgebra A M)).toLinearMap.comp
        (SymmetricAlgebra.ι A M)))

/-- The constant-polynomial map of Tag 06UZ is the one of Tag 06V0. -/
public lemma laurentLarge_constantLaurentMap_eq (A : Type u) (B : Type v) [CommRing A]
    [CommRing B] [Algebra A B] :
    LaurentLarge.constantLaurentMap A B = constantLaurentMapLarge A B := rfl

/-- The graded Laurent map of Tag 06UZ is the one of Tag 06V0. -/
public lemma laurentLarge_gradedLaurentMap_eq (A : Type u) (B : Type v) [CommRing A]
    [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    LaurentLarge.gradedLaurentMap A B 𝒜 = gradedLaurentMapLarge A B 𝒜 := rfl

/-- A grading of a symmetric algebra placing the generators in degree one induces the same
graded Laurent map as the symmetric-power grading does. -/
public lemma gradedLaurentMapLarge_symmetricAlgebra_eq_degreeOne (A : Type u) (M : Type v)
    [CommRing A] [AddCommGroup M] [Module A M]
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (h𝒜 : ∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1) :
    gradedLaurentMapLarge A (SymmetricAlgebra A M) 𝒜 =
      symmetricAlgebraLaurentDegreeOneMapLarge A M := by
  apply AlgHom.ext
  intro z
  induction z using SymmetricAlgebra.induction with
  | algebraMap a => simp [symmetricAlgebraLaurentDegreeOneMapLarge]
  | ι m =>
      rw [gradedLaurentMapLarge_mem A (SymmetricAlgebra A M) 𝒜 1 _ (h𝒜 m)]
      simp only [symmetricAlgebraLaurentDegreeOneMapLarge, SymmetricAlgebra.lift_ι_apply,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
        AlgHom.toLinearMap_apply]
      rfl
  | mul z₁ z₂ hz₁ hz₂ => simp [map_mul, hz₁, hz₂]
  | add z₁ z₂ hz₁ hz₂ => simp [map_add, hz₁, hz₂]

/-- Every generator of a symmetric algebra lies in the first symmetric power. -/
public lemma symmetricAlgebra_generator_mem_symmetricPower_one (A : Type u) (M : Type v)
    [CommRing A] [AddCommGroup M] [Module A M] (m : M) :
    SymmetricAlgebra.ι A M m ∈ symmetricPower A M 1 := by
  simpa only [symmetricPower, pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι A M) m

/-- Weight one over a symmetric algebra does not depend on which degree-one grading is
used to measure it. -/
public lemma weightSpace_one_iff_symmetricPower_large (A : Type u) (M : Type v) [CommRing A]
    [AddCommGroup M] [Module A M] (F : ModuleValuedFunctor.{max u v w, v} A)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (h𝒜 : ∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M))))) :
    x ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 ↔
      x ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F (symmetricPower A M) 1 := by
  change ((LaurentPolynomial.T 1 : LaurentPolynomial (SymmetricAlgebra A M)) •
      F.map ((CommAlgCat.ofHom (constantLaurentMapLarge A (SymmetricAlgebra A M))).op.op) x =
    F.map ((CommAlgCat.ofHom (gradedLaurentMapLarge A (SymmetricAlgebra A M) 𝒜)).op.op) x) ↔
    ((LaurentPolynomial.T 1 : LaurentPolynomial (SymmetricAlgebra A M)) •
      F.map ((CommAlgCat.ofHom (constantLaurentMapLarge A (SymmetricAlgebra A M))).op.op) x =
    F.map ((CommAlgCat.ofHom (gradedLaurentMapLarge A (SymmetricAlgebra A M)
      (symmetricPower A M))).op.op) x)
  rw [gradedLaurentMapLarge_symmetricAlgebra_eq_degreeOne A M 𝒜 h𝒜,
    gradedLaurentMapLarge_symmetricAlgebra_eq_degreeOne A M (symmetricPower A M)
      (symmetricAlgebra_generator_mem_symmetricPower_one A M)]

/-- A morphism of module-valued functors is semilinear over the structure ring, which on the
Laurent algebra is `LaurentPolynomial B`. -/
public lemma app_smul_laurent_large {A : Type u} [CommRing A] {B : Type (max u v)}
    [CommRing B] [Algebra A B] {F G : ModuleValuedFunctor.{max u v w, v} A} (η : F ⟶ G)
    (c : LaurentPolynomial B)
    (z : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B))))) :
    η.app (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) (c • z) =
      c • η.app (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) z :=
  map_smul _ _ _

/-- A monomorphism of module-valued functors detects the weight spaces. -/
public lemma weightSpace_map_iff_of_mono_large {A : Type u} [CommRing A] {B : Type (max u v)}
    [CommRing B] [Algebra A B] {F G : ModuleValuedFunctor.{max u v w, v} A} (η : F ⟶ G)
    [Mono η] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    η.app _ x ∈ LaurentLarge.weightSpace A B G 𝒜 k ↔
      x ∈ LaurentLarge.weightSpace A B F 𝒜 k := by
  let Y := Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))
  have hinj : Function.Injective (η.app Y) :=
    (ModuleCat.mono_iff_injective (η.app Y)).mp inferInstance
  change _ = _ ↔ _ = _
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  exact ⟨fun h => hinj ((app_smul_laurent_large η _ _).trans h),
    fun h => (app_smul_laurent_large η _ _).symm.trans (congrArg _ h)⟩

/-- Zero has every weight. -/
public lemma weightSpace_zero_mem_large {A : Type u} [CommRing A] {B : Type (max u v)}
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{max u v w, v} A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) :
    (0 : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ∈
      LaurentLarge.weightSpace A B F 𝒜 k := by
  change _ = _
  rw [(F.map _).hom.map_zero, (F.map _).hom.map_zero]
  exact smul_zero _

/-- The weight spaces are closed under negation. -/
public lemma weightSpace_neg_mem_large {A : Type u} [CommRing A] {B : Type (max u v)}
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{max u v w, v} A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    {x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))}
    (hx : x ∈ LaurentLarge.weightSpace A B F 𝒜 k) :
    -x ∈ LaurentLarge.weightSpace A B F 𝒜 k := by
  change _ = _ at hx
  change _ = _
  rw [(F.map _).hom.map_neg, (F.map _).hom.map_neg, smul_neg]
  exact congrArg Neg.neg hx

/-- The weight spaces are closed under subtraction. -/
public lemma weightSpace_sub_mem_large {A : Type u} [CommRing A] {B : Type (max u v)}
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{max u v w, v} A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    {x y : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))}
    (hx : x ∈ LaurentLarge.weightSpace A B F 𝒜 k)
    (hy : y ∈ LaurentLarge.weightSpace A B F 𝒜 k) :
    x - y ∈ LaurentLarge.weightSpace A B F 𝒜 k := by
  change _ = _ at hx hy
  change _ = _
  rw [(F.map _).hom.map_sub, (F.map _).hom.map_sub, smul_sub]
  exact congrArg₂ (· - ·) hx hy

/-- **Stacks Lemma 06UW**, read off for a single algebra map: an adequate module-valued
functor commutes with flat base change. Independent-universe form. -/
public lemma adequate_preservesFlatBaseChange_large {A : Type u} [CommRing A]
    (F : ModuleValuedFunctor.{max u v w, v} A) (hF : IsAdequate (𝟭 _) F) :
    LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A F := by
  intro B C _ _ _ _ f
  let : Algebra B C := f.toRingHom.toAlgebra
  intro hflat
  let ι : CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} A := 𝟭 _
  let g : CommAlgCat.of A B ⟶ CommAlgCat.of A C := CommAlgCat.ofHom f
  let : Algebra (↑(ι.obj (CommAlgCat.of A B))) (↑(ι.obj (CommAlgCat.of A C))) :=
    (ι.map g).hom.toRingHom.toAlgebra
  let : Algebra B (↑(ι.obj (CommAlgCat.of A C))) := g.hom.toRingHom.toAlgebra
  let : Module B (↑(ι.obj (CommAlgCat.of A C))) :=
    Module.compHom _ (algebraMap B (↑(ι.obj (CommAlgCat.of A C))))
  refine ⟨LinearEquiv.ofBijective
    (moduleValuedFunctorBaseChangeMap.{max u v w, v, u, max u v, max u v + 1} ι F g)
    (moduleValuedFunctorBaseChangeMap_bijective.{max u v w, v, u, max u v, max u v + 1}
      ι F hF g hflat), fun x => ?_⟩
  change moduleValuedFunctorBaseChangeMap.{max u v w, v, u, max u v, max u v + 1} ι F g
    ((1 : ↑(ι.obj (CommAlgCat.of A C))) ⊗ₜ[↑(ι.obj (CommAlgCat.of A B))] x) =
      F.map g.op.op x
  simpa only [one_smul] using
    moduleValuedFunctorBaseChangeMap_tmul.{max u v w, v, u, max u v, max u v + 1} ι F g
    (1 : C) x

/-- An element lying in two distinct weight spaces of a functor commuting with flat base
change is zero. Independent-universe form. -/
public lemma weightSpace_eq_zero_of_mem_two_weights_large {A : Type u} [CommRing A]
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (F : ModuleValuedFunctor.{max u v w, v} A)
    (hF : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A F)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {k l : ℤ} (hkl : k ≠ l)
    {x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))}
    (hk : x ∈ LaurentLarge.weightSpace A B F 𝒜 k)
    (hl : x ∈ LaurentLarge.weightSpace A B F 𝒜 l) : x = 0 := by
  classical
  obtain ⟨y, -, hy⟩ :=
    LaurentLarge.existsUnique_finsupp_weightSpace_eq_large.{u, v, w} A B F hF 𝒜 x
  have hs {j : ℤ} (hj : x ∈ LaurentLarge.weightSpace A B F 𝒜 j) :
      (∀ i, Finsupp.single j x i ∈ LaurentLarge.weightSpace A B F 𝒜 i) ∧
        (Finsupp.single j x).sum (fun _ z => z) = x := by
    refine ⟨fun i => ?_, by simp⟩
    by_cases hij : i = j
    · simpa [hij] using hj
    · simpa [Finsupp.single_apply, Ne.symm hij] using weightSpace_zero_mem_large F 𝒜 i
  simpa [Finsupp.single_eq_of_ne hkl] using
    DFunLike.congr_fun ((hy _ (hs hk)).trans (hy _ (hs hl)).symm) k

/-- Weight-space membership for a module extension is the corresponding statement about the
base-changed Laurent maps on the tensor product. -/
public lemma moduleExtension_mem_weightSpace_iff_large (A : Type u) [CommRing A]
    (B : Type (max u v)) [CommRing B] [Algebra A B] (N : ModuleCat.{max u v w} A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) (y : TensorProduct A B N) :
    y ∈ LaurentLarge.weightSpace A B (moduleExtension.{max u v w, v} A N) 𝒜 k ↔
      (LaurentPolynomial.T k : LaurentPolynomial B) •
          (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id) y =
        (TensorProduct.map (gradedLaurentMapLarge A B 𝒜).toLinearMap LinearMap.id) y :=
  Iff.rfl

/-- A degree-one tensor pushes forward to a degree-one tensor along a linear map of the
generating modules. -/
public lemma tensor_symmetricAlgebra_map_degreeOne_large {A : Type u} {V W : Type v}
    {N : Type t} [CommRing A] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [AddCommGroup N] [Module A N] (f : V →ₗ[A] W)
    (z : TensorProduct A (SymmetricAlgebra A V) N)
    (hz : z ∈ DirectSum.decomposeTensor (symmetricPower A V) N 1) :
    TensorProduct.map (SymmetricAlgebra.lift ((SymmetricAlgebra.ι A W).comp f)).toLinearMap
      LinearMap.id z ∈ DirectSum.decomposeTensor (symmetricPower A W) N 1 := by
  rw [DirectSum.decomposeTensor_apply] at hz ⊢
  obtain ⟨c, rfl⟩ := hz
  induction c using TensorProduct.inductionOn with
  | tmul x n =>
      obtain ⟨p, hp⟩ : (x : SymmetricAlgebra A V) ∈ LinearMap.range (SymmetricAlgebra.ι A V) := by
        simpa only [symmetricPower, pow_one] using x.property
      refine ⟨(⟨SymmetricAlgebra.ι A W (f p),
        symmetricAlgebra_generator_mem_symmetricPower_one A W (f p)⟩ :
        symmetricPower A W 1) ⊗ₜ[A] n, ?_⟩
      simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        Submodule.subtype_apply, AlgHom.toLinearMap_apply, ← hp,
        SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
  | add c c' hc hc' =>
      simpa only [map_add] using Submodule.add_mem _ hc hc'

/-- A degree-one tensor over the symmetric algebra of a product is recovered from its two
factor components. -/
public lemma tensor_symmetricAlgebra_factor_sum_large {A : Type u} {M : Type v} {N : Type t}
    [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (z : TensorProduct A (SymmetricAlgebra A (M × M)) N)
    (hz : z ∈ DirectSum.decomposeTensor (symmetricPower A (M × M)) N 1) :
    let p₁ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    let q₁ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.fst A M M))
    let q₂ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.snd A M M))
    TensorProduct.map p₁.toLinearMap LinearMap.id
        (TensorProduct.map q₁.toLinearMap LinearMap.id z) +
      TensorProduct.map p₂.toLinearMap LinearMap.id
        (TensorProduct.map q₂.toLinearMap LinearMap.id z) = z := by
  intro p₁ p₂ q₁ q₂
  rw [DirectSum.decomposeTensor_apply] at hz
  obtain ⟨c, rfl⟩ := hz
  induction c using TensorProduct.inductionOn with
  | tmul x n =>
      obtain ⟨m, hm⟩ : (x : SymmetricAlgebra A (M × M)) ∈
          LinearMap.range (SymmetricAlgebra.ι A (M × M)) := by
        simpa only [symmetricPower, pow_one] using x.property
      change p₁ (q₁ (x : SymmetricAlgebra A (M × M))) ⊗ₜ[A] n +
          p₂ (q₂ (x : SymmetricAlgebra A (M × M))) ⊗ₜ[A] n =
        (x : SymmetricAlgebra A (M × M)) ⊗ₜ[A] n
      rw [← hm]
      simp only [p₁, p₂, q₁, q₂, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, ← TensorProduct.add_tmul, ← map_add]
      congr 2
      ext <;> simp
  | add c c' hc hc' =>
      simp only [map_add]
      rw [add_add_add_comm, hc, hc']

/-- Weight one in a submodule-valued functor of a module extension is exactly degree one in
the tensor decomposition. Independent-universe form. -/
public lemma weightOne_iff_tensor_degreeOne_large {A : Type u} {V : Type v} [CommRing A]
    [AddCommGroup V] [Module A V] {N : ModuleCat.{max u v w} A}
    {F : ModuleValuedFunctor.{max u v w, v} A}
    (η : F ⟶ moduleExtension.{max u v w, v} A N) [Mono η]
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A V)) [GradedAlgebra 𝒜]
    (h𝒜 : ∀ p, SymmetricAlgebra.ι A V p ∈ 𝒜 1)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A V))))) :
    x ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A V) F 𝒜 1 ↔
      η.app _ x ∈ DirectSum.decomposeTensor (symmetricPower A V) (N : Type (max u v w)) 1 := by
  rw [weightSpace_one_iff_symmetricPower_large A V F 𝒜 h𝒜,
    ← weightSpace_map_iff_of_mono_large η (symmetricPower A V) 1 x,
    moduleExtension_mem_weightSpace_iff_large A (SymmetricAlgebra A V) N
      (symmetricPower A V) 1 (η.app _ x)]
  exact ⟨moduleExtension_weightOne_mem_degreeOne_large A (SymmetricAlgebra A V)
      (N : Type (max u v w)) (symmetricPower A V)
      (gradedLaurentMapLarge_mem A (SymmetricAlgebra A V) (symmetricPower A V)) _,
    fun hx => moduleExtension_range_weightSpace_large A (SymmetricAlgebra A V)
      (N : Type (max u v w)) (symmetricPower A V) 1
      (gradedLaurentMapLarge_mem A (SymmetricAlgebra A V) (symmetricPower A V) 1) _
      (by rwa [← DirectSum.decomposeTensor_apply])⟩

/-- Killing the generators commutes with the two Laurent maps. -/
public lemma gradedLaurentMapLarge_comp_symmetricAlgebraZeroMapLarge (A : Type u) (M : Type v)
    [CommRing A] [AddCommGroup M] [Module A M]
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜] :
    (gradedLaurentMapLarge A (SymmetricAlgebra A M) 𝒜).comp
        (symmetricAlgebraZeroMapLarge A M) =
      (constantLaurentMapLarge A (SymmetricAlgebra A M)).comp
        (symmetricAlgebraZeroMapLarge A M) := by
  ext m
  simp [symmetricAlgebraZeroMapLarge]

/-- Everything in the image of the generator-killing endomorphism has weight zero. -/
public lemma symmetricAlgebraZeroMapLarge_mem_weightSpace_zero (A : Type u) (M : Type v)
    [CommRing A] [AddCommGroup M] [Module A M] (F : ModuleValuedFunctor.{max u v w, v} A)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M))))) :
    F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op) x ∈
      LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 0 := by
  change (LaurentPolynomial.T 0 : LaurentPolynomial (SymmetricAlgebra A M)) •
      F.map ((CommAlgCat.ofHom (constantLaurentMapLarge A (SymmetricAlgebra A M))).op.op)
        (F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op) x) =
    F.map ((CommAlgCat.ofHom (gradedLaurentMapLarge A (SymmetricAlgebra A M) 𝒜)).op.op)
      (F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op) x)
  rw [← F.map_comp_apply, ← F.map_comp_apply, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    ← CommAlgCat.ofHom_comp, ← CommAlgCat.ofHom_comp,
    gradedLaurentMapLarge_comp_symmetricAlgebraZeroMapLarge]
  exact one_smul _ _

/-- The weight-one part over the symmetric algebra on two copies of a finitely presented
module is the sum of the images from each copy. Independent-universe form. -/
public lemma weightOne_eq_add_images_large {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (F : ModuleValuedFunctor.{max u v w, v} A) (hF : IsAdequate (𝟭 _) F)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule A (SymmetricAlgebra A (M × M))) [GradedAlgebra ℬ]
    (h𝒜 : ∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1)
    (hℬ : ∀ m, SymmetricAlgebra.ι A (M × M) m ∈ ℬ 1) :
    let p₁ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    ∀ z, z ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A (M × M)) F ℬ 1 ↔
      ∃ x y, ∃ z₁ z₂ : F.obj (Opposite.op (Opposite.op
          (CommAlgCat.of A (SymmetricAlgebra A (M × M))))),
        x ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 ∧
        y ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 ∧
        z₁ = F.map ((CommAlgCat.ofHom p₁).op.op) x ∧
        z₂ = F.map ((CommAlgCat.ofHom p₂).op.op) y ∧ z = z₁ + z₂ := by
  obtain ⟨N, P, f, ⟨e⟩⟩ := (isAdequate_iff.{w, v, u} F).mp hF
  let η : F ⟶ moduleExtension.{max u v w, v} A N := e.hom ≫ kernel.ι f
  have : Mono η := inferInstance
  intro p₁ p₂ z
  let q₁ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.fst A M M))
  let q₂ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.snd A M M))
  let X := Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M)))
  let Y := Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A (M × M))))
  constructor
  · intro hz
    have ht := (weightOne_iff_tensor_degreeOne_large η ℬ hℬ z).mp hz
    let x : F.obj X := F.map (CommAlgCat.ofHom q₁).op.op z
    let y : F.obj X := F.map (CommAlgCat.ofHom q₂).op.op z
    have hx : x ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 := by
      rw [weightOne_iff_tensor_degreeOne_large η 𝒜 h𝒜, show η.app X x = _ from
        PresheafOfModules.naturality_apply η (CommAlgCat.ofHom q₁).op.op z]
      exact tensor_symmetricAlgebra_map_degreeOne_large (LinearMap.fst A M M) _ ht
    have hy : y ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 := by
      rw [weightOne_iff_tensor_degreeOne_large η 𝒜 h𝒜, show η.app X y = _ from
        PresheafOfModules.naturality_apply η (CommAlgCat.ofHom q₂).op.op z]
      exact tensor_symmetricAlgebra_map_degreeOne_large (LinearMap.snd A M M) _ ht
    refine ⟨x, y, F.map (CommAlgCat.ofHom p₁).op.op x,
      F.map (CommAlgCat.ofHom p₂).op.op y, hx, hy, rfl, rfl, ?_⟩
    apply (ModuleCat.mono_iff_injective (η.app Y)).mp inferInstance
    refine Eq.trans ?_ (map_add (ConcreteCategory.hom (η.app Y))
      (F.map (CommAlgCat.ofHom p₁).op.op x) (F.map (CommAlgCat.ofHom p₂).op.op y)).symm
    change η.app Y z = η.app Y (F.map (CommAlgCat.ofHom p₁).op.op x) +
      η.app Y (F.map (CommAlgCat.ofHom p₂).op.op y)
    rw [PresheafOfModules.naturality_apply η (CommAlgCat.ofHom p₁).op.op x,
      PresheafOfModules.naturality_apply η (CommAlgCat.ofHom p₂).op.op y]
    dsimp only [x, y]
    rw [PresheafOfModules.naturality_apply η (CommAlgCat.ofHom q₁).op.op z,
      PresheafOfModules.naturality_apply η (CommAlgCat.ofHom q₂).op.op z]
    exact (tensor_symmetricAlgebra_factor_sum_large (η.app Y z) ht).symm
  · rintro ⟨x, y, z₁, z₂, hx, hy, rfl, rfl, rfl⟩
    have key : η.app Y (F.map (CommAlgCat.ofHom p₁).op.op x) +
        η.app Y (F.map (CommAlgCat.ofHom p₂).op.op y) ∈
        DirectSum.decomposeTensor (symmetricPower A (M × M))
          (N : Type (max u v w)) 1 := by
      simp only [PresheafOfModules.naturality_apply]
      exact Submodule.add_mem _
        (tensor_symmetricAlgebra_map_degreeOne_large (LinearMap.inl A M M) _
          ((weightOne_iff_tensor_degreeOne_large η 𝒜 h𝒜 x).mp hx))
        (tensor_symmetricAlgebra_map_degreeOne_large (LinearMap.inr A M M) _
          ((weightOne_iff_tensor_degreeOne_large η 𝒜 h𝒜 y).mp hy))
    exact (weightOne_iff_tensor_degreeOne_large η ℬ hℬ _).mpr
      (Eq.subst (motive := fun c => c ∈ DirectSum.decomposeTensor
          (symmetricPower A (M × M)) (N : Type (max u v w)) 1)
        (map_add (ConcreteCategory.hom (η.app Y))
          (F.map (CommAlgCat.ofHom p₁).op.op x)
          (F.map (CommAlgCat.ofHom p₂).op.op y)).symm key)

/-- The two factor images in weight one have zero intersection. Independent-universe form. -/
public lemma weightOne_images_disjoint_large {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (F : ModuleValuedFunctor.{max u v w, v} A) (hF : IsAdequate (𝟭 _) F)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule A (SymmetricAlgebra A (M × M))) [GradedAlgebra ℬ] :
    let p₁ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    ∀ x y, ∀ z₁ z₂ : F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (SymmetricAlgebra A (M × M))))),
      x ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 →
      y ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 →
      z₁ = F.map ((CommAlgCat.ofHom p₁).op.op) x →
      z₂ = F.map ((CommAlgCat.ofHom p₂).op.op) y → z₁ + z₂ = 0 →
        x = 0 ∧ y = 0 := by
  intro p₁ p₂ x y z₁ z₂ hx hy hz₁ hz₂ hzero
  let q₁ : SymmetricAlgebra A (M × M) →ₐ[A] SymmetricAlgebra A M :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.fst A M M))
  let q₂ : SymmetricAlgebra A (M × M) →ₐ[A] SymmetricAlgebra A M :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.snd A M M))
  have hq₁p₁ : q₁.comp p₁ = AlgHom.id A (SymmetricAlgebra A M) := by
    ext m
    simp [p₁, q₁]
  have hq₁p₂ : q₁.comp p₂ = symmetricAlgebraZeroMapLarge A M := by
    ext m
    simp [p₂, q₁, symmetricAlgebraZeroMapLarge]
  have hq₂p₂ : q₂.comp p₂ = AlgHom.id A (SymmetricAlgebra A M) := by
    ext m
    simp [p₂, q₂]
  have hq₂p₁ : q₂.comp p₁ = symmetricAlgebraZeroMapLarge A M := by
    ext m
    simp [p₁, q₂, symmetricAlgebraZeroMapLarge]
  have hcat₁₁ : (CommAlgCat.ofHom p₁).op.op ≫ (CommAlgCat.ofHom q₁).op.op = 𝟙 _ := by
    simpa using congrArg (fun f => (CommAlgCat.ofHom f).op.op) hq₁p₁
  have hcat₁₂ : (CommAlgCat.ofHom p₂).op.op ≫ (CommAlgCat.ofHom q₁).op.op =
      (CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op := by
    simpa using congrArg (fun f => (CommAlgCat.ofHom f).op.op) hq₁p₂
  have hcat₂₂ : (CommAlgCat.ofHom p₂).op.op ≫ (CommAlgCat.ofHom q₂).op.op = 𝟙 _ := by
    simpa using congrArg (fun f => (CommAlgCat.ofHom f).op.op) hq₂p₂
  have hcat₂₁ : (CommAlgCat.ofHom p₁).op.op ≫ (CommAlgCat.ofHom q₂).op.op =
      (CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op := by
    simpa using congrArg (fun f => (CommAlgCat.ofHom f).op.op) hq₂p₁
  have hmap₁₁ : F.map ((CommAlgCat.ofHom q₁).op.op)
      (F.map ((CommAlgCat.ofHom p₁).op.op) x) = x := by
    rw [← F.map_comp_apply, hcat₁₁]
    change F.presheaf.map (𝟙 _) x = x
    exact F.presheaf.map_id_apply _ x
  have hmap₁₂ : F.map ((CommAlgCat.ofHom q₁).op.op)
      (F.map ((CommAlgCat.ofHom p₂).op.op) y) =
        F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op) y := by
    rw [← F.map_comp_apply, hcat₁₂]
  have hmap₂₂ : F.map ((CommAlgCat.ofHom q₂).op.op)
      (F.map ((CommAlgCat.ofHom p₂).op.op) y) = y := by
    rw [← F.map_comp_apply, hcat₂₂]
    change F.presheaf.map (𝟙 _) y = y
    exact F.presheaf.map_id_apply _ y
  have hmap₂₁ : F.map ((CommAlgCat.ofHom q₂).op.op)
      (F.map ((CommAlgCat.ofHom p₁).op.op) x) =
        F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op) x := by
    rw [← F.map_comp_apply, hcat₂₁]
  have hzero₁ := congrArg (fun z => F.map ((CommAlgCat.ofHom q₁).op.op) z) hzero
  rw [(F.map ((CommAlgCat.ofHom q₁).op.op)).hom.map_add,
    (F.map ((CommAlgCat.ofHom q₁).op.op)).hom.map_zero, hz₁, hz₂, hmap₁₁, hmap₁₂] at hzero₁
  have hzero₂ := congrArg (fun z => F.map ((CommAlgCat.ofHom q₂).op.op) z) hzero
  rw [(F.map ((CommAlgCat.ofHom q₂).op.op)).hom.map_add,
    (F.map ((CommAlgCat.ofHom q₂).op.op)).hom.map_zero, hz₁, hz₂, hmap₂₁, hmap₂₂] at hzero₂
  have hflat := adequate_preservesFlatBaseChange_large F hF
  have hcy_one :
      F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op) y ∈
        LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 := by
    rw [eq_neg_of_add_eq_zero_right hzero₁]
    exact weightSpace_neg_mem_large F 𝒜 1 hx
  have hcx_one :
      F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op) x ∈
        LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 := by
    rw [eq_neg_of_add_eq_zero_left hzero₂]
    exact weightSpace_neg_mem_large F 𝒜 1 hy
  have hcy : F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op) y = 0 :=
    weightSpace_eq_zero_of_mem_two_weights_large F hflat 𝒜 (by norm_num) hcy_one
      (symmetricAlgebraZeroMapLarge_mem_weightSpace_zero A M F 𝒜 y)
  have hcx : F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMapLarge A M)).op.op) x = 0 :=
    weightSpace_eq_zero_of_mem_two_weights_large F hflat 𝒜 (by norm_num) hcx_one
      (symmetricAlgebraZeroMapLarge_mem_weightSpace_zero A M F 𝒜 x)
  constructor
  · rw [hcy] at hzero₁
    exact (add_zero x).symm.trans hzero₁
  · rw [hcx] at hzero₂
    exact (zero_add y).symm.trans hzero₂

/-- In weight one on the symmetric algebra of two copies of a finitely presented module,
every element decomposes uniquely into the two factor images. Independent-universe form. -/
public def HasWeightOneCoproductLarge {A : Type u} [CommRing A]
    (F : ModuleValuedFunctor.{max u v w, v} A) : Prop :=
  ∀ (M : Type v) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule A (SymmetricAlgebra A (M × M))) [GradedAlgebra ℬ],
    (∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1) →
    (∀ m, SymmetricAlgebra.ι A (M × M) m ∈ ℬ 1) →
    let p₁ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    ∀ z, z ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A (M × M)) F ℬ 1 ↔
      ∃! xy : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M)))) ×
          F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M)))),
        xy.1 ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 ∧
        xy.2 ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 ∧
        ∃ z₁ z₂ : F.obj (Opposite.op (Opposite.op
            (CommAlgCat.of A (SymmetricAlgebra A (M × M))))),
          z₁ = F.map ((CommAlgCat.ofHom p₁).op.op) xy.1 ∧
          z₂ = F.map ((CommAlgCat.ofHom p₂).op.op) xy.2 ∧ z = z₁ + z₂

/-- **Stacks Lemma 06V7**, the weight-one coproduct: an adequate module-valued functor has
the weight-one direct-sum decomposition. Independent-universe form. -/
public lemma adequate_hasWeightOneCoproduct_large {A : Type u} [CommRing A]
    (F : ModuleValuedFunctor.{max u v w, v} A) (hF : IsAdequate (𝟭 _) F) :
    HasWeightOneCoproductLarge.{u, v, w} F := by
  intro M _ _ _ 𝒜 _ ℬ _ hgenA hgenB
  dsimp [HasWeightOneCoproductLarge]
  intro z
  constructor
  · intro hz
    obtain ⟨x, y, _, _, hx, hy, rfl, rfl, hsum⟩ :=
      (weightOne_eq_add_images_large F hF 𝒜 ℬ hgenA hgenB z).mp hz
    refine ⟨(x, y), ⟨hx, hy, _, _, rfl, rfl, hsum⟩, ?_⟩
    rintro xy ⟨hx', hy', _, _, rfl, rfl, hsum'⟩
    have hxy0 := weightOne_images_disjoint_large F hF 𝒜 ℬ
      (x - xy.1) (y - xy.2) _ _
      (weightSpace_sub_mem_large F 𝒜 1 hx hx') (weightSpace_sub_mem_large F 𝒜 1 hy hy') rfl rfl
      (by
        rw [map_sub, map_sub]
        exact (sub_add_sub_comm _ _ _ _).trans (sub_eq_zero.mpr (hsum.symm.trans hsum')))
    exact Prod.ext (sub_eq_zero.mp hxy0.1).symm (sub_eq_zero.mp hxy0.2).symm
  · rintro ⟨xy, ⟨hx, hy, z₁, z₂, hz₁, hz₂, rfl⟩, -⟩
    exact (weightOne_eq_add_images_large F hF 𝒜 ℬ hgenA hgenB (z₁ + z₂)).mpr
      ⟨xy.1, xy.2, z₁, z₂, hx, hy, hz₁, hz₂, rfl⟩

end AdequateFunctor
