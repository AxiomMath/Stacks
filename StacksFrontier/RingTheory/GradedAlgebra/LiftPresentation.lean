module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.RingTheory.GradedAlgebra.WeightedPresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting a weighted graded presentation along a square-zero reduction

Let `k` be a commutative ring, `P` a graded `k`-algebra with a weighted graded presentation
`k[X_1, …, X_n] → P`, `X_i ↦ x i` with `x i` homogeneous of degree `d i`, and let `A` be a
commutative `k`-algebra with an augmentation `ε : A →ₐ[k] k`. Let `Q` be a graded `A`-algebra
together with a degree-preserving reduction `π : Q → P` which is semilinear along `ε` and
exhibits `P` as `Q/IQ` for an ideal `I ⊆ ker ε`. This file carries the presentation of `P`
upwards to `Q`:

* the chosen generators `x i` lift to *homogeneous* elements `q i ∈ Q_{d i}` of the same degree;
* for `I` nilpotent the resulting evaluation `A[X_1, …, X_n] → Q`, `X_i ↦ q i`, is surjective;
* for `I` square zero every relation `F` of the presentation of `P` lifts to a weighted
  homogeneous polynomial over `A` of the same weighted degree which is killed by that
  evaluation;
* for `I` square zero and `Q` flat over `A`, those lifted relations generate the whole
  kernel — in the module-theoretic form that a surjection onto a flat module whose kernel lies
  in `I • ⊤` is injective, and in the concrete form that the evaluation kills exactly the ideal
  they generate;
* and, when moreover `ker ε ⊆ I`, the degree-`e` part `I • Q_e` of `I • Q` is identified with
  `I ⊗[k] P_e`, which is what lets the correction term of a lifted relation be recorded by a
  vector over `P`.

These are the first, second, fourth and (the content of the) fifth steps of the Stacks proof of
the tangent-space half of
Tag 0DVZ (`examples-defos.tex:683`), where `A` is `k[ε]` and `I = (ε)`: *"Choose a homogeneous
element `q_i ∈ Q` of degree `d_i` mapping to the image of `X_i` in `P`. Then we obtain
`k[ε][X_1, …, X_n] → Q`, `X_i ↦ q_i`, and since `P = Q/εQ` this map is surjective by Nakayama's
lemma. A small diagram chase shows we can choose homogeneous elements
`F_{ε, j} ∈ k[ε][X_1, …, X_n]` of degree `e_j` mapping to zero in `Q` and mapping to `F_j` in
`k[X_1, …, X_n]`. Then `k[ε][X_1, …, X_n]/(F_{ε, 1}, …, F_{ε, m}) → Q` is a presentation of `Q`
by flatness of `Q` over `k[ε]`."* Nothing deformation-theoretic appears here; the statements are
about graded algebras and modules.

## Main results

* `DirectSum.coe_decompose_map`: a degree-preserving additive map commutes with the graded
  decomposition.
* `DirectSum.exists_mem_map_eq_of_surjective`: a degree-preserving additive surjection is
  surjective on every graded piece.
* `DirectSum.coe_decompose_mem_smul_grading`: the degree-`i` component of an element of `I • ⊤`
  lies in `I • ℳ i`.
* `Submodule.eq_top_of_le_sup_smul_top_of_isNilpotent`: Nakayama's lemma for a nilpotent ideal,
  with no finiteness hypothesis.
* `LinearMap.ker_eq_bot_of_ker_le_smul_top_of_flat`: a surjection onto a flat module whose
  kernel lies in `I • ⊤`, for `I` square zero, is injective. This is the content of the step
  the source states without proof.
* `Module.Flat.of_decomposition`: a module graded by flat submodules is flat.
* `Ideal.exists_addMonoidHom_tmul_smul`: for `I` square zero containing `ker ε` and `N` flat
  over `A`, the multiplication map `I ⊗[k] M → N` is injective with image `I • N`, where
  `M = N/IN`.
* `Ideal.tmul_sum_eq_zero_of_smul_sum_eq_zero`: the form in which the previous result is used.
* `MvPolynomial.IsWeightedHomogeneous.map`: weighted homogeneity is preserved by a change of
  coefficient ring.
* `MvPolynomial.hom_aeval_eq_aeval_map`: naturality of multivariate evaluation in the
  coefficients.
* `MvPolynomial.mem_smul_top_of_map_eq_zero`: a polynomial killed by the coefficientwise
  reduction lies in `I • ⊤`.
* `GradedAlgebra.exists_isWeightedHomogeneous_aeval_eq`: a weighted graded presentation is
  surjective in every weighted degree.
* `GradedAlgebra.exists_homogeneous_lift_generators`: homogeneous lifts of the generators.
* `GradedAlgebra.surjective_aeval_of_lift`: surjectivity of the lifted evaluation.
* `GradedAlgebra.exists_homogeneous_lift_relation`: homogeneous lifts of the relations.
* `GradedAlgebra.mem_sup_span_smul_top_of_aeval_eq_zero`: the kernel of the lifted evaluation
  is the ideal of the lifted relations up to `I • ⊤`.
* `GradedAlgebra.aeval_eq_zero_iff_mem_span_of_flat`: the lifted relations generate the whole
  kernel of the lifted evaluation.

## Implementation notes

Surjectivity of the lifted evaluation uses **no grading at all**: the image of `A[X]` is an
`A`-submodule `S` of `Q` with `Q = S + IQ`, and for nilpotent `I` this forces `S = Q` by
iterating `IQ = I(S + IQ) ⊆ S + I²Q`. In particular it is *not* an instance of the graded
Nakayama lemma `Submodule.IsHomogeneous.le_of_le_smul_of_le_irrelevant`
(`StacksFrontier/RingTheory/GradedAlgebra/Nakayama.lean`, Stacks 0EKB): that lemma requires the
ideal to lie inside the irrelevant ideal of the grading, whereas `I` here lies in degree zero.
Homogeneity of the lifted generators is needed only for the relations.

The nilpotence hypothesis is stated as `IsNilpotent I` for surjectivity and as `I * I = ⊥` for
the lift of relations, which is what the square-zero extension `k[V]` of the application
supplies and what the correction term of the diagram chase needs: the error made by an
arbitrary coefficientwise lift of a relation lies in `I • Q_{e}`, and subtracting a polynomial
with coefficients in `I` moves it into `I • (I • ⊤) = ⊥`.

The comparison `I ⊗[k] M → N` is built from two `TensorProduct.liftAddHom` maps between
`I ⊗[k] M` and `I ⊗[A] N` rather than from a chain of base-change equivalences. The reason is
that `M` carries no `A`-module structure here — in the application it is a graded piece of the
`k`-algebra `P`, on which `A` acts only through `ε` — so neither
`TensorProduct.AlgebraTensorModule.cancelBaseChange` nor any `I ⊗[A] M` is available; and
`I ⊗[A] N`, being only an `A`-module, is not a `k`-module either, so the two maps cannot be
linear. Additive maps are enough, because the statement asserted about them is injectivity.

`DirectSum.coe_decompose_map` is a strict generalisation — the source and target gradings may be
over *different* base rings, which is exactly the case `Q` over `A` and `P` over `k` — of the
`private` theorem `comp_of_graded` of `StacksFrontier/Algebra/DGA/Abelian/KernelCokernel.lean` and of
`StacksFrontier/RingTheory/DividedPowers/TateResolution/Homology.lean`, which state it for an
`R`-linear map over a common `R`; `exists_mem_map_eq_of_surjective` likewise generalises the
`private exists_homogeneous_lift` of the latter file. Those files are not edited here.
-/

@[expose] public section

open DirectSum MvPolynomial TensorProduct

namespace DirectSum

section Decompose

variable {ι : Type*} [DecidableEq ι] {M N σM σN : Type*}
  [AddCommMonoid M] [AddCommMonoid N] [SetLike σM M] [AddSubmonoidClass σM M]
  [SetLike σN N] [AddSubmonoidClass σN N] {ℳ : ι → σM} {𝒩 : ι → σN}
  [Decomposition ℳ] [Decomposition 𝒩]

/-- An additive map between graded additive monoids which preserves degrees commutes with the
graded decomposition: the degree-`i` component of `f z` is the image of the degree-`i`
component of `z`. The two gradings may be indexed by submodules over different base rings. -/
theorem coe_decompose_map (f : M →+ N) (hmem : ∀ (i : ι) (x : M), x ∈ ℳ i → f x ∈ 𝒩 i)
    (i : ι) (z : M) :
    ((decompose 𝒩 (f z)) i : N) = f ((decompose ℳ z) i : M) := by
  refine Decomposition.inductionOn ℳ (by simp) (fun {j} m => ?_) (fun m m' ih ih' => ?_) z
  · rcases eq_or_ne j i with rfl | h
    · rw [decompose_of_mem_same ℳ m.2, decompose_of_mem_same 𝒩 (hmem j m m.2)]
    · rw [decompose_of_mem_ne ℳ m.2 h, decompose_of_mem_ne 𝒩 (hmem j m m.2) h, map_zero]
  · simp [ih, ih']

/-- A degree-preserving additive surjection between graded additive monoids is surjective on
every graded piece: a homogeneous element of degree `i` is the image of a homogeneous element
of degree `i`. -/
theorem exists_mem_map_eq_of_surjective (f : M →+ N)
    (hmem : ∀ (i : ι) (x : M), x ∈ ℳ i → f x ∈ 𝒩 i) (hf : Function.Surjective f)
    {i : ι} {y : N} (hy : y ∈ 𝒩 i) : ∃ x ∈ ℳ i, f x = y := by
  obtain ⟨z, rfl⟩ := hf y
  exact ⟨_, (decompose ℳ z i).2,
    by rw [← coe_decompose_map f hmem i z, decompose_of_mem_same 𝒩 hy]⟩

end Decompose

section Smul

variable {ι A M : Type*} [DecidableEq ι] [CommRing A] [AddCommGroup M] [Module A M]
  {ℳ : ι → Submodule A M} [Decomposition ℳ]

/-- The graded decomposition of a module graded by submodules is linear, so it commutes with
scalar multiplication componentwise. -/
theorem coe_decompose_smul (a : A) (u : M) (i : ι) :
    ((decompose ℳ (a • u)) i : M) = a • ((decompose ℳ u) i : M) := by
  have h := (decomposeLinearEquiv ℳ).map_smul a u
  rw [decomposeLinearEquiv_apply, decomposeLinearEquiv_apply] at h
  rw [h, DFinsupp.smul_apply]
  rfl

/-- The degree-`i` component of an element of `I • ⊤` lies in `I • ℳ i`. Equivalently `I • ⊤`
is a graded submodule whose degree-`i` part is `I • ℳ i`, which holds because the scalars act
without shifting degrees. -/
theorem coe_decompose_mem_smul_grading {I : Ideal A} {z : M}
    (hz : z ∈ I • (⊤ : Submodule A M)) (i : ι) : ((decompose ℳ z) i : M) ∈ I • ℳ i := by
  refine Submodule.smul_induction_on hz (fun a ha u _ => ?_) (fun u v hu hv => ?_)
  · rw [coe_decompose_smul]
    exact Submodule.smul_mem_smul ha (decompose ℳ u i).2
  · have h : ((decompose ℳ (u + v)) i : M) =
        ((decompose ℳ u) i : M) + ((decompose ℳ v) i : M) := by simp
    rw [h]
    exact Submodule.add_mem _ hu hv

end Smul

end DirectSum

/-- The product of two elements of a square-zero ideal vanishes. -/
private theorem mul_eq_zero_of_mem_of_mul_eq_bot {A : Type*} [CommRing A] {I : Ideal A}
    (hI : I * I = ⊥) {a b : A} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have h := Ideal.mul_mem_mul ha hb
  rw [hI] at h
  simpa using h

namespace Submodule

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- A scalar from a square-zero ideal annihilates `I • ⊤`. -/
theorem smul_eq_zero_of_mem_smul_top_of_mul_eq_bot {I : Ideal A} (hI : I * I = ⊥)
    {a : A} (ha : a ∈ I) {z : M} (hz : z ∈ I • (⊤ : Submodule A M)) : a • z = 0 := by
  refine Submodule.smul_induction_on hz (fun b hb u _ => ?_)
    (fun u v hu hv => by rw [smul_add, hu, hv, add_zero])
  rw [smul_smul, mul_eq_zero_of_mem_of_mul_eq_bot hI ha hb, zero_smul]

/-- **Nakayama's lemma for a nilpotent ideal.** A submodule `S` of `M` with `M = S + I • M` is
all of `M` as soon as `I` is nilpotent. Unlike
`Submodule.le_of_le_smul_of_le_jacobson_bot` no finiteness is needed: iterating the hypothesis
gives `M = S + Iᵐ • M` for every `m`. -/
@[ega "0 7.1.13" "special case", ega "IV 2.5.5.4" "special case", sga "3 III 4.6.4" "more general"]
theorem eq_top_of_le_sup_smul_top_of_isNilpotent {I : Ideal A} (hI : IsNilpotent I)
    {S : Submodule A M} (h : (⊤ : Submodule A M) ≤ S ⊔ I • ⊤) : S = ⊤ := by
  obtain ⟨n, hn⟩ := hI
  have step : ∀ m : ℕ, (I ^ m • (⊤ : Submodule A M)) ≤ S ⊔ I ^ (m + 1) • ⊤ := by
    intro m
    rw [Submodule.smul_le]
    intro a ha z _
    obtain ⟨s, hs, y, hy, rfl⟩ := Submodule.mem_sup.mp (h (Submodule.mem_top (x := z)))
    rw [smul_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (S.smul_mem a hs))
      (Submodule.mem_sup_right ?_)
    refine Submodule.smul_induction_on hy (fun b hb u _ => ?_)
      (fun u v hu hv => by rw [smul_add]; exact Submodule.add_mem _ hu hv)
    rw [smul_smul]
    exact Submodule.smul_mem_smul (by rw [pow_succ]; exact Ideal.mul_mem_mul ha hb)
      Submodule.mem_top
  have key : ∀ m : ℕ, (⊤ : Submodule A M) ≤ S ⊔ I ^ m • ⊤ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => exact ih.trans (sup_le le_sup_left (step m))
  have hfin := key n
  rw [hn] at hfin
  rw [show (0 : Ideal A) = ⊥ from rfl, Submodule.bot_smul, sup_bot_eq] at hfin
  exact top_le_iff.mp hfin

end Submodule

namespace LinearMap

variable {A M Q : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup Q] [Module A Q]

/-- The canonical map `I ⊗[A] M → M`, as the inclusion `I ↪ A` tensored with `M` followed by the
unitor `A ⊗[A] M ≃ M`. Written as that composite so that its injectivity for flat `M` is
Mathlib's `Module.Flat.rTensor_preserves_injective_linearMap` with no further work. -/
private noncomputable def idealTensorSmul (I : Ideal A) (M : Type*) [AddCommGroup M]
    [Module A M] : (↥I) ⊗[A] M →ₗ[A] M :=
  (TensorProduct.lid A M).toLinearMap ∘ₗ LinearMap.rTensor M I.subtype

/-- The defining formula of `idealTensorSmul`. -/
private theorem idealTensorSmul_tmul (I : Ideal A) (b : ↥I) (m : M) :
    idealTensorSmul I M (b ⊗ₜ m) = (b : A) • m := rfl

/-- `idealTensorSmul` surjects onto `I • ⊤`. -/
private theorem exists_idealTensorSmul_eq {I : Ideal A} {z : M}
    (hz : z ∈ I • (⊤ : Submodule A M)) : ∃ η, idealTensorSmul I M η = z := by
  refine Submodule.smul_induction_on hz (fun a ha u _ => ⟨⟨a, ha⟩ ⊗ₜ u, rfl⟩) ?_
  rintro u v ⟨ηu, rfl⟩ ⟨ηv, rfl⟩
  exact ⟨ηu + ηv, by rw [map_add]⟩

/-- `idealTensorSmul` is injective on a flat module. -/
private theorem injective_idealTensorSmul (I : Ideal A) (N : Type*) [AddCommGroup N]
    [Module A N] [Module.Flat A N] : Function.Injective (idealTensorSmul I N) :=
  (TensorProduct.lid A N).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := N) I.subtype I.injective_subtype)

/-- **A surjection onto a flat module whose kernel is contained in `I • ⊤`, for a square-zero
ideal `I`, is injective.** This is the content of the step that Stacks 0DVZ states without
proof, *"is a presentation of `Q` by flatness of `Q` over `k[ε]`"*: applied to the quotient of
`A[X_1, …, X_n]` by the lifted relations it says that those relations generate the whole kernel
of the evaluation at the lifted generators, i.e. that the surjection of
`GradedAlgebra.surjective_aeval_of_lift` is a presentation.

The argument is the one the source omits. Writing `ν_M : I ⊗[A] M → M` for the canonical map,
an element `n` of `ker φ` lies in `I • ⊤` and so is `ν_M η` for some `η`. Flatness makes `ν_Q`
injective, and `ν_Q` composed with `id_I ⊗ φ` is `φ` composed with `ν_M`, so `id_I ⊗ φ` kills
`η`; right exactness of `I ⊗ -` then writes `η` as `id_I ⊗ (ker φ).subtype` of something, whose
image under `ν_M` lies in `I • ker φ ⊆ I • (I • ⊤) = ⊥`. Hence `n = 0`.

Only flatness of the *target* is used, and no finiteness or grading anywhere. -/
@[sga "3 VIB 6.2.2" "kernel vanishing"]
theorem ker_eq_bot_of_ker_le_smul_top_of_flat [Module.Flat A Q] {I : Ideal A} (hI : I * I = ⊥)
    (φ : M →ₗ[A] Q) (hsurj : Function.Surjective φ) (hker : LinearMap.ker φ ≤ I • ⊤) :
    LinearMap.ker φ = ⊥ := by
  have hcomm : ∀ ξ : (↥I) ⊗[A] M,
      φ (idealTensorSmul I M ξ) = idealTensorSmul I Q (LinearMap.lTensor (↥I) φ ξ) := by
    intro ξ
    induction ξ using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | tmul b m => rw [idealTensorSmul_tmul, LinearMap.lTensor_tmul, idealTensorSmul_tmul, map_smul]
    | add u v hu hv => simp only [map_add, hu, hv]
  have hkill : ∀ ξ : (↥I) ⊗[A] ↥(LinearMap.ker φ),
      idealTensorSmul I M (LinearMap.lTensor (↥I) (LinearMap.ker φ).subtype ξ) = 0 := by
    intro ξ
    induction ξ using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul b κ =>
        rw [LinearMap.lTensor_tmul, idealTensorSmul_tmul]
        exact Submodule.smul_eq_zero_of_mem_smul_top_of_mul_eq_bot hI b.2 (hker κ.2)
    | add u v hu hv => simp only [map_add, hu, hv, add_zero]
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨η, hη⟩ := exists_idealTensorSmul_eq (hker hn)
  have h0 : LinearMap.lTensor (↥I) φ η = 0 := by
    refine injective_idealTensorSmul I Q ?_
    rw [← hcomm, hη, map_zero]
    exact hn
  obtain ⟨ξ, hξ⟩ :=
    (lTensor_exact (↥I) (LinearMap.exact_subtype_ker_map φ) hsurj η).mp h0
  rw [Submodule.mem_bot, ← hη, ← hξ]
  exact hkill ξ

end LinearMap

namespace Module.Flat

/-- A module which decomposes as a direct sum of flat submodules is flat. For a graded algebra
whose graded pieces are finite projective this gives flatness of the algebra, which is the
hypothesis of `LinearMap.ker_eq_bot_of_ker_le_smul_top_of_flat`. -/
theorem of_decomposition {ι R M : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M]
    [Module R M] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    [∀ i, Module.Flat R (ℳ i)] : Module.Flat R M :=
  Module.Flat.of_linearEquiv (DirectSum.decomposeLinearEquiv ℳ)

end Module.Flat

namespace Ideal

section SquareZero

variable {k A M N : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module A N]

/-- An elementary tensor over a square-zero ideal `I` vanishes as soon as its second factor
lies in `I • ⊤`, because the scalar can be moved across. -/
theorem tmul_eq_zero_of_mem_smul_top {I : Ideal A} (hI : I * I = ⊥) (b : ↥I) {z : N}
    (hz : z ∈ I • (⊤ : Submodule A N)) : (b ⊗ₜ[A] z : (↥I) ⊗[A] N) = 0 := by
  refine Submodule.smul_induction_on hz (fun a ha y _ => ?_) (fun u v hu hv => ?_)
  · have hab : a • b = 0 := Subtype.ext (mul_eq_zero_of_mem_of_mul_eq_bot hI ha b.2)
    rw [← TensorProduct.smul_tmul, hab, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, hu, hv, add_zero]

/-- On a square-zero ideal `I` whose quotient is split off by an augmentation `ε : A →ₐ[k] k`,
the `A`-action agrees with the `k`-action along `ε`: the correction `a - ε a` lies in `I`, so it
annihilates `I`. This is the only use made of the splitting `A = k ⊕ I`. -/
theorem smul_eq_augmentation_smul {I : Ideal A} (hI : I * I = ⊥) (ε : A →ₐ[k] k)
    (hIker : ∀ a : A, a - algebraMap k A (ε a) ∈ I) (a : A) (b : ↥I) :
    a • b = (ε a) • b := by
  refine Subtype.ext ?_
  have h : (a - algebraMap k A (ε a)) * (b : A) = 0 :=
    mul_eq_zero_of_mem_of_mul_eq_bot hI (hIker a) b.2
  have hmul : (a : A) * (b : A) = algebraMap k A (ε a) * (b : A) := by
    rw [sub_mul, sub_eq_zero] at h
    exact h
  simpa [Algebra.smul_def] using hmul

/-- **The square-zero comparison map `I ⊗[k] M → N`.** Let `A` be a `k`-algebra with an
augmentation `ε : A →ₐ[k] k` whose kernel is contained in a square-zero ideal `I`, let `N` be a
flat `A`-module and let `π : N → M` be a surjection, semilinear along `ε`, with kernel exactly
`I • N`. Then multiplication `(b, m) ↦ b • (any lift of m)` is a well-defined additive map
`I ⊗[k] M → N` which is **injective with image `I • N`**.

This is the identification the source of Stacks 0DVZ uses silently when it writes
`F_{ε, j} = F_j + ε G_j` and then *"remembers the element `(g_1, …, g_m)` in
`P_{e_1} ⊕ … ⊕ P_{e_m}`"*: applied to `N = Q_e` and `M = P_e` it says that the degree-`e` part
of `I • Q` is `I ⊗_k P_e`, so that the correction term of a lifted relation is recorded by a
vector over `P` rather than over `Q`.

The map is stated existentially and characterised by `θ (b ⊗ₜ π y) = b • y`, which with
surjectivity of `π` determines it: there is no canonical lift `M → N`, and the construction
uses a set-theoretic section of `π`, which is harmless because `I` annihilates `ker π`.

Only flatness of `N` is used, and no grading. Injectivity is
`Module.Flat.rTensor_preserves_injective_linearMap` applied to `Submodule.subtype I`; the
identification of `I ⊗[k] M` with `I ⊗[A] N` is carried out by the two additive maps `Φ`, `Ψ`
of `TensorProduct.liftAddHom` below, which avoids having to equip `M` with an `A`-module
structure (in the application `M` is a graded piece of a `k`-algebra, and `A` acts on it only
through `ε`). -/
@[sga "3 III 4.12" "special case"]
theorem exists_addMonoidHom_tmul_smul (ε : A →ₐ[k] k) (π : N →+ M) (I : Ideal A)
    [Module.Flat A N] (hI : I * I = ⊥)
    (hIker : ∀ a : A, a - algebraMap k A (ε a) ∈ I)
    (hπsmul : ∀ (a : A) (y : N), π (a • y) = ε a • π y)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ y : N, π y = 0 ↔ y ∈ I • (⊤ : Submodule A N)) :
    ∃ θ : (↥I) ⊗[k] M →+ N,
      (∀ (b : ↥I) (y : N), θ (b ⊗ₜ π y) = (b : A) • y) ∧
      Function.Injective θ ∧
      (∀ ξ, θ ξ ∈ I • (⊤ : Submodule A N)) ∧
      (∀ z ∈ I • (⊤ : Submodule A N), ∃ ξ, θ ξ = z) := by
  classical
  set σ := Function.surjInv hπsurj with hσdef
  have hσ : ∀ m : M, π (σ m) = m := Function.surjInv_eq hπsurj
  have hlift : ∀ (b : ↥I) (y y' : N), π y = π y' → (b ⊗ₜ[A] y : (↥I) ⊗[A] N) = b ⊗ₜ[A] y' := by
    intro b y y' h
    have hz : y - y' ∈ I • (⊤ : Submodule A N) := (hπker _).mp (by rw [map_sub, h, sub_self])
    have hzero := tmul_eq_zero_of_mem_smul_top hI b hz
    rw [TensorProduct.tmul_sub, sub_eq_zero] at hzero
    exact hzero
  have hΦinner : ∀ b : ↥I, ∀ m m' : M,
      (b ⊗ₜ[A] σ (m + m') : (↥I) ⊗[A] N) = b ⊗ₜ[A] σ m + b ⊗ₜ[A] σ m' := by
    intro b m m'
    rw [← TensorProduct.tmul_add]
    exact hlift b _ _ (by rw [hσ, map_add, hσ, hσ])
  set Φ₀ : (↥I) →+ M →+ ((↥I) ⊗[A] N) :=
    AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun m => b ⊗ₜ[A] σ m) (hΦinner b))
      (fun b b' => by ext m; simp [TensorProduct.add_tmul]) with hΦ₀def
  have hΦbal : ∀ (r : k) (b : ↥I) (m : M), Φ₀ (r • b) m = Φ₀ b (r • m) := by
    intro r b m
    show (r • b) ⊗ₜ[A] σ m = b ⊗ₜ[A] σ (r • m)
    have hrb : (r • b : ↥I) = (algebraMap k A r) • b := Subtype.ext (by simp [Algebra.smul_def])
    rw [hrb, TensorProduct.smul_tmul]
    refine hlift b _ _ ?_
    rw [hπsmul, hσ, hσ]
    simp
  set Φ := TensorProduct.liftAddHom Φ₀ hΦbal with hΦdef
  have hΦtmul : ∀ (b : ↥I) (m : M), Φ (b ⊗ₜ[k] m) = b ⊗ₜ[A] σ m := fun _ _ => rfl
  set Ψ₀ : (↥I) →+ N →+ ((↥I) ⊗[k] M) :=
    AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun y => b ⊗ₜ[k] π y)
      (fun y y' => by rw [map_add, TensorProduct.tmul_add]))
      (fun b b' => by ext y; simp [TensorProduct.add_tmul]) with hΨ₀def
  have hΨbal : ∀ (a : A) (b : ↥I) (y : N), Ψ₀ (a • b) y = Ψ₀ b (a • y) := by
    intro a b y
    show (a • b) ⊗ₜ[k] π y = b ⊗ₜ[k] π (a • y)
    rw [hπsmul, smul_eq_augmentation_smul hI ε hIker, TensorProduct.smul_tmul]
  set Ψ := TensorProduct.liftAddHom Ψ₀ hΨbal with hΨdef
  have hΨtmul : ∀ (b : ↥I) (y : N), Ψ (b ⊗ₜ[A] y) = b ⊗ₜ[k] π y := fun _ _ => rfl
  have hΨΦ : ∀ ξ : (↥I) ⊗[k] M, Ψ (Φ ξ) = ξ := by
    intro ξ
    induction ξ using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul b m => rw [hΦtmul, hΨtmul, hσ]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  refine ⟨(LinearMap.idealTensorSmul I N).toAddMonoidHom.comp Φ, ?_, ?_, ?_, ?_⟩
  · intro b y
    show LinearMap.idealTensorSmul I N (Φ (b ⊗ₜ[k] π y)) = (b : A) • y
    rw [hΦtmul, hlift b _ y (hσ _), LinearMap.idealTensorSmul_tmul]
  · intro u v h
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe] at h
    rw [← hΨΦ u, ← hΨΦ v, LinearMap.injective_idealTensorSmul I N h]
  · intro ξ
    induction ξ using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul b m =>
        show LinearMap.idealTensorSmul I N (Φ (b ⊗ₜ[k] m)) ∈ _
        rw [hΦtmul, LinearMap.idealTensorSmul_tmul]
        exact Submodule.smul_mem_smul b.2 Submodule.mem_top
    | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  · intro z hz
    refine Submodule.smul_induction_on hz (fun a ha y _ => ?_) ?_
    · refine ⟨(⟨a, ha⟩ : ↥I) ⊗ₜ[k] π y, ?_⟩
      show LinearMap.idealTensorSmul I N (Φ ((⟨a, ha⟩ : ↥I) ⊗ₜ[k] π y)) = a • y
      rw [hΦtmul, hlift _ _ y (hσ _), LinearMap.idealTensorSmul_tmul]
    · rintro u v ⟨ξu, rfl⟩ ⟨ξv, rfl⟩
      exact ⟨ξu + ξv, by rw [map_add]⟩

/-- **A relation over `I` descends to a relation over `M`.** If a finite combination
`∑ b l • y l` with coefficients in a square-zero ideal `I` vanishes in a flat `A`-module `N`,
then the corresponding tensor `∑ b l ⊗ₜ π (y l)` vanishes in `I ⊗[k] M`.

This is the form in which `exists_addMonoidHom_tmul_smul` is used: it says that the vector
recorded by a polynomial with coefficients in `I` is unchanged by altering that polynomial
within the kernel of the evaluation, which is the first of the two ambiguities Stacks 0DVZ
discusses in its step (vii). -/
theorem tmul_sum_eq_zero_of_smul_sum_eq_zero (ε : A →ₐ[k] k) (π : N →+ M) (I : Ideal A)
    [Module.Flat A N] (hI : I * I = ⊥)
    (hIker : ∀ a : A, a - algebraMap k A (ε a) ∈ I)
    (hπsmul : ∀ (a : A) (y : N), π (a • y) = ε a • π y)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ y : N, π y = 0 ↔ y ∈ I • (⊤ : Submodule A N))
    {ι : Type*} (s : Finset ι) (b : ι → ↥I) (y : ι → N)
    (h : ∑ l ∈ s, (b l : A) • y l = 0) :
    ∑ l ∈ s, (b l) ⊗ₜ[k] (π (y l)) = (0 : (↥I) ⊗[k] M) := by
  obtain ⟨θ, hθ, hθinj, -, -⟩ :=
    exists_addMonoidHom_tmul_smul ε π I hI hIker hπsmul hπsurj hπker
  refine hθinj ?_
  rw [map_sum, map_zero]
  rw [show ∑ l ∈ s, θ ((b l) ⊗ₜ[k] (π (y l))) = ∑ l ∈ s, (b l : A) • y l from
    Finset.sum_congr rfl fun l _ => hθ (b l) (y l)]
  exact h

end SquareZero

end Ideal

namespace MvPolynomial

/-- Weighted homogeneity is preserved by a change of the coefficient ring, because the
coefficients of the image are the images of the coefficients. -/
theorem IsWeightedHomogeneous.map {R S σ M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] {w : σ → M} {φ : MvPolynomial σ R} {m : M}
    (h : φ.IsWeightedHomogeneous w m) (f : R →+* S) :
    (MvPolynomial.map f φ).IsWeightedHomogeneous w m := by
  intro c hc
  refine h (fun h0 => hc ?_)
  rw [coeff_map, h0, map_zero]

universe u v w t

variable {k : Type u} {A : Type v} {P : Type w} {Q : Type t}
  [CommRing k] [CommRing A] [Algebra k A] [CommRing P] [Algebra k P] [CommRing Q] [Algebra A Q]

/-- **Naturality of multivariate evaluation in the coefficients.** If a ring map `π : Q → P`
takes the constants of `A` to the constants of `k` along `ε : A →ₐ[k] k` and takes the points
`q i` to the points `x i`, then it takes the value at `q` of a polynomial over `A` to the value
at `x` of its coefficientwise reduction. -/
theorem hom_aeval_eq_aeval_map (ε : A →ₐ[k] k) (π : Q →+* P)
    (hconst : ∀ a : A, π (algebraMap A Q a) = algebraMap k P (ε a))
    {n : ℕ} {q : Fin n → Q} {x : Fin n → P} (hq : ∀ i, π (q i) = x i)
    (G : MvPolynomial (Fin n) A) :
    π (aeval q G) = aeval x (MvPolynomial.map (ε : A →+* k) G) := by
  have hcomp : π.comp (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q).toRingHom =
      ((aeval x : MvPolynomial (Fin n) k →ₐ[k] P).toRingHom).comp
        (MvPolynomial.map (ε : A →+* k)) :=
    MvPolynomial.ringHom_ext (fun a => by simpa using hconst a) (fun i => by simpa using hq i)
  exact DFunLike.congr_fun hcomp G

/-- The structure map `k → A` is a coefficientwise section of an augmentation `ε : A →ₐ[k] k`,
so it provides a canonical lift of a polynomial over `k` to one over `A`. -/
theorem map_map_algebraMap (ε : A →ₐ[k] k) {n : ℕ} (G : MvPolynomial (Fin n) k) :
    MvPolynomial.map (ε : A →+* k) (MvPolynomial.map (algebraMap k A) G) = G := by
  rw [MvPolynomial.map_map]
  simpa using MvPolynomial.map_id G

/-- A polynomial killed by the coefficientwise reduction along an augmentation has all its
coefficients in the kernel, hence lies in `I • ⊤` as a submodule over the base. -/
theorem mem_smul_top_of_map_eq_zero (ε : A →ₐ[k] k) (I : Ideal A)
    (hεI : ∀ a : A, ε a = 0 → a ∈ I) {n : ℕ} {g : MvPolynomial (Fin n) A}
    (hg : MvPolynomial.map (ε : A →+* k) g = 0) :
    g ∈ I • (⊤ : Submodule A (MvPolynomial (Fin n) A)) := by
  classical
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  have hc : MvPolynomial.coeff m g ∈ I := by
    refine hεI _ ?_
    have hcm := MvPolynomial.coeff_map (ε : A →+* k) g m
    rw [hg, MvPolynomial.coeff_zero] at hcm
    exact hcm.symm
  have hmono : (MvPolynomial.monomial m) (MvPolynomial.coeff m g) =
      MvPolynomial.coeff m g • (MvPolynomial.monomial m) (1 : A) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hmono]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

end MvPolynomial

namespace GradedAlgebra

open MvPolynomial

universe u v w t

variable {k : Type u} {A : Type v} {P : Type w} {Q : Type t}
  [CommRing k] [CommRing A] [Algebra k A] [CommRing P] [Algebra k P] [CommRing Q] [Algebra A Q]

/-- **A weighted graded presentation is surjective in every weighted degree.** If the
evaluation `k[X_1, …, X_n] → P` at homogeneous elements `x i` of degrees `d i` is surjective,
then every homogeneous element of degree `e` is the value of a weighted homogeneous polynomial
of weighted degree `e`. -/
theorem exists_isWeightedHomogeneous_aeval_eq (gradingP : ℕ → Submodule k P)
    [GradedAlgebra gradingP] {n : ℕ} {d : Fin n → ℕ} {x : Fin n → P}
    (hx : ∀ i, x i ∈ gradingP (d i))
    (hxsurj : Function.Surjective (aeval x : MvPolynomial (Fin n) k →ₐ[k] P))
    {e : ℕ} {p : P} (hp : p ∈ gradingP e) :
    ∃ G : MvPolynomial (Fin n) k, IsWeightedHomogeneous d G e ∧ aeval x G = p := by
  let : GradedAlgebra (weightedHomogeneousSubmodule k d) :=
    MvPolynomial.weightedGradedAlgebra k d
  obtain ⟨G, hG, hGp⟩ := DirectSum.exists_mem_map_eq_of_surjective
    (ℳ := weightedHomogeneousSubmodule k d) (𝒩 := gradingP)
    ((aeval x : MvPolynomial (Fin n) k →ₐ[k] P).toRingHom.toAddMonoidHom)
    (fun e' G' hG' => aeval_mem_grading_of_isWeightedHomogeneous gradingP hx
      ((mem_weightedHomogeneousSubmodule k d e' G').mp hG')) hxsurj hp
  exact ⟨G, (mem_weightedHomogeneousSubmodule k d e G).mp hG, hGp⟩

variable (gradingP : ℕ → Submodule k P) (gradingQ : ℕ → Submodule A Q)
  [GradedAlgebra gradingP] [GradedAlgebra gradingQ]
  (ε : A →ₐ[k] k) (π : Q →+* P) (I : Ideal A)

/-- A reduction which is semilinear along an augmentation takes constants to constants. -/
theorem map_algebraMap_of_smul (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y) (a : A) :
    π (algebraMap A Q a) = algebraMap k P (ε a) := by
  rw [Algebra.algebraMap_eq_smul_one, hπsmul, map_one, Algebra.algebraMap_eq_smul_one]

/-- A semilinear reduction takes the value at `q` of the canonical lift of `G` to the value at
`x` of `G`. -/
private theorem hom_aeval_map_algebraMap (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    {n : ℕ} {q : Fin n → Q} {x : Fin n → P} (hq : ∀ i, π (q i) = x i)
    (G : MvPolynomial (Fin n) k) :
    π (aeval q (MvPolynomial.map (algebraMap k A) G)) = aeval x G := by
  rw [MvPolynomial.hom_aeval_eq_aeval_map ε π (map_algebraMap_of_smul ε π hπsmul) hq,
    MvPolynomial.map_map_algebraMap]

omit [Algebra k A] in
/-- **Homogeneous lifts of the generators of a weighted graded presentation.** Along a
degree-preserving surjection `π : Q → P` of graded algebras, homogeneous generators `x i` of
degrees `d i` lift to homogeneous elements `q i` of `Q` of the same degrees.

Neither finiteness nor freeness of the graded pieces of `Q` is used, and the identification of
`P` with a quotient of `Q` enters only through surjectivity of `π`. -/
theorem exists_homogeneous_lift_generators
    (hπmem : ∀ (e : ℕ) (y : Q), y ∈ gradingQ e → π y ∈ gradingP e)
    (hπsurj : Function.Surjective π)
    {n : ℕ} (d : Fin n → ℕ) (x : Fin n → P) (hx : ∀ i, x i ∈ gradingP (d i)) :
    ∃ q : Fin n → Q, (∀ i, q i ∈ gradingQ (d i)) ∧ ∀ i, π (q i) = x i := by
  choose q hq hq' using fun i => DirectSum.exists_mem_map_eq_of_surjective
    (ℳ := gradingQ) (𝒩 := gradingP) π.toAddMonoidHom hπmem hπsurj (hx i)
  exact ⟨q, hq, hq'⟩

omit [GradedAlgebra gradingP] [GradedAlgebra gradingQ] in
/-- **Surjectivity of the lifted evaluation.** If the evaluation `k[X_1, …, X_n] → P` at `x` is
surjective, `π : Q → P` is semilinear along `ε` with kernel contained in `I • Q`, the `q i` lift
the `x i`, and `I` is nilpotent, then the evaluation `A[X_1, …, X_n] → Q` at `q` is surjective.

This is the step the source calls *"surjective by Nakayama's lemma"*. No grading is involved:
the image of `A[X_1, …, X_n]` is an `A`-submodule `S` with `Q = S + I • Q`, and nilpotence of
`I` forces `S = Q`. -/
theorem surjective_aeval_of_lift
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπker : ∀ y : Q, π y = 0 → y ∈ I • (⊤ : Submodule A Q)) (hI : IsNilpotent I)
    {n : ℕ} {x : Fin n → P}
    (hxsurj : Function.Surjective (aeval x : MvPolynomial (Fin n) k →ₐ[k] P))
    {q : Fin n → Q} (hq : ∀ i, π (q i) = x i) :
    Function.Surjective (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q) := by
  have hS : Subalgebra.toSubmodule (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q).range = ⊤ := by
    refine Submodule.eq_top_of_le_sup_smul_top_of_isNilpotent hI (fun z _ => ?_)
    obtain ⟨G, hG⟩ := hxsurj (π z)
    set H := MvPolynomial.map (algebraMap k A) G with hHdef
    refine Submodule.mem_sup.mpr ⟨aeval q H, (Subalgebra.mem_toSubmodule _).mpr ⟨H, rfl⟩,
      z - aeval q H, hπker _ ?_, by ring⟩
    rw [map_sub, hHdef, hom_aeval_map_algebraMap ε π hπsmul hq, hG, sub_self]
  intro y
  have hy : y ∈ Subalgebra.toSubmodule (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q).range := by
    rw [hS]; exact Submodule.mem_top
  exact (Subalgebra.mem_toSubmodule _).mp hy

omit [GradedAlgebra gradingQ] in
/-- Every element of `I • Q_e` is the value at `q` of a weighted homogeneous polynomial of
weighted degree `e` all of whose coefficients lie in `I`, hence one reducing to zero over `k`.
This is the correction term of the diagram chase lifting a relation. -/
theorem exists_isWeightedHomogeneous_aeval_eq_of_mem_smul
    (hπmem : ∀ (e : ℕ) (y : Q), y ∈ gradingQ e → π y ∈ gradingP e)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπker : ∀ y : Q, π y = 0 → y ∈ I • (⊤ : Submodule A Q)) (hIsq : I * I = ⊥)
    (hεI : ∀ a ∈ I, ε a = 0)
    {n : ℕ} {d : Fin n → ℕ} {x : Fin n → P} (hx : ∀ i, x i ∈ gradingP (d i))
    (hxsurj : Function.Surjective (aeval x : MvPolynomial (Fin n) k →ₐ[k] P))
    {q : Fin n → Q} (hq : ∀ i, π (q i) = x i)
    {e : ℕ} {z : Q} (hz : z ∈ I • gradingQ e) :
    ∃ H : MvPolynomial (Fin n) A, IsWeightedHomogeneous d H e ∧
      MvPolynomial.map (ε : A →+* k) H = 0 ∧ aeval q H = z := by
  refine Submodule.smul_induction_on hz (fun a ha v hv => ?_) (fun u v hu hv => ?_)
  · obtain ⟨G, hG, hGv⟩ := exists_isWeightedHomogeneous_aeval_eq gradingP hx hxsurj
      (hπmem e v hv)
    set H₀ := MvPolynomial.map (algebraMap k A) G with hH₀
    have hπH₀ : π (aeval q H₀) = π v := by
      rw [hH₀, hom_aeval_map_algebraMap ε π hπsmul hq, hGv]
    have hdiff : a • (v - aeval q H₀) = 0 :=
      Submodule.smul_eq_zero_of_mem_smul_top_of_mul_eq_bot hIsq ha
        (hπker _ (by rw [map_sub, hπH₀, sub_self]))
    refine ⟨MvPolynomial.C a * H₀, ?_, ?_, ?_⟩
    · simpa using (isWeightedHomogeneous_C d a).mul (hG.map (algebraMap k A))
    · rw [map_mul, MvPolynomial.map_C, show (ε : A →+* k) a = ε a from rfl, hεI a ha,
        map_zero, zero_mul]
    · rw [map_mul, MvPolynomial.aeval_C, ← Algebra.smul_def]
      rw [smul_sub, sub_eq_zero] at hdiff
      exact hdiff.symm
  · obtain ⟨H₁, h₁, h₁', h₁''⟩ := hu
    obtain ⟨H₂, h₂, h₂', h₂''⟩ := hv
    exact ⟨H₁ + H₂, h₁.add h₂, by rw [map_add, h₁', h₂', add_zero],
      by rw [map_add, h₁'', h₂'']⟩

/-- **Homogeneous lifts of the relations of a weighted graded presentation.** Let `F` be a
weighted homogeneous polynomial of weighted degree `e` over `k` which is a relation of the
presentation of `P`, and let `q` be homogeneous lifts of the generators. If `I` is square zero
then `F` lifts to a weighted homogeneous polynomial of the same weighted degree over `A` which
is killed by the evaluation at `q`.

This is the *"small diagram chase"* of the source. The canonical coefficientwise lift
`MvPolynomial.map (algebraMap k A) F` already has the right weighted degree and reduces to `F`;
its value at `q` lies in `I • Q_e`, and `exists_isWeightedHomogeneous_aeval_eq_of_mem_smul`
produces a correction with coefficients in `I`, which therefore does not disturb the
reduction. -/
theorem exists_homogeneous_lift_relation
    (hπmem : ∀ (e : ℕ) (y : Q), y ∈ gradingQ e → π y ∈ gradingP e)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπker : ∀ y : Q, π y = 0 → y ∈ I • (⊤ : Submodule A Q)) (hIsq : I * I = ⊥)
    (hεI : ∀ a ∈ I, ε a = 0)
    {n : ℕ} {d : Fin n → ℕ} {x : Fin n → P} (hx : ∀ i, x i ∈ gradingP (d i))
    (hxsurj : Function.Surjective (aeval x : MvPolynomial (Fin n) k →ₐ[k] P))
    {q : Fin n → Q} (hqmem : ∀ i, q i ∈ gradingQ (d i)) (hq : ∀ i, π (q i) = x i)
    {e : ℕ} {F : MvPolynomial (Fin n) k} (hF : IsWeightedHomogeneous d F e)
    (hF0 : aeval x F = 0) :
    ∃ G : MvPolynomial (Fin n) A, IsWeightedHomogeneous d G e ∧
      MvPolynomial.map (ε : A →+* k) G = F ∧ aeval q G = 0 := by
  set F' := MvPolynomial.map (algebraMap k A) F with hF'def
  have hF' : IsWeightedHomogeneous d F' e := hF.map _
  have hmapF' : MvPolynomial.map (ε : A →+* k) F' = F := MvPolynomial.map_map_algebraMap ε F
  have hmem : aeval q F' ∈ gradingQ e :=
    aeval_mem_grading_of_isWeightedHomogeneous gradingQ hqmem hF'
  have hzker : π (aeval q F') = 0 := by
    rw [hF'def, hom_aeval_map_algebraMap ε π hπsmul hq, hF0]
  have hzI : aeval q F' ∈ I • gradingQ e := by
    have h2 := DirectSum.coe_decompose_mem_smul_grading (ℳ := gradingQ) (hπker _ hzker) e
    rwa [DirectSum.decompose_of_mem_same gradingQ hmem] at h2
  obtain ⟨H, hH, hHmap, hHval⟩ := exists_isWeightedHomogeneous_aeval_eq_of_mem_smul
    gradingP gradingQ ε π I hπmem hπsmul hπker hIsq hεI hx hxsurj hq hzI
  refine ⟨F' - H, hF'.sub hH, ?_, ?_⟩
  · rw [map_sub, hmapF', hHmap, sub_zero]
  · rw [map_sub, hHval, sub_self]

/-- **The kernel of the lifted evaluation is captured by the lifted relations up to `I • ⊤`.**
If `g` over `A` is killed by the evaluation at `q`, then its reduction is killed by the
evaluation at `x`, hence lies in the ideal generated by the relations `F j`; lifting the
coefficients of a representation of that reduction and subtracting leaves a polynomial all of
whose coefficients lie in `I`.

This is the bookkeeping half of the step the source states without proof; the mathematical half
is `LinearMap.ker_eq_bot_of_ker_le_smul_top_of_flat`. No grading is involved. -/
theorem mem_sup_span_smul_top_of_aeval_eq_zero
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hεI : ∀ a : A, ε a = 0 → a ∈ I)
    {n r : ℕ} {x : Fin n → P} {F : Fin r → MvPolynomial (Fin n) k}
    (hxker : ∀ G : MvPolynomial (Fin n) k, aeval x G = 0 → G ∈ Ideal.span (Set.range F))
    {q : Fin n → Q} (hq : ∀ i, π (q i) = x i)
    (Flift : Fin r → MvPolynomial (Fin n) A)
    (hFmap : ∀ j, MvPolynomial.map (ε : A →+* k) (Flift j) = F j)
    {g : MvPolynomial (Fin n) A} (hg : aeval q g = 0) :
    g ∈ (Ideal.span (Set.range Flift)).restrictScalars A ⊔
      I • (⊤ : Submodule A (MvPolynomial (Fin n) A)) := by
  classical
  have hconst := map_algebraMap_of_smul ε π hπsmul
  have hx0 : aeval x (MvPolynomial.map (ε : A →+* k) g) = 0 := by
    rw [← MvPolynomial.hom_aeval_eq_aeval_map ε π hconst hq, hg, map_zero]
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (MvPolynomial (Fin n) k)).mp (hxker _ hx0)
  set g' := ∑ j : Fin r, MvPolynomial.map (algebraMap k A) (c j) * Flift j with hg'def
  refine Submodule.mem_sup.mpr ⟨g', ?_, g - g', ?_, by ring⟩
  · exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · refine MvPolynomial.mem_smul_top_of_map_eq_zero ε I hεI ?_
    rw [map_sub, hg'def, map_sum]
    rw [show ∑ j : Fin r, MvPolynomial.map (ε : A →+* k)
        (MvPolynomial.map (algebraMap k A) (c j) * Flift j) = ∑ j : Fin r, c j * F j from
      Finset.sum_congr rfl fun j _ => by
        rw [map_mul, MvPolynomial.map_map_algebraMap, hFmap j]]
    rw [← hc]
    simp [smul_eq_mul, sub_self]

/-- **The lifted relations present the lift.** For `I` square zero with `ker ε ⊆ I` and `Q` flat
over `A`, a family of lifts `Flift j` of the relations `F j` which are killed by the evaluation
at `q` generates the *whole* kernel of that evaluation.

This is the step Stacks 0DVZ states and does not prove, *"`k[ε][X_1, …, X_n]/(F_{ε, 1}, …,
F_{ε, m}) → Q` is a presentation of `Q` by flatness of `Q` over `k[ε]`"*. Its content is
`LinearMap.ker_eq_bot_of_ker_le_smul_top_of_flat` applied to the `A`-module quotient of
`A[X_1, …, X_n]` by the ideal of the lifted relations, with
`mem_sup_span_smul_top_of_aeval_eq_zero` supplying the hypothesis on the kernel. No grading and
no finiteness are used. -/
theorem aeval_eq_zero_iff_mem_span_of_flat [Module.Flat A Q] (hIsq : I * I = ⊥)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hεI : ∀ a : A, ε a = 0 → a ∈ I)
    {n r : ℕ} {x : Fin n → P} {F : Fin r → MvPolynomial (Fin n) k}
    (hxker : ∀ G : MvPolynomial (Fin n) k, aeval x G = 0 → G ∈ Ideal.span (Set.range F))
    {q : Fin n → Q} (hq : ∀ i, π (q i) = x i)
    (hqsurj : Function.Surjective (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q))
    (Flift : Fin r → MvPolynomial (Fin n) A)
    (hFmap : ∀ j, MvPolynomial.map (ε : A →+* k) (Flift j) = F j)
    (hFval : ∀ j, aeval q (Flift j) = 0)
    (g : MvPolynomial (Fin n) A) :
    aeval q g = 0 ↔ g ∈ Ideal.span (Set.range Flift) := by
  classical
  have hJker : ∀ h ∈ Ideal.span (Set.range Flift), aeval q h = 0 := by
    have hle : Ideal.span (Set.range Flift) ≤
        RingHom.ker (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q).toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hFval j
    exact fun h hh => hle hh
  refine ⟨fun hg => ?_, fun hg => hJker g hg⟩
  set JA := (Ideal.span (Set.range Flift)).restrictScalars A with hJA
  have hle : JA ≤ LinearMap.ker (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q).toLinearMap :=
    fun h hh => hJker h hh
  set φ := Submodule.liftQ JA ((aeval q : MvPolynomial (Fin n) A →ₐ[A] Q).toLinearMap) hle
    with hφdef
  have hφmk : ∀ h, φ (JA.mkQ h) = aeval q h := fun _ => rfl
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨h, rfl⟩ := hqsurj y
    exact ⟨JA.mkQ h, hφmk h⟩
  have hφker : LinearMap.ker φ ≤ I • ⊤ := by
    intro ξ hξ
    obtain ⟨h, rfl⟩ := JA.mkQ_surjective ξ
    have hzero : aeval q h = 0 := by rw [← hφmk h]; exact hξ
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp
      (mem_sup_span_smul_top_of_aeval_eq_zero ε π I hπsmul hεI hxker hq Flift hFmap hzero)
    have hu0 : JA.mkQ u = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hu
    have h1 : JA.mkQ h = JA.mkQ v := by rw [← huv, map_add, hu0, zero_add]
    rw [h1]
    have h2 : (I • (⊤ : Submodule A (MvPolynomial (Fin n) A))).map JA.mkQ ≤ I • ⊤ := by
      rw [Submodule.map_smul'' I ⊤ JA.mkQ]
      exact Submodule.smul_mono le_rfl le_top
    exact h2 ⟨v, hv, rfl⟩
  have hbot := LinearMap.ker_eq_bot_of_ker_le_smul_top_of_flat hIsq φ hφsurj hφker
  have hzero : JA.mkQ g = 0 := by
    rw [← Submodule.mem_bot (R := A), ← hbot]
    show φ (JA.mkQ g) = 0
    rw [hφmk, hg]
  have hmem : g ∈ JA := by
    rw [← Submodule.ker_mkQ JA, LinearMap.mem_ker]
    exact hzero
  exact hmem

end GradedAlgebra

end
