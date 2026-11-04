module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections

/-!
# The lifting problem for filtered colimits of smooth algebras

Let `R → Λ` be a ring map and `I ⊂ R` an ideal with `I² = 0` such that `Λ/IΛ` is a filtered
colimit of smooth `R/I`-algebras. Then any `R`-algebra `A` of finite presentation mapping to `Λ`
maps to `Λ` through a quotient `B/J` of a smooth `R`-algebra `B` by a finitely generated ideal
`J ⊂ IB`. This is the first step towards the stability of ind-smoothness under infinitesimal flat
deformations. When `R → Λ` is in addition flat, the ideal `J` can be removed at the cost of
enlarging `B`: every `R`-algebra map from a smooth algebra `B` to `Λ` extends over a map
`B → B'` to a smooth algebra that kills a prescribed finitely generated ideal `J ⊆ IB` lying in
the kernel.

Combining the two, `Λ` itself is a filtered colimit of smooth `R`-algebras: a map from an
`R`-algebra of finite presentation factors through `B/J` and then, `J` being killed, through the
smooth algebra `B'`. Induction on the order of nilpotency extends this from `I² = 0` to any
nilpotent `I`, which is the stability of ind-smoothness under infinitesimal flat deformations.

## Main results

* `Stacks.Smoothing.exists_smooth_quotient_factorization`: an `R`-algebra map `A → Λ` with `A` of
  finite presentation factors as `A → B/J → Λ` with `B` smooth over `R` and `J ⊂ IB` finitely
  generated.
* `Stacks.Smoothing.exists_smooth_factorization_of_fg_le_map`: if moreover `Λ` is flat over `R`,
  then an `R`-algebra map `B → Λ` with `B` smooth over `R` factors as `B → B' → Λ` with `B'`
  smooth over `R` and with `B → B'` killing any prescribed finitely generated ideal `J ⊆ IB`
  annihilated by `B → Λ`.
* `Stacks.Smoothing.ind_smooth_of_isNilpotent`: if `I` is nilpotent, `Λ/IΛ` is a filtered colimit
  of smooth `R/I`-algebras and `R → Λ` is flat, then `Λ` is a filtered colimit of smooth
  `R`-algebras.

## Implementation notes

"`Λ/IΛ` is a filtered colimit of smooth `R/I`-algebras" is `CategoryTheory.ObjectProperty.ind`
of the ring-map predicate `RingHom.Smooth` on the category `Under (CommRingCat.of (R/I))` of
`R/I`-algebras, the spelling used in Lemma `07C3`; the structure map of `Λ/IΛ` over `R/I` is the
instance `Ideal.Quotient.algebraQuotientOfLEComap`, which is the map induced by `R → Λ` on
quotients.

Rather than the source's route through standard smooth algebras, the proof lifts a smooth
`R/I`-algebra to a smooth `R`-algebra directly (Tag `07M8`). Writing `Λ/IΛ`-valued factorizations,
one first factors `A/IA → B̄ → Λ/IΛ` with `B̄` smooth over `R/I`, then adjoins to `A` variables
`t_i` for a presentation `B̄ = A/IA[t]/(ḡ)` together with variables `δ_{ij}` absorbing the
discrepancies `φ(g_i)(λ) = ∑ ε_{ij} μ_{ij} ∈ IΛ`. The resulting `A`-algebra `A'` of finite
presentation maps to `Λ` and satisfies `A'/IA' ≅ B̄[δ]`, which is smooth over `R/I`. Lifting
`A'/IA'` to a smooth `R`-algebra `B` and lifting `B → B/IB ≅ A'/IA'` along the square-zero
surjection `A' → A'/IA'` by formal smoothness gives a map `B → A'` which is an isomorphism modulo
`I`, hence surjective; its kernel `J` lies in `IB` and is finitely generated because `B` and `A'`
are both of finite presentation over `R`.

Killing a finitely generated ideal `J ⊆ IB` reduces, by induction on a generating set, to killing
a single element `h = ∑ εᵢ bᵢ` with `εᵢ ∈ I`. Flatness enters through the equational criterion
(Tag `00HK`), which rewrites `∑ εᵢ φ(bᵢ) = 0` as `φ(bᵢ) = ∑ aᵢⱼ λⱼ` with `∑ᵢ εᵢ aᵢⱼ = 0`; the
relations `bᵢ = ∑ aᵢⱼ xⱼ` are then imposed on an auxiliary algebra `B[x]`, to which Tag `07CK`
applies, and `h` dies because `∑ᵢ εᵢ aᵢⱼ = 0` and `I² = 0`.

For a nilpotent `I` with `I ^ (n + 1) = 0` the reduction to the square-zero case runs over the
ideal `I₁ = I ^ n` when `n ≥ 1`: it satisfies `I₁² = 0`, the ideal `I·(R/I₁)` has `n`-th power
zero, and `Λ/I₁Λ` is flat over `R/I₁` because it is the base change `(R/I₁) ⊗_R Λ`
(`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`). So induction over `R/I₁` makes `Λ/I₁Λ` a
filtered colimit of smooth `R/I₁`-algebras, and the square-zero case applied to `I₁` concludes.
The induction hypothesis is about `(R/I₁)/(I·(R/I₁))` and `(Λ/I₁Λ)/(I·(Λ/I₁Λ))`, which are `R/I`
and `Λ/IΛ` only up to the third isomorphism theorem (`DoubleQuot.quotQuotEquivQuotOfLE`), so being
a filtered colimit of smooth algebras is first transported along a commuting square of ring
equivalences: a `ColimitPresentation` is carried along the equivalence `Under.map` of an
isomorphism of base rings, smoothness being stable under precomposition with an isomorphism.

## References

* [Stacks Project, Tag 07CK](https://stacks.math.columbia.edu/tag/07CK)
* [Stacks Project, Tag 07CL](https://stacks.math.columbia.edu/tag/07CL)
* [Stacks Project, Tag 07CM](https://stacks.math.columbia.edu/tag/07CM)
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial TensorProduct

noncomputable section

namespace Stacks.Smoothing

/-- Ring-level form of the factorization criterion for filtered colimits: if `Λ` is a filtered
colimit of smooth `R`-algebras, every map to `Λ` from an `R`-algebra of finite presentation
factors through a smooth `R`-algebra. -/
private theorem exists_smooth_factorization_of_ind {R₀ Λ₀ : Type u} [CommRing R₀] [CommRing Λ₀]
    [Algebra R₀ Λ₀]
    (h : ObjectProperty.ind.{u} (fun B : Under (CommRingCat.of R₀) ↦ B.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap R₀ Λ₀))))
    {A₀ : Type u} [CommRing A₀] [Algebra R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (f : A₀ →ₐ[R₀] Λ₀) :
    ∃ (B₀ : Type u) (_ : CommRing B₀) (alg : Algebra R₀ B₀),
      letI := alg
      Algebra.Smooth R₀ B₀ ∧ ∃ (u : A₀ →ₐ[R₀] B₀) (v : B₀ →ₐ[R₀] Λ₀), v.comp u = f := by
  obtain ⟨B, p, q, hpq, hB⟩ :=
    (CommRingCat.ind_under_iff_exists_factorization _
      (fun _ hB ↦ RingHom.Smooth.finitePresentation hB)).1 h
      (Under.mk (CommRingCat.ofHom (algebraMap R₀ A₀)))
      (by
        show (algebraMap R₀ A₀).FinitePresentation
        exact RingHom.finitePresentation_algebraMap.mpr ‹Algebra.FinitePresentation R₀ A₀›)
      (Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext x; exact f.commutes x))
  let : Algebra R₀ B.right := B.hom.hom.toAlgebra
  change Algebra.Smooth R₀ B.right at hB
  refine ⟨B.right, inferInstance, inferInstance, hB,
    { p.right.hom with commutes' := fun r => ?_ },
    { q.right.hom with commutes' := fun r => ?_ }, ?_⟩
  · exact congrArg (fun z : CommRingCat.of R₀ ⟶ B.right ↦ z.hom r) p.w
  · exact congrArg (fun z : CommRingCat.of R₀ ⟶ CommRingCat.of Λ₀ ↦ z.hom r) q.w
  · exact AlgHom.ext fun x => congrArg (fun z ↦ z.right.hom x) hpq

/-- An element of `K B` is a `B`-linear combination of images of elements of `K`, indexed by
`Fin m`. -/
private theorem exists_sum_mul_algebraMap_of_mem_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {K : Ideal A} {x : B} (hx : x ∈ K.map (algebraMap A B)) :
    ∃ (m : ℕ) (c : Fin m → B) (k : Fin m → A),
      (∀ j, k j ∈ K) ∧ x = ∑ j, c j * algebraMap A B (k j) := by
  obtain ⟨m, c, y, hy⟩ := Submodule.mem_span_set'.mp
    (show x ∈ Submodule.span B (algebraMap A B '' (K : Set A)) from hx)
  choose k hkmem hkeq using fun j : Fin m => (y j).2
  refine ⟨m, c, k, hkmem, ?_⟩
  rw [← hy]
  exact Finset.sum_congr rfl fun j _ => by rw [hkeq j]; rfl

/-- The square of the extension of an ideal of square zero is zero. -/
private theorem map_sq_eq_bot {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R}
    (hI : I ^ 2 = ⊥) : I.map (algebraMap R B) ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, hI, Ideal.map_bot]

section Relations

variable {A : Type u} [CommRing A] (K : Ideal A)
    {Bb : Type u} [CommRing Bb] [Algebra (A ⧸ K) Bb]

/-- An `A/K`-algebra map out of a polynomial ring sends a constant to its image in the base. -/
private theorem apply_C_mk {n : ℕ} (π : MvPolynomial (Fin n) (A ⧸ K) →ₐ[A ⧸ K] Bb) (a : A) :
    π (MvPolynomial.C (Ideal.Quotient.mk K a)) = algebraMap (A ⧸ K) Bb (Ideal.Quotient.mk K a) :=
  π.commutes _

/-- Adjoining to `A` variables `t_i` and `δ_j` subject to relations `g_i - ∑_j k_{ij} δ_{ij}`
with `k_{ij} ∈ K` produces an algebra whose reduction modulo `K` is a polynomial algebra in the
`δ`'s over `A/K[t]/(ḡ)`. -/
private theorem exists_quotientEquiv_mvPolynomial
    {n : ℕ} (π : MvPolynomial (Fin n) (A ⧸ K) →ₐ[A ⧸ K] Bb) (hπ : Function.Surjective π)
    {S : Type u} (gb : S → MvPolynomial (Fin n) (A ⧸ K))
    (hkerπ : RingHom.ker π.toRingHom = Ideal.span (Set.range gb))
    (g : S → MvPolynomial (Fin n) A)
    (hg : ∀ x, MvPolynomial.map (Ideal.Quotient.mk K) (g x) = gb x)
    {Δ : Type u} (m : S → ℕ) (kk : (x : S) → Fin (m x) → A) (hkk : ∀ x j, kk x j ∈ K)
    (ι : (x : S) → Fin (m x) → Δ)
    (ρ : S → MvPolynomial (Fin n ⊕ Δ) A)
    (hρ : ∀ x, ρ x = rename Sum.inl (g x) -
      ∑ j : Fin (m x), MvPolynomial.C (kk x j) * X (Sum.inr (ι x j)))
    (N : Ideal (MvPolynomial (Fin n ⊕ Δ) A)) (hN : N = Ideal.span (Set.range ρ)) :
    ∃ e : ((MvPolynomial (Fin n ⊕ Δ) A ⧸ N) ⧸
        K.map (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N))) ≃+* MvPolynomial Δ Bb,
      ∀ a : A, e (Ideal.Quotient.mk _ (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N) a)) =
        MvPolynomial.C (algebraMap (A ⧸ K) Bb (Ideal.Quotient.mk K a)) := by
  classical
  have hρmem : ∀ x, ρ x ∈ N := fun x => hN ▸ Ideal.subset_span ⟨x, rfl⟩
  have hgbker : ∀ x, π (gb x) = 0 := fun x =>
    RingHom.mem_ker.mp (hkerπ ▸ Ideal.subset_span ⟨x, rfl⟩)
  have halg : ∀ a : A, algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N) a =
      Ideal.Quotient.mk N (MvPolynomial.C a) := fun a => rfl
  obtain ⟨Φ₀, hΦ₀C, hΦ₀Xl, hΦ₀Xr⟩ :
      ∃ f : MvPolynomial (Fin n ⊕ Δ) A →+* MvPolynomial Δ Bb,
        (∀ a : A, f (MvPolynomial.C a) =
          MvPolynomial.C (algebraMap (A ⧸ K) Bb (Ideal.Quotient.mk K a))) ∧
        (∀ i, f (X (Sum.inl i)) = MvPolynomial.C (π (X i))) ∧
        (∀ d : Δ, f (X (Sum.inr d)) = X d) :=
    ⟨MvPolynomial.eval₂Hom
      ((MvPolynomial.C : Bb →+* MvPolynomial Δ Bb).comp
        ((algebraMap (A ⧸ K) Bb).comp (Ideal.Quotient.mk K)))
      (Sum.elim (fun i : Fin n => MvPolynomial.C (π (X i))) (fun d : Δ => X d)),
      by simp, by simp, by simp⟩
  have hΦ₀ren : ∀ p : MvPolynomial (Fin n) A,
      Φ₀ (rename Sum.inl p) =
        MvPolynomial.C (π (MvPolynomial.map (Ideal.Quotient.mk K) p)) := by
    have h : Φ₀.comp (MvPolynomial.rename (R := A) Sum.inl (τ := Fin n ⊕ Δ)).toRingHom =
        (MvPolynomial.C : Bb →+* MvPolynomial Δ Bb).comp
          (π.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk K))) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          MvPolynomial.rename_C, MvPolynomial.map_C, hΦ₀C]
        rw [apply_C_mk]
      · intro i
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          MvPolynomial.rename_X, MvPolynomial.map_X, hΦ₀Xl]
    exact fun p => RingHom.congr_fun h p
  have hΦ₀ρ : ∀ x, Φ₀ (ρ x) = 0 := by
    intro x
    rw [hρ x, map_sub, map_sum, hΦ₀ren, hg x, hgbker x, map_zero]
    rw [show ∑ j : Fin (m x), Φ₀ (MvPolynomial.C (kk x j) * X (Sum.inr (ι x j))) = 0 from
      Finset.sum_eq_zero fun j _ => by
        rw [map_mul, hΦ₀C, Ideal.Quotient.eq_zero_iff_mem.mpr (hkk x j), map_zero,
          MvPolynomial.C_0, zero_mul]]
    simp
  have hΦ₀N : N ≤ RingHom.ker Φ₀ := hN ▸ Ideal.span_le.mpr (Set.range_subset_iff.mpr hΦ₀ρ)
  obtain ⟨Φ, hΦ⟩ : ∃ f : ((MvPolynomial (Fin n ⊕ Δ) A ⧸ N) ⧸
      K.map (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N))) →+* MvPolynomial Δ Bb,
      ∀ p, f (Ideal.Quotient.mk _ (Ideal.Quotient.mk N p)) = Φ₀ p := by
    refine ⟨Ideal.Quotient.lift _
      (Ideal.Quotient.lift N Φ₀ (fun p hp => hΦ₀N hp)) ?_, fun p => rfl⟩
    intro q hq
    refine RingHom.mem_ker.mp (Ideal.map_le_iff_le_comap.mpr ?_ hq)
    intro a ha
    refine Ideal.mem_comap.mpr (RingHom.mem_ker.mpr ?_)
    show Φ₀ (MvPolynomial.C a) = 0
    rw [hΦ₀C, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, MvPolynomial.C_0]
  have hKCmem : ∀ a ∈ K,
      Ideal.Quotient.mk (K.map (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N)))
        (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N) a) = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
  obtain ⟨α, hα⟩ : ∃ f : (A ⧸ K) →+* ((MvPolynomial (Fin n ⊕ Δ) A ⧸ N) ⧸
      K.map (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N))),
      ∀ a : A, f (Ideal.Quotient.mk K a) =
        Ideal.Quotient.mk _ (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N) a) :=
    ⟨Ideal.Quotient.lift K ((Ideal.Quotient.mk _).comp
      (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N))) hKCmem, fun a => rfl⟩
  obtain ⟨Ξ, hΞC, hΞX⟩ : ∃ f : MvPolynomial (Fin n) (A ⧸ K) →+*
      ((MvPolynomial (Fin n ⊕ Δ) A ⧸ N) ⧸
        K.map (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N))),
      (∀ r, f (MvPolynomial.C r) = α r) ∧
      (∀ i, f (X i) = Ideal.Quotient.mk _ (Ideal.Quotient.mk N (X (Sum.inl i)))) :=
    ⟨MvPolynomial.eval₂Hom α
      (fun i => Ideal.Quotient.mk _ (Ideal.Quotient.mk N (X (Sum.inl i)))), by simp, by simp⟩
  have hΞmap : ∀ p : MvPolynomial (Fin n) A,
      Ξ (MvPolynomial.map (Ideal.Quotient.mk K) p) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk N (rename Sum.inl p)) := by
    have h : Ξ.comp (MvPolynomial.map (Ideal.Quotient.mk K)) =
        ((Ideal.Quotient.mk _).comp (Ideal.Quotient.mk N)).comp
          (MvPolynomial.rename (R := A) Sum.inl (τ := Fin n ⊕ Δ)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, MvPolynomial.map_C, hΞC, hα, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, MvPolynomial.rename_C, halg]
      · intro i
        simp only [RingHom.comp_apply, MvPolynomial.map_X, hΞX, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, MvPolynomial.rename_X]
    exact fun p => RingHom.congr_fun h p
  have hΞgb : ∀ x, Ξ (gb x) = 0 := by
    intro x
    rw [← hg x, hΞmap]
    have h1 : Ideal.Quotient.mk N (rename Sum.inl (g x)) =
        Ideal.Quotient.mk N
          (∑ j : Fin (m x), MvPolynomial.C (kk x j) * X (Sum.inr (ι x j))) := by
      have h2 := Ideal.Quotient.eq_zero_iff_mem.mpr (hρmem x)
      rw [hρ x, map_sub, sub_eq_zero] at h2
      exact h2
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [h1, map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul, show Ideal.Quotient.mk N (MvPolynomial.C (kk x j)) =
      algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N) (kk x j) from (halg _).symm]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hkk x j))
  have hΞker : RingHom.ker π.toRingHom ≤ RingHom.ker Ξ :=
    hkerπ ▸ Ideal.span_le.mpr (Set.range_subset_iff.mpr hΞgb)
  obtain ⟨χ, hχ0⟩ : ∃ f : Bb →+* ((MvPolynomial (Fin n ⊕ Δ) A ⧸ N) ⧸
      K.map (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N))), f.comp π.toRingHom = Ξ := by
    refine ⟨(Ideal.Quotient.lift (RingHom.ker π.toRingHom) Ξ (fun p hp => hΞker hp)).comp
      (π.toRingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom, ?_⟩
    rw [RingHom.comp_assoc, RingHom.quotientKerEquivOfSurjective_symm_comp]
    exact RingHom.ext fun p => rfl
  have hχ : ∀ p, χ (π p) = Ξ p := fun p => RingHom.congr_fun hχ0 p
  obtain ⟨Ψ, hΨC, hΨX⟩ : ∃ f : MvPolynomial Δ Bb →+* ((MvPolynomial (Fin n ⊕ Δ) A ⧸ N) ⧸
      K.map (algebraMap A (MvPolynomial (Fin n ⊕ Δ) A ⧸ N))),
      (∀ b, f (MvPolynomial.C b) = χ b) ∧
      (∀ d : Δ, f (X d) = Ideal.Quotient.mk _ (Ideal.Quotient.mk N (X (Sum.inr d)))) :=
    ⟨MvPolynomial.eval₂Hom χ
      (fun d => Ideal.Quotient.mk _ (Ideal.Quotient.mk N (X (Sum.inr d)))), by simp, by simp⟩
  have hΦΞ : ∀ p : MvPolynomial (Fin n) (A ⧸ K), Φ (Ξ p) = MvPolynomial.C (π p) := by
    have h : Φ.comp Ξ = (MvPolynomial.C : Bb →+* MvPolynomial Δ Bb).comp π.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        simp only [RingHom.comp_apply, hΞC, hα, halg, hΦ, hΦ₀C, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe]
        rw [apply_C_mk]
      · intro i
        simp only [RingHom.comp_apply, hΞX, hΦ, hΦ₀Xl, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact fun p => RingHom.congr_fun h p
  have hright : ∀ t, Φ (Ψ t) = t := by
    have h : Φ.comp Ψ = RingHom.id (MvPolynomial Δ Bb) := by
      apply MvPolynomial.ringHom_ext
      · intro b
        obtain ⟨p, rfl⟩ := hπ b
        simp only [RingHom.comp_apply, hΨC, hχ, hΦΞ, RingHom.id_apply]
      · intro d
        simp only [RingHom.comp_apply, hΨX, hΦ, hΦ₀Xr, RingHom.id_apply]
    exact fun t => RingHom.congr_fun h t
  have hleft : ∀ q, Ψ (Φ q) = q := by
    have h : Ψ.comp (Φ.comp ((Ideal.Quotient.mk _).comp (Ideal.Quotient.mk N))) =
        (Ideal.Quotient.mk _).comp (Ideal.Quotient.mk N) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, hΦ, hΦ₀C, hΨC]
        rw [← apply_C_mk K π, hχ, hΞC, hα, halg]
      · intro i
        cases i with
        | inl i => simp only [RingHom.comp_apply, hΦ, hΦ₀Xl, hΨC, hχ, hΞX]
        | inr d => simp only [RingHom.comp_apply, hΦ, hΦ₀Xr, hΨX]
    intro q
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact RingHom.congr_fun h p
  refine ⟨{ Φ with invFun := Ψ, left_inv := hleft, right_inv := hright }, fun a => ?_⟩
  show Φ _ = _
  rw [halg a, hΦ, hΦ₀C]

/-- **Adjoining enough variables to make the relations hold.** Let `K ⊂ A` be an ideal and `Λ` an
`A`-algebra. Every `A/K`-algebra `Bb` of finite presentation mapping to `Λ/KΛ` arises, after
adjoining finitely many further variables, as the reduction modulo `K` of an `A`-algebra of finite
presentation mapping to `Λ`. -/
private theorem exists_finitePresentation_quotientEquiv
    {A : Type u} [CommRing A] (K : Ideal A)
    {Λ : Type u} [CommRing Λ] [Algebra A Λ]
    {Bb : Type u} [CommRing Bb] [Algebra (A ⧸ K) Bb]
    [Algebra.FinitePresentation (A ⧸ K) Bb]
    (ψ : Bb →+* (Λ ⧸ K.map (algebraMap A Λ)))
    (hψ : ∀ a : A, ψ (algebraMap (A ⧸ K) Bb (Ideal.Quotient.mk K a)) =
      Ideal.Quotient.mk _ (algebraMap A Λ a)) :
    ∃ (Δ : Type u) (_ : Finite Δ) (Cc : Type u) (_ : CommRing Cc) (alg : Algebra A Cc),
      letI := alg
      Algebra.FinitePresentation A Cc ∧
        ∃ (_ : Cc →ₐ[A] Λ)
          (e : (Cc ⧸ K.map (algebraMap A Cc)) ≃+* MvPolynomial Δ Bb),
          ∀ a : A, e (Ideal.Quotient.mk _ (algebraMap A Cc a)) =
            MvPolynomial.C (algebraMap (A ⧸ K) Bb (Ideal.Quotient.mk K a)) := by
  classical
  obtain ⟨n, π, hπ, hker⟩ := Algebra.FinitePresentation.out (R := A ⧸ K) (A := Bb)
  obtain ⟨s, hs⟩ := hker
  have hmapsurj : Function.Surjective (MvPolynomial.map (Ideal.Quotient.mk K) :
      MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) (A ⧸ K)) :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  choose g hg using fun x : {x // x ∈ s} => hmapsurj (x : MvPolynomial (Fin n) (A ⧸ K))
  choose lam hlam using fun i : Fin n => Ideal.Quotient.mk_surjective
    (I := K.map (algebraMap A Λ)) (ψ (π (X i)))
  have hcomm : ((Ideal.Quotient.mk (K.map (algebraMap A Λ))).comp
      (MvPolynomial.aeval lam : MvPolynomial (Fin n) A →ₐ[A] Λ).toRingHom) =
      ψ.comp (π.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk K))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.aeval_C]
      rw [apply_C_mk, hψ a]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.aeval_X]
      exact hlam i
  have hgker : ∀ x : {x // x ∈ s}, π (x : MvPolynomial (Fin n) (A ⧸ K)) = 0 := fun x =>
    RingHom.mem_ker.mp (hs ▸ Ideal.subset_span x.2)
  have hvanish : ∀ x : {x // x ∈ s},
      (MvPolynomial.aeval lam : MvPolynomial (Fin n) A →ₐ[A] Λ) (g x) ∈
        K.map (algebraMap A Λ) := by
    intro x
    refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    have h2 := RingHom.congr_fun hcomm (g x)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
    rw [h2, hg x, hgker x, map_zero]
  choose m cc kk hkkmem hsum using fun x => exists_sum_mul_algebraMap_of_mem_map (hvanish x)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : {x // x ∈ s} →
      MvPolynomial (Fin n ⊕ ((x : {x // x ∈ s}) × Fin (m x))) A,
      ∀ x, ρ x = rename Sum.inl (g x) -
        ∑ j : Fin (m x), MvPolynomial.C (kk x j) * X (Sum.inr ⟨x, j⟩) := ⟨_, fun _ => rfl⟩
  obtain ⟨Θ, hΘC, hΘinl, hΘinr⟩ :
      ∃ f : MvPolynomial (Fin n ⊕ ((x : {x // x ∈ s}) × Fin (m x))) A →ₐ[A] Λ,
        (∀ a : A, f (MvPolynomial.C a) = algebraMap A Λ a) ∧
        (∀ p : MvPolynomial (Fin n) A, f (rename Sum.inl p) =
          (MvPolynomial.aeval lam : MvPolynomial (Fin n) A →ₐ[A] Λ) p) ∧
        (∀ x j, f (X (Sum.inr ⟨x, j⟩)) = cc x j) :=
    ⟨MvPolynomial.aeval (Sum.elim lam fun d => cc d.1 d.2), fun a => by simp,
      fun p => by simp [MvPolynomial.aeval_rename, Sum.elim_comp_inl], fun x j => by simp⟩
  have hΘρ : ∀ x, Θ (ρ x) = 0 := by
    intro x
    rw [hρ x, map_sub, hΘinl, map_sum, hsum x, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_mul, hΘC, hΘinr]; exact mul_comm _ _
  have hΘN : ∀ p ∈ Ideal.span (Set.range ρ), Θ p = 0 := fun p hp =>
    (Ideal.span_le.mpr (Set.range_subset_iff.mpr hΘρ) :
      Ideal.span (Set.range ρ) ≤ RingHom.ker Θ.toRingHom) hp
  have hkerπ : RingHom.ker π.toRingHom =
      Ideal.span (Set.range fun x : {x // x ∈ s} => (x : MvPolynomial (Fin n) (A ⧸ K))) := by
    rw [← hs]
    congr 1
    ext y
    simp
  obtain ⟨e, he⟩ := exists_quotientEquiv_mvPolynomial K (Bb := Bb) (n := n) π hπ
    (S := {x // x ∈ s}) (gb := fun x => (x : MvPolynomial (Fin n) (A ⧸ K))) (hkerπ := hkerπ)
    (g := g) (hg := hg) (Δ := (x : {x // x ∈ s}) × Fin (m x)) (m := m) (kk := kk)
    (hkk := hkkmem) (ι := fun x j => ⟨x, j⟩) (ρ := ρ) (hρ := hρ)
    (N := Ideal.span (Set.range ρ)) (hN := rfl)
  exact ⟨(x : {x // x ∈ s}) × Fin (m x), inferInstance,
    MvPolynomial (Fin n ⊕ ((x : {x // x ∈ s}) × Fin (m x))) A ⧸ Ideal.span (Set.range ρ),
    inferInstance, inferInstance,
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range ρ)),
    Ideal.Quotient.liftₐ _ Θ hΘN, e, he⟩

end Relations

/-- **The lifting problem.** Let `R → Λ` be a ring map and `I ⊂ R` an ideal with `I² = 0` such
that `Λ/IΛ` is a filtered colimit of smooth `R/I`-algebras. Then every `R`-algebra map
`φ : A → Λ` with `A` of finite presentation over `R` factors as `A → B/J → Λ` with `B` a smooth
`R`-algebra and `J ⊂ IB` a finitely generated ideal. -/
@[stacks 07CK]
theorem exists_smooth_quotient_factorization
    {R Λ A : Type u} [CommRing R] [CommRing Λ] [CommRing A]
    [Algebra R Λ] [Algebra R A] [Algebra.FinitePresentation R A]
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ : ObjectProperty.ind.{u}
      (fun B : Under (CommRingCat.of (R ⧸ I)) ↦ B.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))))
    (φ : A →ₐ[R] Λ) :
    ∃ (B : Type u) (_ : CommRing B) (alg : Algebra R B),
      letI := alg
      Algebra.Smooth R B ∧
        ∃ J : Ideal B, J ≤ I.map (algebraMap R B) ∧ J.FG ∧
          ∃ (α : A →ₐ[R] B ⧸ J) (β : (B ⧸ J) →ₐ[R] Λ), β.comp α = φ := by
  classical
  let : Algebra A Λ := φ.toRingHom.toAlgebra
  have : IsScalarTower R A Λ := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hKΛ : (I.map (algebraMap R A)).map (algebraMap A Λ) = I.map (algebraMap R Λ) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have : Algebra.FinitePresentation (R ⧸ I) (A ⧸ I.map (algebraMap R A)) :=
    Algebra.FinitePresentation.equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).symm
  -- the induced `R/I`-algebra map `A/IA → Λ/IΛ`
  obtain ⟨f, hf⟩ : ∃ f : (A ⧸ I.map (algebraMap R A)) →ₐ[R ⧸ I] (Λ ⧸ I.map (algebraMap R Λ)),
      ∀ a : A, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (algebraMap A Λ a) := by
    refine ⟨AlgHom.extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective
      { Ideal.quotientMap (I.map (algebraMap R Λ)) (algebraMap A Λ)
          (Ideal.map_le_iff_le_comap.mp hKΛ.le) with
        commutes' := fun r => ?_ }, fun a => rfl⟩
    show Ideal.Quotient.mk _ (algebraMap A Λ (algebraMap R A r)) = _
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  -- Step 1: factor `A/IA → Λ/IΛ` through a smooth `R/I`-algebra
  obtain ⟨Bb, hBbring, hBbalg, hBbsm, u, v, huv⟩ := exists_smooth_factorization_of_ind hΛ f
  let := hBbring
  let := hBbalg
  let : Algebra (A ⧸ I.map (algebraMap R A)) Bb := u.toRingHom.toAlgebra
  have : IsScalarTower (R ⧸ I) (A ⧸ I.map (algebraMap R A)) Bb :=
    IsScalarTower.of_algebraMap_eq fun x => (u.commutes x).symm
  have : Algebra.FinitePresentation (A ⧸ I.map (algebraMap R A)) Bb :=
    have : Algebra.FinitePresentation (R ⧸ I) Bb := hBbsm.finitePresentation
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation
      (R := R ⧸ I) (A := A ⧸ I.map (algebraMap R A)) (B := Bb)
  -- Step 2: adjoin variables to realise `Bb[δ]` as the reduction of an `A`-algebra
  obtain ⟨Δ, hΔfin, Cc, hCcring, hCcalg, hCcfp, θ, e, he⟩ :=
    exists_finitePresentation_quotientEquiv (I.map (algebraMap R A)) (Λ := Λ) (Bb := Bb)
      ((Ideal.quotEquivOfEq hKΛ.symm).toRingHom.comp v.toRingHom) (fun a => by
        show Ideal.quotEquivOfEq hKΛ.symm (v (u (Ideal.Quotient.mk _ a))) = _
        rw [show v (u (Ideal.Quotient.mk (I.map (algebraMap R A)) a)) =
          f (Ideal.Quotient.mk _ a) from AlgHom.congr_fun huv _, hf a,
          Ideal.quotEquivOfEq_mk])
  let := hCcring
  let := hCcalg
  let := hΔfin
  let : Algebra R Cc := ((algebraMap A Cc).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A Cc := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FinitePresentation R Cc :=
    have := hCcfp
    Algebra.FinitePresentation.trans R A Cc
  have hICc : I.map (algebraMap R Cc) = (I.map (algebraMap R A)).map (algebraMap A Cc) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  -- Step 3: the reduction of `Cc` modulo `I` is smooth over `R/I`
  have : Algebra.Smooth Bb (MvPolynomial Δ Bb) :=
    { formallySmooth := inferInstance, finitePresentation := inferInstance }
  have : Algebra.Smooth (R ⧸ I) (MvPolynomial Δ Bb) :=
    have : Algebra.Smooth (R ⧸ I) Bb := hBbsm
    Algebra.Smooth.comp (R ⧸ I) Bb (MvPolynomial Δ Bb)
  have hsm : Algebra.Smooth (R ⧸ I) (Cc ⧸ I.map (algebraMap R Cc)) := by
    refine Algebra.Smooth.of_equiv (A := MvPolynomial Δ Bb)
      (AlgEquiv.symm { (Ideal.quotEquivOfEq hICc).trans e with commutes' := fun x => ?_ })
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    show (Ideal.quotEquivOfEq hICc).trans e
      (Ideal.Quotient.mk _ (algebraMap A Cc (algebraMap R A r))) = _
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, he,
      IsScalarTower.algebraMap_apply (R ⧸ I) Bb (MvPolynomial Δ Bb),
      IsScalarTower.algebraMap_apply (R ⧸ I) (A ⧸ I.map (algebraMap R A)) Bb]
    rfl
  -- Step 4: lift the smooth `R/I`-algebra `Cc/ICc` to a smooth `R`-algebra `B`
  obtain ⟨B, hBring, hBalg, hBsm, eB, heB⟩ :=
    exists_smooth_lift_of_surjective R (R ⧸ I) (Cc ⧸ I.map (algebraMap R Cc))
      Ideal.Quotient.mk_surjective hsm
  let := hBring
  let := hBalg
  obtain ⟨eB', heB'⟩ : ∃ eB' : (Cc ⧸ I.map (algebraMap R Cc)) ≃+* B ⧸ I.map (algebraMap R B),
      ∀ r : R, eB' (Ideal.Quotient.mk _ (algebraMap R Cc r)) =
        Ideal.Quotient.mk _ (algebraMap R B r) :=
    ⟨eB.trans (Ideal.quotEquivOfEq
      (by rw [show algebraMap R (R ⧸ I) = Ideal.Quotient.mk I from rfl, Ideal.mk_ker])),
      fun r => by
      rw [RingEquiv.trans_apply,
        show Ideal.Quotient.mk (I.map (algebraMap R Cc)) (algebraMap R Cc r) =
          algebraMap (R ⧸ I) (Cc ⧸ I.map (algebraMap R Cc)) (algebraMap R (R ⧸ I) r) from rfl,
        heB r, Ideal.quotEquivOfEq_mk]⟩
  -- Step 5: lift `B → Cc/ICc` to `B → Cc` using formal smoothness
  obtain ⟨w, hw⟩ : ∃ w : B →ₐ[R] (Cc ⧸ I.map (algebraMap R Cc)),
      ∀ b : B, w b = eB'.symm (Ideal.Quotient.mk _ b) := by
    refine ⟨{ eB'.symm.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap R B))) with
      commutes' := fun r => ?_ }, fun b => rfl⟩
    show eB'.symm (Ideal.Quotient.mk _ (algebraMap R B r)) = _
    rw [← heB' r, RingEquiv.symm_apply_apply]
    rfl
  obtain ⟨ψ', hψ'⟩ := Algebra.FormallySmooth.exists_lift (R := R) (A := B)
    (I.map (algebraMap R Cc)) ⟨2, map_sq_eq_bot hI⟩ w
  have hψ'mk : ∀ b : B, Ideal.Quotient.mk (I.map (algebraMap R Cc)) (ψ' b) = w b :=
    fun b => AlgHom.congr_fun hψ' b
  -- Step 6: `ψ'` is surjective
  have hmod : ∀ c : Cc, ∃ b : B, c - ψ' b ∈ I.map (algebraMap R Cc) := by
    intro c
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (eB' (Ideal.Quotient.mk _ c))
    refine ⟨b, ?_⟩
    have h1 : Ideal.Quotient.mk (I.map (algebraMap R Cc)) c =
        Ideal.Quotient.mk (I.map (algebraMap R Cc)) (ψ' b) := by
      rw [hψ'mk, hw, hb, RingEquiv.symm_apply_apply]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, sub_self]
  have hrange : ∀ y ∈ I.map (algebraMap R Cc), ∃ b : B, y = ψ' b := by
    intro y hy
    obtain ⟨k, cs, ii, hiimem, rfl⟩ := exists_sum_mul_algebraMap_of_mem_map hy
    choose bs hbs using fun t : Fin k => hmod (cs t)
    refine ⟨∑ t, bs t * algebraMap R B (ii t), ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h2 : (cs t - ψ' (bs t)) * algebraMap R Cc (ii t) = 0 := by
      have := Ideal.mul_mem_mul (hbs t) (Ideal.mem_map_of_mem (algebraMap R Cc) (hiimem t))
      rwa [← pow_two, map_sq_eq_bot hI, Ideal.mem_bot] at this
    rw [map_mul, ψ'.commutes, ← sub_eq_zero, ← sub_mul, h2]
  have hsurj : Function.Surjective ψ' := by
    intro c
    obtain ⟨b, hb⟩ := hmod c
    obtain ⟨b', hb'⟩ := hrange _ hb
    exact ⟨b + b', by rw [map_add, ← hb']; ring⟩
  -- Step 7: assemble
  refine ⟨B, hBring, hBalg, hBsm, RingHom.ker ψ'.toRingHom, ?_, ?_, ?_⟩
  · intro b hb
    have h1 : eB'.symm (Ideal.Quotient.mk (I.map (algebraMap R B)) b) = 0 := by
      rw [← hw b, ← hψ'mk b, show ψ' b = 0 from hb]
      exact map_zero _
    refine Ideal.Quotient.eq_zero_iff_mem.mp (eB'.symm.injective ?_)
    rw [h1, map_zero]
  · let : Algebra.FinitePresentation R B := hBsm.finitePresentation
    exact Algebra.FinitePresentation.ker_fG_of_surjective ψ' hsurj
  · refine ⟨(Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom.comp
      (IsScalarTower.toAlgHom R A Cc),
      (θ.restrictScalars R).comp (Ideal.quotientKerAlgEquivOfSurjective hsurj).toAlgHom,
      AlgHom.ext fun a => ?_⟩
    show θ ((Ideal.quotientKerAlgEquivOfSurjective hsurj)
      ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (algebraMap A Cc a))) = φ a
    rw [AlgEquiv.apply_symm_apply, θ.commutes]
    rfl

section KillIdeal

variable {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]

/-- An `R`-algebra map carries `IB` into `IB'`. -/
private theorem mem_map_of_algHom {B B' : Type u} [CommRing B] [CommRing B']
    [Algebra R B] [Algebra R B'] (I : Ideal R) (α : B →ₐ[R] B') {x : B}
    (hx : x ∈ I.map (algebraMap R B)) : α x ∈ I.map (algebraMap R B') := by
  have h : (I.map (algebraMap R B)).map (α : B →+* B') = I.map (algebraMap R B') := by
    rw [Ideal.map_map, α.comp_algebraMap]
  exact h ▸ Ideal.mem_map_of_mem _ hx

/-- The single-generator case of Tag `07CL`: one element of `IB` annihilated by `φ` can be
killed by enlarging `B` to another smooth `R`-algebra mapping to `Λ`. -/
private theorem exists_smooth_factorization_of_mem_map
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ : ObjectProperty.ind.{u}
      (fun C : Under (CommRingCat.of (R ⧸ I)) ↦ C.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))))
    [Module.Flat R Λ] {B : Type u} [CommRing B] [Algebra R B] (hB : Algebra.Smooth R B)
    (φ : B →ₐ[R] Λ) (h : B) (hh : h ∈ I.map (algebraMap R B)) (hφh : φ h = 0) :
    ∃ (B' : Type u) (_ : CommRing B') (alg : Algebra R B'),
      letI := alg
      Algebra.Smooth R B' ∧
        ∃ (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ), α h = 0 ∧ β.comp α = φ := by
  classical
  have := hB.formallySmooth
  have := hB.finitePresentation
  -- Step 1: write `h = ∑ εᵢ cᵢ` with `εᵢ ∈ I` and `cᵢ ∈ B`.
  obtain ⟨n, c, ε, hεI, hh2⟩ := exists_sum_mul_algebraMap_of_mem_map hh
  -- Step 2: the equational criterion for flatness.
  obtain ⟨k, a, y, hcy, hεa⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := Λ)
      (f := ε) (x := fun i => φ (c i)) (by
        have e : ∑ i, algebraMap R Λ (ε i) * φ (c i) = 0 := by
          rw [show ∑ i, algebraMap R Λ (ε i) * φ (c i) =
              φ (∑ i, c i * algebraMap R B (ε i)) from by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_mul, φ.commutes, mul_comm],
            ← hh2, hφh]
        simpa [Algebra.smul_def] using e)
  have hcy' : ∀ i, φ (c i) = ∑ j, algebraMap R Λ (a i j) * y j := fun i => by
    simpa [Algebra.smul_def] using hcy i
  -- Step 3: the auxiliary algebra `C = B[x]/(cᵢ - ∑ⱼ aᵢⱼ xⱼ)`, of finite presentation over `R`.
  let rel : Fin n → MvPolynomial (Fin k) B := fun i =>
    MvPolynomial.C (c i) - ∑ j, MvPolynomial.C (algebraMap R B (a i j)) * X j
  let N : Ideal (MvPolynomial (Fin k) B) := Ideal.span (Set.range rel)
  have hrelN : ∀ i, rel i ∈ N := fun i => Ideal.subset_span ⟨i, rfl⟩
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range rel)
  have : Algebra.FinitePresentation R (MvPolynomial (Fin k) B) :=
    Algebra.FinitePresentation.mvPolynomial R B (Fin k)
  have : Algebra.FinitePresentation R (MvPolynomial (Fin k) B ⧸ N) :=
    Algebra.FinitePresentation.quotient hNfg
  -- Step 4: the `R`-algebra map `C → Λ` sending `xⱼ` to `yⱼ`.
  have hkill : ∀ p ∈ N, MvPolynomial.aevalTower φ y p = 0 := by
    have hrelzero : ∀ i, MvPolynomial.aevalTower φ y (rel i) = 0 := by
      intro i
      show MvPolynomial.aevalTower φ y
        (MvPolynomial.C (c i) - ∑ j, MvPolynomial.C (algebraMap R B (a i j)) * X j) = 0
      rw [map_sub, map_sum, MvPolynomial.aevalTower_C,
        show ∑ j, MvPolynomial.aevalTower φ y (MvPolynomial.C (algebraMap R B (a i j)) * X j) =
            ∑ j, algebraMap R Λ (a i j) * y j from
          Finset.sum_congr rfl fun j _ => by
            rw [map_mul, MvPolynomial.aevalTower_C, MvPolynomial.aevalTower_X, φ.commutes],
        ← hcy' i, sub_self]
    intro p hp
    exact (Ideal.span_le.mpr (Set.range_subset_iff.mpr hrelzero) :
      N ≤ RingHom.ker (MvPolynomial.aevalTower φ y : _ →+* Λ)) hp
  -- Step 5: factor `C → Λ` through a quotient of a smooth algebra (Tag `07CK`).
  obtain ⟨B', hB'ring, hB'alg, hB'sm, J', hJ'I, hJ'fg, α₀, β₀, hαβ⟩ :=
    exists_smooth_quotient_factorization I hI hΛ
      (Ideal.Quotient.liftₐ N (MvPolynomial.aevalTower φ y) hkill)
  let := hB'ring
  let := hB'alg
  have hJ'2 : J' ^ 2 = ⊥ :=
    le_antisymm ((Ideal.pow_right_mono hJ'I 2).trans (map_sq_eq_bot hI).le) bot_le
  -- Step 6: lift `B → C → B'/J'` to `B → B'` by formal smoothness of `B`.
  have hqsurj : Function.Surjective (Ideal.Quotient.mkₐ R J' : B' →ₐ[R] B' ⧸ J') :=
    Ideal.Quotient.mkₐ_surjective R J'
  have hqnil : IsNilpotent (RingHom.ker ((Ideal.Quotient.mkₐ R J' : B' →ₐ[R] B' ⧸ J') :
      B' →+* B' ⧸ J')) := by
    rw [Ideal.Quotient.mkₐ_ker]
    exact ⟨2, hJ'2⟩
  obtain ⟨ι, hι⟩ : ∃ ι : B →ₐ[R] MvPolynomial (Fin k) B ⧸ N,
      ∀ b : B, ι b = Ideal.Quotient.mk N (MvPolynomial.C b) :=
    ⟨(Ideal.Quotient.mkₐ R N).comp (IsScalarTower.toAlgHom R B (MvPolynomial (Fin k) B)),
      fun _ => rfl⟩
  obtain ⟨α, hqα⟩ : ∃ α : B →ₐ[R] B', ∀ b : B, Ideal.Quotient.mk J' (α b) = α₀ (ι b) :=
    ⟨Algebra.FormallySmooth.liftOfSurjective (α₀.comp ι) (Ideal.Quotient.mkₐ R J') hqsurj hqnil,
      fun b => AlgHom.congr_fun (Algebra.FormallySmooth.comp_liftOfSurjective
        (α₀.comp ι) (Ideal.Quotient.mkₐ R J') hqsurj hqnil) b⟩
  refine ⟨B', hB'ring, hB'alg, hB'sm, α, β₀.comp (Ideal.Quotient.mkₐ R J'), ?_, ?_⟩
  · -- Step 7: `α h = 0`.
    choose ξ hξ using fun j : Fin k =>
      Ideal.Quotient.mk_surjective (I := J') (α₀ (Ideal.Quotient.mk N (X j)))
    have hθ : ∀ i, α (c i) - ∑ j, algebraMap R B' (a i j) * ξ j ∈ J' := by
      intro i
      have key : Ideal.Quotient.mk N (MvPolynomial.C (c i)) =
          ∑ j, Ideal.Quotient.mk N (MvPolynomial.C (algebraMap R B (a i j)) * X j) := by
        rw [← map_sum, ← sub_eq_zero, ← map_sub]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrelN i)
      have h1 : Ideal.Quotient.mk J' (α (c i)) =
          ∑ j, algebraMap R (B' ⧸ J') (a i j) * Ideal.Quotient.mk J' (ξ j) := by
        rw [hqα (c i), hι, key, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_mul, hξ j]
        congr 1
        show α₀ (algebraMap R (MvPolynomial (Fin k) B ⧸ N) (a i j)) = _
        rw [α₀.commutes]
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, h1,
        show ∑ j, Ideal.Quotient.mk J' (algebraMap R B' (a i j) * ξ j) =
            ∑ j, algebraMap R (B' ⧸ J') (a i j) * Ideal.Quotient.mk J' (ξ j) from
          Finset.sum_congr rfl fun j _ => by rw [map_mul]; rfl,
        sub_self]
    have hεθ : ∀ i,
        algebraMap R B' (ε i) * (α (c i) - ∑ j, algebraMap R B' (a i j) * ξ j) = 0 := by
      intro i
      have hmem := Ideal.mul_mem_mul
        (Ideal.mem_map_of_mem (algebraMap R B') (hεI i)) (hJ'I (hθ i))
      rwa [← pow_two, map_sq_eq_bot hI, Ideal.mem_bot] at hmem
    have key : ∀ i, algebraMap R B' (ε i) * α (c i) =
        ∑ j, algebraMap R B' (ε i * a i j) * ξ j := by
      intro i
      have hST : algebraMap R B' (ε i) * (∑ j, algebraMap R B' (a i j) * ξ j) =
          ∑ j, algebraMap R B' (ε i * a i j) * ξ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_mul, mul_assoc]
      rw [← sub_eq_zero, ← hST, ← mul_sub]
      exact hεθ i
    have e1 : α h = ∑ i, ∑ j, algebraMap R B' (ε i * a i j) * ξ j := by
      rw [hh2, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, α.commutes, mul_comm, key i]
    rw [e1, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_mul, ← map_sum, hεa j, map_zero, zero_mul]
  · -- Step 8: `β ∘ α = φ`.
    refine AlgHom.ext fun b => ?_
    show β₀ (Ideal.Quotient.mk J' (α b)) = φ b
    rw [hqα b, hι,
      show β₀ (α₀ (Ideal.Quotient.mk N (MvPolynomial.C b))) =
        Ideal.Quotient.liftₐ N (MvPolynomial.aevalTower φ y) hkill
          (Ideal.Quotient.mk N (MvPolynomial.C b)) from AlgHom.congr_fun hαβ _]
    show MvPolynomial.aevalTower φ y (MvPolynomial.C b) = φ b
    rw [MvPolynomial.aevalTower_C]

/-- Tag `07CL` for a finite family of elements of `IB`, by induction on its length. -/
private theorem exists_smooth_factorization_of_forall_mem_map
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ : ObjectProperty.ind.{u}
      (fun C : Under (CommRingCat.of (R ⧸ I)) ↦ C.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))))
    [Module.Flat R Λ] (n : ℕ) :
    ∀ (B : Type u) (_ : CommRing B) (_ : Algebra R B), Algebra.Smooth R B →
      ∀ (φ : B →ₐ[R] Λ) (s : Fin n → B),
        (∀ i, s i ∈ I.map (algebraMap R B)) → (∀ i, φ (s i) = 0) →
        ∃ (B' : Type u) (_ : CommRing B') (alg : Algebra R B'),
          letI := alg
          Algebra.Smooth R B' ∧
            ∃ (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ), (∀ i, α (s i) = 0) ∧ β.comp α = φ := by
  induction n with
  | zero =>
    intro B hBr hBa hB φ s _ _
    exact ⟨B, hBr, hBa, hB, AlgHom.id R B, φ, fun i => i.elim0, AlgHom.comp_id φ⟩
  | succ n ih =>
    intro B hBr hBa hB φ s hsI hsφ
    let := hBr
    let := hBa
    obtain ⟨B₁, hB₁r, hB₁a, hB₁, α₁, β₁, hα₁, hβ₁⟩ :=
      exists_smooth_factorization_of_mem_map I hI hΛ hB φ (s (Fin.last n))
        (hsI (Fin.last n)) (hsφ (Fin.last n))
    let := hB₁r
    let := hB₁a
    obtain ⟨B₂, hB₂r, hB₂a, hB₂, α₂, β₂, hα₂, hβ₂⟩ :=
      ih B₁ hB₁r hB₁a hB₁ β₁ (fun i : Fin n => α₁ (s i.castSucc))
        (fun i => mem_map_of_algHom I α₁ (hsI i.castSucc))
        (fun i => by
          rw [show β₁ (α₁ (s i.castSucc)) = φ (s i.castSucc) from
            AlgHom.congr_fun hβ₁ (s i.castSucc)]
          exact hsφ i.castSucc)
    have hlast : (α₂.comp α₁) (s (Fin.last n)) = 0 := by
      show α₂ (α₁ (s (Fin.last n))) = 0
      rw [hα₁, map_zero]
    have hcast : ∀ j : Fin n, (α₂.comp α₁) (s j.castSucc) = 0 := fun j => hα₂ j
    have hcomp : β₂.comp (α₂.comp α₁) = φ := by rw [← AlgHom.comp_assoc, hβ₂, hβ₁]
    refine ⟨B₂, hB₂r, hB₂a, hB₂, α₂.comp α₁, β₂, fun i => ?_, hcomp⟩
    by_cases hi : (i : ℕ) < n
    · have hieq : i = Fin.castSucc ⟨(i : ℕ), hi⟩ := by
        rw [Fin.ext_iff, Fin.val_castSucc]
      rw [hieq]
      exact hcast ⟨(i : ℕ), hi⟩
    · have hieq : i = Fin.last n := by
        have h1 := i.isLt
        rw [Fin.ext_iff, Fin.val_last]
        omega
      rw [hieq]
      exact hlast

/-- **Stacks Project, Tag 07CL.** Let `I ⊂ R` be an ideal with `I² = 0` such that `Λ/IΛ` is a
filtered colimit of smooth `R/I`-algebras, and let `Λ` be flat over `R`. Then an `R`-algebra map
`φ : B → Λ` with `B` smooth over `R` factors as `B → B' → Λ` with `B'` smooth over `R` and with
`B → B'` killing any prescribed finitely generated ideal `J ⊆ IB` that `φ` annihilates. -/
@[stacks 07CL]
theorem exists_smooth_factorization_of_fg_le_map
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ : ObjectProperty.ind.{u}
      (fun C : Under (CommRingCat.of (R ⧸ I)) ↦ C.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))))
    [Module.Flat R Λ] {B : Type u} [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (φ : B →ₐ[R] Λ) (J : Ideal B) (hJI : J ≤ I.map (algebraMap R B)) (hJfg : J.FG)
    (hφJ : ∀ x ∈ J, φ x = 0) :
    ∃ (B' : Type u) (_ : CommRing B') (alg : Algebra R B'),
      letI := alg
      Algebra.Smooth R B' ∧
        ∃ (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ), (∀ x ∈ J, α x = 0) ∧ β.comp α = φ := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  have hmem : ∀ i, s i ∈ J := by
    intro i
    rw [← hs]
    exact Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨B', hB'r, hB'a, hB', α, β, hα, hβ⟩ :=
    exists_smooth_factorization_of_forall_mem_map I hI hΛ n B ‹CommRing B› ‹Algebra R B›
      ‹Algebra.Smooth R B› φ s (fun i => hJI (hmem i)) (fun i => hφJ (s i) (hmem i))
  refine ⟨B', hB'r, hB'a, hB', α, β, ?_, hβ⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hα i
  | zero => exact map_zero α
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul b y _ hy => rw [smul_eq_mul, map_mul, hy, mul_zero]

end KillIdeal

section Nilpotent

/-- Being a filtered colimit of smooth algebras transports along a commuting square of ring
equivalences: if `Λ₁` is a filtered colimit of smooth `R₁`-algebras and ring equivalences
`R₁ ≃ R₂`, `Λ₁ ≃ Λ₂` identify the structure maps, then `Λ₂` is a filtered colimit of smooth
`R₂`-algebras. -/
private theorem ind_smooth_of_ringEquiv {R₁ R₂ Λ₁ Λ₂ : Type u} [CommRing R₁] [CommRing R₂]
    [CommRing Λ₁] [CommRing Λ₂] [Algebra R₁ Λ₁] [Algebra R₂ Λ₂]
    (e : R₁ ≃+* R₂) (g : Λ₁ ≃+* Λ₂)
    (hg : ∀ r : R₁, g (algebraMap R₁ Λ₁ r) = algebraMap R₂ Λ₂ (e r))
    (h : ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of R₁) ↦ C.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap R₁ Λ₁)))) :
    ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of R₂) ↦ C.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap R₂ Λ₂))) := by
  obtain ⟨J, _, _, pres, hp⟩ := h
  let i : CommRingCat.of R₁ ≅ CommRingCat.of R₂ := e.toCommRingCatIso
  have ht : ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of R₂) ↦ C.hom.hom.Smooth)
      ((Under.map i.inv).obj (Under.mk (CommRingCat.ofHom (algebraMap R₁ Λ₁)))) :=
    ⟨J, inferInstance, inferInstance, pres.map (Under.map i.inv),
      fun j ↦ RingHom.Smooth.comp (RingHom.Smooth.of_bijective e.symm.bijective) (hp j)⟩
  refine (ObjectProperty.ind.{u} _).prop_of_iso (Under.isoMk g.toCommRingCatIso ?_) ht
  ext r
  show g (algebraMap R₁ Λ₁ (e.symm r)) = algebraMap R₂ Λ₂ r
  rw [hg, e.apply_symm_apply]

variable {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]

/-- **The square-zero case of Tag `07CM`.** Let `I ⊂ R` be an ideal with `I² = 0` such that
`Λ/IΛ` is a filtered colimit of smooth `R/I`-algebras, and let `Λ` be flat over `R`. Then `Λ` is
a filtered colimit of smooth `R`-algebras. -/
private theorem ind_smooth_of_sq_eq_bot (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ : ObjectProperty.ind.{u}
      (fun C : Under (CommRingCat.of (R ⧸ I)) ↦ C.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))))
    [Module.Flat R Λ] :
    ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of R) ↦ C.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap R Λ))) := by
  refine (CommRingCat.ind_under_iff_exists_factorization _
    (fun _ hC ↦ RingHom.Smooth.finitePresentation hC)).2 ?_
  intro A hA f
  let : Algebra R A.right := A.hom.hom.toAlgebra
  let : Algebra.FinitePresentation R A.right := hA
  let φ : A.right →ₐ[R] Λ :=
    { f.right.hom with commutes' := fun r ↦ congrArg (fun q ↦ q.hom r) f.w }
  -- Tag `07CK`: factor `φ` through a quotient `B/J` of a smooth `R`-algebra by `J ⊆ IB`
  obtain ⟨B, hBr, hBa, hB, J, hJI, hJfg, α, β, hαβ⟩ :=
    exists_smooth_quotient_factorization I hI hΛ φ
  let := hBr
  let := hBa
  let := hB
  -- Tag `07CL`: kill `J` at the cost of enlarging `B` to a smooth `R`-algebra `B'`
  obtain ⟨B', hB'r, hB'a, hB', α', β', hα'J, hβ'⟩ :=
    exists_smooth_factorization_of_fg_le_map I hI hΛ (β.comp (Ideal.Quotient.mkₐ R J)) J hJI hJfg
      fun x hx ↦ by
        show β (Ideal.Quotient.mk J x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  let := hB'r
  let := hB'a
  -- `α'` kills `J`, hence factors through `B/J`, and `β'` recovers `β`
  let ᾱ : (B ⧸ J) →ₐ[R] B' := Ideal.Quotient.liftₐ J α' hα'J
  have hcomp : β'.comp (ᾱ.comp α) = φ := by
    refine AlgHom.ext fun a ↦ ?_
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (α a)
    show β' (ᾱ (α a)) = φ a
    rw [← hb, show ᾱ (Ideal.Quotient.mk J b) = α' b from rfl,
      show β' (α' b) = β (Ideal.Quotient.mk J b) from AlgHom.congr_fun hβ' b, hb]
    exact AlgHom.congr_fun hαβ a
  refine ⟨Under.mk (CommRingCat.ofHom (algebraMap R B')),
    Under.homMk (CommRingCat.ofHom (ᾱ.comp α).toRingHom)
      (by ext r; exact (ᾱ.comp α).commutes r),
    Under.homMk (CommRingCat.ofHom β'.toRingHom) (by ext r; exact β'.commutes r), ?_, ?_⟩
  · ext x
    exact congrArg (fun q : A.right →ₐ[R] Λ ↦ q x) hcomp
  · show (algebraMap R B').Smooth
    exact RingHom.smooth_algebraMap.mpr hB'

/-- Tag `07CM` for an ideal with `I ^ (n + 1) = 0`, by induction on `n`. -/
private theorem ind_smooth_of_pow_succ_eq_bot (n : ℕ) :
    ∀ (R : Type u) (_ : CommRing R) (Λ : Type u) (_ : CommRing Λ) (_ : Algebra R Λ)
      (_ : Module.Flat R Λ) (I : Ideal R), I ^ (n + 1) = ⊥ →
      ObjectProperty.ind.{u}
        (fun C : Under (CommRingCat.of (R ⧸ I)) ↦ C.hom.hom.Smooth)
        (Under.mk (CommRingCat.ofHom (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))) →
      ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of R) ↦ C.hom.hom.Smooth)
        (Under.mk (CommRingCat.ofHom (algebraMap R Λ))) := by
  induction n with
  | zero =>
    intro R _ Λ _ _ _ I hI hΛ
    exact ind_smooth_of_sq_eq_bot I (pow_eq_zero_of_le (by omega) hI) hΛ
  | succ n ih =>
    intro R _ Λ _ _ _ I hI hΛ
    have hI₁le : I ^ (n + 1) ≤ I := Ideal.pow_le_self (by omega)
    have hJ₁le : (I ^ (n + 1)).map (algebraMap R Λ) ≤ I.map (algebraMap R Λ) :=
      Ideal.map_mono hI₁le
    -- `Λ/I₁Λ` is the base change `(R/I₁) ⊗_R Λ`, hence flat over `R/I₁`
    let : Module.Flat (R ⧸ I ^ (n + 1)) (Λ ⧸ (I ^ (n + 1)).map (algebraMap R Λ)) :=
      Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Λ (I ^ (n + 1))).toLinearEquiv
    -- the ideal `I·(Λ/I₁Λ)` computed through `R/I₁` and through `Λ` agree
    have hA : (I.map (Ideal.Quotient.mk (I ^ (n + 1)))).map
          (algebraMap (R ⧸ I ^ (n + 1)) (Λ ⧸ (I ^ (n + 1)).map (algebraMap R Λ))) =
        (I.map (algebraMap R Λ)).map
          (Ideal.Quotient.mk ((I ^ (n + 1)).map (algebraMap R Λ))) := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
    refine ind_smooth_of_sq_eq_bot (I ^ (n + 1))
      (by
        rw [← pow_mul]
        exact pow_eq_zero_of_le (by omega) hI)
      (ih (R ⧸ I ^ (n + 1)) inferInstance (Λ ⧸ (I ^ (n + 1)).map (algebraMap R Λ))
        inferInstance inferInstance inferInstance (I.map (Ideal.Quotient.mk (I ^ (n + 1))))
        (by rw [← Ideal.map_pow]; exact Ideal.map_quotient_self _) ?_)
    refine ind_smooth_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hI₁le).symm
      ((DoubleQuot.quotQuotEquivQuotOfLE hJ₁le).symm.trans (Ideal.quotEquivOfEq hA.symm))
      (fun r ↦ ?_) hΛ
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
    show (Ideal.quotEquivOfEq hA.symm) ((DoubleQuot.quotQuotEquivQuotOfLE hJ₁le).symm
      (Ideal.Quotient.mk (I.map (algebraMap R Λ)) (algebraMap R Λ x))) = _
    rw [DoubleQuot.quotQuotEquivQuotOfLE_symm_mk]
    show _ = algebraMap _ _ ((DoubleQuot.quotQuotEquivQuotOfLE hI₁le).symm
      (Ideal.Quotient.mk I x))
    rw [DoubleQuot.quotQuotEquivQuotOfLE_symm_mk]
    rfl

/-- **Stacks Project, Tag 07CM: ind-smoothness of an algebra is stable under infinitesimal
deformations.** Let `R → Λ` be a ring map and `I ⊂ R` a nilpotent ideal. If `Λ/IΛ` is a filtered
colimit of smooth `R/I`-algebras and `R → Λ` is flat, then `Λ` is a filtered colimit of smooth
`R`-algebras.

Here "filtered colimit of smooth algebras" is `CategoryTheory.ObjectProperty.ind` of
`RingHom.Smooth` on `Under (CommRingCat.of R)`, the spelling of `07C3`, `07CK` and `07CL`;
nilpotence is `IsNilpotent I`, that is `I ^ n = ⊥` for some `n`; and flatness is
`Module.Flat R Λ`. -/
@[stacks 07CM]
theorem ind_smooth_of_isNilpotent (I : Ideal R) (hI : IsNilpotent I)
    (hΛ : ObjectProperty.ind.{u}
      (fun C : Under (CommRingCat.of (R ⧸ I)) ↦ C.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))))
    [Module.Flat R Λ] :
    ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of R) ↦ C.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom (algebraMap R Λ))) := by
  obtain ⟨n, hn⟩ := hI
  rw [Ideal.zero_eq_bot] at hn
  exact ind_smooth_of_pow_succ_eq_bot n R inferInstance Λ inferInstance inferInstance
    inferInstance I (pow_eq_zero_of_le (by omega) hn) hΛ

end Nilpotent

end Stacks.Smoothing
