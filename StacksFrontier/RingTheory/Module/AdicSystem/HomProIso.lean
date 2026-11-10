module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.RingTheory.Noetherian.AdicKernelStabilization

/-!
# The adic comparison of a module of homomorphisms is a pro-isomorphism

Let `I` be an ideal of a Noetherian ring `A` and let `M`, `N` be finite `A`-modules.  The
comparison

`Hom_A(M, N) ⧸ Iⁿ Hom_A(M, N) ⟶ Hom_A(M, N ⧸ Iⁿ N)`,

which reduces the target of a homomorphism modulo `Iⁿ`, is an isomorphism at no single level:
its kernel and its cokernel are killed by a power of `I` and no more.  It is a
*pro-isomorphism* — invertible after a shift of the index — and that is the Artin–Rees content
of the comparison.

Both halves are proved here from the Artin–Rees lemma.  Pro-injectivity is Artin–Rees for the
embedding of `Hom_A(M, N)` into `Nʳ` given by a system of generators of `M`: a homomorphism
whose image lies in `I ^ (n + c) N` already lies in `Iⁿ Hom_A(M, N)`.  Pro-surjectivity is
Artin–Rees for the relation map `(Aʳ →ₗ N) ⟶ Nᵗ` of a presentation of `M`: a homomorphism into
`N ⧸ I ^ (n + c) N` becomes, after reduction to `N ⧸ Iⁿ N`, the reduction of an honest
homomorphism `M ⟶ N`.  The two are then assembled into a pro-isomorphism of inverse sequences
in the sense of `InverseSequence.ProIso`.

## Main definitions

* `Stacks.AdicSystem.HomProIso.comparison` — the comparison
  `Hom_A(M, N) ⧸ Iⁿ Hom_A(M, N) →ₗ Hom_A(M, N ⧸ Iⁿ N)`.
* `Stacks.AdicSystem.HomProIso.targetTransition` — the transition map of the target sequence:
  reduction of `N ⧸ I ^ m N` to `N ⧸ Iⁿ N` in the target of a homomorphism out of `M`.
* `Stacks.AdicSystem.HomProIso.homQuotSystem` and `Stacks.AdicSystem.HomProIso.targetSystem` —
  the two inverse sequences, as functors `ℕᵒᵖ ⥤ ModuleCat A`.
* `Stacks.AdicSystem.HomProIso.proBack` — the backward map of the pro-isomorphism.

## Main results

* `Stacks.AdicSystem.HomProIso.exists_mem_pow_smul_of_range_le` — pro-injectivity: a
  homomorphism with image in `I ^ (n + c) N` lies in `Iⁿ Hom_A(M, N)`, for a `c` independent of
  `n`.
* `Stacks.AdicSystem.HomProIso.exists_comparison_eq_targetTransition` — pro-surjectivity: the
  reduction to `N ⧸ Iⁿ N` of a homomorphism `M ⟶ N ⧸ I ^ (n + c) N` is in the image of the
  comparison at `n`, for a `c` independent of `n`.
* `Stacks.AdicSystem.HomProIso.exists_proSection_and_proCancellation` — the two halves at one
  common shift.
* `Stacks.AdicSystem.HomProIso.nonempty_proIso` — **the comparison is a pro-isomorphism** of the
  inverse sequence of adic quotients of `Hom_A(M, N)` with the inverse sequence of
  homomorphisms into the adic quotients of `N`.

## Implementation notes

Pro-injectivity and pro-surjectivity both come from one lemma, the Artin–Rees shift for a
preimage `Stacks.AdicCompletion.exists_comap_pow_smul_le_ker_sup`, applied to two different maps
into a finite free module over `N`.  The translation between "every value lies in `Iⁿ N`" and
"the tuple of values lies in `Iⁿ Nʳ`" is `mem_pow_smul_pi`, which holds for any ideal.

No `@[stacks 09BB]` attribute is carried here.  Part (2) of that tag asserts a *uniform*
annihilator — one `c` with `I ^ c` killing the kernel and the cokernel of the comparison at every
`n` — which implies the pro-isomorphism below but is not implied by it, a shift being weaker than
an annihilator.  Part (2) is proved and registered at
`Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion`.

A preimage under the comparison involves a choice, so the backward maps are not built pointwise.
They are the composite of the reduction, corestricted to the range of the comparison, with the
map that the transition map of the source induces on that range.  Pro-surjectivity is what makes
the corestriction possible and pro-injectivity is what makes the induced map exist, and the
resulting family is then automatically compatible with the transition maps.

## References

* [Stacks Project, Tag 09BB](https://stacks.math.columbia.edu/tag/09BB)
* [Stacks Project, Tag 00IN](https://stacks.math.columbia.edu/tag/00IN)
-/

@[expose] public section

open CategoryTheory Opposite

namespace Stacks.AdicSystem.HomProIso

universe u v w

/-! ### Tuples of elements of an adic multiple -/

/-- A tuple all of whose entries lie in `J P` lies in `J` times the module of tuples.  The entry
at `i` is the image of an entry under the `i`-th inclusion, which carries `J P` into `J Pʳ`. -/
theorem mem_pow_smul_pi {A : Type u} {P : Type v} [CommRing A] [AddCommGroup P] [Module A P]
    {r : ℕ} (J : Ideal A) (x : Fin r → P) (h : ∀ i, x i ∈ J • (⊤ : Submodule A P)) :
    x ∈ J • (⊤ : Submodule A (Fin r → P)) := by
  have hx : x = ∑ i, Pi.single i (x i) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  refine Submodule.sum_mem _ fun i _ => ?_
  have he : (Pi.single i (x i) : Fin r → P) =
      (LinearMap.single A (fun _ : Fin r => P) i) (x i) := rfl
  rw [he]
  have hmap : Submodule.map (LinearMap.single A (fun _ : Fin r => P) i)
      (J • (⊤ : Submodule A P)) ≤ J • (⊤ : Submodule A (Fin r → P)) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hmap (Submodule.mem_map_of_mem (h i))

/-! ### The comparison and the two inverse sequences -/

section Comparison

variable {A : Type u} {M : Type v} {N : Type w} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- Composing the transition maps of the adic quotients of a module. -/
theorem transitionMap_trans (I : Ideal A) (P : Type*) [AddCommGroup P] [Module A P]
    {n p q : ℕ} (h₁ : n ≤ p) (h₂ : p ≤ q) (ξ : P ⧸ I ^ q • (⊤ : Submodule A P)) :
    AdicCompletion.transitionMap I P h₁ (AdicCompletion.transitionMap I P h₂ ξ) =
      AdicCompletion.transitionMap I P (h₁.trans h₂) ξ := by
  induction ξ using Submodule.Quotient.induction_on with | _ x => rfl

/-- **The comparison.**  A homomorphism `M ⟶ N` taken modulo `Iⁿ Hom_A(M, N)` is read as a
homomorphism `M ⟶ N ⧸ Iⁿ N`.  This is well defined because `Iⁿ` annihilates `N ⧸ Iⁿ N`. -/
noncomputable def comparison (I : Ideal A) (n : ℕ) :
    ((M →ₗ[A] N) ⧸ I ^ n • (⊤ : Submodule A (M →ₗ[A] N))) →ₗ[A]
      (M →ₗ[A] (N ⧸ I ^ n • (⊤ : Submodule A N))) :=
  Submodule.liftQ _
    (LinearMap.compRight (M := M) A (I ^ n • (⊤ : Submodule A N)).mkQ) <| by
    intro f hf
    refine LinearMap.ext fun x => ?_
    exact (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.smul_top_le_comap_smul_top (I ^ n) (LinearMap.applyₗ x) hf)

/-- The comparison sends the class of `f` to the homomorphism `x ↦ f x mod Iⁿ N`. -/
theorem comparison_mk_apply (I : Ideal A) (n : ℕ) (f : M →ₗ[A] N) (x : M) :
    comparison I n (Submodule.Quotient.mk f) x = Submodule.Quotient.mk (f x) := rfl

/-- The comparison at level `n` kills a homomorphism exactly when its image lies in `Iⁿ N`. -/
theorem comparison_mk_eq_zero_iff (I : Ideal A) (n : ℕ) (f : M →ₗ[A] N) :
    comparison I n (Submodule.Quotient.mk f) = 0 ↔
      ∀ x, f x ∈ I ^ n • (⊤ : Submodule A N) := by
  simp only [LinearMap.ext_iff, comparison_mk_apply, LinearMap.zero_apply,
    Submodule.Quotient.mk_eq_zero]

/-- **The transition map of the target sequence.**  Reduction of `N ⧸ I ^ m N` to `N ⧸ Iⁿ N`,
applied in the target of a homomorphism out of `M`. -/
noncomputable def targetTransition (I : Ideal A) {n m : ℕ} (h : n ≤ m) :
    (M →ₗ[A] (N ⧸ I ^ m • (⊤ : Submodule A N))) →ₗ[A]
      (M →ₗ[A] (N ⧸ I ^ n • (⊤ : Submodule A N))) :=
  LinearMap.compRight (M := M) A (AdicCompletion.transitionMap I N h)

/-- The transition map of the target sequence applies the reduction `N ⧸ I ^ m N ⟶ N ⧸ Iⁿ N`
pointwise. -/
theorem targetTransition_apply (I : Ideal A) {n m : ℕ} (h : n ≤ m)
    (g : M →ₗ[A] (N ⧸ I ^ m • (⊤ : Submodule A N))) (x : M) :
    targetTransition I h g x = AdicCompletion.transitionMap I N h (g x) := rfl

/-- The transition map of the target sequence from level `n` to itself is the identity. -/
theorem targetTransition_refl (I : Ideal A) (n : ℕ)
    (g : M →ₗ[A] (N ⧸ I ^ n • (⊤ : Submodule A N))) :
    targetTransition I (le_refl n) g = g := by
  refine LinearMap.ext fun x => ?_
  rw [targetTransition_apply]
  induction g x using Submodule.Quotient.induction_on with | _ y => rfl

/-- Composing the transition maps of the target sequence. -/
theorem targetTransition_trans (I : Ideal A) {n p q : ℕ} (h₁ : n ≤ p) (h₂ : p ≤ q)
    (g : M →ₗ[A] (N ⧸ I ^ q • (⊤ : Submodule A N))) :
    targetTransition I h₁ (targetTransition I h₂ g) = targetTransition I (h₁.trans h₂) g :=
  LinearMap.ext fun x => transitionMap_trans I N h₁ h₂ (g x)

/-- **The comparison is a morphism of inverse sequences.** -/
theorem comparison_comp_transition (I : Ideal A) {n m : ℕ} (h : n ≤ m)
    (ξ : (M →ₗ[A] N) ⧸ I ^ m • (⊤ : Submodule A (M →ₗ[A] N))) :
    comparison I n (AdicCompletion.transitionMap I (M →ₗ[A] N) h ξ) =
      targetTransition I h (comparison I m ξ) := by
  induction ξ using Submodule.Quotient.induction_on with | _ f => rfl

/-- The inverse sequence `n ↦ Hom_A(M, N) ⧸ Iⁿ Hom_A(M, N)`. -/
noncomputable def homQuotSystem (I : Ideal A) : ℕᵒᵖ ⥤ ModuleCat.{max v w} A where
  obj n := ModuleCat.of A ((M →ₗ[A] N) ⧸ I ^ n.unop • (⊤ : Submodule A (M →ₗ[A] N)))
  map h := ModuleCat.ofHom (AdicCompletion.transitionMap I (M →ₗ[A] N) (leOfHom h.unop))
  map_id _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun ξ => ?_)
    induction ξ using Submodule.Quotient.induction_on with | _ f => rfl
  map_comp _ _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun ξ => ?_)
    induction ξ using Submodule.Quotient.induction_on with | _ f => rfl

/-- The inverse sequence `n ↦ Hom_A(M, N ⧸ Iⁿ N)`. -/
noncomputable def targetSystem (I : Ideal A) : ℕᵒᵖ ⥤ ModuleCat.{max v w} A where
  obj n := ModuleCat.of A (M →ₗ[A] (N ⧸ I ^ n.unop • (⊤ : Submodule A N)))
  map h := ModuleCat.ofHom (targetTransition I (leOfHom h.unop))
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun g => targetTransition_refl I _ g)
  map_comp f g :=
    ModuleCat.hom_ext (LinearMap.ext fun h =>
      (targetTransition_trans I (leOfHom g.unop) (leOfHom f.unop) h).symm)

/-- The transition maps of `homQuotSystem` are the adic transition maps of `Hom_A(M, N)`. -/
theorem tr_homQuotSystem (I : Ideal A) {n m : ℕ} (h : n ≤ m) :
    InverseSequence.tr (homQuotSystem (M := M) (N := N) I) h =
      ModuleCat.ofHom (AdicCompletion.transitionMap I (M →ₗ[A] N) h) := rfl

/-- The transition maps of `targetSystem` are the maps `targetTransition`. -/
theorem tr_targetSystem (I : Ideal A) {n m : ℕ} (h : n ≤ m) :
    InverseSequence.tr (targetSystem (M := M) (N := N) I) h =
      ModuleCat.ofHom (targetTransition (M := M) (N := N) I h) := rfl

end Comparison

/-! ### Pro-injectivity -/

section ProInjective

variable {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

/-- Artin–Rees shift for a map into a finite free module: if every value of `L x` lies in
`I ^ (n + c) N`, then `x` lies in `ker L + Iⁿ P`, for a `c` independent of `n`. -/
private theorem exists_mem_ker_sup_pow_smul {P : Type*} [AddCommGroup P] [Module A P] {r : ℕ}
    (I : Ideal A) (L : P →ₗ[A] (Fin r → N)) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : P), (∀ i, L x i ∈ I ^ (n + c) • (⊤ : Submodule A N)) →
      x ∈ LinearMap.ker L ⊔ I ^ n • (⊤ : Submodule A P) := by
  obtain ⟨c, hc⟩ := Stacks.AdicCompletion.exists_comap_pow_smul_le_ker_sup I L
  exact ⟨c, fun n x hx => hc n (n + c) le_rfl (mem_pow_smul_pi _ _ hx)⟩

/-- **Pro-injectivity, as Artin–Rees for a module of homomorphisms.**  There is a constant `c`,
independent of `n`, such that a homomorphism `M →ₗ N` whose image lies in `I ^ (n + c) N`
already lies in `Iⁿ Hom_A(M, N)`.

Generators `s₁, …, s_r` of `M` embed `Hom_A(M, N)` into `Nʳ` by evaluation, and the image of a
homomorphism lies in `I ^ l N` exactly when its tuple of values lies in `I ^ l Nʳ`.  The
statement is then the Artin–Rees shift for that embedding. -/
theorem exists_mem_pow_smul_of_range_le (I : Ideal A) :
    ∃ c : ℕ, ∀ (n : ℕ) (f : M →ₗ[A] N),
      (∀ x, f x ∈ I ^ (n + c) • (⊤ : Submodule A N)) →
        f ∈ I ^ n • (⊤ : Submodule A (M →ₗ[A] N)) := by
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  set ev : (M →ₗ[A] N) →ₗ[A] (Fin r → N) :=
    LinearMap.pi (fun i => LinearMap.applyₗ (s i))
  have hker : LinearMap.ker ev = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun f hf => ?_
    refine LinearMap.ext_on hs fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact congrFun hf i
  obtain ⟨c, hc⟩ := exists_mem_ker_sup_pow_smul I ev
  refine ⟨c, fun n f hf => ?_⟩
  simpa only [hker, bot_sup_eq] using hc n f fun i => hf (s i)

/-- **Pro-injectivity of the comparison.**  There is a constant `c`, independent of `n`, such
that the transition map down to level `n` kills the kernel of the comparison at level `n + c`:
the kernel of the comparison is pro-zero. -/
theorem exists_transition_eq_zero_of_comparison_eq_zero (I : Ideal A) :
    ∃ c : ℕ, ∀ (n : ℕ) (ξ : (M →ₗ[A] N) ⧸ I ^ (n + c) • (⊤ : Submodule A (M →ₗ[A] N))),
      comparison I (n + c) ξ = 0 →
        AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right n c) ξ = 0 := by
  obtain ⟨c, hc⟩ := exists_mem_pow_smul_of_range_le (M := M) (N := N) I
  refine ⟨c, fun n ξ hξ => ?_⟩
  induction ξ using Submodule.Quotient.induction_on with
  | _ f =>
    exact (Submodule.Quotient.mk_eq_zero _).2
      (hc n f ((comparison_mk_eq_zero_iff I (n + c) f).1 hξ))

end ProInjective

/-! ### Pro-surjectivity -/

section ProSurjective

variable {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

omit [IsNoetherianRing A] [Module.Finite A M] [Module.Finite A N] in
/-- A homomorphism killed by the kernel of a surjection factors through the surjection. -/
theorem exists_comp_eq_of_surjective {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] M) (hπ : Function.Surjective π) (l : P →ₗ[A] N)
    (hl : LinearMap.ker π ≤ LinearMap.ker l) :
    ∃ f : M →ₗ[A] N, ∀ x, f (π x) = l x := by
  refine ⟨(Submodule.liftQ _ l hl).comp (π.quotKerEquivOfSurjective hπ).symm.toLinearMap,
    fun x => ?_⟩
  change Submodule.liftQ _ l hl ((π.quotKerEquivOfSurjective hπ).symm (π x)) = l x
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- **Pro-surjectivity, as Artin–Rees for the relations of a presentation.**  There is a
constant `c`, independent of `n`, such that every homomorphism `g : M →ₗ N ⧸ I ^ (n + c) N`
reduces, at level `n`, to the comparison of an honest homomorphism `M →ₗ N`: the cokernel of the
comparison is pro-zero.

Write `M` as a quotient of `Aʳ` by the kernel `Z` of the projection, a finite module because `A`
is Noetherian, with generators `z₁, …, z_t`.  Lift `g` along the projection to `l : Aʳ →ₗ N`,
which is possible because `Aʳ` is free; then `l` carries each `z_j` into `I ^ (n + c) N`, since
`g` kills the relations.  Artin–Rees for the map `(Aʳ →ₗ N) ⟶ Nᵗ` evaluating at the `z_j` splits
`l` as a homomorphism killing `Z` — which factors through `M` — plus an element of
`Iⁿ (Aʳ →ₗ N)`, and the second summand is invisible at level `n`. -/
theorem exists_comparison_eq_targetTransition (I : Ideal A) :
    ∃ c : ℕ, ∀ (n : ℕ) (g : M →ₗ[A] (N ⧸ I ^ (n + c) • (⊤ : Submodule A N))),
      ∃ f : M →ₗ[A] N,
        targetTransition I (Nat.le_add_right n c) g =
          comparison I n (Submodule.Quotient.mk f) := by
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have hπ : Function.Surjective (Fintype.linearCombination A s) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hs]
  obtain ⟨t, z, hz⟩ := Module.Finite.exists_fin (R := A)
    (M := LinearMap.ker (Fintype.linearCombination A s))
  set L : ((Fin r → A) →ₗ[A] N) →ₗ[A] (Fin t → N) :=
    LinearMap.pi (fun j => LinearMap.applyₗ ((z j : Fin r → A)))
  obtain ⟨c, hc⟩ := exists_mem_ker_sup_pow_smul I L
  refine ⟨c, fun n g => ?_⟩
  obtain ⟨l, hlg⟩ := Module.projective_lifting_property
    (I ^ (n + c) • (⊤ : Submodule A N)).mkQ (g.comp (Fintype.linearCombination A s))
    (Submodule.mkQ_surjective _)
  have hlz : ∀ j, l (z j : Fin r → A) ∈ I ^ (n + c) • (⊤ : Submodule A N) := by
    intro j
    refine (Submodule.Quotient.mk_eq_zero _).1 ?_
    have h1 : (I ^ (n + c) • (⊤ : Submodule A N)).mkQ (l (z j : Fin r → A)) =
        g (Fintype.linearCombination A s (z j : Fin r → A)) := LinearMap.congr_fun hlg _
    have h2 : Fintype.linearCombination A s (z j : Fin r → A) = 0 := (z j).2
    rw [h2, map_zero] at h1
    exact h1
  obtain ⟨l₀, hl₀, l₁, hl₁, hsum⟩ := Submodule.mem_sup.1 (hc n l hlz)
  have hl₀ker : LinearMap.ker (Fintype.linearCombination A s) ≤ LinearMap.ker l₀ := by
    intro y hy
    have hcomp : l₀.comp (LinearMap.ker (Fintype.linearCombination A s)).subtype = 0 := by
      refine LinearMap.ext_on hz fun x hx => ?_
      obtain ⟨j, rfl⟩ := hx
      exact congrFun (LinearMap.mem_ker.1 hl₀) j
    exact LinearMap.congr_fun hcomp ⟨y, hy⟩
  obtain ⟨f, hf⟩ := exists_comp_eq_of_surjective _ hπ l₀ hl₀ker
  refine ⟨f, LinearMap.ext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := hπ x
  have hgy : g (Fintype.linearCombination A s y) =
      (I ^ (n + c) • (⊤ : Submodule A N)).mkQ (l y) := (LinearMap.congr_fun hlg y).symm
  rw [targetTransition_apply, hgy, comparison_mk_apply, hf y]
  refine (Submodule.Quotient.eq _).2 ?_
  have hdiff : l y - l₀ y = l₁ y := by rw [← hsum]; simp
  change l y - l₀ y ∈ I ^ n • (⊤ : Submodule A N)
  rw [hdiff]
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) (LinearMap.applyₗ y) hl₁

end ProSurjective

/-! ### The pro-isomorphism -/

section ProIso

variable {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

/-- **The two halves of the pro-isomorphism at one common shift.**  For a single constant `c`:
the reduction to level `n` of a homomorphism `M →ₗ N ⧸ I ^ (n + c) N` is in the image of the
comparison at `n`, and the transition map down to level `n` kills the kernel of the comparison
at level `n + c`. -/
theorem exists_proSection_and_proCancellation (I : Ideal A) :
    ∃ c : ℕ,
      (∀ (n : ℕ) (g : M →ₗ[A] (N ⧸ I ^ (n + c) • (⊤ : Submodule A N))),
        ∃ f : M →ₗ[A] N,
          targetTransition I (Nat.le_add_right n c) g =
            comparison I n (Submodule.Quotient.mk f)) ∧
      (∀ (n : ℕ) (ξ : (M →ₗ[A] N) ⧸ I ^ (n + c) • (⊤ : Submodule A (M →ₗ[A] N))),
        comparison I (n + c) ξ = 0 →
          AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right n c) ξ = 0) := by
  obtain ⟨c₁, hc₁⟩ := exists_comparison_eq_targetTransition (M := M) (N := N) I
  obtain ⟨c₂, hc₂⟩ := exists_transition_eq_zero_of_comparison_eq_zero (M := M) (N := N) I
  refine ⟨c₁ + c₂, fun n g => ?_, fun n ξ hξ => ?_⟩
  · obtain ⟨f, hf⟩ := hc₁ n (targetTransition I (by omega : n + c₁ ≤ n + (c₁ + c₂)) g)
    exact ⟨f, by rw [← hf, targetTransition_trans]⟩
  · have hηzero : comparison I (n + c₂)
        (AdicCompletion.transitionMap I (M →ₗ[A] N)
          (by omega : n + c₂ ≤ n + (c₁ + c₂)) ξ) = 0 := by
      rw [comparison_comp_transition, hξ, map_zero]
    have h1 := hc₂ n _ hηzero
    rwa [transitionMap_trans] at h1

/-- The map that pro-injectivity induces on the range of the comparison at level `n + c`: the
transition map down to level `n` kills the kernel of the comparison there, so it descends. -/
noncomputable def rangeDescend (I : Ideal A) (c : ℕ)
    (hcan : ∀ (n : ℕ) (ξ : (M →ₗ[A] N) ⧸ I ^ (n + c) • (⊤ : Submodule A (M →ₗ[A] N))),
      comparison I (n + c) ξ = 0 →
        AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right n c) ξ = 0)
    (n : ℕ) :
    (LinearMap.range (comparison (M := M) (N := N) I (n + c))) →ₗ[A]
      ((M →ₗ[A] N) ⧸ I ^ n • (⊤ : Submodule A (M →ₗ[A] N))) :=
  (Submodule.liftQ (LinearMap.ker (comparison I (n + c)))
      (AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right n c))
      (fun ξ hξ => hcan n ξ hξ)).comp
    (comparison I (n + c)).quotKerEquivRange.symm.toLinearMap

omit [IsNoetherianRing A] [Module.Finite A M] [Module.Finite A N] in
/-- `rangeDescend` sends the image of `ξ` under the comparison at level `n + c` to the reduction
of `ξ` to level `n`. -/
theorem rangeDescend_rangeRestrict (I : Ideal A) (c : ℕ) (hcan) (n : ℕ)
    (ξ : (M →ₗ[A] N) ⧸ I ^ (n + c) • (⊤ : Submodule A (M →ₗ[A] N))) :
    rangeDescend I c hcan n ((comparison I (n + c)).rangeRestrict ξ) =
      AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right n c) ξ := by
  have hsymm : (comparison (M := M) (N := N) I (n + c)).quotKerEquivRange.symm
      ((comparison I (n + c)).rangeRestrict ξ) = Submodule.Quotient.mk ξ :=
    (LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivRange_apply_mk _ ξ).symm
  have hcomp : rangeDescend I c hcan n ((comparison I (n + c)).rangeRestrict ξ) =
      Submodule.liftQ (LinearMap.ker (comparison (M := M) (N := N) I (n + c)))
        (AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right n c))
        (fun ζ hζ => hcan n ζ hζ)
        ((comparison (M := M) (N := N) I (n + c)).quotKerEquivRange.symm
          ((comparison I (n + c)).rangeRestrict ξ)) := rfl
  rw [hcomp, hsymm]
  rfl

/-- Reduction to level `n + c`, corestricted to the range of the comparison there, which
pro-surjectivity makes possible. -/
noncomputable def targetRestrict (I : Ideal A) (c : ℕ)
    (hsec : ∀ (n : ℕ) (g : M →ₗ[A] (N ⧸ I ^ (n + c) • (⊤ : Submodule A N))),
      ∃ f : M →ₗ[A] N,
        targetTransition I (Nat.le_add_right n c) g =
          comparison I n (Submodule.Quotient.mk f))
    (n : ℕ) :
    (M →ₗ[A] (N ⧸ I ^ (n + c + c) • (⊤ : Submodule A N))) →ₗ[A]
      (LinearMap.range (comparison (M := M) (N := N) I (n + c))) :=
  LinearMap.codRestrict _ (targetTransition I (Nat.le_add_right (n + c) c)) fun g => by
    obtain ⟨f, hf⟩ := hsec (n + c) g
    exact ⟨Submodule.Quotient.mk f, hf.symm⟩

/-- **The backward map of the pro-isomorphism.**  Reduce a homomorphism
`M →ₗ N ⧸ I ^ (n + c + c) N` to level `n + c`, where pro-surjectivity puts it in the range of the
comparison, and then descend to `Hom_A(M, N) ⧸ Iⁿ Hom_A(M, N)` by the map pro-injectivity
induces on that range. -/
noncomputable def proBack (I : Ideal A) (c : ℕ)
    (hsec : ∀ (n : ℕ) (g : M →ₗ[A] (N ⧸ I ^ (n + c) • (⊤ : Submodule A N))),
      ∃ f : M →ₗ[A] N,
        targetTransition I (Nat.le_add_right n c) g =
          comparison I n (Submodule.Quotient.mk f))
    (hcan : ∀ (n : ℕ) (ξ : (M →ₗ[A] N) ⧸ I ^ (n + c) • (⊤ : Submodule A (M →ₗ[A] N))),
      comparison I (n + c) ξ = 0 →
        AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right n c) ξ = 0)
    (n : ℕ) :
    (M →ₗ[A] (N ⧸ I ^ (n + c + c) • (⊤ : Submodule A N))) →ₗ[A]
      ((M →ₗ[A] N) ⧸ I ^ n • (⊤ : Submodule A (M →ₗ[A] N))) :=
  (rangeDescend I c hcan n).comp (targetRestrict I c hsec n)

omit [IsNoetherianRing A] [Module.Finite A M] [Module.Finite A N] in
/-- The backward map is characterised by the comparison: whenever the reduction of `g` to level
`n + c` is the comparison of `ξ`, the backward map sends `g` to the transition of `ξ`. -/
theorem proBack_eq (I : Ideal A) (c : ℕ) (hsec) (hcan) (n : ℕ)
    (g : M →ₗ[A] (N ⧸ I ^ (n + c + c) • (⊤ : Submodule A N)))
    (ξ : (M →ₗ[A] N) ⧸ I ^ (n + c) • (⊤ : Submodule A (M →ₗ[A] N)))
    (h : targetTransition I (Nat.le_add_right (n + c) c) g = comparison I (n + c) ξ) :
    proBack I c hsec hcan n g =
      AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right n c) ξ := by
  have hcod : targetRestrict I c hsec n g = (comparison I (n + c)).rangeRestrict ξ :=
    Subtype.ext h
  exact (congrArg (rangeDescend I c hcan n) hcod).trans
    (rangeDescend_rangeRestrict I c hcan n ξ)

/-- **The comparison is a pro-isomorphism.**  For finite modules `M`, `N` over a Noetherian
ring `A` and an ideal `I`, the comparison

`Hom_A(M, N) ⧸ Iⁿ Hom_A(M, N) ⟶ Hom_A(M, N ⧸ Iⁿ N)`

is a pro-isomorphism of inverse sequences: after a shift of the index it has a two-sided
inverse, compatibly with the transition maps.  The comparison is an isomorphism at no single
level, its kernel and cokernel being killed by a power of `I` and no more, and the shift is what
absorbs that failure.

The forward maps are the comparisons themselves, at no shift; the backward maps are
`Stacks.AdicSystem.HomProIso.proBack`, built from pro-surjectivity and pro-injectivity at one
common shift `c`, at the shift `n + c + c`. -/
theorem nonempty_proIso (I : Ideal A) :
    Nonempty (InverseSequence.ProIso (homQuotSystem (M := M) (N := N) I)
      (targetSystem (M := M) (N := N) I)) := by
  obtain ⟨c, hsec, hcan⟩ := exists_proSection_and_proCancellation (M := M) (N := N) I
  have hβmono : Monotone (fun n : ℕ => n + c + c) := fun a b h =>
    Nat.add_le_add_right (Nat.add_le_add_right h c) c
  have hβle : ∀ n : ℕ, n ≤ n + c + c := fun n =>
    (Nat.le_add_right n c).trans (Nat.le_add_right (n + c) c)
  -- The forward maps form a morphism of inverse sequences.
  have hφnat : ∀ {n m : ℕ} (h : n ≤ m),
      InverseSequence.tr (homQuotSystem (M := M) (N := N) I) h ≫
          ModuleCat.ofHom (comparison (M := M) (N := N) I n) =
        ModuleCat.ofHom (comparison (M := M) (N := N) I m) ≫
          InverseSequence.tr (targetSystem (M := M) (N := N) I) h := by
    intro n m h
    exact ModuleCat.hom_ext (LinearMap.ext fun ξ => comparison_comp_transition I h ξ)
  -- The backward maps are compatible with the transition maps.
  have hψnat : ∀ {n m : ℕ} (h : n ≤ m)
      (g : M →ₗ[A] (N ⧸ I ^ (m + c + c) • (⊤ : Submodule A N))),
      proBack I c hsec hcan n (targetTransition I (hβmono h) g) =
        AdicCompletion.transitionMap I (M →ₗ[A] N) h (proBack I c hsec hcan m g) := by
    intro n m h g
    obtain ⟨f, hf⟩ := hsec (m + c) g
    have hm : proBack I c hsec hcan m g =
        AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right m c)
          (Submodule.Quotient.mk f) := proBack_eq I c hsec hcan m g _ hf
    have hn : proBack I c hsec hcan n (targetTransition I (hβmono h) g) =
        AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right n c)
          (AdicCompletion.transitionMap I (M →ₗ[A] N)
            (by omega : n + c ≤ m + c) (Submodule.Quotient.mk f)) := by
      refine proBack_eq I c hsec hcan n _ _ ?_
      rw [comparison_comp_transition, ← hf, targetTransition_trans, targetTransition_trans]
    rw [hn, hm, transitionMap_trans, transitionMap_trans]
  -- Backward after forward is a transition map of the source.
  have hψφ : ∀ (n : ℕ) (ξ : (M →ₗ[A] N) ⧸ I ^ (n + c + c) • (⊤ : Submodule A (M →ₗ[A] N))),
      proBack I c hsec hcan n (comparison I (n + c + c) ξ) =
        AdicCompletion.transitionMap I (M →ₗ[A] N) (hβle n) ξ := by
    intro n ξ
    have key : proBack I c hsec hcan n (comparison I (n + c + c) ξ) =
        AdicCompletion.transitionMap I (M →ₗ[A] N) (Nat.le_add_right n c)
          (AdicCompletion.transitionMap I (M →ₗ[A] N)
            (Nat.le_add_right (n + c) c) ξ) := by
      refine proBack_eq I c hsec hcan n _ _ ?_
      rw [comparison_comp_transition]
    rw [key, transitionMap_trans]
  -- Forward after backward is a transition map of the target.
  have hφψ : ∀ (n : ℕ) (g : M →ₗ[A] (N ⧸ I ^ (n + c + c) • (⊤ : Submodule A N))),
      comparison I n (proBack I c hsec hcan n g) = targetTransition I (hβle n) g := by
    intro n g
    obtain ⟨f, hf⟩ := hsec (n + c) g
    rw [proBack_eq I c hsec hcan n g _ hf, comparison_comp_transition, ← hf,
      targetTransition_trans]
  exact ⟨{
    α := id
    β := fun n => n + c + c
    αmono := monotone_id
    βmono := hβmono
    αle := fun n => le_refl n
    βle := hβle
    φ := fun n => ModuleCat.ofHom (comparison I n)
    ψ := fun n => ModuleCat.ofHom (proBack I c hsec hcan n)
    φnat := fun h => hφnat h
    ψnat := fun h => ModuleCat.hom_ext (LinearMap.ext fun g => hψnat h g)
    ψφ := fun n => ModuleCat.hom_ext (LinearMap.ext fun ξ => hψφ n ξ)
    φψ := fun n => ModuleCat.hom_ext (LinearMap.ext fun g => hφψ n g) }⟩

end ProIso

end Stacks.AdicSystem.HomProIso

end
