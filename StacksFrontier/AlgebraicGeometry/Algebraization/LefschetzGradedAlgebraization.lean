module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationSituation
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit

/-!
# Graded algebraization in the Lefschetz situation

Work in the algebraization situation of a Noetherian ring `A` with ideals `I ⊆ 𝔞`, and assume
`A` is graded with `𝔞 = A₊` the irrelevant ideal and `I` homogeneous. A coherent formal module
on `U = Spec(A) ∖ V(𝔞)` which is presented by an inverse system `(Mₙ)` of graded `A`-modules and
which extends canonically to `Spec(A)` is the completion of a single finite graded `A`-module.

The geometry enters only through the graded inverse system `(Nₙ)` that the `𝐆ₘ`-equivariant
structure attaches to the canonical extension, and through the comparison `(Mₙ) → (Nₙ)` whose
kernel and cokernel are `𝔞`-power torsion.

## Main results

* `Stacks.Algebraization.exists_finite_graded_algebraization` — the finite graded module `N`,
  the identification `N/IⁿN ≃ Nₙ` compatible with the transition maps, and the graded
  comparison of `(Mₙ)` with `(N/IⁿN)` modulo `𝔞`-power torsion.

## Implementation notes

The source's index `n` runs over all of `ℕ` here, so the level `0` term is forced to vanish:
`I⁰ = A`. Degrees of modules are integers and degrees of the ring are naturals, as in Stacks
0EKC. The quotients `N/IⁿN` appear literally, as `P ⧸ Iⁿ • ⊤`; a map into such a quotient is
called degree-preserving when every homogeneous element of degree `d` is sent to the class of a
homogeneous element of degree `d`, and the inverse system structure on the quotients is the
family of canonical projections, written out elementwise rather than through `Submodule.mapQ`.

The `𝐆ₘ`-equivariant descent of the canonical extension (Stacks 0EKJ, 0EKL, 0EIS, 0EIR) and the
torsion comparison of Stacks 0BK0 are carried as hypotheses.

## References

* [Stacks Project, Tag 0EL4](https://stacks.math.columbia.edu/tag/0EL4)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 0EKC](https://stacks.math.columbia.edu/tag/0EKC)
-/


@[expose] public section

open scoped Pointwise

universe u v w

namespace Stacks.Algebraization

section Graded

attribute [local instance] Classical.propDecidable

variable {A : Type u} [CommRing A]

/-- Ideal-power torsion transports along a linear equivalence. -/
private lemma isIPowerTorsion_of_linearEquiv {X Y : Type w} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] {I : Ideal A} (e : X ≃ₗ[A] Y) (h : IsIPowerTorsion A X I) :
    IsIPowerTorsion A Y I := by
  intro y
  obtain ⟨n, hn, h0⟩ := h (e.symm y)
  refine ⟨n, hn, fun a ha => ?_⟩
  have h1 := congrArg e (h0 a ha)
  simpa using h1

variable {X : Type w} [AddCommGroup X] (𝒳 : ℤ → AddSubgroup X) [DirectSum.Decomposition 𝒳]

/-- The degree-`d` homogeneous component of an element of a graded module. -/
private noncomputable def component (d : ℤ) : X →+ X where
  toFun x := (DirectSum.decompose 𝒳 x d : X)
  map_zero' := by simp
  map_add' x y := by
    simp only [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]

private lemma component_mem (d : ℤ) (x : X) : component 𝒳 d x ∈ 𝒳 d :=
  (DirectSum.decompose 𝒳 x d).2

private lemma component_of_mem_same {d : ℤ} {x : X} (hx : x ∈ 𝒳 d) : component 𝒳 d x = x :=
  DirectSum.decompose_of_mem_same 𝒳 hx

private lemma component_of_mem_ne {d d' : ℤ} {x : X} (hx : x ∈ 𝒳 d) (h : d ≠ d') :
    component 𝒳 d' x = 0 :=
  DirectSum.decompose_of_mem_ne 𝒳 hx h

variable [Module A X] {Y : Type w} [AddCommGroup Y] [Module A Y] (𝒴 : ℤ → AddSubgroup Y)
  [DirectSum.Decomposition 𝒴]

/-- A degree-preserving map commutes with taking homogeneous components. -/
private lemma component_comp (f : X →ₗ[A] Y) (hf : ∀ (d : ℤ) (x : X), x ∈ 𝒳 d → f x ∈ 𝒴 d)
    (d : ℤ) (x : X) : component 𝒴 d (f x) = f (component 𝒳 d x) := by
  induction x using DirectSum.Decomposition.inductionOn 𝒳 with
  | zero => simp
  | @homogeneous i x =>
    by_cases h : i = d
    · subst h
      rw [component_of_mem_same 𝒳 x.2, component_of_mem_same 𝒴 (hf _ _ x.2)]
    · rw [component_of_mem_ne 𝒳 x.2 h, component_of_mem_ne 𝒴 (hf _ _ x.2) h, map_zero]
  | add x y hx hy => simp [hx, hy]

/-- A degree-preserving surjection of graded modules is surjective in every degree. -/
private lemma exists_mem_grade_eq_of_surjective (f : X →ₗ[A] Y)
    (hf : ∀ (d : ℤ) (x : X), x ∈ 𝒳 d → f x ∈ 𝒴 d) (hsurj : Function.Surjective f)
    {d : ℤ} {y : Y} (hy : y ∈ 𝒴 d) : ∃ x ∈ 𝒳 d, f x = y := by
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨component 𝒳 d x, component_mem 𝒳 d x,
    (component_comp 𝒳 𝒴 f hf d x).symm.trans (component_of_mem_same 𝒴 hy)⟩

end Graded
section Quotients

variable {A : Type u} [CommRing A] {P : Type w} [AddCommGroup P] [Module A P]

/-- A compatible system of surjections with kernels `Iⁿ P` identifies the quotients
`P/IⁿP` with the targets, compatibly with the quotient maps. -/
private lemma exists_quotPowEquiv {N : ℕ → Type w} [∀ n, AddCommGroup (N n)]
    [∀ n, Module A (N n)] (I : Ideal A) (f : ∀ n, P →ₗ[A] N n)
    (hfsurj : ∀ n, Function.Surjective (f n))
    (hfker : ∀ n, LinearMap.ker (f n) = I ^ n • (⊤ : Submodule A P)) :
    ∃ e : ∀ n, (P ⧸ I ^ n • (⊤ : Submodule A P)) ≃ₗ[A] N n,
      ∀ (n : ℕ) (x : P), e n (Submodule.Quotient.mk x) = f n x := by
  refine ⟨fun n => (Submodule.quotEquivOfEq _ _ (hfker n).symm).trans
    ((f n).quotKerEquivOfSurjective (hfsurj n)), fun n x => ?_⟩
  simp [LinearMap.quotKerEquivOfSurjective_apply_mk]

variable {X Y Z : Type w} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
  [AddCommGroup Z] [Module A Z]

/-- Precomposing an isomorphism with a linear map does not change the kernel, so the kernel
stays ideal-power torsion. -/
private lemma isIPowerTorsion_ker_symm_comp {I : Ideal A} (e : X ≃ₗ[A] Y) (c : Z →ₗ[A] Y)
    (h : IsIPowerTorsion A (LinearMap.ker c) I) :
    IsIPowerTorsion A (LinearMap.ker (e.symm.toLinearMap.comp c)) I := by
  have hk : LinearMap.ker (e.symm.toLinearMap.comp c) = LinearMap.ker c := by
    ext z
    simp
  exact isIPowerTorsion_of_linearEquiv (LinearEquiv.ofEq _ _ hk.symm) h

/-- Precomposing an isomorphism with a linear map carries its cokernel isomorphically, so the
cokernel stays ideal-power torsion. -/
private lemma isIPowerTorsion_coker_symm_comp {I : Ideal A} (e : X ≃ₗ[A] Y) (c : Z →ₗ[A] Y)
    (h : IsIPowerTorsion A (Y ⧸ LinearMap.range c) I) :
    IsIPowerTorsion A (X ⧸ LinearMap.range (e.symm.toLinearMap.comp c)) I := by
  refine isIPowerTorsion_of_linearEquiv
    (Submodule.Quotient.equiv _ _ e.symm ?_) h
  exact (LinearMap.range_comp c _).symm

end Quotients

/-- In the algebraization situation of a graded ring `A` whose irrelevant ideal is `𝔞` and whose
ideal `I` is homogeneous, let `(Mₙ)` be the inverse system of graded modules presenting a coherent
formal module on `U`, let `(Nₙ)` be the graded inverse system attached to its canonical extension,
and let `(Mₙ) → (Nₙ)` be a degree-preserving comparison with `𝔞`-power torsion kernel and cokernel.
Then there is a finite graded `A`-module `N` with `N/IⁿN ≃ Nₙ` compatibly with the transition maps,
and `(Mₙ)` maps to the inverse system `(N/IⁿN)` by degree-preserving maps with `𝔞`-power torsion
kernel and cokernel. -/
@[stacks 0EL4 "(a) and (b); graded Gm-descent (0EKL) and the 0BK0 comparison hypothesised"]
public theorem exists_finite_graded_algebraization (S : AlgebraizationSituation.{u})
    {σ : Type v} [SetLike σ S.A] [AddSubmonoidClass σ S.A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (hirr : S.a = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) (hIhom : S.I.IsHomogeneous 𝒜)
    {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module S.A (M n)]
    (ℳ : ∀ n, ℤ → AddSubgroup (M n)) [∀ n, DirectSum.Decomposition (ℳ n)]
    (s : ∀ n, M (n + 1) →ₗ[S.A] M n)
    {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module S.A (N n)]
    [∀ n, Module.Finite S.A (N n)]
    (𝒩 : ∀ n, ℤ → AddSubgroup (N n)) [∀ n, DirectSum.Decomposition (𝒩 n)]
    (h𝒩 : ∀ (n i : ℕ) (d : ℤ) (a : S.A) (x : N n), a ∈ 𝒜 i → x ∈ 𝒩 n d → a • x ∈ 𝒩 n (i + d))
    (t : ∀ n, N (n + 1) →ₗ[S.A] N n)
    (ht : ∀ (n : ℕ) (d : ℤ) (x : N (n + 1)), x ∈ 𝒩 (n + 1) d → t n x ∈ 𝒩 n d)
    (htsurj : ∀ n, Function.Surjective (t n))
    (htker : ∀ n, LinearMap.ker (t n) = S.I ^ n • (⊤ : Submodule S.A (N (n + 1))))
    (c : ∀ n, M n →ₗ[S.A] N n)
    (hc : ∀ (n : ℕ) (d : ℤ) (x : M n), x ∈ ℳ n d → c n x ∈ 𝒩 n d)
    (hcs : ∀ n, (t n).comp (c (n + 1)) = (c n).comp (s n))
    (hcker : ∀ n, IsIPowerTorsion S.A (LinearMap.ker (c n)) S.a)
    (hccoker : ∀ n, IsIPowerTorsion S.A (N n ⧸ LinearMap.range (c n)) S.a) :
    ∃ (P : Type w) (_ : AddCommGroup P) (_ : Module S.A P) (𝒬 : ℤ → AddSubgroup P)
        (_ : DirectSum.Decomposition 𝒬)
        (e : ∀ n, (P ⧸ S.I ^ n • (⊤ : Submodule S.A P)) ≃ₗ[S.A] N n)
        (g : ∀ n, M n →ₗ[S.A] P ⧸ S.I ^ n • (⊤ : Submodule S.A P)),
      Module.Finite S.A P ∧
      (∀ (i : ℕ) (d : ℤ) (a : S.A) (x : P), a ∈ 𝒜 i → x ∈ 𝒬 d → a • x ∈ 𝒬 (i + d)) ∧
      (∀ (n : ℕ) (d : ℤ) (x : P), x ∈ 𝒬 d → e n (Submodule.Quotient.mk x) ∈ 𝒩 n d) ∧
      (∀ (n : ℕ) (x : P),
        t n (e (n + 1) (Submodule.Quotient.mk x)) = e n (Submodule.Quotient.mk x)) ∧
      (∀ (n : ℕ) (x : M n), e n (g n x) = c n x) ∧
      (∀ (n : ℕ) (d : ℤ) (x : M n), x ∈ ℳ n d →
        ∃ p ∈ 𝒬 d, g n x = Submodule.Quotient.mk p) ∧
      (∀ (n : ℕ) (x : M (n + 1)) (p : P), g (n + 1) x = Submodule.Quotient.mk p →
        g n (s n x) = Submodule.Quotient.mk p) ∧
      (∀ n, IsIPowerTorsion S.A (LinearMap.ker (g n)) S.a) ∧
      (∀ n, IsIPowerTorsion S.A
        ((P ⧸ S.I ^ n • (⊤ : Submodule S.A P)) ⧸ LinearMap.range (g n)) S.a) := by
  have hI : S.I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := hirr ▸ S.I_le_a
  obtain ⟨P, hPg, hPm, 𝒬, hdec, f, hfin, hgr, hfgr, hfsurj, hfker, hfcomp⟩ :=
    hIhom.exists_finite_graded_forall_ker_eq_pow_smul_top hI 𝒩 h𝒩 t ht htsurj htker
  obtain ⟨e, he⟩ := exists_quotPowEquiv S.I f hfsurj hfker
  have hg : ∀ (n : ℕ) (x : M n),
      e n (((e n).symm.toLinearMap.comp (c n)) x) = c n x := fun n x => by simp
  refine ⟨P, hPg, hPm, 𝒬, hdec, e, fun n => (e n).symm.toLinearMap.comp (c n),
    hfin, hgr, ?_, ?_, hg, ?_, ?_, ?_, ?_⟩
  · intro n d x hx
    rw [he]
    exact hfgr n d x hx
  · intro n x
    rw [he, he, ← LinearMap.comp_apply, hfcomp]
  · intro n d x hx
    obtain ⟨p, hp, hfp⟩ :=
      exists_mem_grade_eq_of_surjective 𝒬 (𝒩 n) (f n) (hfgr n) (hfsurj n) (hc n d x hx)
    refine ⟨p, hp, (e n).injective ?_⟩
    rw [hg n x, he]
    exact hfp.symm
  · intro n x p hp
    have hx : c (n + 1) x = f (n + 1) p := by rw [← hg (n + 1) x, hp, he]
    refine (e n).injective ?_
    rw [hg n (s n x), he, show c n (s n x) = t n (c (n + 1) x) from
      (LinearMap.congr_fun (hcs n) x).symm, hx, ← LinearMap.comp_apply, hfcomp]
  · exact fun n => isIPowerTorsion_ker_symm_comp (e n) (c n) (hcker n)
  · exact fun n => isIPowerTorsion_coker_symm_comp (e n) (c n) (hccoker n)

end Stacks.Algebraization

end
