module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Ring

/-!
# Homogeneous polynomials evaluated at global sections of an invertible sheaf

Let `L` be an invertible sheaf of modules on a ringed site, let `s₀, …, s_{m-1}` be global
sections of `L^{⊗ N}` and let `P ∈ ℤ[T₀, …, T_{m-1}]` be homogeneous of degree `d`. Then
`P(s₀, …, s_{m-1})` is a global section of `L^{⊗ (d · N)}`.

This is the step that turns a homogeneous polynomial on a projective space into a section of a
tensor power, which is how a homogeneous polynomial avoiding finitely many homogeneous primes
produces the affine nonvanishing open of [Stacks, Tag 09NV] and [Stacks, Tag 0E21].

The statement is proved in two independent halves.

* A **purely graded-algebra** fact, for any internally graded commutative ring: a homogeneous
  polynomial of degree `d` evaluated at elements all of degree `N` lands in degree `d • N`.
  Mathlib has `SetLike.prod_pow_mem_graded` for a single monomial but nothing about a
  homogeneous polynomial, so this is new.
* The **internal grading of `Γ_*`** itself. The graded ring
  `Stacks.Monoidal.PowerSystem.gradedRing` is *externally* graded — a
  `DirectSum.GRing` on the family `n ↦ (𝟙_ ⟶ L^{⊗ n})` — whereas `MvPolynomial.aeval` needs a
  single ring with a `GradedRing` family of subgroups inside it. The passage between the two is
  the direct sum together with the ranges of its inclusions, exactly as
  `Stacks.RelativeProj.Situation.sectionRingGrading` does for the section rings of a relative
  `Proj`.

## Main definitions

* `Stacks.Monoidal.PowerSystem.sectionRing`: the direct sum `⨁ₙ (𝟙_ ⟶ Sₙ)` of the groups of
  global sections of the powers, a ring by `Stacks.Monoidal.PowerSystem.gradedRing`.
* `Stacks.Monoidal.PowerSystem.sectionGrading`: its degree-`n` component, the range of the
  `n`-th inclusion into the direct sum.

## Main results

* `MvPolynomial.IsHomogeneous.eval₂_mem_graded`: in an internally graded commutative ring, a
  degree-`d` homogeneous polynomial evaluated at elements of degree `N` lies in degree `d • N`,
  provided the coefficients map into degree `0`.
* `MvPolynomial.IsHomogeneous.aeval_mem_graded`: the same with integer coefficients, where the
  condition on the coefficients is automatic.
* `Stacks.Monoidal.PowerSystem.sectionGradedRing`: `⨁ₙ (𝟙_ ⟶ Sₙ)` is internally graded by
  `sectionGrading`.
* `Stacks.Monoidal.PowerSystem.exists_aeval_eq_of_isHomogeneous` and
  `Stacks.SheafOfModules.Invertible.exists_aeval_eq_of_isHomogeneous`: **a homogeneous
  polynomial of degree `d` with integer coefficients, evaluated at global sections of `L^{⊗ N}`,
  is a global section of `L^{⊗ (d * N)}`.**
* `Stacks.SheafOfModules.Invertible.exists_sections_aeval_eq_of_isHomogeneous`: the same read
  through `PresheafOfModules.sections` rather than through morphisms out of the tensor unit.

## Implementation notes

**The commutativity hypothesis `hβ` is carried, not discharged.** `MvPolynomial.aeval` requires
a *commutative* target ring, and the graded ring `Γ_*(X, L)` is only known to be commutative
given the commutativity constraint of Tag 01CU — see
`Stacks.SheafOfModules.Invertible.homGradedCommRing`, which carries it in exactly the same
form. That constraint is not a formal consequence of the symmetric monoidal axioms and is not
proved in this repository, so it appears here as a hypothesis in exactly that shape; these
results become unconditional by deleting the hypothesis as soon as it lands.

**What is unconditional.** Everything except the evaluation statements: the direct sum, the
grading, its decomposition and the `GradedRing` instance need only the unconditional
`Stacks.Monoidal.PowerSystem.gradedRing`.

The grading is by the *ranges* of the inclusions `DirectSum.of _ n` rather than by a family of
subtypes, so that membership of `sectionGrading n` says literally "comes from a global section
of the `n`-th power", which is what the evaluation statements then extract. It is an `abbrev`
rather than a `def` so that the `DirectSum` simp set applies to it.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 0E21](https://stacks.math.columbia.edu/tag/0E21)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
-/

@[expose] public section

open CategoryTheory MonoidalCategory DirectSum Finset
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u w

/-! ### Homogeneous polynomials in an internally graded commutative ring -/

namespace MvPolynomial.IsHomogeneous

section Eval

variable {σ R A ι S : Type*} [CommSemiring R] [CommSemiring A] [AddCommMonoid ι]
  [SetLike S A] [AddSubmonoidClass S A] (𝒜 : ι → S) [SetLike.GradedMonoid 𝒜]

/-- A homogeneous polynomial of degree `d` evaluated at elements of degree `N` of an internally
graded commutative ring lies in degree `d • N`, provided every coefficient maps into degree `0`.

Mathlib's `SetLike.prod_pow_mem_graded` is this statement for a single monomial; the content
here is that the degree of each monomial of `p` is the degree of `p`, which is homogeneity. -/
theorem eval₂_mem_graded {g : R →+* A} (hg : ∀ r, g r ∈ 𝒜 0) {x : σ → A} {N : ι}
    (hx : ∀ i, x i ∈ 𝒜 N) {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    MvPolynomial.eval₂ g x p ∈ 𝒜 (d • N) := by
  classical
  rw [MvPolynomial.eval₂_eq]
  refine sum_mem fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have := hp (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight, Finsupp.linearCombination, Finsupp.sum] using this
  have hprod : ∏ i ∈ m.support, x i ^ m i ∈ 𝒜 (∑ i ∈ m.support, m i • N) :=
    SetLike.prod_pow_mem_graded 𝒜 (fun _ => N) x (fun i => m i) fun i _ => hx i
  rw [← Finset.sum_smul, hdeg] at hprod
  simpa using SetLike.mul_mem_graded (hg (MvPolynomial.coeff m p)) hprod

end Eval

section AEval

variable {σ A ι S : Type*} [CommRing A] [AddCommMonoid ι] [SetLike S A] [AddSubgroupClass S A]
  (𝒜 : ι → S) [SetLike.GradedMonoid 𝒜]

/-- A homogeneous polynomial of degree `d` with **integer** coefficients, evaluated at elements
of degree `N` of an internally graded commutative ring, lies in degree `d • N`. The hypothesis
of `MvPolynomial.IsHomogeneous.eval₂_mem_graded` on the coefficients is automatic: an integer is
an integer multiple of `1`, which has degree `0`. -/
theorem aeval_mem_graded {x : σ → A} {N : ι} (hx : ∀ i, x i ∈ 𝒜 N)
    {p : MvPolynomial σ ℤ} {d : ℕ} (hp : p.IsHomogeneous d) :
    MvPolynomial.aeval x p ∈ 𝒜 (d • N) := by
  rw [MvPolynomial.aeval_def]
  refine hp.eval₂_mem_graded 𝒜 (fun r => ?_) hx
  have h : (algebraMap ℤ A) r = r • (1 : A) := by simp
  rw [h]
  exact zsmul_mem (SetLike.one_mem_graded 𝒜) r

end AEval

end MvPolynomial.IsHomogeneous

/-! ### The internal grading of the graded ring of sections -/

namespace Stacks.Monoidal

namespace PowerSystem

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] (S : PowerSystem C)

/-- The graded ring of global sections of a power system, as the direct sum of its homogeneous
pieces. It is a ring by `Stacks.Monoidal.PowerSystem.gradedRing`, and a commutative ring by
`Stacks.Monoidal.PowerSystem.gradedCommRing` under the commutativity constraint. -/
abbrev sectionRing := ⨁ n : ℕ, (𝟙_ C ⟶ S.obj n)

/-- The degree-`n` homogeneous component of `Stacks.Monoidal.PowerSystem.sectionRing`: the range
of the `n`-th inclusion into the direct sum, so that an element lies in it exactly when it comes
from a global section of the `n`-th power. -/
abbrev sectionGrading (n : ℕ) : AddSubgroup S.sectionRing :=
  (DirectSum.of (fun n : ℕ => 𝟙_ C ⟶ S.obj n) n).range

omit [MonoidalPreadditive C] in
/-- A global section of the `n`-th power has degree `n` in the ring of sections. -/
theorem of_mem_sectionGrading {n : ℕ} (t : 𝟙_ C ⟶ S.obj n) :
    DirectSum.of (fun n : ℕ => 𝟙_ C ⟶ S.obj n) n t ∈ S.sectionGrading n :=
  ⟨t, rfl⟩

/-- The ring of sections, decomposed by its own summands. -/
@[instance_reducible]
noncomputable def sectionRingDecomposition : DirectSum.Decomposition S.sectionGrading := by
  classical
  let d : S.sectionRing →+ ⨁ n : ℕ, S.sectionGrading n :=
    DirectSum.toAddMonoid fun n =>
      (DirectSum.of (fun n : ℕ => S.sectionGrading n) n).comp
        (DirectSum.of (fun n : ℕ => 𝟙_ C ⟶ S.obj n) n).rangeRestrict
  refine DirectSum.Decomposition.ofAddHom _ d ?_ ?_
  · apply DirectSum.addHom_ext
    intro n x
    simp [d]
  · apply DirectSum.addHom_ext
    intro n ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := hx
    simp [d]; rfl

section GradedRing

variable [DirectSum.GRing (fun n : ℕ => 𝟙_ C ⟶ S.obj n)]

/-- The ring of global sections of a power system is internally graded by its homogeneous
summands. -/
noncomputable instance sectionGradedRing : GradedRing S.sectionGrading where
  __ := S.sectionRingDecomposition
  one_mem := ⟨_, (DirectSum.one_def _).symm⟩
  mul_mem := by
    rintro n m a b ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨_, (DirectSum.of_mul_of (A := fun n : ℕ => 𝟙_ C ⟶ S.obj n) a b).symm⟩

end GradedRing

section Evaluation

variable [DirectSum.GCommRing (fun n : ℕ => 𝟙_ C ⟶ S.obj n)]

omit [MonoidalPreadditive C] in
/-- **A homogeneous polynomial of degree `d` with integer coefficients, evaluated at global
sections of the `N`-th power, is a global section of the `(d * N)`-th power.** -/
theorem exists_aeval_eq_of_isHomogeneous {σ : Type*} {N : ℕ} (x : σ → (𝟙_ C ⟶ S.obj N))
    {P : MvPolynomial σ ℤ} {d : ℕ} (hP : P.IsHomogeneous d) :
    ∃ t : 𝟙_ C ⟶ S.obj (d * N),
      DirectSum.of (fun n : ℕ => 𝟙_ C ⟶ S.obj n) (d * N) t =
        MvPolynomial.aeval
          (fun i => DirectSum.of (fun n : ℕ => 𝟙_ C ⟶ S.obj n) N (x i)) P := by
  have h := hP.aeval_mem_graded S.sectionGrading
    (x := fun i => DirectSum.of (fun n : ℕ => 𝟙_ C ⟶ S.obj n) N (x i)) (N := N)
    fun i => S.of_mem_sectionGrading (x i)
  rw [smul_eq_mul] at h
  exact h

end Evaluation

end PowerSystem

end Stacks.Monoidal

/-! ### Homogeneous polynomials in the global sections of an invertible sheaf -/

namespace Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
  Stacks.SheafOfModules.monoidalPreadditive Stacks.SheafOfModules.braidedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L]

/-- **A homogeneous polynomial of degree `d` with integer coefficients, evaluated at global
sections of `L^{⊗ N}`, is a global section of `L^{⊗ (d * N)}`**, given the commutativity
constraint `hβ` of Tag 01CU.

This is the construction `P ↦ P(s₀, …, s_{m-1})` by which [Stacks, Tag 09NV] and
[Stacks, Tag 0E21] turn a homogeneous polynomial on a projective space into a section of a
tensor power of `L`. The sections are spelled as morphisms out of the tensor unit, which is how
the graded ring `Stacks.Monoidal.PowerSystem.gradedRing` is indexed; see
`Stacks.SheafOfModules.Invertible.exists_sections_aeval_eq_of_isHomogeneous` for the version in
`PresheafOfModules.sections`. -/
theorem exists_aeval_eq_of_isHomogeneous
    (hβ : ∀ a b : ℕ, (β_ (tensorPower O hO L (a : ℤ)) (tensorPower O hO L (b : ℤ))).hom
        ≫ (tensorPowerMulIso O hO L b a).hom
      = (tensorPowerMulIso O hO L a b).hom
        ≫ eqToHom (congrArg (fun k : ℕ => tensorPower O hO L (k : ℤ)) (Nat.add_comm a b)))
    {σ : Type*} {N : ℕ}
    (x : σ → (𝟙_ (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      ⟶ tensorPower O hO L (N : ℤ)))
    {P : MvPolynomial σ ℤ} {d : ℕ} (hP : P.IsHomogeneous d) :
    letI := homGradedCommRing O hO L hβ
    ∃ t : 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
        ⟶ tensorPower O hO L ((d * N : ℕ) : ℤ),
      DirectSum.of (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ⟶ tensorPower O hO L (n
            : ℤ)) (d * N) t =
        MvPolynomial.aeval (fun i => DirectSum.of (fun n : ℕ =>
          𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO))
            ⟶ tensorPower O hO L (n : ℤ)) N (x i)) P := by
  let i₀ := homGradedCommRing O hO L hβ
  let _ : DirectSum.GCommRing
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ (tensorPowerSystem O hO L).obj n) := i₀
  exact (tensorPowerSystem O hO L).exists_aeval_eq_of_isHomogeneous x hP

/-- The same as `Stacks.SheafOfModules.Invertible.exists_aeval_eq_of_isHomogeneous`, with the
global sections spelled as `PresheafOfModules.sections` rather than as morphisms out of the
tensor unit; the two are identified by `SheafOfModules.unitHomEquiv`, which is
`Stacks.SheafOfModules.Invertible.sectionToHom`. -/
theorem exists_sections_aeval_eq_of_isHomogeneous
    (hβ : ∀ a b : ℕ, (β_ (tensorPower O hO L (a : ℤ)) (tensorPower O hO L (b : ℤ))).hom
        ≫ (tensorPowerMulIso O hO L b a).hom
      = (tensorPowerMulIso O hO L a b).hom
        ≫ eqToHom (congrArg (fun k : ℕ => tensorPower O hO L (k : ℤ)) (Nat.add_comm a b)))
    {σ : Type*} {N : ℕ} (s : σ → (tensorPower O hO L (N : ℤ)).sections)
    {P : MvPolynomial σ ℤ} {d : ℕ} (hP : P.IsHomogeneous d) :
    letI := homGradedCommRing O hO L hβ
    ∃ t : (tensorPower O hO L ((d * N : ℕ) : ℤ)).sections,
      DirectSum.of (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ⟶ tensorPower O hO L (n
            : ℤ)) (d * N)
            (sectionToHom O hO L t) =
        MvPolynomial.aeval (fun i => DirectSum.of (fun n : ℕ =>
          𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO))
            ⟶ tensorPower O hO L (n : ℤ)) N (sectionToHom O hO L (s i))) P := by
  obtain ⟨t, ht⟩ := exists_aeval_eq_of_isHomogeneous O hO L hβ
    (fun i => sectionToHom O hO L (s i)) hP
  exact ⟨homToSection O hO L t, by rwa [sectionToHom_homToSection]⟩

end Stacks.SheafOfModules.Invertible

end
