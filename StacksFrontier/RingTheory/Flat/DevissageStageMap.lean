module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support
public import StacksFrontier.RingTheory.Flat.DevissageLength
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The map of a dévissage stage, and the drop of its cokernel

A stage of a complete dévissage of `N/S/R` over a prime `r` of `R`
(`Module.DevissageStage`, Stacks 05HX) carries a map `α : Bᵐ → M` from a finite free module over
the smooth lower algebra `B` which is required to become an isomorphism after passing to the
residue field of the prime `rB`. Stacks 05HF asserts that such an `α` always exists, and that its
cokernel then vanishes at `rB`, which is what makes the support of the cokernel on the fibre
strictly smaller than the support of `N` on the fibre and so lets the construction of Stacks 05HR
and 05I1 recurse.

Both assertions are pure commutative algebra, and that is how they are proved here: for a finite
module `N` over any commutative ring `B` and any prime `p` of `B` there is an `m` and a map
`α : (Fin m →₀ B) →ₗ[B] N` with `α ⊗ κ(p)` bijective, and for any such `α` the cokernel
`N ⧸ range α` has vanishing localization at `p`.

## Main results

* `Module.exists_tmul_one_eq_basis`: a finite module over a commutative ring has a finite family
  of elements whose images in the fibre at a prime form a basis of that fibre.
* `Module.bijective_baseChange_linearCombination`: the map out of a finite free module determined
  by such a family is an isomorphism over the residue field of the prime.
* `Module.subsingleton_localizedModule_quotient_range`: **Nakayama for the cokernel.** If
  `α ⊗ κ(p)` is surjective then `N ⧸ range α` localizes to zero at `p`; equivalently
  `Module.notMem_support_quotient_range`, the prime is not in the support of the cokernel.
* `Module.exists_bijective_baseChange_residueField`: **the algebraic content of Stacks 05HF.**
  Both conclusions together, for an arbitrary finite module and prime.
* `Module.DevissageStage.exists_multiplicity_alpha`: the same statement at the stage prime `rB` of
  a dévissage stage, which is the form the recursion of Stacks 05HR consumes: the rank and the map
  of a stage can be chosen so that the cokernel of the map vanishes at the stage prime.

## Implementation notes

The family of elements is extracted from the spanning family `N → κ(p) ⊗[B] N`, `x ↦ 1 ⊗ x`, by
`exists_linearIndependent'`: a linearly independent subfamily of a spanning family of a vector
space spans, hence is a basis, and it is finite because the fibre of a finite module is a
finite-dimensional vector space. Indexing it by `Fin m` rather than by the abstract index type
`exists_linearIndependent'` returns is what makes the resulting map a map out of
`Fin m →₀ B`, as `Module.CompleteDevissage` demands.

That the map is an isomorphism over `κ(p)` is not checked elementwise: the base change of
`Finsupp.basisSingleOne` is a basis of `κ(p) ⊗[B] (Fin m →₀ B)` which the base change of the map
carries to the chosen basis of the fibre, so the base change *is* the isomorphism of bases, and
bijectivity is read off that.

The vanishing of the cokernel at `p` is Nakayama's lemma, but it is not applied directly: the
tensor product `κ(p) ⊗[B] (N ⧸ range α)` vanishes by right exactness, and
`Module.mem_support_iff_nontrivial_residueField_tensorProduct` converts vanishing of that fibre
into vanishing of the localization for a finite module — that lemma is where Mathlib already
performs the Nakayama step.

This file does **not** carry a `@[stacks 05HF]` attribute. The source's 05HF is stated for a one
step dévissage of a sheaf `F/X/S` over a point `s`, and its conclusion is the strict inequality of
the dimensions of the supports of the cokernel and of `F` on the fibre over `s`. Neither the one
step dévissage of a sheaf nor that dimension comparison is formalized here: what is proved is the
algebra that the source's proof consists of, namely the construction of `α` by lifting a basis of
the fibre and the Nakayama step which removes the stage prime from the support of the cokernel.
The dimension inequality follows from the latter only together with geometric irreducibility of
the fibre of `Spec B → Spec R`, which makes `rB` the generic point of that fibre, and that step is
not in this file.

## References

* [Stacks Project, Tag 05HF](https://stacks.math.columbia.edu/tag/05HF)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module

/-- **A finite module has a finite family of elements whose fibre at a prime is a basis.**

The images `1 ⊗ x i` of the family in `κ(p) ⊗[B] N` form a basis of that fibre over `κ(p)`. This
is the choice of `x₁, …, xᵣ ∈ N` lifting a basis of `N ⊗_B κ(p)` in the proof of Stacks 05HF. -/
theorem exists_tmul_one_eq_basis (B : Type u) [CommRing B] (N : Type v) [AddCommGroup N]
    [Module B N] [Module.Finite B N] (p : Ideal B) [p.IsPrime] :
    ∃ (m : ℕ) (x : Fin m → N) (b : Module.Basis (Fin m) p.ResidueField
      (p.ResidueField ⊗[B] N)), ∀ i, (1 : p.ResidueField) ⊗ₜ x i = b i := by
  set K := p.ResidueField
  have hspan : Submodule.span K (Set.range fun y : N => (1 : K) ⊗ₜ[B] y) = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun y => ?_
    induction y with
    | tmul c z =>
        rw [show c ⊗ₜ[B] z = c • ((1 : K) ⊗ₜ[B] z) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, rfl⟩)
    | add z w hz hw => exact add_mem hz hw
  obtain ⟨ι, a, -, hsp, hli⟩ := exists_linearIndependent' K fun y : N => (1 : K) ⊗ₜ[B] y
  have hb : ⊤ ≤ Submodule.span K (Set.range ((fun y : N => (1 : K) ⊗ₜ[B] y) ∘ a)) := by
    rw [hsp, hspan]
  let b : Module.Basis ι K (K ⊗[B] N) := Module.Basis.mk hli hb
  have : Finite ι := Module.Finite.finite_basis b
  let e : ι ≃ Fin (Nat.card ι) := Finite.equivFin ι
  exact ⟨Nat.card ι, a ∘ e.symm, b.reindex e, fun i => by simp [b, e]⟩

/-- **A family of elements whose fibre is a basis determines a fibrewise isomorphism.**

The `B`-linear map out of `Fin m →₀ B` sending the `i`-th generator to `x i` becomes bijective
after base change to the residue field of `p`, because it carries the base change of
`Finsupp.basisSingleOne` to the given basis of the fibre. -/
theorem bijective_baseChange_linearCombination {B : Type u} [CommRing B] {N : Type v}
    [AddCommGroup N] [Module B N] {p : Ideal B} [p.IsPrime] {m : ℕ} {x : Fin m → N}
    (b : Module.Basis (Fin m) p.ResidueField (p.ResidueField ⊗[B] N))
    (hx : ∀ i, (1 : p.ResidueField) ⊗ₜ x i = b i) :
    Function.Bijective
      (LinearMap.baseChange p.ResidueField (Finsupp.linearCombination B x)) := by
  set K := p.ResidueField
  let sb : Module.Basis (Fin m) K (K ⊗[B] (Fin m →₀ B)) :=
    (Finsupp.basisSingleOne (R := B) (ι := Fin m)).baseChange K
  have key : LinearMap.baseChange K (Finsupp.linearCombination B x) =
      (sb.equiv b (Equiv.refl _)).toLinearMap := by
    refine sb.ext fun i => ?_
    simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, ← hx]
    simp [sb]
  exact key ▸ (sb.equiv b (Equiv.refl _)).bijective

/-- **Nakayama for the cokernel of a fibrewise surjective map.**

If the base change of `α` to the residue field of a prime `p` is surjective, then the cokernel of
`α` has vanishing localization at `p`. This is the step "`N' ⊗ κ(p) = 0`, hence `N'_p = 0` by
Nakayama's lemma" in the proof of Stacks 05HF. -/
@[sga "3 V 4.1.3" "more general"]
theorem subsingleton_localizedModule_quotient_range {B : Type u} [CommRing B] {N : Type v}
    [AddCommGroup N] [Module B N] [Module.Finite B N] {p : Ideal B} [p.IsPrime] {m : ℕ}
    {α : (Fin m →₀ B) →ₗ[B] N}
    (hsurj : Function.Surjective (LinearMap.baseChange p.ResidueField α)) :
    Subsingleton (LocalizedModule p.primeCompl (N ⧸ LinearMap.range α)) := by
  set K := p.ResidueField
  have hzero : Subsingleton (K ⊗[B] (N ⧸ LinearMap.range α)) := by
    refine (subsingleton_iff_forall_eq 0).2 fun y => ?_
    obtain ⟨z, rfl⟩ := LinearMap.baseChange_surjective K (Submodule.mkQ_surjective _) y
    obtain ⟨w, rfl⟩ := hsurj z
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.range_mkQ_comp,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum B) ∉
      Module.support B (N ⧸ LinearMap.range α) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.2 hzero
  exact Module.notMem_support_iff.1 hnot

/-- **The prime is not in the support of the cokernel.** The form of
`Module.subsingleton_localizedModule_quotient_range` which the dimension comparison of
Stacks 05HF consumes: the support of the cokernel misses `p`, so when `p` is the generic point of
an irreducible fibre the support of the cokernel on that fibre is strictly smaller. -/
theorem notMem_support_quotient_range {B : Type u} [CommRing B] {N : Type v}
    [AddCommGroup N] [Module B N] [Module.Finite B N] {p : Ideal B} [hp : p.IsPrime] {m : ℕ}
    {α : (Fin m →₀ B) →ₗ[B] N}
    (hsurj : Function.Surjective (LinearMap.baseChange p.ResidueField α)) :
    (⟨p, hp⟩ : PrimeSpectrum B) ∉ Module.support B (N ⧸ LinearMap.range α) :=
  Module.notMem_support_iff.2 (subsingleton_localizedModule_quotient_range hsurj)

/-- **The shrinking which makes the cokernel of the stage map vanish identically.**

The cokernel of a fibrewise surjective map vanishes not only at `p` but on a standard open
neighbourhood of `p`: there is an element `f` outside `p` such that the cokernel is already zero
over `B[1/f]`. This is the algebraic content of the step in the proof of Stacks 05HR in which the
lower algebra of a stage is shrunk by Stacks 05HA (05HC) so that the cokernel becomes zero and the
dévissage terminates. It is `LocalizedModule.exists_subsingleton_away` applied to the cokernel,
which is a finite module over `B`. -/
theorem exists_away_subsingleton_quotient_range {B : Type u} [CommRing B] {N : Type v}
    [AddCommGroup N] [Module B N] [Module.Finite B N] {p : Ideal B} [p.IsPrime] {m : ℕ}
    {α : (Fin m →₀ B) →ₗ[B] N}
    (hsurj : Function.Surjective (LinearMap.baseChange p.ResidueField α)) :
    ∃ f ∉ p, Subsingleton (LocalizedModule.Away f (N ⧸ LinearMap.range α)) := by
  have := subsingleton_localizedModule_quotient_range hsurj
  exact LocalizedModule.exists_subsingleton_away p

/-- **The algebraic content of Stacks 05HF.**

Let `N` be a finite module over a commutative ring `B` and let `p` be a prime of `B`. Then there
is a map `α` from a finite free `B`-module to `N` which is an isomorphism over the residue field
of `p`, and the cokernel of any such map vanishes at `p`.

In the source this is applied with `B` the smooth lower algebra of a one step dévissage, `N` the
pushforward of the dévissaged sheaf to `Spec B` and `p` the generic point of the fibre of
`Spec B → Spec R`; the conclusion there is that the support of the cokernel on the fibre has
strictly smaller dimension, which is this statement together with irreducibility of that
fibre. -/
theorem exists_bijective_baseChange_residueField (B : Type u) [CommRing B] (N : Type v)
    [AddCommGroup N] [Module B N] [Module.Finite B N] (p : Ideal B) [p.IsPrime] :
    ∃ (m : ℕ) (α : (Fin m →₀ B) →ₗ[B] N),
      Function.Bijective (LinearMap.baseChange p.ResidueField α) ∧
        Subsingleton (LocalizedModule p.primeCompl (N ⧸ LinearMap.range α)) := by
  obtain ⟨m, x, b, hx⟩ := exists_tmul_one_eq_basis B N p
  have hbij := bijective_baseChange_linearCombination b hx
  exact ⟨m, Finsupp.linearCombination B x, hbij,
    subsingleton_localizedModule_quotient_range hbij.surjective⟩

namespace DevissageStage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

/-- **Stacks 05HF at the stage prime of a dévissage stage.**

The rank and the map of a stage of a complete dévissage can be chosen so that, in addition to the
fibre condition the stage already requires, the cokernel of the map vanishes at the stage prime
`rB`. This is the form the recursion of Stacks 05HR consumes: the next stage of the dévissage is
built from that cokernel, and the vanishing at `rB` is what makes the recursion descend.

The map produced here has nothing to do with the one the given stage carries; the stage is used
only for its algebras, its module and the primality of `rB`. -/
theorem exists_multiplicity_alpha (E : DevissageStage R S N r) :
    ∃ (m : ℕ) (α : (Fin m →₀ E.B) →ₗ[E.B] E.M),
      Function.Bijective
          (LinearMap.baseChange (Ideal.map (algebraMap R E.B) r).ResidueField α) ∧
        Subsingleton (LocalizedModule (Ideal.map (algebraMap R E.B) r).primeCompl
          (E.M ⧸ LinearMap.range α)) :=
  exists_bijective_baseChange_residueField E.B E.M (Ideal.map (algebraMap R E.B) r)

end DevissageStage

end Module

end
