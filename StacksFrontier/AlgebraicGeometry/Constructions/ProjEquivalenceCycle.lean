module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleMorphismConverse

/-!
# The cycle of Tag 01NB closes for a triple over a scheme

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)` and `Y` a scheme. A triple `(d, L, ψ)`
over `Y` classifies a morphism `Y ⟶ X` by [Stacks, Tag 01N8]. For two triples `(d, L, ψ)` and
`(d', L', ψ')` over `Y`, [Stacks, Tag 01NB] asserts the equivalence of

1. at `n = lcm(d, d')`, written `n = ad = a'd'`, there is an isomorphism
   `β : L^{⊗ a} ≅ (L')^{⊗ a'}` with `β ∘ ψ|_{A^{(n)}} = ψ'|_{A^{(n)}}`;
2. the same at `n = dd'`, that is with `β : L^{⊗ d'} ≅ (L')^{⊗ d}` — the two triples are
   *equivalent*;
3. the same for *some* positive `n = ad = a'd'`;
4. the two classified morphisms `Y ⟶ X` are equal.

This file proves the equivalence of the four conditions for triples over a scheme,
`Stacks.AlgebraicGeometry.ProjTripleClassifying.Triple`.

## Main results

* `Stacks.AlgebraicGeometry.ProjEquivalenceCycle.agree_of_sameMorphism_of_mul_eq`: two triples over
  a scheme classifying the same morphism satisfy the agreement condition at **every** pair of
  positive weights `(a, a')` with `ad = a'd'`.
* `Stacks.AlgebraicGeometry.ProjEquivalenceCycle.agree_of_sameMorphism`: clause (4) implies
  clause (2).
* `Stacks.AlgebraicGeometry.ProjEquivalenceCycle.agreeAtSome_of_sameMorphism`: clause (4) implies
  clause (3).
* `Stacks.AlgebraicGeometry.ProjEquivalenceCycle.agree_of_agreeAtLcm`: clause (1) implies
  clause (2).
* `Stacks.AlgebraicGeometry.ProjEquivalenceCycle.agreeAtSome_of_agreeAtLcm`: clause (1) implies
  clause (3).
* `Stacks.AlgebraicGeometry.ProjEquivalenceCycle.tfae_triple`: the four conditions of [Stacks,
  Tag 01NB] are equivalent, as a single `List.TFAE`.

## References

* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidalCategory
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTripleClassifying
open Stacks.AlgebraicGeometry.ProjTripleMorphismConverse
  (agree_of_sameMorphism_of_deg_eq)
open Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism
  (classifyingMorphism_veroneseRestrict sameMorphism_of_agreeAtLcm)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjEquivalenceCycle

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {Y : Scheme.{u}}

/-- **The agreement condition of [Stacks, Tag 01NB] at a pair of weights `(a, a')`**: an
isomorphism `β : L^{⊗ a} ≅ (L')^{⊗ a'}` carrying the restriction of `ψ` to the Veronese subring
`A^{(ad)}` to the restriction of `ψ'` to `A^{(a'd')}`, degreewise, with the two readings of one
homogeneous element matched by the equality of their underlying elements of `A`. -/
def AgreeAt (t t' : Triple 𝒜 Y) (a a' : ℕ) : Prop :=
  ∃ β : natTensorPow t.module a ≅ natTensorPow t'.module a',
    ∀ (m : ℕ) (x : 𝒜 (m * (a * t.deg))) (x' : 𝒜 (m * (a' * t'.deg))), (x : A) = (x' : A) →
      (natTensorPowCongr β m).hom.app ⊤
          ((ProjVeroneseRestrict.veroneseRestrict 𝒜 t.psi a).toFun m x)
        = (ProjVeroneseRestrict.veroneseRestrict 𝒜 t'.psi a').toFun m x'

/-- **Clause (4) of [Stacks, Tag 01NB] implies the agreement condition at every pair of weights
`(a, a')` with `ad = a'd'`.** The case `(a, a') = (lcm(d, d')/d, lcm(d, d')/d')` is clause (1),
and the case `(a, a') = (d', d)` is clause (2). -/
theorem agree_of_sameMorphism_of_mul_eq (t t' : Triple 𝒜 Y) {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a')
    (hn : a * t.deg = a' * t'.deg) (h : SameMorphism 𝒜 t t') :
    AgreeAt t t' a a' := by
  have hsame : SameMorphism 𝒜 (t.veroneseRestrict a ha) (t'.veroneseRestrict a' ha') :=
    ((classifyingMorphism_veroneseRestrict 𝒜 t a ha).trans h).trans
      (classifyingMorphism_veroneseRestrict 𝒜 t' a' ha').symm
  exact agree_of_sameMorphism_of_deg_eq 𝒜 _ _ hn hsame

/-- **Clause (4) of [Stacks, Tag 01NB] implies clause (2).** Two triples over `Y` classifying the
same morphism `Y ⟶ Proj(A)` are *equivalent*: there is an isomorphism
`β : L^{⊗ d'} ≅ (L')^{⊗ d}` carrying `ψ|_{A^{(dd')}}` to `ψ'|_{A^{(dd')}}`. -/
theorem agree_of_sameMorphism (t t' : Triple 𝒜 Y) (h : SameMorphism 𝒜 t t') :
    AgreeAt t t' t'.deg t.deg :=
  agree_of_sameMorphism_of_mul_eq t t' t'.deg_pos t.deg_pos (mul_comm t'.deg t.deg) h

/-- The agreement condition at the weights `(d', d)` gives it at some pair of positive weights. -/
private theorem exists_agree_of_agree_swap (t t' : Triple 𝒜 Y) (h : AgreeAt t t' t'.deg t.deg) :
    ∃ a a' : ℕ, 0 < a ∧ 0 < a' ∧ a * t.deg = a' * t'.deg ∧ AgreeAt t t' a a' :=
  ⟨t'.deg, t.deg, t'.deg_pos, t.deg_pos, mul_comm t'.deg t.deg, h⟩

/-- **Clause (4) of [Stacks, Tag 01NB] implies clause (3).** Two triples over `Y` classifying the
same morphism satisfy the agreement condition at some pair of positive weights `(a, a')` with
`ad = a'd'`. -/
theorem agreeAtSome_of_sameMorphism (t t' : Triple 𝒜 Y) (h : SameMorphism 𝒜 t t') :
    ∃ a a' : ℕ, 0 < a ∧ 0 < a' ∧ a * t.deg = a' * t'.deg ∧ AgreeAt t t' a a' :=
  exists_agree_of_agree_swap t t' (agree_of_sameMorphism t t' h)

/-- **Clause (1) of [Stacks, Tag 01NB] implies clause (2), for a triple over a scheme.** The
agreement condition at `n = lcm(d, d')` gives the agreement condition at `n = dd'`. -/
theorem agree_of_agreeAtLcm (t t' : Triple 𝒜 Y)
    (h : AgreeAt t t' (Nat.lcm t.deg t'.deg / t.deg) (Nat.lcm t.deg t'.deg / t'.deg)) :
    AgreeAt t t' t'.deg t.deg :=
  agree_of_sameMorphism t t' (sameMorphism_of_agreeAtLcm 𝒜 t t' h.choose h.choose_spec)

/-- **Clause (1) of [Stacks, Tag 01NB] implies clause (3), for a triple over a scheme.** The
agreement condition at `n = lcm(d, d')` gives the agreement condition at some pair of positive
weights `(a, a')` with `ad = a'd'`. -/
theorem agreeAtSome_of_agreeAtLcm (t t' : Triple 𝒜 Y)
    (h : AgreeAt t t' (Nat.lcm t.deg t'.deg / t.deg) (Nat.lcm t.deg t'.deg / t'.deg)) :
    ∃ a a' : ℕ, 0 < a ∧ 0 < a' ∧ a * t.deg = a' * t'.deg ∧ AgreeAt t t' a a' :=
  exists_agree_of_agree_swap t t' (agree_of_agreeAtLcm t t' h)

/-- For two triples `t`, `t'` over a scheme the following are equivalent: the agreement condition
at the weights `(lcm(d, d') / d, lcm(d, d') / d')`; the agreement condition at the weights
`(d', d)`; the agreement condition at some positive weights `(a, a')` with `a * d = a' * d'`; the
two triples classify the same morphism. Here `d = t.deg` and `d' = t'.deg`. -/
@[stacks 01NB "all four clauses of the tag are equivalent, for two triples over a scheme, as a
single statement; the list entries are clauses (1), (2), (3), (4) in that order"]
theorem tfae_triple (t t' : Triple 𝒜 Y) :
    List.TFAE
      [AgreeAt t t' (Nat.lcm t.deg t'.deg / t.deg) (Nat.lcm t.deg t'.deg / t'.deg),
        AgreeAt t t' t'.deg t.deg,
        ∃ a a' : ℕ, 0 < a ∧ 0 < a' ∧ a * t.deg = a' * t'.deg ∧ AgreeAt t t' a a',
        SameMorphism 𝒜 t t'] := by
  tfae_have 1 → 2 := agree_of_agreeAtLcm t t'
  tfae_have 2 → 3 := exists_agree_of_agree_swap t t'
  tfae_have 3 → 4 := fun ⟨a, a', ha, ha', hn, β, hβ⟩ =>
    ProjTripleVeroneseMorphism.sameMorphism_of_agreeAtSome 𝒜 t t' ha ha' hn β hβ
  tfae_have 4 → 1 := fun h =>
    ProjTripleMorphismConverse.agreeAtLcm_of_sameMorphism 𝒜 t t' h
  tfae_finish

end Stacks.AlgebraicGeometry.ProjEquivalenceCycle

end
