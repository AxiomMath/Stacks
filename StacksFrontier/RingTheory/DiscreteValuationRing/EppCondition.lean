module

public import StacksFrontier.FieldTheory.PerfectCore
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution

/-!
# Epp's residue-field condition

Epp's theorem on elimination of wild ramification (Stacks Tag 09F9) carries one hypothesis
beyond having an extension of discrete valuation rings `A → B`: when the residue characteristic
is `p > 0`, every element of

$$\bigcap_{n \ge 1} \kappa_B^{p^n}$$

must be separable algebraic over `κ_A`. In the language of `perfectCore` this says every element
of the perfect core of `κ_B` is separable over `κ_A`, and this file gives that condition a name,
`Stacks.EppTheorem.EppCondition`, together with the lemmas that move it along the two kinds of
enlargement the proof of 09F9 performs.

Naming the condition is not cosmetic. Written inline it is a
four-line `∀ x, (∀ n, 1 ≤ n → ∃ y, y ^ p ^ n = x) → IsSeparable _ x` hypothesis, which each
declaration using it would have to unfold by hand against
`mem_perfectCore_iff`. `eppCondition_iff_forall_one_le` does that unfolding once.

## Main definitions

* `Stacks.EppTheorem.EppCondition A B p`: Epp's residue-field condition for `A → B`.

## Main results

* `Stacks.EppTheorem.eppCondition_iff_forall_one_le`: the condition, spelled out in the `⋂_{n ≥ 1}`
  form in which Tag 09F9 states it.
* `Stacks.EppTheorem.EppCondition.of_residueField_surjective`: the condition passes along a square
  whose upper residue-field map is surjective. This covers passage to the completion and to a
  `ULift`, the two places 09F9's proof changes the rings without changing the residue fields.
* `Stacks.EppTheorem.EppCondition.of_isSepClosure`: the condition passes *upward* along a square
  whose upper residue fields are separable closures of the lower ones — the enlargement Tag 09ET
  produces.
* `Stacks.EppTheorem.perfectCore_residueField_le_of_isSepClosure`: the same enlargement in the
  sharper form Tag 09F9's proof actually records, namely `κ_{A'} ⊇ ⋂ κ_{B'}^{p^n}`.
* `Stacks.EppTheorem.isAlgClosed_perfectCore_residueField`: after that enlargement the perfect core
  upstairs is algebraically closed.

Taken together the last three are the sound half of 09F9's separable-closure reduction. The
unsound half is the *descent* of a weak solution back along the same square, which is clause (3)
of Tag 09ET, and that clause is false: there is an extension of discrete valuation rings with no
finite weak solution which acquires one upstairs. Nothing in this file depends on that clause.

## References

* [Epp, *Elimination of wild ramification*][epp1973]
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09ET](https://stacks.math.columbia.edu/tag/09ET)
-/

@[expose] public section

open IsLocalRing

namespace Stacks.EppTheorem

variable (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] (p : ℕ) [ExpChar (ResidueField B) p]

/-- **Epp's residue-field condition** for a local homomorphism `A → B`: every element of the
perfect core of the residue field of `B` is separable algebraic over the residue field of `A`.

This is the hypothesis of Tag 09F9 in residue characteristic `p > 0`. In residue characteristic
zero, taking `p = 1`, the perfect core is everything and the condition is the assertion that
`κ_B / κ_A` is separable algebraic; 09F9 does not impose it there, and its proof in that case
goes through Abhyankar's lemma instead. -/
def EppCondition : Prop :=
  ∀ x : ResidueField B, x ∈ perfectCore (ResidueField B) p → IsSeparable (ResidueField A) x

variable {A B p}

/-- Epp's condition as Tag 09F9 states it, in terms of `⋂_{n ≥ 1} κ_B^{p^n}` unfolded to
iterated `p`-power roots. -/
theorem eppCondition_iff_forall_one_le :
    EppCondition A B p ↔ ∀ x : ResidueField B,
      (∀ n : ℕ, 1 ≤ n → ∃ y : ResidueField B, y ^ p ^ n = x) →
        IsSeparable (ResidueField A) x :=
  ⟨fun h x hx => h x (mem_perfectCore_iff_forall_one_le.mpr hx),
   fun h x hx => h x (mem_perfectCore_iff_forall_one_le.mp hx)⟩

end Stacks.EppTheorem

namespace Stacks.EppTheorem

section Surjective

variable {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [IsLocalRing A] [IsLocalRing A'] [IsLocalRing B] [IsLocalRing B']
  [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B] [Algebra A B']
  [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap B B')]
  [IsLocalHom (algebraMap A' B')] [IsLocalHom (algebraMap A B)]
  [IsLocalHom (algebraMap A B')]
  [IsScalarTower A A' B'] [IsScalarTower A B B']
  {p : ℕ} [ExpChar (ResidueField B) p] [ExpChar (ResidueField B') p]

/-- Epp's condition passes along a square of local rings whose upper residue-field map is
surjective, hence an isomorphism.

The proof of Tag 09F9 uses this twice: to replace `A → B` by the extension of their completions,
whose residue fields are unchanged, and to move the whole square into a single universe by
`ULift`. -/
theorem EppCondition.of_residueField_surjective
    (hsurj : Function.Surjective (algebraMap (ResidueField B) (ResidueField B')))
    (h : EppCondition A B p) : EppCondition A' B' p :=
  fun _ hx => isSeparable_of_mem_perfectCore_of_surjective hsurj h hx

end Surjective

section IsSepClosure

variable {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [IsLocalRing A] [IsLocalRing A'] [IsLocalRing B] [IsLocalRing B']
  [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B] [Algebra A B']
  [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap B B')]
  [IsLocalHom (algebraMap A' B')] [IsLocalHom (algebraMap A B)]
  [IsLocalHom (algebraMap A B')]
  [IsScalarTower A A' B'] [IsScalarTower A B B']
  [IsSepClosure (ResidueField A) (ResidueField A')]
  [IsSepClosure (ResidueField B) (ResidueField B')]
  {p : ℕ} [ExpChar (ResidueField B) p] [ExpChar (ResidueField B') p]

/-- **Epp's condition transfers upward along a separable-closure enlargement.**

Given a square of local rings whose upper residue fields are separable algebraic closures of the
lower ones, Epp's condition for `A → B` implies Epp's condition for `A' → B'`.

This is the sound half of the reduction to separably closed residue fields in the proof of Tag
09F9. It rests on `minpoly_coeff_mem_perfectCore`: an element of the perfect core upstairs is
separable over `κ_B`, and the coefficients of its minimal polynomial lie in the perfect core of
`κ_B`, where the hypothesis applies to them; so the element is separable over `κ_A` and therefore
lies in the separably closed field `κ_{A'}`.

The *downward* transfer of a weak solution along the same square is clause (3) of Tag 09ET and is
false. This lemma is not affected — it is an
ascent, and the counterexample to that clause violates Epp's condition by design. -/
theorem EppCondition.of_isSepClosure (h : EppCondition A B p) : EppCondition A' B' p := by
  have : Algebra.IsSeparable (ResidueField B) (ResidueField B') := IsSepClosure.separable
  have : IsSepClosed (ResidueField A') := IsSepClosure.sep_closed (ResidueField A)
  intro x hx
  obtain ⟨a, rfl⟩ := perfectCore_mem_range_of_separable_square (k := ResidueField A)
    (l := ResidueField B) (K := ResidueField A') (L := ResidueField B') (p := p) h hx
  exact isSeparable_algebraMap a

/-- The sharper form of `EppCondition.of_isSepClosure` that Tag 09F9's proof records: after the
enlargement, the perfect core upstairs is *contained in* the base residue field, rather than
merely separable over it.

The containment is what the subsequent argument needs, since it goes on to choose a coefficient
ring with residue field the perfect core and a map into the base. -/
theorem perfectCore_residueField_le_of_isSepClosure (h : EppCondition A B p) :
    perfectCore (ResidueField B') p ≤
      (algebraMap (ResidueField A') (ResidueField B')).fieldRange := by
  have : IsSepClosed (ResidueField A') := IsSepClosure.sep_closed (ResidueField A)
  exact perfectCore_le_fieldRange (EppCondition.of_isSepClosure (A := A) (B := B) h)

/-- After the separable-closure enlargement the perfect core of the residue field upstairs is
algebraically closed.

This, and not the condition itself, is what the algebraically-closed-residue-field case of Epp's
theorem (Tag 09F8) consumes: 09F8 requires its base residue field to be algebraically closed and
equal to the perfect core upstairs. -/
theorem isAlgClosed_perfectCore_residueField (B B' : Type*) [CommRing B] [CommRing B']
    [IsLocalRing B] [IsLocalRing B'] [Algebra B B'] [IsLocalHom (algebraMap B B')]
    [IsSepClosure (ResidueField B) (ResidueField B')] (p : ℕ) [ExpChar (ResidueField B') p] :
    IsAlgClosed (perfectCore (ResidueField B') p) := by
  have : IsSepClosed (ResidueField B') := IsSepClosure.sep_closed (ResidueField B)
  exact perfectCore.isAlgClosed

end IsSepClosure

end Stacks.EppTheorem

namespace IsDiscreteValuationRing

/-- Extensions of discrete valuation rings compose.

Deliberately carries no `@[stacks 09E4]` attribute. Tag 09E4 is a *definition* tag, so its
covering set is the definitions, which
`StacksFrontier/RingTheory/DiscreteValuationRing/Solution.lean` already registers (`IsExtension`,
`ramificationIndex`, `IsWeaklyUnramified`, `residueDegree`). Transitivity is a consequence of
those definitions rather than part of them, and tagging it here would make this file a second
provider for a tag that already has one. -/
theorem IsExtension.trans (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [IsDomain A]
    [IsDomain B] [IsDomain C] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsExtension A B] [IsExtension B C] : IsExtension A C where
  toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective A C).mpr <| by
    rw [IsScalarTower.algebraMap_eq A B C]
    exact (FaithfulSMul.algebraMap_injective B C).comp (FaithfulSMul.algebraMap_injective A B)
  toIsLocalHom := by
    rw [IsScalarTower.algebraMap_eq A B C]
    infer_instance

end IsDiscreteValuationRing
