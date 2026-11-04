module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Dualizing
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs

/-!
# Dualizing complexes over algebras essentially of finite type

An algebra essentially of finite type over a Noetherian ring that has a dualizing complex again
has a dualizing complex.  Writing such an algebra as a localization of a finite type algebra, the
finite type step is [stacks 0BZL] and the localization step is [stacks 0A7G].

## Main results

* `Dualizing.isNoetherianRing_of_isEssentiallyOfFiniteType` — a ring essentially of finite type
  over a Noetherian ring is Noetherian.
* `Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType` — [stacks 0A7K].

## Implementation notes

Noetherianity of the target ring is part of the existential conclusion rather than a hypothesis:
`Dualizing.IsDualizingComplex` is stated only over a Noetherian ring, so the conclusion cannot be
written down without it, and here it is automatic.

## References

* [Stacks Project, Tag 0A7K](https://stacks.math.columbia.edu/tag/0A7K)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- An algebra essentially of finite type is a localization of a finite type algebra. -/
private theorem exists_finiteType_localization {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (hB : IsEssentiallyOfFiniteType A B (algebraMap A B)) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T) (_ : Algebra T B) (M : Submonoid T),
      Algebra.FiniteType A T ∧ IsLocalization M B := by
  obtain ⟨T, hT, hAT, hft, M, hTB, -, hloc⟩ := hB
  exact ⟨T, hT, hAT, hTB, M, hft, hloc⟩

/-- A ring essentially of finite type over a Noetherian ring is Noetherian: it is a localization
of a finite type algebra, and each of those two constructions preserves Noetherianity. -/
theorem isNoetherianRing_of_isEssentiallyOfFiniteType {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [Algebra A B]
    (hB : IsEssentiallyOfFiniteType A B (algebraMap A B)) : IsNoetherianRing B := by
  obtain ⟨T, _, _, _, M, _, _⟩ := exists_finiteType_localization hB
  exact IsLocalization.isNoetherianRing M B (Algebra.FiniteType.isNoetherianRing A T)

/-- **Stacks Project, Tag 0A7K.** If a Noetherian ring `A` has a dualizing complex, then every
`A`-algebra essentially of finite type over `A` has a dualizing complex. -/
@[stacks 0A7K]
theorem exists_isDualizingComplex_of_isEssentiallyOfFiniteType {A B : Type u} [CommRing A]
    [CommRing B] [IsNoetherianRing A] [Algebra A B]
    (hB : IsEssentiallyOfFiniteType A B (algebraMap A B))
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K) :
    ∃ (hB' : IsNoetherianRing B) (L : DerivedCategory (ModuleCat.{u} B)),
      @IsDualizingComplex B _ hB' _ L := by
  have hBn := isNoetherianRing_of_isEssentiallyOfFiniteType hB
  obtain ⟨T, _, _, _, M, _, _⟩ := exists_finiteType_localization hB
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing A T
  obtain ⟨n, g, hg⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := T)).mp inferInstance
  let p : PolynomialPresentation (algebraMap A T) :=
    { variableCount := n
      toRingHom := g.toRingHom
      commutes := by ext r; exact g.commutes r
      surjective := hg }
  refine ⟨hBn, _,
    isDualizingComplex_localization M (p.upperShriekFunctor.{u, u}.obj K) ?_⟩
  exact p.upperShriekFunctor_isDualizingComplex K hK

end Dualizing

end
