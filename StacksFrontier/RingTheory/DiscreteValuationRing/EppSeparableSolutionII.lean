module

public import StacksFrontier.RingTheory.DiscreteValuationRing.SeparableSolution
public import StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationTheorem
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.RingTheory.Nagata.Universes

/-!
# Separable solutions for extensions essentially of finite type

Let `A → B` be an extension of discrete valuation rings with fraction fields `K ⊂ L` such that `B`
is essentially of finite type over `A`, one of `A` and `B` is a Nagata ring, and `L / K` is
separable. Then there exists a separable solution for `A → B`. Along the way, a ring essentially
of finite type over a Nagata ring is a Nagata ring.

## Main results

* `IsNagataRing.of_isEssentiallyOfFiniteType`: if `A` is Nagata and `B` is essentially of finite
  type over `A`, then `B` is Nagata.
* `IsDiscreteValuationRing.exists_isSeparableSolution_of_isEssentiallyOfFiniteType`: for `A` and
  `B` in a common universe, a solution for `A → B` gives a separable solution.
* `IsDiscreteValuationRing.exists_isSeparableSolution_of_isNagataRing_of_eppTheorem`: a separable
  solution exists, assuming Epp's theorem at the two universe levels at which it is used.
* `IsDiscreteValuationRing.exists_isSeparableSolution_of_essFiniteType_of_eppTheorem_monomorphic`:
  the same, assuming Epp's theorem at two single universes.
* `IsDiscreteValuationRing.exists_isSeparableSolution_of_essFiniteType`: a separable solution
  exists.

## References

* [The Stacks Project, Tag 0BRP](https://stacks.math.columbia.edu/tag/0BRP)
-/


@[expose] public section

universe u uA uB uK uL uE

/-! ### Nagata rings essentially of finite type -/

/-- **A ring essentially of finite type over a Nagata ring is Nagata.** -/
theorem IsNagataRing.of_isEssentiallyOfFiniteType {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (hA : IsNagataRing A)
    (hft : IsEssentiallyOfFiniteType A B (algebraMap A B)) :
    IsNagataRing B := by
  obtain ⟨T, _, _, _, M, _, -, hloc⟩ := hft
  have h := (isNagataRing_tfae (R := A)).out 1 2
  exact isNagata_of_isLocalization T M B (h.mp hA T)

/-! ### Separable solutions -/

namespace IsDiscreteValuationRing

/-- **Separable solutions, assuming Epp's theorem.** Let `A → B` be an extension of discrete
valuation rings with fraction fields `K ⊂ L` such that `B` is essentially of finite type over `A`,
`A` or `B` is a Nagata ring, and `L / K` is separable. If Epp's theorem holds at the universe
levels `.{uA, uB, uK, uL}` and `.{uK, max uL uK, uK, max uL uK}`, then there exists a separable
solution for `A → B`. -/
theorem exists_isSeparableSolution_of_isNagataRing_of_eppTheorem
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.EssFiniteType A B]
    (hNagata : IsNagataRing A ∨ IsNagataRing B)
    (hsep : Algebra.IsSeparableExtension K L)
    (hEpp : Stacks.EliminateRamification.EppTheorem.{uA, uB, uK, uL})
    (hEppLocal : Stacks.EliminateRamification.EppTheorem.{uK, max uL uK, uK, max uL uK}) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D₁ : IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L K₁,
        D₁.IsSeparableSolution.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK, max uL uK} :=
  exists_isSeparableSolution_of_exists_isSolution A B K L hsep
    (hNagata.elim (fun hA => IsNagataRing.of_essFiniteType hA) id)
    (Stacks.EliminateRamification.exists_finite_extension_isSolution_of_eppTheorem A B K L hEpp
      hEppLocal)

/-- **Separable solutions, assuming Epp's theorem at single universes.** The conclusion of
`exists_isSeparableSolution_of_isNagataRing_of_eppTheorem`, assuming Epp's theorem at the universe
levels `.{v, v, v, v}` for `v = max uA uB uK uL` and for `v = max uK uL`. -/
theorem exists_isSeparableSolution_of_essFiniteType_of_eppTheorem_monomorphic
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.EssFiniteType A B]
    (hNagata : IsNagataRing A ∨ IsNagataRing B)
    (hsep : Algebra.IsSeparableExtension K L)
    (hMono : Stacks.EliminateRamification.EppTheorem.{max uA uB uK uL, max uA uB uK uL, max uA uB uK
      uL,
      max uA uB uK uL})
    (hMonoLocal : Stacks.EliminateRamification.EppTheorem.{max uK uL, max uK uL, max uK uL, max uK
      uL}) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D₁ : IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L K₁,
        D₁.IsSeparableSolution.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK, max uL uK} :=
  exists_isSeparableSolution_of_isNagataRing_of_eppTheorem A B K L hNagata hsep
    (Stacks.EppTheorem.eppTheorem_of_monomorphic hMono)
    (Stacks.EppTheorem.eppTheorem_of_monomorphic hMonoLocal)

/-- Let `A → B` be an extension of discrete valuation rings with fraction fields `K ⊂ L` such that
`B` is essentially of finite type over `A`, `A` or `B` is a Nagata ring, and `L / K` is separable.
Then there exists a separable solution for `A → B`. -/
@[stacks 0BRP]
theorem exists_isSeparableSolution_of_essFiniteType
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.EssFiniteType A B]
    (hNagata : IsNagataRing A ∨ IsNagataRing B)
    (hsep : Algebra.IsSeparableExtension K L) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D₁ : IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L K₁,
        D₁.IsSeparableSolution.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK, max uL uK} :=
  exists_isSeparableSolution_of_essFiniteType_of_eppTheorem_monomorphic
    A B K L hNagata hsep
      Stacks.EppTheorem.eppTheorem_monomorphic Stacks.EppTheorem.eppTheorem_monomorphic

/-- **A solution gives a separable solution.** Let `A → B` be an extension of discrete valuation
rings in a common universe with fraction fields `K ⊂ L`. Assume

* `B` is essentially of finite type over `A`;
* `A` or `B` is a Nagata ring;
* `L / K` is separable;
* there is a solution for `A → B`.

Then there is a separable solution for `A → B`. -/
theorem exists_isSeparableSolution_of_isEssentiallyOfFiniteType
    (A : Type u) (B : Type u) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    (hft : IsEssentiallyOfFiniteType A B (algebraMap A B))
    (hnagata : IsNagataRing A ∨ IsNagataRing B)
    (hsep : Algebra.IsSeparableExtension K L)
    (hsolution :
      ∃ (K₂ : Type uE) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∃ D₂ : IntegralClosureBaseChange.{u, u, uK, uL, uE,
          max uL uE, uE, max uL uE} A B K L K₂,
        D₂.IsSolution.{u, u, uK, uL, uE,
          max uL uE, uE, max uL uE, max uL uE}) :
    ∃ (K₁ : Type uE) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D₁ : IntegralClosureBaseChange.{u, u, uK, uL, uE,
          max uL uE, uE, max uL uE} A B K L K₁,
        D₁.IsSeparableSolution.{u, u, uK, uL, uE,
          max uL uE, uE, max uL uE, max uL uE} := by
  have hB : IsNagataRing B :=
    hnagata.elim (fun hA => IsNagataRing.of_isEssentiallyOfFiniteType hA hft) id
  exact exists_isSeparableSolution_of_exists_isSolution A B K L hsep hB hsolution

end IsDiscreteValuationRing
