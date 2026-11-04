module

public import StacksFrontier.Examples.Flatness.FlatAlgebraNotFilteredColimit
public import StacksFrontier.Examples.Flatness.OrdinaryCone.CharacteristicTwo

/-!
# Flat algebras which are not filtered colimits of finitely presented flat algebras

There is a commutative ring `A` with a flat algebra `B` which is the colimit of no filtered
diagram of finitely presented flat `A`-algebras; moreover `A` may be chosen to be a finite type
algebra over a prime field `𝔽_p`, or a one-dimensional Noetherian local ring whose residue field
has characteristic zero.

In positive characteristic one may take `A = 𝔽₂[x₁, x₂, x₃]` and its absolute integral closure
`A⁺`; in characteristic zero, the completion of a one-dimensional henselian local ring of
derivation constants.

## Main results

* `Stacks.Examples.exists_flat_algebra_not_filteredColimit`: there is a ring with a flat algebra
  which is not a filtered colimit of finitely presented flat algebras, and the ring may be chosen
  to be of finite type over `ZMod p` for a prime `p`, or a one-dimensional Noetherian local ring
  whose residue field has characteristic zero.

## References

* [Stacks Project, Tag 0ATF](https://stacks.math.columbia.edu/tag/0ATF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Examples

/-- There is a commutative ring with a flat algebra which is the colimit of no filtered diagram of
finitely presented flat algebras; the ring may be chosen to be a finite type algebra over `𝔽_p`
for a prime `p`, or a one-dimensional Noetherian local ring whose residue field has
characteristic zero. -/
@[stacks 0ATF]
theorem exists_flat_algebra_not_filteredColimit :
    (∃ (A : CommRingCat.{max u v}) (B : CommAlgCat.{max u v} A), Module.Flat A B ∧
      ∀ (J : Type v) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommAlgCat.{max u v} A),
        (∀ j, Algebra.FinitePresentation A (F.obj j) ∧ Module.Flat A (F.obj j)) →
          ∀ c : Cocone F, c.pt = B → IsEmpty (IsColimit c)) ∧
    (∃ p : ℕ, p.Prime ∧ ∃ (A : CommRingCat.{max u v}) (_ : Algebra (ZMod p) A),
      Algebra.FiniteType (ZMod p) A ∧ ∃ B : CommAlgCat.{max u v} A, Module.Flat A B ∧
        ∀ (J : Type v) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommAlgCat.{max u v} A),
          (∀ j, Algebra.FinitePresentation A (F.obj j) ∧ Module.Flat A (F.obj j)) →
            ∀ c : Cocone F, c.pt = B → IsEmpty (IsColimit c)) ∧
    (∃ A : CommRingCat.{max u v}, ∃ hloc : IsLocalRing A,
      letI : IsLocalRing A := hloc
      IsNoetherianRing A ∧ ringKrullDim A = 1 ∧
        CharZero (IsLocalRing.ResidueField A) ∧
          ∃ B : CommAlgCat.{max u v} A, Module.Flat A B ∧
            ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
              (F : J ⥤ CommAlgCat.{max u v} A),
              (∀ j, Algebra.FinitePresentation A (F.obj j) ∧
                Module.Flat A (F.obj j)) →
                ∀ c : Cocone F, c.pt = B → IsEmpty (IsColimit c)) :=
  ⟨exists_flat_algebra_not_filteredColimit_finitePresentation_flat.{u, v},
    ⟨2, Nat.prime_two, exists_charTwo_finiteType_flat_algebra_not_filteredColimit.{u, v}⟩,
    exists_charZero_local_flat_algebra_not_filteredColimit.{u, v}⟩

end Stacks.Examples
