module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedFrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen

/-!
# Reducedness of the Frobenius twist, geometric reducedness, and dense smooth opens

Let `X` be a reduced scheme locally of finite type over a field `k` of characteristic `p > 0`.
Then the Frobenius twist `X^{(p)}` is reduced if and only if `X` is geometrically reduced over
`k`, if and only if `X` contains a dense open subscheme which is smooth over `k`. For a variety
over `k` the last condition may be weakened to the existence of a nonempty open subscheme smooth
over `k`.

## Main results

* `AlgebraicGeometry.isReduced_frobeniusTwist_tfae` is the three-term equivalence.
* `AlgebraicGeometry.isReduced_frobeniusTwist_iff_exists_dense_open_smooth` is the equivalence of
  its first and last conditions, stated as an iff.
* `AlgebraicGeometry.isReduced_frobeniusTwist_tfae_of_isVariety` is the equivalence for a
  variety, with a nonempty open in place of a dense one.

## Implementation notes

The first equivalence is Stacks Tag 0CCE and the second is Stacks Tag 056V, whose hypotheses
(reducedness of `X` and finite type of the structure morphism) are exactly the ones assumed here;
both are available for a variety over `k`. The characteristic hypothesis on `k` supplies the
characteristic hypothesis needed to form the absolute Frobenius of `Spec k`, and hence the
Frobenius twist, through the identity structure morphism of `Spec k`.

The underlying space of a variety is irreducible, so a nonempty open of it is dense; the two
forms of the third condition therefore agree there, and the statement proved for a reduced
scheme locally of finite type is more general than the source's.

## References

* [Stacks Project, Tag 0CCF](https://stacks.math.columbia.edu/tag/0CCF)
-/

@[expose] public section

open CategoryTheory
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0CCF.** For a reduced scheme `X` locally of finite type over a field
`k` of characteristic `p > 0`, the following are equivalent: the Frobenius twist of `X` is
reduced, `X` is geometrically reduced over `k`, and `X` has a dense open subscheme smooth over
`k`. -/
@[stacks 0CCF "reduced_twist_tfae"]
theorem isReduced_frobeniusTwist_tfae
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsReduced X] [LocallyOfFiniteType f] :
    let hS : IsInCharacteristic (Spec (.of k)) p :=
      Stacks.Frobenius.isInCharacteristic_of_over (Over.mk (𝟙 (Spec (.of k))))
    List.TFAE
      [IsReduced (((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk f)).left),
        GeometricallyReduced f,
        ∃ U : X.Opens, Dense (U : Set X) ∧ Smooth (U.ι ≫ f)] := by
  intro hS
  tfae_have 1 ↔ 2 := (geometricallyReduced_iff_isReduced_frobeniusTwist p f).symm
  tfae_have 2 ↔ 3 := geometricallyReduced_iff_exists_dense_open_smooth f
  tfae_finish

/-- A reduced scheme locally of finite type over a field of characteristic `p > 0` has a reduced
Frobenius twist if and only if it contains a dense open subscheme smooth over the field. -/
theorem isReduced_frobeniusTwist_iff_exists_dense_open_smooth
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsReduced X] [LocallyOfFiniteType f] :
    let hS : IsInCharacteristic (Spec (.of k)) p :=
      Stacks.Frobenius.isInCharacteristic_of_over (Over.mk (𝟙 (Spec (.of k))))
    IsReduced (((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk f)).left) ↔
      ∃ U : X.Opens, Dense (U : Set X) ∧ Smooth (U.ι ≫ f) :=
  (isReduced_frobeniusTwist_tfae p f).out 1 3

/-- **Stacks Project, Tag 0CCF.** For a variety `X` over a field `k` of characteristic `p > 0`,
the following are equivalent: the Frobenius twist of `X` is reduced, `X` is geometrically reduced
over `k`, and there is a nonempty open subscheme of `X` smooth over `k`. -/
@[stacks 0CCF "reduced_twist_tfae, the variety form with a nonempty smooth open"]
theorem isReduced_frobeniusTwist_tfae_of_isVariety
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f] :
    let hS : IsInCharacteristic (Spec (.of k)) p :=
      Stacks.Frobenius.isInCharacteristic_of_over (Over.mk (𝟙 (Spec (.of k))))
    List.TFAE
      [IsReduced (((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk f)).left),
        GeometricallyReduced f,
        ∃ U : X.Opens, (U : Set X).Nonempty ∧ Smooth (U.ι ≫ f)] := by
  intro hS
  have h23 := geometricallyReduced_iff_exists_dense_open_smooth f
  tfae_have 1 ↔ 2 := (geometricallyReduced_iff_isReduced_frobeniusTwist p f).symm
  tfae_have 2 → 3 := fun h ↦ (h23.mp h).imp fun _ ⟨hd, hs⟩ ↦ ⟨hd.nonempty, hs⟩
  tfae_have 3 → 2 := fun ⟨U, hne, hs⟩ ↦ h23.mpr ⟨U, U.isOpen.dense hne, hs⟩
  tfae_finish

end AlgebraicGeometry

end
