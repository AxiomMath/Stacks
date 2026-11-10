module

public import StacksFrontier.Deformation.Examples.Linear.CoprimeCoverStagedTower
public import StacksFrontier.Deformation.Examples.Linear.FlatAlgebraLiftCoprimeCover

/-!
# Stacks 0DZ7 at a principal multiplicative set, from the staged lifting data of the cover

`StacksFrontier/Deformation/Examples/Linear/FlatAlgebraLiftCoprimeCover.lean` proves that the
converse
of Stacks 0DZ7 at a principal multiplicative set is *equivalent* to an auxiliary-free gluing
principle about a comaximal pair `f, g` in a finite type flat `A`-algebra `B` with `A → B_h`
syntomic for every `h ∈ (f)`.
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverStagedTower.lean` packages the deformation
theory that principle runs on as `Deformation.Examples.CoprimeCover.CoverLiftTower` and proves the
staged induction from it, modulo one named further assertion.

This file joins the two. It states, as a single Prop, what the missing `Ext` interface is asked to
deliver — for every instance of the gluing principle's data, a staged lifting tower whose top stage
produces a flat lift of `B` — and deduces from it the gluing principle, the converse of Stacks 0DZ7
at a principal `S`, and the tag's whole biconditional there.

## What is still open, exactly

The presentation Prop below has three conjuncts past the tower itself: that the tower's base stage
carries a lift whose restriction rises to the top (which a flat lift of `B_g` over the thickening
provides), that the top stage of the tower produces a flat lift of `B`, and
`Deformation.Examples.CoprimeCover.CoverLiftTower.WeakLink`. The first two are the construction of
the interface — the torsor of flat lifts under `Ext¹(NL, · ⊗ K)` (Stacks 08S7, present in this
repository for an arbitrary square-zero problem as
`Stacks.Deformation.isomorphismClassesTorsor`, but without a flatness condition on
`Stacks.Deformation.SquareZeroExtensionProblem.CompatibleExtension`), the obstruction class in
`Ext²`, the vanishing of `Ext²` for a local complete intersection that Stacks 07M8 rests on, and
naturality under localization. The third is **not** part of that construction: it is independent of
every field of the tower, which is what
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverStagedTowerIndependence.lean` proves, so it
has to be established from structure the tower does not record.

For a kernel `I` with `I³ = 0` the third conjunct is unnecessary, by
`Deformation.Examples.CoprimeCover.CoverLiftTower.exists_gl_of_le_two`: a tower with `N ≤ 2`
reaches its top stage from the lifting data alone. So the interface alone settles the first
nilpotence index at which the tag is open, and the weak link is what the indices beyond it need.

## Main definitions

* `Deformation.Examples.CoprimeCover.CoverLiftTowerPresentation` — the interface, as one Prop:
  every instance of the gluing principle's data is presented by a staged lifting tower with the
  weak link, whose top stage produces a flat lift.

## Main results

* `Deformation.Examples.CoprimeCover.flatAlgebraLiftCoprimeCoverStatement_of_presentation` — the
  presentation implies the gluing principle.
* `Deformation.Examples.CoprimeCover.flatAlgebraLiftAwayStatement_of_presentation` — hence the
  converse of Stacks 0DZ7 at a principal multiplicative set.
* `Deformation.Examples.CoprimeCover.hasFlatAlgebraLift_localization_iff_of_presentation` — hence
  the whole biconditional of Stacks 0DZ7 there, the forward implication being unconditional.

## Implementation notes

**No Stacks attribute is claimed.** Every result here carries the presentation Prop as a
hypothesis, and that Prop is open: it asserts both the existence of the interface and the weak
link. What the file records is a reduction, with the two halves of what is left separated — one a
construction whose pieces are identified, the other an assertion proved independent of them.

**The instance arguments of the tower inside the existential.** The translation and obstruction
modules are quantified existentially together with their `AddCommGroup` and `Module` structures,
which are then available as local instances for the tower's own instance arguments. Keeping them
stage-independent is what makes this possible; see the implementation notes of
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverStagedTower.lean` for why it costs no
generality.

## References

* [Stacks Project, Tag 0DZ7](https://stacks.math.columbia.edu/tag/0DZ7)
* [Stacks Project, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
* [Stacks Project, Tag 08S7](https://stacks.math.columbia.edu/tag/08S7)
-/

@[expose] public noncomputable section

universe u

namespace Deformation.Examples.CoprimeCover

/-- **The deformation-theoretic interface the gluing principle of Stacks 0DZ7 asks for.** For every
surjection `A' → A` of Noetherian rings with nilpotent kernel, every finite type flat `A`-algebra
`B`, every comaximal pair `f, g ∈ B` with `A → B_h` syntomic for all `h ∈ (f)`, and every flat
`A'`-lift of `B_g`: a staged lifting tower for the cover, a base lift whose restriction rises to
the top of the tower, the weak link, and the production of a flat `A'`-lift of `B` from the top
stage.

This is one Prop with two very different conjuncts. The tower, the base lift and the final
implication are the interface to be built — lift torsor, obstruction class, its
Bockstein-plus-cup-square variation, vanishing of `Ext²` over a local complete intersection,
naturality under localization. The weak link is independent of all the tower's fields
(`Deformation.Examples.CoprimeCover.StagedIndependence.exists_tower_not_weakLink`), and is needed
only where two or more stages of the filtration remain. -/
def CoverLiftTowerPresentation : Prop :=
  ∀ (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B],
    Function.Surjective (algebraMap A' A) →
    IsNilpotent (RingHom.ker (algebraMap A' A)) →
    ∀ [Algebra.FiniteType A B] [Module.Flat A B] (f g : B),
    (∀ h ∈ Ideal.span {f}, Algebra.Syntomic A (Localization.Away h)) →
    Ideal.span {f} ⊔ Ideal.span {g} = ⊤ →
    ∀ (C : Type u) [CommRing C] [Algebra B C] [IsLocalization (Submonoid.powers g) C]
      [Algebra A C] [IsScalarTower A B C],
    HasFlatAlgebraLift A' A C →
    ∃ (n N : ℕ) (T₁ T₂ : Type u) (_i₁ : AddCommGroup T₁) (_j₁ : Module B T₁)
      (_i₂ : AddCommGroup T₂) (_j₂ : Module B T₂) (D : CoverLiftTower B f n N T₁ T₂)
      (x : D.Gl 0), D.liftsTo N 0 (D.res x) ∧ D.WeakLink ∧
        (Nonempty (D.Gl N) → HasFlatAlgebraLift A' A B)

/-- **The interface implies the two-element Zariski gluing principle for flat algebra lifts.** The
staged induction of `Deformation.Examples.CoprimeCover.CoverLiftTower.exists_gl_of_weakLink`
carries the presented tower to its top stage, and the presentation turns that into a flat lift of
`B`. -/
theorem flatAlgebraLiftCoprimeCoverStatement_of_presentation
    (H : CoverLiftTowerPresentation.{u}) : FlatAlgebraLiftCoprimeCoverStatement.{u} := by
  intro A' A B _ _ _ _ _ _ _ hsurjA hnilA _ _ f g hsyn hfg C _ _ _ _ _ hC
  obtain ⟨n, N, T₁, T₂, _, _, _, _, D, x, hx, hWL, hfin⟩ :=
    H A' A B hsurjA hnilA f g hsyn hfg C hC
  exact hfin (D.exists_gl_of_weakLink hWL x hx)

/-- **The interface implies the converse of Stacks 0DZ7 at a principal multiplicative set.** By
`Deformation.Examples.CoprimeCover.flatAlgebraLiftAwayStatement_of_coprimeCoverStatement` the
gluing principle *is* that converse, the ideal `𝔟`, the condition `hSb` and the multiplicative set
all being eliminable from it. -/
theorem flatAlgebraLiftAwayStatement_of_presentation
    (H : CoverLiftTowerPresentation.{u}) : FlatAlgebraLiftAwayStatement.{u} :=
  flatAlgebraLiftAwayStatement_of_coprimeCoverStatement
    (flatAlgebraLiftCoprimeCoverStatement_of_presentation H)

/-- **The interface implies Stacks 0DZ7 at a principal multiplicative set.** The forward
implication is `Deformation.hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift`, which needs
nothing beyond surjectivity of `A' → A`; the converse is the interface through the gluing
principle.

This carries no Stacks attribute: its hypothesis is open. -/
theorem hasFlatAlgebraLift_localization_iff_of_presentation
    (H : CoverLiftTowerPresentation.{u})
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B]
    (s : B) (C : Type u) [CommRing C] [Algebra B C] [IsLocalization (Submonoid.powers s) C]
    [Algebra A C] [IsScalarTower A B C]
    (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (hSb : ∀ q : Ideal B, q.IsPrime → b ≤ q → ∀ t ∈ Submonoid.powers s, t ∉ q) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A C :=
  hasFlatAlgebraLift_localization_iff_of_coprimeCoverStatement
    (flatAlgebraLiftCoprimeCoverStatement_of_presentation H) A' A B hsurjA hnilA s C b hsyn hSb

end Deformation.Examples.CoprimeCover

end
