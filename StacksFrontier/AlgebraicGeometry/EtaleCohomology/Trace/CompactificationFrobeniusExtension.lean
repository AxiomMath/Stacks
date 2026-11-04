module

public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFrobeniusIteration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusAction

/-!
# The geometric Frobenius extends to the base change of a compactification

Let `k` be a finite field with `q = p ^ f` elements, let `X` be a scheme over `k`, and let
`j : X ⟶ X̄` be a compactification of `X` over `Spec k`.  For an extension field `K` of `k` the
base change `j_K : X_K ⟶ X̄_K` is a compactification of `X_K` over `Spec K`
(`Stacks.EtaleCohomology.compactificationFieldBaseChange`), and the base change
`π_{X̄} × id` of the geometric Frobenius of `X̄` is an endomorphism of it over `Spec K`
restricting to `π_X × id` on `X_K`.  This is how the source makes the geometric Frobenius act on
`RΓ_c(X_k̄, K)`: it compactifies `X` over `k`, where the Frobenius extends because it is
natural, and base changes.

## Main definitions

* `Stacks.EtaleCohomology.compactificationFieldBaseChangeFrobenius` — the endomorphism
  `π_{X̄} × id` of the compactification `j_K`, extending `π_X × id`.

## Main results

* `Stacks.EtaleCohomology.geometricFrobenius_left_comp_immersion` — the geometric Frobenius
  commutes with the open immersion of a compactification.

## Implementation notes

The extension property is checked on the two projections of `X̄_K`: on the second both sides
are the projection to `Spec K`, and on the first it is naturality of the iterated absolute
Frobenius along `j` (`AlgebraicGeometry.absoluteFrobeniusPow_naturality`).

## References

* [Stacks Project, Tag 03SQ](https://stacks.math.columbia.edu/tag/03SQ)
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f))
  (K : Type u) [Field K] [Algebra k K] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The geometric Frobenius commutes with the open immersion of a compactification: this is
naturality of the iterated absolute Frobenius. -/
@[reassoc]
public lemma geometricFrobenius_left_comp_immersion :
    (geometricFrobenius (Over.mk f) p q hcard).left ≫ j.immersion =
      j.immersion ≫ (geometricFrobenius (Over.mk j.toBase) p q hcard).left :=
  absoluteFrobeniusPow_naturality j.immersion p _ _ q

/-- **The geometric Frobenius on the base change of a compactification.**  The endomorphism
`π_{X̄} × id` of `X̄_K` is an endomorphism over `Spec K` of the compactification `j_K` of `X_K`
induced by `j`, and it extends the endomorphism `π_X × id` of `X_K`. -/
public def compactificationFieldBaseChangeFrobenius :
    CompactificationEndomorphism (compactificationFieldBaseChange f j K)
      (geometricFrobeniusBaseChange (Over.mk f) K p q hcard) where
  hom := geometricFrobeniusBaseChange (Over.mk j.toBase) K p q hcard
  hom_comp_toBase := geometricFrobeniusBaseChange_comp_snd (Over.mk j.toBase) K p q hcard
  immersion_comp_hom := by
    change compactificationFieldBaseChangeImmersion f j K ≫
        geometricFrobeniusBaseChange (Over.mk j.toBase) K p q hcard =
      geometricFrobeniusBaseChange (Over.mk f) K p q hcard ≫
        compactificationFieldBaseChangeImmersion f j K
    refine pullback.hom_ext ?_ ?_
    · have h1 := geometricFrobeniusBaseChange_comp_fst (Over.mk j.toBase) K p q hcard
      have h2 := geometricFrobeniusBaseChange_comp_fst (Over.mk f) K p q hcard
      have h3 := compactificationFieldBaseChange_immersion_comp_fst f j K
      have h4 := geometricFrobenius_left_comp_immersion f j p q hcard
      dsimp only [Over.mk_hom] at h1 h2 h3 h4 ⊢
      rw [Category.assoc, h1, reassoc_of% h3, Category.assoc, h3, reassoc_of% h2, h4]
    · have h1 := geometricFrobeniusBaseChange_comp_snd (Over.mk j.toBase) K p q hcard
      have h2 := geometricFrobeniusBaseChange_comp_snd (Over.mk f) K p q hcard
      have h3 := compactificationFieldBaseChange_immersion_comp_snd f j K
      dsimp only [Over.mk_hom] at h1 h2 h3 ⊢
      rw [Category.assoc, h1, h3, Category.assoc, h3, h2]

/-- The underlying endomorphism of `compactificationFieldBaseChangeFrobenius` is the base change
`π_{X̄} × id` of the geometric Frobenius of the compactification. -/
@[simp]
public lemma compactificationFieldBaseChangeFrobenius_hom :
    (compactificationFieldBaseChangeFrobenius f j K p q hcard).hom =
      geometricFrobeniusBaseChange (Over.mk j.toBase) K p q hcard := rfl

end Stacks.EtaleCohomology

end
