module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence

/-!
# The localization sequence along an arbitrary open immersion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `j : U ⟶ X` be an open immersion and let `i : Y ⟶ X` be a closed
immersion whose image is the complement of the image of `j`. Stacks 02RX says that

  `A_k(Y) → A_k(X) → A_k(U) → 0`

is exact, the first map being `i_*` and the second the restriction `j^*`. The library states it
for the inclusion of an open subscheme `V ⊆ X`
(`Stacks.Chow.exact_chowPushforward_chowGroupOpensRestrict`,
`Stacks.Chow.surjective_chowGroupOpensRestrictOfIsOpenImmersion`). This file reads it along an
arbitrary open immersion, with restriction `Stacks.Chow.chowGroupRestrict`: that restriction is
the restriction to the image `j.opensRange` followed by the transport along the isomorphism onto
the image (`Stacks.Chow.chowGroupRestrict_eq_chowPushforwardOfIso`), and the transport is
bijective.

## Main results

* `Stacks.Chow.surjective_chowGroupRestrict` — **Stacks 02RX**, exactness at `A_k(U)`.
* `Stacks.Chow.exact_chowPushforward_chowGroupRestrict` — **Stacks 02RX**, exactness at `A_k(X)`.

## References

* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
  (k : ℤ)

/-- **Stacks 02RX**, exactness at `A_k(U)`, along an arbitrary open immersion: restriction of
cycle classes along an open immersion is surjective. -/
theorem surjective_chowGroupRestrict :
    Function.Surjective (chowGroupRestrict C sX sU j hj k) := by
  rw [chowGroupRestrict_eq_chowPushforwardOfIso, AddMonoidHom.coe_comp]
  exact (chowGroupEquivOfIso C (j.opensRange.ι ≫ sX) sU j.isoOpensRange.inv
    (isoOpensRange_inv_comp_base C sX sU j hj) k).surjective.comp
      (surjective_chowGroupOpensRestrictOfIsOpenImmersion C sX j.opensRange k)

/-- **Stacks 02RX**, exactness at `A_k(X)`, along an arbitrary open immersion: for a closed
immersion `i : Y ⟶ X` whose image is the complement of the image of `j`, a class on `X` restricts
to zero along `j` exactly when it is pushed forward along `i`. -/
theorem exact_chowPushforward_chowGroupRestrict {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sY)
    (hcomplement : Set.range i.base = (Set.range j.base)ᶜ) :
    Function.Exact (chowPushforwardOfIsClosedImmersion C sY sX i hi k)
      (chowGroupRestrict C sX sU j hj k) := by
  have hc : Set.range i.base = (Set.range j.opensRange.ι.base)ᶜ := by
    rw [hcomplement]
    congr 1
    rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange]
  intro x
  rw [chowGroupRestrict_eq_chowPushforwardOfIso, AddMonoidHom.comp_apply,
    ← exact_chowPushforward_chowGroupOpensRestrict C sX sY i hi j.opensRange hc k x]
  exact (chowGroupEquivOfIso C (j.opensRange.ι ≫ sX) sU j.isoOpensRange.inv
    (isoOpensRange_inv_comp_base C sX sU j hj) k).map_eq_zero_iff

end Stacks.Chow

end
