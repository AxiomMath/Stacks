module

public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.Basic
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective

/-!
# Stacks 081F with its Chow hypothesis discharged over a Noetherian stage

`StacksFrontier/AlgebraicGeometry/ProperLimitStage/Basic.lean` proves Stacks 081F — properness
of a morphism over the limit of a cofiltered system descends to some finite stage — on the
hypothesis `hchow : HasChowModification f₀.left`, and its implementation note records that
"nothing in this repository produces a `HasChowModification`".

**That note has expired.** [Stacks, Tag 0200], Chow's lemma over a Noetherian base, is now
proved and tagged: `AlgebraicGeometry.hasDenseChowModification`
(`StacksFrontier/AlgebraicGeometry/Segre/ChartSurjective.lean:461`, with `@[stacks 0200]` at
`:460`) produces it unconditionally for a separated, quasi-compact morphism locally of finite
type onto a Noetherian scheme, and `AlgebraicGeometry.hasChowModification` (`:466`) is its
`HasChowModification` form. So the hypothesis is dischargeable, at the price of asking the stage
base `Y₀` to be Noetherian rather than merely quasi-compact and quasi-separated.

That price is not paid in the application this matters for. The limit presentations in which
Stacks 081F is used — writing an arbitrary ring as the filtered colimit of its Noetherian
subrings, as [Stacks, Tag 0EX4] does to reach a Noetherian base — have **Noetherian stages** and
a non-Noetherian limit, so the hypothesis holds at every `Y₀` and is exactly the form those
arguments quote.

## Main results

* `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian`: **Stacks 081F with
  `hchow` discharged**, for a Noetherian stage base.

## Implementation notes

**No `@[stacks 081F]` attribute is attached.** Stacks 081F discharges Chow's lemma over a
quasi-compact quasi-separated base, which is [Stacks, Tag 0202]; what is available here is the
Noetherian case [Stacks, Tag 0200], so the statement below carries `IsNoetherian Y₀.left` and
`IsSeparated f₀.left` — two hypotheses the tag does not carry. Withholding is deliberate: with
0202 in place the same proof gives the tag, and the only change would be to delete those two
binders.

**Two of Chow's four hypotheses cost nothing here, and each was found by a different
instrument.** `[CompactSpace Y₀.left]`, which
`exists_isProper_baseChange_of_isLimit_of_hasChowModification` takes as a binder, is not repeated
here because `AlgebraicGeometry.IsNoetherian` implies it — that one the
`linter.overlappingInstances` check reports. `[QuasiCompact f₀.left]` is not a binder either,
because `AlgebraicGeometry.quasiCompact_of_compactSpace` gets it from `[CompactSpace X₀.left]`,
which the original statement already had; the linter is silent about that one and it was found by
a negative control that *failed to fail*. The other five quasi-compactness and
quasi-separatedness binders are kept, none of them being implied.

## References

* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe v u

/-- **Stacks 081F over a Noetherian stage, with Chow's lemma discharged.** Let `D` be a cofiltered
inverse system of schemes with affine transition morphisms and limit cone `c`, and let
`f₀ : X₀ ⟶ Y₀` be a morphism of schemes over the stage `D.obj i₀` which is separated and locally
of finite type, with `Y₀` Noetherian, and which becomes proper after base change to the limit.
Then `f₀` is proper after base change to some later stage.

This is `exists_isProper_baseChange_of_isLimit_of_hasChowModification` with its hypothesis
supplied by `AlgebraicGeometry.hasChowModification`, [Stacks, Tag 0200]. -/
theorem exists_isProper_baseChange_of_isLimit_of_isNoetherian
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    [IsProper ((Over.pullback (c.π.app i₀)).map f₀).left]
    [IsNoetherian Y₀.left] [IsSeparated f₀.left] :
    ∃ (i : I) (hi : i ⟶ i₀), IsProper ((Over.pullback (D.map hi)).map f₀).left :=
  exists_isProper_baseChange_of_isLimit_of_hasChowModification D c hc i₀ X₀ Y₀ f₀
    (hasChowModification.{u} f₀.left)

end AlgebraicGeometry

end
