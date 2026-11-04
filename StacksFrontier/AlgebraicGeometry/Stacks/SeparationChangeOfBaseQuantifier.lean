module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteSource
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase

/-!
# The 04XB conditions that quantify over algebraic spaces, and change of base (Stacks 04X5, 04XB)

Let `g : S ⟶ S'` be a morphism of a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S`. Construction A of **Stacks 04X5**
views `f` as a 1-morphism `changeBase f` over the big fppf site of `S'`
(`AlgebraicGeometry.Stack.changeBaseHom`), and
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase` compares a condition of Properties
of Stacks, Section 04XB, on the relative diagonal of `f` with the same condition on the relative
diagonal of `changeBase f` — for a condition read on **étale charts**.

This file does the same for the three conditions of Stacks 04XB which are **not** read on étale
charts: quasi-compactness (`AlgebraicGeometry.Stack.IsQuasiCompact`, the condition at **Stacks
03HE**), quasi-separatedness (`AlgebraicGeometry.Stack.IsQuasiSeparated`, at **Stacks 03HL** part
(3)) and properness (`AlgebraicGeometry.Stack.IsProper`, at **Stacks 03ZM**). Those are the three
conditions the remaining two separation axioms of **Stacks 04YW** are built from: a 1-morphism of
algebraic stacks is separated when its relative diagonal is proper, and quasi-separated when its
relative diagonal is quasi-compact and quasi-separated.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompact_changeBaseHom_iff`,
  `AlgebraicGeometry.Stack.isQuasiSeparated_changeBaseHom_iff` and
  `AlgebraicGeometry.Stack.isProper_changeBaseHom_iff`: a 1-morphism satisfies the condition of
  Stacks 04XB at quasi-compactness, quasi-separatedness or properness exactly when the
  1-morphism produced by Construction A out of it does.
* `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_of_changeBase`,
  `AlgebraicGeometry.Stack.isQuasiSeparated_relativeDiagonal_of_changeBase` and
  `AlgebraicGeometry.Stack.isProper_relativeDiagonal_of_changeBase`: each of those conditions
  passes from the relative diagonal of the view of `f` over `S'` to the relative diagonal of `f`.
* `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_changeBase`,
  `AlgebraicGeometry.Stack.isQuasiSeparated_relativeDiagonal_changeBase` and
  `AlgebraicGeometry.Stack.isProper_relativeDiagonal_changeBase`: the converses — each condition
  passes from the relative diagonal of `f` to the relative diagonal of the view of `f` over `S'`.
  These are the direction the separation axioms of **Stacks 04YW** are carried in, and so the
  input `AlgebraicGeometry.Stack.isSeparatedAbs_of_isSeparated` and
  `AlgebraicGeometry.Stack.isQuasiSeparatedAbs_of_isQuasiSeparated` need in order to read the
  hypothesis on `f` over `S` rather than over the larger base.

## Implementation notes

**Where the difficulty is, and why it is not in this file.** An étale-chart condition is tested
on the charts of the representing morphism of algebraic spaces, so it transports as soon as the
charts do. Each of the three conditions here instead quantifies over the algebraic spaces over
the base, and the domain of that quantifier changes when the base changes; so the statements
below are not corollaries of the étale-chart ones. The comparison of the two quantifier domains
is `StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase`, whose implementation notes describe
it: a test object over the smaller base is carried forward by the lower-shriek extension, while a
test object over the larger base is replaced — using that it is quasi-compact — by a
*representable* test object, which is in the image of the extension. Given that space-level
input, the two steps here are word for word the two steps of
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase`.

**The two steps.** Each `..._changeBaseHom_iff` is the argument of
`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_changeBaseHom_iff` with its space-level
ingredient replaced: the quantifications over scheme-valued points match up by
`AlgebraicGeometry.Stack.comp_changeBase_p_eq_map` and
`AlgebraicGeometry.Stack.exists_comp_p_eq_map_of_changeBase`, and the ones over representing
algebraic spaces by `CategoryTheory.TwoFibreProductOver.fstEquivalenceOver_trans` and its
converse, so the morphism being tested is the same object on both sides, living over the same
scheme over `S`; what is left is that its condition does not depend on whether that scheme is
read over `S` or over `S'`, which is
`AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor_iff` and its two companions.
Applying that to the relative diagonal of `f` gives the condition for `changeBase (Δ_f)`, and the
second step moves from there to `Δ_{changeBase f}` along
`AlgebraicGeometry.Stack.relocalizeBaseFunctor`; that move is **Stacks 0457** for the condition,
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, whose 2-commutativity isomorphism is
the identity by `AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor_changeBase`.

**No instance on the property is demanded.** As in the étale-chart file the conditions are the
quantifier of `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**) written out
longhand, which is how `AlgebraicGeometry.Stack.IsQuasiCompact`,
`AlgebraicGeometry.Stack.IsQuasiSeparated` and `AlgebraicGeometry.Stack.IsProper` are already
stated; and `AlgebraicGeometry.Stack.relativeProperty_of_equivalences` is used in its written-out
form rather than through the abbreviation `hasRelativeProperty_of_equivalences`, because that
abbreviation carries locality at the target for the fppf precoverage as an instance hypothesis
on the property and that is not available for these three.

**Both directions of the second step are proved.**
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences` consumes an equivalence of the
targets, and the two directions use the two comparison 1-morphisms of the 2-fibre products:
`AlgebraicGeometry.Stack.relocalizeBaseFunctor`, which is strictly over the site on the nose, and
`AlgebraicGeometry.Stack.unrelocalizeBaseFunctor`, which is so only through the identification
recorded in the `hx` field of an object of the relocalized 2-fibre product. Clauses of **Stacks
050N** consume the first and clauses of **Stacks 050L** the second.

**No tag.** None of these statements is a numbered result: Stacks 04X5 names only the four clauses
of Stacks 026O, and the transfer of a Stacks 04XB condition on a relative diagonal is a step the
source performs inside the proofs of Stacks 050L and 050N rather than a lemma of its own.

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-! ### The condition of Stacks 04XB at the three properties, and Construction A -/

/-- **Quasi-compactness in the sense of Stacks 04XB is unchanged by Construction A.** A
1-morphism of categories fibred in groupoids over the big fppf site of `S` is quasi-compact in
the relative sense of Stacks 04XB exactly when the 1-morphism over the big fppf site of `S'`
produced by Construction A has that property.

The quantifications over scheme-valued points and over representing algebraic spaces match up as
in `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_changeBaseHom_iff`; what is left is
`AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor_iff`. -/
theorem isQuasiCompact_changeBaseHom_iff
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    IsQuasiCompact B S' hS' (changeBaseHom B S S' hS hS' g f) ↔ IsQuasiCompact B S hS f := by
  constructor
  · rintro hbig U y hy F hF ⟨E⟩
    exact (Space.isQuasiCompact_spacesOverSmallerBaseFunctor_iff B U.left.1 S U.left.2 hS
      U.hom S' hS' g (U.hom ≫ g) rfl F hF).1 <| hbig ((Over.map g).obj U) y
        (comp_changeBase_p_eq_map B S S' hS hS' g 𝒴.val U y hy) F hF
        ⟨TwoFibreProductOver.unrelocalizeFstEquivalenceOver_trans g hy f.hom.w E⟩
  · rintro hsmall U' y hy' F hF ⟨E'⟩
    obtain ⟨h₀, hy, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒴.val U' y hy'
    rw [← hg, Over.mapComp_eq] at E'
    exact (Space.isQuasiCompact_spacesOverSmallerBaseFunctor_iff B U'.left.1 S U'.left.2
      hS h₀ S' hS' g U'.hom hg F hF).2 <| hsmall (Over.mk h₀) y hy F hF
        ⟨TwoFibreProductOver.fstEquivalenceOver_trans g hy f.hom.w E'⟩

/-- **Quasi-separatedness in the sense of Stacks 04XB is unchanged by Construction A.** The
argument of `AlgebraicGeometry.Stack.isQuasiCompact_changeBaseHom_iff` with
`AlgebraicGeometry.Space.isQuasiSeparated_spacesOverSmallerBaseFunctor_iff` in place of its
space-level ingredient. -/
theorem isQuasiSeparated_changeBaseHom_iff
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    IsQuasiSeparated B S' hS' (changeBaseHom B S S' hS hS' g f) ↔ IsQuasiSeparated B S hS f := by
  constructor
  · rintro hbig U y hy F hF ⟨E⟩
    exact (Space.isQuasiSeparated_spacesOverSmallerBaseFunctor_iff B U.left.1 S U.left.2 hS
      U.hom S' hS' g (U.hom ≫ g) rfl F hF).1 <| hbig ((Over.map g).obj U) y
        (comp_changeBase_p_eq_map B S S' hS hS' g 𝒴.val U y hy) F hF
        ⟨TwoFibreProductOver.unrelocalizeFstEquivalenceOver_trans g hy f.hom.w E⟩
  · rintro hsmall U' y hy' F hF ⟨E'⟩
    obtain ⟨h₀, hy, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒴.val U' y hy'
    rw [← hg, Over.mapComp_eq] at E'
    exact (Space.isQuasiSeparated_spacesOverSmallerBaseFunctor_iff B U'.left.1 S U'.left.2
      hS h₀ S' hS' g U'.hom hg F hF).2 <| hsmall (Over.mk h₀) y hy F hF
        ⟨TwoFibreProductOver.fstEquivalenceOver_trans g hy f.hom.w E'⟩

/-- **Properness in the sense of Stacks 04XB is unchanged by Construction A.** The argument of
`AlgebraicGeometry.Stack.isQuasiCompact_changeBaseHom_iff` with
`AlgebraicGeometry.Space.isProper_spacesOverSmallerBaseFunctor_iff` in place of its space-level
ingredient. -/
theorem isProper_changeBaseHom_iff
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    IsProper B S' hS' (changeBaseHom B S S' hS hS' g f) ↔ IsProper B S hS f := by
  constructor
  · rintro hbig U y hy F hF ⟨E⟩
    exact (Space.isProper_spacesOverSmallerBaseFunctor_iff B U.left.1 S U.left.2 hS
      U.hom S' hS' g (U.hom ≫ g) rfl F hF).1 <| hbig ((Over.map g).obj U) y
        (comp_changeBase_p_eq_map B S S' hS hS' g 𝒴.val U y hy) F hF
        ⟨TwoFibreProductOver.unrelocalizeFstEquivalenceOver_trans g hy f.hom.w E⟩
  · rintro hsmall U' y hy' F hF ⟨E'⟩
    obtain ⟨h₀, hy, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒴.val U' y hy'
    rw [← hg, Over.mapComp_eq] at E'
    exact (Space.isProper_spacesOverSmallerBaseFunctor_iff B U'.left.1 S U'.left.2
      hS h₀ S' hS' g U'.hom hg F hF).2 <| hsmall (Over.mk h₀) y hy F hF
        ⟨TwoFibreProductOver.fstEquivalenceOver_trans g hy f.hom.w E'⟩

/-! ### Transfer along the relative diagonal -/

section RelativeDiagonal

variable (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴)

/-- **Quasi-compactness of Stacks 04XB passes from the relative diagonal of the view of `f` over
`S'` to the relative diagonal of `f`.**

The two steps are `AlgebraicGeometry.Stack.isQuasiCompact_changeBaseHom_iff`, which transfers the
condition for `changeBase (Δ_f)` back to `Δ_f`, and **Stacks 0457** for the condition
(`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`) along the equivalence
`AlgebraicGeometry.Stack.relocalizeBaseFunctor` of the two targets, whose 2-commutativity
isomorphism is the identity by
`AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor_changeBase`. -/
theorem isQuasiCompact_relativeDiagonal_of_changeBase
    (h : IsQuasiCompact B S' hS'
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f))) :
    IsQuasiCompact B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f) := by
  have _ : Functor.IsEquivalence
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence
      (𝟭 (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.obj))
  have _ : Functor.IsEquivalence
      (relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f).toFunctor :=
    isEquivalence_relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f
  exact (isQuasiCompact_changeBaseHom_iff B S S' hS hS' g
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).1
    (relativeProperty_of_equivalences B S' hS'
      (fun _ _ k => Space.IsQuasiCompact B S' hS' k.hom)
      (changeBaseHom B S S' hS hS' g (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).hom
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)).hom
      (BasedFunctor.id _) (relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f) (Iso.refl _) h)

/-- **Quasi-separatedness of Stacks 04XB passes from the relative diagonal of the view of `f`
over `S'` to the relative diagonal of `f`.** -/
theorem isQuasiSeparated_relativeDiagonal_of_changeBase
    (h : IsQuasiSeparated B S' hS'
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f))) :
    IsQuasiSeparated B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f) := by
  have _ : Functor.IsEquivalence
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence
      (𝟭 (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.obj))
  have _ : Functor.IsEquivalence
      (relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f).toFunctor :=
    isEquivalence_relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f
  exact (isQuasiSeparated_changeBaseHom_iff B S S' hS hS' g
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).1
    (relativeProperty_of_equivalences B S' hS'
      (fun _ _ k => Space.IsQuasiSeparated B S' hS' k.hom)
      (changeBaseHom B S S' hS hS' g (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).hom
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)).hom
      (BasedFunctor.id _) (relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f) (Iso.refl _) h)

/-- **Properness of Stacks 04XB passes from the relative diagonal of the view of `f` over `S'`
to the relative diagonal of `f`.** -/
theorem isProper_relativeDiagonal_of_changeBase
    (h : IsProper B S' hS'
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f))) :
    IsProper B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f) := by
  have _ : Functor.IsEquivalence
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence
      (𝟭 (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.obj))
  have _ : Functor.IsEquivalence
      (relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f).toFunctor :=
    isEquivalence_relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f
  exact (isProper_changeBaseHom_iff B S S' hS hS' g
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).1
    (relativeProperty_of_equivalences B S' hS'
      (fun _ _ k => Space.IsProper B S' hS' k.hom)
      (changeBaseHom B S S' hS hS' g (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).hom
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)).hom
      (BasedFunctor.id _) (relocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f) (Iso.refl _) h)

/-- **Quasi-compactness of Stacks 04XB is carried from the relative diagonal of `f` to the
relative diagonal of the view of `f` over `S'`.**

The converse of `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_of_changeBase`. The two
steps are the same, with **Stacks 0457** applied along
`AlgebraicGeometry.Stack.unrelocalizeBaseFunctor` rather than along
`AlgebraicGeometry.Stack.relocalizeBaseFunctor`, which is the direction of the equivalence
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences` consumes here. -/
theorem isQuasiCompact_relativeDiagonal_changeBase
    (h : IsQuasiCompact B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)) :
    IsQuasiCompact B S' hS'
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)) := by
  have _ : Functor.IsEquivalence
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence
      (𝟭 (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.obj))
  have _ : Functor.IsEquivalence (unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f).toFunctor :=
    isEquivalence_unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f
  exact relativeProperty_of_equivalences B S' hS'
    (fun _ _ k => Space.IsQuasiCompact B S' hS' k.hom)
    (relativeDiagonalBasedFunctor B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
      (changeBaseHom B S S' hS hS' g f).hom)
    (changeBaseFunctor B S S' hS hS' g (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom))
    (BasedFunctor.id _) (unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f) (Iso.refl _)
    ((isQuasiCompact_changeBaseHom_iff B S S' hS hS' g
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).2 h)

/-- **Quasi-separatedness of Stacks 04XB is carried from the relative diagonal of `f` to the
relative diagonal of the view of `f` over `S'`.** -/
theorem isQuasiSeparated_relativeDiagonal_changeBase
    (h : IsQuasiSeparated B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)) :
    IsQuasiSeparated B S' hS'
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)) := by
  have _ : Functor.IsEquivalence
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence
      (𝟭 (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.obj))
  have _ : Functor.IsEquivalence (unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f).toFunctor :=
    isEquivalence_unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f
  exact relativeProperty_of_equivalences B S' hS'
    (fun _ _ k => Space.IsQuasiSeparated B S' hS' k.hom)
    (relativeDiagonalBasedFunctor B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
      (changeBaseHom B S S' hS hS' g f).hom)
    (changeBaseFunctor B S S' hS hS' g (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom))
    (BasedFunctor.id _) (unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f) (Iso.refl _)
    ((isQuasiSeparated_changeBaseHom_iff B S S' hS hS' g
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).2 h)

/-- **Properness of Stacks 04XB is carried from the relative diagonal of `f` to the relative
diagonal of the view of `f` over `S'`.** With
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_changeBase` this is
the transfer the separatedness axiom of **Stacks 04YW** needs along Construction A, and so the
input of **Stacks 050L** part (7) with the hypothesis on `f` read over `S` rather than over the
larger base. -/
theorem isProper_relativeDiagonal_changeBase
    (h : IsProper B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)) :
    IsProper B S' hS'
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)) := by
  have _ : Functor.IsEquivalence
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence
      (𝟭 (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.obj))
  have _ : Functor.IsEquivalence (unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f).toFunctor :=
    isEquivalence_unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f
  exact relativeProperty_of_equivalences B S' hS'
    (fun _ _ k => Space.IsProper B S' hS' k.hom)
    (relativeDiagonalBasedFunctor B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
      (changeBaseHom B S S' hS hS' g f).hom)
    (changeBaseFunctor B S S' hS hS' g (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom))
    (BasedFunctor.id _) (unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f) (Iso.refl _)
    ((isProper_changeBaseHom_iff B S S' hS hS' g
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).2 h)

end RelativeDiagonal

end AlgebraicGeometry.Stack

end
