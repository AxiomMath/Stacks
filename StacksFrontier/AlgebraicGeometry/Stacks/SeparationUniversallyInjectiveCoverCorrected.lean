module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.MapCospanPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationUniversallyInjectiveCover

/-!
# Stacks 0CPQ, corrected

`StacksFrontier/AlgebraicGeometry/Stacks/SeparationUniversallyInjectiveCover.lean` proves
**Stacks 0CPQ** with universal closedness of the relative diagonal `Δ_f` added, local finite type
of a relative diagonal assumed, and the permanence of three properties under forming `f × f`
assumed. This file removes the last two assumptions, shows that the added one is equivalent to the
conclusion given the other hypotheses, and registers a corrected form.

The published statement is false: the obstruction is separatedness of the base change `i` of
`Δ_g` along `f × f`, and a counterexample is
`Stacks.Examples.not_forall_isSeparated_of_isSeparated_comp_of_universallyInjective`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isSeparated_of_isSeparated_comp_of_universallyInjective_of_universallyClosed_relativeDiagonal`:
  Stacks 0CPQ assuming only universal closedness of `Δ_f`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_relativeDiagonal_of_isSeparated` and
  `.isSeparated_iff_universallyClosed_relativeDiagonal`: under the hypotheses of the tag,
  universal closedness of `Δ_f` is equivalent to separatedness of `g`.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isSeparated_of_isSeparated_comp_of_universallyInjective_of_isSeparated_diagonal`:
  **Stacks 0CPQ**, corrected form, with the relative diagonal of `g` assumed separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isSeparated_of_isSeparated_comp_of_universallyInjective_of_isRepresentableByAlgebraicSpaces`:
  the corrected form when `g` is representable by algebraic spaces, where the extra hypothesis
  holds automatically.

## References

* [Stacks Project, Tag 0CPQ](https://stacks.math.columbia.edu/tag/0CPQ)
* [Stacks Project, Tag 0CPT](https://stacks.math.columbia.edu/tag/0CPT)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u v w

namespace AlgebraicStacks

/-- **Stacks 0CPQ, with universal closedness of `Δ_f` assumed.** Let `f : 𝒳 ⟶ 𝒴` and
`g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. If `f` is surjective, flat, locally of
finite presentation and universally injective, if the relative diagonal of `f` is universally
closed, and if `f ≫ g` is separated, then `g` is separated.

The relative diagonal of `f` is surjective by Stacks 0CPN, so properness of `Δ_{f ≫ g} = Δ_f ≫ i`
gives properness of the comparison 1-morphism `i : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳`; and `i` is a base change
of `Δ_g` along `f × f`, so properness of `Δ_g` descends by Stacks 0CPP.

Given the other hypotheses, universal closedness of `Δ_f` is also a consequence of the
conclusion — `AlgebraicGeometry.Stack.AlgebraicStacks`
`.universallyClosed_relativeDiagonal_of_isSeparated` — so the implication below is in fact an
equivalence. See the implementation notes.

It carries no tag: the added hypothesis is equivalent to the conclusion, so the registration of
Stacks 0CPQ sits on the corrected form
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isSeparated_of_isSeparated_comp_of_universallyInjective_of_isSeparated_diagonal`, whose added
hypothesis is on `g` and is strictly weaker than the conclusion. -/
theorem
    isSeparated_of_isSeparated_comp_of_universallyInjective_of_universallyClosed_relativeDiagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfSurj : Stack.IsSurjective B S hS f)
    (hfFlat : IsFlat B S hS f)
    (hfLfp : IsLocallyOfFinitePresentation B S hS f)
    (hfUI : Stack.UniversallyInjective B S hS f)
    (hh : IsSeparated B S hS (f ≫ g))
    (hdiagUC : Stack.UniversallyClosed B S hS (relativeDiagonal B S hS f).hom) :
    IsSeparated B S hS g := by
  have hrepf := Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hreph :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS (f ≫ g)
  have hrepg := Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS g
  have hdec : Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒵.val (f ≫ g).hom =
      (relativeDiagonal B S hS f).hom ≫ (mapBase B S hS f f g).hom :=
    congrArg (fun k => k.hom) (relativeDiagonal_comp B S hS f g)
  have hreph' : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒵.val (f ≫ g).hom).hom := hreph
  have hh' : Stack.IsProper B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒵.val (f ≫ g).hom) := hh
  rw [hdec] at hreph' hh'
  have hiLFT := Stack.relativeProperty_baseChange.{u, u, u + 1} B S hS
    (Space.locallyOfFiniteTypeProperty B S hS) 𝒴.val
    (twoFibreProduct B S hS g g).val (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val
    (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒵.val g.hom)
    (mapCospan B S hS f f g).hom (mapBaseSquare B S hS f f g)
    (isTwoFibreProduct_mapBaseSquare B S hS f f g)
    (Stack.isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack B S hS g).choose_spec
  have hdfSurj := (Stack.pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
      (relativeDiagonal B S hS f) hrepf).1
    (Stack.isSurjective_relativeDiagonal_of_universallyInjective B S hS f hfUI)
  have hiProper := Stack.isProper_of_isSurjective_universallyClosed_comp B S hS
    (relativeDiagonal B S hS f).hom (mapBase B S hS f f g).hom
    hrepf hreph' hdfSurj hdiagUC hh' hiLFT
  have hBC : (Space.properProperty B S hS).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B S hS
  have hLT : (Space.properProperty B S hS).IsLocalAtTarget
      (Space.Topology.precoverage.{u, u} .fppf B S hS) :=
    Space.proper_isLocalAtTarget_fppf B S hS
  refine (Stack.hasRelativeProperty_iff_of_fppfCoverStack B S hS
    (Space.properProperty B S hS) (relativeDiagonal B S hS g) (mapCospan B S hS f f g) hrepg
    (isSurjective_mapCospan B S hS f f g hfSurj hfSurj)
    (isFlat_mapCospan B S hS f f g hfFlat hfFlat)
    (isLocallyOfFinitePresentation_mapCospan B S hS f f g hfLfp hfLfp)
    (mapBaseSquareStacks B S hS f g)
    (isTwoFibreProduct_mapBaseSquareStacks B S hS f g)).2 ⟨?_, hiProper⟩
  exact Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒴.val
    (twoFibreProduct B S hS g g).val (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val
    (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒵.val g.hom)
    (mapCospan B S hS f f g).hom (mapBaseSquare B S hS f f g)
    (isTwoFibreProduct_mapBaseSquare B S hS f f g) hrepg

/-- **Separatedness of `g` makes the relative diagonal of `f` universally closed.** Let
`f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S` with `f ≫ g` and `g`
separated. Then `Δ_f` is proper in the sense of Properties of Stacks, Section 04XB, in
particular universally closed there.

Separatedness of `g` makes `Δ_g` separated, and then part (3) of **Stacks 050M** cancels the
comparison 1-morphism `i` out of `Δ_{f ≫ g} = Δ_f ≫ i`. No hypothesis on `f` is used. -/
theorem universallyClosed_relativeDiagonal_of_isSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hh : IsSeparated B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    Stack.UniversallyClosed B S hS (relativeDiagonal B S hS f).hom :=
  Stack.universallyClosed_of_isProper B S hS _
    (isSeparated_of_comp_of_isSeparated_diagonal B S hS f g hh
      (Stack.isSeparated_of_isProper B S hS _ hg))

/-- **Under the remaining hypotheses of Stacks 0CPQ, universal closedness of `Δ_f` is equivalent
to separatedness of `g`.** The implication that matters is
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isSeparated_of_isSeparated_comp_of_universallyInjective_of_universallyClosed_relativeDiagonal`;
the converse is
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_relativeDiagonal_of_isSeparated` and
needs only separatedness of `f ≫ g`.

So the hypothesis on `Δ_f` cannot be replaced by anything strictly weaker: a property implied by
universal closedness of `Δ_f` but not implying it cannot imply separatedness of `g`, because
separatedness of `g` implies universal closedness of `Δ_f`. -/
theorem isSeparated_iff_universallyClosed_relativeDiagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfSurj : Stack.IsSurjective B S hS f)
    (hfFlat : IsFlat B S hS f)
    (hfLfp : IsLocallyOfFinitePresentation B S hS f)
    (hfUI : Stack.UniversallyInjective B S hS f)
    (hh : IsSeparated B S hS (f ≫ g)) :
    IsSeparated B S hS g ↔
      Stack.UniversallyClosed B S hS (relativeDiagonal B S hS f).hom :=
  ⟨universallyClosed_relativeDiagonal_of_isSeparated B S hS f g hh,
    isSeparated_of_isSeparated_comp_of_universallyInjective_of_universallyClosed_relativeDiagonal
      B S hS f g hfSurj hfFlat hfLfp hfUI hh⟩

/-- **Stacks 0CPQ, corrected: `g` with separated diagonal.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be
1-morphisms of algebraic stacks over `S`. If `f` is surjective, flat, locally of finite
presentation and universally injective, if `f ≫ g` is separated, and if the relative diagonal
`Δ_g : 𝒴 ⟶ 𝒴 ×_𝒵 𝒴` is separated in the sense of Properties of Stacks, Section 04XB, then `g`
is separated.

The added hypothesis is on `g`, not on `f`, and it is strictly weaker than the conclusion, which
asks `Δ_g` to be proper. It is exactly what the published statement is missing: the comparison
1-morphism `i : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳` is a base change of `Δ_g` (Stacks 050H), so it is separated,
and then part (3) of Stacks 050M cancels it out of the proper `Δ_{f ≫ g} = Δ_f ≫ i`, making `Δ_f`
proper, in particular universally closed; the published route through Stacks 0CPN, Stacks 08AJ
and Stacks 0CPP then goes through
(`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isSeparated_of_isSeparated_comp_of_universallyInjective_of_universallyClosed_relativeDiagonal`).
Without it the statement fails, the obstruction being separatedness of `i`:
`Stacks.Examples.not_forall_isSeparated_of_isSeparated_comp_of_universallyInjective`. It holds
whenever `g` is representable by algebraic spaces,
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isSeparated_of_isSeparated_comp_of_universallyInjective_of_isRepresentableByAlgebraicSpaces`. -/
@[stacks 0CPQ "corrected form: the relative diagonal of g is assumed separated, which holds when \
g is representable by algebraic spaces and is strictly weaker than the conclusion; the published \
statement fails, see \
Stacks.Examples.not_forall_isSeparated_of_isSeparated_comp_of_universallyInjective"]
theorem isSeparated_of_isSeparated_comp_of_universallyInjective_of_isSeparated_diagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfSurj : Stack.IsSurjective B S hS f)
    (hfFlat : IsFlat B S hS f)
    (hfLfp : IsLocallyOfFinitePresentation B S hS f)
    (hfUI : Stack.UniversallyInjective B S hS f)
    (hh : IsSeparated B S hS (f ≫ g))
    (hΔg : Stack.IsSeparated.{u, u, u + 1} B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒵.val g.hom)) :
    IsSeparated B S hS g :=
  isSeparated_of_isSeparated_comp_of_universallyInjective_of_universallyClosed_relativeDiagonal
    B S hS f g hfSurj hfFlat hfLfp hfUI hh
    (Stack.universallyClosed_of_isProper B S hS _
      (isSeparated_of_comp_of_isSeparated_diagonal B S hS f g hh hΔg))

/-- **Stacks 0CPQ for `g` representable by algebraic spaces.** Let `f : 𝒳 ⟶ 𝒴` and
`g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S` with `g` representable by algebraic
spaces. If `f` is surjective, flat, locally of finite presentation and universally injective and
`f ≫ g` is separated, then `g` is separated.

The relative diagonal of a 1-morphism representable by algebraic spaces is a monomorphism, hence
separated (Stacks 04YQ, parts (3) and (4)), which is the hypothesis of
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isSeparated_of_isSeparated_comp_of_universallyInjective_of_isSeparated_diagonal`. -/
theorem isSeparated_of_isSeparated_comp_of_universallyInjective_of_isRepresentableByAlgebraicSpaces
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfSurj : Stack.IsSurjective B S hS f)
    (hfFlat : IsFlat B S hS f)
    (hfLfp : IsLocallyOfFinitePresentation B S hS f)
    (hfUI : Stack.UniversallyInjective B S hS f)
    (hh : IsSeparated B S hS (f ≫ g))
    (hg : Stack.IsRepresentableByAlgebraicSpaces B S hS g.hom.hom) :
    IsSeparated B S hS g :=
  isSeparated_of_isSeparated_comp_of_universallyInjective_of_isSeparated_diagonal
    B S hS f g hfSurj hfFlat hfLfp hfUI hh
    (Stack.isSeparated_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS g hg).2

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
