module

public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso

/-!
# Tag 03GL's coordinate-pinned comparison, written out as its own construction

The statement of Stacks Tag 03GL uses one datum it leaves unconstructed: the coordinate-pinned
comparison between the base-change model `ℙⁿ_R = Spec R ×_{Spec ℤ} Proj (ULift ℤ)[T₀,…,Tₙ]`
and the polynomial model `Proj R[T₀,…,Tₙ]`, bundled with the coefficient homomorphism, its
domain of definition, and the two compatibilities with the projections of the base change.
That bundle is constructed in this library as
`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`
(`../ProjBaseChange/IsIso.lean`), on the back of
`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare`.

This file is a faithfulness check for that construction, and it carries no attribute and no
registration of its own. It states the bundle **without naming any bundling structure and
without naming the abbreviations the library statement uses**: the comparison appears as a
nested existential over the six fields, projective space over `R` is written out as the
pullback of the two morphisms to the terminal scheme, the integral model is written out as
`Proj` of the integral polynomial grading, the Tag 01MY domain of definition is written out
as the supremum of the standard opens `D₊(ψ f)`, and the morphism to the integral model is
written out as the composite the definition spells it to be. No structure named
`PolynomialComparison` can satisfy the statement by sharing a name with the intended one, and
no abbreviation can satisfy it by unfolding to something else.

Four of those expansions are also recorded here as individual equations, each by `rfl`, so
that the pinning of each abbreviation to the written-out construction is a separate
machine-checked fact rather than something readable only off the big statement.

## Main results

* `Stacks.Tag03GLComparisonAudit.exists_coordinatePinnedComparison`: the comparison, stated
  over written-out constructions and proved from the bundled construction.
* `Stacks.Tag03GLComparisonAudit.projectiveSpaceAtUniverse_eq_proj`,
  `Stacks.Tag03GLComparisonAudit.projectiveSpaceOverRing_eq_pullback`,
  `Stacks.Tag03GLComparisonAudit.toIntegralAtUniverse_eq_pullbackSnd` and
  `Stacks.Tag03GLComparisonAudit.mapDomain_eq_iSup_basicOpen`: the four expansions, each a
  definitional equation.

## What this does not claim

Tag 03GL carries three labelled assertions. Two of them — `"the ideal is graded"` and
`"the degreewise kernels"` — are registered on Tag 0BXK declarations in
`../IdealRegistration/Tags.lean`. The third, `"the closed subscheme is the Proj of the
quotient"`, is **not closed by the comparison below**: the comparison is the datum that
assertion's statement is phrased over, not the assertion. Its content is an equality of two
ideal sheaves on `Proj R[T₀,…,Tₙ]`, reduced in `../ProjQuotientSaturationKer/Basic.lean` to an
equality of kernels of ring homomorphisms over the standard opens, computed there over the
standard charts, and assembled — over an arbitrary coefficient ring — by
`Stacks.ClosedSubschemeProjectiveSpace.closedSubscheme_iso_projQuotient` in
`../ClosedSubschemeProjectiveSpace/Basic.lean`, which is where that assertion is registered.
**No attribute is attached and no `add_to_stacks` registration is made here**, because the
comparison is a definition in the statement of Tag 03GL and is not one of its three labelled
assertions.

## References

* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Tag03GLComparisonAudit

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The four abbreviations, pinned to their constructions -/

/-- The integral model of projective `n`-space is `Proj` of the integral polynomial grading. -/
public theorem projectiveSpaceAtUniverse_eq_proj :
    AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n =
      AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
  rfl

/-- Projective `n`-space over a ring is the fibre product of `Spec R` with the integral model
over the terminal scheme. -/
public theorem projectiveSpaceOverRing_eq_pullback (A : CommRingCat.{u}) :
    AlgebraicGeometry.projectiveSpaceOverRing n A =
      pullback (terminal.from (Spec A))
        (terminal.from (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)))) :=
  rfl

/-- The projection of projective space over `S` to the integral model is the second pullback
projection. -/
public theorem toIntegralAtUniverse_eq_pullbackSnd (S : Scheme.{u}) :
    AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n S =
      pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) :=
  rfl

/-- Tag 01MY's domain of definition is the supremum of the standard opens `D₊(ψ f)` over the
homogeneous `f` of positive degree. -/
public theorem mapDomain_eq_iSup_basicOpen
    (ψ : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) :
    Stacks.AlgebraicGeometry.ProjShared.mapDomain
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ψ =
      ⨆ (d : ℕ) (_hd : 0 < d)
          (f : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) d),
        AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (ψ f) :=
  rfl

/-! ### The comparison -/

/-- **The coordinate-pinned comparison of the two models of projective `n`-space over `R`.**
There is a graded ring homomorphism from the integral polynomial grading to the polynomial
grading over `R` which is the canonical coefficient map on polynomials — so it preserves each
named homogeneous coordinate — whose Tag 01MY domain of definition is all of
`Proj R[T₀,…,Tₙ]`, together with an isomorphism from the base-change model
`Spec R ×_* Proj (ULift ℤ)[T₀,…,Tₙ]` to `Proj R[T₀,…,Tₙ]` commuting both with the projection
to the integral model and with the projection to `Spec R`.

Every object in the statement is written out as the construction it is, so that the statement
mentions no bundling structure, no model-of-projective-space abbreviation and no named domain
of definition. -/
public theorem exists_coordinatePinnedComparison :
    ∃ coordinateMap :
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) →+*ᵍ
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R,
      (∀ F : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ),
          coordinateMap F =
            MvPolynomial.map ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom) F) ∧
      ∃ hdom : (⨆ (d : ℕ) (_hd : 0 < d)
            (f : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) d),
          AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (coordinateMap f)) = ⊤,
        ∃ iso : pullback (terminal.from (Spec (CommRingCat.of R)))
              (terminal.from (AlgebraicGeometry.Proj
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)))) ≅
            AlgebraicGeometry.Proj
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
          (iso.hom ≫ ((Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ hdom.symm).hom ≫
              Stacks.AlgebraicGeometry.ProjTwistChain.mapHom _ _ coordinateMap) =
            pullback.snd _ _) ∧
          (iso.hom ≫ AlgebraicGeometry.Proj.toSpecZero
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≫
              Spec.map (CommRingCat.ofHom
                ((GradedRing.projZeroRingHom'
                  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).comp
                  (algebraMap R (MvPolynomial (Fin (n + 1)) R)))) =
            pullback.fst _ _) :=
  ⟨(Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).coordinateMap,
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).coordinateMap_apply,
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).domain_eq_top,
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).iso,
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).toIntegral,
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).toBase⟩

end Stacks.Tag03GLComparisonAudit

end
