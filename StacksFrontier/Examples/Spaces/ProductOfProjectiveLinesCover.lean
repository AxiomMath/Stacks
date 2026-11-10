module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.AffineTransition
public import StacksFrontier.Examples.Spaces.ProductOfProjectiveLines

/-!
# Quasi-compact coverings of the functor of infinite tuples of points of a scheme

Let `P` be a separated scheme and let `q : X ⟶ P` be a morphism from an affine scheme. The
`ι`-fold product `X^ι` exists as a scheme for an arbitrary index type `ι`, because a diagram of
affine schemes has a limit, and it is again affine. Composing its projections with `q` gives a
morphism of presheaves `X^ι ⟶ powPresheaf ι P`, and that morphism is representable and
quasi-compact: every base change of it along a scheme-valued point of `powPresheaf ι P` is a
quasi-compact morphism of schemes.

For `P = ℙ¹` and `ι = ULift ℕ` the target is the functor `(ℙ¹)^∞` of
`StacksFrontier/Examples/Spaces/ProductOfProjectiveLines.lean`, and `q` the standard affine chart
of `ℙ¹`; the functor `(ℙ¹)^∞` therefore receives a quasi-compact representable morphism of
presheaves from an affine scheme.

## Main definitions

* `AlgebraicGeometry.affinePow`: the `ι`-fold product of an affine scheme, an affine scheme.
* `AlgebraicGeometry.affinePowπ`: its projections.
* `AlgebraicGeometry.powCover`: the morphism `X^ι ⟶ powPresheaf ι P` induced by `q : X ⟶ P`.
* `AlgebraicGeometry.projectiveLineChart` and `AlgebraicGeometry.projectiveLineChartι`: the
  standard affine chart of `ℙ¹` and its inclusion.
* `AlgebraicGeometry.projectiveLinePowCover`: that morphism for the standard affine chart of
  `ℙ¹`, with target `(ℙ¹)^∞`.

## Main results

* `AlgebraicGeometry.relativelyRepresentable_powCover`: `powCover q` is representable.
* `AlgebraicGeometry.quasiCompact_presheaf_powCover`: `powCover q` is quasi-compact, in the
  sense of `CategoryTheory.MorphismProperty.presheaf`.
* `AlgebraicGeometry.quasiCompact_presheaf_projectiveLinePowCover` and
  `AlgebraicGeometry.relativelyRepresentable_projectiveLinePowCover`: the two statements for
  `(ℙ¹)^∞`.

## Implementation notes

The `ι`-fold product of an affine scheme is taken from
`AlgebraicGeometry.Scheme.affineLimitCone`, the limit cone of an arbitrary small diagram of
affine schemes, applied to the constant discrete diagram; no finiteness or cofiltration
hypothesis on `ι` is involved, and the apex is affine by
`AlgebraicGeometry.Scheme.isAffine_affineLimitCone_pt`.

Quasi-compactness is checked on the base changes constructed in
`AlgebraicGeometry.powPresheaf.fibre`: the base change of a scheme-valued point `A` along a
scheme-valued point `B` is a closed subscheme of the product of the two source schemes, so it
is quasi-compact over the second factor as soon as the first factor is affine — a closed
immersion is quasi-compact, and the projection away from an affine factor is a base change of
the structure morphism of that factor. Affineness of `X^ι` is what makes this apply, and it is
the only property of `X` used.

### No `@[stacks 078F]`

This file does not discharge any conjunct of tag 078F, so it carries no scoped tag for it. The
third conjunct asks for a morphism to the witness from a scheme that is surjective, flat,
universally open *and* quasi-compact; of those four properties only quasi-compactness is proved
here, and it is proved for the covering by a product of copies of an affine scheme rather than
for the morphism `(SL₂)^∞ ⟶ (ℙ¹)^∞` of the Stacks Project's argument. The remaining three
properties need the morphism `SL₂ ⟶ ℙ¹`, which is not available, and the behaviour of faithful
flatness under infinite fibre products over an arbitrary base scheme; the covering constructed
here is not surjective, since the standard chart of `ℙ¹` misses a point in every component.

## References

* [Stacks Project, Tag 078F](https://stacks.math.columbia.edu/tag/078F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section AffinePow

variable (ι : Type u) (X : Scheme.{u}) [IsAffine X]

/-- Every object of the constant discrete diagram at an affine scheme is affine. -/
instance isAffine_constDiscreteFunctor_obj (j : Discrete ι) :
    IsAffine ((Discrete.functor fun (_ : ι) => X).obj j) :=
  inferInstanceAs (IsAffine X)

/-- The `ι`-fold product of an affine scheme, as a limit cone of the constant discrete diagram
at it: such a limit exists for an arbitrary index type because every object of the diagram is
affine. -/
def affinePowCone : LimitCone (Discrete.functor fun (_ : ι) => X) :=
  Scheme.affineLimitCone _

/-- The `ι`-fold product `X^ι` of an affine scheme `X`, for an arbitrary index type `ι`. -/
def affinePow : Scheme.{u} := (affinePowCone ι X).cone.pt

/-- The `ι`-fold product `X^ι` of an affine scheme `X` is affine. -/
instance isAffine_affinePow : IsAffine (affinePow ι X) :=
  Scheme.isAffine_affineLimitCone_pt _

/-- The `i`-th projection `X^ι ⟶ X`. -/
def affinePowπ (i : ι) : affinePow ι X ⟶ X := (affinePowCone ι X).cone.π.app ⟨i⟩

/-- The morphism to `X^ι` determined by a family of morphisms to `X`. -/
def affinePowLift {W : Scheme.{u}} (f : ι → (W ⟶ X)) : W ⟶ affinePow ι X :=
  (affinePowCone ι X).isLimit.lift (Fan.mk W f)

/-- The morphism determined by a family of morphisms to `X` has that family as its
components. -/
@[reassoc (attr := simp)]
lemma affinePowLift_π {W : Scheme.{u}} (f : ι → (W ⟶ X)) (i : ι) :
    affinePowLift ι X f ≫ affinePowπ ι X i = f i :=
  (affinePowCone ι X).isLimit.fac (Fan.mk W f) ⟨i⟩

/-- Two morphisms to `X^ι` with the same components agree. -/
lemma affinePow_hom_ext {W : Scheme.{u}} {a b : W ⟶ affinePow ι X}
    (h : ∀ i, a ≫ affinePowπ ι X i = b ≫ affinePowπ ι X i) : a = b :=
  (affinePowCone ι X).isLimit.hom_ext fun ⟨i⟩ => h i

end AffinePow

/-- The projection of a product of schemes to its second factor is quasi-compact as soon as the
first factor is affine, being a base change of the structure morphism of that factor. -/
lemma quasiCompact_prod_snd (U V : Scheme.{u}) [IsAffine U] :
    QuasiCompact (prod.snd : U ⨯ V ⟶ V) := by
  have h := IsPullback.of_isLimit_binaryFan_of_isTerminal (prodIsProd U V) terminalIsTerminal
  simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at h
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback h inferInstance

namespace powPresheaf

variable {ι : Type u} {P : Scheme.{u}} [P.IsSeparated] {U V : Scheme.{u}} [IsAffine U]
  (A : yoneda.obj U ⟶ powPresheaf ι P) (B : yoneda.obj V ⟶ powPresheaf ι P)

omit [IsAffine U] in
/-- The inclusion of the base change of two scheme-valued points into the product of their
source schemes is a closed immersion. -/
instance isClosedImmersion_fibreι : IsClosedImmersion (fibreι A B) :=
  inferInstanceAs (IsClosedImmersion (interEqualizerι ..))

/-- The base change of a scheme-valued point of `powPresheaf ι P` along another one is
quasi-compact over the second one as soon as the first source scheme is affine: it is a closed
subscheme of the product of the two sources, and the projection of that product away from an
affine factor is quasi-compact. -/
instance quasiCompact_fibreι_comp_snd : QuasiCompact (fibreι A B ≫ prod.snd) :=
  have : QuasiCompact (fibreι A B) := inferInstance
  have : QuasiCompact (prod.snd : U ⨯ V ⟶ V) := quasiCompact_prod_snd U V
  inferInstance

end powPresheaf

section PowCover

variable {ι : Type u} {X P : Scheme.{u}} [IsAffine X] [P.IsSeparated] (q : X ⟶ P)

/-- The morphism of presheaves from the `ι`-fold product of an affine scheme `X` to
`powPresheaf ι P` induced by a morphism `q : X ⟶ P`: its `i`-th component is the `i`-th
projection of `X^ι` followed by `q`. -/
def powCover : yoneda.obj (affinePow ι X) ⟶ powPresheaf ι P :=
  yonedaEquiv.symm fun i => affinePowπ ι X i ≫ q

omit [P.IsSeparated] in
/-- The components of `AlgebraicGeometry.powCover`. -/
@[simp]
lemma yonedaEquiv_powCover (i : ι) :
    yonedaEquiv (powCover (ι := ι) q) i = affinePowπ ι X i ≫ q := by
  have h : yonedaEquiv (powCover (ι := ι) q) = fun i => affinePowπ ι X i ≫ q :=
    yonedaEquiv.apply_symm_apply _
  rw [h]

/-- The covering morphism of `powPresheaf ι P` attached to a morphism from an affine scheme is
a representable morphism of presheaves. -/
theorem relativelyRepresentable_powCover :
    yoneda.relativelyRepresentable (powCover (ι := ι) q) :=
  relativelyRepresentable_yonedaEquiv_symm_powPresheaf _ _

/-- The covering morphism of `powPresheaf ι P` attached to a morphism from an affine scheme is
quasi-compact: it is representable, and every base change of it along a scheme-valued point of
`powPresheaf ι P` is a quasi-compact morphism of schemes. -/
theorem quasiCompact_presheaf_powCover :
    MorphismProperty.presheaf (C := Scheme.{u}) @QuasiCompact (powCover (ι := ι) q) :=
  have : MorphismProperty.RespectsIso (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  MorphismProperty.relative.of_exists fun {_} B =>
    ⟨powPresheaf.fibre _ B, yoneda.map (powPresheaf.fibreι _ B ≫ prod.fst),
      powPresheaf.fibreι _ B ≫ prod.snd, powPresheaf.isPullback_fibre _ B, inferInstance⟩

end PowCover

section ProjectiveLinePow

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard affine chart of `ℙ¹`: the spectrum of the degree-zero part of the
localization of `ℤ[T₀, T₁]` at the first homogeneous coordinate, that is, the complement of
the hyperplane `T₀ = 0`. -/
def projectiveLineChart : Scheme.{u} :=
  Spec (.of <| HomogeneousLocalization.Away
    (MvPolynomial.homogeneousSubmodule (Fin 2) (ULift.{u} ℤ)) (MvPolynomial.X 0))

/-- The standard affine chart of `ℙ¹` is affine. -/
instance isAffine_projectiveLineChart : IsAffine projectiveLineChart.{u} :=
  inferInstanceAs (IsAffine (Spec _))

/-- The first homogeneous coordinate of `ℤ[T₀, T₁]` is homogeneous of degree one. -/
lemma mvPolynomialX_mem_homogeneousSubmodule_one :
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) (ULift.{u} ℤ)) ∈
      MvPolynomial.homogeneousSubmodule (Fin 2) (ULift.{u} ℤ) 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _)

/-- The standard affine chart of `ℙ¹` is an open subscheme of it: the first homogeneous
coordinate is homogeneous of degree one, which is positive. -/
def projectiveLineChartι : projectiveLineChart.{u} ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  Proj.awayι _ (MvPolynomial.X 0) mvPolynomialX_mem_homogeneousSubmodule_one.{u} Nat.one_pos

/-- The inclusion of the standard affine chart of `ℙ¹` into `ℙ¹` is an open immersion. -/
instance isOpenImmersion_projectiveLineChartι :
    IsOpenImmersion projectiveLineChartι.{u} :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι ..))

/-- The covering morphism of `(ℙ¹)^∞` attached to the standard affine chart of `ℙ¹`: the
`ULift ℕ`-fold product of that chart, mapping to `(ℙ¹)^∞` by the chart inclusion in every
component. -/
def projectiveLinePowCover :
    yoneda.obj (affinePow (ULift.{u} ℕ) projectiveLineChart.{u}) ⟶ projectiveLinePow.{u} :=
  powCover projectiveLineChartι.{u}

/-- `(ℙ¹)^∞` receives a representable morphism of presheaves from an affine scheme. -/
theorem relativelyRepresentable_projectiveLinePowCover :
    yoneda.relativelyRepresentable projectiveLinePowCover.{u} :=
  relativelyRepresentable_powCover _

/-- That morphism is quasi-compact: every base change of it along a scheme-valued point of
`(ℙ¹)^∞` is a quasi-compact morphism of schemes. -/
theorem quasiCompact_presheaf_projectiveLinePowCover :
    MorphismProperty.presheaf (C := Scheme.{u}) @QuasiCompact projectiveLinePowCover.{u} :=
  quasiCompact_presheaf_powCover _

end ProjectiveLinePow

end AlgebraicGeometry

end
