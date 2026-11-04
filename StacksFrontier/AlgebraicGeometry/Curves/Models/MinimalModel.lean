module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularProperModel
public import StacksFrontier.AlgebraicGeometry.Models.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve

/-!
# Minimal models of smooth projective curves

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth projective
curve over `K` with `H⁰(C, 𝒪_C) = K`. A *minimal model* of `C` is a regular, proper model
`X ⟶ Spec(R)` of `C` whose total space contains no exceptional curve of the first kind.

## Main definitions

* `AlgebraicGeometry.Scheme.HasExceptionalCurveOfFirstKind` — a scheme contains an exceptional
  curve of the first kind, i.e. the bare property obtained from
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` by quantifying over the
  closed subscheme, the field and the presentation of the subscheme as a projective line.
* `Stacks.Models.IsMinimalModel` — the property of being a minimal model.

## Main results

* `Stacks.Models.RegularProperModelSituation.isMinimalModel` — a regular proper model situation
  whose total space contains no exceptional curve of the first kind is a minimal model.

## Implementation notes

The notion of a model is the one of Tag 0C2S, `Stacks.Models.IsModel`: a flat finite-type
`R`-scheme together with an identification of its generic fibre with `C`. This is the notion the
neighbouring Tag 0C2U is stated against, so minimality is a property of the triple `(c, p, e)`
rather than of the bundled situation of Tag 0C61; the bridge to that situation is
`RegularProperModelSituation.isMinimalModel`.

The hypotheses on the curve — smooth, projective, one-dimensional, and with no global functions
beyond the constants — are carried by the definition itself, as instance arguments where the
library has a class for them (`AlgebraicGeometry.IsCurve`, `AlgebraicGeometry.Smooth`) and as
fields otherwise. This matches `RegularProperModelSituation`, which carries projectivity and
the condition `H⁰(C, 𝒪_C) = K` as fields in the same two shapes.

Tag 0C2I states the notion of an exceptional curve of the first kind for a Noetherian scheme.
No Noetherian hypothesis is imposed here, following
`Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`; the total space of a model is of finite
type over `R`, hence Noetherian, so nothing is lost at the point of use.

## References

* [Stacks Project, Tag 0C2V](https://stacks.math.columbia.edu/tag/0C2V)
* [Stacks Project, Section 0C2I](https://stacks.math.columbia.edu/tag/0C2I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme *contains an exceptional curve of the first kind* when some closed subscheme of it
is an effective Cartier divisor isomorphic to the projective line over some field, under an
isomorphism pulling the normal sheaf back to `𝒪(-1)`. -/
public def Scheme.HasExceptionalCurveOfFirstKind (X : Scheme.{u}) : Prop :=
  ∃ (k : Type u) (hk : Field k) (D : X.IdealSheafData)
    (e : @projectiveLineProj k hk ≅ D.subscheme),
      @Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind X D k hk e

end AlgebraicGeometry

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Stacks Project, Tag 0C2V.** A *minimal model* of a smooth projective curve `C` over `K`
with `H⁰(C, 𝒪_C) = K` is a regular, proper model `X ⟶ Spec(R)` of `C` such that `X` contains no
exceptional curve of the first kind. -/
@[stacks 0C2V "a minimal model of a smooth projective curve"]
public structure IsMinimalModel {C X : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c]
    [Smooth c] (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) : Prop where
  /-- The curve is projective over its ground field. -/
  curveProjective : Stacks.HProjective.IsHProjective c
  /-- The canonical homomorphism from the ground field to the global functions of the curve is
  an isomorphism, i.e. `H⁰(C, 𝒪_C) = K`. -/
  isIso_globalSections : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)
  /-- The morphism `p`, with the identification `e` of its generic fibre, is a model of `C`. -/
  isModel : IsModel c p e
  /-- The model is proper over the discrete valuation ring. -/
  isProper : IsProper p
  /-- The total space of the model is regular. -/
  regular : IsRegular X
  /-- The total space of the model contains no exceptional curve of the first kind. -/
  not_hasExceptionalCurveOfFirstKind : ¬ X.HasExceptionalCurveOfFirstKind

/-- The regular proper model of Tag 0C61 is a minimal model as soon as its total space contains
no exceptional curve of the first kind. -/
public theorem RegularProperModelSituation.isMinimalModel (S : RegularProperModelSituation.{u})
    (hS : ¬ S.X.HasExceptionalCurveOfFirstKind) :
    IsMinimalModel S.C_to_K S.X_to_R S.genericFiberIso where
  curveProjective := S.curveProjective
  isIso_globalSections := S.isIso_globalSections
  isModel := ⟨S.flat, S.locallyOfFiniteType, S.quasiCompact, S.genericFiberIso_over_K⟩
  isProper := S.modelProper
  regular := S.regular
  not_hasExceptionalCurveOfFirstKind := hS

end Stacks.Models

end
