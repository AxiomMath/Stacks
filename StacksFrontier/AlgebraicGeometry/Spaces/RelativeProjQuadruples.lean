module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Union
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The functor of quadruples of the relative Proj of an algebraic space

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `𝒜` be a quasi-coherent
graded `𝒪_X`-algebra.  The relative homogeneous spectrum of `𝒜` is the functor whose value on a
test scheme `T` is the set of equivalence classes of quadruples `(d, f : T → X, ℒ, ψ)`: an
integer `d ≥ 1`, a `T`-point `f` of `X`, an invertible `𝒪_T`-module `ℒ`, and a homomorphism of
graded `𝒪_T`-algebras `ψ : f^*𝒜^{(d)} ⟶ ⨁_{n ≥ 0} ℒ^{⊗ n}` whose degree-one component
`f^*𝒜_d ⟶ ℒ` is surjective.  Two quadruples of one degree are identified when an isomorphism of
`ℒ` carries `ψ` to `ψ'`, and quadruples of different degrees when their restrictions to a common
multiple of the degrees are so carried.

This file constructs that set, for every test object of the ambient big fppf site.

## Main definitions

* `AlgebraicGeometry.Space.GradedAlgebraPoints` is the restriction of a quasi-coherent graded
  `𝒪_X`-algebra to the scheme points of `X`: a quasi-coherent graded algebra `f^*𝒜` on the
  scheme of `T` for every object `T` of the site and every `T`-point `f` of `X`.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.Quadruples` is the type of quadruples of a fixed
  degree over a fixed `T`-point of `X`.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F` is **the value `F(T)` on a test object** of
  the functor of quadruples: the union over `d ≥ 1` of the sets of quadruples of degree `d`,
  fibred over the `T`-points of `X`.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.mk` is the point of `F(T)` of a quadruple of
  positive degree, and `GradedAlgebraPoints.F.point` the `T`-point of `X` it lies over.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.toSchemeF` compares `F(T)` with the
  scheme-level functor of quadruples of the restricted algebra.

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.mk_eq_mk_of_strictlyEquivalent`: strictly
  equivalent quadruples of one degree have the same point of `F(T)`.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.mk_eq_mk_of_equivalent`: equivalent quadruples
  of possibly different degrees have the same point of `F(T)`.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.exists_quadruple`: every point of `F(T)` comes
  from a quadruple of some positive degree, so the quadruples of the several degrees jointly
  cover `F(T)`.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.point_mk`: the point of `X` a quadruple lies
  over is the morphism the quadruple records.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.toSchemeF_injective` and
  `GradedAlgebraPoints.F.toSchemeF_mk`: over a fixed `T`-point `f` of `X` the set of quadruples
  is exactly the fibre over the identity of the scheme-level set of quadruples of `f^*𝒜`.

## Implementation notes

**The quadruples are the scheme-level ones.**  A quadruple over a `T`-point `f` of `X` is a
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple` for the graded algebra `f^*𝒜` on the
scheme of `T` and for the identity morphism of that scheme.  The source's `ψ` is a map out of
`f^*𝒜^{(d)}`, and `f^*𝒜` is already what the restriction supplies, so the morphism along which
the scheme-level quadruple pulls its algebra back is the identity; pullback along the identity
is isomorphic, though not equal, to the identity functor.  Taking the quadruples in that form
is what makes the two identifications available here with no further work: strict equivalence
inside a degree and the equivalence of Tag 01NW across degrees are
`...RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent` and `...Quadruple.Equivalent`, and the
union is their quotient `...RelativeProjQcohSheaf.UnionRel`, so the content of Tag 01NW holds
in `F(T)` by construction.

**The restriction `f^*𝒜` is a datum.**  The family of restrictions is taken as data, exactly as
the field `AlgebraicGeometry.Space.RelativeProjPoints.algebra` takes it.  Nothing below uses any
property of the family, so no statement here is weakened by its being assumed; what the
assumption costs is that `F` is attached to the family rather than to `𝒜`.

This is *not* because the restriction is unavailable.  It is available: the pullback of modules
along an arbitrary morphism of algebraic spaces is
`AlgebraicGeometry.Space.modulePullback` (Stacks 03LU), it preserves quasi-coherence with no
hypothesis on the morphism by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`
(Stacks 03GA), its graded counterpart is `Stacks.Sheaves.GradedAlgebraPullback.gradedPull` at
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` (Stacks 0FQX), and the restriction of a
graded algebra on `X` to an étale scheme chart is
`AlgebraicGeometry.Space.relativeProjChartAlgebra`, which lands in a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` — Situation 01NN on the chart.
A scheme point `f : yoneda.obj T ⟶ X` is handled by pulling back along `f` and then restricting
at the identity chart `AlgebraicGeometry.Space.idEtaleChart` of `T`, the device
`AlgebraicGeometry.Space.baseChangeModule` uses in the single-module case, with the
quasi-coherence of that last step supplied by
`...isQuasicoherent_restrictToChartScheme_idEtaleChart`.

What stands in the way of assembling those into the family is narrower, and is recorded here so
it is not mistaken for the whole construction: the chart restriction is stated for
`SheafOfModules.GradedAlgebra.{u, u, u, u + 1}` and `modulePullback` for `Modules.{u, u}`, while
the homogeneous pieces of `AlgebraicGeometry.Space.RelativeProjSituation` live at
`.{u, m, u, u + 1}` with `m` a free universe, so the chain runs only at `m = u`; and the
comparison `g^*(f^*𝒜) ≅ (f ∘ g)^*𝒜`, which exists on the small étale site as
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso` for arbitrary morphisms, is not
transported through the chart restriction to an isomorphism of graded algebras on the schemes.

**`F` is the value of the functor, not the functor.**  The restriction map of the functor along
a morphism `T' ⟶ T` of test objects is the pullback of a quadruple *together with* the
comparison of the restrictions of `𝒜` along a scheme point and along its composite with
`T' ⟶ T`, and it is the second of those that the datum below does not carry.  The pullback of a
quadruple is not the obstruction: at the level of schemes it is constructed, as
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.pullback`, with both functor laws
(`...F.pullback_id` and `...F.pullback_comp`) and assembled into the presheaf
`...RelativeProjQcohSheaf.F.functor` on all test schemes, and its main input, the compatibility
of the comparison `k^*(ℒ^{⊗ n}) ≅ (k^*ℒ)^{⊗ n}` of the integral tensor powers of an invertible
module with the coherent multiplication of Tag 01CU, is proved in every integral bidegree by
`StacksDraft.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback.pieceIso_mul`.  The
inverse limit over the quasi-compact opens by which the source extends `F` from quasi-compact
test schemes to all of them is likewise constructed at the level of schemes, as
`...RelativeProjQcohSheaf.F.limFunctor`, and agrees with the union on a quasi-compact test
scheme by `...RelativeProjQcohSheaf.F.limEquiv`.  So what is built here is the value of the
functor on every test object and not the functor, and the one input that is missing is the
comparison of the restrictions of `𝒜` along two scheme points — which is itself a clause of
Stacks 084B.

**The fibration over the points of `X`.**  The identifications relate only quadruples over one
and the same `T`-point of `X`, so `F(T)` is a sigma type over the `T`-points of `X` with the
union of the quadruples of positive degree in each fibre.  A `T`-point of `X` is a morphism
`yoneda.obj T ⟶ X`, which is the library's spelling throughout `Spaces/`; for a sheaf `X` it is
the same thing as an element of `X(T)`.

## References

* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The restriction of a quasi-coherent graded `𝒪_X`-algebra to the scheme points of `X`.**

For every object `T` of the big fppf site and every `T`-point `f` of `X`, a graded algebra on
the scheme underlying `T`: the restriction `f^*𝒜` of Situation 0849's algebra along `f`.

This is the datum from which the functor of quadruples of Tag 084A is built, and it is the same
datum as the field `AlgebraicGeometry.Space.RelativeProjPoints.algebra`. -/
structure GradedAlgebraPoints (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The restriction of the graded algebra to a scheme point of `X`. -/
  algebra (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)

namespace GradedAlgebraPoints

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : GradedAlgebraPoints B S hS X)

/-- **The quadruples of degree `d` over a `T`-point `f` of `X`.**

The pair `(ℒ, ψ)` of Section 01NS for the restricted algebra `f^*𝒜` on the scheme of `T`: an
invertible `𝒪_T`-module `ℒ` and a homomorphism of graded algebras
`ψ : f^*𝒜^{(d)} ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}` whose degree-one component is surjective. -/
abbrev Quadruples (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (d : ℤ) :=
  Quadruple (𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (r.algebra T f) d

/-- **Stacks 084A.** The value `F(T)` on a test object of the functor of quadruples of the
relative homogeneous spectrum of a quasi-coherent graded `𝒪_X`-algebra: the union over `d ≥ 1`
of the sets of quadruples `(d, f : T → X, ℒ, ψ)` of degree `d`, modulo strict equivalence inside
a degree and the equivalence of Tag 01NW across degrees.

The identifications relate only quadruples over the same `T`-point of `X`, so the set is fibred
over the `T`-points of `X`, which is the morphism a quadruple records. -/
@[stacks 084A "the value F(T) of the functor on a test object, as the union over d ≥ 1 of the \
quadruples (d, f : T → X, L, psi) modulo strict equivalence inside a degree and the \
equivalence of Tag 01NW across degrees, the restriction of the graded algebra to the scheme \
points of X being a datum; the functoriality in the test object and the inverse limit over \
the quasi-compact opens are not constructed, the pullback of a quadruple not being available"]
def F (T : BigFppfOver B S hS) : Type (u + 1) :=
  Σ f : yoneda.obj T ⟶ X,
    Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T f))

/-- The point of `F(T)` of a quadruple of positive degree over a `T`-point `f` of `X`. -/
def F.mk {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X) {d : ℤ} (hd : 0 < d)
    (P : r.Quadruples T f d) : r.F T :=
  ⟨f, Quot.mk _ ⟨⟨d, hd⟩, P⟩⟩

/-- The `T`-point of `X` a point of `F(T)` lies over. -/
def F.point {T : BigFppfOver B S hS} (ξ : r.F T) : yoneda.obj T ⟶ X := ξ.1

/-- The point of `F(T)` of a quadruple over `f` lies over `f`. -/
@[simp] theorem F.point_mk {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X) {d : ℤ} (hd : 0 < d)
    (P : r.Quadruples T f d) : F.point r (F.mk r f hd P) = f :=
  rfl

/-- Strictly equivalent quadruples of one degree have the same point of `F(T)`. -/
theorem F.mk_eq_mk_of_strictlyEquivalent {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X)
    {d : ℤ} (hd : 0 < d) {P Q : r.Quadruples T f d} (h : Quadruple.StrictlyEquivalent P Q) :
    F.mk r f hd P = F.mk r f hd Q :=
  congrArg (fun q => (⟨f, q⟩ : r.F T)) (Quot.sound (UnionRel.strict h))

/-- **The identification of Tag 01NW, inside `F(T)`.** Equivalent quadruples of possibly
different degrees have the same point of `F(T)`. -/
theorem F.mk_eq_mk_of_equivalent {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X)
    {d d' : ℤ} (hd : 0 < d) (hd' : 0 < d') {P : r.Quadruples T f d} {Q : r.Quadruples T f d'}
    (h : Quadruple.Equivalent P Q) : F.mk r f hd P = F.mk r f hd' Q :=
  congrArg (fun q => (⟨f, q⟩ : r.F T)) (Quot.sound (UnionRel.equivalent h))

/-- Every point of `F(T)` comes from a quadruple of some positive degree: the quadruples of the
several positive degrees jointly cover `F(T)`. -/
theorem F.exists_quadruple {T : BigFppfOver B S hS} (ξ : r.F T) :
    ∃ (d : ℤ) (hd : 0 < d) (P : r.Quadruples T (F.point r ξ) d),
      F.mk r (F.point r ξ) hd P = ξ := by
  obtain ⟨f, q⟩ := ξ
  induction q using Quot.ind with
  | _ x => exact ⟨x.1.1, x.1.2, x.2, rfl⟩

/-- **The fibre of `F(T)` over a `T`-point of `X`, inside the scheme-level functor of
quadruples.** The quadruples over `f` are the quadruples of the restricted algebra `f^*𝒜` on the
scheme of `T` over the identity morphism of that scheme, so they form the fibre over the
identity of the scheme-level set of quadruples of Tag 01NX. -/
def F.toSchemeF (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T f))) :
    Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F (r.algebra T f)
      ((BigFppfOver.toScheme B S hS).obj T) :=
  ⟨𝟙 _, q⟩

/-- The fibre of `F(T)` over `f` maps injectively to the scheme-level set of quadruples. -/
theorem F.toSchemeF_injective (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    Function.Injective (F.toSchemeF r T f) := fun _ _ h =>
  eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp h).2

/-- The point of the scheme-level set of quadruples attached to a quadruple of positive degree
is the one the scheme-level construction attaches to it. -/
theorem F.toSchemeF_mk (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) {d : ℤ} (hd : 0 < d)
    (P : r.Quadruples T f d) :
    F.toSchemeF r T f (F.mk r f hd P).2 =
      Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.mk
        (𝟙 ((BigFppfOver.toScheme B S hS).obj T)) hd P :=
  rfl

end GradedAlgebraPoints

end AlgebraicGeometry.Space

end
