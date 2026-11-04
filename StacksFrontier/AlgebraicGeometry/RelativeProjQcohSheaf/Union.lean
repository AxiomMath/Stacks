module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Equivalence

/-!
# The functor represented by relative Proj: the union over the degrees

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN). Section 01NS attaches to
each integer `d ≥ 1` the functor `F_d` of strict equivalence classes of quadruples
`(d, f : T → S, L, ψ)`, and for `d' = a d` a transformation `F_d → F_{d'}` sending the quadruple
`(d, f, L, ψ)` to `(d', f, L^{⊗ a}, ψ|_{f^*𝒜^{(d')}})`. Tag 01NW says that two quadruples have
the same image under these transformations exactly when they are *equivalent*, so the
transformations are injective and the colimit of the system is the union

`F(T) = ⋃_{d ∈ ℕ} F_d(T)`

of the sets `F_d(T)` inside it. That union, and its extension to an arbitrary test scheme by
the inverse limit over the quasi-compact opens, is the functor `F : Sch^{opp} ⟶ Sets` of the
display 01NX, whose representability is Tag 01NY.

This file constructs the union. A point of `F(T)` over a morphism `f : T ⟶ S` is a quadruple of
some positive degree over `f`, taken up to the identifications that the union makes: strict
equivalence inside a single degree, which is already the identification defining `F_d(T)`, and
equivalence of quadruples of different degrees, which is the identification of Tag 01NW. Both
are constructors of `UnionRel`, so both hold in `F(T)` by construction, and the canonical map
`F_d(T) → F(T)` is therefore defined for every `d ≥ 1`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.PositiveQuadruple`: a quadruple over a test
  scheme of some **positive** degree, the degree being part of the datum. This is the disjoint
  union over `d ≥ 1` of the quadruples of degree `d`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.UnionRel`: the identifications the union
  makes — strict equivalence inside one degree, and equivalence across degrees.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F`: **the value `F(T)` of the functor of the
  display 01NX**, the union over `d ≥ 1` of the sets `F_d(T)`, fibred over the morphisms
  `T ⟶ S`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.mk`: the point of `F(T)` of a quadruple of
  positive degree, and `Fd.toF` the canonical map `F_d(T) → F(T)`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.mk_eq_mk_of_strictlyEquivalent`: strictly
  equivalent quadruples of one degree have the same point of `F(T)`, which is what makes
  `Fd.toF` well defined.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.mk_eq_mk_of_equivalent`: **equivalent
  quadruples of possibly different degrees have the same point of `F(T)`**, the identification
  of Tag 01NW.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.toF_mk`: the canonical map `F_d(T) → F(T)`
  sends the class of a quadruple to its point, so the `F_d(T)` jointly cover `F(T)`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.exists_quadruple`: every point of `F(T)`
  comes from a quadruple of some positive degree.

## Implementation notes

The union is taken as `Quot UnionRel` rather than as a `Quotient` because the transitivity of
`UnionRel` across three different degrees is not available *here*: it needs the implication (3)
implies (1) of Tag 01NW, which is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.lcm_compatible_of_exists_compatible`
of `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.EquivalenceDescent`, and it needs the
transitions `F_d → F_{a d}`, which are built in modules downstream of this one. `Quot` of a
relation is the quotient by the equivalence relation it generates, so the construction is
unaffected, and the two identifications the source makes hold in `F(T)` by `Quot.sound`.

`UnionRel` **is** an equivalence relation, so the quotient below is the quotient by the two
identifications the source makes and nothing more: that is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.unionRel_equivalence` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionEquivalenceRelation`, where the
relation is identified with cofinal equality in a common multiple of the two degrees. The
converse of the two theorems below — that two quadruples with the same point of `F(T)` *are*
equivalent, and strictly equivalent when their degrees agree — is
`...RelativeProjQcohSheaf.F.mk_eq_mk_iff_equivalent` and `...F.mk_eq_mk_iff_strictlyEquivalent`
there, and the injectivity of the transformations `F_d → F_{d'}` that the source asserts is
`...RelativeProjQcohSheaf.Fd.scale_injective`. Neither Tag 01NB nor Tag 01NU is used for any of
it.

`UnionRel` is an inductive relation with one constructor per identification rather than a
disjunction of the two. A disjunction would have to compare the degrees of its two arguments,
and the quadruples of different degrees have different types, so stating "the degrees agree and
the quadruples are strictly equivalent" would need a transport of a quadruple along an equality
of degrees; the inductive form has the degrees match by unification instead and needs no
transport, which is what keeps `Fd.toF` free of bookkeeping.

The degree is carried as a `Subtype` of `ℤ`, so that a point of `F(T)` records a positive degree
and `UnionRel` never relates a quadruple of degree `0` or of negative degree. Section 01NS fixes
`d ≥ 1`, and the union of the display is over the positive integers.

## Not done here

* **`F` is not made a functor here, and the inverse limit over the quasi-compact opens is not
  constructed here.** The map `F(T) → F(T')` of a morphism `g : T' ⟶ T` of test schemes is
  built in `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionPullback`, out of the
  pullback of a quadruple of `...RelativeProjQcohSheaf.QuadruplePullback` and the proof that it
  respects both identifications below; its two functor laws, and the functor they assemble into,
  are `...RelativeProjQcohSheaf.UnionFunctor`. Its main input, the comparison
  `k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` of the **integral** tensor powers of an invertible module
  compatibly with the coherent multiplication of Tag 01CU, is available in every integral
  bidegree both as `...LaurentPullback.pieceIso_mul` and as the `laurentPullback_mul` used here;
  these two are the same statement about the same comparison and one of them should be removed,
  routing consumers to `pieceIso_mul`. So what is built here is the value of the functor on a
  test scheme, for every test scheme, and not the functor. The inverse limit over the
  quasi-compact opens is `...RelativeProjQcohSheaf.F.limFunctor` of
  `...RelativeProjQcohSheaf.UnionRepresentable`.
* **The transformations `F_d → F_{d'}` of the source are not constructed here.** Sending
  `(d, f, L, ψ)` to `(d', f, L^{⊗ a}, ψ|_{f^*𝒜^{(d')}})` is
  `...RelativeProjQcohSheaf.Quadruple.scale`, descended to the classes as
  `...RelativeProjQcohSheaf.Fd.scale` in `...RelativeProjQcohSheaf.PowerTransitionDescent` and
  packaged as a morphism of functors `...RelativeProjQcohSheaf.Fd.scaleNat` in
  `...RelativeProjQcohSheaf.PowerTransitionPullback`. The union above is built from the
  identifications directly, which is equivalent to building it from the transformations
  precisely because of Tag 01NW, and is how the source describes `F(T)` as a set.
* No statement that a point of `F(T)` determines its degree up to the identifications. The
  injectivity of `Fd.toF`, which is the sense in which the `F_d(T)` are *subsets* of the union,
  is `...RelativeProjQcohSheaf.Fd.toF_injective` of
  `...RelativeProjQcohSheaf.UnionEquivalenceRelation`.
* Quasi-compactness of `T` plays no role: the union is formed for every test scheme. For a
  quasi-compact `T` this is the source's `F(T)`; for a general `T` the source's `F(T)` is
  instead the inverse limit of these over the quasi-compact opens, which is
  `...RelativeProjQcohSheaf.F.limFunctor`.

## References

* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S T : Scheme.{u}}

/-- A quadruple over the test scheme `T` of some **positive** degree, the degree being part of
the datum: the disjoint union over `d ≥ 1` of the quadruples of degree `d` over `f`. -/
def PositiveQuadruple (f : T ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) :=
  Σ d : {d : ℤ // 0 < d}, Quadruple f A d.1

/-- The identifications made by the union `⋃_{d} F_d(T)`: two quadruples of the **same** degree
are identified when they are strictly equivalent, which is the identification already defining
`F_d(T)` (Section 01NS), and two quadruples of **possibly different** degrees are identified
when they are equivalent, which is the identification of Tag 01NW. -/
inductive UnionRel {f : T ⟶ S}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} :
    PositiveQuadruple f A → PositiveQuadruple f A → Prop
  /-- Strictly equivalent quadruples of one degree are identified. -/
  | strict {d : {d : ℤ // 0 < d}} {P Q : Quadruple f A d.1} :
      Quadruple.StrictlyEquivalent P Q → UnionRel ⟨d, P⟩ ⟨d, Q⟩
  /-- Equivalent quadruples of possibly different degrees are identified. -/
  | equivalent {d d' : {d : ℤ // 0 < d}} {P : Quadruple f A d.1} {Q : Quadruple f A d'.1} :
      Quadruple.Equivalent P Q → UnionRel ⟨d, P⟩ ⟨d', Q⟩

/-- **Stacks Project, display 01NX.** The value `F(T)` of the functor `F : Sch^{opp} ⟶ Sets` of
relative Proj on a test scheme `T`: the union over `d ≥ 1` of the sets `F_d(T)` of Section
01NS, that is, the quadruples over `T` of positive degree modulo strict equivalence inside a
degree and equivalence across degrees.

As for `F_d`, the identifications relate only quadruples over the same morphism `f : T ⟶ S`, so
the set is fibred over the morphisms `T ⟶ S`, which is the morphism recorded by a quadruple. -/
def F (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (T : Scheme.{u}) : Type (u + 1) :=
  Σ f : T ⟶ S, Quot (UnionRel (f := f) (A := A))

/-- The point of `F(T)` of a quadruple of positive degree over `f : T ⟶ S`. -/
def F.mk {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (f : T ⟶ S) {d : ℤ} (hd : 0 < d) (P : Quadruple f A d) : F A T :=
  ⟨f, Quot.mk _ ⟨⟨d, hd⟩, P⟩⟩

/-- Quadruples related by `UnionRel` give equal points of `F(T)`. -/
private theorem mk_eq_mk_of_unionRel
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    {f : T ⟶ S} {x y : PositiveQuadruple f A} (h : UnionRel x y) :
    (⟨f, Quot.mk _ x⟩ : F A T) = ⟨f, Quot.mk _ y⟩ :=
  congrArg (fun q => (⟨f, q⟩ : F A T)) (Quot.sound h)

/-- Strictly equivalent quadruples of one degree have the same point of `F(T)`. -/
theorem F.mk_eq_mk_of_strictlyEquivalent
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    {f : T ⟶ S} {d : ℤ} (hd : 0 < d) {P Q : Quadruple f A d}
    (h : Quadruple.StrictlyEquivalent P Q) : F.mk f hd P = F.mk f hd Q :=
  mk_eq_mk_of_unionRel (UnionRel.strict h)

/-- **Stacks Project, Tag 01NW, the identification made by the union.** Equivalent quadruples
of possibly different degrees have the same point of `F(T)`. -/
theorem F.mk_eq_mk_of_equivalent
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    {f : T ⟶ S} {d d' : ℤ} (hd : 0 < d) (hd' : 0 < d') {P : Quadruple f A d}
    {Q : Quadruple f A d'} (h : Quadruple.Equivalent P Q) : F.mk f hd P = F.mk f hd' Q :=
  mk_eq_mk_of_unionRel (UnionRel.equivalent h)

/-- **The canonical map `F_d(T) → F(T)`**, for `d ≥ 1`: a strict equivalence class of
quadruples of degree `d` is a point of the union. It is well defined by
`F.mk_eq_mk_of_strictlyEquivalent`. -/
def Fd.toF {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    {d : ℤ} (hd : 0 < d) (ξ : Fd A d T) : F A T :=
  ⟨ξ.1, Quot.lift (fun P => Quot.mk (UnionRel (f := ξ.1) (A := A)) ⟨⟨d, hd⟩, P⟩)
    (fun _ _ h => Quot.sound (UnionRel.strict h)) ξ.2⟩

/-- The canonical map `F_d(T) → F(T)` sends the class of a quadruple of degree `d` to its point
of `F(T)`. -/
@[simp] theorem Fd.toF_mk
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    {d : ℤ} (hd : 0 < d) {f : T ⟶ S} (P : Quadruple f A d) :
    Fd.toF hd (Fd.mk f P) = F.mk f hd P :=
  rfl

/-- Every point of `F(T)` comes from a quadruple of some positive degree: the sets `F_d(T)`
jointly cover the union. -/
theorem F.exists_quadruple
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (ξ : F A T) :
    ∃ (d : ℤ) (hd : 0 < d) (P : Quadruple ξ.1 A d), F.mk ξ.1 hd P = ξ := by
  obtain ⟨f, q⟩ := ξ
  induction q using Quot.ind with
  | _ x => exact ⟨x.1.1, x.1.2, x.2, rfl⟩

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
