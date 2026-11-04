module

public import StacksFrontier.AlgebraicGeometry.ProjF1Reduction.Basic
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PullbackIsos

/-!
# Tag 01O4 consumes two fields of a twist datum, and only in one clause

`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation` is parameterised by a
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, which has nine fields: the glued graded
algebra, its quasi-coherence, commutativity of its product, the chart identifications, the
graded-algebra property of those identifications, the homogeneous-section map, and the unit,
multiplicativity and chart description of that map. Tag 01O4 uses the twist datum only to
*normalise* the representing bijections at the identity of relative Proj, and this file measures
exactly how much of the datum that normalisation sees.

Two measurements, each discharged by a declaration below rather than asserted.

**The normalisation clause reads only `algebra` and `ψ`.**
`Stacks.AlgebraicGeometry.ProjF1Normalisation.TwistNormalisation` is the two-field datum, and
`isCanonicalTwistPair_eq_isCanonicalTwistPairOf` is a `rfl`: the canonicality predicate at a
twist datum *is* the predicate at its normalisation. Seven fields are therefore invisible to the
statement of Tag 01O4 — in particular `chartData` and `isGradedChartIso`, which
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.isGradedChartIso` settles for the glued twists, and
`isQuasicoherent`, `mul_comm`, `ψ_one`, `ψ_mul` and `ψ_chart`. A whole twist datum for an
arbitrary quasi-coherent graded algebra is
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, so the parameter `D` below
is one a caller can supply.

**And the normalisation clause is one field of seven.** The other six fields of
`F1Representation` — the universal pair, the representing bijections, their normalisation at the
identity, the pullback of classes, its computation by a representative, and naturality — do not
mention the twist datum at all.
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle` is that twist-datum-free part, which
`F1Representation` now extends, and
`representationEquiv` is an equivalence between representations over a twist datum and bundles
satisfying one `Prop`. So the existence half of Tag 01O4 can be stated, and attacked, with no
twist datum in sight.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjF1Normalisation.TwistNormalisation`: the glued graded algebra on
  relative Proj together with the homogeneous-section map, and nothing else.
* `Stacks.AlgebraicGeometry.ProjF1Normalisation.ofTwistData`: the two fields of a twist datum
  that Tag 01O4 reads.
* `Stacks.AlgebraicGeometry.ProjF1Normalisation.IsCanonicalTwistPairOf`: canonicality of a pair
  against a normalisation datum.
* `Stacks.AlgebraicGeometry.ProjF1Normalisation.F1Bundle`: the six twist-datum-free fields of a
  representation.

## Main results

* `Stacks.AlgebraicGeometry.ProjF1Normalisation.isCanonicalTwistPair_eq_isCanonicalTwistPairOf`:
  the canonicality clause of Tag 01O4 at a twist datum is, definitionally, the clause at its
  two-field normalisation.
* `Stacks.AlgebraicGeometry.ProjF1Normalisation.representationEquiv`: a representation over a
  twist datum is exactly a bundle together with canonicality of its universal pair.
* `Stacks.AlgebraicGeometry.ProjF1Normalisation.representationOfNormalisationEq`: twist data with
  the same normalisation have the same representations.
* `Stacks.AlgebraicGeometry.ProjF1Normalisation.homEquiv_eq_pullbackClass` and
  `exists_isPullbackPair_homEquiv`: **the forward direction of Tag 01O4's bijection carries no
  choice.** Every value of it is the strict-equivalence class of the canonical pullback of the
  universal pair along the classifying morphism, by naturality at the identity of relative Proj.
* `Stacks.AlgebraicGeometry.ProjF1Normalisation.canonicalRepresentationOfBundle`: **the residue
  of the label `01O4 "represents_f1"`, with every dischargeable hypothesis discharged.** From a
  bundle over the canonically constructed pullback comparison, plus canonicality of its universal
  pair, Tag 01O4's representation follows.

## Implementation notes

**Why this is a reduction and not a weakening.** `F1Representation` quantifies over the twist
datum, so a construction for an arbitrary datum specialises to the canonical one; replacing the
datum by its two-field normalisation enlarges the class quantified over, so the reduced statement
is stronger, not weaker. Nothing below assumes anything about a normalisation datum that a twist
datum does not supply — `ofTwistData` is a plain projection.

**No dot notation is introduced on another file's structures.** `bundleOfRepresentation` and
`representationOfBundle` are spelled out rather than declared in the
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation` namespace, so that this file adds no
name to a namespace it does not own.

**The naturality field is supplied, not assumed.**
`Stacks.AlgebraicGeometry.ProjRepresentsF1.bundleOfHomEquiv` builds a bundle from four inputs
rather than six: the pullback operation on classes is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackClassOf` and naturality is then
`pullbackClassOf_homEquiv`, which holds for any family of bijections.

## What is not done here, and the precise residue

**No `F1Bundle` is constructed, no `F1Representation` is constructed, and no project tag is
attached.** The label `01O4 "represents_f1"` covers four assertions. Three are proved:
`Stacks.AlgebraicGeometry.ProjRepresentsF1.strictlyEquivalent_equivalence`,
`quot_mk_eq_iff_strictlyEquivalent` and `F1Representation.classifyingMorphism_spec`. The fourth
is the representation itself, and after this file its residue is exactly

> an `F1Bundle A TA (tensorAlgebraPullbackIsos TA)` whose universal pair is canonical,

whose two pieces of content, beyond the hypothesis `generated` that the caller supplies, are the
fields `universal` and `homEquiv`. The second is a
*bijection* between the morphisms `T ⟶ Proj A` over `S` and the strict-equivalence classes of
invertible degree-one quotients of `f⁎A`. By `homEquiv_eq_pullbackClass` that bijection is not a
choice — it is the pullback-of-the-universal-pair map — so what is owed of it is that this one
determined map is bijective: that every invertible degree-one quotient on a test scheme is
strictly equivalent to the pullback of the universal one along exactly one morphism to relative
Proj.

**Both fields need the tag's generation hypothesis, and `F1Bundle` states it.** Tag 01O4 reads
`𝒜` generated as an `𝒜₀`-algebra by `𝒜₁`; the repository spells that
`Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne`, and it is the field
`F1Bundle.generated`, inherited by `F1Representation`. Without that field the structure said more
than the tag:
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isEmpty_relativeProj_of_f1Bundle_of_isZero_piece_one`
reads the single field `universal` and concludes that a bundle for an algebra with a vanishing
`𝒜₁` empties the relative `Proj`. So for `𝒜 = 𝒪_S[x]` with `x` of degree two, where `𝒜₁ = 0` and
`Proj_S(𝒜) = S`, the field `universal` alone already has no term over a nonempty base. Its two
ingredients are `isZero_L_of_isZero_piece_one`, which makes every pair's invertible sheaf a zero
object, and `isEmpty_of_isZero_of_isInvertible`, which empties a scheme carrying an invertible
zero object. The companion `eq_zero_of_isZero_piece_one_of_generated` shows that generation in
degree one excludes the configuration outright, which is why the hypothesis sits in the structure
rather than on each construction of a field, exactly as in the source.

**A morphism into relative Proj out of such a quotient is available.** Pinned Mathlib offers only
`AlgebraicGeometry.Proj.fromOfGlobalSections`, whose input is a ring map into global sections —
the trivial bundle — while `AlgebraicGeometry.Proj.map` goes from a `Proj` to a `Proj`. This
repository goes further: `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProjOfIsUnit`
turns a ring map out of the graded sections over an affine open of the base, inverting one
positive-degree homogeneous section, into a morphism `X ⟶ Proj_S(𝒜)` over that open, and
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.toRelativeProjOfPair` feeds a quotient pair into
it through the dehomogenization at a trivializing degree-one section. What the bijection needs
beyond those is the trivialization datum, the glueing of the local morphisms over a cover of the
test scheme, and injectivity and surjectivity of the assembled map.

**The twist datum is therefore not what the label waits on.** By the measurements above, a
complete `TwistData` would discharge none of the residue's content, and the residue's content can
be stated without one.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ProjF1Normalisation

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})

/-! ### The two fields of a twist datum that Tag 01O4 reads -/

/-- The glued graded algebra on a relative Proj together with its homogeneous-section map, and
nothing else: the part of `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` that the
statement of Tag 01O4 consumes. -/
public structure TwistNormalisation where
  /-- The integer-graded sheaf of algebras on the relative Proj. -/
  algebra : SchemeGradedAlgebra (relativeProj A).scheme
  /-- The degreewise map from the base algebra to the direct image of the twists. -/
  ψ (n : ℕ) : A.piece (n : ℤ) ⟶
    (Scheme.Modules.pushforward (relativeProj A).toBase).obj (algebra.piece (n : ℤ))

/-- The normalisation datum underlying a twist datum: its graded algebra and its
homogeneous-section map. -/
public def ofTwistData (D : TwistData A) : TwistNormalisation A where
  algebra := D.algebra
  ψ := D.ψ

/-- The graded algebra of `ofTwistData A D` is that of the twist datum `D`. -/
@[simp]
public theorem ofTwistData_algebra (D : TwistData A) :
    (ofTwistData A D).algebra = D.algebra :=
  rfl

/-- The homogeneous-section map of `ofTwistData A D` is that of the twist datum `D`. -/
@[simp]
public theorem ofTwistData_ψ (D : TwistData A) : (ofTwistData A D).ψ = D.ψ :=
  rfl

/-! ### Canonicality against a normalisation datum -/

/-- A pair on relative Proj is the canonical twist pair of a *normalisation* datum `N` when its
invertible sheaf is identified with the degree-one piece of `N.algebra` by a graded-algebra
homomorphism that is an isomorphism in every nonnegative degree, is unital and
generator-compatible, and carries the pair's graded map to `N.ψ`.

This is `Stacks.AlgebraicGeometry.ProjRepresentsF1.IsCanonicalTwistPair` with the seven unused
fields of a twist datum removed; see
`isCanonicalTwistPair_eq_isCanonicalTwistPairOf`. -/
public def IsCanonicalTwistPairOf (N : TwistNormalisation A)
    (P : F1Pair A TA (relativeProj A).toBase) : Prop :=
  ∃ (β : P.L ≅ N.algebra.piece 1)
    (γ : SheafOfModules.GradedAlgebra.Hom
      (TA (relativeProj A).scheme P.L).tensor N.algebra),
    (∀ n : ℕ, IsIso (γ.app (n : ℤ))) ∧
    ((TA (relativeProj A).scheme P.L).tensorGenerator ≫ γ.app 1 = β.hom) ∧
    (SheafOfModules.sectionsMap (γ.app 0)
      (TA (relativeProj A).scheme P.L).tensor.one = N.algebra.one) ∧
    (∀ n : ℕ, P.ψ (n : ℤ) ≫
      (Scheme.Modules.pushforward (relativeProj A).toBase).map (γ.app (n : ℤ)) = N.ψ n)

/-- **Tag 01O4's canonicality clause sees exactly two fields of a twist datum.** The predicate at
a twist datum is, definitionally, the predicate at its two-field normalisation: the proof is
`rfl`.

Consequently `chartData`, `isGradedChartIso`, `isQuasicoherent`, `mul_comm`, `ψ_one`, `ψ_mul` and
`ψ_chart` do not occur in the statement of Tag 01O4, however much they are needed to construct a
twist datum. -/
public theorem isCanonicalTwistPair_eq_isCanonicalTwistPairOf (D : TwistData A)
    (P : F1Pair A TA (relativeProj A).toBase) :
    IsCanonicalTwistPair A TA D P = IsCanonicalTwistPairOf A TA (ofTwistData A D) P :=
  rfl

/-! ### The twist-datum-free part of a representation -/

variable {ι : TensorAlgebraPullbackIsos.{u} TA}

/-! ### The representation splits as a bundle and one clause -/

/-- The twist-datum-free part of a representation: its `F1Bundle` parent. -/
public abbrev bundleOfRepresentation {D : TwistData A} (R : F1Representation A TA ι D) :
    F1Bundle A TA ι := R.toF1Bundle

/-- A bundle whose universal pair is canonical for the normalisation of a twist datum is a
representation over that datum. -/
public def representationOfBundle (D : TwistData A) (B : F1Bundle A TA ι)
    (hB : IsCanonicalTwistPairOf A TA (ofTwistData A D) B.universal) :
    F1Representation A TA ι D :=
  { B with universal_isCanonical := hB }

/-- **The twist datum enters Tag 01O4 through a single `Prop`.** A representation over a twist
datum is exactly a twist-datum-free bundle together with canonicality of its universal pair
against the datum's two-field normalisation.

Both round trips are `rfl`: the two structures have the same six remaining fields. -/
public def representationEquiv (D : TwistData A) :
    F1Representation A TA ι D ≃
      {B : F1Bundle A TA ι // IsCanonicalTwistPairOf A TA (ofTwistData A D) B.universal} where
  toFun R := ⟨bundleOfRepresentation A TA R, R.universal_isCanonical⟩
  invFun B := representationOfBundle A TA D B.1 B.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Twist data with the same normalisation have the same representations.** This is the
reduction in its sharpest form: no property of a twist datum beyond its graded algebra and its
homogeneous-section map can affect whether Tag 01O4's representation exists over it. -/
public def representationOfNormalisationEq {D E : TwistData A}
    (h : ofTwistData A D = ofTwistData A E) (R : F1Representation A TA ι D) :
    F1Representation A TA ι E :=
  representationOfBundle A TA E (bundleOfRepresentation A TA R) (h ▸ R.universal_isCanonical)

/-! ### The bijection's forward direction carries no choice -/

/-- **The value of a representing bijection is forced.** On the element `⟨g, rfl⟩` the bijection of
a bundle is the pullback along `g` of the class of the universal pair: naturality applied at the
identity of relative Proj, together with the normalisation `homEquiv_id`.

No field of the bundle beyond `universal`, `pullbackClass` and those two equations is used. -/
public theorem homEquiv_comp_eq_pullbackClass (B : F1Bundle A TA ι) {T : Scheme.{u}}
    (g : T ⟶ (relativeProj A).scheme) :
    B.homEquiv (g ≫ (relativeProj A).toBase) ⟨g, rfl⟩ =
      B.pullbackClass g (Quot.mk _ B.universal) :=
  Eq.trans
    (Eq.trans
      (congrArg (B.homEquiv (g ≫ (relativeProj A).toBase))
        (Subtype.ext (Category.comp_id g).symm))
      (B.homEquiv_natural g ⟨𝟙 _, Category.id_comp _⟩))
    (congrArg (B.pullbackClass g) B.homEquiv_id)

/-- The same at an arbitrary element of the fibre: every value of the bijection is the class of a
pullback of the universal pair, transported along the element's own factorisation. -/
public theorem homEquiv_eq_pullbackClass (B : F1Bundle A TA ι) {T : Scheme.{u}} {f : T ⟶ S}
    (h : {g : T ⟶ (relativeProj A).scheme // g ≫ (relativeProj A).toBase = f}) :
    B.homEquiv f h = h.2 ▸ B.pullbackClass h.1 (Quot.mk _ B.universal) := by
  obtain ⟨g, rfl⟩ := h
  exact homEquiv_comp_eq_pullbackClass A TA B g

/-- **Tag 01O4's bijection is the pullback-of-the-universal-pair map, and nothing else.** Every
value of it is the strict-equivalence class of a pair that is the canonical pullback of the
universal pair along the classifying morphism.

So the content still owed by the label is not *which* map the bijection is — that is determined —
but that this determined map is bijective. -/
public theorem exists_isPullbackPair_homEquiv (B : F1Bundle A TA ι) {T : Scheme.{u}}
    (g : T ⟶ (relativeProj A).scheme) :
    ∃ Q : F1Pair A TA (g ≫ (relativeProj A).toBase),
      IsPullbackPair A TA ι g B.universal Q ∧
        B.homEquiv (g ≫ (relativeProj A).toBase) ⟨g, rfl⟩ = Quot.mk _ Q := by
  obtain ⟨Q, hQ, hclass⟩ := B.pullbackClass_rep g B.universal
  exact ⟨Q, hQ, Eq.trans (homEquiv_comp_eq_pullbackClass A TA B g) hclass⟩

/-! ### The residue of the label -/

/-- **The residue of `01O4 "represents_f1"`, with every dischargeable hypothesis discharged.**
Tag 01O4's representation, in the form whose pullback comparison on tensor algebras is
constructed rather than assumed, follows from a twist-datum-free bundle together with canonicality
of its universal pair.

What is still owed is therefore one `F1Bundle`, and in it two fields: the universal pair
`universal` and the bijection `homEquiv`. Both read Tag 01O4's hypothesis that the algebra is
generated in degree one, which `F1Bundle` does not state; see the module docstring. -/
public def canonicalRepresentationOfBundle (D : TwistData A)
    (B : F1Bundle A TA (tensorAlgebraPullbackIsos TA))
    (hB : IsCanonicalTwistPairOf A TA (ofTwistData A D) B.universal) :
    F1RepresentationCanonical A TA D :=
  representationOfBundle A TA D B hB

end Stacks.AlgebraicGeometry.ProjF1Normalisation

end
