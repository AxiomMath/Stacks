module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement

/-!
# Relative Proj as a representation of the functor of invertible degree-one quotients

Tag 01O4 asserts that, for a quasi-coherent graded algebra `A` on a scheme `S` generated in
degree one, the relative homogeneous spectrum of `A` represents the functor `F1` of
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Basic`, and that the representing bijections
are normalised at the identity by the pair consisting of the degree-one twist and the glued
homogeneous-section map of Tag 01NR.

This file writes that assertion down — the universal pair, what it means for a pair to be the
canonical twist pair, the pullback of a pair along a morphism of test schemes, and the bundle of
representing bijections — and proves the one assertion of the tag that follows from the bundle
alone: the morphism classified by a pair induces exactly the class of that pair.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebraPullbackIsos`: a comparison, in every
  degree, of the pullback of a tensor algebra with the tensor algebra of the pullback. This too
  is a hypothesis; see the implementation notes.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.pullbackMap`: the adjoint transpose of a
  component of the graded map, a morphism out of the pulled-back homogeneous piece.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.IsPullbackPair`: the canonical pullback of a pair
  along a morphism of test schemes.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.IsCanonicalTwistPair`: the pair furnished by the
  graded twists and the homogeneous-section map on relative Proj.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation`: the representing bijections,
  together with the universal pair that normalises them at the identity.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation.classifyingMorphism`: the morphism
  to relative Proj classified by a pair.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation.classifyingMorphism_spec`: the
  classifying morphism of a pair induces precisely the strict isomorphism class of that pair.

## Implementation notes

**The universal pair is pinned against a `TwistData`, taken as a parameter.** Tag 01O4 fixes the
universal pair by the graded twists of Tag 01NR; `Stacks.AlgebraicGeometry.RelativeProjTwists.`
`TwistData` is the library form of that datum, and one exists for every quasi-coherent graded
algebra: `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, which reads
nothing beyond the algebra itself, the nested cocycle of Tag 01MZ being settled in every integer
degree by `Stacks.AlgebraicGeometry.ProjTwistCocycle.isNestedCocycle`. That term is what makes the
parameter `D` of `F1Representation` and of
`Stacks.AlgebraicGeometry.ProjF1Normalisation.canonicalRepresentationOfBundle` something a caller
can supply. `IsCanonicalTwistPair` still takes the twist
datum as an argument. This is a generalisation rather than a weakening: Tag 01NR's uniqueness
assertion says any two twist data are related by a unique compatible isomorphism, so the
property at one of them determines it at all.

**The pullback comparison on the tensor algebra is a parameter, and is the narrowest one that
the tag's statement needs.** Tag 01CI asserts `f^*T(F) = T(f^*F)`. The graded-algebra form of
that, the invertibility of `SheafOfModules.GradedAlgebra.pullbackComparison`, is open; but
`IsPullbackPair` uses only the degreewise isomorphisms, with no multiplicativity, unitality or
generator compatibility, and those are constructed from Tag 01CD in
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PullbackIsos` — so the parameter is
dischargeable, by `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorAlgebraPullbackIsos`.

**Pullback is spelled with `AlgebraicGeometry.Scheme.Modules.pullback` throughout**, rather than
with the ringed-space `modulePullback` of a morphism's underlying sheafed-space morphism. The
two agree, and the scheme-level spelling is the one the surrounding Mathlib API — the adjunction
and `Scheme.Modules.pullbackComp` — is stated in, so no transport appears in the statement.

**`F1Bundle` carries the tag's generation hypothesis as its field `generated`.** Tag 01O4 reads
`𝒜` generated as an `𝒜₀`-algebra by `𝒜₁`, which is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne` of `ProjRepresentsF1.Basic`:
over every affine open of the base, the degree-one part generates the ring of homogeneous
sections as an algebra over the degree-zero part. That is the notion the tag's other registered
assertion is already stated at — `Stacks.AlgebraicGeometry.TwistMapsInvertible.`
`relativeProjTwists_isInvertible` carries its unfolding verbatim — and the one the tagged statement
`Stmt_01O4__represents_f1` writes down, so no new spelling of degree-one generation is introduced
here. The sheaf-level `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.`
`IsGeneratedInDegreeOneAt` is the additive-subgroup form over a single open, from which this
follows by `adjoin_grading_one_eq_top`; `SheafOfModules.GradedAlgebra.IsGeneratedInDegreeOne`
belongs to the other relative-Proj substrate and is not stated for `SheafGradedAlgebra` at all.

The field is not decoration. `StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.GenerationNecessary`
measures both sides of it. Its `isZero_L_of_isZero_piece_one` shows that a zero `𝒜₁` makes the
invertible sheaf of every pair a zero object, which the field `F1Pair.invertible` contradicts on a
nonempty scheme — so for `𝒜 = 𝒪_S[x]` with `x` of degree two the field `universal` alone has no
term, and a structure omitting `generated` would assert representability for that algebra too.
Its `eq_zero_of_isZero_piece_one_of_generated` shows that generation in degree one is exactly what
excludes that configuration: with it a zero `𝒜₁` forces every positive-degree piece to vanish
over every affine open, which puts the algebra in degree zero, where the relative `Proj` is empty
and the functor has nothing to represent.

**`classifyingMorphism_spec` is a projection of the bundle, by design.** It is
`Equiv.apply_symm_apply` for the representing bijection, and that is all the source claims at
this point: the content is the existence of the bijection, which is `F1Representation` itself.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)

## Not done here

**No `F1Representation` is constructed.** The existence assertion of Tag 01O4 — that relative
Proj represents `F1` when the algebra is generated in degree one — is not proved, and the
missing declaration is named in the accompanying report. Consequently no project tag is attached
in this directory: the label `01O4 "represents_f1"` covers four assertions, three of which are
available here and in `ProjRepresentsF1.Basic`, and the covering set is therefore incomplete.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! ### The pullback comparison, as a hypothesis -/

/-- A degreewise comparison of the pullback of a tensor algebra with the tensor algebra of the
pullback, for every morphism of schemes and every sheaf of modules on its target.

This is the content of Tag 01CI that Tag 01O4's pullback clause consumes. It is a hypothesis
because invertibility of the canonical comparison is not available in the library; see the
implementation notes. -/
public abbrev TensorAlgebraPullbackIsos (TA : TensorAlgebras.{u}) : Type (u + 1) :=
  ∀ {T T' : Scheme.{u}} (g : T' ⟶ T) (L : T.Modules) (n : ℤ),
    (Scheme.Modules.pullback g).obj ((TA T L).tensor.piece n) ≅
      (TA T' ((Scheme.Modules.pullback g).obj L)).tensor.piece n

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})

/-! ### Pulling a pair back along a morphism of test schemes -/

/-- The adjoint form of a component of the graded map: a morphism out of the pulled-back
homogeneous piece of the algebra on the base. -/
public def F1Pair.pullbackMap {T : Scheme.{u}} {f : T ⟶ S} (P : F1Pair A TA f) (n : ℤ) :
    (Scheme.Modules.pullback f).obj (A.piece n) ⟶ (TA T P.L).tensor.piece n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (P.ψ n)

/-- A pair over `T'` is the pullback of a pair over `T` along `g : T' ⟶ T` when there is an
isomorphism of the pulled-back invertible sheaf with the new one, and a unital isomorphism of
the corresponding tensor algebras extending it on the degree-one generators, under which the
pulled-back graded map becomes the new graded map in every degree. -/
public def IsPullbackPair (ι : TensorAlgebraPullbackIsos.{u} TA) {T T' : Scheme.{u}}
    {f : T ⟶ S} (g : T' ⟶ T) (P : F1Pair A TA f) (Q : F1Pair A TA (g ≫ f)) : Prop :=
  ∃ (β : (Scheme.Modules.pullback g).obj P.L ≅ Q.L)
    (γ : (TA T' ((Scheme.Modules.pullback g).obj P.L)).tensor ≅ (TA T' Q.L).tensor),
    ((TA T' ((Scheme.Modules.pullback g).obj P.L)).tensorGenerator ≫ γ.hom.app 1 =
      β.hom ≫ (TA T' Q.L).tensorGenerator) ∧
    (SheafOfModules.sectionsMap (γ.hom.app 0)
      (TA T' ((Scheme.Modules.pullback g).obj P.L)).tensor.one = (TA T' Q.L).tensor.one) ∧
    (∀ n, (Scheme.Modules.pullbackComp g f).inv.app (A.piece n) ≫
        (Scheme.Modules.pullback g).map (P.pullbackMap A TA n) ≫
        (ι g P.L n).hom ≫ γ.hom.app n = Q.pullbackMap A TA n)

/-! ### The universal pair -/

/-- A pair on relative Proj is *the* canonical twist pair of a twist datum `D` when its
invertible sheaf is the degree-one twist, its tensor algebra maps to the glued graded algebra by
a homomorphism that is an isomorphism in every nonnegative degree and is unital and
generator-compatible, and its graded map becomes the homogeneous-section map of `D` under that
homomorphism. -/
public def IsCanonicalTwistPair (D : TwistData A)
    (P : F1Pair A TA (relativeProj A).toBase) : Prop :=
  ∃ (β : P.L ≅ D.algebra.piece 1)
    (γ : SheafOfModules.GradedAlgebra.Hom
      (TA (relativeProj A).scheme P.L).tensor D.algebra),
    (∀ n : ℕ, IsIso (γ.app (n : ℤ))) ∧
    ((TA (relativeProj A).scheme P.L).tensorGenerator ≫ γ.app 1 = β.hom) ∧
    (SheafOfModules.sectionsMap (γ.app 0)
      (TA (relativeProj A).scheme P.L).tensor.one = D.algebra.one) ∧
    (∀ n : ℕ, P.ψ (n : ℤ) ≫
      (Scheme.Modules.pushforward (relativeProj A).toBase).map (γ.app (n : ℤ)) = D.ψ n)

/-! ### The representation -/

/-- The hypothesis of Tag 01O4 together with the six fields of a representation that do not
mention a twist datum: generation in degree one, the universal pair, the representing
bijections, their normalisation at the identity of relative Proj, the pullback of
strict-equivalence classes, its computation by a representative, and naturality.

Generation in degree one is a field rather than a parameter of the constructions because it is
a hypothesis of the tag on the algebra alone, and because without it the remaining fields have
no term for some algebras: see
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isEmpty_relativeProj_of_f1Bundle_of_isZero_piece_one`
and the implementation notes. -/
public structure F1Bundle (ι : TensorAlgebraPullbackIsos.{u} TA) where
  /-- The algebra is generated in degree one over its degree-zero part: Tag 01O4's hypothesis. -/
  generated : IsGeneratedInDegreeOne A
  /-- The universal pair, over relative Proj itself. -/
  universal : F1Pair A TA (relativeProj A).toBase
  /-- The representing bijection over a test scheme. -/
  homEquiv {T : Scheme.{u}} (f : T ⟶ S) :
    {g : T ⟶ (relativeProj A).scheme // g ≫ (relativeProj A).toBase = f} ≃ F1 A TA f
  /-- At the identity of relative Proj it takes the value of the universal pair. -/
  homEquiv_id :
    homEquiv (relativeProj A).toBase ⟨𝟙 _, Category.id_comp _⟩ = Quot.mk _ universal
  /-- Pullback of classes along a morphism of test schemes. -/
  pullbackClass {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T) : F1 A TA f → F1 A TA (g ≫ f)
  /-- Pullback of classes is computed by the canonical pullback of a representative. -/
  pullbackClass_rep {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T) (P : F1Pair A TA f) :
    ∃ Q : F1Pair A TA (g ≫ f),
      IsPullbackPair A TA ι g P Q ∧ pullbackClass g (Quot.mk _ P) = Quot.mk _ Q
  /-- The representing bijections are natural in the test scheme. -/
  homEquiv_natural {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T)
      (h : {k : T ⟶ (relativeProj A).scheme // k ≫ (relativeProj A).toBase = f}) :
    homEquiv (g ≫ f)
        ⟨g ≫ h.1, by simpa [Category.assoc] using congrArg (fun k => g ≫ k) h.2⟩ =
      pullbackClass g (homEquiv f h)

/-- The representing bijections of Tag 01O4, together with the universal pair that normalises
them at the identity morphism of relative Proj and the pullback operation on classes that makes
them natural: a bundle whose universal pair is the canonical one of the twist datum. -/
public structure F1Representation (ι : TensorAlgebraPullbackIsos.{u} TA) (D : TwistData A)
    extends F1Bundle A TA ι where
  /-- The universal pair is the canonical pair of the twist datum. -/
  universal_isCanonical : IsCanonicalTwistPair A TA D toF1Bundle.universal


namespace F1Representation

variable {A TA} {ι : TensorAlgebraPullbackIsos.{u} TA} {D : TwistData A}
  (R : F1Representation A TA ι D)

/-- The morphism to relative Proj classified by an invertible degree-one quotient pair. -/
public def classifyingMorphism {T : Scheme.{u}} (f : T ⟶ S) (P : F1Pair A TA f) :
    {g : T ⟶ (relativeProj A).scheme // g ≫ (relativeProj A).toBase = f} :=
  (R.homEquiv f).symm (Quot.mk _ P)

/-- **Tag 01O4.** The classifying morphism of a pair induces precisely the strict isomorphism
class of that pair. -/
public theorem classifyingMorphism_spec {T : Scheme.{u}} (f : T ⟶ S) (P : F1Pair A TA f) :
    R.homEquiv f (R.classifyingMorphism f P) = Quot.mk _ P :=
  (R.homEquiv f).apply_symm_apply _

end F1Representation

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
