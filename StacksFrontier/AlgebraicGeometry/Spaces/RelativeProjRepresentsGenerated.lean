module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridgeProof
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Epi
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPointTwists
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Multiplication

/-!
# Stacks 085D from degree-one generation alone

`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProj.lean` identifies the points of the relative
`Proj` of a graded algebra on an algebraic space with the functor `F₁` of triples, given a
scheme-level representation of Stacks 01O4 at each point of the base.  The proof uses only the
three clauses of that representation which make up a
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle`; this file states the bijection from a
bundle, and then discharges the bundle from the source's degree-one generation hypothesis by
`Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle`, which is where Stacks 085D part (1) is
registered with its scheme-level input proved.

Parts (2) and (3) of Stacks 085D are assertions about the twists `𝒪_P(n)`.  The relative Proj
of an algebraic space is presented in this library through its base changes
`T ×_X P = Proj_T(f^*𝒜)` to the scheme points `f : T ⟶ X` of the base
(`AlgebraicGeometry.Space.RelativeProjPoints`), and its twists through their base changes,
which are the twists of Stacks 01NR on `Proj_T(f^*𝒜)`
(`AlgebraicGeometry.Space.RelativeProjPoints.pointTwistData`, the base-change clause of
Stacks 084D).  Both parts are étale local on `P`, and the source's proof is "see Stacks 01O4 for
the case of schemes": so they are stated at every scheme point of the base, where they are the
scheme-level surjectivity of `π^*𝒜_1 ⟶ 𝒪(1)`
(`Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose`) and the invertibility and
multiplication clauses of Stacks 01O4.

## Main results

* `AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfBundle`,
  `AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfBundle_natural` and
  `AlgebraicGeometry.Space.RelativeProjPoints.homEquivF1OfBundle`: the bijection from a bundle.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfGenerated`,
  `AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfGenerated_natural` and
  `AlgebraicGeometry.Space.RelativeProjPoints.homEquivF1OfGenerated`: **Stacks 085D, part (1)**,
  under degree-one generation.
* `AlgebraicGeometry.Space.RelativeProjPoints.epi_psiTranspose_pointTwistData_one`:
  **Stacks 085D, part (2)**: the canonical map `π^*𝒜_1 ⟶ 𝒪_P(1)` is surjective.
* `AlgebraicGeometry.Space.RelativeProjPoints.isInvertible_pointTwist` and
  `AlgebraicGeometry.Space.RelativeProjPoints.isIso_mulSheaf_pointTwistAlgebra`:
  **Stacks 085D, part (3)**: every `𝒪_P(n)` is invertible and the multiplication maps
  `𝒪_P(n) ⊗ 𝒪_P(m) ⟶ 𝒪_P(n + m)` are isomorphisms.

## References

* [Stacks Project, Tag 085D](https://stacks.math.columbia.edu/tag/085D)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

section DegreeOne

open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace RelativeProjPoints

variable {B S hS} {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X}
    (d : RelativeProjPoints B S hS π)

section RepresentsOfBundle

variable (TA : TensorAlgebras.{u}) (i : TensorAlgebraPullbackIsos.{u} TA)
    (bun : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      F1Bundle (d.algebra T f) TA i)

/-! #### The bijection from a bundle of scheme-level representing bijections

Only three of the clauses of Stacks 01O4 enter: the bijection at each test scheme, its pullback
operation on classes, and their naturality.  All three are fields of
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle`, so that is the hypothesis taken here; the
twist datum and the canonicality of the universal pair, which
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation` adds on top of the bundle, are never
read.  Taking the bundle rather than the representation is what lets the hypothesis be discharged
below, because `Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle` builds a bundle from the
source's degree-one generation hypothesis alone. -/

/-- **The relative Proj represents the functor of triples over a point of the base, given a
bundle of scheme-level representing bijections.**

For `P = Proj_X(𝒜)`, the `T'`-points of `P` lying over a point `f` of `X` at `T` are the strict
isomorphism classes of pairs `(ℒ, ψ)` with `ℒ` invertible on the scheme of `T'` and
`ψ : f^*𝒜 ⟶ ⨁_{n ≥ 0} ℒ^{⊗ n}` a graded algebra map surjective in degree one — that is, the
triples `(f ∘ r, ℒ, ψ)` of the functor `F₁`.

The relative Proj enters through its base changes to schemes, as Stacks 084B presents them, and
the scheme-level bijections enter as `bun`.  This is the shape of Stacks 085D part (1) with its
scheme-level input still open; `AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfGenerated`
is the same statement with that input discharged. -/
noncomputable def pointEquivF1OfBundle (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) :
    {u : yoneda.obj T' ⟶ P // u ≫ π = yoneda.map r ≫ f} ≃
      F1 (d.algebra T f) TA ((BigFppfOver.toScheme B S hS).map r) :=
  (d.pointEquivProjOver T f r).trans ((bun T f).homEquiv _)

/-- The class of triples attached to a point of `P`, computed through the section of the
scheme-level relative Proj. -/
theorem pointEquivF1OfBundle_apply (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (u : {u : yoneda.obj T' ⟶ P // u ≫ π = yoneda.map r ≫ f}) :
    d.pointEquivF1OfBundle TA i bun T f r u =
      (bun T f).homEquiv ((BigFppfOver.toScheme B S hS).map r)
        (d.pointEquivProjOver T f r u) := rfl

/-- **The bijection of `pointEquivF1OfBundle` is natural in the test object.**

Restricting a `T'`-point of `P` along `r' : T'' ⟶ T'` pulls back the class of triples it
represents.  Both sides are computed by the one scheme-level bundle at the point `f`, so this is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle.homEquiv_natural` together with the
naturality of the geometric half. -/
theorem pointEquivF1OfBundle_natural (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' T'' : BigFppfOver B S hS} (r : T' ⟶ T) (r' : T'' ⟶ T')
    (u : {u : yoneda.obj T' ⟶ P // u ≫ π = yoneda.map r ≫ f}) :
    d.pointEquivF1OfBundle TA i bun T f (r' ≫ r) ⟨yoneda.map r' ≫ u.1, by
        rw [Category.assoc, u.2, ← Category.assoc, ← CategoryTheory.Functor.map_comp]⟩
      = (bun T f).pullbackClass ((BigFppfOver.toScheme B S hS).map r')
          (d.pointEquivF1OfBundle TA i bun T f r u) := by
  rw [pointEquivF1OfBundle_apply, pointEquivF1OfBundle_apply,
    ← (bun T f).homEquiv_natural ((BigFppfOver.toScheme B S hS).map r')
      (d.pointEquivProjOver T f r u)]
  exact congrArg _ (Subtype.ext (pointEquivProjOver_natural d T f r r' u))

/-- **The `T`-points of `P = Proj_X(𝒜)` are the triples of `F₁`, given a bundle of scheme-level
representing bijections.**

The decomposition of a point of `P` by its image in `X` matches the decomposition of a triple by
its first component, and over each point of `X` the two fibres agree by
`AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfBundle`. -/
noncomputable def homEquivF1OfBundle (T : BigFppfOver B S hS) :
    (yoneda.obj T ⟶ P) ≃ Σ f : yoneda.obj T ⟶ X, F1 (d.algebra T f) TA (𝟙 _) :=
  (Equiv.sigmaFiberEquiv (fun u : yoneda.obj T ⟶ P => u ≫ π)).symm.trans
    (Equiv.sigmaCongrRight fun f =>
      (Equiv.subtypeEquivRight (fun u => by
        rw [CategoryTheory.Functor.map_id, Category.id_comp])).trans
        (d.pointEquivF1OfBundle TA i bun T f (𝟙 T)))

end RepresentsOfBundle

section RepresentsOfGenerated

variable (TA : TensorAlgebras.{u})
    (hgen : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      IsGeneratedInDegreeOne (d.algebra T f))

/-! #### Stacks 085D part (1) at the source's hypotheses

The scheme-level input is now discharged.  `Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle`
builds, from the degree-one generation hypothesis of Stacks 01O4 and nothing else, the bundle of
representing bijections of that tag at the canonical pullback comparison
`Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorAlgebraPullbackIsos`; it is the first component
of the registered Stacks 01O4 statement
`Stacks.AlgebraicGeometry.TwistMapsInvertible.f1Bundle_and_twists`.  Applying it at each scheme
point of the base turns `hgen` from a hypothesis that justified `rep` into the hypothesis that
*produces* it, and leaves the three declarations below standing on exactly the data of
Stacks 084B and exactly the hypothesis of Stacks 085D. -/

/-- **Stacks 085D, part (1), fibred over a point of the base.**

For a quasi-coherent graded `𝒪_X`-algebra `𝒜` generated as an `𝒜₀`-algebra by `𝒜₁` and
`P = Proj_X(𝒜)`, the `T'`-points of `P` lying over a point `f` of `X` at `T` are the strict
isomorphism classes of pairs `(ℒ, ψ)` with `ℒ` invertible on the scheme of `T'` and
`ψ : f^*𝒜 ⟶ ⨁_{n ≥ 0} ℒ^{⊗ n}` a graded algebra map surjective in degree one — that is, the
triples `(f ∘ r, ℒ, ψ)` of the functor `F₁`.

The relative Proj enters through its base changes to schemes, which is what Stacks 084B supplies
and all the source's proof uses.  The degree-one generation hypothesis `hgen` is the source's
own, and it is the only hypothesis: the scheme-level representing bijections of Stacks 01O4 are
built from it by `Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle`, not assumed. -/
@[stacks 085D "part (1), over a point of the base: for a quasi-coherent graded O_X-algebra A \
generated as an A_0-algebra by A_1 and P = Proj_X(A), the T'-points of P lying over a T-point f \
of X are in bijection with the strict isomorphism classes of pairs (L, psi) -- L invertible on \
the scheme of T' and psi : f^*A -> ⨁_{n >= 0} L^{tensor n} a graded algebra map surjective in \
degree one -- that is, with the triples (f . r, L, psi) of F_1 over f. The scheme-level \
representing bijections of Stacks 01O4 are proved from the degree-one generation, by \
ProjRepresentsF1.f1Bundle. P is given, as throughout this library's relative Proj of algebraic \
spaces, by its base changes T x_X P = Proj_T(f^*A) to the scheme points of X \
(RelativeProjPoints, the second assertion of Stacks 084B); TA is the choice of tensor algebras \
needed to write ⨁_{n >= 0} L^{tensor n}. Parts (2) and (3) are \
epi_psiTranspose_pointTwistData_one, isInvertible_pointTwist and \
isIso_mulSheaf_pointTwistAlgebra"]
noncomputable def pointEquivF1OfGenerated (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) :
    {u : yoneda.obj T' ⟶ P // u ≫ π = yoneda.map r ≫ f} ≃
      F1 (d.algebra T f) TA ((BigFppfOver.toScheme B S hS).map r) :=
  d.pointEquivF1OfBundle TA (tensorAlgebraPullbackIsos TA)
    (fun T f => f1Bundle (d.algebra T f) TA (hgen T f)) T f r

/-- **Stacks 085D, part (1): the representing bijection is natural in the test object.**

Restricting a `T'`-point of `P` along `r' : T'' ⟶ T'` pulls back the class of triples it
represents.  Only the degree-one generation hypothesis of the source enters; the scheme-level
naturality it is read off is that of
`Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle`. -/
@[stacks 085D "part (1), naturality of the representing bijection in the test object, under \
degree-one generation alone: restricting a T'-point of P along r' : T'' -> T' pulls back the \
class of triples it represents, along the pullback-of-classes operation of the scheme-level \
bijections that ProjRepresentsF1.f1Bundle builds from the degree-one generation"]
theorem pointEquivF1OfGenerated_natural (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' T'' : BigFppfOver B S hS} (r : T' ⟶ T) (r' : T'' ⟶ T')
    (u : {u : yoneda.obj T' ⟶ P // u ≫ π = yoneda.map r ≫ f}) :
    d.pointEquivF1OfGenerated TA hgen T f (r' ≫ r) ⟨yoneda.map r' ≫ u.1, by
        rw [Category.assoc, u.2, ← Category.assoc, ← CategoryTheory.Functor.map_comp]⟩
      = (f1Bundle (d.algebra T f) TA (hgen T f)).pullbackClass
          ((BigFppfOver.toScheme B S hS).map r')
          (d.pointEquivF1OfGenerated TA hgen T f r u) :=
  d.pointEquivF1OfBundle_natural TA (tensorAlgebraPullbackIsos TA)
    (fun T f => f1Bundle (d.algebra T f) TA (hgen T f)) T f r r' u

/-- **Stacks 085D, part (1).** For a quasi-coherent graded `𝒪_X`-algebra `𝒜` generated as an
`𝒜₀`-algebra by `𝒜₁`, the `T`-points of `P = Proj_X(𝒜)` are the strict isomorphism classes of
triples `(f, ℒ, ψ)` of the functor `F₁`: a point `f` of `X` at `T`, an invertible module `ℒ` on
the scheme of `T`, and a graded algebra map `f^*𝒜 ⟶ ⨁_{n ≥ 0} ℒ^{⊗ n}` surjective in degree one.

The decomposition of a point of `P` by its image in `X` matches the decomposition of a triple by
its first component, and over each point of `X` the two fibres agree by
`AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfGenerated`.  Degree-one generation is
the only hypothesis. -/
@[stacks 085D "part (1): for a quasi-coherent graded O_X-algebra A generated as an \
A_0-algebra by A_1, the T-points of P = Proj_X(A) are in bijection with the strict isomorphism \
classes of triples (f, L, psi) of the functor F_1 -- a T-point f of X, an invertible module L \
on the scheme of T, and a graded algebra map f^*A -> ⨁_{n >= 0} L^{tensor n} surjective in \
degree one. The scheme-level representing bijections of Stacks 01O4 are proved from the \
degree-one generation, by ProjRepresentsF1.f1Bundle. P is given by its base changes \
T x_X P = Proj_T(f^*A) to the scheme points of X (RelativeProjPoints, the second assertion of \
Stacks 084B). F_1 is given fibred over the points of X, with its functoriality in the test \
object over each point (pointEquivF1OfGenerated_natural), because RelativeProjPoints does not \
record the comparison g^*(f^*A) = (f . g)^*A between restrictions at different points"]
noncomputable def homEquivF1OfGenerated (T : BigFppfOver B S hS) :
    (yoneda.obj T ⟶ P) ≃ Σ f : yoneda.obj T ⟶ X, F1 (d.algebra T f) TA (𝟙 _) :=
  d.homEquivF1OfBundle TA (tensorAlgebraPullbackIsos TA)
    (fun T f => f1Bundle (d.algebra T f) TA (hgen T f)) T

/-! #### Stacks 085D parts (2) and (3), on the twists

The twists `𝒪_P(n)` and the canonical map `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` of Stacks 084D are
given, at each scheme point `f : T ⟶ X` of the base, by their base changes to
`T ×_X P = Proj_T(f^*𝒜)`: the canonical twist datum
`AlgebraicGeometry.Space.RelativeProjPoints.pointTwistData` of Stacks 01NR there.  Surjectivity
of a map of modules, invertibility of a module and bijectivity of a map of modules are étale
local, so parts (2) and (3) on `P` say exactly that they hold after base change to every scheme
point of the base.  At a scheme point they are the case of schemes, which is the source's whole
proof ("see Constructions, Lemma 01O4"), applied to `f^*𝒜`, which is generated in degree one. -/

include hgen

/-- **Stacks 085D, part (2).**  For a quasi-coherent graded `𝒪_X`-algebra `𝒜` generated as an
`𝒜₀`-algebra by `𝒜₁` and `P = Proj_X(𝒜)`, the canonical map `π^*𝒜₁ ⟶ 𝒪_P(1)` is surjective:
after base change to any scheme point `f : T ⟶ X` of the base it is the transpose
`π_T^*(f^*𝒜)₁ ⟶ 𝒪(1)` of the degree-one component of `ψ` on `Proj_T(f^*𝒜)`, and that is an
epimorphism by `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose`. -/
@[stacks 085D "part (2): for a quasi-coherent graded O_X-algebra A generated as an A_0-algebra \
by A_1 and P = Proj_X(A), the canonical map pi^*A_1 -> O_P(1) is surjective, at every scheme \
point f : T -> X of the base: the transpose pi_T^*(f^*A)_1 -> O(1) of the degree-one component \
of psi on T x_X P = Proj_T(f^*A) is an epimorphism of sheaves of modules"]
theorem epi_psiTranspose_pointTwistData_one (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    Epi (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.psiTranspose (d.pointTwistData T f) 1) :=
  Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose (d.pointTwistData T f)
    (hgen T f)

/-- **Stacks 085D, part (3), invertibility.**  For a quasi-coherent graded `𝒪_X`-algebra `𝒜`
generated as an `𝒜₀`-algebra by `𝒜₁` and `P = Proj_X(𝒜)`, each twist `𝒪_P(n)` is invertible:
after base change to any scheme point `f : T ⟶ X` of the base it is the twist `𝒪(n)` of
`Proj_T(f^*𝒜)`, which is invertible by Stacks 01O4,
`Stacks.AlgebraicGeometry.TwistMapsInvertible.twistDataOfGradedAlgebra_isInvertible`. -/
@[stacks 085D "part (3), invertibility: for a quasi-coherent graded O_X-algebra A generated as \
an A_0-algebra by A_1 and P = Proj_X(A), every O_P(n), n in Z, is an invertible module, at every \
scheme point f : T -> X of the base: the twist O(n) on T x_X P = Proj_T(f^*A) is invertible"]
theorem isInvertible_pointTwist (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (relativeProj (d.algebra T f)).scheme.presheaf
      (relativeProj (d.algebra T f)).scheme.ringCatSheaf.2 (d.pointTwist T f n) :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.twistDataOfGradedAlgebra_isInvertible (hgen T f) n

/-- **Stacks 085D, part (3), multiplication.**  For a quasi-coherent graded `𝒪_X`-algebra `𝒜`
generated as an `𝒜₀`-algebra by `𝒜₁` and `P = Proj_X(𝒜)`, the multiplication maps induce
isomorphisms `𝒪_P(n) ⊗_{𝒪_P} 𝒪_P(m) ⟶ 𝒪_P(n + m)` for all integers `n` and `m`: after base
change to any scheme point `f : T ⟶ X` of the base they are the multiplication maps of the twists
of `Proj_T(f^*𝒜)`, which are isomorphisms by Stacks 01O4,
`Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_mulSheaf_twistDataOfGradedAlgebra`. -/
@[stacks 085D "part (3), multiplication: for a quasi-coherent graded O_X-algebra A generated as \
an A_0-algebra by A_1 and P = Proj_X(A), the multiplication maps O_P(n) (x) O_P(m) -> O_P(n+m) \
are isomorphisms for all integers n, m, at every scheme point f : T -> X of the base: the \
multiplication of the twists on T x_X P = Proj_T(f^*A) is an isomorphism in all degrees"]
theorem isIso_mulSheaf_pointTwistAlgebra (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    (n m : ℤ) :
    IsIso (_root_.SheafOfModules.GradedAlgebra.mulSheaf (d.pointTwistAlgebra T f) n m) :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_mulSheaf_twistDataOfGradedAlgebra
    (hgen T f) n m

end RepresentsOfGenerated

end RelativeProjPoints

end DegreeOne

end AlgebraicGeometry.Space

end
