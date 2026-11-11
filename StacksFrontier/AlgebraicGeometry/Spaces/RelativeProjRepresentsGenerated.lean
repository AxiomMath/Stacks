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
`Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle`.  Stacks 085D itself is registered on the
constructed relative Proj: part (1) is
`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjIsoF1OfGenerated`, parts (2) and (3)
are in `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjTwistsGenerated.lean`.

Parts (2) and (3) of Stacks 085D are assertions about the twists `𝒪_P(n)`.  The relative Proj
of an algebraic space is presented in this library through its base changes
`T ×_X P = Proj_T(f^*𝒜)` to the scheme points `f : T ⟶ X` of the base
(`AlgebraicGeometry.Space.RelativeProjPoints`), and its twists through their base changes,
which are the twists of Stacks 01NR on `Proj_T(f^*𝒜)`
(`AlgebraicGeometry.Space.RelativeProjPoints.pointTwistData`, the base-change clause of
Stacks 084D).  This file records the base changes of the two parts to every scheme point of
the base, where they are the scheme-level surjectivity of `π^*𝒜_1 ⟶ 𝒪(1)`
(`Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose`) and the invertibility and
multiplication clauses of Stacks 01O4.  The statements on the twists `𝒪_P(n)` of `P` itself,
descended along an étale atlas, are
`AlgebraicGeometry.Space.RelativeProjSituation.epi_psiTwistHom_one`,
`AlgebraicGeometry.Space.RelativeProjSituation.isInvertibleModule_twistModule` and
`AlgebraicGeometry.Space.RelativeProjSituation.isIso_mulSheaf_twistGradedAlgebra`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfBundle`,
  `AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfBundle_natural` and
  `AlgebraicGeometry.Space.RelativeProjPoints.homEquivF1OfBundle`: the bijection from a bundle.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfGenerated`,
  `AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfGenerated_natural` and
  `AlgebraicGeometry.Space.RelativeProjPoints.homEquivF1OfGenerated`: the bijection fibred over
  the points of the base, under degree-one generation.
* `AlgebraicGeometry.Space.RelativeProjPoints.epi_psiTranspose_pointTwistData_one`: after base
  change to a scheme point of the base, the canonical map `π^*𝒜_1 ⟶ 𝒪(1)` is surjective.
* `AlgebraicGeometry.Space.RelativeProjPoints.isInvertible_pointTwist` and
  `AlgebraicGeometry.Space.RelativeProjPoints.isIso_mulSheaf_pointTwistAlgebra`: after base
  change to a scheme point of the base, every `𝒪(n)` is invertible and the multiplication maps
  `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)` are isomorphisms.

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

/-! #### The bijection at the source's hypotheses

The scheme-level input is now discharged.  `Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle`
builds, from the degree-one generation hypothesis of Stacks 01O4 and nothing else, the bundle of
representing bijections of that tag at the canonical pullback comparison
`Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorAlgebraPullbackIsos`; it is the first component
of the registered Stacks 01O4 statement
`Stacks.AlgebraicGeometry.TwistMapsInvertible.f1Bundle_and_twists`.  Applying it at each scheme
point of the base turns `hgen` from a hypothesis that justified `rep` into the hypothesis that
*produces* it, and leaves the three declarations below standing on exactly the data of
Stacks 084B and exactly the hypothesis of Stacks 085D. -/

/-- **The relative Proj represents the functor of triples over a point of the base, under
degree-one generation.**

For a quasi-coherent graded `𝒪_X`-algebra `𝒜` generated as an `𝒜₀`-algebra by `𝒜₁` and
`P = Proj_X(𝒜)`, the `T'`-points of `P` lying over a point `f` of `X` at `T` are the strict
isomorphism classes of pairs `(ℒ, ψ)` with `ℒ` invertible on the scheme of `T'` and
`ψ : f^*𝒜 ⟶ ⨁_{n ≥ 0} ℒ^{⊗ n}` a graded algebra map surjective in degree one — that is, the
triples `(f ∘ r, ℒ, ψ)` of the functor `F₁`.

The relative Proj enters through its base changes to schemes, which is what Stacks 084B supplies
and all the source's proof uses.  The degree-one generation hypothesis `hgen` is the source's
own, and it is the only hypothesis: the scheme-level representing bijections of Stacks 01O4 are
built from it by `Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle`, not assumed. -/
noncomputable def pointEquivF1OfGenerated (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) :
    {u : yoneda.obj T' ⟶ P // u ≫ π = yoneda.map r ≫ f} ≃
      F1 (d.algebra T f) TA ((BigFppfOver.toScheme B S hS).map r) :=
  d.pointEquivF1OfBundle TA (tensorAlgebraPullbackIsos TA)
    (fun T f => f1Bundle (d.algebra T f) TA (hgen T f)) T f r

/-- **The bijection of `pointEquivF1OfGenerated` is natural in the test object.**

Restricting a `T'`-point of `P` along `r' : T'' ⟶ T'` pulls back the class of triples it
represents.  Only the degree-one generation hypothesis of the source enters; the scheme-level
naturality it is read off is that of
`Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle`. -/
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

/-- **The points of the relative Proj, fibred over the points of the base, under degree-one
generation.** For a quasi-coherent graded `𝒪_X`-algebra `𝒜` generated as an
`𝒜₀`-algebra by `𝒜₁`, the `T`-points of `P = Proj_X(𝒜)` are the strict isomorphism classes of
triples `(f, ℒ, ψ)` of the functor `F₁`: a point `f` of `X` at `T`, an invertible module `ℒ` on
the scheme of `T`, and a graded algebra map `f^*𝒜 ⟶ ⨁_{n ≥ 0} ℒ^{⊗ n}` surjective in degree one.

The decomposition of a point of `P` by its image in `X` matches the decomposition of a triple by
its first component, and over each point of `X` the two fibres agree by
`AlgebraicGeometry.Space.RelativeProjPoints.pointEquivF1OfGenerated`.  Degree-one generation is
the only hypothesis. -/
noncomputable def homEquivF1OfGenerated (T : BigFppfOver B S hS) :
    (yoneda.obj T ⟶ P) ≃ Σ f : yoneda.obj T ⟶ X, F1 (d.algebra T f) TA (𝟙 _) :=
  d.homEquivF1OfBundle TA (tensorAlgebraPullbackIsos TA)
    (fun T f => f1Bundle (d.algebra T f) TA (hgen T f)) T

/-! #### The twists after base change to a scheme point

The twists `𝒪_P(n)` and the canonical map `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` of Stacks 084D are
given, at each scheme point `f : T ⟶ X` of the base, by their base changes to
`T ×_X P = Proj_T(f^*𝒜)`: the canonical twist datum
`AlgebraicGeometry.Space.RelativeProjPoints.pointTwistData` of Stacks 01NR there.  Surjectivity
of a map of modules, invertibility of a module and bijectivity of a map of modules are étale
local; at a scheme point they are the case of schemes, Stacks 01O4, applied to `f^*𝒜`, which is
generated in degree one.  The three lemmas below are these base changes.  Stacks 085D (2) and (3)
on the twists of `P` itself are
`AlgebraicGeometry.Space.RelativeProjSituation.epi_psiTwistHom_one`,
`AlgebraicGeometry.Space.RelativeProjSituation.isInvertibleModule_twistModule` and
`AlgebraicGeometry.Space.RelativeProjSituation.isIso_mulSheaf_twistGradedAlgebra`. -/

include hgen

/-- **The canonical map `π^*𝒜₁ ⟶ 𝒪(1)` after base change to a scheme point is surjective.**
For a quasi-coherent graded `𝒪_X`-algebra `𝒜` generated as an `𝒜₀`-algebra by `𝒜₁` and
`P = Proj_X(𝒜)`, after base change to a scheme point `f : T ⟶ X` of the base the map
`π^*𝒜₁ ⟶ 𝒪_P(1)` is the transpose
`π_T^*(f^*𝒜)₁ ⟶ 𝒪(1)` of the degree-one component of `ψ` on `Proj_T(f^*𝒜)`, and that is an
epimorphism by `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose`. -/
theorem epi_psiTranspose_pointTwistData_one (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    Epi (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.psiTranspose (d.pointTwistData T f) 1) :=
  Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose (d.pointTwistData T f)
    (hgen T f)

/-- **The twists after base change to a scheme point are invertible.**  For a quasi-coherent
graded `𝒪_X`-algebra `𝒜` generated as an `𝒜₀`-algebra by `𝒜₁` and `P = Proj_X(𝒜)`, the base change
of the twist `𝒪_P(n)` to a scheme point `f : T ⟶ X` of the base is the twist `𝒪(n)` of
`Proj_T(f^*𝒜)`, which is invertible by Stacks 01O4,
`Stacks.AlgebraicGeometry.TwistMapsInvertible.twistDataOfGradedAlgebra_isInvertible`. -/
theorem isInvertible_pointTwist (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (relativeProj (d.algebra T f)).scheme.presheaf
      (relativeProj (d.algebra T f)).scheme.ringCatSheaf.2 (d.pointTwist T f n) :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.twistDataOfGradedAlgebra_isInvertible (hgen T f) n

/-- **The multiplication of the twists after base change to a scheme point is an
isomorphism.**  For a quasi-coherent graded `𝒪_X`-algebra `𝒜` generated as an `𝒜₀`-algebra by `𝒜₁`
and `P = Proj_X(𝒜)`, after base change to a scheme point `f : T ⟶ X` of the base the maps
`𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)`, for all integers `n` and `m`, are the multiplication maps of the twists
of `Proj_T(f^*𝒜)`, which are isomorphisms by Stacks 01O4,
`Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_mulSheaf_twistDataOfGradedAlgebra`. -/
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
