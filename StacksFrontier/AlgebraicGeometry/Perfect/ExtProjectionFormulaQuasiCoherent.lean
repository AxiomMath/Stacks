module

public import StacksFrontier.AlgebraicGeometry.Perfect.ExtProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectInternalHomPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# A projection formula for Ext with quasi-coherent coefficients

Let `S` be a scheme, `f : X ⟶ S` a morphism locally of finite type, `E` a perfect object of
`D(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with support
proper over `S` — the situation of [Stacks, Tag 0DJR], where
`K = Rf_*RSheafHom_{𝒪_X}(E, 𝒢)` is shown to be perfect.  [Stacks, Tag 08ID] asserts functorial
isomorphisms

`H^i(S, K ⊗^L_{𝒪_S} ℱ) ≅ Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)`

for `ℱ` quasi-coherent on `S`, compatible with boundary maps.

## Main definitions

* `Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent.derivedSheafHomFunctor` is
  `RSheafHom_{𝒪_X}(E, -)` on `D(𝒪_X)`.
* `Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent.extFunctor` is
  `ℱ ↦ RSheafHom_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)`, whose `i`-th hypercohomology on `X` is
  `Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)` by [Stacks, Tag 08DK].
* `Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent.baseTensorSheafHomFunctor` is
  `ℱ ↦ K ⊗^L_{𝒪_S} ℱ` for the `K` of [Stacks, Tag 0DJR].
* `Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent.DualSheafHomData` is the conclusion of
  [Stacks, Tag 08DQ] for `E`: a dual `E^∨` with `E^∨ ⊗^L_{𝒪_X} - ≅ RSheafHom_{𝒪_X}(E, -)`.

## Main results

* `Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent.extCohomologyIsoSheafHom`: given a dual
  `DualSheafHomData E` and the input bundle of [Stacks, Tag 0A1F] at that dual, for every `i` an
  isomorphism `H^i(S, K ⊗^L_{𝒪_S} ℱ) ≅ H^i(X, RSheafHom_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ))`, as a
  natural isomorphism of functors in `ℱ`.

[Stacks, Tag 08ID] itself, under exactly the source's hypotheses and with the compatibility with
boundary maps, is `Stacks.Cohomology.ExtPerfectProjection.extIso_qcoh_boundary`
(`StacksFrontier.AlgebraicGeometry.Perfect.ExtPerfectProjectionBoundary`), which builds the dual by
[Stacks, Tag 08DQ] and applies the boundary form of [Stacks, Tag 0A1F].
* `Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent.extCohomologyIsoQuasicoherent` is its
  restriction to the quasi-coherent `𝒪_S`-modules, the shape in which the source states it.

## Implementation notes

**The source's proof is a reduction to [Stacks, Tag 0A1F].**  It chooses a dual perfect complex
`E^∨` by [Stacks, Tag 08DQ] and uses that twice: once to rewrite
`RSheafHom_{𝒪_X}(E, 𝒢) = E^∨ ⊗^L_{𝒪_X} 𝒢`, so that the `K` of [Stacks, Tag 0DJR] becomes the
`K` of [Stacks, Tag 0DJQ] for the pair `(E^∨, 𝒢)`, and once to rewrite

`Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ) = H^i(X, E^∨ ⊗^L_{𝒪_X} (𝒢 ⊗_{𝒪_X} f^*ℱ))`

for each coefficient module `ℱ`.  After those two rewrites the assertion is exactly
[Stacks, Tag 0A1F] applied to `E^∨` and `𝒢`, which is
`Stacks.Cohomology.ExtProjectionFormula.extCohomologyIso` here.  This file is that reduction and
nothing more: everything the source's proof of [Stacks, Tag 0A1F] does — the projection formula,
associativity of the derived tensor product, the identification of
`𝒢 ⊗^L_{𝒪_X} Lf^*ℱ` with `𝒢 ⊗_{𝒪_X} f^*ℱ`, and Leray — happens inside that tag, whose input
bundle `Stacks.Cohomology.ExtProjectionFormula.ExtProjectionInput` is taken here unchanged at
`E^∨`.  In particular the two assumptions that tag carries, and only those, pass through.

**The extra input of this file.**  One thing beyond the input bundle of [Stacks, Tag 0A1F]:
`DualSheafHomData`, the conclusion of [Stacks, Tag 08DQ] for `E`, asked for as a function of
perfectness of `E`.  [Stacks, Tag 08DQ] is proved in this repository
(`Stacks.SheafOfModules.derivedTensorDualNatIsoOfIsPerfectSpace` and
`Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace`); that proof is what
`Stacks.Cohomology.ExtPerfectProjection.extIso_qcoh_boundary` uses, whereas the construction here
keeps the dual abstract.  Two differences from
`Stacks.Cohomology.PerfectInternalHomPushforward.DualTensorData`: the perfectness of `E^∨` is
not a field here, because it is already the `isPerfect` field of the input bundle of
[Stacks, Tag 0A1F] at `E^∨`; and the isomorphism is asked for as a natural isomorphism of
functors `E^∨ ⊗^L_{𝒪_X} - ≅ RSheafHom_{𝒪_X}(E, -)` on all of `D(𝒪_X)`, because the source uses
it at `𝒢` and at every `𝒢 ⊗_{𝒪_X} f^*ℱ`.  It is still weaker than the tag, which asserts that
the canonical map of [Stacks, Tag 08I1] is the isomorphism.

**How `Ext` is read.**  `Ext^i_{𝒪_X}(E, N)` is the `i`-th hypercohomology of
`RSheafHom_{𝒪_X}(E, N)` on `X`, which is [Stacks, Tag 08DK]; that identification with
`ShiftedHom E N i` is proved in this repository in degree zero over the whole space
(`Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv`) and in every degree over an open
for the chosen K-injective model
(`Stacks.SheafOfModules.homSheafComplexSectionHomologyEquiv`).  The right-hand side below is the
hypercohomology; the reading as shifted morphisms `Hom_{D(𝒪_X)}(E, -[i])`, for perfect `E`, is the
one taken in `Stacks.Cohomology.ExtPerfectProjection.extIso_qcoh_boundary`, through
`Stacks.Cohomology.PerfectDualExt.extIso`.

**The hypotheses that are not needed.**  `S` is not assumed Noetherian: that assumption enters
[Stacks, Tag 0DJR] only to make `K` perfect, and perfectness of `K` is not used in the
construction of the isomorphisms.  Perfectness of `E` is used, as the source uses it, solely to
produce the dual.

**Boundary maps.**  The compatibility with boundary maps is not part of the statements of this
file; it is proved in `Stacks.Cohomology.ExtPerfectProjection.extIso_qcoh_boundary`.  It asks
that for a short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of quasi-coherent `𝒪_S`-modules the square

`H^i(S, K ⊗^L_{𝒪_S} ℱ₃) → Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ₃)`,
`H^{i+1}(S, K ⊗^L_{𝒪_S} ℱ₁) → Ext^{i+1}_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ₁)`

commutes, where the left vertical map is the connecting map of the distinguished triangle
obtained by applying `K ⊗^L_{𝒪_S} -` to the triangle of the sequence and the right vertical map
is the connecting map of the triangle of the short exact sequence of complexes
`0 → 𝒢 ⊗_{𝒪_X} f^*ℱ₁ → 𝒢 ⊗_{𝒪_X} f^*ℱ₂ → 𝒢 ⊗_{𝒪_X} f^*ℱ₃ → 0`, which is exact because the
terms of `𝒢` are flat over `S`.  Naturality in `ℱ` gives the squares on the first two legs of
those two triangles, but in a triangulated category such a pair of squares always admits *some*
fill-in on the third leg, so the compatibility needs the separate argument made there.

## References

* [Stacks Project, Tag 08ID](https://stacks.math.columbia.edu/tag/08ID)
* [Stacks Project, Tag 0A1F](https://stacks.math.columbia.edu/tag/0A1F)
* [Stacks Project, Tag 0DJR](https://stacks.math.columbia.edu/tag/0DJR)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.ExtProjectionFormula
open Stacks.Cohomology.PerfectInternalHomPushforward (derivedSheafHomObj)
open Stacks.Cohomology.ProperSupportPerfection (derivedPushforwardOX)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

namespace Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
  (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)

/-! ### The two sides of the tag -/

/-- `RSheafHom_{𝒪_X}(E, -)`, the derived internal Hom of [Stacks, Tag 08DI] out of a fixed
object `E` of `D(𝒪_X)`.  Its value at `RSheafHom_{𝒪_X}(E, 𝒢)` is
`Stacks.Cohomology.PerfectInternalHomPushforward.derivedSheafHomObj`. -/
abbrev derivedSheafHomFunctor :
    DerivedCategory (OXMod.{u, u} X.toRingedSpace) ⥤
      DerivedCategory (OXMod.{u, u} X.toRingedSpace) :=
  (Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)

/-- The object `K = Rf_*RSheafHom_{𝒪_X}(E, 𝒢)` of `D(𝒪_S)` of [Stacks, Tag 0DJR]. -/
abbrev sheafHomPushforwardK : DerivedCategory (OXMod.{u, u} S.toRingedSpace) :=
  (derivedPushforwardOX f).obj (derivedSheafHomObj (X := X) E G)

/-- **The left-hand side of [Stacks, Tag 08ID] before cohomology**: `ℱ ↦ K ⊗^L_{𝒪_S} ℱ`, with
`ℱ` placed in degree zero and `K` the object of [Stacks, Tag 0DJR]. -/
abbrev baseTensorSheafHomFunctor :
    OXMod.{u, u} S.toRingedSpace ⥤ DerivedCategory (OXMod.{u, u} S.toRingedSpace) :=
  DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0 ⋙
    (derivedTensorProductFunctor S.toRingedSpace.sheaf).obj (sheafHomPushforwardK f E G)

/-- **The right-hand side of [Stacks, Tag 08ID] before cohomology**:
`ℱ ↦ RSheafHom_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)`, with `f^*` the ordinary pullback of
[Stacks, Tag 0096] and `𝒢 ⊗_{𝒪_X} f^*ℱ` the degreewise tensor product
`Stacks.Cohomology.ExtProjectionFormula.tensorModuleComplex`.  Its `i`-th hypercohomology on `X`
is `Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)` by [Stacks, Tag 08DK]. -/
abbrev extFunctor :
    OXMod.{u, u} S.toRingedSpace ⥤ DerivedCategory (OXMod.{u, u} X.toRingedSpace) :=
  modulePullback f.toLRSHom.toShHom ⋙ tensorModuleComplex X G ⋙ DerivedCategory.Q ⋙
    derivedSheafHomFunctor E

/-! ### The hypothesis -/

/-- **The conclusion of [Stacks, Tag 08DQ] for `E`**: a dual `E^∨` of `E` whose derived tensor
product with an arbitrary object of `D(𝒪_X)` is the derived internal Hom out of `E`,

`E^∨ ⊗^L_{𝒪_X} - ≅ RSheafHom_{𝒪_X}(E, -)`,

naturally in that object.  The source's proof of [Stacks, Tag 08ID] uses exactly this: at `𝒢`,
to identify the `K` of [Stacks, Tag 0DJR] with the `K` of [Stacks, Tag 0DJQ] for `(E^∨, 𝒢)`, and
at each `𝒢 ⊗_{𝒪_X} f^*ℱ`, to identify `Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)` with
`H^i(X, E^∨ ⊗^L_{𝒪_X} (𝒢 ⊗_{𝒪_X} f^*ℱ))`.

Perfectness of `E^∨`, the other assertion of [Stacks, Tag 08DQ], is not a field: it is the
`isPerfect` field of `Stacks.Cohomology.ExtProjectionFormula.ExtProjectionInput` at `E^∨`.  The
derived tensor product is the one of [Stacks, Tag 06YU] that [Stacks, Tag 0A1F] is stated at, so
that the identification lands where that tag can consume it; the isomorphism is not required to
be the canonical map of [Stacks, Tag 08I1], which is what makes this weaker than the tag it
stands for. -/
structure DualSheafHomData where
  /-- The dual `E^∨` of `E`. -/
  dual : DerivedCategory (OXMod.{u, u} X.toRingedSpace)
  /-- `E^∨ ⊗^L_{𝒪_X} - ≅ RSheafHom_{𝒪_X}(E, -)`: the second assertion of
  [Stacks, Tag 08DQ], in the form the source's proof uses it. -/
  iso : (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj dual ≅ derivedSheafHomFunctor E

/-! ### The isomorphism -/

variable [LocallyOfFiniteType f]

/-- **The isomorphisms of [Stacks, Tag 08ID] from a given dual.**  In the situation of
[Stacks, Tag 0DJR], with
`K = Rf_*RSheafHom_{𝒪_X}(E, 𝒢)`, there are isomorphisms

`H^i(S, K ⊗^L_{𝒪_S} ℱ) ≅ Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)`,

functorial in the `𝒪_S`-module `ℱ` — the statement is a natural isomorphism of functors on
`𝒪_S`-modules, so functoriality is part of its type — and `Γ(S, 𝒪_S)`-linear.  The right-hand
side is the `i`-th hypercohomology of `RSheafHom_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)` on `X`, which is
`Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)` by [Stacks, Tag 08DK].  Quasi-coherence of `ℱ` is not assumed;
see `extCohomologyIsoQuasicoherent` for the restriction to quasi-coherent modules that the
source states.

This is the source's proof.  `hdual`, which is [Stacks, Tag 08DQ] for `E`, turns perfectness of
`E` into a dual `E^∨` with `E^∨ ⊗^L_{𝒪_X} - ≅ RSheafHom_{𝒪_X}(E, -)`.  Applying that at `𝒢` and
pushing forward identifies `K` with the `K` of [Stacks, Tag 0DJQ] for `(E^∨, 𝒢)`, applying it at
`𝒢 ⊗_{𝒪_X} f^*ℱ` identifies the right-hand side with `H^i(X, E^∨ ⊗^L_{𝒪_X} (𝒢 ⊗ f^*ℱ))`, and
in between the assertion is [Stacks, Tag 0A1F] at `E^∨`.

Beyond `hdual` nothing is carried here: `h` is the input bundle of [Stacks, Tag 0A1F] at `E^∨`,
whose two carried fields are the projection formula [Stacks, Tag 08EU] at `ℱ` and the flat
identification [Stacks, Tag 08DE], and whose other two fields are the source's assumptions on
`E^∨` and `𝒢`.  The compatibility with boundary maps is not part of this statement; the tag in full,
unconditional and with boundary maps, is
`Stacks.Cohomology.ExtPerfectProjection.extIso_qcoh_boundary`. -/
def extCohomologyIsoSheafHom (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hdual : RingedSpace.IsPerfect (X := X.toRingedSpace) E → DualSheafHomData E)
    (h : ExtProjectionInput f (hdual hE).dual G) (i : ℤ) :
    baseTensorSheafHomFunctor f E G ⋙ cohomologyOnBase S i ≅
      extFunctor f E G ⋙ cohomologyOnSource f i :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0)
        ((derivedTensorProductFunctor S.toRingedSpace.sheaf).mapIso
          ((derivedPushforwardOX f).mapIso
            ((hdual hE).iso.app (DerivedCategory.Q.obj G))).symm))
      (cohomologyOnBase S i) ≪≫
    extCohomologyIso f (hdual hE).dual G h i ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (modulePullback f.toLRSHom.toShHom ⋙ tensorModuleComplex X G ⋙ DerivedCategory.Q)
        (hdual hE).iso)
      (cohomologyOnSource f i)

/-- The full subcategory of quasi-coherent `𝒪_S`-modules, included into all `𝒪_S`-modules. -/
abbrev quasicoherentInclusion (Z : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent (structureSheafOfRings Z.toRingedSpace)).FullSubcategory ⥤
      OXMod.{u, u} Z.toRingedSpace :=
  (SheafOfModules.isQuasicoherent (structureSheafOfRings Z.toRingedSpace)).ι

/-- **The isomorphisms of `extCohomologyIsoSheafHom` for `ℱ` quasi-coherent**: the isomorphisms
`H^i(S, K ⊗^L_{𝒪_S} ℱ) ≅ Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)` of `extCohomologyIsoSheafHom`,
restricted along the inclusion of the quasi-coherent `𝒪_S`-modules.  The restriction carries no
information beyond `extCohomologyIsoSheafHom`, which holds for every `𝒪_S`-module; it is
recorded because quasi-coherence is a hypothesis of the source. -/
def extCohomologyIsoQuasicoherent (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hdual : RingedSpace.IsPerfect (X := X.toRingedSpace) E → DualSheafHomData E)
    (h : ExtProjectionInput f (hdual hE).dual G) (i : ℤ) :
    quasicoherentInclusion S ⋙ baseTensorSheafHomFunctor f E G ⋙ cohomologyOnBase S i ≅
      quasicoherentInclusion S ⋙ extFunctor f E G ⋙ cohomologyOnSource f i :=
  Functor.isoWhiskerLeft (quasicoherentInclusion S)
    (extCohomologyIsoSheafHom f E G hE hdual h i)

end Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent

end
