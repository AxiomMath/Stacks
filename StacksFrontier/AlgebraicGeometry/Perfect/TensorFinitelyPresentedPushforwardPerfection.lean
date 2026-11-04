module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.TensorFlat
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness of the derived pushforward of a tensor product, over a Noetherian model

Let `f : X ⟶ S` be a morphism of schemes of finite presentation, let `E` be a perfect object of
`D(𝒪_X)` and let `𝒢^•` be a bounded complex of finitely presented `𝒪_X`-modules, flat over `S`,
whose support is proper over `S`.  [Stacks, Tag 0A1H] asserts two things about
`K = Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)`: that its formation commutes with arbitrary base change, and that
`K` is a perfect object of `D(𝒪_S)`.  The base-change half used below is [Stacks, Tag 0A1D],
`AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_isPullback`.

**This file proves the perfection half from a Noetherian model of the data.**  The source's
proof of that half is a Noetherian approximation: `S` is written as a limit of affine schemes of
finite type over `ℤ`, the morphism `f`, the complex `𝒢^•` and the object `E` are descended to a
finite stage ([Stacks, Tag 01ZM], [Stacks, Tag 01ZR], [Stacks, Tag 05LY],
[Stacks, Tag 081G], [Stacks, Tag 09RF]), [Stacks, Tag 0DJQ] is applied over that Noetherian
stage, and the conclusion is transported back along the base change — using the base-change half.
The theorem below is that last step, with the descended data as hypotheses: a cartesian square

```
X --q--> X₀
|        |
f        f₀
v        v
S --p--> S₀
```

with `S₀` Noetherian and `f₀` of finite presentation, a perfect `E₀` in `D(𝒪_{X₀})` and a
complex `𝒢₀^•` satisfying [Stacks, Tag 0A1H]'s conditions over `S₀`, together with
`Lq^*E₀ ≅ E` and `q^*𝒢₀^• ≅ 𝒢^•`.

## Main results

* `AlgebraicGeometry.FlatProperSupportFinitelyPresented.flatProperSupportComplex_of_isNoetherian`:
  over a Noetherian base the hypothesis of [Stacks, Tag 0A1H] on the complex is the hypothesis of
  [Stacks, Tag 0DJQ] on it, the two differing only in finite presentation versus coherence of the
  terms ([Stacks, Tag 01XZ]).
* `AlgebraicGeometry.isQuasicoherent_homology_of_ringedSpaceIsPerfect`: a perfect object of
  `D(𝒪_X)` has quasi-coherent cohomology in every degree.
* `AlgebraicGeometry.isPerfect_derivedPushforward_derivedTensor_of_noetherianStage`: the
  perfection half of [Stacks, Tag 0A1H], from a Noetherian model of the data.

## Implementation notes

**What the descent would still need.**  The Noetherian model is a hypothesis here and not a
construction, and the obstruction is one single tag: [Stacks, Tag 09RF].  Of the five tags the
source's approximation uses, four are available in this library —
`AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation`
([Stacks, Tag 01ZM] part (1)),
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs` and
`Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_of_isLimit`
([Stacks, Tag 01ZR] parts (1) and (2)),
`AlgebraicGeometry.eventually_isFlatOver_modulePullback` ([Stacks, Tag 05LY]) and
`AlgebraicGeometry.exists_isProper_schemeTheoreticSupport_baseChange_of_isLimit`
([Stacks, Tag 081G]) — and so is the limit presentation of an affine base,
`CommRingCat.exists_colimitPresentation_arrow_finiteType`.  What is missing is the descent of
`E`: [Stacks, Tag 09RF] is carried in
`StacksFrontier/AlgebraicGeometry/Perfect/LimitPerfectObjects.lean` only as the canonical cocone of
functors `D_perf(𝒪_{S_i}) ⥤ D_perf(𝒪_S)` and their coherence, with the clause strings of
`AlgebraicGeometry.DescentSituation.perfectComparison_coherence` and
`AlgebraicGeometry.DescentSituation.perfectTransitionComp_coherence` recording that neither full
faithfulness nor essential surjectivity of the comparison out of the colimit is included.
Essential surjectivity is exactly the statement that a perfect object on the limit is the derived
pullback of a perfect object at a stage, and nothing else in either tree supplies it: the
repository has it as an unproved `Prop`,
`AlgebraicGeometry.PerfectDescendsAlongBaseChangedTower`, and in the relative
form of [Stacks, Tag 0DI8] as the unproved predicate
`AlgebraicGeometry.RelativeDescentSituation.PerfectEssentiallySurjective`; what is proved is the
ring-level [Stacks, Tag 0BC7] and the affine case of [Stacks, Tag 0DI8].

**What is carried, and why.**

* `D`, `hcoh`, `htor` and `htorfin` — the data and the three residues of
  [Stacks, Tag 0DJQ]: the certified derived sheaf tensoring over `f₀⁻¹𝒪_{S₀}`, its two
  pushforward residues, and the fourth clause of [Stacks, Tag 08EV] for the derived tensor
  product, which `Stacks.Cohomology.PerfectPushforward.TensorPushforwardData` carries as its
  `hasFiniteTorDimension` field.  The derived tensor product `T` of that theorem is not carried:
  it is taken to be
  `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, whose `tensor` is the
  bifunctor `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` the base-change map is
  written at, so the two halves meet at one spelling of `⊗^L`.

**What is no longer carried.**  Quasi-coherence of the cohomology of `E₀` is *not* a hypothesis,
although the base-change half carries the corresponding `hE`: the implementation notes of that
file say that the implication perfect ⟹ quasi-coherent cohomology "is not available at this
spelling of the category of `𝒪_X`-modules", and that is no longer the case.
`AlgebraicGeometry.RingedSpace.IsPerfect.isPseudoCoherent` and
`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent` ([Stacks, Tag 08E5]) compose at
`DerivedCategory X₀.Modules`, with `HasDerivedCategory.standard` in scope and with no bridge
written: the two spellings `StrictlyPerfect.OXMod X₀.toRingedSpace` and
`AlgebraicGeometry.Scheme.Modules X₀` of the category of `𝒪_{X₀}`-modules are `rfl`-equal, the
two sheaves of rings being the same term by
`AlgebraicGeometry.RingedSpace.structureSheafOfRings_eq_ringSheaf`, and the conversion check
crosses them.  `AlgebraicGeometry.isQuasicoherent_homology_of_ringedSpaceIsPerfect` below is that
composition.

## References

* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 09RF](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.PerfectPushforward (schemeSite)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S X₀ S₀ : Scheme.{u}}

/-! ### The hypothesis of Stacks 0A1H is the hypothesis of Stacks 0DJQ over a Noetherian base -/

/-- **Over a Noetherian base the two hypotheses on the complex agree.**
`AlgebraicGeometry.FlatProperSupportFinitelyPresented`, the hypothesis of [Stacks, Tag 0A1H] on
`𝒢^•`, asks finite presentation of the terms, while
`Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex`, the hypothesis of
[Stacks, Tag 0DJQ], asks coherence; when the base is Noetherian and `f` is locally of finite
presentation the source is locally Noetherian, where the two conditions on a module coincide by
[Stacks, Tag 01XZ]. The other three clauses — boundedness, flatness over the base and proper
support — are the same conditions and are passed through. -/
public theorem FlatProperSupportFinitelyPresented.flatProperSupportComplex_of_isNoetherian
    (f : X ⟶ S)
    [IsNoetherian S] [LocallyOfFinitePresentation f] {G : CochainComplex X.Modules ℤ}
    (hG : FlatProperSupportFinitelyPresented f G) :
    Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G :=
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  { bounded := hG.bounded
    isCoherent := fun i =>
      (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isFinitePresentation
        (G.X i)).mpr (hG.isFinitePresentation i)
    isFlatOver := hG.isFlatOver
    properSupport := hG.properSupport }

/-! ### Quasi-coherent cohomology from perfectness -/

/-- **A perfect object of `D(𝒪_X)` has quasi-coherent cohomology.** It is pseudo-coherent by
`AlgebraicGeometry.RingedSpace.IsPerfect.isPseudoCoherent`, and a pseudo-coherent object of the
derived category of modules on a scheme lies in `D_QCoh` by [Stacks, Tag 08E5]. -/
public theorem isQuasicoherent_homology_of_ringedSpaceIsPerfect (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (n : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent :=
  isQuasicoherentDerived_of_isPseudoCoherent X E hE.isPseudoCoherent n

/-! ### The perfection half of Stacks 0A1H over a Noetherian model -/

/-- **[Stacks, Tag 0A1H], the perfection half of the conclusion, from a Noetherian model of the
data.** Let

```
X --q--> X₀
|        |
f        f₀
v        v
S --p--> S₀
```

be a cartesian square of schemes with `S₀` Noetherian and `f₀` of finite presentation, let `E₀`
be a perfect object of `D(𝒪_{X₀})` and let `𝒢₀^•` be a bounded complex of finitely presented
`𝒪_{X₀}`-modules, flat over `S₀`, with support proper over `S₀`. Let `E` in `D(𝒪_X)` and
`𝒢^•` on `X` be identified with `Lq^*E₀` and with the ordinary pullback `q^*𝒢₀^•`. Then

`K = Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)`

is a perfect object of `D(𝒪_S)`.

This is the final step of the source's proof of the perfection half, and the whole of it after
the Noetherian approximation: [Stacks, Tag 0DJQ] makes `K₀ = Rf_{0*}(E₀ ⊗^L 𝒢₀^•)` perfect over
the Noetherian base `S₀`, the base-change half of [Stacks, Tag 0A1H] identifies `Lp^*K₀` with
`K`, and [Stacks, Tag 09UA] carries perfectness along `Lp^*`. The approximation itself is the
hypothesis, and the implementation notes of this file name the one tag that blocks it,
[Stacks, Tag 09RF].

Cf. Stacks Tag 0A1H; not registered because it carries the residues `hcoh`, `htor` and
`htorfin` of Stacks Tag 0DJQ, and a Noetherian model of the data as a hypothesis. -/
public theorem isPerfect_derivedPushforward_derivedTensor_of_noetherianStage
    (f : X ⟶ S) (f₀ : X₀ ⟶ S₀) (p : S ⟶ S₀) (q : X ⟶ X₀)
    (hsq : IsPullback q f f₀ p)
    (sq : q.toLRSHom.toShHom ≫ f₀.toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ p.toLRSHom.toShHom)
    [IsNoetherian S₀] (hf₀ : FinitePresentation f₀)
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S₀.toRingedSpace f₀.base))
    (hcoh : letI : LocallyOfFinitePresentation f₀ := hf₀.locallyOfFinitePresentation
      letI : LocallyOfFiniteType f₀ := inferInstance
      Stacks.Cohomology.PerfectPushforward.PushforwardCoherenceResidue f₀
        (Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX f₀))
    (htor : letI : LocallyOfFinitePresentation f₀ := hf₀.locallyOfFinitePresentation
      letI : LocallyOfFiniteType f₀ := inferInstance
      Stacks.Cohomology.PerfectPushforward.PushforwardTorDimensionResidue f₀ D
        (Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX f₀))
    (E₀ : DerivedCategory X₀.Modules)
    (hE₀ : RingedSpace.IsPerfect (X := X₀.toRingedSpace) E₀)
    (G₀ : CochainComplex X₀.Modules ℤ)
    (hG₀ : letI : LocallyOfFinitePresentation f₀ := hf₀.locallyOfFinitePresentation
      FlatProperSupportFinitelyPresented f₀ G₀)
    (htorfin : D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction f₀).obj
      (((derivedTensorProductFunctor X₀.sheaf).obj E₀).obj (DerivedCategory.Q.obj G₀))))
    (E : DerivedCategory X.Modules) (G : CochainComplex X.Modules ℤ)
    (eE : (derivedPullback q.toLRSHom.toShHom).obj E₀ ≅ E)
    (eG : (pullbackComplex q.toLRSHom.toShHom).obj G₀ ≅ G) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) := by
  let : LocallyOfFinitePresentation f₀ := hf₀.locallyOfFinitePresentation
  let : LocallyOfFiniteType f₀ := inferInstance
  have h0 := Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor
    f₀ D (canonicalDerivedTensorProduct (schemeSite X₀).O) hcoh htor E₀ G₀
    { isPerfect := hE₀
      flatProperSupport := hG₀.flatProperSupportComplex_of_isNoetherian f₀
      hasFiniteTorDimension := htorfin }
  have h1 := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    p.toLRSHom.toShHom _ h0
  have h2 : IsIso (tensorFlatBaseChangeMap f₀ p f q sq E₀ G₀) :=
    isIso_tensorFlatBaseChangeMap_of_isPullback f₀ p f q hsq hf₀.quasiCompact hf₀.quasiSeparated
      sq E₀ (isQuasicoherent_homology_of_ringedSpaceIsPerfect E₀ hE₀) G₀ hG₀.minus
      hG₀.isQuasicoherent hG₀.isFlatOver
  have h3 := Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    (@asIso _ _ _ _ _ h2) h1
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} ?_ h3
  exact (derivedPushforward f.toLRSHom.toShHom).mapIso
    (((derivedTensorProductFunctor X.sheaf).mapIso eE).app _ ≪≫
      ((derivedTensorProductFunctor X.sheaf).obj E).mapIso (DerivedCategory.Q.mapIso eG))

end AlgebraicGeometry

end
