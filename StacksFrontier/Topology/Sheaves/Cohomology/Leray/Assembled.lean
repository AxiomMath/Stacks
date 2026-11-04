module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Homology.SpectralSequence.SpectralObjectFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.GrothendieckSequenceAbuts
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.LowDegreeSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FunctorialSpectralObject

/-!
# The Leray spectral sequence of a morphism of ringed spaces

For a morphism of ringed spaces `f : X ⟶ Y`, the Leray spectral sequence ([Stacks, Tag 01F2]) is
a functor `D⁺(Mod(𝒪_X)) ⥤ E₂CohomologicalSpectralSequence (Γ(Y, 𝒪_Y)-Mod)` together with a
natural identification of its second page with `H^p(Y, R^q f_* K)`, its abutment on the
hypercohomology of `X` with scalars restricted along `f`, and the low-degree sequence for abelian
sheaves on the underlying spaces. These four data form the structure
`Stacks.Cohomology.LerayCard.LeraySpectralSequenceData`.

## Main definitions

* `Stacks.Cohomology.LerayCard.LeraySpectralSequenceData`: the four data of
  [Stacks, Tag 01F2].
* `Stacks.Cohomology.LerayCard.pageTwoNatIso`: the natural identification of the second page of
  the spectral sequence of the spectral object of a canonical truncation tower, pushed along a
  triangulated functor.
* `Stacks.Cohomology.LerayCard.leraySequence` and
  `Stacks.Cohomology.LerayCard.leraySpectralSequencePageTwoIso`: the `sequence` and
  `pageTwoIso` fields for a morphism of ringed spaces.
* `Stacks.Cohomology.LerayCard.leraySpectralSequenceDataOfAbuts`: the whole structure, given
  its convergence clause.
* `Stacks.Cohomology.LerayCard.leraySpectralSequence`: **the Leray spectral sequence of a
  morphism of ringed spaces**, with no hypothesis on `f`.

## Main results

* `Stacks.Cohomology.LerayCard.abutsTo_leraySequence`: the Leray spectral sequence abuts to the
  hypercohomology of `X`, with scalars restricted along `f`.

## Implementation notes

* `sequence` is `lerayCohomologySpectralObject f ⋙ E₂SpectralSequenceFunctor _`, the
  truncation-tower spectral object
  `Stacks.Cohomology.LerayTruncation.lerayCohomologySpectralObject` read through the functor
  `CategoryTheory.Abelian.SpectralObject.E₂SpectralSequenceFunctor`.
* `pageTwoIso` is the composite of three identifications: the natural first-page identification
  of the spectral sequence of a spectral object (`spectralSequenceFirstPageXNatIso`, whose target
  is the truncation composite `τ^{≥q} τ^{<q+1} ⋙ Φ ⋙ H^{p+q}`); the natural isomorphism
  `τ^{≥q} τ^{<q+1} ≅ H^q ⋙ single q`; and the degree shift
  `single q ⋙ Φ ⋙ H^{p+q} ≅ single 0 ⋙ Φ ⋙ H^p`, whose right-hand side is
  `CategoryTheory.Functor.rightDerivedPlus` by definition.
* `abelianLowDegree` is `Stacks.Cohomology.LerayLowDegree.abelianLerayLowDegreeData`. It is
  available only when the coefficient universe of the abelian sheaves is that of the space:
  the structure needs `(abelianPushforward.{u, max u v} f).PreservesInjectiveObjects`, and the
  only instance is at `.{u, u}`
  (`Stacks.Cohomology.LerayLowDegree.abelianPushforward_preservesInjectiveObjects`). This is a
  universe constraint coming from Mathlib: the two routes to left exactness of the inverse image
  at coefficients `AddCommGrpCat.{max u v}`, namely the instance of
  `CategoryTheory.Functor.SmallCategories` for `sheafPullback` of a representably flat functor
  and `CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits` through
  `CategoryTheory.lan_preservesFiniteLimits_of_flat`, both require
  `Category.{u} AddCommGrpCat.{max u v}`, that is `max u v = u`. So
  `leraySpectralSequenceDataOfAbuts` is stated at `.{u, u}` where [Stacks, Tag 01F2] has
  `.{u, v}`.
* `abuts` is `abutsTo_leraySequence`. Convergence is proved for the truncation-tower spectral
  sequence directly, by `Stacks.Cohomology.LerayModules.abutsTo_lerayCohomologySpectralObject`,
  whose only input is boundedness of the Leray spectral object, unconditional since a right
  derived functor is left `t`-exact; the comparison of two spectral sequences in the proof of
  [Stacks, Tag 01F2] is not used. The abutment family there is `n ↦ H^n(RΓ(Y, ⊤) (Rf_* K))`, and
  it is identified degreewise with `n ↦ H^n(R(restrictScalars) (RΓ(X, f^{-1}⊤) K))` by the
  derived square of [Stacks, Tag 01EZ],
  `Stacks.Cohomology.DerivedPushforwardSections.rightDerivedSectionsRestrictionIso f ⊤`, moved
  onto the abutment by `CategoryTheory.SpectralSequence.AbutsTo.of_iso`. The composition
  isomorphism `R(Γ(Y, -) ∘ f_*) ≅ RΓ(Y, -) ∘ Rf_*` of [Stacks, Tag 015M] is not needed: the
  truncation-tower abutment is already stated on the composite of the two derived functors.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.LerayTruncation

universe u u' v v' w w'

namespace Stacks.Cohomology.LerayCard

attribute [local instance] HasDerivedCategory.standard

-- Pointwise right derivability is found from `EnoughInjectives` by this instance, given
-- precedence over the one that would try to prove termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian
  LerayModules.evaluationAdditive
  DerivedPushforwardSections.modulePushforward_additive
  LerayTruncation.commShiftRightDerivedFunctorPlus
  LerayTruncation.isTriangulatedRightDerivedFunctorPlus

section Generic

variable {B : Type u} {C : Type u'} [Category.{v} B] [Category.{v'} C] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w'} C]

/-- **The second page of the spectral sequence of a cohomology spectral object, naturally.**
At `(p, q)` the second page of the `E₂`-cohomological spectral sequence of
`cohomologySpectralObjectFunctor Φ` is `H^{p+q}(Φ(τ^{≥q} τ^{<q+1} -))`, as a natural
isomorphism of functors on `D⁺(ℬ)`. -/
def pageTwoNatIso (Φ : DerivedCategory.Plus B ⥤ DerivedCategory.Plus C)
    [Φ.CommShift ℤ] [Φ.IsTriangulated] (p q : ℤ) :
    cohomologySpectralObjectFunctor Φ ⋙ Abelian.SpectralObject.E₂SpectralSequenceFunctor C ⋙
        SpectralSequence.pageFunctor _ _ 2 2 ⋙ HomologicalComplex.eval _ _ (p, q) ≅
      DerivedCategory.Plus.TStructure.t.truncGELT q (q + 1) ⋙ Φ ⋙
        DerivedCategory.Plus.homologyFunctor C (p + q) :=
  Functor.isoWhiskerLeft _
    (Abelian.SpectralObject.spectralSequenceFirstPageXNatIso
      Abelian.SpectralObject.coreE₂Cohomological (p, q) (q : EInt) ((q + 1 : ℤ) : EInt)
      rfl rfl (p + q) rfl)

/-- **The second page of the spectral sequence of a cohomology spectral object is a double
derived functor.** At `(p, q)` it is `H^q` of the object followed by the `p`-th right derived
functor computed by `Φ`, naturally in the object. -/
@[sga "4 XVII 5.1.8.1" "partial"]
def pageTwoNatIsoDerived (Φ : DerivedCategory.Plus B ⥤ DerivedCategory.Plus C)
    [Φ.CommShift ℤ] [Φ.IsTriangulated] (p q : ℤ) :
    cohomologySpectralObjectFunctor Φ ⋙ Abelian.SpectralObject.E₂SpectralSequenceFunctor C ⋙
        SpectralSequence.pageFunctor _ _ 2 2 ⋙ HomologicalComplex.eval _ _ (p, q) ≅
      DerivedCategory.Plus.homologyFunctor B q ⋙ DerivedCategory.Plus.singleFunctor B 0 ⋙ Φ ⋙
        DerivedCategory.Plus.homologyFunctor C p :=
  pageTwoNatIso Φ p q ≪≫
    Functor.isoWhiskerRight
        (DerivedCategory.Plus.truncGELTIsoHomologyFunctorCompSingleFunctor q)
        (Φ ⋙ DerivedCategory.Plus.homologyFunctor C (p + q)) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor B q)
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso Φ p q)

end Generic

section Leray

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The functorial Leray spectral sequence**: the `E₂`-cohomological spectral sequence of the
Leray spectral object `Stacks.Cohomology.LerayTruncation.lerayCohomologySpectralObject`, as a
functor on `D⁺(Mod(𝒪_X))`. -/
def leraySequence :
    DerivedCategory.Plus (ModuleSheaves X) ⥤
      E₂CohomologicalSpectralSequence
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op (⊤ : Opens Y.carrier)))) :=
  lerayCohomologySpectralObject f ⋙ Abelian.SpectralObject.E₂SpectralSequenceFunctor _

/-- **The second page of the Leray spectral sequence is `H^p(Y, R^q f_* -)`, naturally**: at
`(p, q)` it is `R^q f_*` followed by the `p`-th right derived functor of `Γ(Y, -)`. -/
def leraySpectralSequencePageTwoIso (p q : ℤ) :
    leraySequence f ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ (p, q) ≅
      (modulePushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleSheaves Y) q ⋙
        (SheafOfModules.evaluation (structureSheafRing Y)
          (op (⊤ : Opens Y.carrier))).rightDerivedPlus p :=
  Functor.isoWhiskerLeft (modulePushforward f).rightDerivedFunctorPlus
    (pageTwoNatIsoDerived
      (SheafOfModules.evaluation (structureSheafRing Y)
        (op (⊤ : Opens Y.carrier))).rightDerivedFunctorPlus p q)

/-- **The Leray spectral sequence abuts to the hypercohomology of the source**: for every `K`,
`leraySequence f` at `K` abuts to `n ↦ H^n(R(restrictScalars) (RΓ(X, f^{-1}⊤) K))`, the
hypercohomology of `X` with scalars restricted along `f`. -/
theorem abutsTo_leraySequence (K : DerivedCategory.Plus (ModuleSheaves X)) :
    SpectralSequence.AbutsTo ((leraySequence f).obj K) (fun n ↦
      (DerivedCategory.Plus.homologyFunctor _ n).obj
        (((SheafOfModules.evaluation (structureSheafRing X)
            (op ((opensMap f).obj (⊤ : Opens Y.carrier)))).rightDerivedFunctorPlus ⋙
          (ModuleCat.restrictScalars
            ((structureSheafHom f).hom.app
              (op (⊤ : Opens Y.carrier))).hom).rightDerivedFunctorPlus).obj K)) :=
  (LerayModules.abutsTo_lerayCohomologySpectralObject f K).of_iso fun n ↦
    (DerivedCategory.Plus.homologyFunctor _ n).mapIso
      ((DerivedPushforwardSections.rightDerivedSectionsRestrictionIso f
        (⊤ : Opens Y.carrier)).symm.app K)

end Leray

/-- **The data of [Stacks, Tag 01F2]** for a morphism of ringed spaces `f : X ⟶ Y`: the
functorial Leray spectral sequence of `Γ(Y, 𝒪_Y)`-modules, its natural second-page
identification with `H^p(Y, R^q f_* K)`, its abutment on the hypercohomology of `X` with
scalars restricted along `f`, and the low-degree Leray sequence for abelian sheaves on the
underlying spaces. -/
structure LeraySpectralSequenceData {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) where
  /-- The canonical low-degree sequence for abelian sheaves on the underlying spaces. -/
  abelianLowDegree : LerayLowDegree.AbelianLerayLowDegreeData.{u, v} f.hom.base
  /-- The spectral sequence, as a functor on the bounded below derived category. -/
  sequence : DerivedCategory.Plus (ModuleSheaves X) ⥤
    E₂CohomologicalSpectralSequence
      (ModuleCat ((structureSheafRing Y).obj.obj (op (⊤ : Opens Y.carrier))))
  /-- The second page is `H^p(Y, R^q f_* -)`, naturally in the complex. -/
  pageTwoIso (p q : ℤ) :
    sequence ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ (p, q) ≅
      (modulePushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleSheaves Y) q ⋙
        (SheafOfModules.evaluation (structureSheafRing Y)
          (op (⊤ : Opens Y.carrier))).rightDerivedPlus p
  /-- The spectral sequence abuts to the hypercohomology of `X`, with scalars restricted
  along `f`. -/
  abuts (K : DerivedCategory.Plus (ModuleSheaves X)) :
    SpectralSequence.AbutsTo (sequence.obj K) (fun n ↦
      (DerivedCategory.Plus.homologyFunctor _ n).obj
        (((SheafOfModules.evaluation (structureSheafRing X)
            (op ((opensMap f).obj (⊤ : Opens Y.carrier)))).rightDerivedFunctorPlus ⋙
          (ModuleCat.restrictScalars
            ((structureSheafHom f).hom.app
              (op (⊤ : Opens Y.carrier))).hom).rightDerivedFunctorPlus).obj K))

/-- **The Leray spectral sequence of a morphism of ringed spaces, given its convergence
clause.** The functorial spectral sequence `leraySequence f`, its natural second-page
identification, and the low-degree sequence for abelian sheaves, together with a given abutment
of `leraySequence f` on the hypercohomology of `X`. -/
def leraySpectralSequenceDataOfAbuts {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (habuts : ∀ K : DerivedCategory.Plus (ModuleSheaves X),
      SpectralSequence.AbutsTo ((leraySequence f).obj K) (fun n ↦
        (DerivedCategory.Plus.homologyFunctor _ n).obj
          (((SheafOfModules.evaluation (structureSheafRing X)
              (op ((opensMap f).obj (⊤ : Opens Y.carrier)))).rightDerivedFunctorPlus ⋙
            (ModuleCat.restrictScalars
              ((structureSheafHom f).hom.app
                (op (⊤ : Opens Y.carrier))).hom).rightDerivedFunctorPlus).obj K))) :
    LeraySpectralSequenceData.{u, u} f where
  abelianLowDegree := LerayLowDegree.abelianLerayLowDegreeData.{u, u} f.hom.base
  sequence := leraySequence f
  pageTwoIso p q := leraySpectralSequencePageTwoIso f p q
  abuts := habuts

/-- **The Leray spectral sequence of a morphism of ringed spaces**, [Stacks, Tag 01F2]. For
`f : X ⟶ Y` a morphism of ringed spaces, this is the functorial `E₂`-cohomological spectral
sequence of `Γ(Y, 𝒪_Y)`-modules on `D⁺(Mod(𝒪_X))` whose second page is `H^p(Y, R^q f_* K)`
naturally in `K`, which abuts to `H^{p+q}(X, K)` with scalars restricted along `f`, together
with the low-degree Leray sequence for abelian sheaves on the underlying spaces.

The abelian sheaves have coefficients in the universe of the space, `.{u, u}`, where
[Stacks, Tag 01F2] allows `.{u, v}`; see the implementation notes of this module. -/
@[stacks 01F2]
def leraySpectralSequence {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    LeraySpectralSequenceData.{u, u} f :=
  leraySpectralSequenceDataOfAbuts f (abutsTo_leraySequence f)

end Stacks.Cohomology.LerayCard

end
