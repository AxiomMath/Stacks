module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWatts
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsHypotheses
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.LinearTensorEquivalence
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic

/-!
# Eilenberg-Watts runs on the functor of the affine case of Tag 0EX3 (b)

The proof of [Stacks, Tag 0EX3] (b) reduces to `Y' = Spec R'` and there considers the
endofunctor of `R'`-modules

> `Φ(M) = H^d(X', F' ⊗_{𝒪_{X'}} (f')^* M~)`

asserts that it is right exact and commutes with direct sums, and concludes by Eilenberg-Watts
that it is tensoring with `Φ(R') = H^d(X', F')`. The source constructs **no global sheaf map**
for (b): the reduction to an affine base is what makes the statement an `R'`-module statement,
and the affine case therefore needs neither an open-restriction comparison nor a canonical map
on sheaves.

This file assembles `Φ` and runs `Stacks.EilenbergWatts.iso` on it. `Φ` factors as

> `T ⋙ H^d(X', -) ⋙ restrictScalars`

where `T : ModuleCat R' ⥤ QCoh(X')` is the geometric factor `M ↦ F' ⊗ (f')^* M~` and the tail
is `Stacks.AlgebraicGeometry.TopDegreeBaseChange.qcohCohomology` followed by restriction of
scalars along `R' ⟶ Γ(X', ⊤)`. **The geometric factor is taken as an argument, together with
the four properties Eilenberg-Watts needs of it.** What is proved here is that those four
properties of `T` plus the four properties of the cohomological tail — the two in
`StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear` and the two in
`StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsHypotheses` — give the four
properties of `Φ`, and hence the Eilenberg-Watts isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineTopDegreeFunctor`: `Φ`, as an endofunctor
  of `ModuleCat R'`, built from a geometric factor `T`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.linear_restrictScalars`: restriction of scalars
  along an algebra map is linear over the base ring. This is the tail of `Φ`.
* `additive_affineTopDegreeFunctor`, `linear_affineTopDegreeFunctor`,
  `preservesColimitsOfShape_discrete_affineTopDegreeFunctor` and
  `preservesFiniteColimits_affineTopDegreeFunctor`: the four hypotheses of
  `Stacks.EilenbergWatts.iso`, for `Φ`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineTopDegreeFunctorIso`: **Eilenberg-Watts
  for `Φ`.** `Φ` is tensoring with the `R'`-module `Φ(R')`. This is the conclusion the affine
  case of [Stacks, Tag 0EX3] (b) rests on.
* `isLinearRightExactAndPreservesDirectSums_affineTopDegreeFunctor`, in the same namespace:
  the same four properties of `Φ`, read as membership of the full subcategory of
  [Stacks, Tag 0GNV]. The library has a **second, stronger** Eilenberg-Watts: the equivalence
  `ModuleCat.tensorFunctorEquivalence`, whose object property
  `ModuleCat.IsLinearRightExactAndPreservesDirectSums` is literally the conjunction of the three
  non-additivity hypotheses of `Stacks.EilenbergWatts.iso`. `Φ` satisfies it, so the affine case
  of (b) has two independent routes to its conclusion.

## Implementation notes

*What is not here, stated precisely.* The geometric factor `T` is not constructed. Its
underlying formula is `tilde.functor ⋙ Scheme.Modules.pullback f' ⋙ tensorLeftFunctor F'`,
whose values are quasi-coherent by `AlgebraicGeometry.tilde`'s own instance,
`AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent` and
`AlgebraicGeometry.tensorSheaf_isQuasicoherent`, so the lift through
`CategoryTheory.ObjectProperty.lift` is available; and its additivity, right exactness and
preservation of direct sums are available from the three factors, `tilde` being a left adjoint
(`AlgebraicGeometry.tilde.adjunction`), `Scheme.Modules.pullback` likewise, and
`Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits` giving the tensor factor.
Its **`R'`-linearity** comes in three named pieces: `Functor.Linear R`
for `AlgebraicGeometry.tilde.functor` is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.linear_tildeFunctor`, and the pullback
and tensor halves are `over_pullback_linear` and `tensorLeft_linear` in
`StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic`.

*Two spellings of the ring of global functions.* `moduleGlobalSections` is valued in
`ModuleCat Γ(X, ⊤)`, the `CommRingCat` spelling, while `AlgebraicGeometry.baseRingToSections`
returns a map into the `RingCat` spelling `X.ringCatSheaf.obj.obj (op ⊤)`. The two carriers are
definitionally equal and instance search does not cross between them, so the algebra structure
is named once at the `Γ` spelling — which is what
`Stacks.Cohomology.AffineBase.baseSectionsAlgebra` already does — and the restriction of
scalars is taken along `algebraMap` rather than along `baseRingToSections` directly.

*Declared types for the composites.* Three of the four hypotheses assemble by instance search
only after both factors of `qcohCohomology` are named with a declared type through
`X.Modules`: the inclusion of the quasi-coherent modules reaches the middle category as
`SheafOfModules X.ringCatSheaf` and the cohomology functor reaches it as `X.Modules`, and the
composite instances do not fire across that gap. This is the documented transparency cure and
no transparency option is set.

*Two Eilenberg-Watts theorems in the library, and this file names both.*
`Stacks.EilenbergWatts.iso`
(`StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWatts`) gives the natural
isomorphism `tensorLeft (F R) ≅ F` for one functor. `ModuleCat.tensorFunctorEquivalence`,
which carries [Stacks, Tag 0GNV], gives
the *equivalence* between modules over `A ⊗_R B` and the functors themselves, which is strictly
more: it is natural in the functor as well. Their hypotheses coincide --
`ModuleCat.IsLinearRightExactAndPreservesDirectSums R A B` unfolds to `F.Linear R`,
`PreservesFiniteColimits F` and `∀ J, PreservesColimitsOfShape (Discrete J) F` -- so anything
that feeds one feeds the other, and the two overlap. That is recorded here as a theorem rather
than as a comment so that the overlap is machine-checkable.

*No `@[stacks]` attribute.* `Φ` is an object inside the proof of [Stacks, Tag 0EX3] (b), not a
conclusion of the tag, and the Eilenberg-Watts step is the one the source leaves to the reader
and that `StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWatts` already
carries. The Tag 0GNV attribute is on
`ModuleCat.tensorFunctorEquivalence`, where it belongs; the membership statement below is not a
member of a covering set for it.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase
open scoped ModuleCat.Algebra

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **Restriction of scalars along an algebra map is linear over the base ring.** The `R`-action
on a morphism of `S`-modules is multiplication by `algebraMap R S`, which is what the `R`-action
on the restricted module is too, so the two sides agree on the nose. -/
theorem linear_restrictScalars (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Functor.Linear R (ModuleCat.restrictScalars.{u} (algebraMap R S)) := by
  rw [Functor.linear_iff]
  intro M r
  apply ModuleCat.hom_ext
  rfl

variable (R : Type u) [CommRing R] (W : Over (Spec (.of R))) (d : ℕ)

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

/-- **The functor `Φ` of the affine case of [Stacks, Tag 0EX3] (b)**,
`M ↦ H^d(X', F' ⊗ (f')^* M~)`, as an endofunctor of `ModuleCat R'`. The geometric factor `T`,
which carries `M` to the quasi-coherent module `F' ⊗ (f')^* M~`, is an argument; the tail is the
degree-`d` cohomology of `X'` followed by restriction of scalars along the structure morphism
read at the top open. -/
def affineTopDegreeFunctor
    (T : ModuleCat.{u} R ⥤
      (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  T ⋙ qcohCohomology W.left d ⋙ ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))

section Hypotheses

variable (T : ModuleCat.{u} R ⥤
  (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory)

/-- **The first hypothesis of `Stacks.EilenbergWatts.iso` for `Φ`.** -/
theorem additive_affineTopDegreeFunctor [T.Additive] :
    (affineTopDegreeFunctor R W d T).Additive := by
  unfold affineTopDegreeFunctor
  infer_instance

/-- **The second hypothesis of `Stacks.EilenbergWatts.iso` for `Φ`**: `R`-linearity. The
cohomological half is `Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections`
and the tail is `linear_restrictScalars`. -/
theorem linear_affineTopDegreeFunctor
    (hT : letI : Linear R (SheafOfModules.{u} W.left.ringCatSheaf) := modulesLinear R W
      Functor.Linear R T) :
    Functor.Linear R (affineTopDegreeFunctor R W d T) := by
  let _ : Linear R (SheafOfModules.{u} W.left.ringCatSheaf) := modulesLinear R W
  let _ : Linear R W.left.Modules := modulesLinear R W
  have hT' := hT
  -- Both factors of `qcohCohomology` are named with a declared type through `W.left.Modules`:
  -- without that the middle category is reached by two spellings and the composite instance
  -- does not fire.
  let iotaP : (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory ⥤
      W.left.Modules := ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf)
  let H : W.left.Modules ⥤ ModuleCat.{u} Γ(W.left, ⊤) :=
    (moduleGlobalSections W.left).rightDerived d
  have hι : Functor.Linear R iotaP := inferInstanceAs (Functor.Linear R
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf)))
  have hH : Functor.Linear R H := linear_rightDerived_moduleGlobalSections R W d
  have hqc : Functor.Linear R (qcohCohomology W.left d) :=
    show Functor.Linear R (iotaP ⋙ H) from inferInstance
  have hrs : Functor.Linear R (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))) :=
    linear_restrictScalars R Γ(W.left, ⊤)
  unfold affineTopDegreeFunctor
  infer_instance

/-- **The fourth hypothesis of `Stacks.EilenbergWatts.iso` for `Φ`**: `Φ` commutes with
arbitrary direct sums. The cohomological half is
`preservesColimitsOfShape_discrete_qcohCohomology`, which is [Stacks, Tag 01FF] carried to the
`ModuleCat`-valued functor and from directed colimits to coproducts. -/
theorem preservesColimitsOfShape_discrete_affineTopDegreeFunctor
    [CompactSpace (W.left : Type u)] [QuasiSeparatedSpace (W.left : Type u)]
    (hT : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) T) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (affineTopDegreeFunctor R W d T) := by
  have ha := hT J
  have hb := preservesColimitsOfShape_discrete_qcohCohomology W.left d J
  unfold affineTopDegreeFunctor
  infer_instance

/-- **The third hypothesis of `Stacks.EilenbergWatts.iso` for `Φ`**: `Φ` is right exact. The
cohomological half is `preservesFiniteColimits_qcohCohomology`, whose input is the top-degree
vanishing that conclusion (a) of [Stacks, Tag 0EX3] supplies through [Stacks, Tag 01XK]. -/
theorem preservesFiniteColimits_affineTopDegreeFunctor [PreservesFiniteColimits T]
    (hvan : ∀ F : W.left.Modules, F.IsQuasicoherent →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj F)) :
    PreservesFiniteColimits (affineTopDegreeFunctor R W d T) := by
  have h := preservesFiniteColimits_qcohCohomology W.left d hvan
  unfold affineTopDegreeFunctor
  infer_instance

/-- **Eilenberg-Watts for the functor of the affine case of [Stacks, Tag 0EX3] (b).** `Φ` is
tensoring with the `R`-module `Φ(R)`, which is the conclusion the source draws from

> *"Any right exact `R'`-linear functor `Mod_{R'} → Mod_{R'}` which commutes with direct sums is
> given by tensoring with an `R'`-module (omitted; left as exercise for the reader)."*

The exercise is `Stacks.EilenbergWatts.iso`; what is checked here is that the geometric factor's
four properties and the cohomological tail's four properties compose to the four it asks for.
Over an affine base the vanishing hypothesis is supplied unconditionally by
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.isZero_cohomology_of_lt`, and the two
finiteness hypotheses on the space by `compactSpace_X'` and `quasiSeparatedSpace_X'`. -/
def affineTopDegreeFunctorIso
    [T.Additive] [PreservesFiniteColimits T]
    (hTsum : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) T)
    (hTlin : letI : Linear R (SheafOfModules.{u} W.left.ringCatSheaf) := modulesLinear R W
      Functor.Linear R T)
    (hvan : ∀ F : W.left.Modules, F.IsQuasicoherent →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj F))
    [CompactSpace (W.left : Type u)] [QuasiSeparatedSpace (W.left : Type u)] :
    MonoidalCategory.tensorLeft
        ((affineTopDegreeFunctor R W d T).obj (ModuleCat.of R R)) ≅
      affineTopDegreeFunctor R W d T :=
  haveI := additive_affineTopDegreeFunctor R W d T
  haveI := linear_affineTopDegreeFunctor R W d T hTlin
  haveI := fun J : Type u =>
    preservesColimitsOfShape_discrete_affineTopDegreeFunctor R W d T hTsum J
  haveI := preservesFiniteColimits_affineTopDegreeFunctor R W d T hvan
  Stacks.EilenbergWatts.iso (affineTopDegreeFunctor R W d T)

/-- **`Φ` lies in the full subcategory classified by [Stacks, Tag 0GNV].** The object property
`ModuleCat.IsLinearRightExactAndPreservesDirectSums R R R` is exactly `R`-linearity, right
exactness and preservation of arbitrary direct sums, so this is the four hypotheses above
repackaged for the library's second Eilenberg-Watts theorem,
`ModuleCat.tensorFunctorEquivalence`. The affine case of [Stacks, Tag 0EX3] (b) can therefore be
concluded from either. -/
theorem isLinearRightExactAndPreservesDirectSums_affineTopDegreeFunctor
    [T.Additive] [PreservesFiniteColimits T]
    (hTsum : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) T)
    (hTlin : letI : Linear R (SheafOfModules.{u} W.left.ringCatSheaf) := modulesLinear R W
      Functor.Linear R T)
    (hvan : ∀ F : W.left.Modules, F.IsQuasicoherent →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj F))
    [CompactSpace (W.left : Type u)] [QuasiSeparatedSpace (W.left : Type u)] :
    ModuleCat.IsLinearRightExactAndPreservesDirectSums R R R
      (affineTopDegreeFunctor R W d T) :=
  ⟨linear_affineTopDegreeFunctor R W d T hTlin,
    preservesFiniteColimits_affineTopDegreeFunctor R W d T hvan,
    fun J => preservesColimitsOfShape_discrete_affineTopDegreeFunctor R W d T hTsum J⟩

end Hypotheses

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
