module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsSituation
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonFunctor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonQcoh

/-!
# The two functors of Tag 0EX3 (b) over an affine base, read on modules over the base ring

Over an affine base `Y'` the quasi-coherent modules are the modules over `R' = Γ(Y', ⊤)`, by
[Stacks, Tag 01I7]: the associated-module functor and global sections are mutually inverse on
them.  This file composes the two functors of conclusion (b) of [Stacks, Tag 0EX3] with that
comparison, obtaining two **endofunctors of `ModuleCat R'`**, and verifies for each of them the
three hypotheses of the Eilenberg-Watts rigidity criterion
`Stacks.EilenbergWatts.isIso_app_of_isIso_app_self_of_natIso` — additivity, right exactness and
preservation of arbitrary direct sums.

Both are built on the geometric factor
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactor`, `M ↦ F ⊗ g^* M~` for a scheme
over `Spec R'`, whose three hypotheses are proved unconditionally: the source functor is that
factor taken on the base itself, at the module `R^d f'_* F'`, and the target functor is that
factor taken on `X'` at `F'`, followed by the degree-`d` cohomology of `X'`.  Nothing has to be
proved about the source's cohomological tail, because global sections of quasi-coherent modules
on an affine scheme is an **equivalence**, hence preserves every colimit.

## Main definitions

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `qcohGlobalSections`: global sections of the quasi-coherent modules of a scheme.
* `baseOver`: the affine base of a situation, read as a scheme over the spectrum of its own ring
  of functions.
* `affineSourceFunctor`: `M ↦ Γ(R^d f'_* F' ⊗ M~, ⊤)`.
* `affineTargetFunctor`: `M ↦ H^d(X', F' ⊗ (f')^* M~)`, with its scalars restricted along
  `(f')^♯`.

## Main results

* `isEquivalence_qcohGlobalSections`: **on an affine scheme, global sections is an equivalence
  from the quasi-coherent modules to the modules over the ring of functions.**
* `additive_affineSourceFunctor`, `preservesFiniteColimits_affineSourceFunctor`,
  `preservesColimitsOfShape_discrete_affineSourceFunctor`: the three hypotheses, for the source.
* `additive_affineTargetFunctor`, `preservesFiniteColimits_affineTargetFunctor`,
  `preservesColimitsOfShape_discrete_affineTargetFunctor`: the three, for the target.

## Implementation notes

*Why the scalars are restricted along `(f')^♯` and not along the algebra map.* The cohomology
`H^d(X', -)` is a module over `Γ(X', ⊤)`, and what makes it one over `Γ(Y', ⊤)` is restriction of
scalars.  Two ring maps do the job and they are *equal*, by
`Stacks.Cohomology.AffineBase.baseRingToSections_isoSpec_top`: the algebra map of
`Stacks.Cohomology.AffineBase.baseSectionsAlgebra`, which
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeFunctor` uses, and `(f')^♯` read
at the top open, which is the one [Stacks, Tag 01XK] is stated at.  The second is taken here, so
that the comparison with the sections of the higher direct image needs no transport along that
equality; the three hypotheses are reproved for it from the same inputs rather than quoted from
`topDegreeFunctor`, which is three lines each.

*Why `Stacks.Coherent.affineTilde` is not the comparison used.* The associated-module functor of
an affine scheme is available in two shapes, `Stacks.Coherent.affineTilde` and the two leading
factors `tildeFactor ⋙ pullbackFactor` of the geometric factor.  The second is the one
whose colimit-preservation instances are keyed on declarations whose codomains are spelled
through `AlgebraicGeometry.Scheme.Modules`, and the directory records that instance search does
not cross between that spelling and `SheafOfModules` of the structure sheaf; composites built
from the first shape therefore fail to acquire the instances.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Coherent
open Stacks.Cohomology.AffineBase
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-! ### Global sections of quasi-coherent modules on an affine scheme -/

/-- The global sections of the quasi-coherent modules of a scheme, as a functor to modules over
the ring of functions. -/
def qcohGlobalSections (Z : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory ⥤ ModuleCat.{u} Γ(Z, ⊤) :=
  ObjectProperty.ι (SheafOfModules.isQuasicoherent Z.ringCatSheaf) ⋙ moduleGlobalSections Z

variable (Z : Scheme.{u})

/-- Global sections of quasi-coherent modules is additive. -/
instance additive_qcohGlobalSections : (qcohGlobalSections Z).Additive where
  map_add := (moduleGlobalSections Z).map_add

/-- **Every module over the ring of functions of an affine scheme is the module of sections of a
quasi-coherent module**, namely of the associated one. -/
instance essSurj_qcohGlobalSections [IsAffine Z] : (qcohGlobalSections Z).EssSurj :=
  ⟨fun M => ⟨⟨(affineTilde Z).obj M, affineTilde_quasicoherent Z M⟩,
    ⟨show (qcohGlobalSections Z).obj _ ≅ M from (affineTildeSectionsIso Z M).symm⟩⟩⟩

/-- **On an affine scheme global sections is an equivalence from the quasi-coherent modules to
the modules over the ring of functions.**  This is [Stacks, Tag 01I7]: it is fully faithful by
`Stacks.Coherent.affineQuasicoherentSectionsFullyFaithful` and essentially surjective because
every module is the sections of its associated module. -/
instance isEquivalence_qcohGlobalSections [IsAffine Z] : (qcohGlobalSections Z).IsEquivalence :=
  ⟨(affineQuasicoherentSectionsFullyFaithful Z).faithful,
    (affineQuasicoherentSectionsFullyFaithful Z).full, inferInstance⟩

/-- Being an equivalence, global sections of quasi-coherent modules on an affine scheme
preserves every colimit. -/
instance preservesColimitsOfSize_qcohGlobalSections [IsAffine Z] :
    PreservesColimitsOfSize.{u, u} (qcohGlobalSections Z) :=
  Adjunction.leftAdjoint_preservesColimits (qcohGlobalSections Z).asEquivalence.toAdjunction

/-- In particular it is right exact. -/
instance preservesFiniteColimits_qcohGlobalSections [IsAffine Z] :
    PreservesFiniteColimits (qcohGlobalSections Z) := inferInstance

/-! ### Restriction of scalars preserves direct sums -/

/-- **Restriction of scalars along a ring map commutes with arbitrary direct sums**, colimits of
modules being computed on the underlying abelian groups. -/
instance preservesColimitsOfShape_discrete_restrictScalars {A B : Type u} [Ring A] [Ring B]
    (φ : A →+* B) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (ModuleCat.restrictScalars.{u} φ) :=
  ⟨fun {_} => inferInstance⟩

/-! ### The two functors of conclusion (b) over an affine base -/

variable (S : TopDegreeBaseChangeSituation.{u}) [IsAffine S.Y'] (F' : S.X'.Modules)
  [F'.IsQuasicoherent]

omit [IsAffine S.Y'] in
/-- **The top higher direct image of a quasi-coherent module in a situation is
quasi-coherent**, by [Stacks, Tag 01XJ] and the finiteness of `f'`. -/
theorem isQuasicoherent_topDirectImage_f' :
    (topDirectImage S.f' F' S.d).IsQuasicoherent := by
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  infer_instance

/-- `R^d f'_* F'`, as a quasi-coherent module on the base. -/
abbrev topDirectImageQcoh : (SheafOfModules.isQuasicoherent S.Y'.ringCatSheaf).FullSubcategory :=
  ⟨topDirectImage S.f' F' S.d, isQuasicoherent_topDirectImage_f' S F'⟩

/-- `F'`, as a quasi-coherent module on `X'`. -/
abbrev coefficientQcoh : (SheafOfModules.isQuasicoherent S.X'.ringCatSheaf).FullSubcategory :=
  ⟨F', inferInstance⟩

/-- **The affine base of a situation, read as a scheme over the spectrum of its own ring of
functions.**  Its underlying scheme is `S.Y'` itself, as that of
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.affineBaseOver` is `S.X'`. -/
abbrev baseOver : Over (Spec (CommRingCat.of Γ(S.Y', ⊤))) := Over.mk S.Y'.isoSpec.hom

/-- **The source functor of conclusion (b) over an affine base, read on modules over the base
ring**: `M ↦ Γ(R^d f'_* F' ⊗_{𝒪_{Y'}} M~, ⊤)`. -/
abbrev affineSourceFunctor : ModuleCat.{u} Γ(S.Y', ⊤) ⥤ ModuleCat.{u} Γ(S.Y', ⊤) :=
  geometricFactor Γ(S.Y', ⊤) (baseOver S) (topDirectImageQcoh S F') ⋙ qcohGlobalSections S.Y'

/-- **The target functor of conclusion (b) over an affine base, read on modules over the base
ring**: `M ↦ H^d(X', F' ⊗_{𝒪_{X'}} (f')^* M~)`, with its scalars restricted along `(f')^♯`. -/
abbrev affineTargetFunctor : ModuleCat.{u} Γ(S.Y', ⊤) ⥤ ModuleCat.{u} Γ(S.Y', ⊤) :=
  geometricFactor Γ(S.Y', ⊤) S.affineBaseOver (coefficientQcoh S F') ⋙
    qcohCohomology S.X' S.d ⋙ ModuleCat.restrictScalars S.f'.appTop.hom

/-- **The first Eilenberg-Watts hypothesis for the source functor.** -/
instance additive_affineSourceFunctor : (affineSourceFunctor S F').Additive :=
  inferInstanceAs ((geometricFactor Γ(S.Y', ⊤) (baseOver S) (topDirectImageQcoh S F') ⋙
    qcohGlobalSections S.Y').Additive)

/-- **The second Eilenberg-Watts hypothesis for the source functor**: right exactness. -/
instance preservesFiniteColimits_affineSourceFunctor :
    PreservesFiniteColimits (affineSourceFunctor S F') :=
  inferInstanceAs (PreservesFiniteColimits
    (geometricFactor Γ(S.Y', ⊤) (baseOver S) (topDirectImageQcoh S F') ⋙
      qcohGlobalSections S.Y'))

/-- **The third Eilenberg-Watts hypothesis for the source functor**: it commutes with arbitrary
direct sums. -/
theorem preservesColimitsOfShape_discrete_affineSourceFunctor (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (affineSourceFunctor S F') :=
  have := preservesColimitsOfShape_discrete_geometricFactor Γ(S.Y', ⊤) (baseOver S)
    (topDirectImageQcoh S F') J
  inferInstance

/-- **The first Eilenberg-Watts hypothesis for the target functor.** -/
instance additive_affineTargetFunctor : (affineTargetFunctor S F').Additive :=
  inferInstanceAs ((geometricFactor Γ(S.Y', ⊤) S.affineBaseOver (coefficientQcoh S F') ⋙
    qcohCohomology S.X' S.d ⋙ ModuleCat.restrictScalars S.f'.appTop.hom).Additive)

/-- **The second Eilenberg-Watts hypothesis for the target functor**: right exactness.  The
cohomological factor is right exact because the degree-`(d+1)` cohomology of a quasi-coherent
module on `X'` vanishes, which is conclusion (a) of [Stacks, Tag 0EX3] through
[Stacks, Tag 01XK]. -/
theorem preservesFiniteColimits_affineTargetFunctor :
    PreservesFiniteColimits (affineTargetFunctor S F') :=
  have := TopDegreeBaseChangeSituation.preservesFiniteColimits_qcohCohomology_X' S
  inferInstance

/-- **The third Eilenberg-Watts hypothesis for the target functor**: it commutes with arbitrary
direct sums.  The cohomological factor does because `X'` is quasi-compact and
quasi-separated. -/
theorem preservesColimitsOfShape_discrete_affineTargetFunctor (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (affineTargetFunctor S F') :=
  have := preservesColimitsOfShape_discrete_geometricFactor Γ(S.Y', ⊤) S.affineBaseOver
    (coefficientQcoh S F') J
  have := TopDegreeBaseChangeSituation.preservesColimitsOfShape_discrete_qcohCohomology_X'
    S J
  inferInstance

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
