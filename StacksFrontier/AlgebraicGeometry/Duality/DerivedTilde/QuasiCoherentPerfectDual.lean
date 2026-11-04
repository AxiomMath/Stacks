module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidalUnitors
public import StacksFrontier.AlgebraicGeometry.Duality.InternalHom.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularRightAdjoint.SheafHom
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidalModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual

/-!
# Left duals of perfect objects of `D_QCoh(𝒪_X)`

For a scheme `X` and a perfect object `K` of `D(𝒪_X)`, the derived dual
`K^∨ = R𝓗om(K, 𝒪_X)` is a left dual of `K` (Stacks 0FPC). This file carries that exact pairing
from the standard model of `D(𝒪_X)`, where it is constructed, to the locally small model and then
to the full monoidal subcategory `D_QCoh(𝒪_X)`, the dual having quasi-coherent cohomology sheaves.

## Main definitions

* `Stacks.Duality.exactPairingDerivedDualStandard`: the exact pairing `(K, K^∨)` at the standard
  model of `D(𝒪_X)`.
* `Stacks.Duality.perfectDual`: the dual of a perfect object of `D_QCoh(𝒪_X)`, as an object of
  `D_QCoh(𝒪_X)`.
* `Stacks.Duality.exactPairingPerfectDual`: the exact pairing `(K, K^∨)` in `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.Duality.nonempty_hasRightDual_of_isPerfect`: every perfect object of `D_QCoh(𝒪_X)` has
  a right dual.
* `Stacks.Duality.nonempty_hasRightDual_subcategory_of_isCompactObject`: for `X` qcqs, so does
  every compact object of `D_QCoh(𝒪_X)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {X : Scheme.{u}}

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The left dual of a perfect object of `D(𝒪_X)` at the standard model.** For a perfect `K`,
`K^∨ = R𝓗om(K, 𝒪_X)` with the coevaluation and the evaluation of Stacks 0FPC is an exact pairing
in the monoidal structure of Stacks 0FPT on the standard model of `D(𝒪_X)`. -/
@[instance_reducible]
def exactPairingDerivedDualStandard
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace
      (HasDerivedCategory.standard _) K) :
    letI := Scheme.Modules.standardDerivedMonoidal X
    ExactPairing K (Stacks.SheafOfModules.derivedDual X.sheaf K) :=
  Stacks.SheafOfModules.exactPairingDerivedDual X.sheaf K
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X.toRingedSpace K hK)

end Standard

/-- **The derived dual of a perfect object has quasi-coherent cohomology sheaves.** For `K`
perfect in `D(𝒪_X)`, the cohomology sheaves of `K^∨ = R𝓗om(K, 𝒪_X)` are quasi-coherent: `K` is
pseudo-coherent and `𝒪_X` is in `D⁺_QCoh(𝒪_X)` (Stacks 0A6H). -/
theorem isQuasicoherent_homology_derivedDual (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      (Stacks.SheafOfModules.derivedDual X.sheaf K)).IsQuasicoherent :=
  InternalHom.isQuasicoherent_homology_derivedSheafHom_of_isPseudoCoherent K
    (DerivedPushforward.derivedStructureSheaf X).obj
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect K hK)
    ⟨KoszulRegular.isBoundedBelow_singleFunctor_obj (SheafOfModules.unit X.ringCatSheaf),
      (DerivedPushforward.derivedStructureSheaf X).property⟩ i

/-- **The dual of a perfect object of `D_QCoh(𝒪_X)`**: the derived dual `K^∨ = R𝓗om(K, 𝒪_X)`,
which has quasi-coherent cohomology sheaves. -/
def perfectDual (K : quasiCoherentDerivedCategory X)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj) :
    quasiCoherentDerivedCategory X :=
  ⟨Stacks.SheafOfModules.derivedDual X.sheaf K.obj,
    fun i => isQuasicoherent_homology_derivedDual K.obj hK i⟩

/-- The underlying object of `perfectDual` is the derived dual. -/
theorem perfectDual_obj (K : quasiCoherentDerivedCategory X)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj) :
    (perfectDual K hK).obj = Stacks.SheafOfModules.derivedDual X.sheaf K.obj :=
  rfl

/-- **The left dual of a perfect object of `D_QCoh(𝒪_X)`.** For `K` perfect, the derived dual
`K^∨ = R𝓗om(K, 𝒪_X)` is a left dual of `K` in the monoidal category `D_QCoh(𝒪_X)`: the exact
pairing of Stacks 0FPC at the standard model, carried to the locally small model and reflected
along the fully faithful monoidal inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`. -/
@[instance_reducible]
def exactPairingPerfectDual (K : quasiCoherentDerivedCategory X)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj) :
    ExactPairing K (perfectDual K hK) :=
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI : ExactPairing ((ObjectProperty.ι _).obj K) ((ObjectProperty.ι _).obj (perfectDual K hK)) :=
    Scheme.Modules.exactPairingOfStandard X K.obj _
      (exactPairingDerivedDualStandard K.obj
        ((AlgebraicGeometry.PerfectApproximation.isPerfect_standard_iff K.obj).2 hK))
  ExactPairing.ofFullyFaithful (ObjectProperty.ι _) K (perfectDual K hK)

/-- **Every perfect object of `D_QCoh(𝒪_X)` has a right dual**, namely `perfectDual`. -/
theorem nonempty_hasRightDual_of_isPerfect (K : quasiCoherentDerivedCategory X)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj) :
    Nonempty (HasRightDual K) :=
  ⟨@HasRightDual.mk _ _ _ K (perfectDual K hK) (exactPairingPerfectDual K hK)⟩

/-- **Every compact object of `D_QCoh(𝒪_X)` has a right dual** for the full monoidal subcategory
structure `Stacks.Duality.monoidalCategory_quasiCoherentDerivedCategory`, for `X` quasi-compact and
quasi-separated: it is perfect. -/
theorem nonempty_hasRightDual_subcategory_of_isCompactObject [CompactSpace X]
    [QuasiSeparatedSpace X] (K : quasiCoherentDerivedCategory X) (hK : IsCompactObject.{u} K) :
    Nonempty (HasRightDual K) :=
  nonempty_hasRightDual_of_isPerfect K (isPerfect_of_isCompactObject K hK)

end Stacks.Duality

end
