module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorAmplitudeQuasiCoherentTests
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.RestrictTensorModule

/-!
# The quasi-coherent test modules of an open subscheme come from the whole scheme

For an open subscheme `U ⊆ X` whose inclusion `j : U → X` is quasi-compact and quasi-separated,
every quasi-coherent `𝒪_U`-module is the restriction of a quasi-coherent `𝒪_X`-module, namely its
direct image along `j`. Consequently condition (2) of Stacks 08EA — the derived tensor product of
`E` with every quasi-coherent module has no cohomology outside `[a, b]` — passes from `X` to `U`.

## Main results

* `AlgebraicGeometry.restrictModulesPushforwardIso`: the restriction to `U` of the direct image
  along `U.ι` is isomorphic to the identity.
* `AlgebraicGeometry.exists_isQuasicoherent_restrictModules_iso`: **essential surjectivity of
  `QCoh(𝒪_X) → QCoh(𝒪_U)`** for `U.ι` quasi-compact and quasi-separated, and
  `AlgebraicGeometry.exists_isQuasicoherent_restrictModules_iso_of_isAffineOpen`, the case of an
  affine open `U` of a quasi-separated scheme.
* `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent.restrictModules`: **condition
  (2) of Stacks 08EA restricts to an open subscheme** with the same interval.

## References

* [Stacks Project, Lemma 36.10.3 (Tag 08EA)](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Lemma 26.24.1 (Tag 01LC)](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry

universe u

/-- The restriction to `U` of the direct image along `U.ι` of an `𝒪_U`-module `G` is isomorphic
to `G`, via the counit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. -/
def restrictModulesPushforwardIso {X : Scheme.{u}} (U : X.Opens) (G : U.toScheme.Modules) :
    (AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U).obj
        ((Scheme.Modules.pushforward U.ι).obj G) ≅ G :=
  (AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor X U).app _ ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app G

/-- **`QCoh(𝒪_X) → QCoh(𝒪_U)` is essentially surjective** when the inclusion of the open
subscheme `U` is quasi-compact and quasi-separated: every quasi-coherent `𝒪_U`-module is the
restriction of a quasi-coherent `𝒪_X`-module. -/
theorem exists_isQuasicoherent_restrictModules_iso {X : Scheme.{u}} (U : X.Opens)
    [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (G : OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) (hG : G.IsQuasicoherent) :
    ∃ F : OXMod.{u, u} X.toRingedSpace, F.IsQuasicoherent ∧
      Nonempty ((AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U).obj F ≅ G) :=
  ⟨(Scheme.Modules.pushforward U.ι).obj G,
    @AlgebraicGeometry.pushforward_isQuasicoherent _ _ U.ι _ _ G hG,
    ⟨restrictModulesPushforwardIso U G⟩⟩

/-- **`QCoh(𝒪_X) → QCoh(𝒪_U)` is essentially surjective for an affine open of a quasi-separated
scheme.** -/
theorem exists_isQuasicoherent_restrictModules_iso_of_isAffineOpen {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsAffineOpen U)
    (G : OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) (hG : G.IsQuasicoherent) :
    ∃ F : OXMod.{u, u} X.toRingedSpace, F.IsQuasicoherent ∧
      Nonempty ((AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U).obj F ≅ G) :=
  have : IsAffine U.toScheme := hU
  exists_isQuasicoherent_restrictModules_iso U G hG

end AlgebraicGeometry

namespace Stacks.Cohomology.TorAmplitude

open _root_.AlgebraicGeometry

universe u d

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **Condition (2) of Stacks 08EA restricts to an open subscheme**, with the same interval,
whenever the inclusion of the subscheme is quasi-compact and quasi-separated. -/
theorem HasTorAmplitudeOnQuasicoherent.restrictModules {X : Scheme.{u}} (U : X.Opens)
    [QuasiCompact U.ι] [QuasiSeparated U.ι]
    [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (a b : ℤ)
    (h : HasTorAmplitudeOnQuasicoherent X.toRingedSpace E a b) :
    HasTorAmplitudeOnQuasicoherent (X.toRingedSpace.restrict U.isOpenEmbedding)
      ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E) a b := by
  intro G hG i hi
  obtain ⟨F, hF, ⟨eG⟩⟩ := exists_isQuasicoherent_restrictModules_iso U G hG
  refine IsZero.of_iso
    (isZero_homologyFunctor_derTensor_restrictModules X.toRingedSpace U E F i (h F hF i hi))
    ((DerivedCategory.homologyFunctor _ i).mapIso
      (((derTensor (X.toRingedSpace.restrict U.isOpenEmbedding)).tensor.obj _).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso eG.symm)))

end Stacks.Cohomology.TorAmplitude

end
