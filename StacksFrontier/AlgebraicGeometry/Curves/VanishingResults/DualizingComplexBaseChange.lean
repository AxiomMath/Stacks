module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.BaseFieldInvariance

/-!
# The dualizing complex of a proper scheme under extension of the ground field

Let `X` be a proper scheme over a field `k`, let `K/k` be a field extension and let
`X' = X_K` with projection `g' : X' ⟶ X`. Part (2) of [Stacks, Tag 0E32]: the pullbacks of
`ω_X^• = f^×(𝒪_{Spec k})` and of `ω_X = H^{-1}(ω_X^•)` to `X'` are the dualizing complex and the
dualizing sheaf of [Stacks, Tag 0BS2] for `X' ⟶ Spec K`.

## Main results

* `Stacks.Duality.quasiCoherentDerivedPullbackDerivedStructureSheafIsoOfFlat`:
  `L(g)^*𝒪_Y ≅ 𝒪_X` for a flat morphism `g : X ⟶ Y`.
* `Stacks.Duality.dualizingComplexOverFieldBaseChangeIso`: `L(g')^*ω_X^• ≅ ω_{X'}^•`.
* `Stacks.Duality.dualizingSheafOverFieldBaseChangeIso`: `(g')^*ω_X ≅ ω_{X'}`.
* `Stacks.Duality.nonempty_dualizingComplexOverField_baseChange_iso`: both isomorphisms exist.

## References

* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0AA8](https://stacks.math.columbia.edu/tag/0AA8)
* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open DerivedPushforward

/-- For a flat morphism `g : X ⟶ Y`, `L(g)^*𝒪_Y ≅ 𝒪_X` in `D_QCoh`. -/
def quasiCoherentDerivedPullbackDerivedStructureSheafIsoOfFlat {X Y : Scheme.{u}} (g : X ⟶ Y)
    [Flat g] :
    (quasiCoherentDerivedPullback' g).obj (derivedStructureSheaf Y) ≅ derivedStructureSheaf X :=
  haveI := preservesFiniteLimits_modulesPullback_of_flat g
  (DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).isoMk
    (AlgebraicGeometry.DerivedAffinePushforward.derivedPullbackSingleIsoOfExact g
        (SheafOfModules.unit Y.ringCatSheaf) ≪≫
      (DerivedCategory.singleFunctor X.Modules 0).mapIso (Scheme.Modules.pullbackUnitIso g))

section FieldExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsProper f] (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of K))
  (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))

/-- `L(g')^*ω_X^• ≅ ω_{X'}^•` for the base change `X' = X_K` of a proper scheme `X` over `k`
along a field extension `K/k`: the pullback of the dualizing complex `f^×(𝒪_{Spec k})` of
[Stacks, Tag 0BS2] is the dualizing complex of `X' ⟶ Spec K`. -/
def dualizingComplexOverFieldBaseChangeIso :
    haveI := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
    (quasiCoherentDerivedPullback' g').obj (dualizingComplexOverField f) ≅
      dualizingComplexOverField f' := by
  haveI := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
  have hTor : TorIndependent f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    torIndependent_of_flat_right _ _
  haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent h hTor
  exact @asIso _ _ _ _ _
      (isIso_twistedInverseImageBaseChangeMap_app_of_flat h hTor (derivedStructureSheaf _)) ≪≫
    (twistedInverseImage f' _).mapIso
      (quasiCoherentDerivedPullbackDerivedStructureSheafIsoOfFlat _)

/-- `(g')^*ω_X ≅ ω_{X'}` for the base change `X' = X_K` of a proper scheme `X` over `k` along
a field extension `K/k`: the pullback of the dualizing sheaf `ω_X = H^{-1}(ω_X^•)` of
[Stacks, Tag 0BS2] is the dualizing sheaf of `X' ⟶ Spec K`. -/
def dualizingSheafOverFieldBaseChangeIso :
    haveI := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
    (Scheme.Modules.pullback g').obj (dualizingSheafOverField f) ≅ dualizingSheafOverField f' :=
  haveI := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
  haveI : Flat g' := MorphismProperty.of_isPullback h.flip inferInstance
  haveI := preservesFiniteLimits_modulesPullback_of_flat g'
  homologyDerivedPullbackIso g' _ (-1) ≪≫
    (DerivedCategory.homologyFunctor X'.Modules (-1)).mapIso
      ((ObjectProperty.ι _).mapIso (dualizingComplexOverFieldBaseChangeIso f g' f' h))

/-- Let `X` be a proper scheme over a field `k`, let `K/k` be a field extension and `X' = X_K`
the base change, with projection `g'`. Then the pullbacks of `ω_X^•` and `ω_X` to `X'` are the
dualizing complex and the dualizing sheaf of [Stacks, Tag 0BS2] for `X' ⟶ Spec K`:
`L(g')^*ω_X^• ≅ ω_{X'}^•` and `(g')^*ω_X ≅ ω_{X'}`. No hypothesis on `dim X` is needed. -/
@[stacks 0E32 "part (2)"]
theorem nonempty_dualizingComplexOverField_baseChange_iso :
    haveI := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
    Nonempty ((quasiCoherentDerivedPullback' g').obj (dualizingComplexOverField f) ≅
        dualizingComplexOverField f') ∧
      Nonempty ((Scheme.Modules.pullback g').obj (dualizingSheafOverField f) ≅
        dualizingSheafOverField f') :=
  ⟨⟨dualizingComplexOverFieldBaseChangeIso f g' f' h⟩,
    ⟨dualizingSheafOverFieldBaseChangeIso f g' f' h⟩⟩

end FieldExtension

end Stacks.Duality
