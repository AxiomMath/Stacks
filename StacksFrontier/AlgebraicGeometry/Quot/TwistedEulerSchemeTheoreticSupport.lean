module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFiberedUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFibreOverPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyOverRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseModuleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerPolynomial
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModuleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorQuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators

/-!
# The twisted Euler characteristic on a closed subspace proper over the residue field

Let `(T, 𝓕)` be an object of `Coh_{X/B}`, `t ∈ T` a point and `X_t` the fibre. The support of
`𝓕_t` is proper over `κ(t)`, so by Stacks 0CZI the module `𝓕_t` is the direct image `i_*𝒢` of a
quasi-coherent module of finite type `𝒢` along the inclusion `i : Z ⟶ X_t` of a closed subspace
`Z` which is proper over `κ(t)`. This file moves the twisted Euler characteristic of Stacks 0DNF
onto `Z`:

`χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = χ(Z, 𝒢 ⊗ i^*L_t^{⊗ n})`,

by the projection formula `i_*𝒢 ⊗ L_t^{⊗ n} ≅ i_*(𝒢 ⊗ i^*L_t^{⊗ n})` and Stacks 0D2U for the
affine morphism `i`, the Euler characteristic of `Z` being taken along `Z ⟶ X_t ⟶ Spec κ(t)`.
Viewed over `Spec κ(t)` (Stacks 04SG), `Z` is a proper algebraic space over the field `κ(t)`, and
the right-hand side is the alternating sum of the dimensions of its cohomology over the base
`Spec κ(t)`: the setting of Stacks 0DN4.

## Main results

* `AlgebraicGeometry.Space.CoherentObject.exists_closedSubspace_fibreModule`: `𝓕_t = i_*𝒢` for
  a quasi-coherent `𝒢` of finite type on a closed subspace `Z` proper over `κ(t)`.
* `AlgebraicGeometry.Space.CoherentObject.twistedEuler_eq_eulerCharacteristicAlong_closedSubspace`:
  `χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = χ(Z, 𝒢 ⊗ i^*L_t^{⊗ n})`.
* `AlgebraicGeometry.Space.CoherentObject.isProper_closedSubspaceOverPoint`: the closed subspace,
  viewed over `Spec κ(t)`, is proper over `Spec κ(t)`.
* `AlgebraicGeometry.Space.CoherentObject.twistedEuler_eq_finsum_closedSubspaceOverPoint`:
  the twisted Euler characteristic is the alternating sum of the dimensions of the cohomology
  over `Spec κ(t)` of a module on a proper algebraic space over `κ(t)`.
* `AlgebraicGeometry.Space.CoherentObject.exists_twistedEuler_eq_eulerCharacteristic`: **the
  twisted Euler characteristics of Stacks 0DNF are the twisted Euler characteristics
  `χ(Z, 𝒢 ⊗ ℒ^{⊗ n})` (Stacks 0DN1) of a coherent module `𝒢` and an invertible module `ℒ` on a
  proper algebraic space `Z` over `Spec κ(t)`**, the input of Stacks 0DN4,
  `AlgebraicGeometry.Space.IsTwistedEulerNumericalPolynomial`.

## Implementation notes

The Euler characteristic of Stacks 0DN1 is taken in the universe `u + 1` of the small étale
sites (the parameter `w` of `AlgebraicGeometry.Space.eulerCharacteristic` is `u`), which is the
universe of `AlgebraicGeometry.Space.CoherentObject.twistedEuler`. The coherence of `𝒢` on `Z`
comes from the quasi-coherence and finite type of the module of Stacks 0CZI, transported to the
space over `Spec κ(t)`, which is locally Noetherian, being proper over a field.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0CZI](https://stacks.math.columbia.edu/tag/0CZI)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.CoherentObject

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- The projection `X_t ⟶ Spec κ(t)` of the fibre, as a morphism to the representable presheaf of
`Spec κ(t)` over `S`. -/
abbrev fibreProjection (A : CoherentObject D) (t : A.testScheme) :
    (A.fibreSpace t).1 ⟶ yoneda.obj (Over.mk (A.pointSchemeHom' t)) :=
  (D.projection (A.pointTest t)).hom

/-- **The pullback of `𝓕` to the fibre has support proper over `κ(t)`**: it is the module of the
pullback of the object of `Coh_{X/B}` to the point. -/
theorem fibreModule_hasProperSupport (A : CoherentObject D) (t : A.testScheme) :
    ∃ hp : IsLocallyOfFiniteType B S hS (A.fibreProjection t),
      HasProperSupport B S hS (A.fibreSpace t).2
        ((schemeSpaceFunctor B S hS).obj (A.pointTest t).left).2 (A.fibreProjection t) hp
        ((SheafOfModules.toSheaf _).obj (A.fibreModule t)) := by
  obtain ⟨hp, hU, hproper⟩ := (CoherentSituation.pullbackObject'
    (modulePullbackStabilityOfFinitePresentation B S hS) A (A.pointTestHom t)).properSupport
  exact ⟨hp, hU, hproper⟩

/-- **The pullback of `𝓕` to the fibre lives on a closed subspace proper over `κ(t)`** (Stacks
0CZI): `𝓕_t ≅ i_*𝒢` for a quasi-coherent `𝒪_Z`-module `𝒢` of finite type on a closed subspace
`i : Z ⟶ X_t` whose composite with `X_t ⟶ Spec κ(t)` is proper. -/
theorem exists_closedSubspace_fibreModule (A : CoherentObject D) (t : A.testScheme) :
    ∃ (Z : ClosedSubspaces B S hS (A.fibreSpace t).1)
      (G : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).1
        (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).2),
      G.IsQuasicoherentOnSite ∧ SheafOfModules.IsFiniteTypeOnSite G ∧
        IsProper B S hS (Z.1.ι ≫ A.fibreProjection t) ∧
        Nonempty ((modulePushforward B S hS
          (closedSubspaceInclusion B S hS (A.fibreSpace t) Z)).obj G ≅ A.fibreModule t) := by
  let A' := CoherentSituation.pullbackObject'
    (modulePullbackStabilityOfFinitePresentation B S hS) A (A.pointTestHom t)
  have hqc : (A.fibreModule t).IsQuasicoherentOnSite := A'.quasicoherent
  have : (A.fibreModule t).IsFinitePresentationOnSite := A'.finitePresentation
  have hft : SheafOfModules.IsFiniteTypeOnSite (A.fibreModule t) := inferInstance
  obtain ⟨hp, hps⟩ := A.fibreModule_hasProperSupport t
  exact ((hasProperSupport_tfae B S hS (A.fibreSpace t)
    ((schemeSpaceFunctor B S hS).obj (A.pointTest t).left) (A.fibreProjection t) hp
    (A.fibreModule t) hqc hft
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _ hft)).out 1 3).1 hps

/-- The pullback `(L^{⊗ n})_t` of the `n`-th tensor power of `L` to the fibre, the twist of
`AlgebraicGeometry.Space.CoherentObject.twistedEuler`. -/
abbrev fibreTwist (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) (n : ℤ) :
    Modules.{u, u} B S hS (A.fibreSpace t).1 (A.fibreSpace t).2 :=
  (modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))).obj
    (invertibleTensorPower B S hS D.X.1 D.X.2 L n)

/-- **The twisted Euler characteristic is computed on a closed subspace carrying `𝓕_t`.** If
`𝓕_t ≅ i_*𝒢` for a quasi-coherent module `𝒢` on a closed subspace `i : Z ⟶ X_t`, then

`χ(X_t, 𝓕_t ⊗ (L^{⊗ n})_t) = χ(Z, 𝒢 ⊗ i^*(L^{⊗ n})_t)`,

the right-hand side taken along `Z ⟶ X_t ⟶ Spec κ(t)`. The projection formula identifies
`i_*𝒢 ⊗ (L^{⊗ n})_t` with `i_*(𝒢 ⊗ i^*(L^{⊗ n})_t)`, and Stacks 0D2U for the affine morphism `i`
the Euler characteristics of the latter on `X_t` and of `𝒢 ⊗ i^*(L^{⊗ n})_t` on `Z`. -/
theorem twistedEuler_eq_eulerCharacteristicAlong_closedSubspace
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) (Z : ClosedSubspaces B S hS (A.fibreSpace t).1)
    (G : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).1
      (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).2) (hG : G.IsQuasicoherentOnSite)
    (e : (modulePushforward B S hS (closedSubspaceInclusion B S hS (A.fibreSpace t) Z)).obj G ≅
      A.fibreModule t) (n : ℤ) :
    twistedEuler L A t n =
      eulerCharacteristicAlong B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).1
        (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).2 (A.testScheme.residueField t)
        (smallerBaseRingHom B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z)
          (A.testScheme.residueField t) _ (A.pointSchemeHom' t)
          ((closedSubspaceInclusion B S hS (A.fibreSpace t) Z).hom ≫ A.fibreProjection t))
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          (smallEtaleRingedSite B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).1
            (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).2).O).obj G).obj
          ((modulePullback B S hS (closedSubspaceInclusion B S hS (A.fibreSpace t) Z)).obj
            (fibreTwist L A t n))) := by
  let i := closedSubspaceInclusion B S hS (A.fibreSpace t) Z
  have hi : IsClosedImmersion B S hS i.hom := Z.2.2
  have hrep := relativelyRepresentable_of_isAffineHom B S hS i
    (isAffineHom_of_isClosedImmersion B S hS i.hom hi)
  have hinv := isInvertible_modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))
    (invertibleTensorPower B S hS D.X.1 D.X.2 L n)
  have hLqc : ((modulePullback B S hS i).obj (fibreTwist L A t n)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isInvertible i _ hinv
  have hqc : (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).1
        (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).2).O).obj G).obj
      ((modulePullback B S hS i).obj (fibreTwist L A t n))).IsQuasicoherentOnSite :=
    @Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite.{u + 1, u, u}
      _ _ (smallEtaleRingedSite B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).1
        (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).2).J _ _ _
      (smallEtaleRingedSite B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).1
        (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).2).O G
      ((modulePullback B S hS i).obj (fibreTwist L A t n)) hG hLqc
  refine (eulerCharacteristicAlong_congr _ _ _ _ _ _ _
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).mapIso e.symm).app
          (fibreTwist L A t n) ≪≫
        sheafTensorModulePushforwardIso B S hS i hi G (fibreTwist L A t n))).trans ?_
  exact (eulerCharacteristicAlong_modulePushforward_of_isAffineHom B S hS i hrep
    (A.testScheme.residueField t) (A.fibreFieldHom t) _
    (isAffineHom_of_isClosedImmersion B S hS i.hom hi)
    (globalSectionRingHomsCompatible_globalSectionsRingHom B S hS i hrep (A.fibreProjection t)
      (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom) _ hqc).symm

/-- A closed subspace `Z` of the fibre `X_t`, viewed as an algebraic space over `Spec κ(t)`
through `Z ⟶ X_t ⟶ Spec κ(t)` (Stacks 04SG). -/
def closedSubspaceOverPoint (A : CoherentObject D) (t : A.testScheme)
    (Z : ClosedSubspaces B S hS (A.fibreSpace t).1) :
    AlgebraicSpaces B (Spec (.of (A.testScheme.residueField t)))
      (B.residueField_spec_contains A.T.left.left.property t) :=
  spaceOverSmallerBase B _ S _ hS (A.pointSchemeHom' t)
    (closedSubspaceToSpace B S hS (A.fibreSpace t) Z)
    ((closedSubspaceInclusion B S hS (A.fibreSpace t) Z).hom ≫ A.fibreProjection t)

/-- **A closed subspace of the fibre proper over `κ(t)` is a proper algebraic space over
`Spec κ(t)`**: properness of the structure morphism does not depend on the base scheme. -/
theorem isProper_closedSubspaceOverPoint (A : CoherentObject D) (t : A.testScheme)
    (Z : ClosedSubspaces B S hS (A.fibreSpace t).1)
    (hZ : IsProper B S hS (Z.1.ι ≫ A.fibreProjection t)) :
    IsProper B _ _ (toYonedaId B _ _ (A.closedSubspaceOverPoint t Z).1) := by
  refine (isProper_relocalizeToYoneda_iff B _ S _ hS (A.pointSchemeHom' t)
    (A.closedSubspaceOverPoint t Z).1 (A.closedSubspaceOverPoint t Z).2).1 ?_
  have key := (isProper_isIso_comp_iff B S hS (relocalizeSpaceOverSmallerBaseIso B _ S _ hS
    (A.pointSchemeHom' t) (closedSubspaceToSpace B S hS (A.fibreSpace t) Z)
    ((closedSubspaceInclusion B S hS (A.fibreSpace t) Z).hom ≫ A.fibreProjection t)).hom
    ((closedSubspaceInclusion B S hS (A.fibreSpace t) Z).hom ≫ A.fibreProjection t)).2 hZ
  rw [relocalizeSpaceOverSmallerBaseIso_hom_comp] at key
  exact key

/-- **The twisted Euler characteristic is computed over `Spec κ(t)` on a closed subspace carrying
`𝓕_t`.** If `𝓕_t ≅ i_*𝒢` for a quasi-coherent module `𝒢` on a closed subspace `i : Z ⟶ X_t`,
then `χ(X_t, 𝓕_t ⊗ (L^{⊗ n})_t)` is the alternating sum of the `κ(t)`-dimensions of the
cohomology, over the base `Spec κ(t)`, of the module corresponding to `𝒢 ⊗ i^*(L^{⊗ n})_t` on
`Z` viewed over `Spec κ(t)`; for `Z` proper over `κ(t)` that space is proper over `Spec κ(t)`
(`AlgebraicGeometry.Space.CoherentObject.isProper_closedSubspaceOverPoint`). -/
theorem twistedEuler_eq_finsum_closedSubspaceOverPoint
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) (Z : ClosedSubspaces B S hS (A.fibreSpace t).1)
    (G : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).1
      (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).2) (hG : G.IsQuasicoherentOnSite)
    (e : (modulePushforward B S hS (closedSubspaceInclusion B S hS (A.fibreSpace t) Z)).obj G ≅
      A.fibreModule t) (n : ℤ) :
    twistedEuler L A t n =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank (A.testScheme.residueField t)
        (cohomologyOverBase.{u, u + 1} (A.testScheme.residueField t) B _
          (A.closedSubspaceOverPoint t Z).1 (A.closedSubspaceOverPoint t Z).2
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
            ((smallerBaseModulesEquivalence.{u, u} B _ S _ hS (A.pointSchemeHom' t)
              (closedSubspaceToSpace B S hS (A.fibreSpace t) Z)
              ((closedSubspaceInclusion B S hS (A.fibreSpace t) Z).hom ≫
                A.fibreProjection t)).functor.obj
              (((Stacks.SheafOfModules.Tensor.sheafTensor
                (smallEtaleRingedSite B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).1
                  (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).2).O).obj G).obj
                ((modulePullback B S hS (closedSubspaceInclusion B S hS (A.fibreSpace t) Z)).obj
                  (fibreTwist L A t n))))) i) : ℤ) :=
  (A.twistedEuler_eq_eulerCharacteristicAlong_closedSubspace L t Z G hG e n).trans
    (eulerCharacteristicAlong_eq_finsum_spaceOverSmallerBase B S hS
      (closedSubspaceToSpace B S hS (A.fibreSpace t) Z) (A.testScheme.residueField t) _
      (A.pointSchemeHom' t)
      ((closedSubspaceInclusion B S hS (A.fibreSpace t) Z).hom ≫ A.fibreProjection t) _)

/-- The pullback `i^*L_t` to a closed subspace `i : Z ⟶ X_t` of the pullback `L_t` of `L` to
the fibre. -/
abbrev closedSubspaceTwist (L : Modules.{u, u} B S hS D.X.1 D.X.2) (A : CoherentObject D)
    (t : A.testScheme) (Z : ClosedSubspaces B S hS (A.fibreSpace t).1) :
    Modules.{u, u} B S hS (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).1
      (closedSubspaceToSpace B S hS (A.fibreSpace t) Z).2 :=
  (modulePullback B S hS (closedSubspaceInclusion B S hS (A.fibreSpace t) Z)).obj
    ((modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))).obj L)

/-- **The twisted Euler characteristics of Stacks 0DNF are the twisted Euler characteristics of a
coherent module on a proper algebraic space over the residue field.** For an object `(T, 𝓕)` of
`Coh_{X/B}`, an invertible `𝒪_X`-module `L` and a point `t ∈ T`, there are a proper algebraic
space `Z` over `Spec κ(t)` — a closed subspace of the fibre `X_t` carrying `𝓕_t`, viewed over
`κ(t)` — a coherent `𝒪_Z`-module `𝒢` and an invertible `𝒪_Z`-module `ℒ` such that

`χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = χ(Z, 𝒢 ⊗ ℒ^{⊗ n})`

for every `n ∈ ℤ`, the right-hand side being the Euler characteristic of Stacks 0DN1 of the twist
`AlgebraicGeometry.Space.twistedModuleUlift`. This is the input of Stacks 0DN4 for `r = 1`,
`AlgebraicGeometry.Space.IsTwistedEulerNumericalPolynomial`. -/
theorem exists_twistedEuler_eq_eulerCharacteristic (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) :
    ∃ (Z : AlgebraicSpaces B (Spec (.of (A.testScheme.residueField t)))
        (B.residueField_spec_contains A.T.left.left.property t))
      (hf : IsProper B _ _ (toYonedaId B _ _ Z.1))
      (G ℒ : Modules.{u, u} B _ _ Z.1 Z.2)
      (_ : IsCoherent B _ _ Z.1 Z.2 G)
      (hℒ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B _ _ Z.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B _ _ Z.1 Z.2).O)).property
        ℒ)
      (hcoh : ∀ n : Fin 1 → ℤ, IsCoherent B _ _ Z.1 Z.2
        (@twistedModuleUlift.{u, u} B _ _ Z.1 Z.2 1 G (fun _ => ℒ) (fun _ => hℒ) n)),
      ∀ n : ℤ, twistedEuler L A t n =
        @eulerCharacteristic.{u, u} (A.testScheme.residueField t) _ B _ Z.1 Z.2
          (toYonedaId B _ _ Z.1) hf
          (@twistedModuleUlift.{u, u} B _ _ Z.1 Z.2 1 G (fun _ => ℒ) (fun _ => hℒ) (fun _ => n))
          (hcoh _) := by
  obtain ⟨Zc, G, hG, hGft, hZp, ⟨e⟩⟩ := A.exists_closedSubspace_fibreModule t
  let Zsp := closedSubspaceToSpace B S hS (A.fibreSpace t) Zc
  let i := closedSubspaceInclusion B S hS (A.fibreSpace t) Zc
  let φZ := i.hom ≫ A.fibreProjection t
  let Φ := (smallerBaseModulesEquivalence.{u, u} B _ S _ hS (A.pointSchemeHom' t) Zsp φZ).functor
  have hf := A.isProper_closedSubspaceOverPoint t Zc hZp
  have hLt := isInvertible_modulePullback B S hS (baseChangeProjection D.f (A.pointTest t)) L
  have hLZ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Zsp.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Zsp.1 Zsp.2).O)).property
      (closedSubspaceTwist L A t Zc) :=
    isInvertible_modulePullback B S hS i _
  have hL' := isInvertible_smallerBaseModules B _ S _ hS (A.pointSchemeHom' t) Zsp φZ
    (closedSubspaceTwist L A t Zc)
  have hnoeth : Fact (HasEtaleLocalProperty B _ _ (A.closedSubspaceOverPoint t Zc).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper (A.testScheme.residueField t) B _
      (A.closedSubspaceOverPoint t Zc).1 (A.closedSubspaceOverPoint t Zc).2 _ hf⟩
  have hGcoh := @isCoherent_smallerBaseModules B _ S _ hS (A.pointSchemeHom' t) Zsp φZ hnoeth G hG
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite G hGft)
  refine ⟨A.closedSubspaceOverPoint t Zc, hf, Φ.obj G, Φ.obj (closedSubspaceTwist L A t Zc),
    hGcoh, hL', fun n => @isCoherent_twistedModuleUlift.{u, u} B _ _ _ _ hnoeth 1 _ _
      (fun _ => hL') n hGcoh, fun n => ?_⟩
  rw [A.twistedEuler_eq_finsum_closedSubspaceOverPoint L t Zc G hG e n,
    eulerCharacteristic_eq_finsum]
  refine finsum_congr fun q => ?_
  congr 2
  refine (cohomologyOverBaseIso.{u, u} _ B _ _ _
    (uliftForPresentationMapIso.{u, u} B _ _ _ _ ?_) q).toLinearEquiv.finrank_eq
  let eL : (modulePullback B S hS i).obj (fibreTwist L A t n) ≅
      invertibleTensorPower B S hS Zsp.1 Zsp.2 (closedSubspaceTwist L A t Zc) n :=
    (modulePullback B S hS i).mapIso
        (modulePullbackInvertibleTensorPowerIso B S hS (baseChangeProjection D.f (A.pointTest t))
          L n) ≪≫
      modulePullbackInvertibleTensorPowerIso B S hS i _ n
  exact smallerBaseModulesTensorIso B _ S _ hS (A.pointSchemeHom' t) Zsp φZ G _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B _ _ (A.closedSubspaceOverPoint t Zc).1
        (A.closedSubspaceOverPoint t Zc).2).O).obj (Φ.obj G)).mapIso
      (Φ.mapIso eL ≪≫ smallerBaseModulesTensorPowerIso B _ S _ hS (A.pointSchemeHom' t) Zsp φZ
        (closedSubspaceTwist L A t Zc) n)

end AlgebraicGeometry.Space.CoherentObject

end
