module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceBoundedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistencePushforwardTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceLimitProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.BaseObjectAtAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.AffineBaseSectionsRingTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangePseudoCoherentIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePseudoCoherentSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtalePerfectTensorPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategoryPerfect
public import StacksFrontier.Homology.DerivedCategory.StandardModuleCatModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomTensorDualNatural
public import StacksFrontier.CategoryTheory.Adjunction.LiftLeftAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedHomBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSnd
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceEtaleSectionsBaseChange

/-!
# The derived sections `Mₙ = RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)` of Situation 0DIK

In Situation [Stacks, Tag 0DIK], for `E ∈ D(𝒪_X)` write `Eₙ = Lpₙ^*E` for its derived pullback
to `Xₙ` and `Mₙ = RΓ(Xₙ, Eₙ ⊗^L Kₙ) ∈ D(Aₙ)`, the derived sections over the affine base
`Spec Aₙ`. This file gathers the ingredients of the proof of [Stacks, Tag 0DIM]:

* for `E` perfect, `Eₙ ⊗^L Kₙ` is pseudo-coherent (Stacks 09J9); when `X` is proper over `A`,
  `Xₙ → Spec Aₙ` is flat, proper and of finite presentation, so [Stacks, Tag 0CTN] makes `Mₙ`
  pseudo-coherent;
* the transition square `Xₙ = Xₙ₊₁ ×_{Spec Aₙ₊₁} Spec Aₙ` is cartesian, and the canonical maps
  `Mₙ₊₁ ⊗^L_{Aₙ₊₁} Aₙ ⟶ Mₙ` (base change of `RΓ`, then Stacks 07A4, `Liₙ^*Eₙ₊₁ ≅ Eₙ` and `φₙ`)
  are isomorphisms, by Tor independence of the flat `Xₙ₊₁ → Spec Aₙ₊₁`;
* `Ψ = RΓ(X, E ⊗^L -)` over `Spec A` is, for `E` perfect, a right adjoint whose left adjoint
  takes values in `D_QCoh(𝒪_X)`; hence it inverts the counit of the coherator.

## Main definitions

* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.stageSectionsFunctor`: `RΓ(Xₙ, -)` over
  `Spec Aₙ`.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.stageTensor`, `…stageSections`: `Eₙ ⊗^L
  Kₙ` and
  `Mₙ`.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.stageSectionsBaseChange`:
  `Mₙ₊₁ ⊗^L_{Aₙ₊₁} Aₙ ⟶ Mₙ`.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.limitTensorSections`: `RΓ(X, E ⊗^L -)`
  over
  `Spec A`, with its adjunction `limitTensorSectionsAdjunction`.

## Main results

* `AlgebraicGeometry.Space.DerivedExistenceSystem.isPseudoCoherent_stageSections`.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.isPullback_transitionSpace`.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.isIso_stageSectionsBaseChange`.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.isIso_stageProjectionFormula`: Stacks
  08IN for
  `pₙ : Xₙ → X`.
* `SeparatedDerivedExistenceSystem.isIso_limitTensorSections_map_coheratorCounit`.

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
* [Stacks Project, Tag 0CTN](https://stacks.math.columbia.edu/tag/0CTN)
* [Stacks Project, Tag 09J9](https://stacks.math.columbia.edu/tag/09J9)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- **`RΓ(Xₙ, -)` over `Spec Aₙ`**: the derived direct image along `Xₙ → Spec Aₙ` followed by the
derived sections of the affine base `Spec Aₙ`. -/
abbrev stageSectionsFunctor (n : ℕ) :
    spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase (D.stage n) ⥤
      StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme D.B (limitBase D.system)
        D.containsLimitBase).obj (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n),
          ⊤) :=
  derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) ⋙
    representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)

variable (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)

/-- **`Eₙ ⊗^L Kₙ`** on `Xₙ`, with `Eₙ = Lpₙ^*E`. -/
abbrev stageTensor (n : ℕ) :
    spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase (D.stage n) :=
  ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase (D.stage n)).obj
    ((D.stageDerivedPullback n).obj E)).obj (D.K n)

/-- **`Mₙ = RΓ(Xₙ, Eₙ ⊗^L Kₙ)`** in `D(Aₙ)`. -/
abbrev stageSections (n : ℕ) :=
  (D.stageSectionsFunctor n).obj (D.stageTensor E n)

/-- **`Eₙ ⊗^L Kₙ` is pseudo-coherent** for `E` perfect: `Eₙ` is perfect (Stacks 08H6) and `Kₙ` is
pseudo-coherent, so Stacks 09J9 (2) applies. -/
theorem isPseudoCoherent_stageTensor (hE : spaceIsPerfect D.B (limitBase D.system)
    D.containsLimitBase D.X.left E) (n : ℕ) :
    letI := spaceHasDerivedCategory D.B (limitBase D.system) D.containsLimitBase (D.stage n)
    (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase (D.stage n).1
      (D.stage n).2).IsPseudoCoherent (D.stageTensor E n) :=
  isPseudoCoherent_smallEtaleDerivedTensor_of_isPerfect _ _
    (isPerfect_smallEtaleDerivedModulePullback
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) E hE)
    (D.pseudoCoherent n)

omit E in
/-- **The derived sections `Mₙ = RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)` are pseudo-coherent for every perfect
`E` and every `n`.** This is where properness enters the proof of Stacks 0DIQ (through
Stacks 0CTN); in the generalization of Stacks 0DIR it comes instead from the supports of the
`Kₙ` being proper over the `Aₙ`. -/
def StageSectionsPseudoCoherent : Prop :=
  ∀ E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left,
    spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E → ∀ n : ℕ,
      @StacksDraft.PseudoCoherence.IsPseudoCoherent _ _ (_) (D.stageSections E n)

/-! ### The base change squares -/

/-- `Spec A` is affine, as an instance on the inverse-limit base object. -/
instance isAffine_toScheme_limitBaseObject :
    IsAffine ((BigFppfOver.toScheme D.B (limitBase D.system) D.containsLimitBase).obj
      (limitBaseObject D.system D.B D.containsLimitBase)) :=
  D.isAffine_limitBaseObject

/-- **`Xₙ = Xₙ₊₁ ×_{Spec Aₙ₊₁} Spec Aₙ`**: the transition square of the infinitesimal base
changes is cartesian, since both `Xₙ` and `Xₙ₊₁` are base changes of `X`. -/
theorem isPullback_transitionSpace (n : ℕ) :
    IsPullback (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
      (baseSpaceTransition D.system D.B D.containsLimitBase D.containsBaseAt n) := by
  refine IsPullback.of_right
    (h₁₂ := spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
    (h₂₂ := baseSpaceProjection D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))
    (v₁₃ := D.X.hom) ?_
    (transitionSpace_spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)).flip
  rw [transitionSpace_spaceProjection, baseSpaceTransition_baseSpaceProjection]
  exact (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).flip

/-- **The base change map of `RΓ` along the transition square**,
`RΓ(Xₙ₊₁, H) ⊗^L_{Aₙ₊₁} Aₙ ⟶ RΓ(Xₙ, Liₙ^* H)`. -/
abbrev transitionSectionsBaseChange (n : ℕ)
    (H : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase (D.stage (n + 1))) :=
  affineBaseDerivedSectionsBaseChangeMap D.B (limitBase D.system) D.containsLimitBase
    (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.isPullback_transitionSpace n).w H

/-- **The base change map along the transition square is invertible on `D_QCoh`**: `Xₙ₊₁` is
flat over `Spec Aₙ₊₁`, so `Xₙ₊₁` and `Spec Aₙ` are Tor independent over `Spec Aₙ₊₁`. -/
theorem isIso_transitionSectionsBaseChange (n : ℕ)
    (H : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase (D.stage (n + 1)))
    (hH : QcohDerived D.B (limitBase D.system) D.containsLimitBase (D.stage (n + 1)) H) :
    IsIso (D.transitionSectionsBaseChange n H) :=
  isIso_affineBaseDerivedSectionsBaseChangeMap _ _ _ _ _ _ _ (D.isPullback_transitionSpace n)
    (isFinitePresentation_spaceBaseProjection _ _ _ _ _ D.finitePresentation (n + 1)).2.1
    (isFinitePresentation_spaceBaseProjection _ _ _ _ _ D.finitePresentation (n + 1)).2.2
    (torIndependent_of_isFlat_left _ _ (isFlat_spaceBaseProjection _ _ _ _ _ D.flat (n + 1)))
    H hH

/-! ### The comparison `RΓ(X, E ⊗^L Rpₙ,* Kₙ) ≅ Mₙ` -/

/-- **`RΓ(X, -)` over `Spec A`**: the derived direct image along `X → Spec A` followed by the
derived sections of `Spec A`. -/
abbrev limitSectionsFunctor :
    spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
      StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme D.B (limitBase D.system)
        D.containsLimitBase).obj (limitBaseObject D.system D.B D.containsLimitBase), ⊤) :=
  derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase D.X.hom ⋙
    representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)

/-- **`RΓ(X, Rpₙ,* -) = RΓ(Xₙ, -)` read over `A`**, the base change isomorphism for the cartesian
square `Xₙ = X ×_{Spec A} Spec Aₙ`. -/
abbrev stagePushforwardSectionsIso (n : ℕ) :=
  affineBaseDerivedSectionsPushforwardIso D.B (limitBase D.system) D.containsLimitBase
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) D.X.hom
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).flip.w

/-- **The projection formula `E ⊗^L Rpₙ,* Kₙ ≅ Rpₙ,*(Eₙ ⊗^L Kₙ)`** (Stacks 08IN), for `E` with
quasi-coherent cohomology. -/
theorem isIso_stageProjectionFormula (n : ℕ)
    (hE : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left E) :
    IsIso (smallEtaleProjectionFormulaMapSnd
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) E (D.K n)) :=
  isIso_smallEtaleProjectionFormulaMapSnd D.B (limitBase D.system) D.containsLimitBase
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (isQuasiCompact_spaceProjection D n) (isQuasiSeparated_spaceProjection D n)
    E hE (D.K n) (fun q => D.isQuasicoherentOnSite_homology_K n q)

/-! ### The transitions `Mₙ₊₁ ⊗^L_{Aₙ₊₁} Aₙ ≅ Mₙ` -/

/-- `Liₙ^* Eₙ₊₁ ≅ Eₙ`: the composition isomorphism of derived pullbacks (Stacks 0D6D) along
`iₙ ≫ pₙ₊₁ = pₙ`. -/
abbrev stagePullbackCompIso (n : ℕ) :
    D.stageDerivedPullback (n + 1) ⋙
        transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n ≅
      D.stageDerivedPullback n :=
  smallEtaleDerivedModulePullbackCompIso D.B (limitBase D.system) D.containsLimitBase
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)) ≪≫
    eqToIso (congrArg (fun φ => smallEtaleDerivedModulePullback D.B (limitBase D.system)
      D.containsLimitBase φ)
      (transitionSpace_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))

/-- **The transition `Liₙ^*(Eₙ₊₁ ⊗^L Kₙ₊₁) ⟶ Eₙ ⊗^L Kₙ`**: Stacks 07A4, then `Liₙ^* Eₙ₊₁ ≅ Eₙ`
in the first factor and `φₙ` in the second. -/
abbrev stageTensorTransition (n : ℕ) :
    (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).obj
        (D.stageTensor E (n + 1)) ⟶ D.stageTensor E n :=
  (smallEtaleDerivedPullbackTensorIso
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).hom.app
      ((D.stageDerivedPullback (n + 1)).obj E, D.K (n + 1)) ≫
    (Functor.uncurry.obj (smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
      (D.stage n))).map ((D.stagePullbackCompIso n).hom.app E ×ₘ D.φ n)

/-- The transition `Liₙ^*(Eₙ₊₁ ⊗^L Kₙ₊₁) ⟶ Eₙ ⊗^L Kₙ` is an isomorphism. -/
instance isIso_stageTensorTransition (n : ℕ) : IsIso (D.stageTensorTransition E n) := by
  have h : IsIso ((D.stagePullbackCompIso n).hom.app E ×ₘ D.φ n) :=
    (isIso_prod_iff _ _).mpr ⟨by exact Iso.isIso_hom ((D.stagePullbackCompIso n).app E),
      by exact D.φ_isIso n⟩
  exact IsIso.comp_isIso' inferInstance
    (Iso.isIso_hom ((Functor.uncurry.obj (smallEtaleDerivedTensor D.B (limitBase D.system)
      D.containsLimitBase (D.stage n))).mapIso (@asIso _ _ _ _ _ h)))

/-- **The canonical map `Mₙ₊₁ ⊗^L_{Aₙ₊₁} Aₙ ⟶ Mₙ`**: the base change map of `RΓ` along the
transition square, followed by `RΓ(Xₙ, -)` of the transition of `Eₙ ⊗^L Kₙ`. -/
abbrev stageSectionsBaseChange (n : ℕ) :=
  D.transitionSectionsBaseChange n (D.stageTensor E (n + 1)) ≫
    (D.stageSectionsFunctor n).map (D.stageTensorTransition E n)

/-- **`Mₙ₊₁ ⊗^L_{Aₙ₊₁} Aₙ ≅ Mₙ`** for `E` with quasi-coherent cohomology. -/
theorem isIso_stageSectionsBaseChange (n : ℕ)
    (hE : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left E) :
    IsIso (D.stageSectionsBaseChange E n) := by
  have := D.isIso_transitionSectionsBaseChange n (D.stageTensor E (n + 1))
    (qcohDerived_smallEtaleDerivedTensor _ _ _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback D.B (limitBase D.system)
        D.containsLimitBase
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)) E hE)
      (fun q => D.isQuasicoherentOnSite_homology_K (n + 1) q))
  exact IsIso.comp_isIso' inferInstance (Iso.isIso_hom ((D.stageSectionsFunctor n).mapIso
    (@asIso _ _ _ _ (D.stageTensorTransition E n) (D.isIso_stageTensorTransition E n))))

/-! ### `RΓ(X, E ⊗^L -)` commutes with the derived limit -/

/-- **`Ψ = RΓ(X, E ⊗^L -)` over `Spec A`.** -/
abbrev limitTensorSections :
    spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
      StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme D.B (limitBase D.system)
        D.containsLimitBase).obj (limitBaseObject D.system D.B D.containsLimitBase), ⊤) :=
  (smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left).obj E ⋙
    D.limitSectionsFunctor

/-- **`Ψ` is a right adjoint for `E` perfect**: its left adjoint is `M ↦ Lf^*(M^~) ⊗^L E^∨`. -/
def limitTensorSectionsAdjunction
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E) :
    (representedAffineDerivedAssociated D.B (limitBase D.system) D.containsLimitBase
        (limitBaseObject D.system D.B D.containsLimitBase) ⋙
      smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase D.X.hom) ⋙
      (smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left).flip.obj
        (smallEtaleDerivedDual D.B (limitBase D.system) D.containsLimitBase D.X.left E) ⊣
      D.limitTensorSections E :=
  (affineBaseDerivedSectionsAdjunction D.B (limitBase D.system) D.containsLimitBase
    D.X.hom).comp
    (smallEtaleDerivedTensorDualAdjunction D.B (limitBase D.system) D.containsLimitBase
      D.X.left E hE)

/-- The left adjoint of `Ψ` takes values in `D_QCoh(𝒪_X)`. -/
theorem qcohDerived_limitTensorSections_leftAdjoint_obj
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E)
    (M : StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme D.B (limitBase D.system)
      D.containsLimitBase).obj (limitBaseObject D.system D.B D.containsLimitBase), ⊤)) :
    spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left
      (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left).obj
        ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
          D.X.hom).obj ((representedAffineDerivedAssociated D.B (limitBase D.system)
            D.containsLimitBase (limitBaseObject D.system D.B D.containsLimitBase)).obj M))).obj
        (smallEtaleDerivedDual D.B (limitBase D.system) D.containsLimitBase D.X.left E)) :=
  qcohDerived_smallEtaleDerivedTensor _ _ _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback D.B (limitBase D.system)
      D.containsLimitBase D.X.hom _
      (qcohDerived_representedAffineDerivedAssociated_obj D.B (limitBase D.system)
        D.containsLimitBase (limitBaseObject D.system D.B D.containsLimitBase) M))
    (qcohDerived_of_isPerfect _ _ _ _ _
      (isPerfect_smallEtaleDerivedDual D.B (limitBase D.system) D.containsLimitBase D.X.left E
        hE))

/-- **`Ψ` inverts the coherator counit**: `RΓ(X, E ⊗^L DQ_X(L)) ≅ RΓ(X, E ⊗^L L)`. -/
theorem isIso_limitTensorSections_map_coheratorCounit
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E)
    (L : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left) :
    IsIso ((D.limitTensorSections E).map (D.coheratorAdjunction.counit.app L)) :=
  Adjunction.isIso_map_counit_app_of_forall D.coheratorAdjunction
    (D.limitTensorSectionsAdjunction E hE) (D.qcohDerived_limitTensorSections_leftAdjoint_obj E hE)
    L

end SeparatedDerivedExistenceSystem

namespace DerivedExistenceSystem

/-- **`Mₙ` is pseudo-coherent** for `E` perfect: [Stacks, Tag 0CTN] for the flat, proper
morphism `Xₙ → Spec Aₙ` of finite presentation, applied to the pseudo-coherent `Eₙ ⊗^L Kₙ`, and
the derived sections of the affine base. -/
theorem isPseudoCoherent_stageSections (D : DerivedExistenceSystem.{u})
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E) (n : ℕ) :
    @StacksDraft.PseudoCoherence.IsPseudoCoherent _ _ (_) (D.toSeparated.stageSections E n) := by
  have h0CTN := (isPseudoCoherent_derivedModulePushforward_and_isIso_baseChange
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (isFlat_spaceBaseProjection _ _ _ _ _ D.flat n)
    (isProper_spaceBaseProjection _ _ _ _ _ D.proper n)
    (isFinitePresentation_spaceBaseProjection _ _ _ _ _ D.finitePresentation n)
    (D.toSeparated.stageTensor E n) (D.toSeparated.isPseudoCoherent_stageTensor E hE n)).1
  have hq := derivedCategoryB_of_isPseudoCoherent_unconditional D.B (limitBase D.system)
    D.containsLimitBase _ _ _ h0CTN
  rw [@StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _ _ (_)]
  intro m
  obtain ⟨L, hL, e⟩ := h0CTN
  exact isPseudoCoherentFrom_representedAffineDerivedSections_obj D.B (limitBase D.system)
    D.containsLimitBase (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n) _ hq m
    ⟨L, hL m, e⟩

/-- **The derived sections `Mₙ` are pseudo-coherent** in Situation 0DIK, for every perfect `E`
and every `n`. -/
theorem stageSectionsPseudoCoherent (D : DerivedExistenceSystem.{u}) :
    D.toSeparated.StageSectionsPseudoCoherent :=
  fun E hE n => D.isPseudoCoherent_stageSections E hE n

end DerivedExistenceSystem

end AlgebraicGeometry.Space

end
