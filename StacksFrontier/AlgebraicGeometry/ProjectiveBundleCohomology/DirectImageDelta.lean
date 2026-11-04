module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.LerayAffineBase.Basic
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsCohomologyBridge

/-!
# The higher direct images of a morphism of schemes as a universal δ-functor

For a morphism of schemes `f : X ⟶ Y`, the higher direct images `R^q f_*`, in the indexing
`CategoryTheory.Functor.rightDerived` by injective resolutions, form a universal cohomological
δ-functor. Precomposing a δ-functor with an exact functor, or postcomposing it with one, gives a
δ-functor again. For a finite locally free `𝒪_Y`-module `ℰ`, the δ-functors
`ℱ ↦ R^q f_*(ℱ ⊗ f^* ℰ)` and `ℱ ↦ R^q f_* ℱ ⊗ ℰ` are both universal, and the projection formula
in degree zero extends uniquely to an isomorphism of δ-functors between them.

## Main definitions

* `CategoryTheory.DeltaFunctor.postcompNatTrans`: a natural transformation of exact functors,
  as a morphism of the δ-functors postcomposed with them.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.rightDerivedZeroIsoPlus`: `R⁰ F ≅ F` for a
  left exact `F`, through the indexing `CategoryTheory.Functor.rightDerivedPlus`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.projectionFormulaDelta`: the projection
  formula as an isomorphism of δ-functors.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.DeltaFunctor.isIso_δ_of_isZero`: the
  connecting morphism of a short exact sequence whose middle term is killed in two consecutive
  degrees is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open Stacks.AlgebraicGeometry.LerayAffineBase (pushDelta)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace CategoryTheory.DeltaFunctor

variable {A B B' : Type*} [Category A] [Category B] [Category B'] [Abelian A] [Abelian B]
  [Abelian B'] (F : DeltaFunctor A B) (Ψ : B ⥤ B') [Ψ.Additive] [PreservesFiniteLimits Ψ]
  [PreservesFiniteColimits Ψ]

/-- A natural transformation of exact functors induces a morphism of the postcomposed
δ-functors. -/
@[simps]
public def postcompNatTrans {Ψ' : B ⥤ B'} [Ψ'.Additive] [PreservesFiniteLimits Ψ']
    [PreservesFiniteColimits Ψ'] (ν : Ψ ⟶ Ψ') : F.postcomp Ψ ⟶ F.postcomp Ψ' where
  app n := Functor.whiskerLeft (F.functor n) ν
  comm _hS _n := (ν.naturality _).symm

end CategoryTheory.DeltaFunctor

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

/-- **A δ-functor whose two middle terms vanish has an invertible connecting morphism.** -/
public theorem DeltaFunctor.isIso_δ_of_isZero {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] (F : DeltaFunctor A B) {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) (h : IsZero ((F.functor n).obj S.X₂)) (h' : IsZero ((F.functor (n + 1)).obj S.X₂)) :
    IsIso (F.δ hS n) :=
  have := F.mono_δ_of_map_g_eq_zero hS n (h.eq_of_src _ _)
  have := F.epi_δ_of_map_f_eq_zero hS n (h'.eq_of_tgt _ _)
  isIso_of_mono_of_epi _

/-- **`R⁰ F ≅ F` for a left exact functor**, read through the indexing
`CategoryTheory.Functor.rightDerivedPlus`. -/
public def rightDerivedZeroIsoPlus {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] :
    F.rightDerived 0 ≅ F :=
  Stacks.DerivedIndexing.rightDerivedIso F 0 ≪≫ Stacks.RightDerivedPlus.rightDerivedPlusZeroIso F

section Delta

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The higher direct images form a universal δ-functor: they vanish on injectives. -/
public instance isUniversal_pushDelta : (pushDelta f).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun n I _ =>
    Functor.isZero_rightDerived_obj_injective_succ _ n I

variable (G : Y.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]

/-- `ℱ ↦ R^q f_*(ℱ ⊗ f^* ℰ)`, as a δ-functor. -/
public abbrev projectionSourceDelta : DeltaFunctor X.Modules Y.Modules :=
  (pushDelta f).precomp
    (Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback f).obj G))

/-- `ℱ ↦ R^q f_* ℱ ⊗ ℰ`, as a δ-functor. -/
public abbrev projectionTargetDelta : DeltaFunctor X.Modules Y.Modules :=
  (pushDelta f).postcomp (Stacks.ProjectionFormula.tensorRightInvertible Y G)

/-- `ℱ ↦ R^q f_*(ℱ ⊗ f^* ℰ)` is a universal δ-functor: it is effaceable, since `ℐ ⊗ f^* ℰ` is
injective for an injective `ℐ`. -/
public instance isUniversal_projectionSourceDelta : (projectionSourceDelta f G).IsUniversal :=
  haveI : (projectionSourceDelta f G).Effaceable :=
    DeltaFunctor.Effaceable.precomp _ _ fun M =>
      ⟨Injective.under M, Injective.ι M, inferInstance, fun n =>
        haveI := Stacks.ProjectionFormula.injective_tensorRightInvertible_obj_of_isFiniteLocallyFree
          X ((Scheme.Modules.pullback f).obj G) (Injective.under M) inferInstance
        Functor.isZero_rightDerived_obj_injective_succ _ n _⟩
  DeltaFunctor.isUniversal_of_effaceable _

/-- `ℱ ↦ R^q f_* ℱ ⊗ ℰ` is a universal δ-functor: it vanishes on injectives in positive degrees. -/
public instance isUniversal_projectionTargetDelta : (projectionTargetDelta f G).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun n I _ =>
    (Stacks.ProjectionFormula.tensorRightInvertible Y G).map_isZero
      (Functor.isZero_rightDerived_obj_injective_succ _ n I)

/-- The projection formula `f_*(ℱ ⊗ f^* ℰ) ≅ f_* ℱ ⊗ ℰ` in degree zero. -/
public def projectionFormulaZero :
    (projectionSourceDelta f G).functor 0 ≅ (projectionTargetDelta f G).functor 0 :=
  Functor.isoWhiskerLeft _ (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f)) ≪≫
    Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso f G ≪≫
    Functor.isoWhiskerRight (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward f)).symm _

/-- **The projection formula `R^q f_*(ℱ ⊗ f^* ℰ) ≅ R^q f_* ℱ ⊗ ℰ` as an isomorphism of
δ-functors**, for a finite locally free `ℰ`: the unique extension of the degree-zero formula. -/
public def projectionFormulaDelta : projectionSourceDelta f G ≅ projectionTargetDelta f G :=
  DeltaFunctor.IsUniversal.isoOfIso (projectionFormulaZero f G)

/-- The projection formula in degree `q` at a module. -/
public def projectionFormulaDeltaApp (F : X.Modules) (q : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerived q).obj
        ((Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback f).obj G)).obj
          F) ≅
      (Stacks.ProjectionFormula.tensorRightInvertible Y G).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj F) where
  hom := ((projectionFormulaDelta f G).hom.app q).app F
  inv := ((projectionFormulaDelta f G).inv.app q).app F
  hom_inv_id := congrArg
    (fun η : projectionSourceDelta f G ⟶ projectionSourceDelta f G => (η.app q).app F)
    (projectionFormulaDelta f G).hom_inv_id
  inv_hom_id := congrArg
    (fun η : projectionTargetDelta f G ⟶ projectionTargetDelta f G => (η.app q).app F)
    (projectionFormulaDelta f G).inv_hom_id

end Delta

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
