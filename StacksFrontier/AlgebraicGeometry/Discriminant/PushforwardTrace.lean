module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantIdeal
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.RingTheory.TraceElement.LocalizationCover
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of a finite flat morphism

Let `f : Y ⟶ X` be a finite flat morphism of schemes with `X` locally Noetherian. Over an affine
open `U` of `X` the ring `B = Γ(Y, f⁻¹U)` is a finite flat, hence finite projective, algebra over
`A = Γ(X, U)`, so multiplication by a section `b ∈ B` has a trace `Tr_{B/A}(b) ∈ A`. These traces
glue to a morphism of `𝒪_X`-modules `Trace_f : f_* 𝒪_Y ⟶ 𝒪_X` (Stacks, Section 0BVH).

The gluing rests on compatibility with restriction: for affine opens `U' ⊆ U` of `X`, the ring
`Γ(Y, f⁻¹U')` is the base change `Γ(X, U') ⊗_{Γ(X, U)} Γ(Y, f⁻¹U)`, because `f_* 𝒪_Y` is
quasi-coherent, and the trace of a finite projective algebra commutes with base change. A family
of linear maps on the sections over a basis of opens, compatible with restriction, extends
uniquely to a morphism of sheaves of modules.

## Main definitions

* `Stacks.Discriminant.pushforwardTrace`: the trace `f_* 𝒪_Y ⟶ 𝒪_X` of a finite flat morphism.

## Main results

* `Stacks.Discriminant.pushforwardTrace_app`: over an affine open `U` of `X`, the trace sends a
  section `b` over `f⁻¹U` to the trace of multiplication by `b` over `Γ(X, U)`.

## References

* [Stacks Project, Section 0BVH](https://stacks.math.columbia.edu/tag/0BVH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Discriminant

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The projective trace of multiplication does not change when the algebra structure is
replaced by an equal one. -/
theorem finiteProjectiveTrace_lmul_congr_ringHom {R C : Type*} [CommRing R] [CommRing C]
    {φ ψ : R →+* C} (h : φ = ψ)
    (h₁ : letI := φ.toAlgebra; Module.Finite R C) (h₂ : letI := φ.toAlgebra; Module.Projective R C)
    (h₃ : letI := ψ.toAlgebra; Module.Finite R C) (h₄ : letI := ψ.toAlgebra; Module.Projective R C)
    (c : C) :
    (letI := φ.toAlgebra
     finiteProjectiveTrace R C (Algebra.lmul R C c)) =
      (letI := ψ.toAlgebra
       finiteProjectiveTrace R C (Algebra.lmul R C c)) := by
  subst h
  rfl

section Affine

variable [IsFinite f]

/-- Over an affine open `U` of the base, the sections of the source over `f ⁻¹ U` are a finite
algebra over the sections over `U`. -/
theorem module_finite_app (U : X.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    Module.Finite Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) :=
  f.finite_app U.1 U.2

variable [Flat f] [IsLocallyNoetherian X]

/-- Over an affine open `U` of the base, the sections of the source over `f ⁻¹ U` are a finite
projective algebra over the sections over `U`. -/
theorem module_projective_app (U : X.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    Module.Projective Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := by
  let := (f.app U.1).hom.toAlgebra
  have : Module.Finite Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := module_finite_app f U
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hflat : Module.Flat Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := by
    have h := HasRingHomProperty.appLE @Flat f inferInstance U
      ⟨f ⁻¹ᵁ U.1, IsAffineHom.isAffine_preimage _ U.2⟩ le_rfl
    rw [Scheme.Hom.appLE_eq_app] at h
    exact h
  have : Module.FinitePresentation Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) :=
    Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

/-- The trace over an affine open `U` of the base: the linear map `Γ(Y, f ⁻¹ U) → Γ(X, U)`
sending `b` to the trace of multiplication by `b`. -/
@[sga "1 I 4.10" "partial"]
def localTrace (U : X.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    Γ(Y, f ⁻¹ᵁ U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1) :=
  letI := (f.app U.1).hom.toAlgebra
  letI := module_finite_app f U
  letI := module_projective_app f U
  (finiteProjectiveTrace Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1)).comp (Algebra.lmul _ _).toLinearMap

/-- The trace over affine opens commutes with restriction to a smaller affine open. -/
theorem localTrace_restrict (U U' : X.affineOpens) (h : U'.1 ≤ U.1) (b : Γ(Y, f ⁻¹ᵁ U.1)) :
    localTrace f U' (Y.presheaf.map (homOfLE (f.preimage_mono h)).op b) =
      X.presheaf.map (homOfLE h).op (localTrace f U b) := by
  let : Algebra Γ(X, U.1) Γ(X, U'.1) := algebraOfLE X h
  let : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(X, U'.1) Γ(Y, f ⁻¹ᵁ U'.1) := (f.app U'.1).hom.toAlgebra
  let : Algebra Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ U'.1) :=
    (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U'.1) :=
    (X.presheaf.map (homOfLE h).op ≫ f.app U'.1).hom.toAlgebra
  have : IsScalarTower Γ(X, U.1) Γ(X, U'.1) Γ(Y, f ⁻¹ᵁ U'.1) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ U'.1) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show (X.presheaf.map (homOfLE h).op ≫ f.app U'.1) r =
        (f.app U.1 ≫ Y.presheaf.map (homOfLE (f.preimage_mono h)).op) r
      rw [f.naturality]
      rfl
  have := module_finite_app f U
  have := module_projective_app f U
  have := module_finite_app f U'
  have := module_projective_app f U'
  have : ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent :=
    have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f _
  have hbc : IsBaseChange Γ(X, U'.1)
      ((Algebra.linearMap Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ U'.1)).restrictScalars Γ(X, U.1)) :=
    isBaseChange_restrictₗ ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit Y.ringCatSheaf)) U'.2 U.2 h
  exact finiteProjectiveTrace_lmul_baseChange hbc b

end Affine

variable [IsFinite f] [Flat f] [IsLocallyNoetherian X]

/-- The trace over an affine open of the base, as a map of sections of `𝒪_X`-modules. -/
def localTraceHom (U : X.affineOpens) :
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)).val.obj (op U.1) ⟶
      (SheafOfModules.unit X.ringCatSheaf).val.obj (op U.1) :=
  letI := (f.app U.1).hom.toAlgebra
  ModuleCat.ofHom (R := Γ(X, U.1)) (X := Γ(Y, f ⁻¹ᵁ U.1)) (Y := Γ(X, U.1)) (localTrace f U)

/-- **The trace of a finite flat morphism** `f : Y ⟶ X` (Stacks, Section 0BVH): the morphism
`f_* 𝒪_Y ⟶ 𝒪_X` of `𝒪_X`-modules sending a local section to the trace of multiplication by
it. -/
def pushforwardTrace : (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
    SheafOfModules.unit X.ringCatSheaf :=
  BasisRestriction.moduleSheafHomOfSectionHomOnBasis _ _ (fun U : X.affineOpens => U.1)
    (localTraceHom f)
    (by rw [Subtype.range_coe]; exact X.isBasis_affineOpens)
    (fun U U' h s => localTrace_restrict f U U' h s)

/-- Over an affine open `U` of the base, the trace of `f` sends a section `b` over `f ⁻¹ U` to
the trace of multiplication by `b`. -/
theorem pushforwardTrace_app (U : X.affineOpens) (b : Γ(Y, f ⁻¹ᵁ U.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) :=
      (f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
    haveI : Module.Finite Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := by
      have h := module_finite_app f U
      rwa [← Scheme.Hom.appLE_eq_app] at h
    haveI : Module.Projective Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := by
      have h := module_projective_app f U
      rwa [← Scheme.Hom.appLE_eq_app] at h
    (pushforwardTrace f).app U.1 b =
      finiteProjectiveTrace Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1)
        (Algebra.lmul Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) b) := by
  have h : (pushforwardTrace f).val.app (op U.1) = localTraceHom f U :=
    BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app _ _ _ _ _ _ U
  refine (congrArg (fun φ => φ.hom b) h).trans ?_
  exact finiteProjectiveTrace_lmul_congr_ringHom (congrArg CommRingCat.Hom.hom
    (Scheme.Hom.appLE_eq_app f).symm) (module_finite_app f U) (module_projective_app f U) _ _ b

end Stacks.Discriminant

end
