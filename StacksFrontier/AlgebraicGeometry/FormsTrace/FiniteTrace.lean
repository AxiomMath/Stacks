module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteStratificationInvariant
public import StacksFrontier.RingTheory.FormsTrace.BaseChange
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# The trace of a finite locally free morphism

Let `f : Y → X` be a finite, flat morphism of finite presentation.  Over an affine open
`U = Spec A ⊂ X` the ring `B = Γ(Y, f⁻¹U)` is a finite projective `A`-module, and the trace
`Trace_{B/A} : B → A` of Discriminants, Section 0BVH, is defined
(`Stacks.FormsTrace.trace`).  These maps commute with restriction to smaller affine opens and
glue to a map of `𝒪_X`-modules `Trace_f : f_*𝒪_Y → 𝒪_X`,
`AlgebraicGeometry.Scheme.Hom.finiteTrace`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.finiteTrace`: the trace `f_*𝒪_Y → 𝒪_X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.finiteTrace_app_of_isAffineOpen`: on an affine open `U`, the
  trace is `Trace_{Γ(Y, f⁻¹U)/Γ(X, U)}`.

## References

* [Stacks Project, Section 0BVH](https://stacks.math.columbia.edu/tag/0BVH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Over an affine open `U`, `Γ(Y, f⁻¹U)` is a finite `Γ(X, U)`-module for a finite `f`. -/
theorem moduleFinite_app [IsFinite f] (U : X.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
  f.finite_app U hU

/-- Over an affine open `U`, `Γ(Y, f⁻¹U)` is a projective `Γ(X, U)`-module for a finite flat `f`
of finite presentation. -/
theorem moduleProjective_app [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Module.Projective Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := by
  let := (f.app U).hom.toAlgebra
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := f.moduleFinite_app U hU
  have : Module.Flat Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := by
    have h := f.flat_appLE hU hV le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at h
  have : Algebra.FinitePresentation Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := by
    have h := f.finitePresentation_appLE hU hV le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at h
  have : Module.FinitePresentation Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  exact Module.Flat.projective_of_finitePresentation

variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

/-- The trace `Γ(Y, f⁻¹U) → Γ(X, U)` over an affine open `U`, as a map of the sections of
`f_*𝒪_Y` and `𝒪_X`. -/
def affineTrace (U : X.affineOpens) :
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)).val.obj (op U.1) ⟶
      (SheafOfModules.unit X.ringCatSheaf).val.obj (op U.1) := by
  letI := (f.app U.1).hom.toAlgebra
  haveI := f.moduleFinite_app U.1 U.2
  haveI := f.moduleProjective_app U.1 U.2
  change ModuleCat.of Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) ⟶ ModuleCat.of Γ(X, U.1) Γ(X, U.1)
  exact ModuleCat.ofHom (Stacks.FormsTrace.trace Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1))

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- For a finite `f` and affine opens `V ⊆ U` of `X`, the square of rings
`Γ(X, U) → Γ(Y, f⁻¹U)`, `Γ(X, V) → Γ(Y, f⁻¹V)` is a pushout. -/
theorem isPushout_app_restrict (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    IsPushout (f.app U.1) (X.presheaf.map (homOfLE h).op)
      (Y.presheaf.map (homOfLE (f.preimage_mono h)).op) (f.app V.1) := by
  have hpo := Stacks.Morphisms.isPushout_appLE_of_isPullback (IsPullback.id_vert f).flip U V
    (show V.1 ≤ (𝟙 X) ⁻¹ᵁ U.1 from h) (show f ⁻¹ᵁ V.1 ≤ (𝟙 Y) ⁻¹ᵁ (f ⁻¹ᵁ U.1) from
      f.preimage_mono h)
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app] at hpo
  convert hpo using 1 <;> exact (Category.id_comp _).symm

/-- **The traces over affine opens commute with restriction.** -/
theorem affineTrace_restrict (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (s : ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)).val.obj
      (op U.1)) :
    f.affineTrace V
        (((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)).val.map
          (homOfLE h).op s) =
      (SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE h).op (f.affineTrace U s) := by
  let : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, V.1) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let : Algebra Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    (f.app U.1 ≫ Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom.toAlgebra
  have hsq := isPushout_app_restrict f U V h
  have : IsScalarTower Γ(X, U.1) Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change (f.app U.1 ≫ Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom x =
        (X.presheaf.map (homOfLE h).op ≫ f.app V.1).hom x
      rw [hsq.w]
  have : IsScalarTower Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  have : Algebra.IsPushout Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    (CommRingCat.isPushout_iff_isPushout.mp hsq.flip).symm
  have := f.moduleFinite_app U.1 U.2
  have := f.moduleProjective_app U.1 U.2
  have := f.moduleFinite_app V.1 V.2
  have := f.moduleProjective_app V.1 V.2
  exact Stacks.FormsTrace.trace_algebraMap_of_isPushout (R₁ := Γ(X, U.1))
    (B₁ := Γ(Y, f ⁻¹ᵁ U.1)) (R₂ := Γ(X, V.1)) (B₂ := Γ(Y, f ⁻¹ᵁ V.1)) s

/-- **The trace `Trace_f : f_*𝒪_Y → 𝒪_X`** of a finite flat morphism of finite presentation
(Discriminants, Section 0BVH): over an affine open `U` it is the trace of the finite projective
`Γ(X, U)`-algebra `Γ(Y, f⁻¹U)`. -/
def finiteTrace :
    (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis _ _ (fun U : X.affineOpens => U.1)
    f.affineTrace (by simpa using X.isBasis_affineOpens)
    (fun U V h s => f.affineTrace_restrict U V h s)

/-- On an affine open the trace `Trace_f` is `Trace_{Γ(Y, f⁻¹U)/Γ(X, U)}`. -/
theorem finiteTrace_val_app (U : X.affineOpens) :
    (f.finiteTrace).val.app (op U.1) = f.affineTrace U :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app _ _ _ _ _ _ U

/-- **On an affine open `U`, `Trace_f` is the trace of the finite projective algebra
`Γ(Y, f⁻¹U)` over `Γ(X, U)`**, the algebra structure being `f.app U`. -/
theorem finiteTrace_app_of_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    ∀ [Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U)] [Module.Projective Γ(X, U) Γ(Y, f ⁻¹ᵁ U)]
      (b : Γ(Y, f ⁻¹ᵁ U)),
      (f.finiteTrace).app U b = Stacks.FormsTrace.trace Γ(X, U) Γ(Y, f ⁻¹ᵁ U) b :=
  fun b => congrArg (fun φ => φ.hom b) (f.finiteTrace_val_app ⟨U, hU⟩)

end Scheme.Hom

end AlgebraicGeometry
