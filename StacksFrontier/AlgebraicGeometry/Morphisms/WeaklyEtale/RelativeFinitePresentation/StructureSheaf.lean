module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.Algebra.Module.FinitePresentationRel.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Defs

/-!
# Local finite presentation and the structure sheaf

A locally finite type morphism of schemes is locally of finite presentation exactly when its
structure sheaf is finitely presented relative to the base.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_iff_structureSheaf_finitelyPresentedRelative`
  characterizes local finite presentation by the relative finite presentation of the structure
  sheaf.

## Implementation notes

The structure sheaf is regarded as a sheaf of modules using `SheafOfModules.unit`. Relative
finite presentation is `AlgebraicGeometry.IsFinitelyPresentedRelative`.

## References

* [Stacks Project, Tag 09T8](https://stacks.math.columbia.edu/tag/09T8)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private theorem algebra_finitePresentation_iff_self_relative
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    Algebra.FinitePresentation R A ↔ Module.FinitePresentationRel R A A := by
  constructor
  · intro _
    exact (Module.finitePresentationRel_iff (R := R) (A := A) (M := A)).2 inferInstance
  · rintro ⟨n, α, hα, hfp⟩
    let P := MvPolynomial (Fin n) R
    let : Algebra P A := α.toRingHom.toAlgebra
    let : Module P A := Module.compHom A α.toRingHom
    let l : P →ₗ[P] A :=
      { toFun := α, map_add' := α.map_add, map_smul' := fun r x => map_mul α r x }
    have hker : (RingHom.ker α.toRingHom).FG := by
      show (LinearMap.ker l).FG
      exact (Module.FinitePresentation.fg_ker_iff l hα).2 hfp
    exact Algebra.FinitePresentation.of_surjective (f := α) hα hker

private theorem appLE_finitePresentation_iff_unit_relative
    {X S : Scheme.{u}} {M : X.Modules}
    (hM : M = SheafOfModules.unit X.ringCatSheaf)
    (f : X ⟶ S) (V : S.Opens) (U : X.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) [IsAffine V] [IsAffine U] :
    (f.appLE V U hUV).hom.FinitePresentation ↔
      (letI : Algebra (S.presheaf.obj (Opposite.op V))
          (X.presheaf.obj (Opposite.op U)) :=
          (f.appLE V U hUV).hom.toAlgebra
       Module.FinitePresentationRel (S.presheaf.obj (Opposite.op V))
         (X.presheaf.obj (Opposite.op U))
         ((Scheme.Modules.presheaf M).obj (Opposite.op U))) := by
  subst M
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  show RingHom.FinitePresentation (algebraMap Γ(S, V) Γ(X, U)) ↔
    Module.FinitePresentationRel Γ(S, V) Γ(X, U) Γ(X, U)
  rw [RingHom.finitePresentation_algebraMap]
  exact algebra_finitePresentation_iff_self_relative (R := Γ(S, V)) (A := Γ(X, U))

/-- **Stacks Project, Tag 09T8.** A locally finite type morphism is locally of finite
presentation if and only if its structure sheaf is finitely presented relative to the base. -/
@[stacks 09T8 "morphism_iff_structure_sheaf_relative"]
theorem locallyOfFinitePresentation_iff_structureSheaf_finitelyPresentedRelative
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation f ↔
      IsFinitelyPresentedRelative f (SheafOfModules.unit X.ringCatSheaf) := by
  constructor
  · intro hf
    refine ⟨S.affineOpens, fun V => V.1, iSup_affineOpens_eq_top S, fun V => V.2, fun V => ?_⟩
    let I : Type u := {U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ V.1}
    let U : I → X.Opens := fun i => i.1.1
    have hU : (⨆ i, U i) = f ⁻¹ᵁ V.1 := by
      refine le_antisymm (iSup_le fun i => i.2) fun x hx => ?_
      obtain ⟨W, hW, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
      exact le_iSup U ⟨⟨W, hW⟩, hWle⟩ hxW
    refine ⟨I, U, hU, fun i => i.1.2, fun i => ?_⟩
    let : Algebra Γ(S, V.1) Γ(X, U i) := (f.appLE V.1 (U i) i.2).hom.toAlgebra
    have : IsAffine V.1 := V.2
    have : IsAffine (U i) := i.1.2
    exact (appLE_finitePresentation_iff_unit_relative rfl f V.1 (U i) i.2).mp
      (hf.finitePresentation_appLE V.2 i.1.2 i.2)
  · rintro ⟨J, V, hV, hVa, hU⟩
    apply (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
      (Q := RingHom.FinitePresentation)
      (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.finitePresentation_holdsForLocalizationAway).left).2
    intro x
    obtain ⟨j, hj⟩ := hV.exists_mem (f x)
    obtain ⟨I, U, hUeq, hUa, hRel⟩ := hU j
    obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by simpa using (show x ∈ ⨆ i, U i by rwa [hUeq])
    have e : U i ≤ f ⁻¹ᵁ V j := (le_iSup U i).trans hUeq.le
    have : IsAffine (V j) := hVa j
    have : IsAffine (U i) := hUa i
    exact ⟨⟨V j, hVa j⟩, ⟨U i, hUa i⟩, hi, e,
      (appLE_finitePresentation_iff_unit_relative rfl f (V j) (U i) e).mpr (hRel i)⟩

end AlgebraicGeometry
