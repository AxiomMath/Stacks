module

public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalHom
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionFree
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHullAdjunction.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveTorsionFree.Basic
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic

/-!
# A torsion free coherent module injects into its double dual

On an integral scheme, the canonical map of a coherent module to its double dual is a
monomorphism if and only if the module is torsion free.

## Main results

* `exists_dualSection_annihilating_germ`: every `𝒪_{X,x}`-linear functional on the stalk of a
  finitely presented module is represented, near `x`, by a local section of the dual module, in
  the sense that a local section of the module annihilated by that section of the dual has germ
  annihilated by the functional.
* `mono_toDoubleDual_of_isTorsionFree`: on an integral scheme, the canonical map of a torsion
  free coherent module to its double dual is a monomorphism.
* `mono_toDoubleDual_iff_isTorsionFree`: on an integral scheme, the canonical map of a coherent
  module to its double dual is a monomorphism if and only if the module is torsion free.

## References

* [Stacks Project, Tag 0AY2](https://stacks.math.columbia.edu/tag/0AY2)
* [Stacks Project, Tag 0AV0](https://stacks.math.columbia.edu/tag/0AV0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- For a finitely presented module `F` and an `𝒪_{X,x}`-linear functional `α` on the stalk
`F_x`, there is a section `lam` of the dual module on a neighbourhood `U` of `x` such that a local
section of `F` on which `lam` vanishes has germ annihilated by `α`. -/
public theorem exists_dualSection_annihilating_germ (F : X.Modules) [F.IsFinitePresentation]
    (x : X) (α : Module.Dual (ToType (X.presheaf.stalk x)) (ToType (F.presheaf.stalk x))) :
    ∃ (U : X.Opens) (_ : x ∈ U) (lam : Γ(dualSheaf F, U)),
      ∀ (V : X.Opens) (hVU : V ≤ U) (hxV : x ∈ V) (t : Γ(F, V)),
        dualPairing F lam (Over.mk (homOfLE hVU)) t = 0 →
          α (F.presheaf.germ V x hxV t) = 0 := by
  have e := structureSheafStalkLinearEquiv X x
  obtain ⟨U, hxU, φ, hφ⟩ := Stacks.SheafOfModules.SheafHomStalk.exists_localHom_of_stalkLinearMap
    X.toTopCat X.sheaf F (structureSheafModule X) x (e.symm.toLinearMap ∘ₗ α)
  refine ⟨U, hxU, φ.val, fun V hVU hxV t ht => ?_⟩
  have hg : TopCat.Presheaf.germ (C := Ab.{u}) (structureSheafModule X).val.presheaf V x hxV
      ((φ.val.app (op (Over.mk (homOfLE hVU)))) t) = 0 := by
    rw [show (φ.val.app (op (Over.mk (homOfLE hVU)))) t = 0 from ht]
    exact map_zero _
  have hα : e.symm (α (F.presheaf.germ V x hxV t)) = 0 := (hφ V hVU hxV t).symm.trans hg
  exact e.symm.injective (hα.trans (map_zero e.symm).symm)

/-- On an integral scheme, the canonical map of a torsion free coherent module to its double dual
is a monomorphism. -/
public theorem mono_toDoubleDual_of_isTorsionFree [IsIntegral X] (F : X.Modules)
    [F.IsCoherent] (h : IsTorsionFree F) : Mono (toDoubleDual F) := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType (M := F)
  have : F.IsFinitePresentation := CoherentTFAE.isFinitePresentation_of_isCoherent' F
  refine @OXModule.mono_of_stalkMapAdd_injective _ F _ (toDoubleDual F) (fun x => ?_)
  have : Module.Finite (ToType (X.presheaf.stalk x)) (ToType (F.presheaf.stalk x)) :=
    Stacks.StalkFiniteType.finite_stalk F x
  have : Module.IsTorsionFree (ToType (X.presheaf.stalk x)) (ToType (F.presheaf.stalk x)) :=
    (AlgebraicGeometry.isTorsionFree_iff_forall_stalk F).1 h x
  have hinj := (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
    (R := ToType (X.presheaf.stalk x)) (M := ToType (F.presheaf.stalk x))).2.2
      inferInstance |>.2 inferInstance
  have key : ∀ m : ToType (F.presheaf.stalk x),
      OXModule.stalkMapAdd F (dualSheaf (dualSheaf F)) (toDoubleDual F) x m = 0 → m = 0 := by
    intro m hm
    obtain ⟨W, hxW, s, rfl⟩ := F.presheaf.exists_germ_eq m
    have hgf : OXModule.stalkMapAdd F (dualSheaf (dualSheaf F)) (toDoubleDual F) x
          (F.presheaf.germ W x hxW s) =
        (dualSheaf (dualSheaf F)).presheaf.germ W x hxW
          (Scheme.Modules.Hom.app (toDoubleDual F) W s) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _
    rw [hgf] at hm
    have hz : (dualSheaf (dualSheaf F)).presheaf.germ W x hxW
          (Scheme.Modules.Hom.app (toDoubleDual F) W s) =
        (dualSheaf (dualSheaf F)).presheaf.germ W x hxW 0 := by
      rw [hm]
      exact (map_zero _).symm
    obtain ⟨W₁, hxW₁, i₁, i₁', hW₁⟩ :=
      (dualSheaf (dualSheaf F)).presheaf.germ_eq x hxW hxW _ 0 hz
    have hW₁W : W₁ ≤ W := leOfHom i₁
    have hzero : Scheme.Modules.Hom.app (toDoubleDual F) W₁
        (F.presheaf.map (homOfLE hW₁W).op s) = 0 := by
      have hnat : (dualSheaf (dualSheaf F)).presheaf.map (homOfLE hW₁W).op
            (Scheme.Modules.Hom.app (toDoubleDual F) W s) =
          Scheme.Modules.Hom.app (toDoubleDual F) W₁ (F.presheaf.map (homOfLE hW₁W).op s) :=
        (PresheafOfModules.naturality_apply (toDoubleDual F).val (homOfLE hW₁W).op s).symm
      rw [← hnat, ← show i₁ = homOfLE hW₁W from Subsingleton.elim _ _, hW₁, map_zero]
    refine hinj ?_
    rw [map_zero]
    refine LinearMap.ext fun α => ?_
    obtain ⟨U, hxU, lam, hlam⟩ := exists_dualSection_annihilating_germ F x α
    have hxV : x ∈ U ⊓ W₁ := ⟨hxU, hxW₁⟩
    have hVU : (U ⊓ W₁ : X.Opens) ≤ U := inf_le_left
    have hVW₁ : (U ⊓ W₁ : X.Opens) ≤ W₁ := inf_le_right
    have hres : F.presheaf.map (homOfLE hVW₁).op (F.presheaf.map (homOfLE hW₁W).op s) =
        F.presheaf.map (homOfLE (hVW₁.trans hW₁W)).op s := by
      rw [← F.presheaf.map_comp_apply]
      rfl
    have hpair : dualPairing F lam (Over.mk (homOfLE hVU))
        (F.presheaf.map (homOfLE (hVW₁.trans hW₁W)).op s) = 0 := by
      have h0 := congrArg (fun y => dualPairing (dualSheaf F) y (Over.mk (homOfLE hVW₁))
        ((dualSheaf F).presheaf.map (homOfLE hVU).op lam)) hzero
      rw [toDoubleDual_dualPairing] at h0
      refine Eq.trans ?_ h0
      rw [← hres]
      exact (dualPairing_map F hVU lam (Over.mk (𝟙 (U ⊓ W₁ : X.Opens)))
        (F.presheaf.map (homOfLE hVW₁).op (F.presheaf.map (homOfLE hW₁W).op s))).symm
    have hgerm := hlam (U ⊓ W₁) hVU hxV _ hpair
    rwa [F.presheaf.germ_res_apply] at hgerm
  intro a b hab
  have h0 : OXModule.stalkMapAdd F (dualSheaf (dualSheaf F)) (toDoubleDual F) x (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.1 (key _ h0)

/-- On an integral scheme, the canonical map of a coherent module to its double dual is a
monomorphism if and only if the module is torsion free. -/
@[stacks 0AY2 "part (2)"]
public theorem mono_toDoubleDual_iff_isTorsionFree [IsIntegral X] (F : X.Modules)
    [F.IsCoherent] : Mono (toDoubleDual F) ↔ IsTorsionFree F :=
  ⟨fun hm => @isTorsionFree_of_mono_toDoubleDual X _ F hm, mono_toDoubleDual_of_isTorsionFree F⟩

/-- On an integral scheme, the canonical map of a coherent module to its double dual is injective
on the sections over every open if and only if the module is torsion free. -/
public theorem injective_toDoubleDual_app_iff_isTorsionFree [IsIntegral X] (F : X.Modules)
    [F.IsCoherent] :
    (∀ U : X.Opens, Function.Injective (Scheme.Modules.Hom.app (toDoubleDual F) U)) ↔
      IsTorsionFree F := by
  refine ⟨fun hinj => isTorsionFree_of_injective_toDual (toDoubleDual F) hinj, fun h => ?_⟩
  have : Mono (toDoubleDual F) := mono_toDoubleDual_of_isTorsionFree F h
  exact fun U => injective_app_of_mono (toDoubleDual F) U

/-- On an integral scheme, a map `j` of a coherent module `F` to its reflexive hull sending a
local section `f` of `F` to evaluation at `f` is a monomorphism if and only if `F` is torsion
free. -/
public theorem mono_toReflexiveHull_iff_isTorsionFree [IsIntegral X] (F : X.Modules)
    [F.IsCoherent]
    (j : { j : F ⟶ ReflexiveModules.reflexiveHull F //
      ∀ (U : X.Opens) (f : Γ(F, U)) (lam : Γ(dualSheaf F, U)),
        (((j.val.app (op U)).hom f).app (op (Over.mk (𝟙 U)))).hom lam =
          (lam.app (op (Over.mk (𝟙 U)))).hom f }) :
    Mono j.1 ↔ IsTorsionFree F := by
  rw [ReflexiveHull.toReflexiveHull_eq X F j]
  exact mono_toDoubleDual_iff_isTorsionFree F

/-- On an integral locally Noetherian scheme, the canonical map of a coherent module to its double
dual is a monomorphism if and only if the module is torsion free. -/
public theorem mono_toDoubleDual_iff_isTorsionFree_of_isLocallyNoetherian [IsIntegral X]
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] :
    Mono (toDoubleDual F) ↔ IsTorsionFree F :=
  mono_toDoubleDual_iff_isTorsionFree F

end Stacks.AlgebraicGeometry.ReflexiveModules

end
