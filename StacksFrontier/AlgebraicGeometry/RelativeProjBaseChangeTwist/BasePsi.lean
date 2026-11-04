module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.LegSections
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Psi

/-!
# The homogeneous-section map of a pulled-back graded algebra

Let `f : P' ⟶ P`, `g : S' ⟶ S` be morphisms of schemes over structure morphisms `P ⟶ S`,
`P' ⟶ S'` with `f ≫ p = p' ≫ g`, and let `ψ₀ : M ⟶ p_* O` be a morphism of modules on `S`. Its
base change is the morphism `g^*M ⟶ p'_*(f^*O)` adjoint to
`M ⟶ p_* O ⟶ p_* f_* f^* O = g_* p'_* f^* O`. This file constructs it and computes it on
pulled-back sections: it carries the pullback along `g` of a section `a` to the pullback along `f`
of `ψ₀(a)`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi`: the base-changed morphism.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi_pullbackSection`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules (pullbackSection)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S S' P P' : Scheme.{u}} (p : P ⟶ S) (p' : P' ⟶ S') (g : S' ⟶ S) (f : P' ⟶ P)
  (hfg : f ≫ p = p' ≫ g) {M : S.Modules} {O : P.Modules}
  (ψ₀ : M ⟶ (Scheme.Modules.pushforward p).obj O)

/-- The morphism `M ⟶ g_* p'_* f^* O` whose adjoint is `basePsi`. -/
def basePsiAdj :
    M ⟶ (Scheme.Modules.pushforward g).obj
      ((Scheme.Modules.pushforward p').obj ((Scheme.Modules.pullback f).obj O)) :=
  ψ₀ ≫ (Scheme.Modules.pushforward p).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app O) ≫
    (Scheme.Modules.pushforwardComp f p).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr hfg).hom.app _ ≫
    (Scheme.Modules.pushforwardComp p' g).inv.app _

/-- **The base change of `ψ₀ : M ⟶ p_* O`**: the morphism `g^*M ⟶ p'_*(f^*O)`. -/
def basePsi :
    (Scheme.Modules.pullback g).obj M ⟶
      (Scheme.Modules.pushforward p').obj ((Scheme.Modules.pullback f).obj O) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (basePsiAdj p p' g f hfg ψ₀)

/-- `basePsiAdj` on sections: `ψ₀`, then the unit of `f^* ⊣ f_*`, then the identification of
the two inverse images of an open. -/
theorem basePsiAdj_app (U : S.Opens) (a : M.val.obj (op U)) :
    (basePsiAdj p p' g f hfg ψ₀).val.app (op U) a =
      ((Scheme.Modules.pullback f).obj O).val.map
        (eqToHom (congrArg (fun φ => φ ⁻¹ᵁ U) hfg).symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app O).val.app
          (op (p ⁻¹ᵁ U)) (ψ₀.val.app (op U) a)) :=
  rfl

/-- **`basePsi` on a pulled-back section.** -/
theorem basePsi_pullbackSection (U : S.Opens) (V : S'.Opens) (h : V ≤ g ⁻¹ᵁ U)
    (h' : p' ⁻¹ᵁ V ≤ f ⁻¹ᵁ (p ⁻¹ᵁ U)) (a : M.val.obj (op U)) :
    (basePsi p p' g f hfg ψ₀).val.app (op V) (pullbackSection g M U V h a) =
      pullbackSection f O (p ⁻¹ᵁ U) (p' ⁻¹ᵁ V) h' (ψ₀.val.app (op U) a) := by
  have hadj : ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map (basePsi p p' g f hfg ψ₀)) =
      basePsiAdj p p' g f hfg ψ₀ :=
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  have h1 := PresheafOfModules.naturality_apply (basePsi p p' g f hfg ψ₀).val (homOfLE h).op
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op U) a)
  have h2 := congrArg (fun φ => φ.val.app (op U) a) hadj
  unfold pullbackSection
  refine h1.trans ?_
  refine (congrArg _ h2).trans ?_
  refine Eq.trans (congrArg _ (basePsiAdj_app p p' g f hfg ψ₀ U a)) ?_
  exact PresheafOfModules.map_map_eq_map ((Scheme.Modules.pullback f).obj O).val
    (eqToHom (congrArg (fun φ => φ ⁻¹ᵁ U) hfg).symm).op
    (homOfLE (show p' ⁻¹ᵁ V ≤ p' ⁻¹ᵁ (g ⁻¹ᵁ U) from fun _ hx => h hx)).op (homOfLE h').op _

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
