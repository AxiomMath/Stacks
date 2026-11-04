module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.BasePsi
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentGlue

/-!
# The base change of a homogeneous-section map: naturality and composition

Let `f : P' ⟶ P`, `g : S' ⟶ S` be morphisms of schemes over structure morphisms `p : P ⟶ S`,
`p' : P' ⟶ S'` with `f ≫ p = p' ≫ g`, and let `ψ₀ : M ⟶ p_* O`.  Its base change
`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi` is the morphism
`g^*M ⟶ p'_*(f^*O)` adjoint to `M ⟶ p_* O ⟶ g_* p'_* f^* O`.  This file proves:

* it is natural in `M` and in `O`;
* it does not see the spelling of `f` (`basePsi_congr`);
* base change along a composite square is base change along the two squares in turn
  (`basePsi_comp`), and, when the second square lies over the identity of the base, base change
  along the composite is base change along the first square followed by the unit of the
  inverse image along the second (`basePsi_comp_unit`).

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi_comp_pushforward_map`,
  `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi_pullback_map_comp`: naturality
  in `O` and in `M`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi_congr`: the base change does not
  depend on the spelling of `f`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi_comp_unit`: base change along a
  composite square over the identity of the base.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi_comp`: base change along a
  composite square.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules (pullbackSection)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

variable {S S' P P' : Scheme.{u}} (p : P ⟶ S) (p' : P' ⟶ S') (g : S' ⟶ S) (f : P' ⟶ P)
  (hfg : f ≫ p = p' ≫ g) {M : S.Modules} {O : P.Modules}
  (ψ₀ : M ⟶ (Scheme.Modules.pushforward p).obj O)

include hfg in
/-- The preimage inclusion carried by a commutative square. -/
theorem preimage_le_of_comm (U : S.Opens) : p' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ f ⁻¹ᵁ (p ⁻¹ᵁ U) :=
  (congrArg (fun φ => φ ⁻¹ᵁ U) hfg).ge

/-- `basePsi` on the pullback of a section over the whole preimage. -/
theorem basePsi_pullbackSection_preimage (U : S.Opens) (a : M.val.obj (op U)) :
    (basePsi p p' g f hfg ψ₀).val.app (op (g ⁻¹ᵁ U)) (pullbackSection g M U (g ⁻¹ᵁ U) le_rfl a) =
      pullbackSection f O (p ⁻¹ᵁ U) (p' ⁻¹ᵁ (g ⁻¹ᵁ U)) (preimage_le_of_comm p p' g f hfg U)
        (ψ₀.val.app (op U) a) :=
  basePsi_pullbackSection p p' g f hfg ψ₀ U (g ⁻¹ᵁ U) le_rfl _ a

/-- **`basePsi` is natural in the module upstairs.** -/
theorem basePsi_comp_pushforward_map {O₂ : P.Modules} (t : O ⟶ O₂) :
    basePsi p p' g f hfg (ψ₀ ≫ (Scheme.Modules.pushforward p).map t) =
      basePsi p p' g f hfg ψ₀ ≫
        (Scheme.Modules.pushforward p').map ((Scheme.Modules.pullback f).map t) := by
  refine ModuleLimits.hom_ext_of_pullbackSection g fun U a => ?_
  refine (basePsi_pullbackSection_preimage p p' g f hfg _ U a).trans ?_
  refine Eq.trans ?_ (congrArg (((Scheme.Modules.pullback f).map t).val.app
    (op (p' ⁻¹ᵁ (g ⁻¹ᵁ U)))) (basePsi_pullbackSection_preimage p p' g f hfg ψ₀ U a)).symm
  exact (Scheme.Modules.pullbackSection_naturality f t (p ⁻¹ᵁ U) _ _ _).symm

/-- **`basePsi` is natural in the module downstairs.** -/
theorem basePsi_pullback_map_comp {M₂ : S.Modules} (m : M₂ ⟶ M) :
    basePsi p p' g f hfg (m ≫ ψ₀) =
      (Scheme.Modules.pullback g).map m ≫ basePsi p p' g f hfg ψ₀ := by
  refine ModuleLimits.hom_ext_of_pullbackSection g fun U a => ?_
  refine (basePsi_pullbackSection_preimage p p' g f hfg _ U a).trans ?_
  refine Eq.trans ?_ (congrArg ((basePsi p p' g f hfg ψ₀).val.app (op (g ⁻¹ᵁ U)))
    (Scheme.Modules.pullbackSection_naturality g m U (g ⁻¹ᵁ U) le_rfl a)).symm
  exact (basePsi_pullbackSection_preimage p p' g f hfg ψ₀ U (m.val.app (op U) a)).symm

/-- **`basePsi` does not see the spelling of the morphism upstairs.** -/
theorem basePsi_congr {f₁ : P' ⟶ P} (hf : f = f₁) (hfg₁ : f₁ ≫ p = p' ≫ g) :
    basePsi p p' g f hfg ψ₀ ≫
        (Scheme.Modules.pushforward p').map ((Scheme.Modules.pullbackCongr hf).hom.app O) =
      basePsi p p' g f₁ hfg₁ ψ₀ := by
  subst hf
  exact (congrArg (basePsi p p' g f hfg ψ₀ ≫ ·)
    ((Scheme.Modules.pushforward p').map_id _)).trans (Category.comp_id _)

/-- Pulling a section back twice, along `f` to a smaller open and then along `f₁`, does not see
the intermediate open. -/
theorem pullbackSection_pullbackSection_shrink {X₁ X₂ X₃ : Scheme.{u}} (f₁ : X₁ ⟶ X₂)
    (f₂ : X₂ ⟶ X₃) (F : X₃.Modules) (U : X₃.Opens) (W : X₂.Opens) (V : X₁.Opens)
    (hW : W ≤ f₂ ⁻¹ᵁ U) (hV : V ≤ f₁ ⁻¹ᵁ W) (hV' : V ≤ f₁ ⁻¹ᵁ (f₂ ⁻¹ᵁ U))
    (x : F.val.obj (op U)) :
    pullbackSection f₁ ((Scheme.Modules.pullback f₂).obj F) W V hV
        (pullbackSection f₂ F U W hW x) =
      pullbackSection f₁ ((Scheme.Modules.pullback f₂).obj F) (f₂ ⁻¹ᵁ U) V hV'
        (pullbackSection f₂ F U (f₂ ⁻¹ᵁ U) le_rfl x) := by
  rw [← ModuleLimits.pullbackSection_shrink f₂ F U (f₂ ⁻¹ᵁ U) W le_rfl hW hW x]
  exact ModuleLimits.pullbackSection_target_le f₁ _ hW V hV' hV _

/-- Reading `basePsi` along a composite `f₁ ≫ f` through `(f₁ ≫ f)^* ≅ f₁^* f^*` on the pullback of
a section gives the double pullback of `ψ₀ a`. -/
private theorem pullbackComp_inv_basePsi_pullbackSection {S₁ P₁ P₂ : Scheme.{u}} (p : P ⟶ S)
    (p₁ : P₁ ⟶ S₁) (g : S₁ ⟶ S) (f₁ : P₁ ⟶ P₂) (f : P₂ ⟶ P) (h : (f₁ ≫ f) ≫ p = p₁ ≫ g)
    (ψ₀ : M ⟶ (Scheme.Modules.pushforward p).obj O) (U : S.Opens) (a : M.val.obj (op U))
    (hV : p₁ ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ f₁ ⁻¹ᵁ (f ⁻¹ᵁ (p ⁻¹ᵁ U))) :
    ((Scheme.Modules.pullbackComp f₁ f).inv.app O).val.app (op (p₁ ⁻¹ᵁ (g ⁻¹ᵁ U)))
      ((basePsi p p₁ g (f₁ ≫ f) h ψ₀).val.app (op (g ⁻¹ᵁ U))
        (pullbackSection g M U (g ⁻¹ᵁ U) le_rfl a)) =
      pullbackSection f₁ ((Scheme.Modules.pullback f).obj O) (f ⁻¹ᵁ (p ⁻¹ᵁ U))
        (p₁ ⁻¹ᵁ (g ⁻¹ᵁ U)) hV (pullbackSection f O (p ⁻¹ᵁ U) (f ⁻¹ᵁ (p ⁻¹ᵁ U)) le_rfl
          (ψ₀.val.app (op U) a)) := by
  rw [basePsi_pullbackSection_preimage p p₁ g (f₁ ≫ f) h ψ₀ U a]
  refine (congrArg (fun z => ((Scheme.Modules.pullbackComp f₁ f).inv.app O).val.app
    (op (p₁ ⁻¹ᵁ (g ⁻¹ᵁ U))) z) (Scheme.Modules.pullbackSection_comp f₁ f O (p ⁻¹ᵁ U)
      (f ⁻¹ᵁ (p ⁻¹ᵁ U)) (p₁ ⁻¹ᵁ (g ⁻¹ᵁ U)) le_rfl hV
      (preimage_le_of_comm p p₁ g (f₁ ≫ f) h U) _).symm).trans ?_
  exact congrArg (fun k => k.val.app (op (p₁ ⁻¹ᵁ (g ⁻¹ᵁ U)))
    (pullbackSection f₁ ((Scheme.Modules.pullback f).obj O) (f ⁻¹ᵁ (p ⁻¹ᵁ U))
      (p₁ ⁻¹ᵁ (g ⁻¹ᵁ U)) hV (pullbackSection f O (p ⁻¹ᵁ U) (f ⁻¹ᵁ (p ⁻¹ᵁ U)) le_rfl
        (ψ₀.val.app (op U) a))))
    ((Scheme.Modules.pullbackComp f₁ f).hom_inv_id_app O)

/-- **Base change along a composite square over the identity of the base.**  For `f₁ : P₁ ⟶ P'`
over `S'` (`f₁ ≫ p' = p₁`), base change of `ψ₀` along `f₁ ≫ f`, read through
`(f₁ ≫ f)^* ≅ f₁^* f^*`, is base change along `f` followed by the unit of `f₁^* ⊣ f₁_*`. -/
theorem basePsi_comp_unit {P₁ : Scheme.{u}} (p₁ : P₁ ⟶ S') (f₁ : P₁ ⟶ P') (h₁ : f₁ ≫ p' = p₁)
    (h₁₂ : (f₁ ≫ f) ≫ p = p₁ ≫ g) :
    basePsi p p₁ g (f₁ ≫ f) h₁₂ ψ₀ ≫
        (Scheme.Modules.pushforward p₁).map ((Scheme.Modules.pullbackComp f₁ f).inv.app O) =
      basePsi p p' g f hfg ψ₀ ≫
        (Scheme.Modules.pushforward p').map
          ((Scheme.Modules.pullbackPushforwardAdjunction f₁).unit.app
            ((Scheme.Modules.pullback f).obj O)) ≫
        (Scheme.Modules.pushforwardComp f₁ p').hom.app _ ≫
        (Scheme.Modules.pushforwardCongr h₁).hom.app _ := by
  refine ModuleLimits.hom_ext_of_pullbackSection g fun U a => ?_
  have hV : p₁ ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ f₁ ⁻¹ᵁ (p' ⁻¹ᵁ (g ⁻¹ᵁ U)) :=
    (congrArg (fun φ => φ ⁻¹ᵁ (g ⁻¹ᵁ U)) h₁).ge
  have hV' : p₁ ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ f₁ ⁻¹ᵁ (f ⁻¹ᵁ (p ⁻¹ᵁ U)) :=
    hV.trans (f₁.preimage_mono (preimage_le_of_comm p p' g f hfg U))
  have hR : ((Scheme.Modules.pullbackPushforwardAdjunction f₁).unit.app
        ((Scheme.Modules.pullback f).obj O)).val.app (op (p' ⁻¹ᵁ (g ⁻¹ᵁ U)))
        ((basePsi p p' g f hfg ψ₀).val.app (op (g ⁻¹ᵁ U))
          (pullbackSection g M U (g ⁻¹ᵁ U) le_rfl a)) =
      pullbackSection f₁ ((Scheme.Modules.pullback f).obj O) (p' ⁻¹ᵁ (g ⁻¹ᵁ U))
        (f₁ ⁻¹ᵁ (p' ⁻¹ᵁ (g ⁻¹ᵁ U))) le_rfl
        (pullbackSection f O (p ⁻¹ᵁ U) (p' ⁻¹ᵁ (g ⁻¹ᵁ U)) (preimage_le_of_comm p p' g f hfg U)
          (ψ₀.val.app (op U) a)) := by
    rw [basePsi_pullbackSection_preimage p p' g f hfg ψ₀ U a]
    unfold pullbackSection
    rw [show (homOfLE (le_refl (f₁ ⁻¹ᵁ (p' ⁻¹ᵁ (g ⁻¹ᵁ U))))).op = 𝟙 _ from Subsingleton.elim _ _]
    exact (PresheafOfModules.map_id_apply _ _ _).symm
  show ((Scheme.Modules.pullbackComp f₁ f).inv.app O).val.app (op (p₁ ⁻¹ᵁ (g ⁻¹ᵁ U)))
      ((basePsi p p₁ g (f₁ ≫ f) h₁₂ ψ₀).val.app (op (g ⁻¹ᵁ U))
        (pullbackSection g M U (g ⁻¹ᵁ U) le_rfl a)) =
    ((Scheme.Modules.pullback f₁).obj ((Scheme.Modules.pullback f).obj O)).val.map
      (homOfLE hV).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f₁).unit.app
        ((Scheme.Modules.pullback f).obj O)).val.app (op (p' ⁻¹ᵁ (g ⁻¹ᵁ U)))
        ((basePsi p p' g f hfg ψ₀).val.app (op (g ⁻¹ᵁ U))
          (pullbackSection g M U (g ⁻¹ᵁ U) le_rfl a)))
  rw [pullbackComp_inv_basePsi_pullbackSection p p₁ g f₁ f h₁₂ ψ₀ U a hV', hR,
    ModuleLimits.pullbackSection_shrink f₁ _ _ _ _ le_rfl hV hV]
  exact (pullbackSection_pullbackSection_shrink f₁ f O (p ⁻¹ᵁ U) _ _
    (preimage_le_of_comm p p' g f hfg U) hV hV' _).symm

/-- **Base change along a composite square.**  For a second square `f₁ : P₁ ⟶ P₂` over
`g₁ : S₁ ⟶ S₂` (with `f₁ ≫ p₂ = p₁ ≫ g₁`), base change of `ψ₀` along the composite square,
read through `g₁^* g₂^* ≅ (g₁ ≫ g₂)^*` and `(f₁ ≫ f₂)^* ≅ f₁^* f₂^*`, is base change along the
second square of the base change along the first. -/
theorem basePsi_comp {S₁ S₂ P₁ P₂ : Scheme.{u}} (p₂ : P₂ ⟶ S₂) (p₁ : P₁ ⟶ S₁) (g₂ : S₂ ⟶ S)
    (g₁ : S₁ ⟶ S₂) (f₂ : P₂ ⟶ P) (f₁ : P₁ ⟶ P₂) (h₂ : f₂ ≫ p = p₂ ≫ g₂)
    (h₁ : f₁ ≫ p₂ = p₁ ≫ g₁) (h₁₂ : (f₁ ≫ f₂) ≫ p = p₁ ≫ (g₁ ≫ g₂)) :
    (Scheme.Modules.pullbackComp g₁ g₂).hom.app M ≫ basePsi p p₁ (g₁ ≫ g₂) (f₁ ≫ f₂) h₁₂ ψ₀ ≫
        (Scheme.Modules.pushforward p₁).map ((Scheme.Modules.pullbackComp f₁ f₂).inv.app O) =
      basePsi p₂ p₁ g₁ f₁ h₁ (basePsi p p₂ g₂ f₂ h₂ ψ₀) := by
  refine ModuleLimits.hom_ext_of_doublePullbackSection g₁ g₂ fun U a => ?_
  have hV : p₁ ⁻¹ᵁ (g₁ ⁻¹ᵁ (g₂ ⁻¹ᵁ U)) ≤ f₁ ⁻¹ᵁ (f₂ ⁻¹ᵁ (p ⁻¹ᵁ U)) :=
    (preimage_le_of_comm p₂ p₁ g₁ f₁ h₁ (g₂ ⁻¹ᵁ U)).trans
      (f₁.preimage_mono (preimage_le_of_comm p p₂ g₂ f₂ h₂ U))
  have hC : ((Scheme.Modules.pullbackComp g₁ g₂).hom.app M).val.app
      (op (g₁ ⁻¹ᵁ (g₂ ⁻¹ᵁ U))) (ModuleLimits.doublePullbackSection g₁ g₂ M U a) =
      pullbackSection (g₁ ≫ g₂) M U ((g₁ ≫ g₂) ⁻¹ᵁ U) le_rfl a :=
    Scheme.Modules.pullbackSection_comp g₁ g₂ M U (g₂ ⁻¹ᵁ U) _ le_rfl le_rfl le_rfl a
  have hR : (basePsi p₂ p₁ g₁ f₁ h₁ (basePsi p p₂ g₂ f₂ h₂ ψ₀)).val.app
      (op (g₁ ⁻¹ᵁ (g₂ ⁻¹ᵁ U))) (ModuleLimits.doublePullbackSection g₁ g₂ M U a) =
      pullbackSection f₁ ((Scheme.Modules.pullback f₂).obj O) (f₂ ⁻¹ᵁ (p ⁻¹ᵁ U))
        (p₁ ⁻¹ᵁ (g₁ ⁻¹ᵁ (g₂ ⁻¹ᵁ U))) hV (pullbackSection f₂ O (p ⁻¹ᵁ U) (f₂ ⁻¹ᵁ (p ⁻¹ᵁ U))
          le_rfl (ψ₀.val.app (op U) a)) := by
    rw [ModuleLimits.doublePullbackSection,
      basePsi_pullbackSection_preimage p₂ p₁ g₁ f₁ h₁ _ (g₂ ⁻¹ᵁ U),
      basePsi_pullbackSection_preimage p p₂ g₂ f₂ h₂ ψ₀ U a]
    exact pullbackSection_pullbackSection_shrink f₁ f₂ O (p ⁻¹ᵁ U) _ _
      (preimage_le_of_comm p p₂ g₂ f₂ h₂ U) _ hV _
  show ((Scheme.Modules.pullbackComp f₁ f₂).inv.app O).val.app
      (op (p₁ ⁻¹ᵁ ((g₁ ≫ g₂) ⁻¹ᵁ U)))
      ((basePsi p p₁ (g₁ ≫ g₂) (f₁ ≫ f₂) h₁₂ ψ₀).val.app (op ((g₁ ≫ g₂) ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackComp g₁ g₂).hom.app M).val.app
          (op (g₁ ⁻¹ᵁ (g₂ ⁻¹ᵁ U))) (ModuleLimits.doublePullbackSection g₁ g₂ M U a))) = _
  rw [hC, pullbackComp_inv_basePsi_pullbackSection p p₁ (g₁ ≫ g₂) f₁ f₂ h₁₂ ψ₀ U a hV]
  exact hR.symm

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
