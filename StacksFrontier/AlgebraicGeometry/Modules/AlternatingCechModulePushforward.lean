module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChange
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Čech cochains of a direct image

Let `g : X' ⟶ X` be a morphism of schemes, `U : I → X.Opens` a family of opens and `U'` its
inverse image, `U' i = g ⁻¹ᵁ U i`. For an `𝒪_{X'}`-module `ℳ` the sections of `g_*ℳ` over an
open `W` of `X` are the sections of `ℳ` over `g ⁻¹ᵁ W`, so a Čech cochain of `g_*ℳ` for `U` is a
Čech cochain of `ℳ` for `U'`, up to the identification of the intersections of `U'` with the
preimages of the intersections of `U`. This file records that transport and its compatibility
with the Čech differential and with alternating cochains.

## Main definitions

* `Stacks.Cech.cochainPushforward`: the transport of Čech cochains.
* `Stacks.Cech.alternatingCochainPushforward`: its restriction to alternating cochains.

## Main results

* `Stacks.Cech.cochainPushforward_cechD`: the transport commutes with the Čech differential.
* `Stacks.Cech.cochainPushforward_isAlternating`: it preserves alternating cochains.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cech

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {I : Type u} (U : I → X.Opens) (U' : I → X'.Opens)
  (hU' : ∀ i, U' i = g ⁻¹ᵁ U i) (M : X'.Modules)

/-- Two composites of restrictions with the same source and target agree. -/
theorem restr_restr_eq {Y : TopCat} (ℱ : TopCat.Presheaf Ab Y) {V W W' Z : Opens Y}
    (h₁ : W ≤ V) (h₂ : Z ≤ W) (h₃ : W' ≤ V) (h₄ : Z ≤ W') (x : (ℱ.obj (op V) : Type _)) :
    CechCochains.restr ℱ h₂ (CechCochains.restr ℱ h₁ x) =
      CechCochains.restr ℱ h₄ (CechCochains.restr ℱ h₃ x) := by
  rw [CechCochains.restr_restr, CechCochains.restr_restr]

/-- The direct image `g_*ℳ`, as a module on the scheme `X`. -/
abbrev pushforwardModule : X.Modules := (modulePushforward g.toLRSHom.toShHom).obj M

include hU' in
/-- The intersection of `U'` lies in the preimage of the intersection of `U`, spelled through the
inverse-image functor on opens that the direct image is built with. -/
theorem inter_le_opensMap {p : ℕ} (i : Fin (p + 1) → I) :
    CechCochains.inter U' i ≤ (opensMap g.toLRSHom.toShHom).obj (CechCochains.inter U i) :=
  (inter_eq_preimage g U U' (Equiv.refl I) hU' i).le

/-- **Transport of a Čech cochain of `g_*ℳ` for `U` to a Čech cochain of `ℳ` for `U'`**: in
each tuple, restrict the section of `ℳ` over the preimage of the intersection of `U` to the
intersection of `U'`. -/
def cochainPushforward (p : ℕ)
    (s : CechCochains.Cochain U (pushforwardModule g M).presheaf p) :
    CechCochains.Cochain U' M.presheaf p := fun i ↦
  CechCochains.restr M.presheaf (inter_le_opensMap g U U' hU' i) (s i)

/-- The transport is additive. -/
theorem cochainPushforward_add (p : ℕ)
    (s t : CechCochains.Cochain U (pushforwardModule g M).presheaf p) :
    cochainPushforward g U U' hU' M p (s + t) =
      cochainPushforward g U U' hU' M p s + cochainPushforward g U U' hU' M p t := by
  funext i
  exact map_add _ (s i) (t i)

/-- Restriction in the direct image is restriction along the preimages. -/
theorem restr_modulePushforward {V W : X.Opens} (h : W ≤ V)
    (x : Γ(pushforwardModule g M, V)) :
    CechCochains.restr (pushforwardModule g M).presheaf h x =
      CechCochains.restr M.presheaf ((opensMap g.toLRSHom.toShHom).monotone h) x :=
  rfl

/-- **The transport commutes with the Čech differential.** -/
theorem cochainPushforward_cechD (p : ℕ)
    (s : CechCochains.Cochain U (pushforwardModule g M).presheaf p) :
    CechCochains.cechD U' M.presheaf p (cochainPushforward g U U' hU' M p s) =
      cochainPushforward g U U' hU' M (p + 1)
        (CechCochains.cechD U (pushforwardModule g M).presheaf p s) := by
  funext i
  show (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr M.presheaf (CechCochains.inter_le_omit U' i j)
        (CechCochains.restr M.presheaf (inter_le_opensMap g U U' hU' (i ∘ j.succAbove))
          (s (i ∘ j.succAbove)))) =
    CechCochains.restr M.presheaf (inter_le_opensMap g U U' hU' i)
      (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr M.presheaf
          ((opensMap g.toLRSHom.toShHom).monotone (CechCochains.inter_le_omit U i j))
          (s (i ∘ j.succAbove)))
  refine Eq.trans ?_ (map_sum _ _ _).symm
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  refine Eq.trans ?_ (map_zsmul _ _ _).symm
  exact congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) (restr_restr_eq M.presheaf _ _ _ _ _)

/-- **The transport carries alternating cochains to alternating cochains.** -/
theorem cochainPushforward_isAlternating (p : ℕ)
    (s : CechCochains.Cochain U (pushforwardModule g M).presheaf p)
    (hs : CechCochains.IsAlternating U (pushforwardModule g M).presheaf s) :
    CechCochains.IsAlternating U' M.presheaf (cochainPushforward g U U' hU' M p s) := by
  refine ⟨fun i hi ↦ ?_, fun i a b hab ↦ ?_⟩
  · show CechCochains.restr M.presheaf (inter_le_opensMap g U U' hU' i) (s i) = 0
    rw [hs.1 i hi]
    exact map_zero _
  · show CechCochains.restr M.presheaf (inter_le_opensMap g U U' hU' (i ∘ Equiv.swap a b))
        (s (i ∘ Equiv.swap a b)) =
      -CechCochains.permIso U' M.presheaf i (Equiv.swap a b)
        (CechCochains.restr M.presheaf (inter_le_opensMap g U U' hU' i) (s i))
    rw [hs.2 i a b hab]
    refine (map_neg _ _).trans (congrArg Neg.neg ?_)
    exact restr_restr_eq M.presheaf _ _ _ _ _

/-- The transport on alternating cochains. -/
def alternatingCochainPushforward (p : ℕ)
    (s : CechCochains.alternatingSubgroup U
      (pushforwardModule g M).presheaf p) :
    CechCochains.alternatingSubgroup U' M.presheaf p :=
  ⟨cochainPushforward g U U' hU' M p s.1, cochainPushforward_isAlternating g U U' hU' M p s.1 s.2⟩

end Stacks.Cech

end
