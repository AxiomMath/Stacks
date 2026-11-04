module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerDivisorBaseChange

/-!
# The Kummer flag class under inverse image

Let `g : U' ⟶ U` be a morphism of `k`-schemes and `D`, `D'` flags of `d` divisor data on `U` and
`U'` with `g(V'_m) ⊆ V_m`, `g(W'_m) ⊆ W_m` and `a'_m = g^♯ a_m`. The inverse image along `g` of the
Kummer flag class of `D`, read through `g⁻¹ Λ_U ≅ Λ_{U'}` and the identification
`g⁻¹(E_0 ⋯ E_{d-1} Λ_U) ≅ E'_0 ⋯ E'_{d-1} Λ_{U'}` built from
`Stacks.EtaleCohomology.closedRestrictionInverseImageIso`, is the Kummer flag class of `D'`
(`Stacks.EtaleCohomology.KummerFlag.transport_kummerFlagClass`): by induction, the first divisor
class is natural (`Stacks.EtaleCohomology.KummerFlag.transport_kummerDivisorClass`) and `g⁻¹`
commutes with the restrictions `E_0` (`Stacks.EtaleCohomology.KummerFlag.transport_map`).
Raising every unit to the power `e` multiplies the class by `e^d`
(`Stacks.EtaleCohomology.KummerFlag.kummerFlagClassPow_eq`).

## Main definitions

* `Stacks.EtaleCohomology.KummerFlag.flagSheafIso`
* `Stacks.EtaleCohomology.KummerFlag.kummerFlagClassPow`

## Main results

* `Stacks.EtaleCohomology.KummerFlag.transport_kummerFlagClass`
* `Stacks.EtaleCohomology.KummerFlag.kummerFlagClassPow_eq`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.ExtTransport

universe u

namespace Stacks.EtaleCohomology.KummerFlag

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits comp_preservesFiniteLimits
  comp_preservesFiniteColimits

section Abstract

variable {C C' : Type*} [Category C] [Abelian C] [Category C'] [Abelian C'] [HasExt C]
  [HasExt C'] [EnoughInjectives C] (G : C ⥤ C') [G.Additive] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G] (E : C ⥤ C) [E.Additive] [PreservesFiniteLimits E]
  [PreservesFiniteColimits E] (E' : C' ⥤ C') [E'.Additive] [PreservesFiniteLimits E']
  [PreservesFiniteColimits E'] (β : E ⋙ G ≅ G ⋙ E')

/-- **An exact functor commuting with `G` commutes with transport along `G`.** -/
theorem transport_map {X Y : C} {X' Y' : C'} (eX : X' ≅ G.obj X) (eY : Y' ≅ G.obj Y) {n : ℕ}
    (y : Ext X Y n) :
    transport G (E'.map eX.hom ≫ β.inv.app X) (β.hom.app Y ≫ E'.map eY.inv) n
        (y.mapExactFunctor E) =
      (transport G eX.hom eY.inv n y).mapExactFunctor E' := by
  have h1 : transport G (E'.map eX.hom ≫ β.inv.app X) (β.hom.app Y ≫ E'.map eY.inv) n
      (y.mapExactFunctor E) = transport (E ⋙ G) (E'.map eX.hom ≫ β.inv.app X)
        (β.hom.app Y ≫ E'.map eY.inv) n y := by
    rw [transport_apply, transport_apply, Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
  have h2 : (transport G eX.hom eY.inv n y).mapExactFunctor E' =
      transport (G ⋙ E') (E'.map eX.hom) (E'.map eY.inv) n y := by
    rw [transport_apply, transport_apply, sandwich_apply, sandwich_apply, Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀,
      Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
  rw [h1, h2, transport_iso β]

end Abstract

/-- The Yoneda product of `m • x` and `n • y` is `(m * n) • (x ∘ y)`. -/
theorem nsmul_comp_nsmul {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y Z : C} {a b c : ℕ}
    (x : Ext X Y a) (y : Ext Y Z b) (h : a + b = c) (m n : ℕ) :
    (m • x).comp (n • y) h = (m * n) • x.comp y h := by
  have h1 : (m • x).comp (n • y) h = m • x.comp (n • y) h :=
    map_nsmul ((n • y).postcomp X h) m x
  have h2 : x.comp (n • y) h = n • x.comp y h := map_nsmul (x.precomp Z h) n y
  rw [h1, h2, smul_smul]

section Flag

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))
  {U U' : Scheme.{u}} (fU : U ⟶ Spec (.of k)) (fU' : U' ⟶ Spec (.of k)) (g : U' ⟶ U)
  (hg : g ≫ fU = fU')

/-- The Kummer flag class of `d` divisor data with every unit raised to the power `e`. -/
def kummerFlagClassPow (e : ℕ) : {d : ℕ} → (D : Fin d → DivisorDatum U) →
    Ext (flagSheaf (N := N) D) (unitSheaf (X := U) N) (2 * d)
  | 0, _ => Ext.mk₀ (𝟙 _)
  | d + 1, D => ((kummerFlagClassPow e (fun m => D m.succ)).mapExactFunctor
      (closedRestriction (N := N) (D 0).i)).comp
        (kummerDivisorClass hζ hN fU (D 0).j (D 0).i (D 0).range_eq ((D 0).a ^ e)) (by ring)

/-- Raising the units to the power `1` gives the Kummer flag class. -/
theorem kummerFlagClassPow_one : ∀ {d : ℕ} (D : Fin d → DivisorDatum U),
    kummerFlagClassPow hζ hN fU 1 D = kummerFlagClass hζ hN fU D
  | 0, _ => rfl
  | d + 1, D => by
    rw [kummerFlagClassPow, kummerFlagClass, kummerFlagClassPow_one (fun m => D m.succ), pow_one]

/-- **Raising the units to the power `e` multiplies the Kummer flag class by `e^d`.** -/
theorem kummerFlagClassPow_eq (e : ℕ) : ∀ {d : ℕ} (D : Fin d → DivisorDatum U),
    kummerFlagClassPow hζ hN fU e D = (e ^ d) • kummerFlagClass hζ hN fU D
  | 0, _ => by rw [pow_zero, one_smul]; rfl
  | d + 1, D => by
    rw [kummerFlagClassPow, kummerFlagClass, kummerFlagClassPow_eq e (fun m => D m.succ),
      kummerDivisorClass_pow]
    rw [show ((e ^ d) • kummerFlagClass hζ hN fU (fun m => D m.succ)).mapExactFunctor
        (closedRestriction (N := N) (D 0).i) = (e ^ d) • (kummerFlagClass hζ hN fU
          (fun m => D m.succ)).mapExactFunctor (closedRestriction (N := N) (D 0).i) from
        map_nsmul ((closedRestriction (N := N) (D 0).i).mapExtAddHom _ _ _) _ _,
      nsmul_comp_nsmul, pow_succ]
    rfl

variable (N) in
/-- The identification `E'_0 ⋯ E'_{d-1} Λ_{U'} ≅ g⁻¹(E_0 ⋯ E_{d-1} Λ_U)` of the sheaves carrying
the Kummer flag classes. -/
def flagSheafIso : {d : ℕ} → (D : Fin d → DivisorDatum U) → (D' : Fin d → DivisorDatum U') →
    (gV : ∀ m, (D' m).V ⟶ (D m).V) → (∀ m, (D' m).j ≫ g = gV m ≫ (D m).j) →
    (gW : ∀ m, (D' m).W ⟶ (D m).W) → (∀ m, (D' m).i ≫ g = gW m ≫ (D m).i) →
    (flagSheaf (N := N) D' ≅ (etaleModuleInverseImage.{u, 0} (ZMod N) g).obj (flagSheaf (N := N) D))
  | 0, _, _, _, _, _, _ => constantInverseImageIso (ZMod N) g
  | _ + 1, D, D', gV, hV, gW, hW =>
      (closedRestriction (N := N) (D' 0).i).mapIso
          (flagSheafIso (fun m => D m.succ) (fun m => D' m.succ) (fun m => gV m.succ)
            (fun m => hV m.succ) (fun m => gW m.succ) (fun m => hW m.succ)) ≪≫
        (closedRestrictionInverseImageIsoApp (ZMod N) g (D 0).i (D 0).j (D 0).range_eq (D' 0).i
          (D' 0).j (D' 0).range_eq (gW 0) (hW 0) (gV 0) (hV 0)
          (flagSheaf (N := N) (fun m => D m.succ))).symm

include hζ hg in
/-- **The Kummer flag class is natural under inverse image**: if `g(V'_m) ⊆ V_m`, `g(W'_m) ⊆ W_m`
and `g^♯ a_m = a'_m ^ e`, the inverse image of the Kummer flag class of `D` is the Kummer flag
class of `D'` with units raised to the power `e`. -/
theorem transport_kummerFlagClass [NeZero N] (e : ℕ) : ∀ {d : ℕ} (D : Fin d → DivisorDatum U)
    (D' : Fin d → DivisorDatum U') (gV : ∀ m, (D' m).V ⟶ (D m).V)
    (hV : ∀ m, (D' m).j ≫ g = gV m ≫ (D m).j) (gW : ∀ m, (D' m).W ⟶ (D m).W)
    (hW : ∀ m, (D' m).i ≫ g = gW m ≫ (D m).i)
    (_ : ∀ m, Units.map (gV m).appTop.hom (D m).a = (D' m).a ^ e)
    [∀ m, PreconnectedSpace (D' m).V],
    transport (etaleModuleInverseImage.{u, 0} (ZMod N) g)
        (flagSheafIso N g D D' gV hV gW hW).hom (constantInverseImageIso (ZMod N) g).inv (2 * d)
        (kummerFlagClass hζ hN fU D) =
      kummerFlagClassPow hζ hN fU' e D'
  | 0, D, D', gV, hV, gW, hW, _, _ => by
    show transport (etaleModuleInverseImage.{u, 0} (ZMod N) g)
      (constantInverseImageIso (ZMod N) g).hom (constantInverseImageIso (ZMod N) g).inv 0
        (Ext.mk₀ (𝟙 (unitSheaf (X := U) N))) = Ext.mk₀ (𝟙 (unitSheaf (X := U') N))
    rw [transport_apply, sandwich_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
      Ext.mk₀_comp_mk₀, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  | d + 1, D, D', gV, hV, gW, hW, ha, _ => by
    have := etaleModules_enoughInjectives.{u, 0} (ZMod N) U
    rw [kummerFlagClass, kummerFlagClassPow]
    refine (transport_comp (etaleModuleInverseImage.{u, 0} (ZMod N) g) _
      (divisorThirdIso (N := N) g (D 0) (D' 0) (gV 0) (hV 0) (gW 0) (hW 0)) _ _ _ _).trans ?_
    rw [transport_kummerDivisorClass hζ hN fU fU' g hg (D 0) (D' 0) (gV 0) (hV 0) (gW 0) (hW 0),
      ha 0]
    congr 1
    have h := transport_map (etaleModuleInverseImage.{u, 0} (ZMod N) g)
      (closedRestriction (N := N) (D 0).i) (closedRestriction (N := N) (D' 0).i)
      (closedRestrictionInverseImageIso (ZMod N) g (D 0).i (D 0).j (D 0).range_eq (D' 0).i
        (D' 0).j (D' 0).range_eq (gW 0) (hW 0) (gV 0) (hV 0))
      (flagSheafIso N g (fun m => D m.succ) (fun m => D' m.succ) (fun m => gV m.succ)
        (fun m => hV m.succ) (fun m => gW m.succ) (fun m => hW m.succ))
      (constantInverseImageIso (ZMod N) g) (kummerFlagClass hζ hN fU (fun m => D m.succ))
    rwa [transport_kummerFlagClass e (fun m => D m.succ) (fun m => D' m.succ) (fun m => gV m.succ)
      (fun m => hV m.succ) (fun m => gW m.succ) (fun m => hW m.succ) (fun m => ha m.succ)] at h

end Flag

end Stacks.EtaleCohomology.KummerFlag

end
