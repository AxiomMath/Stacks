module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyConstantDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurvePoincareDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Poincaré duality for locally constant `ℤ/ℓ`-coefficients on a smooth proper curve

Let `X` be a smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible
in `k` and `t : H²(X, ℤ/ℓ) → ℤ/ℓ` an injective trace. For every finite type locally constant sheaf
`F` of `ℤ/ℓ`-modules on `X` the Yoneda pairing

`Ext^i(ℤ/ℓ, F) × Ext^{2-i}(F, ℤ/ℓ) → Ext²(ℤ/ℓ, ℤ/ℓ) → ℤ/ℓ`

is perfect.

This is the dévissage `Stacks.EtaleCohomology.isDualityPerfect_of_isFiniteTypeLocallyConstant`
applied with:

* the vanishing `H^q(T, K) = 0` for `q > 2` on every curve `T` (Tag 0A53,
  `Stacks.EtaleCohomology.TorsionSheafSituation.isVanishingAboveDegreeTwo`), read in sheaves of
  `ℤ/ℓ`-modules through `Stacks.EtaleCohomology.extForgetSheafHAddEquiv`;
* duality at `ℤ/ℓ_T` on a connected finite étale cover `T`, which is again a smooth proper curve
  (`Stacks.EtaleCohomology.ExtensionTorsor.isDualityPerfect_unitSheaf`), for the transferred
  trace, which is injective: the transfer `H²(T, ℤ/ℓ) → H²(X, ℤ/ℓ)` is onto
  (`CategoryTheory.Abelian.Ext.surjective_transferTrace_id`, the trace `π_*ℤ/ℓ → ℤ/ℓ` being onto
  and `H³ = 0`), and both groups have `ℓ` elements.

## Main results

* `Stacks.EtaleCohomology.subsingleton_ext_unitSheaf_of_curve`: `Ext^q(ℤ/ℓ_T, K) = 0`, `q > 2`.
* `Stacks.EtaleCohomology.injective_coverTrace_of_smoothProperCurve`.
* `Stacks.EtaleCohomology.isDualityPerfect_of_isFiniteTypeLocallyConstant_of_smoothProperCurve`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **`Ext^q(ℤ/ℓ_T, K) = 0` for `q > 2`** on a separated scheme of finite type and dimension at
most one over an algebraically closed field (Tag 0A53). -/
theorem subsingleton_ext_unitSheaf_of_curve {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g] (hdim : topologicalKrullDim T ≤ 1) (K : EtaleModules.{u, 0} (ZMod ℓ) T)
    (q : ℕ) (hq : 2 < q) : Subsingleton (Ext (unitSheaf (X := T) ℓ) K q) := by
  let S : TorsionSheafSituation.{u, 0} :=
    { k := k
      X := T
      structureMorphism := g
      dimension_le_one := hdim
      F := (etaleModuleUnderlyingAbelian T (ZMod ℓ)).obj K
      isTorsion := by
        intro U x
        refine ⟨⊤, T.smallEtaleTopology.top_mem U, fun V h _ => ⟨ℓ, (Fact.out : ℓ.Prime).pos, ?_⟩⟩
        change ℓ • (K.obj.map h.op x : K.obj.obj (Opposite.op V)) = 0
        rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul] }
  have : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian T (ZMod ℓ)).obj K) q) :=
    S.isVanishingAboveDegreeTwo q hq
  exact (extForgetSheafHAddEquiv (ZMod ℓ) T K q).toEquiv.subsingleton

/-- A connected finite étale cover of a curve is a curve. -/
private theorem isCurve_comp_of_finiteEtale {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f] {T : Scheme.{u}} (π : T ⟶ X)
    [IsFinite π] [Etale π] [ConnectedSpace T] : IsCurve k (π ≫ f) := by
  have : IsFinite (Scheme.Etale.mk π).hom := ‹IsFinite π›
  have : ConnectedSpace (Scheme.Etale.mk π).left := ‹ConnectedSpace T›
  exact isCurve_comp_of_isFinite f (V := Scheme.Etale.mk π)

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

omit [IsProper f] in
include f in
/-- `Ext^q(ℤ/ℓ_T, K) = 0` for `q > 2` on a finite étale cover `T` of a curve. -/
theorem subsingleton_ext_unitSheaf_of_finiteEtale_curve {T : Scheme.{u}} (π : T ⟶ X)
    [IsFinite π] [Etale π] (K : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext (unitSheaf (X := T) ℓ) K q) := by
  have hdim : topologicalKrullDim T ≤ 1 :=
    IsCurve.topologicalKrullDim_eq_one f ▸ topologicalKrullDim_le_of_etale π
  exact subsingleton_ext_unitSheaf_of_curve (π ≫ f) hdim K q hq

include f in
/-- On a connected finite étale cover `T` of a smooth proper curve, the trace transferred from an
injective trace on `H²(X, ℤ/ℓ)` is injective on `H²(T, ℤ/ℓ)`. -/
theorem injective_coverTrace_of_smoothProperCurve (hℓ : IsUnit (ℓ : k))
    (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (ht : Function.Injective t)
    {T : Scheme.{u}} (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T] :
    Function.Injective (coverTrace π 2 t) := by
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have := surjective_of_finiteEtale_of_connectedSpace π
  have : IsCurve k (π ≫ f) := isCurve_comp_of_finiteEtale f π
  have hT : Nat.card (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) 2) = ℓ :=
    natCard_ext_two_unitSheaf (π ≫ f) hℓ
  have : Finite (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) 2) :=
    Nat.finite_of_card_ne_zero (by rw [hT]; exact (Fact.out : ℓ.Prime).ne_zero)
  exact injective_coverTrace π 2 t ht
    (fun K => subsingleton_ext_unitSheaf_of_finiteEtale_curve f (𝟙 X) K 3 (by norm_num))
    (by rw [hT, natCard_ext_two_unitSheaf f hℓ])

include f in
/-- **Poincaré duality for finite type locally constant `ℤ/ℓ`-coefficients on a smooth proper
curve** over an algebraically closed field, `ℓ` invertible: for an injective trace
`t : H²(X, ℤ/ℓ) → ℤ/ℓ` the Yoneda pairing `Ext^i(ℤ/ℓ, F) × Ext^{2-i}(F, ℤ/ℓ) → ℤ/ℓ` is perfect in
every degree. -/
@[sga "4½ Arcata 6.1" "special case"]
theorem isDualityPerfect_of_isFiniteTypeLocallyConstant_of_smoothProperCurve
    (hℓ : IsUnit (ℓ : k)) (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ)
    (ht : Function.Injective t) (F : EtaleModules.{u, 0} (ZMod ℓ) X)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology F) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2 t F := by
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  refine isDualityPerfect_of_isFiniteTypeLocallyConstant 2 t
    (fun T π _ _ K => subsingleton_ext_unitSheaf_of_finiteEtale_curve f π K 3 (by norm_num))
    (fun T π _ _ _ => ?_) F hF
  have : IsCurve k (π ≫ f) := isCurve_comp_of_finiteEtale f π
  exact isDualityPerfect_unitSheaf (π ≫ f) hℓ (coverTrace π 2 t)
    (injective_coverTrace_of_smoothProperCurve f hℓ t ht π)

end Curve

end Stacks.EtaleCohomology

end
