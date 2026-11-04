module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyConstantDevissage
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingAbsolute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional

/-!
# Duality for locally constant `ℤ/ℓ`-coefficients on a proper scheme, from the constant case

Let `X` be a connected scheme proper over an algebraically closed field `k`, of dimension at most
`d`, and `t` an injective trace on `Ext^{2d}(ℤ/ℓ_X, ℤ/ℓ_X)`.  Poincaré duality for every finite
type locally constant sheaf of `ℤ/ℓ`-modules on `X`,

`Ext^i(ℤ/ℓ, F) × Ext^{2d-i}(F, ℤ/ℓ) → Ext^{2d}(ℤ/ℓ, ℤ/ℓ) → ℤ/ℓ` perfect,

follows from duality for the constant sheaf `ℤ/ℓ_T` on every connected finite étale `T → X`
(for any injective trace), given that `Ext^{2d}(ℤ/ℓ_T, ℤ/ℓ_T)` is finite with as many elements
as `Ext^{2d}(ℤ/ℓ_X, ℤ/ℓ_X)`.  This is the dévissage
`Stacks.EtaleCohomology.isDualityPerfect_of_isFiniteTypeLocallyConstant` with `N = 2d`; the
vanishing it needs, `Ext^q(ℤ/ℓ_T, K) = H^q(T, K) = 0` for `q > 2d`, is Tag 095U.

## Main results

* `Stacks.EtaleCohomology.subsingleton_ext_unitSheaf_of_proper`.
* `Stacks.EtaleCohomology.isDualityPerfect_of_isFiniteTypeLocallyConstant_of_proper`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **`Ext^q(ℤ/ℓ_T, K) = 0` for `q > 2 dim T`** on a scheme proper over a separably closed field
(Tag 095U, read in sheaves of `ℤ/ℓ`-modules through
`Stacks.EtaleCohomology.extForgetSheafHAddEquiv`). -/
theorem subsingleton_ext_unitSheaf_of_proper {k : Type u} [Field k] [IsSepClosed k]
    {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) [IsProper g] (d : ℕ)
    (hdim : topologicalKrullDim T ≤ d) (K : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ)
    (hq : 2 * d < q) : Subsingleton (Ext (unitSheaf (X := T) ℓ) K q) := by
  have h : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian T (ZMod ℓ)).obj K) q) :=
    properSeparablyClosedSheafHVanishingStatement_of_properDirectImageVanishingStatement
      properDirectImageVanishingStatement k g d hdim _
      (torsionSheafProperty_etaleModuleUnderlyingAbelian_zmod ℓ K) q hq
  exact (extForgetSheafHAddEquiv (ZMod ℓ) T K q).toEquiv.subsingleton

section Proper

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsProper f] (d : ℕ)

include f in
/-- `Ext^q(ℤ/ℓ_T, K) = 0` for `q > 2d` on a finite étale `T` over a proper scheme of dimension at
most `d`. -/
theorem subsingleton_ext_unitSheaf_of_finiteEtale_proper (hdim : topologicalKrullDim X ≤ d)
    {T : Scheme.{u}} (π : T ⟶ X) [IsFinite π] [Etale π] (K : EtaleModules.{u, 0} (ZMod ℓ) T)
    (q : ℕ) (hq : 2 * d < q) : Subsingleton (Ext (unitSheaf (X := T) ℓ) K q) :=
  subsingleton_ext_unitSheaf_of_proper (π ≫ f) d
    ((topologicalKrullDim_le_of_etale π).trans hdim) K q hq

include f in
/-- **Poincaré duality for finite type locally constant `ℤ/ℓ`-coefficients on a connected scheme
proper over a separably closed field, from the constant case.**  Let `dim X ≤ d` and `t` be an
injective trace on `Ext^{2d}(ℤ/ℓ_X, ℤ/ℓ_X)`.  If on every connected finite étale `T → X` the group
`Ext^{2d}(ℤ/ℓ_T, ℤ/ℓ_T)` is finite with as many elements as `Ext^{2d}(ℤ/ℓ_X, ℤ/ℓ_X)` and duality
holds at `ℤ/ℓ_T` for every injective trace, then the Yoneda pairing
`Ext^i(ℤ/ℓ, F) × Ext^{2d-i}(F, ℤ/ℓ) → ℤ/ℓ` is perfect for every finite type locally constant
`F`. -/
theorem isDualityPerfect_of_isFiniteTypeLocallyConstant_of_proper [ConnectedSpace X]
    (hdim : topologicalKrullDim X ≤ d)
    (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ) (ht : Function.Injective t)
    (hcard : ∀ (T : Scheme.{u}) (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T],
      Finite (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) (2 * d)) ∧
        Nat.card (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) (2 * d)) =
          Nat.card (Ext (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) (2 * d)))
    (hconst : ∀ (T : Scheme.{u}) (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T]
      (t' : Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ), Function.Injective t' →
        Ext.IsDualityPerfect (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) t' (unitSheaf ℓ))
    (F : EtaleModules.{u, 0} (ZMod ℓ) X)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology F) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) t F := by
  refine isDualityPerfect_of_isFiniteTypeLocallyConstant (2 * d) t
    (fun T π _ _ K => subsingleton_ext_unitSheaf_of_finiteEtale_proper f d hdim π K _
      (by omega)) (fun T π _ _ _ => ?_) F hF
  have := surjective_of_finiteEtale_of_connectedSpace π
  obtain ⟨hfin, hc⟩ := hcard T π
  exact hconst T π _ (injective_coverTrace π (2 * d) t ht
    (fun K => subsingleton_ext_unitSheaf_of_finiteEtale_proper f d hdim (𝟙 X) K _ (by omega)) hc)

end Proper

end Stacks.EtaleCohomology
