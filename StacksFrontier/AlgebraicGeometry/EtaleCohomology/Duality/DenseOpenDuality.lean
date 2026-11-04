module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.OpenClosedDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleOpens
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces

/-!
# Poincaré duality from a dense open, stratum by stratum

Let `W` be a scheme with noetherian underlying space, `L` a sheaf of `ℤ/ℓ`-modules on `W`, and
`Φ` an exact functor from sheaves on `W` to sheaves on a scheme `X̄` (for an open `j : W → X̄`,
`Φ = j_!`). For an open `V` of `W` write `F_V = j_{V!} L|_V`; for `V ≤ V'` the comparison
`F_V → F_{V'}` is a monomorphism, and its cokernel is supported on `V' \ V`.

Suppose duality holds on `X̄` (for `O = ℤ/ℓ_X̄`, a dualizing object `D` and a trace `t` on
`Ext^N(ℤ/ℓ, D)`) at `Φ(F_{W°})` for an open `W°`, with `Ext^q(Φ(F_{W°}), D) = 0` for `q > N`, and
that every open `V ⊇ W°` other than `W` is contained in a strictly larger open `V'` with a short
exact sequence `0 → F_V → F_{V'} → C → 0` such that duality and the same vanishing hold at
`Φ(C)`. If moreover `Ext^{N+1}(ℤ/ℓ, Φ(M)) = 0` for every sheaf `M` on `W` (for `Φ = j_!` and `X̄`
proper of dimension at most `N / 2` this is Tag 095U), then duality and the vanishing hold at
`Φ(L)`.

The noetherian hypothesis is used through the ascending chain condition on the opens of `W`: a
maximal open `V ⊇ W°` at which the conclusion holds exists, and it is `W`, since otherwise the
five lemma `CategoryTheory.Abelian.Ext.isDualityPerfect_X₂` and the long exact sequence of
`Ext(-, D)` give the conclusion at a strictly larger `V'`.

## Main results

* `Stacks.EtaleCohomology.isDualityPerfect_of_dense_open`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime] {W X : Scheme.{u}}
  (Φ : EtaleModules.{u, 0} (ZMod ℓ) W ⥤ EtaleModules.{u, 0} (ZMod ℓ) X) [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (L : EtaleModules.{u, 0} (ZMod ℓ) W)
  (D : EtaleModules.{u, 0} (ZMod ℓ) X) {N : ℕ} (t : Ext (unitSheaf (X := X) ℓ) D N →+ ZMod ℓ)

/-- Duality on `X̄` at `Φ(L)`, together with the vanishing of `Ext^q(Φ(L), D)` for `q > N`, from
the same at `Φ(F_{W₀})` for an open `W₀` and at the third term `Φ(C)` of a short exact sequence
`0 → F_V → F_{V'} → C → 0` (up to isomorphism of its first two terms) for every open `V ⊇ W₀`
other than `W`, with `V < V'`, provided `Ext^{N+1}(ℤ/ℓ, Φ(M)) = 0` for every sheaf `M` on `W`. -/
theorem isDualityPerfect_of_dense_open [TopologicalSpace.NoetherianSpace W] (W₀ : W.Opens)
    (hvan : ∀ M : EtaleModules.{u, 0} (ZMod ℓ) W,
      Subsingleton (Ext (unitSheaf (X := X) ℓ) (Φ.obj M) (N + 1)))
    (h₀ : Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
        (Φ.obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj L)) ∧
      ∀ q, N < q → Subsingleton
        (Ext (Φ.obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj L)) D q))
    (hstrat : ∀ V : W.Opens, W₀ ≤ V → V ≠ ⊤ → ∃ (V' : W.Opens) (_ : V < V')
      (S : ShortComplex (EtaleModules.{u, 0} (ZMod ℓ) W)), S.ShortExact ∧
        Nonempty (S.X₁ ≅ (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V.ι).obj L) ∧
        Nonempty (S.X₂ ≅ (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V'.ι).obj L) ∧
        Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t (Φ.obj S.X₃) ∧
        ∀ q, N < q → Subsingleton (Ext (Φ.obj S.X₃) D q)) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t (Φ.obj L) ∧
      ∀ q, N < q → Subsingleton (Ext (Φ.obj L) D q) := by
  let F : W.Opens → EtaleModules.{u, 0} (ZMod ℓ) W := fun V =>
    (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V.ι).obj L
  let Q : EtaleModules.{u, 0} (ZMod ℓ) W → Prop := fun M =>
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t (Φ.obj M) ∧
      ∀ q, N < q → Subsingleton (Ext (Φ.obj M) D q)
  let P : W.Opens → Prop := fun V => Q (F V)
  have transfer : ∀ {A B : EtaleModules.{u, 0} (ZMod ℓ) W}, (A ≅ B) → Q A → Q B := fun e h =>
    ⟨Ext.isDualityPerfect_of_iso (Φ.mapIso e) h.1, fun q hq =>
      Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source (Φ.mapIso e) q (h.2 q hq)⟩
  have step : ∀ (V V' : W.Opens) (S : ShortComplex (EtaleModules.{u, 0} (ZMod ℓ) W)),
      S.ShortExact → (S.X₁ ≅ F V) → (S.X₂ ≅ F V') → P V → Q S.X₃ → P V' := by
    intro V V' S hS e₁ e₂ hV hc
    have hS' := hS.map_of_exact Φ
    have h₁ := transfer e₁.symm hV
    exact transfer e₂ ⟨Ext.isDualityPerfect_X₂ hS' h₁.1 hc.1 (hvan _)
        (hc.2 (N + 1) (Nat.lt_succ_self N)) (fun M j H φ => exists_extend_zmod H φ),
      fun q hq => Ext.subsingleton_ext_left_X₂_of_shortExact hS' D (h₁.2 q hq) (hc.2 q hq)⟩
  obtain ⟨Vm, ⟨hVm₀, hVm⟩, hmax⟩ :=
    (wellFounded_gt (α := W.Opens)).has_min {V | W₀ ≤ V ∧ P V} ⟨W₀, le_rfl, h₀⟩
  by_cases htop : Vm = ⊤
  · subst htop
    have := isIso_etaleModuleExtensionByZeroAdj_counit_app_top (ZMod ℓ) L
    exact transfer (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ)
      (⊤ : W.Opens).ι).counit.app L)) hVm
  · obtain ⟨V', hlt, S, hS, ⟨e₁⟩, ⟨e₂⟩, hc⟩ := hstrat Vm hVm₀ htop
    exact absurd hlt (hmax V' ⟨hVm₀.trans hlt.le, step Vm V' S hS e₁ e₂ hVm hc⟩)

end Stacks.EtaleCohomology
