module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairingFiveLemma
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyConstantDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle

/-!
# Duality on an open and on its closed complement

Let `i : Z → W` be a closed immersion and `w : U → W` the open immersion of the complement, `L` a
sheaf of `ℤ/ℓ`-modules on `W`, and `Φ` an exact functor from sheaves on `W` to sheaves on `X̄`: for
an open `j : W → X̄` it is `j_!`, for a closed `W` of an open `j : W' → X̄` it is
`j_! ∘ (W → W')_*` (coefficients supported on `W`). The image under `Φ` of the short exact sequence
of Tag 095L on `W`,

`0 → Φ(w_! w⁻¹ L) → Φ(L) → Φ(i_* i⁻¹ L) → 0`,

relates duality on `X̄` (for `O = ℤ/ℓ_X̄`, any dualizing object `D` and trace `t`) at its three
terms: duality on the open `U` and on the sheaves supported on the boundary `Z` gives duality on
`W` (`isDualityPerfect_extensionByZero_of_open_of_closed`), and conversely duality on `W` and on
`Z` gives duality on `U` (`isDualityPerfect_extensionByZero_open_of_closed`). The vanishing of
`Ext^q(Φ(L), D)` in high degrees passes along the same sequence
(`subsingleton_ext_extensionByZero_of_open_of_closed`).

## Main results

* `CategoryTheory.Abelian.Ext.subsingleton_ext_left_X₂_of_shortExact`.
* `Stacks.EtaleCohomology.shortExact_extensionByZero_openClosed`.
* `Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_of_open_of_closed`.
* `Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_open_of_closed`.
* `Stacks.EtaleCohomology.subsingleton_ext_extensionByZero_of_open_of_closed`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- If `Ext^n(X₁, Y)` and `Ext^n(X₃, Y)` vanish for a short exact sequence `0 → X₁ → X₂ → X₃ → 0`,
so does `Ext^n(X₂, Y)`. -/
theorem subsingleton_ext_left_X₂_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    {n : ℕ} (h₁ : Subsingleton (Ext S.X₁ Y n)) (h₃ : Subsingleton (Ext S.X₃ Y n)) :
    Subsingleton (Ext S.X₂ Y n) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : Ext S.X₂ Y n, x = 0 := fun x => by
    obtain ⟨x₃, hx₃⟩ := contravariant_sequence_exact₂ hS Y x (Subsingleton.elim _ _)
    rw [← hx₃, Subsingleton.elim x₃ 0, comp_zero]
  rw [key a, key b]

end CategoryTheory.Abelian.Ext

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime] {Z U W X : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
  (w : U ⟶ W) [IsOpenImmersion w] (hiw : Set.range w.base = (Set.range i.base)ᶜ)
  (Φ : EtaleModules.{u, 0} (ZMod ℓ) W ⥤ EtaleModules.{u, 0} (ZMod ℓ) X) [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (L : EtaleModules.{u, 0} (ZMod ℓ) W)

include hiw

/-- The short exact sequence `0 → Φ(w_! w⁻¹ L) → Φ(L) → Φ(i_* i⁻¹ L) → 0`: Tag 095L on `W`,
under the exact functor `Φ`. -/
theorem shortExact_extensionByZero_openClosed :
    ∃ S : ShortComplex (EtaleModules.{u, 0} (ZMod ℓ) X), S.ShortExact ∧
      S.X₁ = Φ.obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) w).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) w).obj L)) ∧
      S.X₂ = Φ.obj L ∧
      S.X₃ = Φ.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj L)) := by
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage (ZMod ℓ) i w hiw L
  exact ⟨_, hS.map_of_exact Φ, rfl, rfl, rfl⟩

variable (D : EtaleModules.{u, 0} (ZMod ℓ) X) {N : ℕ} (t : Ext (unitSheaf (X := X) ℓ) D N →+ ZMod ℓ)

/-- **Duality on `W` from duality on an open `U` and on the closed complement `Z`.** If duality
holds at `Φ(w_! w⁻¹ L)` and at `Φ(i_* i⁻¹ L)`, `Ext^{N+1}(ℤ/ℓ, Φ(w_! w⁻¹ L)) = 0` (compactly
supported cohomology of `U` above the top degree) and `Ext^{N+1}(Φ(i_* i⁻¹ L), D) = 0`, then
duality holds at `Φ(L)`. -/
theorem isDualityPerfect_extensionByZero_of_open_of_closed
    (hU : Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
      (Φ.obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) w).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) w).obj L))))
    (hZ : Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
      (Φ.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj L))))
    (hvU : Subsingleton (Ext (unitSheaf (X := X) ℓ)
      (Φ.obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) w).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) w).obj L))) (N + 1)))
    (hvZ : Subsingleton (Ext (Φ.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj L))) D (N + 1))) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
      (Φ.obj L) := by
  obtain ⟨_, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage (ZMod ℓ) i w hiw L
  exact Ext.isDualityPerfect_X₂ (hS.map_of_exact Φ) hU hZ hvU hvZ
    (fun M j H φ => exists_extend_zmod H φ)

/-- **Duality on an open `U` from duality on `W` and on the closed complement `Z`.** If duality
holds at `Φ(L)` and at `Φ(i_* i⁻¹ L)` and `Ext^{N+1}(Φ(i_* i⁻¹ L), D) = 0`, then duality holds
at `Φ(w_! w⁻¹ L)`. -/
theorem isDualityPerfect_extensionByZero_open_of_closed
    (hW : Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
      (Φ.obj L))
    (hZ : Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
      (Φ.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj L))))
    (hvZ : Subsingleton (Ext (Φ.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj L))) D (N + 1))) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
      (Φ.obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) w).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) w).obj L))) := by
  obtain ⟨_, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage (ZMod ℓ) i w hiw L
  exact Ext.isDualityPerfect_X₁ (hS.map_of_exact Φ) hW hZ hvZ
    (fun M j H φ => exists_extend_zmod H φ)

/-- **Vanishing of `Ext^q(Φ(L), D)` from the open and the closed pieces**: the
cohomological-dimension clause passes along `0 → Φ(w_! w⁻¹ L) → Φ(L) → Φ(i_* i⁻¹ L) → 0`. -/
theorem subsingleton_ext_extensionByZero_of_open_of_closed {q : ℕ}
    (hvU : Subsingleton (Ext (Φ.obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) w).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) w).obj L))) D q))
    (hvZ : Subsingleton (Ext (Φ.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj L))) D q)) :
    Subsingleton (Ext (Φ.obj L) D q) := by
  obtain ⟨_, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage (ZMod ℓ) i w hiw L
  exact Ext.subsingleton_ext_left_X₂_of_shortExact (hS.map_of_exact Φ) D hvU hvZ

end Stacks.EtaleCohomology
