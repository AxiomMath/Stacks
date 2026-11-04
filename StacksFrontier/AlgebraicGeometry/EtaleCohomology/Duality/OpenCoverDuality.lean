module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperLocallyConstantDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleOpens
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairingFiveLemma

/-!
# Gluing Poincaré duality over a finite open cover

Let `X̄` be a scheme, `D` a sheaf of `ℤ/ℓ`-modules on `X̄_étale` (the dualizing object: `ℤ/ℓ`, or
`j_{W!} ℤ/ℓ` for an open `W`), `t : Ext^N(ℤ/ℓ, D) → ℤ/ℓ` a trace and `F` a sheaf of `ℤ/ℓ`-modules
on `X̄_étale`. For an open `V` write `F_V = j_{V!} F|_V`; duality at `F_V` (for `O = ℤ/ℓ_X̄`) is
Poincaré duality on `V` with coefficients `F|_V`, `Ext^i(ℤ/ℓ, F_V) = H^i_c(V, F)` and (for
`D = ℤ/ℓ`) `Ext^j(F_V, ℤ/ℓ) = Ext^j_V(F|_V, ℤ/ℓ)`, for the trace `t` restricted along
`H^N_c(V) → H^N(X̄)`. If `H^{N+1}_c(V, F) = 0` for all `V` (for `X̄` proper of dimension `≤ d` and
`N = 2d` this is Tag 095U), duality at `F_V` for every finite intersection of members of a finite
family of opens gives duality at `F_V` for their union, and so after any exact functor `Φ` (for
coefficients supported on a stratum): the Mayer–Vietoris sequence
`Stacks.EtaleCohomology.shortExact_etaleModuleOpensShortComplex` and the gluing
`CategoryTheory.Abelian.Ext.isDualityPerfect_sup'_of_shortExact`.
## Main results

* `Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_sup'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  preservesBinaryBiproducts_of_preservesBinaryProducts

variable {ℓ : ℕ} [Fact ℓ.Prime] {X Y : Scheme.{u}} (N : ℕ) (D : EtaleModules.{u, 0} (ZMod ℓ) X)
  (t : Ext (unitSheaf (X := X) ℓ) D N →+ ZMod ℓ)
  (Φ : EtaleModules.{u, 0} (ZMod ℓ) Y ⥤ EtaleModules.{u, 0} (ZMod ℓ) X) [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (F : EtaleModules.{u, 0} (ZMod ℓ) Y)

/-- **Poincaré duality glues over a finite open cover.** Let `Φ` be an exact functor from sheaves
on `Y` to sheaves on `X̄` (the identity, or `j_! i_*` for a stratum `i : Y → W` of an open
`j : W → X̄`). If `Ext^{N+1}(ℤ/ℓ, Φ(j_{V!} F|_V)) = 0` for every open `V` of `Y`, and duality holds
at `Φ(j_{V!} F|_V)` for every finite intersection `V` of members of a finite nonempty family of
opens, it holds at `Φ(j_{V!} F|_V)` for their union. -/
theorem isDualityPerfect_extensionByZero_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (U : ι → Y.Opens)
    (hvan : ∀ V : Y.Opens, Subsingleton (Ext (unitSheaf (X := X) ℓ)
      (Φ.obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V.ι).obj F)) (N + 1)))
    (hU : ∀ K ⊆ s, ∀ hK : K.Nonempty, Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
      (Φ.obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) (K.inf' hK U).ι).obj F))) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
      (Φ.obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) (s.sup' hs U).ι).obj F)) :=
  Ext.isDualityPerfect_sup'_of_shortExact
    (fun V : Y.Opens => Φ.obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V.ι).obj F))
    (fun A B => ⟨_, (shortExact_etaleModuleOpensShortComplex (ZMod ℓ) A B F).map_of_exact Φ,
      ⟨Iso.refl _⟩, ⟨Φ.mapBiprod _ _⟩, ⟨Iso.refl _⟩⟩) hvan
    (fun _ _ H φ => exists_extend_zmod H φ) hs U hU

end Stacks.EtaleCohomology
