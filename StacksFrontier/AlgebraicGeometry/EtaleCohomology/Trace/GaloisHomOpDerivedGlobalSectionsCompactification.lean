module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpDerivedGlobalSections

/-!
# `Γ^Gal(X̄, ℋom^•_ℤ((j_! F)[0], K)) ≅ RΓ^Gal(X, ℋom_ℤ(F, ω))` for a compactification

The case of `Stacks.EtaleCohomology.galoisHomOpDerivedGlobalSectionsOverIso` for a
compactification `j : X ⟶ X̄` of a quasi-compact and quasi-separated `k`-scheme `X`.

## Main definitions

* `Stacks.EtaleCohomology.compactificationImmersionOverHom`: The open immersion `j : X ⟶ X̄` of
  a compactification, as a morphism over `Spec k`.
* `Stacks.EtaleCohomology.galoisHomOpDerivedGlobalSectionsIso`: The isomorphism
  `Γ^Gal(X̄, ℋom^•_ℤ((j_! F)[0], K)) ≅ RΓ^Gal(X, ℋom_ℤ(F, ω))` for a compactification `j`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.AbelianInternalHom
  Stacks.ConstantSheaf Stacks.Frobenius

universe w₁ w₂ w₃ w₄ u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f))

attribute [local instance] quasiCompact_overMk_hom_of_quasiCompact
  quasiSeparated_overMk_hom_of_quasiSeparated

/-- The open immersion `j : X ⟶ X̄` of a compactification, as a morphism over `Spec k`. -/
abbrev compactificationImmersionOverHom : Over.mk f ⟶ Over.mk j.toBase :=
  Over.homMk j.immersion (Over.w j.obj.hom)

/-- The underlying morphism of schemes of `compactificationImmersionOverHom j` is an open
immersion. -/
instance isOpenImmersion_compactificationImmersionOverHom :
    IsOpenImmersion (compactificationImmersionOverHom j).left :=
  inferInstanceAs (IsOpenImmersion j.immersion)

variable [QuasiCompact f] [QuasiSeparated f]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ (Over.mk f).left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λᵐᵒᵖ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange (Over.mk f) kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)]
  {n : ℕ} [NeZero n]

/-- **`Γ^Gal(X̄, ℋom^•_ℤ((j_! F)[0], K)) ≅ RΓ^Gal(X, ℋom_ℤ(F, ω))`** in the derived category of
discrete Galois `Λᵐᵒᵖ`-modules, for a compactification `j : X ⟶ X̄` of a quasi-compact and
quasi-separated `k`-scheme, a sheaf `F` of `Λ`-modules on `X` whose underlying abelian sheaf is
that of a locally constant sheaf `G'` of `ℤ/n`-modules with finitely presented values, a sheaf `ω`
of `ℤ/n`-modules on `X` locally constant on an injective module, and an injective resolution
`j_! ω ⟶ K` in sheaves of `ℤ/n`-modules on `X̄`. -/
def galoisHomOpDerivedGlobalSectionsIso (F : EtaleModules.{u, 0} Λ (Over.mk f).left)
    (G' : EtaleModules.{u, 0} (ZMod n) (Over.mk f).left) (e : toAb _ F ≅ toAb _ G')
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0}
      (Over.mk f).left.smallEtaleTopology (ZMod n) G')
    (ω : EtaleModules.{u, 0} (ZMod n) (Over.mk f).left)
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective (Over.mk f).left.smallEtaleTopology
      (ZMod n) ω)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) (Over.mk j.toBase).left) ℤ)
    [K₀.IsStrictlyGE 0] [∀ q, Injective (K₀.X q)]
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := (Over.mk f).left)
        (X := (Over.mk j.toBase).left) (compactificationImmersionOverHom j).left).obj ω) ⟶ K₀)
    [QuasiIso ι₀] :=
  galoisHomOpDerivedGlobalSectionsOverIso Λ kbar (compactificationImmersionOverHom j) F G' e hG' ω
    hω K₀ ι₀

end Stacks.EtaleCohomology

end
