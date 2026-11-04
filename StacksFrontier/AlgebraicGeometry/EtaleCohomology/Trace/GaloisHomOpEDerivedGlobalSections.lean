module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpDerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpComplexPrecompQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpPairing

/-!
# `Γ^Gal(Ȳ, ℋom^•_ℤ(I, res_ℤ K))` computes `RΓ^Gal(Y, ℋom_ℤ(F, ω))`

Let `i : Y ⟶ Ȳ` be an open immersion of quasi-compact and quasi-separated `k`-schemes, `F` and `ω`
as in `Stacks.EtaleCohomology.galoisHomOpDerivedGlobalSectionsOverIso`, `i_! ω ⟶ K` an injective
resolution in sheaves of `ℤ/n`-modules on `Ȳ`, `n Λ = 0`, and `I` an injective resolution of
`(i_! F)[0]`. Then the complex of discrete Galois `Λᵐᵒᵖ`-modules
`Γ^Gal(Ȳ, ℋom^•_ℤ(I, res_ℤ K))` (`Stacks.EtaleCohomology.galoisHomOpE`, the complex `E` of the
evaluation pairing) represents `RΓ^Gal(Y, ℋom_ℤ(F, ω))`: precomposition with `(i_! F)[0] ⟶ I`
is a quasi-isomorphism after `Γ^Gal`
(`Stacks.EtaleCohomology.quasiIso_galoisGlobalSections_homOpComplexPrecomp`), and
`Γ^Gal(Ȳ, ℋom^•_ℤ((i_! F)[0], K))` computes `RΓ^Gal(Y, ℋom_ℤ(F, ω))`
(`Stacks.EtaleCohomology.galoisHomOpDerivedGlobalSectionsOverIso`).

## Main definitions

* `Stacks.EtaleCohomology.galoisHomOpEDerivedGlobalSectionsOverIso`.

## Implementation notes

The complexes `(i_! F)[0]` and `res_ℤ K` enter through variables `Z` and `Kc` with equations `hZ`
and `hKc`, so that a caller can pass them in its own spelling. The local instances are those of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpDerivedGlobalSections` (see its
implementation notes).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.AbelianInternalHom
  Stacks.ConstantSheaf Stacks.Frobenius

universe w₁ w₂ w₃ w₄ u

namespace Stacks.EtaleCohomology

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance 10000] isRightCancelAdd_int_galoisHomOpDerived
  preservesZeroMorphisms_forgetAbOp_galoisHomOpDerived
  preservesZeroMorphisms_forgetAbZMod_galoisHomOpDerived
  preservesZeroMorphisms_forgetAbZModBar_galoisHomOpDerived
  preservesZeroMorphisms_homOp_galoisHomOpDerived preservesZeroMorphisms_homAb_galoisHomOpDerived
  preservesZeroMorphisms_restriction_galoisHomOpDerived
  preservesZeroMorphisms_etaleRestriction_galoisHomOpDerived
  preservesZeroMorphisms_galoisGlobalSections_galoisHomOpDerived
  additive_galoisGlobalSections_galoisHomOpDerived enoughInjectives_galoisHomOpDerived
  hasZeroObject_zmod_galoisHomOpDerived hasZeroObject_zmodBar_galoisHomOpDerived
  hasZeroObject_op_galoisHomOpDerived hasZeroObject_ab_galoisHomOpDerived etale_galoisHomOpDerived
  preservesZeroMorphisms_galoisGlobalSectionsBar_galoisHomOpDerived
  hasZeroObject_bar_galoisHomOpDerived hasZeroObject_abBar_galoisHomOpDerived
  hasZeroObject_opBar_galoisHomOpDerived

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb) [IsOpenImmersion i.left]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]

/-- Restriction of scalars `ℤ ⟶ ℤ/n` preserves zero morphisms (see the implementation notes). -/
local instance (priority := 10000) preservesZeroMorphisms_restrictScalarsInt_galoisHomOpE {n : ℕ} :
    (etaleModuleRestrictScalars (Int.castRingHom (ZMod n)) Yb.left).PreservesZeroMorphisms :=
  inferInstance

/-- `galoisHomOpE`, with the shape and instances of this file. -/
def galoisHomOpEIso [CompactSpace (kbar ≃ₐ[k] kbar)] [Finite Λ]
    (L : CochainComplex (EtaleModules.{u, 0} Λ Yb.left) ℤ)
    (Kc : CochainComplex (EtaleModules.{u, 0} ℤ Yb.left) ℤ) :
    galoisHomOpE Yb kbar L Kc ≅
      ((galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (homOpComplex Yb.left.smallEtaleTopology L (etaleHomOpTarget Yb Kc)) :=
  Iso.refl _

omit [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom] in
/-- The complex of abelian sheaves underlying `res_ℤ K` is that underlying `K`. -/
theorem etaleHomOpTarget_eq_of_restrictScalarsInt {n : ℕ}
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ)
    (Kc : CochainComplex (EtaleModules.{u, 0} ℤ Yb.left) ℤ)
    (hKc : Kc = ((etaleModuleRestrictScalars (Int.castRingHom (ZMod n))
      Yb.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) :
    etaleHomOpTarget Yb Kc =
      ((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₀ := by
  subst hKc
  rfl

/-- Precomposition with a quasi-isomorphism is a quasi-isomorphism after `Γ^Gal(Ȳ, -)`, for the
complex of abelian sheaves underlying a bounded below complex of injective sheaves of
`ℤ/n`-modules, `n Λ = 0`
(`Stacks.EtaleCohomology.quasiIso_galoisGlobalSections_homOpComplexPrecomp`). -/
theorem quasiIso_galoisGlobalSections_homOpComplexPrecomp_forgetAb {n : ℕ}
    (hn : (n : Λ) = 0) {L L' : CochainComplex (EtaleModules.{u, 0} Λ Yb.left) ℤ} (g : L' ⟶ L)
    [QuasiIso g] (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [K₀.IsStrictlyGE 0]
    [∀ q, Injective (K₀.X q)] :
    QuasiIso (((galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (homOpComplexPrecomp
        (M := ((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀) g)) :=
  quasiIso_galoisGlobalSections_homOpComplexPrecomp Λ hn kbar Yb g K₀ 0

section Derived

variable [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λᵐᵒᵖ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange Y kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)]
  [CompactSpace (kbar ≃ₐ[k] kbar)] [Finite Λ] {n : ℕ} [NeZero n]

/-- **`Γ^Gal(Ȳ, ℋom^•_ℤ(I, res_ℤ K)) ≅ RΓ^Gal(Y, ℋom_ℤ(F, ω))`** in the derived category of
discrete Galois `Λᵐᵒᵖ`-modules, for an injective resolution `I` of `(i_! F)[0]`, an injective
resolution `i_! ω ⟶ K` in sheaves of `ℤ/n`-modules on `Ȳ`, and `n Λ = 0`. -/
def galoisHomOpEDerivedGlobalSectionsOverIso (F : EtaleModules.{u, 0} Λ Y.left)
    (G' : EtaleModules.{u, 0} (ZMod n) Y.left) (e : toAb _ F ≅ toAb _ G')
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G')
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective Y.left.smallEtaleTopology (ZMod n) ω)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [K₀.IsStrictlyGE 0]
    [∀ q, Injective (K₀.X q)]
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) [hι₀ : QuasiIso ι₀] (hn : (n : Λ) = 0)
    {Z : CochainComplex (EtaleModules.{u, 0} Λ Yb.left) ℤ}
    (hZ : Z = (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F))
    (I : CochainComplex.InjectiveResolution Z)
    (Kc : CochainComplex (EtaleModules.{u, 0} ℤ Yb.left) ℤ)
    (hKc : Kc = ((etaleModuleRestrictScalars (Int.castRingHom (ZMod n))
      Yb.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) :
    DerivedCategory.Q.obj (galoisHomOpE Yb kbar I.cocomplex Kc) ≅
      DerivedCategory.Plus.ι.obj ((galoisDerivedGlobalSections Λᵐᵒᵖ Y kbar).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (homOpSheaf Y.left.smallEtaleTopology F (toAb _ ω)))) :=
  haveI := quasiIso_galoisGlobalSections_homOpComplexPrecomp_forgetAb Λ kbar hn I.ι K₀
  DerivedCategory.Q.mapIso (galoisHomOpEIso Λ kbar I.cocomplex Kc ≪≫
      ((galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (eqToIso (congrArg (homOpComplex Yb.left.smallEtaleTopology I.cocomplex)
          (etaleHomOpTarget_eq_of_restrictScalarsInt K₀ Kc hKc)))) ≪≫
    asIso (DerivedCategory.Q.map
      (((galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (homOpComplexPrecomp
          (M := ((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K₀) I.ι))) ≪≫
    DerivedCategory.Q.mapIso
      (((galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (eqToIso (congrArg (fun L => homOpComplex Yb.left.smallEtaleTopology L
          (((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K₀)) hZ))) ≪≫
    galoisHomOpDerivedGlobalSectionsOverIso Λ kbar i F G' e hG' ω hω K₀ ι₀

end Derived

end Stacks.EtaleCohomology

end
