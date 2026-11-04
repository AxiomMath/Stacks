module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DirectImageExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.CurveHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Boundedness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `H²_c` of `R j_* F` on a curve whose boundary complement is affine

Let `Ω` be an algebraically closed field, `g : U ⟶ Spec Ω` with a compactification
`e : U ⟶ X̄`, `ḡ : X̄ ⟶ Spec Ω`, and `j : U₀ ⟶ U` an open immersion. Suppose that the open
`V = X̄ ∖ (U ∖ U₀)` of `X̄` is an affine curve. Then for every sheaf `F` of `ℤ/N`-modules on
`U₀`,

`H²(R g_!(R j_* F)) = 0`.

By excision
(`Stacks.EtaleCohomology.nonempty_etaleModuleDerivedExtensionByZero_derivedDirectImage_iso`)
`e_!(R j_* F) ≅ R v_*(e'_! F)` for the inclusions `v : V ⟶ X̄`, `e' : U₀ ⟶ V`, so
`R g_!(R j_* F) = R ḡ_* R v_*(e'_! F) = R(ḡ ∘ v)_*(e'_! F)`, whose `H²` is `H²(V, e'_! F)`, zero
on an affine curve over an algebraically closed field (Stacks 03SC (2),
`Stacks.EtaleCohomology.isZero_rightDerived_pushforward_of_isAffineHom_of_dim_le_one`).

This is the vanishing on a geometric fibre behind the Gysin map of the Leray step of the
reduction of the weight bound of Weil II to curves
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerived_etaleModuleDirectImage_of_isAffineHom_of_dim_le_one`:
  Stacks 03SC (2) for sheaves of `ℤ/N`-modules.
* `Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_derivedDirectImage_of_isAffine`.

## Implementation notes

The statements are made in the standard model `HasDerivedCategory.standard`, in which
`Stacks.EtaleCohomology.derivedLowerShriek` is defined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- **Stacks 03SC (2) for sheaves of `ℤ/N`-modules, relative form**: `R^q h_* W = 0` for
`q ≥ 2`, `h : Y ⟶ X` affine and `Y` locally of finite type and of dimension at most one over an
algebraically closed field. The underlying abelian sheaf of `W` is killed by `N`. -/
@[sga "4 XIX 3.2" "special case"]
theorem isZero_rightDerived_etaleModuleDirectImage_of_isAffineHom_of_dim_le_one (Ω : Type u)
    [Field Ω] [IsAlgClosed Ω] {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h]
    (p : Y ⟶ Spec (.of Ω)) [LocallyOfFiniteType p] (hdim : topologicalKrullDim Y ≤ 1) (N : ℕ)
    [NeZero N] (W : EtaleModules.{u, 0} (ZMod N) Y) (q : ℕ) (hq : 2 ≤ q) :
    IsZero (((etaleModuleDirectImage.{u, 0} (ZMod N) h).rightDerived q).obj W) := by
  refine isZero_of_isZero_etaleModuleForget_obj (ZMod N) X ?_
  exact (isZero_rightDerived_pushforward_of_isAffineHom_of_dim_le_one Ω h p hdim _
    (torsionSheafProperty_etaleModuleForget_obj_of_nsmul_eq_zero (ZMod N) N (NeZero.pos N)
      (ZMod.natCast_self N) W) q hq).of_iso
    (etaleModuleForgetRightDerivedDirectImageIso (ZMod N) h W q)

/-- **`H²(R g_!(R j_* F)) = 0` when the complement in the compactification of `U ∖ U₀` is an
affine curve.** Let `jc` be a compactification `e : U ⟶ X̄` of `g : U ⟶ Spec Ω`, `i : D ⟶ X̄`
the closed complement of `U`, `v : V ⟶ X̄` an open immersion through which `i` factors, and
`U₀ = U ×_X̄ V` with `j : U₀ ⟶ U`, `e' : U₀ ⟶ V`, the image of `e'` being the complement of
`D` in `V`. If `V` is affine, locally of finite type and of dimension at most one over `Ω`,
algebraically closed, then `H²(R g_!(R j_* F)) = 0` for every sheaf `F` of `ℤ/N`-modules on
`U₀`. -/
theorem isZero_homology_two_derivedLowerShriek_derivedDirectImage_of_isAffine (Ω : Type u)
    [Field Ω] [IsAlgClosed Ω] {U U₀ V D : Scheme.{u}} (g : U ⟶ Spec (.of Ω))
    (jc : CompactificationOf (Over.mk g)) (j : U₀ ⟶ U) [IsOpenImmersion j] (i : D ⟶ jc.space)
    [IsClosedImmersion i] (hei : Set.range jc.immersion.base = (Set.range i.base)ᶜ)
    (v : V ⟶ jc.space) [IsOpenImmersion v] (c : D ⟶ V) (hc : c ≫ v = i) (e' : U₀ ⟶ V)
    [IsOpenImmersion e'] (sq : IsPullback e' j v jc.immersion)
    (hce : Set.range e'.base = (Set.range c.base)ᶜ) [IsAffine V]
    [LocallyOfFiniteType (v ≫ jc.toBase)] (hdim : topologicalKrullDim V ≤ 1) (N : ℕ) [NeZero N]
    (F : EtaleModules.{u, 0} (ZMod N) U₀) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} g jc (ZMod N)).obj
        ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  obtain ⟨ex⟩ := nonempty_etaleModuleDerivedExtensionByZero_derivedDirectImage_iso (ZMod N)
    jc.immersion i hei v c hc e' j sq hce F
  have : IsAffineHom (v ≫ jc.toBase) := isAffineHom_of_isAffine _
  have h2 := isZero_rightDerived_etaleModuleDirectImage_of_isAffineHom_of_dim_le_one Ω
    (v ≫ jc.toBase) (v ≫ jc.toBase) hdim N ((etaleModuleExtensionByZero.{u, 0} (ZMod N) e').obj F)
    2 le_rfl
  have h2' := (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (etaleModuleDirectImage.{u, 0} (ZMod N) (v ≫ jc.toBase)) (m := 2) (n := 2) rfl _).2 h2
  refine h2'.of_iso ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) jc.toBase).mapIso ex ≪≫
      (etaleModuleDerivedDirectImageComp.{u, 0} (ZMod N) v jc.toBase _ rfl).symm.app _))

end Stacks.EtaleCohomology

end
