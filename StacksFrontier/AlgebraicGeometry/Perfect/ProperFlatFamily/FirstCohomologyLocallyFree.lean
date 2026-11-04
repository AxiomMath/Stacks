module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UnitSpreading
public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing
public import StacksFrontier.Homology.Perfect.SingleDegreeFibre
public import StacksFrontier.Homology.Perfect.FibreQuasiIsoSpreading
public import StacksFrontier.Homology.ExtendScalars.Localization
public import StacksFrontier.Homology.PseudoCoherent.Local
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# The first cohomology of a proper flat family whose fibres have constant functions

Let `f : X ⟶ Spec A` be proper, flat and locally of finite presentation, and assume that every
fibre `X_p` has only constant functions, `κ(p) = H⁰(X_p, 𝒪_{X_p})`, and no cohomology of its
structure sheaf above degree one. Then `H¹(X, 𝒪_X)` is a finite locally free `A`-module.

This is the module-theoretic heart of part (b) of [Stacks, Tag 0GKA]. The source argues with
the splitting `Rf_*𝒪_X = 𝒪_S ⊕ P` of [Stacks, Tag 0E62]; here the same information is extracted
from the mapping cone `M` of the unit `A ⟶ RΓ(X, 𝒪_X)`, computed on the alternating Čech model
`D` of a finite affine cover with affine intersections:

1. `D` is a bounded complex of flat `A`-modules, perfect in `D(A)` ([Stacks, Tag 0B91]), and so is
   the cone `M`; its derived fibre at `p` is the cone of the unit of the fibre, because `D` is
   termwise flat and its formation commutes with base change ([Stacks, Tag 01XL]).
2. On the fibre the unit is an isomorphism on `H⁰` (the fibre has only constant functions), and
   the fibre has no cohomology in degrees `≥ 2`; by the long exact sequence of the cone, the
   derived fibre of `M` at `p` is concentrated in degree `1`.
3. A perfect complex whose derived fibre is concentrated in one degree is, near `p`, a finite free
   module placed in that degree ([Stacks, Tag 0BCD]). On that neighbourhood
   `H¹(D)_a = H¹(D ⊗ A_a) = H¹(M ⊗ A_a)` is finite free, the middle identification being the long
   exact sequence of the cone, since `A_a` placed in degree `0` has no `H¹` and no `H²`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.ProperFlatGlobalSections`.

* `isIso_homologyMap_zero_unitModelMap_fibre`:
  the unit of the fibre is an isomorphism on `H⁰` of the Čech model.
* `isZero_homology_extendScalarsCx_of_subsingleton`:
  vanishing cohomology of a base change is vanishing homology of the base-changed Čech model.
* `exists_away_free_homology_one`: near every
  prime, `H¹` of the Čech model becomes finite free.
* `isFiniteLocallyFree_homology_one`:
  `H¹` of the Čech model is a finite locally free `A`-module.

## References

* [Stacks Project, Tag 0GKA](https://stacks.math.columbia.edu/tag/0GKA)
* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open StacksDraft.Perfect
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The unit of a fibre with only constant functions is an isomorphism on `H⁰`.** Let `f` be
separated with a finite affine cover `U`, and let `X_p` be the fibre over a prime `p` of `A`, on
which `κ(p) ⟶ Γ(X_p, 𝒪_{X_p})` is bijective. Then the unit `A ⟶ RΓ(X, 𝒪_X)` on the Čech model,
base changed to `κ(p)`, is an isomorphism on `H⁰`. -/
theorem isIso_homologyMap_zero_unitModelMap_fibre [IsSeparated f]
    {I : Type u} [Finite I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hfib : Function.Bijective (Stacks.Cech.globalRingHom fp).hom) :
    IsIso (HomologicalComplex.homologyMap
      (extendScalarsCxMap (unitModelMap f U hU hU.le) (algebraMap A p.ResidueField)) 0) := by
  classical
  set O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : O.IsFinitePresentation := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit X
  have : O.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation O
  set D := baseAlternatingCechComplex f U hU O
  set u := unitModelMap f U hU hU.le
  set e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)
  set ψ := algebraMap A p.ResidueField
  set one : Γ(O, ⊤) := (show Γ(O, ⊤) from (1 : Γ(X, ⊤)))
  set Up : I → Xp.Opens := fun i => gp ⁻¹ᵁ U i
  set Op : Xp.Modules := (Scheme.Modules.pullback gp).obj O
  set τ := fibreTransport ψ hsq O U hU hUaff
  have hcovp : gp ⁻¹ᵁ (⊤ : X.Opens) ≤ ⨆ i, Up i :=
    le_top.trans (top_eq_iSup_preimage gp U hU).le
  let := Stacks.Cech.sectionsModule fp Op (gp ⁻¹ᵁ ⊤)
  have hle := Stacks.Cech.preimage_le_of_le U (fun _ => le_top) gp Up (Equiv.refl I)
    (preimage_eq_preimage_equivRefl gp U)
  set ι' := Stacks.Cech.sectionsToAlternatingₗ fp Up Op hle
  set pbs1 := Stacks.Cech.pullbackSections gp O ⊤ one
  have hτu : ∀ c : p.ResidueField, (τ 0).hom ((extendScalarsCxMap u ψ).f 0
      (c ⊗ₜ[A, ψ] e.inv (1 : A))) = c • ι' pbs1 := by
    intro c
    have h1 : (extendScalarsCxMap u ψ).f 0 (c ⊗ₜ[A, ψ] e.inv (1 : A)) =
        c • (show (ModuleCat.extendScalars.{u, u, u} ψ).obj (D.X 0) from
          (1 : p.ResidueField) ⊗ₜ[A, ψ] unitCochain f U hU (1 : A)) := by
      change ((ModuleCat.extendScalars.{u, u, u} ψ).map (u.f 0)).hom _ = _
      rw [ModuleCat.ExtendScalars.map_tmul, unitModelMap_f_zero_apply]
      refine Eq.trans ?_ (ModuleCat.ExtendScalars.smul_tmul ψ c 1 _).symm
      rw [mul_one]
    rw [h1, map_smul]
    congr 1
    let : Algebra A p.ResidueField := ψ.toAlgebra
    have h2 := fibreTransport_one_tmul ψ hsq O U hU hUaff 0 (unitCochain f U hU (1 : A))
    let := Stacks.Cech.sectionsModule f O ⊤
    have h3 : (baseAlternatingCechComplexXIso f U hU O 0).hom (unitCochain f U hU (1 : A)) =
        Stacks.Cech.sectionsToAlternatingₗ f U O (fun _ => le_top) one := by
      refine (Iso.inv_hom_id_apply (baseAlternatingCechComplexXIso f U hU O 0) _).trans ?_
      exact congrArg (Stacks.Cech.sectionsToAlternatingₗ f U O (fun _ => le_top))
        (one_smul A one)
    refine h2.trans ((congrArg _ h3).trans ?_)
    exact Stacks.Cech.alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ f U O
      (fun _ => le_top) gp Up (Equiv.refl I) (preimage_eq_preimage_equivRefl gp U) ψ fp
      (fun W => Stacks.Cech.baseRingHom_comp_app ψ f fp gp hsq W) one
  set eF := (Scheme.Modules.pullbackUnitIso gp).hom.app (gp ⁻¹ᵁ ⊤)
  set eF' : Γ(Op, gp ⁻¹ᵁ ⊤) → Γ(Xp, gp ⁻¹ᵁ ⊤) := fun z => eF z
  have heF0 : eF' 0 = 0 := map_zero eF.hom
  have heF1 : eF' pbs1 = (1 : Γ(Xp, (gp ⁻¹ᵁ ⊤))) :=
    (AlgebraicGeometry.SectionsEqualizer.moduleHom_app_preimage_top gp _ pbs1).trans
      (by
        have h := AlgebraicGeometry.SectionsEqualizer.pullbackUnitIso_unit gp (1 : Γ(X, ⊤))
        have h2 := AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit gp O one
        refine Eq.trans ?_ (h.trans (map_one (Scheme.Hom.appTop gp).hom))
        exact congrArg (fun z => (Scheme.Modules.pullbackUnitIso gp).hom.app ⊤ z) h2.symm)
  have hE : ∀ c : p.ResidueField,
      eF' (c • pbs1) = (Stacks.Cech.baseRingHom fp (gp ⁻¹ᵁ ⊤)).hom c :=
    fun c => (Scheme.Modules.Hom.app_smul (Scheme.Modules.pullbackUnitIso gp).hom
      ((Stacks.Cech.baseRingHom fp (gp ⁻¹ᵁ ⊤)).hom c) pbs1).trans
      ((congrArg (fun z => (Stacks.Cech.baseRingHom fp (gp ⁻¹ᵁ ⊤)).hom c * z) heF1).trans
        (mul_one _))
  have hinv : ∀ z, ((Scheme.Modules.pullbackUnitIso gp).inv.app (gp ⁻¹ᵁ ⊤)) (eF z) = z :=
    fun z => (ConcreteCategory.congr_hom (congrArg (fun t => Scheme.Modules.Hom.app t (gp ⁻¹ᵁ ⊤))
      (Iso.hom_inv_id (Scheme.Modules.pullbackUnitIso gp))) z).trans (CategoryTheory.id_apply z)
  have heF_inj : Function.Injective eF' := fun x y hxy =>
    (hinv x).symm.trans
      ((congrArg ((Scheme.Modules.pullbackUnitIso gp).inv.app (gp ⁻¹ᵁ ⊤)) hxy).trans (hinv y))
  have hbij : Function.Bijective (Stacks.Cech.baseRingHom fp (gp ⁻¹ᵁ ⊤)).hom :=
    bijective_baseRingHom_of_eq_top fp gp.preimage_top hfib
  have hF1 : ∀ c : p.ResidueField, ι' (c • pbs1) = 0 → c = 0 := by
    intro c hc
    have h0 : c • pbs1 = 0 := Stacks.Cech.sectionsToAlternatingₗ_injective fp Up Op _ hcovp
      (hc.trans (map_zero ι').symm)
    exact hbij.1 ((((hE c).symm.trans (congrArg eF' h0)).trans heF0).trans (map_zero _).symm)
  have hF2 : ∀ s' : Γ(Op, (gp ⁻¹ᵁ ⊤)), ∃ c : p.ResidueField, s' = c • pbs1 := by
    intro s'
    obtain ⟨c, hc⟩ := hbij.2 (eF' s')
    exact ⟨c, heF_inj ((hE c).trans hc).symm⟩
  have hC1 : IsZero ((baseUnitComplex A).X 1) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ 1 (by decide)
  have hsubCκ : ∀ z : (extendScalarsCx ψ (baseUnitComplex A)).X 1, z = 0 :=
    fun z => @Subsingleton.elim _ ((ModuleCat.isZero_iff_subsingleton).1
      ((ModuleCat.extendScalars.{u, u, u} ψ).map_isZero hC1)) z 0
  have hτinj : Function.Injective (τ 0).hom := fun x y hxy => by
    simpa using congrArg (τ 0).inv.hom hxy
  have h0 : ∀ x : (extendScalarsCx ψ (baseUnitComplex A)).X 0,
      (extendScalarsCxMap u ψ).f 0 x = 0 → x = 0 := fun x hx => by
    obtain ⟨c, rfl⟩ := exists_eq_tmul_of_generator ψ (e.inv (1 : A)) baseUnitComplex_gen x
    have h := hτu c
    rw [show (extendScalarsCxMap u ψ).f 0 (c ⊗ₜ[A, ψ] e.inv (1 : A)) = 0
      from hx, map_zero, ← map_smul] at h
    rw [hF1 c h.symm]
    exact TensorProduct.zero_tmul (M := (ModuleCat.restrictScalars.{u} ψ).obj
      (ModuleCat.of p.ResidueField p.ResidueField)) _
  have h0' : ∀ y : (extendScalarsCx ψ D).X 0, (extendScalarsCx ψ D).d 0 1 y = 0 →
      ∃ x : (extendScalarsCx ψ (baseUnitComplex A)).X 0,
        (extendScalarsCx ψ (baseUnitComplex A)).d 0 1 x = 0 ∧
          (extendScalarsCxMap u ψ).f 0 x = y := fun y hy => by
    have hd := fibreTransport_d_apply ψ hsq O U hU hUaff 0 y
    have hd0 : Stacks.Cech.alternatingCechModuleD fp Up Op 0 ((τ 0).hom y) = 0 := by
      refine hd.symm.trans ?_
      change (τ (0 + 1)).hom ((extendScalarsCx ψ D).d 0 1 y) = 0
      rw [show (extendScalarsCx ψ D).d 0 1 y = 0 from hy, map_zero]
    have hr := Stacks.Cech.range_sectionsToAlternatingₗ fp Up Op hle hcovp
    obtain ⟨s', hs'⟩ : (τ 0).hom y ∈ LinearMap.range ι' := hr ▸ hd0
    obtain ⟨c, rfl⟩ := hF2 s'
    refine ⟨c ⊗ₜ[A, ψ] e.inv (1 : A), hsubCκ _, hτinj ?_⟩
    rw [hτu c, ← hs', map_smul]
  have hm : Mono (HomologicalComplex.homologyMap (extendScalarsCxMap u ψ) 0) := by
    rw [HomologicalComplex.mono_homologyMap_iff_elementwise _ (-1) 0 1 (by simp) (by simp)]
    intro x _ y hy
    refine ⟨0, ?_⟩
    rw [map_zero]
    refine (h0 x (hy.trans ?_)).symm
    rw [((extendScalarsCx ψ D).isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src
      ((extendScalarsCx ψ D).d (-1) 0) 0]
    rfl
  have he : Epi (HomologicalComplex.homologyMap (extendScalarsCxMap u ψ) 0) := by
    rw [HomologicalComplex.epi_homologyMap_iff_elementwise _ (-1) 0 1 (by simp) (by simp)]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := h0' y hy
    exact ⟨x, hx, 0, by rw [map_zero, add_zero]⟩
  exact isIso_of_mono_of_epi _

/-- **Vanishing cohomology of a base change is vanishing homology of the base-changed Čech
model.** For a base change `X'` of `X` along `Spec A' ⟶ Spec A` and a quasi-coherent `F`, if
`Hʲ(X', g^* F) = 0` then the Čech model of `F`, base changed termwise to `A'`, has no homology in
degree `j`. -/
theorem isZero_homology_extendScalarsCx_of_subsingleton [IsSeparated f]
    {A' : Type u} [CommRing A'] (φ : A →+* A') {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of A')}
    {g : X' ⟶ X} (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I] [LinearOrder I]
    (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i)) (j : ℕ)
    (hvan : Subsingleton
      (((moduleGlobalSections X').rightDerived j).obj ((Scheme.Modules.pullback g).obj F))) :
    IsZero ((extendScalarsCx φ (baseAlternatingCechComplex f U hU F)).homology (j : ℤ)) := by
  have : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g F
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ (j : ℤ)).mapIso
    (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff))
  refine IsZero.of_iso ?_ (homologyBaseAlternatingCechComplexIso f' _
    (top_eq_iSup_preimage g U hU) _ (iInf_preimage_isAffineOpen φ hsq U hUaff) j)
  exact @ModuleCat.isZero_of_subsingleton _ _ _ hvan

/-- The homology of `A` placed in degree zero, base changed termwise along any ring map,
vanishes outside degree zero. -/
theorem isZero_homology_extendScalarsCx_baseUnitComplex {B : Type u} [CommRing B] (φ : A →+* B)
    (j : ℤ) (hj : j ≠ 0) : IsZero ((extendScalarsCx φ (baseUnitComplex A)).homology j) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((ModuleCat.extendScalars.{u, u, u} φ).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ j hj))

/-- **Near every prime, `H¹` of the Čech model becomes finite free.** Let `f : X ⟶ Spec A` be
proper, flat and locally of finite presentation, with a finite affine cover `U` with affine
intersections, and let `p` be a prime of `A` whose fibre `X_p` has only constant functions and no
cohomology of `𝒪` in degrees `≥ 2`. Then there is `a ∉ p` such that the localization at `a` of
`H¹` of the Čech model of `𝒪_X` is a finite free `A_a`-module. -/
theorem exists_away_free_homology_one [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    {I : Type u} [Finite I] [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hfib : Function.Bijective (Stacks.Cech.globalRingHom fp).hom)
    (hvan : ∀ j : ℕ, 2 ≤ j → Subsingleton (((moduleGlobalSections Xp).rightDerived j).obj
      ((Scheme.Modules.pullback gp).obj (SheafOfModules.unit X.ringCatSheaf)))) :
    ∃ a : A, a ∉ p ∧
      Module.Free (Localization.Away a) (LocalizedModule (Submonoid.powers a)
        ((baseAlternatingCechComplex f U hU (SheafOfModules.unit X.ringCatSheaf)).homology 1)) ∧
      Module.Finite (Localization.Away a) (LocalizedModule (Submonoid.powers a)
        ((baseAlternatingCechComplex f U hU (SheafOfModules.unit X.ringCatSheaf)).homology 1)) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  set O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : O.IsFinitePresentation := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit X
  have : O.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation O
  have hflat : IsFlatOver f.toLRSHom.toShHom O := fun x =>
    (AlgebraicGeometry.MorphismOfGerms.flat_stalkMap_iff_isFlatOverAt_unit f x).1
      (Flat.stalkMap f x)
  set D := baseAlternatingCechComplex f U hU O
  have hDperf : IsPerfect (DerivedCategory.Q.obj D) :=
    isPerfect_of_iso (alternatingCechIsoDerivedGlobalSectionsOverBase f U hU O haff)
      (isPerfect_derivedGlobalSectionsOverBase_of_isProper f O hflat)
  have hDflat : ∀ i, Module.Flat A (D.X i) := flat_baseAlternatingCechComplex_X f U hU O hUaff hflat
  have : (baseUnitComplex A).IsStrictlyLE (Fintype.card I : ℤ) :=
    CochainComplex.isStrictlyLE_of_le _ 0 _ (by omega)
  set u := unitModelMap f U hU hU.le
  set M := CochainComplex.mappingCone u
  have : D.IsStrictlyGE 0 := isStrictlyGE_baseAlternatingCechComplex f U hU O
  have : D.IsStrictlyLE (Fintype.card I : ℤ) := isStrictlyLE_baseAlternatingCechComplex f U hU O
  have := isStrictlyGE_mappingCone u 0
  have := isStrictlyLE_mappingCone u (Fintype.card I : ℤ)
  have := flat_mappingCone_X u
  have hMperf : IsPerfect (DerivedCategory.Q.obj M) :=
    isPerfect_mappingCone u (isPerfect_baseUnitComplex A) hDperf
  set ψ := algebraMap A p.ResidueField
  have h0 := isIso_homologyMap_zero_unitModelMap_fibre f U hU hUaff p hsq hfib
  have hDvan : ∀ j : ℤ, j ≠ 0 → j ≠ 1 → IsZero ((extendScalarsCx ψ D).homology j) := by
    intro j hj0 hj1
    rcases lt_or_gt_of_ne hj0 with hneg | hpos
    · exact ShortComplex.isZero_homology_of_isZero_X₂ _
        ((extendScalarsCx ψ D).isZero_of_isStrictlyGE 0 j hneg)
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m := ⟨j.toNat, (Int.toNat_of_nonneg hpos.le).symm⟩
      exact isZero_homology_extendScalarsCx_of_subsingleton f ψ hsq O U hU hUaff m
        (hvan m (by omega))
  -- the derived fibre of the cone is concentrated in degree one
  have hfibM : ∀ j : ℤ, j ≠ 1 → IsZero ((extendScalarsCx ψ M).homology j) := by
    intro j hj
    refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ j).mapIso
      (extendScalarsCxMappingConeIso u ψ))
    refine isZero_homology_mappingCone_of_epi_of_mono _ j (j + 1) rfl ?_ ?_
    · by_cases hj0 : j = 0
      · subst hj0
        infer_instance
      · exact (hDvan j hj0 hj).epi _
    · by_cases hj0 : j + 1 = 0
      · rw [hj0]
        infer_instance
      · exact (isZero_homology_extendScalarsCx_baseUnitComplex ψ (j + 1) hj0).mono _
  have hvanish : ∀ j : ℤ, j ≠ 1 →
      Module.finrank p.ResidueField (derivedFibreHomology.{u, u} p
        (DerivedCategory.Q.obj M) j) = 0 := by
    intro j hj
    obtain ⟨e⟩ := nonempty_homology_totalDerived_iso_of_flat ψ M (Fintype.card I : ℤ) j
    have := ModuleCat.subsingleton_of_isZero ((hfibM j hj).of_iso e)
    exact Module.finrank_zero_of_subsingleton
  obtain ⟨a, ha, ⟨e⟩⟩ :=
    exists_away_iso_singleFunctor_free_of_fibre_concentrated.{u, u} p
      (DerivedCategory.Q.obj M) hMperf 1 hvanish
  refine ⟨a, ha, ?_⟩
  set Aa := Localization.Away a
  set φa := algebraMap A Aa
  let := HasDerivedCategory.standard (ModuleCat.{u} Aa)
  set r := Module.finrank p.ResidueField
    (derivedFibreHomology.{u, u} p (DerivedCategory.Q.obj M) 1)
  -- `H¹` of the localized cone is free
  let e1 : (extendScalarsCx φa M).homology 1 ≅ ModuleCat.of Aa (ULift.{u} (Fin r → Aa)) :=
    (nonempty_homology_totalDerived_iso_of_flat φa M (Fintype.card I : ℤ) 1).some.symm ≪≫
      (DerivedCategory.homologyFunctor _ 1).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} Aa) 1).app _
  -- `H¹` of the localized Čech model is `H¹` of the localized cone
  let T := DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle (extendScalarsCxMap u φa))
  have hT : T ∈ distTriang _ :=
    DerivedCategory.mappingCone_triangle_distinguished (extendScalarsCxMap u φa)
  have hmono : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} Aa) 1).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT 1]
    exact ((isZero_homology_extendScalarsCx_baseUnitComplex φa 1 (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ 1).app _)).eq_of_src _ _
  have hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} Aa) 1).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT 1 2 (by omega)]
    exact ((isZero_homology_extendScalarsCx_baseUnitComplex φa 2 (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ 2).app _)).eq_of_tgt _ _
  have hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} Aa) 1).map T.mor₂) :=
    isIso_of_mono_of_epi _
  let e2 : (extendScalarsCx φa D).homology 1 ≅
      (CochainComplex.mappingCone (extendScalarsCxMap u φa)).homology 1 :=
    ((DerivedCategory.homologyFunctorFactors _ 1).app _).symm ≪≫
      @asIso _ _ _ _ ((DerivedCategory.homologyFunctor (ModuleCat.{u} Aa) 1).map T.mor₂) hiso ≪≫
      (DerivedCategory.homologyFunctorFactors _ 1).app _
  let e3 : (extendScalarsCx φa M).homology 1 ≅
      (CochainComplex.mappingCone (extendScalarsCxMap u φa)).homology 1 :=
    (HomologicalComplex.homologyFunctor _ _ 1).mapIso (extendScalarsCxMappingConeIso u φa)
  -- localization commutes with homology
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φa) :=
    StacksDraft.PseudoCoherence.preservesFiniteLimits_extendScalars_of_flat φa
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : (ModuleCat.extendScalars.{u, u, u} φa).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let e4 : (extendScalarsCx φa D).homology 1 ≅
      (ModuleCat.extendScalars.{u, u, u} φa).obj (D.homology 1) :=
    ShortComplex.mapHomologyIso (D.sc 1) (ModuleCat.extendScalars.{u, u, u} φa)
  let e5 := (extendScalars_iso_localizedModuleFunctor.{u, u} (Submonoid.powers a)).app
    (D.homology 1)
  let E : (Fin r → Aa) ≃ₗ[Aa] LocalizedModule (Submonoid.powers a) (D.homology 1) :=
    ULift.moduleEquiv.symm.trans
      ((e5.symm ≪≫ e4.symm ≪≫ e2 ≪≫ e3.symm ≪≫ e1).toLinearEquiv.symm.trans
      (Shrink.linearEquiv.{u} (Localization (Submonoid.powers a))
        (LocalizedModule (Submonoid.powers a) (D.homology 1))))
  exact ⟨Module.Free.of_equiv E, Module.Finite.equiv E⟩

/-- **`H¹` of the Čech model is finite locally free.** Let `f : X ⟶ Spec A` be proper, flat and
locally of finite presentation, with a finite affine cover `U` with affine intersections, and
assume that at every prime `p` of `A` the fibre `X_p` has only constant functions and no
cohomology of `𝒪` in degrees `≥ 2`. Then `H¹` of the Čech model of `𝒪_X` is a finite locally
free `A`-module. -/
theorem isFiniteLocallyFree_homology_one [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    {I : Type u} [Finite I] [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (hfib : ∀ (p : Ideal A) [p.IsPrime], Function.Bijective (Stacks.Cech.globalRingHom
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).hom)
    (hvan : ∀ (p : Ideal A) [p.IsPrime] (j : ℕ), 2 ≤ j → Subsingleton
      (((moduleGlobalSections
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).rightDerived
          j).obj ((Scheme.Modules.pullback
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).obj
              (SheafOfModules.unit X.ringCatSheaf)))) :
    Module.IsFiniteLocallyFree A
      ((baseAlternatingCechComplex f U hU (SheafOfModules.unit X.ringCatSheaf)).homology 1) := by
  classical
  choose a ha hfree hfin using fun m : {m : Ideal A // m.IsMaximal} =>
    haveI := m.2.isPrime
    exists_away_free_homology_one f U hU hUaff haff m.1
      (IsPullback.of_hasPullback f _) (hfib m.1) (hvan m.1)
  refine ⟨{m : Ideal A // m.IsMaximal}, a, ?_, fun m => ⟨hfree m, hfin m⟩⟩
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  exact ha ⟨m, hm⟩ (hle (Ideal.subset_span ⟨⟨m, hm⟩, rfl⟩))

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
