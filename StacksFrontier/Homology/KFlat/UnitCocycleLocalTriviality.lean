module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.CechUnitSplitting
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings

/-!
# Degree-zero cohomology and base change for a K-flat complex with a unit cocycle

Let `R` be a Noetherian ring and `C` a complex of flat `R`-modules concentrated in degrees `≥ 0`
which is K-flat, has finite cohomology modules and no cohomology in large degrees. Let `x₀` be a
degree-zero cocycle of `C`, and `𝔭` a prime of `R` such that `H⁰(C ⊗_R κ(𝔭))` is one-dimensional
and `x₀` survives in `C ⊗_R κ(𝔭)`. Then there is `h ∉ 𝔭` such that for every `R`-algebra `B` in
which `h` is invertible, the degree-zero cocycles of `C ⊗_R B` form a free `B`-module of rank one.

This is the commutative algebra of cohomology and base change in degree zero (Stacks 0CTM, 0BCD,
0A1U) for the Čech complex `C` of the structure sheaf of a proper flat family over `Spec R` with
respect to an affine étale chart, the cocycle `x₀` being the cochain of the function `1`. That
Čech complex is not bounded above, so the argument of
`Stacks.AlgebraicGeometry.ProperFlatFamilyCech.exists_away_unitSplitting` (which is stated for
the bounded alternating Čech complex of a finite cover) is run here with K-flatness in place of
boundedness: K-flat complexes compute derived extension of scalars, and extension of scalars
preserves quasi-isomorphisms between them.

## Main results

* `CochainComplex.exists_away_nonempty_ker_extendScalars_linearEquiv`: the statement above.

## Implementation notes

The minimal representative of Stacks 0BCD
(`StacksDraft.Perfect.exists_away_bounded_free_complex_representing_of_fibre_vanishing_below`)
gives `g ∉ 𝔭` and a bounded complex `P` of finite free `R_g`-modules, zero in negative degrees
and with `P⁰` free of rank `dim H⁰(C ⊗ κ(𝔭)) = 1`, quasi-isomorphic to `C ⊗ R_g`. The cocycle `x₀`
lifts to a cocycle `z ∈ P⁰ ≅ R_g`, nonzero modulo `𝔭`; inverting a numerator of `z` kills the
first differential of `P`, so over every `R_h`-algebra `B` the degree-zero cocycles of `P ⊗ B`
are `P⁰ ⊗ B ≅ B`, and those of `C ⊗ B` are the same by K-flatness.

The derived categories used in the proof are the standard models, fixed by `letI` inside the
proof; the statement involves none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CochainComplex

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections Stacks.AlgebraicGeometry.ProperFlatFamilyCech
open scoped ChangeOfRings TensorProduct Matrix

/-- **Degree-zero cohomology and base change near a point, for a K-flat complex with a unit
cocycle.** Let `C` be a K-flat complex of flat modules over a Noetherian ring `R`, concentrated in
degrees `≥ 0`, with finite cohomology vanishing in large degrees, and let `x₀` be a degree-zero
cocycle. If at a prime `𝔭` the degree-zero cohomology of `C ⊗_R κ(𝔭)` is one-dimensional and
`x₀` survives in `C ⊗_R κ(𝔭)`, there is `h ∉ 𝔭` such that for every `R`-algebra `B` in which `h`
is invertible, the degree-zero cocycles of `C ⊗_R B` form a free `B`-module of rank one. -/
theorem exists_away_nonempty_ker_extendScalars_linearEquiv {R : Type u} [CommRing R]
    [IsNoetherianRing R] (C : CochainComplex (ModuleCat.{u} R) ℤ) [C.IsStrictlyGE 0]
    [∀ n : ℤ, Module.Flat R (C.X n)] (hC : CochainComplex.KFlat.{u, u} C)
    (hfin : ∀ i : ℤ, Module.Finite R (C.homology i))
    (hbd : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (C.homology i))
    (x₀ : C.X 0) (hx₀ : (C.d 0 1).hom x₀ = 0) (p : Ideal R) [p.IsPrime]
    (hrank : Module.finrank p.ResidueField
      ((extendScalarsComplex (algebraMap R p.ResidueField) C).homology 0) = 1)
    (hne : (1 : p.ResidueField) ⊗ₜ[R, algebraMap R p.ResidueField] x₀ ≠ 0) :
    ∃ h : R, h ∉ p ∧ ∀ {B : Type u} [CommRing B] (φ : R →+* B), IsUnit (φ h) →
      Nonempty (LinearMap.ker ((extendScalarsComplex φ C).d 0 1).hom ≃ₗ[B] B) := by
  classical
  let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let κ := p.ResidueField
  let : HasDerivedCategory (ModuleCat.{u} κ) := HasDerivedCategory.standard _
  -- derived extension of scalars of `C` is computed termwise, `C` being K-flat
  have hmodelIso : ∀ {T : Type u} [CommRing T] (φ : R →+* T),
      let : HasDerivedCategory (ModuleCat.{u} T) := HasDerivedCategory.standard _
      Nonempty ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj (DerivedCategory.Q.obj C) ≅
        DerivedCategory.Q.obj (extendScalarsComplex φ C)) := fun {T} _ φ => by
    let : HasDerivedCategory (ModuleCat.{u} T) := HasDerivedCategory.standard _
    exact ⟨@asIso _ _ _ _ _
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        φ).comparison_isIso_of_kFlat C hC)⟩
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj C) := by
    refine ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology.{u, u}
      (DerivedCategory.Q.obj C) 0 R).2.1).2 ⟨?_, fun i => ?_⟩
    · obtain ⟨b, hb⟩ := hbd
      exact ⟨b, fun i hi => (hb i hi).of_iso
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app C)⟩
    · have : Module.Finite R ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
        (ComplexShape.up ℤ) i).obj C) := hfin i
      exact Module.Finite.equiv
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app C).toLinearEquiv.symm
  have hiso : ∀ i : ℤ, (DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R κ)).functor.obj (DerivedCategory.Q.obj C)) ≅
      (extendScalarsComplex (algebraMap R κ) C).homology i := fun i =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).mapIso
        (hmodelIso (algebraMap R κ)).some ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} κ) i).app _
  have hvan : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R κ)).functor.obj (DerivedCategory.Q.obj C))) := fun i hi =>
    IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap R κ)).map_isZero
        (C.isZero_of_isStrictlyGE 0 i hi))) (hiso i)
  open StacksDraft.Perfect in
  obtain ⟨g, hg, -, P, b, hPge, hPle, hPX, ⟨eP⟩⟩ :=
    exists_away_bounded_free_complex_representing_of_fibre_vanishing_below.{u, u}
      p (DerivedCategory.Q.obj C) hpc ⟨0, inferInstance⟩ 0 hvan
  let Rg := Localization.Away g
  let : HasDerivedCategory (ModuleCat.{u} Rg) := HasDerivedCategory.standard _
  let α := algebraMap R Rg
  let r := Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) 0).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R κ)).functor.obj (DerivedCategory.Q.obj C)))
  let β := Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) 1).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R κ)).functor.obj (DerivedCategory.Q.obj C)))
  have hr : r = 1 := (hiso 0).toLinearEquiv.finrank_eq.trans hrank
  have : P.IsStrictlyLE b := hPle
  have : P.IsStrictlyGE 0 := hPge
  have hproj : ∀ n, Projective (P.X n) := fun n =>
    Projective.of_iso (hPX n).some.symm
      (ModuleCat.projective_of_free (Module.Free.chooseBasis Rg _))
  have : ∀ n, Module.Flat Rg (P.X n) := fun n =>
    Module.Flat.of_linearEquiv (hPX n).some.toLinearEquiv
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨u, hu⟩ := StacksDraft.PseudoCoherence.exists_chainMap_of_isKProjective P
    (extendScalarsComplex α C) (eP.hom ≫ (hmodelIso α).some.hom)
  have : QuasiIso u := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 (by
    rw [hu]
    infer_instance)
  have hP : IsZero (P.X (-1)) := P.isZero_of_isStrictlyGE 0 (-1)
  let e₀ : P.X 0 ≅ ModuleCat.of Rg (Fin r → Rg) :=
    (hPX 0).some ≪≫ (ULift.moduleEquiv (R := Rg) (M := Fin r → Rg)).toModuleIso
  let e₁ : P.X 1 ≅ ModuleCat.of Rg (Fin β → Rg) :=
    (hPX 1).some ≪≫ (ULift.moduleEquiv (R := Rg) (M := Fin β → Rg)).toModuleIso
  let L : (Fin r → Rg) →ₗ[Rg] (Fin β → Rg) := e₁.hom.hom ∘ₗ (P.d 0 1).hom ∘ₗ e₀.inv.hom
  let M := LinearMap.toMatrix' L
  have hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv := by
    ext x
    simp [M, L]
  -- K-flatness of the localized complex
  have hCg : CochainComplex.KFlat.{u, u} (extendScalarsComplex α C) :=
    CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} α C hC
  have hPkf : CochainComplex.KFlat.{u, u} P := CochainComplex.KFlat.kFlat_of_flat P b
  -- the cocycle of `P` lifting `x₀`
  have hPd : P.d (-1) 0 = 0 := hP.eq_of_src _ _
  have hext : ∀ {S T : Type u} [CommRing S] [CommRing T] (ψ : S →+* T)
      (D : CochainComplex (ModuleCat.{u} S) ℤ), IsZero (D.X (-1)) →
      (extendScalarsComplex ψ D).d (-1) 0 = 0 := fun ψ D hD =>
    ((ModuleCat.extendScalars.{u, u, u} ψ).map_isZero hD).eq_of_src _ _
  have hC1 : IsZero (C.X (-1)) := C.isZero_of_isStrictlyGE 0 (-1) (by omega)
  have hCd : (extendScalarsComplex α C).d (-1) 0 = 0 := hext α C hC1
  let x₁ : (extendScalarsComplex α C).X 0 := (1 : Rg) ⊗ₜ[R, α] x₀
  have hx₁ : x₁ ∈ LinearMap.ker ((extendScalarsComplex α C).d 0 1).hom := by
    refine LinearMap.mem_ker.2 ?_
    show (ModuleCat.extendScalars.{u, u, u} α).map (C.d 0 1) ((1 : Rg) ⊗ₜ[R, α] x₀) = 0
    rw [ModuleCat.ExtendScalars.map_tmul, hx₀, TensorProduct.tmul_zero]
    rfl
  obtain ⟨z, hz⟩ := (bijective_kerRestrict u hPd hCd).2 ⟨_, hx₁⟩
  have hz' : u.f 0 z = x₁ := congrArg Subtype.val hz
  have hr0 : 0 < r := by omega
  let k₀ : Fin r := ⟨0, hr0⟩
  let w : Fin r → Rg := e₀.hom z
  let a : Rg := w k₀
  have hMw : M *ᵥ w = 0 := by
    have hL : L w = 0 := by
      show e₁.hom.hom ((P.d 0 1).hom (e₀.inv.hom (e₀.hom.hom z.1))) = 0
      have h0 : e₀.inv.hom (e₀.hom.hom z.1) = z.1 := by
        show (e₀.hom ≫ e₀.inv).hom z.1 = z.1
        rw [e₀.hom_inv_id]
        rfl
      rw [h0, show (P.d 0 1).hom z.1 = 0 from z.2, map_zero]
    rw [← hL]
    exact LinearMap.toMatrix'_mulVec L w
  -- the residue field and the lift of `x₀` modulo `𝔭`
  have hgκ : IsUnit (algebraMap R κ g) :=
    isUnit_iff_ne_zero.2 fun h => hg (by rwa [← Ideal.ker_algebraMap_residueField p])
  let χ : Rg →+* κ := IsLocalization.Away.lift g hgκ
  have hχ : χ.comp α = algebraMap R κ := IsLocalization.Away.lift_comp g hgκ
  have hsub : ∀ k : Fin r, k = k₀ := fun k => Fin.ext (by have := k.2; simp [k₀]; omega)
  have hχa : χ a ≠ 0 := by
    intro h0
    have key : ((1 : κ) ⊗ₜ[Rg, χ] z.1 : (ModuleCat.extendScalars.{u, u, u} χ).obj (P.X 0)) =
        0 := by
      apply (termEquiv χ e₀).injective
      refine (termEquiv_tmul χ e₀ 1 z.1).trans (Eq.trans ?_ (termEquiv χ e₀).map_zero.symm)
      funext k
      rw [hsub k]
      show χ a * 1 = 0
      rw [h0, zero_mul]
    have h2 : (ModuleCat.extendScalarsComp α χ).inv.app (C.X 0)
        ((ModuleCat.extendScalars.{u, u, u} χ).map (u.f 0) ((1 : κ) ⊗ₜ[Rg, χ] z.1)) =
        (1 : κ) ⊗ₜ[R, χ.comp α] x₀ := by
      rw [ModuleCat.ExtendScalars.map_tmul, hz']
      exact Stacks.Cech.extendScalarsComp_inv_app_one_one_tmul α χ (C.X 0) _
    have h3 : (ModuleCat.extendScalarsComp α χ).inv.app (C.X 0)
        ((ModuleCat.extendScalars.{u, u, u} χ).map (u.f 0) ((1 : κ) ⊗ₜ[Rg, χ] z.1)) = 0 := by
      rw [key]
      show ((ModuleCat.extendScalarsComp α χ).inv.app (C.X 0)).hom
        (((ModuleCat.extendScalars.{u, u, u} χ).map (u.f 0)).hom 0) = 0
      rw [LinearMap.map_zero, LinearMap.map_zero]
    exact one_tmul_ne_zero_congr hχ _ hne (h2.symm.trans h3)
  -- inverting a numerator of `a`
  obtain ⟨⟨a', ⟨_, n, rfl⟩⟩, ha'⟩ := IsLocalization.surj (Submonoid.powers g) a
  dsimp only at ha'
  have ha'p : a' ∉ p := by
    intro hmem
    have h1 : algebraMap R κ a' = 0 := by
      rwa [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
    have h2 := congrArg χ ha'
    rw [map_mul, ← RingHom.comp_apply χ α, ← RingHom.comp_apply χ α, hχ, h1, map_pow] at h2
    exact hχa ((mul_eq_zero.mp h2).resolve_right (pow_ne_zero _ hgκ.ne_zero))
  let h := g * a'
  have hh : h ∉ p := fun hm => (Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hm).elim hg ha'p
  let Rh := Localization.Away h
  let β' : Rg →+* Rh := IsLocalization.Away.awayToAwayRight g a'
  have hβ' : β'.comp α = algebraMap R Rh :=
    RingHom.ext fun x => IsLocalization.Away.awayToAwayRight_eq g a' x
  have hunitRh : IsUnit (algebraMap R Rh h) := IsLocalization.Away.algebraMap_isUnit h
  have hgh : algebraMap R Rh h = algebraMap R Rh g * algebraMap R Rh a' := map_mul _ g a'
  have hua' : IsUnit (algebraMap R Rh a') := isUnit_of_mul_isUnit_right (hgh ▸ hunitRh)
  have hβa : IsUnit (β' a) := by
    have h2 := congrArg β' ha'
    rw [map_mul, ← RingHom.comp_apply β' α, ← RingHom.comp_apply β' α, hβ', map_pow] at h2
    rw [← h2] at hua'
    exact isUnit_of_mul_isUnit_left hua'
  have hM0 : M.map β' = 0 :=
    matrix_map_eq_zero_of_mulVec hr M w hMw β' (fun k => by rw [hsub k]; exact hβa)
  refine ⟨h, hh, fun {B} _ φ hφ => ?_⟩
  let ψ : Rh →+* B := IsLocalization.Away.lift h hφ
  have hψ : ψ.comp (algebraMap R Rh) = φ := IsLocalization.Away.lift_comp h hφ
  let γ : Rg →+* B := ψ.comp β'
  have hγ : γ.comp α = φ := by rw [RingHom.comp_assoc, hβ', hψ]
  -- over `B`, the first differential of `P ⊗ B` vanishes
  let PB := extendScalarsComplex γ P
  have hd0 : PB.d 0 1 = 0 := by
    ext x
    apply (termEquiv γ e₁).injective
    refine (termEquiv_map γ e₀ e₁ (P.d 0 1) M hM x).trans ?_
    have hMγ : M.map γ = 0 := by
      have : M.map γ = (M.map β').map ψ := by
        ext i j
        rfl
      rw [this, hM0]
      ext i j
      simp
    rw [hMγ, Matrix.zero_mulVec]
    exact (termEquiv γ e₁).map_zero.symm
  -- `P ⊗ B ⟶ C ⊗ B` is a quasi-isomorphism
  let uB : PB ⟶ extendScalarsComplex γ (extendScalarsComplex α C) :=
    (CochainComplex.extendScalarsLarge.{u, u, u} γ).map u
  have : QuasiIso uB :=
    CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat γ u hPkf hCg
  have hPBd : PB.d (-1) 0 = 0 := hext γ P hP
  have hCBd : (extendScalarsComplex γ (extendScalarsComplex α C)).d (-1) 0 = 0 :=
    hext γ _ ((ModuleCat.extendScalars.{u, u, u} α).map_isZero hC1)
  have : QuasiIsoAt uB 0 := inferInstance
  have hbij := bijective_kerRestrict uB hPBd hCBd
  have htop : LinearMap.ker (PB.d 0 1).hom = ⊤ := by
    rw [hd0]
    exact LinearMap.ker_zero
  let eC : extendScalarsComplex γ (extendScalarsComplex α C) ≅ extendScalarsComplex φ C :=
    (extendScalarsComplexCompIso α γ).app C ≪≫ extendScalarsComplexCongr hγ C
  have hbijC := bijective_kerRestrict eC.hom hCBd (hext φ C hC1)
  have : Unique (Fin r) := ⟨⟨k₀⟩, hsub⟩
  exact ⟨(LinearEquiv.ofBijective _ hbijC).symm.trans ((LinearEquiv.ofBijective _ hbij).symm.trans
    ((LinearEquiv.ofTop _ htop).trans ((termEquiv γ e₀).trans
      (LinearEquiv.funUnique (Fin r) B B))))⟩

end CochainComplex

end
