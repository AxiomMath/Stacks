module

public import StacksFrontier.Homology.Perfect.MinimalModelDegreeZero
public import StacksFrontier.Homology.Perfect.BaseChange
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.RingTheory.Flat.Prod

/-!
# Lifting degree-zero cocycles from a fibre, for perfect complexes

Let `A` be a commutative ring, `𝔭` a prime with residue field `κ(𝔭)`, and `Φ : C ⟶ D` a map of
bounded above complexes of flat `A`-modules with perfect images in `D(A)` and with `D⁻¹ = 0`.
`StacksDraft.ConeLift.exists_cocycle_lift_of_isPerfect` says: if `H⁰(Φ ⊗ κ(𝔭))` and
`H¹(Φ ⊗ κ(𝔭))` are injective and every degree-zero cocycle of `D ⊗ κ(𝔭)` lifts to a degree-zero
cocycle of `D`, then every degree-zero cocycle `x` of `C ⊗ κ(𝔭)` lifts, up to a unit, to a
degree-zero cocycle `c` of `C`: `1 ⊗ c = s • x` for some `s ∉ 𝔭`.

This is the form of the argument of [Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
that the theorem of the cube consumes. The proof localizes at `𝔭`, where the mapping cone of `Φ`
has a model minimal in degree zero (`StacksDraft.MinimalModel.exists_minimal_model`, built on
[Stacks, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)), applies
`StacksDraft.ConeLift.exists_cocycle_lift` over the local ring `A_𝔭`, and clears denominators.
The hypotheses at `κ(𝔭)` are transported to the local ring through the composition isomorphism
of extension of scalars `A → A_𝔭 → κ(𝔭)`.

## Main results

* `StacksDraft.ConeLift.exists_cocycle_lift_of_isPerfect`: the statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open StacksDraft.Perfect (IsPerfect)

universe u

namespace StacksDraft.ConeLift

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- In degree `i` the mapping cone is `C^{i+1} ⊕ D^i`, through its two inclusions and two
projections. -/
noncomputable def coneXEquiv {R : Type u} [CommRing R] {C D : CochainComplex (ModuleCat.{u} R) ℤ}
    (Φ : C ⟶ D) (i : ℤ) : (CochainComplex.mappingCone Φ).X i ≃ₗ[R] C.X (i + 1) × D.X i := by
  let fst := (CochainComplex.mappingCone.fst Φ).1.v i (i + 1) rfl
  let snd := (CochainComplex.mappingCone.snd Φ).v i i (add_zero i)
  let inl := (CochainComplex.mappingCone.inl Φ).v (i + 1) i (by omega)
  let inr := (CochainComplex.mappingCone.inr Φ).f i
  have h1 : fst ≫ inl + snd ≫ inr = 𝟙 _ := CochainComplex.mappingCone.id_X Φ i (i + 1) rfl
  have h2 : inl ≫ fst = 𝟙 _ := CochainComplex.mappingCone.inl_v_fst_v Φ (i + 1) i rfl
  have h3 : inr ≫ snd = 𝟙 _ := CochainComplex.mappingCone.inr_f_snd_v Φ i
  have h4 : inl ≫ snd = 0 := CochainComplex.mappingCone.inl_v_snd_v Φ (i + 1) i (by omega)
  have h5 : inr ≫ fst = 0 := CochainComplex.mappingCone.inr_f_fst_v Φ i (i + 1) rfl
  exact
    { toFun := fun x => (fst.hom x, snd.hom x)
      invFun := fun y => inl.hom y.1 + inr.hom y.2
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp
      left_inv := fun x => by simpa using congrArg (fun m => m.hom x) h1
      right_inv := fun y => by
        have a := congrArg (fun m => m.hom y.1) h2
        have b := congrArg (fun m => m.hom y.2) h3
        have c := congrArg (fun m => m.hom y.1) h4
        have d := congrArg (fun m => m.hom y.2) h5
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
          LinearMap.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at a b c d
        ext <;> simp [a, b, c, d] }

/-- The terms of a mapping cone of complexes of flat modules are flat. -/
theorem flat_mappingCone_X {R : Type u} [CommRing R] {C D : CochainComplex (ModuleCat.{u} R) ℤ}
    (Φ : C ⟶ D) [∀ i, Module.Flat R (C.X i)] [∀ i, Module.Flat R (D.X i)] (i : ℤ) :
    Module.Flat R ((CochainComplex.mappingCone Φ).X i) :=
  have : Module.Flat R (C.X (i + 1) × D.X i) := Module.Flat.prod
  Module.Flat.of_linearEquiv (coneXEquiv Φ i)

/-- A mapping cone of complexes vanishing above `b` vanishes above `b`. -/
theorem isStrictlyLE_mappingCone {R : Type u} [CommRing R]
    {C D : CochainComplex (ModuleCat.{u} R) ℤ} (Φ : C ⟶ D) (b : ℤ) [C.IsStrictlyLE b]
    [D.IsStrictlyLE b] : (CochainComplex.mappingCone Φ).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have h1 := ModuleCat.subsingleton_of_isZero (C.isZero_of_isStrictlyLE b (i + 1) (by omega))
  have h2 := ModuleCat.subsingleton_of_isZero (D.isZero_of_isStrictlyLE b i hi)
  exact @ModuleCat.isZero_of_subsingleton _ _ _ (coneXEquiv Φ i).toEquiv.subsingleton

/-- Extension of scalars carries a flat module to a flat module. -/
theorem flat_extendScalars_obj {B : Type u} [CommRing B] [Algebra A B] (N : ModuleCat.{u} A)
    [Module.Flat A N] :
    Module.Flat B ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).obj N) := by
  have : Module.Flat B (TensorProduct A B N) := Module.Flat.baseChange A B N
  exact Module.Flat.of_linearEquiv
    (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv A B N)

/-- Extension of scalars of a complex of flat modules with perfect image has perfect image. -/
theorem isPerfect_extendScalars {B : Type u} [CommRing B] (ψ : A →+* B)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) [M.IsStrictlyLE b]
    [∀ i, Module.Flat A (M.X i)] (hM : IsPerfect (DerivedCategory.Q.obj M)) :
    IsPerfect (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) := by
  have h := StacksDraft.Perfect.isPerfect_derivedExtensionScalars.{u, u, u} ψ _ hM
  let Dψ := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} ψ
  have hc : IsIso (Dψ.comparison.app M) :=
    CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.comparison_isIso_of_flat
      Dψ M b
  exact StacksDraft.Perfect.isPerfect_of_iso (asIso (Dψ.comparison.app M)).symm h

/-- **Lifting a degree-zero cocycle of the closed fibre, over a local ring.** -/
theorem exists_cocycle_lift_local {R : Type u} [CommRing R] [IsLocalRing R]
    {C D : CochainComplex (ModuleCat.{u} R) ℤ} (Φ : C ⟶ D) (b : ℤ) [C.IsStrictlyLE b]
    [D.IsStrictlyLE b] [∀ i, Module.Flat R (C.X i)] [∀ i, Module.Flat R (D.X i)]
    (hD : IsZero (D.X (-1))) (hCp : IsPerfect (DerivedCategory.Q.obj C))
    (hDp : IsPerfect (DerivedCategory.Q.obj D))
    (h0 : ∀ x : bcObj (IsLocalRing.residue R) (C.X 0),
      (bcMap (IsLocalRing.residue R) (C.d 0 1)).hom x = 0 →
      (bcMap (IsLocalRing.residue R) (Φ.f 0)).hom x = 0 → x = 0)
    (h1 : ∀ c : bcObj (IsLocalRing.residue R) (C.X 1),
      (bcMap (IsLocalRing.residue R) (C.d 1 2)).hom c = 0 →
      ∀ e : bcObj (IsLocalRing.residue R) (D.X 0),
      (bcMap (IsLocalRing.residue R) (Φ.f 1)).hom c =
        (bcMap (IsLocalRing.residue R) (D.d 0 1)).hom e →
        ∃ c' : bcObj (IsLocalRing.residue R) (C.X 0),
          (bcMap (IsLocalRing.residue R) (C.d 0 1)).hom c' = c)
    (hsurj : ∀ y : bcObj (IsLocalRing.residue R) (D.X 0),
      (bcMap (IsLocalRing.residue R) (D.d 0 1)).hom y = 0 →
      ∃ y' : D.X 0, (D.d 0 1).hom y' = 0 ∧ (bcUnit (IsLocalRing.residue R) _).hom y' = y)
    (x : bcObj (IsLocalRing.residue R) (C.X 0))
    (hx : (bcMap (IsLocalRing.residue R) (C.d 0 1)).hom x = 0) :
    ∃ c : C.X 0, (C.d 0 1).hom c = 0 ∧ (bcUnit (IsLocalRing.residue R) _).hom c = x := by
  let res := IsLocalRing.residue R
  have : ∀ i, Module.Flat R ((CochainComplex.mappingCone Φ).X i) := flat_mappingCone_X Φ
  have := isStrictlyLE_mappingCone Φ b
  have hKp : IsPerfect (DerivedCategory.Q.obj (CochainComplex.mappingCone Φ)) :=
    (StacksDraft.Perfect.isPerfect_of_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished Φ)).1 hCp hDp
  have hKpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
      (DerivedCategory.Q.obj (CochainComplex.mappingCone Φ)) :=
    ((StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u} _).1.mp
      hKp).1
  have hneg : IsZero ((((ModuleCat.extendScalars.{u, u, u} res).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone Φ)).homology (-1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    have key : ∀ z : bcObj res ((CochainComplex.mappingCone Φ).X (-1)),
        (bcMap res ((CochainComplex.mappingCone Φ).d (-1) 0)).hom z = 0 → z = 0 := by
      intro z hz
      have hsndm : (CochainComplex.mappingCone.snd Φ).v (-1) (-1) (add_zero _) = 0 :=
        hD.eq_of_tgt _ _
      have F8 : (CochainComplex.mappingCone.fst Φ).1.v (-1) 0 (by omega) ≫
          (CochainComplex.mappingCone.inl Φ).v 0 (-1) (by omega) = 𝟙 _ := by
        have h := CochainComplex.mappingCone.id_X Φ (-1) 0 (by omega)
        rwa [hsndm, zero_comp, add_zero] at h
      have F3 := CochainComplex.mappingCone.d_fst_v Φ (-1) 0 1 (by omega) (by omega)
      have F4 := CochainComplex.mappingCone.d_snd_v Φ (-1) 0 (by omega)
      rw [hsndm, zero_comp, add_zero] at F4
      have hdz : (bcMap res (C.d 0 1)).hom ((bcMap res
          ((CochainComplex.mappingCone.fst Φ).1.v (-1) 0 (by omega))).hom z) = 0 := by
        have := congrArg (fun t => (bcMap res ((CochainComplex.mappingCone.fst Φ).1.v 0 1
          (by omega))).hom t) hz
        simp only [map_zero] at this
        rw [bcMap_apply_bcMap, F3, bcMap_neg, ModuleCat.hom_neg, LinearMap.neg_apply,
          neg_eq_zero] at this
        rwa [bcMap_apply_bcMap]
      have hΦz : (bcMap res (Φ.f 0)).hom ((bcMap res
          ((CochainComplex.mappingCone.fst Φ).1.v (-1) 0 (by omega))).hom z) = 0 := by
        have := congrArg (fun t => (bcMap res ((CochainComplex.mappingCone.snd Φ).v 0 0
          (add_zero _))).hom t) hz
        simp only [map_zero] at this
        rw [bcMap_apply_bcMap, F4] at this
        rwa [bcMap_apply_bcMap]
      have h0z := h0 _ hdz hΦz
      have := congrArg (fun m => (bcMap res m).hom z) F8
      rw [bcMap_id] at this
      change _ = z at this
      rw [← this, ← bcMap_apply_bcMap, h0z, map_zero]
    intro z hz
    exact ⟨0, by rw [map_zero]; exact (key z hz).symm⟩
  obtain ⟨P, u, hu, -, hP0free, hP0fin, hmin₁, hmin₂⟩ :=
    StacksDraft.MinimalModel.exists_minimal_model (CochainComplex.mappingCone Φ) b hKpc hneg
  exact exists_cocycle_lift res Φ hD P u hmin₁ hmin₂ h0 h1 hsurj x hx

/-- **Lifting a degree-zero cocycle of a fibre, for perfect complexes.** See the module
documentation: a degree-zero cocycle `x` of `C ⊗ κ(𝔭)` lifts, up to a scalar `s ∉ 𝔭`, to a
degree-zero cocycle of `C`. -/
theorem exists_cocycle_lift_of_isPerfect (𝔭 : Ideal A) [𝔭.IsPrime]
    {C D : CochainComplex (ModuleCat.{u} A) ℤ} (Φ : C ⟶ D) (b : ℤ) [C.IsStrictlyLE b]
    [D.IsStrictlyLE b] [∀ i, Module.Flat A (C.X i)] [∀ i, Module.Flat A (D.X i)]
    (hD : IsZero (D.X (-1))) (hCp : IsPerfect (DerivedCategory.Q.obj C))
    (hDp : IsPerfect (DerivedCategory.Q.obj D))
    (h0 : ∀ x : bcObj (algebraMap A 𝔭.ResidueField) (C.X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) (C.d 0 1)).hom x = 0 →
      (bcMap (algebraMap A 𝔭.ResidueField) (Φ.f 0)).hom x = 0 → x = 0)
    (h1 : ∀ c : bcObj (algebraMap A 𝔭.ResidueField) (C.X 1),
      (bcMap (algebraMap A 𝔭.ResidueField) (C.d 1 2)).hom c = 0 →
      ∀ e : bcObj (algebraMap A 𝔭.ResidueField) (D.X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) (Φ.f 1)).hom c =
        (bcMap (algebraMap A 𝔭.ResidueField) (D.d 0 1)).hom e →
        ∃ c' : bcObj (algebraMap A 𝔭.ResidueField) (C.X 0),
          (bcMap (algebraMap A 𝔭.ResidueField) (C.d 0 1)).hom c' = c)
    (hsurj : ∀ y : bcObj (algebraMap A 𝔭.ResidueField) (D.X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) (D.d 0 1)).hom y = 0 →
      ∃ y' : D.X 0, (D.d 0 1).hom y' = 0 ∧ ∃ t : A, t ∉ 𝔭 ∧
        (bcUnit (algebraMap A 𝔭.ResidueField) _).hom y' = t • y)
    (x : bcObj (algebraMap A 𝔭.ResidueField) (C.X 0))
    (hx : (bcMap (algebraMap A 𝔭.ResidueField) (C.d 0 1)).hom x = 0) :
    ∃ c : C.X 0, (C.d 0 1).hom c = 0 ∧ ∃ s : A, s ∉ 𝔭 ∧
      (bcUnit (algebraMap A 𝔭.ResidueField) _).hom c = s • x := by
  classical
  let A' := Localization.AtPrime 𝔭
  let ψ : A →+* A' := algebraMap A A'
  let res : A' →+* 𝔭.ResidueField := IsLocalRing.residue A'
  let ρ := algebraMap A 𝔭.ResidueField
  let G := ModuleCat.extendScalars.{u, u, u} ψ
  have : G.Additive := extendScalars_additive ψ
  let E : ModuleCat.extendScalars.{u, u, u} ρ ≅ G ⋙ ModuleCat.extendScalars.{u, u, u} res :=
    ModuleCat.extendScalarsComp ψ res
  let eh : ∀ M : ModuleCat.{u} A, bcObj ρ M →+ bcObj res (G.obj M) := fun M =>
    (E.hom.app M).hom.toAddMonoidHom
  let ei : ∀ M : ModuleCat.{u} A, bcObj res (G.obj M) →+ bcObj ρ M := fun M =>
    (E.inv.app M).hom.toAddMonoidHom
  have Ehi : ∀ (M : ModuleCat.{u} A) (t : bcObj res (G.obj M)), eh M (ei M t) = t := fun M t =>
    congrArg (fun m => m.hom t) (E.inv_hom_id_app M)
  have Eih : ∀ (M : ModuleCat.{u} A) (t : bcObj ρ M), ei M (eh M t) = t := fun M t =>
    congrArg (fun m => m.hom t) (E.hom_inv_id_app M)
  have Einat : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N) (t : bcObj res (G.obj M)),
      ei N ((bcMap res (G.map f)).hom t) = (bcMap ρ f).hom (ei M t) := fun f t =>
    congrArg (fun m => m.hom t) (E.inv.naturality f)
  have Ez : ∀ {M N : ModuleCat.{u} A} {f : M ⟶ N} {t : bcObj res (G.obj M)},
      (bcMap res (G.map f)).hom t = 0 → (bcMap ρ f).hom (ei M t) = 0 := fun h => by
    rw [← Einat, h, map_zero]
  have Ehnat : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N) (t : bcObj ρ M),
      eh N ((bcMap ρ f).hom t) = (bcMap res (G.map f)).hom (eh M t) := fun f t =>
    congrArg (fun m => m.hom t) (E.hom.naturality f)
  have Eunit : ∀ (M : ModuleCat.{u} A) (m : M),
      eh M ((bcUnit ρ M).hom m) = (bcUnit res (G.obj M)).hom ((bcUnit ψ M).hom m) :=
    fun M m => ModuleCat.extendScalarsComp_hom_app_one_tmul ψ res M m
  have Esmul : ∀ (M : ModuleCat.{u} A) (a : A) (t : bcObj ρ M),
      eh M (a • t) = ψ a • eh M t := fun M a t =>
    (E.hom.app M).hom.map_smul (ρ a) t
  let C' := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  let D' := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj D
  let Φ' : C' ⟶ D' := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map Φ
  have hD' : IsZero (D'.X (-1)) := G.map_isZero hD
  have h0' : ∀ x : bcObj res (C'.X 0), (bcMap res (C'.d 0 1)).hom x = 0 →
      (bcMap res (Φ'.f 0)).hom x = 0 → x = 0 := by
    intro x hx1 hx2
    have := h0 (ei _ x) (Ez hx1) (Ez hx2)
    rw [← Ehi _ x, this, map_zero]
  have h1' : ∀ c : bcObj res (C'.X 1), (bcMap res (C'.d 1 2)).hom c = 0 →
      ∀ e : bcObj res (D'.X 0), (bcMap res (Φ'.f 1)).hom c = (bcMap res (D'.d 0 1)).hom e →
        ∃ c' : bcObj res (C'.X 0), (bcMap res (C'.d 0 1)).hom c' = c := by
    intro c hc e he
    change (bcMap res (G.map (Φ.f 1))).hom c = (bcMap res (G.map (D.d 0 1))).hom e at he
    obtain ⟨c', hc'⟩ := h1 (ei _ c) (Ez hc) (ei _ e)
      (by rw [← Einat, ← Einat, he])
    refine ⟨eh _ c', ?_⟩
    change (bcMap res (G.map (C.d 0 1))).hom (eh _ c') = c
    rw [← Ehnat, hc', Ehi]
  have hsurj' : ∀ y : bcObj res (D'.X 0), (bcMap res (D'.d 0 1)).hom y = 0 →
      ∃ y' : D'.X 0, (D'.d 0 1).hom y' = 0 ∧ (bcUnit res _).hom y' = y := by
    intro y hy
    obtain ⟨y'', hy''d, t, ht, hy''⟩ := hsurj (ei _ y) (Ez hy)
    have hut : IsUnit (ψ t) := IsLocalization.map_units A' (⟨t, ht⟩ : 𝔭.primeCompl)
    let v : (G.obj (D.X 0) : Type u) := (bcUnit ψ (D.X 0)).hom y''
    have hv : (D'.d 0 1).hom v = 0 := by
      change (bcUnit ψ _).hom ((D.d 0 1).hom y'') = 0
      rw [hy''d, map_zero]
    refine ⟨hut.unit⁻¹.1 • v, ?_, ?_⟩
    · rw [(D'.d 0 1).hom.map_smul, hv, smul_zero]
    · have h2 : (bcUnit res (G.obj (D.X 0))).hom v = ψ t • y := by
        change (bcUnit res (G.obj (D.X 0))).hom ((bcUnit ψ _).hom y'') = _
        rw [← Eunit, hy'', Esmul, Ehi]
      change (bcUnit res (G.obj (D.X 0))).hom (hut.unit⁻¹.1 • v) = y
      rw [(bcUnit res (G.obj (D.X 0))).hom.map_smul, h2, smul_smul, IsUnit.val_inv_mul, one_smul]
  have : ∀ i, Module.Flat A' (C'.X i) := fun i => flat_extendScalars_obj (C.X i)
  have : ∀ i, Module.Flat A' (D'.X i) := fun i => flat_extendScalars_obj (D.X i)
  have : CochainComplex.IsStrictlyLE C' b := (CochainComplex.isStrictlyLE_iff C' b).2
    fun i hi => G.map_isZero (CochainComplex.isZero_of_isStrictlyLE C b i hi)
  have : CochainComplex.IsStrictlyLE D' b := (CochainComplex.isStrictlyLE_iff D' b).2
    fun i hi => G.map_isZero (CochainComplex.isZero_of_isStrictlyLE D b i hi)
  have hx' : (bcMap res (C'.d 0 1)).hom (eh _ x) = 0 := by
    change (bcMap res (G.map (C.d 0 1))).hom (eh _ x) = 0
    rw [← Ehnat, hx, map_zero]
  obtain ⟨c', hc'd, hc'x⟩ := exists_cocycle_lift_local Φ' b hD' (isPerfect_extendScalars ψ C b hCp)
    (isPerfect_extendScalars ψ D b hDp) h0' h1' hsurj' (eh _ x) hx'
  -- clearing denominators, in the honest tensor product `A_𝔭 ⊗_A C^i`
  let e : ∀ M : ModuleCat.{u} A, G.obj M ≃ₗ[A'] TensorProduct A A' M := fun M =>
    StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv A A' M
  have he1 : ∀ (M : ModuleCat.{u} A) (m : M), e M ((bcUnit ψ M).hom m) = (1 : A') ⊗ₜ m :=
    fun _ _ => rfl
  have hloc : ∀ M : ModuleCat.{u} A,
      IsLocalizedModule 𝔭.primeCompl (TensorProduct.mk A A' M 1) := fun M => by
    rw [isLocalizedModule_iff_isBaseChange 𝔭.primeCompl A']
    exact TensorProduct.isBaseChange A M A'
  obtain ⟨⟨c₀, s⟩, hs⟩ := IsLocalizedModule.surj 𝔭.primeCompl
    (TensorProduct.mk A A' (C.X 0) 1) (e _ c')
  have hs' : ψ s • c' = (bcUnit ψ (C.X 0)).hom c₀ := by
    apply (e _).injective
    rw [he1, map_smul]
    exact (algebraMap_smul A' (s : A) (e _ c')).trans hs
  have hd₀ : TensorProduct.mk A A' (C.X 1) 1 ((C.d 0 1).hom c₀) =
      TensorProduct.mk A A' (C.X 1) 1 0 := by
    rw [map_zero]
    change (1 : A') ⊗ₜ[A] (C.d 0 1).hom c₀ = 0
    rw [← he1, ← bcMap_bcUnit, ← hs']
    change e _ ((C'.d 0 1).hom (ψ s • c')) = 0
    rw [map_smul, hc'd, smul_zero, map_zero]
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := 𝔭.primeCompl)
    (f := TensorProduct.mk A A' (C.X 1) 1) hd₀
  refine ⟨(t : A) • c₀, ?_, (t : A) * s, 𝔭.primeCompl.mul_mem t.2 s.2, ?_⟩
  · rw [map_smul]; simpa [Submonoid.smul_def] using ht
  · have himg : eh _ ((bcUnit ρ (C.X 0)).hom c₀) = eh _ ((s : A) • x) := by
      rw [Eunit, ← hs', Esmul, map_smul]
      exact congrArg (ψ s • ·) hc'x
    have := congrArg (ei _) himg
    rw [Eih, Eih] at this
    rw [map_smul, this, smul_smul]

end StacksDraft.ConeLift

end
