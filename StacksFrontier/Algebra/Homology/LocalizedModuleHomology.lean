module

public import StacksFrontier.Homology.KFlat.Flat
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import StacksFrontier.Homology.TorAmplitude.Comparison

/-!
# Localization of modules and the cohomology of complexes

Let `R` be a commutative ring and `S` a submonoid of `R`. Localization at `S` is exact, so a map
of complexes of `R`-modules which is a localization at `S` in every degree induces a localization
at `S` on every cohomology module. This file records that statement together with what it takes
to carry a cohomological localization through a total tensor product with a K-flat complex.

## Main results

* `CochainComplex.isLocalizedModule_homologyMap`: a degreewise localization of complexes induces
  a localization on cohomology.
* `IsLocalizedModule.directSum_lmap` and `IsLocalizedModule.of_isColimit_cofan`: a direct sum, and
  more generally a map of coproducts, of localizations is a localization.
* `CochainComplex.isLocalizedModule_homologyMap_whiskerLeft`: if every element of `S` acts
  invertibly on the terms of `Z` and `κ : Y ⟶ Z` induces localizations at `S` on cohomology, so
  does `P ◁ κ` for every K-flat complex `P`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- An element of a complex of modules killed by the differential is a cycle. -/
theorem exists_cycles_of_d_eq_zero (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (x : K.X n) (hx : K.d n (n + 1) x = 0) : ∃ z : K.cycles n, K.iCycles n z = x := by
  let S := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d n (n + 1))
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S
    (K.cyclesIsKernel n (n + 1) (by simp))
  exact (ShortComplex.moduleCat_exact_iff S).mp hS x hx

/-- Every homology class is represented by a cycle. -/
theorem exists_homologyπ_eq (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (x : K.homology n) : ∃ z : K.cycles n, K.homologyπ n z = x :=
  (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance x

end CochainComplex

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Multiplication by an element of `S` is bijective on the target of a localization map. -/
theorem bijective_smul_of_isLocalizedModule {S : Submonoid R} {M M' : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (s : S) : Function.Bijective (fun y : M' => (s : R) • y) := by
  have := IsLocalizedModule.map_units f s
  rw [Module.End.isUnit_iff] at this
  exact this

open CochainComplex.KFlat in
/-- **A degreewise localization of complexes localizes cohomology.** If every component of a
map of complexes of `R`-modules is a localization at `S`, so is the map it induces on each
cohomology module. -/
theorem isLocalizedModule_homologyMap (S : Submonoid R)
    {Y Y' : CochainComplex (ModuleCat.{v} R) ℤ} (ℓ : Y ⟶ Y')
    (h : ∀ i, IsLocalizedModule S (ℓ.f i).hom) (n : ℤ) :
    IsLocalizedModule S (HomologicalComplex.homologyMap ℓ n).hom := by
  have hb : ∀ (s : S) (i : ℤ), Function.Bijective (fun y : Y'.X i => (s : R) • y) :=
    fun s i => bijective_smul_of_isLocalizedModule (ℓ.f i).hom s
  have hcomm : ∀ (i j : ℤ) (y : Y.X i), ℓ.f j (Y.d i j y) = Y'.d i j (ℓ.f i y) := fun i j y =>
    (congrArg (fun k : Y.X i ⟶ Y'.X j => k y) (ℓ.comm i j)).symm
  have hmap : ∀ z : Y.cycles n, HomologicalComplex.homologyMap ℓ n (Y.homologyπ n z) =
      Y'.homologyπ n (HomologicalComplex.cyclesMap ℓ n z) := fun z =>
    congrArg (fun k : Y.cycles n ⟶ Y'.homology n => k z)
      (HomologicalComplex.homologyπ_naturality ℓ n)
  have hci : ∀ z : Y.cycles n, Y'.iCycles n (HomologicalComplex.cyclesMap ℓ n z) =
      ℓ.f n (Y.iCycles n z) := fun z =>
    congrArg (fun k : Y.cycles n ⟶ Y'.X n => k z) (HomologicalComplex.cyclesMap_i ℓ n)
  have hinj : ∀ (K : CochainComplex (ModuleCat.{v} R) ℤ), Function.Injective (K.iCycles n) :=
    fun K => (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  have hid : ∀ (K : CochainComplex (ModuleCat.{v} R) ℤ) (z : K.cycles n),
      K.d n (n + 1) (K.iCycles n z) = 0 := fun K z =>
    congrArg (fun k : K.cycles n ⟶ K.X (n + 1) => k z) (K.iCycles_d n (n + 1))
  refine ⟨fun s => ?_, fun x => ?_, fun {x₁ x₂} hx => ?_⟩
  · rw [Module.End.isUnit_iff]
    refine ⟨?_, ?_⟩
    · intro x₁ x₂ hx
      obtain ⟨z₁, rfl⟩ := exists_homologyπ_eq Y' n x₁
      obtain ⟨z₂, rfl⟩ := exists_homologyπ_eq Y' n x₂
      have hx' : Y'.homologyπ n ((s : R) • (z₁ - z₂)) = 0 := by
        rw [map_smul, map_sub, smul_sub, sub_eq_zero]
        exact hx
      rw [homologyπ_eq_zero_iff] at hx'
      obtain ⟨w, hw⟩ := hx'
      obtain ⟨w₀, rfl⟩ := (hb s (n - 1)).2 w
      rw [← sub_eq_zero, ← map_sub, homologyπ_eq_zero_iff]
      refine ⟨w₀, (hb s n).1 ?_⟩
      change (s : R) • Y'.d (n - 1) n w₀ = (s : R) • Y'.iCycles n (z₁ - z₂)
      rw [← map_smul, ← map_smul]
      exact hw
    · intro x
      obtain ⟨z, rfl⟩ := exists_homologyπ_eq Y' n x
      obtain ⟨y₀, hy₀⟩ := (hb s n).2 (Y'.iCycles n z)
      have hd : Y'.d n (n + 1) y₀ = 0 := by
        refine (hb s (n + 1)).1 (?_ : (s : R) • Y'.d n (n + 1) y₀ = (s : R) • 0)
        rw [smul_zero, ← map_smul]
        change Y'.d n (n + 1) ((fun y : Y'.X n => (s : R) • y) y₀) = 0
        rw [hy₀]
        exact hid Y' z
      obtain ⟨z₀, hz₀⟩ := exists_cycles_of_d_eq_zero Y' n y₀ hd
      refine ⟨Y'.homologyπ n z₀, ?_⟩
      change (s : R) • Y'.homologyπ n z₀ = Y'.homologyπ n z
      rw [← map_smul]
      congr 1
      apply hinj Y'
      rw [map_smul, hz₀]
      exact hy₀
  · obtain ⟨z, rfl⟩ := exists_homologyπ_eq Y' n x
    obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj S (ℓ.f n).hom (Y'.iCycles n z)
    rw [Submonoid.smul_def] at hms
    change (s : R) • Y'.iCycles n z = ℓ.f n m at hms
    have hdm : (ℓ.f (n + 1)).hom (Y.d n (n + 1) m) = (ℓ.f (n + 1)).hom 0 := by
      rw [map_zero]
      change ℓ.f (n + 1) (Y.d n (n + 1) m) = 0
      rw [hcomm, ← hms, map_smul, hid Y' z, smul_zero]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := (ℓ.f (n + 1)).hom) hdm
    rw [smul_zero, Submonoid.smul_def] at ht
    obtain ⟨c, hc⟩ := exists_cycles_of_d_eq_zero Y n ((t : R) • m)
      (by rw [map_smul]; exact ht)
    refine ⟨⟨Y.homologyπ n c, t * s⟩, ?_⟩
    rw [Submonoid.smul_def]
    change ((t * s : S) : R) • Y'.homologyπ n z =
      HomologicalComplex.homologyMap ℓ n (Y.homologyπ n c)
    rw [hmap, ← map_smul]
    congr 1
    apply hinj Y'
    rw [map_smul, hci, hc, map_smul, ← hms, Submonoid.coe_mul, mul_smul]
  · obtain ⟨z₁, rfl⟩ := exists_homologyπ_eq Y n x₁
    obtain ⟨z₂, rfl⟩ := exists_homologyπ_eq Y n x₂
    have h0 : HomologicalComplex.homologyMap ℓ n (Y.homologyπ n (z₁ - z₂)) = 0 := by
      rw [map_sub, map_sub, sub_eq_zero]
      exact hx
    rw [homologyMap_eq_zero_iff ℓ n _ (z₁ - z₂) rfl] at h0
    obtain ⟨w, hw⟩ := h0
    obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj S (ℓ.f (n - 1)).hom w
    rw [Submonoid.smul_def] at hms
    change (s : R) • w = ℓ.f (n - 1) m at hms
    have heq : (ℓ.f n).hom ((s : R) • Y.iCycles n (z₁ - z₂)) =
        (ℓ.f n).hom (Y.d (n - 1) n m) := by
      change ℓ.f n ((s : R) • Y.iCycles n (z₁ - z₂)) = ℓ.f n (Y.d (n - 1) n m)
      rw [hcomm, ← hms, map_smul, map_smul, hw]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := (ℓ.f n).hom) heq
    rw [Submonoid.smul_def, Submonoid.smul_def] at ht
    refine ⟨t * s, ?_⟩
    rw [← sub_eq_zero, ← smul_sub, ← map_sub, Submonoid.smul_def, ← map_smul,
      homologyπ_eq_zero_iff]
    refine ⟨(t : R) • m, ?_⟩
    rw [map_smul, map_smul, ← ht, Submonoid.coe_mul, mul_smul]

end CochainComplex

namespace IsLocalizedModule

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- **A direct sum of localizations is a localization.** -/
theorem directSum_lmap {ι : Type*} {M M' : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R (M' i)] (f : ∀ i, M i →ₗ[R] M' i) [∀ i, IsLocalizedModule S (f i)] :
    IsLocalizedModule S (DirectSum.lmap f) := by
  classical
  refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
  · have hb : ∀ i, Function.Bijective (fun y : M' i => (s : R) • y) := fun i =>
      CochainComplex.bijective_smul_of_isLocalizedModule (f i) s
    rw [Module.End.isUnit_iff]
    refine ⟨fun y₁ y₂ hy => ?_, fun y => ?_⟩
    · ext i
      exact (hb i).1 (congrArg (fun z : DirectSum ι M' => z i) hy)
    · choose g hg using fun i => (hb i).2
      have hg' : ∀ i (b : M' i), (s : R) • g i b = b := hg
      let gl : ∀ i, M' i →+ M' i := fun i =>
        { toFun := g i
          map_zero' := (hb i).1 ((hg' i 0).trans (smul_zero _).symm)
          map_add' := fun a b => (hb i).1 ((hg' i (a + b)).trans (by
            change a + b = (s : R) • (g i a + g i b)
            rw [smul_add, hg' i a, hg' i b])) }
      refine ⟨DFinsupp.mapRange.addMonoidHom gl y, ?_⟩
      ext i
      exact hg i (y i)
  · induction y using DirectSum.induction_on with
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | of i y =>
      obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalizedModule.surj S (f i) y
      refine ⟨⟨DirectSum.of M i x, s⟩, ?_⟩
      rw [Submonoid.smul_def] at hxs ⊢
      change (s : R) • DirectSum.lof R ι M' i y = DirectSum.lmap f (DirectSum.lof R ι M i x)
      rw [DirectSum.lmap_lof, ← map_smul, hxs]
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨⟨x₁, s₁⟩, e₁⟩ := h₁
      obtain ⟨⟨x₂, s₂⟩, e₂⟩ := h₂
      refine ⟨⟨(s₂ : R) • x₁ + (s₁ : R) • x₂, s₁ * s₂⟩, ?_⟩
      rw [Submonoid.smul_def] at e₁ e₂ ⊢
      dsimp only at e₁ e₂ ⊢
      rw [map_add, map_smul, map_smul, ← e₁, ← e₂, smul_add, Submonoid.coe_mul, smul_smul,
        smul_smul, mul_comm (s₂ : R)]
  · have h0 : ∀ i, f i (x₁ i - x₂ i) = f i 0 := fun i => by
      rw [map_sub, map_zero, sub_eq_zero]
      exact congrArg (fun z : DirectSum ι M' => z i) hx
    choose c hc using fun i => IsLocalizedModule.exists_of_eq (S := S) (f := f i) (h0 i)
    classical
    refine ⟨∏ i ∈ (x₁ - x₂).support, c i, ?_⟩
    rw [← sub_eq_zero, ← smul_sub]
    ext i
    rw [DirectSum.zero_apply]
    change ((∏ j ∈ (x₁ - x₂).support, c j : S) : R) • (x₁ - x₂) i = 0
    by_cases hi : i ∈ (x₁ - x₂).support
    · rw [← Finset.mul_prod_erase _ _ hi, Submonoid.coe_mul, mul_comm, mul_smul]
      have := hc i
      rw [smul_zero, Submonoid.smul_def] at this
      rw [DirectSum.sub_apply, this, smul_zero]
    · rw [DFinsupp.notMem_support_iff.mp hi, smul_zero]

/-- A coproduct of modules is isomorphic to their direct sum, compatibly with the injections. -/
private theorem exists_iso_directSum_of_isColimit {J : Type w} [DecidableEq J]
    {M : J → ModuleCat.{max w v} R} {c : Cofan M} (hc : IsColimit c) :
    ∃ e : c.pt ≅ ModuleCat.of R (DirectSum J fun i ↦ M i),
      ∀ j, c.inj j ≫ e.hom = ModuleCat.ofHom (DirectSum.lof R J (fun i ↦ M i) j) := by
  have : HasCoproduct M := ⟨⟨⟨c, hc⟩⟩⟩
  refine ⟨hc.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫ ModuleCat.coprodIsoDirectSum M,
    fun j => ?_⟩
  rw [Iso.trans_hom, ← Category.assoc]
  exact (congrArg (· ≫ (ModuleCat.coprodIsoDirectSum M).hom)
    (hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨j⟩)).trans
    (ModuleCat.ι_coprodIsoDirectSum_hom M j)

/-- **A colimit of localizations is a localization.** If two coproducts of modules are compared
by a map restricting on each summand to a localization at `S`, that map is a localization at
`S`. -/
theorem of_isColimit_cofan {J : Type w} {M M' : J → ModuleCat.{max w v} R}
    {c : Cofan M} (hc : IsColimit c) {c' : Cofan M'} (hc' : IsColimit c')
    (g : c.pt ⟶ c'.pt) (f : ∀ j, M j ⟶ M' j) (hfg : ∀ j, c.inj j ≫ g = f j ≫ c'.inj j)
    (hf : ∀ j, IsLocalizedModule S (f j).hom) : IsLocalizedModule S g.hom := by
  classical
  obtain ⟨e, he⟩ := exists_iso_directSum_of_isColimit hc
  obtain ⟨e', he'⟩ := exists_iso_directSum_of_isColimit hc'
  have hg : g ≫ e'.hom = e.hom ≫ ModuleCat.ofHom (DirectSum.lmap fun j => (f j).hom) := by
    refine Cofan.IsColimit.hom_ext hc _ _ fun j => ?_
    rw [reassoc_of% (hfg j), he', reassoc_of% (he j)]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (DirectSum.lmap_lof (fun j => (f j).hom) j x).symm
  have hg2 : g = e.hom ≫ ModuleCat.ofHom (DirectSum.lmap fun j => (f j).hom) ≫ e'.inv := by
    rw [← Category.assoc, ← hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : ∀ j, IsLocalizedModule S (f j).hom := hf
  have := directSum_lmap S fun j => (f j).hom
  have := IsLocalizedModule.of_linearEquiv_right S (DirectSum.lmap fun j => (f j).hom)
    e.toLinearEquiv
  have h2 := IsLocalizedModule.of_linearEquiv S
    ((DirectSum.lmap fun j => (f j).hom) ∘ₗ (e.toLinearEquiv : c.pt →ₗ[R] _))
    e'.symm.toLinearEquiv
  rw [hg2]
  exact h2

end IsLocalizedModule

namespace CochainComplex

open MonoidalCategory

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Localization at `S`, as an endofunctor of the category of `R`-modules. -/
noncomputable def localizedModuleEnd : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (LocalizedModule S M)
  map f := ModuleCat.ofHom (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
    (LocalizedModule.mkLinearMap S _) f.hom)
  map_id M := by
    ext : 1
    exact IsLocalizedModule.map_id S _
  map_comp f g := by
    ext : 1
    apply IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S _)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S _))
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      IsLocalizedModule.map_apply]

/-- Localization at `S` is an additive functor on `R`-modules. -/
instance : (localizedModuleEnd S (R := R)).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (by
    simp only [localizedModuleEnd, ModuleCat.hom_add, ModuleCat.hom_ofHom, map_add]
    rfl)

/-- The localization maps, as a map from a complex to its degreewise localization. -/
noncomputable def toLocalizedModuleEnd (Y : CochainComplex (ModuleCat.{u} R) ℤ) :
    Y ⟶ ((localizedModuleEnd S).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y where
  f i := ModuleCat.ofHom (LocalizedModule.mkLinearMap S (Y.X i))
  comm' i j _ := by
    ext x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, localizedModuleEnd]
    exact IsLocalizedModule.map_apply S (LocalizedModule.mkLinearMap S _)
      (LocalizedModule.mkLinearMap S _) (Y.d i j).hom x

/-- In each degree, the map from a complex to its degreewise localization is a localization
at `S`. -/
instance (Y : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    IsLocalizedModule S ((toLocalizedModuleEnd S Y).f i).hom :=
  inferInstanceAs (IsLocalizedModule S (LocalizedModule.mkLinearMap S (Y.X i)))

/-- The degreewise lifts of a map to a complex on which `S` acts invertibly commute with the
differentials. -/
theorem lift_comp_d {Y Z : CochainComplex (ModuleCat.{u} R) ℤ} (κ : Y ⟶ Z)
    (hZ : ∀ i (s : S), IsUnit (algebraMap R (Module.End R (Z.X i)) s)) (i j : ℤ) :
    (Z.d i j).hom ∘ₗ IsLocalizedModule.lift S (LocalizedModule.mkLinearMap S (Y.X i))
        (κ.f i).hom (hZ i) =
      IsLocalizedModule.lift S (LocalizedModule.mkLinearMap S (Y.X j)) (κ.f j).hom (hZ j) ∘ₗ
        IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
          (LocalizedModule.mkLinearMap S _) (Y.d i j).hom := by
  apply IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S _) (hZ j)
  refine LinearMap.ext fun x => ?_
  have h4 := congrArg (fun k : Y.X i ⟶ Z.X j => k x) (κ.comm i j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h4
  simp only [LinearMap.comp_apply, IsLocalizedModule.lift_apply, IsLocalizedModule.map_apply]
  exact h4

/-- A map to a complex on which `S` acts invertibly factors through the degreewise
localization. -/
noncomputable def liftLocalizedModuleEnd {Y Z : CochainComplex (ModuleCat.{u} R) ℤ} (κ : Y ⟶ Z)
    (hZ : ∀ i (s : S), IsUnit (algebraMap R (Module.End R (Z.X i)) s)) :
    ((localizedModuleEnd S).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y ⟶ Z where
  f i := ModuleCat.ofHom
    (IsLocalizedModule.lift S (LocalizedModule.mkLinearMap S (Y.X i)) (κ.f i).hom (hZ i))
  comm' i j _ := ModuleCat.hom_ext (lift_comp_d S κ hZ i j)

/-- The factorization `liftLocalizedModuleEnd` of a map through the degreewise localization,
precomposed with the localization maps, recovers the map. -/
theorem toLocalizedModuleEnd_comp_lift {Y Z : CochainComplex (ModuleCat.{u} R) ℤ} (κ : Y ⟶ Z)
    (hZ : ∀ i (s : S), IsUnit (algebraMap R (Module.End R (Z.X i)) s)) :
    toLocalizedModuleEnd S Y ≫ liftLocalizedModuleEnd S κ hZ = κ := by
  ext i x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact IsLocalizedModule.lift_apply S (LocalizedModule.mkLinearMap S (Y.X i)) (κ.f i).hom
    (hZ i) x

end CochainComplex

namespace CochainComplex

open MonoidalCategory

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Tensoring a localization map on the left with a fixed module gives a localization map. -/
theorem isLocalizedModule_lTensor (N : Type*) [AddCommGroup N] [Module R N] {M M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (g : M →ₗ[R] M')
    [IsLocalizedModule S g] : IsLocalizedModule S (g.lTensor N) := by
  have h1 := IsLocalizedModule.rTensor (R := R) (A := R) S (N := N) g
  have h2 := IsLocalizedModule.of_linearEquiv_right S
    (TensorProduct.AlgebraTensorModule.rTensor R N g) (TensorProduct.comm R N M)
  have h3 := IsLocalizedModule.of_linearEquiv S
    ((TensorProduct.AlgebraTensorModule.rTensor R N g) ∘ₗ (TensorProduct.comm R N M).toLinearMap)
    (TensorProduct.comm R M' N)
  have he : ((TensorProduct.comm R M' N).toLinearMap ∘ₗ
      (TensorProduct.AlgebraTensorModule.rTensor R N g) ∘ₗ
        (TensorProduct.comm R N M).toLinearMap) = g.lTensor N := by
    apply TensorProduct.ext'
    intro x y
    rfl
  rw [← he]
  exact h3

/-- The termwise components of the whiskering of a degreewise localization by a fixed complex
are localizations. -/
theorem isLocalizedModule_whiskerLeft_f (P : CochainComplex (ModuleCat.{u} R) ℤ)
    {Y Y' : CochainComplex (ModuleCat.{u} R) ℤ} (ℓ : Y ⟶ Y')
    (h : ∀ i, IsLocalizedModule S (ℓ.f i).hom) (n : ℤ) :
    IsLocalizedModule S ((P ◁ ℓ).f n).hom := by
  classical
  refine IsLocalizedModule.of_isColimit_cofan S (GradedObject.isColimitCofanMapObj _ _ n)
    (GradedObject.isColimitCofanMapObj _ _ n) ((P ◁ ℓ).f n)
    (fun x => P.X x.1.1 ◁ ℓ.f x.1.2) (fun x => ?_) (fun x => ?_)
  · have := HomologicalComplex.ι_mapBifunctorMap (𝟙 P) ℓ (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ) x.1.1 x.1.2 n x.2
    rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at this
    exact this
  · have := h x.1.2
    exact isLocalizedModule_lTensor S (P.X x.1.1) (ℓ.f x.1.2).hom

end CochainComplex

namespace CochainComplex

open MonoidalCategory

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- **Tensoring with a K-flat complex preserves cohomological localizations.** Let `κ : Y ⟶ Z`
be a map of complexes of `R`-modules such that every element of `S` acts invertibly on every
term of `Z`. If `κ` induces a localization at `S` on every cohomology module, so does `P ◁ κ`
for every K-flat complex `P`. -/
theorem isLocalizedModule_homologyMap_whiskerLeft (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.KFlat) {Y Z : CochainComplex (ModuleCat.{u} R) ℤ} (κ : Y ⟶ Z)
    (hZ : ∀ i (s : S), IsUnit (algebraMap R (Module.End R (Z.X i)) s))
    (hκ : ∀ n, IsLocalizedModule S (HomologicalComplex.homologyMap κ n).hom) (n : ℤ) :
    IsLocalizedModule S (HomologicalComplex.homologyMap (P ◁ κ) n).hom := by
  let η := toLocalizedModuleEnd S Y
  let κ' := liftLocalizedModuleEnd S κ hZ
  have hfac : η ≫ κ' = κ := toLocalizedModuleEnd_comp_lift S κ hZ
  have hη : ∀ m, IsLocalizedModule S (HomologicalComplex.homologyMap η m).hom := fun m =>
    isLocalizedModule_homologyMap S η (fun i => inferInstance) m
  have hiso : ∀ m, IsIso (HomologicalComplex.homologyMap κ' m) := fun m =>
    ModuleCat.isIso_of_isLocalizedModule_comp (hη m)
      (by rw [← HomologicalComplex.homologyMap_comp, hfac]; exact hκ m)
  have hq : QuasiIso κ' := ⟨fun m => (quasiIsoAt_iff_isIso_homologyMap κ' m).2 (hiso m)⟩
  have hq' : QuasiIso (P ◁ κ') := StacksDraft.TorAmplitude.quasiIso_tensorLeft_map P hP κ'
  have hPη : IsLocalizedModule S (HomologicalComplex.homologyMap (P ◁ η) n).hom :=
    isLocalizedModule_homologyMap S (P ◁ η)
      (fun i => isLocalizedModule_whiskerLeft_f S P η (fun j => inferInstance) i) n
  have hisoP : IsIso (HomologicalComplex.homologyMap (P ◁ κ') n) :=
    (quasiIsoAt_iff_isIso_homologyMap (P ◁ κ') n).1 inferInstance
  have hcomp : HomologicalComplex.homologyMap (P ◁ κ) n =
      HomologicalComplex.homologyMap (P ◁ η) n ≫ HomologicalComplex.homologyMap (P ◁ κ') n := by
    rw [← HomologicalComplex.homologyMap_comp, ← MonoidalCategory.whiskerLeft_comp, hfac]
  rw [hcomp, ModuleCat.hom_comp]
  exact IsLocalizedModule.of_linearEquiv S _
    (asIso (HomologicalComplex.homologyMap (P ◁ κ') n)).toLinearEquiv

end CochainComplex
