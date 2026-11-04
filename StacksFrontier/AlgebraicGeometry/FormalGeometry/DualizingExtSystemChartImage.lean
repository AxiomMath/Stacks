module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemChartDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemChartTransport
public import StacksFrontier.Homology.ExtendScalars.Localization

/-!
# The images of the transition maps over a chart, read back over `A`

Over a chart `D(f)` of the punctured spectrum, the route of [Stacks, Tag 0EHK] proves that the
images of the transition maps of the `Ext` system stop growing over the completed chart ring
`B = (A_f)^∧_{I A_f}`, for the system transported to `B`
(`Stacks.Algebraization.dualizingExtSystemChartTransport`). This file reads that statement back
over `A`, in the `Submodule.localized₀` form in which
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_chart` consumes it.

## Main results

* `Stacks.Algebraization.range_map_eq_iff_of_iso` — equalities of images of transition maps are
  invariant under isomorphism of systems.
* `Stacks.Algebraization.range_eq_range_of_extendScalars_adicCompletion` — an equality of images
  descends along extension of scalars to the adic completion, when the target is power torsion.
* `Stacks.Algebraization.exists_localized₀_range_eq_of_chartTransport` — the chart statement
  over `B` gives the chart statement over `A`.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **Equalities of images of transition maps are invariant under isomorphism of systems.** -/
public theorem range_map_eq_iff_of_iso {R : Type u} [Ring R] {F F' : ℕ ⥤ ModuleCat.{u} R}
    (e : F ≅ F') {a m n : ℕ} (h₁ : m ≤ n) (h₂ : a ≤ n) :
    LinearMap.range (F.map (homOfLE h₁)).hom = LinearMap.range (F.map (homOfLE h₂)).hom ↔
      LinearMap.range (F'.map (homOfLE h₁)).hom =
        LinearMap.range (F'.map (homOfLE h₂)).hom := by
  have key : ∀ {k : ℕ} (h : k ≤ n), LinearMap.range (F'.map (homOfLE h)).hom =
      Submodule.map (e.hom.app n).hom (LinearMap.range (F.map (homOfLE h)).hom) := by
    intro k h
    have hnat : F'.map (homOfLE h) = e.inv.app k ≫ F.map (homOfLE h) ≫ e.hom.app n := by
      rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
    rw [hnat, ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (ConcreteCategory.bijective_of_isIso (e.inv.app k)).2),
      ModuleCat.hom_comp, LinearMap.range_comp]
  rw [key h₁, key h₂]
  exact (Submodule.map_injective_of_injective
    (ConcreteCategory.bijective_of_isIso (e.hom.app n)).1).eq_iff.symm

section Descent

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)

/-- The carrier of an extension of scalars is the tensor product, linearly over the larger
ring. -/
public def extendScalarsObjIso (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R (AdicCompletion J R))).obj M ≅
      ModuleCat.of (AdicCompletion J R) (AdicCompletion J R ⊗[R] M) :=
  let X := (ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))).obj
    (ModuleCat.of (AdicCompletion J R) (AdicCompletion J R))
  haveI : IsScalarTower R (AdicCompletion J R) X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (AdicCompletion J R) (AdicCompletion J R) :
      X ≃ₗ[AdicCompletion J R] AdicCompletion J R) (LinearEquiv.refl R M)).toModuleIso

omit [IsNoetherianRing R] in
/-- The identification `extendScalarsObjIso` of an extension of scalars with a tensor product is
natural in the module. -/
public theorem extendScalarsObjIso_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R (AdicCompletion J R))).map g ≫
        (extendScalarsObjIso J N).hom =
      (extendScalarsObjIso J M).hom ≫
        ModuleCat.ofHom (g.hom.baseChange (AdicCompletion J R)) :=
  ModuleCat.ExtendScalars.hom_ext fun _ => rfl

/-- **An equality of images descends along extension of scalars to the adic completion**, when
the common target is power torsion. -/
public theorem range_eq_range_of_extendScalars_adicCompletion {X₁ X₂ Y : ModuleCat.{u} R}
    (hY : IsIPowerTorsion R Y J) (u : X₁ ⟶ Y) (v : X₂ ⟶ Y)
    (h : LinearMap.range
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap R (AdicCompletion J R))).map u).hom =
      LinearMap.range
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap R (AdicCompletion J R))).map v).hom) :
    LinearMap.range u.hom = LinearMap.range v.hom := by
  refine Stacks.range_eq_range_of_baseChange_adicCompletion J hY u.hom v.hom ?_
  have key : ∀ {X : ModuleCat.{u} R} (w : X ⟶ Y),
      LinearMap.range (w.hom.baseChange (AdicCompletion J R)) =
        Submodule.map (extendScalarsObjIso J Y).hom.hom (LinearMap.range
          ((ModuleCat.extendScalars.{u, u, u} (algebraMap R (AdicCompletion J R))).map w).hom) := by
    intro X w
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨_, ⟨(extendScalarsObjIso J X).inv.hom x, rfl⟩, ?_⟩
      have := congrArg (fun φ => φ.hom ((extendScalarsObjIso J X).inv.hom x))
        (extendScalarsObjIso_naturality J w)
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
        ModuleCat.hom_ofHom] at this
      rw [this]
      congr 1
      exact congrArg (fun φ => φ.hom x) (extendScalarsObjIso J X).inv_hom_id
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨(extendScalarsObjIso J X).hom.hom x, ?_⟩
      have := congrArg (fun φ => φ.hom x) (extendScalarsObjIso_naturality J w)
      simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
        ModuleCat.hom_ofHom] using this.symm
  rw [key, key, h]

end Descent

/-- `Submodule.localized₀` does not depend on the chosen localization map, up to the comparison
isomorphism of two localizations. -/
public theorem map_linearEquiv_localized₀ {R : Type*} [CommRing R] (p : Submonoid R)
    {M N₁ N₂ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂] (f₁ : M →ₗ[R] N₁) (f₂ : M →ₗ[R] N₂)
    [IsLocalizedModule p f₁] [IsLocalizedModule p f₂] (K : Submodule R M) :
    Submodule.map (IsLocalizedModule.linearEquiv p f₁ f₂).toLinearMap
        (Submodule.localized₀ p f₁ K) = Submodule.localized₀ p f₂ K := by
  have hmk : ∀ (m : M) (s : p), IsLocalizedModule.linearEquiv p f₁ f₂
      (IsLocalizedModule.mk' f₁ m s) = IsLocalizedModule.mk' f₂ m s := by
    intro m s
    refine (IsLocalizedModule.mk'_eq_iff.mpr ?_).symm
    have h1 : (s : R) • IsLocalizedModule.mk' f₁ m s = f₁ m := IsLocalizedModule.mk'_cancel' f₁ m s
    show f₂ m = (s : R) • _
    rw [← LinearEquiv.map_smul, h1, IsLocalizedModule.linearEquiv_apply]
  ext x
  constructor
  · rintro ⟨_, ⟨m, hm, s, rfl⟩, rfl⟩
    exact ⟨m, hm, s, (hmk m s).symm⟩
  · rintro ⟨m, hm, s, rfl⟩
    exact ⟨_, ⟨m, hm, s, rfl⟩, hmk m s⟩

section Chart

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **The chart statement over the completed chart ring gives the chart statement over `A`.**
Let `G = dualizingExtSystem M ω i` and let `D` be the `Ext` system of the transport of `(M_n)`
and `ω` to `B = (A_f)^∧_{I A_f}`. If from some index `a` on the images of the transition maps of
`D` stop growing, then so do the localizations away from `f` of the images of the transition maps
of `G`. -/
public theorem exists_localized₀_range_eq_of_chartTransport (I : Ideal A) (f : A)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hMfin : ∀ n : ℕ, Module.Finite A (M.obj (op n)))
    (hMann : ∀ n : ℕ, ∃ k : ℕ, I ^ k • (⊤ : Submodule A (M.obj (op n))) = ⊥)
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω) (i : ℤ)
    (hD : ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      LinearMap.range ((dualizingExtSystem (chartTransportSystem I f M)
          (chartTransportComplex I f ω) i).map (homOfLE hmn)).hom =
        LinearMap.range ((dualizingExtSystem (chartTransportSystem I f M)
          (chartTransportComplex I f ω) i).map (homOfLE (hm.trans hmn))).hom) :
    ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      Submodule.localized₀ (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) ((dualizingExtSystem M ω i).obj n))
          (LinearMap.range ((dualizingExtSystem M ω i).map (homOfLE hmn)).hom) =
        Submodule.localized₀ (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) ((dualizingExtSystem M ω i).obj n))
          (LinearMap.range ((dualizingExtSystem M ω i).map (homOfLE (hm.trans hmn))).hom) := by
  let G := dualizingExtSystem M ω i
  let L := ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers f)
  let ext₂ := ModuleCat.extendScalars.{u, u, u} (algebraMap (Localization.Away f)
    (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f)))
  -- the transported system is the localized system extended to `B`
  let e : (G ⋙ L) ⋙ ext₂ ≅ dualizingExtSystem (chartTransportSystem I f M)
      (chartTransportComplex I f ω) i :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft G
        (extendScalars_iso_localizedModuleFunctor.{u, u} (Submonoid.powers f)).symm) ext₂ ≪≫
      dualizingExtSystemChartTransport I f ω hω i M hMfin
  obtain ⟨a, ha⟩ := hD
  refine ⟨a, fun m hm => ?_⟩
  obtain ⟨k, hk⟩ := ha m hm
  refine ⟨k, fun n hmn hkn => ?_⟩
  have hB := (range_map_eq_iff_of_iso e hmn (hm.trans hmn)).mpr (hk n hmn hkn)
  -- the target of the localized maps is power torsion
  obtain ⟨c, hc⟩ := hMann n
  have hc' := smul_top_dualizingExtSystem_eq_bot M ω i n hc
  have htors : IsIPowerTorsion (Localization.Away f)
      ((G.obj n).localizedModule (Submonoid.powers f))
      (I.map (algebraMap A (Localization.Away f))) := by
    refine isIPowerTorsion_of_smul_top_eq_bot I c (le_antisymm ?_ bot_le)
    rw [Submodule.smul_le]
    intro r hr x _
    obtain ⟨⟨m, t⟩, rfl⟩ := (IsLocalizedModule.mk'_surjective (Submonoid.powers f)
      ((G.obj n).localizedModuleMkLinearMap (Submonoid.powers f))) x
    rw [Submodule.mem_bot, Function.uncurry_apply_pair, ← IsLocalizedModule.mk'_smul]
    have hm : r • m = 0 := by
      have := Submodule.smul_mem_smul hr (Submodule.mem_top (R := A) (x := m))
      rw [hc'] at this
      exact (Submodule.mem_bot A).mp this
    rw [hm, IsLocalizedModule.mk'_zero]
  have hAf := range_eq_range_of_extendScalars_adicCompletion
    (I.map (algebraMap A (Localization.Away f))) htors
    (L.map (G.map (homOfLE hmn))) (L.map (G.map (homOfLE (hm.trans hmn)))) hB
  -- read the localized ranges as `localized₀`
  have hloc : ∀ {j : ℕ} (h : j ≤ n),
      Submodule.map (IsLocalizedModule.linearEquiv (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) (G.obj n))
          ((G.obj n).localizedModuleMkLinearMap (Submonoid.powers f))).toLinearMap
        (Submodule.localized₀ (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) (G.obj n))
          (LinearMap.range (G.map (homOfLE h)).hom)) =
        (LinearMap.range (L.map (G.map (homOfLE h))).hom :
          Submodule (Localization.Away f) ((G.obj n).localizedModule (Submonoid.powers f))
        ).restrictScalars A := by
    intro j h
    rw [map_linearEquiv_localized₀,
      ← LinearMap.range_localizedMap_eq_localized₀_range (Submonoid.powers f)
        ((G.obj j).localizedModuleMkLinearMap (Submonoid.powers f))
        ((G.obj n).localizedModuleMkLinearMap (Submonoid.powers f)) (G.map (homOfLE h)).hom]
    rfl
  exact Submodule.map_injective_of_injective (LinearEquiv.injective _)
    ((hloc hmn).trans ((congrArg (Submodule.restrictScalars A) hAf).trans
      (hloc (hm.trans hmn)).symm))

end Chart

end Stacks.Algebraization

end
