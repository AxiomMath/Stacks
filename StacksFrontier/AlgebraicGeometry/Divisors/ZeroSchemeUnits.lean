module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.ZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedBerthelotOgus
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.ZeroSchemeIdeal

/-!
# Elementary invariances of the zero scheme of a section

## Main results

* `Stacks.Divisors.zeroScheme_smul_of_isUnit`: multiplying the section by a unit does not change
  its zero scheme.
* `Stacks.Divisors.zeroScheme_congr_iso`: transporting the section along an isomorphism of
  invertible modules does not change its zero scheme.
* `Stacks.Divisors.IdealSheafData.ext_of_comap_eq`: an ideal sheaf is determined by its
  restrictions to the members of an open cover.
* `Stacks.Divisors.ne_zero_of_isEffectiveCartierDivisor_zeroScheme`: on a nonempty scheme the
  zero section does not cut out an effective Cartier divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- Spans of the values of linear functionals at two vectors are nested if every functional at
the first vector is a functional at the second. -/
private theorem span_eval_le_span_eval {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (m : M) (n : N)
    (h : ∀ φ : N →ₗ[R] R, ∃ ψ : M →ₗ[R] R, φ n = ψ m) :
    Ideal.span {a | ∃ φ : N →ₗ[R] R, a = φ n} ≤ Ideal.span {a | ∃ ψ : M →ₗ[R] R, a = ψ m} := by
  rw [Ideal.span_le]
  rintro _ ⟨φ, rfl⟩
  obtain ⟨ψ, hψ⟩ := h φ
  exact Ideal.subset_span ⟨ψ, hψ⟩

/-- **The zero scheme is unchanged by a unit.** For a global unit `a` of `X` and a global
section `s` of an invertible module, `Z(a • s) = Z(s)`. -/
theorem zeroScheme_smul_of_isUnit (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {a : Γ(X, ⊤)} (ha : IsUnit a) :
    zeroScheme X L (a • s) = zeroScheme X L s := by
  unfold zeroScheme
  congr 1
  funext U
  set b := X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op a
  have hb : IsUnit b := ha.map _
  have hres : L.presheaf.map (homOfLE le_top).op (a • s) =
      b • L.presheaf.map (homOfLE le_top).op s := Scheme.Modules.map_smul L _ a s
  rw [hres]
  obtain ⟨u, hu⟩ := hb
  refine le_antisymm (span_eval_le_span_eval _ _ fun φ => ⟨b • φ, by simp⟩)
    (span_eval_le_span_eval _ _ fun φ => ⟨(↑u⁻¹ : Γ(X, U.1)) • φ, ?_⟩)
  rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← hu, Units.inv_mul,
    one_mul]

/-- The application of a morphism of `𝒪_X`-modules on an open, as a linear map. -/
noncomputable def homAppLinear {L L' : X.Modules} (φ : L ⟶ L') (U : X.Opens) :
    Γ(L, U) →ₗ[Γ(X, U)] Γ(L', U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul φ

/-- Applying a morphism of `𝒪_X`-modules commutes with restriction of sections. -/
theorem homApp_map {L L' : X.Modules} (φ : L ⟶ L') {U V : X.Opens} (i : V ⟶ U) (x : Γ(L, U)) :
    φ.app V (L.presheaf.map i.op x) = L'.presheaf.map i.op (φ.app U x) := by
  simpa using congrArg (fun g => g.hom x) (φ.mapPresheaf.naturality i.op)

/-- **The zero scheme is unchanged by an isomorphism of invertible modules.** -/
theorem zeroScheme_congr_iso {L L' : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
    (e : L ≅ L') (s : Γ(L, ⊤)) :
    zeroScheme X L' (Scheme.Modules.Hom.app e.hom ⊤ s) = zeroScheme X L s := by
  unfold zeroScheme
  congr 1
  funext U
  rw [← homApp_map]
  refine le_antisymm (span_eval_le_span_eval _ _ fun φ => ⟨φ ∘ₗ homAppLinear e.hom U.1, rfl⟩)
    (span_eval_le_span_eval _ _ fun φ => ⟨φ ∘ₗ homAppLinear e.inv U.1, ?_⟩)
  show _ = φ (e.inv.app U.1 (e.hom.app U.1 _))
  congr 1
  have h := congrArg (fun g => (Scheme.Modules.Hom.app g U.1).hom
    (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s)) e.hom_inv_id
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h
  exact h.symm

/-- **An ideal sheaf is determined on an open cover.** Two ideal sheaves whose inverse images
agree on every member of an open cover are equal. -/
theorem IdealSheafData.ext_of_comap_eq {I J : X.IdealSheafData} {ι : Type*} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (h : ∀ i, I.comap (U i).ι = J.comap (U i).ι) : I = J := by
  let V : (Σ i, (U i).toScheme.affineOpens) → X.affineOpens := fun p =>
    ⟨(U p.1).ι ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion _⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top V ?_ fun p => ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := TopologicalSpace.Opens.mem_iSup.1 (hU ▸ trivial)
    obtain ⟨W, hxW⟩ : ∃ W : (U i).toScheme.affineOpens, (⟨x, hi⟩ : U i) ∈ W.1 := by
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
        (U i).toScheme.isBasis_affineOpens.exists_subset_of_mem_open
          (Set.mem_univ (⟨x, hi⟩ : U i)) isOpen_univ
      exact ⟨⟨W, hW⟩, hxW⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, W⟩, ⟨⟨x, hi⟩, hxW, rfl⟩⟩
  · have h1 := congrArg (fun K : (U p.1).toScheme.IdealSheafData => K.ideal p.2) (h p.1)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h1
    have h2 := congrArg (Ideal.comap ((U p.1).ι.appIso p.2.1).hom.hom) h1
    simp only [Ideal.comap_comap] at h2
    have hid : ((U p.1).ι.appIso p.2.1).inv.hom.comp ((U p.1).ι.appIso p.2.1).hom.hom =
        RingHom.id _ := by
      rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
    rwa [hid, Ideal.comap_id, Ideal.comap_id] at h2

/-- **The zero section does not cut out an effective Cartier divisor** on a nonempty scheme:
the defining ideal of its zero scheme is zero, and zero is a nonzerodivisor only in the zero
ring. -/
theorem ne_zero_of_isEffectiveCartierDivisor_zeroScheme [Nonempty X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (h : IsEffectiveCartierDivisor (zeroScheme X L s)) : s ≠ 0 := by
  rintro rfl
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hU, hxU, f, hf, hgen⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor _ h x
  have hbot : (zeroScheme X L 0).ideal ⟨U, hU⟩ = ⊥ := by
    rw [zeroScheme_ideal, eq_bot_iff, Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    simp
  rw [hbot, eq_comm, Ideal.span_singleton_eq_bot] at hgen
  subst hgen
  have hsub : Subsingleton Γ(X, U) :=
    subsingleton_of_forall_eq 0 fun a => hf.left (show 0 * a = 0 * 0 by simp)
  have : IsEmpty (Spec Γ(X, U)) := inferInstanceAs (IsEmpty (PrimeSpectrum Γ(X, U)))
  exact IsEmpty.false (hU.isoSpec.hom.base ⟨x, hxU⟩)

end Stacks.Divisors
