module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.FromGlobalSections

/-!
# Rescaling the ring homomorphism defining a morphism to `Proj`

`AlgebraicGeometry.Proj.fromOfGlobalSections` depends on a ring homomorphism
`f : A →+* Γ(X, ⊤)`; the morphism to `Proj 𝒜` it produces is unchanged when each graded piece
`𝒜 d` is rescaled by the `d`-th power of a fixed unit of `Γ(X, ⊤)`. This is the uniqueness clause
of [Stacks, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8) for a graded ring generated in
degree one.

## Main results

* `AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit`: the morphism to `Proj 𝒜` is
  unchanged by rescaling the ring homomorphism degreewise by a unit.
* `AlgebraicGeometry.Proj.isoOfEq_hom_comp_toBasicOpenOfGlobalSections`: the same at the level of
  a single chart.
* `AlgebraicGeometry.Proj.Away_lift_comp_map_comp_algebraMap`: on the degree-zero ring `(𝒜 r)`
  the ring homomorphism and its rescaling induce the same map.
* `AlgebraicGeometry.Proj.isoOfEq_hom_comp_toSpecΓ_restrict_basicOpenIsoSpecAway_hom`: the
  canonical morphism `X_x ⟶ Spec Γ(X, ⊤)[1/x]` depends on `x` only up to a unit.
* `AlgebraicGeometry.Proj.basicOpen_unit_mul`: the nonvanishing locus of `u * x` is that of `x`.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {X : Scheme.{u}}

/-- Multiplying a global function by a unit does not change its nonvanishing locus. -/
theorem basicOpen_unit_mul (x : Γ(X, ⊤)) (u : Γ(X, ⊤)ˣ) :
    X.basicOpen ((u : Γ(X, ⊤)) * x) = X.basicOpen x := by
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit u.isUnit, top_inf_eq]

/-- **The canonical morphism `X_x ⟶ Spec Γ(X, ⊤)[1/x]` depends on `x` only up to a unit.**
Replacing `x` by `x' = u * x` leaves the morphism unchanged, except for the identification
`Γ(X, ⊤)[1/x'] ⟶ Γ(X, ⊤)[1/x]` of the two localizations, which is `IsLocalization.Away.lift`. -/
@[reassoc]
theorem isoOfEq_hom_comp_toSpecΓ_restrict_basicOpenIsoSpecAway_hom (x x' : Γ(X, ⊤))
    (hb : X.basicOpen x = X.basicOpen x')
    (hu : IsUnit (algebraMap Γ(X, ⊤) (Localization.Away x) x')) :
    (X.isoOfEq hb).hom ≫
      X.homOfLE (X.toSpecΓ_preimage_basicOpen x').ge ≫
        (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen x') ≫ (basicOpenIsoSpecAway x').hom =
      (X.homOfLE (X.toSpecΓ_preimage_basicOpen x).ge ≫
          (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen x) ≫ (basicOpenIsoSpecAway x).hom) ≫
        Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift (S := Localization.Away x') x' hu)) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x'))))]
  simp only [Category.assoc]
  rw [homOfLE_toSpecΓ_restrict_basicOpenIsoSpecAway_hom_SpecMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp,
    homOfLE_toSpecΓ_restrict_basicOpenIsoSpecAway_hom_SpecMap, Scheme.isoOfEq_hom_ι_assoc]

section Graded

variable {σ : Type*} {A : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- If `f' a = u ^ d * f a` for every `a ∈ 𝒜 d`, then on the degree-zero ring `(𝒜 r)` the two
ring homomorphisms `f` and `f'` induce the same map into `Γ(X, ⊤)[1/f r]`. -/
theorem Away_lift_comp_map_comp_algebraMap (f f' : A →+* Γ(X, ⊤)) (u : Γ(X, ⊤)ˣ)
    (hff' : ∀ (d : ℕ), ∀ a ∈ 𝒜 d, f' a = (u : Γ(X, ⊤)) ^ d * f a)
    {r : A} {n : ℕ} (hr : r ∈ 𝒜 n)
    (hu : IsUnit (algebraMap Γ(X, ⊤) (Localization.Away (f r)) (f' r))) :
    (IsLocalization.Away.lift (S := Localization.Away (f' r)) (f' r) hu).comp
        ((IsLocalization.map (M := .powers r) (T := .powers (f' r))
            (Localization.Away (f' r)) f'
            (Submonoid.powers_le.mpr (Submonoid.mem_powers _))).comp
          (algebraMap (Away 𝒜 r) (Localization.Away r))) =
      (IsLocalization.map (M := .powers r) (T := .powers (f r))
          (Localization.Away (f r)) f
          (Submonoid.powers_le.mpr (Submonoid.mem_powers _))).comp
        (algebraMap (Away 𝒜 r) (Localization.Away r)) := by
  ext z
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hr z
  simp only [RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk', map_pow]
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  have hfa : f' a = (u : Γ(X, ⊤)) ^ (m * n) * f a := by
    simpa only [smul_eq_mul] using hff' (m • n) a ha
  have hfr : f' r ^ m = (u : Γ(X, ⊤)) ^ (m * n) * f r ^ m := by
    rw [hff' n r hr, mul_pow, ← pow_mul, mul_comm n m]
  show (algebraMap Γ(X, ⊤) (Localization.Away (f r))) (f' a) =
    (algebraMap Γ(X, ⊤) (Localization.Away (f r))) (f' r ^ m) *
      IsLocalization.mk' (Localization.Away (f r)) (f a)
        (⟨f r ^ m, m, rfl⟩ : Submonoid.powers (f r))
  rw [hfa, hfr, map_mul, map_mul, mul_assoc]
  exact congrArg
    ((algebraMap Γ(X, ⊤) (Localization.Away (f r))) ((u : Γ(X, ⊤)) ^ (m * n)) * ·)
    (IsLocalization.mk'_spec' (Localization.Away (f r)) (f a)
      (⟨f r ^ m, m, rfl⟩ : Submonoid.powers (f r))).symm

/-- Rescaling the ring homomorphism degreewise by a unit does not change the chart morphism
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`. -/
@[reassoc]
theorem isoOfEq_hom_comp_toBasicOpenOfGlobalSections (f f' : A →+* Γ(X, ⊤)) (u : Γ(X, ⊤)ˣ)
    (hff' : ∀ (d : ℕ), ∀ a ∈ 𝒜 d, f' a = (u : Γ(X, ⊤)) ^ d * f a)
    {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n)
    (hb : X.basicOpen (f r) = X.basicOpen (f' r))
    (hu : IsUnit (algebraMap Γ(X, ⊤) (Localization.Away (f r)) (f' r))) :
    (X.isoOfEq hb).hom ≫ toBasicOpenOfGlobalSections 𝒜 f' rfl hn hr =
      toBasicOpenOfGlobalSections 𝒜 f rfl hn hr := by
  rw [← cancel_mono (basicOpenIsoSpec 𝒜 r hr hn).hom]
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [isoOfEq_hom_comp_toSpecΓ_restrict_basicOpenIsoSpecAway_hom_assoc (f r) (f' r) hb hu,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Away_lift_comp_map_comp_algebraMap 𝒜 f f' u hff' hr hu]

/-- **`AlgebraicGeometry.Proj.fromOfGlobalSections` is unchanged when the ring homomorphism is
rescaled degreewise by a unit.** If `u : Γ(X, ⊤)` is a unit and `f' a = u ^ d * f a` for every
`a ∈ 𝒜 d`, then `f` and `f'` define the same morphism `X ⟶ Proj 𝒜`. This is the uniqueness
clause of [Stacks, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8) for a graded ring
generated in degree one. -/
theorem fromOfGlobalSections_congr_unit (f f' : A →+* Γ(X, ⊤)) (u : Γ(X, ⊤)ˣ)
    (hff' : ∀ (d : ℕ), ∀ a ∈ 𝒜 d, f' a = (u : Γ(X, ⊤)) ^ d * f a)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f' = ⊤) :
    fromOfGlobalSections 𝒜 f hf = fromOfGlobalSections 𝒜 f' hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun i ↦ ?_
  obtain ⟨n, r, hn, hr⟩ := i
  have hb : X.basicOpen (f r) = X.basicOpen (f' r) := by
    rw [hff' n r hr, ← Units.val_pow_eq_pow_val, basicOpen_unit_mul]
  have hu : IsUnit (algebraMap Γ(X, ⊤) (Localization.Away (f r)) (f' r)) := by
    rw [hff' n r hr, map_mul]
    exact ((algebraMap Γ(X, ⊤) (Localization.Away (f r))).isUnit_map
      (u.isUnit.pow n)).mul (IsLocalization.Away.algebraMap_isUnit (f r))
  show (X.basicOpen (f r)).ι ≫ fromOfGlobalSections 𝒜 f hf =
    (X.basicOpen (f r)).ι ≫ fromOfGlobalSections 𝒜 f' hf'
  rw [basicOpen_ι_comp_fromOfGlobalSections 𝒜 f hf hn hr, ← Scheme.isoOfEq_hom_ι X hb,
    Category.assoc, basicOpen_ι_comp_fromOfGlobalSections 𝒜 f' hf' hn hr,
    isoOfEq_hom_comp_toBasicOpenOfGlobalSections_assoc 𝒜 f f' u hff' hn hr hb hu]

end Graded

end AlgebraicGeometry.Proj

end
