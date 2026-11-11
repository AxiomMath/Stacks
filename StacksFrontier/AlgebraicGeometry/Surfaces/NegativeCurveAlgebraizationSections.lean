module

public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraization
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme

/-!
# Global functions on the algebraization of the formal neighbourhood

Let `A` be a Noetherian local ring, `J ⊆ 𝔪` an ideal and `f : Y ⟶ Spec A` universally closed with
`Y` locally Noetherian. A global function on `Y` vanishing on every `Y ×_{Spec A} Spec (A ⧸ Jⁿ⁺¹)`
vanishes (Krull's intersection theorem at the points of the closed fibre, to which every point of
`Y` specialises).

Applied to the algebraization `Y ⟶ Spec A` of the adic tower
`Xₙ = C_{M n} ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)` of
`AlgebraicGeometry.Scheme.IdealSheafData.exists_isProper_algebraization`, this shows that
`A ⟶ Γ(Y, 𝒪_Y)` is bijective: `A` is the ring `lim Γ(Xₙ, 𝒪)` of compatible functions on the tower,
because the `Xₙ` are pinched between the thickenings `Cₙ ⊆ Xₙ ⊆ C_{M n} ⊆ X_{M n}`.

## Main results

* `AlgebraicGeometry.eq_zero_of_forall_pullbackFst_appTop_eq_zero`: the vanishing statement.
* `AlgebraicGeometry.Scheme.IdealSheafData.bijective_adicTowerFunctions`: `A ≅ lim Γ(Xₙ, 𝒪)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.bijective_appTop_of_isPullback`: `A ≅ Γ(Y, 𝒪_Y)`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

section Krull

open Stacks.Cohomology.FormalFunctions

variable {A : Type u} [CommRing A] [IsLocalRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
  (J : Ideal A)

/-- **Functions vanishing on all the thickenings `Y ×_A A ⧸ Jⁿ⁺¹` have zero germ along the closed
fibre** (Krull's intersection theorem). Let `J ⊆ 𝔪` and `Y` locally Noetherian. If a global
function `s` on `Y` vanishes on every `Y ×_{Spec A} Spec (A ⧸ Jⁿ⁺¹)`, its germ at every point over
the closed point of `Spec A` vanishes. -/
theorem germ_eq_zero_of_forall_pullbackFst_appTop_eq_zero [IsLocallyNoetherian Y]
    (hJ : J ≤ maximalIdeal A) (s : Γ(Y, ⊤))
    (hs : ∀ n, (pullback.fst f (adicThickeningι A J n)).appTop s = 0)
    (y : Y) (hy : f y = closedPoint A) : Y.presheaf.germ ⊤ y trivial s = 0 := by
  obtain ⟨_, ⟨U', hU', rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let U : Y.affineOpens := ⟨U', hU'⟩
  change y ∈ U.1 at hyU
  let res : Γ(Y, ⊤) ⟶ Γ(Y, U.1) := Y.presheaf.map (homOfLE le_top).op
  let ψ : A →+* Γ(Y, U.1) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ res).hom
  set b := res s with hb
  -- `b` lies in every power of `J Γ(Y, U)`
  have hpow : ∀ n, b ∈ Ideal.map ψ J ^ (n + 1) := by
    intro n
    let := IsClosedImmersion.spec_of_quotient_mk (R := .of A) (J ^ (n + 1))
    have hker : b ∈ (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (J ^ (n + 1)))))).ker.ideal U := by
      rw [Scheme.Hom.ker_apply, RingHom.mem_ker, hb]
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
      change (Limits.pullback f _).presheaf.map _
        ((pullback.fst f (adicThickeningι A J n)).appTop s) = 0
      rw [hs n, map_zero]
    rw [← Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst,
      baseIdealSheaf_ideal, baseIdeal, Ideal.map_map, Ideal.map_pow] at hker
    exact hker
  have hinf : b ∈ (⨅ i : ℕ, Ideal.map ψ J ^ i • ⊤ : Submodule Γ(Y, U.1) Γ(Y, U.1)) := by
    refine Submodule.mem_iInf _ |>.mpr fun i => ?_
    rw [smul_eq_mul, Ideal.mul_top]
    cases i with
    | zero => simp
    | succ i => exact hpow i
  have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨⟨r, hr⟩, hrb⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff _ b).mp hinf
  -- the germ of `r` is not a unit, `y` lying over the closed point
  have hmax : Ideal.map ψ J ≤
      (maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ U.1 y hyU).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff,
      ← Scheme.mem_basicOpen _ _ y hyU]
    intro hmem
    have h1 : y ∈ Y.basicOpen (f.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) := by
      have h2 : ψ a = res (f.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) := rfl
      rw [h2, Scheme.basicOpen_res] at hmem
      exact hmem.2
    have h3 : y ∈ f ⁻¹ᵁ (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) := by
      rw [Scheme.preimage_basicOpen]
      exact h1
    rw [basicOpen_eq_of_affine] at h3
    have h4 : a ∉ (f y).asIdeal := h3
    rw [hy] at h4
    exact h4 (hJ ha)
  have hunit : IsUnit (Y.presheaf.germ U.1 y hyU (1 - r)) := by
    rw [map_sub, map_one]
    exact isUnit_one_sub_self_of_mem_nonunits _ (hmax hr)
  have hzero : Y.presheaf.germ U.1 y hyU (1 - r) * Y.presheaf.germ U.1 y hyU b = 0 := by
    rw [← map_mul, sub_mul, one_mul]
    rw [show r * b = b from hrb, sub_self, map_zero]
  have hb0 : Y.presheaf.germ U.1 y hyU b = 0 := (hunit.mul_right_eq_zero).mp hzero
  rw [hb, TopCat.Presheaf.germ_res_apply] at hb0
  exact hb0

/-- **A global function vanishing on all the thickenings `Y ×_A A ⧸ Jⁿ⁺¹` vanishes**, for `Y`
locally Noetherian and universally closed over the local ring `A` and `J ⊆ 𝔪`: every point of `Y`
specialises to a point of the closed fibre, where the germ vanishes by
`AlgebraicGeometry.germ_eq_zero_of_forall_pullbackFst_appTop_eq_zero`. -/
theorem eq_zero_of_forall_pullbackFst_appTop_eq_zero [IsLocallyNoetherian Y] [UniversallyClosed f]
    (hJ : J ≤ maximalIdeal A) (s : Γ(Y, ⊤))
    (hs : ∀ n, (pullback.fst f (adicThickeningι A J n)).appTop s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext Y.sheaf ⊤ s 0 fun y _ => ?_
  rw [map_zero]
  have hcl : IsClosed (f '' closure {y}) := f.isClosedMap _ isClosed_closure
  have hmem : closedPoint A ∈ f '' closure {y} :=
    (specializes_closedPoint (f y)).mem_closed hcl ⟨y, subset_closure rfl, rfl⟩
  obtain ⟨y', hy'cl, hy'⟩ := hmem
  have h0 := germ_eq_zero_of_forall_pullbackFst_appTop_eq_zero f J hJ s hs y' hy'
  obtain ⟨W, hW, iU, iV, e⟩ := Y.presheaf.germ_eq (U := ⊤) (V := ⊤) y' trivial trivial s 0
    (h0.trans (map_zero _).symm)
  have hyW : y ∈ W := (specializes_iff_mem_closure.mpr hy'cl).mem_open W.2 hW
  have e' := congrArg (Y.presheaf.germ W y hyW) e
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, map_zero] at e'
  exact e'

end Krull

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (I : Ideal (formalNeighborhoodRing D))
  {M : ℕ → ℕ}

/-! ### Morphisms into the adic tower -/

/-- Morphisms into `Xₙ = C_{M n} ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)` are determined by their components in
`C_{M n}`, `Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec A` being a monomorphism. -/
theorem adicTower_hom_ext {T : Scheme.{u}} {n : ℕ} {u v : T ⟶ adicTower D I M n}
    (h : u ≫ adicTowerToThickeningOfD D I M n = v ≫ adicTowerToThickeningOfD D I M n) :
    u = v := by
  refine pullback.hom_ext h ?_
  rw [← cancel_mono (adicThickeningι (formalNeighborhoodRing D) I n), Category.assoc,
    Category.assoc, ← pullback.condition, reassoc_of% h]

/-- Inclusions of thickenings compose. -/
@[reassoc]
theorem thickeningInclusion_comp {i j k : ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) :
    thickeningInclusion D h₁ ≫ thickeningInclusion D h₂ = thickeningInclusion D (h₁.trans h₂) := by
  rw [thickeningInclusion, thickeningInclusion, inclusion_comp]
  rfl

/-- The inclusion of a thickening into itself is the identity. -/
theorem thickeningInclusion_refl (i : ℕ) : thickeningInclusion D (le_refl i) = 𝟙 _ :=
  inclusion_id _

/-- The thickening `Cₘ` inside `Xₙ`, for `m ≤ M n` and `Iⁿ⁺¹` vanishing on `Cₘ`. -/
def thickeningToAdicTower {m n : ℕ} (hmn : m ≤ M n)
    (hJ : I ^ (n + 1) ≤ RingHom.ker (formalNeighborhoodProjection D m)) :
    thickening D m ⟶ adicTower D I M n :=
  pullback.lift (thickeningInclusion D hmn)
    (adicThickeningLift _ I n (formalNeighborhoodProjection D m) hJ)
    (by rw [thickeningInclusion_thickeningToSpec, adicThickeningLift_ι]; rfl)

/-- `Cₘ ⟶ Xₙ ⟶ C_{M n}` is the inclusion. -/
@[reassoc (attr := simp)]
theorem thickeningToAdicTower_fst {m n : ℕ} (hmn : m ≤ M n)
    (hJ : I ^ (n + 1) ≤ RingHom.ker (formalNeighborhoodProjection D m)) :
    thickeningToAdicTower D I hmn hJ ≫ adicTowerToThickeningOfD D I M n =
      thickeningInclusion D hmn :=
  pullback.lift_fst _ _ _

/-! ### The ring of functions on the tower -/

variable (hM : Monotone M)

/-- The ring `lim Γ(Xₙ, 𝒪)` of compatible functions on the adic tower. -/
def adicTowerFunctions : Subring (∀ n, Γ(adicTower D I M n, ⊤)) where
  carrier := {x | ∀ n, (adicTowerSucc D I hM n).appTop (x (n + 1)) = x n}
  zero_mem' n := map_zero _
  one_mem' n := map_one _
  add_mem' ha hb n := by simp [map_add, ha n, hb n]
  mul_mem' ha hb n := by simp [map_mul, ha n, hb n]
  neg_mem' ha n := by simp [map_neg, ha n]

/-- The function on `Xₙ` of a formal function: its restriction along `Xₙ ⟶ C_{M n}`. -/
theorem adicTowerSucc_appTop_fst_appTop (n : ℕ) (a : formalNeighborhoodRing D) :
    (adicTowerSucc D I hM n).appTop ((adicTowerToThickeningOfD D I M (n + 1)).appTop
      (formalNeighborhoodProjection D (M (n + 1)) a)) =
      (adicTowerToThickeningOfD D I M n).appTop (formalNeighborhoodProjection D (M n) a) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    adicTowerSucc_adicTowerToThickeningOfD, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  congr 1
  exact thickeningRestrictionLE_formalNeighborhoodProjection D (hM (Nat.le_succ n)) a

/-- **Formal functions restrict to the tower**: `A ⟶ lim Γ(Xₙ, 𝒪)`. -/
def toAdicTowerFunctions : formalNeighborhoodRing D →+* adicTowerFunctions D I hM :=
  (RingHom.pi fun n => ((adicTowerToThickeningOfD D I M n).appTop.hom).comp
    (formalNeighborhoodProjection D (M n))).codRestrict _ fun a n =>
      adicTowerSucc_appTop_fst_appTop D I hM n a

/-- The components of `A ⟶ lim Γ(Xₙ, 𝒪)`. -/
@[simp]
theorem toAdicTowerFunctions_apply (a : formalNeighborhoodRing D) (n : ℕ) :
    (toAdicTowerFunctions D I hM a : ∀ n, Γ(adicTower D I M n, ⊤)) n =
      (adicTowerToThickeningOfD D I M n).appTop (formalNeighborhoodProjection D (M n) a) :=
  rfl

variable {D I hM}

/-- Restricting along the iterated transition maps of the tower, for compatible functions. -/
theorem exists_adicTower_hom (x : adicTowerFunctions D I hM) {n m : ℕ} (hnm : n ≤ m) :
    ∃ g : adicTower D I M n ⟶ adicTower D I M m,
      g ≫ adicTowerToThickeningOfD D I M m =
        adicTowerToThickeningOfD D I M n ≫ thickeningInclusion D (hM hnm) ∧
      g.appTop ((x : ∀ n, Γ(adicTower D I M n, ⊤)) m) = (x : ∀ n, Γ(adicTower D I M n, ⊤)) n := by
  induction m, hnm using Nat.le_induction with
  | base =>
    refine ⟨𝟙 _, ?_, rfl⟩
    rw [Category.id_comp, thickeningInclusion_refl, Category.comp_id]
  | succ m hnm ih =>
    obtain ⟨g, hg, hgx⟩ := ih
    refine ⟨g ≫ adicTowerSucc D I hM m, ?_, ?_⟩
    · rw [Category.assoc, adicTowerSucc_adicTowerToThickeningOfD, reassoc_of% hg,
        thickeningInclusion_comp]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, x.2 m, hgx]

variable (D I hM)

/-- **`A` is the ring of functions on the adic tower.** If `Iⁿ⁺¹` vanishes on `Cₙ` and
`n ≤ M n` for all `n`, the restriction `A ⟶ lim Γ(Xₙ, 𝒪)` is bijective: the members of the tower
are pinched between thickenings, `Cₙ ⊆ Xₙ ⊆ C_{M n} ⊆ X_{M n}`. -/
theorem bijective_toAdicTowerFunctions
    (hIF : ∀ n, I ^ (n + 1) ≤ RingHom.ker (formalNeighborhoodProjection D n))
    (hMle : ∀ n, n ≤ M n) :
    Function.Bijective (toAdicTowerFunctions D I hM) := by
  let ι : ∀ m, thickening D m ⟶ adicTower D I M m := fun m =>
    thickeningToAdicTower D I (hMle m) (hIF m)
  have hι : ∀ m (a : formalNeighborhoodRing D), (ι m).appTop
      ((toAdicTowerFunctions D I hM a : ∀ n, Γ(adicTower D I M n, ⊤)) m) =
        formalNeighborhoodProjection D m a := by
    intro m a
    rw [toAdicTowerFunctions_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      thickeningToAdicTower_fst]
    exact thickeningRestrictionLE_formalNeighborhoodProjection D (hMle m) a
  refine ⟨(injective_iff_map_eq_zero _).mpr fun a ha => ?_, fun x => ?_⟩
  · refine Subtype.ext (funext fun m => ?_)
    have h := hι m a
    rw [ha] at h
    exact (h.symm.trans (map_zero _) :)
  · have hcomp : ∀ m, thickeningInclusion D (Nat.le_succ m) ≫ ι (m + 1) =
        ι m ≫ adicTowerSucc D I hM m := by
      intro m
      refine adicTower_hom_ext D I ?_
      rw [Category.assoc, thickeningToAdicTower_fst, Category.assoc,
        adicTowerSucc_adicTowerToThickeningOfD, thickeningToAdicTower_fst_assoc,
        thickeningInclusion_comp, thickeningInclusion_comp]
    let a : formalNeighborhoodRing D := ⟨fun m => (ι m).appTop
        ((x : ∀ n, Γ(adicTower D I M n, ⊤)) m), fun m => by
      rw [thickeningRestriction_eq_inclusion_appTop D m (pow_succ_le_pow_succ D (Nat.le_succ m))]
      change (thickeningInclusion D (Nat.le_succ m)).appTop ((ι (m + 1)).appTop _) = _
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hcomp, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, x.2 m]⟩
    refine ⟨a, Subtype.ext (funext fun n => ?_)⟩
    obtain ⟨g, hg, hgx⟩ := exists_adicTower_hom x (hMle n)
    have hgι : g = adicTowerToThickeningOfD D I M n ≫ ι (M n) :=
      adicTower_hom_ext D I (by rw [hg, Category.assoc, thickeningToAdicTower_fst])
    rw [toAdicTowerFunctions_apply]
    change (adicTowerToThickeningOfD D I M n).appTop ((ι (M n)).appTop _) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← hgι, hgx]

/-! ### Global functions on the algebraization -/

/-- **`A ⟶ Γ(Y, 𝒪_Y)` is bijective for an algebraization `Y` of the adic tower.** Let `A` be a
Noetherian local ring of formal functions, `I ⊆ 𝔪` with `Iⁿ⁺¹` vanishing on `Cₙ`, and `n ≤ M n`.
Let `fY : Y ⟶ Spec A` be proper with morphisms `kₙ : Xₙ ⟶ Y`, compatible with the transitions and
exhibiting `Xₙ` as `Y ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)` (the data produced by
`AlgebraicGeometry.Scheme.IdealSheafData.exists_isProper_algebraization`). Then
`A ⟶ Γ(Y, 𝒪_Y)` is bijective: its composite with the restriction `Γ(Y, 𝒪_Y) ⟶ lim Γ(Xₙ, 𝒪)` is
`AlgebraicGeometry.Scheme.IdealSheafData.bijective_toAdicTowerFunctions`, and the restriction is
injective by `AlgebraicGeometry.eq_zero_of_forall_pullbackFst_appTop_eq_zero`. -/
theorem bijective_appTop_of_isPullback [IsLocalRing (formalNeighborhoodRing D)]
    [IsNoetherianRing (formalNeighborhoodRing D)]
    (hImax : I ≤ maximalIdeal (formalNeighborhoodRing D))
    (hIF : ∀ n, I ^ (n + 1) ≤ RingHom.ker (formalNeighborhoodProjection D n))
    (hMle : ∀ n, n ≤ M n) {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of (formalNeighborhoodRing D)))
    [IsProper fY] (k : ∀ n, adicTower D I M n ⟶ Y)
    (hk : ∀ n, adicTowerSucc D I hM n ≫ k (n + 1) = k n)
    (hcart : ∀ n, IsPullback (k n) (adicTowerToThickening D I M n) fY
      (adicThickeningι (formalNeighborhoodRing D) I n)) :
    Function.Bijective
      ((Scheme.ΓSpecIso (.of (formalNeighborhoodRing D))).inv ≫ fY.appTop).hom := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  let φ := ((Scheme.ΓSpecIso (.of (formalNeighborhoodRing D))).inv ≫ fY.appTop).hom
  let ρ : Γ(Y, ⊤) →+* adicTowerFunctions D I hM :=
    (RingHom.pi fun n => (k n).appTop.hom).codRestrict _ fun s n => by
      change (adicTowerSucc D I hM n).appTop ((k (n + 1)).appTop s) = (k n).appTop s
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hk]
  have hρφ : ∀ a, ρ (φ a) = toAdicTowerFunctions D I hM a := by
    intro a
    refine Subtype.ext (funext fun n => ?_)
    change (k n).appTop (fY.appTop _) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, (hcart n).w,
      ← pullback.condition, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact congrArg _ (thickeningToSpec_appTop_ΓSpecIso_inv D (M n) a)
  have hρ : Function.Injective ρ := by
    refine (injective_iff_map_eq_zero ρ).mpr fun s hs => ?_
    refine eq_zero_of_forall_pullbackFst_appTop_eq_zero fY I hImax s fun n => ?_
    have hkn : (k n).appTop s = 0 := by
      have h := congrFun (congrArg Subtype.val hs) n
      exact h
    have hfst : pullback.fst fY (adicThickeningι (formalNeighborhoodRing D) I n) =
        (hcart n).isoPullback.inv ≫ k n := by
      rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_fst]
    rw [hfst]
    exact (congrArg (fun t => (hcart n).isoPullback.inv.appTop t) hkn).trans (map_zero _)
  have hΘ := bijective_toAdicTowerFunctions D I hM hIF hMle
  refine ⟨fun a b hab => hΘ.1 (by rw [← hρφ, ← hρφ, hab]), fun s => ?_⟩
  obtain ⟨a, ha⟩ := hΘ.2 (ρ s)
  exact ⟨a, hρ (by rw [hρφ, ha])⟩

variable {D}

open Stacks.Ample Stacks.Divisors in
/-- **The algebraization of the formal neighbourhood of a curve with positive conormal bundle has
`A` as ring of global functions.** In the situation of
`AlgebraicGeometry.Scheme.IdealSheafData.IsPositiveConormal.exists_isProper_algebraization`, there
is a proper `fY : Y ⟶ Spec A` algebraizing the `𝔪`-adic tower, with an ample invertible module
restricting to `𝒪_X(-C)` on the tower, such that `A ⟶ Γ(Y, 𝒪_Y)` is bijective. -/
theorem IsPositiveConormal.exists_isProper_algebraization_bijective_appTop
    [IsEffectiveCartierDivisor D] {c : ℕ} (hD : IsPositiveConormal D c) {N : ℕ}
    (hgg : ∀ V : X.affineOpens, D.ideal V ^ (N + 1) ≤
      Ideal.span (chartGlobalSymbols D V N) ⊔ D.ideal V ^ (N + 2))
    {R : CommRingCat.{u}} (f : X ⟶ Spec R) [IsProper f]
    (hC : IsAmple D.subscheme (conormalModule D)) :
    letI := hD.isLocalRing
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of (formalNeighborhoodRing D))), IsProper fY ∧
      (∃ (𝒩 : Y.Modules) (h𝒩 : IsInvertibleModule Y 𝒩), @IsAmple Y 𝒩 h𝒩) ∧
      (∃ (k : ∀ n, adicTower D (maximalIdeal _) (positiveConormalTowerIndex N) n ⟶ Y),
        (∀ n, adicTowerSucc D _ (monotone_positiveConormalTowerIndex N) n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n)
          (adicTowerToThickening D (maximalIdeal _) (positiveConormalTowerIndex N) n)
          fY (adicThickeningι (formalNeighborhoodRing D) (maximalIdeal _) n)) ∧
      Function.Bijective
        ((Scheme.ΓSpecIso (.of (formalNeighborhoodRing D))).inv ≫ fY.appTop).hom := by
  let _ := hD.isLocalRing
  have : IsNoetherianRing (formalNeighborhoodRing D) :=
    hD.isNoetherianCompleteLocalRing.isNoetherian
  obtain ⟨Y, fY, hfY, 𝒩, h𝒩, h𝒩a, k, hk, hcart, -⟩ :=
    hD.exists_isProper_algebraization hgg f hC
  have := hfY
  exact ⟨Y, fY, hfY, ⟨𝒩, h𝒩, h𝒩a⟩, ⟨k, hk, hcart⟩,
    bijective_appTop_of_isPullback D _ (monotone_positiveConormalTowerIndex N) le_rfl
      hD.maximalIdeal_pow_le_ker
      (fun n => by simp only [positiveConormalTowerIndex]; nlinarith) fY k hk hcart⟩

end Scheme.IdealSheafData

end AlgebraicGeometry

end
