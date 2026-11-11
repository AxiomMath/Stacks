module

public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraizationTower
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalNeighborhoodTopology

/-!
# The adic tower of the formal neighbourhood is cartesian

Let `D` be an ideal sheaf on a scheme `X`, `A = lim Γ(Cₙ, 𝒪)` the ring of formal functions along
the subscheme it cuts out, `I` an ideal of `A` and `M : ℕ → ℕ` monotone. The adic tower
`Xₙ = C_{M n} ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)` of
`AlgebraicGeometry.Scheme.IdealSheafData.adicTower` is a tower over the adic thickenings of
`Spec A`. This file shows that its squares are cartesian,

`Xₙ ≅ Xₙ₊₁ ×_{Spec A ⧸ Iⁿ⁺²} Spec (A ⧸ Iⁿ⁺¹)`,

as soon as `D^{M n + 1}` dies on `C_{M (n + 1)} ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)`, in the affine-local
form `D(V)^{M n + 1} ⊆ Iⁿ⁺¹ · Γ(X, V) + D(V)^{M (n + 1) + 1}`. For a curve with positive conormal
bundle and `I = 𝔪` this holds for `M n = (N + 1) (n + 1)`, by the cofinality of the `𝔪`-adic
and `D`-adic topologies
(`AlgebraicGeometry.Scheme.IdealSheafData.IsPositiveConormal.pow_le_comap_map_maximalIdeal_pow`).
These are the cartesian squares in the hypotheses of Grothendieck's algebraization theorem
(Stacks 089A).

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.pow_le_ker_comp_subschemeι`: a morphism into the
  `N`-th thickening whose global sections kill the projections of an ideal `J` of `A` factors, on
  `X`, through the `m`-th thickening when `D(V)^{m+1} ⊆ J · Γ(X, V) + D(V)^{N+1}`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isIso_pullbackMap_thickeningInclusion`: the closed
  immersion `Cₘ ×_A A ⧸ Iⁿ⁺¹ ⟶ C_N ×_A A ⧸ Iⁿ⁺¹` is then an isomorphism.
* `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_adicTowerSucc`: the squares of the adic
  tower are cartesian.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsPositiveConormal.isPullback_adicTowerSucc`: the
  same for the `𝔪`-adic tower `C_{(N+1)(n+1)} ×_A A ⧸ 𝔪ⁿ⁺¹` of a curve with positive conormal
  bundle `L` such that `L^{N+1}` is globally generated.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- On global sections, `Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec A` kills `Iⁿ⁺¹`. -/
theorem adicThickeningι_appTop_ΓSpecIso_inv_eq_zero (A : Type u) [CommRing A] (I : Ideal A)
    (n : ℕ) {a : A} (ha : a ∈ I ^ (n + 1)) :
    (adicThickeningι A I n).appTop ((Scheme.ΓSpecIso (.of A)).inv a) = 0 := by
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.ofHom_apply,
    Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero] at h
  exact h.symm

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- On global sections, `Cₙ ⟶ Spec A` is the projection `A ⟶ Γ(Cₙ, 𝒪)`. -/
theorem ΓSpecIso_inv_comp_thickeningToSpec_appTop (n : ℕ) :
    (Scheme.ΓSpecIso (.of (formalNeighborhoodRing D))).inv ≫ (thickeningToSpec D n).appTop =
      CommRingCat.ofHom (formalNeighborhoodProjection D n) := by
  simp only [thickeningToSpec, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  exact (congrArg (_ ≫ ·)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (formalNeighborhoodProjection D n)))).trans
    (Iso.inv_hom_id_assoc _ _)

/-- On global sections, `Cₙ ⟶ Spec A` is the projection `A ⟶ Γ(Cₙ, 𝒪)`, elementwise. -/
theorem thickeningToSpec_appTop_ΓSpecIso_inv (n : ℕ) (a : formalNeighborhoodRing D) :
    (thickeningToSpec D n).appTop ((Scheme.ΓSpecIso (.of (formalNeighborhoodRing D))).inv a) =
      formalNeighborhoodProjection D n a := by
  rw [← CommRingCat.comp_apply, ΓSpecIso_inv_comp_thickeningToSpec_appTop]
  rfl

/-- **A morphism into a thickening killing an ideal of `A` lands in a smaller thickening, over an
affine open.** Let `f : T ⟶ C_N` be a morphism whose map on global sections kills the projections
to `Γ(C_N, 𝒪)` of an ideal `J` of `A`. If `D(V)^{m+1} ⊆ J · Γ(X, V) + D(V)^{N+1}` over an affine
open `V` of `X`, then `D(V)^{m+1}` is killed by `T ⟶ C_N ⟶ X` over `V`. -/
theorem pow_le_ker_app_comp_subschemeι {m N : ℕ} (J : Ideal (formalNeighborhoodRing D))
    {V : X.affineOpens}
    (hcof : D.ideal V ^ (m + 1) ≤
      Ideal.comap (Ideal.Quotient.mk (D.ideal V ^ (N + 1)))
        (Ideal.map (formalNeighborhoodChart D V N) J))
    {T : Scheme.{u}} (f : T ⟶ thickening D N)
    (hf : ∀ a ∈ J, f.appTop (formalNeighborhoodProjection D N a) = 0) :
    D.ideal V ^ (m + 1) ≤ RingHom.ker ((f ≫ (D ^ (N + 1)).subschemeι).app V.1).hom := by
  intro b hb
  have h1 := hcof hb
  rw [Ideal.mem_comap] at h1
  let χ : Γ(X, V.1) ⧸ D.ideal V ^ (N + 1) →+* Γ(T, f ⁻¹ᵁ thickeningChart D V N) :=
    (f.app (thickeningChart D V N)).hom.comp (thickeningChartEquiv D V N).toRingHom
  have hχ : ∀ a ∈ J, χ (formalNeighborhoodChart D V N a) = 0 := by
    intro a ha
    simp only [χ, formalNeighborhoodChart, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    rw [thickeningChartRestrict, ← CommRingCat.comp_apply, Scheme.Hom.naturality,
      CommRingCat.comp_apply]
    change (T.presheaf.map _).hom (f.appTop (formalNeighborhoodProjection D N a)) = 0
    rw [hf a ha, map_zero]
  have hle : Ideal.map (χ.comp (formalNeighborhoodChart D V N)) J ≤ ⊥ :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => by
      simpa only [Ideal.mem_comap, RingHom.comp_apply, Ideal.mem_bot] using hχ a ha
  have h2 : χ (Ideal.Quotient.mk _ b) = 0 := by
    have h3 := Ideal.mem_map_of_mem χ h1
    rw [Ideal.map_map] at h3
    simpa only [Ideal.mem_bot] using hle h3
  rw [RingHom.mem_ker]
  have h4 : ((f ≫ (D ^ (N + 1)).subschemeι).app V.1).hom b = χ (Ideal.Quotient.mk _ b) := by
    simp only [χ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      thickeningChartEquiv_mk]
    rfl
  exact h4.trans h2

/-- **A morphism into a thickening killing an ideal of `A` lands in a smaller thickening.** Let
`f : T ⟶ C_N` be a quasi-compact morphism whose map on global sections kills the projections to
`Γ(C_N, 𝒪)` of an ideal `J` of `A`. If `D(V)^{m+1} ⊆ J · Γ(X, V) + D(V)^{N+1}` over every member
`V` of an affine open cover of `X`, then `D^{m+1}` lies in the kernel of `T ⟶ C_N ⟶ X`. -/
theorem pow_le_ker_comp_subschemeι {m N : ℕ} (J : Ideal (formalNeighborhoodRing D))
    {ι : Type*} (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤)
    (hcof : ∀ i, D.ideal (U i) ^ (m + 1) ≤
      Ideal.comap (Ideal.Quotient.mk (D.ideal (U i) ^ (N + 1)))
        (Ideal.map (formalNeighborhoodChart D (U i) N) J))
    {T : Scheme.{u}} (f : T ⟶ thickening D N) [QuasiCompact f]
    (hf : ∀ a ∈ J, f.appTop (formalNeighborhoodProjection D N a) = 0) :
    D ^ (m + 1) ≤ (f ≫ (D ^ (N + 1)).subschemeι).ker := by
  refine le_of_iSup_eq_top U hU fun i => ?_
  rw [Scheme.Hom.ker_apply, ideal_pow, Pi.pow_apply]
  exact pow_le_ker_app_comp_subschemeι D J (hcof i) f hf

/-- **The cofinality condition is empty away from `C`**: over an affine open `V` with
`D(V) = Γ(X, V)`, every `D(V)^{m+1}` lies in `J · Γ(X, V) + D(V)^{N+1}`. -/
theorem pow_le_comap_map_formalNeighborhoodChart_of_ideal_eq_top {V : X.affineOpens}
    (hV : D.ideal V = ⊤) (m N : ℕ) (J : Ideal (formalNeighborhoodRing D)) :
    D.ideal V ^ (m + 1) ≤ Ideal.comap (Ideal.Quotient.mk (D.ideal V ^ (N + 1)))
      (Ideal.map (formalNeighborhoodChart D V N) J) := fun b _ => by
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (by rw [hV, Ideal.top_pow]; trivial)]
  exact zero_mem _

variable (I : Ideal (formalNeighborhoodRing D))

/-- A scheme over `C_N` whose map to `Spec A` factors through `Spec A ⧸ J` kills, on global
sections, the projections of `J`. -/
theorem appTop_formalNeighborhoodProjection_eq_zero {N n : ℕ} {T : Scheme.{u}}
    (u : T ⟶ thickening D N) (v : T ⟶ adicThickening (formalNeighborhoodRing D) I n)
    (huv : u ≫ thickeningToSpec D N = v ≫ adicThickeningι (formalNeighborhoodRing D) I n)
    {a : formalNeighborhoodRing D} (ha : a ∈ I ^ (n + 1)) :
    u.appTop (formalNeighborhoodProjection D N a) = 0 := by
  have key : CommRingCat.ofHom (formalNeighborhoodProjection D N) ≫ u.appTop =
      (Scheme.ΓSpecIso (.of (formalNeighborhoodRing D))).inv ≫
        (adicThickeningι (formalNeighborhoodRing D) I n).appTop ≫ v.appTop := by
    rw [← ΓSpecIso_inv_comp_thickeningToSpec_appTop, Category.assoc, ← Scheme.Hom.comp_appTop,
      huv, Scheme.Hom.comp_appTop]
  have h2 := ConcreteCategory.congr_hom key a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply,
    CommRingCat.ofHom_apply, adicThickeningι_appTop_ΓSpecIso_inv_eq_zero _ I n ha, map_zero] at h2
  exact h2

/-- **The closed immersion `Cₘ ×_A A ⧸ Iⁿ⁺¹ ⟶ C_N ×_A A ⧸ Iⁿ⁺¹` is an isomorphism** when
`D(V)^{m+1} ⊆ Iⁿ⁺¹ · Γ(X, V) + D(V)^{N+1}` over every member `V` of an affine open cover of `X`:
then `D^{m+1}` dies on `C_N ×_A A ⧸ Iⁿ⁺¹`, which therefore lies in `Cₘ`. -/
theorem isIso_pullbackMap_thickeningInclusion {m N n : ℕ} (h : m ≤ N)
    {ι : Type*} (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤)
    (hcof : ∀ i, D.ideal (U i) ^ (m + 1) ≤
      Ideal.comap (Ideal.Quotient.mk (D.ideal (U i) ^ (N + 1)))
        (Ideal.map (formalNeighborhoodChart D (U i) N) (I ^ (n + 1)))) :
    IsIso (pullback.map (thickeningToSpec D m) (adicThickeningι (formalNeighborhoodRing D) I n)
      (thickeningToSpec D N) (adicThickeningι (formalNeighborhoodRing D) I n)
      (thickeningInclusion D h) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, thickeningInclusion_thickeningToSpec])
      (by rw [Category.comp_id, Category.id_comp])) := by
  have hker := pow_le_ker_comp_subschemeι D (I ^ (n + 1)) U hU hcof
    (pullback.fst (thickeningToSpec D N) (adicThickeningι (formalNeighborhoodRing D) I n))
    (fun a ha => appTop_formalNeighborhoodProjection_eq_zero D I _ _ pullback.condition ha)
  let g : pullback (thickeningToSpec D N) (adicThickeningι (formalNeighborhoodRing D) I n) ⟶
      thickening D m :=
    IsClosedImmersion.lift (D ^ (m + 1)).subschemeι
      (pullback.fst (thickeningToSpec D N) (adicThickeningι (formalNeighborhoodRing D) I n) ≫
        (D ^ (N + 1)).subschemeι)
      (by rwa [ker_subschemeι])
  have hg₀ : g ≫ (D ^ (m + 1)).subschemeι =
      pullback.fst (thickeningToSpec D N) (adicThickeningι (formalNeighborhoodRing D) I n) ≫
        (D ^ (N + 1)).subschemeι :=
    IsClosedImmersion.lift_fac _ _ _
  have hg : g ≫ thickeningInclusion D h =
      pullback.fst (thickeningToSpec D N) (adicThickeningι (formalNeighborhoodRing D) I n) := by
    rw [← cancel_mono (D ^ (N + 1)).subschemeι, Category.assoc, thickeningInclusion,
      inclusion_subschemeι, hg₀]
  have hw : g ≫ thickeningToSpec D m =
      pullback.snd (thickeningToSpec D N) (adicThickeningι (formalNeighborhoodRing D) I n) ≫
        adicThickeningι (formalNeighborhoodRing D) I n := by
    rw [← thickeningInclusion_thickeningToSpec D h, reassoc_of% hg, pullback.condition]
  let e := pullback.lift (f := thickeningToSpec D m)
    (g := adicThickeningι (formalNeighborhoodRing D) I n) g (pullback.snd _ _) hw
  have he₁ : e ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  have he₂ : e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  refine ⟨⟨e, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · rw [← cancel_mono (D ^ (m + 1)).subschemeι, Category.assoc, Category.assoc,
        reassoc_of% he₁, hg₀, pullback.lift_fst_assoc, Category.assoc, thickeningInclusion,
        inclusion_subschemeι, Category.id_comp]
    · rw [Category.assoc, he₂, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, reassoc_of% he₁, hg, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, he₂, Category.id_comp]

variable {M : ℕ → ℕ} (hM : Monotone M)

/-- **The squares of the adic tower are cartesian**:
`Cₘ₍ₙ₎ ×_A A ⧸ Iⁿ⁺¹ ≅ (Cₘ₍ₙ₊₁₎ ×_A A ⧸ Iⁿ⁺²) ×_{A ⧸ Iⁿ⁺²} A ⧸ Iⁿ⁺¹`, provided
`D(V)^{M n + 1} ⊆ Iⁿ⁺¹ · Γ(X, V) + D(V)^{M (n + 1) + 1}` over every member `V` of an affine open
cover of `X`. -/
theorem isPullback_adicTowerSucc {ι : Type*} (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤)
    (hcof : ∀ (n : ℕ) (i : ι), D.ideal (U i) ^ (M n + 1) ≤
      Ideal.comap (Ideal.Quotient.mk (D.ideal (U i) ^ (M (n + 1) + 1)))
        (Ideal.map (formalNeighborhoodChart D (U i) (M (n + 1))) (I ^ (n + 1))))
    (n : ℕ) :
    IsPullback (adicTowerSucc D I hM n) (adicTowerToThickening D I M n)
      (adicTowerToThickening D I M (n + 1))
      (adicThickeningSucc (formalNeighborhoodRing D) I n) := by
  have hiso := isIso_pullbackMap_thickeningInclusion D I (hM (Nat.le_succ n)) U hU (hcof n)
  have outer : IsPullback (adicTowerSucc D I hM n ≫ adicTowerToThickeningOfD D I M (n + 1))
      (adicTowerToThickening D I M n) (thickeningToSpec D (M (n + 1)))
      (adicThickeningSucc (formalNeighborhoodRing D) I n ≫
        adicThickeningι (formalNeighborhoodRing D) I (n + 1)) := by
    rw [adicTowerSucc_adicTowerToThickeningOfD, adicThickeningSucc_ι]
    exact IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, thickeningInclusion_thickeningToSpec, pullback.condition]⟩
      (@asIso _ _ _ _ _ hiso) (pullback.lift_fst _ _ _)
      ((pullback.lift_snd _ _ _).trans (Category.comp_id _))
  exact IsPullback.of_right outer (adicTowerSucc_adicTowerToThickening D I hM n)
    (IsPullback.of_hasPullback _ _)

/-- The thickenings `C_{(N + 1)(n + 1)}` used for the `𝔪`-adic tower of a curve whose conormal
power `L^{N+1}` is globally generated. -/
abbrev positiveConormalTowerIndex (N n : ℕ) : ℕ := (N + 1) * (n + 1)

/-- The indices `(N + 1)(n + 1)` increase with `n`. -/
theorem monotone_positiveConormalTowerIndex (N : ℕ) : Monotone (positiveConormalTowerIndex N) :=
  fun _ _ h => Nat.mul_le_mul_left _ (Nat.succ_le_succ h)

variable {D}

open Stacks.Divisors in
/-- **Cofinality along the `𝔪`-adic tower.** For a curve with positive conormal bundle `L` such
that `L^{N+1}` is globally generated, the thickenings `M n = (N + 1)(n + 1)` satisfy
`D(V)^{M n + 1} ⊆ 𝔪ⁿ⁺¹ Γ(X, V) + D(V)^{M (n + 1) + 1}` on every affine open `V`. -/
theorem IsPositiveConormal.pow_le_comap_map_positiveConormalTowerIndex
    [IsEffectiveCartierDivisor D] {c : ℕ} (hD : IsPositiveConormal D c) {N : ℕ}
    (hgg : ∀ V : X.affineOpens, D.ideal V ^ (N + 1) ≤
      Ideal.span (chartGlobalSymbols D V N) ⊔ D.ideal V ^ (N + 2))
    (n : ℕ) (V : X.affineOpens) :
    letI := hD.isLocalRing
    D.ideal V ^ (positiveConormalTowerIndex N n + 1) ≤
      Ideal.comap (Ideal.Quotient.mk (D.ideal V ^ (positiveConormalTowerIndex N (n + 1) + 1)))
        (Ideal.map (formalNeighborhoodChart D V (positiveConormalTowerIndex N (n + 1)))
          (IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ^ (n + 1))) :=
  (Ideal.pow_le_pow_right (by simp [positiveConormalTowerIndex])).trans
    (hD.pow_le_comap_map_maximalIdeal_pow hgg _ (n + 1) V)

open Stacks.Divisors in
/-- **The `𝔪`-adic tower of a curve with positive conormal bundle is cartesian.** Let `C ⊆ X` be
an effective Cartier divisor with positive conormal bundle `L` (in the sense of
`AlgebraicGeometry.Scheme.IdealSheafData.IsPositiveConormal`) such that `L^{N+1}` is generated
by its global sections. With `𝔪` the maximal ideal of `A = lim Γ(Cₙ, 𝒪)` and
`Xₙ = C_{(N+1)(n+1)} ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)`, the squares
`Xₙ ⟶ Xₙ₊₁` over `Spec (A ⧸ 𝔪ⁿ⁺¹) ⟶ Spec (A ⧸ 𝔪ⁿ⁺²)` are cartesian. -/
theorem IsPositiveConormal.isPullback_adicTowerSucc [IsEffectiveCartierDivisor D] {c : ℕ}
    (hD : IsPositiveConormal D c) {N : ℕ}
    (hgg : ∀ V : X.affineOpens, D.ideal V ^ (N + 1) ≤
      Ideal.span (chartGlobalSymbols D V N) ⊔ D.ideal V ^ (N + 2))
    (n : ℕ) :
    letI := hD.isLocalRing
    IsPullback
      (adicTowerSucc D (IsLocalRing.maximalIdeal _) (monotone_positiveConormalTowerIndex N) n)
      (adicTowerToThickening D (IsLocalRing.maximalIdeal _) (positiveConormalTowerIndex N) n)
      (adicTowerToThickening D (IsLocalRing.maximalIdeal _) (positiveConormalTowerIndex N) (n + 1))
      (adicThickeningSucc (formalNeighborhoodRing D) (IsLocalRing.maximalIdeal _) n) := by
  let _ := hD.isLocalRing
  exact Scheme.IdealSheafData.isPullback_adicTowerSucc D _ (monotone_positiveConormalTowerIndex N)
    (fun V : X.affineOpens => V) (iSup_affineOpens_eq_top X)
    (hD.pow_le_comap_map_positiveConormalTowerIndex hgg) n

end Scheme.IdealSheafData

end AlgebraicGeometry

end
