module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.StalkToFormalNeighborhood
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalIdempotentTower
public import StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningRestriction
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionSteinCase
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionCofinality

/-!
# The completed local ring at the image point is the ring of compatible functions

Let `f : X ⟶ Y` be a proper morphism onto a locally Noetherian scheme with `f_* 𝒪_X = 𝒪_Y`, let
`D` be an ideal sheaf on the Noetherian scheme `X` with reduced subscheme, carried by `f` to a
closed point `y`, and assume that the set-theoretic fibre `f ⁻¹ {y}` lies in the support of `D`.
Step 2 of the proof of [Stacks, Tag 0C2L] identifies the completion of `𝒪_{Y, y}` with the ring

`A = lim H⁰(Eₙ, 𝒪_{Eₙ})`

of compatible functions on the thickenings `Eₙ = (D ^ n).subscheme`
(`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing`): by the theorem on formal
functions [Stacks, Tag 02OD], `𝒪_{Y, y}^∧` is the limit of the global functions on the
infinitesimal neighbourhoods `Xₙ = X ×_Y Spec (𝒪_{Y, y}/𝔪_y ⁿ)` of the fibre, and the two towers
`(Eₙ)` and `(Xₙ)` of closed subschemes of `X` are cofinal.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningToInfinitesimal` — the morphism
  `Eₙ₊₁ ⟶ Xₙ₊₁` over `X`.
* `AlgebraicGeometry.Scheme.IdealSheafData.infinitesimalToThickening` — a morphism `Xₘ ⟶ E_K` over
  `X`, for an index `K` with `D ^ K` vanishing on `Xₘ`.
* `AlgebraicGeometry.Scheme.IdealSheafData.towerLimitToFormalNeighborhood` — the resulting
  bijection `lim Γ(Xₙ, 𝒪) ⟶ A`.
* `AlgebraicGeometry.Scheme.IdealSheafData.completionToFormalNeighborhood` — the ring map
  `𝒪_{Y, y}^∧ ⟶ A` extending `AlgebraicGeometry.Scheme.IdealSheafData.stalkToFormalNeighborhood`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.toSpecΓ_specMap_stalkToΓ_fromSpecStalk` — a morphism all of
  whose points go to `y` factors through `Spec 𝒪_{Y, y} ⟶ Y`.
* `Stacks.FormalFunctions.bijective_canonicalStalkComparison_of_isProper` — the canonical
  comparison map of [Stacks, Tag 02OD] at `p = 0` is bijective.
* `AlgebraicGeometry.Scheme.IdealSheafData.bijective_completionToFormalNeighborhood` — the ring
  map `𝒪_{Y, y}^∧ ⟶ A` is bijective.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_ringEquiv_adicCompletion_formalNeighborhoodRing`
  — in the setting of [Stacks, Tag 0C2L], `𝒪_{Y, y}^∧ ≅ A` as rings, compatibly with the maps
  from `𝒪_{Y, y}`.

## References

* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Stacks.FormalFunctions
  Stacks.IntertwinedFiltration

universe u

namespace Stacks.FormalFunctions

/-- **The canonical comparison map of [Stacks, Tag 02OD] at `p = 0` is bijective**, for a proper
morphism onto a locally Noetherian scheme. -/
public theorem bijective_canonicalStalkComparison_of_isProper {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.IsLocallyNoetherian Y]
    (y : Y) : Function.Bijective (canonicalStalkComparison f y) := by
  obtain ⟨q, hq, hnorm, hbij⟩ := isFormalFunctionsStalk_of_isProper f y
  obtain rfl : q = infinitesimalStalkRestrict f y := funext fun n ↦ LinearMap.ext fun a ↦ by
    obtain ⟨U, hy, s, rfl⟩ := exists_pushforwardStalkGerm_eq f y a
    rw [hnorm, infinitesimalStalkRestrict_germ]
  exact hbij

end Stacks.FormalFunctions

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {T Y : Scheme.{u}} (h : T ⟶ Y) (y : Y) (hy : ∀ t : T, h.base t = y)

/-- **A scheme lying over the point `y` maps through `Spec 𝒪_{Y, y}`**: a morphism `h : T ⟶ Y`
all of whose points go to `y` is `T ⟶ Spec Γ(T, 𝒪_T) ⟶ Spec 𝒪_{Y, y} ⟶ Y`, the middle arrow
being `AlgebraicGeometry.Scheme.Hom.stalkToΓ`. -/
public theorem toSpecΓ_specMap_stalkToΓ_fromSpecStalk :
    T.toSpecΓ ≫ Spec.map (stalkToΓ h y hy) ≫ Y.fromSpecStalk y = h := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    (isBasis_affineOpens Y).exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have e₁ : (⊤ : (Spec Γ(T, ⊤)).Opens) ≤
      (Spec.map (stalkToΓ h y hy) ≫ Y.fromSpecStalk y) ⁻¹ᵁ U := fun p _ ↦
    le_preimage_fromSpecStalk_of_mem y U hyU (Set.mem_univ ((Spec.map (stalkToΓ h y hy)).base p))
  have e₂ : (⊤ : T.Opens) ≤ T.toSpecΓ ⁻¹ᵁ ⊤ := le_top
  have e₃ : (⊤ : (Spec Γ(T, ⊤)).Opens) ≤ Spec.map (stalkToΓ h y hy) ⁻¹ᵁ ⊤ := le_top
  refine Stacks.Smooth.hom_ext_of_appLE hU (e₂.trans ((Opens.map T.toSpecΓ.base).map
    (homOfLE e₁)).le) (top_le_preimage_of_forall_base_eq h y hy U hyU) ?_
  rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ e₁ e₂,
    ← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ (le_preimage_fromSpecStalk_of_mem y U hyU) e₃,
    fromSpecStalk_appLE_top, appLE_top_eq_appTop, appLE_top_eq_appTop, Scheme.toSpecΓ_appTop,
    ← germ_stalkToΓ h y hy U hyU, Category.assoc, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

end Scheme.Hom

namespace Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (D : X.IdealSheafData) (f : X ⟶ Y) (y : Y)
  (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y)

/-! ### The thickenings lie in the infinitesimal neighbourhoods -/

/-- The pullback of a germ at `y` to the `(n + 1)`-st thickening vanishes if the germ lies in
`𝔪_y ^ (n + 1)`, for `D` with reduced subscheme. -/
public theorem stalkToThickening_eq_zero [IsReduced D.subscheme] (n : ℕ)
    {a : Y.presheaf.stalk y} (ha : a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)) :
    (stalkToThickening D f y hmaps n).hom a = 0 :=
  (mem_formalNeighborhoodFiltration_succ_iff D n _).1
    (stalkToFormalNeighborhood_mem_filtration D f y hmaps (n + 1) ha)

/-- The ring map `𝒪_{Y, y}/𝔪_y ^ (n + 1) ⟶ Γ(Eₙ₊₁, 𝒪)` induced by
`AlgebraicGeometry.Scheme.IdealSheafData.stalkToThickening`. -/
public def thickeningToStalkQuotient [IsReduced D.subscheme] (n : ℕ) :
    stalkQuotient y (n + 1) ⟶ Γ(thickening D n, ⊤) :=
  CommRingCat.ofHom (Ideal.Quotient.lift _ (stalkToThickening D f y hmaps n).hom
    fun _ ha ↦ stalkToThickening_eq_zero D f y hmaps n ha)

/-- `AlgebraicGeometry.Scheme.IdealSheafData.thickeningToStalkQuotient` sends the class of a germ
to its pullback to the thickening. -/
@[simp]
public theorem thickeningToStalkQuotient_mk [IsReduced D.subscheme] (n : ℕ)
    (a : Y.presheaf.stalk y) :
    (thickeningToStalkQuotient D f y hmaps n).hom (Ideal.Quotient.mk _ a) =
      (stalkToThickening D f y hmaps n).hom a :=
  rfl

/-- The quotient map `𝒪_{Y, y} ⟶ 𝒪_{Y, y}/𝔪_y ^ (n + 1)` followed by
`AlgebraicGeometry.Scheme.IdealSheafData.thickeningToStalkQuotient` is
`AlgebraicGeometry.Scheme.IdealSheafData.stalkToThickening`. -/
public theorem toStalkQuotient_comp_thickeningToStalkQuotient [IsReduced D.subscheme] (n : ℕ) :
    toStalkQuotient y (n + 1) ≫ thickeningToStalkQuotient D f y hmaps n =
      stalkToThickening D f y hmaps n :=
  CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)

/-- **`Eₙ₊₁ ⊆ Xₙ₊₁`**: the `(n + 1)`-st thickening of `D` maps to the `(n + 1)`-st infinitesimal
neighbourhood `X ×_Y Spec (𝒪_{Y, y}/𝔪_y ^ (n + 1))` of the fibre, over `X`. The second component
is the spectrum of `𝒪_{Y, y}/𝔪_y ^ (n + 1) ⟶ Γ(Eₙ₊₁, 𝒪)`. -/
public def thickeningToInfinitesimal [IsReduced D.subscheme] (n : ℕ) :
    thickening D n ⟶ infinitesimalNeighbourhood f y (n + 1) :=
  pullback.lift (D ^ (n + 1)).subschemeι
    ((thickening D n).toSpecΓ ≫ Spec.map (thickeningToStalkQuotient D f y hmaps n)) <| by
    rw [Category.assoc, infinitesimalBase, ← Spec.map_comp_assoc,
      toStalkQuotient_comp_thickeningToStalkQuotient]
    exact (Scheme.Hom.toSpecΓ_specMap_stalkToΓ_fromSpecStalk _ y
      (base_thickening_eq D f y hmaps n)).symm

/-- `Eₙ₊₁ ⟶ Xₙ₊₁` is a morphism over `X`. -/
@[reassoc (attr := simp)]
public theorem thickeningToInfinitesimal_ι [IsReduced D.subscheme] (n : ℕ) :
    thickeningToInfinitesimal D f y hmaps n ≫ infinitesimalι f y (n + 1) =
      (D ^ (n + 1)).subschemeι :=
  pullback.lift_fst _ _ _

/-- The base ring map of `Xₙ` on the germ of a function `t` near `y` is the pullback of `t` along
`Xₙ ⟶ X ⟶ Y`. -/
public theorem infinitesimalBaseRingHom_germ (n : ℕ) (U : Y.Opens) (hy : y ∈ U) (t : Γ(Y, U))
    (hle : (⊤ : (infinitesimalNeighbourhood f y n).Opens) ≤ (infinitesimalι f y n ≫ f) ⁻¹ᵁ U) :
    infinitesimalBaseRingHom f y n (Y.presheaf.germ U y hy t) =
      ((infinitesimalι f y n ≫ f).appLE U ⊤ hle).hom t := by
  rw [← infinitesimalRestrict_app f y n U hy t, infinitesimalRestrict, ← CommRingCat.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

/-- Pulling the base ring map of `Xₙ₊₁` back to `Eₙ₊₁` is pulling germs back to `Eₙ₊₁`. -/
public theorem appTop_thickeningToInfinitesimal_infinitesimalBaseRingHom [IsReduced D.subscheme]
    (n : ℕ) (a : Y.presheaf.stalk y) :
    (thickeningToInfinitesimal D f y hmaps n).appTop.hom
        (infinitesimalBaseRingHom f y (n + 1) a) =
      (stalkToThickening D f y hmaps n).hom a := by
  obtain ⟨U, hyU, t, rfl⟩ := TopCat.Presheaf.germ_exist _ a
  have hle : (⊤ : (infinitesimalNeighbourhood f y (n + 1)).Opens) ≤
      (infinitesimalι f y (n + 1) ≫ f) ⁻¹ᵁ U :=
    top_le_preimage_infinitesimalι f y (n + 1) U hyU
  rw [infinitesimalBaseRingHom_germ f y (n + 1) U hyU t hle, stalkToThickening,
    Scheme.Hom.stalkToΓ_germ, ← CommRingCat.comp_apply,
    ← appLE_top_eq_appTop (thickeningToInfinitesimal D f y hmaps n)
      (top_le_preimage_top _),
    Scheme.Hom.appLE_comp_appLE]
  exact ConcreteCategory.congr_hom (appLE_congr_hom
    (by rw [← Category.assoc, thickeningToInfinitesimal_ι]) U ⊤ _ _) t

/-! ### The infinitesimal neighbourhoods lie in the thickenings -/

/-- Every point of every infinitesimal neighbourhood of the fibre goes to `y`. -/
public theorem base_infinitesimalι_eq (m : ℕ) (x : infinitesimalNeighbourhood f y m) :
    f.base ((infinitesimalι f y m).base x) = y := by
  have hmem : f.base ((infinitesimalι f y m).base x) ∈
      Set.range (infinitesimalBase y m).base :=
    ⟨(infinitesimalStructure f y m).base x,
      congrArg (fun k : Scheme.Hom _ _ => k.base x) (infinitesimalι_comp f y m).symm⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : Subsingleton (Y.presheaf.stalk y ⧸ stalkMaximalIdeal y ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr ((pow_zero _).trans Ideal.one_eq_top)
    obtain ⟨p, -⟩ := hmem
    refine absurd (Ideal.eq_top_iff_one p.asIdeal |>.mpr ?_) p.isPrime.ne_top
    have h0 : (1 : Y.presheaf.stalk y ⧸ stalkMaximalIdeal y ^ 0) = 0 := Subsingleton.elim _ _
    exact h0 ▸ p.asIdeal.zero_mem
  · rwa [range_infinitesimalBase y hm] at hmem

/-- **`Xₘ ⊆ E_K` for some `K`**: some power of `D` vanishes on the `m`-th infinitesimal
neighbourhood of the fibre. -/
public theorem exists_pow_succ_le_ker_infinitesimalι [IsNoetherian X] [IsNoetherian Y]
    (hy : IsClosed ({y} : Set Y)) (hfib : f.base ⁻¹' {y} ⊆ (D.support : Set X)) (m : ℕ) :
    ∃ K : ℕ, D ^ (K + 1) ≤ (infinitesimalι f y m).ker := by
  have : QuasiCompact (infinitesimalBase y m) :=
    (quasiCompact_iff_compactSpace _).2 inferInstance
  obtain ⟨K, hK⟩ : ∃ K : ℕ, D ^ K ≤ (infinitesimalι f y m).ker := by
    rw [exists_pow_le_iff_le_radical, ← vanishingIdeal_support,
      ← le_support_iff_le_vanishingIdeal]
    intro x hx
    have hx' : x ∈ closure (Set.range (infinitesimalι f y m).base) := by
      rwa [← Scheme.Hom.support_ker]
    refine hfib (closure_minimal ?_ (hy.preimage f.continuous) hx')
    rintro _ ⟨z, rfl⟩
    exact base_infinitesimalι_eq f y m z
  exact ⟨K, (le_def.mpr fun U ↦ by
    simp only [ideal_pow]
    exact Ideal.pow_le_pow_right (by omega)).trans hK⟩

variable (hK : ∀ m : ℕ, ∃ K : ℕ, D ^ (K + 1) ≤ (infinitesimalι f y m).ker)

/-- An index `K` such that `D ^ (K + 1)` vanishes on the `m`-th infinitesimal neighbourhood. -/
public def infinitesimalThickeningIndex (m : ℕ) : ℕ := (hK m).choose

/-- **The morphism `Xₘ ⟶ E_K` over `X`**, through the scheme-theoretic image of `Xₘ ⟶ X`. -/
public def infinitesimalToThickening (m : ℕ) :
    infinitesimalNeighbourhood f y m ⟶ thickening D (infinitesimalThickeningIndex D f y hK m) :=
  (infinitesimalι f y m).toImage ≫ inclusion (hK m).choose_spec

/-- `Xₘ ⟶ E_K` is a morphism over `X`. -/
@[reassoc (attr := simp)]
public theorem infinitesimalToThickening_subschemeι (m : ℕ) :
    infinitesimalToThickening D f y hK m ≫
        (D ^ (infinitesimalThickeningIndex D f y hK m + 1)).subschemeι =
      infinitesimalι f y m := by
  simp [infinitesimalToThickening, infinitesimalThickeningIndex]

/-! ### The two inverse limits -/

/-- `Γ` is contravariant on composites, read on an element. -/
public theorem appTop_comp_apply {A B C : Scheme.{u}} (g : A ⟶ B) (g' : B ⟶ C) (z : Γ(C, ⊤)) :
    (g ≫ g').appTop.hom z = g.appTop.hom (g'.appTop.hom z) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- A compatible function on the thickenings restricts from any thickening to any smaller one. -/
public theorem appTop_inclusion_apply_formalNeighborhood (a : formalNeighborhoodRing D) {i j : ℕ}
    (h : i ≤ j) :
    (inclusion (pow_succ_le_pow_succ D h)).appTop.hom ((a : ∀ n, Γ(thickening D n, ⊤)) j) =
      (a : ∀ n, Γ(thickening D n, ⊤)) i :=
  thickeningRestrictionLE_formalNeighborhoodProjection D h a

/-- A compatible family of functions on the infinitesimal neighbourhoods restricts from any of
them to any smaller one. -/
public theorem appTop_infinitesimalTransition_apply
    (t : towerLimit (infinitesimalFunctions f y) (infinitesimalFunctionsMap f y)) {i j : ℕ}
    (h : i ≤ j) :
    (infinitesimalTransition f y h).appTop.hom ((t : ∀ n, infinitesimalFunctions f y n) j) =
      (t : ∀ n, infinitesimalFunctions f y n) i :=
  t.2 i j h

/-- If `u ≫ v ≫ g = g'`, then `u^* v^*` of a restriction `g^* x` of `x` is `g'^* x`. -/
private theorem appTop_comp_comp_apply_eq {A B C E : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ C)
    (g : C ⟶ E) (g' : A ⟶ E) (h : u ≫ v ≫ g = g') {x : Γ(E, ⊤)} {y : Γ(C, ⊤)} {z : Γ(A, ⊤)}
    (hy : g.appTop.hom x = y) (hz : g'.appTop.hom x = z) :
    u.appTop.hom (v.appTop.hom y) = z := by
  subst hy hz
  rw [← h, appTop_comp_apply, appTop_comp_apply]

/-- **The map `lim Γ(Xₙ, 𝒪) ⟶ lim Γ(Eₙ, 𝒪)`**, restriction along `Eₙ₊₁ ⟶ Xₙ₊₁`. -/
public def towerLimitToFormalNeighborhood [IsReduced D.subscheme]
    (t : towerLimit (infinitesimalFunctions f y) (infinitesimalFunctionsMap f y)) :
    formalNeighborhoodRing D :=
  ⟨fun n ↦ (thickeningToInfinitesimal D f y hmaps n).appTop.hom
      ((t : ∀ k, infinitesimalFunctions f y k) (n + 1)), fun n ↦ by
    have hmor : inclusion (show D ^ (n + 2) ≤ D ^ (n + 1) from pow_succ_le_pow_succ D
          (Nat.le_succ n)) ≫ thickeningToInfinitesimal D f y hmaps (n + 1) =
        thickeningToInfinitesimal D f y hmaps n ≫
          infinitesimalTransition f y (Nat.le_succ (n + 1)) := by
      rw [← cancel_mono (infinitesimalι f y (n + 2))]
      simp
    change (inclusion _).appTop.hom _ = _
    rw [← appTop_comp_apply, hmor, appTop_comp_apply, appTop_infinitesimalTransition_apply]⟩

/-- **The map `lim Γ(Eₙ, 𝒪) ⟶ lim Γ(Xₙ, 𝒪)`**, restriction along `Xₘ ⟶ E_K`. -/
public def formalNeighborhoodToTowerLimit (a : formalNeighborhoodRing D) :
    towerLimit (infinitesimalFunctions f y) (infinitesimalFunctionsMap f y) :=
  ⟨fun m ↦ (infinitesimalToThickening D f y hK m).appTop.hom
      ((a : ∀ n, Γ(thickening D n, ⊤)) (infinitesimalThickeningIndex D f y hK m)), by
    intro m m' h
    have h₁ : infinitesimalThickeningIndex D f y hK m ≤
        infinitesimalThickeningIndex D f y hK m + infinitesimalThickeningIndex D f y hK m' :=
      Nat.le_add_right _ _
    have h₂ : infinitesimalThickeningIndex D f y hK m' ≤
        infinitesimalThickeningIndex D f y hK m + infinitesimalThickeningIndex D f y hK m' :=
      Nat.le_add_left _ _
    have hmor : infinitesimalTransition f y h ≫ infinitesimalToThickening D f y hK m' ≫
          inclusion (pow_succ_le_pow_succ D h₂) =
        infinitesimalToThickening D f y hK m ≫ inclusion (pow_succ_le_pow_succ D h₁) := by
      rw [← cancel_mono (D ^ (infinitesimalThickeningIndex D f y hK m +
        infinitesimalThickeningIndex D f y hK m' + 1)).subschemeι]
      simp
    have key := congrArg (fun g ↦ g.appTop.hom ((a : ∀ n, Γ(thickening D n, ⊤))
      (infinitesimalThickeningIndex D f y hK m + infinitesimalThickeningIndex D f y hK m'))) hmor
    rwa [appTop_comp_apply, appTop_comp_apply, appTop_comp_apply,
      appTop_inclusion_apply_formalNeighborhood D a h₁,
      appTop_inclusion_apply_formalNeighborhood D a h₂] at key⟩

/-- `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodToTowerLimit` is a right inverse of
`AlgebraicGeometry.Scheme.IdealSheafData.towerLimitToFormalNeighborhood`. -/
public theorem towerLimitToFormalNeighborhood_formalNeighborhoodToTowerLimit
    [IsReduced D.subscheme] (a : formalNeighborhoodRing D) :
    towerLimitToFormalNeighborhood D f y hmaps (formalNeighborhoodToTowerLimit D f y hK a) =
      a := by
  refine Subtype.ext (funext fun n ↦ ?_)
  have h₁ : infinitesimalThickeningIndex D f y hK (n + 1) ≤
      n + infinitesimalThickeningIndex D f y hK (n + 1) := Nat.le_add_left _ _
  have h₂ : n ≤ n + infinitesimalThickeningIndex D f y hK (n + 1) := Nat.le_add_right _ _
  have hmor : thickeningToInfinitesimal D f y hmaps n ≫ infinitesimalToThickening D f y hK (n + 1)
        ≫ inclusion (pow_succ_le_pow_succ D h₁) = inclusion (pow_succ_le_pow_succ D h₂) := by
    rw [← cancel_mono (D ^ (n + infinitesimalThickeningIndex D f y hK (n + 1) + 1)).subschemeι]
    simp
  exact appTop_comp_comp_apply_eq _ _ _ _ hmor (appTop_inclusion_apply_formalNeighborhood D a h₁)
    (appTop_inclusion_apply_formalNeighborhood D a h₂)

/-- `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodToTowerLimit` is a left inverse of
`AlgebraicGeometry.Scheme.IdealSheafData.towerLimitToFormalNeighborhood`. -/
public theorem formalNeighborhoodToTowerLimit_towerLimitToFormalNeighborhood
    [IsReduced D.subscheme]
    (t : towerLimit (infinitesimalFunctions f y) (infinitesimalFunctionsMap f y)) :
    formalNeighborhoodToTowerLimit D f y hK (towerLimitToFormalNeighborhood D f y hmaps t) =
      t := by
  refine Subtype.ext (funext fun m ↦ ?_)
  have h₁ : infinitesimalThickeningIndex D f y hK m + 1 ≤
      m + (infinitesimalThickeningIndex D f y hK m + 1) := Nat.le_add_left _ _
  have h₂ : m ≤ m + (infinitesimalThickeningIndex D f y hK m + 1) := Nat.le_add_right _ _
  have hmor : infinitesimalToThickening D f y hK m ≫
        thickeningToInfinitesimal D f y hmaps (infinitesimalThickeningIndex D f y hK m) ≫
        infinitesimalTransition f y h₁ = infinitesimalTransition f y h₂ := by
    rw [← cancel_mono (infinitesimalι f y (m + (infinitesimalThickeningIndex D f y hK m + 1)))]
    simp
  exact appTop_comp_comp_apply_eq _ _ _ _ hmor (appTop_infinitesimalTransition_apply f y t h₁)
    (appTop_infinitesimalTransition_apply f y t h₂)

include hK in
/-- **The towers `(Eₙ)` and `(Xₙ)` have the same limit**: restriction along `Eₙ₊₁ ⟶ Xₙ₊₁` is a
bijection `lim Γ(Xₙ, 𝒪) ⟶ lim Γ(Eₙ, 𝒪)`. -/
public theorem bijective_towerLimitToFormalNeighborhood [IsReduced D.subscheme] :
    Function.Bijective (towerLimitToFormalNeighborhood D f y hmaps) :=
  ⟨Function.LeftInverse.injective
      (formalNeighborhoodToTowerLimit_towerLimitToFormalNeighborhood D f y hmaps hK),
    Function.RightInverse.surjective
      (towerLimitToFormalNeighborhood_formalNeighborhoodToTowerLimit D f y hmaps hK)⟩

/-! ### The completion of the local ring -/

/-- **The ring map `𝒪_{Y, y}^∧ ⟶ A = lim Γ(Eₙ, 𝒪)`**, extending
`AlgebraicGeometry.Scheme.IdealSheafData.stalkToFormalNeighborhood`: its `n`-th component is the
pullback to `Eₙ₊₁` of the image of a completed germ in `𝒪_{Y, y}/𝔪_y ^ (n + 1)`. -/
public def completionToFormalNeighborhood [IsReduced D.subscheme] :
    AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) →+*
      formalNeighborhoodRing D where
  toFun x := ⟨fun n ↦ (thickeningToStalkQuotient D f y hmaps n).hom
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (n + 1) x), fun n ↦ by
    obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective _ _ x
    change thickeningRestriction D n ((thickeningToStalkQuotient D f y hmaps (n + 1)).hom
      (AdicCompletion.evalₐ _ (n + 2) (AdicCompletion.mk _ _ s))) =
      (thickeningToStalkQuotient D f y hmaps n).hom
        (AdicCompletion.evalₐ _ (n + 1) (AdicCompletion.mk _ _ s))
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, thickeningToStalkQuotient_mk,
      thickeningRestriction_stalkToThickening, ← thickeningToStalkQuotient_mk,
      AdicCompletion.Ideal.mk_eq_mk _ (Nat.le_succ (n + 1))]⟩
  map_one' := Subtype.ext (funext fun n ↦ by
    change (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) 1) = 1
    rw [map_one, map_one])
  map_mul' a b := Subtype.ext (funext fun n ↦ by
    change (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) (a * b)) =
      (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) a) *
        (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) b)
    rw [map_mul, map_mul])
  map_zero' := Subtype.ext (funext fun n ↦ by
    change (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) 0) = 0
    rw [map_zero, map_zero])
  map_add' a b := Subtype.ext (funext fun n ↦ by
    change (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) (a + b)) =
      (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) a) +
        (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) b)
    rw [map_add, map_add])

/-- On the image of a germ,
`AlgebraicGeometry.Scheme.IdealSheafData.completionToFormalNeighborhood` is
`AlgebraicGeometry.Scheme.IdealSheafData.stalkToFormalNeighborhood`. -/
@[simp]
public theorem completionToFormalNeighborhood_of [IsReduced D.subscheme]
    (a : Y.presheaf.stalk y) :
    completionToFormalNeighborhood D f y hmaps (AdicCompletion.of _ _ a) =
      stalkToFormalNeighborhood D f y hmaps a :=
  Subtype.ext (funext fun n ↦ by
    show (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1)
      (AdicCompletion.of _ _ a)) = _
    rw [AdicCompletion.evalₐ_of, thickeningToStalkQuotient_mk]
    rfl)

/-- The identification `𝒪_{Y, y} ≅ (f_* 𝒪_X)_y` of `𝒪_{Y, y}`-modules, for `f_* 𝒪_X = 𝒪_Y`. -/
public def stalkLinearEquivPushforwardStalk [IsIso f.c] :
    Y.presheaf.stalk y ≃ₗ[Y.presheaf.stalk y] pushforwardStalkModule f y :=
  LinearEquiv.ofBijective
    { toFun := (toPushforwardStalk f y).hom
      map_add' := map_add _
      map_smul' := fun r s ↦ map_mul (toPushforwardStalk f y).hom r s }
    (by
      have : IsIso (toPushforwardStalk f y) := by
        unfold toPushforwardStalk
        exact Functor.map_isIso (TopCat.Presheaf.stalkFunctor CommRingCat y) f.c
      exact ConcreteCategory.bijective_of_isIso (toPushforwardStalk f y))

/-- **`𝒪_{Y, y}^∧ ⟶ A` factors through the theorem on formal functions**: it is the completion of
`𝒪_{Y, y} ≅ (f_* 𝒪_X)_y`, followed by the comparison map of [Stacks, Tag 02OD] and the
restriction `lim Γ(Xₙ, 𝒪) ⟶ lim Γ(Eₙ, 𝒪)`. -/
public theorem completionToFormalNeighborhood_eq [IsReduced D.subscheme] [IsIso f.c]
    (x : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :
    completionToFormalNeighborhood D f y hmaps x =
      towerLimitToFormalNeighborhood D f y hmaps (canonicalStalkComparison f y
        (AdicCompletion.congr _ (stalkLinearEquivPushforwardStalk f y) x)) := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective _ _ x
  refine Subtype.ext (funext fun n ↦ ?_)
  have hC : ((canonicalStalkComparison f y (AdicCompletion.congr _
      (stalkLinearEquivPushforwardStalk f y) (AdicCompletion.mk _ _ s)) :
        ∀ k, infinitesimalFunctions f y k) (n + 1)) =
      infinitesimalStalkRestrict f y (n + 1) ((toPushforwardStalk f y).hom (s.val (n + 1))) :=
    rfl
  show (thickeningToStalkQuotient D f y hmaps n).hom
      (AdicCompletion.evalₐ _ (n + 1) (AdicCompletion.mk _ _ s)) =
    (thickeningToInfinitesimal D f y hmaps n).appTop.hom _
  rw [hC, AdicCompletion.evalₐ_mk, thickeningToStalkQuotient_mk]
  exact (appTop_thickeningToInfinitesimal_infinitesimalBaseRingHom D f y hmaps n _).symm.trans
    (congrArg _ (infinitesimalStalkRestrictHom_toPushforwardStalk f y (n + 1) _).symm)

include hK in
/-- **`𝒪_{Y, y}^∧ ⟶ A` is bijective**, for `f` proper onto a locally Noetherian scheme with
`f_* 𝒪_X = 𝒪_Y`, given that every infinitesimal neighbourhood of the fibre lies in a thickening of
`D`. -/
public theorem bijective_completionToFormalNeighborhood [IsReduced D.subscheme] [IsIso f.c]
    [IsProper f] [IsLocallyNoetherian Y] :
    Function.Bijective (completionToFormalNeighborhood D f y hmaps) := by
  have heq : ⇑(completionToFormalNeighborhood D f y hmaps) =
      towerLimitToFormalNeighborhood D f y hmaps ∘ canonicalStalkComparison f y ∘
        AdicCompletion.congr _ (stalkLinearEquivPushforwardStalk f y) :=
    funext (completionToFormalNeighborhood_eq D f y hmaps)
  rw [heq]
  exact (bijective_towerLimitToFormalNeighborhood D f y hmaps hK).comp
    ((bijective_canonicalStalkComparison_of_isProper f y).comp (LinearEquiv.bijective _))

variable {D}

/-- **The completed local ring at `y` is the ring of [Stacks, Tag 0C2K]**, step 2 of the proof of
[Stacks, Tag 0C2L]. In the Stein case — `f` proper onto a Noetherian scheme, `f_* 𝒪_X = 𝒪_Y`, the
exceptional curve carried to the closed point `y` and the fibre over `y` contained in the curve —
the completion of `𝒪_{Y, y}` is isomorphic, as a ring, to the ring `A = lim H⁰(Eₙ, 𝒪_{Eₙ})` of
compatible functions on the thickenings of the curve, by an isomorphism extending the pullback
of germs `𝒪_{Y, y} ⟶ A`. -/
public theorem exists_ringEquiv_adicCompletion_formalNeighborhoodRing [IsNoetherian X]
    {k : Type u} [Field k] (e : projectiveLineProj k ≅ D.subscheme) (f : X ⟶ Y) (y : Y)
    (hsetup : D.IsSteinContractionSetup f y) (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y)
    (hfib : f.base ⁻¹' {y} ⊆ (D.support : Set X)) :
    ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+*
        D.formalNeighborhoodRing,
      ∀ a, ψ (AdicCompletion.of _ _ a) = D.stalkToFormalNeighborhood f y hmaps a := by
  have := isReduced_subscheme_of_projectiveLineProj_iso k e
  have := hsetup.isNoetherian
  have := hsetup.isProper
  have := hsetup.isIso_c
  exact ⟨RingEquiv.ofBijective _ (bijective_completionToFormalNeighborhood D f y hmaps
      (exists_pow_succ_le_ker_infinitesimalι D f y hsetup.isClosed_singleton hfib)),
    completionToFormalNeighborhood_of D f y hmaps⟩

end Scheme.IdealSheafData

end AlgebraicGeometry

end
