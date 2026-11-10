module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartTowerCharts
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.SpanOverBase
public import StacksFrontier.AlgebraicGeometry.OpensCoverHom
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.Deformation.Artin.Versality.WeakTowerEffectivity

/-!
# Effectivity of a tower with a good two-chart datum

This file proves `AlgebraicGeometry.C1590Private.TwoChartTowerEffective`: a tower
`Xₙ ⟶ Spec Rₙ` of flat deformations with cartesian transition maps, over a tower of rings with
surjective transition maps whose kernels over `R₀` are square-zero, whose first member `X₀` is
proper and of finite presentation and carries a good two-chart datum, is effective over `lim Rₙ`.

## Main definitions

* `AlgebraicGeometry.C1590Private.TwoChartTower.CompatibleCharts.total`: the scheme `Y` glued
  from `Spec S_(s)` and `Spec S_(t)`.
* `AlgebraicGeometry.C1590Private.TwoChartTower.CompatibleCharts.totalHom`: the structure
  morphism `Y ⟶ Spec (lim Rₙ)`.
* `AlgebraicGeometry.C1590Private.TwoChartTower.CompatibleCharts.level`: the map `Xₙ ⟶ Y`.

## Main results

* `AlgebraicGeometry.C1590Private.twoChartTowerEffective`: a tower with a good two-chart datum
  is effective.

## Implementation notes

* The datum lifts to every level, staying good, with section modules forming a tower of finite
  projective modules with base change (`twoChartDatumLifts`, `twoChartGoodOfThickening`).
* `P_k = lim_n Γ(Xₙ, Lₙ^{⊗ k})` and `S = ⨁_k P_k`, the graded ring
  `AlgebraicGeometry.C1590Private.TwoChartTower.CompatibleCharts.ring`; its homogeneous
  localizations `S_(s)`, `S_(t)` are flat over `lim Rₙ` and reduce to the rings of sections of the
  charts of every `Xₙ`.
* `Y` is `Spec S_(s)` glued to `Spec S_(t)` along `Spec S_(st)` (`AlgebraicGeometry.SpanGlue`), the
  maps `Xₙ ⟶ Y` are glued from the charts, and the squares are cartesian chart by chart, where they
  are `Spec` of pushout squares of rings.
* `Y` is flat by construction; it is proper and of finite presentation because `Y₀ = X₀` is, by
  the deformation-theoretic transfer of these properties across the first-order thickening
  `Spec R₀ ⟶ Spec (lim Rₙ)` (Stacks 06AG).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin.SquareZeroTower
  HomogeneousLocalization

universe u

namespace AlgebraicGeometry.C1590Private.TwoChartTower

/-- The open immersion `Spec Γ(X, U) ⟶ X` followed by `X ⟶ Spec R` is `Spec` of the structure
map `R → Γ(X, U)`. -/
theorem fromSpec_comp_eq {X : Scheme.{u}} {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R))
    {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ π = Spec.map (CommRingCat.ofHom (TwoChartDatum.baseOfSpecOn π U)) := by
  have hiso : (Spec (.of R)).isoSpec.inv = Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
    rw [← cancel_epi (Spec (.of R)).isoSpec.hom, Iso.hom_inv_id, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  rw [TwoChartDatum.baseOfSpecOn_eq_appLE, CommRingCat.ofHom_comp, Spec.map_comp,
    CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, ← hiso, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec π (isAffineOpen_top _) hU]

section Glue

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] {f : ∀ n, R (n + 1) →+* R n}
  {X : ℕ → Scheme.{u}} {π : ∀ n, X n ⟶ Spec (.of (R n))} {ι : ∀ n, X n ⟶ X (n + 1)}

namespace CompatibleCharts

variable (C : CompatibleCharts ι)
  (hpb : ∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n))))

/-! ### The glued scheme -/

/-- `Spec S_(st) ⟶ Spec S_(s)`. -/
def incS : Spec (.of (Away C.𝒜 (C.sElt * C.tElt))) ⟶ Spec (.of (Away C.𝒜 C.sElt)) :=
  Spec.map (CommRingCat.ofHom C.awayMapS)

/-- `Spec S_(st) ⟶ Spec S_(t)`. -/
def incT : Spec (.of (Away C.𝒜 (C.sElt * C.tElt))) ⟶ Spec (.of (Away C.𝒜 C.tElt)) :=
  Spec.map (CommRingCat.ofHom C.awayMapT)

/-- `Spec S_(st) ⟶ Spec S_(s)` is an open immersion. -/
instance : IsOpenImmersion C.incS := by
  let := C.awayMapS.toAlgebra
  have := Away.isLocalization_mul C.sElt_mem C.tElt_mem
    (rfl : C.sElt * C.tElt = C.sElt * C.tElt) one_ne_zero
  exact IsOpenImmersion.of_isLocalization (Away.isLocalizationElem C.sElt_mem C.tElt_mem)

/-- `Spec S_(st) ⟶ Spec S_(t)` is an open immersion. -/
instance : IsOpenImmersion C.incT := by
  let := C.awayMapT.toAlgebra
  have := Away.isLocalization_mul C.tElt_mem C.sElt_mem (mul_comm C.sElt C.tElt) one_ne_zero
  exact IsOpenImmersion.of_isLocalization (Away.isLocalizationElem C.tElt_mem C.sElt_mem)

/-- The image of `incT` lies in the basic open of `Spec S_(t)` defined by the element
`Away.isLocalizationElem C.tElt_mem C.sElt_mem`. -/
theorem incT_mem_basicOpen (w : Spec (.of (Away C.𝒜 (C.sElt * C.tElt)))) :
    C.incT w ∈ PrimeSpectrum.basicOpen (Away.isLocalizationElem C.tElt_mem C.sElt_mem) := by
  let := C.awayMapT.toAlgebra
  have := Away.isLocalization_mul C.tElt_mem C.sElt_mem (mul_comm C.sElt C.tElt) one_ne_zero
  exact (Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range (Away C.𝒜 (C.sElt * C.tElt))
    (Away.isLocalizationElem C.tElt_mem C.sElt_mem)) (C.incT w)).mp ⟨w, rfl⟩

/-- The image of `incS` lies in the basic open of `Spec S_(s)` defined by the element
`Away.isLocalizationElem C.sElt_mem C.tElt_mem`. -/
theorem incS_mem_basicOpen (w : Spec (.of (Away C.𝒜 (C.sElt * C.tElt)))) :
    C.incS w ∈ PrimeSpectrum.basicOpen (Away.isLocalizationElem C.sElt_mem C.tElt_mem) := by
  let := C.awayMapS.toAlgebra
  have := Away.isLocalization_mul C.sElt_mem C.tElt_mem
    (rfl : C.sElt * C.tElt = C.sElt * C.tElt) one_ne_zero
  exact (Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range (Away C.𝒜 (C.sElt * C.tElt))
    (Away.isLocalizationElem C.sElt_mem C.tElt_mem)) (C.incS w)).mp ⟨w, rfl⟩

/-- **The limit scheme `Y = Spec S_(s) ∪ Spec S_(t)`.** -/
abbrev total : Scheme.{u} := SpanGlue.glued C.incS C.incT

/-- `Spec S_(s) ⟶ Spec (lim Rₙ)`. -/
def structS : Spec (.of (Away C.𝒜 C.sElt)) ⟶ Spec (.of (limit f)) :=
  Spec.map (CommRingCat.ofHom (C.awayAlg hpb C.sElt))

/-- `Spec S_(t) ⟶ Spec (lim Rₙ)`. -/
def structT : Spec (.of (Away C.𝒜 C.tElt)) ⟶ Spec (.of (limit f)) :=
  Spec.map (CommRingCat.ofHom (C.awayAlg hpb C.tElt))

/-- The structure maps of `Spec S_(s)` and `Spec S_(t)` agree on `Spec S_(st)`. -/
theorem incS_structS : C.incS ≫ C.structS hpb = C.incT ≫ C.structT hpb := by
  rw [incS, incT, structS, structT, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r =>
    (C.awayMapS_awayAlg hpb r).trans (C.awayMapT_awayAlg hpb r).symm)

/-- **The structure morphism `Y ⟶ Spec (lim Rₙ)`.** -/
def totalHom : C.total ⟶ Spec (.of (limit f)) :=
  SpanGlue.desc C.incS C.incT (C.structS hpb) (C.structT hpb) (C.incS_structS hpb)

/-- The structure morphism `Y ⟶ Spec (lim Rₙ)` is flat. -/
theorem flat_totalHom (hPS : ∀ k, 1 ≤ k → C.PieceSplit (f := f) π k) : Flat (C.totalHom hpb) := by
  have : Flat (C.structS hpb) := by
    rw [structS, Flat.SpecMap_iff]
    exact C.flat_away hpb C.sAmb_mem hPS
  have : Flat (C.structT hpb) := by
    rw [structT, Flat.SpecMap_iff]
    exact C.flat_away hpb C.tAmb_mem hPS
  exact SpanGlue.flat_desc _ _ _ _ _

/-! ### The maps from the levels -/

/-- `Uₙ ⟶ Spec Γ(Xₙ, Uₙ) ⟶ Spec S_(s) ⟶ Y`. -/
def levelU (n : ℕ) : (C.D n).U.toScheme ⟶ C.total :=
  (C.D n).U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (C.evalU n)) ≫ SpanGlue.ι₁ C.incS C.incT

/-- `Vₙ ⟶ Spec Γ(Xₙ, Vₙ) ⟶ Spec S_(t) ⟶ Y`. -/
def levelV (n : ℕ) : (C.D n).V.toScheme ⟶ C.total :=
  (C.D n).V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (C.evalV n)) ≫ SpanGlue.ι₂ C.incS C.incT

/-- The maps `Uₙ ⟶ Y` and `Vₙ ⟶ Y` agree on `Uₙ ⊓ Vₙ`. -/
theorem levelU_levelV (n : ℕ) :
    (X n).homOfLE (inf_le_left : (C.D n).U ⊓ (C.D n).V ≤ (C.D n).U) ≫ C.levelU n =
      (X n).homOfLE (inf_le_right : (C.D n).U ⊓ (C.D n).V ≤ (C.D n).V) ≫ C.levelV n := by
  rw [levelU, levelV, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc]
  have h1 : CommRingCat.ofHom (C.evalU n) ≫
      (X n).presheaf.map (homOfLE (inf_le_left : (C.D n).U ⊓ (C.D n).V ≤ (C.D n).U)).op =
        CommRingCat.ofHom C.awayMapS ≫ CommRingCat.ofHom (C.evalUV n) := by
    ext z
    exact (C.evalUV_awayMapS n z).symm
  have h2 : CommRingCat.ofHom (C.evalV n) ≫
      (X n).presheaf.map (homOfLE (inf_le_right : (C.D n).U ⊓ (C.D n).V ≤ (C.D n).V)).op =
        CommRingCat.ofHom C.awayMapT ≫ CommRingCat.ofHom (C.evalUV n) := by
    ext z
    exact (C.evalUV_awayMapT n z).symm
  rw [h1, h2, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
  congr 2
  exact SpanGlue.glue_condition C.incS C.incT

/-- The two charts of `Xₙ`, indexed by `Bool`. -/
def charts (n : ℕ) : Bool → (X n).Opens := fun b => cond b (C.D n).V (C.D n).U

/-- The maps out of the two charts of `Xₙ`. -/
def chartMaps (n : ℕ) : ∀ b, (C.charts n b).toScheme ⟶ C.total
  | false => C.levelU n
  | true => C.levelV n

/-- There is a unique map `Xₙ ⟶ Y` restricting to `levelU` on `Uₙ` and to `levelV` on `Vₙ`. -/
theorem exists_level (n : ℕ) :
    ∃! j : X n ⟶ C.total, ∀ b, (C.charts n b).ι ≫ j = C.chartMaps n b := by
  refine Scheme.existsUnique_hom_of_opens_cover (C.charts n) (fun x => ?_) (C.chartMaps n) ?_
  · have hx : x ∈ (C.D n).U ⊔ (C.D n).V := (C.D n).sup_eq_top ▸ trivial
    rcases hx with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  · intro a b
    cases a <;> cases b
    · rfl
    · exact C.levelU_levelV n
    · have e₁ : (C.D n).V ⊓ (C.D n).U ≤ (C.D n).U ⊓ (C.D n).V := le_of_eq (inf_comm _ _)
      change (X n).homOfLE inf_le_left ≫ C.levelV n = (X n).homOfLE inf_le_right ≫ C.levelU n
      rw [← (X n).homOfLE_homOfLE e₁ inf_le_right, ← (X n).homOfLE_homOfLE e₁ inf_le_left,
        Category.assoc, Category.assoc, C.levelU_levelV n]
    · rfl

/-- **The map `Xₙ ⟶ Y`.** -/
def level (n : ℕ) : X n ⟶ C.total := (C.exists_level n).exists.choose

/-- The restriction of `level n` to `Uₙ` is `levelU n`. -/
theorem ι_level_U (n : ℕ) : (C.D n).U.ι ≫ C.level n = C.levelU n :=
  (C.exists_level n).exists.choose_spec false

/-- The restriction of `level n` to `Vₙ` is `levelV n`. -/
theorem ι_level_V (n : ℕ) : (C.D n).V.ι ≫ C.level n = C.levelV n :=
  (C.exists_level n).exists.choose_spec true

/-- A map `Xₙ ⟶ Y` restricting to `levelU n` on `Uₙ` and to `levelV n` on `Vₙ` is `level n`. -/
theorem level_eq_of (n : ℕ) {j : X n ⟶ C.total} (hU : (C.D n).U.ι ≫ j = C.levelU n)
    (hV : (C.D n).V.ι ≫ j = C.levelV n) : j = C.level n :=
  (C.exists_level n).unique (fun | false => hU | true => hV)
    (fun b => (C.exists_level n).exists.choose_spec b)

/-- On points of `Uₙ`, `level n` agrees with `levelU n`. -/
theorem level_ι_apply_U (n : ℕ) (x : (C.D n).U.toScheme) :
    C.level n ((C.D n).U.ι x) = C.levelU n x := by
  rw [← Scheme.Hom.comp_apply, C.ι_level_U]

/-- On points of `Vₙ`, `level n` agrees with `levelV n`. -/
theorem level_ι_apply_V (n : ℕ) (x : (C.D n).V.toScheme) :
    C.level n ((C.D n).V.ι x) = C.levelV n x := by
  rw [← Scheme.Hom.comp_apply, C.ι_level_V]

/-- The composite `Spec Γ(Xₙ, Uₙ) ⟶ Xₙ ⟶ Y` is `Spec Γ(Xₙ, Uₙ) ⟶ Spec S_(s) ⟶ Y`. -/
theorem fromSpec_level_U (n : ℕ) :
    (C.D n).isAffineOpen_U.fromSpec ≫ C.level n =
      Spec.map (CommRingCat.ofHom (C.evalU n)) ≫ SpanGlue.ι₁ C.incS C.incT := by
  rw [← (C.D n).isAffineOpen_U.isoSpec_inv_ι, Category.assoc, C.ι_level_U, levelU,
    ← (C.D n).isAffineOpen_U.isoSpec_hom, Iso.inv_hom_id_assoc]

/-- The composite `Spec Γ(Xₙ, Vₙ) ⟶ Xₙ ⟶ Y` is `Spec Γ(Xₙ, Vₙ) ⟶ Spec S_(t) ⟶ Y`. -/
theorem fromSpec_level_V (n : ℕ) :
    (C.D n).isAffineOpen_V.fromSpec ≫ C.level n =
      Spec.map (CommRingCat.ofHom (C.evalV n)) ≫ SpanGlue.ι₂ C.incS C.incT := by
  rw [← (C.D n).isAffineOpen_V.isoSpec_inv_ι, Category.assoc, C.ι_level_V, levelV,
    ← (C.D n).isAffineOpen_V.isoSpec_hom, Iso.inv_hom_id_assoc]

/-- A point of `Xₙ` outside `Uₙ` lies in `Vₙ`. -/
theorem mem_V_of_not_mem_U (n : ℕ) {x : X n} (hx : x ∉ (C.D n).U) : x ∈ (C.D n).V :=
  ((C.D n).sup_eq_top ▸ trivial : x ∈ (C.D n).U ⊔ (C.D n).V).resolve_left hx

/-- A point of `Xₙ` outside `Vₙ` lies in `Uₙ`. -/
theorem mem_U_of_not_mem_V (n : ℕ) {x : X n} (hx : x ∉ (C.D n).V) : x ∈ (C.D n).U :=
  ((C.D n).sup_eq_top ▸ trivial : x ∈ (C.D n).U ⊔ (C.D n).V).resolve_right hx

/-- The part of `Xₙ` over the first chart of `Y` is `Uₙ`. -/
theorem level_preimage_ι₁ (n : ℕ) :
    C.level n ⁻¹ᵁ (SpanGlue.ι₁ C.incS C.incT).opensRange = (C.D n).U := by
  ext x
  constructor
  · intro hx
    by_contra hxU
    let p : (C.D n).V.toScheme := ⟨x, C.mem_V_of_not_mem_U n hxU⟩
    obtain ⟨y, hy⟩ := hx
    have hy' : SpanGlue.ι₁ C.incS C.incT y = SpanGlue.ι₂ C.incS C.incT
        (Spec.map (CommRingCat.ofHom (C.evalV n)) ((C.D n).V.toSpecΓ p)) := by
      rw [hy, show x = (C.D n).V.ι p from rfl, C.level_ι_apply_V, levelV,
        Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    obtain ⟨w, hw⟩ := (SpanGlue.exists_eq_iff_mem_range₂ C.incS C.incT _).mp ⟨y, hy'⟩
    have hmem := C.incT_mem_basicOpen w
    rw [hw] at hmem
    have hA : (C.D n).V.toSpecΓ p ∈ PrimeSpectrum.basicOpen
        (C.evalV n (Away.isLocalizationElem C.tElt_mem C.sElt_mem)) := hmem
    rw [evalV_isLocalizationElem] at hA
    have hB : p ∈ (C.D n).V.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (C.D n).a := hA
    rw [Scheme.Opens.toSpecΓ_preimage_basicOpen] at hB
    have hC : x ∈ (X n).basicOpen (C.D n).a := hB
    rw [(C.D n).basicOpen_a] at hC
    exact hxU hC.1
  · intro hxU
    let p : (C.D n).U.toScheme := ⟨x, hxU⟩
    refine ⟨Spec.map (CommRingCat.ofHom (C.evalU n)) ((C.D n).U.toSpecΓ p), ?_⟩
    change _ = C.level n ((C.D n).U.ι p)
    rw [C.level_ι_apply_U, levelU, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]

/-- The part of `Xₙ` over the second chart of `Y` is `Vₙ`. -/
theorem level_preimage_ι₂ (n : ℕ) :
    C.level n ⁻¹ᵁ (SpanGlue.ι₂ C.incS C.incT).opensRange = (C.D n).V := by
  ext x
  constructor
  · intro hx
    by_contra hxV
    let p : (C.D n).U.toScheme := ⟨x, C.mem_U_of_not_mem_V n hxV⟩
    obtain ⟨y, hy⟩ := hx
    have hy' : SpanGlue.ι₂ C.incS C.incT y = SpanGlue.ι₁ C.incS C.incT
        (Spec.map (CommRingCat.ofHom (C.evalU n)) ((C.D n).U.toSpecΓ p)) := by
      rw [hy, show x = (C.D n).U.ι p from rfl, C.level_ι_apply_U, levelU,
        Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    obtain ⟨w, hw⟩ := (SpanGlue.exists_eq_iff_mem_range₁ C.incS C.incT _).mp ⟨y, hy'⟩
    have hmem := C.incS_mem_basicOpen w
    rw [hw] at hmem
    have hA : (C.D n).U.toSpecΓ p ∈ PrimeSpectrum.basicOpen
        (C.evalU n (Away.isLocalizationElem C.sElt_mem C.tElt_mem)) := hmem
    rw [evalU_isLocalizationElem] at hA
    have hB : p ∈ (C.D n).U.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (C.D n).b := hA
    rw [Scheme.Opens.toSpecΓ_preimage_basicOpen] at hB
    have hC : x ∈ (X n).basicOpen (C.D n).b := hB
    rw [(C.D n).basicOpen_b] at hC
    exact hxV hC.2
  · intro hxV
    let p : (C.D n).V.toScheme := ⟨x, hxV⟩
    refine ⟨Spec.map (CommRingCat.ofHom (C.evalV n)) ((C.D n).V.toSpecΓ p), ?_⟩
    change _ = C.level n ((C.D n).V.ι p)
    rw [C.level_ι_apply_V, levelV, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]

/-! ### The levels are the base changes of `Y` -/

/-- A chart `Spec A ⟶ Z` of the target meets `X` in an affine open `U` of `X`; if the ring maps
form a pushout, the corresponding chart square over `Spec L` is a pullback. -/
private theorem isPullback_chart_of_isPushout {X Z : Scheme.{u}} {R : Type u} [CommRing R]
    {L A : CommRingCat.{u}} (l : X ⟶ Z) (π : X ⟶ Spec (.of R)) (d : Z ⟶ Spec L)
    (j : Spec A ⟶ Z) {U : X.Opens} (hU : IsAffineOpen U) (p : L ⟶ .of R) (a : L ⟶ A)
    (e : A ⟶ Γ(X, U)) (hA : IsPullback hU.fromSpec (Spec.map e) l j)
    (hpush : IsPushout p a (CommRingCat.ofHom (TwoChartDatum.baseOfSpecOn π U)) e)
    (hd : j ≫ d = Spec.map a) :
    IsPullback (pullback.snd l j) (pullback.fst l j ≫ π) (j ≫ d) (Spec.map p) := by
  have hsq := (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip
  refine hsq.of_iso hA.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      fromSpec_comp_eq]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp, hd]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- `Xₙ` is the base change of `Y ⟶ Spec (lim Rₙ)` along `Spec Rₙ ⟶ Spec (lim Rₙ)`. -/
theorem isPullback_level (hf : ∀ n, Function.Surjective (f n))
    (hPS : ∀ k, 1 ≤ k → C.PieceSplit (f := f) π k) (n : ℕ) :
    IsPullback (C.level n) (π n) (C.totalHom hpb)
      (Spec.map (CommRingCat.ofHom (towerLimitProj f n))) := by
  refine SpanGlue.isPullback_of_charts C.incS C.incT (C.level n) (π n) (C.totalHom hpb) _ ?_ ?_
  · have hA : IsPullback (C.D n).isAffineOpen_U.fromSpec
        (Spec.map (CommRingCat.ofHom (C.evalU n))) (C.level n) (SpanGlue.ι₁ C.incS C.incT) :=
      (IsOpenImmersion.isPullback _ _ _ _ (C.fromSpec_level_U n)
        (by rw [C.level_preimage_ι₁, IsAffineOpen.opensRange_fromSpec])).flip
    have hpush : IsPushout (CommRingCat.ofHom (towerLimitProj f n))
        (CommRingCat.ofHom (C.awayAlg hpb C.sElt))
        (CommRingCat.ofHom (TwoChartDatum.baseOfSpecOn (π n) (C.D n).U))
        (CommRingCat.ofHom (C.evalU n)) :=
      FormalSpace.CartesianColimit.isPushout_of_surjective_of_ker_eq _ _ _ _
        (CommRingCat.hom_ext (RingHom.ext fun r => (C.evalU_awayAlg hpb n r).symm))
        (towerLimitProj_surjective f hf n) (C.evalU_surjective hPS n) (C.ker_evalU hpb hPS n)
    exact isPullback_chart_of_isPushout _ _ _ _ (C.D n).isAffineOpen_U _ _ _ hA hpush
      (SpanGlue.ι₁_desc ..)
  · have hA : IsPullback (C.D n).isAffineOpen_V.fromSpec
        (Spec.map (CommRingCat.ofHom (C.evalV n))) (C.level n) (SpanGlue.ι₂ C.incS C.incT) :=
      (IsOpenImmersion.isPullback _ _ _ _ (C.fromSpec_level_V n)
        (by rw [C.level_preimage_ι₂, IsAffineOpen.opensRange_fromSpec])).flip
    have hpush : IsPushout (CommRingCat.ofHom (towerLimitProj f n))
        (CommRingCat.ofHom (C.awayAlg hpb C.tElt))
        (CommRingCat.ofHom (TwoChartDatum.baseOfSpecOn (π n) (C.D n).V))
        (CommRingCat.ofHom (C.evalV n)) :=
      FormalSpace.CartesianColimit.isPushout_of_surjective_of_ker_eq _ _ _ _
        (CommRingCat.hom_ext (RingHom.ext fun r => (C.evalV_awayAlg hpb n r).symm))
        (towerLimitProj_surjective f hf n) (C.evalV_surjective hPS n) (C.ker_evalV hpb hPS n)
    exact isPullback_chart_of_isPushout _ _ _ _ (C.D n).isAffineOpen_V _ _ _ hA hpush
      (SpanGlue.ι₂_desc ..)

/-- **The maps `Xₙ ⟶ Y` are compatible with the transition maps.** -/
theorem ι_comp_level (n : ℕ) : ι n ≫ C.level (n + 1) = C.level n := by
  refine C.level_eq_of n ?_ ?_
  · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (ι n) (C.preimage_U n).ge, Category.assoc,
      C.ι_level_U, levelU, ← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp_assoc,
      levelU]
    congr 2
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun z => C.ρU_evalU n z))
  · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (ι n) (C.preimage_V n).ge, Category.assoc,
      C.ι_level_V, levelV, ← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp_assoc,
      levelV]
    congr 2
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun z => C.ρV_evalV n z))

end CompatibleCharts

end Glue

/-! ### Building the compatible charts -/

section Build

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] {f : ∀ n, R (n + 1) →+* R n}
  {X : ℕ → Scheme.{u}} {π : ∀ n, X n ⟶ Spec (.of (R n))} {ι : ∀ n, X n ⟶ X (n + 1)}

/-- If every `ker (Rₙ → R₀)` is square-zero, then so is every `ker (Rₙ₊₁ → Rₙ)`. -/
theorem ker_sq_eq_bot (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥) (n : ℕ) :
    RingHom.ker (f n) ^ 2 = ⊥ := by
  have hle : RingHom.ker (f n) ≤ RingHom.ker (toBase f (n + 1)) := fun x hx => by
    rw [RingHom.mem_ker, toBase_succ, RingHom.mem_ker.mp hx, map_zero]
  exact le_bot_iff.mp ((Ideal.pow_right_mono hle 2).trans (hsq (n + 1)).le)

/-- **The datum lifts up the tower, staying good.** -/
theorem exists_isGoodTower (hf : ∀ n, Function.Surjective (f n))
    (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥)
    (hpb : ∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n))))
    (hflat : ∀ n, Flat (π n)) (D : TwoChartDatum (X 0))
    (hD : D.IsGood (TwoChartDatum.baseOfSpec (π 0))) :
    ∃ C : CompatibleCharts ι, C.IsGoodTower f π := by
  have hsq' := ker_sq_eq_bot hsq
  have hstep : ∀ n (Dn : {D' : TwoChartDatum (X n) // D'.IsGood (TwoChartDatum.baseOfSpec (π n))}),
      ∃ D' : {D' : TwoChartDatum (X (n + 1)) //
          D'.IsGood (TwoChartDatum.baseOfSpec (π (n + 1)))},
        ∃ (hU : ι n ⁻¹ᵁ D'.1.U = Dn.1.U) (hV : ι n ⁻¹ᵁ D'.1.V = Dn.1.V),
          (ι n).appLE _ _ hU.ge D'.1.b = Dn.1.b ∧ (ι n).appLE _ _ hV.ge D'.1.a = Dn.1.a := by
    intro n Dn
    obtain ⟨D', hU, hV, hU', hV', hb, ha⟩ := twoChartDatumLifts (R n) (R (n + 1)) (f n) (hf n)
      (hsq' n) (X n) (X (n + 1)) (π n) (π (n + 1)) (ι n) (hpb n) (hflat (n + 1)) Dn.1 Dn.2
    have hgood := (twoChartGoodOfThickening (R n) (R (n + 1)) (f n) (hf n) (hsq' n) (X n)
      (X (n + 1)) (π n) (π (n + 1)) (ι n) (hpb n) (hflat (n + 1)) Dn.1 D' hU hV hU' hV' hb ha
      Dn.2).1
    exact ⟨⟨D', hgood⟩, hU', hV', hb, ha⟩
  choose step hstep using hstep
  let seq : ∀ n, {D' : TwoChartDatum (X n) // D'.IsGood (TwoChartDatum.baseOfSpec (π n))} :=
    fun n => Nat.rec (motive := fun n =>
      {D' : TwoChartDatum (X n) // D'.IsGood (TwoChartDatum.baseOfSpec (π n))}) ⟨D, hD⟩
      (fun n Dn => step n Dn) n
  let C : CompatibleCharts ι :=
    { D := fun n => (seq n).1
      preimage_U := fun n => (hstep n (seq n)).choose
      preimage_V := fun n => (hstep n (seq n)).choose_spec.choose
      b_eq := fun n => (hstep n (seq n)).choose_spec.choose_spec.1
      a_eq := fun n => (hstep n (seq n)).choose_spec.choose_spec.2 }
  have hG : ∀ n, _ := fun n => twoChartGoodOfThickening (R n) (R (n + 1)) (f n) (hf n) (hsq' n)
    (X n) (X (n + 1)) (π n) (π (n + 1)) (ι n) (hpb n) (hflat (n + 1)) (C.D n) (C.D (n + 1))
    (C.preimage_U n).ge (C.preimage_V n).ge (C.preimage_U n) (C.preimage_V n) (C.b_eq n)
    (C.a_eq n) (seq n).2
  exact ⟨C, fun n => (seq n).2, fun n k hk q hq => ((hG n).2 k hk).2.1 q hq,
    fun n k hk => ((hG n).2 k hk).2.2⟩

end Build

end AlgebraicGeometry.C1590Private.TwoChartTower

namespace AlgebraicGeometry.C1590Private

open TwoChartTower

/-- **Effectivity of a tower with a good two-chart datum.** Let `⋯ → R₁ → R₀` be a tower
with surjective transition maps and square-zero kernels over `R₀`, `Xₙ ⟶ Spec Rₙ` flat with
cartesian transition maps, `X₀` proper and of finite presentation over `R₀` with a good two-chart
datum. Then there is a flat, proper, finitely presented `Y ⟶ Spec (lim Rₙ)` with compatible maps
`Xₙ ⟶ Y` exhibiting each `Xₙ` as the base change of `Y`. -/
theorem twoChartTowerEffective : TwoChartTowerEffective.{u} := by
  intro R _ f hf hsq _ X π ι hpb hflat hproper hlfp D hD
  obtain ⟨C, hG⟩ := exists_isGoodTower hf hsq hpb hflat D hD
  have hPS : ∀ k, 1 ≤ k → C.PieceSplit (f := f) π k := fun k hk =>
    C.pieceSplit hf (ker_sq_eq_bot hsq) hpb hG k hk
  have hpb0 := C.isPullback_level hpb hf hPS 0
  have hproj : towerLimitProj f 0 = limitBase f := RingHom.ext fun _ => rfl
  have hfirst : Stacks.Thickenings.IsFirstOrderThickening
      (Spec.map (CommRingCat.ofHom (towerLimitProj f 0))) :=
    Stacks.Smooth.isFirstOrderThickening_specMap _ (towerLimitProj_surjective f hf 0)
      (by rw [CommRingCat.hom_ofHom, hproj]; exact ker_limitBase_sq f hsq)
  have hfinite : Stacks.Thickenings.IsFiniteOrderThickening
      (Spec.map (CommRingCat.ofHom (towerLimitProj f 0))) := ⟨hfirst.1, 1, hfirst.2⟩
  let Dg : Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.{u} :=
    { S := Spec (.of (R 0))
      S' := Spec (.of (limit f))
      iS := Spec.map (CommRingCat.ofHom (towerLimitProj f 0))
      iS_finiteOrder := hfinite
      X := X 0
      X' := C.total
      iX := C.level 0
      iX_thickening := Stacks.Thickenings.isThickening_of_isPullback hpb0 hfinite.isThickening
      Y := Spec (.of (R 0))
      Y' := Spec (.of (limit f))
      iY := Spec.map (CommRingCat.ofHom (towerLimitProj f 0))
      iY_thickening := hfinite.isThickening
      pX := π 0
      pX' := C.totalHom hpb
      pY := 𝟙 _
      pY' := 𝟙 _
      f := π 0
      f' := C.totalHom hpb
      f_over_S := Category.comp_id _
      f'_over_S' := Category.comp_id _
      f_thickening_comm := hpb0.w.symm
      X_cartesian := hpb0
      Y_cartesian := IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩
      X'_flat := C.flat_totalHom hpb hPS }
  exact ⟨C.total, C.totalHom hpb, C.level, C.flat_totalHom hpb hPS,
    Dg.isProper_iff.mp hproper, Dg.locallyOfFinitePresentation_iff.mp hlfp,
    C.isPullback_level hpb hf hPS, C.ι_comp_level⟩

end AlgebraicGeometry.C1590Private

end
