module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.Groupoids.FittingIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chain of Fitting ideals of a module on an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G` be
a finite type quasi-coherent `𝒪_F`-module.  The Fitting ideals of `G` form an increasing chain

`0 = Fit₋₁(G) ⊆ Fit₀(G) ⊆ Fit₁(G) ⊆ … ⊆ 𝒪_F`

of sheaves of ideals of `𝒪_F`, indexed by `ℤ` as the module-theoretic `fittingIdeal` is, and this
chain is *characterised* by its sections: over an affine étale chart `U` the sections of `Fit_k(G)`
are the module-theoretic `k`-th Fitting ideal of the sections `G(U)` over the chart ring `𝒪_F(U)`.

## Main definitions

* `AlgebraicGeometry.Space.fittingIdealInt` is the `k`-th Fitting ideal sheaf of an `𝒪_F`-module
  for `k : ℤ`: the smallest sheaf of ideals of `𝒪_F` whose sections over every affine étale chart
  contain the module-theoretic Fitting ideal of the sections there.
* `AlgebraicGeometry.Space.chartFittingIdeal` is the sheaf of ideals of sections of `𝒪_F` that
  restrict into the chartwise Fitting ideal over every affine étale chart below.

## Main results

* `AlgebraicGeometry.Space.fittingIdealInt_obj_eq`: **over an affine étale chart the sections of
  `Fit_k(G)` are exactly the module-theoretic Fitting ideal of the sections of `G`.**  This is the
  characterisation of Stacks 0CZ3, and with it `AlgebraicGeometry.Space.fittingIdealInt` is
  pinned down rather than merely bounded below.
* `AlgebraicGeometry.Space.fittingIdeal_obj_eq_fittingIdealOnChart` is the same statement for the
  `ℕ`-indexed `AlgebraicGeometry.Space.fittingIdeal`.
* `AlgebraicGeometry.Space.fittingIdealInt_eq_bot_of_lt_zero` and
  `AlgebraicGeometry.Space.fittingIdealInt_obj_eq_bot_of_lt_zero`: `Fit₋₁(G) = 0`.
* `AlgebraicGeometry.Space.monotone_fittingIdealInt`: the chain increases.
* `AlgebraicGeometry.Space.chartFittingIdeal_isSheaf_aux` and
  `AlgebraicGeometry.Space.mem_chartFittingIdeal_affine_iff`: the chartwise Fitting ideals already
  satisfy the sheaf condition, which is why the infimum defining `Fit_k(G)` is attained.
* `Ideal.mem_of_map_mem_pi_faithfullyFlat`: membership in an ideal is detected by a finite family
  of ring maps whose product is faithfully flat.

## Implementation notes

`AlgebraicGeometry.Space.fittingIdeal` is defined as an infimum, so on its own it only comes with
the inclusion `AlgebraicGeometry.Space.mem_fittingIdeal_of_mem_fittingIdealOnChart` of the
chartwise ideal into the sections.  The reverse inclusion — the content of Stacks 0CZ3 — is proved
here by exhibiting a single sheaf of ideals whose sections over an affine chart are *exactly* the
chartwise Fitting ideal, namely `AlgebraicGeometry.Space.chartFittingIdeal`; the infimum is then
below it, and the two inclusions meet.

That `AlgebraicGeometry.Space.chartFittingIdeal` is a sheaf of ideals, and not merely a family of
ideals, is the only mathematical input: a covering sieve of an affine étale chart contains a
*finite* family of affine étale charts whose restriction maps on regular functions are jointly
faithfully flat, the chartwise Fitting ideals base change along each of them by Stacks 07ZA
(`AlgebraicGeometry.Space.fittingIdealOnChart_baseChange`), and an ideal is recovered from its
extensions along a jointly faithfully flat finite family.

Everything is stated for a module that is cartesian on affine charts with finite sections over the
affine charts; for a finite type quasi-coherent module both hold, the first by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` (Stacks 03DX(2)).
The finiteness of the sections over every affine chart is the étale-local reading of finite type
that the conventions of Stacks 0CZ3 use, under which the Fitting ideals are defined chartwise.

## References

* [Stacks Project, Tag 0CZ3](https://stacks.math.columbia.edu/tag/0CZ3)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w m

/-! ### Descent of membership in an ideal along a finite faithfully flat family -/

/-- **Membership in an ideal is detected by a finite family of ring maps whose product is
faithfully flat.**  The extension of an ideal to the product ring is the product of its
extensions, and the contraction of an extended ideal along a faithfully flat ring map is the
ideal itself. -/
@[ega "0 6.5.1" "special case"]
theorem Ideal.mem_of_map_mem_pi_faithfullyFlat {A : Type u} [CommRing A]
    {ι : Type v} [Finite ι] {R : ι → Type w} [∀ i, CommRing (R i)] (f : ∀ i, A →+* R i)
    (hff : (RingHom.pi f).FaithfullyFlat) (I : Ideal A) {x : A}
    (hx : ∀ i, f i x ∈ I.map (f i)) : x ∈ I := by
  let : Algebra A (∀ i, R i) := (RingHom.pi f).toAlgebra
  let : Module.FaithfullyFlat A (∀ i, R i) := hff
  have hmap : I.map (RingHom.pi f) = Ideal.pi fun i => I.map (f i) := by
    refine Ideal.piOrderIso.injective (funext fun i => ?_)
    show (I.map (RingHom.pi f)).map (Pi.evalRingHom R i) =
      (Ideal.pi fun i => I.map (f i)).map (Pi.evalRingHom R i)
    rw [Ideal.map_map, Ideal.map_evalRingHom_pi]
    rfl
  have hmem : (RingHom.pi f) x ∈ I.map (RingHom.pi f) := by
    rw [hmap]; exact hx
  exact (Ideal.comap_map_eq_self_of_faithfullyFlat (A := A) (B := ∀ i, R i) I) ▸ hmem

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Base change of the chartwise Fitting ideals -/

variable {B S hS F hF}

/-- **Stacks 07ZA for the charts of an algebraic space, in every integer degree.**  Where the base
change comparison over `f : V ⟶ U` is bijective, the `k`-th Fitting ideal of the sections over `V`
is generated by the image of the `k`-th Fitting ideal of the sections over `U`. -/
theorem fittingIdealChart_baseChange (G : Modules.{u, m} B S hS F hF) (k : ℤ)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    [Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U))]
    [Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V))]
    (hf : Function.Bijective (sectionsBaseChange G f)) :
    _root_.fittingIdeal (R := chartRing B S hS F hF V) (M := G.val.obj (op V)) k =
      Ideal.map (chartRestrict f)
        (_root_.fittingIdeal (R := chartRing B S hS F hF U) (M := G.val.obj (op U)) k) := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [fittingIdeal_eq_bot_of_lt_zero hk, fittingIdeal_eq_bot_of_lt_zero hk, Ideal.map_bot]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) := ⟨k.toNat, by omega⟩
    exact fittingIdealOnChart_baseChange G j f hf

/-- The chartwise Fitting ideals base change between affine charts of a module cartesian on
affine charts, in every integer degree. -/
theorem fittingIdealChart_baseChange_of_isCartesianOnAffineCharts
    (G : Modules.{u, m} B S hS F hF) (hG : IsCartesianOnAffineCharts G) (k : ℤ)
    {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (f : V ⟶ U) [Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U))] :
    letI := module_finite_sections_of_bijective_chartBaseChange G f (hG U V hU hV f)
    _root_.fittingIdeal (R := chartRing B S hS F hF V) (M := G.val.obj (op V)) k =
      Ideal.map (chartRestrict f)
        (_root_.fittingIdeal (R := chartRing B S hS F hF U) (M := G.val.obj (op U)) k) := by
  have _ := module_finite_sections_of_bijective_chartBaseChange G f (hG U V hU hV f)
  exact fittingIdealChart_baseChange G k f (hG U V hU hV f)

/-! ### The sheaf of ideals cut out by the chartwise Fitting ideals -/

/-- The sections of `𝒪_F` over an étale chart that restrict into the `k`-th chartwise Fitting
ideal over every affine étale chart below it. -/
noncomputable def chartFittingSubpresheaf (G : Modules.{u, m} B S hS F hF)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (k : ℤ) :
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).val.Submodule where
  obj X :=
    { carrier := {a | ∀ (W : SmallEtale B S hS F)
        (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
        (g : W ⟶ X.unop),
          chartRestrict (hF := hF) g a ∈
            @_root_.fittingIdeal (chartRing B S hS F hF W) _ (G.val.obj (op W)) _ _ (hfin W hW) k}
      add_mem' := fun {x y} ha hb W hW g => by
        let x' : chartRing B S hS F hF X.unop := x
        let y' : chartRing B S hS F hF X.unop := y
        have hgoal : chartRestrict (hF := hF) g (x' + y') ∈
            @_root_.fittingIdeal (chartRing B S hS F hF W) _ (G.val.obj (op W)) _ _
              (hfin W hW) k := by
          rw [map_add (chartRestrict (hF := hF) g) x' y']
          exact Ideal.add_mem _ (ha W hW g) (hb W hW g)
        exact hgoal
      zero_mem' := fun W hW g => by
        change chartRestrict (hF := hF) g (0 : chartRing B S hS F hF X.unop) ∈ _
        rw [map_zero]
        exact Ideal.zero_mem _
      smul_mem' := fun c x ha W hW g => by
        let c' : chartRing B S hS F hF X.unop := c
        let x' : chartRing B S hS F hF X.unop := x
        have hgoal : chartRestrict (hF := hF) g (c' * x') ∈
            @_root_.fittingIdeal (chartRing B S hS F hF W) _ (G.val.obj (op W)) _ _
              (hfin W hW) k := by
          rw [map_mul (chartRestrict (hF := hF) g) c' x']
          exact Ideal.mul_mem_left _ _ (ha W hW g)
        exact hgoal }
  map {X Y} f := fun a ha W hW g =>
    (DFunLike.congr_fun (chartRestrict_comp (hF := hF) f.unop g) a) ▸ ha W hW (g ≫ f.unop)

/-- **The chartwise Fitting ideals satisfy the sheaf condition.**  A section of the chart ring
lying in the extension of the chartwise Fitting ideal along each member of a finite jointly
faithfully flat family of affine charts already lies in the chartwise Fitting ideal. -/
theorem chartFittingIdeal_isSheaf_aux (G : Modules.{u, m} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (k : ℤ) {X : SmallEtale B S hS F} (a : chartRing B S hS F hF X)
    (hcov : (chartFittingSubpresheaf G hfin k).toSubfunctor.sieveOfSection a ∈
      SmallEtale.topology B S hS F X) :
    a ∈ (chartFittingSubpresheaf G hfin k).obj (op X) := by
  intro W hW g
  have _ := hfin W hW
  obtain ⟨n, z, φ, hzaff, hzT, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS F hF hW
      (GrothendieckTopology.pullback_stable (SmallEtale.topology B S hS F) g hcov)
  refine Ideal.mem_of_map_mem_pi_faithfullyFlat
    (fun i => chartRestrict (hF := hF) (φ i)) hff _ fun i => ?_
  have _ := hfin (z i) (hzaff i)
  have hres : chartRestrict (hF := hF) (𝟙 (z i))
      (chartRestrict (hF := hF) (φ i ≫ g) a) ∈
      @_root_.fittingIdeal (chartRing B S hS F hF (z i)) _ (G.val.obj (op (z i))) _ _
        (hfin (z i) (hzaff i)) k :=
    hzT i (z i) (hzaff i) (𝟙 (z i))
  have key : chartRestrict (hF := hF) (φ i ≫ g) a ∈
      @_root_.fittingIdeal (chartRing B S hS F hF (z i)) _ (G.val.obj (op (z i))) _ _
        (hfin (z i) (hzaff i)) k := by
    rwa [chartRestrict_id, RingHom.id_apply] at hres
  have hbc : @_root_.fittingIdeal (chartRing B S hS F hF (z i)) _ (G.val.obj (op (z i))) _ _
      (hfin (z i) (hzaff i)) k =
      Ideal.map (chartRestrict (hF := hF) (φ i))
        (@_root_.fittingIdeal (chartRing B S hS F hF W) _ (G.val.obj (op W)) _ _ (hfin W hW) k) :=
    fittingIdealChart_baseChange_of_isCartesianOnAffineCharts G hG k hW (hzaff i) (φ i)
  have heq : chartRestrict (hF := hF) (φ i ≫ g) a =
      chartRestrict (hF := hF) (φ i) (chartRestrict (hF := hF) g a) :=
    DFunLike.congr_fun (chartRestrict_comp (hF := hF) g (φ i)) a
  rw [← heq]
  exact hbc ▸ key

/-- **The sections of `𝒪_F` restricting into the chartwise Fitting ideals form a sheaf of
ideals.** -/
noncomputable def chartFittingIdeal (G : Modules.{u, m} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (k : ℤ) :
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).Submodule where
  toSubmodule := chartFittingSubpresheaf G hfin k
  isSheaf X a hcov := chartFittingIdeal_isSheaf_aux G hG hfin k (X := X.unop) a hcov

/-- Over an affine étale chart the sections of `AlgebraicGeometry.Space.chartFittingIdeal` are
exactly the chartwise Fitting ideal. -/
theorem mem_chartFittingIdeal_affine_iff (G : Modules.{u, m} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (k : ℤ) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (a : chartRing B S hS F hF U) :
    a ∈ (chartFittingIdeal G hG hfin k).toSubmodule.obj (op U) ↔
      a ∈ @_root_.fittingIdeal (chartRing B S hS F hF U) _ (G.val.obj (op U)) _ _
        (hfin U hU) k := by
  refine ⟨fun ha => ?_, fun ha W hW g => ?_⟩
  · have h := ha U hU (𝟙 U)
    rwa [chartRestrict_id, RingHom.id_apply] at h
  · have _ := hfin U hU
    have _ := hfin W hW
    rw [fittingIdealChart_baseChange_of_isCartesianOnAffineCharts G hG k hU hW g]
    exact Ideal.mem_map_of_mem _ ha

/-! ### The chain of Fitting ideal sheaves -/

variable (B S hS F hF)

open scoped Classical in
/-- **The `k`-th Fitting ideal sheaf of an `𝒪_F`-module, for `k : ℤ`**: the smallest sheaf of
ideals of `𝒪_F` whose sections over every affine étale chart contain the module-theoretic `k`-th
Fitting ideal of the sections of the module there.

For `k < 0` the chartwise ideal is zero, so `Fit₋₁(G) = 0`. -/
@[stacks 0CZ3 "the chain Fit_k, k : ℤ"]
noncomputable def fittingIdealInt (G : Modules.{u, m} B S hS F hF) (k : ℤ) :
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).Submodule := by
  classical
  exact sInf { I | ∀ U : SmallEtale B S hS F,
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
    ∀ a : chartRing B S hS F hF U, (if h : Module.Finite
        (chartRing B S hS F hF U) (G.val.obj (op U)) then
        a ∈ @_root_.fittingIdeal (chartRing B S hS F hF U) _ (G.val.obj (op U)) _ _ h k
      else False) → a ∈ I.toSubmodule.obj (op U) }

variable {B S hS F hF}

/-- `Fit_k(G)` is contained in every sheaf of ideals of `𝒪_F` whose sections over each affine
étale chart contain the chartwise Fitting ideal. -/
theorem fittingIdealInt_le (G : Modules.{u, m} B S hS F hF) (k : ℤ)
    {I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule}
    (hI : ∀ V : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V) →
      ∀ (b : chartRing B S hS F hF V)
        (h : Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V))),
        b ∈ @_root_.fittingIdeal (chartRing B S hS F hF V) _ (G.val.obj (op V)) _ _ h k →
          b ∈ I.toSubmodule.obj (op V)) :
    fittingIdealInt B S hS F hF G k ≤ I := by
  classical
  refine sInf_le ?_
  intro V hV b hb
  by_cases h : Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V))
  · exact hI V hV b h (by simpa [h] using hb)
  · simp [h] at hb

/-- Every section of the chartwise Fitting ideal over an affine étale chart is a section of
`Fit_k(G)` over that chart. -/
theorem mem_fittingIdealInt_of_mem_chart (G : Modules.{u, m} B S hS F hF) (k : ℤ)
    (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    [h : Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U))]
    (a : chartRing B S hS F hF U)
    (ha : a ∈ _root_.fittingIdeal (R := chartRing B S hS F hF U) (M := G.val.obj (op U)) k) :
    a ∈ (fittingIdealInt B S hS F hF G k).toSubmodule.obj (op U) := by
  classical
  refine (SheafOfModules.Submodule.mem_sInf_obj
    (M := SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) _
    (op U) a).mpr ?_
  intro I hI
  exact hI U hU a (by simpa using ⟨h, ha⟩)

/-! ### The characterisation of the chain by its sections -/

/-- A sheaf of ideals below `AlgebraicGeometry.Space.chartFittingIdeal` has sections over an affine
étale chart inside the chartwise Fitting ideal. -/
private theorem obj_le_fittingIdeal_of_le_chartFittingIdeal (G : Modules.{u, m} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (k : ℤ) {I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule}
    (hle : I ≤ chartFittingIdeal G hG hfin k) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    I.toSubmodule.obj (op U) ≤
      @_root_.fittingIdeal (chartRing B S hS F hF U) _ (G.val.obj (op U)) _ _ (hfin U hU) k :=
  fun a ha => (mem_chartFittingIdeal_affine_iff G hG hfin k hU a).mp
    ((PresheafOfModules.Submodule.le_iff.mp (SheafOfModules.Submodule.le_iff.mp hle)) (op U) ha)

/-- **Stacks 0CZ3: over an affine étale chart the sections of `Fit_k(G)` are exactly the
module-theoretic `k`-th Fitting ideal of the sections of `G` over the chart ring.**

One inclusion is the defining property of `AlgebraicGeometry.Space.fittingIdealInt`; the other
holds because the sections restricting into the chartwise Fitting ideals already form a sheaf of
ideals containing them, so the infimum is below it. -/
@[stacks 0CZ3 "the chartwise characterisation of the sections"]
theorem fittingIdealInt_obj_eq (G : Modules.{u, m} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (k : ℤ) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    (fittingIdealInt B S hS F hF G k).toSubmodule.obj (op U) =
      @_root_.fittingIdeal (chartRing B S hS F hF U) _ (G.val.obj (op U)) _ _ (hfin U hU) k := by
  have hle : fittingIdealInt B S hS F hF G k ≤ chartFittingIdeal G hG hfin k :=
    fittingIdealInt_le G k fun V hV b hbfin hb => by
      exact (mem_chartFittingIdeal_affine_iff G hG hfin k hV b).mpr hb
  refine le_antisymm (obj_le_fittingIdeal_of_le_chartFittingIdeal G hG hfin k hle hU)
    fun a ha => ?_
  · have _ := hfin U hU
    exact mem_fittingIdealInt_of_mem_chart G k U hU a ha

/-- **Stacks 0CZ3 for the `ℕ`-indexed Fitting ideal sheaf**: over an affine étale chart the
sections of `AlgebraicGeometry.Space.fittingIdeal` are exactly the chartwise Fitting ideal of
`AlgebraicGeometry.Space.fittingIdealOnChart`. -/
@[stacks 0CZ3 "the chartwise characterisation, in nonnegative degree"]
theorem fittingIdeal_obj_eq_fittingIdealOnChart (G : Modules.{u, m} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (r : ℕ) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    (fittingIdeal B S hS F hF G r).toSubmodule.obj (op U) =
      @fittingIdealOnChart B S hS F hF G r U (hfin U hU) := by
  have hle : fittingIdeal B S hS F hF G r ≤ chartFittingIdeal G hG hfin (r : ℤ) :=
    fittingIdeal_le G r fun V hV b hbfin hb => by
      exact (mem_chartFittingIdeal_affine_iff G hG hfin (r : ℤ) hV b).mpr hb
  refine le_antisymm (obj_le_fittingIdeal_of_le_chartFittingIdeal G hG hfin (r : ℤ) hle hU)
    fun a ha => ?_
  · have _ := hfin U hU
    exact mem_fittingIdeal_of_mem_fittingIdealOnChart G r U hU a ha

/-- The `ℤ`-indexed Fitting ideal sheaf agrees with the `ℕ`-indexed one in nonnegative degree. -/
theorem fittingIdealInt_natCast (G : Modules.{u, m} B S hS F hF) (r : ℕ) :
    fittingIdealInt B S hS F hF G (r : ℤ) = fittingIdeal B S hS F hF G r := by
  refine le_antisymm (fittingIdealInt_le G (r : ℤ) fun V hV b hbfin hb => ?_)
    (fittingIdeal_le G r fun V hV b hbfin hb => ?_)
  · have _ := hbfin
    exact mem_fittingIdeal_of_mem_fittingIdealOnChart G r V hV b hb
  · have _ := hbfin
    exact mem_fittingIdealInt_of_mem_chart G (r : ℤ) V hV b hb

/-! ### The two ends of the chain -/

/-- **`Fit₋₁(G) = 0`, and more generally the Fitting ideal sheaves vanish in negative degree**: in
negative degree the chartwise Fitting ideal is zero, so every sheaf of ideals belongs to the
family whose infimum defines `Fit_k(G)`. -/
@[stacks 0CZ3 "Fit_{-1} = 0"]
theorem fittingIdealInt_eq_bot_of_lt_zero (G : Modules.{u, m} B S hS F hF) {k : ℤ} (hk : k < 0) :
    fittingIdealInt B S hS F hF G k = ⊥ := by
  refine le_antisymm (fittingIdealInt_le G k fun V hV b h hb => ?_) bot_le
  have _ := h
  rw [fittingIdeal_eq_bot_of_lt_zero hk, Ideal.mem_bot] at hb
  rw [hb]
  exact Submodule.zero_mem _

/-- `Fit₋₁(G) = 0`. -/
theorem fittingIdealInt_neg_one (G : Modules.{u, m} B S hS F hF) :
    fittingIdealInt B S hS F hF G (-1) = ⊥ :=
  fittingIdealInt_eq_bot_of_lt_zero G (by norm_num)

/-- In negative degree the sections of `Fit_k(G)` over an affine étale chart are zero; for
`k = -1` this is the bottom `0 = Fit₋₁(G)` of the chain of Stacks 0CZ3. -/
theorem fittingIdealInt_obj_eq_bot_of_lt_zero (G : Modules.{u, m} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    {k : ℤ} (hk : k < 0) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    (fittingIdealInt B S hS F hF G k).toSubmodule.obj (op U) = ⊥ := by
  rw [fittingIdealInt_obj_eq G hG hfin k hU]
  exact @fittingIdeal_eq_bot_of_lt_zero (chartRing B S hS F hF U) _
    (G.val.obj (op U)) _ _ (hfin U hU) k hk

/-- Every member of the chain is a sheaf of ideals of `𝒪_F`, that is, `Fit_k(G) ⊆ 𝒪_F`: the top
of the chain of Stacks 0CZ3. -/
theorem fittingIdealInt_le_top (G : Modules.{u, m} B S hS F hF) (k : ℤ) :
    fittingIdealInt B S hS F hF G k ≤ ⊤ := le_top

/-- **The chain of Fitting ideal sheaves increases.**  A sheaf of ideals whose sections over every
affine étale chart contain the chartwise `Fit_l` contains the chartwise `Fit_k` there too, for
`k ≤ l`, so the family whose infimum is `Fit_l(G)` is contained in the family for `Fit_k(G)`. -/
@[stacks 0CZ3 "the chain increases"]
theorem monotone_fittingIdealInt (G : Modules.{u, m} B S hS F hF) :
    Monotone fun k : ℤ => fittingIdealInt B S hS F hF G k := by
  intro k l hkl
  refine fittingIdealInt_le G k fun V hV b h hb => ?_
  have _ := h
  exact mem_fittingIdealInt_of_mem_chart G l V hV b
    (Stacks.Fitting.fittingIdeal_monotone (R := chartRing B S hS F hF V)
      (M := G.val.obj (op V)) hkl hb)

/-! ### Stacks 0CZ3 -/

/-- **Stacks 0CZ3.**  For a finite type quasi-coherent `𝒪_X`-module `G` on an algebraic space `X`
the Fitting ideals form an increasing chain `0 = Fit₋₁(G) ⊆ Fit₀(G) ⊆ … ⊆ 𝒪_X` of sheaves of
ideals, characterised by: over every affine étale chart `U` the sections of `Fit_k(G)` are the
module-theoretic `k`-th Fitting ideal of the sections `G(U)` over the chart ring `𝒪_X(U)`.

The finiteness of the sections over every affine chart is the étale-local reading of finite type
used by the conventions of Stacks 0CZ3, under which the Fitting ideals are defined chartwise. -/
@[stacks 0CZ3]
theorem fittingIdealInt_chain (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : G.IsQuasicoherentOnSite)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W))) :
    fittingIdealInt B S hS X.1 X.2 G (-1) = ⊥ ∧
      Monotone (fun k : ℤ => fittingIdealInt B S hS X.1 X.2 G k) ∧
      (∀ k : ℤ, fittingIdealInt B S hS X.1 X.2 G k ≤ ⊤) ∧
      ∀ (k : ℤ) (U : SmallEtale B S hS X.1)
        (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)),
        (fittingIdealInt B S hS X.1 X.2 G k).toSubmodule.obj (op U) =
          @_root_.fittingIdeal (chartRing B S hS X.1 X.2 U) _ (G.val.obj (op U)) _ _
            (hfin U hU) k := by
  have hcart : IsCartesianOnAffineCharts G :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G hG
  exact ⟨fittingIdealInt_neg_one G, monotone_fittingIdealInt G,
    fun k => fittingIdealInt_le_top G k,
    fun k U hU => fittingIdealInt_obj_eq G hcart hfin k hU⟩

end AlgebraicGeometry.Space

end
