module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule

/-!
# Sections of a sheaf of ideals and of a submodule over an étale chart

Let `F` be an algebraic space, let `I ⊆ 𝒪_F` be a sheaf of ideals and let `M` be an
`𝒪_F`-module on the small étale site of `F`.  Over an étale chart `U` the sections of `I`, of its
powers `Iⁿ` and of a submodule `N ⊆ M` form an ideal of, respectively a submodule over, the ring
`𝒪_F(U)` of regular functions on the chart.

## Main definitions

* `AlgebraicGeometry.Space.chartSectionIdeal`: the ideal `I(U) ⊆ 𝒪_F(U)`.
* `AlgebraicGeometry.Space.chartIdealPow`: the ideal `Iⁿ(U) ⊆ 𝒪_F(U)`.
* `AlgebraicGeometry.Space.chartSubmodule`: the `𝒪_F(U)`-submodule `N(U) ⊆ M(U)`.

## Main results

* `AlgebraicGeometry.Space.mem_idealPowSmul_of_sieve` and
  `AlgebraicGeometry.Space.exists_sieve_of_mem_idealPowSmul`: a section of `M` over a chart is a
  section of `Iⁿ · N` exactly when it restricts into the objectwise product `Iⁿ(·) · N(·)` along
  some covering sieve.  Membership in the product is local, so this is its defining property.
* `AlgebraicGeometry.Space.pow_chartSectionIdeal_le_chartIdealPow` and
  `AlgebraicGeometry.Space.pow_chartSectionIdeal_smul_top_le_chartSubmodule`: an honest `n`-fold
  product of sections of `I` is a section of `Iⁿ`, and such a product times a section of `M` is a
  section of `Iⁿ M`.  The converses are only local.

## Implementation notes

A sheaf of ideals indexes its sections by the objects of the small étale ringed site, whereas
`AlgebraicGeometry.Space.chartRing` indexes them by the étale charts; the two indexings agree
only once the ringed site is unfolded.  The three definitions above are therefore ordinary
definitions rather than abbreviations, so that their signatures mention only `chartRing` and
every goal built from them stays type-correct at `implicit` transparency.
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The structure sheaf of the small étale ringed site of an algebraic space, as a sheaf of
commutative rings.  Named so that the sheaf of ideals it carries can be spelled out where the
elaborator cannot recover it from a sheaf of ideals alone. -/
abbrev siteStructure : CategoryTheory.Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u} :=
  (smallEtaleRingedSite B S hS F hF).O

/-! ### The ideal of sections of a sheaf of ideals -/

/-- The ideal `I(U) ⊆ 𝒪_F(U)` of sections of a sheaf of ideals over an étale chart. -/
noncomputable def chartSectionIdeal (I : IdealSheaves B S hS F hF)
    (U : SmallEtale B S hS F) : Ideal (chartRing B S hS F hF U) :=
  I.obj (op U)

/-- Membership in the ideal of sections over a chart is membership in the sheaf of ideals. -/
theorem mem_chartSectionIdeal_iff (I : IdealSheaves B S hS F hF) (U : SmallEtale B S hS F)
    {a : chartRing B S hS F hF U} :
    a ∈ chartSectionIdeal B S hS F hF I U ↔ a ∈ I.obj (op U) :=
  Iff.rfl

/-- The ideal of sections over a chart is the ideal of sections of the sheaf of ideals there. -/
theorem chartSectionIdeal_eq_ringSectionIdeal (I : IdealSheaves B S hS F hF)
    (U : SmallEtale B S hS F) :
    chartSectionIdeal B S hS F hF I U = Stacks.Sites.ringSectionIdeal I (op U) :=
  rfl

/-- The ideal `Iⁿ(U) ⊆ 𝒪_F(U)` of sections of the `n`-th power of a sheaf of ideals over an étale
chart. -/
noncomputable def chartIdealPow (I : IdealSheaves B S hS F hF) (n : ℕ)
    (U : SmallEtale B S hS F) : Ideal (chartRing B S hS F hF U) :=
  (Stacks.Sites.idealPow (O := siteStructure B S hS F hF) I n).obj (op U)

/-- Membership in the ideal of sections of `Iⁿ` over a chart is membership in `Iⁿ`. -/
theorem mem_chartIdealPow_iff (I : IdealSheaves B S hS F hF) (n : ℕ)
    (U : SmallEtale B S hS F) {a : chartRing B S hS F hF U} :
    a ∈ chartIdealPow B S hS F hF I n U ↔
      a ∈ (Stacks.SheafOfModules.sheafifySubmodule
        (Stacks.Sites.presheafIdealPow (O := siteStructure B S hS F hF) I n)).obj (op U) :=
  Iff.rfl

/-- An `n`-fold product of sections of a sheaf of ideals is a section of its `n`-th power. -/
theorem pow_chartSectionIdeal_le_chartIdealPow (I : IdealSheaves B S hS F hF) (n : ℕ)
    (U : SmallEtale B S hS F) :
    chartSectionIdeal B S hS F hF I U ^ n ≤ chartIdealPow B S hS F hF I n U :=
  fun _ ha => Stacks.Sites.mem_idealPow_of_mem_pow I n ha

/-- Restriction carries the `n`-th power of the ideal of sections of a sheaf of ideals into the
`n`-th power of the ideal of sections over the smaller chart. -/
theorem chartRestrict_mem_pow_chartSectionIdeal (I : IdealSheaves B S hS F hF)
    {X Y : SmallEtale B S hS F} (f : Y ⟶ X) (n : ℕ)
    {r : chartRing B S hS F hF X} (hr : r ∈ chartSectionIdeal B S hS F hF I X ^ n) :
    chartRestrict (hF := hF) f r ∈ chartSectionIdeal B S hS F hF I Y ^ n := by
  have h1 : Ideal.map (chartRestrict (hF := hF) f) (chartSectionIdeal B S hS F hF I X)
      ≤ chartSectionIdeal B S hS F hF I Y :=
    Ideal.map_le_iff_le_comap.2 fun _ ha => I.map_mem f.op ha
  have h2 := Ideal.pow_right_mono h1 n
  rw [← Ideal.map_pow] at h2
  exact h2 (Ideal.mem_map_of_mem _ hr)

/-! ### The sections of a submodule of an `𝒪_F`-module -/

/-- The `𝒪_F(U)`-submodule `N(U) ⊆ M(U)` of sections of a submodule of an `𝒪_F`-module over an
étale chart. -/
noncomputable def chartSubmodule {M : Modules.{u, m} B S hS F hF} (N : M.Submodule)
    (U : SmallEtale B S hS F) : Submodule (chartRing B S hS F hF U) (M.val.obj (op U)) :=
  N.obj (op U)

/-- Restriction carries the sections of a submodule over a chart into its sections over a
smaller chart. -/
theorem chartRestrictLinear_mem_chartSubmodule {M : Modules.{u, m} B S hS F hF}
    (N : M.Submodule) {U V : SmallEtale B S hS F} (φ : V ⟶ U) {x : M.val.obj (op U)}
    (hx : x ∈ chartSubmodule B S hS F hF N U) :
    chartRestrictLinear M φ x ∈ chartSubmodule B S hS F hF N V :=
  N.map_mem φ.op hx

/-- The `b`-th power of the ideal of sections times the sections of a module lies in the
sections of `Iᵇ M`. -/
theorem pow_chartSectionIdeal_smul_top_le_chartSubmodule (I : IdealSheaves B S hS F hF) (b : ℕ)
    {M : Modules.{u, m} B S hS F hF} (U : SmallEtale B S hS F) :
    chartSectionIdeal B S hS F hF I U ^ b •
        (⊤ : Submodule (chartRing B S hS F hF U) (M.val.obj (op U)))
      ≤ chartSubmodule B S hS F hF (idealPowSubmodule I b M) U :=
  Submodule.smul_le.2 fun _ hs mm _ => smul_mem_idealPowSubmodule_of_mem_pow I b hs mm

/-- Restriction carries the objectwise product `Iⁿ(X) · M(X)` into `Iⁿ(Y) · M(Y)`. -/
theorem map_mem_pow_chartSectionIdeal_smul_top (I : IdealSheaves B S hS F hF)
    (M : Modules.{u, m} B S hS F hF) {X Y : SmallEtale B S hS F} (f : Y ⟶ X)
    (n : ℕ) {x : M.val.obj (op X)}
    (hx : x ∈ chartSectionIdeal B S hS F hF I X ^ n •
      (⊤ : Submodule (chartRing B S hS F hF X) (M.val.obj (op X)))) :
    chartRestrictLinear M f x ∈ chartSectionIdeal B S hS F hF I Y ^ n •
      (⊤ : Submodule (chartRing B S hS F hF Y) (M.val.obj (op Y))) := by
  refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun y z hy hz => ?_)
  · rw [chartRestrictLinear_smul M]
    exact Submodule.smul_mem_smul
      (chartRestrict_mem_pow_chartSectionIdeal B S hS F hF I f n hr) Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hy hz

/-! ### The product `Iⁿ · N`, read on sections -/

/-- The objectwise product of the `n`-th power of a sheaf of ideals with an objectwise submodule
is the product of the ideal of sections with the sections. -/
theorem presheafIdealSmul_obj_eq (I : IdealSheaves B S hS F hF) (n : ℕ)
    {M : Modules.{u, m} B S hS F hF} (N : M.Submodule) (U : SmallEtale B S hS F) :
    chartIdealPow B S hS F hF I n U • chartSubmodule B S hS F hF N U
      = (Stacks.Sites.presheafIdealSmul (O := siteStructure B S hS F hF) (M := M)
        (Stacks.Sites.idealPow (O := siteStructure B S hS F hF) I n)
        N.toSubmodule).obj (op U) :=
  (Stacks.Sites.presheafIdealSmul_obj (O := siteStructure B S hS F hF) (M := M)
    (Stacks.Sites.idealPow (O := siteStructure B S hS F hF) I n) N.toSubmodule (op U)).symm

/-- Restriction carries the objectwise product `Iⁿ(U) · N(U)` into `Iⁿ(V) · N(V)`. -/
theorem chartRestrictLinear_mem_chartIdealPow_smul (I : IdealSheaves B S hS F hF) (n : ℕ)
    {M : Modules.{u, m} B S hS F hF} (N : M.Submodule) {U V : SmallEtale B S hS F} (φ : V ⟶ U)
    {x : M.val.obj (op U)}
    (hx : x ∈ chartIdealPow B S hS F hF I n U • chartSubmodule B S hS F hF N U) :
    chartRestrictLinear M φ x
      ∈ chartIdealPow B S hS F hF I n V • chartSubmodule B S hS F hF N V := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun y z hy hz => ?_)
  · rw [chartRestrictLinear_smul M]
    exact Submodule.smul_mem_smul
      ((Stacks.Sites.idealPow (O := siteStructure B S hS F hF) I n).map_mem φ.op hr)
      (chartRestrictLinear_mem_chartSubmodule B S hS F hF N φ hy)
  · rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- **A section lying in the objectwise product `Iⁿ · N` on a covering sieve is a section of
`Iⁿ · N`.**  Membership in the product is local, so this is its defining property. -/
theorem mem_idealPowSmul_of_sieve (I : IdealSheaves B S hS F hF) (n : ℕ)
    {M : Modules.{u, m} B S hS F hF} (N : M.Submodule) {U : SmallEtale B S hS F}
    {x : M.val.obj (op U)} {Sv : Sieve U} (hSv : Sv ∈ SmallEtale.topology B S hS F U)
    (hx : ∀ ⦃Y : SmallEtale B S hS F⦄ (f : Y ⟶ U), Sv f → chartRestrictLinear M f x
      ∈ chartIdealPow B S hS F hF I n Y • chartSubmodule B S hS F hF N Y) :
    x ∈ (Stacks.Sites.idealPowSmul I n N).obj (op U) :=
  Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem (S := Sv) hSv fun _ f hf =>
    (presheafIdealSmul_obj_eq B S hS F hF I n N _).le (hx f hf)

/-- **A section of `Iⁿ · N` restricts into the objectwise product along a covering sieve.** -/
theorem exists_sieve_of_mem_idealPowSmul (I : IdealSheaves B S hS F hF) (n : ℕ)
    {M : Modules.{u, m} B S hS F hF} (N : M.Submodule) {U : SmallEtale B S hS F}
    {x : M.val.obj (op U)} (hx : x ∈ (Stacks.Sites.idealPowSmul I n N).obj (op U)) :
    ∃ Sv : Sieve U, Sv ∈ SmallEtale.topology B S hS F U ∧
      ∀ ⦃Y : SmallEtale B S hS F⦄ (f : Y ⟶ U), Sv f → chartRestrictLinear M f x
        ∈ chartIdealPow B S hS F hF I n Y • chartSubmodule B S hS F hF N Y := by
  obtain ⟨Sv, hSv, h⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule hx
  refine ⟨Sv, hSv, fun {Y} f hf => ?_⟩
  exact (presheafIdealSmul_obj_eq B S hS F hF I n N Y).ge (h f hf)

end AlgebraicGeometry.Space

end
