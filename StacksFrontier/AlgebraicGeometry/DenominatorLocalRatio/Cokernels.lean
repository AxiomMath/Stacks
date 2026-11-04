module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian
public import StacksFrontier.AlgebraicGeometry.DenominatorIdealSupport.Basic
public import StacksFrontier.AlgebraicGeometry.DenominatorLocalRatio.Basic
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection

/-!
# The cokernel of the denominator ideal inclusion is supported on a nowhere dense closed set

For an invertible sheaf `L` on a scheme `X` and a meromorphic section `s` of `L`, the cokernel of
the inclusion of the denominator ideal of `s` in `𝒪_X` is supported on a closed nowhere dense
subset of `X`.

## Main results

* `dense_iSup_basicOpen`: the union of the basic opens of a family of local nonzerodivisors is
  dense.
* `notMem_supp_cokernel`: a point near which a morphism of sheaves of modules is sectionwise
  surjective is not in the support of its cokernel.
* `denominatorIdeal_inclusion_support`: the cokernel of the inclusion of the denominator ideal in
  the structure sheaf is supported on a closed nowhere dense subset.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorIdealResidue

universe u

namespace Stacks.DenominatorCokernel

variable (X : Scheme.{u})

/-! ### Density of the basic open of a nonzerodivisor -/

/-- **The basic open of a nonzerodivisor meets every nonempty open subset of its affine open.** -/
lemma exists_mem_basicOpen_of_mem {U : Opens X} (hU : IsAffineOpen U) {b : Γ(X, U)}
    (hb : b ∈ nonZeroDivisors Γ(X, U)) {V : Opens X} (hVU : V ≤ U) {y : X} (hy : y ∈ V) :
    ∃ z : X, z ∈ V ∧ z ∈ X.basicOpen b := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  obtain ⟨g, hgV, hyg⟩ := hU.exists_basicOpen_le (⟨y, hy⟩ : V) (hVU hy)
  have hloc := hU.isLocalization_basicOpen g
  have hb'nzd : X.presheaf.map (homOfLE (X.basicOpen_le g)).op b ∈
      nonZeroDivisors Γ(X, X.basicOpen g) :=
    (IsLocalization.nonZeroDivisors_le_comap (M := Submonoid.powers g)
      (S := Γ(X, X.basicOpen g))) hb
  have hbot : X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le g)).op b) = ⊥ := by
    rw [X.basicOpen_res]
    refine le_antisymm (fun w hw => ?_) bot_le
    exact absurd hw.2 (hcon w (hgV hw.1))
  have hVbot : X.basicOpen g = ⊥ :=
    Stacks.IdealSheafSupport.eq_bot_of_subset_zeroLocus ⟨X.basicOpen g, hU.basicOpen g⟩
      (s := {X.presheaf.map (homOfLE (X.basicOpen_le g)).op b}) rfl hb'nzd
      (fun w _ => (X.mem_zeroLocus_iff _ w).mpr (fun _ hf => by rw [hf, hbot]; exact fun h => h))
  rw [hVbot] at hyg
  simp at hyg

/-- **The union of the basic opens of a family of local nonzerodivisors is dense.** -/
lemma dense_iSup_basicOpen (V : X → Opens X) (hV : ∀ x, x ∈ V x)
    (hVaff : ∀ x, IsAffineOpen (V x)) (b : ∀ x, Γ(X, V x))
    (hb : ∀ x, b x ∈ nonZeroDivisors Γ(X, V x)) :
    Dense (((⨆ x, X.basicOpen (b x) : Opens X)) : Set X) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨y, hy⟩ := hUne
  obtain ⟨z, hz, hzb⟩ := exists_mem_basicOpen_of_mem X (hVaff y) (hb y)
    (V := ⟨U, hU⟩ ⊓ V y) inf_le_right (y := y) ⟨hy, hV y⟩
  exact ⟨z, hz.1, Opens.mem_iSup.mpr ⟨y, hzb⟩⟩

/-- **The complement of the union of the basic opens of a family of local nonzerodivisors is
closed and nowhere dense.** -/
lemma isClosed_isNowhereDense_compl_iSup_basicOpen (V : X → Opens X) (hV : ∀ x, x ∈ V x)
    (hVaff : ∀ x, IsAffineOpen (V x)) (b : ∀ x, Γ(X, V x))
    (hb : ∀ x, b x ∈ nonZeroDivisors Γ(X, V x)) :
    IsClosed ((((⨆ x, X.basicOpen (b x) : Opens X)) : Set X)ᶜ) ∧
      IsNowhereDense ((((⨆ x, X.basicOpen (b x) : Opens X)) : Set X)ᶜ) := by
  rw [isClosed_isNowhereDense_iff_compl, compl_compl]
  exact ⟨(⨆ x, X.basicOpen (b x) : Opens X).isOpen,
    dense_iSup_basicOpen X V hV hVaff b hb⟩

/-! ### The support of a cokernel -/

variable (L : SheafOfModules.{u} (O X))

/-- A sheaf of modules on a scheme, read as a sheaf of modules on the underlying ringed space. -/
abbrev asModuleSheaf (F : SheafOfModules.{u} (O X)) :
    RingedSpace.ModuleSheaf.{u} X.toRingedSpace :=
  ⟨F.val, F.isSheaf⟩

/-- **A point near which a morphism of sheaves of modules is sectionwise surjective is not in
the support of its cokernel.** -/
lemma notMem_supp_cokernel {M N : SheafOfModules.{u} (O X)} (φ : M ⟶ N) (x : X)
    (hsurj : ∀ U : Opens X, x ∈ U → ∃ V : Opens X, V ≤ U ∧ x ∈ V ∧
      ∀ n : N.val.obj (op V), ∃ m : M.val.obj (op V), φ.val.app (op V) m = n) :
    x ∉ (asModuleSheaf X (cokernel φ)).supp := by
  rintro ⟨a, ha⟩
  obtain ⟨U, hxU, q, hq⟩ := TopCat.Presheaf.exists_germ_eq
    (asModuleSheaf X (cokernel φ)).abPresheaf a
  have hls := SheafOfModules.cokernel_isLocallySurjective φ (cokernel.π φ)
    (cokernel.condition φ) (cokernelIsCokernel φ)
  obtain ⟨V, hVU, ⟨n, hn⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hls U q x hxU
  obtain ⟨V', hV'V, hxV', hsur⟩ := hsurj V hxV
  obtain ⟨m, hm⟩ := hsur (N.val.map (homOfLE hV'V).op n)
  have hπ0 : (cokernel.π φ).val.app (op V') (φ.val.app (op V') m) = 0 := by
    have h0 := ConcreteCategory.congr_hom
      (congrArg (fun ψ : M ⟶ cokernel φ => ψ.val.app (op V')) (cokernel.condition φ)) m
    exact h0
  have hn' : (cokernel.π φ).val.app (op V) n =
      (cokernel φ).val.map (homOfLE hVU).op q := hn
  have hzero : (asModuleSheaf X (cokernel φ)).abPresheaf.map
      ((homOfLE hV'V ≫ homOfLE hVU) : V' ⟶ U).op q = 0 := by
    have e1 : (asModuleSheaf X (cokernel φ)).abPresheaf.map
        ((homOfLE hV'V ≫ homOfLE hVU) : V' ⟶ U).op q =
        (cokernel φ).val.map (homOfLE hV'V).op ((cokernel.π φ).val.app (op V) n) := by
      rw [hn']
      exact PresheafOfModules.map_comp_apply (cokernel φ).val
        (homOfLE hVU).op (homOfLE hV'V).op q
    rw [e1, ← PresheafOfModules.naturality_apply (cokernel.π φ).val (homOfLE hV'V).op n,
      ← hm, hπ0]
    rfl
  apply ha
  rw [← hq, ← TopCat.Presheaf.germ_res_apply (asModuleSheaf X (cokernel φ)).abPresheaf
    ((homOfLE hV'V ≫ homOfLE hVU) : V' ⟶ U) x hxV' q, hzero, map_zero]

/-! ### The cokernel of the ideal inclusion -/

/-- A section of the structure sheaf restricts to a unit on any open set inside its basic
open. -/
lemma isUnit_res_of_le_basicOpen {V : Opens X} (b : Γ(X, V)) {W : Opens X}
    (hW : W ≤ X.basicOpen b) (hWV : W ≤ V) :
    IsUnit (X.presheaf.map (homOfLE hWV).op b) := by
  have h2 := (X.toRingedSpace.isUnit_res_basicOpen b).map
    (X.presheaf.map (homOfLE hW).op).hom
  have key : X.presheaf.map (homOfLE hWV).op b =
      (X.presheaf.map (homOfLE (X.basicOpen_le b)).op ≫
        X.presheaf.map (homOfLE hW).op) b :=
    ConcreteCategory.congr_hom (X.presheaf.map_comp
      (homOfLE (X.basicOpen_le b)).op (homOfLE hW).op) b
  rw [key]
  exact h2

variable (s : MeromorphicSection.{u, u} X.sheaf L)

/-- The denominator relation restricts to a smaller open set. -/
lemma toK_app_eq_sectionMap_app_restrict {V W : Opens X} (hWV : W ≤ V)
    (b : (((SheafOfModules.unit (O X)).val.obj (op V)) : Type u))
    (t : (L.val.obj (op V) : Type u))
    (hbt : (toK X L).val.app (op V) t = (sectionMap X L s).val.app (op V) b)
    (cm : (((SheafOfModules.unit (O X)).val.obj (op W)) : Type u))
    (hcm : (SheafOfModules.unit (O X)).val.map (homOfLE hWV).op b = cm)
    (tm : (L.val.obj (op W) : Type u)) (htm : L.val.map (homOfLE hWV).op t = tm) :
    (toK X L).val.app (op W) tm = (sectionMap X L s).val.app (op W) cm := by
  rw [← hcm, ← htm, PresheafOfModules.naturality_apply (sectionMap X L s).val (homOfLE hWV).op b,
    PresheafOfModules.naturality_apply (toK X L).val (homOfLE hWV).op t, hbt]

/-- **Where a denominator is invertible, every section of the structure sheaf is a denominator.**
If `cm · s` is regular over `W` and `cm` is a unit there, then every `n ∈ 𝒪_X(W)` is the image of
a section of the denominator ideal over `W`. -/
lemma exists_eq_denominatorIdealι_app {W : Opens X}
    (cm : (((SheafOfModules.unit (O X)).val.obj (op W)) : Type u))
    (tm : (L.val.obj (op W) : Type u))
    (hbt : (toK X L).val.app (op W) tm = (sectionMap X L s).val.app (op W) cm)
    (c : Stacks.DenominatorLocalRatio.oScalar X W) (hc : cm = c) (hu : IsUnit c)
    (n : Stacks.DenominatorLocalRatio.oScalar X W) :
    ∃ d : (denominatorIdeal X L s).val.obj (op W),
      (denominatorIdealι X L s).val.app (op W) d = n := by
  obtain ⟨u, hu'⟩ := hu
  have hn : n = (n * (↑u⁻¹ : Stacks.DenominatorLocalRatio.oScalar X W)) • cm := by
    rw [hc, ← hu']
    show n = n * (↑u⁻¹ : Stacks.DenominatorLocalRatio.oScalar X W) *
      (↑u : Stacks.DenominatorLocalRatio.oScalar X W)
    rw [mul_assoc, Units.inv_mul, mul_one]
  refine (denominatorIdeal_sections X L s W n).mpr
    ⟨(n * (↑u⁻¹ : Stacks.DenominatorLocalRatio.oScalar X W)) • tm, ?_⟩
  conv_lhs => rw [hn, map_smul, ← hbt]
  rw [← map_smul]

/-- **The cokernel of the inclusion of the denominator ideal in the structure sheaf is supported
on a closed nowhere dense subset.** -/
@[stacks 02P0 "support of the first cokernel"]
theorem denominatorIdeal_inclusion_support
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L) :
    ∃ T : Set X, IsClosed T ∧ IsNowhereDense T ∧
      (asModuleSheaf X (cokernel (denominatorIdealι X L s))).supp ⊆ T := by
  choose V _ hxV hVaff _ b hb t hbt using fun x : X =>
    Stacks.DenominatorLocalRatio.exists_affineOpen_denominator X L s hL ⊤ x (Opens.mem_top x)
  obtain ⟨hTclosed, hTnd⟩ :=
    isClosed_isNowhereDense_compl_iSup_basicOpen X V hxV hVaff b hb
  refine ⟨_, hTclosed, hTnd, fun y hy => ?_⟩
  intro hyW
  obtain ⟨x, hx⟩ := Opens.mem_iSup.mp hyW
  refine notMem_supp_cokernel X (denominatorIdealι X L s) y (fun U hyU => ?_) hy
  refine ⟨U ⊓ X.basicOpen (b x), inf_le_left, ⟨hyU, hx⟩, fun n => ?_⟩
  exact exists_eq_denominatorIdealι_app X L s _ _
    (toK_app_eq_sectionMap_app_restrict X L s
      (inf_le_right.trans (X.basicOpen_le (b x))) (b x) (t x) (hbt x) _ rfl _ rfl)
    _ rfl
    (isUnit_res_of_le_basicOpen X (b x) inf_le_right
      (inf_le_right.trans (X.basicOpen_le (b x)))) n

end Stacks.DenominatorCokernel

end
