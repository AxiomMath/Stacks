module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchCriterion

/-!
# The functor of points of a branch of the zero scheme of a tensor product

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂`, let `i : D → Y` be the zero scheme of `s` and let
`q : T = Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y` be the ambient fibre product of [Stacks,
Tag 0F97], with `ι : L → T` the zero scheme of `z₁ ⊗ z₂ - q^*s` and `D₁`, `D₂` the two branches.
Viewing `Dᵢ` as a closed subscheme of `T` through `ιᵢ = (Dᵢ → L) ≫ ι`, this file proves

**a morphism `f : W ⟶ T` factors through `D₁` if and only if `f` kills `z₁` and `f ≫ q` factors
through `D`**,

and the same for `D₂` with `z₂`. Equivalently, the defining ideal of `Dᵢ` inside `T` is the join
`Z(zᵢ) ⊔ L` — the sum of the two ideals, which is the scheme-theoretic intersection of the two
closed subschemes.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.branchι₁` and `branchι₂`: the closed immersions `Dᵢ ⟶ T` of the
  two branches into the ambient fibre product.

## Main results

* `Stacks.Chow.TensorZeroScheme.factorsThrough_branch₁_iff` and `factorsThrough_branch₂_iff`:
  **the functor of points of the branch.**
* `Stacks.Chow.TensorZeroScheme.factorsThrough_branch₁_iff_factorsThrough_zeroIdeal` and
  `factorsThrough_branch₂_iff_factorsThrough_zeroIdeal`: the same, with the condition on `f ≫ q`
  written as a factorization through `i` rather than as an inclusion of ideal sheaves.
* `Stacks.Chow.TensorZeroScheme.ker_branchι₁` and `ker_branchι₂`: **the defining ideal of `Dᵢ`
  inside `T` is `Z(zᵢ) ⊔ L`.**
* `Stacks.Chow.TensorZeroScheme.branchι₁_comp_firstProj` and `branchι₂_comp_secondProj`: **the
  `i`-th coordinate of `Dᵢ` is the zero section** of the `i`-th line bundle, taken along the
  branch's own composite with `q`.

## Implementation notes

The forward direction of the criterion is the vanishing of the two sections on the subschemes
they cut out; the backward direction factors `f` through `ι` first, using that killing the
equation is implied by killing `zᵢ` together with the factorization of `f ≫ q` through `D`, and
then factors the result through `Dᵢ ⟶ L`. No ideal-theoretic computation is needed for the
criterion; the join identity is deduced from it afterwards, by applying the criterion to the
closed immersion of the join itself.

`Stacks.Chow.TensorZeroScheme.branchι₁_comp_firstProj` upgrades "`ι₁` composed with the first
projection factors through the zero section" to an identity, using that the zero section is a
section of the line bundle's structure morphism
(`Stacks.LineBundle.Situation.zeroSection_comp_totalSpaceToBase`); the factor is then forced to
be `ι₁ ≫ q`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

@[expose] public noncomputable section

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

/-- **The zero section of the line bundle of an invertible module is a section of its structure
morphism**, at the `Stacks.LineBundle.lineBundleProj` spelling of that morphism. -/
theorem zeroSection_comp_lineBundleProj (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] :
    (Stacks.LineBundle.inverseSituation Y M).zeroSection ≫
        Stacks.LineBundle.lineBundleProj Y M = CategoryStruct.id Y :=
  (Stacks.LineBundle.inverseSituation Y M).zeroSection_comp_totalSpaceToBase

/-- **A morphism to `Y` followed by the zero section is still a morphism over `Y`**: the
reassociated form of `Stacks.Chow.TensorZeroScheme.zeroSection_comp_lineBundleProj`. It is
stated separately because the contraction it performs occurs in every lift into the ambient
fibre product whose vanishing coordinate is the zero section, and a named theorem is checked
once where an inline chain is rechecked at each use. -/
theorem comp_zeroSection_comp_lineBundleProj {W : Scheme.{u}} (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (a : W ⟶ Y) :
    (a ≫ (Stacks.LineBundle.inverseSituation Y M).zeroSection) ≫
        Stacks.LineBundle.lineBundleProj Y M = a :=
  (Category.assoc a (Stacks.LineBundle.inverseSituation Y M).zeroSection
        (Stacks.LineBundle.lineBundleProj Y M)).trans
    ((congrArg (fun k : Y ⟶ Y => a ≫ k) (zeroSection_comp_lineBundleProj Y M)).trans
      (Category.comp_id a))

include h₁ h₂ in
/-- **The closed immersion `D₁ ⟶ T` of the first branch into the ambient fibre product.** -/
def branchι₁ : (branch₁ Y L₁ L₂ s).subscheme ⟶ totalSpace Y L₁ L₂ :=
  (branch₁ Y L₁ L₂ s).subschemeι ≫ spaceι Y L₁ L₂ s

include h₁ h₂ in
/-- **The closed immersion `D₂ ⟶ T` of the second branch into the ambient fibre product.** -/
def branchι₂ : (branch₂ Y L₁ L₂ s).subscheme ⟶ totalSpace Y L₁ L₂ :=
  (branch₂ Y L₁ L₂ s).subschemeι ≫ spaceι Y L₁ L₂ s

include h₁ h₂ in
/-- **The left-hand square of the diagram of [Stacks, Tag 0F97]**, read with `D₁` inside the
ambient fibre product: `p₁ ≫ i = ι₁ ≫ q`. -/
theorem proj₁_comp_zeroIdeal_subschemeι :
    proj₁ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι =
      branchι₁ Y L₁ L₂ s ≫ totalProj Y L₁ L₂ :=
  (branch₁_subschemeι_comp_proj Y L₁ L₂ s).symm.trans
    (Category.assoc ((branch₁ Y L₁ L₂ s).subschemeι) (spaceι Y L₁ L₂ s)
      (totalProj Y L₁ L₂)).symm

include h₁ h₂ in
/-- **The right-hand square of the diagram of [Stacks, Tag 0F97]**, read with `D₂` inside the
ambient fibre product: `p₂ ≫ i = ι₂ ≫ q`. -/
theorem proj₂_comp_zeroIdeal_subschemeι :
    proj₂ Y L₁ L₂ s ≫ (zeroIdeal Y L₁ L₂ s).subschemeι =
      branchι₂ Y L₁ L₂ s ≫ totalProj Y L₁ L₂ :=
  (branch₂_subschemeι_comp_proj Y L₁ L₂ s).symm.trans
    (Category.assoc ((branch₂ Y L₁ L₂ s).subschemeι) (spaceι Y L₁ L₂ s)
      (totalProj Y L₁ L₂)).symm

include h₁ h₂ in
/-- The first branch lies over `D`: the ideal of `D` lies in the kernel of `ι₁ ≫ q`. -/
theorem zeroIdeal_le_ker_branchι₁_comp_totalProj :
    zeroIdeal Y L₁ L₂ s ≤ (branchι₁ Y L₁ L₂ s ≫ totalProj Y L₁ L₂).ker :=
  (Stacks.Divisors.le_ker_iff_factorsThrough _ _).mpr
    ⟨proj₁ Y L₁ L₂ s, proj₁_comp_zeroIdeal_subschemeι Y L₁ L₂ s⟩

include h₁ h₂ in
/-- The second branch lies over `D`: the ideal of `D` lies in the kernel of `ι₂ ≫ q`. -/
theorem zeroIdeal_le_ker_branchι₂_comp_totalProj :
    zeroIdeal Y L₁ L₂ s ≤ (branchι₂ Y L₁ L₂ s ≫ totalProj Y L₁ L₂).ker :=
  (Stacks.Divisors.le_ker_iff_factorsThrough _ _).mpr
    ⟨proj₂ Y L₁ L₂ s, proj₂_comp_zeroIdeal_subschemeι Y L₁ L₂ s⟩

include h₁ h₂ in
/-- **The first fibre coordinate vanishes on the first branch.** -/
theorem pullbackGlobalSections_coord₁_branchι₁ :
    pullbackGlobalSections (branchι₁ Y L₁ L₂ s)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂) = 0 :=
  (pullbackGlobalSections_section₁_eq_zero_iff Y L₁ L₂ s
      ((branch₁ Y L₁ L₂ s).subschemeι)).mp
    ((Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme
      (spaceIdeal Y L₁ L₂ s).subscheme ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁)
      (section₁ Y L₁ L₂ s) ((branch₁ Y L₁ L₂ s).subschemeι)).mpr
      ⟨CategoryStruct.id _, Category.id_comp _⟩)

include h₁ h₂ in
/-- **The second fibre coordinate vanishes on the second branch.** -/
theorem pullbackGlobalSections_coord₂_branchι₂ :
    pullbackGlobalSections (branchι₂ Y L₁ L₂ s)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂) = 0 :=
  (pullbackGlobalSections_section₂_eq_zero_iff Y L₁ L₂ s
      ((branch₂ Y L₁ L₂ s).subschemeι)).mp
    ((Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme
      (spaceIdeal Y L₁ L₂ s).subscheme ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂)
      (section₂ Y L₁ L₂ s) ((branch₂ Y L₁ L₂ s).subschemeι)).mpr
      ⟨CategoryStruct.id _, Category.id_comp _⟩)

/-- A morphism `f : W ⟶ T` factors through `B ⟶ L ⟶ T`, for an ideal `B` of `L` cut out by the
vanishing of the coordinate `c`, exactly when it kills `c` and `f ≫ q` factors through `D`. -/
private theorem exists_comp_eq_iff_of_le_ker_iff
    (B : (spaceIdeal Y L₁ L₂ s).subscheme.IdealSheafData)
    (M : (totalSpace Y L₁ L₂).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (totalSpace Y L₁ L₂).sheaf.obj
      (totalSpace Y L₁ L₂).ringCatSheaf.property M]
    (c : Γ(M, ⊤))
    (hB : ∀ {W : Scheme.{u}} (f' : W ⟶ (spaceIdeal Y L₁ L₂ s).subscheme),
      B ≤ f'.ker ↔ pullbackGlobalSections (f' ≫ spaceι Y L₁ L₂ s) M c = 0)
    (hprod : ∀ {W : Scheme.{u}} (f : W ⟶ totalSpace Y L₁ L₂), pullbackGlobalSections f M c = 0 →
      pullbackGlobalSections f
        (Stacks.Divisors.tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)) (coordProduct Y L₁ L₂) = 0)
    (hD : zeroIdeal Y L₁ L₂ s ≤ ((B.subschemeι ≫ spaceι Y L₁ L₂ s) ≫ totalProj Y L₁ L₂).ker)
    {W : Scheme.{u}} (f : W ⟶ totalSpace Y L₁ L₂) :
    (∃ u : W ⟶ B.subscheme, u ≫ B.subschemeι ≫ spaceι Y L₁ L₂ s = f) ↔
      pullbackGlobalSections f M c = 0 ∧ zeroIdeal Y L₁ L₂ s ≤ (f ≫ totalProj Y L₁ L₂).ker := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨Stacks.Divisors.pullbackGlobalSections_comp_eq_zero u _ M c
      ((hB _).mp (Scheme.IdealSheafData.ker_subschemeι B).ge), ?_⟩
    rw [Category.assoc]
    exact hD.trans (Scheme.Hom.le_ker_comp u _)
  · rintro ⟨hc, hD'⟩
    have hsp : spaceIdeal Y L₁ L₂ s ≤ f.ker :=
      (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker
          (Stacks.Divisors.tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
            ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)) (equation Y L₁ L₂ s) f).mp
        ((pullbackGlobalSections_equation_eq_zero_iff Y L₁ L₂ s f (hprod f hc)).mpr hD')
    obtain ⟨f', hf'⟩ :=
      (Stacks.Divisors.le_ker_iff_factorsThrough (spaceIdeal Y L₁ L₂ s) f).mp hsp
    have hf'' : f' ≫ spaceι Y L₁ L₂ s = f := hf'
    obtain ⟨u, hu⟩ := (Stacks.Divisors.le_ker_iff_factorsThrough B f').mp
      ((hB f').mpr (by rwa [hf'']))
    exact ⟨u, by rw [← Category.assoc, hu, hf'']⟩

include h₁ h₂ in
/-- **The functor of points of the first branch**: a morphism to `T` factors through `D₁`
exactly when it kills `z₁` and the ideal of `D` lies in the kernel of its composite with
`q`. -/
theorem factorsThrough_branch₁_iff {W : Scheme.{u}} (f : W ⟶ totalSpace Y L₁ L₂) :
    (∃ u : W ⟶ (branch₁ Y L₁ L₂ s).subscheme, u ≫ branchι₁ Y L₁ L₂ s = f) ↔
      pullbackGlobalSections f ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
          (coord₁ Y L₁ L₂) = 0 ∧
        zeroIdeal Y L₁ L₂ s ≤ (f ≫ totalProj Y L₁ L₂).ker :=
  exists_comp_eq_iff_of_le_ker_iff Y L₁ L₂ s (branch₁ Y L₁ L₂ s) _ (coord₁ Y L₁ L₂)
    (fun f' => (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ (section₁ Y L₁ L₂ s)
      f').symm.trans (pullbackGlobalSections_section₁_eq_zero_iff Y L₁ L₂ s f'))
    (fun f hc => pullbackGlobalSections_coordProduct_eq_zero_of_coord₁ Y L₁ L₂ f hc)
    (zeroIdeal_le_ker_branchι₁_comp_totalProj Y L₁ L₂ s) f

include h₁ h₂ in
/-- **The functor of points of the second branch**: a morphism to `T` factors through `D₂`
exactly when it kills `z₂` and the ideal of `D` lies in the kernel of its composite with
`q`. -/
theorem factorsThrough_branch₂_iff {W : Scheme.{u}} (f : W ⟶ totalSpace Y L₁ L₂) :
    (∃ u : W ⟶ (branch₂ Y L₁ L₂ s).subscheme, u ≫ branchι₂ Y L₁ L₂ s = f) ↔
      pullbackGlobalSections f ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)
          (coord₂ Y L₁ L₂) = 0 ∧
        zeroIdeal Y L₁ L₂ s ≤ (f ≫ totalProj Y L₁ L₂).ker :=
  exists_comp_eq_iff_of_le_ker_iff Y L₁ L₂ s (branch₂ Y L₁ L₂ s) _ (coord₂ Y L₁ L₂)
    (fun f' => (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ (section₂ Y L₁ L₂ s)
      f').symm.trans (pullbackGlobalSections_section₂_eq_zero_iff Y L₁ L₂ s f'))
    (fun f hc => pullbackGlobalSections_coordProduct_eq_zero_of_coord₂ Y L₁ L₂ f hc)
    (zeroIdeal_le_ker_branchι₂_comp_totalProj Y L₁ L₂ s) f

include h₁ h₂ in
/-- **The functor of points of the first branch**, with the condition over `D` written as a
factorization through `i`. -/
theorem factorsThrough_branch₁_iff_factorsThrough_zeroIdeal {W : Scheme.{u}}
    (f : W ⟶ totalSpace Y L₁ L₂) :
    (∃ u : W ⟶ (branch₁ Y L₁ L₂ s).subscheme, u ≫ branchι₁ Y L₁ L₂ s = f) ↔
      pullbackGlobalSections f ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
          (coord₁ Y L₁ L₂) = 0 ∧
        ∃ h : W ⟶ (zeroIdeal Y L₁ L₂ s).subscheme,
          h ≫ (zeroIdeal Y L₁ L₂ s).subschemeι = f ≫ totalProj Y L₁ L₂ :=
  (factorsThrough_branch₁_iff Y L₁ L₂ s f).trans
    (and_congr_right' (Stacks.Divisors.le_ker_iff_factorsThrough (zeroIdeal Y L₁ L₂ s)
      (f ≫ totalProj Y L₁ L₂)))

include h₁ h₂ in
/-- **The functor of points of the second branch**, with the condition over `D` written as a
factorization through `i`. -/
theorem factorsThrough_branch₂_iff_factorsThrough_zeroIdeal {W : Scheme.{u}}
    (f : W ⟶ totalSpace Y L₁ L₂) :
    (∃ u : W ⟶ (branch₂ Y L₁ L₂ s).subscheme, u ≫ branchι₂ Y L₁ L₂ s = f) ↔
      pullbackGlobalSections f ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)
          (coord₂ Y L₁ L₂) = 0 ∧
        ∃ h : W ⟶ (zeroIdeal Y L₁ L₂ s).subscheme,
          h ≫ (zeroIdeal Y L₁ L₂ s).subschemeι = f ≫ totalProj Y L₁ L₂ :=
  (factorsThrough_branch₂_iff Y L₁ L₂ s f).trans
    (and_congr_right' (Stacks.Divisors.le_ker_iff_factorsThrough (zeroIdeal Y L₁ L₂ s)
      (f ≫ totalProj Y L₁ L₂)))

/-! ### The defining ideal of a branch inside the ambient fibre product -/

/-- The kernel of `B ⟶ L ⟶ T` is the join of the ideal of `L` and the zero ideal of the
coordinate `c`, as soon as `B ⟶ T` kills `c` and every morphism killing `c` and the equation
factors through it. -/
private theorem ker_comp_spaceι_eq_sup
    (B : (spaceIdeal Y L₁ L₂ s).subscheme.IdealSheafData)
    (M : (totalSpace Y L₁ L₂).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (totalSpace Y L₁ L₂).sheaf.obj
      (totalSpace Y L₁ L₂).ringCatSheaf.property M]
    (c : Γ(M, ⊤))
    (hc : pullbackGlobalSections (B.subschemeι ≫ spaceι Y L₁ L₂ s) M c = 0)
    (hcrit : ∀ {W : Scheme.{u}} (f : W ⟶ totalSpace Y L₁ L₂), pullbackGlobalSections f M c = 0 →
      pullbackGlobalSections f
        (Stacks.Divisors.tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)) (equation Y L₁ L₂ s) = 0 →
      ∃ u : W ⟶ B.subscheme, u ≫ B.subschemeι ≫ spaceι Y L₁ L₂ s = f) :
    (B.subschemeι ≫ spaceι Y L₁ L₂ s).ker =
      Stacks.Divisors.zeroScheme _ M c ⊔ spaceIdeal Y L₁ L₂ s := by
  refine le_antisymm ?_
    (sup_le ((Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ c _).mp hc) ?_)
  · have hker := Scheme.IdealSheafData.ker_subschemeι
      (Stacks.Divisors.zeroScheme _ M c ⊔ spaceIdeal Y L₁ L₂ s)
    obtain ⟨u, hu⟩ := hcrit _
      ((Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ c _).mpr
        (le_sup_left.trans hker.ge))
      ((Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ (equation Y L₁ L₂ s) _).mpr
        (le_sup_right.trans hker.ge))
    have h := Scheme.Hom.le_ker_comp u (B.subschemeι ≫ spaceι Y L₁ L₂ s)
    rwa [hu, hker] at h
  · exact (Scheme.IdealSheafData.ker_subschemeι (spaceIdeal Y L₁ L₂ s)).ge.trans
      (Scheme.Hom.le_ker_comp B.subschemeι (spaceι Y L₁ L₂ s))

include h₁ h₂ in
/-- **The defining ideal of `D₁` inside `T` is `Z(z₁) ⊔ L`.** The join is the sum of the two
ideals, which is the scheme-theoretic intersection of the two closed subschemes; in the order on
`AlgebraicGeometry.Scheme.IdealSheafData`, which is the order on ideals and so opposite to
inclusion of subschemes, a larger ideal is a smaller subscheme. -/
theorem ker_branchι₁ :
    (branchι₁ Y L₁ L₂ s).ker =
      Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂) ⊔
        spaceIdeal Y L₁ L₂ s :=
  ker_comp_spaceι_eq_sup Y L₁ L₂ s (branch₁ Y L₁ L₂ s) _ (coord₁ Y L₁ L₂)
    (pullbackGlobalSections_coord₁_branchι₁ Y L₁ L₂ s)
    (fun f hc he => (factorsThrough_branch₁_iff Y L₁ L₂ s f).mpr
      ⟨hc, (pullbackGlobalSections_equation_eq_zero_iff Y L₁ L₂ s f
        (pullbackGlobalSections_coordProduct_eq_zero_of_coord₁ Y L₁ L₂ f hc)).mp he⟩)

include h₁ h₂ in
/-- **The defining ideal of `D₂` inside `T` is `Z(z₂) ⊔ L`.** -/
theorem ker_branchι₂ :
    (branchι₂ Y L₁ L₂ s).ker =
      Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂) ⊔
        spaceIdeal Y L₁ L₂ s :=
  ker_comp_spaceι_eq_sup Y L₁ L₂ s (branch₂ Y L₁ L₂ s) _ (coord₂ Y L₁ L₂)
    (pullbackGlobalSections_coord₂_branchι₂ Y L₁ L₂ s)
    (fun f hc he => (factorsThrough_branch₂_iff Y L₁ L₂ s f).mpr
      ⟨hc, (pullbackGlobalSections_equation_eq_zero_iff Y L₁ L₂ s f
        (pullbackGlobalSections_coordProduct_eq_zero_of_coord₂ Y L₁ L₂ f hc)).mp he⟩)

/-! ### The vanishing coordinate of a branch is the zero section -/

/-- A morphism that is a zero section over some `g` is the zero section over its composite with
the structure morphism. -/
private theorem eq_comp_zeroSection_of_comp_lineBundleProj_eq {W : Scheme.{u}} (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (x : W ⟶ Stacks.LineBundle.lineBundleSpace Y M) (g h : W ⟶ Y)
    (hx : g ≫ (Stacks.LineBundle.inverseSituation Y M).zeroSection = x)
    (hh : x ≫ Stacks.LineBundle.lineBundleProj Y M = h) :
    x = h ≫ (Stacks.LineBundle.inverseSituation Y M).zeroSection := by
  subst hx hh
  exact congrArg (· ≫ (Stacks.LineBundle.inverseSituation Y M).zeroSection)
    (comp_zeroSection_comp_lineBundleProj Y M g).symm

include h₁ h₂ in
/-- **The first coordinate of the first branch is the zero section** of the first line bundle,
taken along the branch's own composite with `q`. -/
theorem branchι₁_comp_firstProj :
    branchι₁ Y L₁ L₂ s ≫ firstProj Y L₁ L₂ =
      (branchι₁ Y L₁ L₂ s ≫ totalProj Y L₁ L₂) ≫
        (Stacks.LineBundle.inverseSituation Y L₁).zeroSection := by
  obtain ⟨g, hg⟩ := (pullbackGlobalSections_coord₁_eq_zero_iff Y L₁ L₂
    (branchι₁ Y L₁ L₂ s)).mp (pullbackGlobalSections_coord₁_branchι₁ Y L₁ L₂ s)
  exact eq_comp_zeroSection_of_comp_lineBundleProj_eq Y L₁ _ g _ hg
    (by rw [Category.assoc]; rfl)

include h₁ h₂ in
/-- **The second coordinate of the second branch is the zero section** of the second line
bundle. -/
theorem branchι₂_comp_secondProj :
    branchι₂ Y L₁ L₂ s ≫ secondProj Y L₁ L₂ =
      (branchι₂ Y L₁ L₂ s ≫ totalProj Y L₁ L₂) ≫
        (Stacks.LineBundle.inverseSituation Y L₂).zeroSection := by
  obtain ⟨g, hg⟩ := (pullbackGlobalSections_coord₂_eq_zero_iff Y L₁ L₂
    (branchι₂ Y L₁ L₂ s)).mp (pullbackGlobalSections_coord₂_branchι₂ Y L₁ L₂ s)
  exact eq_comp_zeroSection_of_comp_lineBundleProj_eq Y L₂ _ g _ hg
    (by rw [Category.assoc, secondProj_comp])

end Stacks.Chow.TensorZeroScheme

end
