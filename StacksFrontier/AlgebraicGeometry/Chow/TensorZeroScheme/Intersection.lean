module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchLineBundle

/-!
# The intersection of the two branches of the zero scheme of a tensor product

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be the zero scheme of `s`, as in [Stacks, Tag 0F97], with
`q : T = Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y` the ambient fibre product, `ι : L → T` the zero
scheme of `z₁ ⊗ z₂ - q^*s` and `D₁`, `D₂` the two branches. This file proves the tag's conditions
(6) and (7):

**the scheme-theoretic intersection `D₁ ∩ D₂` maps isomorphically to `D`, and the resulting
closed immersion `D₁ ∩ D₂ ⟶ D₁` is the zero section of the line bundle `D₁ ⟶ D`.**

The scheme-theoretic intersection is the join `D₁ ⊔ D₂` of ideal sheaves, the order on
`AlgebraicGeometry.Scheme.IdealSheafData` being the order on ideals and so opposite to inclusion
of subschemes.

Both conditions come from one computation. A morphism to `T` factors through `D₁` exactly when it
kills `z₁` and lies over `D`, and through `D₂` exactly when it kills `z₂` and lies over `D`
(`Stacks.Chow.TensorZeroScheme.factorsThrough_branch₁_iff`); killing both coordinates is, by
[Stacks, Tag 0F96](1) applied to each of the two line bundle factors, the same as factoring
through the zero section of `T`. So `D₁ ∩ D₂` inside `T` is the zero section of `T` restricted to
`D`, which is a copy of `D`.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.totalSpaceZeroSection`: **the zero section `Y ⟶ T`** of the
  ambient fibre product.
* `Stacks.Chow.TensorZeroScheme.zeroSectionOverZeroIdeal`: its restriction `D ⟶ T` to `D`, which
  is the inverse of the isomorphism of condition (6).

## Main results

* `Stacks.Chow.TensorZeroScheme.inclusion_comp_branchι₁_eq`: **the intersection, read inside `T`,
  is the zero section of `T` over `D`.**
* `Stacks.Chow.TensorZeroScheme.isIso_intersection_proj₁`: **[Stacks, Tag 0F97](6)**.
* `Stacks.Chow.TensorZeroScheme.intersection_comp_branchIso₁` and
  `intersection_comp_branchIso₂`: **[Stacks, Tag 0F97](7)**, for the identifications
  `Stacks.Chow.TensorZeroScheme.branchIso₁` and `branchIso₂` of condition (4).

## Implementation notes

The inverse of the morphism of condition (6) is written down rather than produced from an
abstract criterion: it is the zero section of `T` restricted to `D`, which factors through both
branches by the factorization criterion and hence through their intersection, the two factors
agreeing because `ι` is a monomorphism. Both composites are then checked by cancelling a
monomorphism, so no computation with sections occurs here beyond the two vanishing statements
that produce the factorizations.

Condition (7) is stated for the identification `Stacks.Chow.TensorZeroScheme.branchIso₁` of
condition (4) constructed in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchLineBundle`, as the tag's
`Decomposition` record takes a chosen identification and constrains that same one. It reduces,
through `zeroSectionFibreProduct₁_comp_branchBundleIso₁_hom`, to an identity of morphisms into
the fibre product `D ×_Y Tot(L₂^{⊗ -1})`, which is checked on the two coordinates: over `D` it is
the definition of `p₁`, and in the line bundle it is the vanishing of the second fibre coordinate
on the intersection — which holds because the intersection, mapped into `T`, also factors through
`D₂`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

/-! ### The zero section of the ambient fibre product -/

include h₁ h₂ in
/-- **The zero section `Y ⟶ T` of the ambient fibre product**: the zero section of each of the
two line bundles. -/
def totalSpaceZeroSection : Y ⟶ totalSpace Y L₁ L₂ :=
  Limits.pullback.lift (Stacks.LineBundle.inverseSituation Y L₁).zeroSection
    (Stacks.LineBundle.inverseSituation Y L₂).zeroSection
    (((Stacks.LineBundle.inverseSituation Y L₁).zeroSection_comp_totalSpaceToBase).trans
      ((Stacks.LineBundle.inverseSituation Y L₂).zeroSection_comp_totalSpaceToBase).symm)

include h₁ h₂ in
/-- The first coordinate of the zero section of `T` is the zero section of the first line
bundle. -/
theorem totalSpaceZeroSection_comp_firstProj :
    totalSpaceZeroSection Y L₁ L₂ ≫ firstProj Y L₁ L₂ =
      (Stacks.LineBundle.inverseSituation Y L₁).zeroSection :=
  Limits.pullback.lift_fst _ _ _

include h₁ h₂ in
/-- The second coordinate of the zero section of `T` is the zero section of the second line
bundle. -/
theorem totalSpaceZeroSection_comp_secondProj :
    totalSpaceZeroSection Y L₁ L₂ ≫ secondProj Y L₁ L₂ =
      (Stacks.LineBundle.inverseSituation Y L₂).zeroSection :=
  Limits.pullback.lift_snd _ _ _

include h₁ h₂ in
/-- The zero section of `T` is a section of the structure morphism `q`. -/
theorem totalSpaceZeroSection_comp_totalProj :
    totalSpaceZeroSection Y L₁ L₂ ≫ totalProj Y L₁ L₂ = CategoryTheory.CategoryStruct.id Y :=
  (Category.assoc (totalSpaceZeroSection Y L₁ L₂) (firstProj Y L₁ L₂)
        (Stacks.LineBundle.lineBundleProj Y L₁)).symm.trans
    ((congrArg (fun z : Y ⟶ Stacks.LineBundle.lineBundleSpace Y L₁ =>
          z ≫ Stacks.LineBundle.lineBundleProj Y L₁)
        (totalSpaceZeroSection_comp_firstProj Y L₁ L₂)).trans
      (Stacks.LineBundle.inverseSituation Y L₁).zeroSection_comp_totalSpaceToBase)

include h₁ h₂ in
/-- **A morphism to `T` whose two coordinates are the zero sections is the zero section of `T`,
taken along its own composite with `q`.** -/
theorem eq_comp_totalSpaceZeroSection {W : Scheme.{u}} (f : W ⟶ totalSpace Y L₁ L₂)
    (hc₁ : f ≫ firstProj Y L₁ L₂ =
      (f ≫ totalProj Y L₁ L₂) ≫ (Stacks.LineBundle.inverseSituation Y L₁).zeroSection)
    (hc₂ : f ≫ secondProj Y L₁ L₂ =
      (f ≫ totalProj Y L₁ L₂) ≫ (Stacks.LineBundle.inverseSituation Y L₂).zeroSection) :
    f = (f ≫ totalProj Y L₁ L₂) ≫ totalSpaceZeroSection Y L₁ L₂ :=
  totalSpace_hom_ext Y L₁ L₂
    (hc₁.trans ((congrArg (fun z : Y ⟶ Stacks.LineBundle.lineBundleSpace Y L₁ =>
            (f ≫ totalProj Y L₁ L₂) ≫ z)
          (totalSpaceZeroSection_comp_firstProj Y L₁ L₂)).symm.trans
        (Category.assoc (f ≫ totalProj Y L₁ L₂) (totalSpaceZeroSection Y L₁ L₂)
          (firstProj Y L₁ L₂)).symm))
    (hc₂.trans ((congrArg (fun z : Y ⟶ Stacks.LineBundle.lineBundleSpace Y L₂ =>
            (f ≫ totalProj Y L₁ L₂) ≫ z)
          (totalSpaceZeroSection_comp_secondProj Y L₁ L₂)).symm.trans
        (Category.assoc (f ≫ totalProj Y L₁ L₂) (totalSpaceZeroSection Y L₁ L₂)
          (secondProj Y L₁ L₂)).symm))

variable (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

include h₁ h₂ in
/-- **The zero section of `T` restricted to `D`.** This is the inverse of the isomorphism of
[Stacks, Tag 0F97](6). -/
def zeroSectionOverZeroIdeal : (zeroIdeal Y L₁ L₂ s).subscheme ⟶ totalSpace Y L₁ L₂ :=
  (zeroIdeal Y L₁ L₂ s).subschemeι ≫ totalSpaceZeroSection Y L₁ L₂

include h₁ h₂ in
/-- The restricted zero section lies over `D` through `i`. -/
theorem zeroSectionOverZeroIdeal_comp_totalProj :
    zeroSectionOverZeroIdeal Y L₁ L₂ s ≫ totalProj Y L₁ L₂ =
      (zeroIdeal Y L₁ L₂ s).subschemeι := by
  rw [zeroSectionOverZeroIdeal, Category.assoc, totalSpaceZeroSection_comp_totalProj,
    Category.comp_id]

include h₁ h₂ in
/-- The first fibre coordinate vanishes on the restricted zero section. -/
theorem pullbackGlobalSections_coord₁_zeroSectionOverZeroIdeal :
    pullbackGlobalSections (zeroSectionOverZeroIdeal Y L₁ L₂ s)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂) = 0 :=
  (pullbackGlobalSections_coord₁_eq_zero_iff Y L₁ L₂
      (zeroSectionOverZeroIdeal Y L₁ L₂ s)).mpr
    ⟨(zeroIdeal Y L₁ L₂ s).subschemeι,
      ((Category.assoc (zeroIdeal Y L₁ L₂ s).subschemeι (totalSpaceZeroSection Y L₁ L₂)
            (firstProj Y L₁ L₂)).trans
        (congrArg (fun z : Y ⟶ Stacks.LineBundle.lineBundleSpace Y L₁ =>
            (zeroIdeal Y L₁ L₂ s).subschemeι ≫ z)
          (totalSpaceZeroSection_comp_firstProj Y L₁ L₂))).symm⟩

include h₁ h₂ in
/-- The second fibre coordinate vanishes on the restricted zero section. -/
theorem pullbackGlobalSections_coord₂_zeroSectionOverZeroIdeal :
    pullbackGlobalSections (zeroSectionOverZeroIdeal Y L₁ L₂ s)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂) = 0 :=
  (pullbackGlobalSections_coord₂_eq_zero_iff Y L₁ L₂
      (zeroSectionOverZeroIdeal Y L₁ L₂ s)).mpr
    ⟨(zeroIdeal Y L₁ L₂ s).subschemeι,
      ((Category.assoc (zeroIdeal Y L₁ L₂ s).subschemeι (totalSpaceZeroSection Y L₁ L₂)
            (secondProj Y L₁ L₂)).trans
        (congrArg (fun z : Y ⟶ Stacks.LineBundle.lineBundleSpace Y L₂ =>
            (zeroIdeal Y L₁ L₂ s).subschemeι ≫ z)
          (totalSpaceZeroSection_comp_secondProj Y L₁ L₂))).symm⟩

include h₁ h₂ in
/-- The restricted zero section lies over `D`. -/
theorem zeroIdeal_le_ker_zeroSectionOverZeroIdeal_comp_totalProj :
    zeroIdeal Y L₁ L₂ s ≤ (zeroSectionOverZeroIdeal Y L₁ L₂ s ≫ totalProj Y L₁ L₂).ker := by
  refine le_of_eq (Eq.symm ?_)
  rw [zeroSectionOverZeroIdeal_comp_totalProj, Scheme.IdealSheafData.ker_subschemeι]

/-! ### The intersection inside the ambient fibre product -/

include h₁ h₂ in
/-- The intersection `D₁ ∩ D₂`, read inside `T` through the first branch, is the composite of its
own closed immersion into `L` with `ι`. -/
theorem inclusion_comp_branchι₁ :
    Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₁ Y L₁ L₂ s =
      (branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s).subschemeι ≫ spaceι Y L₁ L₂ s := by
  rw [branchι₁, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

include h₁ h₂ in
/-- The intersection `D₁ ∩ D₂`, read inside `T` through the second branch. -/
theorem inclusion_comp_branchι₂ :
    Scheme.IdealSheafData.inclusion
          (le_sup_right : branch₂ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₂ Y L₁ L₂ s =
      (branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s).subschemeι ≫ spaceι Y L₁ L₂ s := by
  rw [branchι₂, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

include h₁ h₂ in
/-- **The two readings of the intersection inside `T` agree.** -/
theorem inclusion_comp_branchι₁_eq_inclusion_comp_branchι₂ :
    Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₁ Y L₁ L₂ s =
      Scheme.IdealSheafData.inclusion
          (le_sup_right : branch₂ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₂ Y L₁ L₂ s :=
  (inclusion_comp_branchι₁ Y L₁ L₂ s).trans (inclusion_comp_branchι₂ Y L₁ L₂ s).symm

include h₁ h₂ in
/-- The intersection lies over `D` through `p₁`. -/
theorem inclusion_comp_branchι₁_comp_totalProj :
    (Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₁ Y L₁ L₂ s) ≫ totalProj Y L₁ L₂ =
      (Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₁ Y L₁ L₂ s) ≫ (zeroIdeal Y L₁ L₂ s).subschemeι := by
  simp only [Category.assoc, ← proj₁_comp_zeroIdeal_subschemeι]

include h₁ h₂ in
/-- The intersection lies over `D` through `p₂`, and the two readings agree. -/
theorem inclusion_comp_branchι₂_comp_totalProj :
    (Scheme.IdealSheafData.inclusion
          (le_sup_right : branch₂ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₂ Y L₁ L₂ s) ≫ totalProj Y L₁ L₂ =
      (Scheme.IdealSheafData.inclusion
          (le_sup_right : branch₂ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₂ Y L₁ L₂ s) ≫ (zeroIdeal Y L₁ L₂ s).subschemeι := by
  simp only [Category.assoc, ← proj₂_comp_zeroIdeal_subschemeι]

/-- Precomposing an identity "this coordinate is the zero section" with a further morphism. The
reassociation is done here, where every variable is a plain scheme or morphism: in the statements
below the zero section's source and target are the `X` and `totalSpace` fields of a line-bundle
situation, which are the base and the line bundle only at default transparency, so those goals are
not type-correct at the transparency level `rw` and `simp` elaborate their patterns at. -/
private theorem comp_coord_eq_comp_zeroSection {W V T A B : Scheme.{u}} (c : W ⟶ V) (f : V ⟶ T)
    (p : T ⟶ B) (q : T ⟶ A) (z : A ⟶ B) (h : f ≫ p = (f ≫ q) ≫ z) :
    (c ≫ f) ≫ p = ((c ≫ f) ≫ q) ≫ z :=
  (Category.assoc c f p).trans
    ((congrArg (fun y : V ⟶ B => c ≫ y) h).trans
      ((Category.assoc c (f ≫ q) z).symm.trans
        (congrArg (fun y : W ⟶ A => y ≫ z) (Category.assoc c f q).symm)))

include h₁ h₂ in
/-- **The second fibre coordinate of the intersection is the zero section** of the second line
bundle: the intersection factors through the second branch, whose second coordinate vanishes. -/
theorem inclusion_comp_branchι₁_comp_secondProj :
    (Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₁ Y L₁ L₂ s) ≫ secondProj Y L₁ L₂ =
      ((Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₁ Y L₁ L₂ s) ≫ totalProj Y L₁ L₂) ≫
        (Stacks.LineBundle.inverseSituation Y L₂).zeroSection := by
  rw [inclusion_comp_branchι₁_eq_inclusion_comp_branchι₂]
  exact comp_coord_eq_comp_zeroSection _ _ _ _ _ (branchι₂_comp_secondProj Y L₁ L₂ s)

include h₁ h₂ in
/-- **The first fibre coordinate of the intersection is the zero section** of the first line
bundle. -/
theorem inclusion_comp_branchι₂_comp_firstProj :
    (Scheme.IdealSheafData.inclusion
          (le_sup_right : branch₂ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₂ Y L₁ L₂ s) ≫ firstProj Y L₁ L₂ =
      ((Scheme.IdealSheafData.inclusion
          (le_sup_right : branch₂ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₂ Y L₁ L₂ s) ≫ totalProj Y L₁ L₂) ≫
        (Stacks.LineBundle.inverseSituation Y L₁).zeroSection := by
  rw [← inclusion_comp_branchι₁_eq_inclusion_comp_branchι₂]
  exact comp_coord_eq_comp_zeroSection _ _ _ _ _ (branchι₁_comp_firstProj Y L₁ L₂ s)

include h₁ h₂ in
/-- **The intersection `D₁ ∩ D₂`, read inside `T`, is the zero section of `T` over `D`.** -/
theorem inclusion_comp_branchι₁_eq :
    Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        branchι₁ Y L₁ L₂ s =
      ((Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₁ Y L₁ L₂ s) ≫ (zeroIdeal Y L₁ L₂ s).subschemeι) ≫
        totalSpaceZeroSection Y L₁ L₂ := by
  rw [← inclusion_comp_branchι₁_comp_totalProj]
  refine eq_comp_totalSpaceZeroSection Y L₁ L₂ _ ?_
    (inclusion_comp_branchι₁_comp_secondProj Y L₁ L₂ s)
  exact comp_coord_eq_comp_zeroSection _ _ _ _ _ (branchι₁_comp_firstProj Y L₁ L₂ s)

/-! ### Condition (6) -/

include h₁ h₂ in
/-- **[Stacks, Tag 0F97](6)**: the scheme-theoretic intersection `D₁ ∩ D₂` maps isomorphically to
`D`. The inverse is the zero section of `T` restricted to `D`. -/
theorem isIso_intersection_proj₁ :
    IsIso (Scheme.IdealSheafData.inclusion
      (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₁ Y L₁ L₂ s) := by
  obtain ⟨u₁, hu₁⟩ := (factorsThrough_branch₁_iff Y L₁ L₂ s
      (zeroSectionOverZeroIdeal Y L₁ L₂ s)).mpr
    ⟨pullbackGlobalSections_coord₁_zeroSectionOverZeroIdeal Y L₁ L₂ s,
      zeroIdeal_le_ker_zeroSectionOverZeroIdeal_comp_totalProj Y L₁ L₂ s⟩
  obtain ⟨u₂, hu₂⟩ := (factorsThrough_branch₂_iff Y L₁ L₂ s
      (zeroSectionOverZeroIdeal Y L₁ L₂ s)).mpr
    ⟨pullbackGlobalSections_coord₂_zeroSectionOverZeroIdeal Y L₁ L₂ s,
      zeroIdeal_le_ker_zeroSectionOverZeroIdeal_comp_totalProj Y L₁ L₂ s⟩
  have : Mono (spaceι Y L₁ L₂ s) :=
    show Mono (spaceIdeal Y L₁ L₂ s).subschemeι from inferInstance
  have hv : u₂ ≫ (branch₂ Y L₁ L₂ s).subschemeι = u₁ ≫ (branch₁ Y L₁ L₂ s).subschemeι := by
    rw [← cancel_mono (spaceι Y L₁ L₂ s), Category.assoc, Category.assoc, ← branchι₁, ← branchι₂,
      hu₁, hu₂]
  have hle : branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s ≤
      (u₁ ≫ (branch₁ Y L₁ L₂ s).subschemeι).ker :=
    sup_le ((Scheme.IdealSheafData.ker_subschemeι _).ge.trans (u₁.le_ker_comp _))
      (hv ▸ (Scheme.IdealSheafData.ker_subschemeι _).ge.trans (u₂.le_ker_comp _))
  obtain ⟨n, hn⟩ := (Stacks.Divisors.le_ker_iff_factorsThrough
    (branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) (u₁ ≫ (branch₁ Y L₁ L₂ s).subschemeι)).mp hle
  have h1 : n ≫ (Scheme.IdealSheafData.inclusion
        (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
      branchι₁ Y L₁ L₂ s) = zeroSectionOverZeroIdeal Y L₁ L₂ s := by
    rw [inclusion_comp_branchι₁, ← Category.assoc, hn, Category.assoc, ← branchι₁, hu₁]
  have : Mono ((branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s).subschemeι ≫ spaceι Y L₁ L₂ s) :=
    inferInstance
  refine ⟨⟨n, ?_, ?_⟩⟩
  · rw [← cancel_mono ((branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s).subschemeι ≫ spaceι Y L₁ L₂ s),
      Category.id_comp, ← inclusion_comp_branchι₁, Category.assoc, h1,
      zeroSectionOverZeroIdeal, ← Category.assoc, ← inclusion_comp_branchι₁_eq]
  · rw [← cancel_mono (zeroIdeal Y L₁ L₂ s).subschemeι, Category.id_comp, Category.assoc,
      ← inclusion_comp_branchι₁_comp_totalProj, ← Category.assoc, h1,
      zeroSectionOverZeroIdeal_comp_totalProj]

/-! ### Condition (7) -/

include h₁ h₂ in
/-- **[Stacks, Tag 0F97](7) for the first branch**: the closed immersion `D₁ ∩ D₂ ⟶ D₁` is the
zero section of the line bundle `D₁ ⟶ D`, read through the identification
`Stacks.Chow.TensorZeroScheme.branchIso₁` of condition (4). -/
theorem intersection_comp_branchIso₁ :
    Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        (branchIso₁ Y L₁ L₂ s).hom =
      (Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₁ Y L₁ L₂ s) ≫ (branchSituation Y L₁ L₂ s L₂).zeroSection := by
  rw [branchIso₁_hom, ← zeroSectionFibreProduct₁_comp_branchBundleIso₁_hom, ← Category.assoc,
    ← Category.assoc]
  refine congrArg (fun z : (branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s).subscheme ⟶
      branchFibreProduct₁ Y L₁ L₂ s => z ≫ (branchBundleIso₁ Y L₁ L₂ s).hom) ?_
  refine branchFibreProduct₁_hom_ext Y L₁ L₂ s ?_ ?_
  · rw [Category.assoc, branchToFibreProduct₁_comp_base, Category.assoc,
      zeroSectionFibreProduct₁_comp_base, Category.comp_id]
  · rw [Category.assoc, branchToFibreProduct₁_comp_fibre, Category.assoc,
      zeroSectionFibreProduct₁_comp_fibre, ← Category.assoc,
      inclusion_comp_branchι₁_comp_secondProj, inclusion_comp_branchι₁_comp_totalProj]
    exact Category.assoc _ _ _

include h₁ h₂ in
/-- **[Stacks, Tag 0F97](7) for the second branch**: the closed immersion `D₁ ∩ D₂ ⟶ D₂` is the
zero section of the line bundle `D₂ ⟶ D`, read through the identification
`Stacks.Chow.TensorZeroScheme.branchIso₂` of condition (4). -/
theorem intersection_comp_branchIso₂ :
    Scheme.IdealSheafData.inclusion
          (le_sup_right : branch₂ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        (branchIso₂ Y L₁ L₂ s).hom =
      (Scheme.IdealSheafData.inclusion
          (le_sup_right : branch₂ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₂ Y L₁ L₂ s) ≫ (branchSituation Y L₁ L₂ s L₁).zeroSection := by
  rw [branchIso₂_hom, ← zeroSectionFibreProduct₂_comp_branchBundleIso₂_hom, ← Category.assoc,
    ← Category.assoc]
  refine congrArg (fun z : (branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s).subscheme ⟶
      branchFibreProduct₂ Y L₁ L₂ s => z ≫ (branchBundleIso₂ Y L₁ L₂ s).hom) ?_
  refine branchFibreProduct₂_hom_ext Y L₁ L₂ s ?_ ?_
  · rw [Category.assoc, branchToFibreProduct₂_comp_base, Category.assoc,
      zeroSectionFibreProduct₂_comp_base, Category.comp_id]
  · rw [Category.assoc, branchToFibreProduct₂_comp_fibre, Category.assoc,
      zeroSectionFibreProduct₂_comp_fibre, ← Category.assoc,
      inclusion_comp_branchι₂_comp_firstProj, inclusion_comp_branchι₂_comp_totalProj]
    exact Category.assoc _ _ _

end Stacks.Chow.TensorZeroScheme

end
