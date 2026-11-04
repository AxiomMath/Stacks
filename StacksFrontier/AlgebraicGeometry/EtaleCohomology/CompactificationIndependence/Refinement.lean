module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem

/-!
# Extension by zero along a refinement of compactifications

Let `j : X ⟶ A` and `k : X ⟶ B` be open immersions and `g : A ⟶ B` a separated morphism with
`j ≫ g = k`; for instance `j` and `k` are compactifications of `X` over a base and `g` is a
morphism of compactifications. This file constructs the canonical comparison

`θ_g : k_! ⟶ g_* ∘ j_!`

of functors on sheaves of `Λ`-modules on the small étale sites, the underived map behind the
map of [Stacks, Tag 0F7G] (there it is the identification `k_! = g_! j_! = g_* j_!` of Tags 0F79
and 0F51), and proves that these comparisons are compatible with composition.

The comparison is pinned by the canonical inclusion `ε_j : j_! ⟶ j_*` of extension by zero into
direct image: `θ_g` is the unique map with `θ_g ≫ g_* ε_j = ε_k`, up to the identification
`g_* j_* = k_*`. Uniqueness holds because `g_* ε_j` becomes invertible after restriction to `X`
(see `isIso_etaleModuleRestriction_map_directImage_map_extensionByZeroToDirectImage`):
over `X` the scheme `A ×_B X` contains `X` as an open and closed subscheme, whose complement maps
into the complement of `X` in `A`, where both `j_!` and `j_*` vanish.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroToDirectImage`: `ε_j : j_! ⟶ j_*`.
* `Stacks.EtaleCohomology.etaleModuleRefinementComparison`: `θ_g : k_! ⟶ g_* ∘ j_!`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleRefinementComparison_comp_map`: `θ_g ≫ g_* ε_j = ε_k`.
* `Stacks.EtaleCohomology.etaleModuleRefinementComparison_comp`: the cocycle law
  `θ_{g ≫ h} = θ_h ≫ h_* θ_g`, up to `h_* g_* = (g ≫ h)_*`.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-! ### Extension by zero into direct image -/

section Inclusion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **The inclusion `ε_j : j_! ⟶ j_*`** of extension by zero into direct image along an open
immersion: the unit `j_! F ⟶ j_* j^{-1} j_! F` of restriction against direct image, followed by
`j_*` of the inverse of the invertible unit `F ⟶ j^{-1} j_! F`. -/
def etaleModuleExtensionByZeroToDirectImage :
    etaleModuleExtensionByZero.{u, r} Λ j ⟶ etaleModuleDirectImage.{u, r} Λ j :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (etaleModuleExtensionByZero.{u, r} Λ j)
      (etaleModuleRestrictionDirectImageAdj.{u, r} Λ j).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (inv (etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit)
      (etaleModuleDirectImage.{u, r} Λ j) ≫
    (Functor.leftUnitor _).hom

/-- The component of `ε_j` at `F`: the unit `j_! F ⟶ j_* j^{-1} j_! F` followed by `j_*` of the
inverse of the unit `F ⟶ j^{-1} j_! F`. -/
lemma etaleModuleExtensionByZeroToDirectImage_app (F : EtaleModules.{u, r} Λ U) :
    (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F =
      (etaleModuleRestrictionDirectImageAdj.{u, r} Λ j).unit.app
          ((etaleModuleExtensionByZero.{u, r} Λ j).obj F) ≫
        (etaleModuleDirectImage.{u, r} Λ j).map
          (inv ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app F)) := by
  simp [etaleModuleExtensionByZeroToDirectImage]

/-- For an open immersion the counit `j^{-1} j_* F ⟶ F` of restriction against the direct image
formed from base change is invertible: that direct image is right adjoint to restriction, as is
the right Kan extension along composition with `j`, whose counit is invertible. -/
instance isIso_etaleModuleRestrictionDirectImageAdj_counit :
    IsIso (etaleModuleRestrictionDirectImageAdj.{u, r} Λ j).counit := by
  have h := Adjunction.rightAdjointUniq_hom_counit
    (etaleModuleRestrictionDirectImageAdj.{u, r} Λ j) (etaleModuleEtaleDirectImageAdj.{u, r} Λ j)
  rw [← h]
  infer_instance

/-- `ε_j` is invertible after restriction to `U`. -/
instance isIso_etaleModuleRestriction_map_extensionByZeroToDirectImage
    (F : EtaleModules.{u, r} Λ U) :
    IsIso ((etaleModuleRestriction.{u, r} Λ j).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F)) := by
  rw [etaleModuleExtensionByZeroToDirectImage_app, Functor.map_comp]
  have : IsIso ((etaleModuleRestriction.{u, r} Λ j).map
      ((etaleModuleRestrictionDirectImageAdj.{u, r} Λ j).unit.app
        ((etaleModuleExtensionByZero.{u, r} Λ j).obj F))) :=
    IsIso.of_isIso_fac_right
      ((etaleModuleRestrictionDirectImageAdj.{u, r} Λ j).left_triangle_components _)
  infer_instance

end Inclusion

/-! ### `g_* ε_j` is invertible over `X` -/

section Refinement

variable {X A B : Scheme.{u}} (j : X ⟶ A) (k : X ⟶ B) (g : A ⟶ B) [IsOpenImmersion j]
  [IsOpenImmersion k] [IsSeparated g]

/-- The section `X ⟶ A ×_B X` of the second projection given by `j`. -/
abbrev refinementSection (hjk : j ≫ g = k) : X ⟶ pullback g k :=
  pullback.lift j (𝟙 X) (by rw [hjk, Category.id_comp])

variable {j k g} (hjk : j ≫ g = k)

omit [IsOpenImmersion j] [IsOpenImmersion k] [IsSeparated g] in
include hjk in
/-- The section `X ⟶ A ×_B X` followed by the first projection is `j`. -/
lemma refinementSection_fst : refinementSection j k g hjk ≫ pullback.fst g k = j :=
  pullback.lift_fst _ _ _

omit [IsOpenImmersion j] [IsOpenImmersion k] [IsSeparated g] in
include hjk in
/-- The section `X ⟶ A ×_B X` is a section of the second projection. -/
lemma refinementSection_snd : refinementSection j k g hjk ≫ pullback.snd g k = 𝟙 X :=
  pullback.lift_snd _ _ _

/-- The section `X ⟶ A ×_B X` is an open immersion. -/
instance isOpenImmersion_refinementSection : IsOpenImmersion (refinementSection j k g hjk) := by
  have : IsOpenImmersion (refinementSection j k g hjk ≫ pullback.fst g k) := by
    rw [refinementSection_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst g k)

/-- The section is also a closed immersion: it is a section of the separated morphism
`A ×_B X ⟶ X`, the base change of `g`. -/
instance isClosedImmersion_refinementSection :
    IsClosedImmersion (refinementSection j k g hjk) := by
  have : UniversallyClosed (refinementSection j k g hjk ≫ pullback.snd g k) := by
    rw [refinementSection_snd]; infer_instance
  have : UniversallyClosed (refinementSection j k g hjk) :=
    UniversallyClosed.of_comp_of_isSeparated _ (pullback.snd g k)
  exact .of_isPreimmersion _ (refinementSection j k g hjk).isClosedMap.isClosed_range

/-- The open complement of the section in `A ×_B X`. -/
abbrev refinementComplement : (pullback g k).Opens :=
  ⟨(Set.range (refinementSection j k g hjk).base)ᶜ,
    (refinementSection j k g hjk).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The range of the inclusion of `refinementComplement` is the complement of the range of the
section. -/
lemma range_refinementComplement :
    Set.range (refinementComplement hjk).ι.base =
      (Set.range (refinementSection j k g hjk).base)ᶜ := by
  simp [refinementComplement]

/-- The complement of the section maps into the complement of `X` in `A`. -/
lemma disjoint_range_refinementComplement :
    Disjoint (Set.range ((refinementComplement hjk).ι ≫ pullback.fst g k).base)
      (Set.range j.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨w, rfl⟩ ⟨x, hx⟩
  have hw : (refinementComplement hjk).ι.base w ∈ Set.range (refinementComplement hjk).ι.base :=
    ⟨w, rfl⟩
  rw [range_refinementComplement] at hw
  apply hw
  refine ⟨x, (pullback.fst g k).isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, refinementSection_fst, hx, Scheme.Hom.comp_apply]

include hjk in
/-- `ε_j` restricted to `A ×_B X` is invertible: there `X` is open and closed, both sides are
supported on it, and over it `ε_j` restricts to an isomorphism. -/
lemma isIso_etaleModuleRestriction_fst_map_extensionByZeroToDirectImage
    (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleRestriction.{u, r} Λ (pullback.fst g k)).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F)) := by
  let s := refinementSection j k g hjk
  let O := refinementComplement hjk
  let r := etaleModuleRestriction.{u, r} Λ (pullback.fst g k)
  have hO := range_refinementComplement hjk
  have hdisj := disjoint_range_refinementComplement hjk
  have hzA : IsZero ((etaleModuleRestriction.{u, r} Λ O.ι).obj
      (r.obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F))) :=
    (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ _ j hdisj F).of_iso
      ((etaleModuleRestrictionCompIso.{u, r} Λ O.ι (pullback.fst g k)).app _ ≪≫
        (etaleModuleInverseImageRestrictionIso.{u, r} Λ (O.ι ≫ pullback.fst g k)).symm.app _)
  have hzB : IsZero ((etaleModuleRestriction.{u, r} Λ O.ι).obj
      (r.obj ((etaleModuleDirectImage.{u, r} Λ j).obj F))) :=
    (isZero_etaleModuleRestriction_etaleModuleDirectImage_of_disjoint Λ j _ hdisj.symm F).of_iso
      ((etaleModuleRestrictionCompIso.{u, r} Λ O.ι (pullback.fst g k)).app _)
  have hA := isIso_etaleModuleInverseImageAdj_unit_app_of_isZero Λ s O.ι hO _ hzA
  have hB := isIso_etaleModuleInverseImageAdj_unit_app_of_isZero Λ s O.ι hO _ hzB
  have hs : IsIso ((etaleModuleRestriction.{u, r} Λ s).map
      (r.map ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F))) := by
    have key : ∀ (a : X ⟶ A) (_ : a = j) [Etale a], IsIso ((etaleModuleRestriction.{u, r} Λ a).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F)) := by
      rintro a rfl _
      exact isIso_etaleModuleRestriction_map_extensionByZeroToDirectImage Λ a F
    exact (NatIso.isIso_map_iff (etaleModuleRestrictionCompIso.{u, r} Λ s (pullback.fst g k)) _).2
      (key _ (refinementSection_fst hjk))
  have hs' : IsIso ((etaleModuleInverseImage.{u, r} Λ s).map
      (r.map ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F))) :=
    (NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, r} Λ s) _).2 hs
  have hn := (etaleModuleInverseImageAdj.{u, r} Λ s).unit.naturality
    (r.map ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F))
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  exact IsIso.of_isIso_fac_right hn

include hjk in
/-- **`g_* ε_j` is invertible after restriction to `X`**, for open immersions `j`, `k` and a
separated `g` with `j ≫ g = k`. Restriction to `X` along `k` of a direct image along `g` is the
direct image along `A ×_B X ⟶ X` of the restriction to `A ×_B X`, and there `ε_j` is
invertible. -/
theorem isIso_etaleModuleRestriction_map_directImage_map_extensionByZeroToDirectImage
    (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleRestriction.{u, r} Λ k).map ((etaleModuleDirectImage.{u, r} Λ g).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F))) := by
  have := isIso_etaleModuleRestriction_fst_map_extensionByZeroToDirectImage Λ hjk F
  have hn := (etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{max (u + 1) r} Λ)
    (IsPullback.of_hasPullback g k).flip).hom.naturality
      ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F)
  dsimp only [Functor.comp_map] at hn
  exact IsIso.of_isIso_fac_left hn.symm

end Refinement

/-! ### The comparison `θ_g : k_! ⟶ g_* j_!` -/

section Comparison

variable {X A B : Scheme.{u}} {j : X ⟶ A} {k : X ⟶ B} {g : A ⟶ B} [IsOpenImmersion j]
  [IsOpenImmersion k] [IsSeparated g] (hjk : j ≫ g = k)

/-- `g_* ε_j` after restriction to `X`, as a natural transformation; it is invertible. -/
abbrev refinementRestrictedInclusion :
    etaleModuleExtensionByZero.{u, r} Λ j ⋙ etaleModuleDirectImage.{u, r} Λ g ⋙
        etaleModuleRestriction.{u, r} Λ k ⟶
      etaleModuleDirectImage.{u, r} Λ j ⋙ etaleModuleDirectImage.{u, r} Λ g ⋙
        etaleModuleRestriction.{u, r} Λ k :=
  Functor.whiskerRight (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j)
    (etaleModuleDirectImage.{u, r} Λ g ⋙ etaleModuleRestriction.{u, r} Λ k)

include hjk in
/-- `g_* ε_j` restricted to `X` is invertible. -/
theorem isIso_refinementRestrictedInclusion :
    IsIso (refinementRestrictedInclusion.{u, r} Λ (j := j) (k := k) (g := g)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F => ?_
  exact isIso_etaleModuleRestriction_map_directImage_map_extensionByZeroToDirectImage Λ hjk F

/-- The map `F ⟶ (g_* j_* F)|_X` adjoint to `ε_k`, read through `g_* j_* = k_*`. -/
def refinementTarget :
    𝟭 (EtaleModules.{u, r} Λ X) ⟶
      etaleModuleDirectImage.{u, r} Λ j ⋙ etaleModuleDirectImage.{u, r} Λ g ⋙
        etaleModuleRestriction.{u, r} Λ k :=
  (etaleModuleExtensionByZeroAdj.{u, r} Λ k).unit ≫
    Functor.whiskerRight (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ k ≫
        (etaleModuleDirectImageComp.{u, r} Λ j g k hjk.symm).inv)
      (etaleModuleRestriction.{u, r} Λ k)

/-- The map `F ⟶ (g_* j_! F)|_X` adjoint to `θ_g`. -/
def refinementComparisonAdj :
    𝟭 (EtaleModules.{u, r} Λ X) ⟶
      etaleModuleExtensionByZero.{u, r} Λ j ⋙ etaleModuleDirectImage.{u, r} Λ g ⋙
        etaleModuleRestriction.{u, r} Λ k :=
  haveI := isIso_refinementRestrictedInclusion Λ hjk
  refinementTarget Λ hjk ≫ inv (refinementRestrictedInclusion.{u, r} Λ (j := j) (k := k) (g := g))

/-- `refinementComparisonAdj` followed by `refinementRestrictedInclusion` is `refinementTarget`. -/
lemma refinementComparisonAdj_comp :
    refinementComparisonAdj Λ hjk ≫ refinementRestrictedInclusion.{u, r} Λ (j := j) (k := k)
      (g := g) = refinementTarget Λ hjk := by
  simp [refinementComparisonAdj]

/-- **The comparison `θ_g : k_! ⟶ g_* j_!`** attached to open immersions `j`, `k` and a separated
`g` with `j ≫ g = k`: the map adjoint to `refinementComparisonAdj`. It is characterized by
`θ_g ≫ g_* ε_j = ε_k` (`etaleModuleRefinementComparison_comp_map`). -/
def etaleModuleRefinementComparison :
    etaleModuleExtensionByZero.{u, r} Λ k ⟶
      etaleModuleExtensionByZero.{u, r} Λ j ⋙ etaleModuleDirectImage.{u, r} Λ g where
  app F := ((etaleModuleExtensionByZeroAdj.{u, r} Λ k).homEquiv _ _).symm
    ((refinementComparisonAdj Λ hjk).app F)
  naturality {F F'} φ := by
    rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    exact (refinementComparisonAdj Λ hjk).naturality φ

/-- The map adjoint to the component of `θ_g` at `F` is the component of `refinementComparisonAdj`
at `F`. -/
lemma homEquiv_etaleModuleRefinementComparison_app (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleExtensionByZeroAdj.{u, r} Λ k).homEquiv _ _
        ((etaleModuleRefinementComparison Λ hjk).app F) =
      (refinementComparisonAdj Λ hjk).app F := by
  simp [etaleModuleRefinementComparison]

/-- **The normalization of `θ_g`**: `θ_g ≫ g_* ε_j = ε_k`, read through `g_* j_* = k_*`. -/
theorem etaleModuleRefinementComparison_comp_map (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleRefinementComparison Λ hjk).app F ≫
        (etaleModuleDirectImage.{u, r} Λ g).map
          ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F) =
      (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ k).app F ≫
        (etaleModuleDirectImageComp.{u, r} Λ j g k hjk.symm).inv.app F := by
  apply ((etaleModuleExtensionByZeroAdj.{u, r} Λ k).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, homEquiv_etaleModuleRefinementComparison_app,
    Adjunction.homEquiv_unit]
  have h := congrArg (fun t => NatTrans.app t F) (refinementComparisonAdj_comp Λ hjk)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  dsimp only [Functor.comp_map] at h
  rw [h]
  simp [refinementTarget]

include hjk in
/-- **Uniqueness**: two maps out of `k_! F` into `g_* j_! F` agreeing after `g_* ε_j` agree. -/
theorem etaleModuleRefinement_hom_ext {F : EtaleModules.{u, r} Λ X}
    {α β : (etaleModuleExtensionByZero.{u, r} Λ k).obj F ⟶
      (etaleModuleDirectImage.{u, r} Λ g).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F)}
    (h : α ≫ (etaleModuleDirectImage.{u, r} Λ g).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F) =
      β ≫ (etaleModuleDirectImage.{u, r} Λ g).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F)) : α = β := by
  have := isIso_etaleModuleRestriction_map_directImage_map_extensionByZeroToDirectImage Λ hjk F
  apply ((etaleModuleExtensionByZeroAdj.{u, r} Λ k).homEquiv _ _).injective
  have h' := congrArg ((etaleModuleExtensionByZeroAdj.{u, r} Λ k).homEquiv _ _) h
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right] at h'
  exact (cancel_mono _).1 h'

end Comparison

/-! ### The cocycle law -/

section Cocycle

variable {X A B C : Scheme.{u}} {j : X ⟶ A} {k : X ⟶ B} {l : X ⟶ C} {g : A ⟶ B} {h : B ⟶ C}
  [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l] [IsSeparated g] [IsSeparated h]
  (gh : A ⟶ C) [IsSeparated gh] (hgh : gh = g ≫ h)
  (hjk : j ≫ g = k) (hkl : k ≫ h = l) (hjl : j ≫ gh = l)

/-- **The cocycle law for `θ`**: `θ_{g ≫ h} = θ_h ≫ h_* θ_g`, up to `h_* g_* = (g ≫ h)_*`. -/
theorem etaleModuleRefinementComparison_comp (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleRefinementComparison Λ hjl).app F =
      (etaleModuleRefinementComparison Λ hkl).app F ≫
        (etaleModuleDirectImage.{u, r} Λ h).map ((etaleModuleRefinementComparison Λ hjk).app F) ≫
          (etaleModuleDirectImageComp.{u, r} Λ g h gh hgh).hom.app
            ((etaleModuleExtensionByZero.{u, r} Λ j).obj F) := by
  apply etaleModuleRefinement_hom_ext Λ hjl
  rw [etaleModuleRefinementComparison_comp_map]
  have hn := (etaleModuleDirectImageComp.{u, r} Λ g h gh hgh).hom.naturality
    ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F)
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, Category.assoc, ← hn, ← Functor.map_comp_assoc,
    etaleModuleRefinementComparison_comp_map, Functor.map_comp, ← Category.assoc,
    ← Category.assoc, etaleModuleRefinementComparison_comp_map, Category.assoc, Category.assoc]
  congr 1
  have hc := smallEtalePushforwardComp'_inv_app_cocycle j g h k hjk.symm gh hgh l hkl.symm
    hjl.symm (ModuleCat.{max (u + 1) r} Λ) F
  show (etaleModuleDirectImageComp.{u, r} Λ j gh l hjl.symm).inv.app F =
    (etaleModuleDirectImageComp.{u, r} Λ k h l hkl.symm).inv.app F ≫
      (etaleModuleDirectImage.{u, r} Λ h).map
        ((etaleModuleDirectImageComp.{u, r} Λ j g k hjk.symm).inv.app F) ≫
      (etaleModuleDirectImageComp.{u, r} Λ g h gh hgh).hom.app _
  have hc' : (etaleModuleDirectImageComp.{u, r} Λ k h l hkl.symm).inv.app F ≫
      (etaleModuleDirectImage.{u, r} Λ h).map
        ((etaleModuleDirectImageComp.{u, r} Λ j g k hjk.symm).inv.app F) =
      (etaleModuleDirectImageComp.{u, r} Λ j gh l hjl.symm).inv.app F ≫
        (etaleModuleDirectImageComp.{u, r} Λ g h gh hgh).inv.app
          ((etaleModuleDirectImage.{u, r} Λ j).obj F) := hc
  rw [← Category.assoc, hc', Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

end Cocycle

end Stacks.EtaleCohomology

end
