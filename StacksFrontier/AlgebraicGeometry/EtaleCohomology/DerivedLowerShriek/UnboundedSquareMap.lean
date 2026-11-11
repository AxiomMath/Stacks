module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.UnboundedCompositionIsoToDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.DirectImageCompCoherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionByZeroToDirectImageMono
public import StacksFrontier.CategoryTheory.Functor.Derived.BaseChangeHorizontalPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleCoinduction
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerivedQ

/-!
# The maps of [Stacks, Tag 0F7B] on unbounded derived categories, and their pasting

Let `Λ` be a ring and consider a commutative square of schemes
```
P --b--> T
|f'      |f̄
v        v
Y --i--> S
```
with `b` and `i` open immersions. An isomorphism `μ : i_! ∘ f'_* ≅ f̄_* ∘ b_!` of functors on
sheaves of `Λ`-modules induces, by the universal property of the right derived functor
`i_! ∘ Rf'_*` of `i_! ∘ f'_*` on `D(P_étale, Λ)`, a map
```
i_! ∘ Rf'_* ⟶ Rf̄_* ∘ b_!
```
on unbounded derived categories (`Stacks.EtaleCohomology.derivedExtensionByZeroSquareMap`): the map
of [Stacks, Tag 0F7B]. On sheaves the source pins `μ`: it is the inclusion
`i_! f'_* ⊆ (f' ≫ i)_* = (b ≫ f̄)_* ⊇ f̄_* b_!`, that is, `μ` followed by `f̄_*` of
`b_! ⟶ b_*` is `i_! ⟶ i_*` (`Stacks.EtaleCohomology.IsExtensionByZeroBaseChange`), and such a
`μ` is unique since `b_! ⟶ b_*` is a monomorphism.

This file proves that the maps compose along two squares on top of each other
([Stacks, Tag 0F7C]) and side by side ([Stacks, Tag 0F7D]), that the open immersion case of
[Stacks, Tag 0F7B] for a cartesian square (`etaleModuleExtensionByZeroDirectImageUnboundedIso`)
is such a map, and that so is the map of [Stacks, Tag 0F7G] for a morphism of compactifications
(`derivedRefinementComparisonUnboundedUniv`). These are the inputs of the associativity of the
isomorphisms of [Stacks, Tag 0F7J] on unbounded derived categories ([Stacks, Tag 0F7K]).

## Main definitions

* `Stacks.EtaleCohomology.IsExtensionByZeroBaseChange`: the property pinning the map of sheaves.
* `Stacks.EtaleCohomology.derivedExtensionByZeroSquareMap`: the map of [Stacks, Tag 0F7B].

## Main results

* `Stacks.EtaleCohomology.IsExtensionByZeroBaseChange.ext`: uniqueness on sheaves.
* `Stacks.EtaleCohomology.IsExtensionByZeroBaseChange.vertical_paste` and
  `Stacks.EtaleCohomology.IsExtensionByZeroBaseChange.horizontal_paste`: pasting on sheaves.
* `Stacks.EtaleCohomology.derivedExtensionByZeroSquareMap_vertical_paste`:
  [Stacks, Tag 0F7C].
* `Stacks.EtaleCohomology.derivedExtensionByZeroSquareMap_horizontal_paste`:
  [Stacks, Tag 0F7D].
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroDirectImageUnboundedIsoE_inv`: the open
  immersion case of [Stacks, Tag 0F7B] is the map of its square.
* `Stacks.EtaleCohomology.derivedRefinementComparisonUnboundedUniv_eq_squareMap`: the map of
  [Stacks, Tag 0F7G] is the map of its square.

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F7C](https://stacks.math.columbia.edu/tag/0F7C)
* [Stacks Project, Tag 0F7D](https://stacks.math.columbia.edu/tag/0F7D)
* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ]

/-! ### The map of sheaves of a square -/

section Sheaves

/-- **The condition pinning the map of [Stacks, Tag 0F7B] on sheaves.** For a commutative square
`b ≫ f̄ = h = f' ≫ i` with `b` and `i` open immersions, `μ : i_! f'_* ⟶ f̄_* b_!` followed by
`f̄_*` of `ε_b : b_! ⟶ b_*` is `ε_i : i_! ⟶ i_*` at `f'_*`, both read in `h_*`. -/
def IsExtensionByZeroBaseChange {P T Y S : Scheme.{u}} {b : P ⟶ T} {i : Y ⟶ S}
    [IsOpenImmersion b] [IsOpenImmersion i] {f' : P ⟶ Y} {fb : T ⟶ S} (h : P ⟶ S)
    (hb : h = b ≫ fb) (hi : h = f' ≫ i)
    (μ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ⟶
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb) : Prop :=
  ∀ F, μ.app F ≫ (etaleModuleDirectImage.{u, 0} Λ fb).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app F) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ b fb h hb).hom.app F =
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i).app
        ((etaleModuleDirectImage.{u, 0} Λ f').obj F) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ f' i h hi).hom.app F

/-- `f̄_*` of `ε_b`, read in `h_*`, is a monomorphism. -/
lemma mono_etaleModuleDirectImage_map_extensionByZeroToDirectImage_comp {P T S : Scheme.{u}}
    (b : P ⟶ T) [IsOpenImmersion b] (fb : T ⟶ S) (h : P ⟶ S) (hb : h = b ≫ fb)
    (F : EtaleModules.{u, 0} Λ P) :
    Mono ((etaleModuleDirectImage.{u, 0} Λ fb).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app F) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ b fb h hb).hom.app F) := by
  have h₀ := mono_etaleModuleExtensionByZeroToDirectImage_app Λ b F
  refine ⟨fun {W} x y hxy => ?_⟩
  have hxy' : x ≫ (etaleModuleDirectImage.{u, 0} Λ fb).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app F) =
      y ≫ (etaleModuleDirectImage.{u, 0} Λ fb).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app F) :=
    (Iso.cancel_iso_hom_right _ _ ((etaleModuleDirectImageComp.{u, 0} Λ b fb h hb).app F)).1
      (by simpa only [Category.assoc, Iso.app_hom] using hxy)
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ fb).homEquiv W
    ((etaleModuleExtensionByZero.{u, 0} Λ b).obj F)).symm.injective
  have e := congrArg ((etaleModuleInverseImageAdj.{u, 0} Λ fb).homEquiv W
    ((etaleModuleDirectImage.{u, 0} Λ b).obj F)).symm hxy'
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_right_symm] at e
  exact (cancel_mono ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app F)).1 e

variable {Λ} in
/-- **The map of [Stacks, Tag 0F7B] on sheaves is unique.** -/
theorem IsExtensionByZeroBaseChange.ext {P T Y S : Scheme.{u}} {b : P ⟶ T} {i : Y ⟶ S}
    [IsOpenImmersion b] [IsOpenImmersion i] {f' : P ⟶ Y} {fb : T ⟶ S} {h : P ⟶ S}
    {hb : h = b ≫ fb} {hi : h = f' ≫ i}
    {μ μ' : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ⟶
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb}
    (hμ : IsExtensionByZeroBaseChange Λ h hb hi μ)
    (hμ' : IsExtensionByZeroBaseChange Λ h hb hi μ') : μ = μ' := by
  refine NatTrans.ext (funext fun F => ?_)
  have := mono_etaleModuleDirectImage_map_extensionByZeroToDirectImage_comp Λ b fb h hb F
  exact (cancel_mono _).1 ((hμ F).trans (hμ' F).symm)

variable {Λ} in
/-- **Vertical pasting on sheaves**: for two squares on top of each other, the maps of the
squares compose to the map of the rectangle. -/
theorem IsExtensionByZeroBaseChange.vertical_paste {P T Y S Y₂ S₂ : Scheme.{u}}
    {b : P ⟶ T} {i : Y ⟶ S} {m : Y₂ ⟶ S₂} [IsOpenImmersion b] [IsOpenImmersion i]
    [IsOpenImmersion m] {f' : P ⟶ Y} {fb : T ⟶ S} {g' : Y ⟶ Y₂} {gb : S ⟶ S₂}
    {pg : P ⟶ Y₂} {pf : T ⟶ S₂} (hpg : pg = f' ≫ g') (hpf : pf = fb ≫ gb)
    {h₁ : P ⟶ S} {hb₁ : h₁ = b ≫ fb} {hi₁ : h₁ = f' ≫ i}
    {h₂ : Y ⟶ S₂} {hi₂ : h₂ = i ≫ gb} {hm₂ : h₂ = g' ≫ m}
    {H : P ⟶ S₂} {hbH : H = b ≫ pf} {hmH : H = pg ≫ m}
    {μ₁ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ⟶
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb}
    {μ₂ : etaleModuleDirectImage.{u, 0} Λ g' ⋙ etaleModuleExtensionByZero.{u, 0} Λ m ⟶
      etaleModuleExtensionByZero.{u, 0} Λ i ⋙ etaleModuleDirectImage.{u, 0} Λ gb}
    {μ : etaleModuleDirectImage.{u, 0} Λ pg ⋙ etaleModuleExtensionByZero.{u, 0} Λ m ⟶
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ pf}
    (hμ₁ : IsExtensionByZeroBaseChange Λ h₁ hb₁ hi₁ μ₁)
    (hμ₂ : IsExtensionByZeroBaseChange Λ h₂ hi₂ hm₂ μ₂)
    (hμ : IsExtensionByZeroBaseChange Λ H hbH hmH μ) (F : EtaleModules.{u, 0} Λ P) :
    (etaleModuleExtensionByZero.{u, 0} Λ m).map
        ((etaleModuleDirectImageComp.{u, 0} Λ f' g' pg hpg).hom.app F) ≫ μ.app F =
      μ₂.app ((etaleModuleDirectImage.{u, 0} Λ f').obj F) ≫
        (etaleModuleDirectImage.{u, 0} Λ gb).map (μ₁.app F) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ fb gb pf hpf).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ b).obj F) := by
  have := mono_etaleModuleDirectImage_map_extensionByZeroToDirectImage_comp Λ b pf H hbH F
  refine (cancel_mono ((etaleModuleDirectImage.{u, 0} Λ pf).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app F) ≫
    (etaleModuleDirectImageComp.{u, 0} Λ b pf H hbH).hom.app F)).1 ?_
  have hHh₁ : H = h₁ ≫ gb := by rw [hbH, hpf, hb₁, Category.assoc]
  have hHh₂ : H = f' ≫ h₂ := by rw [hmH, hpg, hm₂, Category.assoc]
  -- the pentagons of the composition isomorphisms of direct images
  have P₁ := etaleModuleDirectImageComp_assoc_app Λ b fb gb h₁ hb₁ pf hpf H hHh₁ hbH F
  have P₂ := etaleModuleDirectImageComp_assoc_app Λ f' g' m pg hpg h₂ hm₂ H hmH hHh₂ F
  have P₃ := etaleModuleDirectImageComp_assoc_app Λ f' i gb h₁ hi₁ h₂ hi₂ H hHh₁ hHh₂ F
  have nε := (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ m).naturality
    ((etaleModuleDirectImageComp.{u, 0} Λ f' g' pg hpg).hom.app F)
  have nc := (etaleModuleDirectImageComp.{u, 0} Λ fb gb pf hpf).hom.naturality
    ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app F)
  have h2 := hμ₂ ((etaleModuleDirectImage.{u, 0} Λ f').obj F)
  have h1 := congrArg (etaleModuleDirectImage.{u, 0} Λ gb).map (hμ₁ F)
  simp only [Functor.map_comp] at h1
  simp only [Functor.comp_map, Functor.comp_obj] at nε nc
  rw [Category.assoc, hμ F, reassoc_of% nε, P₂, Category.assoc, Category.assoc,
    ← reassoc_of% nc, ← P₁, reassoc_of% h1, P₃, reassoc_of% h2]

variable {Λ} in
/-- **Horizontal pasting on sheaves**: for two squares side by side, the maps of the squares
compose to the map of the rectangle. -/
theorem IsExtensionByZeroBaseChange.horizontal_paste {P₁ P₂ P₃ Y₁ Y₂ Y₃ : Scheme.{u}}
    {b₁ : P₁ ⟶ P₂} {b₂ : P₂ ⟶ P₃} {i₁ : Y₁ ⟶ Y₂} {i₂ : Y₂ ⟶ Y₃} [IsOpenImmersion b₁]
    [IsOpenImmersion b₂] [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    {f₁ : P₁ ⟶ Y₁} {f₂ : P₂ ⟶ Y₂} {f₃ : P₃ ⟶ Y₃}
    {h₁ : P₁ ⟶ Y₂} {hb₁ : h₁ = b₁ ≫ f₂} {hi₁ : h₁ = f₁ ≫ i₁}
    {h₂ : P₂ ⟶ Y₃} {hb₂ : h₂ = b₂ ≫ f₃} {hi₂ : h₂ = f₂ ≫ i₂}
    {H : P₁ ⟶ Y₃} {hbH : H = (b₁ ≫ b₂) ≫ f₃} {hiH : H = f₁ ≫ i₁ ≫ i₂}
    {μ₁ : etaleModuleDirectImage.{u, 0} Λ f₁ ⋙ etaleModuleExtensionByZero.{u, 0} Λ i₁ ⟶
      etaleModuleExtensionByZero.{u, 0} Λ b₁ ⋙ etaleModuleDirectImage.{u, 0} Λ f₂}
    {μ₂ : etaleModuleDirectImage.{u, 0} Λ f₂ ⋙ etaleModuleExtensionByZero.{u, 0} Λ i₂ ⟶
      etaleModuleExtensionByZero.{u, 0} Λ b₂ ⋙ etaleModuleDirectImage.{u, 0} Λ f₃}
    {μ : etaleModuleDirectImage.{u, 0} Λ f₁ ⋙ etaleModuleExtensionByZero.{u, 0} Λ (i₁ ≫ i₂) ⟶
      etaleModuleExtensionByZero.{u, 0} Λ (b₁ ≫ b₂) ⋙ etaleModuleDirectImage.{u, 0} Λ f₃}
    (hμ₁ : IsExtensionByZeroBaseChange Λ h₁ hb₁ hi₁ μ₁)
    (hμ₂ : IsExtensionByZeroBaseChange Λ h₂ hb₂ hi₂ μ₂)
    (hμ : IsExtensionByZeroBaseChange Λ H hbH hiH μ) (F : EtaleModules.{u, 0} Λ P₁) :
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ i₁ i₂).inv.app
        ((etaleModuleDirectImage.{u, 0} Λ f₁).obj F) ≫ μ.app F =
      (etaleModuleExtensionByZero.{u, 0} Λ i₂).map (μ₁.app F) ≫
        μ₂.app ((etaleModuleExtensionByZero.{u, 0} Λ b₁).obj F) ≫
        (etaleModuleDirectImage.{u, 0} Λ f₃).map
          ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ b₁ b₂).inv.app F) := by
  have := mono_etaleModuleDirectImage_map_extensionByZeroToDirectImage_comp Λ (b₁ ≫ b₂) f₃ H
    hbH F
  refine (cancel_mono ((etaleModuleDirectImage.{u, 0} Λ f₃).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ (b₁ ≫ b₂)).app F) ≫
    (etaleModuleDirectImageComp.{u, 0} Λ (b₁ ≫ b₂) f₃ H hbH).hom.app F)).1 ?_
  have hHh₁ : H = h₁ ≫ i₂ := by rw [hiH, hi₁, Category.assoc]
  have hHb₁ : H = b₁ ≫ h₂ := by rw [hbH, hb₂, Category.assoc]
  -- `ε` along composites of open immersions
  have εi := etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage Λ i₁ i₂
    ((etaleModuleDirectImage.{u, 0} Λ f₁).obj F)
  have εb := etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage Λ b₁ b₂ F
  -- the pentagons of the composition isomorphisms of direct images
  have P₁ := etaleModuleDirectImageComp_assoc_app Λ f₁ i₁ i₂ h₁ hi₁ (i₁ ≫ i₂) rfl H hHh₁ hiH F
  have P₂ := etaleModuleDirectImageComp_assoc_app Λ b₁ f₂ i₂ h₁ hb₁ h₂ hi₂ H hHh₁ hHb₁ F
  have P₃ := etaleModuleDirectImageComp_assoc_app Λ b₁ b₂ f₃ (b₁ ≫ b₂) rfl h₂ hb₂ H hbH hHb₁ F
  have nμ₂ := μ₂.naturality ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b₁).app F)
  have nε := (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i₂).naturality (μ₁.app F ≫
    (etaleModuleDirectImage.{u, 0} Λ f₂).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b₁).app F))
  have h2 := hμ₂ ((etaleModuleDirectImage.{u, 0} Λ b₁).obj F)
  have h1 := hμ₁ F
  simp only [Functor.comp_map, Functor.comp_obj] at nμ₂ nε
  have εi' : (etaleModuleExtensionByZeroCompIso.{u, 0} Λ i₁ i₂).inv.app
      ((etaleModuleDirectImage.{u, 0} Λ f₁).obj F) ≫
      (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ (i₁ ≫ i₂)).app
        ((etaleModuleDirectImage.{u, 0} Λ f₁).obj F) =
      (etaleModuleExtensionByZero.{u, 0} Λ i₂).map
          ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i₁).app
            ((etaleModuleDirectImage.{u, 0} Λ f₁).obj F)) ≫
        (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i₂).app
          ((etaleModuleDirectImage.{u, 0} Λ i₁).obj ((etaleModuleDirectImage.{u, 0} Λ f₁).obj F)) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ i₁ i₂ (i₁ ≫ i₂) rfl).hom.app
          ((etaleModuleDirectImage.{u, 0} Λ f₁).obj F) := by
    rw [← εi]
    simp
  have εb' : (etaleModuleExtensionByZeroCompIso.{u, 0} Λ b₁ b₂).inv.app F ≫
      (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ (b₁ ≫ b₂)).app F =
      (etaleModuleExtensionByZero.{u, 0} Λ b₂).map
          ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b₁).app F) ≫
        (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b₂).app
          ((etaleModuleDirectImage.{u, 0} Λ b₁).obj F) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ b₁ b₂ (b₁ ≫ b₂) rfl).hom.app F := by
    rw [← εb]
    simp
  rw [Category.assoc, hμ F, reassoc_of% εi', ← P₁]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, εb', Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, P₃, ← reassoc_of% nμ₂, reassoc_of% h2, ← P₂]
  have nε₁ := (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i₂).naturality
    ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i₁).app
      ((etaleModuleDirectImage.{u, 0} Λ f₁).obj F))
  rw [reassoc_of% nε₁, ← Functor.map_comp_assoc (etaleModuleExtensionByZero.{u, 0} Λ i₂),
    reassoc_of% nε]
  congr 1
  simp only [← Functor.map_comp_assoc, Category.assoc, h1]

/-- **The vertical pasting of two isomorphisms of squares** on sheaves:
`m_! (f' ≫ g')_* ≅ m_! g'_* f'_* ≅ ḡ_* i_! f'_* ≅ ḡ_* f̄_* b_! ≅ (f̄ ≫ ḡ)_* b_!`. -/
def etaleModuleSquareVerticalPaste {P T Y S Y₂ S₂ : Scheme.{u}}
    {b : P ⟶ T} {i : Y ⟶ S} {m : Y₂ ⟶ S₂} [IsOpenImmersion b] [IsOpenImmersion i]
    [IsOpenImmersion m] {f' : P ⟶ Y} {fb : T ⟶ S} {g' : Y ⟶ Y₂} {gb : S ⟶ S₂}
    {pg : P ⟶ Y₂} {pf : T ⟶ S₂} (hpg : pg = f' ≫ g') (hpf : pf = fb ≫ gb)
    (μ₁ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb)
    (μ₂ : etaleModuleDirectImage.{u, 0} Λ g' ⋙ etaleModuleExtensionByZero.{u, 0} Λ m ≅
      etaleModuleExtensionByZero.{u, 0} Λ i ⋙ etaleModuleDirectImage.{u, 0} Λ gb) :
    etaleModuleDirectImage.{u, 0} Λ pg ⋙ etaleModuleExtensionByZero.{u, 0} Λ m ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ pf :=
  Functor.isoWhiskerRight (etaleModuleDirectImageComp.{u, 0} Λ f' g' pg hpg).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ μ₂ ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight μ₁ _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleDirectImageComp.{u, 0} Λ fb gb pf hpf)

/-- The component of `etaleModuleSquareVerticalPaste`. -/
lemma etaleModuleSquareVerticalPaste_hom_app {P T Y S Y₂ S₂ : Scheme.{u}}
    {b : P ⟶ T} {i : Y ⟶ S} {m : Y₂ ⟶ S₂} [IsOpenImmersion b] [IsOpenImmersion i]
    [IsOpenImmersion m] {f' : P ⟶ Y} {fb : T ⟶ S} {g' : Y ⟶ Y₂} {gb : S ⟶ S₂}
    {pg : P ⟶ Y₂} {pf : T ⟶ S₂} (hpg : pg = f' ≫ g') (hpf : pf = fb ≫ gb)
    (μ₁ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb)
    (μ₂ : etaleModuleDirectImage.{u, 0} Λ g' ⋙ etaleModuleExtensionByZero.{u, 0} Λ m ≅
      etaleModuleExtensionByZero.{u, 0} Λ i ⋙ etaleModuleDirectImage.{u, 0} Λ gb)
    (F : EtaleModules.{u, 0} Λ P) :
    (etaleModuleSquareVerticalPaste Λ hpg hpf μ₁ μ₂).hom.app F =
      (etaleModuleExtensionByZero.{u, 0} Λ m).map
          ((etaleModuleDirectImageComp.{u, 0} Λ f' g' pg hpg).inv.app F) ≫
        μ₂.hom.app ((etaleModuleDirectImage.{u, 0} Λ f').obj F) ≫
        (etaleModuleDirectImage.{u, 0} Λ gb).map (μ₁.hom.app F) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ fb gb pf hpf).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ b).obj F) := by
  simp [etaleModuleSquareVerticalPaste]

variable {Λ} in
/-- **The vertical pasting of maps pinned by `ε` is pinned by `ε`.** -/
theorem IsExtensionByZeroBaseChange.verticalPaste {P T Y S Y₂ S₂ : Scheme.{u}}
    {b : P ⟶ T} {i : Y ⟶ S} {m : Y₂ ⟶ S₂} [IsOpenImmersion b] [IsOpenImmersion i]
    [IsOpenImmersion m] {f' : P ⟶ Y} {fb : T ⟶ S} {g' : Y ⟶ Y₂} {gb : S ⟶ S₂}
    {pg : P ⟶ Y₂} {pf : T ⟶ S₂} (hpg : pg = f' ≫ g') (hpf : pf = fb ≫ gb)
    {h₁ : P ⟶ S} {hb₁ : h₁ = b ≫ fb} {hi₁ : h₁ = f' ≫ i}
    {h₂ : Y ⟶ S₂} {hi₂ : h₂ = i ≫ gb} {hm₂ : h₂ = g' ≫ m}
    {μ₁ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb}
    {μ₂ : etaleModuleDirectImage.{u, 0} Λ g' ⋙ etaleModuleExtensionByZero.{u, 0} Λ m ≅
      etaleModuleExtensionByZero.{u, 0} Λ i ⋙ etaleModuleDirectImage.{u, 0} Λ gb}
    (hμ₁ : IsExtensionByZeroBaseChange Λ h₁ hb₁ hi₁ μ₁.hom)
    (hμ₂ : IsExtensionByZeroBaseChange Λ h₂ hi₂ hm₂ μ₂.hom)
    (H : P ⟶ S₂) (hbH : H = b ≫ pf) (hmH : H = pg ≫ m) :
    IsExtensionByZeroBaseChange Λ H hbH hmH
      (etaleModuleSquareVerticalPaste Λ hpg hpf μ₁ μ₂).hom := by
  intro F
  have hHh₁ : H = h₁ ≫ gb := by rw [hbH, hpf, hb₁, Category.assoc]
  have hHh₂ : H = f' ≫ h₂ := by rw [hmH, hpg, hm₂, Category.assoc]
  have P₁ := etaleModuleDirectImageComp_assoc_app Λ b fb gb h₁ hb₁ pf hpf H hHh₁ hbH F
  have P₂ := etaleModuleDirectImageComp_assoc_app Λ f' g' m pg hpg h₂ hm₂ H hmH hHh₂ F
  have P₃ := etaleModuleDirectImageComp_assoc_app Λ f' i gb h₁ hi₁ h₂ hi₂ H hHh₁ hHh₂ F
  have nε := (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ m).naturality
    ((etaleModuleDirectImageComp.{u, 0} Λ f' g' pg hpg).inv.app F)
  have nc := (etaleModuleDirectImageComp.{u, 0} Λ fb gb pf hpf).hom.naturality
    ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app F)
  have h2 := hμ₂ ((etaleModuleDirectImage.{u, 0} Λ f').obj F)
  have h1 := congrArg (etaleModuleDirectImage.{u, 0} Λ gb).map (hμ₁ F)
  simp only [Functor.map_comp] at h1
  simp only [Functor.comp_map, Functor.comp_obj] at nε nc
  rw [etaleModuleSquareVerticalPaste_hom_app]
  simp only [Category.assoc]
  rw [← reassoc_of% nc, ← P₁, reassoc_of% h1, P₃, reassoc_of% h2, ← P₂, reassoc_of% nε,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]


section ProperOpen

/-- **`ε_r : r_! ⟶ r_*` is an isomorphism for a proper open immersion `r`**: through the
identity of `U` it is the comparison `θ_r : r_! ⟶ r_* (𝟙_U)_!` of [Stacks, Tag 0F7G], invertible
since `r` is proper, followed by `r_*` of `ε_{𝟙_U}`, which is invertible since restriction along
`𝟙_U` reflects isomorphisms. -/
theorem isIso_etaleModuleExtensionByZeroToDirectImage_app_of_isProper {U V : Scheme.{u}}
    (r : U ⟶ V) [IsOpenImmersion r] [IsProper r] (F : EtaleModules.{u, 0} Λ U) :
    IsIso ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ r).app F) := by
  have hid : IsIso ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ (𝟙 U)).app F) :=
    isIso_of_isIso_etaleModuleRestriction Λ (𝟙 U) _ inferInstance
  have hθ := isIso_etaleModuleRefinementComparison_univ Λ (Category.id_comp r)
  have e := etaleModuleRefinementComparison_comp_map Λ (Category.id_comp r) F
  have : IsIso ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ r).app F ≫
      (etaleModuleDirectImageComp.{u, 0} Λ (𝟙 U) r r (Category.id_comp r).symm).inv.app F) := by
    rw [← e]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((etaleModuleDirectImageComp.{u, 0} Λ (𝟙 U) r r (Category.id_comp r).symm).inv.app F)

/-- `ε_r : r_! ⟶ r_*` is an isomorphism for a proper open immersion `r`. -/
instance isIso_etaleModuleExtensionByZeroToDirectImage_of_isProper {U V : Scheme.{u}}
    (r : U ⟶ V) [IsOpenImmersion r] [IsProper r] :
    IsIso (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ r) :=
  have := fun F => isIso_etaleModuleExtensionByZeroToDirectImage_app_of_isProper Λ r F
  NatIso.isIso_of_isIso_app _

variable {P T Y S : Scheme.{u}} {b : P ⟶ T} {i : Y ⟶ S} [IsOpenImmersion b] [IsOpenImmersion i]
  {f' : P ⟶ Y} [IsOpenImmersion f'] [IsProper f'] {fb : T ⟶ S} [IsProper fb]
  (w : b ≫ fb = f' ≫ i)

/-- **The map of [Stacks, Tag 0F7B] of a square whose left side is a proper open immersion**:
for `b ≫ f̄ = f' ≫ i` with `f'` a proper open immersion and `f̄` proper,
`i_! f'_* ≅ i_! f'_! ≅ (f' ≫ i)_! ≅ f̄_* b_!`, the last isomorphism being the comparison of
[Stacks, Tag 0F7G] for `b ≫ f̄ = f' ≫ i`. -/
def etaleModuleSquareIsoOfIsProperOpen :
    etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb :=
  haveI := isIso_etaleModuleRefinementComparison_univ Λ w
  Functor.isoWhiskerRight (asIso (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ f')).symm
      (etaleModuleExtensionByZero.{u, 0} Λ i) ≪≫
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ f' i).symm ≪≫
    asIso (etaleModuleRefinementComparison Λ w)

/-- The component of `etaleModuleSquareIsoOfIsProperOpen`. -/
lemma etaleModuleSquareIsoOfIsProperOpen_hom_app (F : EtaleModules.{u, 0} Λ P) :
    (etaleModuleSquareIsoOfIsProperOpen Λ w).hom.app F =
      (etaleModuleExtensionByZero.{u, 0} Λ i).map
          ((asIso (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ f')).inv.app F) ≫
        (etaleModuleExtensionByZeroCompIso.{u, 0} Λ f' i).inv.app F ≫
        (etaleModuleRefinementComparison Λ w).app F :=
  rfl

/-- The map `etaleModuleSquareIsoOfIsProperOpen` is pinned by `ε`. -/
theorem isExtensionByZeroBaseChange_etaleModuleSquareIsoOfIsProperOpen :
    IsExtensionByZeroBaseChange Λ (f' ≫ i) w.symm rfl
      (etaleModuleSquareIsoOfIsProperOpen Λ w).hom := by
  intro F
  have e1 := etaleModuleRefinementComparison_comp_map Λ w F
  have e2 := etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage Λ f' i F
  have hε : (asIso (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ f')).inv.app F ≫
      (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ f').app F = 𝟙 _ :=
    (asIso (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ f')).inv_hom_id_app F
  rw [etaleModuleSquareIsoOfIsProperOpen_hom_app, Category.assoc, Category.assoc,
    reassoc_of% e1, Iso.inv_hom_id_app, ← e2]
  simp only [Category.comp_id, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, hε,
    CategoryTheory.Functor.map_id, Category.id_comp]

end ProperOpen

/-- **The open immersion case of [Stacks, Tag 0F7B] on sheaves is the map pinned by `ε`**, over
a torsion ring. -/
theorem isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb]
    (i : Y ⟶ Ub) [IsOpenImmersion i] (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y)
    (sq : IsPullback b f' fb i) :
    IsExtensionByZeroBaseChange Λ (f' ≫ i) sq.w.symm rfl
      (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq).hom :=
  fun F => etaleModuleDirectImageExtensionByZeroIso_hom_comp_toDirectImage Λ fb i b f' sq hΛ F

section Refinement

variable {X A B : Scheme.{u}} {j : X ⟶ A} {k : X ⟶ B} {g : A ⟶ B} [IsOpenImmersion j]
  [IsOpenImmersion k] [IsSeparated g] (hjk : j ≫ g = k)

/-- The comparison `θ_g : k_! ⟶ g_* j_!` of [Stacks, Tag 0F7G], as the map of the square
`j ≫ g = 𝟙 ≫ k`: `k_! (𝟙_X)_* ≅ k_! ⟶ g_* j_!`. -/
def etaleModuleRefinementSquare :
    etaleModuleDirectImage.{u, 0} Λ (𝟙 X) ⋙ etaleModuleExtensionByZero.{u, 0} Λ k ⟶
      etaleModuleExtensionByZero.{u, 0} Λ j ⋙ etaleModuleDirectImage.{u, 0} Λ g :=
  Functor.whiskerRight (etaleModuleDirectImageIdIso.{u, 0} Λ X).hom _ ≫
    (Functor.leftUnitor _).hom ≫ etaleModuleRefinementComparison Λ hjk

/-- The component of `etaleModuleRefinementSquare`. -/
lemma etaleModuleRefinementSquare_app (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleRefinementSquare Λ hjk).app F =
      (etaleModuleExtensionByZero.{u, 0} Λ k).map
          ((etaleModuleDirectImageIdIso.{u, 0} Λ X).hom.app F) ≫
        (etaleModuleRefinementComparison Λ hjk).app F := by
  simp [etaleModuleRefinementSquare]

/-- **The map of [Stacks, Tag 0F7G] on sheaves is pinned by `ε`.** -/
theorem isExtensionByZeroBaseChange_etaleModuleRefinementSquare :
    IsExtensionByZeroBaseChange Λ k hjk.symm (Category.id_comp k).symm
      (etaleModuleRefinementSquare Λ hjk) := by
  intro F
  rw [etaleModuleRefinementSquare_app, Category.assoc,
    reassoc_of% etaleModuleRefinementComparison_comp_map, Iso.inv_hom_id_app, Category.comp_id,
    etaleModuleDirectImageComp_id_left_hom_app]
  exact (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ k).naturality
    ((etaleModuleDirectImageIdIso.{u, 0} Λ X).hom.app F)

end Refinement

end Sheaves

/-! ### The map of a square on unbounded derived categories -/

section Derived

open Stacks.Injectives.KInjectiveResolution (isRightDerivedFunctor_iff_isIso_app_of_isKInjective
  invertsQuasiIso_mapHomologicalComplex_comp_Q InvertsQuasiIsoOfIsKInjective
  invertsQuasiIsoOfIsKInjective_comp)

/-- `Q ⋙ Rj_! ≅ j_! ⋙ Q`: the unbounded derived extension by zero is extension by zero applied
degreewise. -/
def etaleModuleDerivedExtensionByZeroUnboundedFactors {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    DerivedCategory.Q ⋙ etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j ≅
      (etaleModuleExtensionByZero.{u, 0} Λ j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ j) ≪≫
    (etaleModuleExtensionByZero.{u, 0} Λ j).mapDerivedCategoryFactors

/-- The derivation unit of `Rj_!` at a complex is the factorization `Q ⋙ Rj_! ≅ j_! ⋙ Q`. -/
lemma etaleModuleDerivedExtensionByZeroUnboundedUnit_app_eq_factors_inv {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] (K : CochainComplex (EtaleModules.{u, 0} Λ U) ℤ) :
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ j).app K =
      (etaleModuleDerivedExtensionByZeroUnboundedFactors Λ j).inv.app K := by
  have h₁ : (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ j).app K ≫
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ j).hom.app
        (DerivedCategory.Q.obj K) =
      (etaleModuleExtensionByZero.{u, 0} Λ j).mapDerivedCategoryFactors.inv.app K := by
    rw [etaleModuleDerivedExtensionByZeroUnboundedIso,
      Stacks.Injectives.KInjectiveResolution.isoMapDerivedCategoryOfIsRightDerivedFunctor,
      Functor.rightDerivedNatIso_hom, Functor.rightDerivedNatTrans_app]
    simp
  simp only [etaleModuleDerivedExtensionByZeroUnboundedFactors, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerLeft_app, ← h₁,
    Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- `Rf_* ⋙ G`, with the unit of `Rf_*` followed by `G`, is a right derived functor of
`f_* ⋙ Q ⋙ G`: both are computed on K-injective complexes. -/
instance isRightDerivedFunctor_etaleModuleDerivedDirectImageUnbounded_whiskerUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) {H : Type*} [Category* H]
    (G : DerivedCategory (EtaleModules.{u, 0} Λ Y) ⥤ H) :
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f ⋙ G).IsRightDerivedFunctor
      (Stacks.DerivedBaseChange.whiskerUnit
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f) G)
      (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIsoOfIsKInjective_comp
      (invertsQuasiIso_mapHomologicalComplex_comp_Q (etaleModuleDirectImage.{u, 0} Λ f)) G)]
  intro I hI
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, 0} Λ f I hI
  simp only [Stacks.DerivedBaseChange.whiskerUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id]
  infer_instance

variable {P T Y S : Scheme.{u}} (b : P ⟶ T) (i : Y ⟶ S) [IsOpenImmersion b] [IsOpenImmersion i]
  (f' : P ⟶ Y) (fb : T ⟶ S)

/-- The isomorphism of degreewise functors on cochain complexes induced by an isomorphism
`i_! f'_* ≅ f̄_* b_!` of functors on sheaves. -/
def etaleModuleSquareComplexIso
    (μ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb) :
    (etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (etaleModuleExtensionByZero.{u, 0} Λ i).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (etaleModuleDirectImage.{u, 0} Λ fb).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
    NatIso.mapHomologicalComplex μ (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- The component of `etaleModuleSquareComplexIso`. -/
lemma etaleModuleSquareComplexIso_hom_app
    (μ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb)
    (K : CochainComplex (EtaleModules.{u, 0} Λ P) ℤ) :
    (etaleModuleSquareComplexIso Λ b i f' fb μ).hom.app K =
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app K).hom ≫
        (NatIso.mapHomologicalComplex μ (ComplexShape.up ℤ)).hom.app K ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv.app K :=
  rfl

/-- `etaleModuleSquareComplexIso` is `μ` in each degree. -/
@[simp]
lemma etaleModuleSquareComplexIso_hom_app_f
    (μ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb)
    (K : CochainComplex (EtaleModules.{u, 0} Λ P) ℤ) (n : ℤ) :
    ((etaleModuleSquareComplexIso Λ b i f' fb μ).hom.app K).f n = μ.hom.app (K.X n) := by
  simp [etaleModuleSquareComplexIso]

/-- **The map `i_! ∘ Rf'_* ⟶ Rf̄_* ∘ b_!` of [Stacks, Tag 0F7B]** on unbounded derived categories,
induced by an isomorphism `μ : i_! f'_* ≅ f̄_* b_!` of functors on sheaves: the base change map
`Stacks.DerivedBaseChange.squareMap` of the square of degreewise functors. -/
def derivedExtensionByZeroSquareMap
    (μ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb) :
    etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f' ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ i ⟶
      etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ b ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb :=
  Stacks.DerivedBaseChange.squareMap
    (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P) (ComplexShape.up ℤ))
    (etaleModuleDerivedExtensionByZeroUnboundedFactors Λ b)
    (etaleModuleDerivedExtensionByZeroUnboundedFactors Λ i)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f')
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb)
    (etaleModuleSquareComplexIso Λ b i f' fb μ)

/-- The characterizing property of `derivedExtensionByZeroSquareMap`. -/
@[reassoc]
lemma derivedExtensionByZeroSquareMap_fac_app
    (μ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb)
    (K : CochainComplex (EtaleModules.{u, 0} Λ P) ℤ) :
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ i).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app K) ≫
      (derivedExtensionByZeroSquareMap Λ b i f' fb μ).app (DerivedCategory.Q.obj K) =
    (etaleModuleDerivedExtensionByZeroUnboundedFactors Λ i).hom.app
        (((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((etaleModuleSquareComplexIso Λ b i f' fb μ).hom.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb).app
        (((etaleModuleExtensionByZero.{u, 0} Λ b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb).map
        ((etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ b).app K) := by
  rw [etaleModuleDerivedExtensionByZeroUnboundedUnit_app_eq_factors_inv]
  exact Stacks.DerivedBaseChange.squareMap_fac_app _ _ _ _ _ _ K

/-- Two transformations out of `i_! ∘ Rf'_*` agreeing after the unit of `Rf'_*` agree. -/
lemma derivedExtensionByZeroSquare_ext {H : Type*} [Category* H]
    {G : DerivedCategory (EtaleModules.{u, 0} Λ Y) ⥤ H}
    {G' : DerivedCategory (EtaleModules.{u, 0} Λ P) ⥤ H}
    (τ₁ τ₂ : etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f' ⋙ G ⟶ G')
    (h : ∀ K : CochainComplex (EtaleModules.{u, 0} Λ P) ℤ,
      G.map ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app K) ≫
          τ₁.app (DerivedCategory.Q.obj K) =
        G.map ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app K) ≫
          τ₂.app (DerivedCategory.Q.obj K)) : τ₁ = τ₂ := by
  refine Functor.rightDerived_ext _ (Stacks.DerivedBaseChange.whiskerUnit
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f') G)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simpa [Stacks.DerivedBaseChange.whiskerUnit] using h K


/-! ### Composition of derived extensions by zero -/

/-- `Rb₁_! ⋙ Rb₂_! ≅ R(b₁ ≫ b₂)_!` on unbounded derived categories, through the degreewise
extensions by zero. -/
def derivedExtensionByZeroUnboundedCompIso {X U V : Scheme.{u}} (a : X ⟶ U)
    (c : U ⟶ V) [IsOpenImmersion a] [IsOpenImmersion c] :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ a ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ c ≅
      etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (a ≫ c) :=
  (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ (a ≫ c) ≪≫
    Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a c) ≪≫
    Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ a).symm _ ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ c).symm).symm

/-- The composition isomorphism of derived extensions by zero, on a complex. -/
lemma derivedExtensionByZeroUnboundedCompIso_hom_app_Q {X U V : Scheme.{u}}
    (a : X ⟶ U) (c : U ⟶ V) [IsOpenImmersion a] [IsOpenImmersion c]
    (K : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) :
    (derivedExtensionByZeroUnboundedCompIso Λ a c).hom.app (DerivedCategory.Q.obj K) =
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ c).map
          ((etaleModuleDerivedExtensionByZeroUnboundedFactors Λ a).hom.app K) ≫
        (etaleModuleDerivedExtensionByZeroUnboundedFactors Λ c).hom.app
          (((etaleModuleExtensionByZero.{u, 0} Λ a).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a c).symm (ComplexShape.up ℤ)).hom.app K) ≫
        (etaleModuleDerivedExtensionByZeroUnboundedFactors Λ (a ≫ c)).inv.app K := by
  have h₂ : (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ c)).mapDerivedCategoryFactors.inv.app K ≫
      (Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
        (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a c)).hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a c).symm (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ c).mapDerivedCategoryFactors.inv.app
          (((etaleModuleExtensionByZero.{u, 0} Λ a).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ c).mapDerivedCategory.map
          ((etaleModuleExtensionByZero.{u, 0} Λ a).mapDerivedCategoryFactors.inv.app K) := by
    have hL : Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
        ((etaleModuleExtensionByZero.{u, 0} Λ (a ≫ c)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
        (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ c)).mapDerivedCategory =
        (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ c)).mapDerivedCategoryFactors := rfl
    simp [Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso, Localization.liftNatTrans_app, hL]
  have hdeg : (NatIso.mapHomologicalComplex
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a c).symm (ComplexShape.up ℤ)).inv.app K =
      (Functor.mapHomologicalComplexCompIso
        (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a c).symm (ComplexShape.up ℤ)).inv.app K := by
    ext n : 1
    simp
  rw [hdeg] at h₂
  have h₂' : (Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a c)).inv.app (DerivedCategory.Q.obj K) =
      (etaleModuleExtensionByZero.{u, 0} Λ c).mapDerivedCategory.map
          ((etaleModuleExtensionByZero.{u, 0} Λ a).mapDerivedCategoryFactors.hom.app K) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ c).mapDerivedCategoryFactors.hom.app
          (((etaleModuleExtensionByZero.{u, 0} Λ a).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a c).symm (ComplexShape.up ℤ)).hom.app K) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ c)).mapDerivedCategoryFactors.inv.app K := by
    rw [← Iso.app_inv]
    refine Iso.inv_ext ?_
    rw [Iso.app_hom, ← cancel_epi ((etaleModuleExtensionByZero.{u, 0} Λ
      (a ≫ c)).mapDerivedCategoryFactors.inv.app K), reassoc_of% h₂]
    simp [← Functor.map_comp_assoc]
  have nι := (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ c).hom.naturality
    ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ a).hom.app (DerivedCategory.Q.obj K) ≫
      (etaleModuleExtensionByZero.{u, 0} Λ a).mapDerivedCategoryFactors.hom.app K)
  simp only [derivedExtensionByZeroUnboundedCompIso, Iso.symm_hom, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc, h₂',
    etaleModuleDerivedExtensionByZeroUnboundedFactors, Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  rw [reassoc_of% nι]
  simp only [Functor.map_comp, Category.assoc]

/-! ### The open immersion case -/

/-- The open immersion case of [Stacks, Tag 0F7B] on `D(P_étale, Λ)`, read through the derived
extensions by zero: `Rb_! ⋙ Rf̄_* ≅ Rf'_* ⋙ Ri_!`. -/
def etaleModuleExtensionByZeroDirectImageUnboundedIsoE (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)
    {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
    (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i) [CompactSpace Ub] :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ b ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb ≅
      etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f' ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ i :=
  Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ b) _ ≪≫
    etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ fb i b f' sq ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ i).symm

/-- The component of the inverse of `etaleModuleExtensionByZeroDirectImageUnboundedIsoE`. -/
lemma etaleModuleExtensionByZeroDirectImageUnboundedIsoE_inv_app
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)
    {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
    (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i) [CompactSpace Ub]
    (K : DerivedCategory (EtaleModules.{u, 0} Λ P)) :
    (etaleModuleExtensionByZeroDirectImageUnboundedIsoE Λ hΛ fb i b f' sq).inv.app K =
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ i).hom.app
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f').obj K) ≫
        (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ fb i b f' sq).inv.app K ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb).map
          ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ b).inv.app K) := by
  simp only [etaleModuleExtensionByZeroDirectImageUnboundedIsoE, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_inv, Category.assoc]

section IsoE

variable (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb]
  (i : Y ⟶ Ub) [IsOpenImmersion i] (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y)
  (sq : IsPullback b f' fb i) (K : CochainComplex (EtaleModules.{u, 0} Λ P) ℤ)

/-- The derivation unit of `Rf'_* ⋙ i_!` at a complex. -/
lemma directImageExtensionByZeroUnboundedUnit_app_eq :
    (directImageExtensionByZeroUnboundedUnit Λ i f').app K =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i))
          (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ i).mapDerivedCategoryFactors.inv.app
          (((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ i).mapDerivedCategory.map
          ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app K) := by
  simp only [directImageExtensionByZeroUnboundedUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

omit [IsProper fb] in
/-- The derivation unit of `b_! ⋙ Rf̄_*`, at a complex. -/
lemma extensionByZeroDirectImageUnboundedUnit_app_eq :
    (extensionByZeroDirectImageUnboundedUnit Λ fb b).app K =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb))
          (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb).app
          (((etaleModuleExtensionByZero.{u, 0} Λ b).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb).map
          ((etaleModuleExtensionByZero.{u, 0} Λ b).mapDerivedCategoryFactors.inv.app K) := by
  simp only [extensionByZeroDirectImageUnboundedUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

/-- The derivation unit of `b_! ⋙ Rf̄_*` through `i_! f'_* ≅ f̄_* b_!`. -/
lemma directImageExtensionByZeroUnboundedUnit'_eq [CompactSpace Ub] :
    directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq =
      Functor.whiskerRight (NatIso.mapHomologicalComplex
          (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq) (ComplexShape.up ℤ)).hom
          DerivedCategory.Q ≫ extensionByZeroDirectImageUnboundedUnit Λ fb b :=
  rfl

/-- The inverse of the open immersion case of [Stacks, Tag 0F7B] after the derivation unit of
`Rf'_* ⋙ i_!` is the other derivation unit. -/
lemma directImageExtensionByZeroUnboundedUnit_app_comp_inv [CompactSpace Ub] :
    (directImageExtensionByZeroUnboundedUnit Λ i f').app K ≫
      (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ fb i b f' sq).inv.app
        (DerivedCategory.Q.obj K) =
      (directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq).app K := by
  have hβ : (directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq).app K ≫
      (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ fb i b f' sq).hom.app
        (DerivedCategory.Q.obj K) =
      (directImageExtensionByZeroUnboundedUnit Λ i f').app K := by
    simp only [etaleModuleExtensionByZeroDirectImageUnboundedIso, Functor.rightDerivedNatIso_hom,
      Functor.rightDerivedNatTrans_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [← hβ, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

end IsoE

/-- The chase of `etaleModuleExtensionByZeroDirectImageUnboundedIsoE_inv`, over plain
objects. -/
private lemma isoE_inv_chain {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Q : 𝒞 ⥤ 𝒟)
    {k₁ k₂ k₃ k₄ : 𝒞} {a₀ a₁ a₂ a₃ a₄ c₀ c₅ : 𝒟}
    (eu : a₀ ⟶ a₁) (ιR : a₁ ⟶ a₂) (βi : a₂ ⟶ a₃) (Rι : a₃ ⟶ a₄)
    (ιQ : a₀ ⟶ c₀) (Mu : c₀ ⟶ a₂) (φh : a₀ ⟶ Q.obj k₁) (fh : c₀ ⟶ Q.obj k₁)
    (fi : Q.obj k₁ ⟶ c₀) (x : k₁ ⟶ k₂) (Qc : Q.obj k₂ ⟶ Q.obj k₁) (dU : Q.obj k₂ ⟶ a₂)
    (s : k₁ ⟶ k₄) (y : k₂ ⟶ k₃) (z : k₃ ⟶ k₄) (ub : Q.obj k₄ ⟶ c₅)
    (Rf : c₅ ⟶ a₃) (RuE : c₅ ⟶ a₄)
    (n1 : eu ≫ ιR = ιQ ≫ Mu) (d1 : φh = ιQ ≫ fh) (hu : dU = Qc ≫ fi ≫ Mu)
    (hfi : fh ≫ fi = 𝟙 _) (hQc : Q.map x ≫ Qc = 𝟙 _) (dE : Q.obj k₃ ⟶ a₃)
    (hinv : dU ≫ βi = Q.map y ≫ dE) (hdE : dE = Q.map z ≫ ub ≫ Rf)
    (hb : RuE = Rf ≫ Rι) (hQ : s = x ≫ y ≫ z)
    (Einv : a₁ ⟶ a₄) (hE : Einv = ιR ≫ βi ≫ Rι) :
    eu ≫ Einv = φh ≫ Q.map s ≫ ub ≫ RuE := by
  have hMu : Mu = fh ≫ Q.map x ≫ dU := by rw [hu, reassoc_of% hQc, reassoc_of% hfi]
  rw [hE, reassoc_of% n1, hMu, d1, hb, hQ, Q.map_comp, Q.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hinv, hdE]
  simp only [Category.assoc]

/-- **The open immersion case of [Stacks, Tag 0F7B] is the map of its square**: the inverse of
`Rb_! ⋙ Rf̄_* ≅ Rf'_* ⋙ Ri_!` is the map induced by `i_! f'_* ≅ f̄_* b_!`. -/
theorem etaleModuleExtensionByZeroDirectImageUnboundedIsoE_inv
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)
    {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
    (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i) [CompactSpace Ub] :
    (etaleModuleExtensionByZeroDirectImageUnboundedIsoE Λ hΛ fb i b f' sq).inv =
      derivedExtensionByZeroSquareMap Λ b i f' fb
        (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq) := by
  refine derivedExtensionByZeroSquare_ext Λ f' _ _ (fun K => ?_)
  rw [derivedExtensionByZeroSquareMap_fac_app]
  have nι := (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ i).hom.naturality
    ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app K)
  have d1 : (etaleModuleDerivedExtensionByZeroUnboundedFactors Λ i).hom.app
      (((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ i).hom.app
          (DerivedCategory.Q.obj
            (((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ i).mapDerivedCategoryFactors.hom.app
          (((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) :=
    rfl
  have hb : (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb).map
        ((etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ b).app K) =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb).map
          ((etaleModuleExtensionByZero.{u, 0} Λ b).mapDerivedCategoryFactors.inv.app K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb).map
          ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ b).inv.app
            (DerivedCategory.Q.obj K)) := by
    rw [etaleModuleDerivedExtensionByZeroUnboundedUnit_app_eq_factors_inv]
    exact Functor.map_comp _ _ _
  have hinv := directImageExtensionByZeroUnboundedUnit_app_comp_inv Λ hΛ fb i b f' sq K
  rw [directImageExtensionByZeroUnboundedUnit'_eq, NatTrans.comp_app,
    Functor.whiskerRight_app] at hinv
  exact isoE_inv_chain DerivedCategory.Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nι d1
    (directImageExtensionByZeroUnboundedUnit_app_eq Λ i f' K) (Iso.hom_inv_id_app _ _)
    (DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i))
      (ComplexShape.up ℤ)).app K)).hom_inv_id
    _ hinv (extensionByZeroDirectImageUnboundedUnit_app_eq Λ fb b K) hb
    (etaleModuleSquareComplexIso_hom_app Λ b i f' fb _ K) _
    (etaleModuleExtensionByZeroDirectImageUnboundedIsoE_inv_app Λ hΛ fb i b f' sq _)

/-! ### The map of [Stacks, Tag 0F7G] -/

section Refinement

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {j k : CompactificationOf (Over.mk f)} (ψ : j ⟶ k)

/-- `θ_ψ : k_! ≅ ψ̄_* j_!` for a morphism `ψ` of compactifications, as an isomorphism of the
square `j ≫ ψ̄ = 𝟙 ≫ k`. -/
def refinementSquareIso :
    etaleModuleDirectImage.{u, 0} Λ (𝟙 X) ⋙ etaleModuleExtensionByZero.{u, 0} Λ k.immersion ≅
      etaleModuleExtensionByZero.{u, 0} Λ j.immersion ⋙
        etaleModuleDirectImage.{u, 0} Λ (CompactificationOf.Hom.map ψ) :=
  Functor.isoWhiskerRight (etaleModuleDirectImageIdIso.{u, 0} Λ X) _ ≪≫ Functor.leftUnitor _ ≪≫
    refinementIsoUniv Λ ψ

/-- The isomorphism `refinementSquareIso` is the map pinned by `ε`. -/
lemma refinementSquareIso_hom :
    (refinementSquareIso Λ ψ).hom =
      etaleModuleRefinementSquare Λ (CompactificationOf.immersion_comp_map ψ) := by
  ext F
  simp [refinementSquareIso, etaleModuleRefinementSquare, refinementIsoUniv]

/-- Cancelling an inverse pair in the middle of a composite, over plain objects. -/
private lemma cancel_mid_chain {𝒞 : Type*} [Category* 𝒞] {a b c d e : 𝒞} (A : a ⟶ b)
    (p : b ⟶ c) (q : c ⟶ b) (S : b ⟶ d) (T : d ⟶ e) (X : a ⟶ d) (hφ : p ≫ q = 𝟙 b)
    (hX : X = A ≫ S) : X ≫ T = A ≫ p ≫ q ≫ S ≫ T := by
  rw [reassoc_of% hφ, hX, Category.assoc]

/-- **The map `Rk_! ⟶ Rψ̄_* ∘ Rj_!` of [Stacks, Tag 0F7G] is the map of its square**, through
`𝟭 ≅ R(𝟙_X)_*`. -/
theorem derivedRefinementComparisonUnboundedUniv_eq_squareMap :
    derivedRefinementComparisonUnboundedUniv.{u, 0} Λ ψ =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ X).inv _ ≫
        derivedExtensionByZeroSquareMap Λ j.immersion k.immersion (𝟙 X)
          (CompactificationOf.Hom.map ψ) (refinementSquareIso Λ ψ) := by
  refine Functor.rightDerived_ext _
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ k.immersion)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.id_comp]
  rw [derivedRefinementComparisonUnboundedUniv, Stacks.DerivedBaseChange.compComparison_fac_app,
    etaleModuleDerivedDirectImageUnboundedIdIso_inv_app_Q, Functor.map_comp]
  have nE := (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ k.immersion).naturality
    ((Functor.mapHomologicalComplexIdIso (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ)).inv.app K ≫
      (NatIso.mapHomologicalComplex (etaleModuleDirectImageIdIso.{u, 0} Λ X)
        (ComplexShape.up ℤ)).inv.app K)
  simp only [Functor.comp_map, Functor.id_obj] at nE
  have hQ : ((etaleModuleExtensionByZero.{u, 0} Λ k.immersion).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexIdIso (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ)).inv.app
          K ≫ (NatIso.mapHomologicalComplex (etaleModuleDirectImageIdIso.{u, 0} Λ X)
            (ComplexShape.up ℤ)).inv.app K) ≫
      (etaleModuleSquareComplexIso Λ j.immersion k.immersion (𝟙 X)
        (CompactificationOf.Hom.map ψ) (refinementSquareIso Λ ψ)).hom.app K =
      (Functor.mapHomologicalComplexCompIso (refinementIsoUniv Λ ψ).symm
        (ComplexShape.up ℤ)).inv.app K := by
    ext n : 1
    simp [etaleModuleSquareComplexIso, refinementSquareIso]
  have hQ' := (congrArg DerivedCategory.Q.map hQ).symm.trans (Functor.map_comp _ _ _)
  have hφ := (etaleModuleDerivedExtensionByZeroUnboundedFactors Λ k.immersion).inv_hom_id_app
    (((etaleModuleDirectImage.{u, 0} Λ (𝟙 X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  simp only [Category.assoc]
  rw [← reassoc_of% nE, derivedExtensionByZeroSquareMap_fac_app,
    etaleModuleDerivedExtensionByZeroUnboundedUnit_app_eq_factors_inv Λ k.immersion
      (((etaleModuleDirectImage.{u, 0} Λ (𝟙 X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)]
  exact cancel_mid_chain _ _ _ _ _ _ hφ hQ'

end Refinement

/-! ### Pasting -/

/-- **[Stacks, Tag 0F7C] on unbounded derived categories**: for two squares on top of each other
whose maps of sheaves paste, the map of the rectangle followed by the Leray isomorphism of its
right side is the Leray isomorphism of its left side followed by the maps of the two squares. -/
theorem derivedExtensionByZeroSquareMap_vertical_paste {P T Y S Y₂ S₂ : Scheme.{u}}
    (b : P ⟶ T) (i : Y ⟶ S) (m : Y₂ ⟶ S₂) [IsOpenImmersion b] [IsOpenImmersion i]
    [IsOpenImmersion m] (f' : P ⟶ Y) (fb : T ⟶ S) (g' : Y ⟶ Y₂) (gb : S ⟶ S₂)
    (pg : P ⟶ Y₂) (pf : T ⟶ S₂) (hpg : pg = f' ≫ g') (hpf : pf = fb ≫ gb)
    (μ₁ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb)
    (μ₂ : etaleModuleDirectImage.{u, 0} Λ g' ⋙ etaleModuleExtensionByZero.{u, 0} Λ m ≅
      etaleModuleExtensionByZero.{u, 0} Λ i ⋙ etaleModuleDirectImage.{u, 0} Λ gb)
    (μ : etaleModuleDirectImage.{u, 0} Λ pg ⋙ etaleModuleExtensionByZero.{u, 0} Λ m ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ pf)
    (hpaste : ∀ F : EtaleModules.{u, 0} Λ P, (etaleModuleExtensionByZero.{u, 0} Λ m).map
        ((etaleModuleDirectImageComp.{u, 0} Λ f' g' pg hpg).hom.app F) ≫ μ.hom.app F =
      μ₂.hom.app ((etaleModuleDirectImage.{u, 0} Λ f').obj F) ≫
        (etaleModuleDirectImage.{u, 0} Λ gb).map (μ₁.hom.app F) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ fb gb pf hpf).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ b).obj F)) :
    derivedExtensionByZeroSquareMap Λ b m pg pf μ ≫
        Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ b)
          (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ fb gb pf hpf).hom =
      Functor.whiskerRight
          (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ f' g' pg hpg).hom
          (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ m) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f')
          (derivedExtensionByZeroSquareMap Λ i m g' gb μ₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedExtensionByZeroSquareMap Λ b i f' fb μ₁)
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ gb) ≫
        (Functor.associator _ _ _).hom := by
  rw [etaleModuleDerivedDirectImageUnboundedLerayIso_hom_eq_compComparison,
    etaleModuleDerivedDirectImageUnboundedLerayIso_hom_eq_compComparison]
  refine Stacks.DerivedBaseChange.squareMap_vertical_paste
    (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P) (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ T) (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ Y) (ComplexShape.up ℤ)) _ _ _ _ _ _ _ _
    _ _ _ _ _ _ fun K => ?_
  ext n : 1
  simpa [etaleModuleSquareComplexIso] using hpaste (K.X n)

/-- **[Stacks, Tag 0F7D] on unbounded derived categories**: for two squares side by side whose
maps of sheaves paste, the map of the rectangle is the composite of the maps of the two squares,
through the composition isomorphisms of derived extensions by zero. -/
theorem derivedExtensionByZeroSquareMap_horizontal_paste {P₁ P₂ P₃ Y₁ Y₂ Y₃ : Scheme.{u}}
    (b₁ : P₁ ⟶ P₂) (b₂ : P₂ ⟶ P₃) (i₁ : Y₁ ⟶ Y₂) (i₂ : Y₂ ⟶ Y₃) [IsOpenImmersion b₁]
    [IsOpenImmersion b₂] [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (f₁ : P₁ ⟶ Y₁) (f₂ : P₂ ⟶ Y₂) (f₃ : P₃ ⟶ Y₃)
    (μ₁ : etaleModuleDirectImage.{u, 0} Λ f₁ ⋙ etaleModuleExtensionByZero.{u, 0} Λ i₁ ≅
      etaleModuleExtensionByZero.{u, 0} Λ b₁ ⋙ etaleModuleDirectImage.{u, 0} Λ f₂)
    (μ₂ : etaleModuleDirectImage.{u, 0} Λ f₂ ⋙ etaleModuleExtensionByZero.{u, 0} Λ i₂ ≅
      etaleModuleExtensionByZero.{u, 0} Λ b₂ ⋙ etaleModuleDirectImage.{u, 0} Λ f₃)
    (μ : etaleModuleDirectImage.{u, 0} Λ f₁ ⋙ etaleModuleExtensionByZero.{u, 0} Λ (i₁ ≫ i₂) ≅
      etaleModuleExtensionByZero.{u, 0} Λ (b₁ ≫ b₂) ⋙ etaleModuleDirectImage.{u, 0} Λ f₃)
    (hpaste : ∀ F : EtaleModules.{u, 0} Λ P₁,
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ i₁ i₂).inv.app
          ((etaleModuleDirectImage.{u, 0} Λ f₁).obj F) ≫ μ.hom.app F =
        (etaleModuleExtensionByZero.{u, 0} Λ i₂).map (μ₁.hom.app F) ≫
          μ₂.hom.app ((etaleModuleExtensionByZero.{u, 0} Λ b₁).obj F) ≫
          (etaleModuleDirectImage.{u, 0} Λ f₃).map
            ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ b₁ b₂).inv.app F)) :
    derivedExtensionByZeroSquareMap Λ (b₁ ≫ b₂) (i₁ ≫ i₂) f₁ f₃ μ =
      Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f₁)
          (derivedExtensionByZeroUnboundedCompIso Λ i₁ i₂).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedExtensionByZeroSquareMap Λ b₁ i₁ f₁ f₂ μ₁)
          (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ i₂) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ b₁)
          (derivedExtensionByZeroSquareMap Λ b₂ i₂ f₂ f₃ μ₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedExtensionByZeroUnboundedCompIso Λ b₁ b₂).hom
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f₃) := by
  refine Stacks.DerivedBaseChange.squareMap_horizontal_paste
    (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P₁) (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P₂) (ComplexShape.up ℤ)) _ _ _ _ _ _ _ _ _
    (Functor.mapHomologicalComplexCompIso (etaleModuleExtensionByZeroCompIso.{u, 0} Λ b₁ b₂).symm
      (ComplexShape.up ℤ))
    (Functor.mapHomologicalComplexCompIso (etaleModuleExtensionByZeroCompIso.{u, 0} Λ i₁ i₂).symm
      (ComplexShape.up ℤ)) _ _
    (derivedExtensionByZeroUnboundedCompIso_hom_app_Q Λ b₁ b₂)
    (derivedExtensionByZeroUnboundedCompIso_hom_app_Q Λ i₁ i₂) _ _ _ fun K => ?_
  ext n : 1
  simpa [etaleModuleSquareComplexIso] using hpaste (K.X n)

end Derived

end Stacks.EtaleCohomology

end
