module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestrictionSmallerOpen
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonBilinear
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonReading

/-!
# Compatibility of the tensor comparison of [Stacks, Tag 0EX3] (b) with shrinking the open

By the sheafification adjunction of [Stacks, Tag 01CB], the canonical map of conclusion (b) of
[Stacks, Tag 0EX3] is a bilinear family on sections. This file shows that this family is
compatible with shrinking the open: for `W ≤ V` the comparison built over `V`, restricted to `W`,
is the comparison built over `W`.

## Main results

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `conj_eq_of_cocycle_of_naturality`: in an arbitrary category, a morphism conjugated across two
  cocycle squares related by a naturality square and a compatibility of local morphisms.
* `conjugateRestrict_restrictLEIso`: **the degree-`n` right derived pushforward along `f ∣_ V`,
  conjugated by the restriction comparison of [Stacks, Tag 01E5], is compatible with shrinking
  the open**, for an arbitrary module downstairs and an arbitrary pair of compatible local
  morphisms.
* `unit_app_presheaf_map`: the unit of `f^* ⊣ f_*` commutes with restriction of sections.
* `higherDirectImageTensorSection_restrictLEIso`: **the bilinear family is compatible with
  shrinking the open**, as an identity of morphisms of sheaves.
* `higherDirectImageTensorSection_restrictHomOfLE`: the same compatibility, with the restriction
  of a morphism spelled sectionwise.
* `tensorTopSection_presheaf_map`: the same read on sections, which is the naturality of the
  bilinear family.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open SchemeHigherDirectImage (rightDerivedPlusRestrictObjIso)
open SchemeRestrictionSmallerOpen (preimage_mono rightDerivedPlusRestrictionOfLEObjIso
  rightDerivedPlusRestrictObjIso_ofLE_eq rightDerivedPlusRestrictionOfLEObjIso_hom_naturality)

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] moduleOfPresheafRing

/-! ### The category-theoretic skeleton -/

/-- **Conjugating a morphism across two cocycle squares.**  Given isomorphisms satisfying the
cocycle identities `h₁` and `h₂`, a morphism `w` intertwined with `v` by `σ₁`, `σ₂` (`h₃`) and
carried to `z` by `m₁`, `m₂` (`h₄`), the conjugate of `v` by `u₁`, `u₂` and `l₁`, `l₂` is the
conjugate of `z` by `q₁`, `q₂`. -/
theorem conj_eq_of_cocycle_of_naturality {C : Type*} [Category C]
    {P₁ P₂ Q₁ Q₂ Z₁ Z₂ A₁ A₂ B₁ B₂ : C}
    (σ₁ : P₁ ≅ Q₁) (σ₂ : P₂ ≅ Q₂) (u₁ : Q₁ ≅ Z₁) (u₂ : Q₂ ≅ Z₂)
    (l₁ : Z₁ ≅ A₁) (l₂ : Z₂ ≅ A₂) (m₁ : P₁ ≅ B₁) (m₂ : P₂ ≅ B₂)
    (q₁ : B₁ ≅ A₁) (q₂ : B₂ ≅ A₂) {v : Q₁ ⟶ Q₂} {w : P₁ ⟶ P₂} {z : B₁ ⟶ B₂}
    (h₁ : u₁.hom ≫ l₁.hom = σ₁.inv ≫ m₁.hom ≫ q₁.hom)
    (h₂ : u₂.hom ≫ l₂.hom = σ₂.inv ≫ m₂.hom ≫ q₂.hom)
    (h₃ : w ≫ σ₂.hom = σ₁.hom ≫ v)
    (h₄ : m₁.inv ≫ w ≫ m₂.hom = z) :
    l₁.inv ≫ (u₁.inv ≫ v ≫ u₂.hom) ≫ l₂.hom = q₁.inv ≫ z ≫ q₂.hom := by
  have e₁ : σ₁.inv ≫ m₁.hom = u₁.hom ≫ l₁.hom ≫ q₁.inv := by
    rw [← Category.assoc, h₁]
    simp
  have e₂ : σ₂.hom ≫ u₂.hom ≫ l₂.hom = m₂.hom ≫ q₂.hom := by
    rw [h₂]
    simp
  have e₃ : σ₁.inv ≫ w ≫ σ₂.hom = v := by
    rw [h₃]
    simp
  have e₄ : w ≫ m₂.hom = m₁.hom ≫ z := by
    rw [← h₄]
    simp
  have key : v ≫ u₂.hom ≫ l₂.hom = u₁.hom ≫ l₁.hom ≫ q₁.inv ≫ z ≫ q₂.hom := by
    rw [← e₃]
    simp only [Category.assoc]
    rw [e₂, ← Category.assoc w, e₄]
    simp only [Category.assoc]
    rw [reassoc_of% e₁]
  simp only [Category.assoc]
  rw [key]
  simp

/-! ### The conjugated derived pushforward is compatible with shrinking the open -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (n : ℕ) {W V : Y.Opens} (h : W ≤ V)

/-- **The degree-`n` right derived pushforward along `f ∣_ V`, conjugated by the restriction
comparison of [Stacks, Tag 01E5], is compatible with shrinking the open.**  For modules `F`, `H`
on `X` and morphisms `τ` over `f⁻¹(V)` and `τ'` over `f⁻¹(W)` such that `τ` restricts to `τ'`,
the conjugated derived pushforward of `τ`, restricted to `W`, is that of `τ'`. -/
theorem conjugateRestrict_restrictLEIso (H : X.Modules)
    (τ : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F ⟶
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj H)
    (τ' : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι).obj F ⟶
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι).obj H)
    (hτ : (ModuleLimits.restrictLEIso (preimage_mono f h)).inv.app F ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h))).map τ ≫
          (ModuleLimits.restrictLEIso (preimage_mono f h)).hom.app H = τ') :
    (ModuleLimits.restrictLEIso h).inv.app
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F) ≫
        (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map
            ((rightDerivedPlusRestrictObjIso f V n F).inv ≫
              ((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (n : ℤ)).map τ ≫
                (rightDerivedPlusRestrictObjIso f V n H).hom) ≫
          (ModuleLimits.restrictLEIso h).hom.app
            (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj H) =
      (rightDerivedPlusRestrictObjIso f W n F).inv ≫
        ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (n : ℤ)).map τ' ≫
          (rightDerivedPlusRestrictObjIso f W n H).hom := by
  have hcoc : ∀ M : X.Modules,
      (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map
            (rightDerivedPlusRestrictObjIso f V n M).hom ≫
          (ModuleLimits.restrictLEIso h).hom.app
            (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj M) =
        (rightDerivedPlusRestrictionOfLEObjIso f h n
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)).inv ≫
          ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (n : ℤ)).map
              ((ModuleLimits.restrictLEIso (preimage_mono f h)).hom.app M) ≫
            (rightDerivedPlusRestrictObjIso f W n M).hom := fun M => by
    rw [SchemeRestrictionCocycle.rightDerivedPlusRestrictObjIso_ofLE f h n M,
      rightDerivedPlusRestrictObjIso_ofLE_eq f h n M, Category.assoc]
  have h₄ : ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (n : ℤ)).map
          ((ModuleLimits.restrictLEIso (preimage_mono f h)).inv.app F) ≫
        ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (n : ℤ)).map
            ((Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h))).map τ) ≫
          ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (n : ℤ)).map
            ((ModuleLimits.restrictLEIso (preimage_mono f h)).hom.app H) =
      ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (n : ℤ)).map τ' := by
    rw [← Functor.map_comp, ← Functor.map_comp, hτ]
  rw [Functor.map_comp, Functor.map_comp]
  exact conj_eq_of_cocycle_of_naturality
    (rightDerivedPlusRestrictionOfLEObjIso f h n
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))
    (rightDerivedPlusRestrictionOfLEObjIso f h n
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj H))
    ((Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso
      (rightDerivedPlusRestrictObjIso f V n F))
    ((Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso
      (rightDerivedPlusRestrictObjIso f V n H))
    ((ModuleLimits.restrictLEIso h).app
      (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))
    ((ModuleLimits.restrictLEIso h).app
      (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj H))
    (((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (n : ℤ)).mapIso
      ((ModuleLimits.restrictLEIso (preimage_mono f h)).app F))
    (((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (n : ℤ)).mapIso
      ((ModuleLimits.restrictLEIso (preimage_mono f h)).app H))
    (rightDerivedPlusRestrictObjIso f W n F) (rightDerivedPlusRestrictObjIso f W n H)
    (hcoc F) (hcoc H) (rightDerivedPlusRestrictionOfLEObjIso_hom_naturality f h n τ) h₄

/-! ### The bilinear family is compatible with shrinking the open -/

variable (G : Y.Modules)

/-- **The unit of `f^* ⊣ f_*` commutes with restriction of sections.**  The pullback of the
restriction of a section of `G` to `W` is the restriction to `f⁻¹(W)` of its pullback. -/
theorem unit_app_presheaf_map (s : Γ(G, V)) :
    ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE (preimage_mono f h)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app W
        (G.presheaf.map (homOfLE h).op s) :=
  ModuleLimits.Hom_app_presheaf_map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) h s

/-- **The bilinear family of conclusion (b) of [Stacks, Tag 0EX3] is compatible with shrinking the
open.**  The comparison built over `V`, conjugated by the transitivity isomorphism of restriction
along `W ≤ V`, is the comparison built over `W` for the restricted section. -/
theorem higherDirectImageTensorSection_restrictLEIso (s : Γ(G, V)) :
    (ModuleLimits.restrictLEIso h).inv.app
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F) ≫
        (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map
            (higherDirectImageTensorSection f F G n V s) ≫
          (ModuleLimits.restrictLEIso h).hom.app
            (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
              ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
                  ((Scheme.Modules.pullback f).obj G)))) =
      higherDirectImageTensorSection f F G n W (G.presheaf.map (homOfLE h).op s) := by
  rw [higherDirectImageTensorSection_eq f F G n V s,
    higherDirectImageTensorSection_eq f F G n W (G.presheaf.map (homOfLE h).op s)]
  refine conjugateRestrict_restrictLEIso f F n h
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
        ((Scheme.Modules.pullback f).obj G))) _ _ ?_
  refine Eq.trans (tensorLocalSection_restrictLEIso F ((Scheme.Modules.pullback f).obj G)
    (preimage_mono f h)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s)) ?_
  rw [unit_app_presheaf_map f h G s]

/-- **The restriction to `W ≤ V` of the comparison built over `V` is the comparison built over
`W`**, in the sectionwise spelling
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE` of the restriction of a morphism. -/
theorem higherDirectImageTensorSection_restrictHomOfLE (s : Γ(G, V)) :
    ModuleLimits.restrictHomOfLE h (higherDirectImageTensorSection f F G n V s) =
      higherDirectImageTensorSection f F G n W (G.presheaf.map (homOfLE h).op s) := by
  rw [ModuleLimits.restrictHomOfLE_eq h (higherDirectImageTensorSection f F G n V s),
    higherDirectImageTensorSection_restrictLEIso f F n h G s]

/-- **The naturality of the bilinear family of conclusion (b) of [Stacks, Tag 0EX3]**: the
candidate value on sections over `V`, restricted to `W`, is the candidate value on sections over
`W` of the two restricted sections. -/
theorem tensorTopSection_presheaf_map (s : Γ(G, V))
    (a : Γ(topDirectImage f F n, V)) :
    (topDirectImageTensor f F G n).presheaf.map (homOfLE h).op
        (tensorTopSection f F G n V s a) =
      tensorTopSection f F G n W (G.presheaf.map (homOfLE h).op s)
        ((topDirectImage f F n).presheaf.map (homOfLE h).op a) := by
  rw [tensorTopSection, tensorTopSection,
    topReading_presheaf_map h (higherDirectImageTensorSection f F G n V s) a,
    higherDirectImageTensorSection_restrictHomOfLE f F n h G s]

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
