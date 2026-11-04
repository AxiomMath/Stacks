module

public import StacksFrontier.Cotangent.SurjectionSiteAugmentationFiltration

/-!
# The graded pieces `𝒦ⁿ/𝒦ⁿ⁺¹` of the augmentation filtration

Continuing `StacksFrontier.Cotangent.SurjectionSiteAugmentationFiltration`, this file forms the
graded pieces of the filtration `… ⊆ 𝒦² ⊆ 𝒦 ⊆ Ō` of the presheaf `Ō = 𝒪 ⊗_A B̲` on the small
model of the polynomial site `C_{B/A}`, as presheaves of `B`-modules, together with the short
exact sequence

`0 → 𝒦ⁿ⁺¹ → 𝒦ⁿ → 𝒦ⁿ/𝒦ⁿ⁺¹ → 0`

of presheaves. For a surjective `A → B` the graded piece `𝒦ⁿ/𝒦ⁿ⁺¹` is the `n`-th symmetric
power of `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲`, which is the identification the `E₁`-page of Quillen's spectral
sequence rests on; that identification is not made here.

## Main definitions

* `Stacks.quotSubmoduleFunctor`: the quotient of a subdiagram of a diagram of modules by a
  smaller subdiagram.
* `CommAlgCat.smallPolynomialAugmentationGraded`: the presheaf `𝒦ⁿ/𝒦ⁿ⁺¹`.
* `CommAlgCat.smallPolynomialAugmentationGradedπ`: the projection `𝒦ⁿ → 𝒦ⁿ/𝒦ⁿ⁺¹`.

## Main results

* `CommAlgCat.surjective_smallPolynomialAugmentationGradedπ` and
  `CommAlgCat.ker_smallPolynomialAugmentationGradedπ`: over each object the projection
  `𝒦ⁿ → 𝒦ⁿ/𝒦ⁿ⁺¹` is surjective with kernel `𝒦ⁿ⁺¹`.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks

section Quot

variable {D : Type*} [Category D] {R : Type u} [Ring R]

/-- The quotient of a subdiagram of a diagram of modules by a smaller subdiagram. -/
def quotSubmoduleFunctor (F : D ⥤ ModuleCat.{u} R) (S T : ∀ X : D, Submodule R ↥(F.obj X))
    (hS : ∀ {X Y : D} (f : X ⟶ Y) (x : ↥(F.obj X)), x ∈ S X → (F.map f).hom x ∈ S Y)
    (hT : ∀ {X Y : D} (f : X ⟶ Y) (x : ↥(F.obj X)), x ∈ T X → (F.map f).hom x ∈ T Y)
    (_hle : ∀ X : D, T X ≤ S X) :
    D ⥤ ModuleCat.{u} R where
  obj X := ModuleCat.of R (↥(S X) ⧸ Submodule.comap (S X).subtype (T X))
  map f := ModuleCat.ofHom (Submodule.mapQ _ _ ((F.map f).hom.restrict (fun x hx => hS f x hx))
    (fun x hx => hT f (x : ↥(F.obj _)) hx))
  map_id X := ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    change Submodule.Quotient.mk ((F.map (𝟙 X)).hom.restrict _ x) = Submodule.Quotient.mk x
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    change (F.map (𝟙 X)).hom (x : ↥(F.obj X)) = (x : ↥(F.obj X))
    rw [F.map_id]
    rfl))
  map_comp := fun {X _ _} f g => ModuleCat.hom_ext (Submodule.linearMap_qext _
    (LinearMap.ext fun x => by
      change Submodule.Quotient.mk ((F.map (f ≫ g)).hom.restrict _ x) =
        Submodule.Quotient.mk (((F.map g).hom.restrict _) (((F.map f).hom.restrict _) x))
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      change (F.map (f ≫ g)).hom (x : ↥(F.obj X)) = _
      rw [F.map_comp]
      rfl))

/-- The projection of a subdiagram onto its quotient by a smaller subdiagram. -/
def quotSubmoduleFunctorπ (F : D ⥤ ModuleCat.{u} R) (S T : ∀ X : D, Submodule R ↥(F.obj X))
    (hS : ∀ {X Y : D} (f : X ⟶ Y) (x : ↥(F.obj X)), x ∈ S X → (F.map f).hom x ∈ S Y)
    (hT : ∀ {X Y : D} (f : X ⟶ Y) (x : ↥(F.obj X)), x ∈ T X → (F.map f).hom x ∈ T Y)
    (hle : ∀ X : D, T X ≤ S X) :
    submoduleFunctor F S hS ⟶ quotSubmoduleFunctor F S T hS hT hle where
  app X := ModuleCat.ofHom (Submodule.comap (S X).subtype (T X)).mkQ
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- Each component of `quotSubmoduleFunctorπ` is surjective. -/
lemma surjective_quotSubmoduleFunctorπ (F : D ⥤ ModuleCat.{u} R)
    (S T : ∀ X : D, Submodule R ↥(F.obj X))
    (hS : ∀ {X Y : D} (f : X ⟶ Y) (x : ↥(F.obj X)), x ∈ S X → (F.map f).hom x ∈ S Y)
    (hT : ∀ {X Y : D} (f : X ⟶ Y) (x : ↥(F.obj X)), x ∈ T X → (F.map f).hom x ∈ T Y)
    (hle : ∀ X : D, T X ≤ S X) (X : D) :
    Function.Surjective ((quotSubmoduleFunctorπ F S T hS hT hle).app X).hom :=
  Submodule.mkQ_surjective _

/-- The kernel of the component of `quotSubmoduleFunctorπ` at `X` is `T X`, viewed as a
submodule of `S X`. -/
lemma ker_quotSubmoduleFunctorπ (F : D ⥤ ModuleCat.{u} R)
    (S T : ∀ X : D, Submodule R ↥(F.obj X))
    (hS : ∀ {X Y : D} (f : X ⟶ Y) (x : ↥(F.obj X)), x ∈ S X → (F.map f).hom x ∈ S Y)
    (hT : ∀ {X Y : D} (f : X ⟶ Y) (x : ↥(F.obj X)), x ∈ T X → (F.map f).hom x ∈ T Y)
    (hle : ∀ X : D, T X ≤ S X) (X : D) :
    LinearMap.ker ((quotSubmoduleFunctorπ F S T hS hT hle).app X).hom =
      Submodule.comap (S X).subtype (T X) :=
  Submodule.ker_mkQ _

end Quot

end Stacks

namespace CommAlgCat

section Graded

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-- **The graded piece `𝒦ⁿ/𝒦ⁿ⁺¹`** of the augmentation filtration of `Ō`, as a presheaf of
`B`-modules on the small model of the polynomial site. -/
def smallPolynomialAugmentationGraded (n : ℕ) :
    (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u) :=
  Stacks.quotSubmoduleFunctor (smallPolynomialQuotientModule A B κ)
    (smallPolynomialAugmentationIdealPowSubmodule A B κ n)
    (smallPolynomialAugmentationIdealPowSubmodule A B κ (n + 1))
    (fun f x hx => smallPolynomialAugmentationIdealPow_map_mem A B κ n f x hx)
    (fun f x hx => smallPolynomialAugmentationIdealPow_map_mem A B κ (n + 1) f x hx)
    (smallPolynomialAugmentationIdealPowSubmodule_antitone A B κ (Nat.le_succ n))

/-- The projection `𝒦ⁿ → 𝒦ⁿ/𝒦ⁿ⁺¹`. -/
def smallPolynomialAugmentationGradedπ (n : ℕ) :
    smallPolynomialAugmentationIdealPow A B κ n ⟶ smallPolynomialAugmentationGraded A B κ n :=
  Stacks.quotSubmoduleFunctorπ (smallPolynomialQuotientModule A B κ)
    (smallPolynomialAugmentationIdealPowSubmodule A B κ n)
    (smallPolynomialAugmentationIdealPowSubmodule A B κ (n + 1))
    (fun f x hx => smallPolynomialAugmentationIdealPow_map_mem A B κ n f x hx)
    (fun f x hx => smallPolynomialAugmentationIdealPow_map_mem A B κ (n + 1) f x hx)
    (smallPolynomialAugmentationIdealPowSubmodule_antitone A B κ (Nat.le_succ n))

/-- The projection onto a graded piece is surjective in each degree. -/
lemma surjective_smallPolynomialAugmentationGradedπ (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Function.Surjective ((smallPolynomialAugmentationGradedπ A B κ n).app X).hom :=
  Stacks.surjective_quotSubmoduleFunctorπ _ _ _ _
    (smallPolynomialAugmentationIdealPow_map_mem A B κ (n + 1)) _ X

/-- The kernel of the projection onto a graded piece is the next step of the filtration. -/
lemma ker_smallPolynomialAugmentationGradedπ (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    LinearMap.ker ((smallPolynomialAugmentationGradedπ A B κ n).app X).hom =
      Submodule.comap (smallPolynomialAugmentationIdealPowSubmodule A B κ n X).subtype
        (smallPolynomialAugmentationIdealPowSubmodule A B κ (n + 1) X) :=
  Stacks.ker_quotSubmoduleFunctorπ _ _ _ _
    (smallPolynomialAugmentationIdealPow_map_mem A B κ (n + 1)) _ X

end Graded

end CommAlgCat

end
