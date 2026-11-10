module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement

/-!
# The Čech complex of a one-member covering depends only on the covering object

Two one-member coverings `{X → U}` and `{Y → U}` of the same object whose covering objects are
isomorphic *over* `U` have the same Čech complex, hence the same Čech cohomology.  This file
proves that, and is what lets a vanishing statement proved for one presentation of a covering
object be read at another.

## Main definitions

* `Stacks.CechSite.singletonHomOver`: an isomorphism of the covering objects, read as a
  morphism of families over the identity of the common target.
* `Stacks.CechSite.singletonProductIso`: the induced isomorphism of the iterated fibre
  products.

## Main results

* `Stacks.CechSite.isIso_cechComplexMap_singleton`: the induced map of Čech complexes is an
  isomorphism.
* `Stacks.CechSite.isZero_cechCohomology_singleton_of_iso`: **the transport of vanishing.**

## Implementation notes

The proof is degreewise, exactly as in
`Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts`.  Going through that statement
instead is not possible: it asks for `CategoryTheory.FinitaryExtensive` on the ambient category,
which for a slice category is only a `private` instance of
`StacksFrontier/AlgebraicGeometry/Topologies/StandardCoveringDisjointUnion.lean`.  Nothing here
needs it: both index types are `PUnit`, so the degree-`n` component of the comparison is, up to
the two `CategoryTheory.Limits.productUniqueIso`s, the restriction map along
`Stacks.CechSite.cechProductMap`, and that map is `CategoryTheory.Limits.Pi.map` of an
isomorphism.

`CategoryTheory.PreZeroHypercover.singleton` is made `implicit_reducible`, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/CoproductRefinement.lean`: the morphism
`ε.hom` of the given isomorphism has type `Over.mk h₁ ⟶ Over.mk h₂`, and the families the
iterated fibre products are indexed by are `Over.mk ((singleton h₁).f (i a))`, so the two are
type-correct together only once the one-member family is unfolded.  That unfolding turns the
indexed families into constant ones, which is why the ambient hypothesis is
`CategoryTheory.Limits.HasFiniteWidePullbacks` on the ambient category rather than the
per-family `HasProduct` instances the Čech complex is stated with: those would no longer match
the unfolded goals.

## References

* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

universe w v v' u u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] cechFormalCoproduct cechFormalCoproductMap
  CategoryTheory.PreZeroHypercover.singleton

variable {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C] {U X Y : C}
  (h₁ : X ⟶ U) (h₂ : Y ⟶ U)

/-- An isomorphism over `U` between the covering objects of two one-member coverings of `U`,
read as a morphism of families over `𝟙 U`. -/
noncomputable def singletonHomOver (ε : Over.mk h₁ ≅ Over.mk h₂) :
    (PreZeroHypercover.singleton.{w} h₁).HomOver
      (PreZeroHypercover.singleton.{w} h₂) (𝟙 U) where
  s₀ _ := PUnit.unit
  h₀ _ := ε.hom.left
  w₀ _ := (Over.w ε.hom).trans (Category.comp_id h₁).symm

/-- The product of `n + 1` copies of an isomorphism of the covering objects, as an isomorphism
of the iterated fibre products of the two one-member coverings. -/
noncomputable def singletonProductIso (ε : Over.mk h₁ ≅ Over.mk h₂) (n : ℕ)
    (i : Fin (n + 1) → (PreZeroHypercover.singleton.{w} h₁).I₀) :
    (∏ᶜ (fun a ↦ Over.mk ((PreZeroHypercover.singleton.{w} h₁).f (i a)))) ≅
      ∏ᶜ (fun a ↦ Over.mk ((PreZeroHypercover.singleton.{w} h₂).f
        ((singletonHomOver.{w} h₁ h₂ ε).s₀ (i a)))) :=
  Pi.mapIso (fun _ ↦ ε)

/-- Along `Stacks.CechSite.singletonHomOver`, the map of iterated fibre products is the product
of copies of the given isomorphism. -/
theorem cechProductMap_singletonHomOver (ε : Over.mk h₁ ≅ Over.mk h₂) (n : ℕ)
    (i : Fin (n + 1) → (PreZeroHypercover.singleton.{w} h₁).I₀) :
    cechProductMap (PreZeroHypercover.singleton.{w} h₁)
        (PreZeroHypercover.singleton.{w} h₂) (singletonHomOver.{w} h₁ h₂ ε) n i =
      (singletonProductIso.{w} h₁ h₂ ε n i).hom.left := by
  let Q := ∏ᶜ (fun a ↦ Over.mk ((PreZeroHypercover.singleton.{w} h₁).f (i a)))
  let e : Over.mk (Q.hom ≫ 𝟙 U) ≅ Q := Over.isoMk (Iso.refl Q.left)
  let m : Over.mk (Q.hom ≫ 𝟙 U) ⟶
      ∏ᶜ (fun a ↦ Over.mk ((PreZeroHypercover.singleton.{w} h₂).f
        ((singletonHomOver.{w} h₁ h₂ ε).s₀ (i a)))) :=
    Pi.lift (fun a ↦ Over.homMk
      ((Pi.π (fun b ↦ Over.mk ((PreZeroHypercover.singleton.{w} h₁).f (i b))) a).left ≫
        ε.hom.left)
      ((Category.assoc _ _ _).trans
        ((congrArg
            ((Pi.π (fun b ↦ Over.mk
              ((PreZeroHypercover.singleton.{w} h₁).f (i b))) a).left ≫ ·)
            (Over.w ε.hom)).trans
          ((Over.w (Pi.π (fun b ↦ Over.mk
              ((PreZeroHypercover.singleton.{w} h₁).f (i b))) a)).trans
            (Category.comp_id Q.hom).symm))))
  change m.left = _
  have hm : e.inv ≫ m = (singletonProductIso.{w} h₁ h₂ ε n i).hom := by
    apply Pi.hom_ext
    intro a
    dsimp [m, singletonProductIso]
    simp only [Category.assoc]
    apply Over.OverMorphism.ext
    simp [e]
  simpa [Over.comp_left, e] using congrArg (fun f ↦ f.left) hm

/-- The map of iterated fibre products induced by an isomorphism of covering objects is an
isomorphism. -/
theorem isIso_cechProductMap_singletonHomOver (ε : Over.mk h₁ ≅ Over.mk h₂) (n : ℕ)
    (i : Fin (n + 1) → (PreZeroHypercover.singleton.{w} h₁).I₀) :
    IsIso (cechProductMap (PreZeroHypercover.singleton.{w} h₁)
      (PreZeroHypercover.singleton.{w} h₂) (singletonHomOver.{w} h₁ h₂ ε) n i) := by
  rw [cechProductMap_singletonHomOver]
  exact (inferInstance :
    IsIso ((Over.forget U).map (singletonProductIso.{w} h₁ h₂ ε n i).hom))

section Complex

variable {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]

/-- **The Čech complex of a one-member covering depends only on the covering object.**  An
isomorphism over `U` of the two covering objects induces an isomorphism of the Čech complexes
of `{X → U}` and `{Y → U}`. -/
theorem isIso_cechComplexMap_singleton (ε : Over.mk h₁ ≅ Over.mk h₂) (F : Cᵒᵖ ⥤ A) :
    IsIso (cechComplexMap (PreZeroHypercover.singleton.{w} h₁)
      (PreZeroHypercover.singleton.{w} h₂) (singletonHomOver.{w} h₁ h₂ ε) F) := by
  have hdeg : ∀ n, IsIso ((cechComplexMap (PreZeroHypercover.singleton.{w} h₁)
      (PreZeroHypercover.singleton.{w} h₂) (singletonHomOver.{w} h₁ h₂ ε) F).f n) := by
    intro n
    -- A projection of a product indexed by `Fin (n + 1) → _` over a one-member covering is an
    -- isomorphism.  The `Unique` instance is found here, on the unfolded index type, because
    -- instance search does not perform that unfolding on the products the Čech complex uses.
    have huniq : ∀ {Z : C} (h : Z ⟶ U)
        (f : (Fin (n + 1) → (PreZeroHypercover.singleton.{w} h).I₀) → A) (b),
        IsIso (Pi.π f b) := by
      intro Z h f b
      have : Unique (Fin (n + 1) → (PreZeroHypercover.singleton.{w} h).I₀) := inferInstance
      obtain rfl : b = default := Subsingleton.elim _ _
      rw [← productUniqueIso_hom]
      infer_instance
    refine @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ (huniq h₁ _ _) ?_
      (cechComplexMap_f_Pi_π (PreZeroHypercover.singleton.{w} h₁)
        (PreZeroHypercover.singleton.{w} h₂) (singletonHomOver.{w} h₁ h₂ ε) F n default)
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ (huniq h₂ _ _) ?_
    have := isIso_cechProductMap_singletonHomOver.{w} h₁ h₂ ε n default
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end Complex

section Cohomology

variable {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]

/-- **The transport of Čech vanishing along an isomorphism of the covering object of a
one-member covering.** -/
theorem isZero_cechCohomology_singleton_of_iso (ε : Over.mk h₁ ≅ Over.mk h₂) (F : Cᵒᵖ ⥤ A)
    (p : ℕ) (h : IsZero (cechCohomology (PreZeroHypercover.singleton.{w} h₂) F p)) :
    IsZero (cechCohomology (PreZeroHypercover.singleton.{w} h₁) F p) :=
  have := isIso_cechComplexMap_singleton.{w} h₁ h₂ ε F
  h.of_iso ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    (asIso (cechComplexMap (PreZeroHypercover.singleton.{w} h₁)
      (PreZeroHypercover.singleton.{w} h₂) (singletonHomOver.{w} h₁ h₂ ε) F))).symm

end Cohomology

end Stacks.CechSite

end
