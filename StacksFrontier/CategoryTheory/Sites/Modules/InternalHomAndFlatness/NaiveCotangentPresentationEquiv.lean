module

public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentHomotopy

/-!
# Presentations factoring through each other have homotopy equivalent naive cotangent complexes

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a site and let
`α₁ : E₁ ⟶ B` and `α₂ : E₂ ⟶ B` be two families of generators presenting `B` as a quotient of
the free `A`-algebras `A[E₁]` and `A[E₂]`.  Suppose the two presentations factor through each
other, that is there are morphisms `h : E₁ ⟶ E₂` with `h ≫ α₂ = α₁` and `k : E₂ ⟶ E₁` with
`k ≫ α₁ = α₂`.  Then the chain map `NL(α₁) ⟶ NL(α₂)` induced by `h` is a homotopy equivalence,
hence a quasi-isomorphism.

The two composites `h ≫ k` and `k ≫ h` need not be identities; what replaces that is the
homotopy invariance of the construction, which says that any two morphisms of presentations with
the same source and target induce homotopic chain maps.  So `NL(h) ≫ NL(k) = NL(h ≫ k)` is
homotopic to `NL(𝟙 E₁) = 𝟙`, and symmetrically.

## Main definitions

* `Stacks.SheafOfModules.presentationNaiveCotangentComplexHomotopyEquiv` is the homotopy
  equivalence `NL(α₁) ≃ NL(α₂)` attached to a pair of mutual factorisations.

## Main results

* `Stacks.SheafOfModules.quasiIso_presentationNaiveCotangentComplexMap_of_fac`: the chain map
  induced by `h` is a quasi-isomorphism as soon as a morphism of presentations exists back.

## Implementation notes

Over a general site two presentations need not factor through each other: a factorisation
`E₂ ⟶ E₁` over `B` amounts to lifting the family `α₂` through the locally surjective morphism
`A[E₁] ⟶ B`, and such lifts exist only locally.  The hypothesis of this file is therefore not
automatic, unlike the commutative-algebra statement it renders, where the presenting morphism is
surjective on the nose.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), whose part (2) is the
  homotopy invariance used here and whose part (3) is the commutative-algebra form of this
  statement.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of the
  naive cotangent complex from the presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.SheafOfModules


open Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
variable (A : Sheaf J CommRingCat.{w}) (E₁ E₂ : Functor Cᵒᵖ (Type w))
  (h : E₁ ⟶ E₂) (k : E₂ ⟶ E₁)
  (B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  (α₁ : E₁ ⟶ underlyingPresheaf J B) (α₂ : E₂ ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]
  (hα : h ≫ α₂ = α₁) (hβ : k ≫ α₁ = α₂)

/-- A pair of mutual factorisations of two presentations of `B` over `A` gives a homotopy
equivalence `NL(α₁) ≃ NL(α₂)`, with the chain maps induced by `h` and by `k` as its two
directions.  The two composites are homotopic to the identities because they are induced by
morphisms of presentations `E₁ ⟶ E₁` and `E₂ ⟶ E₂`, as are the identities of `E₁` and `E₂`. -/
noncomputable def presentationNaiveCotangentComplexHomotopyEquiv :
    HomotopyEquiv (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₁ α₁)
      (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₂ α₂) where
  hom := presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα
  inv := presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₂ E₁ k B a α₂ α₁ hβ
  homotopyHomInvId :=
    (Homotopy.ofEq (presentationNaiveCotangentComplexMap_comp.{v, u, w, z}
        J A B a E₁ E₂ E₁ h k α₁ α₂ α₁ hα hβ)).trans
      ((presentationNaiveCotangentComplexHomotopy.{v, u, w, z} J A E₁ E₁ (h ≫ k) (𝟙 E₁) B a
          α₁ α₁ (by rw [Category.assoc, hβ, hα]) (Category.id_comp α₁)).trans
        (Homotopy.ofEq (presentationNaiveCotangentComplexMap_id.{v, u, w, z} J A B a E₁ α₁)))
  homotopyInvHomId :=
    (Homotopy.ofEq (presentationNaiveCotangentComplexMap_comp.{v, u, w, z}
        J A B a E₂ E₁ E₂ k h α₂ α₁ α₂ hβ hα)).trans
      ((presentationNaiveCotangentComplexHomotopy.{v, u, w, z} J A E₂ E₂ (k ≫ h) (𝟙 E₂) B a
          α₂ α₂ (by rw [Category.assoc, hα, hβ]) (Category.id_comp α₂)).trans
        (Homotopy.ofEq (presentationNaiveCotangentComplexMap_id.{v, u, w, z} J A B a E₂ α₂)))

include k hβ in
/-- The chain map `NL(α₁) ⟶ NL(α₂)` induced by a morphism of presentations `h : E₁ ⟶ E₂` is a
quasi-isomorphism as soon as a morphism of presentations `k : E₂ ⟶ E₁` exists in the other
direction: it is then the forward direction of a homotopy equivalence. -/
theorem quasiIso_presentationNaiveCotangentComplexMap_of_fac
    [HasSheafify J AddCommGrpCat.{max w u v z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}] :
    QuasiIso (presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα) :=
  (presentationNaiveCotangentComplexHomotopyEquiv.{v, u, w, z}
    J A E₁ E₂ h k B a α₁ α₂ hα hβ).quasiIso_hom

end Stacks.SheafOfModules

end
