module

public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheafLocalIso
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent

/-!
# Locally surjective maps of generators

Let `A` be a sheaf of commutative rings on a site and `e : E₁ ⟶ E₂` a morphism of presheaves of
sets. If `e` is locally surjective, so is the induced morphism `A[E₁] ⟶ A[E₂]` of free algebra
sheaves: locally every section of `A[E₂]` is a polynomial in finitely many variables, and each
variable is locally the image of a variable of `A[E₁]`. Consequently, if `α : E₂ ⟶ B` presents
a sheaf of rings `B` over `A`, so does `e ≫ α`: refining a presentation along a locally
surjective map of generators keeps it a presentation.

## Main results

* `Stacks.Sites.FreeAlgebra.isLocallySurjective_freeAlgebraSheafMap`: a locally surjective morphism
  `E₁ ⟶ E₂` induces a locally surjective morphism `A[E₁] ⟶ A[E₂]`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafMap_comp_presentation`: the morphism `A[E₁] ⟶ B`
  attached to `e ≫ α` is the composite of `A[E₁] ⟶ A[E₂]` with the morphism attached to `α`.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w

namespace Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] (A : Sheaf J CommRingCat.{w})
  {E₁ E₂ : Functor Cᵒᵖ (Type w)}

section ImageSieve

variable {F G : Cᵒᵖ ⥤ CommRingCat.{w}} (f : F ⟶ G)

/-- For a morphism `f : F ⟶ G` of presheaves of commutative rings, the intersection of the image
sieves of `x` and `y` is contained in the image sieve of `x + y`. -/
theorem imageSieve_add_le {U : C} (x y : G.obj (op U)) :
    Presheaf.imageSieve f x ⊓ Presheaf.imageSieve f y ≤ Presheaf.imageSieve f (x + y) := by
  rintro V g ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

/-- For a morphism `f : F ⟶ G` of presheaves of commutative rings, the intersection of the image
sieves of `x` and `y` is contained in the image sieve of `x * y`. -/
theorem imageSieve_mul_le {U : C} (x y : G.obj (op U)) :
    Presheaf.imageSieve f x ⊓ Presheaf.imageSieve f y ≤ Presheaf.imageSieve f (x * y) := by
  rintro V g ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a * b, by rw [map_mul, map_mul, ha, hb]⟩

omit [HasWeakSheafify J CommRingCat] in
/-- If `S` is a covering sieve of `U` such that for every `g : V ⟶ U` in `S` the image sieve of
the restriction of `x` to `V` covers `V`, then the image sieve of `x` covers `U`. -/
theorem imageSieve_mem_of_locally {U : C} (x : G.obj (op U)) {S : Sieve U} (hS : S ∈ J U)
    (h : ∀ ⦃V : C⦄ (g : V ⟶ U), S g → Presheaf.imageSieve f (G.map g.op x) ∈ J V) :
    Presheaf.imageSieve f x ∈ J U := by
  refine J.transitive hS _ fun V g hg => J.superset_covering ?_ (h g hg)
  rintro W k ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [ha, op_comp, Functor.map_comp]
  rfl

end ImageSieve

variable [J.WEqualsLocallyBijective CommRingCat.{w}]

/-- If `e : E₁ ⟶ E₂` is locally surjective, then so is the induced morphism
`freeAlgebraSheafMap J A e` of free algebra sheaves. -/
theorem isLocallySurjective_freeAlgebraSheafMap (e : E₁ ⟶ E₂)
    [he : Presheaf.IsLocallySurjective J e] :
    Presheaf.IsLocallySurjective J (freeAlgebraSheafMap J A e).hom := by
  let f := (freeAlgebraSheafMap J A e).hom
  let η := (toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E₂)
  have hη : Presheaf.IsLocallySurjective J η := (J.W_toSheafify _).isLocallySurjective
  have hpoly : ∀ (U : C) (p : MvPolynomial (E₂.obj (op U)) (A.obj.obj (op U))),
      Presheaf.imageSieve f (η.app (op U) p) ∈ J U := by
    intro U p
    induction p using MvPolynomial.induction_on with
    | C r =>
      have : η.app (op U) (MvPolynomial.C r) =
          f.app (op U) ((freeAlgebraSheafCoefficientMap J A E₁).hom.app (op U) r) := by
        rw [← freeAlgebraSheafCoefficientMap_app]
        exact (congrArg (fun t : A ⟶ freeAlgebraSheaf J A E₂ => t.hom.app (op U) r)
          (freeAlgebraSheafCoefficientMap_comp_map J A e)).symm
      rw [this, Presheaf.imageSieve_app]
      exact J.top_mem U
    | add p q hp hq =>
      have hadd : (η.app (op U)).hom (p + q) = (η.app (op U)).hom p + (η.app (op U)).hom q :=
        map_add (η.app (op U)).hom p q
      rw [hadd]
      exact J.superset_covering (imageSieve_add_le f _ _) (J.intersection_covering hp hq)
    | mul_X p t hp =>
      have hmul : (ConcreteCategory.hom (η.app (op U))) (p * MvPolynomial.X t) =
          (ConcreteCategory.hom (η.app (op U))) p *
            (ConcreteCategory.hom (η.app (op U))) (MvPolynomial.X t) :=
        map_mul (η.app (op U)).hom p (MvPolynomial.X t)
      refine (congrArg (fun z => Presheaf.imageSieve f z ∈ J U) hmul).mpr ?_
      refine J.superset_covering (imageSieve_mul_le f _ _) (J.intersection_covering hp ?_)
      refine J.superset_covering ?_ (Presheaf.imageSieve_mem J e t)
      rintro V g ⟨s, hs⟩
      refine ⟨(freeAlgebraSheafVariable J A E₁).app (op V) s, ?_⟩
      refine (congrArg (fun k => k.app (op V) s) (freeAlgebraSheafVariable_comp_map J A e)).trans ?_
      show (freeAlgebraSheafVariable J A E₂).app (op V) (e.app (op V) s) = _
      rw [hs, NatTrans.naturality_apply (freeAlgebraSheafVariable J A E₂) g.op t]
      rfl
  exact ⟨fun {U} x => imageSieve_mem_of_locally J f x (Presheaf.imageSieve_mem J η x)
    fun V g ⟨p, hp⟩ => (congrArg (fun z => Presheaf.imageSieve f z ∈ J V) hp).mp (hpoly V p)⟩

variable {B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)

omit [J.WEqualsLocallyBijective CommRingCat] in
/-- The morphism of free algebra sheaves induced by `e : E₁ ⟶ E₂`, followed by the morphism to `B`
determined by `a` and `α`, is the morphism to `B` determined by `a` and `e ≫ α`. -/
theorem freeAlgebraSheafMap_comp_presentation (e : E₁ ⟶ E₂)
    (α : E₂ ⟶ underlyingPresheaf J B) :
    freeAlgebraSheafMap J A e ≫ Stacks.SheafOfModules.presentation J A B a E₂ α =
      Stacks.SheafOfModules.presentation J A B a E₁ (e ≫ α) := by
  refine freeAlgebraSheaf_hom_ext J A B E₁ ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_map,
      freeAlgebraSheafCoefficientMap_comp_desc, freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_map, Category.assoc, freeAlgebraSheafVariable_comp_desc,
      freeAlgebraSheafVariable_comp_desc]

end Stacks.Sites.FreeAlgebra

end
