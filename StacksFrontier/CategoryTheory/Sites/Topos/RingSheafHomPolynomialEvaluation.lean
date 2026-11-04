module

public import StacksFrontier.CategoryTheory.Sites.Topos.PolynomialSystemSections

/-!
# A morphism of sheaves of commutative rings carries polynomial evaluation to polynomial evaluation

Let `α : 𝒪 ⟶ 𝒪'` be a morphism of sheaves of commutative rings on a site. On the underlying
sheaves of sets, `α` is a morphism of the internal commutative ring objects, so postcomposition
with it is a ring homomorphism `(Z ⟶ 𝒪) →+* (Z ⟶ 𝒪')` on generalized elements of every shape
`Z` (`Stacks.Sheaves.PolynomialSystem.postcompRingHom`). Polynomial evaluation is built from
those ring operations and nothing else, so it is carried along: the value of a polynomial `Q` at
coordinates `x i : Z ⟶ 𝒪` is sent to the value of the *same* `Q` at the coordinates `x i ≫ α`,
its coefficients read into the global sections of `𝒪'` through `α`.

This is the companion, for a morphism of ring objects, of
`CategoryTheory.CommRingObj.map_evalSystemHom`, which is the same statement for a
finite-product-preserving *functor*. The two together are what step (3) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6) needs: the functor
transports the row cutting out `h_V` along `g⁻¹`, and the morphism of ring objects `g^♯` then
moves it from `g⁻¹𝒪_Y` onto `𝒪_X`. Nothing here is about `g^♯` specifically; the composite is
assembled in
`StacksFrontier.CategoryTheory.Sites.Topos.InverseImageStructureSharpRow`.

The ring structure on the generalized elements is Mathlib's `CategoryTheory.CommRingObj.Hom`
`.commRing` for the sectionwise ring object `Stacks.sheafCommRingObj`, whose operations are the
sectionwise ones; every proof below is therefore a computation on sections, via
`CategoryTheory.Sheaf.hom_ext_sections` and the five identifications
`Stacks.Sheaves.PolynomialSystem.sections_map_add` and friends.

## Main definitions

* `Stacks.Sheaves.PolynomialSystem.underlyingMap`: the map of underlying sheaves of sets of a
  morphism of sheaves of commutative rings.
* `Stacks.Sheaves.PolynomialSystem.postcompRingHom`: postcomposition with it, as a ring
  homomorphism on generalized elements.

## Main results

* `Stacks.Sheaves.PolynomialSystem.evalRingHom_comp_underlyingMap`: the value of a polynomial,
  pushed along `α`, is the value of the same polynomial at the pushed coordinates and
  coefficients.
* `Stacks.Sheaves.PolynomialSystem.evalSystemHom_comp_piMap` and
  `Stacks.Sheaves.PolynomialSystem.zeroSystemHom_comp_piMap`: the same for the two legs
  `∏ᵏ 𝒪 ⇉ ∏ᵛ 𝒪` of the equalizer presentation cutting out the solutions of a polynomial system,
  the powers being compared by `CategoryTheory.Limits.Pi.map`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CommRingObj Obj

universe w v u

namespace Stacks.Sheaves.PolynomialSystem

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget CommRingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})]

attribute [local instance] Stacks.sheafCommRingObj

variable {O O' : Sheaf J CommRingCat.{w}}

/-- The map of underlying sheaves of sets of a morphism of sheaves of commutative rings. It is a
morphism of the internal commutative ring objects `Stacks.sheafCommRingObj`, which is the content
of `Stacks.Sheaves.PolynomialSystem.postcompRingHom`. -/
abbrev underlyingMap (α : O ⟶ O') :
    Stacks.underlyingRingSheaf J O ⟶ Stacks.underlyingRingSheaf J O' :=
  (sheafCompose J (forget CommRingCat.{w})).map α

variable {Z : Sheaf J (Type w)}

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.HasSheafCompose (forget RingCat)] in
/-- A generalized element pushed along `α` is read on sections by applying `α` to its value
there. -/
theorem sections_map_comp_underlyingMap (α : O ⟶ O') (X : Cᵒᵖ)
    (m : Z ⟶ Stacks.underlyingRingSheaf J O) (z : (Sheaf.sectionsFunctor J X).obj Z) :
    (Sheaf.sectionsFunctor J X).map (m ≫ underlyingMap α) z =
      (α.hom.app X).hom ((Sheaf.sectionsFunctor J X).map m z) := rfl

/-- **Postcomposition with a morphism of sheaves of commutative rings is a ring homomorphism on
generalized elements.** Equivalently: the map of underlying sheaves of sets of `α` is a morphism
of the internal commutative ring objects.

Each of the four axioms is checked on sections, where the internal operations are the sectionwise
ones and `α` is a ring homomorphism on the sections over every object of the site. -/
def postcompRingHom (α : O ⟶ O') (Z : Sheaf J (Type w)) :
    (Z ⟶ Stacks.underlyingRingSheaf J O) →+* (Z ⟶ Stacks.underlyingRingSheaf J O') where
  toFun m := m ≫ underlyingMap α
  map_one' := by
    refine Sheaf.hom_ext_sections fun X z => ?_
    simp only [sections_map_comp_underlyingMap, sections_map_one]
    exact map_one _
  map_mul' a b := by
    refine Sheaf.hom_ext_sections fun X z => ?_
    simp only [sections_map_comp_underlyingMap, sections_map_mul]
    exact map_mul _ _ _
  map_zero' := by
    refine Sheaf.hom_ext_sections fun X z => ?_
    simp only [sections_map_comp_underlyingMap, sections_map_zero]
    exact map_zero _
  map_add' a b := by
    refine Sheaf.hom_ext_sections fun X z => ?_
    simp only [sections_map_comp_underlyingMap, sections_map_add]
    exact map_add _ _ _

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The ring homomorphism `postcompRingHom α Z` sends a generalized element `m` to its composite
`m ≫ underlyingMap α`. -/
theorem postcompRingHom_apply (α : O ⟶ O') (Z : Sheaf J (Type w))
    (m : Z ⟶ Stacks.underlyingRingSheaf J O) :
    postcompRingHom α Z m = m ≫ underlyingMap α := by
  rfl

section Eval

variable {Γ : Type*} [CommRing Γ]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A morphism of sheaves of commutative rings carries polynomial evaluation to polynomial
evaluation.** The value of `Q` at the coordinates `x`, pushed along `α`, is the value of the same
`Q` at the pushed coordinates, its coefficients read into the global sections of `𝒪'` through
`Stacks.Sheaves.PolynomialSystem.postcompRingHom`.

The proof is that both sides are ring homomorphisms in `Q` agreeing on the constants and on the
variables, so `MvPolynomial.ringHom_ext` applies: the left-hand side is the composite of
`CategoryTheory.CommRingObj.evalRingHom` with postcomposition, which is a ring homomorphism
precisely by `Stacks.Sheaves.PolynomialSystem.postcompRingHom`. -/
theorem evalRingHom_comp_underlyingMap (α : O ⟶ O')
    (c : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O))
    {κ : Type*} (x : κ → (Z ⟶ Stacks.underlyingRingSheaf J O)) (Q : MvPolynomial κ Γ) :
    CommRingObj.evalRingHom _ c x Q ≫ underlyingMap α =
      CommRingObj.evalRingHom _ ((postcompRingHom α _).comp c)
        (fun i => x i ≫ underlyingMap α) Q := by
  have key : (postcompRingHom α Z).comp (CommRingObj.evalRingHom _ c x) =
      CommRingObj.evalRingHom _ ((postcompRingHom α _).comp c)
        (fun i => x i ≫ underlyingMap α) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, CommRingObj.evalRingHom_C, postcompRingHom_apply,
        Category.assoc]
    · simp only [RingHom.comp_apply, CommRingObj.evalRingHom_X, postcompRingHom_apply]
  exact RingHom.congr_fun key Q

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A morphism of sheaves of commutative rings carries the row of a polynomial system to the row
of the pushed system.** The first leg of the equalizer presentation: the arrow `∏ᵏ 𝒪 ⟶ ∏ᵛ 𝒪`
whose `j`-th component is the evaluation morphism of `P j` is carried, modulo the two power
comparisons `CategoryTheory.Limits.Pi.map`, to the arrow of the same family over `𝒪'`. -/
theorem evalSystemHom_comp_piMap (α : O ⟶ O')
    (c : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O))
    (κ : Type) [Finite κ] {ν : Type} [Finite ν] (P : ν → MvPolynomial κ Γ) :
    CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O) c κ P ≫
        Limits.Pi.map (fun _ : ν => underlyingMap α) =
      Limits.Pi.map (fun _ : κ => underlyingMap α) ≫
        CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O')
          ((postcompRingHom α _).comp c) κ P := by
  refine Limits.Pi.hom_ext _ _ fun j => ?_
  rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc,
    CommRingObj.evalSystemHom_comp_π, Category.assoc, CommRingObj.evalSystemHom_comp_π,
    CommRingObj.evalPowRingHom, CommRingObj.evalPowRingHom,
    evalRingHom_comp_underlyingMap, CommRingObj.comp_evalRingHom]
  simp only [Limits.Pi.map_π]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A morphism of sheaves of commutative rings carries the zero row to the zero row.** The
companion of `Stacks.Sheaves.PolynomialSystem.evalSystemHom_comp_piMap` for the other leg of the
equalizer presentation. -/
theorem zeroSystemHom_comp_piMap (α : O ⟶ O') (κ ν : Type) [Finite κ] [Finite ν] :
    CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O) κ ν ≫
        Limits.Pi.map (fun _ : ν => underlyingMap α) =
      Limits.Pi.map (fun _ : κ => underlyingMap α) ≫
        CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O') κ ν := by
  refine Limits.Pi.hom_ext _ _ fun j => ?_
  rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc,
    CommRingObj.zeroSystemHom_comp_π, Category.assoc, CommRingObj.zeroSystemHom_comp_π,
    AddMonObj.comp_zero]
  exact map_zero (postcompRingHom α _)

end Eval

end Stacks.Sheaves.PolynomialSystem

end
