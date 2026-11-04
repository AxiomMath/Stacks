module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical presentation of a sheaf of algebras on a site

Let `A ⟶ B` be a morphism of sheaves of commutative rings on a site. Sheafifying the presheaf
`U ↦ A(U)[E(U)]` of polynomial rings on a presheaf of sets `E` gives a sheaf of commutative
rings `A[E]`, which is the free `A`-algebra on `E`: morphisms of sheaves of rings `A[E] ⟶ B`
compatible with the structural morphisms from `A` correspond to morphisms of presheaves of sets
`E ⟶ B`. Taking `E` to be the underlying presheaf of sets of `B`, evaluation of the variable
`[b]` at `b` induces a morphism `A[B] ⟶ B` of `A`-algebras which is surjective as a morphism of
sheaves.

## Main definitions

* `Stacks.Sites.FreeAlgebra.polynomialPresheaf`: the presheaf `U ↦ A(U)[E(U)]`.
* `Stacks.Sites.FreeAlgebra.polynomialCoefficientMap`: the coefficient inclusions
  `A ⟶ A(-)[E(-)]`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheaf`: the sheaf `A[E]`.
* `Stacks.Sites.FreeAlgebra.underlyingPresheaf`: the underlying presheaf of sets of a sheaf of
  commutative rings.
* `Stacks.Sites.FreeAlgebra.canonicalEvaluation`: objectwise evaluation
  `A(U)[B(U)] ⟶ B(U)`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap`: the structural morphism
  `A ⟶ A[E]`.
* `Stacks.Sites.FreeAlgebra.canonicalPresentation`: the morphism `A[B] ⟶ B`.
* `Stacks.Sites.FreeAlgebra.polynomialEvaluation`: objectwise evaluation
  `A(U)[E(U)] ⟶ B(U)` along `a : A ⟶ B` and `e : E ⟶ B`.
* `Stacks.Sites.FreeAlgebra.polynomialVariable`: the variables `E ⟶ A(-)[E(-)]`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable`: the variables `E ⟶ A[E]`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc`: the morphism `A[E] ⟶ B` extending `a` by
  `[x] ↦ e(x)`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafHomEquiv`: the universal property of `A[E]`.

## Main results

* `Stacks.Sites.FreeAlgebra.canonicalPresentation_spec`: before sheafification the canonical
  presentation is evaluation of coefficients along `a` together with `[b] ↦ b`.
* `Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap`: it is a morphism of
  `A`-algebras.
* `Stacks.Sites.FreeAlgebra.canonicalPresentation_isLocallySurjective`: it is surjective.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc_spec`: before sheafification the morphism
  classifying `(a, e)` is evaluation of coefficients along `a` together with `[x] ↦ e(x)`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc` and
  `Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc`: it is a morphism of
  `A`-algebras sending the variable `[x]` to `e(x)`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc_isLocallySurjective`: the morphism classifying
  `(a, e)` is surjective as soon as `e` is, which is the general form of
  `canonicalPresentation_isLocallySurjective`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext`: two morphisms out of `A[E]` agreeing on
  the coefficients and on the variables are equal.
* `Stacks.Sites.FreeAlgebra.canonicalPresentation_eq_desc`: the canonical presentation is the
  morphism classifying the identity of `B`.

## Implementation notes

The notation `A[B]` of the source is `freeAlgebraSheaf J A (underlyingPresheaf J B)`, so the
free algebra is built on an arbitrary presheaf of sets and the sheaf `B` enters only through
its sections. Surjectivity of a morphism of sheaves means local surjectivity of the underlying
morphism of set-valued presheaves. The rule `[b] ↦ b` is recorded by
`canonicalPresentation_spec`, the factorisation through the unit of the sheafification
adjunction, which also feeds the surjectivity proof.

## References

* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU)
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The presheaf of polynomial rings `U ↦ A(U)[E(U)]`. -/
noncomputable def polynomialPresheaf (A : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) : Functor Cᵒᵖ CommRingCat.{w} where
  obj U := CommRingCat.of (MvPolynomial (E.obj U) (A.obj.obj U))
  map {U V} f := CommRingCat.ofHom
    (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map f).hom)
      (fun e ↦ MvPolynomial.X (E.map f e)))
  map_id U := by
    ext <;> simp
  map_comp f g := by
    ext <;> simp

/-- The coefficient inclusions `A(U) → A(U)[E(U)]`, as a morphism of presheaves. -/
noncomputable def polynomialCoefficientMap (A : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) : A.obj ⟶ polynomialPresheaf J A E where
  app U := CommRingCat.ofHom MvPolynomial.C
  naturality := by
    intro U V f
    ext r
    exact (MvPolynomial.eval₂Hom_C _ _ r).symm

variable [HasWeakSheafify J CommRingCat.{w}]

/-- The sheaf `A[E]`, obtained by sheafifying `U ↦ A(U)[E(U)]`. -/
noncomputable def freeAlgebraSheaf (A : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) : Sheaf J CommRingCat.{w} :=
  (presheafToSheaf J CommRingCat.{w}).obj (polynomialPresheaf J A E)

/-- The underlying presheaf of sets of a sheaf of commutative rings. -/
abbrev underlyingPresheaf (B : Sheaf J CommRingCat.{w}) : Functor Cᵒᵖ (Type w) :=
  B.obj ⋙ forget CommRingCat.{w}

/-- Evaluation `A(U)[B(U)] → B(U)`, sending a coefficient through `a` and a variable `[b]`
to `b`. -/
noncomputable def canonicalEvaluation (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    polynomialPresheaf J A (underlyingPresheaf J B) ⟶ B.obj where
  app U := CommRingCat.ofHom (MvPolynomial.eval₂Hom (a.hom.app U).hom id)
  naturality := by
    intro U V f
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      dsimp only [polynomialPresheaf, underlyingPresheaf]
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
      simp only [CommRingCat.hom_ofHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      exact congrArg (fun q : A.obj.obj U ⟶ B.obj.obj V ↦ q.hom r)
        (a.hom.naturality f)
    · intro b
      dsimp only [polynomialPresheaf, underlyingPresheaf]
      simp

/-- The structural morphism `A → A[E]`. -/
noncomputable def freeAlgebraSheafCoefficientMap (A : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) : A ⟶ freeAlgebraSheaf J A E :=
  (fullyFaithfulSheafToPresheaf J CommRingCat.{w}).homEquiv.symm
    (polynomialCoefficientMap J A E ≫
      (toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E))

/-- The structural morphism `A ⟶ A[E]` sends a section `r` of `A` to the class of the constant
polynomial `r`. -/
theorem freeAlgebraSheafCoefficientMap_app (A : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (U : Cᵒᵖ) (r : A.obj.obj U) :
    ((freeAlgebraSheafCoefficientMap J A E).hom.app U).hom r =
      (((toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E)).app U).hom
        (MvPolynomial.C r) :=
  rfl

/-- **Stacks 08TU.** The canonical morphism `A[B] → B`. -/
@[stacks 08TU "the canonical morphism"]
noncomputable def canonicalPresentation (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    freeAlgebraSheaf J A (underlyingPresheaf J B) ⟶ B :=
  (sheafificationAdjunction J CommRingCat.{w}).homEquiv _ _ |>.symm
    (canonicalEvaluation J A B a)

/-- The unit followed by the adjoint transpose of `φ` is `φ`. -/
private theorem toSheafification_comp_map_homEquiv_symm
    {P : Functor Cᵒᵖ CommRingCat.{w}} {B : Sheaf J CommRingCat.{w}} (φ : P ⟶ B.obj) :
    (toSheafification J CommRingCat.{w}).app P ≫ (sheafToPresheaf J CommRingCat.{w}).map
      (((sheafificationAdjunction J CommRingCat.{w}).homEquiv _ _).symm φ) = φ := by
  simpa only [toSheafification, Equiv.apply_symm_apply] using
    ((sheafificationAdjunction J CommRingCat.{w}).homEquiv_unit _ _
      (((sheafificationAdjunction J CommRingCat.{w}).homEquiv _ _).symm φ)).symm

/-- Under full faithfulness, composing with the structural map unfolds through the unit. -/
private theorem homEquiv_coefficientMap_comp (A B : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (g : freeAlgebraSheaf J A E ⟶ B) :
    (fullyFaithfulSheafToPresheaf J CommRingCat.{w}).homEquiv
        (freeAlgebraSheafCoefficientMap J A E ≫ g) =
      polynomialCoefficientMap J A E ≫
        ((toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E) ≫
          (sheafToPresheaf J CommRingCat.{w}).map g) := rfl

/-- A morphism `A[E] ⟶ B` whose composite with the unit is evaluation of coefficients along `a`
respects the structural maps from `A`. -/
private theorem coefficientMap_comp_of_fac (A B : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (a : A ⟶ B) (g : freeAlgebraSheaf J A E ⟶ B)
    (φ : polynomialPresheaf J A E ⟶ B.obj)
    (hg : (toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E) ≫
      (sheafToPresheaf J CommRingCat.{w}).map g = φ)
    (hφ : ∀ (U : Cᵒᵖ) (r : A.obj.obj U), (φ.app U).hom (MvPolynomial.C r) = (a.hom.app U).hom r) :
    freeAlgebraSheafCoefficientMap J A E ≫ g = a := by
  apply (fullyFaithfulSheafToPresheaf J CommRingCat.{w}).homEquiv.injective
  rw [homEquiv_coefficientMap_comp, hg]
  ext U r
  exact hφ U r

/-- The canonical presentation is induced by coefficient evaluation and `[b] ↦ b`. -/
@[stacks 08TU "evaluation on coefficients and variables"]
theorem canonicalPresentation_spec (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    (toSheafification J CommRingCat.{w}).app
        (polynomialPresheaf J A (underlyingPresheaf J B)) ≫
      (sheafToPresheaf J CommRingCat.{w}).map (canonicalPresentation J A B a) =
        canonicalEvaluation J A B a := by
  exact toSheafification_comp_map_homEquiv_symm J _

/-- The canonical presentation `A[B] → B` respects the structural maps from `A`. -/
@[stacks 08TU "compatibility with the A-algebra structures"]
theorem canonicalPresentation_comp_coefficientMap
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B) ≫
      canonicalPresentation J A B a = a := by
  exact coefficientMap_comp_of_fac J A B _ a _ _ (canonicalPresentation_spec J A B a)
    fun _ _ ↦ MvPolynomial.eval₂Hom_C _ _ _

/-- The canonical presentation `A[B] → B` is surjective as a morphism of sheaves. -/
@[stacks 08TU "surjectivity"]
theorem canonicalPresentation_isLocallySurjective
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{w}).map (canonicalPresentation J A B a))
        (forget CommRingCat.{w})) := by
  have h : Presheaf.IsLocallySurjective J (canonicalEvaluation J A B a) :=
    Presheaf.isLocallySurjective_of_surjective J _
      (fun U b ↦ ⟨MvPolynomial.X b, MvPolynomial.eval₂Hom_X' _ _ _⟩)
  exact (Presheaf.isLocallySurjective_iff_whisker_forget J _).mp
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (canonicalPresentation_spec J A B a))

/-! ### The universal property of `A[E]` -/

/-- Evaluation `A(U)[E(U)] → B(U)` along a morphism `a : A ⟶ B` of sheaves of commutative rings
and a morphism `e : E ⟶ B` of presheaves of sets, sending the variable `[x]` to `e(x)`. -/
noncomputable def polynomialEvaluation (A B : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (a : A ⟶ B) (e : E ⟶ underlyingPresheaf J B) :
    polynomialPresheaf J A E ⟶ B.obj where
  app U := CommRingCat.ofHom (MvPolynomial.eval₂Hom (a.hom.app U).hom (e.app U))
  naturality := by
    intro U V f
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      dsimp only [polynomialPresheaf, underlyingPresheaf]
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
      simp only [CommRingCat.hom_ofHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      exact congrArg (fun q : A.obj.obj U ⟶ B.obj.obj V ↦ q.hom r) (a.hom.naturality f)
    · intro x
      dsimp only [polynomialPresheaf, underlyingPresheaf]
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
      simp only [CommRingCat.hom_ofHom, MvPolynomial.eval₂Hom_X']
      exact NatTrans.naturality_apply e f x

omit [HasWeakSheafify J CommRingCat.{w}] in
/-- Objectwise evaluation sends a constant to the image of its coefficient. -/
theorem polynomialEvaluation_C (A B : Sheaf J CommRingCat.{w}) (E : Functor Cᵒᵖ (Type w))
    (a : A ⟶ B) (e : E ⟶ underlyingPresheaf J B) (U : Cᵒᵖ) (r : A.obj.obj U) :
    ((polynomialEvaluation J A B E a e).app U).hom (MvPolynomial.C r) =
      (a.hom.app U).hom r :=
  MvPolynomial.eval₂Hom_C _ _ _

omit [HasWeakSheafify J CommRingCat.{w}] in
/-- Objectwise evaluation sends the variable `[x]` to `e(x)`. -/
theorem polynomialEvaluation_X (A B : Sheaf J CommRingCat.{w}) (E : Functor Cᵒᵖ (Type w))
    (a : A ⟶ B) (e : E ⟶ underlyingPresheaf J B) (U : Cᵒᵖ) (x : E.obj U) :
    ((polynomialEvaluation J A B E a e).app U).hom (MvPolynomial.X x) = e.app U x :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- The variables `E(U) → A(U)[E(U)]`, as a morphism of presheaves of sets. -/
noncomputable def polynomialVariable (A : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) :
    E ⟶ polynomialPresheaf J A E ⋙ forget CommRingCat.{w} where
  app U := TypeCat.ofHom fun x ↦ (MvPolynomial.X x : MvPolynomial (E.obj U) (A.obj.obj U))
  naturality := by
    intro U V f
    ext x
    dsimp only [polynomialPresheaf]
    simp

/-- The variables `E → A[E]`, as a morphism of presheaves of sets. -/
noncomputable def freeAlgebraSheafVariable (A : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) : E ⟶ underlyingPresheaf J (freeAlgebraSheaf J A E) :=
  polynomialVariable J A E ≫ Functor.whiskerRight
    ((toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E))
    (forget CommRingCat.{w})

/-- The variable `[x]` of `A[E]` is the class of the polynomial `X x`. -/
theorem freeAlgebraSheafVariable_app (A : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (U : Cᵒᵖ) (x : E.obj U) :
    (freeAlgebraSheafVariable J A E).app U x =
      (((toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E)).app U).hom
        (MvPolynomial.X x) :=
  rfl

/-- The morphism of sheaves of commutative rings `A[E] → B` extending `a : A ⟶ B` by sending
the variable `[x]` to `e(x)`. -/
noncomputable def freeAlgebraSheafDesc (A B : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (a : A ⟶ B) (e : E ⟶ underlyingPresheaf J B) :
    freeAlgebraSheaf J A E ⟶ B :=
  (sheafificationAdjunction J CommRingCat.{w}).homEquiv _ _ |>.symm
    (polynomialEvaluation J A B E a e)

/-- Before sheafification, the morphism classifying `(a, e)` is evaluation of coefficients along
`a` together with `[x] ↦ e(x)`. -/
theorem freeAlgebraSheafDesc_spec (A B : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (a : A ⟶ B) (e : E ⟶ underlyingPresheaf J B) :
    (toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E) ≫
      (sheafToPresheaf J CommRingCat.{w}).map (freeAlgebraSheafDesc J A B E a e) =
        polynomialEvaluation J A B E a e := by
  exact toSheafification_comp_map_homEquiv_symm J _

/-- The morphism `A[E] → B` classifying `(a, e)` respects the structural maps from `A`. -/
theorem freeAlgebraSheafCoefficientMap_comp_desc (A B : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (a : A ⟶ B) (e : E ⟶ underlyingPresheaf J B) :
    freeAlgebraSheafCoefficientMap J A E ≫ freeAlgebraSheafDesc J A B E a e = a := by
  exact coefficientMap_comp_of_fac J A B E a _ _ (freeAlgebraSheafDesc_spec J A B E a e)
    fun _ _ ↦ MvPolynomial.eval₂Hom_C _ _ _

/-- The morphism `A[E] → B` classifying `(a, e)` sends the variable `[x]` to `e(x)`. -/
theorem freeAlgebraSheafVariable_comp_desc (A B : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (a : A ⟶ B) (e : E ⟶ underlyingPresheaf J B) :
    freeAlgebraSheafVariable J A E ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{w}).map (freeAlgebraSheafDesc J A B E a e))
        (forget CommRingCat.{w}) = e := by
  have key : Functor.whiskerRight ((toSheafification J CommRingCat.{w}).app
        (polynomialPresheaf J A E)) (forget CommRingCat.{w}) ≫
      Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map
        (freeAlgebraSheafDesc J A B E a e)) (forget CommRingCat.{w}) =
      Functor.whiskerRight (polynomialEvaluation J A B E a e) (forget CommRingCat.{w}) := by
    rw [← freeAlgebraSheafDesc_spec J A B E a e, Functor.whiskerRight_comp]
    rfl
  show polynomialVariable J A E ≫ (Functor.whiskerRight ((toSheafification J CommRingCat.{w}).app
      (polynomialPresheaf J A E)) (forget CommRingCat.{w}) ≫ Functor.whiskerRight
      ((sheafToPresheaf J CommRingCat.{w}).map (freeAlgebraSheafDesc J A B E a e))
      (forget CommRingCat.{w})) = e
  rw [key]
  ext U x
  exact MvPolynomial.eval₂Hom_X' _ _ _

/-- **A family of generators which is surjective presents `B`.** If every section of `B` is
locally of the form `e(x)`, then the morphism `A[E] ⟶ B` classifying `(a, e)` is surjective as
a morphism of sheaves: it is already surjective on the variables, `e` factoring through it by
`freeAlgebraSheafVariable_comp_desc`.

For `e` the identity of the underlying presheaf of `B` this is
`canonicalPresentation_isLocallySurjective`; the point of the general form is that a family of
generators assembled from a fibre product is surjective without being an identity. -/
instance freeAlgebraSheafDesc_isLocallySurjective (A B : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (a : A ⟶ B) (e : E ⟶ underlyingPresheaf J B)
    [Presheaf.IsLocallySurjective J e] :
    Presheaf.IsLocallySurjective J (freeAlgebraSheafDesc J A B E a e).hom :=
  (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (freeAlgebraSheafVariable_comp_desc J A B E a e))

/-- Two morphisms out of `A[E]` which agree on the coefficients and on the variables are
equal. -/
theorem freeAlgebraSheaf_hom_ext (A B : Sheaf J CommRingCat.{w}) (E : Functor Cᵒᵖ (Type w))
    {g₁ g₂ : freeAlgebraSheaf J A E ⟶ B}
    (hc : freeAlgebraSheafCoefficientMap J A E ≫ g₁ =
      freeAlgebraSheafCoefficientMap J A E ≫ g₂)
    (hv : freeAlgebraSheafVariable J A E ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{w}).map g₁) (forget CommRingCat.{w}) =
      freeAlgebraSheafVariable J A E ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{w}).map g₂) (forget CommRingCat.{w})) :
    g₁ = g₂ := by
  have hc' := (homEquiv_coefficientMap_comp J A B E g₁).symm.trans
    ((congrArg (fullyFaithfulSheafToPresheaf J CommRingCat.{w}).homEquiv hc).trans
      (homEquiv_coefficientMap_comp J A B E g₂))
  apply ((sheafificationAdjunction J CommRingCat.{w}).homEquiv
    (polynomialPresheaf J A E) B).injective
  refine ((sheafificationAdjunction J CommRingCat.{w}).homEquiv_unit _ B g₁).trans
    (Eq.trans ?_ ((sheafificationAdjunction J CommRingCat.{w}).homEquiv_unit _ B g₂).symm)
  exact NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext (MvPolynomial.ringHom_ext
    (fun r ↦ congrArg (fun t : A.obj ⟶ B.obj ↦ (t.app U).hom r) hc')
    (fun x ↦ congrArg (fun t : E ⟶ underlyingPresheaf J B ↦ t.app U x) hv)))

/-- The sheaf `A[E]` is the free `A`-algebra on the presheaf of sets `E`: morphisms of sheaves
of commutative rings `A[E] ⟶ B` compatible with the structural morphisms from `A` correspond to
morphisms of presheaves of sets `E ⟶ B`. -/
noncomputable def freeAlgebraSheafHomEquiv (A B : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) (a : A ⟶ B) :
    { g : freeAlgebraSheaf J A E ⟶ B // freeAlgebraSheafCoefficientMap J A E ≫ g = a } ≃
      (E ⟶ underlyingPresheaf J B) where
  toFun g := freeAlgebraSheafVariable J A E ≫ Functor.whiskerRight
    ((sheafToPresheaf J CommRingCat.{w}).map g.1) (forget CommRingCat.{w})
  invFun e := ⟨freeAlgebraSheafDesc J A B E a e,
    freeAlgebraSheafCoefficientMap_comp_desc J A B E a e⟩
  left_inv g := Subtype.ext (freeAlgebraSheaf_hom_ext J A B E
    (by rw [freeAlgebraSheafCoefficientMap_comp_desc, g.2])
    (freeAlgebraSheafVariable_comp_desc J A B E a _))
  right_inv e := freeAlgebraSheafVariable_comp_desc J A B E a e

/-- The canonical presentation `A[B] → B` is the morphism classifying the identity of `B`. -/
theorem canonicalPresentation_eq_desc (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    canonicalPresentation J A B a =
      freeAlgebraSheafDesc J A B (underlyingPresheaf J B) a (𝟙 _) := rfl

end Stacks.Sites.FreeAlgebra

end
