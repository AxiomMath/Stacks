module

public import Mathlib.Algebra.MvPolynomial.Eval
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomAlgebra

/-!
# Polynomial maps of a sheaf of commutative rings and their transport

Let `R` be a sheaf of rings with commuting sections on a site.  A polynomial `Q` in finitely
many variables, with coefficients in a commutative ring `A` that acts on `R` through
generalized elements `κ : A →+* (H ⟶ R)` of some shape `H`, defines a morphism of sheaves of
sets

```
  evalHom hc κ Q : H ⨯ Rⁿ ⟶ R,   (h, a) ↦ Q^κ(h)(a),
```

which on sections over every object substitutes the tuple `a` into the polynomial whose
coefficients are the values of `κ` at `h`.  This file constructs it and proves that it commutes
with every finite-product-preserving functor `P` to types: `P.map (evalHom hc κ Q)` is the
polynomial map of `Q` for the ring structure transported to `P.obj R` along `P`.  Applied to the
inverse image of a morphism of topoi, followed by sections, this is what turns a polynomial
identity among sections of `R` into the same identity among sections of an inverse image, as the
proof of Stacks 04KL requires.

## Main definitions

* `CategoryTheory.Sheaf.homCommRing` and `CategoryTheory.Sheaf.ringObjCommRing`: the
  commutative rings of generalized elements of `R`, and of the image of `R` under a
  finite-product-preserving functor, when the sections of `R` commute.
* `CategoryTheory.Sheaf.evalRingHom`: evaluating generalized elements of `R` at an element of
  `P.obj Z`, as a ring homomorphism.
* `CategoryTheory.Sheaf.evalHom`: the polynomial map of `Q`.

## Main results

* `CategoryTheory.Sheaf.sectionsFunctor_map_evalHom`: the polynomial map on sections.
* `CategoryTheory.Sheaf.map_evalHom`: the transport of the polynomial map along `P`.

## Implementation notes

The polynomial map is *defined* as `MvPolynomial.eval₂` in the commutative ring of generalized
elements of shape `H ⨯ Rⁿ`, at the coordinate projections.  Both results are then the
compatibility of `MvPolynomial.eval₂` with a ring homomorphism (`MvPolynomial.eval₂_comp_left`),
for the ring homomorphism "apply `P` and evaluate", and no induction on polynomials is needed.

Commutativity of the sections is a hypothesis `hc` rather than an instance, for the reason
recorded at `CategoryTheory.Sheaf.hom_mul_comm`.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u u'

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] {R : Sheaf J RingCat.{w}}

section Rings

variable (hc : ∀ (X : Cᵒᵖ) (x y : (sectionsFunctor J X).obj (ringSheaf R)), x * y = y * x)

/-- The generalized elements of shape `Z` of a sheaf of rings with commuting sections form a
commutative ring, extending `CategoryTheory.Sheaf.homRing`. -/
@[instance_reducible]
def homCommRing (Z : Sheaf J (Type w)) : CommRing (Z ⟶ ringSheaf R) :=
  { homRing R Z with mul_comm := hom_mul_comm hc }

/-- The image of a sheaf of rings with commuting sections under a finite-product-preserving
functor to types is a commutative ring, extending `CategoryTheory.Sheaf.ringObjRing`. -/
@[instance_reducible]
def ringObjCommRing (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P] :
    CommRing (P.obj (ringSheaf R)) :=
  { ringObjRing R P with mul_comm := ringMulObj_comm hc P }

/-- The sections over `X` of a sheaf of rings with commuting sections form a commutative ring,
extending `CategoryTheory.Sheaf.ringSectionsRing`. -/
@[instance_reducible]
def ringSectionsCommRing (X : Cᵒᵖ) : CommRing ((sectionsFunctor J X).obj (ringSheaf R)) :=
  { ringSectionsRing R X with mul_comm := hc X }

end Rings

variable {Z : Sheaf J (Type w)}

/-- Applying a finite-product-preserving functor `P` to types and evaluating at `z : P.obj Z`
is a ring homomorphism from the generalized elements of shape `Z` of `R` to the ring transported
to `P.obj R`. -/
def evalRingHom (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P] (z : P.obj Z) :
    letI := ringObjRing R P
    (Z ⟶ ringSheaf R) →+* P.obj (ringSheaf R) :=
  letI := ringObjRing R P
  { toFun := fun a => P.map a z
    map_one' := map_hom_one P z
    map_mul' := fun a b => map_hom_mul P a b z
    map_zero' := map_hom_ringZero P z
    map_add' := fun a b => map_hom_add P a b z }

/-- `CategoryTheory.Sheaf.evalRingHom` applies `P` and evaluates. -/
@[simp]
lemma evalRingHom_apply (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]
    (z : P.obj Z) (a : Z ⟶ ringSheaf R) : evalRingHom P z a = P.map a z :=
  rfl

/-- On sections, the unit generalized element of a sheaf of rings takes the value one. -/
lemma sectionsFunctor_map_hom_one (X : Cᵒᵖ) (z : (sectionsFunctor J X).obj Z) :
    (sectionsFunctor J X).map (1 : Z ⟶ ringSheaf R) z = 1 :=
  (map_hom_one (sectionsFunctor J X) z).trans (sectionsFunctor_map_ringOneHom R X _)

/-- Evaluating generalized elements of a sheaf of rings on sections, as a ring homomorphism to
the ring of sections. -/
def sectionsEvalRingHom (X : Cᵒᵖ) (z : (sectionsFunctor J X).obj Z) :
    (Z ⟶ ringSheaf R) →+* (sectionsFunctor J X).obj (ringSheaf R) where
  toFun a := (sectionsFunctor J X).map a z
  map_one' := sectionsFunctor_map_hom_one X z
  map_mul' a b := sectionsFunctor_map_hom_mul X a b z
  map_zero' := sectionsFunctor_map_hom_ringZero X z
  map_add' a b := sectionsFunctor_map_hom_add X a b z

/-- `CategoryTheory.Sheaf.sectionsEvalRingHom` takes sections and evaluates. -/
@[simp]
lemma sectionsEvalRingHom_apply (X : Cᵒᵖ) (z : (sectionsFunctor J X).obj Z)
    (a : Z ⟶ ringSheaf R) : sectionsEvalRingHom X z a = (sectionsFunctor J X).map a z :=
  rfl

section Polynomial

variable (hc : ∀ (X : Cᵒᵖ) (x y : (sectionsFunctor J X).obj (ringSheaf R)), x * y = y * x)
  {A : Type u'} [CommRing A] {H : Sheaf J (Type w)} {ι : Type} [Finite ι]

/-- **The polynomial map of a polynomial with coefficients acting through generalized
elements.**  For `κ : A →+* (H ⟶ R)` and `Q ∈ A[X_i : i ∈ ι]`, the morphism
`H ⨯ R^ι ⟶ R` sending `(h, a)` to the value at `a` of the polynomial whose coefficients are the
values of `κ` at `h`.  It is `MvPolynomial.eval₂` in the commutative ring of generalized elements
of shape `H ⨯ R^ι`, at the coordinate projections. -/
def evalHom (κ : A →+* (H ⟶ ringSheaf R)) (Q : MvPolynomial ι A) :
    H ⨯ ∏ᶜ (fun _ : ι => ringSheaf R) ⟶ ringSheaf R :=
  letI := homCommRing hc (H ⨯ ∏ᶜ (fun _ : ι => ringSheaf R))
  MvPolynomial.eval₂
    ((evalRingHom (coyoneda.obj (op (H ⨯ ∏ᶜ (fun _ : ι => ringSheaf R)))) prod.fst).comp κ)
    (fun i => prod.snd ≫ Pi.π (fun _ : ι => ringSheaf R) i) Q

/-- **Polynomial maps commute with finite-product-preserving functors.**  For a functor `P` to
types preserving finite products and `z ∈ P (H ⨯ R^ι)`, applying `P` to the polynomial map of
`Q` and evaluating at `z` is the value of `Q` — its coefficients evaluated at the `H`-component
of `z` — at the `R^ι`-components of `z`, computed in the ring transported to `P.obj R`. -/
theorem map_evalHom (κ : A →+* (H ⟶ ringSheaf R)) (Q : MvPolynomial ι A)
    (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]
    (z : P.obj (H ⨯ ∏ᶜ (fun _ : ι => ringSheaf R))) :
    letI := ringObjCommRing hc P
    P.map (evalHom hc κ Q) z =
      MvPolynomial.eval (fun i => P.map (prod.snd ≫ Pi.π (fun _ : ι => ringSheaf R) i) z)
        (MvPolynomial.map ((evalRingHom P (P.map prod.fst z)).comp κ) Q) := by
  let := homCommRing hc (H ⨯ ∏ᶜ (fun _ : ι => ringSheaf R))
  let := ringObjCommRing hc P
  rw [MvPolynomial.eval_map]
  refine (MvPolynomial.eval₂_comp_left (evalRingHom (R := R) P z) _ _ Q).trans ?_
  congr 1
  ext c
  exact (P.map_comp_apply _ _ z)

/-- **The polynomial map on sections.**  Over every object `X`, the polynomial map of `Q` sends
a section `z` of `H ⨯ R^ι` to the value of `Q` — its coefficients evaluated at the `H`-component
of `z` — at the `R^ι`-components of `z`, computed in the ring of sections of `R` over `X`. -/
theorem sectionsFunctor_map_evalHom (κ : A →+* (H ⟶ ringSheaf R)) (Q : MvPolynomial ι A)
    (X : Cᵒᵖ) (z : (sectionsFunctor J X).obj (H ⨯ ∏ᶜ (fun _ : ι => ringSheaf R))) :
    letI := ringSectionsCommRing hc X
    (sectionsFunctor J X).map (evalHom hc κ Q) z =
      MvPolynomial.eval
        (fun i => (sectionsFunctor J X).map (prod.snd ≫ Pi.π (fun _ : ι => ringSheaf R) i) z)
        (MvPolynomial.map
          ((sectionsEvalRingHom X ((sectionsFunctor J X).map prod.fst z)).comp κ) Q) := by
  let := homCommRing hc (H ⨯ ∏ᶜ (fun _ : ι => ringSheaf R))
  let := ringSectionsCommRing hc X
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp_left (sectionsEvalRingHom (R := R) X z) _ _ Q).trans
    (by congr 1)

end Polynomial

end CategoryTheory.Sheaf
