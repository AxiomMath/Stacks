module

public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# Transporting a graded-split short exact sequence along an isomorphism of complexes

A `DGCategory.GradedSplitShortExact` is attached to an ordered triple of objects `x, y, z`. Given
an isomorphism in `Comp(A)` of any one of the three objects, the inclusion, projection,
surjection and splitting can be composed with the isomorphism or its inverse to give a
graded-split short exact sequence over the new triple; the four splitting identities follow from
`Iso.hom_inv_id` and `Iso.inv_hom_id`.

## Main definitions

* `DGCategory.GradedSplitShortExact.transportQuotient`: transport along an isomorphism of the
  quotient `z`.
* `DGCategory.GradedSplitShortExact.transportSub`: transport along an isomorphism of the
  subobject `x`.
* `DGCategory.GradedSplitShortExact.transportMiddle`: transport along an isomorphism of the
  middle term `y`.

## Main results

* `DGCategory.GradedSplitShortExact.connectingHom_transportQuotient`,
  `DGCategory.GradedSplitShortExact.connectingHom_transportSub` and
  `DGCategory.GradedSplitShortExact.connectingHom_transportMiddle`: the connecting morphism of a
  transported sequence, as the connecting morphism of the original composed with the isomorphism.

## Implementation notes

An isomorphism of `Comp(A)` is a pair of closed degree-zero morphisms inverse to each other, and
`DGCategory.hom_inv_comp0` and `DGCategory.inv_hom_comp0` state its two identities as identities
of degree-zero composites. Degree-zero composition `DGCategory.comp0` is written `≫₀`, in the
diagrammatic order.

## References

* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

local infixr:80 " ≫₀ " => comp0

namespace GradedSplitShortExact

variable {x y z : A.Obj}

/-- Associativity of composition of two degree-zero morphisms with a degree-one one. -/
private lemma comp_comp_degree_one {v w x y : A.Obj} (f : A.Hom x y 0) (g : A.Hom w x 0)
    (h : A.Hom v w 1) :
    A.comp (by omega : (0 : ℤ) + 1 = 1) f (A.comp (by omega : (0 : ℤ) + 1 = 1) g h) =
      A.comp (by omega : (0 : ℤ) + 1 = 1) (A.comp (by omega : (0 : ℤ) + 0 = 0) f g) h :=
  A.assoc _ _ _ _ f g h

/-- The identity `π a = 1` in the degree-zero notation. -/
private lemma pi_a_comp0 (E : GradedSplitShortExact (A := A) x y z) :
    E.a.1 ≫₀ E.π = A.id x :=
  E.π_a

/-- The identity `b s = 1` in the degree-zero notation. -/
private lemma b_s_comp0 (E : GradedSplitShortExact (A := A) x y z) :
    E.s ≫₀ E.b.1 = A.id z :=
  E.b_s

/-- The identity `π s = 0` in the degree-zero notation. -/
private lemma pi_s_comp0 (E : GradedSplitShortExact (A := A) x y z) :
    E.s ≫₀ E.π = 0 :=
  E.π_s

/-- The identity `a π + s b = 1` in the degree-zero notation. -/
private lemma split_comp0 (E : GradedSplitShortExact (A := A) x y z) :
    E.π ≫₀ E.a.1 + E.b.1 ≫₀ E.s = A.id y :=
  E.a_π_add_s_b

/-! ### Transport along an isomorphism of the quotient -/

/-- The transport of a graded-split short exact sequence `E` over `x, y, z` along an isomorphism
`e : z ≅ z'` of `Comp(A)`: the data `a' = a`, `b' = b ≫ e.hom`, `π' = π`, `s' = e.inv ≫ s`
(composites in the diagrammatic order), a graded-split short exact sequence over `x, y, z'`. -/
public def transportQuotient {z' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from z) ≅ (show A.Comp from z')) :
    GradedSplitShortExact (A := A) x y z' where
  a := E.a
  b := A.compCocycle e.hom E.b
  π := E.π
  s := A.comp (by omega : (0 : ℤ) + 0 = 0) E.s e.inv.1
  π_a := E.π_a
  b_s := by
    change (e.inv.1 ≫₀ E.s) ≫₀ (E.b.1 ≫₀ e.hom.1) = A.id z'
    rw [comp0_assoc e.inv.1 E.s (E.b.1 ≫₀ e.hom.1),
      ← comp0_assoc E.s E.b.1 e.hom.1, b_s_comp0 E, id_comp0, inv_hom_comp0]
  π_s := by
    change (e.inv.1 ≫₀ E.s) ≫₀ E.π = 0
    rw [comp0_assoc e.inv.1 E.s E.π, pi_s_comp0 E, comp0_zero]
  a_π_add_s_b := by
    change E.π ≫₀ E.a.1 + (E.b.1 ≫₀ e.hom.1) ≫₀ (e.inv.1 ≫₀ E.s) = A.id y
    rw [comp0_assoc E.b.1 e.hom.1 (e.inv.1 ≫₀ E.s),
      ← comp0_assoc e.hom.1 e.inv.1 E.s, hom_inv_comp0, id_comp0, split_comp0 E]

/-- The inclusion of `E.transportQuotient e` is that of `E`. -/
@[simp] theorem transportQuotient_a {z' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from z) ≅ (show A.Comp from z')) :
    (E.transportQuotient e).a = E.a := rfl

/-- The surjection of `E.transportQuotient e` is that of `E` followed by `e.hom`. -/
@[simp] theorem transportQuotient_b {z' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from z) ≅ (show A.Comp from z')) :
    (E.transportQuotient e).b = A.compCocycle e.hom E.b := rfl

/-- The projection of `E.transportQuotient e` is that of `E`. -/
@[simp] theorem transportQuotient_π {z' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from z) ≅ (show A.Comp from z')) :
    (E.transportQuotient e).π = E.π := rfl

/-- The splitting of `E.transportQuotient e` is `e.inv` followed by that of `E`. -/
@[simp] theorem transportQuotient_s {z' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from z) ≅ (show A.Comp from z')) :
    (E.transportQuotient e).s = A.comp (by omega : (0 : ℤ) + 0 = 0) E.s e.inv.1 := rfl

/-- The connecting morphism of a sequence transported along an isomorphism `e` of its quotient
is the connecting morphism of the original precomposed with `e.inv`. -/
public theorem connectingHom_transportQuotient {z' : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from z) ≅ (show A.Comp from z')) :
    connectingHom (E.transportQuotient e) =
      A.comp (by omega : (1 : ℤ) + 0 = 1) (connectingHom E) e.inv.1 := by
  have hd : A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) E.s e.inv.1) =
      A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E.s) e.inv.1 := by
    rw [A.leibniz, e.inv.2, A.comp_zero_right, smul_zero, add_zero]
  change A.comp (by omega : (0 : ℤ) + (0 + 1) = 1) E.π
      (A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) E.s e.inv.1)) = _
  rw [hd]
  exact A.assoc (show (1 : ℤ) + 0 = 1 by omega) (show (0 : ℤ) + 1 = 1 by omega)
    (show (0 : ℤ) + 1 = 1 by omega) (show (1 : ℤ) + 0 = 1 by omega) E.π (A.d E.s) e.inv.1

/-! ### Transport along an isomorphism of the subobject -/

/-- The transport of a graded-split short exact sequence `E` over `x, y, z` along an isomorphism
`e : x ≅ x'` of `Comp(A)`: the data `a' = e.inv ≫ a`, `b' = b`, `π' = π ≫ e.hom`, `s' = s`
(composites in the diagrammatic order), a graded-split short exact sequence over `x', y, z`. -/
public def transportSub {x' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from x) ≅ (show A.Comp from x')) :
    GradedSplitShortExact (A := A) x' y z where
  a := A.compCocycle E.a e.inv
  b := E.b
  π := A.comp (by omega : (0 : ℤ) + 0 = 0) e.hom.1 E.π
  s := E.s
  π_a := by
    change (e.inv.1 ≫₀ E.a.1) ≫₀ (E.π ≫₀ e.hom.1) = A.id x'
    rw [comp0_assoc e.inv.1 E.a.1 (E.π ≫₀ e.hom.1),
      ← comp0_assoc E.a.1 E.π e.hom.1, pi_a_comp0 E, id_comp0, inv_hom_comp0]
  b_s := E.b_s
  π_s := by
    change E.s ≫₀ (E.π ≫₀ e.hom.1) = 0
    rw [← comp0_assoc E.s E.π e.hom.1, pi_s_comp0 E, zero_comp0]
  a_π_add_s_b := by
    change (E.π ≫₀ e.hom.1) ≫₀ (e.inv.1 ≫₀ E.a.1) + E.b.1 ≫₀ E.s = A.id y
    rw [comp0_assoc E.π e.hom.1 (e.inv.1 ≫₀ E.a.1),
      ← comp0_assoc e.hom.1 e.inv.1 E.a.1, hom_inv_comp0, id_comp0, split_comp0 E]

/-- The inclusion of `E.transportSub e` is `e.inv` followed by that of `E`. -/
@[simp] theorem transportSub_a {x' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from x) ≅ (show A.Comp from x')) :
    (E.transportSub e).a = A.compCocycle E.a e.inv := rfl

/-- The surjection of `E.transportSub e` is that of `E`. -/
@[simp] theorem transportSub_b {x' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from x) ≅ (show A.Comp from x')) :
    (E.transportSub e).b = E.b := rfl

/-- The projection of `E.transportSub e` is that of `E` followed by `e.hom`. -/
@[simp] theorem transportSub_π {x' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from x) ≅ (show A.Comp from x')) :
    (E.transportSub e).π = A.comp (by omega : (0 : ℤ) + 0 = 0) e.hom.1 E.π := rfl

/-- The splitting of `E.transportSub e` is that of `E`. -/
@[simp] theorem transportSub_s {x' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from x) ≅ (show A.Comp from x')) :
    (E.transportSub e).s = E.s := rfl

/-- The connecting morphism of a sequence transported along an isomorphism `e` of its subobject
is the connecting morphism of the original postcomposed with `e.hom`. -/
public theorem connectingHom_transportSub {x' : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from x) ≅ (show A.Comp from x')) :
    connectingHom (E.transportSub e) =
      A.comp (by omega : (0 : ℤ) + 1 = 1) e.hom.1 (connectingHom E) := by
  change A.comp (by omega : (0 : ℤ) + (0 + 1) = 1)
      (A.comp (by omega : (0 : ℤ) + 0 = 0) e.hom.1 E.π) (A.d E.s) = _
  exact (comp_comp_degree_one e.hom.1 E.π (A.d E.s)).symm

/-! ### Transport along an isomorphism of the middle term -/

/-- The transport of a graded-split short exact sequence `E` over `x, y, z` along an isomorphism
`e : y ≅ y'` of `Comp(A)`: the data `a' = a ≫ e.hom`, `b' = e.inv ≫ b`, `π' = e.inv ≫ π`,
`s' = s ≫ e.hom` (composites in the diagrammatic order), a sequence over `x, y', z`. -/
public def transportMiddle {y' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from y) ≅ (show A.Comp from y')) :
    GradedSplitShortExact (A := A) x y' z where
  a := A.compCocycle e.hom E.a
  b := A.compCocycle E.b e.inv
  π := A.comp (by omega : (0 : ℤ) + 0 = 0) E.π e.inv.1
  s := A.comp (by omega : (0 : ℤ) + 0 = 0) e.hom.1 E.s
  π_a := by
    change (E.a.1 ≫₀ e.hom.1) ≫₀ (e.inv.1 ≫₀ E.π) = A.id x
    rw [comp0_assoc E.a.1 e.hom.1 (e.inv.1 ≫₀ E.π),
      ← comp0_assoc e.hom.1 e.inv.1 E.π, hom_inv_comp0, id_comp0, pi_a_comp0 E]
  b_s := by
    change (E.s ≫₀ e.hom.1) ≫₀ (e.inv.1 ≫₀ E.b.1) = A.id z
    rw [comp0_assoc E.s e.hom.1 (e.inv.1 ≫₀ E.b.1),
      ← comp0_assoc e.hom.1 e.inv.1 E.b.1, hom_inv_comp0, id_comp0, b_s_comp0 E]
  π_s := by
    change (E.s ≫₀ e.hom.1) ≫₀ (e.inv.1 ≫₀ E.π) = 0
    rw [comp0_assoc E.s e.hom.1 (e.inv.1 ≫₀ E.π),
      ← comp0_assoc e.hom.1 e.inv.1 E.π, hom_inv_comp0, id_comp0, pi_s_comp0 E]
  a_π_add_s_b := by
    change (e.inv.1 ≫₀ E.π) ≫₀ (E.a.1 ≫₀ e.hom.1)
        + (e.inv.1 ≫₀ E.b.1) ≫₀ (E.s ≫₀ e.hom.1) = A.id y'
    have h₁ : (e.inv.1 ≫₀ E.π) ≫₀ (E.a.1 ≫₀ e.hom.1) =
        e.inv.1 ≫₀ ((E.π ≫₀ E.a.1) ≫₀ e.hom.1) := by
      rw [comp0_assoc e.inv.1 E.π (E.a.1 ≫₀ e.hom.1), ← comp0_assoc E.π E.a.1 e.hom.1]
    have h₂ : (e.inv.1 ≫₀ E.b.1) ≫₀ (E.s ≫₀ e.hom.1) =
        e.inv.1 ≫₀ ((E.b.1 ≫₀ E.s) ≫₀ e.hom.1) := by
      rw [comp0_assoc e.inv.1 E.b.1 (E.s ≫₀ e.hom.1), ← comp0_assoc E.b.1 E.s e.hom.1]
    rw [h₁, h₂, ← comp0_add, ← add_comp0, split_comp0 E, id_comp0, inv_hom_comp0]

/-- The inclusion of `E.transportMiddle e` is that of `E` followed by `e.hom`. -/
@[simp] theorem transportMiddle_a {y' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from y) ≅ (show A.Comp from y')) :
    (E.transportMiddle e).a = A.compCocycle e.hom E.a := rfl

/-- The surjection of `E.transportMiddle e` is `e.inv` followed by that of `E`. -/
@[simp] theorem transportMiddle_b {y' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from y) ≅ (show A.Comp from y')) :
    (E.transportMiddle e).b = A.compCocycle E.b e.inv := rfl

/-- The projection of `E.transportMiddle e` is `e.inv` followed by that of `E`. -/
@[simp] theorem transportMiddle_π {y' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from y) ≅ (show A.Comp from y')) :
    (E.transportMiddle e).π = A.comp (by omega : (0 : ℤ) + 0 = 0) E.π e.inv.1 := rfl

/-- The splitting of `E.transportMiddle e` is that of `E` followed by `e.hom`. -/
@[simp] theorem transportMiddle_s {y' : A.Obj} (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from y) ≅ (show A.Comp from y')) :
    (E.transportMiddle e).s = A.comp (by omega : (0 : ℤ) + 0 = 0) e.hom.1 E.s := rfl

/-- The connecting morphism is unchanged by transport along an isomorphism of the middle
term. -/
public theorem connectingHom_transportMiddle {y' : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z)
    (e : (show A.Comp from y) ≅ (show A.Comp from y')) :
    connectingHom (E.transportMiddle e) = connectingHom E := by
  have hd : A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) e.hom.1 E.s) =
      A.comp (by omega : (0 : ℤ) + 1 = 1) e.hom.1 (A.d E.s) := by
    simp [A.leibniz, e.hom.2, A.comp_zero_left]
  have step : A.comp (show (0 : ℤ) + 1 = 1 by omega) e.inv.1
      (A.comp (show (0 : ℤ) + 1 = 1 by omega) e.hom.1 (A.d E.s)) = A.d E.s := by
    rw [comp_comp_degree_one, show A.comp (show (0 : ℤ) + 0 = 0 by omega) e.inv.1 e.hom.1 =
      A.id y from hom_inv_comp0 e]
    exact A.id_comp (A.d E.s)
  change A.comp (by omega : (0 : ℤ) + (0 + 1) = 1)
      (A.comp (by omega : (0 : ℤ) + 0 = 0) E.π e.inv.1)
      (A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) e.hom.1 E.s)) = _
  rw [hd, ← comp_comp_degree_one, step]
  exact rfl

end GradedSplitShortExact

end DGCategory

end
