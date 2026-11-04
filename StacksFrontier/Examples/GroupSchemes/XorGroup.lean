module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Group schemes built by multiplying component labels modulo two

A scheme `G` over `S` which is covered by two pieces, each of which is a subobject of the base,
carries a group law over `S` as soon as the two pieces can be multiplied by adding their labels
in `ZMod 2`: the piece labelled `false` is the identity component and the piece labelled `true`
is a copy of it that each element of the group interchanges with the other.

`Stacks.Examples.XorGroupPresentation` packages what such a presentation consists of: the two
pieces together with their inclusions into `G`, the multiplication on `G`, the equation
describing it on pieces, and the assertion that two morphisms out of an `S`-scheme agree as soon
as they agree after restricting to the preimage of each piece. Out of that
`Stacks.Examples.XorGroupPresentation.grpObj` builds the group object.

## Main definitions

* `Stacks.Examples.tensorLeftToPullback`: the underlying scheme of a product in a slice category,
  compared with the fibre product of the two structure morphisms.
* `Stacks.Examples.XorGroupPresentation`: the data presenting a group scheme in this way.
* `Stacks.Examples.XorGroupPresentation.grpObj`: the resulting group object over `S`.

## Implementation notes

That each piece is a subobject of the base — a monomorphism to `S` in the slice category — is
what makes the group axioms automatic: any two morphisms from a fixed `S`-scheme into a single
piece coincide, so after restricting to pieces there is nothing left to check beyond
associativity of `xor` on labels. This is `XorGroupPresentation.part_hom_ext`, and it is used in
place of any computation with the multiplication.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

universe u

namespace Stacks.Examples

/-- The comparison morphism from the underlying scheme of a product in the category of schemes
over `S` to the fibre product of the two structure morphisms. -/
public noncomputable def tensorLeftToPullback {S : Scheme.{u}} (X Y : CategoryTheory.Over S) :
    (X ⊗ Y).left ⟶ pullback X.hom Y.hom :=
  pullback.lift (fst X Y).left (snd X Y).left ((fst X Y).w.trans (snd X Y).w.symm)

/-- The comparison morphism followed by the first projection of the fibre product is the first
projection of the product. -/
public lemma tensorLeftToPullback_comp_fst {S : Scheme.{u}} (X Y : CategoryTheory.Over S) :
    tensorLeftToPullback X Y ≫ pullback.fst X.hom Y.hom = (fst X Y).left :=
  pullback.lift_fst _ _ _

/-- The comparison morphism followed by the second projection of the fibre product is the second
projection of the product. -/
public lemma tensorLeftToPullback_comp_snd {S : Scheme.{u}} (X Y : CategoryTheory.Over S) :
    tensorLeftToPullback X Y ≫ pullback.snd X.hom Y.hom = (snd X Y).left :=
  pullback.lift_snd _ _ _

/-- A presentation of a scheme over `S` as a union of two pieces, each a subobject of `S`,
with a multiplication that adds the labels of the pieces modulo two. -/
public structure XorGroupPresentation (S : Scheme.{u}) where
  /-- The scheme over `S` that is being presented. -/
  carrier : CategoryTheory.Over S
  /-- The two pieces covering the carrier, labelled by `Bool`. -/
  part : Bool → CategoryTheory.Over S
  /-- Each piece is a subobject of the base. -/
  mono_part_hom : ∀ b, Mono (part b).hom
  /-- The inclusion of a piece into the carrier. -/
  partHom : ∀ b, part b ⟶ carrier
  /-- The piece labelled `false` is a terminal object of the slice category. -/
  partUnit : ∀ T : CategoryTheory.Over S, T ⟶ part false
  /-- Two morphisms into pieces multiply to a morphism into the piece labelled by their
  `xor`. -/
  partMul : ∀ {T : CategoryTheory.Over S} (b c : Bool),
    (T ⟶ part b) → (T ⟶ part c) → (T ⟶ part (b ^^ c))
  /-- The multiplication of the group law. -/
  mul : carrier ⊗ carrier ⟶ carrier
  /-- On a pair of morphisms factoring through pieces, the multiplication adds the labels. -/
  lift_partHom_comp_mul : ∀ {T : CategoryTheory.Over S} (b c : Bool)
    (f : T ⟶ part b) (g : T ⟶ part c),
    lift (f ≫ partHom b) (g ≫ partHom c) ≫ mul = partMul b c f g ≫ partHom (b ^^ c)
  /-- Two morphisms out of `T` agree once they agree after restricting along any morphism to
  `T` that sends a given morphism `T ⟶ carrier` into a piece. -/
  hom_ext : ∀ {T Z : CategoryTheory.Over S} (f : T ⟶ carrier) (g h : T ⟶ Z),
    (∀ (b : Bool) (V : CategoryTheory.Over S) (a : V ⟶ T) (t : V ⟶ part b),
      a ≫ f = t ≫ partHom b → a ≫ g = a ≫ h) → g = h

namespace XorGroupPresentation

variable {S : Scheme.{u}} (P : XorGroupPresentation S)

/-- Any two morphisms from a fixed object of the slice category into a single piece agree. -/
public lemma part_hom_ext {T : CategoryTheory.Over S} (b : Bool) (f g : T ⟶ P.part b) :
    f = g := by
  have := P.mono_part_hom b
  exact Over.OverMorphism.ext ((cancel_mono (P.part b).hom).mp (f.w.trans g.w.symm))

/-- Two morphisms into the carrier that factor through pieces with equal labels agree. -/
public lemma comp_partHom_congr {T : CategoryTheory.Over S} {b c : Bool} (h : b = c)
    (f : T ⟶ P.part b) (g : T ⟶ P.part c) : f ≫ P.partHom b = g ≫ P.partHom c := by
  subst h
  exact congrArg (· ≫ P.partHom b) (P.part_hom_ext b f g)

/-- The product of two morphisms into the carrier, computed by the presented multiplication. -/
public noncomputable abbrev prod {T : CategoryTheory.Over S} (f g : T ⟶ P.carrier) :
    T ⟶ P.carrier :=
  lift f g ≫ P.mul

/-- The identity section of the group law: the inclusion of the piece labelled `false`. -/
public noncomputable def one : 𝟙_ (CategoryTheory.Over S) ⟶ P.carrier :=
  P.partUnit _ ≫ P.partHom false

/-- Precomposition distributes over the product of morphisms into the carrier. -/
public lemma comp_prod {T V : CategoryTheory.Over S} (a : V ⟶ T) (f g : T ⟶ P.carrier) :
    a ≫ P.prod f g = P.prod (a ≫ f) (a ≫ g) := by
  simp only [prod, comp_lift_assoc]

/-- The morphisms into the piece labelled `false` are compatible with precomposition. -/
public lemma comp_partUnit {T V : CategoryTheory.Over S} (a : V ⟶ T) :
    a ≫ P.partUnit T = P.partUnit V :=
  P.part_hom_ext _ _ _

/-- The product of morphisms through pieces lies in the piece labelled by the `xor` of labels. -/
private lemma prod_partHom_eq {T : CategoryTheory.Over S} {b c d : Bool} (h : (b ^^ c) = d)
    {f : T ⟶ P.part b} {g : T ⟶ P.part c} {k : T ⟶ P.part d} :
    P.prod (f ≫ P.partHom b) (g ≫ P.partHom c) = k ≫ P.partHom d := by
  simp only [prod, P.lift_partHom_comp_mul]
  exact P.comp_partHom_congr h _ _

/-- The identity section is a left unit for the product. -/
public lemma prod_one_left {T : CategoryTheory.Over S} (f : T ⟶ P.carrier) :
    P.prod (P.partUnit T ≫ P.partHom false) f = f := by
  refine P.hom_ext f _ _ fun b V a t hab => ?_
  rw [P.comp_prod, hab, ← Category.assoc, P.comp_partUnit]
  exact P.prod_partHom_eq (Bool.false_xor b)

/-- The identity section is a right unit for the product. -/
public lemma prod_one_right {T : CategoryTheory.Over S} (f : T ⟶ P.carrier) :
    P.prod f (P.partUnit T ≫ P.partHom false) = f := by
  refine P.hom_ext f _ _ fun b V a t hab => ?_
  rw [P.comp_prod, hab, ← Category.assoc, P.comp_partUnit]
  exact P.prod_partHom_eq (Bool.xor_false b)

/-- Every morphism into the carrier is its own inverse for the product. -/
public lemma prod_self {T : CategoryTheory.Over S} (f : T ⟶ P.carrier) :
    P.prod f f = P.partUnit T ≫ P.partHom false := by
  refine P.hom_ext f _ _ fun b V a t hab => ?_
  rw [P.comp_prod, hab, ← Category.assoc, P.comp_partUnit]
  exact P.prod_partHom_eq (Bool.xor_self b)

/-- Associativity for three morphisms each factoring through a piece. -/
private lemma prod_assoc_parts {T : CategoryTheory.Over S} (b c d : Bool)
    (f : T ⟶ P.part b) (g : T ⟶ P.part c) (h : T ⟶ P.part d) :
    P.prod (P.prod (f ≫ P.partHom b) (g ≫ P.partHom c)) (h ≫ P.partHom d) =
      P.prod (f ≫ P.partHom b) (P.prod (g ≫ P.partHom c) (h ≫ P.partHom d)) := by
  simp only [prod, P.lift_partHom_comp_mul]
  exact P.comp_partHom_congr (Bool.xor_assoc b c d) _ _

/-- The product of morphisms into the carrier is associative. -/
public lemma prod_assoc {T : CategoryTheory.Over S} (f g h : T ⟶ P.carrier) :
    P.prod (P.prod f g) h = P.prod f (P.prod g h) := by
  refine P.hom_ext f _ _ fun b V a f' hf => ?_
  simp only [P.comp_prod, hf]
  refine P.hom_ext (a ≫ g) _ _ fun c W a' g' hg => ?_
  simp only [P.comp_prod, hg]
  refine P.hom_ext (a' ≫ a ≫ h) _ _ fun d Z a'' h' hh => ?_
  simp only [P.comp_prod, hh]
  simpa only [← Category.assoc] using
    P.prod_assoc_parts b c d (a'' ≫ a' ≫ f') (a'' ≫ g') h'

/-- The group object over `S` presented by the data: multiplication adds the labels of the two
pieces modulo two, so every element is its own inverse. -/
@[instance_reducible]
public noncomputable def grpObj : GrpObj P.carrier where
  one := P.one
  mul := P.mul
  one_mul := by
    have h : P.one ▷ P.carrier =
        lift (P.partUnit (𝟙_ (CategoryTheory.Over S) ⊗ P.carrier) ≫ P.partHom false)
          (snd (𝟙_ (CategoryTheory.Over S)) P.carrier) := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ (by simp)
      rw [whiskerRight_fst, lift_fst, one, ← Category.assoc, P.comp_partUnit]
    rw [h]
    exact (P.prod_one_left _).trans (leftUnitor_hom P.carrier).symm
  mul_one := by
    have h : P.carrier ◁ P.one =
        lift (fst P.carrier (𝟙_ (CategoryTheory.Over S)))
          (P.partUnit (P.carrier ⊗ 𝟙_ (CategoryTheory.Over S)) ≫ P.partHom false) := by
      refine CartesianMonoidalCategory.hom_ext _ _ (by simp) ?_
      rw [whiskerLeft_snd, lift_snd, one, ← Category.assoc, P.comp_partUnit]
    rw [h]
    exact (P.prod_one_right _).trans (rightUnitor_hom P.carrier).symm
  mul_assoc := by
    have h := P.prod_assoc (fst (P.carrier ⊗ P.carrier) P.carrier ≫ fst P.carrier P.carrier)
      (fst (P.carrier ⊗ P.carrier) P.carrier ≫ snd P.carrier P.carrier)
      (snd (P.carrier ⊗ P.carrier) P.carrier)
    have hleft : P.mul ▷ P.carrier =
        lift (P.prod (fst (P.carrier ⊗ P.carrier) P.carrier ≫ fst P.carrier P.carrier)
          (fst (P.carrier ⊗ P.carrier) P.carrier ≫ snd P.carrier P.carrier))
          (snd (P.carrier ⊗ P.carrier) P.carrier) := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ (by simp)
      simp only [whiskerRight_fst, lift_fst, prod, ← comp_lift, lift_fst_snd, Category.comp_id]
    have hright : (α_ P.carrier P.carrier P.carrier).hom ≫ P.carrier ◁ P.mul =
        lift (fst (P.carrier ⊗ P.carrier) P.carrier ≫ fst P.carrier P.carrier)
          (P.prod (fst (P.carrier ⊗ P.carrier) P.carrier ≫ snd P.carrier P.carrier)
            (snd (P.carrier ⊗ P.carrier) P.carrier)) := by
      refine CartesianMonoidalCategory.hom_ext _ _ (by simp) ?_
      simp only [Category.assoc, whiskerLeft_snd, lift_snd, prod]
      rw [← Category.assoc]
      exact congrArg (· ≫ P.mul)
        (CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp))
    rw [hleft, ← Category.assoc, hright]
    exact h
  inv := 𝟙 _
  left_inv := by
    rw [one, ← Category.assoc, P.comp_partUnit]
    exact P.prod_self (𝟙 P.carrier)
  right_inv := by
    rw [one, ← Category.assoc, P.comp_partUnit]
    exact P.prod_self (𝟙 P.carrier)

end XorGroupPresentation

end Stacks.Examples

end
