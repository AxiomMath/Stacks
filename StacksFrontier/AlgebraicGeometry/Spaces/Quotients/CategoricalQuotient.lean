module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms

/-!
# Categorical quotients of a pre-relation

A morphism `φ : U ⟶ X` is a *categorical quotient* of a pre-relation `j : R ⟶ U ×_B U` when
it is invariant under `j` and every invariant morphism out of `U` factors uniquely through it.
The same universal property may be imposed only against the objects of a full subcategory, and
it may be imposed in the category of schemes over a base scheme.

A categorical quotient, when it exists, is unique up to a unique isomorphism compatible with
the quotient maps — in the ambient category and in a full subcategory alike.

## Main definitions

* `AlgebraicGeometry.Space.IsCategoricalQuotient`: the quotient property among algebraic spaces
  over the base.
* `AlgebraicGeometry.Space.IsCategoricalQuotientIn`: the quotient property in the full
  subcategory cut out by an object property.
* `AlgebraicGeometry.Space.IsCategoricalQuotientInSchemes`: the quotient property among schemes
  over a base scheme.

## Main results

* `AlgebraicGeometry.Space.categoricalQuotient_unique`: two categorical quotients of one
  pre-relation are uniquely isomorphic over the base, compatibly with their quotient maps.
* `AlgebraicGeometry.Space.categoricalQuotientIn_unique`: the same in a full subcategory.

## References

* [Stacks Project, Tag 048J](https://stacks.math.columbia.edu/tag/048J)
* [Stacks Project, Tag 048K](https://stacks.math.columbia.edu/tag/048K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {B : AlgebraicSpaces site S hS}

/-! ### The three quotient properties -/

/-- A morphism `φ : U ⟶ X` of algebraic spaces over `B` is a *categorical quotient* of a
pre-relation `j` when it is invariant under `j` and every invariant morphism out of `U` factors
uniquely through it. -/
@[stacks 048J "part (1): algebraic spaces",
  stacks 049V "items (2)-(5): the separated, quasi-separated, locally separated and decent"]
noncomputable abbrev IsCategoricalQuotient {R U X : Over B} (j : PreRelation R U)
    (φ : U ⟶ X) : Prop :=
  IsInvariant j φ.left ∧
    ∀ (Y : Over B) (ψ : U ⟶ Y), IsInvariant j ψ.left → ∃! χ : X ⟶ Y, φ ≫ χ = ψ

/-- A morphism `φ : U ⟶ X` is a *categorical quotient in the full subcategory* cut out by an object
property `P` when `R`, `U` and `X` lie in it and the universal property of a categorical quotient
holds against the objects of `P`. -/
@[stacks 048J "part (2): full subcategory",
  stacks 049V "items (2)-(5): the separated, quasi-separated, locally separated and decent"]
noncomputable abbrev IsCategoricalQuotientIn (P : ObjectProperty (Over B)) {R U X : Over B}
    (j : PreRelation R U) (φ : U ⟶ X) : Prop :=
  P R ∧ P U ∧ P X ∧ IsInvariant j φ.left ∧
    ∀ (Y : Over B), P Y → ∀ (ψ : U ⟶ Y), IsInvariant j ψ.left → ∃! χ : X ⟶ Y, φ ≫ χ = ψ

/-- A morphism `φ : U ⟶ X` of schemes over `T` is a *categorical quotient* of a pre-relation of
schemes when it equalizes the target and the source of the pre-relation and every morphism out of
`U` which does so factors uniquely through it. -/
@[stacks 048J "part (3): schemes",
  stacks 049V "items (2)-(5): the separated, quasi-separated, locally separated and decent"]
noncomputable abbrev IsCategoricalQuotientInSchemes {T : Scheme.{u}} {R U X : Over T}
    (j : Stacks.Groupoids.PreRelation R U) (φ : U ⟶ X) : Prop :=
  (j.target ≫ φ = j.source ≫ φ) ∧
    ∀ (Y : Over T) (ψ : U ⟶ Y), (j.target ≫ ψ = j.source ≫ ψ) → ∃! χ : X ⟶ Y, φ ≫ χ = ψ

/-! ### Uniqueness -/

/-- Two objects with the same universal property against a class of test objects, for one class of
admissible morphisms out of `U`, are uniquely isomorphic compatibly with the admissible morphisms
to them. -/
@[sga "3 IV 3.1.2" "partial"]
private theorem unique_iso_of_universal {C : Type*} [Category C] {U X Y : C}
    (P : ObjectProperty C) (Q : ∀ Z : C, (U ⟶ Z) → Prop) (hX : P X) (hY : P Y)
    (φ : U ⟶ X) (ψ : U ⟶ Y) (hφ : Q X φ) (hψ : Q Y ψ)
    (uφ : ∀ Z, P Z → ∀ g : U ⟶ Z, Q Z g → ∃! χ : X ⟶ Z, φ ≫ χ = g)
    (uψ : ∀ Z, P Z → ∀ g : U ⟶ Z, Q Z g → ∃! χ : Y ⟶ Z, ψ ≫ χ = g) :
    ∃! e : X ≅ Y, φ ≫ e.hom = ψ := by
  obtain ⟨p, hp, -⟩ := uφ Y hY ψ hψ
  obtain ⟨q, hq, -⟩ := uψ X hX φ hφ
  have hpq : p ≫ q = 𝟙 X :=
    ((uφ X hX φ hφ).unique (by simp) (by simp [← Category.assoc, hp, hq])).symm
  have hqp : q ≫ p = 𝟙 Y :=
    ((uψ Y hY ψ hψ).unique (by simp) (by simp [← Category.assoc, hq, hp])).symm
  exact ⟨⟨p, q, hpq, hqp⟩, hp, fun e he ↦ Iso.ext ((uφ Y hY ψ hψ).unique hp he).symm⟩

/-- Two categorical quotients of a pre-relation of algebraic spaces over `B` are uniquely
isomorphic over `B`, compatibly with their quotient maps. -/
@[stacks 048K "algebraic spaces over the base"]
theorem categoricalQuotient_unique {R U X Y : Over B} (j : PreRelation R U) (φ : U ⟶ X)
    (ψ : U ⟶ Y) (hφ : IsCategoricalQuotient j φ) (hψ : IsCategoricalQuotient j ψ) :
    ∃! e : X ≅ Y, φ ≫ e.hom = ψ :=
  unique_iso_of_universal (fun _ ↦ True) (fun (Z : Over B) (g : U ⟶ Z) ↦ IsInvariant j g.left)
    trivial trivial φ ψ hφ.1 hψ.1 (fun Z _ ↦ hφ.2 Z) (fun Z _ ↦ hψ.2 Z)

/-- Two categorical quotients of a pre-relation in the full subcategory cut out by an object
property are uniquely isomorphic within that subcategory, compatibly with their quotient maps. -/
@[stacks 048K "full subcategories"]
theorem categoricalQuotientIn_unique (P : ObjectProperty (Over B)) {R U X Y : Over B}
    (j : PreRelation R U) (φ : U ⟶ X) (ψ : U ⟶ Y)
    (hφ : IsCategoricalQuotientIn P j φ) (hψ : IsCategoricalQuotientIn P j ψ) :
    ∃! e : X ≅ Y, φ ≫ e.hom = ψ :=
  unique_iso_of_universal P (fun (Z : Over B) (g : U ⟶ Z) ↦ IsInvariant j g.left)
    hφ.2.2.1 hψ.2.2.1 φ ψ hφ.2.2.2.1 hψ.2.2.2.1 hφ.2.2.2.2 hψ.2.2.2.2

end AlgebraicGeometry.Space

end
