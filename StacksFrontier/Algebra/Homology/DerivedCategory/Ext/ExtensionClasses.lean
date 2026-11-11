module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import StacksFrontier.Algebra.Homology.ShortComplex.Extension
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtOneAndVanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# The Ext-group of isomorphism classes of extensions

Let `𝒜` be an abelian category and `A`, `B` objects of `𝒜`. An extension of `B` by `A` is a
short exact sequence `0 → A → E → B → 0`, and a morphism of extensions is a morphism of the middle
terms compatible with the identities of `A` and `B`; so the extensions of `B` by `A` form a
category (Stacks 010J, `CategoryTheory.Abelian.Extension` in
`StacksFrontier.Algebra.Homology.ShortComplex.Extension`). The set of isomorphism classes of
objects of this category is the Ext-group `Ext_𝒜(B, A)` (Stacks 010K). No size assumption on
`𝒜` is needed to form it.

When `𝒜` has small derived `Ext` groups, the class of a short exact sequence identifies
`Ext_𝒜(B, A)` with the derived group `Ext^1_𝒜(B, A)` (`CategoryTheory.Abelian.Ext B A 1`).

## Main definitions

* `CategoryTheory.Abelian.Extension.isoMk`, `CategoryTheory.Abelian.Extension.isoX`: isomorphisms
  of extensions are the isomorphisms of middle terms compatible with the maps from `A` and to `B`.
* `CategoryTheory.Abelian.YonedaExt`: the set of isomorphism classes of extensions of `B` by `A`.
* `CategoryTheory.Abelian.YonedaExt.equivExt`: its bijection with `Ext B A 1`, induced by
  `CategoryTheory.ShortComplex.ShortExact.extClass`.

## Implementation notes

The Stacks tag 010K is also registered in `StacksCore/` (by `add_to_stacks`) on Mathlib's derived
`CategoryTheory.Abelian.Ext`, in all degrees; that registration is outside the draft and remains.
The declaration stating the definition of 010K is `CategoryTheory.Abelian.YonedaExt`.

## References

* [Stacks Project, Tag 010J](https://stacks.math.columbia.edu/tag/010J)
* [Stacks Project, Tag 010K](https://stacks.math.columbia.edu/tag/010K)
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Extension

variable {B A : C}

/-- An isomorphism of middle terms compatible with the maps from `A` and to `B` is an
isomorphism of extensions. -/
@[simps]
def isoMk {E F : Extension B A} (e : E.X ≅ F.X) (hf : E.f ≫ e.hom = F.f)
    (hg : e.hom ≫ F.g = E.g) : E ≅ F where
  hom := { hom := e.hom }
  inv :=
    { hom := e.inv
      comm_f := by rw [← hf, Category.assoc, e.hom_inv_id, Category.comp_id]
      comm_g := by rw [← hg, e.inv_hom_id_assoc] }

/-- The middle term of an isomorphism of extensions. -/
@[simps]
def isoX {E F : Extension B A} (e : E ≅ F) : E.X ≅ F.X where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := by rw [← comp_hom, e.hom_inv_id, id_hom]
  inv_hom_id := by rw [← comp_hom, e.inv_hom_id, id_hom]

/-- Two extensions are isomorphic exactly when some isomorphism of their middle terms is
compatible with the maps from `A` and to `B`. -/
lemma isIsomorphic_iff {E F : Extension B A} :
    IsIsomorphic E F ↔ ∃ e : E.X ≅ F.X, E.f ≫ e.hom = F.f ∧ e.hom ≫ F.g = E.g :=
  ⟨fun ⟨e⟩ => ⟨isoX e, e.hom.comm_f, e.hom.comm_g⟩,
    fun ⟨e, hf, hg⟩ => ⟨isoMk e hf hg⟩⟩

end Extension

/-- **The Ext-group `Ext_𝒜(B, A)`.** For objects `A`, `B` of an abelian category `𝒜`, the set of
isomorphism classes of extensions `0 → A → E → B → 0` of `B` by `A`, two extensions being
isomorphic when there is an isomorphism of their middle terms compatible with the identities of
`A` and `B`. (Stacks also registers 010K, in `StacksCore/`, on Mathlib's derived
`CategoryTheory.Abelian.Ext`; `YonedaExt.equivExt` identifies the two in degree one.) -/
@[stacks 010K]
def YonedaExt (B A : C) : Type (max u v) :=
  _root_.Quotient (isIsomorphicSetoid (Extension B A))

namespace YonedaExt

variable {B A : C}

/-- The isomorphism class of an extension. -/
def mk (E : Extension B A) : YonedaExt B A := _root_.Quotient.mk _ E

lemma mk_surjective : Function.Surjective (mk (B := B) (A := A)) :=
  _root_.Quotient.mk_surjective

lemma mk_eq_mk_iff {E F : Extension B A} : mk E = mk F ↔ IsIsomorphic E F :=
  _root_.Quotient.eq

section Comparison

variable [HasExt.{w} C]

/-- The map `Ext_𝒜(B, A) → Ext^1_𝒜(B, A)` sending the class of an extension to its derived
extension class `ShortComplex.ShortExact.extClass`. -/
noncomputable def toExt : YonedaExt B A → Ext.{w} B A 1 :=
  _root_.Quotient.lift (fun E : Extension B A => E.shortExact.extClass) fun E F h =>
    ((Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).2.1 E.X F.X E.f E.g E.zero F.f F.g
      F.zero E.shortExact F.shortExact).2 (Extension.isIsomorphic_iff.1 h)

@[simp]
lemma toExt_mk (E : Extension B A) : toExt.{w} (mk E) = E.shortExact.extClass := rfl

lemma toExt_bijective : Function.Bijective (toExt.{w} (B := B) (A := A)) := by
  obtain ⟨hsurj, hinj, -⟩ := Ext.extClass_surjective_and_eq_iff_iso_and_baerSum.{w} C B A
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · obtain ⟨E, rfl⟩ := mk_surjective x
    obtain ⟨F, rfl⟩ := mk_surjective y
    exact mk_eq_mk_iff.2 (Extension.isIsomorphic_iff.2
      ((hinj E.X F.X E.f E.g E.zero F.f F.g F.zero E.shortExact F.shortExact).1 hxy))
  · obtain ⟨X, f, g, w, h, rfl⟩ := hsurj x
    exact ⟨mk ⟨X, f, g, w, h⟩, rfl⟩

/-- **`Ext_𝒜(B, A)` is the derived `Ext^1_𝒜(B, A)`.** The class map of short exact sequences
induces a bijection from the isomorphism classes of extensions of `B` by `A` onto
`CategoryTheory.Abelian.Ext B A 1`. -/
noncomputable def equivExt (B A : C) : YonedaExt B A ≃ Ext.{w} B A 1 :=
  Equiv.ofBijective toExt toExt_bijective

@[simp]
lemma equivExt_mk (E : Extension B A) : equivExt.{w} B A (mk E) = E.shortExact.extClass := rfl

end Comparison

end YonedaExt

end CategoryTheory.Abelian

end
