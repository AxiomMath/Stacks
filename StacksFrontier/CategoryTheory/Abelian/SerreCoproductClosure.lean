module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.SupportedSerreSubcategory

/-!
# The Serre–coproduct closure is transported by an equivalence

`AlgebraicGeometry.serreCoproductClosure A` is the smallest class of objects of an additive
category containing `A` and closed under zero objects, subobjects, quotients, extensions and
arbitrary coproducts.  Every one of those closure conditions is preserved by an equivalence of
abelian categories, so an equivalence `e : C ≌ D` carries the closure of `A` bijectively onto
the closure of `e.functor.obj A`.

## Main results

* `AlgebraicGeometry.serreCoproductClosure_of_iso_generator` and
  `AlgebraicGeometry.serreCoproductClosure_eq_of_iso` — the closure depends on its generator
  only up to isomorphism.
* `AlgebraicGeometry.serreCoproductClosure_map_of_equivalence` — the functor of an equivalence
  maps the closure of `A` into the closure of `e.functor.obj A`.
* `AlgebraicGeometry.mem_serreCoproductClosure_map_iff` — an object lies in the closure of
  `e.functor.obj A` exactly when its preimage lies in the closure of `A`.
* `AlgebraicGeometry.serreCoproductClosure_map_functor` — **the closure of `e.functor.obj A` is
  the inverse image under `e.inverse` of the closure of `A`**, i.e. the equivalence carries the
  one class onto the other, bijectively.
* `AlgebraicGeometry.serreCoproductClosure_map_obj_iff` — the same statement spelled on objects
  of the source category.

## Implementation notes

`AlgebraicGeometry.serreCoproductClosure` is defined as the intersection of all classes having
the six closure properties, not by a transfinite construction, so no induction principle is
needed to transport it: given a class `P` in the target with the six properties, its inverse
image `P.inverseImage e.functor` has the six properties in the source, and that is the whole
proof.  Mathlib supplies each of the six transports as an instance on
`CategoryTheory.ObjectProperty.inverseImage`, the hypotheses on the functor being preservation
of zero morphisms, monomorphisms, epimorphisms, finite limits, finite colimits and discrete
colimits — all of which hold for the functor of an equivalence, and are found by instance
search from `CategoryTheory.Adjunction.isEquivalence_preservesColimits` and its dual.

The contents are pure category theory, which is why the file sits here; the declarations stay
in the `AlgebraicGeometry` namespace because that is where
`AlgebraicGeometry.serreCoproductClosure` itself is declared, next to [Stacks, Tag 0GPG].

## References

* [Stacks Project, Lemma 56.2.2 (Tag 0GPG)](https://stacks.math.columbia.edu/tag/0GPG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {C : Type (u + 1)} [Category.{u} C] {D : Type (u + 1)} [Category.{u} D]

section Preadditive

variable [Preadditive C]

/-- The Serre–coproduct closure of a generator is closed under isomorphisms of objects: each
class it is intersected over is closed under subobjects, hence under isomorphisms. -/
theorem serreCoproductClosure_prop_of_iso {A E E' : C} (i : E ≅ E')
    (hE : serreCoproductClosure A E) : serreCoproductClosure A E' := by
  intro P hA hzero hsub hquot hext hcop
  exact P.prop_of_iso i (hE P hA hzero hsub hquot hext hcop)

/-- The generator of a Serre–coproduct closure may be replaced by an isomorphic object. -/
theorem serreCoproductClosure_of_iso_generator {A A' E : C} (i : A ≅ A')
    (hE : serreCoproductClosure A E) : serreCoproductClosure A' E := by
  intro P hA' hzero hsub hquot hext hcop
  exact hE P (P.prop_of_iso i.symm hA') hzero hsub hquot hext hcop

/-- Isomorphic generators have the same Serre–coproduct closure. -/
theorem serreCoproductClosure_eq_of_iso {A A' : C} (i : A ≅ A') :
    serreCoproductClosure A = serreCoproductClosure A' := by
  ext E
  exact ⟨serreCoproductClosure_of_iso_generator i, serreCoproductClosure_of_iso_generator i.symm⟩

end Preadditive

section Equivalence

variable [Abelian C] [Abelian D]

/-- **The functor of an equivalence maps the Serre–coproduct closure of `A` into the
Serre–coproduct closure of the image of `A`.** Given a class `P` in the target with the six
closure properties defining `AlgebraicGeometry.serreCoproductClosure`, its inverse image under
the functor has the same six properties in the source, because an equivalence preserves zero
morphisms, monomorphisms, epimorphisms, short exact sequences and arbitrary coproducts. -/
theorem serreCoproductClosure_map_of_equivalence (e : C ≌ D) {A E : C}
    (hE : serreCoproductClosure A E) :
    serreCoproductClosure (e.functor.obj A) (e.functor.obj E) := by
  intro P hA _ _ _ _ hcop
  refine hE (P.inverseImage e.functor) hA ?_ ?_ ?_ ?_ fun ι ↦ ?_ <;> infer_instance

/-- An object of the target lies in the Serre–coproduct closure of `e.functor.obj A` exactly
when its preimage lies in the Serre–coproduct closure of `A`. -/
theorem mem_serreCoproductClosure_map_iff (e : C ≌ D) (A : C) (E' : D) :
    serreCoproductClosure (e.functor.obj A) E' ↔
      serreCoproductClosure A (e.inverse.obj E') :=
  ⟨fun h ↦ serreCoproductClosure_of_iso_generator (e.unitIso.app A).symm
      (serreCoproductClosure_map_of_equivalence e.symm h),
    fun h ↦ serreCoproductClosure_prop_of_iso (e.counitIso.app E')
      (serreCoproductClosure_map_of_equivalence e h)⟩

/-- **An equivalence of abelian categories carries the Serre–coproduct closure of `A` onto the
Serre–coproduct closure of `e.functor.obj A`, bijectively**: the latter class is the inverse
image of the former along the inverse equivalence. -/
theorem serreCoproductClosure_map_functor (e : C ≌ D) (A : C) :
    serreCoproductClosure (e.functor.obj A) =
      (serreCoproductClosure A).inverseImage e.inverse := by
  ext E'
  exact mem_serreCoproductClosure_map_iff e A E'

/-- An object of the source lies in the Serre–coproduct closure of `A` exactly when its image
lies in the Serre–coproduct closure of the image of `A`. -/
theorem serreCoproductClosure_map_obj_iff (e : C ≌ D) (A E : C) :
    serreCoproductClosure (e.functor.obj A) (e.functor.obj E) ↔
      serreCoproductClosure A E :=
  (mem_serreCoproductClosure_map_iff e A (e.functor.obj E)).trans
    ⟨serreCoproductClosure_prop_of_iso (e.unitIso.app E).symm,
      serreCoproductClosure_prop_of_iso (e.unitIso.app E)⟩

end Equivalence

end AlgebraicGeometry

end
