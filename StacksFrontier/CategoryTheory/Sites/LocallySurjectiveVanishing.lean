module

public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Transporting vanishing of sections along a locally surjective morphism

Let `(C, J)` be a site and let `P` be a property of the objects of `C` with the following
refinement property: every covering sieve of an object with the property contains a family which
still generates a covering sieve and all of whose sources have the property. Call such a `P`
*covering-refinable*. The example to keep in mind is flatness of an object of an algebraic stack
(**Stacks 0787**): the morphisms of a covering family lie over flat morphisms of schemes, so a
covering family of a flat object may be taken to consist of flat objects, while an arbitrary
morphism into a flat object has no reason to have a flat source.

For such a `P`, vanishing of the sections at the objects with the property passes along any
locally surjective morphism of presheaves whose target is separated. That is the single statement
proved here, and it has the two consequences the Serre property of the parasitic modules
(**Stacks 0774** (2)) is assembled from: applied to the unit of sheafification it says that
sheafifying preserves the vanishing, and applied to an epimorphism of sheaves it says that a
quotient inherits it.

The argument is the obvious one. Two sections `a`, `b` of the target at an object `y` with `P y`
are locally in the image of the source, each on a covering sieve of `y`; intersect the two sieves
and refine, by the hypothesis on `P`, to a family whose sources have the property. Along a member
of that family both `a` and `b` become images of sections of the source, and those sections live
in a vanishing module, so they agree; hence `a` and `b` agree along the whole sieve the family
generates, which covers, and a separated presheaf has at most one section restricting to a given
family.

## Main definitions

* `CategoryTheory.Presheaf.IsCoveringRefinable`: the refinement property of an object property
  described above.

## Main results

* `CategoryTheory.Presheaf.subsingleton_obj_of_isLocallySurjective`: the transport of vanishing.

## Implementation notes

Vanishing is expressed as `Subsingleton` of the type of sections rather than as an equality with a
zero object, so no additive structure on the value category is used: the proof compares two
sections directly and never names `0`. The value category is therefore an arbitrary concrete
category, and the hypothesis on the target is Mathlib's `CategoryTheory.Presheaf.IsSeparated`,
which a sheaf satisfies by `CategoryTheory.Sheaf.isSeparated`.

The refinement hypothesis asks for a *presieve* `T` inside the given sieve, together with the
covering of the sieve `T` generates, rather than for a subsieve: the families that arise in
practice — the covering families of a site presented by a precoverage — are presieves, and the
sieve they generate consists of their members precomposed with arbitrary morphisms, whose sources
need not have the property. Only the members of `T` are therefore required to have it, and the
passage to the generated sieve is done inside the proof, where restricting along the extra factor
is harmless.
-/

@[expose] public section

open Opposite

namespace CategoryTheory.Presheaf

universe w' v' u' v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- An object property `P` on a site is *covering-refinable* when every covering sieve of an
object satisfying `P` contains a family which generates a covering sieve and all of whose members
have a source satisfying `P`.

This is the property that makes vanishing of sections at the `P`-objects stable under
sheafification; see `CategoryTheory.Presheaf.subsingleton_obj_of_isLocallySurjective`. -/
def IsCoveringRefinable (P : ObjectProperty C) : Prop :=
  ∀ ⦃y : C⦄, P y → ∀ S : Sieve y, S ∈ J y →
    ∃ T : Presieve y, T ≤ S.arrows ∧ Sieve.generate T ∈ J y ∧
      ∀ ⦃z : C⦄ ⦃f : z ⟶ y⦄, T f → P z

variable {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]

/-- **Vanishing of sections at a covering-refinable family of objects passes along a locally
surjective morphism into a separated presheaf.** If `φ : F ⟶ G` is locally surjective for `J`,
the presheaf `G` is separated, the object property `P` is covering-refinable, and the sections of
`F` vanish at every object satisfying `P`, then so do the sections of `G`. -/
theorem subsingleton_obj_of_isLocallySurjective {F G : Cᵒᵖ ⥤ A} (φ : F ⟶ G)
    [IsLocallySurjective J φ] (hG : IsSeparated J G) {P : ObjectProperty C}
    (hP : IsCoveringRefinable J P)
    (hF : ∀ ⦃z : C⦄, P z → Subsingleton (ToType (F.obj (op z))))
    {y : C} (hy : P y) : Subsingleton (ToType (G.obj (op y))) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨T, hTS, hTcov, hTP⟩ := hP hy _
    (J.intersection_covering (imageSieve_mem J φ a) (imageSieve_mem J φ b))
  refine hG y _ hTcov a b ?_
  rintro Z f ⟨W, g, h, hh, rfl⟩
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := hTS _ _ hh
  have hst : G.map h.op a = G.map h.op b := by
    rw [← hs, ← ht, (hF (hTP hh)).elim s t]
  rw [op_comp, G.map_comp, comp_apply, comp_apply, hst]

end CategoryTheory.Presheaf

end
