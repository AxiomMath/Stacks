module

public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily
public import Mathlib.CategoryTheory.Sites.Closed

/-!
# Conservative families of points are those whose germs separate sections

Let `(C, J)` be a site and `{p_i}_{i ∈ I}` a family of points of it. Stacks 00YM says that the
family is conservative (Stacks 00YK (1)) if and only if for every sheaf of sets `F`, every object
`U` and every pair of distinct sections `s ≠ s'` of `F` over `U`, there are an index `i` and an
element `x ∈ u_i(U)` such that the triples `(U, x, s)` and `(U, x, s')` define distinct elements of
the stalk `F_{p_i}`.

## Main results

* `CategoryTheory.GrothendieckTopology.isConservativeFamily_iff_exists_toPresheafFiber_ne`:
  Stacks 00YM, for a family of points `p : ι → J.Point` indexed by an arbitrary type.
* `CategoryTheory.ObjectProperty.isConservativeFamilyOfPoints_iff_exists_toPresheafFiber_ne`:
  the same equivalence for a family given as a predicate `P : ObjectProperty J.Point`, in terms of
  Mathlib's `ObjectProperty.IsConservativeFamilyOfPoints`.
* `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.exists_toPresheafFiber_ne` and
  `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.of_exists_toPresheafFiber_ne`: the
  two directions.

## Implementation notes

* A point of the site is Mathlib's `GrothendieckTopology.Point`, the notion this library uses for
  Stacks 00Y5 (see `StacksFrontier/CategoryTheory/Sites/Point/Basic.lean`); conservativity is the
  library's `IsConservativeFamily` of Stacks 00YK (1). The element of `F_{p}` defined by the triple
  `(U, x, s)` is the germ `Φ.toPresheafFiber U x F.obj s`, the coprojection of `s` into the
  colimit over the neighbourhoods of the point.
* The site is small, `C : Type w` with morphisms in `Type w`, and points and sheaves take values in
  `Type w`: this is the source's setting, where a site has a set of objects and sheaves are
  sheaves of sets.
* The proof differs from the source's, which passes through the sheafification `(h_U)^#` and the
  pushout `G ⨿_F G` of sheaves. The forward direction applies conservativity in the form of
  Mathlib's `IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem` to the equalizer sieve of
  `s` and `s'`: if their germs agree at every point, every neighbourhood of every point of the
  family factors through that sieve, so it covers, and `s = s'` since `F` is separated. For the
  converse, the separation condition applied to the sheaf of `J`-closed sieves and its sections
  `⊤` and `J.close S` shows that a sieve `S` through which every neighbourhood of every point
  factors is covering; that is the criterion of SGA 4 IV 6.5 (a), which is Mathlib's
  `IsConservativeFamilyOfPoints.mk'`.
-/

@[expose] public section

namespace CategoryTheory

open Opposite Limits

universe w t

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}

namespace GrothendieckTopology

/-- The sheaf of `J`-closed sieves, `V ↦ {S : Sieve V | J.IsClosed S}`, as an object of
`Sheaf J (Type w)` for a small site. -/
noncomputable def closedSievesSheaf (J : GrothendieckTopology C) : Sheaf J (Type w) :=
  ⟨(Functor.closedSieves J).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2 (classifier_isSheaf J)⟩

end GrothendieckTopology

namespace ObjectProperty

variable {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}

/-- If the germs at the points of `P` separate distinct sections of every sheaf of sets, then a
sieve `S` on `X` is covering as soon as every neighbourhood `(X, x)` of every point of `P` factors
through `S`. -/
theorem mem_of_exists_toPresheafFiber_ne
    (hP : ∀ (F : Sheaf J (Type w)) (U : C) (s s' : F.obj.obj (op U)), s ≠ s' →
      ∃ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj U),
        Φ.obj.toPresheafFiber U x F.obj s ≠ Φ.obj.toPresheafFiber U x F.obj s')
    {X : C} (S : Sieve X)
    (hS : ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
      ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : Φ.obj.fiber.obj Y), Φ.obj.fiber.map g y = x) :
    S ∈ J X := by
  rw [← J.close_eq_top_iff_mem]
  by_contra h
  have htop : J.IsClosed (⊤ : Sieve X) := fun _ _ _ ↦ trivial
  obtain ⟨Φ, x, hx⟩ := hP (GrothendieckTopology.closedSievesSheaf J) X
    ⟨J.close S, J.close_isClosed S⟩ ⟨(⊤ : Sieve X), htop⟩ (fun e ↦ h (congrArg Subtype.val e))
  apply hx
  obtain ⟨Y, g, hg, y, rfl⟩ := hS Φ x
  have hpull : (GrothendieckTopology.closedSievesSheaf J).obj.map g.op
      ⟨J.close S, J.close_isClosed S⟩ =
      (GrothendieckTopology.closedSievesSheaf J).obj.map g.op ⟨(⊤ : Sieve X), htop⟩ := by
    apply Subtype.ext
    change (J.close S).pullback g = (⊤ : Sieve X).pullback g
    rw [Sieve.pullback_top, ← J.pullback_close, S.pullback_eq_top_of_mem hg,
      J.close_eq_top_iff_mem]
    exact J.top_mem Y
  have key := ConcreteCategory.congr_hom
    (Φ.obj.toPresheafFiber_w g y (GrothendieckTopology.closedSievesSheaf J).obj)
  refine (key _).symm.trans (Eq.trans ?_ (key _))
  exact congrArg (ConcreteCategory.hom
    (Φ.obj.toPresheafFiber Y y (GrothendieckTopology.closedSievesSheaf J).obj)) hpull

/-- If the germs at the points of `P` separate distinct sections of every sheaf of sets, then `P`
is a conservative family of points. This is the converse direction of Stacks 00YM. -/
theorem IsConservativeFamilyOfPoints.of_exists_toPresheafFiber_ne
    (hP : ∀ (F : Sheaf J (Type w)) (U : C) (s s' : F.obj.obj (op U)), s ≠ s' →
      ∃ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj U),
        Φ.obj.toPresheafFiber U x F.obj s ≠ Φ.obj.toPresheafFiber U x F.obj s') :
    P.IsConservativeFamilyOfPoints :=
  IsConservativeFamilyOfPoints.mk' (fun _ S hS ↦ mem_of_exists_toPresheafFiber_ne hP S hS)

/-- The germs at the points of a conservative family separate distinct sections of every sheaf of
sets. This is the forward direction of Stacks 00YM. -/
theorem IsConservativeFamilyOfPoints.exists_toPresheafFiber_ne
    (hP : P.IsConservativeFamilyOfPoints) (F : Sheaf J (Type w)) (U : C)
    (s s' : F.obj.obj (op U)) (h : s ≠ s') :
    ∃ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj U),
      Φ.obj.toPresheafFiber U x F.obj s ≠ Φ.obj.toPresheafFiber U x F.obj s' := by
  by_contra! H
  apply h
  let E : Sieve U := Presheaf.equalizerSieve (F := F.obj) (X := op U) s s'
  let ι : Type w := Σ (Y : C), {f : Y ⟶ U // E f}
  have hE : E ∈ J U := by
    refine J.superset_covering ?_
      ((hP.jointly_reflect_ofArrows_mem (fun a : ι ↦ a.2.1)).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨a⟩
      exact a.2.2
    · intro Φ x
      obtain ⟨Y, f, y, hy, hf⟩ :=
        (Φ.obj.toPresheafFiber_eq_iff' (A := Type w) (P := F.obj) U x s s').1 (H Φ x)
      exact ⟨⟨Y, f, hf⟩, y, hy⟩
  exact (((isSheaf_iff_isSheaf_of_type _ _).1 F.property).isSeparated E hE).ext
    (fun _ _ hf ↦ hf)

/-- **Stacks 00YM**, for a family of points given as a predicate `P` on the points of a site: `P` is
a conservative family if and only if for every sheaf of sets `F`, every object `U` and every pair
of distinct sections `s ≠ s'` of `F` over `U`, some point `Φ` of `P` and some `x ∈ Φ.fiber U` give
`s` and `s'` distinct germs in the stalk of `F` at `Φ`. -/
theorem isConservativeFamilyOfPoints_iff_exists_toPresheafFiber_ne :
    P.IsConservativeFamilyOfPoints ↔
      ∀ (F : Sheaf J (Type w)) (U : C) (s s' : F.obj.obj (op U)), s ≠ s' →
        ∃ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj U),
          Φ.obj.toPresheafFiber U x F.obj s ≠ Φ.obj.toPresheafFiber U x F.obj s' :=
  ⟨fun hP ↦ hP.exists_toPresheafFiber_ne,
    IsConservativeFamilyOfPoints.of_exists_toPresheafFiber_ne⟩

end ObjectProperty

namespace GrothendieckTopology

/-- **Stacks 00YM.** Let `(C, J)` be a site and `{p_i}_{i ∈ I}` a family of points. The family is
conservative if and only if for every sheaf of sets `F`, every object `U` of `C` and every pair of
distinct sections `s ≠ s'` of `F` over `U`, there are an index `i` and `x ∈ u_i(U)` such that the
triples `(U, x, s)` and `(U, x, s')` define distinct elements of the stalk `F_{p_i}`; that element
is the germ `(p i).toPresheafFiber U x F.obj s`. -/
@[stacks 00YM]
theorem isConservativeFamily_iff_exists_toPresheafFiber_ne {ι : Type t}
    (p : ι → Point.{w} J) :
    IsConservativeFamily p ↔
      ∀ (F : Sheaf J (Type w)) (U : C) (s s' : F.obj.obj (op U)), s ≠ s' →
        ∃ (i : ι) (x : (p i).fiber.obj U),
          (p i).toPresheafFiber U x F.obj s ≠ (p i).toPresheafFiber U x F.obj s' := by
  rw [isConservativeFamily_iff_ofObj,
    ObjectProperty.isConservativeFamilyOfPoints_iff_exists_toPresheafFiber_ne]
  refine forall₄_congr fun F U s s' ↦ imp_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨⟨Φ, hΦ⟩, x, hx⟩
    obtain ⟨i, rfl⟩ := (ObjectProperty.ofObj_iff p Φ).1 hΦ
    exact ⟨i, x, hx⟩
  · rintro ⟨i, x, hx⟩
    exact ⟨⟨p i, ObjectProperty.ofObj_apply p i⟩, x, hx⟩

end GrothendieckTopology

end CategoryTheory
