module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategory
public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategoryIsCategory

/-!
# Lifting an equivalence over the site to an equivalence over a category fibred in sets

Let `r : E ⥤ 𝒞` be a category fibred in sets over `𝒞`, let `a : D₁ ⥤ E` and `b : D₂ ⥤ E` be two
categories over `E`, and read them as categories over `𝒞` through `r`. An equivalence over `𝒞`
between the two which commutes *strictly* with the two structure functors to `E` is an
equivalence over `E`.

Only one of the two strict commutations has to be supplied:
`StacksRepresentableCFG.EquivalenceOver.inv_comp_eq_of_isFiberedInSets` produces the other one
from it, because two 1-morphisms into `E` joined by a 2-morphism over `𝒞` are equal
(**Stacks 02Y2**) once `E` is fibred in sets over `𝒞`.

## Main definitions

* `StacksRepresentableCFG.EquivalenceOver.ofIsFiberedInSetsBase`: the equivalence over `E`.

## Main results

* `CategoryTheory.Functor.IsFiberedInSets.exists_eq_eqToHom_of_isHomLift_id`: a morphism of a
  category fibred in sets which lies over an identity is the canonical `eqToHom`.
* `StacksRepresentableCFG.EquivalenceOver.inv_comp_eq_of_isFiberedInSets`: the second strict
  commutation.

## Implementation notes

The coherence conditions of `StacksRepresentableCFG.EquivalenceOver` for the lifted equivalence
are its conditions for the given one: the unit and the counit are unchanged, and a component
which is vertical for `a ⋙ r` is carried by `a` to a vertical morphism of `E`, hence to an
`eqToHom`, which is exactly what verticality for `a` says. The two base objects at which
verticality is stated differ by the object equalities the strict commutations force, so each is
transported along a `congrArg`, as in `StacksRepresentableCFG.EquivalenceOver.trans`.

## References

* [Stacks Project, Tag 02Y2](https://stacks.math.columbia.edu/tag/02Y2)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
-/

@[expose] public section

namespace CategoryTheory

universe v v₁ u u₁

variable {𝒞 : Type u} [Category.{v} 𝒞] {E : Type u₁} [Category.{v₁} E]

/-- **A morphism of a category fibred in sets which lies over an identity is an `eqToHom`.**
Its source and its target agree, and it is the transport along that equality: a lift of a
morphism of the base is unique together with its domain, and the identity is a second lift. -/
theorem Functor.IsFiberedInSets.exists_eq_eqToHom_of_isHomLift_id (r : E ⥤ 𝒞)
    [r.IsFiberedInSets] {y z : E} (φ : y ⟶ z) (hφ : r.IsHomLift (𝟙 (r.obj z)) φ) :
    ∃ h : y = z, φ = eqToHom h := by
  obtain ⟨h, hc⟩ := Functor.IsFiberedInSets.eq_of_isHomLift r (𝟙 (r.obj z)) φ (𝟙 z)
  exact ⟨h, hc.trans (Category.comp_id _)⟩

end CategoryTheory

open CategoryTheory

namespace StacksRepresentableCFG

universe v v₁ v₂ v₃ u u₁ u₂ u₃

variable {𝒞 : Type u} [Category.{v} 𝒞] {E : Type u₁} [Category.{v₁} E]
  {D₁ : Type u₂} [Category.{v₂} D₁] {D₂ : Type u₃} [Category.{v₃} D₂]

/-- A component of a natural transformation which is vertical for `a ⋙ r` is carried by `a` to
a morphism which is vertical for `a`, when `r` is fibred in sets: its image under `a` is
vertical for `r`, hence an `eqToHom`. -/
theorem isHomLift_of_isHomLift_comp_of_isFiberedInSets {r : E ⥤ 𝒞} [r.IsFiberedInSets]
    {p : D₁ ⥤ 𝒞} {a : D₁ ⥤ E} (ha : a ⋙ r = p) {x y : D₁} (φ : x ⟶ y)
    (hφ : p.IsHomLift (𝟙 (p.obj x)) φ) :
    a.IsHomLift (𝟙 (a.obj x)) φ := by
  have hr : r.IsHomLift (𝟙 (p.obj x)) (a.map φ) := Functor.isHomLift_map_of_comp_eq ha _ φ
  have hry : r.obj (a.obj y) = p.obj x := IsHomLift.codomain_eq r (𝟙 (p.obj x)) (a.map φ)
  have hr' : r.IsHomLift (𝟙 (r.obj (a.obj y))) (a.map φ) :=
    hry ▸ hr
  obtain ⟨hobj, hmap⟩ :=
    Functor.IsFiberedInSets.exists_eq_eqToHom_of_isHomLift_id r (a.map φ) hr'
  exact IsHomLift.of_fac' a (𝟙 (a.obj x)) φ rfl hobj.symm (by simpa using hmap)

/-- The counit of an equivalence over `𝒞` is vertical for a structure functor `b` to a category
fibred in sets over `𝒞` through which `q` factors. -/
theorem EquivalenceOver.isHomLift_counitIso_hom_app_of_isFiberedInSets {r : E ⥤ 𝒞}
    [r.IsFiberedInSets] {p : D₁ ⥤ 𝒞} {q : D₂ ⥤ 𝒞} {b : D₂ ⥤ E} (hb : b ⋙ r = q)
    (e : EquivalenceOver p q) (y : D₂) :
    b.IsHomLift (𝟙 (b.obj ((e.inv.functor ⋙ e.hom.functor).obj y))) (e.counitIso.hom.app y) := by
  have hy : q.obj ((e.inv.functor ⋙ e.hom.functor).obj y) = q.obj y := by
    change ((e.inv.functor ⋙ e.hom.functor) ⋙ q).obj y = _
    rw [Functor.assoc, e.hom.w, e.inv.w]
  exact isHomLift_of_isHomLift_comp_of_isFiberedInSets hb (e.counitIso.hom.app y)
    (hy ▸ e.isHomLift_counitIso_hom_app y)

/-- **The second strict commutation comes for free.** If the forward 1-morphism of an
equivalence over `𝒞` commutes strictly with the two structure functors to a category `E` fibred
in sets over `𝒞`, then so does the backward one: the two candidate 1-morphisms into `E` agree on
objects, because the counit is vertical and `E` is fibred in sets, and a 1-morphism into a
category fibred in sets is determined by its action on objects (**Stacks 02Y2**). -/
theorem EquivalenceOver.inv_comp_eq_of_isFiberedInSets (r : E ⥤ 𝒞) [r.IsFiberedInSets]
    {p : D₁ ⥤ 𝒞} {q : D₂ ⥤ 𝒞} {a : D₁ ⥤ E} {b : D₂ ⥤ E} (ha : a ⋙ r = p) (hb : b ⋙ r = q)
    (e : EquivalenceOver p q) (hh : e.hom.functor ⋙ b = a) :
    e.inv.functor ⋙ a = b := by
  refine Functor.IsFiberedInSets.eq_of_obj_eq q r (e.inv.functor ⋙ a) b ?_ hb (fun y => ?_)
  · rw [Functor.assoc, ha, e.inv.w]
  · have := e.isHomLift_counitIso_hom_app_of_isFiberedInSets hb y
    have hobj : b.obj ((e.inv.functor ⋙ e.hom.functor).obj y) = b.obj y :=
      (IsHomLift.codomain_eq b (𝟙 (b.obj ((e.inv.functor ⋙ e.hom.functor).obj y)))
        (e.counitIso.hom.app y)).symm
    exact (Functor.congr_obj hh (e.inv.functor.obj y)).symm.trans hobj

/-- **An equivalence over `𝒞` which commutes strictly with two structure functors to a category
`E` fibred in sets over `𝒞` is an equivalence over `E`.** The two 1-morphisms and the two 2-cells
are the given ones; the strict commutations over `E` are the hypothesis `hh` and
`StacksRepresentableCFG.EquivalenceOver.inv_comp_eq_of_isFiberedInSets`, and verticality over `E`
follows from verticality over `𝒞` because a vertical morphism of a category fibred in sets is an
`eqToHom`. -/
def EquivalenceOver.ofIsFiberedInSetsBase (r : E ⥤ 𝒞) [r.IsFiberedInSets]
    {p : D₁ ⥤ 𝒞} {q : D₂ ⥤ 𝒞} {a : D₁ ⥤ E} {b : D₂ ⥤ E} (ha : a ⋙ r = p) (hb : b ⋙ r = q)
    (e : EquivalenceOver p q) (hh : e.hom.functor ⋙ b = a) :
    EquivalenceOver a b where
  hom := ⟨e.hom.functor, hh⟩
  inv := ⟨e.inv.functor, EquivalenceOver.inv_comp_eq_of_isFiberedInSets r ha hb e hh⟩
  unitIso := e.unitIso
  counitIso := e.counitIso
  unit_over := whiskerRight_eq_eqToHom _ _ _ fun x =>
    isHomLift_of_isHomLift_comp_of_isFiberedInSets ha (e.unitIso.hom.app x)
      (e.isHomLift_unitIso_hom_app x)
  counit_over := whiskerRight_eq_eqToHom _ _ _ fun y =>
    e.isHomLift_counitIso_hom_app_of_isFiberedInSets hb y

end StacksRepresentableCFG

end
