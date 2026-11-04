module

public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetTransport

/-!
# The hom-set form of Stacks 0GMS (2)(c) along an equivalence of sites

Let `e : C' ≌ C` be an equivalence of categories, with topologies `J` on `C` and `J'` on `C'` for
which `e.inverse` is a dense subsite functor, and with no constraint relating the universes of
`C` and `C'`. The hom-set form of condition (2)(c) of Stacks 0GMS asks that every pair of
morphisms out of a common source factors, after a covering, through a member of a given family.
This condition transports along `e`.

## Main results

* `CategoryTheory.exists_covering_hom_pair_inverse`: the condition transports to the image of the
  family under `e.inverse`, composed with the unit.

## References

* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C)

variable [e.inverse.IsDenseSubsite J J']

/-- **The hom-set form of condition (2)(c) of Stacks 0GMS transports along an equivalence of
sites.** Let `V_i` be a family of objects of `C` with morphisms `p_i : V_i ⟶ e.functor.obj W` and
`q_i : V_i ⟶ e.functor.obj W'`, and suppose every pair of morphisms of `C` out of a common
source into `e.functor.obj W` and `e.functor.obj W'` factors, after passing to a covering of that
source, through some `(p_i, q_i)`. Then the transported family has the same property in `C'`, at
`W` and `W'`. -/
theorem exists_covering_hom_pair_inverse {ι : Type*} {W W' : C'} {V : ι → C}
    (p : ∀ i, V i ⟶ e.functor.obj W) (q : ∀ i, V i ⟶ e.functor.obj W')
    (h : ∀ (Y : C) (α : Y ⟶ e.functor.obj W) (β : Y ⟶ e.functor.obj W'),
      ∃ T : Sieve Y, T ∈ J Y ∧ ∀ ⦃Z : C⦄ (g : Z ⟶ Y), T.arrows g →
        ∃ (i : ι) (r : Z ⟶ V i), r ≫ p i = g ≫ α ∧ r ≫ q i = g ≫ β)
    (Y : C') (α : Y ⟶ W) (β : Y ⟶ W') :
    ∃ T : Sieve Y, T ∈ J' Y ∧ ∀ ⦃Z : C'⦄ (g : Z ⟶ Y), T.arrows g →
      ∃ (i : ι) (r : Z ⟶ e.inverse.obj (V i)),
        r ≫ (e.inverse.map (p i) ≫ e.unitIso.inv.app W) = g ≫ α ∧
          r ≫ (e.inverse.map (q i) ≫ e.unitIso.inv.app W') = g ≫ β := by
  obtain ⟨T, hT, hfac⟩ := h (e.functor.obj Y) (e.functor.map α) (e.functor.map β)
  refine ⟨T.functorPullback e.functor, e.functor.cover_lift J' J hT, ?_⟩
  intro Z g hg
  obtain ⟨i, r, hr, hr'⟩ := hfac (e.functor.map g) hg
  refine ⟨i, e.unitIso.hom.app Z ≫ e.inverse.map r, ?_, ?_⟩ <;>
    simp [← Functor.map_comp_assoc, hr, hr']

end CategoryTheory

end
