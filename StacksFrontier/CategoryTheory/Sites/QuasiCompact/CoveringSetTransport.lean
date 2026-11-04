module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Covering families along an equivalence of sites

An equivalence of sites `e : C' ≌ C` moves covering data in both directions, with no constraint
relating the universes of the two underlying categories. This file records the three transports
that checking the hypotheses of Stacks 0GMS case (2) on a model of a site needs: of
`CategoryTheory.GrothendieckTopology.CoversTop`, of a covering family, and of the refinement
relation between a covering family and a sieve.

These are needed because the conditions of Stacks 0GMS live at the canonical sheaf universe
`Type (max u v)` of the site, so they do *not* transport between two equivalent sites by any
equivalence of sheaf categories: for a site with objects in `Type (u + 1)` and morphisms in
`Type u` that universe is `u + 1`, while for an equivalent small model it is `u`, and
`Sheaf J (Type u)` is not equivalent to `Sheaf J (Type (u + 1))`. What does transport is the
site-level data, which is what the statements below are phrased in.

## Main results

* `CategoryTheory.GrothendieckTopology.coversTop_inverse_obj`: a family of objects covering the
  final object of `C` has an image under `e.inverse` covering the final object of `C'`.
* `CategoryTheory.Sieve.ofArrows_inverse_mem`: the image under `e.inverse` of a covering family
  of `e.functor.obj U`, composed with the unit, is a covering family of `U`.
* `CategoryTheory.Sieve.ofArrows_inverse_le`: that image refines any sieve whose direct image
  the original family refines.
* `CategoryTheory.Equivalence.unitHom_comp_inverse_map_functor_map` and
  `CategoryTheory.Equivalence.inverse_map_functor_map_comp_unitInv`: the two rearrangements of
  the naturality of the unit that the transports run on.

## Implementation notes

No `@[stacks]` attribute is carried. The statements are the content of Stacks 03CH (2) only in
the case of an equivalence, which is less general than that tag.

Everything is phrased for `e : C' ≌ C` with the single instance `e.inverse.IsDenseSubsite J J'`,
which is what Mathlib derives continuity, cocontinuity and cover-density of *both* functors of
the equivalence from, and which holds for `J' = e.inverse.inducedTopology J`.

The two algebraic identities that drive the transports are
`Equivalence.unitHom_comp_inverse_map_functor_map` and
`Equivalence.inverse_map_functor_map_comp_unitInv`, both rearrangements of the naturality of the
unit. They are phrased with `Equivalence.unitIso` throughout rather than with
`Equivalence.unit`, so that `CategoryTheory.Iso.hom_inv_id_app` applies to them without a
further rewrite.

## References

* [Stacks Project, Tag 03CH](https://stacks.math.columbia.edu/tag/03CH)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C)

/-- A morphism of `C'` is recovered from its image under `e.functor` by the unit. -/
theorem Equivalence.unitHom_comp_inverse_map_functor_map {Z U : C'} (g : Z ⟶ U) :
    e.unitIso.hom.app Z ≫ e.inverse.map (e.functor.map g) ≫ e.unitIso.inv.app U = g := by
  have h := e.unitIso.hom.naturality g
  simp only [Functor.id_map, Functor.comp_map] at h
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Transporting a morphism of `C'` to `C` and back is conjugation by the unit. -/
theorem Equivalence.inverse_map_functor_map_comp_unitInv {Z U : C'} (g : Z ⟶ U) :
    e.inverse.map (e.functor.map g) ≫ e.unitIso.inv.app U = e.unitIso.inv.app Z ≫ g := by
  calc e.inverse.map (e.functor.map g) ≫ e.unitIso.inv.app U
      = (e.unitIso.inv.app Z ≫ e.unitIso.hom.app Z) ≫
          e.inverse.map (e.functor.map g) ≫ e.unitIso.inv.app U := by
        rw [Iso.inv_hom_id_app, Category.id_comp]
    _ = e.unitIso.inv.app Z ≫ g := by
        rw [Category.assoc, e.unitHom_comp_inverse_map_functor_map g]

variable [e.inverse.IsDenseSubsite J J']

/-- **`CoversTop` transports along an equivalence of sites.** -/
theorem GrothendieckTopology.coversTop_inverse_obj {ι : Type*} {U : ι → C}
    (hU : J.CoversTop U) : J'.CoversTop fun i => e.inverse.obj (U i) := by
  intro X
  refine J'.superset_covering ?_ (e.functor.cover_lift J' J (hU (e.functor.obj X)))
  rintro V g hg
  obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff U (e.functor.map g)).1 hg
  exact (Sieve.mem_ofObjects_iff _ g).2 ⟨i, ⟨e.unitIso.hom.app V ≫ e.inverse.map b⟩⟩

/-- **A covering family transports along an equivalence of sites.** The images under `e.inverse`
of a covering family of `e.functor.obj U`, composed with the unit, form a covering family
of `U`. -/
theorem Sieve.ofArrows_inverse_mem {ι : Type*} {U : C'} {V : ι → C}
    (f : ∀ i, V i ⟶ e.functor.obj U) (hf : Sieve.ofArrows V f ∈ J (e.functor.obj U)) :
    Sieve.ofArrows (fun i => e.inverse.obj (V i))
      (fun i => e.inverse.map (f i) ≫ e.unitIso.inv.app U) ∈ J' U := by
  refine J'.superset_covering ?_ (e.functor.cover_lift J' J hf)
  rintro W g hg
  obtain ⟨Y, a, q, ⟨i⟩, hfac⟩ := hg
  refine ⟨e.inverse.obj (V i), e.unitIso.hom.app W ≫ e.inverse.map a,
    e.inverse.map (f i) ≫ e.unitIso.inv.app U, ⟨i⟩, ?_⟩
  rw [Category.assoc, ← Category.assoc (e.inverse.map a), ← Functor.map_comp, hfac]
  exact e.unitHom_comp_inverse_map_functor_map g

/-- **A refinement transports along an equivalence of sites.** If a covering family of
`e.functor.obj U` refines the direct image of a sieve `R` on `U`, then its transport refines
`R`. -/
theorem Sieve.ofArrows_inverse_le {ι : Type*} {U : C'} {V : ι → C}
    (f : ∀ i, V i ⟶ e.functor.obj U) {R : Sieve U}
    (hle : Sieve.ofArrows V f ≤ R.functorPushforward e.functor) :
    Sieve.ofArrows (fun i => e.inverse.obj (V i))
      (fun i => e.inverse.map (f i) ≫ e.unitIso.inv.app U) ≤ R := by
  rintro W g ⟨Y, a, q, ⟨i⟩, hfac⟩
  obtain ⟨Z, p, b, hp, hb⟩ := hle _ (Sieve.ofArrows_mk V f i)
  have hf' : e.inverse.map (f i) ≫ e.unitIso.inv.app U
      = (e.inverse.map b ≫ e.unitIso.inv.app Z) ≫ p := by
    rw [hb, Functor.map_comp, Category.assoc,
      e.inverse_map_functor_map_comp_unitInv p, Category.assoc]
  rw [← hfac, hf', ← Category.assoc]
  exact R.downward_closed hp _

end CategoryTheory

end
