module

public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers

/-!
# Pinning a derived limit down to a given object with given projections

A derived limit is unique only up to non-unique isomorphism, which is why
`CategoryTheory.Pretriangulated.IsDerivedLimit` is a predicate; and two defining triangles over
the same object differ by an automorphism of it, which is why
`NoetherianAdicCompletion.IsDerivedLimitWithProjections` carries the projections. A statement that
is to identify a *named* object and *named* maps as the derived limit of a tower must therefore
produce a defining triangle whose first map is the product of exactly those projections, and that
is strictly more than exhibiting some derived limit.

This file supplies the reduction every such statement goes through: `K` with projections `π` is a
derived limit of `F` **exactly when** there is an isomorphism from `K` to some derived limit of
`F` carrying `π` to that limit's own projections. The nontrivial direction is the forward one, and
its proof is the triangle axiom in the form
`CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₁`: the two defining
triangles have the *same* second map, the Milnor difference map of `F`, so the identity of their
second and third objects extends to a morphism of triangles, and the five lemma for triangles
makes its first component invertible. The second output of that axiom is precisely the
compatibility of the comparison with the projections, so nothing is left unpinned.

## Main results

* `NoetherianAdicCompletion.isDerivedLimitWithProjections_of_iso` — transporting a derived limit
  with projections backwards along an isomorphism that respects the projections.
* `NoetherianAdicCompletion.exists_iso_of_isDerivedLimitWithProjections` — two derived limits of
  the same tower are isomorphic **by an isomorphism matching their projections**. This is what
  `CategoryTheory.Pretriangulated.IsDerivedLimit` cannot give: an unpinned comparison is only
  determined up to an automorphism of the limit, for instance `-1`, which negates the
  projections.
* `NoetherianAdicCompletion.isDerivedLimitWithProjections_iff_exists_iso` — **the criterion**,
  the two directions combined.

## Implementation notes

The Milnor difference map is never written out: it is read off the two hypotheses by unification,
so the statements here do not repeat it and no `HasLimitsOfShape ℕᵒᵖ` instance has to be
synthesized against a universe metavariable.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace NoetherianAdicCompletion

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Transporting a derived limit with projections backwards along an isomorphism.** If `L` with
projections `q` is a derived limit of `F` and `e : K ≅ L` carries the projections `π` of `K` to
`q`, then `K` with `π` is a derived limit of `F`. -/
public theorem isDerivedLimitWithProjections_of_iso
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    {K L : D} {π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩} {q : ∀ n : ℕ, L ⟶ F.obj ⟨n⟩}
    (hL : IsDerivedLimitWithProjections F L q) (e : K ≅ L)
    (he : ∀ n : ℕ, e.hom ≫ q n = π n) :
    IsDerivedLimitWithProjections F K π := by
  have h := hL.ofIso e.symm
  rwa [show (fun n : ℕ ↦ e.symm.inv ≫ q n) = π from funext he] at h

/-- **Two derived limits of the same tower are isomorphic by an isomorphism matching their
projections.** This is the pinned comparison: the two defining triangles have the same second
map, the Milnor difference map of `F`, so the identity on their second and third objects extends
to a morphism of triangles whose first component is invertible, and the extension carries one
family of projections to the other on the nose. -/
public theorem exists_iso_of_isDerivedLimitWithProjections
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    {K L : D} {π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩} {q : ∀ n : ℕ, L ⟶ F.obj ⟨n⟩}
    (hK : IsDerivedLimitWithProjections F K π)
    (hL : IsDerivedLimitWithProjections F L q) :
    ∃ e : K ≅ L, ∀ n : ℕ, e.hom ≫ q n = π n := by
  obtain ⟨δK, hδK⟩ := hK
  obtain ⟨δL, hδL⟩ := hL
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hδK hδL (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hiso : IsIso a := by
    refine isIso₁_of_isIso₂₃ (Triangle.homMk _ _ a (𝟙 _) (𝟙 _) ha₁
      ((Category.comp_id _).trans (Category.id_comp _).symm) ha₃) hδK hδL ?_ ?_
    · exact inferInstanceAs (IsIso (𝟙 _))
    · exact inferInstanceAs (IsIso (𝟙 _))
  refine ⟨asIso a, fun n ↦ ?_⟩
  have h := congrArg (fun t ↦ t ≫ Pi.π (fun m : ℕ ↦ F.obj ⟨m⟩) n) ha₁
  simp only [Triangle.mk_mor₁, Category.comp_id, Category.assoc, limit.lift_π,
    Fan.mk_π_app] at h
  exact h.symm

/-- **The pinning criterion.** Relative to any one derived limit `L` of `F` with projections `q`,
an object `K` with projections `π` is a derived limit of `F` precisely when there is an
isomorphism `K ≅ L` carrying `π` to `q`.

Every statement identifying a named object as *the* derived limit of a tower, with named
projections, reduces to producing such an isomorphism. -/
public theorem isDerivedLimitWithProjections_iff_exists_iso
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    {K L : D} (π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩) {q : ∀ n : ℕ, L ⟶ F.obj ⟨n⟩}
    (hL : IsDerivedLimitWithProjections F L q) :
    IsDerivedLimitWithProjections F K π ↔ ∃ e : K ≅ L, ∀ n : ℕ, e.hom ≫ q n = π n :=
  ⟨fun hK ↦ exists_iso_of_isDerivedLimitWithProjections hK hL,
    fun ⟨e, he⟩ ↦ isDerivedLimitWithProjections_of_iso hL e he⟩

end NoetherianAdicCompletion

end
