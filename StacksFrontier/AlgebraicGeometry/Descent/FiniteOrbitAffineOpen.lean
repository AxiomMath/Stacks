module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.GluingPoints

/-!
# Orbits of a descent datum along a finite morphism

Let `f : X ⟶ Y` be a morphism of schemes and let `D` be a descent datum relative to the
one-element family `{f}`, with underlying scheme `V = (D.obj ()).left` over `X`. The gluing
isomorphism of `D` moves a point of `V` to the points of `V` which are glued to it: the orbit
of `v ∈ V` is the image under the second projection of the points of `X ×_Y V` obtained by
applying the gluing isomorphism to the points of `V ×_Y X` above `v`.

Two facts about this orbit are proved. It is a *finite* set as soon as `f` is a finite
morphism, with no uniform bound on the number of points in the fibres of `f`; and all of its
points lie in the same fibre of `V ⟶ Y`. Consequently a descent datum whose underlying scheme
has the property that *every* finite tuple of points in one fibre over `Y` lies in a common
affine open has, for each of its points, an affine open containing that point together with its
whole orbit.

This is the step "our assumption shows there exists an affine open of `V` containing the orbit
`t(s^{-1}(v))`, as all the points in this orbit map to the same point of `Y`" in the proof of
Stacks Tag 0H8K, which is also how Stacks Tag 0CCI consumes its hypothesis.

## Main definitions

* `AlgebraicGeometry.DescentData.orbit` is the orbit of a point of the underlying scheme of a
  descent datum relative to a one-element family.

## Main results

* `AlgebraicGeometry.DescentData.finite_orbit`: along a finite morphism every orbit is finite.
* `AlgebraicGeometry.DescentData.structureMap_base_eq_of_mem_orbit`: an orbit lies in a single
  fibre of the composite `V ⟶ X ⟶ Y`.
* `AlgebraicGeometry.DescentData.exists_isAffineOpen_insert_orbit`: if every finite tuple of
  points of `V` in one fibre over `Y` has a common affine open neighbourhood, then every point
  of `V` has an affine open neighbourhood containing its entire orbit.

## Implementation notes

The orbit is defined through `AlgebraicGeometry.DescentData.gluingPullbackIso`, the gluing
isomorphism transported to the literal fibre products, so that it is a set of points of `V`
rather than of a product taken in the category of schemes over `Y`.

Finiteness of an orbit needs no bound on the degree of `f`: the orbit is the image of a fibre
of `pullback.fst ((D.obj ()).hom ≫ f) f`, which is a base change of `f` and hence finite, so
that fibre is already a finite set by `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`.
This is why the hypothesis of Stacks Tag 0CCI, which asks for a common affine open for tuples
of *every* length, makes the passage through a uniform bound on the number of points of a
geometric fibre unnecessary.

The common affine open is obtained by enumerating the finite set `insert v (D.orbit v)` by
`Finset.equivFin`; the enumeration is indexed by `Fin (n + 1)` because that set contains `v`,
and the point `v` itself is adjoined so that the resulting open contains it without using a
diagonal identity for the gluing isomorphism, which `AlgebraicGeometry.DescentData` does not
impose.

## References

* [Stacks Project, Tag 0H8K](https://stacks.math.columbia.edu/tag/0H8K)
* [Stacks Project, Tag 0CCI](https://stacks.math.columbia.edu/tag/0CCI)
* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentData

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The orbit of a point `v` of the underlying scheme of a descent datum relative to the
one-element family `{f}`: the points of that scheme obtained by applying the gluing isomorphism
to the points of `V ×_Y X` lying over `v` and taking the second projection. -/
def orbit (D : DescentData (S := Y) (X := fun _ : Unit ↦ X) (fun _ ↦ f))
    (v : (D.obj ()).left) : Set (D.obj ()).left :=
  (fun z ↦ pullback.snd f ((D.obj ()).hom ≫ f) ((D.gluingPullbackIso () ()).hom z)) ''
    (pullback.fst ((D.obj ()).hom ≫ f) f ⁻¹' {v})

/-- Along a finite morphism every orbit of a descent datum is a finite set: it is the image of
a fibre of a base change of the morphism. -/
lemma finite_orbit [IsFinite f]
    (D : DescentData (S := Y) (X := fun _ : Unit ↦ X) (fun _ ↦ f))
    (v : (D.obj ()).left) : (D.orbit v).Finite :=
  Set.Finite.image _ (Scheme.Hom.finite_preimage_singleton _ v)

/-- All points of an orbit lie in the same fibre of the underlying scheme of a descent datum
over the base. -/
lemma structureMap_base_eq_of_mem_orbit
    (D : DescentData (S := Y) (X := fun _ : Unit ↦ X) (fun _ ↦ f))
    (v : (D.obj ()).left) {w : (D.obj ()).left} (hw : w ∈ D.orbit v) :
    ((D.obj ()).hom ≫ f) w = ((D.obj ()).hom ≫ f) v := by
  obtain ⟨z, hz, rfl⟩ := hw
  have h1 : (D.obj ()).hom (pullback.snd f ((D.obj ()).hom ≫ f)
      ((D.gluingPullbackIso () ()).hom z)) =
      pullback.snd ((D.obj ()).hom ≫ f) f z := by
    rw [← Scheme.Hom.comp_apply (pullback.snd f ((D.obj ()).hom ≫ f)) (D.obj ()).hom,
      ← Scheme.Hom.comp_apply, D.gluingPullbackIso_hom_snd () ()]
  have h2 : ((D.obj ()).hom ≫ f) (pullback.fst ((D.obj ()).hom ≫ f) f z) =
      f (pullback.snd ((D.obj ()).hom ≫ f) f z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  rw [Scheme.Hom.comp_apply, h1, ← h2]
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
  rw [hz]

/-- If every finite tuple of points of the underlying scheme of a descent datum lying in one
fibre over the base has a common affine open neighbourhood, then every point has an affine open
neighbourhood containing its whole orbit. The morphism is only assumed finite; no bound on the
number of points of its fibres is used. -/
theorem exists_isAffineOpen_insert_orbit [IsFinite f]
    (D : DescentData (S := Y) (X := fun _ : Unit ↦ X) (fun _ ↦ f))
    (hV : ∀ (n : ℕ) (y : Y) (v : Fin (n + 1) → (D.obj ()).left),
      (∀ i, ((D.obj ()).hom ≫ f) (v i) = y) →
        ∃ U : (D.obj ()).left.Opens, IsAffineOpen U ∧ ∀ i, v i ∈ U)
    (v : (D.obj ()).left) :
    ∃ U : (D.obj ()).left.Opens,
      IsAffineOpen U ∧ v ∈ U ∧ D.orbit v ⊆ (U : Set (D.obj ()).left) := by
  classical
  set S : Finset (D.obj ()).left := insert v (D.finite_orbit v).toFinset with hS
  have hvS : v ∈ S := by simp [hS]
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨v, hvS⟩
  obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by omega⟩
  set g : Fin (n + 1) → (D.obj ()).left :=
    fun i ↦ ((S.equivFin.symm (Fin.cast hn.symm i) : {x // x ∈ S}) : (D.obj ()).left) with hg
  have hgmem : ∀ i, g i ∈ S := fun i ↦ (S.equivFin.symm (Fin.cast hn.symm i)).2
  have hsurj : ∀ x ∈ S, ∃ i, g i = x := by
    intro x hx
    refine ⟨Fin.cast hn (S.equivFin ⟨x, hx⟩), ?_⟩
    simp [hg]
  have hover : ∀ i, ((D.obj ()).hom ≫ f) (g i) = ((D.obj ()).hom ≫ f) v := by
    intro i
    have hi := hgmem i
    rw [hS, Finset.mem_insert] at hi
    rcases hi with h | h
    · rw [h]
    · exact D.structureMap_base_eq_of_mem_orbit v ((Set.Finite.mem_toFinset _).mp h)
  obtain ⟨U, hU, hmem⟩ := hV n (((D.obj ()).hom ≫ f) v) g hover
  have hUS : ∀ x ∈ S, x ∈ U := fun x hx ↦ by
    obtain ⟨i, hi⟩ := hsurj x hx
    exact hi ▸ hmem i
  exact ⟨U, hU, hUS v hvS, fun w hw ↦ hUS w (by simp [hS, hw])⟩

end AlgebraicGeometry.DescentData

end
