module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantAffineOpenDimensionOneQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ConstructingInvariantOpens
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfDimensionOnePointsFiniteComponents

/-!
# An invariant affine open around a point whose orbit has one-dimensional local rings

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` finite, let `U` be separated and
locally Noetherian, and let `u ∈ U` be a point such that `dim(𝒪_{U, u'}) ≤ 1` for every point
`u'` in the `R`-orbit of `u`. Then `u` lies in an `R`-invariant affine open of `U`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_mem_le_isAffineOpen_of_krullDimLE_one`:
  under the same hypotheses, `u` lies in an `R`-invariant open contained in an affine open.
* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem_of_krullDimLE_one`:
  `u` lies in an `R`-invariant affine open.
* `AlgebraicGeometry.GroupoidScheme.finite_setOf_exists_arrow_source_eq`: the `R`-orbit of a
  point is finite when `s` is finite.
* `AlgebraicGeometry.GroupoidScheme.exists_mem_orbit_mem_closure_of_saturation_closure_eq_univ`:
  if `t(s⁻¹(closure W)) = U`, every orbit meets `closure W`.

## References

* [Stacks Project, Tag 0ABI](https://stacks.math.columbia.edu/tag/0ABI)
* [Stacks Project, Tag 09NN](https://stacks.math.columbia.edu/tag/09NN)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 03LO](https://stacks.math.columbia.edu/tag/03LO)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

/-- The `R`-orbit of a point `u` of the object scheme of a groupoid scheme, namely the set of
points reached by an arrow with source `u`, is finite as soon as the source map is finite. -/
theorem finite_setOf_exists_arrow_source_eq (G : GroupoidScheme S) [IsFinite G.source.left]
    (u : G.objects.left) :
    {u' : G.objects.left |
      ∃ r : G.arrows.left, G.source.left.base r = u ∧ G.target.left.base r = u'}.Finite := by
  refine ((G.source.left.finite_preimage_singleton u).image G.target.left.base).subset ?_
  rintro _ ⟨r, rfl, rfl⟩
  exact ⟨r, rfl, rfl⟩

/-- Lying in a common orbit is a symmetric relation: if some arrow has source `u` and target
`u'`, then some arrow has source `u'` and target `u`. -/
theorem exists_arrow_source_eq_target_eq_symm (G : GroupoidScheme S)
    {u u' : G.objects.left}
    (h : ∃ r : G.arrows.left, G.source.left.base r = u ∧ G.target.left.base r = u') :
    ∃ r : G.arrows.left, G.source.left.base r = u' ∧ G.target.left.base r = u := by
  obtain ⟨r, hs, ht⟩ := h
  obtain ⟨r', ht', hs'⟩ := (equivalence_sourceTargetRel G).symm
    (show Function.SourceTargetRel G.source.left.base G.target.left.base u' u from ⟨r, ht, hs⟩)
  exact ⟨r', hs', ht'⟩

/-- If the saturation `t(s⁻¹(closure W))` of the closure of a subset `W` is the whole object
scheme, then every point has a point of its orbit in `closure W`. -/
theorem exists_mem_orbit_mem_closure_of_saturation_closure_eq_univ (G : GroupoidScheme S)
    (W : Set G.objects.left)
    (hW : G.target.left.base '' (G.source.left.base ⁻¹' closure W) = Set.univ)
    (u : G.objects.left) :
    ∃ u' : G.objects.left,
      (∃ r : G.arrows.left, G.source.left.base r = u ∧ G.target.left.base r = u') ∧
        u' ∈ closure W := by
  obtain ⟨a, hasrc, hatgt⟩ : u ∈ G.target.left.base '' (G.source.left.base ⁻¹' closure W) :=
    hW ▸ Set.mem_univ u
  exact ⟨G.source.left.base a,
    exists_arrow_source_eq_target_eq_symm G ⟨a, rfl, hatgt⟩, hasrc⟩

/-- Let `G` be a groupoid scheme whose source and target maps are finite, whose object scheme is
separated and locally Noetherian, and let `u` be a point of the object scheme whose orbit
consists of points with stalks of Krull dimension at most one. Then `u` lies in an invariant open
of the object scheme which is contained in an affine open. -/
theorem exists_isInvariantOpen_mem_le_isAffineOpen_of_krullDimLE_one
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left]
    [G.objects.left.IsSeparated] [IsLocallyNoetherian G.objects.left]
    (u : G.objects.left)
    (hdim : ∀ u' : G.objects.left,
      (∃ r : G.arrows.left, G.source.left.base r = u ∧ G.target.left.base r = u') →
        Ring.KrullDimLE 1 (G.objects.left.presheaf.stalk u')) :
    ∃ V U' : G.objects.left.Opens,
      IsInvariantOpen G V ∧ IsAffineOpen U' ∧ u ∈ V ∧ V ≤ U' := by
  classical
  set Orb : Set G.objects.left := {u' : G.objects.left |
    ∃ r : G.arrows.left, G.source.left.base r = u ∧ G.target.left.base r = u'}
  have : Finite Orb := (finite_setOf_exists_arrow_source_eq G u).to_subtype
  obtain ⟨U', hU'aff, hU'mem⟩ :=
    exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components
      G.objects.left (_root_.AlgebraicGeometry.finite_irreducibleComponents_of_isCompact
        G.objects.left)
      (fun z : Orb => (z : G.objects.left)) (fun _ => inferInstance)
      (fun z => hdim (z : G.objects.left) z.2)
  have hOrbU' : Orb ⊆ (U' : Set G.objects.left) := fun x hx => hU'mem ⟨x, hx⟩
  set Csat : Set G.objects.left :=
    G.target.left.base '' (G.source.left.base ⁻¹' ((U' : Set G.objects.left)ᶜ))
  have hCclosed : IsClosed Csat :=
    G.target.left.isClosedMap _
      (((U'.2.isClosed_compl).preimage G.source.left.continuous))
  refine ⟨⟨Csatᶜ, hCclosed.isOpen_compl⟩, U',
    isInvariantSet_compl G (isInvariantSet_target_image_source_preimage G _), hU'aff, ?_, ?_⟩
  · rintro ⟨r, hrs, hrt⟩
    exact hrs (hOrbU' (exists_arrow_source_eq_target_eq_symm G ⟨r, rfl, hrt⟩))
  · exact fun y hy => by_contra fun hyU' =>
      hy (subset_target_image_source_preimage G ((U' : Set G.objects.left)ᶜ) hyU')

/-- Let `G` be a groupoid scheme whose source and target maps are finite and whose object scheme
is separated and locally Noetherian, and let `u` be a point of the object scheme such that every
point of the orbit of `u` has a stalk of Krull dimension at most one. Then `u` lies in an
invariant affine open of the object scheme. -/
@[stacks 0ABI]
theorem exists_isInvariantOpen_isAffineOpen_mem_of_krullDimLE_one
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left]
    [G.objects.left.IsSeparated] [IsLocallyNoetherian G.objects.left]
    (u : G.objects.left)
    (hdim : ∀ u' : G.objects.left,
      (∃ r : G.arrows.left, G.source.left.base r = u ∧ G.target.left.base r = u') →
        Ring.KrullDimLE 1 (G.objects.left.presheaf.stalk u')) :
    ∃ W : G.objects.left.Opens, IsInvariantOpen G W ∧ IsAffineOpen W ∧ u ∈ W := by
  obtain ⟨V, U', hVinv, hU'aff, huV, hVU'⟩ :=
    exists_isInvariantOpen_mem_le_isAffineOpen_of_krullDimLE_one G u hdim
  exact exists_isInvariantOpen_isAffineOpen_mem_of_le_isAffineOpen
    Stacks.Thickenings.forall_isAffine_of_isThickening G V U' hVinv hU'aff hVU' u huV hdim

end AlgebraicGeometry.GroupoidScheme

end
