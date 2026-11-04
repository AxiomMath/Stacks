module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# The points of an intersection of closed subspaces

The point set of the intersection of a family of closed subspaces of an algebraic space is the
intersection of their point sets. The inclusion `⊆` holds for any family of subfunctors and is
`AlgebraicGeometry.Space.range_pointsMap_ι_le`; this file supplies the reverse inclusion, which
is the content.

## Main results

* `AlgebraicGeometry.Space.mem_range_pointsMap_ι_iff_value_mem`: a field-valued point of an
  algebraic space has its class in the point set of a closed subspace exactly when its own
  section lies in that subspace. This is Stacks 03JJ read at a field-valued point.
* `AlgebraicGeometry.Space.iInter_range_pointsMap_ι_subset_range_pointsMap_ι_sInf` and
  `AlgebraicGeometry.Space.range_pointsMap_ι_sInf_eq_iInter`: the point set of the
  intersection of a family of closed subspaces is the intersection of their point sets.
* `AlgebraicGeometry.Space.range_pointsMap_ι_iInf_eq_iInter`: the same for an indexed family.

## Implementation notes

*No quasi-compactness, no antitonicity, no cardinality hypothesis.* One might expect the
reverse inclusion to need a compactness argument — a point lying in every member is witnessed
in each by a possibly different field-valued representative, and amalgamating representatives
over an unbounded family is exactly the step that costs a cardinality bound elsewhere in this
development. It costs nothing here, because no amalgamation is needed: by Stacks 03JJ the
*given* representative already lies in each member, since `Spec` of a field is reduced and a
morphism from a reduced algebraic space factors through a closed subspace as soon as its
points do. Membership in a closed subspace is therefore a property of the class, not of the
representative, and the intersection of subfunctors is computed sectionwise
(`CategoryTheory.Subfunctor.sInf_obj`).

This is what makes the result usable for a family indexed by a Zorn chain, whose cardinality
is not bounded by anything: the statement is about an arbitrary `Set (Subfunctor X)`, as is
`AlgebraicGeometry.Space.isClosedSubspace_sInf`.

The easy half is recorded too, so that the equality can be quoted directly rather than
reassembled at each use.

*What this does and does not unblock — read this before chasing the cardinality question.*
This result was proved for Stacks 07SR with transition morphisms that are closed immersions,
where the index is a Zorn chain and no cardinality bound is available. It removes one of the
two obstructions there; it does **not** make that form of 07SR available, and the remaining
obstruction is not the one the reader may expect. The second obstruction was the
closed-subspace analogue of Stacks 086V, and that turned out not to be needed at all: for
closed-immersion transitions the limit `sInf 𝒮` is a closed subspace of *every* member
(`isClosedImmersion_ι_sInf`, and `isClosedImmersion_homOfLe'` for `sInf 𝒮 ≤ Z`), so Stacks
0827 degenerates to extending an open along one closed embedding at a single member, which
`isClosed_range_pointsMap_of_isClosedImmersion`, Tag 04NN and Tag 03BZ all do without a bound.
**The obstruction that remains is a cardinality-free Stacks 07SQ for closed-immersion
transitions** — turning an affine open of the limit into an affine open of a member. That is
a separate problem, running through Stacks 07SI, 084S and Noetherian approximation, and
nothing in this file bears on it. It is not "a size-free 07SR" and it is not Stacks 086V.

## References

* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Membership of a field-valued point in a closed subspace -/

/-- The morphism out of the representable presheaf of the site object of a field-valued
point which the point itself names. -/
noncomputable abbrev fieldPointPresheafHom (p : FieldValuedPoint B S hS X) :
    yoneda.obj p.siteObject ⟶ X :=
  yonedaEquiv.symm p.value

/-- Every point of the representable presheaf named by a field-valued point is carried by
that point's morphism to the point's own class: any field-valued point of
`yoneda p.siteObject` names a morphism to `p.siteObject`, along which `p` restricts. -/
theorem pointsMap_fieldPointHom (p : FieldValuedPoint B S hS X)
    (w : points B S hS (yoneda.obj p.siteObject)) :
    pointsMap B S hS (yoneda.obj p.siteObject) (fieldPointPresheafHom B S hS p) w =
      p.class B S hS X := by
  induction w using Quot.inductionOn with
  | h q =>
    exact Quot.sound ⟨FieldValuedPoint.map B S hS _ (fieldPointPresheafHom B S hS p) q,
      FieldValuedPoint.dominates_refl B S hS X _, ⟨q.value, rfl⟩⟩

/-- A field-valued point whose section lies in a subfunctor has its class in the point set of
that subfunctor. -/
theorem class_mem_range_pointsMap_ι_of_value_mem (Z : Subfunctor X)
    (p : FieldValuedPoint B S hS X) (h : p.value ∈ Z.obj (op p.siteObject)) :
    p.class B S hS X ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) :=
  ⟨FieldValuedPoint.class B S hS Z.toFunctor
    { carrier := p.carrier, contained := p.contained, toBase := p.toBase,
      value := ⟨p.value, h⟩ }, rfl⟩

/-- **Stacks 03JJ at a field-valued point.** The class of a field-valued point of an
algebraic space lies in the point set of a closed subspace exactly when the point's own
section lies in that subspace.

The forward direction is the content: `Spec` of a field is reduced, so Stacks 03JJ lifts the
morphism the point names through the closed subspace. -/
theorem mem_range_pointsMap_ι_iff_value_mem (hX : IsAlgebraicSpace B S hS X)
    (Z : Subfunctor X) (hZ : IsClosedSubspace B S hS Z) (p : FieldValuedPoint B S hS X) :
    p.class B S hS X ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) ↔
      p.value ∈ Z.obj (op p.siteObject) := by
  refine ⟨fun hmem => ?_, class_mem_range_pointsMap_ι_of_value_mem B S hS Z p⟩
  have hred : HasEtaleLocalProperty B S hS (yoneda.obj p.siteObject)
      (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_of_representable B S hS (yoneda.obj p.siteObject)
      (fun T : Scheme.{u} => IsReduced T) p.siteObject (Iso.refl _)
      (inferInstanceAs (IsReduced (Spec (CommRingCat.of p.carrier))))
  have hrange : Set.range (pointsMap B S hS (yoneda.obj p.siteObject)
      (fieldPointPresheafHom B S hS p)) ⊆ Set.range (pointsMap B S hS Z.toFunctor Z.ι) :=
    Set.range_subset_iff.2 fun w => by rwa [pointsMap_fieldPointHom B S hS p w]
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX
    (isAlgebraicSpace_yoneda B S hS p.siteObject) Z hZ hred
    (fieldPointPresheafHom B S hS p)).mpr hrange
  have hfp : yonedaEquiv (fieldPointPresheafHom B S hS p) = p.value :=
    Equiv.apply_symm_apply yonedaEquiv p.value
  have hy := congrArg (yonedaEquiv (X := p.siteObject)) hg
  rw [yonedaEquiv_comp, hfp] at hy
  rw [← hy]
  exact (yonedaEquiv g).property

/-! ### The intersection -/

/-- **The points of an intersection of closed subspaces are the intersection of the points**,
the inclusion that is not formal. A point lying in every member of the family lies in their
intersection, with no hypothesis on the family: by Stacks 03JJ its own representative lies in
every member, and the intersection of subfunctors is computed sectionwise. -/
theorem iInter_range_pointsMap_ι_subset_range_pointsMap_ι_sInf
    (hX : IsAlgebraicSpace B S hS X) (𝒮 : Set (Subfunctor X))
    (h𝒮 : ∀ Z ∈ 𝒮, IsClosedSubspace B S hS Z) :
    (⋂ Z ∈ 𝒮, Set.range (pointsMap B S hS Z.toFunctor Z.ι)) ⊆
      Set.range (pointsMap B S hS (sInf 𝒮).toFunctor (sInf 𝒮).ι) := by
  intro x hx
  induction x using Quot.inductionOn with
  | h p =>
    have hmem : p.value ∈ (sInf 𝒮).obj (op p.siteObject) := by
      rw [Subfunctor.sInf_obj, Set.sInf_eq_sInter, Set.mem_sInter]
      rintro A ⟨Z, hZ, rfl⟩
      exact (mem_range_pointsMap_ι_iff_value_mem B S hS hX Z (h𝒮 Z hZ) p).mp
        (Set.mem_iInter₂.mp hx Z hZ)
    exact class_mem_range_pointsMap_ι_of_value_mem B S hS (sInf 𝒮) p hmem

/-- **The point set of an intersection of closed subspaces is the intersection of their
point sets.** -/
theorem range_pointsMap_ι_sInf_eq_iInter (hX : IsAlgebraicSpace B S hS X)
    (𝒮 : Set (Subfunctor X)) (h𝒮 : ∀ Z ∈ 𝒮, IsClosedSubspace B S hS Z) :
    Set.range (pointsMap B S hS (sInf 𝒮).toFunctor (sInf 𝒮).ι) =
      ⋂ Z ∈ 𝒮, Set.range (pointsMap B S hS Z.toFunctor Z.ι) :=
  le_antisymm
    (Set.subset_iInter₂ fun _ hZ => range_pointsMap_ι_le B S hS (sInf_le hZ))
    (iInter_range_pointsMap_ι_subset_range_pointsMap_ι_sInf B S hS hX 𝒮 h𝒮)

/-- **The point set of an indexed intersection of closed subspaces is the intersection of
their point sets.** -/
theorem range_pointsMap_ι_iInf_eq_iInter (hX : IsAlgebraicSpace B S hS X)
    {ι : Type*} (Z : ι → Subfunctor X) (hZ : ∀ a, IsClosedSubspace B S hS (Z a)) :
    Set.range (pointsMap B S hS (⨅ a, Z a).toFunctor (⨅ a, Z a).ι) =
      ⋂ a, Set.range (pointsMap B S hS (Z a).toFunctor (Z a).ι) := by
  rw [iInf, range_pointsMap_ι_sInf_eq_iInter B S hS hX _
    (Set.forall_mem_range.2 hZ)]
  exact Set.biInter_range

end AlgebraicGeometry.Space

end
