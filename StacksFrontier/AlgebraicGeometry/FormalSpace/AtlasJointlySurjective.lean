module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.CategoryTheory.Sites.Topos.TypeSheafSections

/-!
# A jointly surjective family of fppf sheaves is jointly surjective on points

Let `S` be a scheme contained in a big fppf site `B` and let `{fᵢ : Xᵢ ⟶ X}` be a family of
morphisms of fppf sheaves on the big fppf site of `S` whose induced morphism from the coproduct
is a surjection of sheaves. Then every point of `X`, in the sense of Stacks 03BU, is the image
of a point of one of the `Xᵢ`.

This is the form in which the atlas of a formal algebraic space (Definition 0AIM) is used to
cover the point space: `AlgebraicGeometry.FormalSpace.isSurjective_of_isLocallySurjective` says
only that the coproduct surjects onto the points of `X`, and a point of the coproduct still has
to be traced back to a summand. That step is local: a section of the coproduct lies, on a
covering sieve, in the image of a single summand, and a field-valued point may be refined along
any member of a covering sieve.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_index_pointsMapULift_eq`: every point of the target of a
  jointly surjective family is the image of a point of one of the sources.

## Implementation notes

The local factorization of a section of a coproduct of sheaves of sets through one summand is
`Stacks.Sheaves.TypeSheaf.exists_covering_of_epi_sigmaDesc`, whose value universe is
`Type (max u v)` for a category of objects in `Type u` with morphisms in `Type v`; for the big
fppf site of `S` that is `Type (u + 1)`, the value universe of the formal algebraic spaces.

The refinement of a field-valued point along a covering sieve is the one of
`AlgebraicGeometry.FormalSpace.isSurjective_of_isLocallySurjective`: a member of the sieve whose
image contains the closed point of the field spectrum, and the spectrum of a residue field of
that member at a preimage of the closed point.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A jointly surjective family of morphisms of fppf sheaves is jointly surjective on
points.** If the morphism from the coproduct of a family `{fᵢ : Xᵢ ⟶ X}` is a surjection of
sheaves, then every point of `X` is the image of a point of some `Xᵢ`.

A field-valued point of `X` is a section over the spectrum of a field; that section lies, on a
covering sieve, in the image of a single `fᵢ`; a member of that sieve has in its image the
closed point of the field spectrum, and the residue field of the member at a preimage of the
closed point is a field of the site over which the local preimage becomes a field-valued point
of `Xᵢ` whose image is the given point. -/
theorem exists_index_pointsMapULift_eq {I : Type (u + 1)} {Xi : I → FppfSheaf B S hS}
    {X : FppfSheaf B S hS} (f : ∀ i, Xi i ⟶ X)
    (hf : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f))
    (p : Space.pointsULift.{u + 1} B S hS X.obj) :
    ∃ (i : I) (q : Space.pointsULift.{u + 1} B S hS (Xi i).obj),
      Space.pointsMapULift B S hS (Xi i).obj (f i).hom q = p := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have _ : Epi (Sigma.desc f) := (Sheaf.isLocallySurjective_iff_epi _).mp hf
  induction p using Quot.ind with
  | _ pt => ?_
  obtain ⟨R, hR, hmem⟩ := Stacks.Sheaves.TypeSheaf.exists_covering_of_epi_sigmaDesc
    Xi f (pt.siteObject B S hS X.obj) pt.value
  obtain ⟨V, g, hg, z, -⟩ := BigFppfOver.exists_mem_range_of_mem_topology B S hS hR
    (IsLocalRing.closedPoint pt.carrier)
  obtain ⟨i, a, ha⟩ := hmem g hg
  obtain ⟨K, instK, hK, ρ, -⟩ := Space.exists_fieldSpec_at_point B V.left.2 z
  let r : B.obj hK ⟶ V.left := B.inclusion.preimage (X := B.obj hK) (Y := V.left) ρ
  let m : (Over.mk (r ≫ V.hom) : BigFppfOver B S hS) ⟶ V := Over.homMk r
  refine ⟨i, Quot.mk _ ⟨K, hK, B.inclusion.map (r ≫ V.hom), (Xi i).obj.map m.op a⟩, ?_⟩
  refine Quot.sound ⟨_, Space.FieldValuedPointULift.dominates_refl B S hS X.obj _, m ≫ g, ?_⟩
  change X.obj.map (m ≫ g).op pt.value = (f i).hom.app _ ((Xi i).obj.map m.op a)
  rw [op_comp, X.obj.map_comp, types_comp_apply, ← ha]
  exact (congrArg (fun k => k a) ((f i).hom.naturality m.op)).symm

end AlgebraicGeometry.FormalSpace

end
