module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubsetReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceComparison
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# The closed subspace is a thickening of the completion along it

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `Z ⊆ X` be a closed subspace. The canonical morphism `Z ⟶ X^∧_Z` from `Z` into the
completion of `X` along `Z` is a *representable thickening*: every base change of it along a
scheme-valued point of `X^∧_Z` is a surjective closed immersion of schemes. This is the
assertion of Stacks 0AI9 — a stage of a colimit presentation with thickening transition
morphisms maps to the colimit by a thickening — for the presentation of `X^∧_Z` by the
infinitesimal neighbourhoods of `Z`, which is a colimit of algebraic spaces and not of affine
objects of the site.

With it, **Stacks 0GXW** follows: the reduction of `X^∧_Z` is `Z_red`.

The proof does not pass through the colimit presentation. A scheme-valued point `g` of `X^∧_Z`
has an underlying scheme-valued point `gs` of `X`, because `X^∧_Z ⟶ X` is a monomorphism — it
is the fppf sheafification of the inclusion of a subfunctor of the universe lift of `X`, which
is already a sheaf. Cancelling that monomorphism identifies the base change of `Z ⟶ X^∧_Z`
along `g` with the inverse image `gs⁻¹(Z)`, which is a closed immersion because `Z` is a closed
subspace of `X`. It is surjective because the point set of `gs` lands in the point set of `Z`:
the comparison morphism `X^∧_Z ⟶ X_{/|Z|}` of
`AlgebraicGeometry.Space.completionSubspaceComparison` carries `g` to a scheme-valued point of
the completion of `X` along the closed subset `|Z|` lying over the same `gs`, and such a point
is supported on `|Z|` by
`AlgebraicGeometry.Space.range_pointsMap_subset_of_whiskerRight_eq`. That last statement is
where the locality in the fppf topology happens: a section of a sheafification comes from the
subfunctor only after passing to a covering.

## Main definitions

* `AlgebraicGeometry.Space.completionSubspaceToAmbientLift` is the morphism `X^∧_Z ⟶ X` into
  the universe lift of `X` itself, for an `X` whose universe lift is already a sheaf.

## Main results

* `AlgebraicGeometry.Space.mono_completionSubspaceToAmbientLift`: that morphism is a
  monomorphism.
* `AlgebraicGeometry.FormalSpace.range_pointsMap_subset_subspacePoints`: a scheme-valued point
  of `X^∧_Z` has point-set image in `|Z|`.
* `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_toCompletionSubspace`: the
  canonical morphism `Z ⟶ X^∧_Z` is a representable thickening; this is Stacks 0AI9 for the
  colimit presentation of `X^∧_Z` by the infinitesimal neighbourhoods of `Z`.
* `AlgebraicGeometry.FormalSpace.isReduction_completionSubspace'`: **Stacks 0GXW**.

## Implementation notes

`AlgebraicGeometry.Space.completionSubspaceToAmbient` lands in the sheafification of the
universe lift of `X` rather than in the universe lift itself. For an algebraic space `X` that
sheafification is isomorphic to the universe lift, and
`AlgebraicGeometry.Space.completionSubspaceToAmbientLift` is the lift of the inclusion of the
completion subfunctor through the universal property of sheafification, which avoids carrying
the isomorphism; this is the same device as
`AlgebraicGeometry.Space.completionSheafToAmbient` for the completion along a closed subset.

## References

* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
* [Stacks Project, Tag 0GXU](https://stacks.math.columbia.edu/tag/0GXU)
* [Stacks Project, Tag 0GXW](https://stacks.math.columbia.edu/tag/0GXW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (Z : Subfunctor X)
variable (hXsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))

/-! ### The completion inside the universe lift of the ambient algebraic space -/

/-- The morphism `X^∧_Z ⟶ X` from the completion of `X` along a closed subspace `Z` into the
universe lift of `X`, for an `X` whose universe lift is already an fppf sheaf: the inclusion of
the union of the infinitesimal neighbourhoods of `Z`, lifted through the universal property of
sheafification. -/
def completionSubspaceToAmbientLift :
    (completionSubspace B S hS ⟨X, hX⟩ Z).obj ⟶ X ⋙ uliftFunctor.{u + 1} :=
  (BigFppfOver.topology B S hS).sheafifyLift
    (completionSubspaceSubfunctor B S hS ⟨X, hX⟩ Z).ι hXsheaf

/-- A section of the union of the infinitesimal neighbourhoods of `Z` is carried by
`X^∧_Z ⟶ X` to the section of `X` underlying it. -/
@[simp]
theorem toSheafify_comp_completionSubspaceToAmbientLift :
    (BigFppfOver.topology B S hS).toSheafify
          (completionSubspaceSubfunctor B S hS ⟨X, hX⟩ Z).toFunctor ≫
        completionSubspaceToAmbientLift B S hS hX Z hXsheaf =
      (completionSubspaceSubfunctor B S hS ⟨X, hX⟩ Z).ι :=
  (BigFppfOver.topology B S hS).toSheafify_sheafifyLift _ _

/-- The morphism `X^∧_Z ⟶ X` into the universe lift of `X`, followed by the sheafification
unit of that universe lift, is the morphism `X^∧_Z ⟶ X` into its sheafification: both restrict
along the sheafification unit of the completion subfunctor to the inclusion of that subfunctor
followed by the unit. -/
theorem completionSubspaceToAmbientLift_comp_toSheafify :
    completionSubspaceToAmbientLift B S hS hX Z hXsheaf ≫
        (BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1}) =
      (completionSubspaceToAmbient B S hS ⟨X, hX⟩ Z).hom := by
  refine (BigFppfOver.topology B S hS).sheafify_hom_ext _ _
    ((BigFppfOver.topology B S hS).sheafify_isSheaf _) ?_
  erw [← Category.assoc, toSheafify_comp_completionSubspaceToAmbientLift]
  exact (BigFppfOver.topology B S hS).toSheafify_naturality _

/-- **The morphism `X^∧_Z ⟶ X` is a monomorphism.** Sheafification is left exact, so it carries
the inclusion of the completion subfunctor to a monomorphism, and that monomorphism factors
the morphism into the universe lift through the sheafification unit. -/
theorem mono_completionSubspaceToAmbientLift :
    Mono (completionSubspaceToAmbientLift B S hS hX Z hXsheaf) := by
  have : Mono (completionSubspaceToAmbientLift B S hS hX Z hXsheaf ≫
      (BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1})) := by
    rw [completionSubspaceToAmbientLift_comp_toSheafify]
    exact ((BigFppfOver.topology B S hS).sheafification (Type (u + 1))).map_mono
      (completionSubspaceSubfunctor B S hS ⟨X, hX⟩ Z).ι
  exact mono_of_mono _ ((BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1}))

/-- The comparison morphism `X^∧_Z ⟶ X_{/|Z|}` of Stacks 0H8N is a morphism over `X`: composing
it with the morphism `X_{/|Z|} ⟶ X` gives the morphism `X^∧_Z ⟶ X`. Both are lifts of the
inclusion of the completion subfunctor of `Z`, which is contained in the subfunctor of sections
supported on `|Z|`. -/
theorem completionSubspaceComparison_comp_completionSheafToAmbient :
    (completionSubspaceComparison B S hS ⟨X, hX⟩ Z).hom ≫
        completionSheafToAmbient B S hS X hXsheaf (subspacePoints B S hS Z) =
      completionSubspaceToAmbientLift B S hS hX Z hXsheaf := by
  have hle := completionSubspaceSubfunctor_le_completionSubfunctor B S hS ⟨X, hX⟩ Z
  have hnat : (BigFppfOver.topology B S hS).toSheafify
        (completionSubspaceSubfunctor B S hS ⟨X, hX⟩ Z).toFunctor ≫
      (completionSubspaceComparison B S hS ⟨X, hX⟩ Z).hom =
      Subfunctor.homOfLe hle ≫ (BigFppfOver.topology B S hS).toSheafify
        (completionSubfunctor B S hS X (subspacePoints B S hS Z)).toFunctor :=
    ((BigFppfOver.topology B S hS).toSheafify_naturality _).symm
  refine ((BigFppfOver.topology B S hS).sheafifyLift_unique _ hXsheaf _ ?_)
  erw [← Category.assoc, hnat, Category.assoc,
    toSheafify_comp_completionSheafToAmbient, Subfunctor.homOfLe_ι]

end Space

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (Z : Subfunctor X) (hZ : Space.IsClosedSubspace B S hS Z)
variable (hXsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))

/-! ### A scheme-valued point of the completion is supported on the closed subspace -/

/-- The canonical morphism `Z ⟶ X^∧_Z` is a morphism over `X`: composing it with the morphism
`X^∧_Z ⟶ X` into the universe lift of `X` gives the inclusion of `Z` into `X`, read in the
value universe of the formal algebraic spaces. -/
theorem closedSubspaceToCompletionSubspace_comp_ambientLift :
    (closedSubspaceToCompletionSubspace B S hS hX Z hZ).hom ≫
        Space.completionSubspaceToAmbientLift B S hS hX Z hXsheaf =
      Functor.whiskerRight Z.ι uliftFunctor.{u + 1} := by
  erw [Category.assoc, Space.toSheafify_comp_completionSubspaceToAmbientLift]
  exact closedSubspaceToCompletionSubfunctor_comp_ι B S hS hX Z

/-- **A scheme-valued point of the completion `X^∧_Z` has point-set image in `|Z|`.** The
comparison morphism `X^∧_Z ⟶ X_{/|Z|}` carries it to a scheme-valued point of the completion of
`X` along the closed subset `|Z|` lying over the same scheme-valued point of `X`, and such a
point is supported on `|Z|`. -/
theorem range_pointsMap_subset_subspacePoints {a : BigFppfOver B S hS}
    (g : (uliftYoneda.{u + 1}).obj a ⟶ (Space.completionSubspace B S hS ⟨X, hX⟩ Z).obj)
    {gs : yoneda.obj a ⟶ X}
    (hgs : Functor.whiskerRight gs uliftFunctor.{u + 1} =
      g ≫ Space.completionSubspaceToAmbientLift B S hS hX Z hXsheaf) :
    Set.range (Space.pointsMap B S hS (yoneda.obj a) gs) ⊆ Space.subspacePoints B S hS Z := by
  refine Space.range_pointsMap_subset_of_whiskerRight_eq B S hS
    (Space.subspacePoints B S hS Z) hXsheaf
    (g ≫ (Space.completionSubspaceComparison B S hS ⟨X, hX⟩ Z).hom) ?_
  rw [hgs, Category.assoc,
    Space.completionSubspaceComparison_comp_completionSheafToAmbient B S hS hX Z hXsheaf]

/-! ### The canonical morphism into the completion is a representable thickening -/

/-- **The canonical morphism `Z ⟶ X^∧_Z` is a representable thickening**, which is Stacks 0AI9
for the presentation of `X^∧_Z` by the infinitesimal neighbourhoods of `Z`.

A scheme-valued point of `X^∧_Z` is a scheme-valued point of `X`, because `X^∧_Z ⟶ X` is a
monomorphism and the universe lift of `X` is a sheaf; cancelling that monomorphism exhibits the
base change of `Z ⟶ X^∧_Z` along it as the inverse image of `Z` along a morphism to `X` whose
point set lands in `|Z|`, which is a surjective closed immersion. -/
theorem isRepresentableThickeningULift_toCompletionSubspace :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (closedSubspaceToCompletionSubspace B S hS hX Z hZ).hom := by
  have hXsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}) :=
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X).mpr hX).isSheaf
  have _ : Mono (Space.completionSubspaceToAmbientLift B S hS hX Z hXsheaf) :=
    Space.mono_completionSubspaceToAmbientLift B S hS hX Z hXsheaf
  have _ : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative.of_exists
  intro a g
  obtain ⟨gs, hgs0⟩ := ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
    (Type (u + 1))).obj uliftFunctor.{u + 1}).map_surjective
      (g ≫ Space.completionSubspaceToAmbientLift B S hS hX Z hXsheaf)
  have hgs : Functor.whiskerRight gs uliftFunctor.{u + 1} =
      g ≫ Space.completionSubspaceToAmbientLift B S hS hX Z hXsheaf := hgs0
  obtain ⟨b, snd, fst, sq⟩ := hZ.2.1 gs
  have hsq : IsPullback (Functor.whiskerRight fst uliftFunctor.{u + 1})
      ((uliftYoneda.{u + 1}).map snd)
      (Functor.whiskerRight Z.ι uliftFunctor.{u + 1})
      (Functor.whiskerRight gs uliftFunctor.{u + 1}) :=
    sq.map ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
      (Type (u + 1))).obj uliftFunctor.{u + 1})
  rw [hgs, ← closedSubspaceToCompletionSubspace_comp_ambientLift B S hS hX Z hZ hXsheaf] at hsq
  exact ⟨b, Functor.whiskerRight fst uliftFunctor.{u + 1}, snd,
    isPullback_of_comp_mono _ hsq,
    Space.isThickening_of_isPullback_of_range_subset_of_isClosedSubspace B S hS hZ
      (range_pointsMap_subset_subspacePoints B S hS hX Z hXsheaf g hgs) sq⟩

/-- **Stacks 0GXW.** Let `X` be an algebraic space over `S` and let `Z ⊆ X` be a closed
subspace. The reduction of the completion `X^∧_Z` of `X` along `Z` is `Z_red`: the composite
`Z_red ⟶ Z ⟶ X^∧_Z` exhibits `Z_red` as the reduction of the completion.

Both morphisms are representable thickenings — the first because `Z_red` is a closed subspace
of `X` contained in `Z` with the same point set, the second by
`AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_toCompletionSubspace` — and
`Z_red` is a reduced algebraic space, so the composite exhibits it as the reduction.

This is the unconditional form of
`AlgebraicGeometry.FormalSpace.isReduction_completionSubspace`, which takes the
representability of `Z ⟶ X^∧_Z` as a hypothesis. -/
@[stacks 0GXW]
theorem isReduction_completionSubspace' :
    IsReduction B S hS (Space.completionSubspace B S hS ⟨X, hX⟩ Z)
      (reductionOfClosedSubspaceSheaf B S hS hX Z hZ)
      (reductionInclusion B S hS hX Z hZ ≫
        closedSubspaceToCompletionSubspace B S hS hX Z hZ) :=
  isReduction_of_isRepresentableThickening_closedSubspace B S hS hX Z hZ _
    (isRepresentableThickeningULift_toCompletionSubspace B S hS hX Z hZ)

end FormalSpace

end AlgebraicGeometry

end
