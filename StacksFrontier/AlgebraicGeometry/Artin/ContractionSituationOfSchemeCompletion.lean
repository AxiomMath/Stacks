module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerSituation
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituationOfSchemeBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineStageAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubsetReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The completion of a local scheme at its closed point, as the `W` of Artin's contraction

Let `A` be a Noetherian local ring with `Spec A` in the big fppf site of `S`, over `S` through a
morphism `σ : Spec A ⟶ S`. This file builds the formal algebraic space
`W = (Spec A)_{/\{𝔪\}}`, the completion of the sheaf represented by `Spec A` along its closed
point, and proves the hypotheses that Situation 0GH8
(`AlgebraicGeometry.Artin.ContractionSituation`) and Stacks 0GIB
(`AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_isSeparated`) put on `W`:

* `W` is locally Noetherian (Stacks 0AQ1, part (2));
* `W` is separated over `S`: it is an affine formal algebraic space (Stacks 0AIY), and every
  morphism out of an affine formal algebraic space is separated;
* the reduced closed subspace `W_red` of `Spec A` on the closed point is the reduction of `W`
  (Stacks 0GB9);
* `W_red` is locally of finite type over `S` as soon as `Spec(A/𝔪) ⟶ Spec A ⟶ S` is: `W_red`
  is the image of the closed immersion `Spec(A/𝔪) ⟶ Spec A` (Stacks 03IQ, uniqueness), hence
  represented by `Spec(A/𝔪)`.

Completeness of `A` is not needed for any of these.

## Main definitions

* `AlgebraicGeometry.FormalSpace.closedPointPoints`: the closed point of `|Spec A|`.
* `AlgebraicGeometry.FormalSpace.completionAtClosedPoint`: the completion `W`.
* `AlgebraicGeometry.FormalSpace.reductionAtClosedPoint`: the reduction `W_red`, and
  `AlgebraicGeometry.FormalSpace.reductionAtClosedPointInclusion` its inclusion into `W`.
* `AlgebraicGeometry.FormalSpace.residueObject` and `AlgebraicGeometry.FormalSpace.residueHom`:
  the closed point `Spec κ ⟶ Spec A` as a morphism of the site.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_completionAtClosedPoint`.
* `AlgebraicGeometry.FormalSpace.isSeparatedMorphism_terminal_from_completionAtClosedPoint`.
* `AlgebraicGeometry.FormalSpace.isReduction_reductionAtClosedPointInclusion`.
* `AlgebraicGeometry.FormalSpace.range_yoneda_map_residueHom_eq_reducedClosedSubspace`: the
  reduced closed subspace on the closed point is the image of `Spec κ`.
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeULift_terminal_from_reductionAtClosedPoint`.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
* [Stacks Project, Tag 0AQ1](https://stacks.math.columbia.edu/tag/0AQ1)
* [Stacks Project, Tag 0GB9](https://stacks.math.columbia.edu/tag/0GB9)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [IsLocalRing A] (hA : B.Contains (Spec (.of A)))
  (σ : Spec (.of A) ⟶ S)

/-- The closed point of `Spec A`, as a set of points of the sheaf represented by `Spec A`: the
points lying over the closed point under the comparison of Stacks 03BV. -/
def closedPointPoints : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hA σ))) :=
  Space.pointsToScheme B S hS (affineOver B S hS hA σ) ⁻¹'
    {(IsLocalRing.closedPoint A : PrimeSpectrum A)}

/-- The closed point of `Spec A` is closed in the point space. -/
theorem isClosed_closedPointPoints : IsClosed (closedPointPoints (hS := hS) hA σ) :=
  Space.isClosed_preimage_pointsToScheme (V := affineOver B S hS hA σ)
    (IsLocalRing.isClosed_singleton_closedPoint A)

/-- **The completion of `Spec A` at its closed point**, `W = (Spec A)_{/\{𝔪\}}`, as an fppf
sheaf of `Type (u + 1)` on the big fppf site of `S` (Stacks 0AMC). -/
abbrev completionAtClosedPoint : FppfSheaf B S hS :=
  Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA σ)) (closedPointPoints hA σ)

/-- **The completion of a Noetherian local scheme at its closed point is locally Noetherian**
(Stacks 0AQ1, part (2)): `Spec A` is a locally Noetherian algebraic space. -/
theorem isLocallyNoetherian_completionAtClosedPoint [IsNoetherianRing A] :
    IsLocallyNoetherian B S hS (completionAtClosedPoint hA σ) :=
  isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian (isAlgebraicSpace_yoneda B S hS _)
    (Space.isLocallyNoetherian_yoneda B S hS _
      (inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of A)))))
    _ (isClosed_closedPointPoints hA σ)

/-- The completion of `Spec A` at its closed point is an affine formal algebraic space
(Stacks 0AIY). -/
theorem isAffineFormalAlgebraicSpace_completionAtClosedPoint :
    IsAffineFormalAlgebraicSpace B S hS (completionAtClosedPoint hA σ) := by
  obtain ⟨I, hI⟩ := exists_zeroLocusPoints_eq_of_isClosed B S hS hA σ _
    (isClosed_closedPointPoints hA σ)
  change IsAffineFormalAlgebraicSpace B S hS
    (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA σ)) (closedPointPoints hA σ))
  rw [hI]
  exact isAffineFormalAlgebraicSpace_zeroLocusCompletion B S hS hA σ I
    (hasStageAtlas B S hS hA σ I)

/-- **The completion of `Spec A` at its closed point is separated over `S`**: its structure
morphism is a morphism out of an affine formal algebraic space, and every such morphism is
separated. -/
theorem isSeparatedMorphism_terminal_from_completionAtClosedPoint :
    IsSeparatedMorphism B S hS (terminal.from (completionAtClosedPoint hA σ)) :=
  isSeparatedMorphism_of_isAffineFormalAlgebraicSpace B S hS _
    (isAffineFormalAlgebraicSpace_completionAtClosedPoint hA σ)

/-- **The reduction of the completion of `Spec A` at its closed point**: the reduced closed
subspace of `Spec A` supported on the closed point (Stacks 03IQ), as an fppf sheaf of
`Type (u + 1)`. It is represented by `Spec(A/𝔪)`, by
`AlgebraicGeometry.FormalSpace.range_yoneda_map_residueHom_eq_reducedClosedSubspace`. -/
abbrev reductionAtClosedPoint : FppfSheaf B S hS :=
  reducedClosedSubsetSheaf B S hS (isAlgebraicSpace_yoneda B S hS _) (closedPointPoints hA σ)
    (isClosed_closedPointPoints hA σ)

/-- The inclusion of the reduction into the completion of `Spec A` at its closed point. -/
abbrev reductionAtClosedPointInclusion :
    reductionAtClosedPoint (hS := hS) hA σ ⟶ completionAtClosedPoint hA σ :=
  reducedClosedSubsetToCompletionSheaf B S hS (isAlgebraicSpace_yoneda B S hS _)
    (closedPointPoints hA σ) (isClosed_closedPointPoints hA σ)

/-- **The reduced closed point is the reduction of the completion** (Stacks 0GB9). -/
theorem isReduction_reductionAtClosedPointInclusion :
    IsReduction B S hS (completionAtClosedPoint hA σ) (reductionAtClosedPoint hA σ)
      (reductionAtClosedPointInclusion hA σ) :=
  isReduction_completionSheaf B S hS (isAlgebraicSpace_yoneda B S hS _) _
    (isClosed_closedPointPoints hA σ)

/-! ### The reduction is the spectrum of the residue field -/

/-- The spectrum of the residue field of `A`, as an object of the site over `S` through the
closed point `Spec κ ⟶ Spec A` and `σ`. -/
abbrev residueObject : BigFppfOver B S hS :=
  siteObject B S hS (B.residueField_spec_contains hA (IsLocalRing.closedPoint A))
    ((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A) ≫ σ)

/-- The closed point `Spec κ ⟶ Spec A`, as a morphism of the site over `S`. -/
abbrev residueHom : residueObject (hS := hS) hA σ ⟶ affineOver B S hS hA σ :=
  Over.homMk (ObjectProperty.homMk ((Spec (.of A)).fromSpecResidueField
    (IsLocalRing.closedPoint A))) rfl

/-- The spectrum of a residue field of a scheme is reduced. (Stated for a variable point:
instance search does not see the residue field of `Spec A` at `IsLocalRing.closedPoint A` as a
field, the point being a point of `PrimeSpectrum A`.) -/
theorem isReduced_spec_residueField (X : Scheme.{u}) (x : X) :
    IsReduced (Spec (.of (X.residueField x))) :=
  inferInstance

/-- The closed point `Spec κ ⟶ Spec A` is a closed immersion. -/
theorem isClosedImmersion_toScheme_map_residueHom :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (residueHom hA σ)) := by
  change _root_.AlgebraicGeometry.IsClosedImmersion
    ((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A))
  exact isClosed_singleton_iff_isClosedImmersion.mp
    (IsLocalRing.isClosed_singleton_closedPoint A)

/-- The closed point `Spec κ ⟶ Spec A` is a monomorphism of the site. -/
theorem mono_residueHom : Mono (residueHom (hS := hS) hA σ) := by
  have _ := isClosedImmersion_toScheme_map_residueHom (hS := hS) hA σ
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance

/-- **The reduced closed subspace of `Spec A` on its closed point is the image of
`Spec κ ⟶ Spec A`** (Stacks 03IQ, uniqueness): that image is a closed subspace, its point set
is the closed point, and it is represented by the reduced scheme `Spec κ`. -/
theorem range_yoneda_map_residueHom_eq_reducedClosedSubspace :
    Subfunctor.range (yoneda.map (residueHom (hS := hS) hA σ)) =
      Space.reducedClosedSubspace B S hS (yoneda.obj (affineOver B S hS hA σ))
        (isAlgebraicSpace_yoneda B S hS _) (closedPointPoints hA σ)
        (isClosed_closedPointPoints hA σ) := by
  have _ := mono_residueHom (hS := hS) hA σ
  have _ : Mono (yoneda.map (residueHom (hS := hS) hA σ)) := inferInstance
  have _ : IsIso (Subfunctor.toRange (yoneda.map (residueHom (hS := hS) hA σ))) :=
    inferInstance
  refine Space.eq_reducedClosedSubspace B S hS _ _ _ _ _
    (Space.isClosedSubspace_range_yoneda_map B S hS _
      (isClosedImmersion_toScheme_map_residueHom hA σ)) ?_ ?_
  · have hlι : Subfunctor.toRange (yoneda.map (residueHom (hS := hS) hA σ)) ≫
        (Subfunctor.range (yoneda.map (residueHom (hS := hS) hA σ))).ι =
          yoneda.map (residueHom hA σ) :=
      Subfunctor.toRange_ι _
    rw [← (Space.pointsMap_surjective_of_isIso B S hS
      (Subfunctor.toRange (yoneda.map (residueHom (hS := hS) hA σ)))).range_comp,
      ← Space.pointsMap_comp, hlι, Space.range_pointsMap_yoneda_map]
    have hr : Set.range ((BigFppfOver.toScheme B S hS).map (residueHom (hS := hS) hA σ)).base =
        {(IsLocalRing.closedPoint A : PrimeSpectrum A)} :=
      Scheme.range_fromSpecResidueField _
    rw [hr, Equiv.image_symm_eq_preimage]
    rfl
  · exact Space.hasEtaleLocalProperty_of_representable B S hS _ (fun Y : Scheme.{u} ↦ IsReduced Y)
      (residueObject hA σ) (asIso (Subfunctor.toRange _)).symm
      (isReduced_spec_residueField _ _)

/-- **The reduction of the completion of `Spec A` at its closed point is locally of finite type
over `S`** as soon as the closed point `Spec κ ⟶ Spec A ⟶ S` is: the reduction is the image of
`Spec κ`, so its structure morphism is that of the represented sheaf of `Spec κ`. -/
theorem isLocallyOfFiniteTypeULift_terminal_from_reductionAtClosedPoint
    (hκ : LocallyOfFiniteType
      ((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A) ≫ σ)) :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
      (terminal.from (reductionAtClosedPoint (hS := hS) hA σ).obj) := by
  change Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
    (terminal.from ((Space.reducedClosedSubspace B S hS (yoneda.obj (affineOver B S hS hA σ))
      (isAlgebraicSpace_yoneda B S hS _) (closedPointPoints hA σ)
      (isClosed_closedPointPoints hA σ)).toFunctor ⋙ uliftFunctor.{u + 1}))
  rw [← range_yoneda_map_residueHom_eq_reducedClosedSubspace hA σ]
  have _ := mono_residueHom (hS := hS) hA σ
  have _ : Mono (yoneda.map (residueHom (hS := hS) hA σ)) := inferInstance
  have _ : IsIso (Subfunctor.toRange (yoneda.map (residueHom (hS := hS) hA σ))) :=
    inferInstance
  let e := asIso (Subfunctor.toRange (yoneda.map (residueHom (hS := hS) hA σ)))
  let t : IsTerminal ((uliftYoneda.{u + 1}).obj (⊤_ (BigFppfOver B S hS))) :=
    terminalIsTerminal.isTerminalObj uliftYoneda.{u + 1} _
  have heq : terminal.from ((Subfunctor.range
      (yoneda.map (residueHom (hS := hS) hA σ))).toFunctor ⋙ uliftFunctor.{u + 1}) =
      (Functor.isoWhiskerRight e.symm uliftFunctor.{u + 1}).hom ≫
        ((uliftYoneda.{u + 1}).map (terminal.from (residueObject (hS := hS) hA σ)) ≫
          (t.uniqueUpToIso terminalIsTerminal).hom) :=
    terminal.hom_ext _ _
  rw [heq]
  refine Space.holdsOnEveryEtaleChartULift_precomp B S hS _ _ _
    (Space.holdsOnEveryEtaleChartULift_postcomp B S hS _ _ _
      (Space.isLocallyOfFiniteTypeULift_uliftYoneda_map B S hS _ ?_))
  rw [Space.toScheme_map_terminal_from_eq]
  have _ := hκ
  exact inferInstanceAs (LocallyOfFiniteType
    (((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A) ≫ σ) ≫ _))

end AlgebraicGeometry.FormalSpace

end
