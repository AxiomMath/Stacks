module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovement
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OutsideImageDepth

/-!
# Improving a coherent module: the depth hypothesis discharged

A coherent module on a Noetherian scheme which is canonically the pushforward of its restriction
to an open has depth at least two at the points outside that open ([Stacks, Tag 0EY0] part (3),
for an open immersion). With it, the existence halves of [Stacks, Tag 0EI3] and
[Stacks, Tag 0EI4] hold conditional only on `hext`: the extension of the depth-one quotient
across the subset as a coherent module.

## Main results

* `AlgebraicGeometry.two_le_depth_stalk_of_isIso_unit_outside`: the hypothesis
  `hdepthOutside`, as a theorem.
* `AlgebraicGeometry.exists_isDepthTwoExtension_of_isStabilizedOpenExtension`:
  **[Stacks, Tag 0EI3], existence**, conditional on `hext` alone.
* `AlgebraicGeometry.exists_isNestedImprovement_of_isStabilizedOpenExtension`:
  **[Stacks, Tag 0EI4], existence**, conditional on `hext` alone.

## References

* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0EI4](https://stacks.math.columbia.edu/tag/0EI4)
-/


@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0EY0] part (3), for an open immersion.** A coherent module on a Noetherian
scheme which is canonically the pushforward of its restriction to an open has depth at least two
at every point outside that open. -/
public theorem two_le_depth_stalk_of_isIso_unit_outside (X : Scheme.{u}) [IsNoetherian X]
    (V : X.Opens) (H : X.Modules) (hH : H.IsCoherent)
    (hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H))
    (y : X) (hy : y ∉ (V : Set X)) :
    letI : Module (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) H.val y
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y) := by
  have _ := hH
  have _ : H.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  exact Stacks.AlgebraicGeometry.PushforwardRegularity.two_le_depth_stalk_of_isIso_unit_of_notMem
    V H hunit y hy

/-- A coherent module on a Noetherian scheme admits a map to a coherent module which is an
isomorphism on the stalks away from a specialization-stable subset and whose stalks on that
subset have depth at least two, as soon as the depth-one quotient has a stabilized open
extension across the subset. -/
@[stacks 0EI3 "existence, conditional only on a coherent stabilized open extension of the \
depth-one quotient along the subset; the other hypothesis of \
exists_isDepthTwoExtension, namely Tag 0EY0 part (3), is discharged here"]
public theorem exists_isDepthTwoExtension_of_isStabilizedOpenExtension
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent]
    (hext : ∃ (G : X.Modules) (ψ : depthOneQuotient X T hT F ⟶ G),
      IsStabilizedOpenExtension T ψ) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ :=
  exists_isDepthTwoExtension X T hT F
    (fun V H hH hunit y hy => two_le_depth_stalk_of_isIso_unit_outside X V H hH hunit y hy) hext

/-- A coherent module on a Noetherian scheme admits an improvement along a nested pair `T' ⊆ T`
of subsets stable under specialization, as soon as the depth-one quotient along `T` has a
stabilized open extension across `T'`. -/
@[stacks 0EI4 "existence, conditional only on a coherent stabilized open extension of the \
depth-one quotient along T'; the other hypothesis of exists_isNestedImprovement, namely Tag \
0EY0 part (3), is discharged here"]
public theorem exists_isNestedImprovement_of_isStabilizedOpenExtension
    (X : Scheme.{u}) [IsNoetherian X] (T T' : Set X) (hTT' : T' ⊆ T)
    (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent]
    (hext : ∃ (G : X.Modules) (ψ : depthOneQuotient X T hT F ⟶ G),
      IsStabilizedOpenExtension T' ψ) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsNestedImprovement T T' φ :=
  exists_isNestedImprovement X T T' hTT' hT F
    (fun V H hH hunit y hy => two_le_depth_stalk_of_isIso_unit_outside X V H hH hunit y hy) hext

end AlgebraicGeometry

end
