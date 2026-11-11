module

public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.ClosedAffineBases
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetHenselian
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria.Characterizations
public import StacksFrontier.RingTheory.Henselian.Pair.Nilpotent

/-!
# Closed subsets of `|X|` specializing into a proper subset of `|X₀|`

Let `(Aₙ)` be an inverse system of rings with surjective transitions whose kernels are locally
nilpotent, `A = lim Aₙ`, and `X` an algebraic space separated and of finite presentation over
`A`, with `X₀ = X ×_{Spec A} Spec A₀` (a closed subspace of `X`). Let `Z₀ ⊆ |X₀|` be closed and
proper over `A₀`, and let `W ⊆ |X|` be closed with `W ∩ |X₀| ⊆ Z₀` and such that every point
of `W` specializes to a point of `|X₀|`. Then `W` is proper over `A`.

This is the properness step of the per-degree support clause of the derived form of
Grothendieck's existence theorem proposed in Stacks 0DIR (see the entry for 0DIR in
`errata.md`), there applied to `W = ⋃_{j ≥ i} Supp Hʲ(K)`.

The pair `(A, ker(A → A₀))` is henselian (Stacks 0CT7), `|X₀|` is the set of points of `|X|`
over `V(ker(A → A₀))`, and `W ∩ |X₀|` is the image of a closed subset of `Z₀`, hence proper over
`A` (Stacks 0CZE, 0CZG). So `AlgebraicGeometry.Space.isProperOver_of_forall_specializes_closedFibre`
applies.

## Main results

* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.henselianPair_ker_limit_π`: the pair
  `(A, ker(A → A₀))` is henselian.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.range_pointsMap_spaceProjection_zero`:
  `|X₀|` is the set of points over `V(ker(A → A₀))`.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.isProperOver_of_forall_specializes`:
  the theorem.

## References

* [Stacks Project, Tag 0CT7](https://stacks.math.columbia.edu/tag/0CT7)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem

attribute [local instance] pointTopology

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- **The pair `(A, ker(A → A₀))` is henselian** for `A = lim Aₙ`, the transitions being
surjective with locally nilpotent kernels (Stacks 0CT7). -/
theorem henselianPair_ker_limit_π :
    HenselianPair ↑(limit D.system : CommRingCat) (RingHom.ker (limit.π D.system (op 0)).hom) := by
  have h := henselianRing_ker_limit_π_of_surjective_of_ker_le_nilradical D.system
    (limit.cone D.system) (limit.isLimit D.system)
    (fun n => ⟨D.transition_surjective n,
      fun x hx => mem_nilradical.2 (D.transition_locallyNilpotent n x hx)⟩) 0
  exact @henselianPair_of_henselianRing _ _ _ h

/-- **`|X₀|` is the set of points of `|X|` over `V(ker(A → A₀))`.** -/
theorem range_pointsMap_spaceProjection_zero :
    Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase _
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).hom) =
      pointsMap D.B (limitBase D.system) D.containsLimitBase D.X.left.1 D.X.hom.hom ⁻¹'
        (pointsToScheme D.B (limitBase D.system) D.containsLimitBase
            (limitBaseObject D.system D.B D.containsLimitBase) ⁻¹'
          ((𝟙 _ : (BigFppfOver.toScheme D.B (limitBase D.system) D.containsLimitBase).obj
              (limitBaseObject D.system D.B D.containsLimitBase) ⟶
              Spec (.of ↑(limit D.system : CommRingCat))) ⁻¹'
            PrimeSpectrum.zeroLocus
              (RingHom.ker (limit.π D.system (op 0)).hom :
                Set ↑(limit D.system : CommRingCat)))) := by
  have sq := AlgebraicSpaces.isPullback_hom D.B (limitBase D.system) D.containsLimitBase
    (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X 0)
  have h := preimage_image_pointsMap_of_isPullback D.B (limitBase D.system) D.containsLimitBase
    sq Set.univ
  rw [Set.preimage_univ, Set.image_univ, Set.image_univ] at h
  rw [← h]
  ext w
  have h1 := mem_range_pointsMap_yoneda_map_iff D.B (limitBase D.system) D.containsLimitBase
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt 0)
    (pointsMap D.B (limitBase D.system) D.containsLimitBase D.X.left.1 D.X.hom.hom w)
  have h2 : Set.range ((BigFppfOver.toScheme D.B (limitBase D.system) D.containsLimitBase).map
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt 0)) =
      PrimeSpectrum.zeroLocus
        (RingHom.ker (limit.π D.system (op 0)).hom : Set ↑(limit D.system : CommRingCat)) := by
    change Set.range (PrimeSpectrum.comap (limit.π D.system (op 0)).hom) = _
    exact range_comap_of_surjective _ _
      (GrothendieckExistence.surjective_limit_π D.system D.transition_surjective 0)
  rw [h2] at h1
  exact h1

/-- **A closed subset of `|X|` specializing into a proper subset of `|X₀|` is proper over `A`.**
Let `Z₀ ⊆ |X₀|` be closed and proper over `A₀`, and `W ⊆ |X|` closed, with `W ∩ |X₀|` contained
in the image of `Z₀` and every point of `W` specializing to a point of `|X₀|`. Then `W` is proper
over `A`. -/
theorem isProperOver_of_forall_specializes
    (Z₀ : Set (points D.B (limitBase D.system) D.containsLimitBase
      (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).1))
    (hZ₀ : IsClosed Z₀)
    (hZ₀p : IsProperOver D.B (limitBase D.system) D.containsLimitBase
      (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).2
      (schemeSpace (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt 0)).2
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).hom
      (isLocallyOfFiniteType_spaceBaseProjection D.system D.B D.containsLimitBase
        D.containsBaseAt D.X
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
          D.containsLimitBase D.finitePresentation.1) 0)
      Z₀ hZ₀)
    (W : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1)) (hW : IsClosed W)
    (hWZ : W ∩ Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase _
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).hom) ⊆
      pointsMap D.B (limitBase D.system) D.containsLimitBase _
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).hom '' Z₀)
    (hspec : ∀ x ∈ W, ∃ y ∈ Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase _
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).hom), x ⤳ y) :
    IsProperOver D.B (limitBase D.system) D.containsLimitBase D.X.left.2
      (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
        D.containsLimitBase D.finitePresentation.1) W hW := by
  let X₀ := spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X 0
  let ι := spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0
  let q := spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0
  let b := baseSpaceProjection D.system D.B D.containsLimitBase D.containsBaseAt 0
  have hX := D.X.left.2
  have hA := (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2
  have hft : IsFiniteType D.B (limitBase D.system) D.containsLimitBase D.X.hom.hom :=
    isFiniteType_of_isFinitePresentation _ _ _ D.finitePresentation
  have hrange := D.range_pointsMap_spaceProjection_zero
  -- `W ∩ |X₀|` is the image of the closed subset `ι⁻¹(W) ∩ Z₀` of `Z₀`.
  set Z := pointsMap D.B (limitBase D.system) D.containsLimitBase X₀.1 ι.hom ⁻¹' W ∩ Z₀
  have hZc : IsClosed Z := (hW.preimage (continuous_pointsMap _ _ _ ι.hom)).inter hZ₀
  have hWZ' : W ∩ Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase X₀.1 ι.hom) =
      pointsMap D.B (limitBase D.system) D.containsLimitBase X₀.1 ι.hom '' Z := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := hWZ hx
      exact ⟨z, ⟨hx.1, hz⟩, rfl⟩
    · rintro _ ⟨z, ⟨hzW, -⟩, rfl⟩
      exact ⟨hzW, z, rfl⟩
  have hιc : IsClosedImmersion D.B (limitBase D.system) D.containsLimitBase ι.hom :=
    isClosedImmersion_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective 0
  have hbp : IsProper D.B (limitBase D.system) D.containsLimitBase b.hom :=
    isProper_of_isClosedImmersion _ _ _ (schemeSpace _).2 (schemeSpace _).2 _
      (isClosedImmersion_baseSpaceProjection D.system D.B D.containsLimitBase D.containsBaseAt
        D.transition_surjective 0)
  have hw : ι.hom ≫ D.X.hom.hom = q.hom ≫ b.hom :=
    (AlgebraicSpaces.isPullback_hom D.B (limitBase D.system) D.containsLimitBase
      (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X 0)).w.symm
  have hqft := isLocallyOfFiniteType_spaceBaseProjection D.system D.B D.containsLimitBase
    D.containsBaseAt D.X hft.1 0
  -- `Z` is proper over `A₀`, hence over `A`.
  have hlft : IsLocallyOfFiniteType D.B (limitBase D.system) D.containsLimitBase
      (ι.hom ≫ D.X.hom.hom) := by
    rw [hw]
    exact isLocallyOfFiniteType_comp _ _ _ X₀.2 (schemeSpace _).2 (schemeSpace _).2 _ _ hqft
      hbp.2.1.1
  have hZp : IsProperOver D.B (limitBase D.system) D.containsLimitBase X₀.2 hA
      (ι.hom ≫ D.X.hom.hom) hlft Z hZc := by
    have h := isProperOver_of_subset _ _ _ X₀.2 (schemeSpace _).2 q.hom hqft Z Z₀ hZc hZ₀
      Set.inter_subset_right hZ₀p
    change IsProper D.B (limitBase D.system) D.containsLimitBase (_ ≫ ι.hom ≫ D.X.hom.hom)
    rw [hw, ← Category.assoc]
    exact isProper_comp _ _ _ (isAlgebraicSpace_reducedClosedSubspace _ _ _ _ X₀.2 Z hZc)
      (schemeSpace _).2 (schemeSpace _).2 _ _ h hbp
  -- So `W ∩ |X₀|` is proper over `A`.
  have hT₀ := isProperOver_image_of_universallyClosed _ _ _ X₀.2 hX hA ι.hom D.X.hom.hom
    (universallyClosed_of_isClosedImmersion _ _ _ X₀.2 hX _ hιc) _ hft.1 Z hZc hZp
  refine isProperOver_of_forall_specializes_closedFibre D.B (limitBase D.system)
    D.containsLimitBase ↑(limit D.system : CommRingCat)
    (RingHom.ker (limit.π D.system (op 0)).hom) D.henselianPair_ker_limit_π
    (𝟙 _ : (BigFppfOver.toScheme D.B (limitBase D.system) D.containsLimitBase).obj
      (limitBaseObject D.system D.B D.containsLimitBase) ⟶
      Spec (.of ↑(limit D.system : CommRingCat)))
    hX D.X.hom.hom D.separated hft W hW ?_ ?_
  · have key : ∀ (T T' : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1))
        (hT : IsClosed T) (hT' : IsClosed T'), T = T' →
        IsProperOver D.B (limitBase D.system) D.containsLimitBase hX hA D.X.hom.hom hft.1 T hT →
        IsProperOver D.B (limitBase D.system) D.containsLimitBase hX hA D.X.hom.hom hft.1 T'
          hT' := by
      rintro T _ hT hT' rfl h
      exact h
    exact key _ _ _ _ (hWZ'.symm.trans (congrArg (W ∩ ·) hrange)) hT₀
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hspec x hx
    exact ⟨y, ⟨hW.stableUnderSpecialization hxy hx, (Set.ext_iff.1 hrange y).1 hy⟩, hxy⟩

end AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem

end
