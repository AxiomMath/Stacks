module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImageDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardModuleLength
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingGenericPointField
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralDominantMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralGenericallyFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPushforwardFibreLength
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactDiagonalQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The integral image of an integral closed subspace, its degree, and the generic length

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` with `X` decent, and let `Z ⊂ Y` be an
integral closed subspace. Its image `f(Z) ⊂ X` is the integral closed subspace of `X` on the
closure of `f(|Z|)`, `AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage`, and this
file records the facts about `Z ⟶ f(Z)` which the proof of Stacks 0EDJ uses:

1. `f(Z)` is the scheme-theoretic image of `Z ⟶ X`, by Stacks 0830;
2. for `f` proper and `X` locally Noetherian, `dim Z = dim f(Z) + r`, where `r` is the
   transcendence degree of the generic point of `Z` over that of `f(Z)` (Stacks 0EDC), so that
   `dim f(Z) ≤ dim Z`, and when the two dimensions are the same finite number the equivalent
   conditions of Stacks 0AD5 hold for `Z ⟶ f(Z)`: its degree (Stacks 0AD6) is positive and the
   generic point of `Z` is the only point over the generic point of `f(Z)`;
3. in that case the direct image `(Z ⟶ X)_*𝒪_Z` has length `deg(Z/f(Z))` at every geometric
   point over the generic point of `f(Z)`, and its higher direct images vanish there.

The third item is the "generic rank" computation of the source: the source reads
`deg(Z → f(Z))` as the length of the stalk of `f_*𝒪_Z` at the generic point `ξ` of `f(Z)`, the
morphism being finite over a neighbourhood of `ξ`. Here it is the general formula
`AlgebraicGeometry.Space.geometricLength_modulePushforward_toNat_eq_finsum` for the length of a
proper direct image at a point with finite fibre, evaluated on a fibre with one point, the
generic point `ζ` of `Z`, where the length of `𝒪_Z` is one because `Z` is integral.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.toClosureImage`: the morphism `Z ⟶ f(Z)`.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage_subspace_eq_schemeTheoreticImage`:
  `f(Z)` is the scheme-theoretic image of `Z ⟶ X`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.dimension_eq_dimension_closureImage_add`:
  `dim Z = dim f(Z) + r`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.dimension_closureImage_le`: `dim f(Z) ≤ dim Z`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.hasTranscendenceDegreeAt_zero_of_dimension_eq`:
  equal finite dimensions force transcendence degree zero.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.degree_toClosureImage_pos`: the degree of
  `Z ⟶ f(Z)` is then positive.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.geometricLength_modulePushforward_eq_degree`:
  the length of the direct image of `𝒪_Z` at a geometric point over the generic point of
  `f(Z)` is `deg(Z/f(Z))`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.supportOfSheaf_modulePushforward_subset`,
  `AlgebraicGeometry.Space.IntegralClosedSubspace.mem_supportOfSheaf_modulePushforward` and
  `AlgebraicGeometry.Space.IntegralClosedSubspace.supportOfSheaf_modulePushforward_eq`: that
  direct image is supported in `f(Z)`, its support contains the generic point of `f(Z)` in the
  equidimensional case, and so is all of `f(Z)` once it is closed.
* `AlgebraicGeometry.Space.notMem_supportOfSheaf_rightDerived_modulePushforward_of_finite`: for a
  proper morphism of decent spaces and a quasi-coherent module, the higher direct images vanish
  at every point with finite fibre.
* `IntegralClosedSubspace.supportOfSheaf_rightDerived_modulePushforward_subset`:
  every `R^q (Z ⟶ X)_*𝒪_Z` is supported in `f(Z)`.
* `IntegralClosedSubspace.notMem_supportOfSheaf_rightDerived_modulePushforward`:
  in the equidimensional case the higher direct images `R^q (Z ⟶ X)_*𝒪_Z`, `q > 0`, vanish at
  the generic point of `f(Z)` — the source's appeal to Stacks 0A4K, carried out through a finite
  affine étale chart (Stacks 03LX and 073H).
* `AlgebraicGeometry.Space.isDecentSpace_of_isProper_baseObject` and
  `AlgebraicGeometry.Space.isProper_of_isProper_baseObject`: an algebraic space proper over an
  affine base is decent, and a morphism between two such spaces is proper. These are the
  hypotheses above, in the situation of Stacks 0EDJ.

## References

* [Stacks Project, Tag 0EDJ](https://stacks.math.columbia.edu/tag/0EDJ)
* [Stacks Project, Tag 0830](https://stacks.math.columbia.edu/tag/0830)
* [Stacks Project, Tag 0EDC](https://stacks.math.columbia.edu/tag/0EDC)
* [Stacks Project, Tag 0AD5](https://stacks.math.columbia.edu/tag/0AD5)
* [Stacks Project, Tag 0AD6](https://stacks.math.columbia.edu/tag/0AD6)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 07TY](https://stacks.math.columbia.edu/tag/07TY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The image as a scheme-theoretic image -/

/-- **Stacks 0830, for the image of an integral closed subspace.** The integral closed
subspace of `X` on the closure of `f(|Z|)` is the scheme-theoretic image of `Z ⟶ X`: `Z` is
reduced, so that image is the reduced closed subspace on the closure of the image of its point
map. -/
theorem IntegralClosedSubspace.closureImage_subspace_eq_schemeTheoreticImage
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X) (f : Y ⟶ X)
    (Z : IntegralClosedSubspace B S hS Y) :
    (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace =
      schemeTheoreticImageSubfunctor B S hS (Z.subspace.ι ≫ f) :=
  (schemeTheoreticImageSubfunctor_eq_of_isReduced_of_range_pointsMap_eq B S hS _
    Z.isClosedSubspace.1 hX Z.isIntegralSpace.1
    (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace
    (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isIntegralSpace.1
    (by
      rw [IntegralClosedSubspace.range_pointsMap_ι_comp B S hS f Z]
      exact IntegralClosedSubspace.subspacePointSet_closureImage B S hS hX hXdec f Z)).symm

/-- The morphism `Z ⟶ f(Z)` from an integral closed subspace to its image: the factorization
of `Z ⟶ X` through its scheme-theoretic image. -/
@[ega "IV 6.11.9" "partial"]
noncomputable def IntegralClosedSubspace.toClosureImage (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (f : Y ⟶ X) (Z : IntegralClosedSubspace B S hS Y) :
    Z.subspace.toFunctor ⟶
      (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace.toFunctor :=
  Subfunctor.lift (Z.subspace.ι ≫ f) (by
    rw [IntegralClosedSubspace.closureImage_subspace_eq_schemeTheoreticImage B S hS hX hXdec f Z]
    exact range_le_schemeTheoreticImageSubfunctor B S hS _)

/-- The morphism `Z ⟶ f(Z)` followed by the inclusion `f(Z) ⟶ X` is `Z ⟶ Y ⟶ X`. -/
@[reassoc (attr := simp)]
theorem IntegralClosedSubspace.toClosureImage_ι (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (f : Y ⟶ X) (Z : IntegralClosedSubspace B S hS Y) :
    IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z ≫
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace.ι =
      Z.subspace.ι ≫ f :=
  Subfunctor.lift_ι _ _

/-- The morphism `Z ⟶ f(Z)` is dominant. -/
theorem IntegralClosedSubspace.isDominant_toClosureImage (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (f : Y ⟶ X) (Z : IntegralClosedSubspace B S hS Y) :
    IsDominant B S hS (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) :=
  IntegralClosedSubspace.isDominant_of_comp_ι_eq_closureImage B S hS hX hXdec f Z _
    (IntegralClosedSubspace.toClosureImage_ι B S hS hX hXdec f Z)

/-- The morphism `Z ⟶ f(Z)` is proper when `f` is. -/
theorem IntegralClosedSubspace.isProper_toClosureImage (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X) (f : Y ⟶ X)
    (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y) :
    IsProper B S hS (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) :=
  IntegralClosedSubspace.isProper_of_comp_ι_eq B S hS hY hX f hf Z _ _
    (IntegralClosedSubspace.toClosureImage_ι B S hS hX hXdec f Z)

/-- The generic point of `Z` maps to the generic point of `f(Z)`. -/
theorem IntegralClosedSubspace.isGenericPoint_pointsMap_toClosureImage
    (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (f : Y ⟶ X) (Z : IntegralClosedSubspace B S hS Y) :
    IsGenericPoint
      (pointsMap B S hS Z.subspace.toFunctor
        (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z)
        (Z.genericPoint B S hS))
      (Set.univ : Set (points B S hS
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace.toFunctor)) :=
  isGenericPoint_pointsMap_of_isDominant B S hS _
    (IntegralClosedSubspace.isDominant_toClosureImage B S hS hX hXdec f Z)
    (Z.closure_singleton_genericPoint B S hS)

/-! ### Dimension and degree -/

/-- The datum of Stacks 0EDC attached to `Z ⟶ f(Z)`, for a proper `f` into a locally Noetherian
algebraic space: the two integral spaces, the dominant morphism of finite type between them,
and their generic points. -/
noncomputable abbrev IntegralClosedSubspace.toClosureImageSituation (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (hXLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y) :
    IntegralDominantMorphismSituation B S hS where
  source := Z.subspace.toFunctor
  target := (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace.toFunctor
  hom := IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z
  isAlgebraicSpace_source := Z.isClosedSubspace.1
  isAlgebraicSpace_target :=
    (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace.1
  locallyNoetherian_target :=
    hasEtaleLocalProperty_isLocallyNoetherian_closedSubfunctor B S hS ⟨X, hX⟩ hXLN
      (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace
  isIntegralSpace_source := Z.isIntegralSpace
  isIntegralSpace_target :=
    (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isIntegralSpace
  isDominant := IntegralClosedSubspace.isDominant_toClosureImage B S hS hX hXdec f Z
  isLocallyOfFiniteType :=
    (IntegralClosedSubspace.isProper_toClosureImage B S hS hY hX hXdec f hf Z).2.1.1
  sourcePoint := Z.genericPoint B S hS
  targetPoint := pointsMap B S hS Z.subspace.toFunctor
    (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS)
  isGenericPoint_sourcePoint := Z.closure_singleton_genericPoint B S hS
  isGenericPoint_targetPoint :=
    IntegralClosedSubspace.isGenericPoint_pointsMap_toClosureImage B S hS hX hXdec f Z

/-- **Stacks 0EDC for `Z ⟶ f(Z)`.** For a proper morphism `f : Y ⟶ X` into a decent locally
Noetherian algebraic space, the dimension of an integral closed subspace `Z ⊂ Y` is the
dimension of its image plus the transcendence degree of the generic point of `Z` over that of
`f(Z)`. -/
theorem IntegralClosedSubspace.dimension_eq_dimension_closureImage_add
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (hXLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y) :
    dimension B S hS Z.subspace.toFunctor Z.isClosedSubspace.1 =
      dimension B S hS
          (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace.toFunctor
          (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace.1 +
        (residueFieldTranscendenceDegreeAt B S hS
          (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS) :
            WithBot ℕ∞) :=
  dimension_eq_dimension_add_transcendenceDegree B S hS
    (IntegralClosedSubspace.toClosureImageSituation B S hS hY hX hXdec hXLN f hf Z)
    (IntegralClosedSubspace.isProper_toClosureImage B S hS hY hX hXdec f hf Z) _
    ((residueFieldTranscendenceDegreeAt_eq_iff B S hS _ Z.isClosedSubspace.1
      (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace.1 _ _).1 rfl)

/-- The image of an integral closed subspace under a proper morphism into a decent locally
Noetherian algebraic space has dimension at most that of the subspace. -/
theorem IntegralClosedSubspace.dimension_closureImage_le
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (hXLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y) :
    dimension B S hS
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace.toFunctor
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace.1 ≤
      dimension B S hS Z.subspace.toFunctor Z.isClosedSubspace.1 := by
  rw [IntegralClosedSubspace.dimension_eq_dimension_closureImage_add B S hS hY hX hXdec hXLN f hf Z]
  exact le_add_of_nonneg_right (WithBot.coe_nonneg.mpr (by simp))

/-- If an integral closed subspace and its image under a proper morphism into a decent locally
Noetherian algebraic space have the same finite dimension, the transcendence degree of the
generic point of `Z` over that of `f(Z)` is zero: this is condition (1) of Stacks 0AD5 for
`Z ⟶ f(Z)`, as in the proof of Stacks 0EDJ. -/
theorem IntegralClosedSubspace.hasTranscendenceDegreeAt_zero_of_dimension_eq
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (hXLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y) (d : ℕ)
    (hZ : dimension B S hS Z.subspace.toFunctor Z.isClosedSubspace.1 = d)
    (hfZ : dimension B S hS
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace.toFunctor
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace.1 = d) :
    HasTranscendenceDegreeAt B S hS (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z)
      (Z.genericPoint B S hS) 0 := by
  have h := IntegralClosedSubspace.dimension_eq_dimension_closureImage_add B S hS hY hX hXdec
    hXLN f hf Z
  rw [hZ, hfZ] at h
  refine (residueFieldTranscendenceDegreeAt_eq_iff B S hS _ Z.isClosedSubspace.1
    (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace.1 _ _).1 ?_
  generalize residueFieldTranscendenceDegreeAt B S hS _ _ = r at h ⊢
  have h' : ((d : ℕ∞) : WithBot ℕ∞) = ((d + r : ℕ∞) : WithBot ℕ∞) := by
    exact_mod_cast h
  have h'' : (d : ℕ∞) = d + r := WithBot.coe_injective h'
  induction r using ENat.recTopCoe with
  | top => simp at h''
  | coe r =>
    have : d = d + r := by exact_mod_cast h''
    exact_mod_cast (by omega : r = 0)

/-- **Stacks 0AD5 for `Z ⟶ f(Z)`.** If the transcendence degree of the generic point of `Z` over
that of `f(Z)` is zero, the residue field extension at the generic point of `Z` is finite, and
the generic point of `Z` is the only point of `Z` over the generic point of `f(Z)`. -/
theorem IntegralClosedSubspace.finite_and_unique_of_hasTranscendenceDegreeAt_zero
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y)
    (h0 : HasTranscendenceDegreeAt B S hS
      (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS) 0) :
    HasFiniteResidueFieldExtensionAt B S hS
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace.1
        Z.isIntegralSpace.2.1
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isIntegralSpace.2.1
        (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS) ∧
      ∀ z : points B S hS Z.subspace.toFunctor,
        pointsMap B S hS Z.subspace.toFunctor
            (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) z =
          pointsMap B S hS Z.subspace.toFunctor
            (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS) →
        z = Z.genericPoint B S hS := by
  have h := (tfae_hasTranscendenceDegreeAt_eq_zero_and_isFiniteOverAffineOpen B S hS
    Z.isClosedSubspace.1
    (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace.1
    Z.isIntegralSpace (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isIntegralSpace
    (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z)
    (IntegralClosedSubspace.isProper_toClosureImage B S hS hY hX hXdec f hf Z).2.1.1
    (IntegralClosedSubspace.isDominant_toClosureImage B S hS hX hXdec f Z)
    (Z.closure_singleton_genericPoint B S hS)
    (IntegralClosedSubspace.isGenericPoint_pointsMap_toClosureImage B S hS hX hXdec f Z)).1
  exact ⟨(h.out 1 2).1 h0, (h.out 1 5).1 h0⟩

/-- **The degree of `Z ⟶ f(Z)` is positive** (Stacks 0AD6) once the transcendence degree of the
generic point of `Z` over that of `f(Z)` is zero. -/
theorem IntegralClosedSubspace.degree_toClosureImage_pos
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y)
    (h0 : HasTranscendenceDegreeAt B S hS
      (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS) 0) :
    0 < degree B S hS Z.isClosedSubspace.1
      (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace.1
      Z.isIntegralSpace (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isIntegralSpace
      (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) :=
  degree_pos B S hS _ _ _ _ _ (Z.closure_singleton_genericPoint B S hS)
    (IntegralClosedSubspace.finite_and_unique_of_hasTranscendenceDegreeAt_zero B S hS hY hX hXdec
      f hf Z h0).1

/-! ### The length of the direct image at the generic point of the image -/

/-- For `f` proper, the composite `Z ⟶ Y ⟶ X` of an integral closed subspace is proper. -/
private theorem isProper_ι_comp (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y) :
    IsProper B S hS (Z.subspace.ι ≫ f) :=
  isProper_comp B S hS Z.isClosedSubspace.1 hY hX Z.subspace.ι f
      (isProper_of_isClosedImmersion B S hS Z.isClosedSubspace.1 hY Z.subspace.ι
        Z.isClosedSubspace.2) hf

/-- The point map of `Z ⟶ Y ⟶ X` factors through `Z ⟶ f(Z) ⟶ X`. -/
private theorem pointsMap_ι_comp_eq_pointsMap_toClosureImage
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X) (f : Y ⟶ X)
    (Z : IntegralClosedSubspace B S hS Y) (z : points B S hS Z.subspace.toFunctor) :
    pointsMap B S hS Z.subspace.toFunctor (Z.subspace.ι ≫ f) z =
      pointsMap B S hS (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace.toFunctor
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace.ι
        (pointsMap B S hS Z.subspace.toFunctor
          (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) z) := by
  rw [← IntegralClosedSubspace.toClosureImage_ι B S hS hX hXdec f Z, pointsMap_comp_apply]

/-- Under the hypothesis of Stacks 0AD5, the fibre of `Z ⟶ X` over the generic point `η` of
`f(Z)` is the generic point of `Z` alone. -/
theorem IntegralClosedSubspace.setOf_pointsMap_eq_eq_singleton
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y)
    (h0 : HasTranscendenceDegreeAt B S hS
      (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS) 0)
    {η : points B S hS X}
    (hη : IsGenericPoint η (subspacePointSet B S hS X
      (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace)) :
    {z : points B S hS Z.subspace.toFunctor |
        pointsMap B S hS Z.subspace.toFunctor (Z.subspace.ι ≫ f) z = η} =
      {Z.genericPoint B S hS} := by
  set W := IntegralClosedSubspace.closureImage B S hS hX hXdec f Z
  set t := IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z
  have : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hXdec
  have hgt := pointsMap_ι_comp_eq_pointsMap_toClosureImage B S hS hX hXdec f Z
  have hηζ : η = pointsMap B S hS Z.subspace.toFunctor (Z.subspace.ι ≫ f)
      (Z.genericPoint B S hS) := by
    rw [hη.eq (IntegralClosedSubspace.isGenericPoint_pointsMap_ambientGenericPoint B S hS hY hX
      hXdec f Z)]
    exact (pointsMap_comp_apply B S hS Z.subspace.ι f _).symm
  have : Mono W.subspace.ι := inferInstanceAs (Mono (Subfunctor.ι _))
  have hinj := pointsMap_injective_of_mono B S hS W.subspace.ι
  have huniq := (IntegralClosedSubspace.finite_and_unique_of_hasTranscendenceDegreeAt_zero B S hS
    hY hX hXdec f hf Z h0).2
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun hz => huniq z (hinj ?_), fun hz => hz ▸ hηζ.symm⟩
  rw [← hgt, ← hgt, hz, hηζ]


/-- **The generic rank of the direct image of `𝒪_Z`, Stacks 0EDJ.** Let `f : Y ⟶ X` be a proper
morphism into a decent locally Noetherian algebraic space, let `Z ⊂ Y` be an integral closed
subspace whose generic point has transcendence degree zero over the generic point `η` of its
image `f(Z)`, and let `ȳ` be a geometric point of `X` over `η`. Then the direct image of `𝒪_Z`
along `Z ⟶ X` has length `deg(Z/f(Z))` at `ȳ`.

By Stacks 0AD5 the generic point `ζ` of `Z` is the only point of `Z` over `η`, so the formula
for the length of a proper direct image at a point with finite fibre has a single term,
`length_ζ(𝒪_Z) · [κ(ζ) : κ(η)]`; the length is one because `Z` is integral, and the residue
degree of `Z ⟶ X` at `ζ` is that of `Z ⟶ f(Z)`, the inclusion `f(Z) ⟶ X` being a monomorphism. -/
theorem IntegralClosedSubspace.geometricLength_modulePushforward_eq_degree
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (hXLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y)
    (h0 : HasTranscendenceDegreeAt B S hS
      (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS) 0)
    {η : points B S hS X}
    (hη : IsGenericPoint η (subspacePointSet B S hS X
      (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace))
    (ybar : GeometricPoint B S hS X) (hybar : ybar.LiesOver η) :
    geometricLength B S hS ⟨X, hX⟩ ybar
        ((modulePushforward B S hS
          (ObjectProperty.homMk (Z.subspace.ι ≫ f) :
            (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨X, hX⟩)).obj
          (structureSheafModule B S hS ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩)) =
      degree B S hS Z.isClosedSubspace.1
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isClosedSubspace.1
        Z.isIntegralSpace (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).isIntegralSpace
        (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) := by
  classical
  set W := IntegralClosedSubspace.closureImage B S hS hX hXdec f Z with hW
  set t := IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z with ht
  set ζ := Z.genericPoint B S hS with hζ
  let ZA : AlgebraicSpaces B S hS := ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩
  let XA : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let g : ZA ⟶ XA := ObjectProperty.homMk (Z.subspace.ι ≫ f)
  have hZdec : IsDecentSpace B S hS Z.subspace.toFunctor := Z.isIntegralSpace.2.1
  have hWdec : IsDecentSpace B S hS W.subspace.toFunctor := W.isIntegralSpace.2.1
  have : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hXdec
  have hZf := isProper_ι_comp B S hS hY hX f hf Z
  have : Fact (HasEtaleLocalProperty B S hS Z.subspace.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) :=
    ⟨isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z.isClosedSubspace.1 hX
      (Z.subspace.ι ≫ f) hZf.2.1.1 hXLN⟩
  have hg : IsProper B S hS g.hom := hZf
  have hgt := pointsMap_ι_comp_eq_pointsMap_toClosureImage B S hS hX hXdec f Z
  have hfibre : {z : points B S hS ZA.1 | pointsMap B S hS ZA.1 g.hom z = η} = {ζ} :=
    IntegralClosedSubspace.setOf_pointsMap_eq_eq_singleton B S hS hY hX hXdec f hf Z h0 hη
  have hmax : ∀ z ∈ supportOfSheaf B S hS ZA.1
      ((SheafOfModules.toSheaf _).obj (structureSheafModule B S hS ZA)),
      η ∈ closure {pointsMap B S hS ZA.1 g.hom z} → pointsMap B S hS ZA.1 g.hom z = η := by
    intro z _ hcl
    have hmem : pointsMap B S hS ZA.1 g.hom z ∈ closure {η} := by
      rw [hη]
      exact ⟨_, (hgt z).symm⟩
    exact ((specializes_iff_mem_closure.2 hcl).antisymm (specializes_iff_mem_closure.2 hmem)).eq
  have hL := geometricLength_modulePushforward_toNat_eq_finsum B S hS (Z := ZA) (Y := XA) hZdec
    hXdec hXLN g hg (structureSheafModule B S hS ZA) η (hfibre ▸ Set.finite_singleton ζ) hmax
    ybar hybar (canonicalGeometricPoint B S hS ZA.1) (canonicalGeometricPoint_image B S hS ZA.1)
  rw [hfibre, finsum_mem_singleton] at hL
  have hgenZ : ζ ∈ genericPoints (points B S hS ZA.1) := by
    have : IrreducibleSpace (points B S hS ZA.1) := Z.isIntegralSpace.2.2
    change closure {ζ} ∈ irreducibleComponents _
    rw [Z.closure_singleton_genericPoint B S hS, irreducibleComponents_eq_singleton]
    rfl
  have hone := geometricLength_structureSheafModule_eq_one_of_isIntegralSpace B S hS ZA
    Z.isIntegralSpace (canonicalGeometricPoint B S hS ZA.1 ζ)
    ((canonicalGeometricPoint_image B S hS ZA.1 ζ).symm ▸ hgenZ)
  have hdeg : residueFieldDegreeAt B S hS hX hZdec hXdec g.hom ζ =
      residueFieldDegreeAt B S hS W.isClosedSubspace.1 hZdec hWdec t ζ := by
    change residueFieldDegreeAt B S hS hX hZdec hXdec (Z.subspace.ι ≫ f) ζ = _
    rw [← IntegralClosedSubspace.toClosureImage_ι B S hS hX hXdec f Z,
      residueFieldDegreeAt_comp B S hS W.isClosedSubspace.1 hX hZdec hWdec hXdec t W.subspace.ι ζ,
      residueFieldDegreeAt_eq_one_of_mono B S hS hX hWdec hXdec W.subspace.ι, mul_one]
  have hdegree : degree B S hS Z.isClosedSubspace.1 W.isClosedSubspace.1 Z.isIntegralSpace
      W.isIntegralSpace t = residueFieldDegreeAt B S hS W.isClosedSubspace.1 hZdec hWdec t ζ :=
    degree_eq_residueFieldDegreeAt B S hS Z.isClosedSubspace.1 W.isClosedSubspace.1
      Z.isIntegralSpace W.isIntegralSpace t (Z.closure_singleton_genericPoint B S hS)
  rw [hone, hdeg, ENat.toNat_one, one_mul, ← hdegree] at hL
  have hpos := IntegralClosedSubspace.degree_toClosureImage_pos B S hS hY hX hXdec f hf Z h0
  have hne : geometricLength B S hS XA ybar
      ((modulePushforward B S hS g).obj (structureSheafModule B S hS ZA)) ≠ ⊤ := fun htop => by
    rw [htop, ENat.toNat_top] at hL
    exact hpos.ne hL
  rw [← hL, ENat.natCast_toNat hne]

/-! ### The support of the direct image -/

/-- The support of the direct image of `𝒪_Z` along `Z ⟶ X` lies in the image `f(Z)`: a direct
image is supported in the closure of the image of the support. -/
theorem IntegralClosedSubspace.supportOfSheaf_modulePushforward_subset
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X) (f : Y ⟶ X)
    (Z : IntegralClosedSubspace B S hS Y) :
    supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj
        ((modulePushforward B S hS
          (ObjectProperty.homMk (Z.subspace.ι ≫ f) :
            (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨X, hX⟩)).obj
          (structureSheafModule B S hS ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩))) ⊆
      subspacePointSet B S hS X
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace := by
  refine (supportOfSheaf_modulePushforward_subset_closure B S hS
    (X := ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩) (Y := ⟨X, hX⟩)
    (ObjectProperty.homMk (Z.subspace.ι ≫ f)) _).trans ?_
  rw [IntegralClosedSubspace.subspacePointSet_closureImage B S hS hX hXdec f Z,
    ← IntegralClosedSubspace.range_pointsMap_ι_comp B S hS f Z]
  exact closure_mono (Set.image_subset_range _ _)

/-- Under the hypothesis of
`AlgebraicGeometry.Space.IntegralClosedSubspace.geometricLength_modulePushforward_eq_degree`,
the generic point of `f(Z)` lies in the support of the direct image of `𝒪_Z`: the length there
is the degree of `Z ⟶ f(Z)`, which is positive. -/
theorem IntegralClosedSubspace.mem_supportOfSheaf_modulePushforward
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (hXLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y)
    (h0 : HasTranscendenceDegreeAt B S hS
      (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS) 0)
    {η : points B S hS X}
    (hη : IsGenericPoint η (subspacePointSet B S hS X
      (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace)) :
    η ∈ supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj
        ((modulePushforward B S hS
          (ObjectProperty.homMk (Z.subspace.ι ≫ f) :
            (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨X, hX⟩)).obj
          (structureSheafModule B S hS ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩))) := by
  have hg := isProper_ι_comp B S hS hY hX f hf Z
  have := isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS
    (ObjectProperty.homMk (Z.subspace.ι ≫ f) :
      (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
    hg.2.1.2 (isQuasiSeparated_of_isSeparated B S hS hg.1)
    (structureSheafModule B S hS ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩) inferInstance
  have hpos := IntegralClosedSubspace.degree_toClosureImage_pos B S hS hY hX hXdec f hf Z h0
  have hlen := IntegralClosedSubspace.geometricLength_modulePushforward_eq_degree B S hS hY hX
    hXdec hXLN f hf Z h0 hη (canonicalGeometricPoint B S hS X η)
    (canonicalGeometricPoint_image B S hS X η)
  refine (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS ⟨X, hX⟩ _
    (canonicalGeometricPoint B S hS X η) η (canonicalGeometricPoint_image B S hS X η)).2 ?_
  rw [← Module.length_pos_iff (R := etaleLocalRing B S hS X (canonicalGeometricPoint B S hS X η))]
  change 0 < geometricLength B S hS ⟨X, hX⟩ _ _
  rw [hlen]
  exact_mod_cast hpos

/-- Under the hypothesis of
`AlgebraicGeometry.Space.IntegralClosedSubspace.geometricLength_modulePushforward_eq_degree`,
if the support of the direct image of `𝒪_Z` is closed (for instance if that direct image is
coherent), it is the point set of the image `f(Z)`. -/
theorem IntegralClosedSubspace.supportOfSheaf_modulePushforward_eq
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (hXLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y)
    (h0 : HasTranscendenceDegreeAt B S hS
      (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS) 0)
    (hcl : IsClosed (supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj
        ((modulePushforward B S hS
          (ObjectProperty.homMk (Z.subspace.ι ≫ f) :
            (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨X, hX⟩)).obj
          (structureSheafModule B S hS ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩))))) :
    supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj
        ((modulePushforward B S hS
          (ObjectProperty.homMk (Z.subspace.ι ≫ f) :
            (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨X, hX⟩)).obj
          (structureSheafModule B S hS ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩))) =
      subspacePointSet B S hS X
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace := by
  have hη := IntegralClosedSubspace.isGenericPoint_pointsMap_ambientGenericPoint B S hS hY hX
    hXdec f Z
  refine
    (IntegralClosedSubspace.supportOfSheaf_modulePushforward_subset B S hS hX hXdec f Z).antisymm ?_
  rw [← hη]
  exact closure_minimal (Set.singleton_subset_iff.2
    (IntegralClosedSubspace.mem_supportOfSheaf_modulePushforward B S hS hY hX hXdec hXLN f hf Z
      h0 hη)) hcl

/-! ### The higher direct images vanish at the generic point of the image -/

section HigherDirectImages

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- A module which is a zero object has empty support. -/
theorem supportOfSheaf_eq_empty_of_isZero (X : AlgebraicSpaces B S hS)
    {M : Modules.{u, u} B S hS X.1 X.2} (hM : IsZero M) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) = ∅ := by
  refine Set.subset_empty_iff.1
    ((supportOfSheaf_subset_iff_forall_sectionSupportedIn B S hS X M ∅).2 fun W s => ?_)
  have hs : s = 0 := by
    have h := congrArg (fun φ : M ⟶ M => φ.val.app (Opposite.op W) s) (hM.eq_of_src (𝟙 M) 0)
    simp only at h
    exact h.trans rfl
  rw [hs]
  exact sectionSupportedIn_zero W

/-- **Higher direct images vanish over a point with finite fibre.** Let `g : Z ⟶ X` be a proper
morphism of decent algebraic spaces, let `G` be a quasi-coherent `𝒪_Z`-module and let `η ∈ |X|`
have finite fibre. Then for `q > 0` the point `η` is not in the support of `R^q g_* G`.

There is an affine étale chart `V ⟶ X` through `η` over which the base change of `g` is a finite
morphism of affine schemes (`AlgebraicGeometry.Space.exists_finite_affine_chartDiagram`); the
restriction of `R^q g_* G` to `V` is the higher direct image along that base change (Stacks
03LX), which vanishes for `q > 0` because a finite morphism is affine (Stacks 073H); and the
support of a module is étale local (Stacks 07TY). -/
@[sga "6 X 4.4" "partial"]
theorem notMem_supportOfSheaf_rightDerived_modulePushforward_of_finite
    {Z X : AlgebraicSpaces B S hS} (hZdec : IsDecentSpace B S hS Z.1)
    (hXdec : IsDecentSpace B S hS X.1) (g : Z ⟶ X) (hg : IsProper B S hS g.hom)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : G.IsQuasicoherentOnSite) {η : points B S hS X.1}
    (hfin : {z : points B S hS Z.1 | pointsMap B S hS Z.1 g.hom z = η}.Finite)
    (q : ℕ) (hq : 0 < q) :
    have := hasInjectiveResolutions_modules B S hS Z.1 Z.2
    η ∉ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        (((modulePushforward B S hS g).rightDerived q).obj G)) := by
  intro _ hmem
  obtain ⟨d, e, hpb, -, -, hfinite, he, -, -⟩ :=
    exists_finite_affine_chartDiagram B S hS hZdec hXdec g hg η hfin
  -- the cartesian square of algebraic spaces over the chart
  let VA := chartSpace B S hS X d.V
  let UA := chartSpace B S hS Z d.U
  let f' : UA ⟶ VA := ObjectProperty.homMk (yoneda.map d.g)
  have sq : IsPullback (chartToSpace B S hS Z d.U) f' g (chartToSpace B S hS X d.V) :=
    isPullback_homMk B S hS Z.2 (isAlgebraicSpace_yoneda B S hS _) X.2
      (isAlgebraicSpace_yoneda B S hS _) hpb
  have := hasInjectiveResolutions_modules B S hS UA.1 UA.2
  have hiso := (moduleHigherPushforwardEtaleBaseChangeIso B S hS _ f' g _ sq
    (isEtale_chartToSpace B S hS X d.V) q).app G
  -- the base change is affine, so its higher direct images vanish
  have haff : IsAffineHom B S hS f'.hom := by
    have := hfinite
    exact isAffineHom_of_presheaf ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsAffineHom.{u}) d.g).2 inferInstance)
  have hzero : IsZero (((modulePushforward B S hS f').rightDerived q).obj
      ((etaleModulePullback B S hS (chartToSpace B S hS Z d.U)
        (isEtale_of_isPullback B S hS f' _ _ g sq.flip
          (isEtale_chartToSpace B S hS X d.V))).obj G)) :=
    isZero_rightDerived_modulePushforward_isAffineHom B S hS f' haff _
      (isQuasicoherentOnSite_etaleModulePullback B S hS _ _ _ hG) q hq
  have hiso' : (etaleModulePullback B S hS (chartToSpace B S hS X d.V)
      (isEtale_chartToSpace B S hS X d.V)).obj
        (((modulePushforward B S hS g).rightDerived q).obj G) ≅
      ((modulePushforward B S hS f').rightDerived q).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS Z d.U)
          (isEtale_of_isPullback B S hS f' _ _ g sq.flip
            (isEtale_chartToSpace B S hS X d.V))).obj G) :=
    hiso.symm
  have hempty := supportOfSheaf_eq_empty_of_isZero B S hS VA (hzero.of_iso hiso')
  rw [supportOfSheaf_chartToSpace B S hS X d.V] at hempty
  have hpt : pointsMap B S hS VA.1 (chartToSpace B S hS X d.V).hom
      ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj d.V)).symm e) = η :=
    (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 d.V e).symm.trans he
  refine (Set.eq_empty_iff_forall_notMem.1 hempty)
    ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj d.V)).symm e) ?_
  exact (congrArg (· ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
    (((modulePushforward B S hS g).rightDerived q).obj G))) hpt).mpr hmem

/-- **The higher direct images of `𝒪_Z` vanish at the generic point of `f(Z)`, Stacks 0EDJ.**
Let `f : Y ⟶ X` be a proper morphism into a decent locally Noetherian algebraic space and let
`Z ⊂ Y` be an integral closed subspace whose generic point has transcendence degree zero over
the generic point `η` of `f(Z)`. Then for `q > 0` the point `η` is not in the support of
`R^q (Z ⟶ X)_* 𝒪_Z`.

This is the source's appeal to Stacks 0A4K, that `Z ⟶ X` is finite over a neighbourhood of
`η`: the fibre over `η` is the generic point of `Z` alone (Stacks 0AD5), and
`AlgebraicGeometry.Space.notMem_supportOfSheaf_rightDerived_modulePushforward_of_finite`
applies. -/
theorem IntegralClosedSubspace.notMem_supportOfSheaf_rightDerived_modulePushforward
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)
    (f : Y ⟶ X) (hf : IsProper B S hS f) (Z : IntegralClosedSubspace B S hS Y)
    (h0 : HasTranscendenceDegreeAt B S hS
      (IntegralClosedSubspace.toClosureImage B S hS hX hXdec f Z) (Z.genericPoint B S hS) 0)
    {η : points B S hS X}
    (hη : IsGenericPoint η (subspacePointSet B S hS X
      (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace))
    (q : ℕ) (hq : 0 < q) :
    have := hasInjectiveResolutions_modules B S hS Z.subspace.toFunctor Z.isClosedSubspace.1
    have := modulePushforward_additive B S hS
      (ObjectProperty.homMk (Z.subspace.ι ≫ f) :
        (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
    η ∉ supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj
        (((modulePushforward B S hS
          (ObjectProperty.homMk (Z.subspace.ι ≫ f) :
            (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨X, hX⟩)).rightDerived q).obj
          (structureSheafModule B S hS ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩))) :=
  notMem_supportOfSheaf_rightDerived_modulePushforward_of_finite B S hS
    (Z := ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩) (X := ⟨X, hX⟩) Z.isIntegralSpace.2.1 hXdec
    _ (isProper_ι_comp B S hS hY hX f hf Z) _ inferInstance
    (by
      change {z | pointsMap B S hS Z.subspace.toFunctor (Z.subspace.ι ≫ f) z = η}.Finite
      rw [IntegralClosedSubspace.setOf_pointsMap_eq_eq_singleton B S hS hY hX hXdec f hf Z
        h0 hη]
      exact Set.finite_singleton _) q hq

/-- **The higher direct images of `𝒪_Z` are supported in `f(Z)`.** For a proper morphism
`f : Y ⟶ X` into a decent algebraic space and an integral closed subspace `Z ⊂ Y`, every
`R^q (Z ⟶ X)_* 𝒪_Z` is supported in the image `f(Z)`. In degree zero this is
`AlgebraicGeometry.Space.IntegralClosedSubspace.supportOfSheaf_modulePushforward_subset`; in
positive degree a point off `f(Z)` has empty fibre, and
`AlgebraicGeometry.Space.notMem_supportOfSheaf_rightDerived_modulePushforward_of_finite`
applies. -/
theorem IntegralClosedSubspace.supportOfSheaf_rightDerived_modulePushforward_subset
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (f : Y ⟶ X) (hf : IsProper B S hS f)
    (Z : IntegralClosedSubspace B S hS Y) (q : ℕ) :
    have := hasInjectiveResolutions_modules B S hS Z.subspace.toFunctor Z.isClosedSubspace.1
    have := modulePushforward_additive B S hS
      (ObjectProperty.homMk (Z.subspace.ι ≫ f) :
        (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
    supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj
        (((modulePushforward B S hS
          (ObjectProperty.homMk (Z.subspace.ι ≫ f) :
            (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨X, hX⟩)).rightDerived q).obj
          (structureSheafModule B S hS ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩))) ⊆
      subspacePointSet B S hS X
        (IntegralClosedSubspace.closureImage B S hS hX hXdec f Z).subspace := by
  intro _ _ x hx
  let ZA : AlgebraicSpaces B S hS := ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩
  let XA : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let g : ZA ⟶ XA := ObjectProperty.homMk (Z.subspace.ι ≫ f)
  obtain _ | q := q
  · have := preservesFiniteLimits_modulePushforward B S hS g
    have e := ((modulePushforward B S hS g).rightDerivedZeroIsoSelf.app
      (structureSheafModule B S hS ZA))
    refine IntegralClosedSubspace.supportOfSheaf_modulePushforward_subset B S hS hX hXdec f Z ?_
    exact @supportOfSheaf_subset_of_mono B S hS X hX _ _ ((SheafOfModules.toSheaf _).mapIso e).hom
      (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)) x hx
  · by_contra hxf
    refine notMem_supportOfSheaf_rightDerived_modulePushforward_of_finite B S hS (Z := ZA)
      (X := XA) Z.isIntegralSpace.2.1 hXdec g
      (isProper_ι_comp B S hS hY hX f hf Z) _ inferInstance ?_ (q + 1) q.succ_pos hx
    convert Set.finite_empty
    refine Set.eq_empty_iff_forall_notMem.2 fun z hz => hxf ?_
    rw [← hz, IntegralClosedSubspace.subspacePointSet_closureImage B S hS hX hXdec f Z]
    refine subset_closure ⟨pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι z, ⟨z, rfl⟩, ?_⟩
    exact (pointsMap_comp_apply B S hS Z.subspace.ι f z).symm

end HigherDirectImages

/-! ### Spaces proper over an affine base -/

section ProperOverAffine

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))

/-- The yoneda image of the base object is terminal. -/
private noncomputable def isTerminal_yoneda_baseObject :
    IsTerminal (yoneda.obj (baseObject A B hA)) :=
  IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal

/-- An algebraic space proper over `Spec A` is decent: it is separated over `Spec A`, hence
quasi-separated, and a quasi-separated algebraic space is decent. -/
theorem isDecentSpace_of_isProper_baseObject {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (p : X ⟶ yoneda.obj (baseObject A B hA))
    (hp : IsProper B (Spec (.of A)) hA p) : IsDecentSpace B (Spec (.of A)) hA X := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  have hterm := isTerminal_yoneda_baseObject A B hA
  have hsep : IsAbsolutelySeparated B (Spec (.of A)) hA hZ X :=
    (isAbsolutelySeparated_iff_isSeparatedOver B (Spec (.of A)) hA hZ inferInstance hX).mpr
      ((isSeparatedOver_iff_isSeparated_of_isTerminal B (Spec (.of A)) hA hterm p).mpr hp.1)
  exact isDecentSpace_of_isAbsolutelyQuasiSeparated B (Spec (.of A)) hA X hX
    (isQuasiSeparatedOver_of_isSeparatedOver B (⊤_ Scheme.{u}) hZ _ hsep)

/-- A morphism between algebraic spaces proper over `Spec A` is proper: its composite with the
structure morphism of the target is the structure morphism of the source, the target of the
structure morphisms being terminal, and properness cancels against a separated morphism. -/
theorem isProper_of_isProper_baseObject {X Y : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (hY : IsAlgebraicSpace B (Spec (.of A)) hA Y)
    (pX : X ⟶ yoneda.obj (baseObject A B hA)) (hpX : IsProper B (Spec (.of A)) hA pX)
    (pY : Y ⟶ yoneda.obj (baseObject A B hA)) (hpY : IsProper B (Spec (.of A)) hA pY)
    (f : Y ⟶ X) : IsProper B (Spec (.of A)) hA f := by
  have hterm := isTerminal_yoneda_baseObject A B hA
  refine isProper_of_comp_of_isSeparated B (Spec (.of A)) hA hY hX
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) f pX ?_ hpX.1
  rwa [hterm.hom_ext (f ≫ pX) pY]

end ProperOverAffine

end AlgebraicGeometry.Space

end
