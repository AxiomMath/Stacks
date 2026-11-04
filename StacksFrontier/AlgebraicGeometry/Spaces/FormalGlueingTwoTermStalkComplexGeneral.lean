module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormalGlueingTwoTermStalkComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafStalkAnyGeometricPointGeneral
import all StacksFrontier.AlgebraicGeometry.Spaces.FormalGlueingTwoTermStalkComplex
import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionChartBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportVanishing
import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportProperties
import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Formal glueing: the two-term complex of stalks, for an arbitrary morphism

Let `f : Y ⟶ X` be a morphism of algebraic spaces, `Z ⊆ X` a closed subspace and `u : G ⟶ H` a
map of abelian sheaves on `Y_étale` that becomes invertible over `Y ∖ f⁻¹ Z`.
`StacksFrontier/AlgebraicGeometry/Spaces/FormalGlueingTwoTermStalkComplex.lean` proves Stacks 0AER
for a morphism whose underlying morphism of presheaves is relatively representable, with the
direct image `AlgebraicGeometry.Space.smallEtaleAbelianPushforward`. This file removes that
hypothesis, using the direct image `AlgebraicGeometry.Space.smallEtaleAbelianDirectImage` of an
arbitrary morphism.

## Main results

* `AlgebraicGeometry.Space.isIso_kernelMap_and_mono_cokernelMap_directImageStalkMap`
  is **Stacks 0AER**, at the hypotheses of the source: `f` is an arbitrary morphism of
  algebraic spaces, and the direct image is
  `AlgebraicGeometry.Space.smallEtaleAbelianDirectImage`. The representable form
  `AlgebraicGeometry.Space.isIso_kernelMap_and_mono_cokernelMap_pushforwardStalkMap` is the
  special case; it is kept because it is the form the representable development is stated in.

## Implementation notes

The proof is that of the representable case, step for step, and reuses its private lemmas on
kernels and cokernels of stalk maps, which is why this file imports
`StacksFrontier/AlgebraicGeometry/Spaces/FormalGlueingTwoTermStalkComplex.lean` with `import all`.

## References

* [Stacks Project, Tag 0AER](https://stacks.math.columbia.edu/tag/0AER)
* [Stacks Project, Tag 0AEQ](https://stacks.math.columbia.edu/tag/0AEQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

variable {Z W V : AlgebraicSpaces B S hS}

/-- The two clauses of Stacks 0AER, for a cartesian square, an open subspace and a map of
abelian sheaves which becomes invertible on that open subspace, all given as data -- and for an
arbitrary morphism `f`, using the direct image of
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImage`.

This is `AlgebraicGeometry.Space.isIso_kernelMap_and_mono_cokernelMap_of_isIso_inverseImage`
with the hypothesis that `f` be representable removed.  The proof is step for step the same
one: `f` enters it only through left exactness and additivity of `f_* ⋙ (-)_x̄`, which the
general direct image has, and through the degree-zero case of Stacks 0AEQ, which
`AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support_of_isPullback`
supplies for an arbitrary `f`.  Every other morphism in the argument -- the two closed
immersions, the integral `f'`, and the open immersion `j` -- is representable and keeps the
representable direct image. -/
private theorem isIso_kernelMap_and_mono_cokernelMap_of_isIso_inverseImage_general (f : Y ⟶ X)
    (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (i' : W ⟶ Y)
    (hi' : IsClosedImmersion B S hS i'.hom) (f' : W ⟶ Z)
    (hf'int : IsIntegralHom B S hS f'.hom) (hf'inj : UniversallyInjective B S hS f'.hom)
    (sq : IsPullback f' i' i f) (j : V ⟶ Y)
    (hjr : yoneda.relativelyRepresentable j.hom)
    (hcompl : (Set.range (pointsMap B S hS W.1 i'.hom))ᶜ ⊆
      Set.range (pointsMap B S hS V.1 j.hom))
    (y : GeometricPoint B S hS Y.1) (G H : abelianSheaves.{u + 1} B S hS Y) (u : G ⟶ H)
    (hLu : IsIso ((smallEtaleAbelianInverseImage B S hS j hjr).map u)) :
    IsIso (kernel.map
        ((smallEtaleAbelianDirectImage B S hS f ⋙
            smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map u)
        ((smallEtaleAbelianStalk B S hS y).map u)
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app G)
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app H)
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).naturality u)) ∧
      Mono (cokernel.map
        ((smallEtaleAbelianDirectImage B S hS f ⋙
            smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map u)
        ((smallEtaleAbelianStalk B S hS y).map u)
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app G)
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app H)
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).naturality u)) := by
  have hLex : PreservesFiniteLimits (smallEtaleAbelianInverseImage B S hS j hjr) :=
    preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS j hjr
  have hLcol : PreservesColimits (smallEtaleAbelianInverseImage B S hS j hjr) :=
    (smallEtaleAbelianInverseImageAdjunction B S hS j hjr).leftAdjoint_preservesColimits
  have hLadd : (smallEtaleAbelianInverseImage B S hS j hjr).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hFlim : PreservesFiniteLimits (smallEtaleAbelianDirectImage B S hS f ⋙
      smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)) :=
    comp_preservesFiniteLimits _ _
  have hFadd : (smallEtaleAbelianDirectImage B S hS f ⋙
      smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).Additive := inferInstance
  -- The comparison is invertible at every abelian sheaf supported on `|W|`.
  have hα : ∀ T : abelianSheaves.{u + 1} B S hS Y,
      supportOfSheaf B S hS Y.1 T ⊆ Set.range (pointsMap B S hS W.1 i'.hom) →
        IsIso ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app T) := fun T hT =>
    isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support_of_isPullback B S hS f i hi
      i' hi' f' hf'int hf'inj sq y _ hT
  -- The kernel, the cokernel and the kernel of the image factorisation of `u` are all
  -- supported on `|W|`, their restrictions to `V` being zero.
  have hsupp : ∀ T : abelianSheaves.{u + 1} B S hS Y,
      IsZero ((smallEtaleAbelianInverseImage B S hS j hjr).obj T) →
        supportOfSheaf B S hS Y.1 T ⊆ Set.range (pointsMap B S hS W.1 i'.hom) := fun T hT =>
    supportOfSheaf_subset_of_isZero_smallEtaleAbelianInverseImage B S hS j hjr _ hcompl _ hT
  have hsuppK := hsupp _ ((isZero_kernel_of_mono
    ((smallEtaleAbelianInverseImage B S hS j hjr).map u)).of_iso
      (asIso (kernelComparison u (smallEtaleAbelianInverseImage B S hS j hjr))))
  have hsuppC := hsupp _ ((isZero_cokernel_of_epi
    ((smallEtaleAbelianInverseImage B S hS j hjr).map u)).of_iso
      (asIso (cokernelComparison u (smallEtaleAbelianInverseImage B S hS j hjr))).symm)
  have hmonoLp : Mono ((smallEtaleAbelianInverseImage B S hS j hjr).map
      (factorThruImage u)) := by
    have h₂ : Mono ((smallEtaleAbelianInverseImage B S hS j hjr).map (factorThruImage u) ≫
        (smallEtaleAbelianInverseImage B S hS j hjr).map (image.ι u)) := by
      rw [← Functor.map_comp, image.fac]
      infer_instance
    exact mono_of_mono _ ((smallEtaleAbelianInverseImage B S hS j hjr).map (image.ι u))
  have hsuppKp := hsupp (kernel (factorThruImage u)) ((isZero_kernel_of_mono _).of_iso
    (asIso (kernelComparison (factorThruImage u) (smallEtaleAbelianInverseImage B S hS j hjr))))
  have hαK := hα _ hsuppK
  have hαC := hα _ hsuppC
  refine ⟨isIso_kernelMap_of_isIso_app_kernel
    (smallEtaleAbelianDirectImageStalkMap B S hS f y) u, ?_⟩
  -- An injective presentation of `ker (G ⟶ im u)` among the sheaves supported on `|W|`.
  have hessKp : (smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).essImage
      (kernel (factorThruImage u)) := by
    have hiso := isIso_unit_app_of_supportOfSheaf_subset B S hS i' hi' _ hsuppKp
    exact ⟨(smallEtaleAbelianInverseImage B S hS i' hi'.rep).obj (kernel (factorThruImage u)),
      ⟨(asIso ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).unit.app
        (kernel (factorThruImage u)))).symm⟩⟩
  have hRinj := preservesInjectiveObjects_smallEtaleAbelianPushforward B S hS i' hi'.rep
  obtain ⟨J, hJinj, hJess, e, hemono⟩ := exists_injective_presentation_in_essImage
    (smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep) _ hessKp
  have := hJinj
  have := hemono
  have hsuppJ : supportOfSheaf B S hS Y.1 J ⊆ Set.range (pointsMap B S hS W.1 i'.hom) :=
    supportOfSheaf_subset_of_essImage B S hS i' hi' J hJess
  have hlocsurj : Sheaf.IsLocallySurjective (cokernel.π e) :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := cokernel.π e)).2 inferInstance
  have hsuppCe : supportOfSheaf B S hS Y.1 (cokernel e) ⊆
      Set.range (pointsMap B S hS W.1 i'.hom) := fun x hx =>
    hsuppJ (supportOfSheaf_subset_of_isLocallySurjective B S hS Y.1 Y.property
      (cokernel.π e) hx)
  have hαJ := hα _ hsuppJ
  have hαCe := hα _ hsuppCe
  -- The geometric stalk at `ȳ` is exact, so the comparison transports the epimorphism.
  have hsh : PreservesColimitsOfShape WalkingSpan (smallEtaleAbelianStalk B S hS y) :=
    PreservesFiniteColimits.preservesFiniteColimits _
  have hepiT : Epi ((smallEtaleAbelianStalk B S hS y).map (cokernel.π e)) :=
    preserves_epi_of_preservesColimit _ _
  have hepi1 : Epi ((smallEtaleAbelianDirectImage B S hS f ⋙
      smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map (cokernel.π e) ≫
        (smallEtaleAbelianDirectImageStalkMap B S hS f y).app (cokernel e)) := by
    rw [(smallEtaleAbelianDirectImageStalkMap B S hS f y).naturality (cokernel.π e)]
    infer_instance
  have hepi2 : Epi ((smallEtaleAbelianDirectImage B S hS f ⋙
      smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map (cokernel.π e)) :=
    (epi_comp_iff_of_isIso _ _).mp hepi1
  have hepiF : Epi ((smallEtaleAbelianDirectImage B S hS f ⋙
      smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map (factorThruImage u)) :=
    epi_map_of_injective_kernel_embedding
      (smallEtaleAbelianDirectImage B S hS f ⋙
        smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)) (factorThruImage u) e
  have hmonocc : Mono (cokernelComparison u
      (smallEtaleAbelianDirectImage B S hS f ⋙
        smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y))) :=
    mono_cokernelComparison_of_epi_factorThruImage
      (smallEtaleAbelianDirectImage B S hS f ⋙
        smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)) u
  exact mono_cokernelMap_of_mono_comparison
    (smallEtaleAbelianDirectImageStalkMap B S hS f y) u

/-- **Stacks 0AER.** Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and
let `Z ⊆ X` be a closed subspace such that `f^{-1}Z ⟶ Z` is integral and universally
injective. Let `ȳ` be a geometric point of `Y`, let `x̄ = f(ȳ)` and let `G` be an abelian sheaf
on the small étale site of `Y`. Writing `V = Y ∖ f^{-1}Z` and `j' : V ⟶ Y` for the inclusion,
the map of two-term complexes
```
((f_*G)_x̄ ⟶ (f_*(j'_*(G|_V)))_x̄) ⟶ (G_ȳ ⟶ (j'_*(G|_V))_ȳ)
```
given by the canonical comparison of
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkMap` induces an isomorphism on
kernels and an injection on cokernels. -/
@[stacks 0AER "isomorphism on kernels and injection on cokernels of the two-term stalk
  complexes, for an arbitrary morphism of algebraic spaces"]
theorem isIso_kernelMap_and_mono_cokernelMap_directImageStalkMap (f : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1)
    (hint : IsIntegralHom B S hS (Z.1.fromPreimage f.hom))
    (hinj : UniversallyInjective B S hS (Z.1.fromPreimage f.hom))
    (y : GeometricPoint B S hS Y.1) (G : abelianSheaves.{u + 1} B S hS Y) :
    IsIso (kernel.map
        ((smallEtaleAbelianDirectImage B S hS f ⋙
            smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))
        ((smallEtaleAbelianStalk B S hS y).map
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app G)
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app
          (smallEtaleAbelianRestrictionPushforward B S hS f Z G))
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).naturality
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))) ∧
      Mono (cokernel.map
        ((smallEtaleAbelianDirectImage B S hS f ⋙
            smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))
        ((smallEtaleAbelianStalk B S hS y).map
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app G)
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app
          (smallEtaleAbelianRestrictionPushforward B S hS f Z G))
        ((smallEtaleAbelianDirectImageStalkMap B S hS f y).naturality
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))) := by
  have hWc : IsClosedSubspace B S hS (Z.1.preimage f.hom) :=
    isClosedSubspace_preimage B S hS f.hom Z.1 X.property Y.property Z.2
  have hff := fullyFaithfulSmallEtaleRestrictionOfIsOpenImmersion B S hS
    (openComplementPreimageι B S hS f Z) (isOpenImmersion_openComplementPreimageι B S hS f Z)
    AddCommGrpCat.{u + 1}
  have := hff.full
  have := hff.faithful
  have hcounit : IsIso (smallEtaleAbelianInverseImageAdjunction B S hS
      (openComplementPreimageι B S hS f Z)
      (relativelyRepresentable_openComplementPreimageι B S hS f Z)).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful
      (h := smallEtaleAbelianInverseImageAdjunction B S hS
        (openComplementPreimageι B S hS f Z)
        (relativelyRepresentable_openComplementPreimageι B S hS f Z))
  have hLu : IsIso ((smallEtaleAbelianInverseImage B S hS
      (openComplementPreimageι B S hS f Z)
      (relativelyRepresentable_openComplementPreimageι B S hS f Z)).map
        (smallEtaleAbelianRestrictionUnit B S hS f Z G)) :=
    isIso_map_unit_of_isIso_counit (smallEtaleAbelianInverseImageAdjunction B S hS
      (openComplementPreimageι B S hS f Z)
      (relativelyRepresentable_openComplementPreimageι B S hS f Z)) G
  exact isIso_kernelMap_and_mono_cokernelMap_of_isIso_inverseImage_general B S hS f
    (ObjectProperty.homMk Z.1.ι :
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) Z.2.2
    (ObjectProperty.homMk (Z.1.preimage f.hom).ι :
      (⟨(Z.1.preimage f.hom).toFunctor, hWc.1⟩ : AlgebraicSpaces B S hS) ⟶ Y) hWc.2
    (ObjectProperty.homMk (Z.1.fromPreimage f.hom) :
      (⟨(Z.1.preimage f.hom).toFunctor, hWc.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) hint hinj
    (IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage f.hom Z.1))
    (openComplementPreimageι B S hS f Z)
    (relativelyRepresentable_openComplementPreimageι B S hS f Z)
    (range_pointsMap_openComplementPreimageι B S hS f Z).symm.subset
    y G _ (smallEtaleAbelianRestrictionUnit B S hS f Z G) hLu

end AlgebraicGeometry.Space

end
