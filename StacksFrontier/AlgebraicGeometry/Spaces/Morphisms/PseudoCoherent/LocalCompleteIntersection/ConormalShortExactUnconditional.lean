module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceIdealForm
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedConormalSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedSubspaceCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RepresentableUniversal
public import StacksFrontier.AlgebraicGeometry.Thickenings.TransitivityConormalIdealForm
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.ConormalShortExact

/-!
# Short exactness of the conormal sequence of a local complete intersection morphism of spaces

Let `Z ⟶ Y ⟶ X` be formally unramified morphisms of algebraic spaces over a scheme `S` and assume
`i : Z ⟶ Y` is a local complete intersection morphism.  Stacks 06CC asserts that the conormal
sequence `0 ⟶ i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` of Stacks 06BD is short exact.  This file
proves it with no further hypothesis.

Formal unramifiedness is presented, as in Stacks 06BF, by universal first-order thickenings
`Z ⊂ X₁` and `Y ⊂ X₂` over `X` together with a morphism `g₁ : X₁ ⟶ X₂` over `X` restricting to
`i`; `𝒞_{Z/Y}` is the conormal module of the copy `W` of `Z` inside the fibre product
`F = Y ×_{X₂} X₁ ⊆ X₁`, and the sequence is read on `W`.

The proof follows the source.  The sequence is first rewritten as the inverse image along
`W ⊆ F` of the sequence `g₀^*g₁^*𝓘_Y ⟶ g₀^*𝓘_Z ⟶ 𝓘_W` of defining ideal sheaves
(`AlgebraicGeometry.Space.shortExact_conormalSequence_iff_idealForm`).  Étale charts by schemes
`V₂ ⟶ X₂` over a chart `U ⟶ X`, and `V₁ ⟶ X₁` over `V₂`, surjective on points, localize it to the
corresponding sequence of closed subschemes of the charts
(`AlgebraicGeometry.Space.shortExact_idealForm_of_representedLocalization`); there the closed
immersions are universal first-order thickenings of schemes over `U` by Stacks 060D, the chart of
`F` is the fibre product of schemes, and the case of schemes, Stacks 06BA, applies
(`AlgebraicGeometry.Space.shortExact_representedIdealForm_of_isLocalCompleteIntersection`).

## Main results

* `AlgebraicGeometry.Space.shortExact_representedIdealForm_of_isLocalCompleteIntersection`: the
  case of closed subspaces of representable algebraic spaces, in the form of ideal sheaves.
* `AlgebraicGeometry.Space.shortExact_idealForm_of_representedLocalization`: the ideal form of
  the conormal sequence is short exact once it is so on étale charts by schemes.
* `AlgebraicGeometry.Space.conormalSequence_shortExact_of_isLocalCompleteIntersection`:
  **Stacks 06CC**.

## References

* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
* [Stacks Project, Tag 06BA](https://stacks.math.columbia.edu/tag/06BA)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF)
* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y' Z' : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
  {pY : Y' ⟶ X} {pZ : Z' ⟶ X} (i : Z.toFunctor ⟶ Y.toFunctor)
  (hZ : IsUniversalFirstOrderThickening B S hS Z pZ)
  (hY : IsUniversalFirstOrderThickening B S hS Y pY)
  (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)

/-- `AlgebraicGeometry.Space.universalThickeningCompConormalRightMap` is the conormal map of
Stacks 04CP of the inclusion of the fibre product, by definition. -/
theorem universalThickeningCompConormalRightMap_eq :
    universalThickeningCompConormalRightMap B S hS i hZ hY hfac =
      conormalMap B S hS
        (preimageSubspace B S hS (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
          ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
        (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
        (preimageProjection B S hS (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
          ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
        (conormalEtaleRestrictionSquare B S hS
          (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
          ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩) :=
  rfl

/-- `AlgebraicGeometry.Space.universalThickeningConormalMap` at the square of
`AlgebraicGeometry.Space.universalThickeningComp_square` is the conormal map of Stacks 04CP of
the morphism of Stacks 06BF, by definition. -/
theorem universalThickeningConormalMap_comp_eq :
    universalThickeningConormalMap B S hS (𝟙 X) i hZ hY
        (universalThickeningComp_square B S hS i hfac) =
      conormalMap B S hS ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
        ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
        (universalThickeningCompMap B S hS i hZ hY hfac) (ObjectProperty.homMk i)
        (by
          apply ObjectProperty.hom_ext
          exact universalThickeningMap_restrict B S hS (𝟙 X) i hZ hY
            (universalThickeningComp_square B S hS i hfac)) :=
  rfl

section Representable

variable {T₀ T₁ T₂ U : BigFppfOver B S hS} (g₀ : T₀ ⟶ T₁) (g₁ : T₁ ⟶ T₂) (r₂ : T₂ ⟶ U)
  (W : ClosedSubspaces B S hS (yoneda.obj T₀)) (Z : ClosedSubspaces B S hS (yoneda.obj T₁))
  (Y : ClosedSubspaces B S hS (yoneda.obj T₂))
  (f₀ : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (f₁ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
  (sq₀ : subspaceInclusion B S hS
      ⟨yoneda.obj T₀, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₀⟩ W ≫
        representedSpaceMap B S hS g₀ =
      f₀ ≫ subspaceInclusion B S hS
        ⟨yoneda.obj T₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₁⟩ Z)
  (sq₁ : subspaceInclusion B S hS
      ⟨yoneda.obj T₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₁⟩ Z ≫
        representedSpaceMap B S hS g₁ =
      f₁ ≫ subspaceInclusion B S hS
        ⟨yoneda.obj T₂, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₂⟩ Y)

include sq₀ sq₁ in
/-- **Stacks 06CC for representable ambient spaces, in the form of ideal sheaves.**  Let
`Z ⊆ h_{T₁}` and `Y ⊆ h_{T₂}` be universal first-order thickenings over `h_U`, with structure
morphisms `g₁ ≫ r₂` and `r₂`, let `T₀` be the fibre product `Y₀ ×_{T₂} T₁` of the representing
scheme `Y₀` of `Y`, with projection `g₀ : T₀ ⟶ T₁`, and let `W ⊆ h_{T₀}` be a closed subspace
carried isomorphically onto `Z` over `g₀`.  If the morphism of representing schemes
`Z₀ ⟶ Y₀` induced by `f₁ : Z ⟶ Y` is a local complete intersection morphism, then the sequence
`ι^*g₀^*g₁^*𝓘_Y ⟶ ι^*g₀^*𝓘_Z ⟶ ι^*𝓘_W` of defining ideal sheaves, `ι` being the closed immersion
of the representing scheme of `W`, is short exact.

This is Stacks 06BA for the closed immersions of the representing schemes, which are universal
first-order thickenings of schemes by
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_representedClosedHom`, carried to
algebraic spaces by `AlgebraicGeometry.Space.shortExact_idealForm_of_scheme`. -/
theorem shortExact_representedIdealForm_of_isLocalCompleteIntersection
    (hZ : IsUniversalFirstOrderThickening B S hS Z.1 (schemeSpaceMap (g₁ ≫ r₂)))
    (hY : IsUniversalFirstOrderThickening B S hS Y.1 (schemeSpaceMap r₂))
    (ρ : T₀ ⟶ representedClosedObj B S hS T₂ Y)
    (hF : IsPullback ρ g₀ (representedClosedHom B S hS T₂ Y) g₁) (hf₀ : IsIso f₀.hom)
    (hlci : IsLocalCompleteIntersectionMorphism
      ((BigFppfOver.toScheme B S hS).map (representedClosedLift B S hS Z Y f₁))) :
    ∃ h : (modulePullback B S hS
          (representedSpaceMap B S hS (representedClosedHom B S hS T₀ W))).map
          ((modulePullback B S hS (representedSpaceMap B S hS g₀)).map
            (representedIdealSheafMap B S hS g₁ Z Y f₁ sq₁)) ≫
        (modulePullback B S hS
          (representedSpaceMap B S hS (representedClosedHom B S hS T₀ W))).map
          (representedIdealSheafMap B S hS g₀ W Z f₀ sq₀) = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  have comm₀ := representedClosedHom_comp_eq B S hS g₀ W Z f₀ sq₀
  have comm₁ := representedClosedHom_comp_eq B S hS g₁ Z Y f₁ sq₁
  have hZs := isUniversalFirstOrderThickening_representedClosedHom B S hS Z (g₁ ≫ r₂) hZ
  have hYs := isUniversalFirstOrderThickening_representedClosedHom B S hS Y r₂ hY
  have e : (BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₁ Z ≫ g₁ ≫ r₂) =
      (BigFppfOver.toScheme B S hS).map (representedClosedLift B S hS Z Y f₁) ≫
        (BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₂ Y ≫ r₂) := by
    rw [← Functor.map_comp, ← Category.assoc, comm₁, Category.assoc]
  rw [e] at hZs
  have := isIso_representedClosedLift B S hS W Z f₀ hf₀
  have hk : (BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₀ W) ≫
      (BigFppfOver.toScheme B S hS).map g₀ =
      (BigFppfOver.toScheme B S hS).map (representedClosedLift B S hS W Z f₀) ≫
        (BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₁ Z) := by
    rw [← Functor.map_comp, comm₀, Functor.map_comp]
  have hq : (BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₁ Z) ≫
      (BigFppfOver.toScheme B S hS).map g₁ =
      (BigFppfOver.toScheme B S hS).map (representedClosedLift B S hS Z Y f₁) ≫
        (BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₂ Y) := by
    rw [← Functor.map_comp, comm₁, Functor.map_comp]
  have hqb : (BigFppfOver.toScheme B S hS).map g₁ ≫ (BigFppfOver.toScheme B S hS).map r₂ =
      (BigFppfOver.toScheme B S hS).map (g₁ ≫ r₂) := (Functor.map_comp _ _ _).symm
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hFs := hF.map (BigFppfOver.toScheme B S hS)
  have hmono := mono_representedClosedHom B S hS T₂ Y
  have hkρ₀ : representedClosedHom B S hS T₀ W ≫ ρ =
      representedClosedLift B S hS W Z f₀ ≫ representedClosedLift B S hS Z Y f₁ := by
    rw [← cancel_mono (representedClosedHom B S hS T₂ Y), Category.assoc, hF.w,
      ← Category.assoc, comm₀, Category.assoc, Category.assoc, comm₁]
  have hkρ : (BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₀ W) ≫
      (BigFppfOver.toScheme B S hS).map ρ =
      (BigFppfOver.toScheme B S hS).map (representedClosedLift B S hS W Z f₀) ≫
        (BigFppfOver.toScheme B S hS).map (representedClosedLift B S hS Z Y f₁) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hkρ₀]
  obtain ⟨h, hse⟩ := Stacks.Thickenings.shortExact_transitivityIdealForm
    ((BigFppfOver.toScheme B S hS).map (representedClosedLift B S hS Z Y f₁))
    ((BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₂ Y ≫ r₂))
    ((BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₁ Z))
    ((BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₂ Y))
    ((BigFppfOver.toScheme B S hS).map (g₁ ≫ r₂)) ((BigFppfOver.toScheme B S hS).map r₂)
    ((BigFppfOver.toScheme B S hS).map g₁) ((BigFppfOver.toScheme B S hS).map g₀)
    ((BigFppfOver.toScheme B S hS).map ρ)
    ((BigFppfOver.toScheme B S hS).map (representedClosedHom B S hS T₀ W))
    ((BigFppfOver.toScheme B S hS).map (representedClosedLift B S hS W Z f₀))
    hZs hYs hq hqb hFs hk hkρ hlci
  exact shortExact_idealForm_of_scheme B S hS g₀ g₁ W Z Y f₀ f₁ sq₀ sq₁
    ((BigFppfOver.toScheme B S hS).map (representedClosedLift B S hS W Z f₀)) hk
    ((BigFppfOver.toScheme B S hS).map (representedClosedLift B S hS Z Y f₁)) hq ⟨h, hse⟩

end Representable

section Localization

variable {X₀ X₁ X₂ : AlgebraicSpaces B S hS} (W : ClosedSubspaces B S hS X₀.1)
  (Z : ClosedSubspaces B S hS X₁.1) (Y : ClosedSubspaces B S hS X₂.1)
  (g₀ : X₀ ⟶ X₁) (g₁ : X₁ ⟶ X₂)
  (f₀ : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (f₁ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
  (sq₀ : subspaceInclusion B S hS X₀ W ≫ g₀ = f₀ ≫ subspaceInclusion B S hS X₁ Z)
  (sq₁ : subspaceInclusion B S hS X₁ Z ≫ g₁ = f₁ ≫ subspaceInclusion B S hS X₂ Y)
  {T₀ T₁ T₂ : BigFppfOver B S hS}
  (c₀ : (⟨yoneda.obj T₀, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₀⟩ :
    AlgebraicSpaces B S hS) ⟶ X₀)
  (c₁ : (⟨yoneda.obj T₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₁⟩ :
    AlgebraicSpaces B S hS) ⟶ X₁)
  (c₂ : (⟨yoneda.obj T₂, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₂⟩ :
    AlgebraicSpaces B S hS) ⟶ X₂) (g₀' : T₀ ⟶ T₁) (g₁' : T₁ ⟶ T₂)
  (hc₀ : representedSpaceMap B S hS g₀' ≫ c₁ = c₀ ≫ g₀)
  (hc₁ : representedSpaceMap B S hS g₁' ≫ c₂ = c₁ ≫ g₁)
  (f₀' : (⟨(preimageSubspace B S hS c₀ W).1.toFunctor, (preimageSubspace B S hS c₀ W).2.1⟩ :
      AlgebraicSpaces B S hS) ⟶
    (⟨(preimageSubspace B S hS c₁ Z).1.toFunctor, (preimageSubspace B S hS c₁ Z).2.1⟩ :
      AlgebraicSpaces B S hS))
  (f₁' : (⟨(preimageSubspace B S hS c₁ Z).1.toFunctor, (preimageSubspace B S hS c₁ Z).2.1⟩ :
      AlgebraicSpaces B S hS) ⟶
    (⟨(preimageSubspace B S hS c₂ Y).1.toFunctor, (preimageSubspace B S hS c₂ Y).2.1⟩ :
      AlgebraicSpaces B S hS))
  (sq₀' : subspaceInclusion B S hS
      ⟨yoneda.obj T₀, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₀⟩
        (preimageSubspace B S hS c₀ W) ≫ representedSpaceMap B S hS g₀' =
      f₀' ≫ subspaceInclusion B S hS
        ⟨yoneda.obj T₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₁⟩
          (preimageSubspace B S hS c₁ Z))
  (sq₁' : subspaceInclusion B S hS
      ⟨yoneda.obj T₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₁⟩
        (preimageSubspace B S hS c₁ Z) ≫ representedSpaceMap B S hS g₁' =
      f₁' ≫ subspaceInclusion B S hS
        ⟨yoneda.obj T₂, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₂⟩
          (preimageSubspace B S hS c₂ Y))

include sq₀ sq₁ hc₀ hc₁ in
/-- **The ideal form of the conormal sequence is short exact once it is so on étale charts by
schemes.**  Let `c_i : h_{T_i} ⟶ X_i` be étale charts compatible with `g₀` and `g₁` through
morphisms `g₀' : T₀ ⟶ T₁`, `g₁' : T₁ ⟶ T₂` of the site, with `c₀` surjective on points.  If the
ideal form of the conormal sequence of the inverse images `c₀⁻¹W`, `c₁⁻¹Z`, `c₂⁻¹Y`, read on the
representing scheme of `c₀⁻¹W`, is short exact, then so is the ideal form of the conormal
sequence of `W`, `Z`, `Y`.

The defining ideal sheaves restrict along the étale charts
(`AlgebraicGeometry.Space.isIso_idealSheafMap_of_isFlat`), compatibly with the maps of ideal
sheaves (`AlgebraicGeometry.Space.map_idealSheafMap_comp_idealSheafMap_preimage`), and the chart
of `W` induced by `c₀` is étale and surjective on points, so the inverse image along it is
faithful and exact and reflects short exactness. -/
theorem shortExact_idealForm_of_representedLocalization (hc₀e : IsEtale B S hS c₀.hom)
    (hc₁e : IsEtale B S hS c₁.hom) (hc₂e : IsEtale B S hS c₂.hom)
    (hc₀s : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c₀.hom)
    (h : ∃ h : (modulePullback B S hS (representedSpaceMap B S hS
          (representedClosedHom B S hS T₀ (preimageSubspace B S hS c₀ W)))).map
          ((modulePullback B S hS (representedSpaceMap B S hS g₀')).map
            (representedIdealSheafMap B S hS g₁' (preimageSubspace B S hS c₁ Z)
              (preimageSubspace B S hS c₂ Y) f₁' sq₁')) ≫
        (modulePullback B S hS (representedSpaceMap B S hS
          (representedClosedHom B S hS T₀ (preimageSubspace B S hS c₀ W)))).map
          (representedIdealSheafMap B S hS g₀' (preimageSubspace B S hS c₀ W)
            (preimageSubspace B S hS c₁ Z) f₀' sq₀') = 0,
      (ShortComplex.mk _ _ h).ShortExact) :
    ∃ h : (modulePullback B S hS (subspaceInclusion B S hS X₀ W)).map
          ((modulePullback B S hS g₀).map (idealSheafMap B S hS Z Y g₁ f₁ sq₁)) ≫
        (modulePullback B S hS (subspaceInclusion B S hS X₀ W)).map
          (idealSheafMap B S hS W Z g₀ f₀ sq₀) = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  have i₀ := isIso_idealSheafMap_of_isFlat B S hS c₀ W
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS c₀).1 (isFlat_of_isEtale B S hS hc₀e))
  have i₁ := isIso_idealSheafMap_of_isFlat B S hS c₁ Z
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS c₁).1 (isFlat_of_isEtale B S hS hc₁e))
  have i₂ := isIso_idealSheafMap_of_isFlat B S hS c₂ Y
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS c₂).1 (isFlat_of_isEtale B S hS hc₂e))
  have hde := isEtale_representedPreimageProjection B S hS (V := T₀) c₀ W hc₀e
  have hfa := faithful_modulePullback B S hS _
    (representedPreimageProjection B S hS (V := T₀) c₀ W) hde
    (surjective_representedPreimageProjection B S hS (V := T₀) c₀ W hc₀s)
  have hl := ((exactFunctor_iff _).mp (modulePullback_exact B S hS _ hde)).1
  have hr := ((exactFunctor_iff _).mp (modulePullback_exact B S hS _ hde)).2
  have H₁ := map_idealSheafMap_comp_idealSheafMap_preimage B S hS Z Y g₁ f₁ sq₁ c₁ c₂
      (representedSpaceMap B S hS g₁') hc₁ f₁' sq₁'
  have H₀ := map_idealSheafMap_comp_idealSheafMap_preimage B S hS W Z g₀ f₀ sq₀ c₀ c₁
      (representedSpaceMap B S hS g₀') hc₀ f₀' sq₀'
  have hd := representedSpaceMap_comp_eq_representedPreimageProjection_comp B S hS (V := T₀) c₀ W
  exact @shortExact_of_shortExact_localization B S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc₀ hc₁
    _ _ _ _ _ _
    (idealSheafMap B S hS Z Y g₁ f₁ sq₁) (idealSheafMap B S hS W Z g₀ f₀ sq₀)
    (idealSheafMap B S hS (preimageSubspace B S hS c₁ Z) (preimageSubspace B S hS c₂ Y)
      (representedSpaceMap B S hS g₁') f₁' sq₁')
    (idealSheafMap B S hS (preimageSubspace B S hS c₀ W) (preimageSubspace B S hS c₁ Z)
      (representedSpaceMap B S hS g₀') f₀' sq₀')
    (idealSheafMap B S hS (preimageSubspace B S hS c₂ Y) Y c₂
      (preimageProjection B S hS c₂ Y) (conormalEtaleRestrictionSquare B S hS c₂ Y))
    (idealSheafMap B S hS (preimageSubspace B S hS c₁ Z) Z c₁
      (preimageProjection B S hS c₁ Z) (conormalEtaleRestrictionSquare B S hS c₁ Z))
    (idealSheafMap B S hS (preimageSubspace B S hS c₀ W) W c₀
      (preimageProjection B S hS c₀ W) (conormalEtaleRestrictionSquare B S hS c₀ W))
    i₂ i₁ i₀ _ _ _ _ hd hfa hl hr H₁ H₀ h

end Localization

section General

variable {X X₁ X₂ : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X₁.1)
  (Y : ClosedSubspaces B S hS X₂.1) (p₁ : X₁ ⟶ X) (p₂ : X₂ ⟶ X) (g₁ : X₁ ⟶ X₂)
  (f₁ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
  (sq₁ : subspaceInclusion B S hS X₁ Z ≫ g₁ = f₁ ≫ subspaceInclusion B S hS X₂ Y)

/-- **Stacks 060D for a chart by a scheme.** If `Z ⊆ X₁` is the universal first-order thickening
of `Z` over `X` and `c` is an étale chart of `X₁` by a scheme lying over an étale chart `φ` of `X`
through `r`, then `c⁻¹Z` is the universal first-order thickening of `c⁻¹Z` over the chart of
`X`. -/
private theorem isUniversalFirstOrderThickening_preimageSubspace_of_isEtale
    {U V : BigFppfOver B S hS} (hZ : IsUniversalFirstOrderThickening B S hS Z.1 p₁)
    (φ : schemeSpace U ⟶ X) (hφe : IsEtale B S hS φ.hom)
    (c : (⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS) ⟶ X₁) (hce : IsEtale B S hS c.hom) (r : V ⟶ U)
    (hr : schemeSpaceMap r ≫ φ = c ≫ p₁) :
    IsUniversalFirstOrderThickening B S hS (preimageSubspace B S hS c Z).1 (schemeSpaceMap r) :=
  IsUniversalFirstOrderThickening.etaleLocalization B S hS (V' := schemeSpace V) Z.1 p₁ hZ φ
    hφe c hce (schemeSpaceMap r) hr (Z.1.preimage c.hom) (Z.1.fromPreimage c.hom)
    (Subfunctor.isPullback_preimage c.hom Z.1)

/-- A chart `c₁` of `X₁` lying over a chart `c₂` of `X₂` through `l`, itself lying over a chart
`φ` of `X` through `r₂`, lies over `φ` through `l ≫ r₂`. -/
private theorem schemeSpaceMap_comp_eq_of_chartSquare {U V₁ V₂ : BigFppfOver B S hS}
    (φ : schemeSpace U ⟶ X)
    (c₁ : (⟨yoneda.obj V₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₁⟩ :
      AlgebraicSpaces B S hS) ⟶ X₁)
    (c₂ : (⟨yoneda.obj V₂, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₂⟩ :
      AlgebraicSpaces B S hS) ⟶ X₂) (l : V₁ ⟶ V₂) (r₂ : V₂ ⟶ U)
    (hb₁ : c₁.hom ≫ g₁.hom = yoneda.map l ≫ c₂.hom)
    (hb₂ : c₂.hom ≫ p₂.hom = yoneda.map r₂ ≫ φ.hom) (hg : g₁ ≫ p₂ = p₁) :
    schemeSpaceMap (l ≫ r₂) ≫ φ = c₁ ≫ p₁ :=
  ObjectProperty.hom_ext _ ((congrArg (· ≫ φ.hom) (yoneda.map_comp l r₂)).trans
    ((Category.assoc _ _ _).trans ((congrArg (yoneda.map l ≫ ·) hb₂.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p₂.hom) hb₁.symm).trans
        ((Category.assoc _ _ _).trans
          (congrArg (c₁.hom ≫ ·) (congrArg (fun k => k.hom) hg))))))))

/-- The chart of the fibre product `g₁⁻¹Y` induced by a chart `c₁` of `X₁` lying over a chart `c₂`
of `X₂` through `l` is the inverse image along `l` of the chart `c₂⁻¹Y` of `Y`. -/
private theorem preimageSubspace_comp_eq_preimage_yonedaMap {V₁ V₂ : BigFppfOver B S hS}
    {c₁ : (⟨yoneda.obj V₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₁⟩ :
      AlgebraicSpaces B S hS) ⟶ X₁}
    {c₂ : (⟨yoneda.obj V₂, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₂⟩ :
      AlgebraicSpaces B S hS) ⟶ X₂} {l : V₁ ⟶ V₂}
    (hc₁ : representedSpaceMap B S hS l ≫ c₂ = c₁ ≫ g₁) :
    (preimageSubspace B S hS c₁ (preimageSubspace B S hS g₁ Y)).1 =
      (preimageSubspace B S hS c₂ Y).1.preimage (yoneda.map l) :=
  (Subfunctor.preimage_comp _ _ _).symm.trans
    ((congrArg Y.1.preimage (congrArg (fun k => k.hom) hc₁).symm).trans
      (Subfunctor.preimage_comp _ _ _))

/-- The morphism of representing schemes induced by the chart square of `f₁ : Z ⟶ Y` is a local
complete intersection morphism when `f₁` is one: the chart projections `c₁⁻¹Z ⟶ Z` and
`c₂⁻¹Y ⟶ Y` are étale and the resulting square over `f₁` commutes. -/
private theorem isLocalCompleteIntersectionMorphism_representedClosedLift_preimageLift
    {V₁ V₂ : BigFppfOver B S hS}
    {c₁ : (⟨yoneda.obj V₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₁⟩ :
      AlgebraicSpaces B S hS) ⟶ X₁}
    {c₂ : (⟨yoneda.obj V₂, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₂⟩ :
      AlgebraicSpaces B S hS) ⟶ X₂} {l : V₁ ⟶ V₂}
    (hc₁ : representedSpaceMap B S hS l ≫ c₂ = c₁ ≫ g₁)
    (hlci : IsLocalCompleteIntersection B S hS f₁.hom)
    (hb₁E : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c₁.hom)
    (hb₂E : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c₂.hom) :
    IsLocalCompleteIntersectionMorphism ((BigFppfOver.toScheme B S hS).map
      (representedClosedLift B S hS (preimageSubspace B S hS c₁ Z) (preimageSubspace B S hS c₂ Y)
        (preimageLift B S hS hc₁ Z Y f₁ sq₁))) := by
  refine hlci _ _ (representedPreimageProjection B S hS c₁ Z).hom
    (representedPreimageProjection B S hS c₂ Y).hom _
    (etale_representedPreimageProjection B S hS c₁ Z hb₁E)
    (etale_representedPreimageProjection B S hS c₂ Y hb₂E) ?_
  have e₁ := yoneda_map_representedClosedLift_comp B S hS (preimageSubspace B S hS c₁ Z)
    (preimageSubspace B S hS c₂ Y) (preimageLift B S hS hc₁ Z Y f₁ sq₁)
  have e₂ := congrArg (fun k => k.hom)
    (preimageLift_comp_preimageProjection B S hS hc₁ Z Y f₁ sq₁)
  change _ ≫ (representedClosedMap B S hS V₂ (preimageSubspace B S hS c₂ Y)).hom ≫
      (preimageProjection B S hS c₂ Y).hom =
    ((representedClosedMap B S hS V₁ (preimageSubspace B S hS c₁ Z)).hom ≫
      (preimageProjection B S hS c₁ Z).hom) ≫ f₁.hom
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans (Category.assoc _ _ _).symm)))

/-- **Stacks 06CC.**  Let `Z ⟶ Y ⟶ X` be formally unramified morphisms of algebraic spaces over a
scheme `S`, presented by universal first-order thickenings `Z ⊂ X₁` and `Y ⊂ X₂` over `X`, let
`g₁ : X₁ ⟶ X₂` be a morphism over `X` restricting to `f₁ : Z ⟶ Y` (by Stacks 060A it is the
canonical one), and let `F = Y ×_{X₂} X₁ ⊆ X₁` be the fibre product, inside which `Z` sits as the
inverse image `W` of `Z ⊆ X₁`; by Stacks 06BF it is the universal first-order thickening of `Z`
over `Y`.  If `f₁` is a local complete intersection morphism then the conormal sequence

`0 ⟶ f₁^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`

of Stacks 06BD, read on `W`, is short exact: its first arrow is the inverse image along
`W ⟶ Z` of the conormal map of Stacks 04CP of the square over `g₁`, and its second arrow is the
conormal map of the fibre product square of `W ⊆ F` over `Z ⊆ X₁`. -/
@[stacks 06CC]
theorem conormalSequence_shortExact_of_isLocalCompleteIntersection
    (hZ : IsUniversalFirstOrderThickening B S hS Z.1 p₁)
    (hY : IsUniversalFirstOrderThickening B S hS Y.1 p₂) (hg : g₁ ≫ p₂ = p₁)
    (hlci : IsLocalCompleteIntersection B S hS f₁.hom) :
    ∃ h : (modulePullback B S hS
          (X := ⟨(preimageSubspace B S hS (subspaceInclusion B S hS X₁
                (preimageSubspace B S hS g₁ Y)) Z).1.toFunctor,
              (preimageSubspace B S hS (subspaceInclusion B S hS X₁
                (preimageSubspace B S hS g₁ Y)) Z).2.1⟩)
          (preimageProjection B S hS (subspaceInclusion B S hS X₁
            (preimageSubspace B S hS g₁ Y)) Z)).map (conormalMap B S hS Z Y g₁ f₁ sq₁) ≫
        conormalMap B S hS
          (preimageSubspace B S hS (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z)
          Z (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y))
          (preimageProjection B S hS (subspaceInclusion B S hS X₁
            (preimageSubspace B S hS g₁ Y)) Z)
          (conormalEtaleRestrictionSquare B S hS
            (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z) = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  refine (shortExact_conormalSequence_iff_idealForm B S hS
    (preimageSubspace B S hS (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z)
    Z Y (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) g₁
    (preimageProjection B S hS (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z)
    f₁ (conormalEtaleRestrictionSquare B S hS
      (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z) sq₁).mpr ?_
  -- étale charts `U ⟶ X`, `V₂ ⟶ X₂` over `U` and `V₁ ⟶ X₁` over `V₂`, the last surjective
  have hA := X.2.exists_atlas
  obtain ⟨U, a, haS, haE⟩ := hA
  have hV₂ := exists_surjective_etale_presentation_lift B S hS X₂.2 X.2 p₂.hom U a haS haE
  obtain ⟨V₂, b₂, r₂, hb₂, hb₂S, hb₂E⟩ := hV₂
  have hV₁ := exists_surjective_etale_presentation_lift B S hS X₁.2 X₂.2 g₁.hom V₂ b₂ hb₂S hb₂E
  obtain ⟨V₁, b₁, l, hb₁, hb₁S, hb₁E⟩ := hV₁
  have hφ : ∃ φ : schemeSpace U ⟶ X, φ.hom = a := ⟨ObjectProperty.homMk a, rfl⟩
  obtain ⟨φ, hφ⟩ := hφ
  subst hφ
  have hc₂ : ∃ c : (⟨yoneda.obj V₂, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₂⟩ :
      AlgebraicSpaces B S hS) ⟶ X₂, c.hom = b₂ := ⟨ObjectProperty.homMk b₂, rfl⟩
  obtain ⟨c₂, hc₂⟩ := hc₂
  subst hc₂
  have hc₁ : ∃ c : (⟨yoneda.obj V₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₁⟩ :
      AlgebraicSpaces B S hS) ⟶ X₁, c.hom = b₁ := ⟨ObjectProperty.homMk b₁, rfl⟩
  obtain ⟨c₁, hc₁⟩ := hc₁
  subst hc₁
  have hφe : IsEtale B S hS φ.hom := isEtale_of_presheaf_etale B S hS haE
  have hc₂e : IsEtale B S hS c₂.hom := isEtale_of_presheaf_etale B S hS hb₂E
  have hc₁e : IsEtale B S hS c₁.hom := isEtale_of_presheaf_etale B S hS hb₁E
  have hc₁ : representedSpaceMap B S hS l ≫ c₂ = c₁ ≫ g₁ := ObjectProperty.hom_ext _ hb₁.symm
  -- the localized universal first-order thickenings, Stacks 060D
  have hYl := isUniversalFirstOrderThickening_preimageSubspace_of_isEtale B S hS Y p₂ hY φ hφe c₂
    hc₂e r₂ (ObjectProperty.hom_ext _ hb₂.symm)
  have hZl := isUniversalFirstOrderThickening_preimageSubspace_of_isEtale B S hS Z p₁ hZ φ hφe c₁
    hc₁e (l ≫ r₂) (schemeSpaceMap_comp_eq_of_chartSquare B S hS p₁ p₂ g₁ φ c₁ c₂ l r₂ hb₁ hb₂ hg)
  -- the chart of the fibre product `F = g₁⁻¹Y` and the copy of `Z` inside it
  have hZF := le_preimage_of_comp_eq B S hS Z Y f₁ sq₁
  have hρ := exists_isPullback_representedClosedHom B S hS l
    (preimageSubspace B S hS c₂ Y) (preimageSubspace B S hS c₁ (preimageSubspace B S hS g₁ Y))
    (preimageSubspace_comp_eq_preimage_yonedaMap B S hS Y g₁ hc₁)
  obtain ⟨ρ, hρ⟩ := hρ
  have hc₀ := representedSpaceMap_comp_eq_representedPreimageProjection_comp B S hS c₁
    (preimageSubspace B S hS g₁ Y)
  -- Stacks 06CC on the charts: the local complete intersection hypothesis on the chart square
  have hlci' := isLocalCompleteIntersectionMorphism_representedClosedLift_preimageLift B S hS
    Z Y g₁ f₁ sq₁ hc₁ hlci hb₁E hb₂E
  have hc₀e := isEtale_representedPreimageProjection B S hS c₁ (preimageSubspace B S hS g₁ Y) hc₁e
  have hc₀s := surjective_representedPreimageProjection B S hS c₁
    (preimageSubspace B S hS g₁ Y) hb₁S
  have sq₀' := subspaceInclusion_comp_eq_preimageLift_comp B S hS hc₀
    (preimageSubspace B S hS (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z) Z
    (preimageProjection B S hS (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z)
    (conormalEtaleRestrictionSquare B S hS
      (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z)
  have sq₁' := subspaceInclusion_comp_eq_preimageLift_comp B S hS hc₁ Z Y f₁ sq₁
  have hf₀ := isIso_preimageLift_hom B S hS (preimageSubspace B S hS g₁ Y) Z c₁ hZF
  have hR := shortExact_representedIdealForm_of_isLocalCompleteIntersection B S hS
    (representedClosedHom B S hS V₁ (preimageSubspace B S hS c₁ (preimageSubspace B S hS g₁ Y)))
    l r₂ _ _ _ _ _ sq₀' sq₁' hZl hYl ρ hρ hf₀ hlci'
  exact shortExact_idealForm_of_representedLocalization B S hS
    (preimageSubspace B S hS (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z) Z Y
    (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) g₁
    (preimageProjection B S hS (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z)
    f₁ (conormalEtaleRestrictionSquare B S hS
      (subspaceInclusion B S hS X₁ (preimageSubspace B S hS g₁ Y)) Z) sq₁
    (representedPreimageProjection B S hS c₁ (preimageSubspace B S hS g₁ Y)) c₁ c₂
    (representedClosedHom B S hS V₁ (preimageSubspace B S hS c₁ (preimageSubspace B S hS g₁ Y)))
    l hc₀ hc₁ _ _ sq₀' sq₁' hc₀e hc₁e hc₂e hc₀s hR

end General

end AlgebraicGeometry.Space

end
