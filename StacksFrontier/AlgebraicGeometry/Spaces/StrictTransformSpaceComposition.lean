module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierSupportedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformCartierCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformOffExceptional
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedFunctionsKernelIdeal

/-!
# The strict transform of an algebraic space under a composition of two blowups

Let `S` be a scheme, let `A` be an algebraic space over `S`, let `Z ⊆ A` be a closed subspace
and let `b : A' ⟶ A` be the blowup of `A` in `Z`.  Let `Z' ⊆ A'` be a closed subspace and
`c : A'' ⟶ A'` the blowup of `A'` in `Z'`.  For an algebraic space `f : X ⟶ A` over `A` write
`X'` for the strict transform of `X` with respect to `b`, a closed subspace of `P₁ = X ×_A A'`,
and `X''` for the strict transform of `X'` with respect to `c`, a closed subspace of
`R = X' ×_{A'} A''`.  The base change of the closed immersion `X' ⟶ P₁` along `A'' ⟶ A'` carries
`R` into `Q = P₁ ×_{A'} A''`, and this file identifies the image of `X''` there with the strict
transform of `X` with respect to the pair `(c ≫ b, (c ≫ b)^{-1}Y)`, for `Y ⊆ A` a closed
subspace with `|Y| = |Z| ∪ |b|(|Z'|)`, and deduces that `X''` is isomorphic to the strict
transform of `X` with respect to `c ≫ b` when `c ≫ b` is the blowup of `A` in `Y`.

## Main results

* `AlgebraicGeometry.Space.iteratedStrictTransformBaseChange` is the morphism `R ⟶ Q`, with
  `AlgebraicGeometry.Space.isPullback_iteratedStrictTransformBaseChange` the cartesian square it
  sits in and `AlgebraicGeometry.Space.isClosedImmersion_iteratedStrictTransformBaseChange` its
  being a closed immersion.
* `AlgebraicGeometry.Space.iteratedStrictTransformSpaceι` is the composite closed immersion
  `X'' ⟶ Q`, and
  `AlgebraicGeometry.Space.isClosedSubspace_range_iteratedStrictTransformSpaceι` makes its image
  a closed subspace of `Q`.
* `AlgebraicGeometry.Space.definingIdealAt_range_le_strictTransformIdealSubmodule`: **the
  defining ideal of that image is contained in the ideal of functions supported on the
  exceptional preimage of the composite centre**, at every étale chart of `Q`.
* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_iteratedStrictTransformSpace`: `X''` has no
  nonzero local function supported on the exceptional preimage of the composite centre.
* `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_range_iteratedStrictTransformSpaceι`: the
  image of `X''` in `Q` is the strict transform of `P₁ ⟶ A'` with respect to `c` and the inverse
  image of `Y`.
* `AlgebraicGeometry.Space.exists_iteratedStrictTransformSpace_iso`: if `c ≫ b` is the blowup of
  `A` in `Y`, then `X''` is isomorphic, over `X ×_A A''`, to the strict transform of `X` with
  respect to `c ≫ b`.

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A X A' A'' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A) (c : A'' ⟶ A')
variable (Z : ClosedSubspaces B S hS A.1) (Z' : ClosedSubspaces B S hS A'.1)

/-- The inclusion of a strict transform into `X ×_A A'` is a closed immersion. -/
private theorem isClosedImmersion_strictTransformSpaceι_hom (E : Subfunctor A'.1) :
    IsClosedImmersion B S hS (strictTransformSpaceι B S hS f b E).hom :=
  (strictTransform B S hS f b E).2.2

/-- The base change along `A'' ⟶ A'` of the closed immersion of the first strict transform:
`X' ×_{A'} A'' ⟶ (X ×_A A') ×_{A'} A''`. -/
abbrev iteratedStrictTransformBaseChange :
    strictTransformPullback B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c ⟶
      strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c :=
  strictTransformPullbackMap B S hS (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom))
    (strictTransformPullbackToBlowUp B S hS f b) c

/-- The closed immersion of the second strict transform into `(X ×_A A') ×_{A'} A''`. -/
abbrev iteratedStrictTransformSpaceι :
    strictTransformSpace B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
        (Z'.1.preimage c.hom) ⟶
      strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c :=
  strictTransformSpaceι B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom) ≫
    iteratedStrictTransformBaseChange B S hS f b c Z

/-- The square formed by `X' ×_{A'} A'' ⟶ (X ×_A A') ×_{A'} A''`, the closed immersion
`X' ⟶ X ×_A A'` and the two projections is cartesian. -/
theorem isPullback_iteratedStrictTransformBaseChange :
    IsPullback
      (strictTransformPullbackToSource B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c)
      (iteratedStrictTransformBaseChange B S hS f b c Z)
      (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom))
      (strictTransformPullbackToSource B S hS
        (strictTransformPullbackToBlowUp B S hS f b) c) :=
  isPullback_strictTransformPullbackMap B S hS
    (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom))
    (strictTransformPullbackToBlowUp B S hS f b) c

/-- The base change `X' ×_{A'} A'' ⟶ (X ×_A A') ×_{A'} A''` is a closed immersion. -/
theorem isClosedImmersion_iteratedStrictTransformBaseChange :
    IsClosedImmersion B S hS (iteratedStrictTransformBaseChange B S hS f b c Z).hom :=
  isClosedImmersion_of_isPullback B S hS
    (isPullback_iteratedStrictTransformBaseChange B S hS f b c Z)
    (isClosedImmersion_strictTransformSpaceι_hom B S hS f b _)

/-- The morphism from the second strict transform to `(X ×_A A') ×_{A'} A''` is a closed
immersion. -/
theorem isClosedImmersion_iteratedStrictTransformSpaceι :
    IsClosedImmersion B S hS (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom :=
  isClosedImmersion_comp B S hS _ _
    (isClosedImmersion_strictTransformSpaceι_hom B S hS _ c _)
    (isClosedImmersion_iteratedStrictTransformBaseChange B S hS f b c Z)

/-- The image of the second strict transform in `(X ×_A A') ×_{A'} A''` is a closed
subspace. -/
theorem isClosedSubspace_range_iteratedStrictTransformSpaceι :
    IsClosedSubspace B S hS
      (Subfunctor.range (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom) :=
  isClosedSubspace_range_of_isClosedImmersion B S hS _
    (strictTransformSpace B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom)).2
    (isClosedImmersion_iteratedStrictTransformSpaceι B S hS f b c Z Z')

/-! ### Point-set facts -/

/-- The inverse image under a composite, on points. -/
theorem preimage_pointsMap_comp {F G H : AlgebraicSpaces B S hS} (g₁ : F ⟶ G) (g₂ : G ⟶ H)
    (Y : Set (points B S hS H.1)) :
    pointsMap B S hS F.1 (g₁ ≫ g₂).hom ⁻¹' Y =
      pointsMap B S hS F.1 g₁.hom ⁻¹' (pointsMap B S hS G.1 g₂.hom ⁻¹' Y) := by
  rw [show (g₁ ≫ g₂).hom = g₁.hom ≫ g₂.hom from rfl, pointsMap_comp, Set.preimage_comp]

/-- **The exceptional preimage of the second centre pulls back to the exceptional preimage of
the second centre upstairs** along the base change of the first closed immersion. -/
theorem preimage_exceptionalPreimageSet_iteratedStrictTransformBaseChange :
    pointsMap B S hS _ (iteratedStrictTransformBaseChange B S hS f b c Z).hom ⁻¹'
        exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
          (Z'.1.preimage c.hom) =
      exceptionalPreimageSet B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
        (Z'.1.preimage c.hom) := by
  rw [exceptionalPreimageSet_eq_preimage, exceptionalPreimageSet_eq_preimage,
    ← preimage_pointsMap_comp B S hS (iteratedStrictTransformBaseChange B S hS f b c Z)
      (strictTransformPullbackToBlowUp B S hS (strictTransformPullbackToBlowUp B S hS f b) c),
    strictTransformPullbackMap_toBlowUp]

/-- **The inverse image of the first exceptional preimage** along that base change is the
inverse image, along the projection to the first strict transform, of its own exceptional
divisor. -/
theorem preimage_preimage_exceptionalPreimageSet_iteratedStrictTransformBaseChange :
    pointsMap B S hS _ (iteratedStrictTransformBaseChange B S hS f b c Z).hom ⁻¹'
        (pointsMap B S hS _ (strictTransformPullbackToSource B S hS
            (strictTransformPullbackToBlowUp B S hS f b) c).hom ⁻¹'
          exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom)) =
      pointsMap B S hS _ (strictTransformPullbackToSource B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c).hom ⁻¹'
        (pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ⁻¹'
          exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom)) := by
  rw [← preimage_pointsMap_comp, ← preimage_pointsMap_comp, strictTransformPullbackMap_toSource]

/-! ### The second strict transform is inside the strict transform of the composite -/

/-- On every étale chart of `(X ×_A A') ×_{A'} A''`, the defining ideal of the image of the
second strict transform is contained in the ideal of functions supported on the exceptional
preimage of `Y`, where `|Y| = |Z| ∪ |b|(|Z'|)`. -/
theorem definingIdealAt_range_le_strictTransformIdealSubmodule
    (Y : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (hc : IsBlowupAlong B S hS Z' c)
    (hY : Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
        pointsMap B S hS A'.1 b.hom '' Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι))
    (U : SmallEtale B S hS (strictTransformPullback B S hS
      (strictTransformPullbackToBlowUp B S hS f b) c).1) :
    definingIdealAt B S hS
        (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
        ⟨Subfunctor.range (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom,
          isClosedSubspace_range_iteratedStrictTransformSpaceι B S hS f b c Z Z'⟩ (op U) ≤
      (strictTransformIdealSubmodule B S hS (strictTransformPullbackToBlowUp B S hS f b) c
        (Y.1.preimage (c ≫ b).hom)).toSubmodule.obj (op U) := by
  have hT''closed : IsClosed (exceptionalPreimageSet B S hS
      (strictTransformPullbackToBlowUp B S hS f b) c (Y.1.preimage (c ≫ b).hom)) :=
    isClosed_exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c _
      (isClosedSubspace_preimage B S hS (c ≫ b).hom Y.1 A.2 A''.2 Y.2)
  have hsplit := exceptionalPreimageSet_compositeCentre B S hS f c hb Z' Y hY
  intro s hs
  refine (mem_supportedSectionsSubmodule_iff B S hS
    (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c).1
    (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c).2
    (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
      (Y.1.preimage (c ≫ b).hom))
    (SheafOfModules.unit (structureRingSheaf B S hS (strictTransformPullback B S hS
      (strictTransformPullbackToBlowUp B S hS f b) c))) U s).2 ?_
  refine sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen B S hS _ _ hT''closed
    (SheafOfModules.unit (structureRingSheaf B S hS (strictTransformPullback B S hS
      (strictTransformPullbackToBlowUp B S hS f b) c))) U s
    fun U₀ i hi => ?_
  have hrange : Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS (strictTransformPullback B S hS
        (strictTransformPullbackToBlowUp B S hS f b) c).1).obj U₀)) U₀.1.hom) ⊆
      (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
        (Y.1.preimage (c ≫ b).hom))ᶜ := by
    rintro y ⟨z, rfl⟩
    have hw : yoneda.map ((SmallEtale.toOver B S hS (strictTransformPullback B S hS
        (strictTransformPullbackToBlowUp B S hS f b) c).1).map i) ≫ U.1.hom = U₀.1.hom :=
      CostructuredArrow.w i.hom
    rw [← hw, pointsMap_comp]
    exact hi z
  set Y₀ : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj ((SmallEtale.toOver B S hS (strictTransformPullback B S hS
      (strictTransformPullbackToBlowUp B S hS f b) c).1).obj U₀),
      AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _⟩ with hY₀def
  set g₀ : Y₀ ⟶ strictTransformPullback B S hS
      (strictTransformPullbackToBlowUp B S hS f b) c :=
    ObjectProperty.homMk U₀.1.hom with hg₀def
  have hptsS₁ : Set.range (pointsMap B S hS Y₀.1
      (g₀ ≫ strictTransformPullbackToSource B S hS
        (strictTransformPullbackToBlowUp B S hS f b) c).hom) ⊆
      (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom))ᶜ := by
    rintro y ⟨z, rfl⟩ hmem
    refine hrange ⟨z, rfl⟩ ?_
    rw [hsplit]
    refine Or.inl (Set.mem_preimage.2 ?_)
    change pointsMap B S hS _ (g₀.hom ≫ _) z ∈ _ at hmem
    rwa [pointsMap_comp_apply] at hmem
  have hX' := range_le_strictTransformSubfunctor_of_points_notMem B S hS f b
    ⟨Z.1.preimage b.hom,
      isClosedSubspace_preimage B S hS b.hom Z.1 A.2 A'.2 Z.2⟩
    hb.isPullbackDefined _ hptsS₁
  set t : Y₀ ⟶ strictTransformSpace B S hS f b (Z.1.preimage b.hom) :=
    ObjectProperty.homMk (Subfunctor.lift _ hX') with htdef
  have htfac : t ≫ strictTransformSpaceι B S hS f b (Z.1.preimage b.hom) =
      g₀ ≫ strictTransformPullbackToSource B S hS
        (strictTransformPullbackToBlowUp B S hS f b) c :=
    ObjectProperty.hom_ext _ (Subfunctor.lift_ι _ hX')
  set lam := (isPullback_iteratedStrictTransformBaseChange B S hS f b c Z).lift t g₀ htfac
    with hlamdef
  have hlamfac : lam ≫ iteratedStrictTransformBaseChange B S hS f b c Z = g₀ :=
    (isPullback_iteratedStrictTransformBaseChange B S hS f b c Z).lift_snd t g₀ htfac
  have hptsT₂ : Set.range (pointsMap B S hS Y₀.1 lam.hom) ⊆
      (exceptionalPreimageSet B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
        (Z'.1.preimage c.hom))ᶜ := by
    rintro y ⟨z, rfl⟩ hmem
    rw [← preimage_exceptionalPreimageSet_iteratedStrictTransformBaseChange B S hS f b c Z Z']
      at hmem
    refine hrange ⟨z, rfl⟩ ?_
    rw [hsplit]
    refine Or.inr ?_
    have hgz : pointsMap B S hS Y₀.1 g₀.hom z =
        pointsMap B S hS _ (iteratedStrictTransformBaseChange B S hS f b c Z).hom
          (pointsMap B S hS Y₀.1 lam.hom z) := by
      rw [← hlamfac]
      exact pointsMap_comp_apply B S hS lam.hom _ z
    rwa [show pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS
          (strictTransformPullback B S hS
            (strictTransformPullbackToBlowUp B S hS f b) c).1).obj U₀)) U₀.1.hom z =
        pointsMap B S hS Y₀.1 g₀.hom z from rfl, hgz]
  have hW₂ := range_le_strictTransformSubfunctor_of_points_notMem B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
    ⟨Z'.1.preimage c.hom,
      isClosedSubspace_preimage B S hS c.hom Z'.1 A'.2 A''.2 Z'.2⟩
    hc.isPullbackDefined lam hptsT₂
  have hD : Subfunctor.range g₀.hom ≤
      Subfunctor.range (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom := by
    have hfac : Subfunctor.lift lam.hom hW₂ ≫
        (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom = g₀.hom :=
      calc Subfunctor.lift lam.hom hW₂ ≫
            (strictTransform B S hS
                (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
                (Z'.1.preimage c.hom)).1.ι ≫
              (iteratedStrictTransformBaseChange B S hS f b c Z).hom
          = (Subfunctor.lift lam.hom hW₂ ≫
              (strictTransform B S hS
                  (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
                  (Z'.1.preimage c.hom)).1.ι) ≫
              (iteratedStrictTransformBaseChange B S hS f b c Z).hom :=
            (Category.assoc _ _ _).symm
        _ = lam.hom ≫ (iteratedStrictTransformBaseChange B S hS f b c Z).hom :=
            congrArg (fun φ => φ ≫ (iteratedStrictTransformBaseChange B S hS f b c Z).hom)
              (Subfunctor.lift_ι _ hW₂)
        _ = g₀.hom := congrArg (fun φ : Y₀ ⟶ _ => φ.hom) hlamfac
    rw [← hfac]
    exact Subfunctor.range_comp_le _ _
  refine definingIdealAt_le_ker_of_comp_eq B S hS _ Y₀ _ g₀
    (ObjectProperty.homMk (Subfunctor.lift g₀.hom hD))
    (ObjectProperty.hom_ext _ (Subfunctor.lift_ι _ hD)) U
    ((SmallEtale.toOver B S hS (strictTransformPullback B S hS
      (strictTransformPullbackToBlowUp B S hS f b) c).1).map i) (𝟙 _) ?_ hs
  rw [Category.id_comp]
  exact CostructuredArrow.w i.hom

/-- The points of the inverse image of the centre along a morphism to `X ×_A A'` followed by the
projection to `X` are the inverse image of the exceptional preimage. -/
theorem subspacePointSet_preimage_preimageClosedSubspace_comp_toSource
    {W : AlgebraicSpaces B S hS} (g : W.1 ⟶ (strictTransformPullback B S hS f b).1) :
    subspacePointSet B S hS W.1
        ((preimageClosedSubspace f Z).1.preimage
          (g ≫ (strictTransformPullbackToSource B S hS f b).hom)) =
      pointsMap B S hS W.1 g ⁻¹' exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom) := by
  rw [preimage_preimageClosedSubspace_comp_toSource,
    ← preimage_exceptionalPreimage_eq_preimage_centre]
  exact range_pointsMap_preimage_ι B S hS g _

/-- **The structure sheaf of a strict transform has no nonzero local section supported on its
exceptional divisor.** -/
theorem hasNoSectionsSupportedIn_structureSheaf_strictTransform
    (hb : IsBlowupAlong B S hS Z b) :
    HasNoSectionsSupportedIn B S hS (strictTransformSpace B S hS f b (Z.1.preimage b.hom))
      (pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ⁻¹'
        exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom))
      (SheafOfModules.unit (structureRingSheaf B S hS
        (strictTransformSpace B S hS f b (Z.1.preimage b.hom)))) := by
  have hdiv := hasNoSectionsSupportedIn_structureSheaf_of_isEffectiveCartierDivisor B S hS
    (strictTransformSpace B S hS f b (Z.1.preimage b.hom))
    ⟨(preimageClosedSubspace f Z).1.preimage
        (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom) ≫
          strictTransformPullbackToSource B S hS f b).hom,
      isClosedSubspace_preimage B S hS _ _ X.2
        (strictTransformSpace B S hS f b (Z.1.preimage b.hom)).2
        (preimageClosedSubspace f Z).2⟩
    (isPullbackDefined_strictTransform_of_isBlowupAlong B S hS f b Z hb)
  rwa [show (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom) ≫
        strictTransformPullbackToSource B S hS f b).hom =
      (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ≫
        (strictTransformPullbackToSource B S hS f b).hom from rfl,
    subspacePointSet_preimage_preimageClosedSubspace_comp_toSource B S hS f b Z] at hdiv

/-! ### The open part off the second exceptional divisor, inside the second strict transform -/

/-- The open part of `X' ×_{A'} A''` off the second exceptional divisor lies in the second
strict transform. -/
theorem range_offExceptionalι_le_strictTransformSubfunctor (hc : IsBlowupAlong B S hS Z' c) :
    Subfunctor.range (offExceptionalι B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z').hom ≤
      strictTransformSubfunctor B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
        (Z'.1.preimage c.hom) :=
  range_le_strictTransformSubfunctor_of_points_notMem B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
    ⟨Z'.1.preimage c.hom, isClosedSubspace_preimage B S hS c.hom Z'.1 A'.2 A''.2 Z'.2⟩
    hc.isPullbackDefined _
    (range_pointsMap_offExceptionalι B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z').le

/-- The open part of `R` lying off the second exceptional divisor, as a morphism to the second
strict transform. -/
def offExceptionalToStrictTransform (hc : IsBlowupAlong B S hS Z' c) :
    offExceptionalSpace B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z' ⟶
      strictTransformSpace B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
        (Z'.1.preimage c.hom) :=
  ObjectProperty.homMk
    (Subfunctor.lift _ (range_offExceptionalι_le_strictTransformSubfunctor B S hS f b c Z Z' hc))

/-- The morphism from the open part off the second exceptional divisor to the second strict
transform, followed by the inclusion of the strict transform, is the open inclusion. -/
theorem offExceptionalToStrictTransform_ι (hc : IsBlowupAlong B S hS Z' c) :
    offExceptionalToStrictTransform B S hS f b c Z Z' hc ≫
        strictTransformSpaceι B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom) =
      offExceptionalι B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z' :=
  ObjectProperty.hom_ext _ (Subfunctor.lift_ι _
    (range_offExceptionalι_le_strictTransformSubfunctor B S hS f b c Z Z' hc))

/-- The inclusion of the strict transform into `X ×_A A'` is a monomorphism. -/
theorem mono_strictTransformSpaceι :
    Mono (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom :=
  mono_of_isClosedImmersion B S hS _ (isClosedImmersion_strictTransformSpaceι_hom B S hS f b _)

/-- The underlying morphisms of presheaves satisfy
`offExceptionalToStrictTransform ≫ strictTransformSpaceι = offExceptionalι`. -/
theorem offExceptionalToStrictTransform_hom_ι (hc : IsBlowupAlong B S hS Z' c) :
    (offExceptionalToStrictTransform B S hS f b c Z Z' hc).hom ≫
        (strictTransformSpaceι B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom)).hom =
      (offExceptionalι B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z').hom :=
  congrArg (fun φ : offExceptionalSpace B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z' ⟶
    strictTransformPullback B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c => φ.hom)
    (offExceptionalToStrictTransform_ι B S hS f b c Z Z' hc)

/-- The morphism from the open part off the second exceptional divisor to the second strict
transform is étale. -/
theorem isEtale_offExceptionalToStrictTransform (hc : IsBlowupAlong B S hS Z' c) :
    IsEtale B S hS (offExceptionalToStrictTransform B S hS f b c Z Z' hc).hom := by
  have := mono_strictTransformSpaceι B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z'
  refine isEtale_of_comp_mono B S hS _
    (strictTransformSpaceι B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom)).hom ?_
  rw [offExceptionalToStrictTransform_hom_ι]
  exact isEtale_offExceptionalι B S hS _ c Z'

/-- The morphism from the open part off the second exceptional divisor to the second strict
transform is a monomorphism. -/
theorem mono_offExceptionalToStrictTransform (hc : IsBlowupAlong B S hS Z' c) :
    Mono (offExceptionalToStrictTransform B S hS f b c Z Z' hc).hom := by
  have := mono_offExceptionalι B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z'
  exact mono_of_mono_fac (offExceptionalToStrictTransform_hom_ι B S hS f b c Z Z' hc)

/-- On points, `offExceptionalToStrictTransform` followed by the inclusion of the second strict
transform is the open inclusion `offExceptionalι`. -/
theorem pointsMap_offExceptionalToStrictTransform_comp (hc : IsBlowupAlong B S hS Z' c)
    (x : points B S hS (offExceptionalSpace B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z').1) :
    pointsMap B S hS _ (strictTransformSpaceι B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom)).hom
        (pointsMap B S hS _ (offExceptionalToStrictTransform B S hS f b c Z Z' hc).hom x) =
      pointsMap B S hS _ (offExceptionalι B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z').hom x := by
  rw [← pointsMap_comp_apply, offExceptionalToStrictTransform_hom_ι]

/-- The points in the image of `offExceptionalToStrictTransform` are exactly the points of the
second strict transform off the second exceptional divisor. -/
theorem range_pointsMap_offExceptionalToStrictTransform (hc : IsBlowupAlong B S hS Z' c) :
    Set.range (pointsMap B S hS _
        (offExceptionalToStrictTransform B S hS f b c Z Z' hc).hom) =
      (pointsMap B S hS _ (strictTransformSpaceι B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom)).hom ⁻¹'
        exceptionalPreimageSet B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom))ᶜ := by
  have hinj : Function.Injective (pointsMap B S hS _ (strictTransformSpaceι B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom)).hom) :=
    injective_pointsMap_of_isImmersion B S hS
      (strictTransformPullback B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c).2 _
      (isImmersion_of_isClosedImmersion B S hS
        (isClosedImmersion_strictTransformSpaceι_hom B S hS _ c _))
  have hoff := range_pointsMap_offExceptionalι B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z'
  ext y
  constructor
  · rintro ⟨x, rfl⟩ hmem
    refine hoff.le ⟨x, rfl⟩ ?_
    rwa [← pointsMap_offExceptionalToStrictTransform_comp B S hS f b c Z Z' hc x]
  · intro hy
    obtain ⟨z, hz⟩ := hoff.ge hy
    exact ⟨z, hinj ((pointsMap_offExceptionalToStrictTransform_comp B S hS f b c Z Z' hc z).trans
      hz)⟩

/-- A morphism from a representable to the second strict transform whose points lie off the
second exceptional divisor factors through `offExceptionalToStrictTransform`. -/
theorem factorsThrough_offExceptionalToStrictTransform (hc : IsBlowupAlong B S hS Z' c)
    (A₀ : BigFppfOver B S hS)
    (φ : yoneda.obj A₀ ⟶ (strictTransformSpace B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom)).1)
    (hφ : Set.range (pointsMap B S hS (yoneda.obj A₀) φ) ⊆
      (pointsMap B S hS _ (strictTransformSpaceι B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom)).hom ⁻¹'
        exceptionalPreimageSet B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom))ᶜ) :
    ∃ g, g ≫ (offExceptionalToStrictTransform B S hS f b c Z Z' hc).hom = φ := by
  have := mono_strictTransformSpaceι B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z'
  obtain ⟨g, hg⟩ := factorsThrough_offExceptional B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z'
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A₀)
    (φ ≫ (strictTransformSpaceι B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom)).hom)
    (by
      rintro y ⟨z, rfl⟩
      rw [pointsMap_comp_apply]
      exact hφ ⟨z, rfl⟩)
  refine ⟨g, (cancel_mono (strictTransformSpaceι B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
    (Z'.1.preimage c.hom)).hom).1 ?_⟩
  rw [Category.assoc, offExceptionalToStrictTransform_hom_ι, hg]

/-! ### Two general reductions for functions supported on a union -/

/-- **An étale pullback of a structure sheaf inherits the absence of supported functions from a
second etale morphism.**  Let `j : V ⟶ W` and `g : V ⟶ X₀` be étale morphisms of algebraic
spaces, let `T` be a set of points of `X₀` and `T'` a set of points of `W` with the same inverse
image in the points of `V`, and suppose `𝒪_{X₀}` has no nonzero local section supported on `T`.
Then the étale restriction of `𝒪_W` to `V` has no nonzero local section supported on the
inverse image of `T'`. -/
theorem hasNoSectionsSupportedIn_etaleModulePullback_unit
    {V W X₀ : AlgebraicSpaces B S hS} (j : V ⟶ W) (hj : IsEtale B S hS j.hom)
    (g : V ⟶ X₀) (hg : IsEtale B S hS g.hom)
    (T : Set (points B S hS X₀.1)) (T' : Set (points B S hS W.1))
    (hTT : pointsMap B S hS V.1 j.hom ⁻¹' T' = pointsMap B S hS V.1 g.hom ⁻¹' T)
    (hX₀ : HasNoSectionsSupportedIn B S hS X₀ T
      (SheafOfModules.unit (structureRingSheaf B S hS X₀))) :
    HasNoSectionsSupportedIn B S hS V (pointsMap B S hS V.1 j.hom ⁻¹' T')
      ((etaleModulePullback B S hS j hj).obj
        (SheafOfModules.unit (structureRingSheaf B S hS W))) := by
  intro U s hs
  have h1 := (sectionSupportedIn_etaleModulePullback_iff B S hS j hj T' _ U s).mp hs
  have hmem := (mem_supportedSectionsSubmodule_iff B S hS W.1 W.2 T'
    (SheafOfModules.unit (structureRingSheaf B S hS W)) _ _).2 h1
  have h2 := le_of_eq (supportedSectionsUnit_obj_postcomp B S hS j hj T' _ rfl U).symm hmem
  rw [hTT] at h2
  have h3 := le_of_eq (supportedSectionsUnit_obj_postcomp B S hS g hg T _ rfl U) h2
  exact hX₀ ((smallEtalePostcomp B S hS g hg).obj U) s
    ((mem_supportedSectionsSubmodule_iff B S hS X₀.1 X₀.2 T
      (SheafOfModules.unit (structureRingSheaf B S hS X₀))
      ((smallEtalePostcomp B S hS g hg).obj U) _).1 h3)

/-- **No functions supported on a union.**  Let `j : V ⟶ W` be an étale monomorphism with image
off the closed set `T₂`, through which every morphism from a representable with image off `T₂`
factors.  If `𝒪_W` has no nonzero local section supported on `T₂`, and its étale restriction to
`V` none supported on the inverse image of `T₁`, then `𝒪_W` has none supported on `T₁ ∪ T₂`. -/
theorem hasNoSectionsSupportedIn_union_structureSheaf
    {V W : AlgebraicSpaces B S hS} (j : V ⟶ W) (hj : IsEtale B S hS j.hom) [Mono j.hom]
    (T₁ T₂ : Set (points B S hS W.1)) (hT₂ : IsClosed T₂)
    (hfac : ∀ (A₀ : BigFppfOver B S hS) (φ : yoneda.obj A₀ ⟶ W.1),
      Set.range (pointsMap B S hS (yoneda.obj A₀) φ) ⊆ T₂ᶜ → ∃ g, g ≫ j.hom = φ)
    (hVrange : Set.range (pointsMap B S hS V.1 j.hom) ⊆ T₂ᶜ)
    (hV : HasNoSectionsSupportedIn B S hS V (pointsMap B S hS V.1 j.hom ⁻¹' T₁)
      ((etaleModulePullback B S hS j hj).obj
        (SheafOfModules.unit (structureRingSheaf B S hS W))))
    (hW : HasNoSectionsSupportedIn B S hS W T₂
      (SheafOfModules.unit (structureRingSheaf B S hS W))) :
    HasNoSectionsSupportedIn B S hS W (T₁ ∪ T₂)
      (SheafOfModules.unit (structureRingSheaf B S hS W)) := by
  have hunion := supportedSectionsSubmodule_union_eq_of_isEtale B S hS j hj T₁ T₂ hT₂ hfac hVrange _
    hV
  intro U s hs
  have h1 := (mem_supportedSectionsSubmodule_iff B S hS W.1 W.2 (T₁ ∪ T₂)
    (SheafOfModules.unit (structureRingSheaf B S hS W)) U s).2 hs
  rw [hunion] at h1
  exact hW U s ((mem_supportedSectionsSubmodule_iff B S hS W.1 W.2 T₂
    (SheafOfModules.unit (structureRingSheaf B S hS W)) U s).1 h1)

/-! ### The second strict transform has no functions supported on the exceptional set -/

/-- The open part of `R` lying off the second exceptional divisor maps to the first strict
transform both through the second strict transform and directly. -/
theorem offExceptionalToStrictTransform_comp_toSource (hc : IsBlowupAlong B S hS Z' c) :
    (offExceptionalToStrictTransform B S hS f b c Z Z' hc) ≫
      ((strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom))
      c (Z'.1.preimage c.hom)) ≫
      (strictTransformPullbackToSource B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c)) =
      ((offExceptionalι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      Z') ≫ (strictTransformPullbackToSource B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c)) := by
  rw [← Category.assoc, offExceptionalToStrictTransform_ι B S hS f b c Z Z' hc]

/-- The inverse image, in the open part of `R` off the second exceptional divisor, of the first
exceptional divisor is the same whether computed through the second strict transform or
directly. -/
theorem preimage_pointsMap_offExceptionalToStrictTransform_firstExceptional
    (hc : IsBlowupAlong B S hS Z' c) :
    pointsMap B S hS _ (offExceptionalToStrictTransform B S hS f b c Z Z' hc).hom ⁻¹'
      (pointsMap B S hS _
      ((strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom))
      c (Z'.1.preimage c.hom)) ≫
      (strictTransformPullbackToSource B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c)).hom ⁻¹'
      (pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ⁻¹'
      (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom)))) = pointsMap B S hS _
      ((offExceptionalι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      Z') ≫ (strictTransformPullbackToSource B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c)).hom ⁻¹'
      (pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ⁻¹'
      (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom))) :=
  (preimage_pointsMap_comp B S hS (offExceptionalToStrictTransform B S hS f b c Z Z' hc)
    ((strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
    (Z'.1.preimage c.hom)) ≫
    (strictTransformPullbackToSource B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c))
    (pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ⁻¹'
    (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom)))).symm.trans
    (congrArg
      (fun φ :
      (offExceptionalSpace B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      Z') ⟶ _ => pointsMap B S hS
      (offExceptionalSpace B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      Z').1 φ.hom ⁻¹'
      (pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ⁻¹'
      (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom))))
      (offExceptionalToStrictTransform_comp_toSource B S hS f b c Z Z' hc))

/-- **The exceptional preimage of the composite centre, pulled back to the second strict
transform, is the union of the two exceptional divisors there.** -/
theorem preimage_pointsMap_iteratedStrictTransformSpaceι_compositeCentre
    (Y : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (hY : Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
        pointsMap B S hS A'.1 b.hom '' Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι)) :
    pointsMap B S hS _ (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom ⁻¹'
      (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
      (Y.1.preimage (c ≫ b).hom)) =
      (pointsMap B S hS _
      ((strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom))
      c (Z'.1.preimage c.hom)) ≫
      (strictTransformPullbackToSource B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c)).hom ⁻¹'
      (pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ⁻¹'
      (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom)))) ∪
      (pointsMap B S hS _
      (strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom)).hom ⁻¹'
      (exceptionalPreimageSet B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom))
      c (Z'.1.preimage c.hom))) := by
  rw [exceptionalPreimageSet_compositeCentre B S hS f c hb Z' Y hY, Set.preimage_union,
    show (iteratedStrictTransformSpaceι B S hS f b c Z Z') =
      (strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom)) ≫ (iteratedStrictTransformBaseChange B S hS f b c Z) from rfl,
    preimage_pointsMap_comp B S hS
      (strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom)) (iteratedStrictTransformBaseChange B S hS f b c Z),
      preimage_pointsMap_comp B S hS
      (strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom)) (iteratedStrictTransformBaseChange B S hS f b c Z),
    preimage_preimage_exceptionalPreimageSet_iteratedStrictTransformBaseChange B S hS f b c Z,
    preimage_exceptionalPreimageSet_iteratedStrictTransformBaseChange B S hS f b c Z Z',
    ← preimage_pointsMap_comp B S hS
      (strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom))
      (strictTransformPullbackToSource B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c)]

/-- **The second strict transform has no nonzero local function supported on the exceptional
preimage of the composite centre.** -/
theorem hasNoSectionsSupportedIn_iteratedStrictTransformSpace
    (Y : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (hc : IsBlowupAlong B S hS Z' c)
    (hY : Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
        pointsMap B S hS A'.1 b.hom '' Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι)) :
    HasNoSectionsSupportedIn B S hS
      (strictTransformSpace B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
      (Z'.1.preimage c.hom))
      (pointsMap B S hS _ (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom ⁻¹'
        (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
        (Y.1.preimage (c ≫ b).hom)))
        (SheafOfModules.unit
        (structureRingSheaf B S hS
        (strictTransformSpace B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom))
        c (Z'.1.preimage c.hom)))) := by
  have := mono_offExceptionalToStrictTransform B S hS f b c Z Z' hc
  rw [preimage_pointsMap_iteratedStrictTransformSpaceι_compositeCentre B S hS f b c Z Z' Y hb hY]
  refine hasNoSectionsSupportedIn_union_structureSheaf B S hS
    (offExceptionalToStrictTransform B S hS f b c Z Z' hc)
    (isEtale_offExceptionalToStrictTransform B S hS f b c Z Z' hc)
    (pointsMap B S hS _
    ((strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
    (Z'.1.preimage c.hom)) ≫
    (strictTransformPullbackToSource B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c)).hom ⁻¹'
    (pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ⁻¹'
    (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom))))
    (pointsMap B S hS _
    (strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
    (Z'.1.preimage c.hom)).hom ⁻¹'
    (exceptionalPreimageSet B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
    (Z'.1.preimage c.hom)))
    ((isClosed_exceptionalPreimageSet_preimage B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z').preimage
      ((pointTopologyFamily B S hS).continuous
        (strictTransformSpace B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom))
        c (Z'.1.preimage c.hom)).2
        (strictTransformPullback B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c).2
          (strictTransformSpaceι B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom)).hom))
    (fun A₀ φ hφ =>
      factorsThrough_offExceptionalToStrictTransform B S hS f b c Z Z' hc A₀ φ hφ)
    (range_pointsMap_offExceptionalToStrictTransform B S hS f b c Z Z' hc).le ?_
    (hasNoSectionsSupportedIn_structureSheaf_strictTransform B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z' hc)
  exact hasNoSectionsSupportedIn_etaleModulePullback_unit B S hS
    (offExceptionalToStrictTransform B S hS f b c Z Z' hc)
    (isEtale_offExceptionalToStrictTransform B S hS f b c Z Z' hc)
    ((offExceptionalι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z') ≫
    (strictTransformPullbackToSource B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c))
    (isEtale_offExceptional_toSource B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c Z' hc)
      (pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ⁻¹'
      (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom)))
      (pointsMap B S hS _
      ((strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom))
      c (Z'.1.preimage c.hom)) ≫
      (strictTransformPullbackToSource B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c)).hom ⁻¹'
      (pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Z.1.preimage b.hom)).hom ⁻¹'
      (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom))))
    (preimage_pointsMap_offExceptionalToStrictTransform_firstExceptional B S hS f b c Z Z' hc)
    (hasNoSectionsSupportedIn_structureSheaf_strictTransform B S hS f b Z hb)

/-! ### The image of the second strict transform is the strict transform of the composite -/

/-- The scheme-theoretic image of the closed immersion of the second strict transform into
`(X ×_A A') ×_{A'} A''` is its image. -/
theorem schemeTheoreticImageSubfunctor_iteratedStrictTransformSpaceι :
    schemeTheoreticImageSubfunctor B S hS (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom =
      Subfunctor.range (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom :=
  le_antisymm
    (schemeTheoreticImageSubfunctor_le B S hS (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom
    (isClosedSubspace_range_iteratedStrictTransformSpaceι B S hS f b c Z Z') le_rfl)
    (range_le_schemeTheoreticImageSubfunctor B S hS
      (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom)

/-- The defining ideal sheaf of the image of the second strict transform in
`(X ×_A A') ×_{A'} A''` is the ideal of functions supported on the exceptional preimage of `Y`,
where `|Y| = |Z| ∪ |b|(|Z'|)`. -/
theorem definingIdealSheaf_range_iteratedStrictTransformSpaceι
    (Y : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (hc : IsBlowupAlong B S hS Z' c)
    (hY : Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
        pointsMap B S hS A'.1 b.hom '' Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι)) :
    definingIdealSheaf B S hS
      (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
      ⟨Subfunctor.range (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom,
      (isClosedSubspace_range_iteratedStrictTransformSpaceι B S hS f b c Z Z')⟩ =
      strictTransformIdealSubmodule B S hS (strictTransformPullbackToBlowUp B S hS f b) c
        (Y.1.preimage (c ≫ b).hom) := by
  have h082Z := kernelIdealSheaf_le_definingIdealSheaf_schemeTheoreticImage B S hS
    (iteratedStrictTransformSpaceι B S hS f b c Z Z')
    (isQuasiCompact_of_isClosedImmersion' B S hS
      (isClosedImmersion_iteratedStrictTransformSpaceι B S hS f b c Z Z'))
  have himg : schemeTheoreticImage B S hS (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom
    (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c).2 =
      (⟨Subfunctor.range (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom,
        (isClosedSubspace_range_iteratedStrictTransformSpaceι B S hS f b c Z Z')⟩ : ClosedSubspaces
        B S hS (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c).1) :=
    Subtype.ext (schemeTheoreticImageSubfunctor_iteratedStrictTransformSpaceι B S hS f b c Z Z')
  rw [himg] at h082Z
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U => ?_)
  refine le_antisymm ?_ ?_
  · exact definingIdealAt_range_le_strictTransformIdealSubmodule B S hS f b c Z Z' Y hb hc hY
      U.unop
  · refine le_trans
      (supportedSectionsSubmodule_le_kernelIdealSheaf B S hS
      (iteratedStrictTransformSpaceι B S hS f b c Z Z')
      (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
      (Y.1.preimage (c ≫ b).hom))
      (isClosed_exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
        (Y.1.preimage (c ≫ b).hom)
        (isClosedSubspace_preimage B S hS (c ≫ b).hom Y.1 A.2 A''.2 Y.2))
      (hasNoSectionsSupportedIn_iteratedStrictTransformSpace B S hS f b c Z Z' Y hb hc hY) U) ?_
    exact h082Z U

/-- The strict transform of `X ×_A A' ⟶ A'` with respect to `c` and the inverse image of `Y`,
where `|Y| = |Z| ∪ |b|(|Z'|)`, is the image of the second strict transform. -/
theorem strictTransformSubfunctor_eq_range_iteratedStrictTransformSpaceι
    (Y : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (hc : IsBlowupAlong B S hS Z' c)
    (hY : Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
        pointsMap B S hS A'.1 b.hom '' Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι)) :
    strictTransformSubfunctor B S hS (strictTransformPullbackToBlowUp B S hS f b) c
      (Y.1.preimage (c ≫ b).hom) = Subfunctor.range
      (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom :=
  strictTransformSubfunctor_eq_of_definingIdealSheaf_eq B S hS
    (strictTransformPullbackToBlowUp B S hS f b) c (Y.1.preimage (c ≫ b).hom)
    ⟨Subfunctor.range (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom,
      (isClosedSubspace_range_iteratedStrictTransformSpaceι B S hS f b c Z Z')⟩
    (definingIdealSheaf_range_iteratedStrictTransformSpaceι B S hS f b c Z Z' Y hb hc hY)

/-! ### General: a monomorphism is an isomorphism onto a subfunctor it exhausts -/

/-- The inclusion of a subfunctor into an equal subfunctor is an isomorphism. -/
theorem isIso_homOfLe_of_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G G' : Subfunctor F}
    (h : G = G') : IsIso (Subfunctor.homOfLe (le_of_eq h)) := by
  subst h
  have hid : Subfunctor.homOfLe (le_of_eq (rfl : G = G)) = 𝟙 G.toFunctor :=
    (cancel_mono G.ι).1 (by rw [Subfunctor.homOfLe_ι, Category.id_comp])
  rw [hid]
  infer_instance

/-- A monomorphism of presheaves lifts to an isomorphism onto a subfunctor equal to its
image. -/
theorem isIso_lift_of_range_eq {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ψ : F' ⟶ F) [Mono ψ]
    {G : Subfunctor F} (h : Subfunctor.range ψ = G) :
    IsIso (Subfunctor.lift ψ (le_of_eq h)) := by
  have heq : Subfunctor.lift ψ (le_of_eq h) =
      Subfunctor.toRange ψ ≫ Subfunctor.homOfLe (le_of_eq h) :=
    (cancel_mono G.ι).1 (by
      rw [Subfunctor.lift_ι, Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι])
  rw [heq]
  have := isIso_homOfLe_of_eq B S hS h
  infer_instance

/-! ### The comparison of the two strict transforms of a space -/

/-- The morphism `X' ×_{A'} A'' ⟶ X ×_A A''` is the base change
`X' ×_{A'} A'' ⟶ (X ×_A A') ×_{A'} A''` followed by the canonical isomorphism
`(X ×_A A') ×_{A'} A'' ≅ X ×_A A''`. -/
theorem iteratedStrictTransformSpaceMap_eq :
    (iteratedStrictTransformSpaceMap B S hS f b c (Z.1.preimage b.hom)) =
      (iteratedStrictTransformBaseChange B S hS f b c Z) ≫
      (iteratedStrictTransformPullbackIso B S hS f b c).hom := by
  refine (AlgebraicSpaces.isPullback_fiberProduct B S hS f (c ≫ b)).hom_ext ?_ ?_
  · rw [iteratedStrictTransformSpaceMap_toSource, Category.assoc,
      iteratedStrictTransformPullbackIso_hom_toSource, ← Category.assoc, ← Category.assoc,
      strictTransformPullbackMap_toSource]
  · rw [iteratedStrictTransformSpaceMap_toBlowUp, Category.assoc,
      iteratedStrictTransformPullbackIso_hom_toBlowUp, strictTransformPullbackMap_toBlowUp]

/-- If `c ≫ b` is the blowup of `A` in `Y`, where `|Y| = |Z| ∪ |b|(|Z'|)`, then the image of the
second strict transform in `X ×_A A''` is the strict transform of `X` with respect to `c ≫ b`. -/
theorem range_iteratedStrictTransformSpaceι_comp_iso
    (Y : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (hc : IsBlowupAlong B S hS Z' c)
    (hY : Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
        pointsMap B S hS A'.1 b.hom '' Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι))
    (hd : IsBlowupAlong B S hS Y (c ≫ b)) :
    Subfunctor.range
      ((iteratedStrictTransformSpaceι B S hS f b c Z Z').hom ≫
      (iteratedStrictTransformPullbackIso B S hS f b c).hom.hom) =
      strictTransformSubfunctor B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) := by
  have : IsIso (iteratedStrictTransformPullbackIso B S hS f b c).hom.hom :=
    (ObjectProperty.ι _).map_isIso (iteratedStrictTransformPullbackIso B S hS f b c).hom
  have hT := exceptionalPreimageSet_eq_preimage_of_comp_eq B S hS f (c ≫ b)
    (Y.1.preimage (c ≫ b).hom)
    (strictTransformPullbackToBlowUp B S hS f b) c (Y.1.preimage (c ≫ b).hom) (𝟙 A'')
      (iteratedStrictTransformPullbackIso B S hS f b c).hom
    (by rw [iteratedStrictTransformPullbackIso_hom_toBlowUp, Category.comp_id]) (by simp)
  have hpre := strictTransformSubfunctor_eq_preimage_of_isEffectiveCartierDivisor B S hS f (c ≫ b)
    ⟨(Y.1.preimage (c ≫ b).hom), isClosedSubspace_preimage B S hS (c ≫ b).hom Y.1 A.2 A''.2 Y.2⟩
    hd.isPullbackDefined (strictTransformPullbackToBlowUp B S hS f b) c (Y.1.preimage (c ≫ b).hom)
      (iteratedStrictTransformPullbackIso B S hS f b c).hom (isEtale_of_isIso B S hS _) hT
  rw [Subfunctor.range_comp,
    ← strictTransformSubfunctor_eq_range_iteratedStrictTransformSpaceι B S hS f b c Z Z' Y hb hc
      hY,
    hpre, Subfunctor.preimage_image_of_epi]

/-- If `c ≫ b` is the blowup of `A` in `Y`, where `|Y| = |Z| ∪ |b|(|Z'|)`, then the second
strict transform is isomorphic, compatibly with the morphisms to `X ×_A A''`, to the strict
transform of `X` with respect to `c ≫ b`. -/
theorem exists_iteratedStrictTransformSpace_iso
    (Y : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (hc : IsBlowupAlong B S hS Z' c)
    (hY : Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
        pointsMap B S hS A'.1 b.hom '' Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι))
    (hd : IsBlowupAlong B S hS Y (c ≫ b)) :
    ∃ j : strictTransformSpace B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom))
      c (Z'.1.preimage c.hom) ≅
        strictTransformSpace B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom),
      j.hom ≫ strictTransformSpaceι B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) =
        (strictTransformSpaceι B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom))
        c (Z'.1.preimage c.hom)) ≫
        (iteratedStrictTransformSpaceMap B S hS f b c (Z.1.preimage b.hom)) := by
  have : IsIso (iteratedStrictTransformPullbackIso B S hS f b c).hom.hom :=
    (ObjectProperty.ι _).map_isIso (iteratedStrictTransformPullbackIso B S hS f b c).hom
  have : Mono (iteratedStrictTransformSpaceι B S hS f b c Z Z').hom :=
    mono_of_isClosedImmersion B S hS _
      (isClosedImmersion_iteratedStrictTransformSpaceι B S hS f b c Z Z')
  have : Mono
    ((iteratedStrictTransformSpaceι B S hS f b c Z Z').hom ≫
    (iteratedStrictTransformPullbackIso B S hS f b c).hom.hom) := mono_comp _ _
  have hrange := range_iteratedStrictTransformSpaceι_comp_iso B S hS f b c Z Z' Y hb hc hY hd
  have hiso := isIso_lift_of_range_eq B S hS
    ((iteratedStrictTransformSpaceι B S hS f b c Z Z').hom ≫
    (iteratedStrictTransformPullbackIso B S hS f b c).hom.hom) hrange
  refine ⟨ObjectProperty.isoMk _ (@asIso _ _ _ _ _ hiso), ObjectProperty.hom_ext _ ?_⟩
  show Subfunctor.lift
    ((iteratedStrictTransformSpaceι B S hS f b c Z Z').hom ≫
    (iteratedStrictTransformPullbackIso B S hS f b c).hom.hom) (le_of_eq hrange) ≫
    (strictTransformSubfunctor B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom)).ι = _
  rw [Subfunctor.lift_ι, iteratedStrictTransformSpaceMap_eq B S hS f b c Z]
  exact Category.assoc _ _ _

end AlgebraicGeometry.Space

end
