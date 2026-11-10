module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierSupportedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformCartierCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformComparisonOffExceptional
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessAndStrictTransformImageUnconditional

/-!
# Functoriality of strict transforms along a morphism over the base

Let `b : A' ⟶ A` be the blowup of an algebraic space `A` in a closed subspace `Z`, and let
`c : X₁ ⟶ X` be a morphism of algebraic spaces over `A`.  The strict transform of `X₁` maps to
the strict transform of `X`, compatibly with the morphism `X₁ ×_A A' ⟶ X ×_A A'` induced by `c`.

## Main results

* `AlgebraicGeometry.Space.comp_eq_zero_of_hasNoSectionsSupportedIn`: a morphism `h : Y ⟶ P`
  such that `𝒪_Y` has no sections supported on `h⁻¹(T)` kills the pullback of the sections of
  `𝒪_P` supported on `T`.
* `AlgebraicGeometry.Space.exists_comp_eq_of_hasNoSectionsSupportedIn`: such a morphism factors
  through the closed subspace of `P` cut out by the sections supported on `T`.
* `AlgebraicGeometry.Space.exists_strictTransformSpace_map`: the morphism of strict transforms.
* `AlgebraicGeometry.Space.exists_strictTransformSpace_point_of_notMem`: a point of the strict
  transform of `X` lying off the centre lifts to the strict transform of `X₁` over any given
  point of `X₁` above its image in `X`.
* `AlgebraicGeometry.Space.exists_strictTransformSpace_point_of_isEtale`: the same for any point
  when `c` is étale.

## Implementation notes

The strict transform of `X` is cut out of `X ×_A A'` by the sections of the structure sheaf
supported on the exceptional preimage
(`AlgebraicGeometry.Space.definingIdealSheaf_strictTransform_of_isBlowupAlong`), so a morphism
into `X ×_A A'` factors through it as soon as it kills the pullback of those sections
(Stacks 03MB, `AlgebraicGeometry.Space.exists_comp_eq_iff_modulePullback_map_comp_eq_zero`).  The
pullback of a module with support in `T` has support in the inverse image of `T`, and a morphism
does not enlarge supports; on the strict transform of `X₁` the inverse image of the exceptional
divisor is an effective Cartier divisor
(`AlgebraicGeometry.Space.isPullbackDefined_strictTransform_of_isBlowupAlong`), so its structure
sheaf has no nonzero sections supported there.

For the lifting of points, the point of `X ×_A A'` and the point of `X₁` give a point of
`X₁ ×_A A'` since that space is the base change of `X ×_A A'` along `c`.  It lies on the strict
transform of `X₁` when it is off the exceptional preimage
(`AlgebraicGeometry.Space.preimage_openComplement_le_strictTransform_of_isBlowupAlong`), and,
when `c` is étale, because the strict transform of `X₁` is then the inverse image of the strict
transform of `X` (Stacks 0863, in the form
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_preimage_of_exists_definingIdealSheaf_eq`).

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism into whose source no section is supported over `T` kills the pullback of the
sections supported on `T`.** -/
theorem comp_eq_zero_of_hasNoSectionsSupportedIn {Y P : AlgebraicSpaces B S hS} (h : Y ⟶ P)
    (T : Set (points B S hS P.1))
    (hY : HasNoSectionsSupportedIn B S hS Y (pointsMap B S hS Y.1 h.hom ⁻¹' T)
      (SheafOfModules.unit (structureRingSheaf B S hS Y))) :
    (modulePullback B S hS h).map (supportedSectionsSubmodule B S hS P.1 P.2 T
        (SheafOfModules.unit (structureRingSheaf B S hS P))).ι ≫
      (modulePullbackUnitIso B S hS h).hom = 0 := by
  set M := supportedSectionsSubmodule B S hS P.1 P.2 T
    (SheafOfModules.unit (structureRingSheaf B S hS P))
  have hM : supportOfSheaf B S hS P.1 ((SheafOfModules.toSheaf _).obj M.toSheafOfModules) ⊆ T :=
    (supportOfSheaf_subset_iff_forall_sectionSupportedIn B S hS P _ T).2 fun W s =>
      sectionSupportedIn_of_map T M.ι (fun V a a' haa' => Subtype.ext haa') W s
        ((mem_supportedSectionsSubmodule_iff B S hS P.1 P.2 T _ W s.1).1 s.2)
  have hpull : supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj
      ((modulePullback B S hS h).obj M.toSheafOfModules)) ⊆
        pointsMap B S hS Y.1 h.hom ⁻¹' T :=
    (supportOfSheaf_modulePullback_subset_preimage B S hS h M.toSheafOfModules).trans
      (Set.preimage_mono hM)
  have hsupp := (supportOfSheaf_subset_iff_forall_sectionSupportedIn B S hS Y _ _).1 hpull
  ext W x
  exact hY W.unop _ (sectionSupportedIn_map _ ((modulePullback B S hS h).map M.ι ≫
    (modulePullbackUnitIso B S hS h).hom) W.unop x (hsupp W.unop x))

/-- **A morphism whose source has no sections supported over `T` factors through the closed
subspace cut out by the sections supported on `T`.** -/
theorem exists_comp_eq_of_hasNoSectionsSupportedIn {Y P : AlgebraicSpaces B S hS} (h : Y ⟶ P)
    (T : Set (points B S hS P.1)) (Z : ClosedSubspaces B S hS P.1)
    (hZ : definingIdealSheaf B S hS P Z = supportedSectionsSubmodule B S hS P.1 P.2 T
      (SheafOfModules.unit (structureRingSheaf B S hS P)))
    (hY : HasNoSectionsSupportedIn B S hS Y (pointsMap B S hS Y.1 h.hom ⁻¹' T)
      (SheafOfModules.unit (structureRingSheaf B S hS Y))) :
    ∃ g : Y ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
      g ≫ ObjectProperty.homMk Z.1.ι = h := by
  rw [exists_comp_eq_iff_modulePullback_map_comp_eq_zero B S hS P Z h, hZ]
  exact comp_eq_zero_of_hasNoSectionsSupportedIn h T hY

/-- The base change of `c` commutes with the projections to `A`, on underlying morphisms. -/
private theorem toSource_comp_hom_eq_map_comp {A A' X X₁ : AlgebraicSpaces B S hS}
    (f : X ⟶ A) (c : X₁ ⟶ X) (b : A' ⟶ A) :
    (strictTransformPullbackToSource B S hS (c ≫ f) b).hom ≫ (c ≫ f).hom =
      (strictTransformPullbackMap B S hS c f b).hom ≫
        (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom :=
  congrArg (fun k => k.hom) (by
    rw [← Category.assoc, ← strictTransformPullbackMap_toSource, Category.assoc] :
      strictTransformPullbackToSource B S hS (c ≫ f) b ≫ c ≫ f =
        strictTransformPullbackMap B S hS c f b ≫ strictTransformPullbackToSource B S hS f b ≫ f)

/-- **The morphism of strict transforms induced by a morphism over the base.** Let `b : A' ⟶ A`
be the blowup of `A` in a closed subspace `Zc`, let `f : X ⟶ A` be an algebraic space over `A`
and let `c : X₁ ⟶ X` be a morphism, so that `X₁` lies over `A` by `c ≫ f`.  Then there is a
morphism `p` from the strict transform of `X₁` to the strict transform of `X`, restricting the
base change `X₁ ×_A A' ⟶ X ×_A A'` of `c`; in particular it lies over `c` and over `A'`. -/
theorem exists_strictTransformSpace_map {A A' X X₁ : AlgebraicSpaces B S hS}
    (Zc : ClosedSubspaces B S hS A.1) {b : A' ⟶ A} (hb : IsBlowupAlong B S hS Zc b)
    (f : X ⟶ A) (c : X₁ ⟶ X) :
    ∃ p : strictTransformSpace B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 ⟶
        strictTransformSpace B S hS f b (preimageClosedSubspace b Zc).1,
      p ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Zc).1 =
        strictTransformSpaceι B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 ≫
          strictTransformPullbackMap B S hS c f b ∧
      p ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Zc).1 ≫
          strictTransformPullbackToSource B S hS f b =
        strictTransformSpaceι B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 ≫
          strictTransformPullbackToSource B S hS (c ≫ f) b ≫ c ∧
      p ≫ strictTransformSpaceToBlowUp B S hS f b (preimageClosedSubspace b Zc).1 =
        strictTransformSpaceToBlowUp B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 := by
  set f₁ := c ≫ f with hc
  set E := (preimageClosedSubspace b Zc).1 with hE
  set q := strictTransformPullbackMap B S hS c f b with hq
  have hqS := strictTransformPullbackMap_toSource B S hS c f b
  have hqB := strictTransformPullbackMap_toBlowUp B S hS c f b
  set h := strictTransformSpaceι B S hS f₁ b E ≫ q with hh
  set T := exceptionalPreimageSet B S hS f b E with hT
  have hTeq : T = pointsMap B S hS _ ((strictTransformPullbackToSource B S hS f b).hom ≫ f.hom) ⁻¹'
      subspacePointSet B S hS A.1 Zc.1 :=
    exceptionalPreimageSet_eq_preimage_centre B S hS f b Zc
  set D := preimageClosedSubspace (strictTransformSpaceι B S hS f₁ b E ≫
    strictTransformPullbackToSource B S hS f₁ b) (preimageClosedSubspace f₁ Zc) with hD
  have hDcart : IsEffectiveCartierDivisor B S hS
      (strictTransformSpace B S hS f₁ b E) D :=
    isPullbackDefined_strictTransform_of_isBlowupAlong B S hS f₁ b Zc hb
  have hno := hasNoSectionsSupportedIn_structureSheaf_of_isEffectiveCartierDivisor B S hS _ D
    hDcart
  have hset : pointsMap B S hS _ h.hom ⁻¹' T = subspacePointSet B S hS _ D.1 := by
    have hDpts : subspacePointSet B S hS _ D.1 = pointsMap B S hS _
        ((strictTransformSpaceι B S hS f₁ b E ≫ strictTransformPullbackToSource B S hS f₁ b).hom ≫
          f₁.hom) ⁻¹' subspacePointSet B S hS A.1 Zc.1 := by
      change Set.range (pointsMap B S hS _ ((Zc.1.preimage f₁.hom).preimage _).ι) = _
      rw [range_pointsMap_preimage_ι, range_pointsMap_preimage_ι, pointsMap_comp,
        Set.preimage_comp]
    have hmor : h.hom ≫ (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom =
        (strictTransformSpaceι B S hS f₁ b E ≫ strictTransformPullbackToSource B S hS f₁ b).hom ≫
          f₁.hom := by
      rw [hh]
      exact (Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (toSource_comp_hom_eq_map_comp f c b)).symm
    rw [hDpts, hTeq, ← Set.preimage_comp, ← pointsMap_comp, hmor]
  obtain ⟨g, hg⟩ := exists_comp_eq_of_hasNoSectionsSupportedIn h T
    (strictTransform B S hS f b E)
    (definingIdealSheaf_strictTransform_of_isBlowupAlong B S hS f b Zc hb) (hset ▸ hno)
  have hg' : g ≫ strictTransformSpaceι B S hS f b E = h := hg
  refine ⟨g, hg', ?_, ?_⟩
  · rw [← Category.assoc, hg', hh, Category.assoc, hqS]
  · change g ≫ strictTransformSpaceι B S hS f b E ≫ strictTransformPullbackToBlowUp B S hS f b = _
    rw [← Category.assoc, hg', hh, Category.assoc, hqB]

/-- The base change `X₁ ×_A A' ⟶ X ×_A A'` of `c : X₁ ⟶ X`, read as a cartesian square of
presheaves over `c`. -/
theorem isPullback_hom_strictTransformPullbackMap {A A' X X₁ : AlgebraicSpaces B S hS}
    (f : X ⟶ A) (c : X₁ ⟶ X) (b : A' ⟶ A) :
    IsPullback (strictTransformPullbackToSource B S hS (c ≫ f) b).hom
      (strictTransformPullbackMap B S hS c f b).hom c.hom
      (strictTransformPullbackToSource B S hS f b).hom :=
  AlgebraicSpaces.isPullback_hom B S hS (isPullback_strictTransformPullbackMap B S hS c f b)

/-- A point of `X₁ ×_A A'` on the strict transform of `X₁`, over a point of the strict transform
of `X`, comes from a point of the strict transform of `X₁` mapping to it. -/
theorem exists_strictTransformSpace_point_of_mem_range {A A' X X₁ : AlgebraicSpaces B S hS}
    {b : A' ⟶ A} (E : Subfunctor A'.1) (f : X ⟶ A) (c : X₁ ⟶ X)
    (p : strictTransformSpace B S hS (c ≫ f) b E ⟶ strictTransformSpace B S hS f b E)
    (hp : p ≫ strictTransformSpaceι B S hS f b E =
      strictTransformSpaceι B S hS (c ≫ f) b E ≫ strictTransformPullbackMap B S hS c f b)
    (a : points B S hS (strictTransformSpace B S hS f b E).1)
    (y : points B S hS (strictTransformPullback B S hS (c ≫ f) b).1)
    (hy : pointsMap B S hS _ (strictTransformPullbackMap B S hS c f b).hom y =
      pointsMap B S hS _ (strictTransformSpaceι B S hS f b E).hom a)
    (hmem : y ∈ Set.range (pointsMap B S hS _ (strictTransformSpaceι B S hS (c ≫ f) b E).hom)) :
    ∃ a₁ : points B S hS (strictTransformSpace B S hS (c ≫ f) b E).1,
      pointsMap B S hS _ p.hom a₁ = a ∧
        pointsMap B S hS _ (strictTransformSpaceι B S hS (c ≫ f) b E).hom a₁ = y := by
  obtain ⟨a₁, rfl⟩ := hmem
  refine ⟨a₁, pointsMap_injective_of_mono B S hS (strictTransform B S hS f b E).1.ι ?_, rfl⟩
  change pointsMap B S hS _ (strictTransformSpaceι B S hS f b E).hom (pointsMap B S hS _ p.hom a₁) =
    pointsMap B S hS _ (strictTransformSpaceι B S hS f b E).hom a
  rw [← hy, ← pointsMap_comp_apply, ← pointsMap_comp_apply]
  exact congrArg (fun k => pointsMap B S hS _ k.hom a₁) hp

/-- A point `a` of the strict transform of `X` and a point `x₁` of `X₁` above its image lift to a
point of the strict transform of `X₁` as soon as every point `y` of `X₁ ×_A A'` over them lies on
the strict transform of `X₁`. -/
private theorem exists_strictTransformSpace_point_of_forall_mem_range
    {A A' X X₁ : AlgebraicSpaces B S hS} {b : A' ⟶ A} (E : Subfunctor A'.1) (f : X ⟶ A)
    (c : X₁ ⟶ X) (p : strictTransformSpace B S hS (c ≫ f) b E ⟶ strictTransformSpace B S hS f b E)
    (hp : p ≫ strictTransformSpaceι B S hS f b E =
      strictTransformSpaceι B S hS (c ≫ f) b E ≫ strictTransformPullbackMap B S hS c f b)
    (a : points B S hS (strictTransformSpace B S hS f b E).1) (x₁ : points B S hS X₁.1)
    (hx : pointsMap B S hS _ c.hom x₁ = pointsMap B S hS _
      (strictTransformSpaceι B S hS f b E ≫ strictTransformPullbackToSource B S hS f b).hom a)
    (hmem : ∀ y : points B S hS (strictTransformPullback B S hS (c ≫ f) b).1,
      pointsMap B S hS _ (strictTransformPullbackToSource B S hS (c ≫ f) b).hom y = x₁ →
      pointsMap B S hS _ (strictTransformPullbackMap B S hS c f b).hom y =
        pointsMap B S hS _ (strictTransformSpaceι B S hS f b E).hom a →
      y ∈ Set.range (pointsMap B S hS _ (strictTransformSpaceι B S hS (c ≫ f) b E).hom)) :
    ∃ a₁ : points B S hS (strictTransformSpace B S hS (c ≫ f) b E).1,
      pointsMap B S hS _ p.hom a₁ = a ∧
        pointsMap B S hS _ (strictTransformSpaceι B S hS (c ≫ f) b E ≫
          strictTransformPullbackToSource B S hS (c ≫ f) b).hom a₁ = x₁ := by
  obtain ⟨y, hy₁, hy₂⟩ := exists_points_of_isPullback B S hS
    (isPullback_hom_strictTransformPullbackMap f c b) x₁
    (pointsMap B S hS _ (strictTransformSpaceι B S hS f b E).hom a)
    (by rw [hx, ← pointsMap_comp_apply]; rfl)
  obtain ⟨a₁, ha₁, hya₁⟩ := exists_strictTransformSpace_point_of_mem_range E f c p hp a y hy₂
    (hmem y hy₁ hy₂)
  refine ⟨a₁, ha₁, ?_⟩
  change pointsMap B S hS _
    ((strictTransformSpaceι B S hS (c ≫ f) b E).hom ≫
    (strictTransformPullbackToSource B S hS (c ≫ f) b).hom) a₁ = x₁
  rw [pointsMap_comp_apply, hya₁, hy₁]

/-- **A point of the strict transform lying off the centre lifts along `c`.**  Let `b : A' ⟶ A`
be the blowup of `A` in `Zc`, let `f : X ⟶ A` and `c : X₁ ⟶ X`, and let `p` be the morphism of
strict transforms restricting the base change of `c`.  A point `a` of the strict transform of
`X` whose image in `A` is not in `|Zc|` is the image under `p` of a point of the strict
transform of `X₁` over any given point `x₁` of `X₁` above the image of `a` in `X`. -/
theorem exists_strictTransformSpace_point_of_notMem {A A' X X₁ : AlgebraicSpaces B S hS}
    (Zc : ClosedSubspaces B S hS A.1) {b : A' ⟶ A} (hb : IsBlowupAlong B S hS Zc b)
    (f : X ⟶ A) (c : X₁ ⟶ X)
    (p : strictTransformSpace B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 ⟶
      strictTransformSpace B S hS f b (preimageClosedSubspace b Zc).1)
    (hp : p ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Zc).1 =
      strictTransformSpaceι B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 ≫
        strictTransformPullbackMap B S hS c f b)
    (a : points B S hS (strictTransformSpace B S hS f b (preimageClosedSubspace b Zc).1).1)
    (x₁ : points B S hS X₁.1)
    (hx : pointsMap B S hS _ c.hom x₁ = pointsMap B S hS _
      (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Zc).1 ≫
        strictTransformPullbackToSource B S hS f b).hom a)
    (hZ : pointsMap B S hS _ f.hom (pointsMap B S hS _ c.hom x₁) ∉
      subspacePointSet B S hS A.1 Zc.1) :
    ∃ a₁ : points B S hS
        (strictTransformSpace B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1).1,
      pointsMap B S hS _ p.hom a₁ = a ∧
        pointsMap B S hS _ (strictTransformSpaceι B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 ≫
          strictTransformPullbackToSource B S hS (c ≫ f) b).hom a₁ = x₁ := by
  refine exists_strictTransformSpace_point_of_forall_mem_range _ f c p hp a x₁ hx
    fun y hy₁ hy₂ => ?_
  set C := openComplementOfClosedSubspace B S hS A Zc with hC
  have hle := preimage_openComplement_le_strictTransform_of_isBlowupAlong B S hS (c ≫ f) b Zc hb
  have hyC : y ∈ Set.range (pointsMap B S hS _
      ((C.1.preimage (c ≫ f).hom).preimage
        (strictTransformPullbackToSource B S hS (c ≫ f) b).hom).ι) := by
    rw [range_pointsMap_preimage_ι, Set.mem_preimage, range_pointsMap_preimage_ι,
      Set.mem_preimage, hy₁]
    change pointsMap B S hS _ (c.hom ≫ f.hom) x₁ ∈ subspacePointSet B S hS A.1 C.1
    rw [subspacePointSet_openComplement, pointsMap_comp_apply]
    exact hZ
  obtain ⟨z, rfl⟩ := hyC
  refine ⟨pointsMap B S hS _ (Subfunctor.homOfLe hle) z, ?_⟩
  rw [← pointsMap_comp_apply]
  exact congrArg (fun k => pointsMap B S hS _ k z) (Subfunctor.homOfLe_ι hle)

/-- **Every point of the strict transform lifts along an étale `c`.**  Let `b : A' ⟶ A` be the
blowup of `A` in `Zc`, let `f : X ⟶ A` and let `c : X₁ ⟶ X` be étale, and let `p` be the
morphism of strict transforms restricting the base change of `c`.  A point `a` of the strict
transform of `X` is the image under `p` of a point of the strict transform of `X₁` over any
given point `x₁` of `X₁` above the image of `a` in `X`: the strict transform of `X₁` is the
inverse image of the strict transform of `X` (Stacks 0863). -/
theorem exists_strictTransformSpace_point_of_isEtale {A A' X X₁ : AlgebraicSpaces B S hS}
    (Zc : ClosedSubspaces B S hS A.1) {b : A' ⟶ A} (hb : IsBlowupAlong B S hS Zc b)
    (f : X ⟶ A) (c : X₁ ⟶ X) (hc : IsEtale B S hS c.hom)
    (p : strictTransformSpace B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 ⟶
      strictTransformSpace B S hS f b (preimageClosedSubspace b Zc).1)
    (hp : p ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Zc).1 =
      strictTransformSpaceι B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 ≫
        strictTransformPullbackMap B S hS c f b)
    (a : points B S hS (strictTransformSpace B S hS f b (preimageClosedSubspace b Zc).1).1)
    (x₁ : points B S hS X₁.1)
    (hx : pointsMap B S hS _ c.hom x₁ = pointsMap B S hS _
      (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Zc).1 ≫
        strictTransformPullbackToSource B S hS f b).hom a) :
    ∃ a₁ : points B S hS
        (strictTransformSpace B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1).1,
      pointsMap B S hS _ p.hom a₁ = a ∧
        pointsMap B S hS _ (strictTransformSpaceι B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 ≫
          strictTransformPullbackToSource B S hS (c ≫ f) b).hom a₁ = x₁ := by
  have sq := isPullback_hom_strictTransformPullbackMap f c b
  refine exists_strictTransformSpace_point_of_forall_mem_range _ f c p hp a x₁ hx
    fun y hy₁ hy₂ => ?_
  have hcan : IsEtale B S hS (strictTransformPullbackMap B S hS c f b).hom :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS sq.flip
      (strictTransformPullback B S hS (c ≫ f) b).2 (strictTransformPullback B S hS f b).2 X₁.2
      X.2 hc
  have hT : exceptionalPreimageSet B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1 =
      pointsMap B S hS _ (strictTransformPullbackMap B S hS c f b).hom ⁻¹'
        exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Zc).1 := by
    change exceptionalPreimageSet B S hS (c ≫ f) b (Zc.1.preimage b.hom) =
      pointsMap B S hS _ (strictTransformPullbackMap B S hS c f b).hom ⁻¹'
        exceptionalPreimageSet B S hS f b (Zc.1.preimage b.hom)
    rw [exceptionalPreimageSet_eq_preimage_centre B S hS (c ≫ f) b Zc,
      exceptionalPreimageSet_eq_preimage_centre B S hS f b Zc, ← Set.preimage_comp,
      ← pointsMap_comp, toSource_comp_hom_eq_map_comp]
  have h0863 := strictTransformSubfunctor_eq_preimage_of_exists_definingIdealSheaf_eq B S hS
    f b (preimageClosedSubspace b Zc).1 (c ≫ f) b (preimageClosedSubspace b Zc).1
    (strictTransformPullbackMap B S hS c f b) hcan hT
    ⟨strictTransform B S hS f b (preimageClosedSubspace b Zc).1,
      definingIdealSheaf_strictTransform_of_isBlowupAlong B S hS f b Zc hb⟩
  change y ∈ Set.range (pointsMap B S hS _
    (strictTransformSubfunctor B S hS (c ≫ f) b (preimageClosedSubspace b Zc).1).ι)
  rw [h0863, range_pointsMap_preimage_ι, Set.mem_preimage, hy₂]
  exact Set.mem_range_self _

end AlgebraicGeometry.Space
