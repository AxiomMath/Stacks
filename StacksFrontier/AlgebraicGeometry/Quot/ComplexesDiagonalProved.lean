module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesDiagonalCorrected
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualProved
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplementQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsPoints

/-!
# Stacks 0DPW, corrected: the diagonal of `Complexes_{X/B}` over `B`

Stacks 0DPW says: *the diagonal of `Complexes_{X/B}` over `B` is affine and of finite
presentation.*  **The "affine" part is false as stated.**  The source's proof reduces to showing
that for a scheme `T` over `B` and objects `(T, E)`, `(T, E')` of `Complexes_{X/B}` over `T`, the
functor `Isom(E, E') ⟶ T` is affine and of finite presentation, and then applies Stacks 0DLC,
part (3), as if the open `W(E, E')` of that lemma were all of `T`.  It is not in general: for
`f : X = P¹_B ⟶ B = A²_k`, `s = a(x² - y²) + bxy`, `E = [O(-2) --s--> O]` and `E' = E ⊗ O(2)` in
degrees `-1, 0`, both complexes are `B`-perfect with vanishing negative self-Exts at every point,
`Isom(E, E')` has no points over the origin, and over `U = A² ∖ 0` it is affine over `U` with a
section, so `Isom(E, E') ⟶ A²` affine would make `U` affine.

The **corrected statement**
(`ComplexesSituation.complexesIsom_finitePresentation_and_affine_overQuasiCompactNegativeExtLocus`):
the diagonal of `Complexes_{X/B}` over `B` is representable by algebraic spaces and of finite
presentation, and for objects `(T, E)`, `(T, E')` over the same `T`, `Isom(E, E')` factors
through the open `W(E, E') ∩ W(E', E)` of `T` of Stacks 0DLC, whose inclusion into `T` is
quasi-compact, and is affine and of finite presentation over it: the diagonal is quasi-affine
and of finite presentation.

## Main results

* `AlgebraicGeometry.Space.exists_lift_of_forall_isFieldObject_testPoint_mem`: a test scheme
  over `Y` all of whose points with values in a field lie in an open subspace `W` factors
  through `W` (Stacks 03IE, read on test schemes).
* `AlgebraicGeometry.Space.openSubspaceImmersion_corrected_of_negativeExtLocus`: a locus of
  Stacks 0DLC, part (1), with quasi-compact inclusion, over which the Hom functor is affine and of
  finite presentation, is a quasi-compact open through which the test schemes with vanishing
  negative fibre extensions factor.
* `AlgebraicGeometry.Space.relativeDerivedHom_eq_relativeDerivedHomFunctor`: the relative derived
  Hom functor of the 0DLC statements is the one of the fibre product presentation of `Isom`.
* `ComplexesSituation.complexesIsom_factors_isAffineFinitePresentation_inf`:
  `Isom(E, E')` factors through `W(E, E') ∩ W(E', E)` and is affine and of finite presentation
  over it, whose inclusion into `T` is quasi-compact.
* `ComplexesSituation.complexesIsom_finitePresentation_and_affine_overNegativeExtLocus`: the
  diagonal of `Complexes_{X/B}` over `B` is representable by algebraic spaces and of finite
  presentation, and `Isom(E, E')` is affine and of finite presentation over
  `W(E, E') ∩ W(E', E)`.
* `ComplexesSituation.complexesIsom_finitePresentation_and_affine_overQuasiCompactNegativeExtLocus`:
  the same, with the quasi-compactness of `W(E, E') ∩ W(E', E) ⟶ T`; the corrected Stacks 0DPW.

## References

* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Factoring a test scheme through an open subspace at its field points -/

section FieldPoints

variable {Y : AlgebraicSpaces B S hS}

/-- The test scheme over `Y` of a point of a test scheme `T` with values in a field: the
composite `Spec(k) ⟶ T ⟶ Y`. -/
abbrev fieldPointTest (T : SchemesOver Y) (p : FieldValuedPoint B S hS (yoneda.obj T.left)) :
    SchemesOver Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map p.value ≫ T.hom)

/-- The morphism of test schemes `Spec(k) ⟶ T` over `Y` of a field-valued point of `T`. -/
def fieldPointTestHom (T : SchemesOver Y) (p : FieldValuedPoint B S hS (yoneda.obj T.left)) :
    fieldPointTest T p ⟶ T :=
  CostructuredArrow.homMk p.value rfl

/-- **A test scheme lies over an open subspace when its field points do (Stacks 03IE).**  Let
`W` be an open subspace of an algebraic space `Y` and `T` a test scheme over `Y`.  If every test
scheme `T₀ ⟶ T` over `Y` whose underlying scheme is the spectrum of a field lies in `W`, then the
structure morphism `T ⟶ Y` factors through `W`. -/
theorem exists_lift_of_forall_isFieldObject_testPoint_mem (W : OpenSubspaces B S hS Y.1)
    (T : SchemesOver Y)
    (h : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → (T₀ ⟶ T) →
      testPoint T₀ ∈ W.1.obj (op T₀.left)) :
    ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ openSubspaceAsSpace B S hS W,
      t ≫ openSubspaceImmersion B S hS W = T.hom := by
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS Y.2
    (isAlgebraicSpace_yoneda B S hS T.left) W.1 W.2 T.hom.hom).2 (by
      rintro z ⟨y, rfl⟩
      induction y using Quot.ind with
      | mk p =>
        have hmem := h (fieldPointTest T p) (Stack.isFieldObject_siteObject B S hS _ p)
          (fieldPointTestHom T p)
        refine ⟨FieldValuedPoint.class B S hS W.1.toFunctor
          { carrier := p.carrier, contained := p.contained, toBase := p.toBase,
            value := ⟨testPoint (fieldPointTest T p), hmem⟩ }, ?_⟩
        have hv : testPoint (fieldPointTest T p) = T.hom.hom.app (op p.siteObject) p.value := by
          simp only [testPoint, fieldPointTest, CostructuredArrow.mk_hom_eq_self,
            ObjectProperty.FullSubcategory.comp_hom, schemeSpaceFunctor_map_hom]
          rfl
        exact congrArg (fun v => FieldValuedPoint.class B S hS Y.1
          { carrier := p.carrier, contained := p.contained, toBase := p.toBase, value := v }) hv)
  exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

end FieldPoints

section NegativeExtLocus

variable {X Y : AlgebraicSpaces B S hS}

/-- **A locus of Stacks 0DLC is a quasi-compact open through which test schemes factor.**  Let
`f : X ⟶ Y` and `K, L ∈ D(𝒪_X)`, and let `W` be an open subspace of `Y` characterized as in
Stacks 0DLC, part (1): a point `y` of `Y` with values in a field lies in `W` exactly when
`Ext^i(K_y, L_y) = 0` for `i < 0`.  Suppose that `V ↦ Hom(K_V, L_V)` is an algebraic space
affine and of finite presentation over `W` (Stacks 0DLC, part (3)) and that `W ⟶ Y` is
quasi-compact.  Then the inclusion `W ⟶ Y` is a quasi-compact open immersion through which every
test scheme with vanishing negative fibre extensions from `K` to `L` factors, over which the
relative derived Hom functor is affine and of finite presentation. -/
theorem openSubspaceImmersion_corrected_of_negativeExtLocus (f : X ⟶ Y)
    (K L : derivedModules B S hS X) (W : OpenSubspaces B S hS Y.1)
    (hloc : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left →
      (testPoint T₀ ∈ W.1.obj (op T₀.left) ↔
        ∀ i : ℤ, i < 0 →
          Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull
              (baseChangeProjection f T₀)).obj K ⟶
            (((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T₀)).obj L)⟦i⟧)))
    (hrep : IsAffineFinitePresentationAlgebraicSpaceOver (openSubspaceAsSpace B S hS W)
      ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS)
        (openSubspaceImmersion B S hS W)).op ⋙ relativeDerivedHom f K L))
    (hqc : IsQuasiCompact B S hS (openSubspaceImmersion B S hS W).hom) :
    IsOpenImmersion B S hS (openSubspaceImmersion B S hS W).hom ∧
      IsQuasiCompact B S hS (openSubspaceImmersion B S hS W).hom ∧
      (∀ T : SchemesOver Y, HasNoNegativeFibreExtOver f K L T →
        ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ openSubspaceAsSpace B S hS W,
          t ≫ openSubspaceImmersion B S hS W = T.hom) ∧
      IsAffineFinitePresentationAlgebraicSpaceOver (openSubspaceAsSpace B S hS W)
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS)
          (openSubspaceImmersion B S hS W)).op ⋙ relativeDerivedHomFunctor f K L) :=
  ⟨W.2.2, hqc, fun T hT => exists_lift_of_forall_isFieldObject_testPoint_mem W T
      (fun T₀ hT₀ g => (hloc T₀ hT₀).2 (hT T₀ hT₀ g)), hrep⟩

end NegativeExtLocus

/-- **The two relative derived Hom functors agree.**  The functor `T ↦ Hom(K_T, E_T)` on the test
schemes over `Y` of the statements of Stacks 0DLC, `AlgebraicGeometry.Space.relativeDerivedHom`
(the restriction of the functor on all algebraic spaces over `Y`), is the functor
`AlgebraicGeometry.Space.relativeDerivedHomFunctor` of the fibre product presentation of the
relative derived Isom functor: both send `T` to the morphisms between the derived pullbacks along
`X ×_Y T ⟶ X`, and a morphism of test schemes to derived pullback. -/
theorem relativeDerivedHom_eq_relativeDerivedHomFunctor {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (K E : derivedModules B S hS X) :
    relativeDerivedHom f K E = relativeDerivedHomFunctor f K E :=
  rfl

namespace ComplexesSituation

attribute [local instance] complexesCategory

variable {D : ComplexesSituation B S hS} (A : ComplexesObject D)
  (E' : derivedModules B S hS (D.space A.T)) (h₁ : D.IsRelativelyPerfect A.T E')
  (h₂ : D.HasNoNegativeFibreExt A.T E')

include h₁ h₂ in
/-- **`Isom(E, E')` over `W(E, E') ∩ W(E', E)`.**  Let `(T, E)`, `(T, E')` be objects of
`Complexes_{X/B}` over the same test scheme, and let `W₁`, `W₂` be the opens of `T` of Stacks 0DLC,
part (1), for `(E, E')` and `(E', E)`: a field point `y` of `T` lies in `W₁` exactly when
`Ext^i(E_y, E'_y) = 0` for `i < 0`, and in `W₂` exactly when `Ext^i(E'_y, E_y) = 0` for `i < 0`.
Then the inclusion of `W₁ ∩ W₂` into `T` is quasi-compact, `Isom(E, E')` factors through it, and
`Isom(E, E')` is affine and of finite presentation over it. -/
theorem complexesIsom_factors_isAffineFinitePresentation_inf
    (W₁ W₂ : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1)
    (hW₁ : IsNegativeExtLocus (D.projection A.T) A.E E' W₁)
    (hW₂ : IsNegativeExtLocus (D.projection A.T) E' A.E W₂) :
    IsQuasiCompact B S hS (openSubspaceImmersion B S hS ⟨W₁.1 ⊓ W₂.1,
      isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1 W₁.2
        W₂.2⟩).hom ∧
    (∀ T' : SchemesOver ((schemeSpaceFunctor B S hS).obj A.T.left),
      Nonempty ((relativeDerivedIsomFunctor (D.projection A.T) A.E E').obj (op T')) →
        ∃ t : (schemeSpaceFunctor B S hS).obj T'.left ⟶
            openSubspaceAsSpace B S hS ⟨W₁.1 ⊓ W₂.1,
              isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
                W₁.2 W₂.2⟩,
          t ≫ openSubspaceImmersion B S hS ⟨W₁.1 ⊓ W₂.1,
            isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
              W₁.2 W₂.2⟩ = T'.hom) ∧
    IsAffineFinitePresentationAlgebraicSpaceOver
      (openSubspaceAsSpace B S hS ⟨W₁.1 ⊓ W₂.1,
        isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1 W₁.2
          W₂.2⟩)
      ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS)
        (openSubspaceImmersion B S hS ⟨W₁.1 ⊓ W₂.1,
          isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1 W₁.2
            W₂.2⟩)).op ⋙
        relativeDerivedIsomFunctor (D.projection A.T) A.E E') := by
  let Y := (schemeSpaceFunctor B S hS).obj A.T.left
  let f := D.projection A.T
  have hp := isProper_projection D.toCoherentSituation D.proper A.T
  have hflat := D.projection_isFlat A.T
  have hfp := D.toCoherentSituation.isFinitePresentation_projection A.T
  have hE := A.relativelyPerfect
  let W : OpenSubspaces B S hS Y.1 :=
    ⟨W₁.1 ⊓ W₂.1, isOpenSubspace_inf B S hS Y.2 W₁.1 W₂.1 W₁.2 W₂.2⟩
  have hloc := fun (M N : derivedModules B S hS (D.space A.T)) (hM : D.IsRelativelyPerfect A.T M)
      (hN : D.IsRelativelyPerfect A.T N) (W' : OpenSubspaces B S hS Y.1)
      (hW' : IsNegativeExtLocus f M N W') =>
    have hqc := isQuasiCompact_openSubspaceImmersion_of_isNegativeExtLocus f hp hflat hfp M N
      hM.1 hN W' hW'
    And.intro hqc (openSubspaceImmersion_corrected_of_negativeExtLocus f M N W' hW'
      (relativeDerivedHomRepresentableOverLocus_proved B S hS f hp hflat hfp M N hM.1 hN W' hW')
      hqc).2.2.2
  have hself := fun (M : derivedModules B S hS (D.space A.T)) (hM : D.IsRelativelyPerfect A.T M)
      (hM' : D.HasNoNegativeFibreExt A.T M) =>
    relativeDerivedHomRepresentableOfFibres_proved B S hS f hp hflat hfp M M hM.1 hM
      fun T₀ hT₀ => hasNoNegativeFibreExtOver_of_hasNoNegativeFibreExt A.T M hM' T₀ T₀ hT₀ (𝟙 T₀)
  obtain ⟨hqc₁, hEE'⟩ := hloc A.E E' hE h₁ W₁ hW₁
  obtain ⟨hqc₂, hE'E⟩ := hloc E' A.E h₁ hE W₂ hW₂
  have hEE := hself A.E hE A.noNegativeFibreExt
  have hE'E' := hself E' h₁ h₂
  let j₁ : openSubspaceAsSpace B S hS W ⟶ openSubspaceAsSpace B S hS W₁ :=
    ObjectProperty.homMk (Subfunctor.homOfLe inf_le_left)
  let j₂ : openSubspaceAsSpace B S hS W ⟶ openSubspaceAsSpace B S hS W₂ :=
    ObjectProperty.homMk (Subfunctor.homOfLe inf_le_right)
  have hj₁ : j₁ ≫ openSubspaceImmersion B S hS W₁ = openSubspaceImmersion B S hS W :=
    ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι (inf_le_left : W₁.1 ⊓ W₂.1 ≤ W₁.1))
  have hj₂ : j₂ ≫ openSubspaceImmersion B S hS W₂ = openSubspaceImmersion B S hS W :=
    ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι (inf_le_right : W₁.1 ⊓ W₂.1 ≤ W₂.1))
  refine ⟨?_, ?_, ?_⟩
  · refine isQuasiCompact_ι_of_forall_isCompact_preimage B S hS Y W.2 fun T hT a => ?_
    let R₁ := Set.range (pointsMap B S hS W₁.1.toFunctor W₁.1.ι)
    let R₂ := Set.range (pointsMap B S hS W₂.1.toFunctor W₂.1.ι)
    have hW : W.1 = openSubspaceOfPoints B S hS Y.1 (R₁ ∩ R₂) := by
      ext T x
      have e₁ := Iff.of_eq (congrArg (fun G : Subfunctor Y.1 => x ∈ G.obj T)
        (eq_openSubspaceOfPoints_range_pointsMap B S hS Y.2 W₁.1 W₁.2))
      have e₂ := Iff.of_eq (congrArg (fun G : Subfunctor Y.1 => x ∈ G.obj T)
        (eq_openSubspaceOfPoints_range_pointsMap B S hS Y.2 W₂.1 W₂.2))
      change x ∈ W₁.1.obj T ∧ x ∈ W₂.1.obj T ↔ _
      rw [e₁, e₂, mem_openSubspaceOfPoints_iff, mem_openSubspaceOfPoints_iff,
        mem_openSubspaceOfPoints_iff, Set.subset_inter_iff]
    have hrange : Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) = R₁ ∩ R₂ := by
      rw [hW, range_pointsMap_ι_openSubspaceOfPoints]
    rw [hrange, Set.preimage_inter]
    have := hT
    have : QuasiSeparatedSpace (points B S hS (yoneda.obj T)) :=
      (quasiSeparatedSpace_congr (schemePointsHomeomorph B S hS T)).2 inferInstance
    have hTqc := isQuasiCompactSpace_yoneda_of_isAffine B S hS T hT
    exact (isCompact_preimage_range_of_isQuasiCompact B S hS Y.2 (isAlgebraicSpace_yoneda B S hS T)
        hTqc a W₁.1 W₁.2 hqc₁).inter_of_isOpen
      (isCompact_preimage_range_of_isQuasiCompact B S hS Y.2 (isAlgebraicSpace_yoneda B S hS T)
        hTqc a W₂.1 W₂.2 hqc₂)
      ((isOpen_range_pointsMap_openSubspace W₁).preimage (continuous_pointsMap B S hS a))
      ((isOpen_range_pointsMap_openSubspace W₂).preimage (continuous_pointsMap B S hS a))
  · rintro T' ⟨α⟩
    obtain ⟨hMN, hNM⟩ := hasNoNegativeFibreExtOver_of_relativeDerivedIsomFunctor f
      (hasNoNegativeFibreExtOver_of_hasNoNegativeFibreExt A.T A.E A.noNegativeFibreExt T') α
    exact exists_lift_of_forall_isFieldObject_testPoint_mem W T' fun T₀ hT₀ g =>
      ⟨(hW₁ T₀ hT₀).2 (hMN T₀ hT₀ g), (hW₂ T₀ hT₀).2 (hNM T₀ hT₀ g)⟩
  · exact isAffineFinitePresentationAlgebraicSpaceOver_restrict_relativeDerivedIsomFunctor f
      (openSubspaceImmersion B S hS W) A.E E' (hEE'.restrict_comp j₁ hj₁)
      (hE'E.restrict_comp j₂ hj₂) (hEE.baseChange _) (hE'E'.baseChange _)

/-- Let `f : X ⟶ B` be proper, flat and of finite presentation
(Situation 0DLE), and let `x = (T, E)`, `y = (T, E')` be objects of `Complexes_{X/B}` over the
same scheme `T` and the same morphism `T ⟶ B`, so that `E`, `E'` are `B`-perfect objects of
`D(𝒪_{X_T})` with vanishing negative self-Exts on the fibres; the base change of the diagonal of
`Complexes_{X/B}` over `B` along the `T`-point `(x, y)` of `Complexes_{X/B} ×_B Complexes_{X/B}`
is `Isom(x, y)`.  Then:

1. the presheaf `Isom(x, y)` on `(Sch/T)` is the relative derived Isom functor
   `T' ↦ Isom(E_{T'}, E'_{T'})` of `X_T ⟶ T`;
2. it is an algebraic space of finite presentation over `T`: **the diagonal of `Complexes_{X/B}`
   over `B` is representable by algebraic spaces and of finite presentation**;
3. the opens `W(E, E')` and `W(E', E)` of `T` of Stacks 0DLC, part (1), exist;
4. for these opens (`W(E, E')`: the field points `y` of `T` with `Ext^i(E_y, E'_y) = 0` for
   `i < 0`, and symmetrically), `Isom(x, y)` factors through `W(E, E') ∩ W(E', E)` and is affine
   and of finite presentation over it.

The registered corrected form of Stacks 0DPW, which adds that the inclusion of
`W(E, E') ∩ W(E', E)` into `T` is quasi-compact, is
`complexesIsom_finitePresentation_and_affine_overQuasiCompactNegativeExtLocus`. -/
theorem complexesIsom_finitePresentation_and_affine_overNegativeExtLocus :
    Nonempty ((complexesFunctor D).isomPresheaf ⟨A, rfl⟩ ⟨sameTest A E' h₁ h₂, rfl⟩ ≅
      (overSchemeTest A.T.left).op ⋙ relativeDerivedIsomFunctor (D.projection A.T) A.E E') ∧
    IsFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj A.T.left)
      (relativeDerivedIsomFunctor (D.projection A.T) A.E E') ∧
    (∃ W₁ : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1,
      IsNegativeExtLocus (D.projection A.T) A.E E' W₁) ∧
    (∃ W₂ : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1,
      IsNegativeExtLocus (D.projection A.T) E' A.E W₂) ∧
    ∀ (W₁ W₂ : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1),
      IsNegativeExtLocus (D.projection A.T) A.E E' W₁ →
      IsNegativeExtLocus (D.projection A.T) E' A.E W₂ →
      (∀ T' : SchemesOver ((schemeSpaceFunctor B S hS).obj A.T.left),
        Nonempty ((relativeDerivedIsomFunctor (D.projection A.T) A.E E').obj (op T')) →
          ∃ t : (schemeSpaceFunctor B S hS).obj T'.left ⟶
              openSubspaceAsSpace B S hS ⟨W₁.1 ⊓ W₂.1,
                isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
                  W₁.2 W₂.2⟩,
            t ≫ openSubspaceImmersion B S hS ⟨W₁.1 ⊓ W₂.1,
              isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
                W₁.2 W₂.2⟩ = T'.hom) ∧
      IsAffineFinitePresentationAlgebraicSpaceOver
        (openSubspaceAsSpace B S hS ⟨W₁.1 ⊓ W₂.1,
          isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1 W₁.2
            W₂.2⟩)
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS)
          (openSubspaceImmersion B S hS ⟨W₁.1 ⊓ W₂.1,
            isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
              W₁.2 W₂.2⟩)).op ⋙
          relativeDerivedIsomFunctor (D.projection A.T) A.E E') := by
  have hp := isProper_projection D.toCoherentSituation D.proper A.T
  have hflat := D.projection_isFlat A.T
  have hfp := D.toCoherentSituation.isFinitePresentation_projection A.T
  have hE := A.relativelyPerfect
  obtain ⟨W₁, hW₁⟩ := existsNegativeExtLocus_proved B S hS (D.projection A.T) hp hflat hfp A.E E'
    hE.1 h₁
  obtain ⟨W₂, hW₂⟩ := existsNegativeExtLocus_proved B S hS (D.projection A.T) hp hflat hfp E' A.E
    h₁.1 hE
  obtain ⟨hqc, hfactor, hIsom⟩ :=
    complexesIsom_factors_isAffineFinitePresentation_inf A E' h₁ h₂ W₁ W₂ hW₁ hW₂
  have hopen := (isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
    W₁.2 W₂.2).2
  refine ⟨⟨complexesIsomPresheafIsoRelativeDerivedIsomFunctor A E' h₁ h₂⟩, ?_, ⟨W₁, hW₁⟩,
    ⟨W₂, hW₂⟩, fun W₁ W₂ hW₁ hW₂ =>
      (complexesIsom_factors_isAffineFinitePresentation_inf A E' h₁ h₂ W₁ W₂ hW₁ hW₂).2⟩
  exact IsFinitePresentationAlgebraicSpaceOver.of_restrict
    (mono_of_isOpenImmersion B S hS _ hopen) (isFinitePresentation_of_isOpenImmersion hopen hqc)
    hfactor hIsom

/-- **Stacks 0DPW, corrected: the diagonal of `Complexes_{X/B}` over `B` is quasi-affine and of
finite presentation.**  Let `f : X ⟶ B` be proper, flat and of finite presentation
(Situation 0DLE), and let `x = (T, E)`, `y = (T, E')` be objects of `Complexes_{X/B}` over the
same scheme `T` and the same morphism `T ⟶ B`, so that `E`, `E'` are `B`-perfect objects of
`D(𝒪_{X_T})` with vanishing negative self-Exts on the fibres; the base change of the diagonal of
`Complexes_{X/B}` over `B` along the `T`-point `(x, y)` of `Complexes_{X/B} ×_B Complexes_{X/B}`
is `Isom(x, y)`.  Then:

1. the presheaf `Isom(x, y)` on `(Sch/T)` is the relative derived Isom functor
   `T' ↦ Isom(E_{T'}, E'_{T'})` of `X_T ⟶ T`;
2. it is an algebraic space of finite presentation over `T`: the diagonal of `Complexes_{X/B}`
   over `B` is representable by algebraic spaces and of finite presentation;
3. the opens `W(E, E')` and `W(E', E)` of `T` of Stacks 0DLC, part (1), exist;
4. for these opens (`W(E, E')`: the field points `y` of `T` with `Ext^i(E_y, E'_y) = 0` for
   `i < 0`, and symmetrically), the inclusion of `W(E, E') ∩ W(E', E)` into `T` is
   quasi-compact, and `Isom(x, y)` factors through this open and is affine and of finite
   presentation over it.

**This is the corrected form of Stacks 0DPW**, not the statement as written.  The source asserts
that the diagonal is affine and of finite presentation; the "affine" part is false (its proof
applies Stacks 0DLC, part (3), as if `W(E, E')` were all of `T`): for `X = P¹` over `A²_k`,
`E = [O(-2) --s--> O]` with `s = a(x² - y²) + bxy` and `E' = E ⊗ O(2)`, `Isom(E, E')` is empty
over the origin and has a section over `A² ∖ 0`, so it is not affine over `A²`. -/
@[stacks 0DPW "Corrected statement (Stacks erratum): the source \
asserts that the diagonal of Complexes_{X/B} over B is affine and of finite presentation; the \
'affine' part is false (counterexample: X = P^1 over A^2_k with complexes E = [O(-2) -s-> O], \
s = a(x^2 - y^2) + bxy, and E' = E ⊗ O(2), for which Isom(E, E') is empty over the origin and \
has a section over A^2 minus the origin, so is not affine over A^2). Formalized: the diagonal \
over B is representable by algebraic spaces and of finite presentation, and for (T, E), \
(T, E') the functor Isom(E, E') factors through the open W(E, E') ∩ W(E', E) of 0DLC, whose \
inclusion into T is quasi-compact, and is affine and of finite presentation over it; so the \
diagonal is quasi-affine and of finite presentation."]
theorem complexesIsom_finitePresentation_and_affine_overQuasiCompactNegativeExtLocus :
    Nonempty ((complexesFunctor D).isomPresheaf ⟨A, rfl⟩ ⟨sameTest A E' h₁ h₂, rfl⟩ ≅
      (overSchemeTest A.T.left).op ⋙ relativeDerivedIsomFunctor (D.projection A.T) A.E E') ∧
    IsFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj A.T.left)
      (relativeDerivedIsomFunctor (D.projection A.T) A.E E') ∧
    (∃ W₁ : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1,
      IsNegativeExtLocus (D.projection A.T) A.E E' W₁) ∧
    (∃ W₂ : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1,
      IsNegativeExtLocus (D.projection A.T) E' A.E W₂) ∧
    ∀ (W₁ W₂ : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1),
      IsNegativeExtLocus (D.projection A.T) A.E E' W₁ →
      IsNegativeExtLocus (D.projection A.T) E' A.E W₂ →
      IsQuasiCompact B S hS (openSubspaceImmersion B S hS ⟨W₁.1 ⊓ W₂.1,
          isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
            W₁.2 W₂.2⟩).hom ∧
      (∀ T' : SchemesOver ((schemeSpaceFunctor B S hS).obj A.T.left),
        Nonempty ((relativeDerivedIsomFunctor (D.projection A.T) A.E E').obj (op T')) →
          ∃ t : (schemeSpaceFunctor B S hS).obj T'.left ⟶ openSubspaceAsSpace B S hS ⟨W₁.1 ⊓ W₂.1,
          isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
            W₁.2 W₂.2⟩,
            t ≫ openSubspaceImmersion B S hS ⟨W₁.1 ⊓ W₂.1,
          isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
            W₁.2 W₂.2⟩ = T'.hom) ∧
      IsAffineFinitePresentationAlgebraicSpaceOver (openSubspaceAsSpace B S hS ⟨W₁.1 ⊓ W₂.1,
          isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
            W₁.2 W₂.2⟩)
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS)
          (openSubspaceImmersion B S hS ⟨W₁.1 ⊓ W₂.1,
          isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).2 W₁.1 W₂.1
            W₁.2 W₂.2⟩)).op ⋙
          relativeDerivedIsomFunctor (D.projection A.T) A.E E') := by
  obtain ⟨hiso, hfp, hW₁, hW₂, -⟩ :=
    complexesIsom_finitePresentation_and_affine_overNegativeExtLocus A E' h₁ h₂
  exact ⟨hiso, hfp, hW₁, hW₂, fun W₁ W₂ hW₁ hW₂ =>
    complexesIsom_factors_isAffineFinitePresentation_inf A E' h₁ h₂ W₁ W₂ hW₁ hW₂⟩

end ComplexesSituation

end AlgebraicGeometry.Space

end
