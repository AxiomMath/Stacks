module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyContractionUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyDivisorSheafComparison
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyDivisorSheafFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyRatioMap
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyRatioMapFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilySectionsLift
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.RepresentableFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatMonomorphismRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.AffineCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# A family of curves is a scheme near a fibre carrying two good divisors

Let `X ⟶ S` be a family of curves over an affine Noetherian scheme, `s` a closed point of `S`
with fibre presented by a scheme `V`, and `D₁, D₂` relative effective Cartier divisors of `X`
whose fibres `E₁, E₂` at `s` have disjoint supports and are *good* in a sense fixed by a
predicate `Good`. This file states that the family is then a scheme over a Zariski open
neighbourhood of `s`: every base change of the family through that open has representable total
space. It is step P3 of the route to Stacks 0E6F.

## Main definitions

* `AlgebraicGeometry.C1590Private.SchemeNearFibreOfGoodDivisors`: the statement above, for a
  predicate `Good` on effective Cartier divisors of fibres.

## Main results

* `AlgebraicGeometry.C1590Private.mem_schematicLocus_of_hasRelativeDimensionAt_zero`: a point at
  which a separated morphism of finite type to a scheme has relative dimension zero lies in the
  schematic locus (Stacks 04NW and 03XX).
* `AlgebraicGeometry.C1590Private.exists_open_isRepresentable_of_forall_mem_schematicLocus`: if
  the fibre at a point lies in the schematic locus of the total space, the family is a scheme over
  a Zariski open neighbourhood of the point (the image of the closed complement of the schematic
  locus is closed, the family being proper).
* `AlgebraicGeometry.C1590Private.hasRelativeDimensionAt_zero_of_fibre`: a morphism from an open
  of the total space to a scheme over the base has relative dimension zero along the fibre when it
  restricts there to a locally quasi-finite morphism of schemes (Stacks 04NS).
* `AlgebraicGeometry.C1590Private.restrict_ratioAt_eq_appLE`: on an affine chart diagram over the
  fibre, the ratio `t / 1_D` of a lift `t` of `f · 1_E` is `f`.
* `AlgebraicGeometry.C1590Private.mem_schematicLocus_of_isGoodDivisor`: a fibre point off a good
  divisor lies in the schematic locus.
* `AlgebraicGeometry.C1590Private.schemeNearFibreOfGoodDivisors_of_fibreDivisorSheafComparison`:
  P3 for `IsGoodFibreDivisor`, given piece (c) (`FibreDivisorSheafComparison`).
* `AlgebraicGeometry.C1590Private.schemeNearFibreOfGoodDivisors`: P3 for `IsGoodFibreDivisor`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

section Schematic

open Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A point of a subspace lies in the range of the points of any larger subspace. -/
private theorem mem_range_pointsMap_ι_of_le {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A A' : Subfunctor F} (hle : A ≤ A') {w : points B S hS F}
    (hw : w ∈ Set.range (pointsMap B S hS A.toFunctor A.ι)) :
    w ∈ Set.range (pointsMap B S hS A'.toFunctor A'.ι) := by
  obtain ⟨w₀, rfl⟩ := hw
  exact ⟨pointsMap B S hS _ (Subfunctor.homOfLe hle) w₀, by
    rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩

/-- **A point at which a separated morphism of finite type to a scheme has relative dimension
zero lies in the schematic locus.** The relative-dimension-zero locus is an open subspace on
which the morphism is locally quasi-finite (Stacks 04NW), and it is separated over the scheme,
so it is a scheme by Stacks 03XX. -/
theorem mem_schematicLocus_of_hasRelativeDimensionAt_zero {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (T : BigFppfOver B S hS) (g : F ⟶ yoneda.obj T)
    (hg : IsLocallyOfFiniteType B S hS g) (hsep : Space.IsSeparated B S hS g)
    (w : points B S hS F) (hw : HasRelativeDimensionAt 0 B S hS g w) :
    w ∈ Set.range (pointsMap B S hS (schematicLocus B S hS F).toFunctor
      (schematicLocus B S hS F).ι) := by
  have hT := isAlgebraicSpace_yoneda B S hS T
  set W₀ := relativeDimensionZeroLocus B S hS g
  have hW₀ : IsOpenSubspace B S hS W₀ :=
    isOpenSubspace_relativeDimensionZeroLocus B S hS hF hT g hg
  have hlqf := isLocallyQuasiFinite_relativeDimensionZeroLocus B S hS hF hT g hg
  have hsep₀ : Space.IsSeparated B S hS (W₀.ι ≫ g) :=
    isSeparated_comp B S hS _ _ (isSeparated_of_mono B S hS _ inferInstance) hsep
  have hrep : W₀.toFunctor.IsRepresentable :=
    isRepresentable_of_locallyQuasiFinite_separated B S hS _ _ hW₀.1 hT (W₀.ι ≫ g)
      (inferInstance : (yoneda.obj T).IsRepresentable) hlqf hsep₀
  have hle := le_schematicLocus B S hS F W₀ hW₀ hrep
  have hw' : w ∈ Set.range (pointsMap B S hS W₀.toFunctor W₀.ι) := by
    rw [range_pointsMap_relativeDimensionZeroLocus]
    exact hw
  exact mem_range_pointsMap_ι_of_le B S hS hle hw'

end Schematic

section Shrink

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

attribute [local instance] Space.pointTopology

open Space in
/-- **The shrinking step of P3.** If every point of the fibre of a family of curves at a
field-valued point lies in the schematic locus of the total space, then over a Zariski open
neighbourhood of the point every base change of the family has representable total space. The
open is the complement of the image of the closed complement of the schematic locus, which is
closed because the family is proper. -/
theorem exists_open_isRepresentable_of_forall_mem_schematicLocus (X : CurveFamily B hZ)
    [IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base)]
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (hsch : ∀ y : points B integerBase hZ (yoneda.obj V),
      pointsMap B integerBase hZ _ q y ∈ Set.range (pointsMap B integerBase hZ
        (schematicLocus B integerBase hZ X.total.obj).toFunctor
        (schematicLocus B integerBase hZ X.total.obj).ι)) :
    ∃ (U' : BigFppfOver B integerBase hZ) (j : U' ⟶ X.base),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
      (∃ t : P.siteObject ⟶ U', yoneda.map (t ≫ j) = yonedaEquiv.symm P.value) ∧
      ∀ (Y : CurveFamily B hZ) (φ : Y ⟶ X) (k : Y.base ⟶ U'), k ≫ j = φ.baseMap →
        Y.total.obj.IsRepresentable := by
  classical
  set Sch := schematicLocus B integerBase hZ X.total.obj
  obtain ⟨hSchO, hSchR⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B integerBase hZ
      X.total.2
  set Ssch := Set.range (pointsMap B integerBase hZ Sch.toFunctor Sch.ι)
  have hSopen : IsOpen Ssch := isOpen_range_pointsMap_of_isOpenImmersion B integerBase hZ _ hSchO.2
  have hfcl : IsClosedMap (pointsMap B integerBase hZ X.total.obj X.toBase.hom) :=
    isClosed_of_universallyClosed B integerBase hZ (isAlgebraicSpace_yoneda B integerBase hZ _)
      _ X.proper.2.2
  set Z := pointsMap B integerBase hZ X.total.obj X.toBase.hom '' Sschᶜ
  have hZcl : IsClosed Z := hfcl _ hSopen.isClosed_compl
  set Zs := schemePointsHomeomorph B integerBase hZ X.base '' Z
  have hZscl : IsClosed Zs := (schemePointsHomeomorph B integerBase hZ X.base).isClosedMap _ hZcl
  let O : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens := ⟨Zsᶜ, hZscl.isOpen_compl⟩
  -- the point of `P` lies in `O`
  have hPO : ∀ x : (BigFppfOver.toScheme B integerBase hZ).obj P.siteObject,
      (BigFppfOver.toScheme B integerBase hZ).map P.value x ∈ O := by
    intro x
    set p₀ := (schemePointsHomeomorph B integerBase hZ P.siteObject).symm x
    have hx : pointsToScheme B integerBase hZ P.siteObject p₀ = x :=
      (schemePointsHomeomorph B integerBase hZ P.siteObject).apply_symm_apply x
    rintro ⟨z, ⟨c, hc, rfl⟩, hcz⟩
    have hval := yonedaEquiv_symm_value P
    have h1 : pointsToScheme B integerBase hZ X.base
        (pointsMap B integerBase hZ (yoneda.obj P.siteObject)
          (yoneda.map (show P.siteObject ⟶ X.base from P.value)) p₀) =
          (BigFppfOver.toScheme B integerBase hZ).map P.value x := by
      rw [pointsToScheme_pointsMap_yoneda, hx]
    have hab : pointsMap B integerBase hZ X.total.obj X.toBase.hom c =
        pointsMap B integerBase hZ _ (yonedaEquiv.symm P.value) p₀ := by
      rw [hval]
      exact (schemePointsHomeomorph B integerBase hZ X.base).injective (hcz.trans h1.symm)
    obtain ⟨y, hy, -⟩ := exists_points_of_isPullback B integerBase hZ hq c p₀ hab
    exact hc (hy ▸ hsch y)
  -- the open subscheme `O` as an object of the site
  have : QuasiCompact O.ι := inferInstance
  have hU' : B.Contains O.toScheme :=
    Space.contains_of_locallyOfFiniteType_of_quasiCompact B integerBase hZ (Y₀ := X.base) O.ι
  let U' := BigFppfOver.siteObjectOver B integerBase hZ X.base hU' O.ι
  let j : U' ⟶ X.base := BigFppfOver.siteMapOver B integerBase hZ X.base hU' O.ι
  have hj : (BigFppfOver.toScheme B integerBase hZ).map j = O.ι :=
    BigFppfOver.toScheme_map_siteMapOver _ _ _ _ _ _
  have hrange : Set.range ((BigFppfOver.toScheme B integerBase hZ).map P.value) ⊆
      Set.range O.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hPO x
  let t₀ : (BigFppfOver.toScheme B integerBase hZ).obj P.siteObject ⟶ O.toScheme :=
    IsOpenImmersion.lift O.ι ((BigFppfOver.toScheme B integerBase hZ).map P.value) hrange
  let t : P.siteObject ⟶ U' := homOfToScheme t₀
  refine ⟨U', j, (by
    rw [hj]; exact (inferInstance : AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι O))),
    ⟨t, ?_⟩, ?_⟩
  · rw [yonedaEquiv_symm_value]
    congr 1
    apply hom_ext_of_toScheme
    exact (Functor.map_comp _ _ _).trans (IsOpenImmersion.lift_fac O.ι _ hrange)
  · intro Y φ k hk
    have sqY : IsPullback φ.totalMap.hom Y.toBase.hom X.toBase.hom (schemeSpaceMap φ.baseMap).hom :=
      AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
    set P' := Sch.preimage φ.totalMap.hom
    have hP'O : IsOpenSubspace B integerBase hZ P' :=
      isOpenSubspace_preimage B integerBase hZ φ.totalMap.hom Sch X.total.2 Y.total.2 hSchO
    have hP'R : P'.toFunctor.IsRepresentable := by
      have sq := (Subfunctor.isPullback_preimage φ.totalMap.hom Sch).paste_vert sqY
      have _ := hSchR
      have hpb := isRepresentable_pullback B integerBase hZ
        (isAlgebraicSpace_yoneda B integerBase hZ X.base) hSchR
        (inferInstance : (yoneda.obj Y.base).IsRepresentable) (Sch.ι ≫ X.toBase.hom)
        (schemeSpaceMap φ.baseMap).hom
      exact @isRepresentable_of_natIso _ _ _ _ sq.isoPullback.symm hpb
    have hle : P' ≤ schematicLocus B integerBase hZ Y.total.obj :=
      le_schematicLocus B integerBase hZ _ P' hP'O hP'R
    apply isRepresentable_of_surjective_pointsMap_schematicLocus B integerBase hZ Y.total.2
    intro y
    have hy : pointsMap B integerBase hZ _ φ.totalMap.hom y ∈ Ssch := by
      by_contra hns
      have hz : pointsMap B integerBase hZ _ X.toBase.hom
          (pointsMap B integerBase hZ _ φ.totalMap.hom y) ∈ Z := ⟨_, hns, rfl⟩
      have hcomm : pointsMap B integerBase hZ _ X.toBase.hom
          (pointsMap B integerBase hZ _ φ.totalMap.hom y) =
          pointsMap B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom
            (pointsMap B integerBase hZ _ Y.toBase.hom y) := by
        have e1 := congrFun (pointsMap_comp B integerBase hZ _ φ.totalMap.hom X.toBase.hom) y
        have e2 := congrFun (pointsMap_comp B integerBase hZ _ Y.toBase.hom
          (schemeSpaceMap φ.baseMap).hom) y
        rw [sqY.w] at e1
        exact e1.symm.trans e2
      rw [hcomm, ← hk] at hz
      have hmemO : pointsToScheme B integerBase hZ X.base
          (pointsMap B integerBase hZ (yoneda.obj Y.base) (yoneda.map (k ≫ j))
            (pointsMap B integerBase hZ _ Y.toBase.hom y)) ∈ O := by
        rw [pointsToScheme_pointsMap_yoneda, Functor.map_comp, Scheme.Hom.comp_apply]
        exact ((BigFppfOver.toScheme B integerBase hZ).map k (pointsToScheme B integerBase hZ
          Y.base (pointsMap B integerBase hZ _ Y.toBase.hom y))).2
      exact hmemO ⟨_, hz, rfl⟩
    have hy' : y ∈ Set.range (pointsMap B integerBase hZ P'.toFunctor P'.ι) := by
      rw [range_pointsMap_preimage_ι]
      exact hy
    exact mem_range_pointsMap_ι_of_le B integerBase hZ hle hy'

end Shrink

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **P3 of the 0E6F route.** Over an affine Noetherian base, two relative effective Cartier
divisors whose fibres at a closed point are `Good` with disjoint supports make the family a scheme
over an open neighbourhood `U'` of the point: every base change `Y` of the family through `U'` has
representable total space. -/
def SchemeNearFibreOfGoodDivisors
    (Good : ∀ V : BigFppfOver B integerBase hZ,
      ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData → Prop) : Prop :=
  ∀ (X : CurveFamily B hZ)
    (_ : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (_ : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (_ : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (_ : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (D₁ D₂ : Space.ClosedSubspaces B integerBase hZ X.total.obj)
    (E₁ E₂ : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData),
    Space.IsRelativeEffectiveCartierDivisor B integerBase hZ X.toBase D₁ →
    Space.IsRelativeEffectiveCartierDivisor B integerBase hZ X.toBase D₂ →
    D₁.1.preimage q = (Space.closedSubspaceOfIdeal V E₁).1 →
    D₂.1.preimage q = (Space.closedSubspaceOfIdeal V E₂).1 →
    Disjoint (E₁.support : Set ((BigFppfOver.toScheme B integerBase hZ).obj V))
      E₂.support → Good V E₁ → Good V E₂ →
    ∃ (U' : BigFppfOver B integerBase hZ) (j : U' ⟶ X.base),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
      (∃ t : P.siteObject ⟶ U', yoneda.map (t ≫ j) = yonedaEquiv.symm P.value) ∧
      ∀ (Y : CurveFamily B hZ) (φ : Y ⟶ X) (k : Y.base ⟶ U'), k ≫ j = φ.baseMap →
        Y.total.obj.IsRepresentable

section Proof

variable {B hZ}

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] Space.hasInjectiveResolutions_modules

open Opposite TopologicalSpace Space
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)

/-- **Relative dimension zero along the fibre, from a quasi-finite fibre map.** Let `G ⊆ X` be an
open subspace of the total space of a family of curves, `g : G ⟶ T` a morphism, locally of
finite type, to an object of the site over `X.base`, `V` a presentation of the fibre at a
field-valued point, and `ι : V° ⟶ V` an open immersion with `h_ι ≫ q` landing in `G` through
`φ`. If on every affine chart diagram for `φ` the composite map to `T` is the chart followed by a
locally quasi-finite morphism `ζ : V° ⟶ T`, then `g` has relative dimension zero at every point
of `G` coming from `V°`: base change to the fibre (Stacks 04NS) followed by an étale chart. -/
theorem hasRelativeDimensionAt_zero_of_fibre (X : CurveFamily B hZ)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (G : Subfunctor X.total.obj) (hG : IsOpenSubspace B integerBase hZ G)
    (T : BigFppfOver B integerBase hZ) (πT : T ⟶ X.base) (g : G.toFunctor ⟶ yoneda.obj T)
    (hgπ : g ≫ yoneda.map πT = G.ι ≫ X.toBase.hom)
    (hg : IsLocallyOfFiniteType B integerBase hZ g)
    (Vo : BigFppfOver B integerBase hZ) (ι : Vo ⟶ V)
    (hι : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map ι))
    (φ : yoneda.obj Vo ⟶ G.toFunctor) (hφ : φ ≫ G.ι = yoneda.map ι ≫ q)
    (ζ : (BigFppfOver.toScheme B integerBase hZ).obj Vo ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj T)
    (hζ1 : LocallyOfFiniteType ζ) (hζ2 : LocallyQuasiFinite ζ)
    (hζ : ∀ (A : Space.SmallEtale B integerBase hZ (yoneda.obj Vo))
      (C : Space.SmallEtale B integerBase hZ G.toFunctor) (k : A.1.left ⟶ C.1.left),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj A.1.left) →
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj C.1.left) →
      yoneda.map k ≫ C.1.hom = A.1.hom ≫ φ →
      (BigFppfOver.toScheme B integerBase hZ).map (k ≫ yoneda.preimage (C.1.hom ≫ g)) =
        (BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom) ≫ ζ)
    (y₀ : points B integerBase hZ (yoneda.obj Vo)) :
    HasRelativeDimensionAt 0 B integerBase hZ g (pointsMap B integerBase hZ _ φ y₀) := by
  classical
  -- the fibre `G_P = q⁻¹ G` of `G`, and the base change `g' : G_P ⟶ T_P` of `g`
  let pv : P.siteObject ⟶ X.base := P.value
  have hq' : IsPullback q (yoneda.map v) X.toBase.hom (yoneda.map pv) := by
    rwa [← yonedaEquiv_symm_value]
  let GP := G.preimage q
  have sqA := (Subfunctor.isPullback_preimage q G).paste_vert hq'
  let TP := pullback (yoneda.map πT) (yoneda.map pv)
  have hTP : IsAlgebraicSpace B integerBase hZ TP :=
    isAlgebraicSpace_pullback B integerBase hZ _ _ (isAlgebraicSpace_yoneda _ _ _ T)
      (isAlgebraicSpace_yoneda _ _ _ P.siteObject) (isAlgebraicSpace_yoneda _ _ _ X.base)
  have hw : (G.fromPreimage q ≫ g) ≫ yoneda.map πT = (GP.ι ≫ yoneda.map v) ≫ yoneda.map pv := by
    rw [Category.assoc, hgπ]
    exact sqA.w
  let g' : GP.toFunctor ⟶ TP := pullback.lift (G.fromPreimage q ≫ g) (GP.ι ≫ yoneda.map v) hw
  have sqB : IsPullback (G.fromPreimage q) g' g (pullback.fst (yoneda.map πT) (yoneda.map pv)) := by
    have s : IsPullback (G.fromPreimage q) (g' ≫ pullback.snd _ _) (g ≫ yoneda.map πT)
        (yoneda.map pv) := by
      have e1 : g' ≫ pullback.snd (yoneda.map πT) (yoneda.map pv) = GP.ι ≫ yoneda.map v :=
        pullback.lift_snd _ _ _
      rw [e1, hgπ]
      exact sqA
    exact IsPullback.of_bot s (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
  -- `V°` maps into `G_P`
  let c : yoneda.obj Vo ⟶ GP.toFunctor := Subfunctor.lift (yoneda.map ι) (G := GP)
    (fun a _ ⟨x, hx⟩ => by
      rw [← hx]
      change q.app a ((yoneda.map ι).app a x) ∈ G.obj a
      rw [← NatTrans.comp_app_apply, ← hφ, NatTrans.comp_app_apply]
      exact (φ.app a x).2)
  have hcφ : c ≫ G.fromPreimage q = φ := by
    rw [← cancel_mono G.ι, Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc]
    exact hφ.symm
  -- reduce to `g'` at the image of `y₀` in `G_P`
  have hrd : HasRelativeDimensionAt 0 B integerBase hZ g' (pointsMap B integerBase hZ _ c y₀) := by
    obtain ⟨A, a, ⟨hAaff, C, k, hk, hCaff⟩, z', hz'⟩ :=
      exists_hasAffineChartDiagram B integerBase hZ
      (X := schemeSpace Vo) (X' := ⟨G.toFunctor, hG.1⟩) (ObjectProperty.homMk φ)
      (idEtaleChart B integerBase hZ Vo) (pointsToScheme B integerBase hZ Vo y₀)
    let y'' := (pointsEquivScheme B integerBase hZ A.1.left).symm z'
    have hAhom : A.1.hom = yoneda.map a.hom.left :=
      a.hom.w.symm.trans (Category.comp_id _)
    have hAy : pointsMap B integerBase hZ _ A.1.hom y'' = y₀ := by
      apply injective_pointsToScheme B integerBase hZ Vo
      have h1 := pointsToScheme_pointsMap_yoneda B integerBase hZ a.hom.left y''
      have h2 : pointsToScheme B integerBase hZ A.1.left y'' = z' :=
        (pointsEquivScheme B integerBase hZ A.1.left).apply_symm_apply z'
      refine (congrArg (fun m => pointsToScheme B integerBase hZ Vo
        (pointsMap B integerBase hZ _ m y'')) hAhom).trans (h1.trans ?_)
      rw [h2]
      exact hz'
    have hcO : Space.IsOpenImmersion B integerBase hZ c :=
      isOpenImmersion_of_comp_mono B integerBase hZ c GP.ι
        (isOpenImmersion_yoneda_map B integerBase hZ ι hι)
    have hc' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B integerBase hZ)).presheaf (A.1.hom ≫ c) :=
      (isMultiplicative_presheaf_etale B integerBase hZ).comp_mem _ _ A.2
        (presheaf_etale_of_isOpenImmersion B integerBase hZ hcO)
    have key := (hasRelativeDimensionAt_comp_iff B integerBase hZ 0 (A.1.hom ≫ c) g' hc'
      (isAlgebraicSpace_yoneda _ _ _ A.1.left) hTP y'').1 ?_
    · have e : pointsMap B integerBase hZ _ (A.1.hom ≫ c) y'' =
          pointsMap B integerBase hZ _ c y₀ :=
        (congrFun (pointsMap_comp B integerBase hZ _ A.1.hom c) y'').trans
          (congrArg (pointsMap B integerBase hZ _ c) hAy)
      exact e ▸ key
    have hg'fst : g' ≫ pullback.fst (yoneda.map πT) (yoneda.map pv) = G.fromPreimage q ≫ g :=
      pullback.lift_fst _ _ _
    have hfac : ((A.1.hom ≫ c) ≫ g') ≫ pullback.fst (yoneda.map πT) (yoneda.map pv) =
        yoneda.map (k ≫ yoneda.preimage (C.1.hom ≫ g)) := by
      have h3 : (A.1.hom ≫ c) ≫ G.fromPreimage q = A.1.hom ≫ φ := by
        rw [← hcφ]; exact Category.assoc _ _ _
      rw [Category.assoc, hg'fst, ← Category.assoc, h3,
        show A.1.hom ≫ φ = yoneda.map k ≫ C.1.hom from hk.symm, Functor.map_comp,
        Functor.map_preimage, Category.assoc]
    have hAet : Etale ((BigFppfOver.toScheme B integerBase hZ).map
        (yoneda.preimage A.1.hom)) := by
      have h2 : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B integerBase hZ)).presheaf (yoneda.map a.hom.left) :=
        hAhom ▸ A.2
      have h4 : yoneda.preimage A.1.hom = a.hom.left :=
        yoneda.map_injective ((Functor.map_preimage _ _).trans hAhom)
      rw [h4]
      exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B integerBase hZ _ _).1 h2
    have hZζ := hζ A C k hAaff hCaff hk
    have hlqfS : LocallyQuasiFinite ((BigFppfOver.toScheme B integerBase hZ).map
        (k ≫ yoneda.preimage (C.1.hom ≫ g))) := by
      rw [hZζ]; infer_instance
    have hlftS : LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map
        (k ≫ yoneda.preimage (C.1.hom ≫ g))) := by
      rw [hZζ]; infer_instance
    have hlqf : IsLocallyQuasiFinite B integerBase hZ ((A.1.hom ≫ c) ≫ g') := by
      refine isLocallyQuasiFinite_of_comp B integerBase hZ (isAlgebraicSpace_yoneda _ _ _ _) hTP
        (isAlgebraicSpace_yoneda _ _ _ T) _ (pullback.fst (yoneda.map πT) (yoneda.map pv)) ?_
      rw [hfac]
      exact (isLocallyQuasiFinite_yoneda_map_iff B integerBase hZ _).2 ⟨hlftS, hlqfS⟩
    have hlft : IsLocallyOfFiniteType B integerBase hZ ((A.1.hom ≫ c) ≫ g') := by
      refine Space.isLocallyOfFiniteType_of_comp B integerBase hZ
        (isAlgebraicSpace_yoneda _ _ _ _) hTP (isAlgebraicSpace_yoneda _ _ _ T) _
        (pullback.fst (yoneda.map πT) (yoneda.map pv)) ?_
      rw [hfac]
      exact (isLocallyOfFiniteType_yoneda_map_iff B integerBase hZ _).2 hlftS
    exact (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B integerBase hZ _
      hlft).1 hlqf y''
  have h := (hasRelativeDimensionAt_iff_of_isPullback' B integerBase hZ 0 sqB.flip hG.1
    (isAlgebraicSpace_yoneda _ _ _ T) hTP hg (pointsMap B integerBase hZ _ c y₀)).1 hrd
  have e := congrFun (pointsMap_comp B integerBase hZ _ c (G.fromPreimage q)) y₀
  rw [hcφ] at e
  rw [e]
  exact h

/-- Two successive restrictions of a section of the structure sheaf are one restriction. -/
theorem presheaf_map_map_apply (Z : Scheme.{u}) {W₁ W₂ W₃ : Z.Opens} (i : W₂ ⟶ W₁) (j : W₃ ⟶ W₂)
    (l : W₃ ⟶ W₁) (x : Γ(Z, W₁)) :
    Z.presheaf.map j.op (Z.presheaf.map i.op x) = Z.presheaf.map l.op x := by
  rw [Subsingleton.elim l (j ≫ i), op_comp, Functor.map_comp, CommRingCat.comp_apply]

/-- **The ratio on an affine chart diagram is the given function.** Let `D` be an effective
Cartier divisor on `Y`, `q : h_V ⟶ Y`, and `t` a global section of `𝒪_Y(D)` whose pullback to `V`
is `f · q^*1_D` over every étale chart of `h_V` landing in the open `Uo`. On an affine chart
diagram `k : A ⟶ C` over `q`, with `C` a chart of `Y ∖ D` and `A` landing in `Uo`, the pullback of
the ratio `t / 1_D` along `k` is the restriction of `f`: cancel the pulled-back basis `q^*1_D`. -/
theorem restrict_ratioAt_eq_appLE (Y : AlgebraicSpaces B integerBase hZ)
    (V : BigFppfOver B integerBase hZ) (q : yoneda.obj V ⟶ Y.obj)
    (D : Space.ClosedSubspaces B integerBase hZ Y.obj)
    (hD : Space.IsEffectiveCartierDivisor B integerBase hZ Y D)
    (Uo : ((BigFppfOver.toScheme B integerBase hZ).obj V).Opens)
    (t : (globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
        Y.1 Y.2).O)).obj (Space.associatedInvertibleSheaf B integerBase hZ Y D hD))
    (f : Γ((BigFppfOver.toScheme B integerBase hZ).obj V, Uo))
    (hσ : ∀ (A : Space.SmallEtale B integerBase hZ (yoneda.obj V))
      (hA : ⊤ ≤ (BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom) ⁻¹ᵁ Uo),
      (show ((Space.modulePullback B integerBase hZ
            (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
            (Space.associatedInvertibleSheaf B integerBase hZ Y D hD)).val.obj (op A) from
        ((Space.globalSectionsPullbackMap B integerBase hZ
          (ObjectProperty.homMk q : schemeSpace V ⟶ Y) _).hom t).1 (op A)) =
        (show Space.chartRing B integerBase hZ (schemeSpace V).1 (schemeSpace V).2 A from
          ((BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom)).appLE
            Uo ⊤ hA f) •
          (show ((Space.modulePullback B integerBase hZ
              (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
              (Space.associatedInvertibleSheaf B integerBase hZ Y D hD)).val.obj (op A) from
            ((Space.globalSectionsPullbackMap B integerBase hZ
              (ObjectProperty.homMk q : schemeSpace V ⟶ Y) _).hom
              (Space.canonicalSection B integerBase hZ Y D hD)).1 (op A)))
    (A : Space.SmallEtale B integerBase hZ (yoneda.obj V))
    (C : Space.SmallEtale B integerBase hZ (openComplementSpace B integerBase hZ Y D).1)
    (k : A.1.left ⟶ C.1.left)
    (hAaff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj A.1.left))
    (hCaff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj C.1.left))
    (hk : A.1.hom ≫ q = yoneda.map k ≫ ((complementChart B integerBase hZ Y D).obj C).1.hom)
    (hA : ⊤ ≤ (BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom) ⁻¹ᵁ Uo) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B integerBase hZ).map k).op).hom
        (ratioAt B integerBase hZ Y D hD t C) =
      ((BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom)).appLE Uo ⊤ hA f := by
  let d : ChartDiagram B integerBase hZ (schemeSpace V).1 Y.1
      (ObjectProperty.homMk q : schemeSpace V ⟶ Y).hom :=
    ⟨A, (complementChart B integerBase hZ Y D).obj C, k, hk⟩
  have hM : (Space.associatedInvertibleSheaf B integerBase hZ Y D hD).IsQuasicoherentOnSite :=
    Space.isQuasicoherentOnSite_of_isInvertible B integerBase hZ Y _
      (associatedInvertibleSheaf_isInvertible B integerBase hZ Y D hD)
  have h1 := globalSectionsPullbackMap_val_chartDiagram B integerBase hZ
    (ObjectProperty.homMk q : schemeSpace V ⟶ Y)
    (Space.associatedInvertibleSheaf B integerBase hZ Y D hD) t d
  have h2 := globalSectionsPullbackMap_val_chartDiagram B integerBase hZ
    (ObjectProperty.homMk q : schemeSpace V ⟶ Y)
    (Space.associatedInvertibleSheaf B integerBase hZ Y D hD)
    (Space.canonicalSection B integerBase hZ Y D hD) d
  have h3 := ratioAt_smul B integerBase hZ Y D hD t C
  have h4 := modulePullbackChartSection_smul B integerBase hZ
    (f := (ObjectProperty.homMk q : schemeSpace V ⟶ Y))
    (M := (Space.associatedInvertibleSheaf B integerBase hZ Y D hD)) d
    (ratioAt B integerBase hZ Y D hD t C)
    (canonicalSectionAt B integerBase hZ Y D hD ((complementChart B integerBase hZ Y D).obj C))
  have h5 := hσ A hA
  apply smul_modulePullbackChartSection_injective B integerBase hZ
    (ObjectProperty.homMk q : schemeSpace V ⟶ Y)
    (Space.associatedInvertibleSheaf B integerBase hZ Y D hD) hM d hAaff hCaff _
    (bijective_smul_canonicalSection_complementChart B integerBase hZ Y D hD C)
  change _ • _ = _ • _
  have e1 := h4.symm.trans
    (congrArg (modulePullbackChartSection B integerBase hZ
      (ObjectProperty.homMk q : schemeSpace V ⟶ Y)
      (Space.associatedInvertibleSheaf B integerBase hZ Y D hD) d) h3)
  have e2 := congrArg (fun x : ((Space.modulePullback B integerBase hZ
      (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
      (Space.associatedInvertibleSheaf B integerBase hZ Y D hD)).val.obj (op A) =>
    (show Space.chartRing B integerBase hZ (schemeSpace V).1 (schemeSpace V).2 A from
      ((BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom)).appLE
        Uo ⊤ hA f) • x) h2
  exact (e1.trans h1.symm).trans (h5.trans e2)

/-- **A fibre point off a good divisor lies in the schematic locus.** Let `D` be a relative
effective Cartier divisor of `X` whose fibre `E` at the closed point `P` is a good divisor of the
fibre `V`, and `y` a point of `V` off `E`. The sections `fⱼ` of `𝒪_V(E)` lift (piece (c) and F4)
to sections `tⱼ` of `𝒪_X(D)` near the fibre, and the ratios `tⱼ / 1_D` define `X ∖ D ⟶ 𝔸ⁿ` over
the base. On the fibre this is the finite map `V ∖ E ⟶ 𝔸ⁿ_P` of the `fⱼ` (Q1), so it has
relative dimension zero at `y` (Stacks 04NS), and `y` lies in the schematic locus (Stacks 04NW,
03XX). -/
theorem mem_schematicLocus_of_isGoodDivisor (hc : FibreDivisorSheafComparison B hZ)
    (hQ1 : FibreRatioRingHomFinite.{u}) (hQ2 : RangeLeOpenComplementOfPreimage B hZ)
    (X : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (hN : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (hP : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (D : Space.ClosedSubspaces B integerBase hZ X.total.obj)
    (hD : Space.IsRelativeEffectiveCartierDivisor B integerBase hZ X.toBase D)
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData)
    (hDE : D.1.preimage q = (Space.closedSubspaceOfIdeal V E).1)
    (hgood : IsGoodDivisor ((BigFppfOver.toScheme B integerBase hZ).obj V) E)
    (y : points B integerBase hZ (yoneda.obj V))
    (hy : pointsToScheme B integerBase hZ V y ∈ E.support.compl) :
    pointsMap B integerBase hZ _ q y ∈ Set.range (pointsMap B integerBase hZ
      (schematicLocus B integerBase hZ X.total.obj).toFunctor
      (schematicLocus B integerBase hZ X.total.obj).ι) := by
  classical
  obtain ⟨hECD, hUaff, hH1, n, f, ht, hgen⟩ := hgood
  obtain ⟨hc1, hc2⟩ := hc X.total V q D hD.1 E hECD hDE
  choose t₀ ht₀ using ht
  choose σ hσ using fun i => hc2 (t₀ i) (f i) (ht₀ i)
  have hinv := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (associatedInvertibleSheaf_isInvertible B integerBase hZ X.total D hD.1)
  have hsurj := surjective_globalSectionsPullbackMap_of_fibreH1Zero B hZ X hA hN
    (associatedInvertibleSheaf B integerBase hZ X.total D hD.1) hinv P V v q hq hP (hc1 hH1)
  choose tl htl using fun i => hsurj (σ i)
  have := hA
  let W := openComplementSpace B integerBase hZ X.total D
  let iW := openComplementHom B integerBase hZ X.total D
  let r : Fin n → globalFunctions B integerBase hZ W.1 :=
    fun i => ratio B integerBase hZ X.total D hD.1 (tl i)
  let p := iW ≫ X.toBase
  let g := ratioMap X.base W p r
  have hp1 : IsLocallyOfFiniteType B integerBase hZ p.hom :=
    isLocallyOfFiniteType_comp B integerBase hZ W.2 X.total.2
      (isAlgebraicSpace_yoneda B integerBase hZ X.base) iW.hom X.toBase.hom
      (isLocallyOfFiniteType_of_isEtale' B integerBase hZ _
        (isEtale_openComplementHom B integerBase hZ X.total D))
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
        X.finitePresentation.1)
  have hp2 : Space.IsSeparated B integerBase hZ p.hom :=
    isSeparated_comp B integerBase hZ iW.hom X.toBase.hom
      (Space.isSeparated_of_mono (B := B) (S := integerBase) (hS := hZ) iW.hom
        (inferInstanceAs (Mono (openComplement B integerBase hZ D.1).ι))) X.proper.1
  have hg1 := isLocallyOfFiniteType_ratioMap X.base W p r hp1
  have hg2 := isSeparated_ratioMap X.base W p r hp2
  obtain ⟨w, hw, hwq⟩ : ∃ w : points B integerBase hZ W.1,
      HasRelativeDimensionAt 0 B integerBase hZ g.hom w ∧
        pointsMap B integerBase hZ _ iW.hom w = pointsMap B integerBase hZ _ q y := by
    -- the complement `V° = V ∖ E` as an object of the site
    let U : ((BigFppfOver.toScheme B integerBase hZ).obj V).Opens := E.support.compl
    have : IsAffine U.toScheme := hUaff
    have hVo : B.Contains U.toScheme :=
      BigFppfSite.contains_of_locallyOfFinitePresentation B U.ι V.left.property
    let Vo := BigFppfOver.siteObjectOver B integerBase hZ V hVo U.ι
    let ι : Vo ⟶ V := BigFppfOver.siteMapOver B integerBase hZ V hVo U.ι
    have hι : ⊤ ≤ (BigFppfOver.toScheme B integerBase hZ).map ι ⁻¹ᵁ E.support.compl :=
      (Scheme.Opens.ι_preimage_self U).ge
    have hQ := hQ2 X.total V q D E hDE Vo ι hι
    let φW : yoneda.obj Vo ⟶ W.1 :=
      Subfunctor.lift (yoneda.map ι ≫ q) (G := openComplement B integerBase hZ D.1)
        (fun a _ ⟨x, hx⟩ => hx ▸ hQ a x)
    -- the point of `V°` over `y`
    obtain ⟨y₀, hy₀⟩ : y ∈ Set.range (pointsMap B integerBase hZ _ (yoneda.map ι)) := by
      refine mem_range_pointsMap_yoneda_map B integerBase hZ ι y ?_
      have hr : Set.range ((BigFppfOver.toScheme B integerBase hZ).map ι) = (U : Set _) :=
        Scheme.Opens.range_ι U
      rwa [hr]
    refine ⟨pointsMap B integerBase hZ _ φW y₀, ?_, ?_⟩
    · -- the base field and the fibre over it
      let pv : P.siteObject ⟶ X.base := P.value
      have hq' : IsPullback q (yoneda.map v) X.toBase.hom (yoneda.map pv) := by
        rwa [← yonedaEquiv_symm_value]
      have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) :=
        X.isProper_toScheme_map_of_isPullback_schemeSpaceMap
          (isPullback_homMk_of_isPullback _ v q hq')
      have : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map pv) := hP
      -- `ψ : Γ(Sb)[x₁..xₙ] → Γ(V, V°)`, `xⱼ ↦ fⱼ`, finite by (Q1)
      let ψ : MvPolynomial (Fin n) Γ((BigFppfOver.toScheme B integerBase hZ).obj X.base, ⊤) →+*
          Γ((BigFppfOver.toScheme B integerBase hZ).obj V, U) :=
        MvPolynomial.eval₂Hom
          ((((BigFppfOver.toScheme B integerBase hZ).obj V).presheaf.map
            (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
            (((BigFppfOver.toScheme B integerBase hZ).map v).appTop.hom.comp
              ((BigFppfOver.toScheme B integerBase hZ).map pv).appTop.hom)) f
      have hψ : ψ.Finite := by
        refine hQ1 (K := P.carrier) ((BigFppfOver.toScheme B integerBase hZ).map v) U hUaff f hgen
          ((Scheme.ΓSpecIso (.of P.carrier)).hom.hom.comp
            ((BigFppfOver.toScheme B integerBase hZ).map pv).appTop.hom)
          ((Scheme.ΓSpecIso (.of P.carrier)).commRingCatIsoToRingEquiv.surjective.comp
            (IsClosedImmersion.isAffine_surjective_of_isAffine _).2) ψ
          (fun j => MvPolynomial.eval₂Hom_X' _ _ _) (fun a => ?_)
        rw [MvPolynomial.eval₂Hom_C]
        exact congrArg _ (congrArg _
          (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of P.carrier)) _).symm)
      -- `ζ : V° ≅ Spec Γ(V, V°) ⟶ 𝔸ⁿ_{Sb}`
      let ζ : (BigFppfOver.toScheme B integerBase hZ).obj Vo ⟶
          (BigFppfOver.toScheme B integerBase hZ).obj (affineSpaceOver X.base n) :=
        hUaff.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ)
      have : IsFinite (Spec.map (CommRingCat.ofHom ψ)) := (IsFinite.SpecMap_iff _).2 hψ
      have hζ1 : LocallyOfFiniteType ζ :=
        inferInstanceAs (LocallyOfFiniteType (hUaff.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ)))
      have hζ2 : LocallyQuasiFinite ζ :=
        inferInstanceAs (LocallyQuasiFinite (hUaff.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ)))
      have hζapp : ∀ P' : MvPolynomial (Fin n)
          Γ((BigFppfOver.toScheme B integerBase hZ).obj X.base, ⊤),
          ζ.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n)
            Γ((BigFppfOver.toScheme B integerBase hZ).obj X.base, ⊤)))).inv P') =
            U.topIso.inv (ψ P') := by
        intro P'
        have e := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso _).inv P'))
          (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply,
          CommRingCat.hom_ofHom] at e
        change hUaff.isoSpec.hom.appTop ((Spec.map (CommRingCat.ofHom ψ)).appTop _) = _
        rw [IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply]
        exact congrArg U.topIso.inv.hom e
      have hgπ : g.hom ≫ yoneda.map (affineSpaceOverProj X.base n) =
          (openComplement B integerBase hZ D.1).ι ≫ X.toBase.hom :=
        congrArg (fun m => m.hom) (ratioMap_comp_proj X.base W p r)
      have hιO :
          AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map ι) :=
        inferInstanceAs (AlgebraicGeometry.IsOpenImmersion U.ι)
      refine hasRelativeDimensionAt_zero_of_fibre X P V v q hq (openComplement B integerBase hZ D.1)
        (isOpenSubspace_openComplement B integerBase hZ X.total.2 D.1 D.2)
        (affineSpaceOver X.base n) (affineSpaceOverProj X.base n) g.hom hgπ hg1 Vo ι hιO φW rfl
        ζ hζ1 hζ2 ?_ y₀
      intro A C k hAaff hCaff hk
      have := hAaff
      -- `A` read as an étale chart of `V`
      let A' : Space.SmallEtale B integerBase hZ (yoneda.obj V) :=
        ⟨CostructuredArrow.mk (A.1.hom ≫ yoneda.map ι),
          (isMultiplicative_presheaf_etale B integerBase hZ).comp_mem _ _ A.2
            (presheaf_etale_of_isOpenImmersion B integerBase hZ
              (isOpenImmersion_yoneda_map B integerBase hZ ι hιO))⟩
      have hA'pre : yoneda.preimage A'.1.hom = yoneda.preimage A.1.hom ≫ ι :=
        yoneda.map_injective (by
          rw [Functor.map_preimage, Functor.map_comp, Functor.map_preimage]; rfl)
      have hA'map : (BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A'.1.hom) =
          (BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom) ≫ U.ι := by
        rw [hA'pre, Functor.map_comp]; rfl
      have hA' : ⊤ ≤ (BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A'.1.hom) ⁻¹ᵁ
          E.support.compl := by
        rw [hA'map]
        intro x _
        exact ((BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom) x).2
      have hkA' : A'.1.hom ≫ q =
          yoneda.map k ≫ ((complementChart B integerBase hZ X.total D).obj C).1.hom := by
        change (A.1.hom ≫ yoneda.map ι) ≫ q =
          yoneda.map k ≫ C.1.hom ≫ (openComplement B integerBase hZ D.1).ι
        rw [← Category.assoc (yoneda.map k), hk, Category.assoc, Category.assoc]
        rfl
      have hID := fun j => restrict_ratioAt_eq_appLE X.total V q D hD.1 E.support.compl (tl j)
        (f j) (fun A₀ hA₀ => by rw [htl j]; exact hσ j A₀ hA₀) A' C k hAaff hCaff hkA' hA'
      -- the restriction `Γ(V, V°) → Γ(A)` along `A ⟶ V° ⊆ V`
      have hgen' : ∀ (a b : (BigFppfOver.toScheme B integerBase hZ).obj A.1.left ⟶
          (BigFppfOver.toScheme B integerBase hZ).obj V) (h : a = b) (e : ⊤ ≤ a ⁻¹ᵁ U),
          a.appLE U ⊤ e = b.appLE U ⊤ (h ▸ e) := by
        intro a b h e; subst h; rfl
      have hres : ((BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A'.1.hom)).appLE
          E.support.compl ⊤ hA' =
          U.topIso.inv ≫ ((BigFppfOver.toScheme B integerBase hZ).map
            (yoneda.preimage A.1.hom)).appTop := by
        rw [hgen' _ _ hA'map hA']
        refine (Scheme.Hom.appLE_comp_appLE
          ((BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom)) U.ι U ⊤ ⊤
          (Scheme.Opens.ι_preimage_self U).ge (fun _ _ => trivial)).symm.trans ?_
        congr 1
        · refine (Scheme.Opens.ι_appLE U U ⊤ _).trans ?_
          rw [Scheme.Opens.topIso_inv]
          exact congrArg _ (congrArg _ (Subsingleton.elim _ _))
        · exact Scheme.Hom.appLE_eq_app _
      -- the site morphism `A ⟶ C ⟶ Sb` is `A ⟶ V° ⟶ V ⟶ P ⟶ Sb`
      have hsite : k ≫ yoneda.preimage (C.1.hom ≫ p.hom) =
          yoneda.preimage A.1.hom ≫ ι ≫ v ≫ pv := by
        apply yoneda.map_injective
        rw [Functor.map_comp, Functor.map_preimage, Functor.map_comp, Functor.map_preimage,
          Functor.map_comp, Functor.map_comp]
        have e := congrArg (· ≫ p.hom) hk
        exact (Category.assoc _ _ _).symm.trans (e.trans ((Category.assoc _ _ _).trans
          (congrArg (A.1.hom ≫ ·) (congrArg (yoneda.map ι ≫ ·) hq'.w))))
      have key1 : ∀ s, ((BigFppfOver.toScheme B integerBase hZ).map
          (yoneda.preimage (C.1.hom ≫ g.hom))).appTop s =
          (MvPolynomial.eval₂Hom (pullbackToGlobalFunctions B integerBase hZ W X.base p) r
            ((Scheme.ΓSpecIso _).hom s)).1 (op C) := fun s =>
        congrArg (fun φ => (φ s).1 (op C)) (pullbackToGlobalFunctions_ratioMap X.base W p r)
      have key2 : ∀ P', ((BigFppfOver.toScheme B integerBase hZ).map
          (k ≫ yoneda.preimage (C.1.hom ≫ g.hom))).appTop ((Scheme.ΓSpecIso _).inv P') =
          ((BigFppfOver.toScheme B integerBase hZ).map k).appTop
            ((MvPolynomial.eval₂Hom (pullbackToGlobalFunctions B integerBase hZ W X.base p) r
              P').1 (op C)) := by
        intro P'
        rw [Functor.map_comp]
        change ((BigFppfOver.toScheme B integerBase hZ).map k).appTop
          (((BigFppfOver.toScheme B integerBase hZ).map
            (yoneda.preimage (C.1.hom ≫ g.hom))).appTop _) = _
        refine congrArg (fun x => ((BigFppfOver.toScheme B integerBase hZ).map k).appTop x)
          ((key1 _).trans ?_)
        rw [Iso.inv_hom_id_apply]
      have hring : ((BigFppfOver.toScheme B integerBase hZ).map
            (k ≫ yoneda.preimage (C.1.hom ≫ g.hom))).appTop.hom.comp
            (Scheme.ΓSpecIso _).inv.hom =
          ((BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom) ≫
            ζ).appTop.hom.comp
            (Scheme.ΓSpecIso _).inv.hom := by
        apply MvPolynomial.ringHom_ext
        · intro a
          have l1 : ((BigFppfOver.toScheme B integerBase hZ).map
              (k ≫ yoneda.preimage (C.1.hom ≫ g.hom))).appTop
              ((Scheme.ΓSpecIso _).inv (MvPolynomial.C a)) =
              ((BigFppfOver.toScheme B integerBase hZ).map k).appTop
                (((BigFppfOver.toScheme B integerBase hZ).map
                  (yoneda.preimage (C.1.hom ≫ p.hom))).appTop a) := by
            rw [key2, MvPolynomial.eval₂Hom_C]
            rfl
          have l2 : ((BigFppfOver.toScheme B integerBase hZ).map k).appTop
                (((BigFppfOver.toScheme B integerBase hZ).map
                  (yoneda.preimage (C.1.hom ≫ p.hom))).appTop a) =
              ((BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom)).appTop
                (U.ι.appTop (((BigFppfOver.toScheme B integerBase hZ).map v).appTop
                  (((BigFppfOver.toScheme B integerBase hZ).map pv).appTop a))) := by
            rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Functor.map_comp, hsite]
            simp only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
            rfl
          have l4 : U.topIso.inv (ψ (MvPolynomial.C a)) =
              U.ι.appTop (((BigFppfOver.toScheme B integerBase hZ).map v).appTop
                (((BigFppfOver.toScheme B integerBase hZ).map pv).appTop a)) := by
            rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Scheme.Opens.topIso_inv,
              Scheme.Opens.ι_appTop]
            exact presheaf_map_map_apply _ _ _ _ _
          refine l1.trans (l2.trans ?_)
          change _ = ((BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage A.1.hom)).appTop
            (ζ.appTop _)
          exact congrArg (fun x => ((BigFppfOver.toScheme B integerBase hZ).map
            (yoneda.preimage A.1.hom)).appTop x) ((hζapp _).trans l4).symm
        · intro j
          have m1 : ((BigFppfOver.toScheme B integerBase hZ).map
              (k ≫ yoneda.preimage (C.1.hom ≫ g.hom))).appTop
              ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j)) =
              (Scheme.Γ.map ((BigFppfOver.toScheme B integerBase hZ).map k).op).hom
                (ratioAt B integerBase hZ X.total D hD.1 (tl j) C) := by
            rw [key2, MvPolynomial.eval₂Hom_X']
            rfl
          refine m1.trans ((hID j).trans ((congrArg (fun φ => φ.hom (f j)) hres).trans ?_))
          exact congrArg (fun x => ((BigFppfOver.toScheme B integerBase hZ).map
            (yoneda.preimage A.1.hom)).appTop x)
            ((hζapp _).trans (congrArg _ (MvPolynomial.eval₂Hom_X' _ _ _))).symm
      apply ext_of_isAffine
      refine (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n)
        Γ((BigFppfOver.toScheme B integerBase hZ).obj X.base, ⊤)))).inv).1 ?_
      exact CommRingCat.hom_ext hring
    · rw [← hy₀]
      have e1 := congrFun (pointsMap_comp B integerBase hZ _ φW iW.hom) y₀
      have e2 := congrFun (pointsMap_comp B integerBase hZ _ (yoneda.map ι) q) y₀
      exact e1.symm.trans e2
  have h1 := mem_schematicLocus_of_hasRelativeDimensionAt_zero B integerBase hZ W.2
    (affineSpaceOver X.base n) g.hom hg1 hg2 w hw
  rw [← hwq]
  exact mem_range_pointsMap_schematicLocus_of_isOpenImmersion B integerBase hZ X.total.2 W.2
    iW.hom (isOpenSubspace_openComplement B integerBase hZ X.total.2 D.1 D.2).2 h1
end Proof

open Space in
/-- **P3 of the 0E6F route, given piece (c).** Let `X` be a family of curves over an affine
Noetherian base, `P` a closed point of the base and `V` the fibre. If `D₁, D₂` are relative
effective Cartier divisors of `X` restricting to good divisors `E₁, E₂` of `V` with disjoint
supports, then `X` is a scheme over a Zariski neighbourhood of `P`: every point of the fibre lies
off `E₁` or off `E₂`, hence in the schematic locus (`mem_schematicLocus_of_isGoodDivisor`), and
properness spreads this to an open of the base
(`exists_open_isRepresentable_of_forall_mem_schematicLocus`). -/
theorem schemeNearFibreOfGoodDivisors_of_fibreDivisorSheafComparison
    (hc : FibreDivisorSheafComparison B hZ) :
    SchemeNearFibreOfGoodDivisors B hZ (IsGoodFibreDivisor B hZ) := by
  intro X hA hN P hP V v q hq D₁ D₂ E₁ E₂ hD₁ hD₂ hDE₁ hDE₂ hdisj hg₁ hg₂
  have := hA
  have : IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj X.base) :=
    { toIsLocallyNoetherian := hN }
  refine exists_open_isRepresentable_of_forall_mem_schematicLocus X P V v q hq fun y => ?_
  by_cases h₁ : pointsToScheme B integerBase hZ V y ∈ E₁.support.compl
  · exact mem_schematicLocus_of_isGoodDivisor hc fibreRatioRingHomFinite
      (rangeLeOpenComplementOfPreimage B hZ) X hA hN P hP V v q hq D₁ hD₁ E₁ hDE₁ hg₁ y h₁
  · have h₂ : pointsToScheme B integerBase hZ V y ∈ E₂.support.compl := fun hy₂ =>
      h₁ fun hy₁ => Set.disjoint_left.1 hdisj hy₁ hy₂
    exact mem_schematicLocus_of_isGoodDivisor hc fibreRatioRingHomFinite
      (rangeLeOpenComplementOfPreimage B hZ) X hA hN P hP V v q hq D₂ hD₂ E₂ hDE₂ hg₂ y h₂


/-- **P3 of the 0E6F route.** A family of curves over an affine Noetherian base is a scheme over a
Zariski neighbourhood of a closed point whose fibre carries two good divisors with disjoint
supports, cut out by relative effective Cartier divisors. -/
theorem schemeNearFibreOfGoodDivisors :
    SchemeNearFibreOfGoodDivisors B hZ (IsGoodFibreDivisor B hZ) :=
  schemeNearFibreOfGoodDivisors_of_fibreDivisorSheafComparison B hZ
    (fibreDivisorSheafComparison B hZ)

end AlgebraicGeometry.C1590Private

end
