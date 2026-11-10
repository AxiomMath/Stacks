module

public import StacksFrontier.AlgebraicGeometry.Stacks.StackFlatteningByBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.BlowupRepresentableScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.ChartFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenChartCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFinitePresentationFromFlat

/-!
# Flattening an algebraic stack over a scheme by blowing up (Stacks 0CQ4, scheme base)

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to the algebraic space represented by a
quasi-compact quasi-separated scheme `T`, of finite type and quasi-separated, and let `V ⊆ Y` be a
quasi-compact open with `𝒳_V ⟶ V` flat and locally of finite presentation. Then the conclusion
of [Stacks, Tag 0CQ4] holds: there are a `V`-admissible blowup `b : Y' ⟶ Y` and a closed
substack `𝒳' ⊆ 𝒳_{Y'}` with `𝒳'_V = 𝒳_V` which is flat and of finite presentation over `Y'`.

This is the source's proof with [Stacks, Tag 087E] replaced, the base being a scheme, by its scheme
case [Stacks, Tag 081R]
(`exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`): an affine
smooth chart `U ⟶ 𝒳` gives a morphism of schemes `g : U ⟶ T`, flat and locally of finite
presentation over the open `O ⊆ T` underlying `V`; 081R gives a centre `K` along which the strict
transform of `U` is flat and of finite presentation; the scheme blowup of `T` in `K` is the blowup
of `Y` along the closed subspace cut out by `K`
(`AlgebraicGeometry.Space.isBlowupAlong_closedSubspaceOfIdeal_schemeSpaceMap`), and the strict
transform, a closed subscheme of the chart `U ×_T Bl_K T` of `𝒳_{Y'}`, contains the complement of
the exceptional divisor and cuts out the closed substack.

## Main results

* `exists_isAdmissibleBlowup_isClosedSubstack_isFlat_isFinitePresentation_of_yoneda`:
  [Stacks, Tag 0CQ4] over a scheme, unregistered.
* `AlgebraicGeometry.Space.exists_opens_eq_openSubspaceOfPoints_pointsToScheme`: an open subspace
  of a represented space is cut out by an open of the scheme.
* `AlgebraicGeometry.Space.morphismRestrict_of_holdsOnEveryEtaleChart`: a property of the base
  change of a represented morphism to a represented open is a property of the restriction.

## References

* [Stacks Project, Tag 0CQ4](https://stacks.math.columbia.edu/tag/0CQ4)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An open subspace of the algebraic space represented by `T` is cut out by the points over an
open of `T`.** Its point set is open, hence scheme open (Stacks 03BY), and an open subspace is
determined by its points (Stacks 03BZ). -/
theorem exists_opens_eq_openSubspaceOfPoints_pointsToScheme (T : BigFppfOver B S hS)
    (V : Subfunctor (yoneda.obj T)) (hV : IsOpenSubspace B S hS V) :
    ∃ O : ((BigFppfOver.toScheme B S hS).obj T).Opens,
      V = openSubspaceOfPoints B S hS (yoneda.obj T) (pointsToScheme B S hS T ⁻¹' (O : Set _)) := by
  let := pointTopology B S hS (yoneda.obj T)
  have ho : IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2
  obtain ⟨O, hO, hmem⟩ := (isOpen_yoneda_iff_isSchemeOpen B S hS T _).1 ho
  refine ⟨⟨O, hO⟩, (eq_openSubspaceOfPoints_range_pointsMap B S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) V hV).trans ?_⟩
  congr 1
  ext x
  induction x using Quot.ind with
  | mk p => exact hmem p

/-- The inclusion of an open of the scheme `T`, as a morphism of represented presheaves, is a
monomorphism. -/
theorem mono_yoneda_map_openSubHom (T : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj T).Opens) : Mono (yoneda.map (openSubHom T O)) := by
  have : Mono (openSubHom T O) := (BigFppfOver.toScheme B S hS).mono_of_mono_map (by
    rw [toScheme_map_openSubHom B S hS]
    exact inferInstanceAs (Mono O.ι))
  exact Functor.map_mono yoneda _

/-- **The base change of a represented morphism to a represented open.** For `g : U ⟶ T` and an
open `O ⊆ T`, the square of represented presheaves with corner `g⁻¹(O)` over the range of `O` is
cartesian. -/
theorem isPullback_yoneda_openSubHomOfRestrict {U T : BigFppfOver B S hS} (g : U ⟶ T)
    (O : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    haveI := mono_yoneda_map_openSubHom T O
    IsPullback (yoneda.map (openSubHomOfRestrict g O) ≫
        Subfunctor.toRange (yoneda.map (openSubHom T O)))
      (yoneda.map (openSubHom U ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O)))
      (Subfunctor.range (yoneda.map (openSubHom T O))).ι (yoneda.map g) := by
  have := mono_yoneda_map_openSubHom T O
  refine ((isPullback_openSubHomOfRestrict g O).map yoneda).flip.of_iso (Iso.refl _)
    (asIso (Subfunctor.toRange (yoneda.map (openSubHom T O)))) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [Subfunctor.toRange_ι]
  · simp

/-- **A property of the base change of a represented morphism to a represented open is a property
of the restriction.** If `P` holds on every étale chart of the base change of `g : U ⟶ T` to the
range of an open `O ⊆ T`, then `P` holds for `g|_O`: the identity of `g⁻¹(O)` and the
isomorphism of `O` onto its range form an étale chart. -/
theorem morphismRestrict_of_holdsOnEveryEtaleChart {P : MorphismProperty Scheme.{u}}
    {U T : BigFppfOver B S hS} (g : U ⟶ T) (O : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (h : haveI := mono_yoneda_map_openSubHom T O
      HoldsOnEveryEtaleChart B S hS P (yoneda.map (openSubHomOfRestrict g O) ≫
        Subfunctor.toRange (yoneda.map (openSubHom T O)))) :
    P ((BigFppfOver.toScheme B S hS).map g ∣_ O) := by
  have := mono_yoneda_map_openSubHom T O
  exact h _ _ (yoneda.map (𝟙 _)) (Subfunctor.toRange (yoneda.map (openSubHom T O)))
    (openSubHomOfRestrict g O) (presheaf_yoneda_map_id_etale B S hS _)
    ((isEtale_iff_presheaf_of_yoneda B S hS _).1 (isEtale_of_isIso B S hS _)) (by simp)

/-- A property holding on every étale chart of `k` holds on every étale chart of `e ≫ k` for an
isomorphism `e`. -/
theorem holdsOnEveryEtaleChart_iso_comp {P : MorphismProperty Scheme.{u}}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e] (k : G ⟶ H)
    (hk : HoldsOnEveryEtaleChart B S hS P k) : HoldsOnEveryEtaleChart B S hS P (e ≫ k) :=
  fun U V a b h ha hb hw => hk U V (a ≫ e) b h (isEtale_of_isIso B S hS e U a ha) hb
    (by rw [hw, Category.assoc])

/-- **A property of a closed subscheme over a scheme, read on the closed subspace it cuts out.**
If `P` is étale local on the source and target and `V(J) ⟶ Q ⟶ R` has `P`, then `P` holds on every
étale chart of the inclusion of `Z_J` followed by `Q ⟶ R`. -/
theorem holdsOnEveryEtaleChart_closedSubspaceOfIdeal_ι_comp {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) {Q R : BigFppfOver B S hS}
    (J : ((BigFppfOver.toScheme B S hS).obj Q).IdealSheafData) (m : Q ⟶ R)
    (h : P (J.subschemeι ≫ (BigFppfOver.toScheme B S hS).map m)) :
    HoldsOnEveryEtaleChart B S hS P ((closedSubspaceOfIdeal Q J).1.ι ≫ yoneda.map m) := by
  set j := closedSubschemeOverι B S hS Q J with hjdef
  have : Mono j := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono J.subschemeι))
  have hι : (Subfunctor.range (yoneda.map j)).ι = inv (Subfunctor.toRange (yoneda.map j)) ≫
      yoneda.map j := (IsIso.eq_inv_comp _).2 (Subfunctor.toRange_ι _).symm
  change HoldsOnEveryEtaleChart B S hS P ((Subfunctor.range (yoneda.map j)).ι ≫ yoneda.map m)
  rw [hι, Category.assoc, ← Functor.map_comp]
  refine holdsOnEveryEtaleChart_iso_comp _ _
    (holdsOnEveryEtaleChart_yoneda_map B S hS hP _ ?_)
  rw [Functor.map_comp]
  exact h

/-- The points of the inverse image of a closed subspace are the inverse image of its points. -/
theorem subspacePointSet_preimageClosedSubspace {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) :
    subspacePointSet B S hS Y.1 (preimageClosedSubspace f Z).1 =
      pointsMap B S hS Y.1 f.hom ⁻¹' subspacePointSet B S hS X.1 Z.1 :=
  range_pointsMap_preimage_ι B S hS _ _

/-- **The strict transform of a chart contains the complement of the exceptional divisor**, as
closed and open subspaces of the represented space of the chart `U ×_T Bl_K T`: the open
complement of the inverse image of `Z_K` is the range of the complement of the exceptional
divisor, which lies in its scheme-theoretic closure, cut out by the strict transform ideal. -/
theorem openComplement_preimage_le_closedSubspaceOfIdeal_strictTransform
    {U T : BigFppfOver B S hS} (g : U ⟶ T)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) :
    (openComplementOfClosedSubspace B S hS (schemeSpace (blowUpChartObj g K))
      (preimageClosedSubspace (schemeSpaceMap (blowUpChartSnd g K))
        (preimageClosedSubspace (schemeSpaceMap (blowUpObjHom T K))
          (closedSubspaceOfIdeal T K)))).1 ≤
      (closedSubspaceOfIdeal (blowUpChartObj g K)
        (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
          (_root_.AlgebraicGeometry.blowUpToBase K)
          (_root_.AlgebraicGeometry.exceptionalIdeal K))).1 := by
  let O : ((BigFppfOver.toScheme B S hS).obj T).Opens :=
    ⟨(K.support : Set _)ᶜ, K.support.isClosed.isOpen_compl⟩
  have hK : K.supportSet = (O : Set _)ᶜ := (compl_compl _).symm
  set m := blowUpChartSnd g K ≫ blowUpObjHom T K with hmdef
  let C := openComplementOfClosedSubspace B S hS (schemeSpace (blowUpChartObj g K))
    (preimageClosedSubspace (schemeSpaceMap (blowUpChartSnd g K))
      (preimageClosedSubspace (schemeSpaceMap (blowUpObjHom T K)) (closedSubspaceOfIdeal T K)))
  have hC : C.1 = openSubspaceOfPoints B S hS (yoneda.obj (blowUpChartObj g K))
      (pointsToScheme B S hS _ ⁻¹' ((BigFppfOver.toScheme B S hS).map m ⁻¹ᵁ O : Set _)) := by
    refine (eq_openSubspaceOfPoints_range_pointsMap B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _) C.1 C.2).trans ?_
    congr 1
    have hpts : subspacePointSet B S hS (schemeSpace T).1 (closedSubspaceOfIdeal T K).1 =
        pointsToScheme B S hS T ⁻¹' (K.support : Set _) :=
      subspacePointSet_closedSubspaceOfIdeal T K
    have h1 : Set.range (pointsMap B S hS _ C.1.ι) =
        (subspacePointSet B S hS (schemeSpace (blowUpChartObj g K)).1
          (preimageClosedSubspace (schemeSpaceMap (blowUpChartSnd g K))
            (preimageClosedSubspace (schemeSpaceMap (blowUpObjHom T K))
              (closedSubspaceOfIdeal T K))).1)ᶜ :=
      subspacePointSet_openComplement B S hS _ _
    rw [subspacePointSet_preimageClosedSubspace, subspacePointSet_preimageClosedSubspace,
      hpts] at h1
    refine h1.trans ?_
    ext x
    change ¬ pointsToScheme B S hS T (pointsMap B S hS (yoneda.obj (blowUpObj T K))
        (yoneda.map (blowUpObjHom T K)) (pointsMap B S hS (yoneda.obj (blowUpChartObj g K))
          (yoneda.map (blowUpChartSnd g K)) x)) ∈ (K.support : Set _) ↔
      pointsToScheme B S hS (blowUpChartObj g K) x ∈
        ((BigFppfOver.toScheme B S hS).map m ⁻¹ᵁ O : Set _)
    rw [pointsToScheme_pointsMap, pointsToScheme_pointsMap B S hS (blowUpChartSnd g K) x, hmdef,
      Functor.map_comp]
    exact Iff.rfl
  change C.1 ≤ _
  rw [hC, openSubspaceOfPoints_preimage_pointsToScheme]
  refine (range_le_schemeTheoreticImageSubfunctor B S hS _).trans ?_
  rw [schemeTheoreticImageSubfunctor_yoneda_openSubHom, preimage_eq_exceptionalComplement g O K hK,
    Stacks.StrictTransform.ideal_eq_ker_ι]
  exact le_rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **[Stacks, Tag 0CQ4] over a quasi-compact quasi-separated scheme.** Let `f : 𝒳 ⟶ Y` be a
1-morphism from an algebraic stack to the algebraic space represented by `T`, with `Y`
quasi-compact and quasi-separated, `f` of finite type and quasi-separated, and let `V ⊆ Y` be a
quasi-compact open with `𝒳_V ⟶ V` flat and locally of finite presentation. Then there are a
`V`-admissible blowup `b : Y' ⟶ Y` and a closed substack `𝒳' ⊆ 𝒳_{Y'}` containing every object
over `b⁻¹V` such that `𝒳' ⟶ Y'` is flat and of finite presentation.

The proof is the source's, with [Stacks, Tag 087E] replaced by its scheme case
[Stacks, Tag 081R]: an affine smooth chart `U ⟶ 𝒳` lies over a morphism of schemes `g : U ⟶ T`
which is flat and locally of finite presentation over the open `O` of `T` underlying `V`; 081R
gives a finitely presented centre `K` disjoint from `O` along which the strict transform of `U`
is flat and of finite presentation; the scheme blowup in `K` is the blowup of `Y` along the closed
subspace cut out by `K`, and the strict transform of `U` is a closed subscheme of the chart
`U ×_T Bl_K T` of `𝒳_{Y'}` containing the complement of the exceptional divisor, so it cuts out
the closed substack (Stacks 0507). -/
theorem exists_isAdmissibleBlowup_isClosedSubstack_isFlat_isFinitePresentation_of_yoneda
    (T : BigFppfOver B S hS) (hY : IsAlgebraicSpace B S hS (yoneda.obj T))
    (hYqc : Space.IsQuasiCompactSpace B S hS (yoneda.obj T))
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (yoneda.obj T))
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj T) hY)
    (hft : IsFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (V : Subfunctor (yoneda.obj T)) (hV : Space.IsOpenSubspace B S hS V)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hflat : IsFlat B S hS
      (twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    (hlfp : IsLocallyOfFinitePresentation B S hS
      (twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ ⟨yoneda.obj T, hY⟩),
      Space.IsAdmissibleBlowup B S hS ⟨V, hV⟩ b ∧
        ∃ P : ObjectProperty (twoFibreProductSquare B S hS
            (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).pt.val.val.obj,
          IsClosedSubstack _ P ∧
          (∀ x, ((twoFibreProductSquare B S hS
              (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj
                x).fiber.as ∈ (V.preimage b.hom).obj (Opposite.op ((twoFibreProductSquare B S hS
                  (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj
                    x).base) →
            P x) ∧
          ∀ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased _ P),
            IsFlat B S hS (fullSubcategoryInclusion _ P hP ≫ (twoFibreProductSquare B S hS
              (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst) ∧
            IsFinitePresentation B S hS (fullSubcategoryInclusion _ P hP ≫
              (twoFibreProductSquare B S hS
                (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst) := by
  classical
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) :=
    Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hYqc
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T) :=
    (Space.isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS B.contains_terminal
      T).1 hYqs
  obtain ⟨U, hUaff, c, φ, hcsm, hcsu, ⟨ec⟩, hφft, -, -⟩ :=
    Stack.exists_isAffine_smooth_surjective_chart B S hS hY hYqc hYqs f hft
  have hUsp := isAlgebraicSpace_yoneda B S hS U
  obtain ⟨g, rfl⟩ : ∃ g : U ⟶ T, yoneda.map g = φ := ⟨yoneda.preimage φ, yoneda.map_preimage φ⟩
  -- `V` is the range of an open `O` of `T`
  obtain ⟨O, hO⟩ := Space.exists_opens_eq_openSubspaceOfPoints_pointsToScheme T V hV
  obtain rfl : V = Subfunctor.range (yoneda.map (Space.openSubHom T O)) :=
    hO.trans (Space.openSubspaceOfPoints_preimage_pointsToScheme T O)
  have := Space.mono_yoneda_map_openSubHom T O
  -- `g` is flat and locally of finite presentation over `O`
  obtain ⟨hφVfl, hφVlfp⟩ := Stack.isFlat_isLocallyOfFinitePresentation_pullback_fst_of_isFlat
    B S hS hY hV.1 hUsp (isAlgebraicSpace_yoneda B S hS _) f _ c (yoneda.map g) ec hcsm
    (Space.isPullback_yoneda_openSubHomOfRestrict g O) _
    (isTwoFibreProduct_twoFibreProductSquare B S hS _ f) hflat hlfp
  have hgfl : Flat ((BigFppfOver.toScheme B S hS).map g ∣_ O) :=
    Space.morphismRestrict_of_holdsOnEveryEtaleChart g O hφVfl
  have hglfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g ∣_ O) :=
    Space.morphismRestrict_of_holdsOnEveryEtaleChart g O hφVlfp
  -- the scheme-level hypotheses of Stacks 081R
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) :=
    (Space.isLocallyOfFiniteType_yoneda_map_iff B S hS g).1 hφft.1
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map g) := quasiCompact_of_compactSpace _
  have : QuasiSeparated ((BigFppfOver.toScheme B S hS).map g) := inferInstance
  have hOc : IsCompact (O : Set ((BigFppfOver.toScheme B S hS).obj T)) := by
    have h := Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (Space.isQuasiCompactSpace_of_iso B S hS
        (asIso (Subfunctor.toRange (yoneda.map (Space.openSubHom T O)))).symm hVqc)
    exact isCompact_iff_compactSpace.2 h
  obtain ⟨K, hKfp, hKdisj, -, hKflat, hKfp'⟩ :=
    exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase
      ((BigFppfOver.toScheme B S hS).map g) O hOc hgfl hglfp
  -- the blowup of `Y` along the closed subspace cut out by `K`
  have hb := Space.isBlowupAlong_closedSubspaceOfIdeal_schemeSpaceMap T K hKfp
  have hdisj : Disjoint (Space.subspacePointSet B S hS (yoneda.obj T)
      (Subfunctor.range (yoneda.map (Space.openSubHom T O))))
      (Space.subspacePointSet B S hS (yoneda.obj T) (Space.closedSubspaceOfIdeal T K).1) := by
    rw [Space.subspacePointSet_closedSubspaceOfIdeal, Space.subspacePointSet,
      ← Space.openSubspaceOfPoints_preimage_pointsToScheme,
      Space.range_pointsMap_ι_openSubspaceOfPoints]
    exact hKdisj.preimage _
  refine ⟨AlgebraicGeometry.schemeSpace (Space.blowUpObj T K),
    AlgebraicGeometry.schemeSpaceMap (Space.blowUpObjHom T K),
    ⟨Space.closedSubspaceOfIdeal T K, Space.isFinitePresentation_closedSubspaceOfIdeal T K hKfp,
      hdisj, hb⟩, ?_⟩
  -- the chart `U ×_T Bl_K T ⟶ 𝒳_{Y'}`
  let Q := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS
    (AlgebraicGeometry.schemeSpace (Space.blowUpObj T K)).2 hY
      (yoneda.map (Space.blowUpObjHom T K))) f
  have hQ : Bicategory.IsTwoFibreProduct Q := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  have hP := isAlgebraicSpace_yoneda B S hS (Space.blowUpChartObj g K)
  have hsq : IsPullback (yoneda.map (Space.blowUpChartSnd g K))
      (yoneda.map (Space.blowUpChartFst g K))
      (yoneda.map (Space.blowUpObjHom T K)) (yoneda.map g) :=
    ((Space.isPullback_blowUpChart g K).map yoneda).flip
  obtain ⟨c', hc'sm, hc'su, ⟨ec'⟩, -⟩ := Stack.exists_smooth_surjective_baseChangedChart B S hS
    hY (AlgebraicGeometry.schemeSpace (Space.blowUpObj T K)).2 hUsp hP f _ c (yoneda.map g) ec hsq
    Q hQ
  -- the closed substack cut out by the strict transform
  have hCfl : Space.IsFlat B S hS ((Space.closedSubspaceOfIdeal (Space.blowUpChartObj g K)
      (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
        (_root_.AlgebraicGeometry.blowUpToBase K)
        (_root_.AlgebraicGeometry.exceptionalIdeal K))).1.ι ≫
      yoneda.map (Space.blowUpChartSnd g K)) :=
    Space.holdsOnEveryEtaleChart_closedSubspaceOfIdeal_ι_comp Flat.isEtaleLocalOnSourceAndTarget
      _ _ hKflat
  have hClfp : Space.IsLocallyOfFinitePresentation B S hS
      ((Space.closedSubspaceOfIdeal (Space.blowUpChartObj g K)
      (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
        (_root_.AlgebraicGeometry.blowUpToBase K)
        (_root_.AlgebraicGeometry.exceptionalIdeal K))).1.ι ≫
      yoneda.map (Space.blowUpChartSnd g K)) :=
    Space.holdsOnEveryEtaleChart_closedSubspaceOfIdeal_ι_comp
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget _ _ hKfp'.1
  obtain ⟨Qp, hQc, hQV, hQfl⟩ :=
    Stack.exists_isClosedSubstack_isFlat_isLocallyOfFinitePresentation_of_openComplement_le
      (A' := AlgebraicGeometry.schemeSpace (Space.blowUpObj T K))
      (P := AlgebraicGeometry.schemeSpace (Space.blowUpChartObj g K))
      Q.fst c' (hc'sm hcsm) (hc'su hcsu)
      (AlgebraicGeometry.schemeSpaceMap (Space.blowUpChartSnd g K)) ⟨ec'⟩
      (Space.preimageClosedSubspace (AlgebraicGeometry.schemeSpaceMap (Space.blowUpObjHom T K))
        (Space.closedSubspaceOfIdeal T K)) hb.isPullbackDefined
      (Space.closedSubspaceOfIdeal (Space.blowUpChartObj g K)
        (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
          (_root_.AlgebraicGeometry.blowUpToBase K)
          (_root_.AlgebraicGeometry.exceptionalIdeal K)))
      (Space.openComplement_preimage_le_closedSubspaceOfIdeal_strictTransform g K) hCfl hClfp
  refine ⟨Qp, hQc, fun x hx => hQV x
    (Space.preimage_le_openComplement_preimage_of_disjoint B S hS _ ⟨_, hV⟩ _ hdisj _ hx),
    fun hP' => ?_⟩
  obtain ⟨-, hP'', hci⟩ := hQc
  obtain ⟨hqc, hqs'⟩ := isQuasiCompactMorphism_isQuasiSeparated_comp_fst_of_isClosedImmersion
    B S hS f _ hft.2 hqs _ hci
  exact ⟨(hQfl hP').1, (hQfl hP').2, hqc, hqs'⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
