module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus

/-!
# A codimension-zero point of a quasi-separated algebraic space lies in a scheme

Let `X` be a quasi-separated algebraic space over a scheme `S` and let `x ∈ |X|` be a point of
codimension `0`, that is, one whose local ring has dimension zero. Then some open subspace of
`X` containing `x` is a scheme. This is the final statement of [Stacks Project, Tag 0ADC], and it
is stated here together with the equivalence of the tag's three conditions.

## Main results

* `tfae_localRingDimension_eq_zero_and_exists_isRepresentable_isOpenSubspace` (in namespace
  `AlgebraicGeometry.Space`): the equivalence of conditions (1), (2) and (3) of Stacks 0ADC, and
  the final statement that such a point lies in an open subspace which is a scheme.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_localRingDimension_eq_zero`:
  a point of codimension `0` of a quasi-separated algebraic space over `S` lies in an open
  subspace which is a scheme.

## References

* [Stacks Project, Tag 0ADC](https://stacks.math.columbia.edu/tag/0ADC)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
* [Stacks Project, Tag 0BAS](https://stacks.math.columbia.edu/tag/0BAS)
* [Stacks Project, Tag 0AD0](https://stacks.math.columbia.edu/tag/0AD0)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 0A4H](https://stacks.math.columbia.edu/tag/0A4H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A point mapped along `α` and then `β` lies in the range of the points map of `α ≫ β`. -/
private theorem mem_range_pointsMap_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ G) (β : G ⟶ H) {a : points B S hS F} {y : points B S hS G} {z : points B S hS H}
    (ha : pointsMap B S hS F α a = y) (hy : pointsMap B S hS G β y = z) :
    z ∈ Set.range (pointsMap B S hS F (α ≫ β)) :=
  ⟨a, by rw [pointsMap_comp_apply, ha, hy]⟩

include hZ

/-- A point of codimension `0` of a quasi-separated algebraic space lies in an open subspace
which is a scheme. -/
theorem exists_isRepresentable_isOpenSubspace_of_localRingDimension_eq_zero
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (x : points B S hS F) (hx : localRingDimension B S hS x = 0) :
    ∃ G : Subfunctor F, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  classical
  have hdec : IsDecentSpace B S hS F :=
    isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ F hF
      (isZariskiLocallyQuasiSeparatedOver_of_quasiSeparated B S hS hZ F hF hqs)
  obtain ⟨W, b, hWaff, hbEt, w, hw⟩ := exists_affine_etale_chart_at_point B S hS F hF x
  have hb : IsEtale B S hS b := isEtale_of_presheaf_etale B S hS hbEt
  have hWalg : IsAlgebraicSpace B S hS (yoneda.obj W) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hWaff
  have hWqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj W) :=
    quasiSeparatedSpace_of_isAffine _
  have hfib : {y : points B S hS (yoneda.obj W) |
      pointsMap B S hS (yoneda.obj W) b y = x}.Finite :=
    ((isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS F hF).mp hdec x
      W hWaff b hbEt).1
  have hbqs : IsQuasiSeparated B S hS b :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ hWalg
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj W) hZ
        ⟨W, hWqs, ⟨Functor.RepresentableBy.yoneda W⟩⟩) b
  have hblft : IsLocallyOfFiniteType B S hS b :=
    isLocallyOfFiniteType_of_isEtale B S hS hF hb
  obtain ⟨U, V, g, hUopen, hVopen, hcomm, -, hfibsub, hgfin⟩ :=
    exists_isOpenSubspace_isFinite_openRestriction_of_finite_setFibre B S hS hWalg hF b hbqs
      hblft hqs x hx hfib
  have hValg : IsAlgebraicSpace B S hS V.toFunctor := hVopen.1
  obtain ⟨Z, j, e, hjopen, -⟩ := exists_openImmersion_of_isOpenSubspace B S hS W U hUopen
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map j) := hjopen
  have hZqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Z) :=
    ((BigFppfOver.toScheme B S hS).map j).isOpenEmbedding.quasiSeparatedSpace
  have hgEt : IsEtale B S hS g := by
    refine isEtale_of_comp_mono B S hS g V.ι ?_
    rw [hcomm]
    exact isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS hUopen.2) hb
  have hχEt : IsEtale B S hS (e.hom ≫ g) :=
    isEtale_comp B S hS (isEtale_of_isIso B S hS e.hom) hgEt
  have hχfin : IsFinite B S hS (e.hom ≫ g) :=
    isFinite_of_isPullback B S hS
      (IsPullback.of_horiz_isIso_mono (fst := e.hom) (snd := e.hom ≫ g) (f := g)
        (g := 𝟙 V.toFunctor) ⟨by simp⟩) hgfin
  obtain ⟨V', ψ, hV'open, hψχ, hψsurj, hψEt, hV'image⟩ :=
    exists_isOpenSubspace_etaleImage B S hS hValg Z (e.hom ≫ g)
      (presheaf_etale_of_isEtale B S hS hχEt)
  have hV'alg : IsAlgebraicSpace B S hS V'.toFunctor := hV'open.1
  have hψfin : IsFinite B S hS ψ :=
    isFinite_of_isPullback B S hS (isPullback_id_of_comp_mono ψ V'.ι hψχ) hχfin
  obtain ⟨uU, huU⟩ := hfibsub (show pointsMap B S hS (yoneda.obj W) b w = x from hw)
  have hxVx : pointsMap B S hS V.toFunctor V.ι (pointsMap B S hS U.toFunctor g uU) = x := by
    rw [← pointsMap_comp_apply, hcomm, pointsMap_comp_apply, huU, hw]
  have hxVmem : pointsMap B S hS U.toFunctor g uU ∈
      Set.range (pointsMap B S hS V'.toFunctor V'.ι) := by
    rw [hV'image]
    refine mem_range_pointsMap_comp B S hS e.hom g
      (a := pointsMap B S hS U.toFunctor e.inv uU) ?_ rfl
    rw [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id, id_eq]
  obtain ⟨x'', hx''⟩ := hxVmem
  have hx''dim : localRingDimension B S hS x'' = 0 := by
    have hEt : IsEtale B S hS (V'.ι ≫ V.ι) :=
      isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS hV'open.2)
        (isEtale_of_isOpenImmersion B S hS hVopen.2)
    have hdim := localRingDimension_pointsMap_of_etale B S hS hV'alg hF (V'.ι ≫ V.ι) hEt x''
    rw [pointsMap_comp_apply, hx'', hxVx, hx] at hdim
    exact hdim.symm
  obtain ⟨H, hHopen, hHrep, hHmem⟩ :=
    exists_isRepresentable_isOpenSubspace_mem_range B S hS hV'alg ψ hZqs hψfin
      (isEtale_of_presheaf_etale B S hS hψEt)
      (isSurjective_of_presheafSurjective B S hS ψ hψsurj) x'' hx''dim
  obtain ⟨K, hKopen, hKrep, hKimage⟩ :=
    exists_isOpenSubspace_isRepresentable_of_isOpenSubspace B S hS hValg hV'open hHopen hHrep
  obtain ⟨G, hGopen, hGrep, hGimage⟩ :=
    exists_isOpenSubspace_isRepresentable_of_isOpenSubspace B S hS hF hVopen hKopen hKrep
  refine ⟨G, hGopen, hGrep, ?_⟩
  obtain ⟨h, hh⟩ := hHmem
  have hKmem : pointsMap B S hS U.toFunctor g uU ∈
      Set.range (pointsMap B S hS K.toFunctor K.ι) := by
    rw [hKimage]
    exact mem_range_pointsMap_comp B S hS _ _ hh hx''
  obtain ⟨k, hk⟩ := hKmem
  rw [hGimage]
  exact mem_range_pointsMap_comp B S hS _ _ hk hxVx

/-- Let `x` be a point of a quasi-separated algebraic space over `S`. The
following are equivalent:
1. `x` is a point of codimension `0` on the space, that is, by Tag 04NA, the dimension of the
   local ring there is `0`;
2. the local ring of the space at `x` has dimension `0`, in the chart-wise form of Tag 0BAM:
   every étale scheme chart has a local ring of Krull dimension `0` at each point above `x`;
3. `x` is a generic point of an irreducible component of the space of points.

If these hold, then some open subspace of the space containing `x` is a scheme. -/
@[stacks 0ADC]
theorem tfae_localRingDimension_eq_zero_and_exists_isRepresentable_isOpenSubspace
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F) (x : points B S hS F) :
    [localRingDimension B S hS x = 0, AllChartsLocalRingDimension B S hS x 0,
        x ∈ genericPoints (points B S hS F)].TFAE ∧
      (localRingDimension B S hS x = 0 →
        ∃ G : Subfunctor F, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
          x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι)) := by
  refine ⟨?_, exists_isRepresentable_isOpenSubspace_of_localRingDimension_eq_zero B S hS hZ F
    hF hqs x⟩
  tfae_have 1 ↔ 2 :=
    (localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hF x 0).trans
      (hasChartLocalRingDimension_iff_allChartsLocalRingDimension B S hS hF x 0)
  tfae_have 1 ↔ 3 :=
    localRingDimension_eq_zero_iff_mem_genericPoints_of_quasiSeparated B S hS hZ F hF hqs x
  tfae_finish

end AlgebraicGeometry.Space

end
