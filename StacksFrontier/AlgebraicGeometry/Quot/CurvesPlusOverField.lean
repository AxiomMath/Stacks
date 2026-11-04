module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesFiniteSingularities
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodalLciPlus
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.StalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedPointInfiniteFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFibrePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The finite singular locus condition on a proper scheme over a field (Stacks 0DZW, part (2))

Let `X` be a proper scheme over a field `k` of dimension at most one, flat and of finite
presentation over `k`. Part (2) of Stacks 0DZW says that the classifying morphism of `X` factors
through the substack `Curves⁺` exactly when `X → Spec(k)` is smooth except at finitely many
points. Read on the family of curves attached to `X → Spec(k)`, the defining condition of
`Curves⁺` is that the reduced closed subspace supported on the non-smooth locus is finite over
`Spec(k)`, and this file proves that this holds exactly when the complement of the smooth locus
of `X → Spec(k)` is a finite set.

## Main results

* `AlgebraicGeometry.Space.isSmoothAt_yoneda_map_iff_smoothAt`: a morphism of schemes of the
  site is smooth at a point, as a morphism of algebraic spaces, exactly when it is smooth there
  as a morphism of schemes.
* `AlgebraicGeometry.Space.isSmoothAt_yoneda_map_iff_mem_smoothLocus`: the same, with the
  scheme side read as membership of the smooth locus.
* `AlgebraicGeometry.isFiniteNonSmoothLocus_curveFamilyOfSchemeMorphism_iff`: **Stacks 0DZW**,
  part (2), on the family of curves attached to a proper flat morphism of finite presentation
  onto the spectrum of a field.

## Implementation notes

The non-smooth points of the family correspond to the points outside the smooth locus of the
morphism of schemes, under the bijection between the points of a represented algebraic space
and those of the representing scheme; at a point, both notions of smoothness are read on the
identity chart.

If the reduced non-smooth locus `Z` is finite over `Spec(k)`, it is locally quasi-finite over
`Spec(k)` and quasi-compact, being a closed subspace of the quasi-compact scheme `X`; over a
one-point base a quasi-compact space locally of finite type is quasi-finite at only finitely many
points, so `|Z|`, and with it the non-smooth locus, is finite. Conversely, if the non-smooth
locus is finite, its reduced induced closed subspace `Z` has finitely many points, so every fibre
of `Z → Spec(k)` is finite and `Z → Spec(k)` is locally quasi-finite; it is proper, being a
closed subspace of a proper family, hence finite by Stacks 0A4X.

## References

* [Stacks Project, Tag 0DZW](https://stacks.math.columbia.edu/tag/0DZW)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism `g` of schemes of the site is smooth, as a morphism of algebraic spaces, at the
point of `|h_U|` corresponding to a point `x` of `U` exactly when `g` is smooth at `x`. -/
theorem isSmoothAt_yoneda_map_iff_smoothAt {U W : BigFppfOver B S hS} (g : U ⟶ W)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    IsSmoothAt B S hS (yoneda.map g) ((pointsEquivScheme B S hS U).symm x) ↔
      InfinitesimalLifting.SmoothAt ((BigFppfOver.toScheme B S hS).map g) x := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj U)) := MorphismProperty.id_mem _ _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · classical
    set p := (pointsEquivScheme B S hS U).symm x with hp
    let r : FieldValuedPoint B S hS (yoneda.obj U) := Quot.out p
    have hr : r.class B S hS (yoneda.obj U) = p := Quot.out_eq p
    let c : EtaleChartAtPoint B S hS (yoneda.map g) p :=
      { U := U
        V := W
        a := 𝟙 _
        b := yoneda.map (𝟙 W)
        h := g
        a_etale := hid
        b_etale := presheaf_yoneda_map_id_etale B S hS W
        comm := by rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
        representative := r
        point := IsLocalRing.closedPoint r.carrier
        maps_to := by rw [pointsMap_id, hr]; rfl }
    have hsrc : c.sourcePoint B S hS = x := by
      show pointsToScheme B S hS U (r.class B S hS (yoneda.obj U)) = x
      rw [hr, hp]
      exact pointsToScheme_pointsEquivScheme_symm B S hS U x
    have hc := (isSmoothAt_iff_holdsOnEveryEtaleChartAtPoint B S hS
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS W) _ _).mp h c
    rw [← hsrc]
    exact (smoothAt_iff_hasRepresentativeWithProperty _ _).mpr hc
  · have := isSmoothAt_pointsMap_of_smoothAt B S hS (isAlgebraicSpace_yoneda B S hS U) (𝟙 _)
      hid (yoneda.map g) g (Category.id_comp _) x h
    rwa [pointsMap_id] at this

/-- For a morphism `g` of schemes of the site locally of finite presentation, the induced
morphism of algebraic spaces is smooth at the point corresponding to `x` exactly when `x` lies
in the smooth locus of `g`. -/
theorem isSmoothAt_yoneda_map_iff_mem_smoothLocus {U W : BigFppfOver B S hS} (g : U ⟶ W)
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)]
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    IsSmoothAt B S hS (yoneda.map g) ((pointsEquivScheme B S hS U).symm x) ↔
      x ∈ ((BigFppfOver.toScheme B S hS).map g).smoothLocus :=
  (isSmoothAt_yoneda_map_iff_smoothAt B S hS g x).trans
    (Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus _ x)

/-- For a morphism `g` of schemes of the site locally of finite presentation, the induced
morphism of algebraic spaces is non-smooth at finitely many points exactly when the complement
of the smooth locus of `g` is finite. -/
theorem finite_setOf_not_isSmoothAt_yoneda_map_iff {U W : BigFppfOver B S hS} (g : U ⟶ W)
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)] :
    {p : points B S hS (yoneda.obj U) | ¬ IsSmoothAt B S hS (yoneda.map g) p}.Finite ↔
      (((BigFppfOver.toScheme B S hS).map g).smoothLocus :
        Set ((BigFppfOver.toScheme B S hS).obj U))ᶜ.Finite := by
  set e := pointsEquivScheme B S hS U
  have hset : {p : points B S hS (yoneda.obj U) | ¬ IsSmoothAt B S hS (yoneda.map g) p} =
      e.symm '' (((BigFppfOver.toScheme B S hS).map g).smoothLocus :
        Set ((BigFppfOver.toScheme B S hS).obj U))ᶜ := by
    rw [Equiv.image_symm_eq_preimage]
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
    rw [← isSmoothAt_yoneda_map_iff_mem_smoothLocus B S hS g, Equiv.symm_apply_apply]
  rw [hset, Set.finite_image_iff e.symm.injective.injOn]

end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

attribute [local instance] Space.pointTopology

/-- **Stacks 0DZW, part (2).** For the family of curves attached to a proper flat morphism of
schemes of finite presentation onto the spectrum of a field whose source has dimension at most
one, the reduced non-smooth locus is finite over the base exactly when the morphism of schemes
is smooth except at finitely many points. -/
theorem isFiniteNonSmoothLocus_curveFamilyOfSchemeMorphism_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (k : Type u) [Field k]
    (hk : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k)) :
    IsFiniteNonSmoothLocus B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      (((BigFppfOver.toScheme B integerBase hZ).map g).smoothLocus :
        Set ((BigFppfOver.toScheme B integerBase hZ).obj T))ᶜ.Finite := by
  classical
  set F := curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim
  set Tsch := BigFppfOver.toScheme B integerBase hZ
  rw [← Space.finite_setOf_not_isSmoothAt_yoneda_map_iff B integerBase hZ g]
  have hX := isAlgebraicSpace_yoneda B integerBase hZ T
  have hY := isAlgebraicSpace_yoneda B integerBase hZ W
  let f : yoneda.obj T ⟶ yoneda.obj W := yoneda.map g
  show (∃ Z : Subfunctor (yoneda.obj T),
      Space.IsClosedSubspace B integerBase hZ Z ∧
      Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
        {x | ¬ Space.IsSmoothAt B integerBase hZ f x} ∧
      Space.HasEtaleLocalProperty B integerBase hZ Z.toFunctor
        (fun Y : Scheme.{u} => IsReduced Y) ∧
      Space.IsFinite B integerBase hZ (Z.ι ≫ f)) ↔ _
  constructor
  · rintro ⟨Z, hZcl, hrange, -, hfin⟩
    have hZa : IsAlgebraicSpace B integerBase hZ Z.toFunctor := hZcl.1
    have hlqf := (Space.isProper_and_isLocallyQuasiFinite_of_isFinite B integerBase hZ hZa hY
      _ hfin).2
    have hlft : Space.IsLocallyOfFiniteType B integerBase hZ (Z.ι ≫ f) :=
      Space.holdsOnEveryEtaleChart_mono B integerBase hZ (fun _ h => h.1) hlqf
    have : QuasiCompact (Tsch.map g) := inferInstance
    have : CompactSpace (Tsch.obj W) := by rw [hk]; infer_instance
    have : CompactSpace (Tsch.obj T) := QuasiCompact.compactSpace_of_compactSpace (Tsch.map g)
    have hZqc := Space.isQuasiCompactSpace_of_isClosedImmersion B integerBase hZ
      (Space.isQuasiCompactSpace_yoneda B integerBase hZ T this) Z.ι hZcl.2
    have hsub : Subsingleton (Tsch.obj W) := by rw [hk]; infer_instance
    have hqf := Space.finite_setOf_isQuasiFiniteAt_of_isQuasiCompactSpace B integerBase hZ hZa
      hZqc hsub (Z.ι ≫ f) hlft
    have hall := (Space.isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B integerBase hZ hZa hY
      _).mp hlqf
    rw [← hrange, ← Set.image_univ]
    exact (hqf.subset fun z _ => hall z).image _
  · intro hfinT
    let Tns : Set (Space.points B integerBase hZ (yoneda.obj T)) :=
      {x | ¬ Space.IsSmoothAt B integerBase hZ f x}
    have hT : IsClosed Tns := (Space.isOpen_setOf_isSmoothAt B integerBase hZ hX f).isClosed_compl
    let Z := Space.reducedClosedSubspace B integerBase hZ (yoneda.obj T) hX Tns hT
    have hZcl : Space.IsClosedSubspace B integerBase hZ Z :=
      Space.isClosedSubspace_reducedClosedSubspace B integerBase hZ _ hX Tns hT
    have hrange := Space.range_pointsMap_ι_reducedClosedSubspace B integerBase hZ _ hX Tns hT
    refine ⟨Z, hZcl, hrange,
      Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B integerBase hZ _ hX Tns hT, ?_⟩
    have hZa : IsAlgebraicSpace B integerBase hZ Z.toFunctor := hZcl.1
    have hpr : Space.IsProper B integerBase hZ (Z.ι ≫ f) :=
      Space.isProper_comp B integerBase hZ hZa hX hY Z.ι f
        (Space.isProper_ι_reducedClosedSubspace B integerBase hZ _ hX Tns hT) F.proper
    refine Space.isFinite_of_isProper_of_isLocallyQuasiFinite B integerBase hZ hZa hY _ hpr ?_
    rw [Space.isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B integerBase hZ hZa hY]
    intro z
    have hinj := Space.pointsMap_injective_of_mono B integerBase hZ Z.ι
    have hZfin : (Set.univ : Set (Space.points B integerBase hZ Z.toFunctor)).Finite := by
      refine Set.Finite.of_finite_image ?_ hinj.injOn
      rw [Set.image_univ, hrange]
      exact hfinT
    have hZdec := Space.isDecentSpace_of_isClosedSubspace B integerBase hZ
      (Space.isDecentSpace_yoneda B integerBase hZ T) hZcl
    obtain ⟨p, hp⟩ := Quot.exists_rep (Space.pointsMap B integerBase hZ Z.toFunctor (Z.ι ≫ f) z)
    exact Space.isQuasiFiniteAt_of_finite_setFibre B integerBase hZ hZa hY (Z.ι ≫ f) hpr.2.1.1
      hZdec (Space.isDecentSpace_yoneda B integerBase hZ W) p (hZfin.subset (Set.subset_univ _))
      z hp.symm

end AlgebraicGeometry

end
