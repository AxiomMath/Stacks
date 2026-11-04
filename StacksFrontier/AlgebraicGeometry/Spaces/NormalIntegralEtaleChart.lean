module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.SmoothLocalSource
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative

/-!
# Normal integral affine étale charts

Every point of a normal integral algebraic space over a scheme `S` lies in the image of an
étale morphism to it from a *normal integral affine* scheme.

An affine étale chart `U` of such a space is a normal affine scheme, so the only thing to
prove is that it decomposes as a finite disjoint union of normal integral schemes, which by
Stacks 0357 is finiteness of its irreducible components. That finiteness is where the geometry
of the space enters: the generic point of an irreducible component of `U` has a local ring of
dimension zero (Stacks 0BAQ), a point of `|X|` whose local ring has dimension zero admits no
generization but itself (Stacks 0ABV), and the generic point of the irreducible space `|X|` is
a generization of every point — so all generic points of `U` lie over that one point of `|X|`,
and decency bounds the fibre of `U` there.

## Main results

* `AlgebraicGeometry.Space.pointsMap_eq_of_mem_genericPoints`: a generic point of an
  irreducible component of an étale scheme chart lies over a prescribed point generalizing
  every point of the space.
* `AlgebraicGeometry.Space.finite_irreducibleComponents_of_isAffine_etaleChart`: such a space
  has affine étale charts with finitely many irreducible components.
* `AlgebraicGeometry.Space.exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart`: the
  shrinking step, which shrinks a *prescribed* affine étale chart to a normal integral affine
  open around a prescribed point of it.
* `AlgebraicGeometry.Space.exists_isAffine_isNormal_isIntegral_etaleChart`: **Stacks 0AYH**.

## Implementation notes

The hypothesis that a point `ξ` of `|X|` generalizes every point of `|X|` is carried as data
by the two auxiliary results, rather than deduced, so that neither of them needs sobriety: for
an irreducible point space it is `TopologicalSpace.genericPoint_specializes`, which asks for
quasi-sobriety of `|X|`, and that is Stacks 03K6,
`AlgebraicGeometry.Space.quasiSober_points_of_isDecentSpace`. The main theorem supplies it
there, as does `AlgebraicGeometry.Space.mem_genericPoints_of_localRingDimension_eq_zero`,
which is the half of Stacks 0ABV the source of Stacks 0AYH uses here and carries the same
condition as a hypothesis.

Normality of schemes is local for the étale precoverage because it is local for the smooth
one; that instance is private here, as it is in
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpaceProperties` and in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization`, since a private instance of
another module is not available to instance synthesis.

The image condition is membership of `x` in the range of the map on points induced by the
chart, which is the point-set form of "`x` is in the image of `U → X`"; the étale condition on
the chart is the relatively representable étale property of Stacks 03FR, in the
`MorphismProperty.presheaf` form used throughout the development.

## References

* [Stacks Project, Tag 0AYH](https://stacks.math.columbia.edu/tag/0AYH)
* [Stacks Project, Tag 0357](https://stacks.math.columbia.edu/tag/0357)
* [Stacks Project, Tag 030C](https://stacks.math.columbia.edu/tag/030C)
* [Stacks Project, Tag 033J](https://stacks.math.columbia.edu/tag/033J)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- Normality of schemes is local for the étale precoverage: it is local for the smooth
precoverage by Stacks 034F, and an étale morphism of schemes is smooth. -/
@[sga "7 VIII 6.4" "special case"]
private instance isNormal_isLocal_etalePrecoverage :
    ObjectProperty.IsLocal (fun X : Scheme.{u} ↦ IsNormal X) Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le
    (Scheme.precoverage_mono (P := (@Etale : MorphismProperty Scheme.{u}))
      (Q := (@Smooth : MorphismProperty Scheme.{u}))
      fun _ _ f hf ↦ by
        let _ : Etale f := hf
        infer_instance)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `X` be a decent algebraic space over `S` and let `ξ` be a point of `|X|` which
generalizes every point of `|X|` — the generic point, when `|X|` is irreducible and
quasi-sober. Then every generic point of an irreducible component of an étale scheme chart of
`X` lies over `ξ`.

The local ring of `X` at the image of such a chart point has dimension zero by Stacks 0BAQ,
and a point whose local ring has dimension zero admits no generization but itself. -/
theorem pointsMap_eq_of_mem_genericPoints (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {ξ : points B S hS X}
    (hξ : ∀ y : points B S hS X, ξ ⤳ y) (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (u : points B S hS (yoneda.obj U))
    (hu : pointsToScheme B S hS U u ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :
    pointsMap B S hS (yoneda.obj U) φ u = ξ := by
  have hdim : localRingDimension B S hS (pointsMap B S hS (yoneda.obj U) φ u) = 0 :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX _).mpr
      ⟨U, φ, pointsToScheme B S hS U u, (isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφ,
        chartPoint_pointsToScheme B S hS U φ u, hu⟩
  exact (eq_of_specializes_of_localRingDimension_eq_zero B S hS hX hdec hdim ξ (hξ _)).symm

/-- An affine étale chart of a decent algebraic space over `S` whose point space has a point
generalizing every point has finitely many irreducible components: the generic points of the
chart all lie over that one point, and the fibre of an affine étale chart above a point of a
decent space is finite. -/
theorem finite_irreducibleComponents_of_isAffine_etaleChart (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {ξ : points B S hS X}
    (hξ : ∀ y : points B S hS X, ξ ⤳ y) (U : BigFppfOver B S hS)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ) :
    (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)).Finite := by
  have hmem : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U),
      (schemePointsHomeomorph B S hS U).symm η.1 ∈
        pointsMap B S hS (yoneda.obj U) φ ⁻¹' {ξ} := by
    intro η
    refine Set.mem_preimage.2 (Set.mem_singleton_iff.2 ?_)
    refine pointsMap_eq_of_mem_genericPoints B S hS hX hdec hξ U φ hφ _ ?_
    rw [← schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply]
    exact η.2
  have : Finite ↥(pointsMap B S hS (yoneda.obj U) φ ⁻¹' {ξ}) :=
    (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec ξ U hUaff φ hφ).to_subtype
  have : Finite ↥(genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :=
    Finite.of_injective
      (fun η ↦ (⟨(schemePointsHomeomorph B S hS U).symm η.1, hmem η⟩ :
        ↥(pointsMap B S hS (yoneda.obj U) φ ⁻¹' {ξ})))
      fun η θ h ↦ Subtype.ext (by
        simpa using congrArg (fun z ↦ schemePointsHomeomorph B S hS U z.1) h)
  have : Finite ↥(irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)) :=
    Finite.of_equiv _ (genericPoints.equiv (α := (BigFppfOver.toScheme B S hS).obj U))
  exact Set.toFinite _

/-- Every étale scheme chart of a space with the étale-local property of normality is normal. -/
private theorem isNormal_of_etaleChart (hX : IsAlgebraicSpace B S hS X)
    (hnormal : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsNormal Y))
    (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ X)
    (hψ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ψ) :
    IsNormal ((BigFppfOver.toScheme B S hS).obj V) :=
  (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} ↦ IsNormal Y) hX).mp hnormal
    V ψ hψ

/-- **The shrinking step of Stacks 0AYH.** Let `X` be a normal integral algebraic space over
`S`. Every point of an affine étale scheme chart of `X` has an affine open neighbourhood inside
that chart which is a normal integral scheme.

Normality of `X` is normality of schemes as an étale-local property, so the chart is a normal
scheme; being affine it has finitely many irreducible components, hence decomposes as a
disjoint union of normal integral schemes by Stacks 0357, and an affine open neighbourhood of
the given point inside the summand containing it is the required open.

Unlike `AlgebraicGeometry.Space.exists_isAffine_isNormal_isIntegral_etaleChart`, which chooses
its own chart, this shrinks a *prescribed* one: the open it returns is an open of the given
chart, so a structure carried by that chart — being an elementary étale neighbourhood of a
point of `X`, say — is inherited by the shrunken chart. -/
theorem exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart
    (hX : IsAlgebraicSpace B S hS X)
    (hnormal : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsNormal Y))
    (hintegral : IsIntegralSpace B S hS X) (V : BigFppfOver B S hS)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (ψ : yoneda.obj V ⟶ X)
    (hψ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ψ)
    (a : (BigFppfOver.toScheme B S hS).obj V) :
    ∃ W : ((BigFppfOver.toScheme B S hS).obj V).Opens, a ∈ W ∧ IsAffineOpen W ∧
      IsNormal W.toScheme ∧ IsIntegral W.toScheme := by
  classical
  have hdec : IsDecentSpace B S hS X := IsIntegralSpace.isDecentSpace B S hS X hintegral
  have : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hdec
  have : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hdec
  have : IrreducibleSpace (points B S hS X) :=
    IsIntegralSpace.irreducibleSpace B S hS X hintegral
  -- every étale chart of `X` is a normal scheme, this one in particular
  have hVnormal := isNormal_of_etaleChart B S hS hX hnormal V ψ hψ
  have hcomp : (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj V)).Finite :=
    finite_irreducibleComponents_of_isAffine_etaleChart B S hS hX hdec
      (fun y ↦ genericPoint_specializes y) V hVaff ψ hψ
  have hVfinite : ∀ W : ((BigFppfOver.toScheme B S hS).obj V).Opens,
      IsCompact (W : Set ((BigFppfOver.toScheme B S hS).obj V)) →
      (irreducibleComponents W).Finite := by
    intro W _
    have : QuasiSober ↥(W : Set ((BigFppfOver.toScheme B S hS).obj V)) :=
      W.2.isOpenEmbedding_subtypeVal.quasiSober
    exact Set.Finite.irreducibleComponents_of_isOpenEmbedding _
      W.2.isOpenEmbedding_subtypeVal hcomp
  -- the chart is a disjoint union of normal integral schemes
  obtain ⟨ι, Y, hYnormal, hYintegral, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct hVfinite).mp hVnormal
  obtain ⟨i, t, ht⟩ := (sigmaOpenCover Y).exists_eq (e.hom a)
  have ht' : Sigma.ι Y i t = e.hom a := by
    rw [← sigmaOpenCover_f Y i]
    exact ht
  -- an affine open of the summand through the point
  obtain ⟨-, ⟨W, hWaff, rfl⟩, htW, -⟩ :=
    (Y i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
  have : IsAffine (Scheme.Opens.toScheme W) := hWaff
  have : IsIntegral (Y i) := hYintegral i
  have hmem : a ∈ ((Scheme.Opens.ι W ≫ Sigma.ι Y i ≫ e.inv).opensRange :
      Set ((BigFppfOver.toScheme B S hS).obj V)) := by
    rw [Scheme.Hom.coe_opensRange]
    refine ⟨⟨t, htW⟩, ?_⟩
    show e.inv (Sigma.ι Y i (Scheme.Opens.ι W ⟨t, htW⟩)) = a
    rw [show Scheme.Opens.ι W ⟨t, htW⟩ = t from rfl, ht']
    show (e.hom ≫ e.inv) a = a
    rw [e.hom_inv_id]
    rfl
  refine ⟨(Scheme.Opens.ι W ≫ Sigma.ι Y i ≫ e.inv).opensRange, hmem,
    isAffineOpen_opensRange (Scheme.Opens.ι W ≫ Sigma.ι Y i ≫ e.inv), isNormal_open _, ?_⟩
  have : Nonempty (Scheme.Opens.ι W ≫ Sigma.ι Y i ≫ e.inv).opensRange.toScheme :=
    ⟨⟨a, hmem⟩⟩
  exact isIntegral_of_isOpenImmersion
    ((Scheme.Opens.ι W ≫ Sigma.ι Y i ≫ e.inv).isoOpensRange.inv ≫ Scheme.Opens.ι W)

/-- **Stacks 0AYH.** Let `X` be a normal integral algebraic space over `S`. Every point of
`|X|` is in the image of an étale morphism to `X` from a normal integral affine scheme.

An affine étale chart through the point is shrunk to an affine open which is normal and
integral by
`AlgebraicGeometry.Space.exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart`,
and that open is an object of the chosen big site by
`AlgebraicGeometry.BigFppfOver.exists_affineOpen_restrict`. -/
@[stacks 0AYH]
theorem exists_isAffine_isNormal_isIntegral_etaleChart (hX : IsAlgebraicSpace B S hS X)
    (hnormal : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsNormal Y))
    (hintegral : IsIntegralSpace B S hS X) (x : points B S hS X) :
    ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsNormal ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsIntegral ((BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ ∧
      x ∈ Set.range (pointsMap B S hS (yoneda.obj U) φ) := by
  classical
  obtain ⟨V, ψ, a, hVaff, hψ, hax⟩ := exists_affine_etale_chart_of_point B S hS X hX x
  obtain ⟨W, haW, hWaff, hWnormal, hWintegral⟩ :=
    exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart B S hS hX hnormal hintegral
      V hVaff ψ hψ (pointsToScheme B S hS V a)
  obtain ⟨U, k, hkOpen, hkRange, hUaff⟩ :=
    BigFppfOver.exists_affineOpen_restrict B S hS V ⟨W, hWaff⟩
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map k) := hkOpen
  have hkEtale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) := inferInstance
  have hketale := etale_comp_of_scheme B S hS k ψ hkEtale hψ
  have hUnormal := isNormal_of_etaleChart B S hS hX hnormal U (yoneda.map k ≫ ψ) hketale
  have hmem : pointsToScheme B S hS V a ∈
      Set.range ((BigFppfOver.toScheme B S hS).map k) := by
    rw [hkRange]
    exact haW
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj U) := ⟨hmem.choose⟩
  refine ⟨U, yoneda.map k ≫ ψ, hUaff, hUnormal, ?_, hketale, ?_⟩
  · exact isIntegral_of_isOpenImmersion
      (IsOpenImmersion.isoOfRangeEq ((BigFppfOver.toScheme B S hS).map k) (Scheme.Opens.ι W)
        (hkRange.trans (Scheme.Opens.range_ι W).symm)).hom
  · obtain ⟨b, hb⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B S hS k a hmem
    exact ⟨b, by rw [pointsMap_comp_apply, hb, hax]⟩

end AlgebraicGeometry.Space

end
