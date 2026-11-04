module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFaithfulness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFaithfulnessModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksCore.Tactic.StacksAttribute

/-!
# Maps of constructible abelian sheaves on a limit of schemes are detected at a stage

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms. Two maps of constructible sheaves of abelian groups on
`(X_i)_étale` whose inverse images to `X_étale` agree already agree after inverse image to some
later stage. This is the faithfulness assertion of Tag 09YU, clause (2).

The argument is the one the source runs for clause (1), carried out — as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFaithfulnessModules` for
clause (3) — on the support of the image of the difference rather than on the equalizer. The
image of the difference of the two maps is constructible, because the constructible abelian
sheaves form a weak Serre subcategory by Tag 03RZ and the image is the kernel of the projection
to a cokernel; its support is therefore constructible by Tag 09YS (2). Inverse image to `X` is
exact, so it kills that image, and hence every geometric stalk of the image above a point in the
image of `X` vanishes: the support misses the image of `X`. By Tag 05F4 it then misses the image
of a sufficiently late stage, where Tag 03PU turns the vanishing of all geometric stalks into the
vanishing of the inverse image of the image sheaf, so the inverse image of the difference is
zero.

The source deduces clause (2) from clause (3) by observing that over a quasi-compact scheme a
constructible abelian sheaf is constructible as a sheaf of `ℤ/nℤ`-modules for a suitable `n`.
That route is not taken here: it needs the identification of abelian sheaves killed by `n` with
sheaves of `ℤ/nℤ`-modules, which the library does not have. The direct argument below uses only
the abelian counterparts of the three inputs the module argument uses, all of which are
available: Tag 03RZ for abelian sheaves
(`AlgebraicGeometry.constructibleAbelianSheaf_isWeakSerreClass`), Tag 09YS (2)
(`AlgebraicGeometry.isConstructible_supportSheaf`) and the vanishing case of Tag 03PU for
abelian sheaves (`AlgebraicGeometry.isZero_of_forall_isZero_etaleStalk`).

## Main results

* `AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleAbelianSheaf` — **Tag 09YU, clause
  (2), the faithfulness assertion.**

## Implementation notes

Tag 09YS (2) is stated for the set `AlgebraicGeometry.supportSheaf` of Tag 04FS, which is read
off the geometric stalks of the universe-lifted sheaf, whereas the limit argument needs the locus
of points carrying a nonzero stalk of the sheaf itself. The two sets agree by
`AlgebraicGeometry.isZero_etaleStalk_ulift_iff`, and
`AlgebraicGeometry.isConstructible_setOf_not_isZero_etaleStalk_abelianSheaf` below is Tag 09YS
(2) in the second spelling, matching
`AlgebraicGeometry.isConstructible_support_moduleSheaf` for clause (3).

The coefficient universe is fixed to `AddCommGrpCat.{u + 1}`, which is the universe at which the
vanishing case of Tag 03PU for abelian sheaves is available, the site having a zero sheaf there.

Only the faithfulness assertion of clause (2) is proved, and it is the only assertion of Tag 09YU
that the library can reach at present. The source proves fullness and essential surjectivity by
reducing along Tag 09Y9 — which the library has unconditionally, as
`isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional`
— to the claim that taking sections over a quasi-compact quasi-separated étale object commutes
with the colimit, which is what identifies a map out of a finite coproduct of representables at
the limit with such a map at a stage. The library does not have that claim in the form the
reduction needs. Its Tag 09YQ,
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_isLimit`, is
abelian-valued and computes cohomology, not the degree-zero sections of a sheaf of *sets*; the
set-valued object-wise statement
`Stacks.EtaleCohomology.QcSeparatedColimit.sectionOver_colimit_of_qcqs_etale_object` is on the
affine étale system and carries its finite one-hypercover datum and comparison maps as explicit
hypotheses. Fullness is therefore out of reach, and with it essential surjectivity: the models of
Tags 01ZM (1) and 07RP do write a quasi-compact quasi-separated étale `U` over the limit as a
base change from a stage, but the two maps of the coequalizer presentation have to be descended
as maps of sheaves, which is fullness again. The colimit assertion, which packages faithfulness,
fullness and essential surjectivity, is consequently not proved either, for any of the three
clauses.

## References

* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 09YS](https://stacks.math.columbia.edu/tag/09YS)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 04FS](https://stacks.math.columbia.edu/tag/04FS)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

section Support

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    ((SmallEtale.topology B T.obj T.property).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1}]

/-- **Stacks 09YS, part (2), in the spelling of part (3).** Let `X` be a quasi-compact
quasi-separated scheme. The set of points of `X` carrying a nonzero geometric stalk of a
constructible abelian sheaf is constructible.

`AlgebraicGeometry.isConstructible_supportSheaf` is the same statement for the support of
Tag 04FS, which is computed from the geometric stalks of the universe-lifted sheaf; the two sets
agree because lifting does not change vanishing of a stalk that already exists. -/
public theorem isConstructible_setOf_not_isZero_etaleStalk_abelianSheaf (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    Topology.IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
      ¬ IsZero (etaleStalk B X.obj X.property t F.obj)} := by
  have hset : {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
      ¬ IsZero (etaleStalk B X.obj X.property t F.obj)} =
      supportSheaf B X.obj X.property F := by
    ext x
    simp only [mem_supportSheaf_iff_exists, Set.mem_ofPred_eq]
    exact exists_congr fun t => and_congr_right fun _ =>
      (not_congr (isZero_etaleStalk_ulift_iff B X.obj X.property F t)).symm
  rw [hset]
  exact isConstructible_supportSheaf B X F hF

end Support

section Image

end Image

section Descent

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    ((SmallEtale.topology B T.obj T.property).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1}]
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Stacks 09YU, clause (2), the faithfulness assertion.** Let `X = lim X_i` be the limit of a
directed inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms. Two maps of constructible sheaves of abelian groups on `(X_i)_étale` whose inverse
images to `X_étale` agree agree after inverse image to some later stage.

The image of the difference of the two maps is constructible by Tag 03RZ, so the locus where it
has a nonzero geometric stalk is constructible by Tag 09YS (2); inverse image to `X` is exact and
kills the difference, hence the image, so by Tag 03Q1 that locus misses the image of `X` and by
Tag 05F4 the image of a later stage, where Tag 03PU makes the inverse image of the image sheaf
zero. -/
@[stacks 09YU "clause (2), the faithfulness assertion"]
public theorem smallEtaleStagesFaithful_isConstructibleAbelianSheaf (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFaithful B AddCommGrpCat.{u + 1} Dg c hX
      (fun Y => IsConstructibleAbelianSheaf B Y) := by
  intro i F G hF hG a b hab
  have : Nonempty I := ⟨i⟩
  have : CompactSpace (Dg.obj (op i)).obj := hqc i
  have : QuasiSeparatedSpace (Dg.obj (op i)).obj := hqs i
  -- inverse image to the vertex is exact and additive
  have hprojFL : PreservesFiniteLimits
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i) :=
    preservesFiniteLimits_smallEtaleAbelianPullback B _
  have : PreservesLimitsOfShape WalkingCospan
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i) :=
    hprojFL.preservesFiniteLimits _
  have hprojFC : PreservesFiniteColimits
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i) :=
    preservesFiniteColimits_smallEtaleAbelianPullback B _
  have : PreservesColimitsOfShape WalkingSpan
      (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i) :=
    hprojFC.preservesFiniteColimits _
  have hprojAdd : (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).Additive :=
    additive_smallEtaleAbelianPullback B _
  -- the image of the difference is constructible
  let P : ObjectProperty (Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) AddCommGrpCat.{u + 1}) :=
    fun H => IsConstructibleAbelianSheaf B (Dg.obj (op i)) H
  let _ : P.IsWeakSerreClass := constructibleAbelianSheaf_isWeakSerreClass B (Dg.obj (op i))
  have hE : P (Abelian.image (a - b)) :=
    P.prop_kernel (cokernel.π (a - b)) hG (P.prop_cokernel (a - b) hF hG)
  -- the locus where it has a nonzero stalk is constructible and misses the image of the vertex
  set L : Set (Dg.obj (op i)).obj :=
    {x | ∃ t : GeometricPoint (Dg.obj (op i)).obj, t.LiesOver x ∧
      ¬ IsZero (etaleStalk B (Dg.obj (op i)).obj (Dg.obj (op i)).property t
        (Abelian.image (a - b)).obj)} with hLdef
  have hLc : Topology.IsConstructible L :=
    isConstructible_setOf_not_isZero_etaleStalk_abelianSheaf B (Dg.obj (op i)) _ hE
  set p : B.obj c.pt hX ⟶ Dg.obj (op i) := ObjectProperty.homMk (c.π.app (op i)) with hp
  have hpi : B.inclusion.map p = c.π.app (op i) := rfl
  -- An exact functor kills the image of a morphism it kills: the epimorphism onto and the
  -- monomorphism out of the image go to an epimorphism and a monomorphism whose composite is
  -- zero, so the monomorphism out of the image of the image is itself zero.
  have hzeroproj : IsZero ((smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).obj
      (Abelian.image (a - b))) := by
    have hmapzero :
        (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).map (a - b) = 0 := by
      rw [Functor.map_sub, hab, sub_self]
    have hcomp :
        (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).map
            (Abelian.factorThruImage (a - b)) ≫
          (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).map
            (Abelian.image.ι (a - b)) = 0 := by
      rw [← Functor.map_comp, Abelian.image.fac, hmapzero]
    have hepi : Epi ((smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).map
        (Abelian.factorThruImage (a - b))) := Functor.map_epi _ _
    have hmono : Mono ((smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).map
        (Abelian.image.ι (a - b))) := Functor.map_mono _ _
    have hz : (smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).map
        (Abelian.image.ι (a - b)) = 0 := zero_of_epi_comp _ hcomp
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← cancel_mono ((smallEtaleStageProjection B AddCommGrpCat.{u + 1} Dg c hX i).map
      (Abelian.image.ι (a - b))), Category.id_comp, hz, zero_comp]
  have hlim : Set.range ⇑(c.π.app (op i)) ⊆ Lᶜ := by
    rintro y ⟨y', rfl⟩ ⟨t, htz, hnt⟩
    refine hnt ?_
    have hbase : ((GeometricPoint.ofPoint c.pt y').map (B.inclusion.map p)).hom default =
        t.hom default := by
      refine Eq.trans ?_ htz.symm
      simp only [GeometricPoint.map_hom, hpi]
      simp
    refine IsZero.of_iso ?_ ((etaleStalkPresheafFunctorIsoOfEqBase B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property hbase AddCommGrpCat.{u + 1}).app
        (Abelian.image (a - b)).obj).symm
    refine IsZero.of_iso (Functor.map_isZero
      ((geometricPointSitePoint B c.pt hX (GeometricPoint.ofPoint c.pt y')).sheafFiber
        (A := AddCommGrpCat.{u + 1})) hzeroproj) ?_
    exact (etaleStalkSmallEtalePullObjIso B p (GeometricPoint.ofPoint c.pt y')
      AddCommGrpCat.{u + 1} (Abelian.image (a - b))).symm
  -- so it misses the image of a later stage
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp
    (eventually_range_transition_subset_of_isLocallyConstructible
      (descentSituationOfBigEtaleCone B Dg c hc haff hqc hqs i) Lᶜ
      hLc.compl.isLocallyConstructible hlim)
  obtain ⟨j, hij, hj₀j⟩ := directed_of (· ≤ ·) i j₀
  obtain ⟨hbj, hsub⟩ := hj₀ j hj₀j
  refine ⟨j, hij, ?_⟩
  -- at that stage the inverse image of the image sheaf is zero
  have hzE : IsZero ((smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg hij).obj
      (Abelian.image (a - b))) := by
    refine isZero_of_forall_isZero_etaleStalk B (Dg.obj (op j)).obj
      (Dg.obj (op j)).property _ fun s => ?_
    have hmem : (B.inclusion.map (Dg.map (homOfLE hij).op)).base (s.hom.base default) ∈ Lᶜ :=
      hsub ⟨s.hom.base default, rfl⟩
    have ht : IsZero (etaleStalk B (Dg.obj (op i)).obj (Dg.obj (op i)).property
        (s.map (B.inclusion.map (Dg.map (homOfLE hij).op)))
        (Abelian.image (a - b)).obj) := by
      by_contra hne
      refine hmem ⟨s.map (B.inclusion.map (Dg.map (homOfLE hij).op)), ?_, hne⟩
      simp only [GeometricPoint.LiesOver, GeometricPoint.map_hom]
      simp
    exact IsZero.of_iso ht (etaleStalkSmallEtalePullObjIso B
      (Dg.map (homOfLE hij).op) s AddCommGrpCat.{u + 1} (Abelian.image (a - b)))
  have htrAdd : (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg hij).Additive :=
    additive_smallEtaleAbelianPullback B _
  have hφ : (smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg hij).map (a - b) = 0 := by
    rw [← Abelian.image.fac (a - b), Functor.map_comp, hzE.eq_zero_of_src
      ((smallEtaleStageTransition B AddCommGrpCat.{u + 1} Dg hij).map
        (Abelian.image.ι (a - b))), comp_zero]
  rw [Functor.map_sub, sub_eq_zero] at hφ
  exact hφ

end Descent

end AlgebraicGeometry

end
