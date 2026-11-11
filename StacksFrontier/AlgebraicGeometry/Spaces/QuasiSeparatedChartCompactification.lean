module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ConstructionDatum
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremFiniteFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsolutelyQuasiSeparatedAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAlgebraization

/-!
# A proper compactification of an étale chart of a quasi-separated space

Let `A` be a ring, `S = Spec A`, and `Y` an algebraic space over `S` which is quasi-separated and
of finite type over `S`. This file produces the data with which the quasi-separated case of
Stacks 0GHK replaces `Y` by something proper (step 2 of the design in
`StacksFrontier/AlgebraicGeometry/Spaces/MorphismAlgebraizationQuasiSeparated.lean`):

* an étale surjection `v : V ⟶ Y` from an affine scheme `V`;
* an open immersion `o : V ⟶ P` into a scheme `P` proper (indeed H-projective) over `S`
  (Stacks 01WA);
* a factorization `V ⟶ V̄ ⟶ Y` of `v` with `V ⟶ V̄` an open immersion and `V̄ ⟶ Y` finite
  (Zariski's main theorem, Stacks 082K; `v` is quasi-finite, separated and quasi-compact because
  `V` is affine and `Y` is quasi-separated);
* the scheme-theoretic closure `Ṽ` of the quasi-compact immersion `(j, o) : V ⟶ V̄ ×_S P`
  (Stacks 081U): `V ⊆ Ṽ` is open and `Ṽ ⊆ V̄ ×_S P` is closed.

## Main results

* `AlgebraicGeometry.Space.exists_chartCompactification`: the data above.

## References

* [Stacks Project, Tag 082K](https://stacks.math.columbia.edu/tag/082K)
* [Stacks Project, Tag 081U](https://stacks.math.columbia.edu/tag/081U)
* [Stacks Project, Tag 01WA](https://stacks.math.columbia.edu/tag/01WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {hS : B.Contains (Spec (.of A))}

/-- **A proper compactification of an étale chart of a quasi-separated space.** Let `Y` be an
algebraic space quasi-separated and of finite type over `S = Spec A`. There are an affine scheme
`V` with an étale surjection `v : V ⟶ Y`, a scheme `P` proper over `S` containing `V` as an open
subscheme through `o`, an algebraic space `V̄` finite over `Y` through `π̄`, and an algebraic space
`Ṽ` with an open immersion `k : V ⟶ Ṽ` and a closed immersion `c : Ṽ ⟶ V̄ ×_S P`, such that
`V ⟶ Ṽ ⟶ V̄ ×_S P` lies over `v` on the first factor (after `π̄`) and is `o` on the second. -/
theorem exists_chartCompactification
    {Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B _ hS Y)
    {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hqY : IsQuasiSeparated B _ hS fY) (hfY : IsFiniteType B _ hS fY) :
    ∃ (V : BigFppfOver B (Spec (.of A)) hS) (v : yoneda.obj V ⟶ Y)
      (P : BigFppfOver B (Spec (.of A)) hS) (p : P ⟶ baseObject A B hS) (o : V ⟶ P)
      (Vb : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u) (πb : Vb ⟶ Y)
      (Vt : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u) (k : yoneda.obj V ⟶ Vt)
      (c : Vt ⟶ pullback (πb ≫ fY) (yoneda.map p)),
      IsEtale B _ hS v ∧ IsSurjective B _ hS v ∧
      IsProper B _ hS (yoneda.map p) ∧ IsOpenImmersion B _ hS (yoneda.map o) ∧
      IsAlgebraicSpace B _ hS Vb ∧ IsFinite B _ hS πb ∧
      IsAlgebraicSpace B _ hS Vt ∧ IsOpenImmersion B _ hS k ∧ IsClosedImmersion B _ hS c ∧
      k ≫ c ≫ pullback.fst _ _ ≫ πb = v ∧ k ≫ c ≫ pullback.snd _ _ = yoneda.map o := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  have hbase : IsAlgebraicSpace B _ hS (yoneda.obj (baseObject A B hS)) :=
    isAlgebraicSpace_yoneda B _ hS _
  have hterm := isTerminal_yoneda_obj_base B (Spec (.of A)) hS
  have hfY' : fY = hterm.from Y := hterm.hom_ext _ _
  -- the chart and its projective compactification
  have hft : IsFiniteType B _ hS ((isTerminal_yoneda_obj_base B (Spec (.of A)) hS).from Y) := by
    rw [← (isTerminal_yoneda_obj_base B (Spec (.of A)) hS).hom_ext fY
      ((isTerminal_yoneda_obj_base B (Spec (.of A)) hS).from Y)]
    exact hfY
  have key : ∃ (V : BigFppfOver B (Spec (.of A)) hS) (v : yoneda.obj V ⟶ Y),
      IsEtale B _ hS v ∧ IsSeparated B _ hS v ∧ ∃ (P : BigFppfOver B (Spec (.of A)) hS)
        (o : V ⟶ P), CompactSpace ((BigFppfOver.toScheme B _ hS).obj V) ∧
        IsSurjective B _ hS v ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B _ hS).map o) ∧
        IsProjectiveMorphism (B.inclusion.map P.hom) := by
    obtain ⟨V, v, hv, hvsep, P, o, -, -, -, hVc, hvsurj, ho, hP⟩ :=
      exists_chowConstructionDatum B (.of A) hS ⟨Y, hY⟩ hft 0
    exact ⟨V, v, hv, hvsep, P, o, hVc, hvsurj, ho, hP⟩
  obtain ⟨V, v, hv, hvsep, P, o, hVc, hvsurj, ho, hP⟩ := key
  let p : P ⟶ baseObject A B hS := Over.mkIdTerminal.from P
  have hpP : IsProper B _ hS (yoneda.map p) := by
    refine isProper_yoneda_map B _ hS p ?_
    rw [toScheme_map_from_mkIdTerminal]
    exact isProper_of_isProjectiveMorphism _ hP
  have hoo : IsOpenImmersion B _ hS (yoneda.map o) :=
    (presheaf_yoneda_map_iff B _ hS inferInstance o).2 ho
  -- `Y` is quasi-compact and quasi-separated
  have hYqc : IsQuasiCompactSpace B _ hS Y :=
    isQuasiCompactSpace_of_iso B _ hS (asIso (pullback.snd (𝟙 _) fY))
      (hfY.2 _ hbase (isQuasiCompact_yoneda_of_compact B _ hS _ (by
        change CompactSpace (Spec (.of A)); infer_instance)) (𝟙 _))
  have hbaseqs := isAbsolutelyQuasiSeparated_yoneda_of_isAffine B _ hS hZ (baseObject A B hS)
    (by change IsAffine (Spec (.of A)); infer_instance)
  have hYqs : IsAbsolutelyQuasiSeparated B _ hS hZ Y :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hS hZ hY hbaseqs hqY
  -- Zariski's main theorem for the chart
  have hVyo := isAlgebraicSpace_yoneda B _ hS V
  have hvqc : IsQuasiCompact B _ hS v :=
    isQuasiCompact_of_isQuasiCompactSpace B _ hS hZ hY hYqs
      (isQuasiCompact_yoneda_of_compact B _ hS V hVc) v
  obtain ⟨Vb, j, πb, hVb, hj, hjqc, hπb, hjπ⟩ :=
    exists_isOpenImmersion_isFinite_comp_eq_of_isQuasiFinite v hVyo hY
      ⟨isLocallyQuasiFinite_of_isEtale B _ hS hY hv, hvqc⟩ hvsep hYqc hYqs
  -- the immersion `(j, o) : V ⟶ V̄ ×_S P`
  have hPyo := isAlgebraicSpace_yoneda B _ hS P
  have hw : j ≫ πb ≫ fY = yoneda.map o ≫ yoneda.map p := hterm.hom_ext _ _
  let ι : yoneda.obj V ⟶ pullback (πb ≫ fY) (yoneda.map p) := pullback.lift j (yoneda.map o) hw
  have hw' : 𝟙 _ ≫ (j ≫ πb ≫ fY) = yoneda.map o ≫ yoneda.map p := by
    rw [Category.id_comp]; exact hw
  let γ : yoneda.obj V ⟶ pullback (j ≫ πb ≫ fY) (yoneda.map p) :=
    pullback.lift (𝟙 _) (yoneda.map o) hw'
  let m : pullback (j ≫ πb ≫ fY) (yoneda.map p) ⟶ pullback (πb ≫ fY) (yoneda.map p) :=
    pullback.lift (pullback.fst _ _ ≫ j) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition])
  have hιfac : ι = γ ≫ m := by
    apply pullback.hom_ext
    · simp only [ι, γ, m, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.id_comp]
    · simp only [ι, γ, m, Category.assoc, pullback.lift_snd]
  -- `γ` is a section of a separated projection, `m` a base change of `j`
  have hsepfst : IsSeparated B _ hS (pullback.fst (j ≫ πb ≫ fY) (yoneda.map p)) :=
    isSeparated_pullback_fst_of_snd B _ hS (yoneda.map p) (j ≫ πb ≫ fY)
      (isSeparated_pullback B _ hS _ _ hpP.1)
  have hγ : IsClosedImmersion B _ hS γ :=
    isClosedImmersion_of_isSeparated_of_section B _ hS _ hsepfst γ (pullback.lift_fst _ _ _)
  have hsq : IsPullback m (pullback.fst _ _) (pullback.fst _ _) j := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (πb ≫ fY) (yoneda.map p)).flip
    rw [pullback.lift_snd]
    exact (IsPullback.of_hasPullback (j ≫ πb ≫ fY) (yoneda.map p)).flip
  have hm : IsOpenImmersion B _ hS m := by
    have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hS))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    exact MorphismProperty.of_isPullback hsq.flip hj
  have hP1 : IsAlgebraicSpace B _ hS (pullback (j ≫ πb ≫ fY) (yoneda.map p)) :=
    isAlgebraicSpace_pullback B _ hS _ _ hVyo hPyo hbase
  have hP2 : IsAlgebraicSpace B _ hS (pullback (πb ≫ fY) (yoneda.map p)) :=
    isAlgebraicSpace_pullback B _ hS _ _ hVb hPyo hbase
  have hιimm : IsImmersion B _ hS ι := by
    rw [hιfac]
    exact isImmersion_comp B _ hS γ m (isImmersion_of_isClosedImmersion B _ hS hγ)
      (isImmersion_of_isOpenImmersion B _ hS hm)
  have hιqc : IsQuasiCompact B _ hS ι := by
    rw [hιfac]
    exact isQuasiCompact_comp B _ hS hP1 hP2 γ m (isQuasiCompact_of_isClosedImmersion' B _ hS hγ)
      (isQuasiCompact_of_isPullback B _ hS hsq.flip hjqc)
  -- its scheme-theoretic closure
  obtain ⟨Vt, k, c, hVt, hk, hc, hkc⟩ :=
    exists_isOpenImmersion_isClosedImmersion_comp_eq_of_isQuasiCompact B _ hS hP2 ι hιimm hιqc
  refine ⟨V, v, P, p, o, Vb, πb, Vt, k, c, hv, hvsurj, hpP, hoo, hVb, hπb, hVt, hk, hc, ?_, ?_⟩
  · rw [reassoc_of% hkc, pullback.lift_fst_assoc, hjπ]
  · rw [reassoc_of% hkc, pullback.lift_snd]

end AlgebraicGeometry.Space

end
