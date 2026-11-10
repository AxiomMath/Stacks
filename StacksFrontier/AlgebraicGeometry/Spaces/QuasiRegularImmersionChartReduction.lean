module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenInterchange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSheafCartesianSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RegularImmersion

/-!
# Quasi-regularity of an immersion of algebraic spaces, read on its closed factor

Let `i : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `k : Z ⟶ X'` be its closed factorisation through the open subspace
`X' = X ∖ ∂Z` of Stacks 04CE (`AlgebraicGeometry.Space.immersionClosedFactorization`).  The
quasi-regularity of `i` (Stacks 06BN, part (3)) is defined on the étale scheme charts of `X`.
This file reads it, and local finite presentation, on the étale scheme charts of `X'` instead,
where the base change of `k` is a *closed* immersion of schemes, and it identifies the ideal
of the kernel ideal sheaf of `k` over an open sub-chart with the kernel ideal of the scheme
chart.

## Main results

* `AlgebraicGeometry.quasiRegularImmersionProperty_comp_isOpenImmersion`: a quasi-regular closed
  immersion of schemes followed by an open immersion is a quasi-regular immersion.
* `AlgebraicGeometry.ker_morphismRestrict_appTop`: the kernel of `(j ∣_ O)` on global functions
  is the kernel of `j` on the sections over `O`, read along `O.topIso`.
* `AlgebraicGeometry.Space.isQuasiRegularImmersion_iff_forall_closedFactor`: an immersion of
  algebraic spaces is quasi-regular exactly when the base change of its closed factor along every
  étale scheme chart of `X'` is a quasi-regular immersion of schemes.
* `AlgebraicGeometry.Space.locallyOfFinitePresentation_closedFactor_baseChange`: local finite
  presentation of the immersion gives local finite presentation of those base changes.
* `AlgebraicGeometry.Space.chartSectionIdeal_kernelIdealSheaf_openChart`: over the open sub-chart
  `openChart V O` of a chart `V`, the ideal of sections of the kernel ideal sheaf of a
  representable morphism is the kernel of the scheme base change on the sections over `O`.

## References

* [Stacks Project, Tag 06BN](https://stacks.math.columbia.edu/tag/06BN)
* [Stacks Project, Tag 063J](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- Being a quasi-regular immersion, as a property of morphisms of schemes. -/
abbrev quasiRegularImmersionProperty : MorphismProperty Scheme.{u} :=
  fun _ _ f => ∃ hf : IsImmersion f, @IsQuasiRegularImmersion _ _ f hf

/-- Being a quasi-regular immersion of schemes is invariant under isomorphisms. -/
instance : (quasiRegularImmersionProperty.{u}).RespectsIso :=
  (isLocalAtTarget_quasiRegularImmersion_etale.{u}).toRespects

/-- For an immersion, the morphism property is quasi-regularity. -/
theorem quasiRegularImmersionProperty_iff {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    quasiRegularImmersionProperty i ↔ IsQuasiRegularImmersion i :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨inferInstance, h⟩⟩

/-- Quasi-regularity of an immersion through an open in which it is closed, in the
affine-generator form of Stacks 063G. -/
theorem isQuasiRegularImmersion_iff_kerGeneratedBy {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) (j : Z ⟶ V.toScheme) [IsClosedImmersion j]
    (hij : j ≫ V.ι = i) :
    IsQuasiRegularImmersion i ↔
      KerGeneratedBy (fun {A} _ _ f => RingTheory.Sequence.IsQuasiRegular A (List.ofFn f)) j :=
  (isQuasiRegularImmersion_iff_of_open i V j hij).trans
    (isQuasiRegularIdealSheaf_iff_kerGeneratedBy j)

/-- **A quasi-regular closed immersion followed by an open immersion is a quasi-regular
immersion.**  The composite is closed in the image of the open immersion, and quasi-regularity is
read there (Stacks 063J, independence of the open), after transporting the closed immersion along
the identification of the target with that image. -/
theorem quasiRegularImmersionProperty_comp_isOpenImmersion {A Y W : Scheme.{u}} (j : A ⟶ Y)
    [IsClosedImmersion j] (o : Y ⟶ W) [IsOpenImmersion o]
    (h : quasiRegularImmersionProperty j) : quasiRegularImmersionProperty (j ≫ o) := by
  obtain ⟨_, hj⟩ := h
  have : IsIso (⊤ : Y.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  let jT : A ⟶ (⊤ : Y.Opens).toScheme := j ≫ inv (⊤ : Y.Opens).ι
  have hjT : jT ≫ (⊤ : Y.Opens).ι = j := by simp [jT]
  have hKG := (isQuasiRegularImmersion_iff_kerGeneratedBy j ⊤ jT hjT).mp hj
  let e := o.isoOpensRange
  let c : A ⟶ o.opensRange.toScheme := j ≫ e.hom
  have hc : c ≫ o.opensRange.ι = j ≫ o := by simp [c, e]
  let ε : (⊤ : Y.Opens).toScheme ≅ o.opensRange.toScheme := asIso ((⊤ : Y.Opens).ι ≫ e.hom)
  have hsq : IsPullback (𝟙 A) c jT ε.inv :=
    IsPullback.of_horiz_isIso ⟨by simp [c, jT, ε]⟩
  have hKGc := kerGeneratedBy_of_isPullback isQuasiRegular_of_ringHomFlat hsq hKG
  exact ⟨inferInstance, (isQuasiRegularImmersion_iff_kerGeneratedBy (j ≫ o) o.opensRange c hc).mpr
    hKGc⟩

/-- **The kernel of a restricted morphism on global functions.**  The functions on the open
subscheme `O` killed by `j ∣_ O` are, read along `O.topIso`, the sections over `O` killed by
`j`. -/
theorem ker_morphismRestrict_appTop {Z Y : Scheme.{u}} (j : Z ⟶ Y) (O : Y.Opens) :
    RingHom.ker (j ∣_ O).appTop.hom =
      Ideal.comap O.topIso.hom.hom (RingHom.ker (j.app O).hom) := by
  have h : (j ∣_ O).appTop ≫ (j ⁻¹ᵁ O).topIso.hom = O.topIso.hom ≫ j.app O := by
    have h0 : (j.resLE O (j ⁻¹ᵁ O) le_rfl).appTop ≫ (j ⁻¹ᵁ O).topIso.hom =
        O.topIso.hom ≫ j.appLE O (j ⁻¹ᵁ O) le_rfl :=
      (arrowResLEAppIso j O (j ⁻¹ᵁ O) le_rfl).hom.w.symm
    rwa [j.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at h0
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
  have hinj : Function.Injective (j ⁻¹ᵁ O).topIso.hom.hom :=
    (ConcreteCategory.bijective_of_isIso (j ⁻¹ᵁ O).topIso.hom).1
  have hx := congrArg (fun g : Γ(O.toScheme, ⊤) ⟶ Γ(Z, j ⁻¹ᵁ O) => g.hom x) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hx
  rw [← hx, ← map_zero (j ⁻¹ᵁ O).topIso.hom.hom, hinj.eq_iff]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The kernel ideal sheaf over an open sub-chart -/

section OpenChart

variable {X Z : AlgebraicSpaces B S hS}

/-- **The kernel ideal sheaf over an open sub-chart.**  For a representable morphism
`k : Z ⟶ X`, an étale scheme chart `V` of `X` and a Zariski open `O` of its scheme, the ideal of
sections of the kernel ideal sheaf of `k` over the chart `openChart V O` is the kernel of the
base change `j : Z ×_X V ⟶ V` of `k` on the sections over `O`, read along `O.topIso`. -/
theorem chartSectionIdeal_kernelIdealSheaf_openChart (k : Z ⟶ X)
    (hk : yoneda.relativelyRepresentable k.hom) (V : SmallEtale B S hS X.1)
    (O : (chartScheme V).Opens) :
    chartSectionIdeal B S hS X.1 X.2 (kernelIdealSheaf B S hS k) (openChart B S hS X.1 V O) =
      Ideal.comap (openChartTopRingHom B S hS X V O)
        (RingHom.ker (((BigFppfOver.toScheme B S hS).map (hk.snd V.1.hom)).app O).hom) := by
  have h1 : chartSectionIdeal B S hS X.1 X.2 (kernelIdealSheaf B S hS k)
      (openChart B S hS X.1 V O) =
      RingHom.ker ((BigFppfOver.toScheme B S hS).map
        (hk.snd (openChart B S hS X.1 V O).1.hom)).appTop.hom := by
    change (kernelIdealSheaf B S hS k).obj (op (openChart B S hS X.1 V O)) = _
    rw [kernelIdealSheaf_obj, ker_structureSharp_eq B S hS k hk _,
      chartPullbackRingHom_chartBaseChangeArrow]
    rfl
  have h2 : hk.snd (openChart B S hS X.1 V O).1.hom =
      (openChartBaseChangeIso B S hS k hk V O).hom ≫
        openChartSmallBaseChangeProjection B S hS k hk V O :=
    (openChartBaseChangeIso_hom_comp_projection B S hS k hk V O).symm
  have hinj : Function.Injective ((BigFppfOver.toScheme B S hS).map
      (openChartBaseChangeIso B S hS k hk V O).hom).appTop.hom := by
    have hc : (BigFppfOver.toScheme B S hS).map (openChartBaseChangeIso B S hS k hk V O).inv ≫
        (BigFppfOver.toScheme B S hS).map (openChartBaseChangeIso B S hS k hk V O).hom =
          𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id]
      exact CategoryTheory.Functor.map_id _ _
    refine Function.LeftInverse.injective (g := ((BigFppfOver.toScheme B S hS).map
      (openChartBaseChangeIso B S hS k hk V O).inv).appTop.hom) fun y => ?_
    have h := congrArg (fun g => g.appTop.hom y) hc
    simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
    exact h
  have hker := ker_morphismRestrict_appTop
    ((BigFppfOver.toScheme B S hS).map (hk.snd V.1.hom)) O
  have key : ((BigFppfOver.toScheme B S hS).map
        (hk.snd (openChart B S hS X.1 V O).1.hom)).appTop =
      ((((BigFppfOver.toScheme B S hS).map (hk.snd V.1.hom)) ∣_ O).appTop) ≫
        ((BigFppfOver.toScheme B S hS).map
          (openChartBaseChangeIso B S hS k hk V O).hom).appTop := by
    rw [h2, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  ext x
  have hx := congrArg (fun g => g.hom x) key
  rw [h1]
  exact RingHom.mem_ker.trans ((Eq.congr_left hx).trans ((map_eq_zero_iff _ hinj).trans
    (RingHom.mem_ker.symm.trans (SetLike.ext_iff.mp hker x))))

/-- **The kernel ideal sheaf over an affine open sub-chart is the scheme chart ideal.**  For an
affine open `O` of the scheme of `V` and the base change `j` of `k` along `V` an immersion, the
ideal of sections of the kernel ideal sheaf of `k` over `openChart V O` is the preimage of
`Stacks.Conormal.chartIdeal j O` along the ring isomorphism `Γ(O, ⊤) ≅ Γ(V, O)` of
`AlgebraicGeometry.Space.openChartTopRingHom`. -/
theorem chartSectionIdeal_kernelIdealSheaf_openChart_eq_comap_chartIdeal (k : Z ⟶ X)
    (hk : yoneda.relativelyRepresentable k.hom) (V : SmallEtale B S hS X.1)
    (O : (chartScheme V).affineOpens)
    [_root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map (hk.snd V.1.hom))] :
    chartSectionIdeal B S hS X.1 X.2 (kernelIdealSheaf B S hS k) (openChart B S hS X.1 V O.1) =
      Ideal.comap (openChartTopRingHom B S hS X V O.1)
        (Stacks.Conormal.chartIdeal ((BigFppfOver.toScheme B S hS).map (hk.snd V.1.hom)) O) :=
  chartSectionIdeal_kernelIdealSheaf_openChart B S hS k hk V O.1

end OpenChart

/-! ### Reading quasi-regularity on the closed factor -/

section ClosedFactor

attribute [local instance] pointTopology

/-- A pullback square of representables over a pullback square against a relatively representable
`i` identifies the corner with `hi.pullback q`, compatibly with the second projection. -/
private theorem exists_iso_comp_snd_eq {C : Type*} [Category C] {X Y : Cᵒᵖ ⥤ Type _} {i : Y ⟶ X}
    (hi : yoneda.relativelyRepresentable i) {W T : C} (q : yoneda.obj W ⟶ X)
    {a : yoneda.obj T ⟶ Y} {s : T ⟶ W} (hsq : IsPullback a (yoneda.map s) i q) :
    ∃ e : T ≅ hi.pullback q, e.hom ≫ hi.snd q = s := by
  let eW := hsq.isoIsPullback _ _ (hi.isPullback q)
  refine ⟨yoneda.preimageIso eW, yoneda.map_injective ?_⟩
  simp [eW]

/-- The base change of an étale morphism of representables along a pullback square is étale. -/
private theorem presheaf_etale_fst_of_isPullback {A P R X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : A ⟶ P} {b : A ⟶ R} {f : P ⟶ X₀} {g : R ⟶ X₀} (hsq : IsPullback a b f g)
    (hg : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := by
  have : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip hg

variable {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X₀)
  (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i)

include hX hZ hi in
/-- The inclusion of the complement of the boundary of an immersion is étale after every
representable base change. -/
theorem presheaf_etale_ι_immersionAmbient :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).ι :=
  presheaf_etale_of_isOpenImmersion B S hS
    (isOpenSubspace_immersionAmbient B S hS (Z' := ⟨Z₀, hZ⟩) (X' := ⟨X₀, hX⟩)
      (ObjectProperty.homMk i) hi).2

/-- An étale scheme chart of `X ∖ ∂Z` composed with the inclusion is an étale scheme chart of
`X`. -/
theorem presheaf_etale_comp_ι_immersionAmbient
    (V : SmallEtale B S hS (immersionAmbient B S hS hX hZ i hi).1) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (V.1.hom ≫ (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).ι) :=
  (isMultiplicative_presheaf_etale B S hS).comp_mem _ _ V.property
    (presheaf_etale_ι_immersionAmbient B S hS hX hZ i hi)

/-- The closed factorisation composed with the inclusion of `X ∖ ∂Z` is the immersion. -/
theorem immersionClosedFactorization_hom_comp_ι :
    (immersionClosedFactorization B S hS hX hZ i hi).hom ≫
        (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).ι = i :=
  boundaryComplementLift_comp_ι B S hS hX hZ i hi

/-- If an immersion `i : Z ⟶ X` of algebraic spaces is quasi-regular, then the base change of its
closed factor `Z ⟶ X ∖ ∂Z` along every étale scheme chart `V` of `X ∖ ∂Z` is a quasi-regular
immersion of schemes. -/
theorem quasiRegularImmersionProperty_closedFactor_of_isQuasiRegularImmersion
    (h : IsQuasiRegularImmersion B S hS i)
    (V : SmallEtale B S hS (immersionAmbient B S hS hX hZ i hi).1) :
    quasiRegularImmersionProperty ((BigFppfOver.toScheme B S hS).map
      ((isClosedImmersion_immersionClosedFactorization B S hS hX hZ i hi).1.snd V.1.hom)) := by
  obtain ⟨hi', hall⟩ := h
  set ι := (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).ι
  set hk := (isClosedImmersion_immersionClosedFactorization B S hS hX hZ i hi).1
  set q := V.1.hom ≫ ι
  have hQ := hall V.1.left q (presheaf_etale_comp_ι_immersionAmbient B S hS hX hZ i hi V)
  have : Mono (show (immersionAmbient B S hS hX hZ i hi).1 ⟶ X₀ from ι) := inferInstanceAs
    (Mono (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).ι)
  have hright : IsPullback (𝟙 Z₀) (immersionClosedFactorization B S hS hX hZ i hi).hom i ι :=
    IsPullback.of_horiz_isIso_mono ⟨by
      rw [Category.id_comp, immersionClosedFactorization_hom_comp_ι]⟩
  have hsq : IsPullback (hk.fst V.1.hom ≫ 𝟙 Z₀) (yoneda.map (hk.snd V.1.hom)) i q :=
    (hk.isPullback V.1.hom).paste_horiz hright
  obtain ⟨e, he⟩ := exists_iso_comp_snd_eq hi' q hsq
  rw [← he, Functor.map_comp]
  exact (quasiRegularImmersionProperty.cancel_left_of_respectsIso _ _).mpr hQ

/-- If the base change of the closed factor `Z ⟶ X ∖ ∂Z` of an immersion `i : Z ⟶ X` along every
étale scheme chart of `X ∖ ∂Z` is a quasi-regular immersion of schemes, then `i` is a
quasi-regular immersion. -/
theorem isQuasiRegularImmersion_of_quasiRegularImmersionProperty_closedFactor
    (h : ∀ V : SmallEtale B S hS (immersionAmbient B S hS hX hZ i hi).1,
      quasiRegularImmersionProperty ((BigFppfOver.toScheme B S hS).map
        ((isClosedImmersion_immersionClosedFactorization B S hS hX hZ i hi).1.snd V.1.hom))) :
    IsQuasiRegularImmersion B S hS i := by
  refine ⟨hi.1, fun W q hq => ?_⟩
  set U := boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))
  have hU := isOpenSubspace_immersionAmbient B S hS (Z' := ⟨Z₀, hZ⟩) (X' := ⟨X₀, hX⟩)
    (ObjectProperty.homMk i) hi
  set hιr := hU.2.1
  set hkc := isClosedImmersion_immersionClosedFactorization B S hS hX hZ i hi
  set hk := hkc.1
  set a := hιr.fst q
  have ha := presheaf_etale_fst_of_isPullback B S hS (hιr.isPullback q) hq
  let V : SmallEtale B S hS (immersionAmbient B S hS hX hZ i hi).1 :=
    ⟨CostructuredArrow.mk a, ha⟩
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (hιr.snd q)) :=
    hU.2.2 q (hιr.fst q) (hιr.snd q) (hιr.isPullback q)
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (hk.snd a)) :=
    hkc.2 a (hk.fst a) (hk.snd a) (hk.isPullback a)
  have hsq : IsPullback (hk.fst a) (yoneda.map (hk.snd a) ≫ yoneda.map (hιr.snd q))
      ((immersionClosedFactorization B S hS hX hZ i hi).hom ≫ U.ι) q :=
    (hk.isPullback a).paste_vert (hιr.isPullback q)
  rw [immersionClosedFactorization_hom_comp_ι, ← Functor.map_comp] at hsq
  obtain ⟨e, he⟩ := exists_iso_comp_snd_eq hi.1 q hsq
  refine (quasiRegularImmersionProperty.cancel_left_of_respectsIso
    ((BigFppfOver.toScheme B S hS).map e.hom) _).mp ?_
  rw [← Functor.map_comp, he, Functor.map_comp]
  exact quasiRegularImmersionProperty_comp_isOpenImmersion _
    ((BigFppfOver.toScheme B S hS).map (hιr.snd q)) (h V)

/-- **Quasi-regularity of an immersion is quasi-regularity of its closed factor on charts.**  An
immersion `i : Z ⟶ X` of algebraic spaces is a quasi-regular immersion (Stacks 06BN, part (3))
exactly when, for every étale scheme chart `V` of the complement `X ∖ ∂Z` of its boundary, the
base change of the closed factorisation `Z ⟶ X ∖ ∂Z` of Stacks 04CE along `V` is a quasi-regular
immersion of schemes. -/
theorem isQuasiRegularImmersion_iff_forall_closedFactor :
    IsQuasiRegularImmersion B S hS i ↔
      ∀ V : SmallEtale B S hS (immersionAmbient B S hS hX hZ i hi).1,
        quasiRegularImmersionProperty ((BigFppfOver.toScheme B S hS).map
          ((isClosedImmersion_immersionClosedFactorization B S hS hX hZ i hi).1.snd V.1.hom)) :=
  ⟨fun h V => quasiRegularImmersionProperty_closedFactor_of_isQuasiRegularImmersion
      B S hS hX hZ i hi h V,
    isQuasiRegularImmersion_of_quasiRegularImmersionProperty_closedFactor B S hS hX hZ i hi⟩

/-- **Local finite presentation of an immersion gives local finite presentation of the base
changes of its closed factor.**  If `i : Z ⟶ X` is locally of finite presentation, then so is
the base change of its closed factor `Z ⟶ X ∖ ∂Z` along every étale scheme chart `V` of
`X ∖ ∂Z`. -/
theorem locallyOfFinitePresentation_closedFactor_baseChange
    (h : IsLocallyOfFinitePresentation B S hS i)
    (V : SmallEtale B S hS (immersionAmbient B S hS hX hZ i hi).1) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      ((isClosedImmersion_immersionClosedFactorization B S hS hX hZ i hi).1.snd V.1.hom)) := by
  set hk := (isClosedImmersion_immersionClosedFactorization B S hS hX hZ i hi).1
  have hfst := presheaf_etale_fst_of_isPullback B S hS (hk.isPullback V.1.hom) V.property
  refine h _ V.1.left (hk.fst V.1.hom)
    (V.1.hom ≫ (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).ι)
    (hk.snd V.1.hom) hfst (presheaf_etale_comp_ι_immersionAmbient B S hS hX hZ i hi V) ?_
  have hw := hk.w V.1.hom
  calc yoneda.map (hk.snd V.1.hom) ≫ V.1.hom ≫
        (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).ι
      = (yoneda.map (hk.snd V.1.hom) ≫ V.1.hom) ≫
        (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).ι :=
        (Category.assoc _ _ _).symm
    _ = (hk.fst V.1.hom ≫ (immersionClosedFactorization B S hS hX hZ i hi).hom) ≫
        (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).ι := by rw [hw]
    _ = hk.fst V.1.hom ≫ i := (Category.assoc _ _ _).trans
        (congrArg (hk.fst V.1.hom ≫ ·) (immersionClosedFactorization_hom_comp_ι B S hS hX hZ i hi))

end ClosedFactor

end AlgebraicGeometry.Space

end
