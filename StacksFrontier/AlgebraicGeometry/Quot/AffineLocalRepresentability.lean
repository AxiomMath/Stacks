module

public import StacksFrontier.AlgebraicGeometry.Quot.TestSchemeTotalSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Descent.AffineFinitePresentationCoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveStepOne
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Representability by an algebraic space affine and of finite presentation, from affine data

Let `Y` be an algebraic space over a scheme `S` of a big fppf site and `R` a functor on the test
schemes over `Y`.  Each representability statement of the `Quot` chapter (Stacks 08JX, 08JY,
08K6, 08K9) asserts that some such `R` *is an algebraic space affine and of finite presentation
over `Y`*, `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver`.  This file
reduces that to two inputs: the sheaf property of `R` for the fpqc topology, and representability
of `R`, over every affine test scheme `Z` and on the members `c ⟶ Z` of a family generating a
covering sieve of `Z` (for instance one surjective étale `c ⟶ Z`), by a scheme affine and of
finite presentation over `c`.

## Main definitions

* `AlgebraicGeometry.Space.IsAffineFinitePresentationRepresentedOver` and
  `AlgebraicGeometry.Space.IsAffineFinitePresentationRepresentedOverLift`: `R` is represented over
  the affine test scheme `Z` by an affine scheme of finite presentation over `Z`, for `R` with
  values in `Type u` and in `Type (u + 1)` respectively.

## Main results

* `AlgebraicGeometry.Space.isAffineFinitePresentation_of_sieveLocal`,
  `AlgebraicGeometry.Space.isAffineFinitePresentation_of_etaleLocal` and
  `AlgebraicGeometry.Space.isAffineFinitePresentation_of_affineLocal`: the criterion for `R` with
  values in `Type u`, from representability on a covering, étale-local and affine.
* `AlgebraicGeometry.Space.small_of_isSheaf_of_small_affine`: an fpqc sheaf with `u`-small values
  at the affine test schemes has `u`-small values.
* `AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_of_sieveLocal`,
  `AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_of_etaleLocal` and
  `AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_of_affineLocal`: **the
  criterion**, for `R` with values in `Type (u + 1)`, the value universe of the relative Hom
  functor of Stacks 08JT.

## Implementation notes

The representing algebraic space is the total space of `R`,
`AlgebraicGeometry.Space.totalSpace`.  It is an fppf sheaf because `R` is an fpqc sheaf
(`AlgebraicGeometry.Space.isSheaf_of_isSheaf_presheafPointsOver`); over every affine test scheme
it is represented by the given schemes on the members of the covering
(`AlgebraicGeometry.Space.isPullback_pointsIsoToHom`), hence on `Z` itself by effective descent
along covering sieves of affine morphisms locally of finite presentation
(`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_affineLocallyOfFinitePresentation`),
so its projection to `Y` is affine in the sense of Stacks 03WF.  Representability over an
arbitrary scheme `T` over `Y` is the glueing of relative Tag 03JH,
`AlgebraicGeometry.Space.exists_representing_over_of_openCover`, over the affine opens of `T`;
the glued scheme lies in the size-bounded site because each piece is of finite type over an
affine open of `T`, so has size at most that of `T`
(`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact`), and there are at most
that many affine opens.  The total space is then an algebraic space by
`AlgebraicGeometry.IsAlgebraicSpace.of_relativelyRepresentable`, and the projection is of finite
presentation by Stacks 03XP, read on the represented base changes.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y : AlgebraicSpaces B S hS}

/-- **A presheaf on the test schemes over `Y` is represented over an affine test scheme `Z`**
by a scheme `W` affine and of finite presentation over `Z`: on the test schemes over `Z` the
presheaf is identified with the points of `W` over `Z`. -/
def IsAffineFinitePresentationRepresentedOver (R : (SchemesOver Y)ᵒᵖ ⥤ Type u)
    (Z : SchemesOver Y) : Prop :=
  ∃ (W : BigFppfOver B S hS) (w : W ⟶ Z.left),
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map w) ∧
        Nonempty (spacePointsOver ((schemeSpaceFunctor B S hS).map w) ≅
          (CostructuredArrow.map Z.hom).op ⋙ R)

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

/-- The test scheme over `Y` obtained by composing a morphism `q : c ⟶ Z.left` of the big fppf
site with the structure morphism of the test scheme `Z`. -/
abbrev precompTest (Z : SchemesOver Y) {c : BigFppfOver B S hS} (q : c ⟶ Z.left) :
    SchemesOver Y :=
  CostructuredArrow.mk (Y := c) ((schemeSpaceFunctor B S hS).map q ≫ Z.hom)

/-- If the affine opens of `X` are the ranges of morphisms `f U`, the `f U` jointly cover `X`. -/
private theorem exists_mem_range_of_range_eq_affineOpen {X : Scheme.{u}}
    {V : X.affineOpens → Scheme.{u}} (f : ∀ U, V U ⟶ X) (hf : ∀ U, Set.range (f U) = U) (y : X) :
    ∃ U, y ∈ Set.range (f U) := by
  have hy : y ∈ (⊤ : X.Opens) := trivial
  rw [← iSup_affineOpens_eq_top] at hy
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  exact ⟨U, by rwa [hf U]⟩

/-- A sheaf on the test schemes over `Y` which is `u`-small on the members of an fpqc cover of `T`
indexed by a `u`-small type is `u`-small at `T`. -/
private theorem small_of_ofArrows_mem_fpqc (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1))
    (hR : Presheaf.IsSheaf (fpqcTopology Y) R) {T : SchemesOver Y} {ι : Type u}
    {TU : ι → SchemesOver Y} (f : ∀ i, TU i ⟶ T)
    (hcov : Presieve.ofArrows TU f ∈ (Scheme.fpqcPrecoverage.comap (testSchemeFunctor Y)) T)
    (hsm : ∀ i, Small.{u} (R.obj (op (TU i)))) : Small.{u} (R.obj (op T)) := by
  have hsheaf : Presieve.IsSheafFor R (Presieve.ofArrows TU f) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact ((isSheaf_iff_isSheaf_of_type _ _).1 hR) _
      (Precoverage.generate_mem_toGrothendieck hcov)
  refine small_of_injective (f := fun t (i : ι) => R.map (f i).op t)
    fun t₁ t₂ h => hsheaf.isSeparatedFor.ext fun Z g hg => ?_
  obtain ⟨i⟩ := hg
  exact congrFun h i

/-- A surjective étale morphism `q : c ⟶ Z` with `P` at `precompTest Z q` gives a covering family
of `Z` all of whose members satisfy `P`. -/
private theorem exists_sieve_of_surjective_etale (Z : SchemesOver Y)
    (P : SchemesOver Y → Prop) {c : BigFppfOver B S hS} (q : c ⟶ Z.left)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q)) (hrep : P (precompTest Z q)) :
    ∃ T : Presieve Z.left, Sieve.generate T ∈ BigFppfOver.topology B S hS Z.left ∧
      ∀ ⦃c : BigFppfOver B S hS⦄ (q : c ⟶ Z.left), T q → P (precompTest Z q) := by
  have hqf : Flat ((BigFppfOver.toScheme B S hS).map q) := inferInstance
  have hqp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) := inferInstance
  refine ⟨Presieve.singleton q,
    sieve_generate_singleton_mem_topology_over_of_flat B S hS q hqs hqf hqp, ?_⟩
  rintro c' q' ⟨⟩
  exact hrep

/-- If `P` holds at `Z`, it holds at `precompTest Z (𝟙 Z.left)`, the identity being surjective
étale. -/
private theorem exists_surjective_etale_of_self (Z : SchemesOver Y) (P : SchemesOver Y → Prop)
    (h : P Z) : ∃ (c : BigFppfOver B S hS) (q : c ⟶ Z.left),
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
        Etale ((BigFppfOver.toScheme B S hS).map q) ∧ P (precompTest Z q) := by
  refine ⟨Z.left, 𝟙 _, ?_, ?_, ?_⟩
  · simp only [CategoryTheory.Functor.map_id]
    infer_instance
  · simp only [CategoryTheory.Functor.map_id]
    infer_instance
  · have h' : (schemeSpaceFunctor B S hS).map (𝟙 Z.left) ≫ Z.hom = Z.hom := by simp
    simp only [precompTest]
    rw [h']
    exact h

/-- **The representability criterion, at a presheaf with values in `Type u`.**  A presheaf on the
test schemes over `Y` which is an fpqc sheaf and is represented over every affine test scheme by
an affine scheme of finite presentation is the functor of points of an algebraic space affine and
of finite presentation over `Y`. -/
theorem isAffineFinitePresentation_of_sieveLocal (R : (SchemesOver Y)ᵒᵖ ⥤ Type u)
    (hR : Presheaf.IsSheaf (fpqcTopology Y) R)
    (hloc : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      ∃ T : Presieve Z.left, Sieve.generate T ∈ BigFppfOver.topology B S hS Z.left ∧
        ∀ ⦃c : BigFppfOver B S hS⦄ (q : c ⟶ Z.left), T q →
          IsAffineFinitePresentationRepresentedOver R (precompTest Z q)) :
    ∃ (H : AlgebraicSpaces B S hS) (p : H ⟶ Y), IsAffineHom B S hS p.hom ∧
      IsFinitePresentation B S hS p.hom ∧ Nonempty (spacePointsOver p ≅ R) := by
  classical
  let H₀ := totalSpace R
  let p₀ : H₀ ⟶ Y.1 := totalSpaceProj R
  let e₀ : presheafPointsOver p₀ ≅ R := presheafPointsOverTotalSpaceIso R
  have hH₀ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H₀ :=
    isSheaf_of_isSheaf_presheafPointsOver p₀ ((Presheaf.isSheaf_of_iso_iff e₀).2 hR)
  -- the local squares
  have hsq : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      ∃ (W : BigFppfOver B S hS) (w : W ⟶ Z.left) (q : yoneda.obj W ⟶ H₀),
        IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map w) ∧
        IsPullback q (yoneda.map w) p₀ Z.hom.hom := by
    intro Z hZ
    obtain ⟨T, hT, hTloc⟩ := hloc Z hZ
    have hPbc := affineLocallyOfFinitePresentation_isStableUnderBaseChange.{u}
    have hP : (affineLocallyOfFinitePresentation.{u}.inverseImage
        (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd p₀ Z.hom.hom) := by
      refine isEffectiveDescentAlongCoveringSieve_affineLocallyOfFinitePresentation B S hS
        p₀ hH₀ Y.2.isSheaf Z.hom.hom _ hT fun c' q' hq' => ?_
      obtain ⟨c, u', q, hq, rfl⟩ := hq'
      obtain ⟨W, w, hwa, hw, ⟨φ⟩⟩ := hTloc q hq
      let φ' := φ ≪≫ Functor.isoWhiskerLeft _ e₀.symm
      have sq : IsPullback (pointsIsoToHom φ') (yoneda.map w) p₀ (yoneda.map q ≫ Z.hom.hom) :=
        isPullback_pointsIsoToHom φ'
      have hq₀ : (affineLocallyOfFinitePresentation.{u}.inverseImage
          (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd p₀ (yoneda.map q ≫ Z.hom.hom)) :=
        presheaf_pullback_snd_of_isPullback sq (P := affineLocallyOfFinitePresentation.{u})
          ⟨hwa, hw⟩
      have heq : yoneda.map (u' ≫ q) ≫ Z.hom.hom = yoneda.map u' ≫ (yoneda.map q ≫ Z.hom.hom) := by
        rw [Functor.map_comp]
        exact Category.assoc _ _ _
      have s₁ : IsPullback (pullback.fst p₀ (yoneda.map (u' ≫ q) ≫ Z.hom.hom))
          (pullback.snd p₀ (yoneda.map (u' ≫ q) ≫ Z.hom.hom)) p₀
          (yoneda.map u' ≫ (yoneda.map q ≫ Z.hom.hom)) := by
        rw [← heq]
        exact IsPullback.of_hasPullback _ _
      have _hbc := MorphismProperty.relative_isStableUnderBaseChange
        (affineLocallyOfFinitePresentation.{u}.inverseImage
          (BigFppfOver.toScheme B S hS)) (F := yoneda (C := BigFppfOver B S hS))
      exact MorphismProperty.of_isPullback
        (s₁.of_right' (IsPullback.of_hasPullback p₀ (yoneda.map q ≫ Z.hom.hom))) hq₀
    let g := 𝟙 (yoneda.obj Z.left)
    have hsqZ := (hP.rep.isPullback g).paste_horiz (IsPullback.of_hasPullback p₀ Z.hom.hom)
    have hPsnd : affineLocallyOfFinitePresentation.{u}
        ((BigFppfOver.toScheme B S hS).map (hP.rep.snd g)) := hP.property_snd g
    have : _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B S hS).map (hP.rep.snd g)) := hPsnd.1
    refine ⟨hP.rep.pullback g, hP.rep.snd g, hP.rep.fst g ≫ pullback.fst p₀ Z.hom.hom,
      isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hP.rep.snd g)), hPsnd.2, ?_⟩
    have hg : g ≫ Z.hom.hom = Z.hom.hom := Category.id_comp _
    exact IsPullback.of_iso hsqZ (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp)
      (((Category.comp_id _).trans hg).trans (Category.id_comp _).symm)
  -- representability, with the represented base changes locally of finite presentation
  have hZL : IsZariskiLocalAtTarget
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @AlgebraicGeometry.LocallyOfFinitePresentation.{u}) (Q := RingHom.FinitePresentation)
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hRI : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hrep : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p₀ := by
    refine MorphismProperty.relative.of_exists ?_
    intro T g
    have hpbT : IsPullback (pullback.fst p₀ g) (pullback.snd p₀ g) p₀ g :=
      IsPullback.of_hasPullback p₀ g
    have hF := BigFppfOver.isSheaf_pullback_yoneda_obj p₀ g hH₀ Y.2.isSheaf
    choose V u hu hurange hVaff using fun U => BigFppfOver.exists_affineOpen_restrict B S hS T U
    choose W w q hW hw hpb using fun U => hsq (CostructuredArrow.mk (Y := V U)
      ((schemeSpaceFunctor B S hS).map (u U) ≫ (ObjectProperty.homMk g :
        (schemeSpaceFunctor B S hS).obj T ⟶ Y))) (hVaff U)
    let q' : ∀ U, yoneda.obj (W U) ⟶ pullback p₀ g := fun U =>
      pullback.lift (q U) (yoneda.map (w U) ≫ yoneda.map (u U)) (by
        rw [(hpb U).w, Category.assoc]; rfl)
    have hpb' : ∀ U, IsPullback (q' U) (yoneda.map (w U)) (pullback.snd p₀ g) (yoneda.map (u U)) :=
      fun U => IsPullback.of_right (by simp only [q', pullback.lift_fst]; exact hpb U)
        (by simp only [q', pullback.lift_snd]) hpbT
    have hucov := exists_mem_range_of_range_eq_affineOpen
      (fun U => (BigFppfOver.toScheme B S hS).map (u U)) hurange
    have hcont : ∀ (Zg : Scheme.{u}) (k : ∀ U, (BigFppfOver.toScheme B S hS).obj (W U) ⟶ Zg),
        (∀ U, _root_.AlgebraicGeometry.IsOpenImmersion (k U)) →
          (∀ z : Zg, ∃ U, z ∈ Set.range (k U)) → B.Contains Zg := by
      intro Zg k hk hkcov
      have : Nonempty ((BigFppfOver.toScheme B S hS).obj T).affineOpens :=
        ⟨⟨⊥, isAffineOpen_bot _⟩⟩
      have := hk
      refine B.contains_of_openCover_of_size_le (μ := ((BigFppfOver.toScheme B S hS).obj T).size)
        T.left.2 (Scheme.mk_affineOpens_le_size _) k hkcov fun U => ?_
      have := hw U
      have := hVaff U
      have := hW U
      have := hu U
      have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (w U)) :=
        @_root_.AlgebraicGeometry.isAffineHom_of_isAffine _ _ _ (hW U) (hVaff U)
      exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
        ((BigFppfOver.toScheme B S hS).map (w U))).trans
        (Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map (u U)))
    obtain ⟨Y', e, P, hP, hQP⟩ := exists_representing_over_of_openCover B S hS
      (Q := @AlgebraicGeometry.LocallyOfFinitePresentation.{u}) hZL hF
      (pullback.snd p₀ g) (V := V) (W := W) (u := u) (p := w) (q := q') hu hucov hpb' hw hcont
    exact ⟨Y', e.inv ≫ pullback.fst p₀ g, P,
      hpbT.of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simpa using hP) (by simp) (by simp), hQP⟩
  have hH₀alg : IsAlgebraicSpace B S hS H₀ :=
    IsAlgebraicSpace.of_relativelyRepresentable hH₀ Y.2 hrep.rep
  let H : AlgebraicSpaces B S hS := ⟨H₀, hH₀alg⟩
  let p : H ⟶ Y := ObjectProperty.homMk p₀
  have haff : IsAffineHom B S hS p₀ := by
    intro Z g
    obtain ⟨W, w, q, hW, -, hpb⟩ := hsq
      (CostructuredArrow.mk (Y := (BigAffineFppf.inclusion B S hS).obj Z)
        (ObjectProperty.homMk g : (schemeSpaceFunctor B S hS).obj _ ⟶ Y)) Z.2
    exact ⟨⟨W, hW⟩, q, w, hpb⟩
  refine ⟨H, p, haff, ⟨?_, ?_, ?_⟩, ⟨spacePointsOverIsoPresheafPointsOver p ≪≫ e₀⟩⟩
  · exact (isLocallyOfFinitePresentation_iff_presheaf B S hS hH₀alg Y.2 hrep.rep).2 hrep
  · exact isQuasiCompact_of_isAffineHom' B S hS p₀ hH₀alg Y.2 haff
  · exact isQuasiSeparated_of_isSeparated B S hS
      (isSeparated_of_isAffineHom B S hS p₀ hH₀alg Y.2 haff)

/-- **The representability criterion, at a presheaf with values in `Type u`, from étale-local
representability.** -/
theorem isAffineFinitePresentation_of_etaleLocal (R : (SchemesOver Y)ᵒᵖ ⥤ Type u)
    (hR : Presheaf.IsSheaf (fpqcTopology Y) R)
    (hloc : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      ∃ (c : BigFppfOver B S hS) (q : c ⟶ Z.left),
        Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
          Etale ((BigFppfOver.toScheme B S hS).map q) ∧
            IsAffineFinitePresentationRepresentedOver R (precompTest Z q)) :
    ∃ (H : AlgebraicSpaces B S hS) (p : H ⟶ Y), IsAffineHom B S hS p.hom ∧
      IsFinitePresentation B S hS p.hom ∧ Nonempty (spacePointsOver p ≅ R) := by
  refine isAffineFinitePresentation_of_sieveLocal R hR fun Z hZ => ?_
  obtain ⟨c, q, hqs, hqe, hrep⟩ := hloc Z hZ
  exact exists_sieve_of_surjective_etale Z _ q hqs hqe hrep

/-- **The representability criterion, at a presheaf with values in `Type u`, from affine
representability.**  A presheaf on the test schemes over `Y` which is an fpqc sheaf and is
represented over every affine test scheme by a scheme affine and of finite presentation over it
is the functor of points of an algebraic space affine and of finite presentation over `Y`. -/
theorem isAffineFinitePresentation_of_affineLocal (R : (SchemesOver Y)ᵒᵖ ⥤ Type u)
    (hR : Presheaf.IsSheaf (fpqcTopology Y) R)
    (hloc : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      IsAffineFinitePresentationRepresentedOver R Z) :
    ∃ (H : AlgebraicSpaces B S hS) (p : H ⟶ Y), IsAffineHom B S hS p.hom ∧
      IsFinitePresentation B S hS p.hom ∧ Nonempty (spacePointsOver p ≅ R) := by
  exact isAffineFinitePresentation_of_etaleLocal R hR fun Z hZ =>
    exists_surjective_etale_of_self Z (IsAffineFinitePresentationRepresentedOver R) (hloc Z hZ)

/-- A presheaf on the test schemes over `Y` which is a sheaf for the fpqc topology and has
`u`-small values at the affine test schemes has `u`-small values everywhere: the values at a
test scheme embed into the product of the values at its affine opens. -/
theorem small_of_isSheaf_of_small_affine (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1))
    (hR : Presheaf.IsSheaf (fpqcTopology Y) R)
    (hsm : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      Small.{u} (R.obj (op Z))) (T : SchemesOver Y) : Small.{u} (R.obj (op T)) := by
  classical
  choose V u hu hurange hVaff using fun U => BigFppfOver.exists_affineOpen_restrict B S hS T.left U
  let TU : ((BigFppfOver.toScheme B S hS).obj T.left).affineOpens → SchemesOver Y := fun U =>
    CostructuredArrow.mk (Y := V U) ((schemeSpaceFunctor B S hS).map (u U) ≫ T.hom)
  let ι : ∀ U, TU U ⟶ T := fun U => liftTestAlong T (u U)
  have hcov : Presieve.ofArrows TU ι ∈ (Scheme.fpqcPrecoverage.comap (testSchemeFunctor Y)) T := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    refine Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ ?_
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨exists_mem_range_of_range_eq_affineOpen
      (fun U => (BigFppfOver.toScheme B S hS).map (u U)) hurange, fun U => hu U⟩
  exact small_of_ofArrows_mem_fpqc R hR ι hcov fun U => hsm (TU U) (hVaff U)

/-- **A presheaf on the test schemes over `Y`, with values in `Type (u + 1)`, is represented
over an affine test scheme `Z` by an affine scheme `W` of finite presentation over `Z`**: on the
test schemes over `Z` it is identified with the universe lift of the points of `W` over `Z`. -/
def IsAffineFinitePresentationRepresentedOverLift (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1))
    (Z : SchemesOver Y) : Prop :=
  ∃ (W : BigFppfOver B S hS) (w : W ⟶ Z.left),
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map w) ∧
        Nonempty (spacePointsOver ((schemeSpaceFunctor B S hS).map w) ⋙ uliftFunctor.{u + 1, u} ≅
          (CostructuredArrow.map Z.hom).op ⋙ R)

/-- Removing a universe lift from both sides of an isomorphism of functors to types. -/
def isoOfIsoCompUliftFunctor {C : Type*} [Category* C] {F G : C ⥤ Type u}
    (e : F ⋙ uliftFunctor.{u + 1, u} ≅ G ⋙ uliftFunctor.{u + 1, u}) : F ≅ G :=
  NatIso.ofComponents (fun X => Equiv.toIso (Equiv.ulift.symm.trans
      ((e.app X).toEquiv.trans Equiv.ulift)))
    (fun {X X'} f => by
      ext (x : F.obj X)
      exact congrArg ULift.down
        (NatTrans.naturality_apply e.hom f (ULift.up x : (F ⋙ uliftFunctor.{u + 1, u}).obj X)))

/-- The test scheme over `Z` given by the identity of its underlying object. -/
abbrev identityTest (Z : SchemesOver Y) : SchemesOver ((schemeSpaceFunctor B S hS).obj Z.left) :=
  CostructuredArrow.mk (Y := Z.left) (𝟙 _)

/-- The identity test scheme over `Z`, read over `Y`, is `Z`. -/
def mapIdentityTestIso (Z : SchemesOver Y) :
    (CostructuredArrow.map Z.hom).obj (identityTest Z) ≅ Z :=
  CostructuredArrow.isoMk (Iso.refl _) (by simp)

/-- The morphism from `precompTest Z q` to `Z` whose underlying morphism is `q`. -/
abbrev precompTestHom (Z : SchemesOver Y) {c : BigFppfOver B S hS} (q : c ⟶ Z.left) :
    precompTest Z q ⟶ Z :=
  CostructuredArrow.homMk q rfl

/-- **The representability criterion of this file, at a presheaf with values in `Type (u + 1)`,
from local representability on a covering.**  A presheaf on the test schemes over `Y` which is an
fpqc sheaf, and which over every affine test scheme `Z` is represented, on the members of a
family generating a covering sieve of `Z`, by schemes affine and of finite presentation over
them, is an algebraic space affine and of finite presentation over `Y`. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_of_sieveLocal
    (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)) (hR : Presheaf.IsSheaf (fpqcTopology Y) R)
    (hloc : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      ∃ T : Presieve Z.left, Sieve.generate T ∈ BigFppfOver.topology B S hS Z.left ∧
        ∀ ⦃c : BigFppfOver B S hS⦄ (q : c ⟶ Z.left), T q →
          IsAffineFinitePresentationRepresentedOverLift R (precompTest Z q)) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y R := by
  classical
  have hsmAff : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      Small.{u} (R.obj (op Z)) := by
    intro Z hZ
    obtain ⟨T, hT, hTloc⟩ := hloc Z hZ
    choose V v hVaff hvT hvflat hvlfp hvmem using
      fun x => BigFppfOver.exists_affine_mem_of_mem_topology B S hS hT x
    have hopen : ∀ x, IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map (v x)).base) := by
      intro x
      have _ := hvflat x
      have _ := hvlfp x
      exact ((BigFppfOver.toScheme B S hS).map (v x)).isOpenMap.isOpen_range
    have hsub : (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj Z.left)) ⊆
        ⋃ x, Set.range ((BigFppfOver.toScheme B S hS).map (v x)).base :=
      fun x _ => Set.mem_iUnion.2 ⟨x, hvmem x⟩
    obtain ⟨t, ht⟩ := (CompactSpace.isCompact_univ
      (X := ((BigFppfOver.toScheme B S hS).obj Z.left))).elim_finite_subcover _ hopen hsub
    let TU : {x // x ∈ t} → SchemesOver Y := fun x => precompTest Z (v x.1)
    let ι : ∀ x, TU x ⟶ Z := fun x => precompTestHom Z (v x.1)
    have hcov :
        Presieve.ofArrows TU ι ∈ (Scheme.fpqcPrecoverage.comap (testSchemeFunctor Y)) Z := by
      rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
      refine Scheme.fppfPrecoverage_le_fpqcPrecoverage _ ?_
      rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨fun y => ?_, fun x => ⟨hvflat x.1, hvlfp x.1⟩⟩
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
      exact ⟨⟨x, hx⟩, hyx⟩
    have hsmall : ∀ x, Small.{u} (R.obj (op (TU x))) := by
      intro x
      obtain ⟨c, u', q, hq, huq⟩ := hvT x.1
      obtain ⟨W, w, -, -, ⟨ψ⟩⟩ := hTloc q hq
      let A : SchemesOver ((schemeSpaceFunctor B S hS).obj c) :=
        CostructuredArrow.mk (Y := V x.1) ((schemeSpaceFunctor B S hS).map u')
      have eA : (CostructuredArrow.map (precompTest Z q).hom).obj A ≅ TU x :=
        CostructuredArrow.isoMk (Iso.refl _) (by
          simp only [TU, precompTest, A, CostructuredArrow.map_obj_hom,
            CostructuredArrow.mk_hom_eq_self]
          rw [← huq, Functor.map_comp]
          simp)
      have e : R.obj (op (TU x)) ≃ ULift.{u + 1}
          ((spacePointsOver ((schemeSpaceFunctor B S hS).map w)).obj (op A)) :=
        (R.mapIso eA.op).toEquiv.trans (ψ.app (op A)).toEquiv.symm
      exact small_map e
    exact small_of_ofArrows_mem_fpqc R hR ι hcov hsmall
  have hsm : FunctorToTypes.Small.{u} R := fun X =>
    small_of_isSheaf_of_small_affine R hR hsmAff X.unop
  let R' := FunctorToTypes.shrink.{u} R
  let eR : R' ⋙ uliftFunctor.{u + 1, u} ≅ R :=
    NatIso.ofComponents (fun X => Equiv.toIso (Equiv.ulift.trans (equivShrink _).symm))
      (fun {X X'} f => by
        ext x
        exact (equivShrink (R.obj X')).symm_apply_apply _)
  have hR' : Presheaf.IsSheaf (fpqcTopology Y) R' := by
    rw [isSheaf_iff_isSheaf_of_type] at hR ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 (Presieve.isSheaf_iso _ eR.symm hR)
  have hloc' : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      ∃ T : Presieve Z.left, Sieve.generate T ∈ BigFppfOver.topology B S hS Z.left ∧
        ∀ ⦃c : BigFppfOver B S hS⦄ (q : c ⟶ Z.left), T q →
          IsAffineFinitePresentationRepresentedOver R' (precompTest Z q) := by
    intro Z hZ
    obtain ⟨T, hT, hTloc⟩ := hloc Z hZ
    refine ⟨T, hT, fun c q hq => ?_⟩
    obtain ⟨W, w, hW, hw, ⟨ψ⟩⟩ := hTloc q hq
    exact ⟨W, w, hW, hw, ⟨isoOfIsoCompUliftFunctor
      (ψ ≪≫ Functor.isoWhiskerLeft _ eR.symm ≪≫ (Functor.associator _ _ _).symm)⟩⟩
  obtain ⟨H, p, haff, hfp, ⟨φ⟩⟩ := isAffineFinitePresentation_of_sieveLocal R' hR' hloc'
  exact ⟨H, p, haff, hfp, ⟨Functor.isoWhiskerRight φ _ ≪≫ eR⟩⟩

/-- **The representability criterion of this file, at a presheaf with values in `Type (u + 1)`,
from étale-local representability.**  A presheaf on the test schemes over `Y` which is an fpqc
sheaf, and which over every affine test scheme `Z` becomes, after a surjective étale base change
`c ⟶ Z`, represented by a scheme affine and of finite presentation over `c`, is an algebraic
space affine and of finite presentation over `Y`. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_of_etaleLocal
    (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)) (hR : Presheaf.IsSheaf (fpqcTopology Y) R)
    (hloc : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      ∃ (c : BigFppfOver B S hS) (q : c ⟶ Z.left),
        Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
          Etale ((BigFppfOver.toScheme B S hS).map q) ∧
            IsAffineFinitePresentationRepresentedOverLift R (precompTest Z q)) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y R := by
  refine isAffineFinitePresentationAlgebraicSpaceOver_of_sieveLocal R hR fun Z hZ => ?_
  obtain ⟨c, q, hqs, hqe, hrep⟩ := hloc Z hZ
  exact exists_sieve_of_surjective_etale Z _ q hqs hqe hrep

/-- **The representability criterion of this file, at a presheaf with values in `Type (u + 1)`,
from affine representability.**  A presheaf on the test schemes over `Y` which is an fpqc sheaf
and is represented over every affine test scheme by a scheme affine and of finite presentation
over it is an algebraic space affine and of finite presentation over `Y`. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_of_affineLocal
    (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)) (hR : Presheaf.IsSheaf (fpqcTopology Y) R)
    (hloc : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      IsAffineFinitePresentationRepresentedOverLift R Z) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y R := by
  exact isAffineFinitePresentationAlgebraicSpaceOver_of_etaleLocal R hR fun Z hZ =>
    exists_surjective_etale_of_self Z (IsAffineFinitePresentationRepresentedOverLift R)
      (hloc Z hZ)

end AlgebraicGeometry.Space
