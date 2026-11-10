module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeOfCoversTop
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitEndomorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstDirectImageLocalGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardLeftTExact
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardFieldSectionsVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityFlatInjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeOfFibreSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardFibreSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTopDegree
public import StacksFrontier.Homology.DerivedCategory.HomologyBiprodSingle

/-!
# The first higher direct image of a proper flat family whose fibres are curves

Let `f : X ⟶ Y` be a proper, flat morphism of finite presentation from an algebraic space to a
scheme, such that `k = H⁰(X_k, 𝒪_{X_k})` for every morphism `Spec k ⟶ Y` from the spectrum of a
field, and such that `Hᵠ(X_k, 𝒪_{X_k}) = 0` for `q ≥ 2` on these fibres. This is the situation
of Stacks 0E1J, where the fibres are curves (Cohomology, Proposition 02UZ). Then, étale locally
on `Y`, `Rf_*𝒪_X ≅ 𝒪 ⊕ 𝒪^{⊕n}[-1]`; consequently `R¹f_*𝒪_X` is finite locally free and
`Rⁱf_*𝒪_X = 0` for `i ≥ 2`.

## The argument

This is the proof of Stacks 0E1J, parts (2). By Stacks 0E6B, part (b), étale locally on `Y` we
have `Rf_*𝒪_X ≅ 𝒪 ⊕ P` with `P` strictly perfect in degrees `≥ 1`
(`Space.exists_presieve_isStrictlyPerfect_iso_derivedModulePushforward_of_baseChange`).
At a geometric point `Spec k ⟶ Y` of a chart, cohomology and base change (Stacks 0CTM, part (1))
identifies the derived fibre of `𝒪 ⊕ P` with `RΓ(X_k, 𝒪)`, which has no cohomology in degrees
`≥ 2`; so the derived fibre of `P` lives in degree `1` alone. By Stacks 0BCD at the point
(`AlgebraicGeometry.Space.exists_pointsMap_mem_singleDegreeFreePoints_of_subsingleton`), `P` is
`𝒪^{⊕n}[-1]` on an étale neighbourhood of the point.

## Main results

* `AlgebraicGeometry.Space.exists_chart_iso_biprod_single_free`: the local form of `Rf_*𝒪_X`.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_rightDerived_one_structureSheafModule`:
  `R¹f_*𝒪_X` is finite locally free.
* `AlgebraicGeometry.Space.isZero_homology_derivedModulePushforward_of_two_le`:
  `Hⁱ(Rf_*𝒪_X) = 0` for `i ≥ 2`.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

/- The standard model of the derived category is forced here: it is the model in which the two
results used below are stated, Stacks 0CTM part (1)
(`isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat`) and the étale-local
splitting of `Rf_*𝒪_X` under the hypotheses of Stacks 0E6B
(`exists_presieve_isStrictlyPerfect_iso_derivedModulePushforward_of_baseChange`). -/
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V₀ : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}

/-- The hypothesis `k = H⁰(X_k, 𝒪_{X_k})` of Stacks 0E6B for the fibres of `f : X ⟶ Y` over the
field-valued points of `Y`. -/
def HasBijectiveFieldFibreGlobalFunctions {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop :=
  ∀ p : FieldValuedPoint B S hS Y.1, Function.Bijective (algebraMap p.carrier
    (globalFunctions B (Spec (.of p.carrier)) p.contained
      (fibreOverFieldValuedPoint B S hS f.hom p)))

/-- `Rf_*𝒪_X`, the derived direct image of the structure sheaf placed in degree `0`. -/
abbrev derivedPushforwardStructure {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
  (derivedModulePushforward B S hS f).obj
    ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))

/-- The derived pullback of a bounded above complex of flat modules in degrees `≥ 1` has no
cohomology, hence no sections of its cohomology sheaves, in degrees `< 1`. -/
theorem subsingleton_unit_hom_homology_smallEtaleDerivedModulePullback_Q_of_lt
    {X₁ X₂ : AlgebraicSpaces B S hS} (c : X₁ ⟶ X₂)
    (P : CochainComplex (Modules.{u, u} B S hS X₂.1 X₂.2) ℤ) (r : ℤ)
    (hLE : P.IsStrictlyLE r) (hP1 : P.IsStrictlyGE 1)
    (hflat : ∀ k, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS X₂).O) (P.X k)) (j : ℤ) (hj : j < 1)
    (U : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₁)) :
    Subsingleton (U ⟶ (DerivedCategory.homologyFunctor _ j).obj
      ((smallEtaleDerivedModulePullback B S hS c).obj (DerivedCategory.Q.obj P))) := by
  have : (modulePullback B S hS c).Additive := modulePullback_additive c
  obtain ⟨e₁⟩ := @nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback _ _ _ _ _ c P r
    hLE hflat
  have : CochainComplex.IsStrictlyGE
      (((modulePullback B S hS c).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) 1 :=
    (CochainComplex.isStrictlyGE_iff _ 1).2 fun k hk =>
      (modulePullback B S hS c).map_isZero (P.isZero_of_isStrictlyGE 1 k hk)
  have hz := (DerivedCategory.isZero_of_isGE
    ((DerivedCategory.Q).obj
      (((modulePullback B S hS c).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    1 j hj).of_iso ((DerivedCategory.homologyFunctor _ j).mapIso e₁)
  exact ⟨fun a b => hz.eq_of_tgt a b⟩

/-- If `F(D)` admits at most one morphism from `U` and `φ : E ⟶ D` is a split monomorphism,
then `F(E)` admits at most one morphism from `U`. -/
theorem subsingleton_hom_obj_of_isSplitMono {𝒜 𝒞 : Type*} [Category 𝒜] [Category 𝒞]
    (F : 𝒜 ⥤ 𝒞) (U : 𝒞) {E D : 𝒜} (hD : Subsingleton (U ⟶ F.obj D)) (φ : E ⟶ D)
    (hφ : IsSplitMono φ) : Subsingleton (U ⟶ F.obj E) :=
  ⟨fun _ _ => (cancel_mono (F.map φ)).1 (hD.elim _ _)⟩

/-- If `F(K)` admits at most one morphism from `U` and `K ≅ A ⊞ E`, then `F(E)` admits at most
one morphism from `U`: the inclusion `E ⟶ A ⊞ E ≅ K` is a split monomorphism. The zero morphisms
and the biproduct are implicit arguments, so they are read off the type of `e`. -/
theorem subsingleton_hom_obj_of_iso_biprod {𝒜 𝒞 : Type*} [Category 𝒜] [Category 𝒞]
    {_ : HasZeroMorphisms 𝒜} (F : 𝒜 ⥤ 𝒞) (U : 𝒞) {K A E : 𝒜} {_ : HasBinaryBiproduct A E}
    (e : K ≅ A ⊞ E) (hK : Subsingleton (U ⟶ F.obj K)) : Subsingleton (U ⟶ F.obj E) :=
  subsingleton_hom_obj_of_isSplitMono F U hK (biprod.inr ≫ e.inv)
    (IsSplitMono.mk' ⟨e.hom ≫ biprod.snd, by simp⟩)

/-- **A complex `𝒪 ⊕ P` whose geometric fibre has no sections in degrees `≥ 2` is
`𝒪 ⊕ 𝒪^{⊕n}[-1]` near the point.** Let `K ≅ 𝒪_Z ⊕ P` in `D(𝒪_Z)` with `P` strictly perfect in
degrees `≥ 1`, and let `c : Spec k ⟶ Z` be a geometric point such that the cohomology sheaves
`Hᵐ(Lc^*K)`, `m ≥ 2`, have no nonzero global sections. Then `Lc^*P` has sections in degree `1`
alone, so by Stacks 0BCD at the point there is an étale chart `W` of `Z` through the image of
`c` on which `K` restricts to `𝒪_W ⊕ 𝒪_W^{⊕n}[-1]`. -/
theorem exists_chart_iso_biprod_single_free_of_iso_biprod {Z : AlgebraicSpaces B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (P : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ)
    (hPs : IsStrictlyPerfect.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O) P)
    (hP1 : P.IsStrictlyGE 1)
    (eP : K ≅ (DerivedCategory.singleFunctor _ 0).obj (structureModule Z) ⊞
      DerivedCategory.Q.obj P)
    (p : GeometricPoint B S hS F)
    (c : (⟨yoneda.obj p.val.siteObject, isAlgebraicSpace_yoneda B S hS p.val.siteObject⟩ :
      AlgebraicSpaces B S hS) ⟶ Z)
    (hK : ∀ m : ℕ, 2 ≤ m → Subsingleton (SheafOfModules.unit _ ⟶
      (DerivedCategory.homologyFunctor _ (m : ℤ)).obj
        ((smallEtaleDerivedModulePullback B S hS c).obj K))) :
    ∃ (W : SmallEtale B S hS Z.1) (n : ℕ),
      pointsMap B S hS _ c.hom (GeometricPoint.tautological B S hS p).image ∈
        Set.range (pointsMap B S hS (yoneda.obj W.1.left) W.1.hom) ∧
      Nonempty ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Z W)).obj K ≅
        (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _) ⊞
          (DerivedCategory.singleFunctor _ 1).obj (SheafOfModules.free
            (R := ringedToposStructureRingSheaf B S hS (chartSpace B S hS Z W))
            (ULift.{u} (Fin n)))) := by
  classical
  obtain ⟨r, hr⟩ := hPs.bounded.bddAbove
  have hLE : P.IsStrictlyLE r := by
    refine (CochainComplex.isStrictlyLE_iff P r).2 fun j hj => ?_
    by_contra hz
    exact absurd (hr (by simpa only [Set.mem_ofPred_eq] using hz)) (by omega)
  have hflat : ∀ k, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Z).O) (P.X k) := fun k =>
    Stacks.SheafOfModules.isFlat_of_isRetractOfFiniteFree
      (Y := smallEtaleRingedSite B S hS Z.1 Z.2) (P.X k)
      (Stacks.SheafOfModules.isRetractOfFiniteFree_of_isDirectSummandOfFiniteFree
        (smallEtaleRingedSite B S hS Z.1 Z.2).O (hPs.termDirectSummand k))
  have hc : ∀ j : ℤ, j ≠ 1 → Subsingleton (SheafOfModules.unit _ ⟶
      (DerivedCategory.homologyFunctor _ j).obj
        ((smallEtaleDerivedModulePullback B S hS c).obj (DerivedCategory.Q.obj P))) := by
    intro j hj
    rcases lt_or_gt_of_ne hj with h₁ | h₁
    · exact subsingleton_unit_hom_homology_smallEtaleDerivedModulePullback_Q_of_lt B S hS c P r
        hLE hP1 hflat j h₁ _
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = j := ⟨j.toNat, by omega⟩
      exact subsingleton_hom_obj_of_iso_biprod
        (smallEtaleDerivedModulePullback B S hS c ⋙ DerivedCategory.homologyFunctor _ (m : ℤ))
        _ eP (hK m (by omega))
  obtain ⟨-, W, hW, n, -, ⟨eW⟩⟩ := exists_pointsMap_mem_singleDegreeFreePoints_of_subsingleton
    B S hS (DerivedCategory.Q.obj P) (RingedSite.isPerfect_Q_obj_of_isStrictlyPerfect _ P hPs) 1 p
    c hc
  have : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Z W)).Additive :=
    additive_smallEtaleDerivedModulePullback B S hS _
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Z W))
  exact ⟨W, n, hW, ⟨(smallEtaleDerivedModulePullback B S hS _).mapIso eP ≪≫
    (smallEtaleDerivedModulePullback B S hS _).mapBiprod _ _ ≪≫
      biprod.mapIso (smallEtaleDerivedModulePullbackUnitIso _) eW⟩⟩

/-- **Restricting to a chart of a chart.** If the derived restriction of `K` to a chart `W₀` of a
chart `V` of `Y` is `𝒪 ⊕ 𝒪^{⊕n}[-1]`, so is its derived restriction to the composite chart
`W₀ ⟶ V ⟶ Y`. -/
theorem nonempty_chartLocalization_iso_biprod_single_free {Y : AlgebraicSpaces B S hS}
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (V : SmallEtale B S hS Y.1) (W₀ : SmallEtale B S hS (chartSpace B S hS Y V).1) (n : ℕ)
    (e : (smallEtaleDerivedModulePullback B S hS
        (chartToSpace B S hS (chartSpace B S hS Y V) W₀)).obj
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y V)).obj K) ≅
      (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _) ⊞
        (DerivedCategory.singleFunctor _ 1).obj (SheafOfModules.free
          (R := ringedToposStructureRingSheaf B S hS (chartSpace B S hS (chartSpace B S hS Y V) W₀))
          (ULift.{u} (Fin n)))) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y
        ((SmallEtale.chartLocalization B S hS Y.1 V).obj W₀).left)).obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _) ⊞
        (DerivedCategory.singleFunctor _ 1).obj (SheafOfModules.free
          (R := ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y
            ((SmallEtale.chartLocalization B S hS Y.1 V).obj W₀).left))
          (ULift.{u} (Fin n)))) :=
  ⟨(smallEtaleDerivedModulePullbackCongr B S hS
      (show chartToSpace B S hS Y ((SmallEtale.chartLocalization B S hS Y.1 V).obj W₀).left =
        chartToSpace B S hS (chartSpace B S hS Y V) W₀ ≫ chartToSpace B S hS Y V from
        InducedCategory.hom_ext rfl)).app _ ≪≫
    ((smallEtaleDerivedModulePullbackCompIso B S hS
      (chartToSpace B S hS (chartSpace B S hS Y V) W₀) (chartToSpace B S hS Y V)).app _).symm ≪≫ e⟩

/-- The base change isomorphism `Lg^*Rf_*𝒪_X ≅ Rf'_*𝒪_{X'}` of a cartesian square. -/
private def baseChangeIsoStructure {X' Y' Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (hiso : IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w
      ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)))) :
    (smallEtaleDerivedModulePullback B S hS g).obj (derivedPushforwardStructure B S hS f) ≅
      (derivedModulePushforward B S hS f').obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X')) :=
  @asIso _ _ _ _ _ hiso ≪≫
    (derivedModulePushforward B S hS f').mapIso (smallEtaleDerivedModulePullbackUnitIso g')

/-- **`Rf_*𝒪_X ≅ 𝒪 ⊕ 𝒪^{⊕n}[-1]` étale locally**, for a proper flat morphism of finite
presentation whose fibres over fields have `H⁰ = k` and no cohomology above degree `1`. Every
point of the base lies in the image of an étale chart `W` on which the derived restriction of
`Rf_*𝒪_X` is `𝒪_W ⊕ 𝒪_W^{⊕n}[-1]` for some `n`. -/
theorem exists_chart_iso_biprod_single_free (f : X ⟶ schemeSpace V₀)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (h : HasBijectiveFieldFibreGlobalFunctions B S hS f)
    (hvan : HasVanishingFieldFibreCohomologyAboveOne B S hS f)
    (y : points B S hS (schemeSpace V₀).1) :
    ∃ (W : SmallEtale B S hS (schemeSpace V₀).1) (n : ℕ),
      y ∈ Set.range (pointsMap B S hS (yoneda.obj W.1.left) W.1.hom) ∧
      Nonempty ((smallEtaleDerivedModulePullback B S hS
          (chartToSpace B S hS (schemeSpace V₀) W)).obj (derivedPushforwardStructure B S hS f) ≅
        (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _) ⊞
          (DerivedCategory.singleFunctor _ 1).obj (SheafOfModules.free
            (R := ringedToposStructureRingSheaf B S hS (chartSpace B S hS (schemeSpace V₀) W))
            (ULift.{u} (Fin n)))) := by
  classical
  -- cohomology and base change (Stacks 0CTM, part (1)) for `f` and for its restrictions
  have H := fun V : SmallEtale B S hS (schemeSpace V₀).1 =>
    isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat
      (pullback.snd f (chartToSpace B S hS (schemeSpace V₀) V))
      ((isProper_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback f (chartToSpace B S hS (schemeSpace V₀) V)) hf)
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback f (chartToSpace B S hS (schemeSpace V₀) V)) hfl)
      ((isFinitePresentation_isStableUnderBaseChange (B := B) (S := S) (hS := hS)).of_isPullback
        (IsPullback.of_hasPullback f (chartToSpace B S hS (schemeSpace V₀) V)) hfp)
      _ (isPerfect_unit (pullback f (chartToSpace B S hS (schemeSpace V₀) V)))
  have H₀ := isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp _
    (isPerfect_unit X)
  -- Stacks 0E6B, part (b): `Rf_{V*}𝒪 ≅ 𝒪 ⊕ P` on a covering family of charts `V`
  obtain ⟨R, hR, hP⟩ := exists_presieve_isStrictlyPerfect_iso_derivedModulePushforward_of_baseChange
    B S hS f hf hfl hfp h (fun V => (H V).1) (fun V _ _ g _ f' i sq => (H V).2 _ f' i sq)
    (selfChart B S hS V₀)
  let ι := {q : Σ V : SmallEtale B S hS (schemeSpace V₀).1, V ⟶ selfChart B S hS V₀ // R q.2}
  have hcov : (SmallEtale.topology B S hS (schemeSpace V₀).1).CoversTop (fun i : ι => i.1.1) := by
    refine (GrothendieckTopology.coversTop_iff_of_isTerminal
      (SmallEtale.topology B S hS (schemeSpace V₀).1)
      (selfChart B S hS V₀) (isTerminal_selfChart B S hS V₀) _).2 ?_
    refine GrothendieckTopology.superset_covering _ ?_ hR
    rintro W g ⟨Z, k, g', hg', rfl⟩
    exact ⟨⟨⟨Z, g'⟩, hg'⟩, ⟨k⟩⟩
  -- a geometric point over `y`, lifted to a chart `V` of the family
  obtain ⟨t, rfl⟩ := exists_geometricPoint_liesOver B S hS y
  obtain ⟨i, t', ht'⟩ :=
    SmallEtale.exists_geometricPoint_lift_of_coversTop B S hS (schemeSpace V₀).2 hcov t
  obtain ⟨P, hPs, hP1, ⟨eP⟩⟩ := hP i.1.2 i.2
  let V := i.1.1
  -- the restriction of `Rf_*𝒪_X` to `V` is `Rf_{V*}𝒪`
  let sqV := IsPullback.of_hasPullback f (chartToSpace B S hS (schemeSpace V₀) V)
  have hisoV := H₀.2 (chartToSpace B S hS (schemeSpace V₀) V) _ _ sqV
  let eW : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS (schemeSpace V₀) V)).obj
      (derivedPushforwardStructure B S hS f) ≅
      (derivedModulePushforward B S hS
          (pullback.snd f (chartToSpace B S hS (schemeSpace V₀) V))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (structureModule (pullback f (chartToSpace B S hS (schemeSpace V₀) V)))) :=
    baseChangeIsoStructure B S hS _ _ _ _ sqV hisoV
  -- the geometric point as a morphism `c : Spec k ⟶ V`
  let g₀ : t'.val.siteObject ⟶ (SmallEtale.toOver B S hS (schemeSpace V₀).1).obj V := t'.val.value
  let c := representedSpaceMap B S hS g₀
  let pY : FieldValuedPoint B S hS (schemeSpace V₀).1 :=
    FieldValuedPoint.map B S hS _ V.1.hom t'.val
  have hpY : c ≫ chartToSpace B S hS (schemeSpace V₀) V = schemeSpaceMap pY.value := by
    have ha : yoneda.map (yonedaEquiv V.obj.hom) = V.obj.hom :=
      yonedaEquiv.injective (yonedaEquiv_yoneda_map _)
    refine InducedCategory.hom_ext ?_
    change yoneda.map g₀ ≫ V.obj.hom = yoneda.map (V.obj.hom.app _ g₀)
    rw [← ha]
    exact (yoneda.map_comp _ _).symm
  -- the fibre over the geometric point, and cohomology and base change along it
  let X' := AlgebraicSpaces.fiberProduct B S hS f (schemeSpaceMap pY.value)
  let sqF := AlgebraicSpaces.isPullback_fiberProduct B S hS f (schemeSpaceMap pY.value)
  have hisoF := H₀.2 (schemeSpaceMap pY.value) _ _ sqF
  let eF₀ : (smallEtaleDerivedModulePullback B S hS c).obj
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS (schemeSpace V₀) V)).obj
        (derivedPushforwardStructure B S hS f)) ≅
      (derivedModulePushforward B S hS
        (ObjectProperty.homMk (pullback.snd f.hom (schemeSpaceMap pY.value).hom) :
          X' ⟶ schemeSpace pY.siteObject)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X')) :=
    (smallEtaleDerivedModulePullbackCompIso B S hS c
        (chartToSpace B S hS (schemeSpace V₀) V)).app _ ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS hpY).app _ ≪≫
      baseChangeIsoStructure B S hS _ _ _ _ sqF hisoF
  -- the fibre `Lc^*(Rf_{V*}𝒪)` has no sections in degrees `≥ 2`
  have hK : ∀ m : ℕ, 2 ≤ m → Subsingleton (SheafOfModules.unit _ ⟶
      (DerivedCategory.homologyFunctor _ (m : ℤ)).obj
        ((smallEtaleDerivedModulePullback B S hS c).obj ((derivedModulePushforward B S hS
          (pullback.snd f (chartToSpace B S hS (schemeSpace V₀) V))).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (structureModule (pullback f (chartToSpace B S hS (schemeSpace V₀) V))))))) :=
    fun m hm => by
    have hD : Subsingleton (SheafOfModules.unit _ ⟶
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj t'.val.siteObject, isAlgebraicSpace_yoneda B S hS _⟩)) (m : ℤ)).obj
          ((derivedModulePushforward B S hS
            (ObjectProperty.homMk (pullback.snd f.hom (schemeSpaceMap pY.value).hom) :
              X' ⟶ schemeSpace pY.siteObject)).obj
            ((DerivedCategory.singleFunctor _ 0).obj (structureModule X')))) :=
      subsingleton_unit_hom_homology_derivedModulePushforward_fiberProduct B S hS f hvan pY m hm
    exact (Iso.homCongr (Iso.refl (SheafOfModules.unit _))
      ((DerivedCategory.homologyFunctor _ (m : ℤ)).mapIso
        ((smallEtaleDerivedModulePullback B S hS c).mapIso eW.symm ≪≫ eF₀))).subsingleton
  obtain ⟨W₀, n, ⟨w, hw⟩, ⟨eW₀⟩⟩ := exists_chart_iso_biprod_single_free_of_iso_biprod B S hS _ P
    hPs hP1 eP t' c hK
  refine ⟨((SmallEtale.chartLocalization B S hS (schemeSpace V₀).1 V).obj W₀).left, n, ⟨w, ?_⟩,
    nonempty_chartLocalization_iso_biprod_single_free B S hS _ V W₀ n
      ((smallEtaleDerivedModulePullback B S hS _).mapIso eW ≪≫ eW₀)⟩
  have hc' : c.hom = yonedaEquiv.symm t'.val.value ≫ 𝟙 _ := by
    rw [Category.comp_id]
    exact yonedaEquiv.injective (by rw [Equiv.apply_symm_apply]; exact yonedaEquiv_yoneda_map _)
  have h1 := pointsMap_yonedaEquiv_symm_comp_tautological t' (𝟙 _)
  rw [← hc'] at h1
  change pointsMap B S hS _ (W₀.1.hom ≫ V.1.hom) w = t.image
  refine (pointsMap_comp_apply B S hS W₀.1.hom V.1.hom w).trans ?_
  rw [hw]
  refine (congrArg (pointsMap B S hS _ V.1.hom) h1).trans ?_
  change _ = t.val.class B S hS _
  rw [← ht']
  rfl

/-- `H¹(Rf_*𝒪_X) ≅ R¹f_*𝒪_X`. -/
private def homologyOneDerivedPushforwardStructureIso {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (DerivedCategory.homologyFunctor _ 1).obj (derivedPushforwardStructure B S hS f) ≅
      ((modulePushforward B S hS f).rightDerived 1).obj (structureSheafModule B S hS X) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  (DerivedCategory.homologyFunctor _ 1).mapIso
      ((smallEtaleDerivedModulePushforwardIso B S hS f).app _) ≪≫
    homologyDerivedModulePushforwardSingleIso B S hS f (structureSheafModule B S hS X) 0 1 1
      (by norm_num)

/-- **`R¹f_*𝒪_X` is restricted to a free module on the charts of the local form.** On an étale
chart `W` on which `Rf_*𝒪_X` restricts to `𝒪_W ⊕ 𝒪_W^{⊕n}[-1]`, the restriction of `R¹f_*𝒪_X`
is `𝒪_W^{⊕n}`: the cohomology sheaves of the derived restriction along an étale morphism are the
restrictions of the cohomology sheaves, and `H¹(Rf_*𝒪_X) = R¹f_*𝒪_X`. -/
def modulePullbackRightDerivedOneIsoFree {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (W : SmallEtale B S hS Y.1) (n : ℕ)
    (e : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj
        (derivedPushforwardStructure B S hS f) ≅
      (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _) ⊞
        (DerivedCategory.singleFunctor _ 1).obj (SheafOfModules.free
          (R := ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y W))
          (ULift.{u} (Fin n)))) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (modulePullback B S hS (chartToSpace B S hS Y W)).obj
        (((modulePushforward B S hS f).rightDerived 1).obj (structureSheafModule B S hS X)) ≅
      SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y W))
        (ULift.{u} (Fin n)) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  (modulePullback B S hS (chartToSpace B S hS Y W)).mapIso
      (((DerivedCategory.homologyFunctor _ 1).mapIso
        ((smallEtaleDerivedModulePushforwardIso B S hS f).app _) ≪≫
      homologyDerivedModulePushforwardSingleIso B S hS f (structureSheafModule B S hS X) 0 1 1
        (by norm_num)).symm) ≪≫
    (smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale (chartToSpace B S hS Y W)
      (isEtale_chartToSpace B S hS Y W) _ 1).symm ≪≫
    (DerivedCategory.homologyFunctor _ 1).mapIso e ≪≫
    DerivedCategory.homologyBiprodSingleIso _ _ (by norm_num)

/-- **Stacks 0E1J, part (2), for a proper flat family over a scheme.** For a proper, flat
morphism of finite presentation `f : X ⟶ Y` from an algebraic space to a scheme with
`k = H⁰(X_k, 𝒪_{X_k})` and `Hᵠ(X_k, 𝒪_{X_k}) = 0` for `q ≥ 2` on the fibres over fields,
`R¹f_*𝒪_X` is a finite locally free `𝒪_Y`-module: it is finite free on the étale charts of the
local form `Rf_*𝒪_X ≅ 𝒪 ⊕ 𝒪^{⊕n}[-1]` (`exists_chart_iso_biprod_single_free`), whose images
cover `Y`. -/
theorem isFiniteLocallyFree_rightDerived_one_structureSheafModule (f : X ⟶ schemeSpace V₀)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (h : HasBijectiveFieldFibreGlobalFunctions B S hS f)
    (hvan : HasVanishingFieldFibreCohomologyAboveOne B S hS f) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (((modulePushforward B S hS f).rightDerived 1).obj (structureSheafModule B S hS X)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  choose W n hW e using fun y => exists_chart_iso_biprod_single_free B S hS f hf hfl hfp h hvan y
  have hsh : ∀ Z : SmallEtale B S hS (schemeSpace V₀).1,
      HasWeakSheafify ((SmallEtale.topology B S hS (schemeSpace V₀).1).over Z) AddCommGrpCat.{u} :=
    fun Z => inferInstance
  have hlb : ∀ Z : SmallEtale B S hS (schemeSpace V₀).1,
      ((SmallEtale.topology B S hS (schemeSpace V₀).1).over Z).WEqualsLocallyBijective
        AddCommGrpCat.{u} := fun Z => inferInstance
  exact AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_coversTop
    (SmallEtale.coversTop_of_forall_mem_range B S hS fun y => ⟨y, hW y⟩) _ fun y =>
      ⟨ULift.{u} (Fin (n y)), inferInstance, ⟨overFreeIsoOfModulePullback B S hS _ (W y) _ _
        (modulePullbackRightDerivedOneIsoFree B S hS f (W y) (n y) (e y).some)⟩⟩

/-- `𝒪 ⊕ M[-1]` has no cohomology in degrees `> 1`. -/
theorem isLE_one_biprod_single_zero_single_one {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    [HasDerivedCategory 𝒜] (A M : 𝒜) :
    ((DerivedCategory.singleFunctor 𝒜 0).obj A ⊞
      (DerivedCategory.singleFunctor 𝒜 1).obj M).IsLE 1 := by
  rw [DerivedCategory.isLE_iff]
  intro m hm
  have := preservesBinaryBiproducts_of_preservesBiproducts (DerivedCategory.homologyFunctor 𝒜 m)
  exact IsZero.of_iso ((biprod_isZero_iff _ _).2
    ⟨((DerivedCategory.singleFunctor 𝒜 0).obj A).isZero_of_isLE 0 m (by omega),
      ((DerivedCategory.singleFunctor 𝒜 1).obj M).isZero_of_isLE 1 m (by omega)⟩)
    ((DerivedCategory.homologyFunctor 𝒜 m).mapBiprod _ _)

/-- `Rf_*𝒪_X` has no cohomology in degrees `> 1`, under the hypotheses of
`exists_chart_iso_biprod_single_free`: this is étale local, and true for `𝒪 ⊕ 𝒪^{⊕n}[-1]`. -/
theorem isLE_one_derivedPushforwardStructure (f : X ⟶ schemeSpace V₀)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (h : HasBijectiveFieldFibreGlobalFunctions B S hS f)
    (hvan : HasVanishingFieldFibreCohomologyAboveOne B S hS f) :
    (derivedPushforwardStructure B S hS f).IsLE 1 := by
  choose W n hW e using fun y => exists_chart_iso_biprod_single_free B S hS f hf hfl hfp h hvan y
  refine isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_of_forall_mem_range B S hS fun y => ⟨y, hW y⟩) _ 1 fun y => ?_
  have := isLE_one_biprod_single_zero_single_one (SheafOfModules.unit
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS (schemeSpace V₀) (W y))))
    (SheafOfModules.free
      (R := ringedToposStructureRingSheaf B S hS (chartSpace B S hS (schemeSpace V₀) (W y)))
      (ULift.{u} (Fin (n y))))
  exact DerivedCategory.TStructure.t.isLE_of_iso (e y).some.symm 1

/-- **Stacks 0E1J, part (3), for a proper flat family over a scheme.** Under the hypotheses of
`isFiniteLocallyFree_rightDerived_one_structureSheafModule`, the formation of `R¹f_*𝒪_X` commutes
with arbitrary base change: for every cartesian square with `g : Y' ⟶ Y`, `g^*R¹f_*𝒪_X ≅
R¹f'_*𝒪_{X'}`. By cohomology and base change (Stacks 0CTM, part (1)),
`Lg^*Rf_*𝒪_X ≅ Rf'_*𝒪_{X'}`; as `Rf_*𝒪_X` has no cohomology above degree `1`, taking `H¹`
commutes with `Lg^*`. -/
theorem nonempty_modulePullback_rightDerived_one_iso (f : X ⟶ schemeSpace V₀)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (h : HasBijectiveFieldFibreGlobalFunctions B S hS f)
    (hvan : HasVanishingFieldFibreCohomologyAboveOne B S hS f)
    {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ schemeSpace V₀) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
    Nonempty ((modulePullback B S hS g).obj
        (((modulePushforward B S hS f).rightDerived 1).obj (structureSheafModule B S hS X)) ≅
      ((modulePushforward B S hS f').rightDerived 1).obj (structureSheafModule B S hS X')) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  have H₀ := isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp _
    (isPerfect_unit X)
  have hiso := H₀.2 g f' g' sq
  obtain ⟨eT⟩ := nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE g
    (derivedPushforwardStructure B S hS f) 1 (isLE_one_derivedPushforwardStructure B S hS f hf hfl
      hfp h hvan)
  exact ⟨(modulePullback B S hS g).mapIso
      (homologyOneDerivedPushforwardStructureIso B S hS f).symm ≪≫ eT.symm ≪≫
    (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')) 1).mapIso
      (baseChangeIsoStructure B S hS f g f' g' sq hiso) ≪≫
    homologyOneDerivedPushforwardStructureIso B S hS f'⟩

end AlgebraicGeometry.Space

end
