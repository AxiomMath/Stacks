module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineTorAmplitude

/-!
# Locally bounded below objects of `D(𝒪_X)` for an algebraic space

An object `E` of `D(𝒪_X)` on an algebraic space `X` is *locally bounded below* when every point
of `|X|` lies in the image of an étale chart `V` of `X` over which the cohomology sheaves `H^i(E)`
vanish for all `i` below some bound. This is the condition of Stacks 0GFK (2), the étale-local
form of the condition of the same name on a ringed space. On a quasi-compact algebraic space
finitely many such charts suffice, so a locally bounded below object is bounded below.

## Main definitions

* `AlgebraicGeometry.Space.IsLocallyBoundedBelow`

## Main results

* `AlgebraicGeometry.Space.exists_isZero_homology_of_isLocallyBoundedBelow`: on a quasi-compact
  algebraic space a locally bounded below object is bounded below.
* `AlgebraicGeometry.Space.isLocallyBoundedBelow_of_isZero_homology`: a bounded below object is
  locally bounded below.
* `AlgebraicGeometry.Space.isZero_homology_iff_representedAffineDerivedSections`: on an affine
  represented algebraic space the cohomology sheaves of `E ∈ D_QCoh` vanish in a degree exactly
  when the cohomology of `RΓ(E)` does.

## References

* [Stacks Project, Tag 0GFK](https://stacks.math.columbia.edu/tag/0GFK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Locally bounded below.** An object `E` of `D(𝒪_X)` is locally bounded below when every point
of `|X|` lies in the image of an étale chart `V` of `X` and an integer `N` such that the
restrictions to `V` of the cohomology sheaves `H^i(E)` vanish for all `i < N`. -/
def IsLocallyBoundedBelow (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) : Prop :=
  ∀ x : points B S hS X.1, ∃ V : SmallEtale B S hS X.1,
    x ∈ Set.range (pointsMap B S hS _ (chartToSpace B S hS X V).hom) ∧ ∃ N : ℤ, ∀ i : ℤ, i < N →
      IsZero (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E).over
        (V : (smallEtaleRingedSite B S hS X.1 X.2).C))

/-- A bounded below object is locally bounded below. -/
theorem isLocallyBoundedBelow_of_isZero_homology (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (N : ℤ)
    (h : ∀ i : ℤ, i < N →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E)) :
    IsLocallyBoundedBelow X E := by
  intro x
  obtain ⟨U₀, a, ha_surj, ha_et⟩ := X.2.exists_atlas
  obtain ⟨u, hu⟩ := (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U₀ a).1 ha_surj x
  exact ⟨⟨CostructuredArrow.mk a, ha_et⟩, ⟨u, hu⟩, N, fun i hi =>
    @Functor.map_isZero _ _ _ _ _ _ (SheafOfModules.overFunctor _ _)
      ⟨fun _ _ ↦ by rfl⟩ _ (h i hi)⟩

/-- **On a quasi-compact algebraic space a locally bounded below object is bounded below**:
finitely many charts carrying a bound cover `|X|`, and a module whose restrictions to the charts
of a covering vanish is zero. -/
theorem exists_isZero_homology_of_isLocallyBoundedBelow (X : AlgebraicSpaces B S hS)
    (hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : IsLocallyBoundedBelow X E) :
    ∃ N : ℤ, ∀ j : ℤ, j < N →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) j).obj E) := by
  classical
  let := pointTopology B S hS X.1
  have := compactSpace_points_of_isQuasiCompactSpace B S hS X.2 hX
  choose V hV N hN using hE
  let O : points B S hS X.1 → Set (points B S hS X.1) := fun x =>
    Set.range (pointsMap B S hS _ (chartToSpace B S hS X (V x)).hom)
  have hO : ∀ x, IsOpen (O x) := fun x =>
    let := pointTopology B S hS (yoneda.obj (V x).1.left)
    (isOpenMap_pointsMap_of_isEtale B S hS _ (isAlgebraicSpace_yoneda B S hS _) X.2
      ((isEtale_iff_presheaf_of_yoneda B S hS _).2 (V x).2)).isOpen_range
  have hcov : Set.univ ⊆ ⋃ x, O x := fun x _ => Set.mem_iUnion.2 ⟨x, hV x⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover O hO hcov
  refine ⟨-∑ x ∈ F, |N x|, fun j hj => ?_⟩
  refine isZero_of_supportOfSheaf_eq_empty B S hS X _ ?_
  refine Set.eq_empty_of_forall_notMem fun y hy => ?_
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  have hjx : j < N x := by
    have h1 : |N x| ≤ ∑ x ∈ F, |N x| :=
      Finset.single_le_sum (f := fun x => |N x|) (fun _ _ => abs_nonneg _) hx
    have h2 := neg_abs_le (N x)
    omega
  have := supportOfSheaf_inter_range_eq_empty_of_isZero_over B S hS X _ (V x) (hN x j hjx)
  exact (Set.eq_empty_iff_forall_notMem.mp this) y ⟨hy, hyx⟩

/-- A sheaf of modules whose support misses the image of an étale chart `V` restricts to zero on
the slice at `V`. -/
theorem isZero_over_of_supportOfSheaf_inter_range_eq_empty (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (h : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ∩
      Set.range (pointsMap B S hS _ (chartToSpace B S hS X V).hom) = ∅) :
    IsZero (M.over (V : (smallEtaleRingedSite B S hS X.1 X.2).C)) := by
  have h0 : IsZero ((etaleModulePullback B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).obj M) := by
    refine isZero_of_supportOfSheaf_eq_empty B S hS (chartSpace B S hS X V) _ ?_
    rw [supportOfSheaf_chartToSpace, Set.preimage_eq_empty_iff, Set.disjoint_iff_inter_eq_empty]
    exact h
  have hs := (isZero_etaleModulePullback_chartToSpace_iff B S hS X V M).1 h0
  exact Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections
    (C := Over (V : (smallEtaleRingedSite B S hS X.1 X.2).C)) _ fun W => hs W.unop.left W.unop.hom

/-- **The support of a cohomology sheaf of an étale derived pullback is an inverse image**: for
`a : X ⟶ Y` étale, `Supp Hⁱ(La^*E) = |a|⁻¹ Supp Hⁱ(E)`. -/
theorem supportOfSheaf_homology_smallEtaleDerivedModulePullback {X Y : AlgebraicSpaces B S hS}
    (a : X ⟶ Y) (ha : IsEtale B S hS a.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (i : ℤ) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
          ((smallEtaleDerivedModulePullback B S hS a).obj E))) =
      pointsMap B S hS X.1 a.hom ⁻¹' supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj E)) := by
  rw [← supportOfSheaf_homology_etaleRestrict B S hS a ha E i]
  have key : ∀ {F G : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}} (e : F ≅ G),
      supportOfSheaf B S hS X.1 F = supportOfSheaf B S hS X.1 G := fun e =>
    have : Mono e.hom := @IsIso.mono_of_iso _ _ _ _ e.hom (Iso.isIso_hom e)
    have : Mono e.inv := @IsIso.mono_of_iso _ _ _ _ e.inv (Iso.isIso_inv e)
    Set.eq_of_subset_of_subset (supportOfSheaf_subset_of_mono B S hS X.1 X.2 e.hom)
      (supportOfSheaf_subset_of_mono B S hS X.1 X.2 e.inv)
  exact key ((SheafOfModules.toSheaf _).mapIso
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).mapIso
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app E)))

/-- On an étale chart `V`, the restriction of `Hⁱ(E)` to the slice at `V` vanishes exactly when
`Hⁱ` of the derived pullback of `E` to the algebraic space represented by `V` does. -/
theorem isZero_over_homology_iff (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (V : SmallEtale B S hS X.1) (i : ℤ) :
    IsZero (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E).over
        (V : (smallEtaleRingedSite B S hS X.1 X.2).C)) ↔
      IsZero ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2) i).obj
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E)) := by
  refine Iff.trans ?_ (supportOfSheaf_eq_empty_iff_isZero B S hS (chartSpace B S hS X V) _)
  rw [supportOfSheaf_homology_smallEtaleDerivedModulePullback _ (isEtale_chartToSpace B S hS X V)]
  rw [Set.preimage_eq_empty_iff, Set.disjoint_iff_inter_eq_empty]
  exact ⟨supportOfSheaf_inter_range_eq_empty_of_isZero_over B S hS X _ V,
    isZero_over_of_supportOfSheaf_inter_range_eq_empty X _ V⟩

/-- **Charts through a point of an étale space, over a given chart.** Let `f : Y ⟶ X` be étale,
`U` a chart of `X` and `u` a point of `U` whose image in `|X|` is the image of a point `y` of `Y`.
Then some chart `V` of `Y` through `y` maps to `U` over `X`. -/
theorem exists_chart_lift_mem_range_of_isEtale {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (U : SmallEtale B S hS X.1)
    (u : points B S hS (yoneda.obj U.1.left)) (y : points B S hS Y.1)
    (hy : pointsMap B S hS _ U.1.hom u = pointsMap B S hS Y.1 f.hom y) :
    ∃ (V : SmallEtale B S hS Y.1) (p : V.1.left ⟶ U.1.left),
      yoneda.map p ≫ U.1.hom = V.1.hom ≫ f.hom ∧
        y ∈ Set.range (pointsMap B S hS _ V.1.hom) := by
  have sq := IsPullback.of_hasPullback U.1.hom f.hom
  obtain ⟨q, -, hq2⟩ := exists_point_of_isPullback_presheaf B S hS sq u y hy
  have hQ : IsAlgebraicSpace B S hS (pullback U.1.hom f.hom) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS _) Y.2 X.2
  have hU : IsEtale B S hS U.1.hom := (isEtale_iff_presheaf_of_yoneda B S hS _).2 U.2
  have hfst : IsEtale B S hS (pullback.fst U.1.hom f.hom) := by
    have h := isEtale_pullback_snd B S hS (isAlgebraicSpace_yoneda B S hS _) X.2 Y.2
      f.hom U.1.hom hf
    have e : pullback.fst U.1.hom f.hom =
        (pullbackSymmetry U.1.hom f.hom).hom ≫ pullback.snd f.hom U.1.hom := by simp
    rw [e]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _) h
  have hsnd : IsEtale B S hS (pullback.snd U.1.hom f.hom) :=
    isEtale_pullback_snd B S hS Y.2 X.2 (isAlgebraicSpace_yoneda B S hS _) U.1.hom f.hom hU
  obtain ⟨A, a, w, ha, hw, -, -⟩ :=
    exists_etale_scheme_chart_through_point B S hS hQ (pullback.fst U.1.hom f.hom) hfst q
  have hV : IsEtaleChart B S hS Y.1 (CostructuredArrow.mk (a ≫ pullback.snd U.1.hom f.hom)) :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).1 (isEtale_comp B S hS ha hsnd)
  refine ⟨⟨CostructuredArrow.mk (a ≫ pullback.snd U.1.hom f.hom), hV⟩,
    yoneda.preimage (a ≫ pullback.fst U.1.hom f.hom), ?_, w, ?_⟩
  · simp only [Functor.map_preimage, Category.assoc, pullback.condition]
    rfl
  · show pointsMap B S hS _ (a ≫ pullback.snd U.1.hom f.hom) w = y
    rw [pointsMap_comp, Function.comp_apply, hw, hq2]

/-- **Étale pullback preserves local boundedness below**: if `E` is locally bounded below on `X`
and `a : X' ⟶ X` is étale, then `La^*E` is locally bounded below on `X'`. -/
theorem isLocallyBoundedBelow_smallEtaleDerivedModulePullback {X X' : AlgebraicSpaces B S hS}
    (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : IsLocallyBoundedBelow X E) :
    IsLocallyBoundedBelow X' ((smallEtaleDerivedModulePullback B S hS a).obj E) := by
  intro x'
  obtain ⟨V, ⟨v, hv⟩, N, hN⟩ := hE (pointsMap B S hS _ a.hom x')
  obtain ⟨V', p, hp, hx'⟩ := exists_chart_lift_mem_range_of_isEtale a ha V v x' hv
  refine ⟨V', hx', N, fun i hi => isZero_over_of_supportOfSheaf_inter_range_eq_empty X' _ V' ?_⟩
  have h0 := supportOfSheaf_inter_range_eq_empty_of_isZero_over B S hS X _ V (hN i hi)
  rw [supportOfSheaf_homology_smallEtaleDerivedModulePullback a ha]
  refine Set.eq_empty_of_forall_notMem fun y ⟨hy, w, hw⟩ => ?_
  subst hw
  refine (Set.eq_empty_iff_forall_notMem.mp h0) _ ⟨hy, pointsMap B S hS _ (yoneda.map p) w, ?_⟩
  show (pointsMap B S hS _ V.1.hom ∘ pointsMap B S hS _ (yoneda.map p)) w =
    (pointsMap B S hS _ a.hom ∘ pointsMap B S hS _ V'.1.hom) w
  rw [← pointsMap_comp, ← pointsMap_comp, hp]

/-- The algebraic space represented by an étale chart with affine scheme is quasi-compact. -/
theorem isQuasiCompactSpace_chartSpace (X : AlgebraicSpaces B S hS) (W : SmallEtale B S hS X.1)
    (hW : IsAffine (chartScheme W)) : IsQuasiCompactSpace B S hS (chartSpace B S hS X W).1 :=
  isQuasiCompactSpace_yoneda_of_isAffine B S hS W.1.left hW

/-- **A locally bounded below object is bounded below on an affine chart.** -/
theorem exists_isZero_homology_chartToSpace_of_isLocallyBoundedBelow (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : IsLocallyBoundedBelow X E)
    (W : SmallEtale B S hS X.1) (hW : IsAffine (chartScheme W)) :
    ∃ N : ℤ, ∀ j : ℤ, j < N → IsZero ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (chartSpace B S hS X W).1 (chartSpace B S hS X W).2) j).obj
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X W)).obj E)) :=
  exists_isZero_homology_of_isLocallyBoundedBelow _ (isQuasiCompactSpace_chartSpace X W hW) _
    (isLocallyBoundedBelow_smallEtaleDerivedModulePullback _ (isEtale_chartToSpace B S hS X W) E hE)

section Affine

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- On an affine represented algebraic space, the `i`-th cohomology sheaf of `E ∈ D_QCoh` vanishes
exactly when the `i`-th cohomology module of `RΓ(E)` does: `E` is the associated object of
`RΓ(E)`, and the associated-module functor is exact and reflects zero objects. -/
theorem isZero_homology_iff_representedAffineDerivedSections
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hE : QcohDerived B S hS (schemeSpace U) E) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj E) ↔
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((representedAffineDerivedSections B S hS U).obj E)) := by
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hE
  let c : (representedAffineDerivedAssociated B S hS U).obj
      ((representedAffineDerivedSections B S hS U).obj E) ≅ E :=
    asIso ((representedAffineDerivedAdjunction B S hS U).counit.app E)
  refine (Iso.isZero_iff ((DerivedCategory.homologyFunctor _ i).mapIso c.symm ≪≫
    ((representedAffineAssociated B S hS U).mapDerivedCategoryHomologyIso i).app _)).trans ?_
  exact isZero_representedAffineAssociated_obj_iff B S hS U _

/-- **On an affine represented algebraic space, local boundedness below is boundedness below of
the derived sections.** -/
theorem isLocallyBoundedBelow_iff_exists_isGE_representedAffineDerivedSections
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hE : QcohDerived B S hS (schemeSpace U) E) :
    IsLocallyBoundedBelow (schemeSpace U) E ↔
      ∃ a : ℤ, ((representedAffineDerivedSections B S hS U).obj E).IsGE a := by
  refine ⟨fun h => ?_, fun ⟨a, ha⟩ => isLocallyBoundedBelow_of_isZero_homology (schemeSpace U) E a
    fun i hi => (isZero_homology_iff_representedAffineDerivedSections U E hE i).2
      ((DerivedCategory.isGE_iff _ a).1 ha i hi)⟩
  obtain ⟨N, hN⟩ := exists_isZero_homology_of_isLocallyBoundedBelow (schemeSpace U)
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS U inferInstance) E h
  exact ⟨N, (DerivedCategory.isGE_iff _ N).2 fun i hi =>
    (isZero_homology_iff_representedAffineDerivedSections U E hE i).1 (hN i hi)⟩

end Affine

end AlgebraicGeometry.Space

end
