module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedDualPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedDualAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffineDerivedAssociatedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.Homology.Perfect.MinimalRepresentativeFieldPoint
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareCube

/-!
# Stacks 0BCD at the field points of an algebraic space

Let `Y` be an algebraic space and `E ∈ D(𝒪_Y)` perfect. If the derived fibre `Ly^*E` lies in
`D^{≥ m}` at every field-valued point `y : Spec k ⟶ Y`, then the dual `E^∨ = R𝓗om(E, 𝒪_Y)` lies
in `D^{≤ -m}`. This is More on Algebra, Lemma 0BCD read on an étale neighbourhood of each point
of `Y`, as in the proof of Stacks 0DKY.

For a chart `U` of `Y` with affine scheme, `Φ` denotes the derived associated-module functor
`D(Γ(U)) ⥤ D(𝒪_U)`.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main results

* `exists_isPerfect_iso_representedAffineDerivedAssociated`: a perfect object on an affine
  represented algebraic space is `Φ` of a perfect complex of modules (Stacks 08H1 with
  Stacks 08JL).
* `isGE_of_isZero_homology_representedAffineDerivedAssociated_obj`: `Φ` reflects `D^{≥ m}`.
* `exists_mem_basicOpen_isStrictlyGE_model_of_forall_fieldValuedPoint_isGE`: Stacks 0BCD at the
  residue field points of an affine chart.
* `exists_isStrictlyGE_model_openChart_basicOpen`: on a basic open of an affine chart, `E` has a
  strictly perfect model in degrees `≥ m`.
* `isLE_smallEtaleDerivedDual_of_forall_fieldValuedPoint_isGE`: the statement above.

## References

* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 08H1](https://stacks.math.columbia.edu/tag/08H1)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Perfect objects on an affine represented space -/

/-- **A perfect object on an affine represented algebraic space is `Φ` of a perfect complex.**
For `U` with affine underlying scheme and `E ∈ D(𝒪_{h_U})` perfect, `E ≅ Φ(RΓ(E))` with `RΓ(E)`
perfect in `D(Γ(U))`. -/
theorem exists_isPerfect_iso_representedAffineDerivedAssociated (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hE : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPerfect E) :
    ∃ M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)),
      StacksDraft.Perfect.IsPerfect M ∧
        Nonempty (E ≅ (representedAffineDerivedAssociated B S hS U).obj M) := by
  have hQ := qcohDerived_of_isPerfect B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E hE
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hQ
  exact ⟨_, isPerfect_representedAffineDerivedSections_obj B S hS U E hE,
    ⟨(asIso ((representedAffineDerivedAdjunction B S hS U).counit.app E)).symm⟩⟩

/-- **`Φ` reflects `D^{≥ m}`.** If the cohomology of `Φ(X)` vanishes in degrees `< m`, then
`X ∈ D^{≥ m}`. -/
theorem isGE_of_isZero_homology_representedAffineDerivedAssociated_obj (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (X : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) (m : ℤ)
    (h : ∀ i < m, IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((representedAffineDerivedAssociated B S hS U).obj X))) :
    X.IsGE m := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  let Φ₀ := representedAffineAssociated B S hS U
  have := (representedAffineAssociatedFullyFaithful B S hS U).faithful
  have h₁ : IsZero (Φ₀.obj ((DerivedCategory.homologyFunctor _ i).obj X)) :=
    (h i hi).of_iso ((Φ₀.mapDerivedCategoryHomologyIso i).app X).symm
  rw [IsZero.iff_id_eq_zero]
  exact Φ₀.map_injective (h₁.eq_of_src _ _)

/-! ### The field point and the basic open at a point of an affine chart -/

/-- **0BCD at the residue field point of a point of an affine chart.** Let `W` be a chart of `Y`
with affine scheme, `E|_W ≅ Φ(M)` with `M` perfect, and assume `Ly^*E ∈ D^{≥ m}` at every
field-valued point `y` of `Y`. Then every point `w` of `W` lies in a basic open `D(f)` such that
for every localization `S'` of `Γ(W)` away from `f`, `M ⊗ᴸ S'` is represented by a bounded
complex of finite projective modules in degrees `≥ m`. -/
theorem exists_mem_basicOpen_isStrictlyGE_model_of_forall_fieldValuedPoint_isGE
    {Y : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (W : SmallEtale B S hS Y.1) [IsAffine (chartScheme W)]
    (M : DerivedCategory (ModuleCat.{u} Γ(chartScheme W, ⊤)))
    (hM : StacksDraft.Perfect.IsPerfect M)
    (eW : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj E ≅
      (representedAffineDerivedAssociated B S hS ((SmallEtale.toOver B S hS Y.1).obj W)).obj M)
    (m : ℤ)
    (h : ∀ p : FieldValuedPoint B S hS Y.1,
      ((smallEtaleDerivedModulePullback B S hS p.toSpace).obj E).IsGE m)
    (w : chartScheme W) :
    ∃ f : Γ(chartScheme W, ⊤), w ∈ (chartScheme W).basicOpen f ∧
      ∀ (S' : Type u) [CommRing S'] [Algebra Γ(chartScheme W, ⊤) S']
        [IsLocalization.Away f S'],
        ∃ (P : CochainComplex (ModuleCat.{u} S') ℤ) (b : ℤ),
          P.IsStrictlyGE m ∧ P.IsStrictlyLE b ∧
            (∀ i, Module.Finite S' (P.X i)) ∧ (∀ i, Module.Projective S' (P.X i)) ∧
            Nonempty (DerivedCategory.Q.obj P ≅
              (totalDerivedExtensionScalars.{u, u, u}
                (algebraMap Γ(chartScheme W, ⊤) S')).functor.obj M) := by
  let T := (SmallEtale.toOver B S hS Y.1).obj W
  let r := schemePointRepresentative B S hS T w
  let q := FieldValuedPoint.map B S hS (yoneda.obj T) (chartToSpace B S hS Y W).hom r
  have hq : q.toSpace = representedSpaceMap B S hS r.siteHom ≫ chartToSpace B S hS Y W :=
    ObjectProperty.hom_ext _ (fieldMorphism_map_yoneda B S hS Y.1 _ r)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj r.siteObject) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of r.carrier)))
  let φ := (Scheme.Hom.appTop (B.inclusion.map r.siteHom.left)).hom
  have hL : IsField Γ((BigFppfOver.toScheme B S hS).obj r.siteObject, ⊤) :=
    MulEquiv.isField (Field.toIsField r.carrier)
      (Scheme.ΓSpecIso (CommRingCat.of r.carrier)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨eD⟩ := nonempty_smallEtaleDerivedModulePullback_representedAffineDerivedAssociated_iso
    r.siteHom (totalDerivedExtensionScalars.{u, u, u} φ) M hM
  have h' := h q
  rw [hq] at h'
  have hGE : ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj M).IsGE m := by
    refine isGE_of_isZero_homology_representedAffineDerivedAssociated_obj r.siteObject _ m
      fun i hi => ?_
    exact ((DerivedCategory.isGE_iff _ m).1 h' i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso
        ((((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS r.siteHom)
          (chartToSpace B S hS Y W)).app E).symm ≪≫
          (smallEtaleDerivedModulePullback B S hS
            (representedSpaceMap B S hS r.siteHom)).mapIso eW ≪≫ eD).symm))
  obtain ⟨f, hf, hall⟩ :=
    StacksDraft.Perfect.exists_isStrictlyGE_model_away_of_isGE_totalDerived_field hL φ M hM m hGE
  refine ⟨f, ?_, hall⟩
  let := hL.toField
  have hu : IsUnit (φ f) := (isUnit_iff_ne_zero).2 fun h0 => hf (RingHom.mem_ker.2 h0)
  have hpre := Scheme.preimage_basicOpen_top (B.inclusion.map r.siteHom.left) f
  rw [Scheme.basicOpen_of_isUnit _ hu] at hpre
  have hι : B.inclusion.map r.siteHom.left = (chartScheme W).fromSpecResidueField w :=
    toScheme_map_siteHom_schemePointRepresentative B S hS T w
  let pt : (BigFppfOver.toScheme B S hS).obj r.siteObject :=
    show PrimeSpectrum r.carrier from IsLocalRing.closedPoint r.carrier
  have hpt : pt ∈ (B.inclusion.map r.siteHom.left) ⁻¹ᵁ (chartScheme W).basicOpen f := by
    have htop : pt ∈ (⊤ : (Scheme.Opens _)) := trivial
    rw [← hpre] at htop
    exact htop
  have hw : (B.inclusion.map r.siteHom.left) pt = w := by
    rw [hι]
    exact Scheme.fromSpecResidueField_apply w _
  rw [← hw]
  exact hpt

/-- **On the basic open, `E` has a strictly perfect model in degrees `≥ m`.** Let `W` be a chart
of `Y` with affine scheme and `E|_W ≅ Φ(M)` with `M` perfect, and let `f ∈ Γ(W)` be such that for
every localization `S'` of `Γ(W)` away from `f`, `M ⊗ᴸ S'` is represented by a bounded complex of
finite projective modules in degrees `≥ m`. Then the derived pullback of `E` to the basic-open
chart `D(f)` of `W` is isomorphic to a bounded complex of retracts of finite free modules
concentrated in degrees `≥ m`. -/
theorem exists_isStrictlyGE_model_openChart_basicOpen {Y : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (W : SmallEtale B S hS Y.1) [IsAffine (chartScheme W)]
    (M : DerivedCategory (ModuleCat.{u} Γ(chartScheme W, ⊤)))
    (hM : StacksDraft.Perfect.IsPerfect M)
    (eW : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj E ≅
      (representedAffineDerivedAssociated B S hS ((SmallEtale.toOver B S hS Y.1).obj W)).obj M)
    (m : ℤ) (f : Γ(chartScheme W, ⊤))
    (hall : ∀ (S' : Type u) [CommRing S'] [Algebra Γ(chartScheme W, ⊤) S']
        [IsLocalization.Away f S'],
        ∃ (P : CochainComplex (ModuleCat.{u} S') ℤ) (b : ℤ),
          P.IsStrictlyGE m ∧ P.IsStrictlyLE b ∧
            (∀ i, Module.Finite S' (P.X i)) ∧ (∀ i, Module.Projective S' (P.X i)) ∧
            Nonempty (DerivedCategory.Q.obj P ≅
              (totalDerivedExtensionScalars.{u, u, u}
                (algebraMap Γ(chartScheme W, ⊤) S')).functor.obj M)) :
    ∃ P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (chartSpace B S hS Y (openChart B S hS Y.1 W ((chartScheme W).basicOpen f))))) ℤ,
      (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
        (chartSpace B S hS Y (openChart B S hS Y.1 W ((chartScheme W).basicOpen f))))) (P.X j)) ∧
      {i : ℤ | ¬ IsZero (P.X i)}.Finite ∧ P.IsStrictlyGE m ∧
      Nonempty ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y
        (openChart B S hS Y.1 W ((chartScheme W).basicOpen f)))).obj E ≅
          DerivedCategory.Q.obj P) := by
  let O := (chartScheme W).basicOpen f
  let T := (SmallEtale.toOver B S hS Y.1).obj W
  let g := openSubHom T O
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (openSub T O)) :=
    isAffine_chartScheme_openChart_basicOpen B S hS Y.1 W inferInstance f
  let ψ := (Scheme.Hom.appTop (B.inclusion.map g.left)).hom
  obtain ⟨eD⟩ := nonempty_smallEtaleDerivedModulePullback_representedAffineDerivedAssociated_iso
    g (totalDerivedExtensionScalars.{u, u, u} ψ) M hM
  have hψ : ψ = algebraMap Γ(chartScheme W, ⊤) Γ(O, ⊤) :=
    congrArg (fun k : O.toScheme ⟶ chartScheme W => k.appTop.hom)
      (toScheme_map_openSubHom B S hS T O)
  obtain ⟨P', b, hge, hle, hfin, hproj, ⟨eP⟩⟩ := hall Γ(O, ⊤)
  let Φ₀ := representedAffineAssociated B S hS (openSub T O)
  have hchart : chartToSpace B S hS Y (openChart B S hS Y.1 W O) =
      representedSpaceMap B S hS g ≫ chartToSpace B S hS Y W := rfl
  let e : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y
      (openChart B S hS Y.1 W O))).obj E ≅
      DerivedCategory.Q.obj ((Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P') :=
    ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g)
        (chartToSpace B S hS Y W)).app E).symm ≪≫
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).mapIso eW ≪≫ eD ≪≫
      (representedAffineDerivedAssociated B S hS (openSub T O)).mapIso
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr hψ).app M ≪≫ eP.symm) ≪≫
      Φ₀.mapDerivedCategoryFactors.app P'
  refine ⟨(Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P', fun j => ?_, ?_, ?_, ⟨e⟩⟩
  · have hsum := @isDirectSummandOfFiniteFree_representedAffineAssociated_obj B S hS
      (openSub T O) _ (P'.X j) (hfin j) (hproj j)
    obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free _ _).1 hsum
    let R₁ := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (yoneda.obj (openSub T O)) (isAlgebraicSpace_yoneda B S hS (openSub T O))).O
    let O₁ := SheafOfModules.unit R₁
    let eb : SheafOfModules.free (R := R₁) (ULift.{u} (Fin n)) ≅ ⨁ fun _ : Fin n => O₁ :=
      (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) => O₁)).symm ≪≫
        (biproduct.isoCoproduct _).symm
    have hret : IsRetractOfFiniteFree O₁ (P'.X j |> Φ₀.obj) :=
      ⟨n, i ≫ eb.hom, eb.inv ≫ r, by rw [Category.assoc, Iso.hom_inv_id_assoc, hir]⟩
    exact hret
  · refine (Set.finite_Icc m b).subset fun i hi => ⟨?_, ?_⟩
    · exact not_lt.1 fun hlt => hi (Φ₀.map_isZero (P'.isZero_of_isStrictlyGE m i hlt))
    · exact not_lt.1 fun hlt =>
        hi (Φ₀.map_isZero (P'.isZero_of_isStrictlyLE b i hlt))
  · exact (CochainComplex.isStrictlyGE_iff _ m).2 fun i hi =>
      Φ₀.map_isZero (P'.isZero_of_isStrictlyGE m i hi)

/-! ### The amplitude of the dual -/

/-- **Stacks 0BCD at the field points of an algebraic space, for the dual.** Let `Y` be an
algebraic space and `E ∈ D(𝒪_Y)` perfect such that `Ly^*E ∈ D^{≥ m}` for every field-valued
point `y : Spec k ⟶ Y`. Then the dual `E^∨ = R𝓗om(E, 𝒪_Y)` lies in `D^{≤ -m}`. -/
theorem isLE_smallEtaleDerivedDual_of_forall_fieldValuedPoint_isGE (Y : AlgebraicSpaces B S hS)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) E) (m : ℤ)
    (h : ∀ p : FieldValuedPoint B S hS Y.1,
      ((smallEtaleDerivedModulePullback B S hS p.toSpace).obj E).IsGE m) :
    (smallEtaleDerivedDual B S hS Y E).IsLE (-m) := by
  refine isLE_of_forall_covering_isLE_smallEtaleDerivedModulePullback_chartToSpace _ (-m)
    fun U => ?_
  let R : Presieve U := fun V _ =>
    ∃ P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (chartSpace B S hS Y V))) ℤ,
      (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
        (chartSpace B S hS Y V))) (P.X j)) ∧
      {i : ℤ | ¬ IsZero (P.X i)}.Finite ∧ P.IsStrictlyGE m ∧
      Nonempty ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y V)).obj E ≅
          DerivedCategory.Q.obj P)
  refine ⟨R, ?_, fun V _ ⟨P, hP, hbdd, hge, ⟨e⟩⟩ => ?_⟩
  · rw [SmallEtale.mem_topology_iff_exists_mem_range]
    intro z
    obtain ⟨O, hO, hzO, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (chartScheme U).isBasis_affineOpens) (TopologicalSpace.Opens.mem_top z)
    let W := openChart B S hS Y.1 U O
    have : IsAffine (chartScheme W) := hO
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W)) :=
      hO
    obtain ⟨M, hM, ⟨eW⟩⟩ := exists_isPerfect_iso_representedAffineDerivedAssociated
      ((SmallEtale.toOver B S hS Y.1).obj W)
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj E)
      (isPerfect_smallEtaleDerivedModulePullback (chartToSpace B S hS Y W) E hE)
    let w : chartScheme W := ⟨z, hzO⟩
    obtain ⟨f, hw, hall⟩ :=
      exists_mem_basicOpen_isStrictlyGE_model_of_forall_fieldValuedPoint_isGE E W M hM eW m h w
    obtain ⟨P, hP, hbdd, hge, he⟩ :=
      exists_isStrictlyGE_model_openChart_basicOpen E W M hM eW m f hall
    let g := openChartInclusion B S hS Y.1 W ((chartScheme W).basicOpen f) ≫
      openChartInclusion B S hS Y.1 U O
    refine ⟨openChart B S hS Y.1 W ((chartScheme W).basicOpen f), g,
      ⟨_, 𝟙 _, g, ⟨P, hP, hbdd, hge, he⟩, Category.id_comp g⟩, ⟨⟨w, hw⟩, ?_⟩⟩
    rw [Functor.map_comp, Functor.map_comp, toScheme_map_toOver_map_openChartInclusion,
      toScheme_map_toOver_map_openChartInclusion]
    rfl
  · have := hge
    have := isLE_smallEtaleDerivedDual_of_iso_Q_of_isStrictlyGE P hP hbdd m e
    exact DerivedCategory.TStructure.t.isLE_of_iso
      (smallEtaleDerivedModulePullbackDualIso (chartToSpace B S hS Y V) E hE).symm (-m)

end AlgebraicGeometry.Space

end
