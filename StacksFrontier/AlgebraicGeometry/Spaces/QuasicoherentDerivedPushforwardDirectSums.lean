module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsUnitCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree

/-!
# The derived direct image commutes with direct sums on `D_QCoh`

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a scheme
`S` contained in a big fppf site `B`.  Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with
direct sums (Stacks 08FB).

## Main results

* `AlgebraicGeometry.Space.preservesCoproducts_quasicoherentDerivedPushforward`: Stacks 08FB.
* `AlgebraicGeometry.Space.preservesColimit_derivedModulePushforward`: the same statement in
  `D(𝒪_Y)`, for direct sums of objects of `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.preservesColimit_derivedModulePushforward_of_isAffineSpace`: the case
  of an affine target, from compactness of `𝒪_X[0]` and generation of `D_QCoh(𝒪_Y)` by `𝒪_Y[0]`.
* `AlgebraicGeometry.Space.isZero_of_forall_isAffineChart`: a module on an algebraic space is zero
  as soon as its restrictions to the affine étale charts are.

## References

* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### Locality on the affine étale charts -/

/-- A module on an algebraic space is zero as soon as its restriction to every affine étale chart
is zero: its sections over the affine charts vanish, and the affine charts cover. -/
theorem isZero_of_forall_isAffineChart (Y : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (h : ∀ A : SmallEtale B S hS Y.1, IsAffineChart B S hS Y.1 A →
      IsZero ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y A)
        (isEtale_chartToSpace B S hS Y A)).obj M)) :
    IsZero M := by
  let K := (HomologicalComplex.single (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ) 0).obj M
  have hK : K.ExactAt 0 := by
    refine exactAt_of_forall_isAffineChart B S hS Y.1 Y.2 K 0 fun A hA => ?_
    let F := Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS Y.1 Y.2) A
    have hz : IsZero (F.obj M) := by
      have := (SheafOfModules.isZero_iff_forall_isZero_obj _ _).mp (h A hA)
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj A))
      exact Functor.map_isZero (forget₂ _ AddCommGrpCat) this
    refine HomologicalComplex.ExactAt.of_iso ?_
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M).symm
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hz.of_iso (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj M))
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hK
  exact hK.of_iso (HomologicalComplex.singleObjHomologySelfIso _ 0 M).symm


/-! ### An affine target -/

attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory


/-- Postcomposing the legs of a cofan with `v` postcomposes its compactness map with `v`. -/
private theorem cofanMap_comp {D : Type*} [Category D] [Preadditive D] (K : D) {I : Type*}
    [DecidableEq I] {E : I → D} {T T' : D} (j : ∀ i, E i ⟶ T) (v : T ⟶ T')
    (x : DirectSum I fun i => (K ⟶ E i)) :
    cofanMap K (fun i => j i ≫ v) x = cofanMap K j x ≫ v := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y => rw [cofanMap_of, cofanMap_of, Category.assoc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, Preadditive.add_comp]

/-- **`Rf_*` commutes with direct sums on `D_QCoh` over an affine target.** Let `f : X ⟶ Y` be
quasi-compact and quasi-separated with `Y` affine. `𝒪_Y[0]` is a compact generator of `D_QCoh(𝒪_Y)`,
and `Hom(𝒪_Y[n], Rf_* -) = Hom(𝒪_X[n], -)` by adjunction, with `𝒪_X[0]` compact relative to
`D_QCoh(𝒪_X)` since `X` is quasi-compact and quasi-separated. -/
theorem preservesColimit_derivedModulePushforward_of_isAffineSpace (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1) {I : Type u}
    (E : I → DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ i, QcohDerived B S hS X (E i)) :
    PreservesColimit (Discrete.functor E) (derivedModulePushforward B S hS f) := by
  classical
  have hZ := B.contains_terminal
  have hXqc := isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS f.hom hY hfqc
  have hXqs :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS
        hZ f.hom (CategoryTheory.ObjectProperty.FullSubcategory.property _) hY hfqs
  let R := derivedModulePushforward B S hS f
  let P := QcohDerived B S hS Y
  have := isClosedUnderColimitsOfShape_qcohDerived B S hS Y I
  have := isClosedUnderColimitsOfShape_qcohDerived B S hS X I
  have hRE : ∀ i, P (R.obj (E i)) := fun i =>
    qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs _ (hE i)
  have h1 : P (∐ fun i => R.obj (E i)) :=
    P.prop_colimit (Discrete.functor fun i => R.obj (E i)) fun j => hRE j.as
  have h2 : P (R.obj (∐ E)) := qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs _
    ((QcohDerived B S hS X).prop_colimit (Discrete.functor E) fun j => hE j.as)
  let K₁ : P.FullSubcategory := ⟨_, h1⟩
  let K₂ : P.FullSubcategory := ⟨_, h2⟩
  let σ := sigmaComparison R E
  let b : K₁ ⟶ K₂ := ObjectProperty.homMk σ
  have hgen := (isCompactObject_and_isWeakTriangulatedGenerator_unitQuasicoherent
    (X := Y.1) (hX := Y.2) hY).2
  have hb : IsIso b := hgen.isIso_of_bijective_comp b fun Q hQ => by
    obtain ⟨Q₀, a, eQ, hQ₀⟩ := hQ
    obtain rfl := (ObjectProperty.singleton_iff _ _).1 hQ₀
    let eQ' : Q.obj ≅ (unitDerived Y)⟦a⟧ := P.ι.mapIso eQ ≪≫ (P.ι.commShiftIso a).app _
    have hQc : IsQcohCompact B S hS Y Q.obj :=
      ((isQcohCompact_unitDerived_of_isAffineSpace Y hY).shift a).of_iso eQ'.symm
    let L := smallEtaleDerivedModulePullback B S hS f
    let eL : L.obj Q.obj ≅ (unitDerived X)⟦a⟧ :=
      L.mapIso eQ' ≪≫ (L.commShiftIso a).app _ ≪≫
        (shiftFunctor _ a).mapIso
          (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) f)
    have hQX : IsQcohCompact B S hS X (L.obj Q.obj) :=
      ((isQcohCompact_unitDerived hZ X hXqc hXqs).shift a).of_iso eL.symm
    have hbij₁ : Function.Bijective (cofanMap Q.obj (Sigma.ι fun i => R.obj (E i))) :=
      hQc (fun i => R.obj (E i)) hRE _ (coproductIsCoproduct _)
    have hadd := (smallEtaleDerivedModuleAdjunction B S hS f).right_adjoint_additive
    have hbij₂ : Function.Bijective (cofanMap Q.obj fun i => R.map (Sigma.ι E i)) :=
      (bijective_cofanMap_map_iff_of_adjunction (smallEtaleDerivedModuleAdjunction B S hS f)
        Q.obj (Sigma.ι E)).2 (hQX E hE _ (coproductIsCoproduct _))
    have hj : (fun i => R.map (Sigma.ι E i)) = fun i => Sigma.ι (fun i => R.obj (E i)) i ≫ σ :=
      funext fun i => (ι_comp_sigmaComparison R E i).symm
    have hcomp : ⇑(cofanMap Q.obj fun i => R.map (Sigma.ι E i)) =
        (fun g => g ≫ σ) ∘ cofanMap Q.obj (Sigma.ι fun i => R.obj (E i)) := by
      rw [hj]
      funext x
      exact cofanMap_comp _ _ _ x
    have hσ : Function.Bijective fun g : P.ι.obj Q ⟶ P.ι.obj K₁ => g ≫ P.ι.map b := by
      rw [hcomp] at hbij₂
      exact (Function.Bijective.of_comp_iff _ hbij₁).1 hbij₂
    have hkey : (fun g : Q ⟶ K₁ => g ≫ b) =
        P.fullyFaithfulι.homEquiv.symm ∘ (fun g : P.ι.obj Q ⟶ P.ι.obj K₁ => g ≫ P.ι.map b) ∘
          P.fullyFaithfulι.homEquiv := by
      funext g
      apply P.fullyFaithfulι.map_injective
      simp only [Function.comp_apply, Functor.map_comp, Functor.FullyFaithful.homEquiv_apply,
        Functor.FullyFaithful.homEquiv_symm_apply]
      rfl
    rw [hkey]
    exact P.fullyFaithfulι.homEquiv.symm.bijective.comp
      (hσ.comp P.fullyFaithfulι.homEquiv.bijective)
  have : IsIso σ := inferInstanceAs (IsIso (P.ι.map b))
  exact PreservesCoproduct.of_iso_comparison R E

/-! ### An arbitrary target -/

/-- **`Rf_*` commutes with direct sums of objects of `D_QCoh`** for a quasi-compact and
quasi-separated morphism `f : X ⟶ Y` of algebraic spaces, in `D(𝒪_Y)`. The comparison map is an
isomorphism on every affine étale chart `V` of `Y`, where Stacks 08GE identifies it with the
comparison map of the base change `V ×_Y X ⟶ V`, over the affine target `V`. -/
theorem preservesColimit_derivedModulePushforward (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) {I : Type u}
    (E : I → DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ i, QcohDerived B S hS X (E i)) :
    PreservesColimit (Discrete.functor E) (derivedModulePushforward B S hS f) := by
  let R := derivedModulePushforward B S hS f
  suffices IsIso (sigmaComparison R E) from PreservesCoproduct.of_iso_comparison R E
  refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_affineCharts B S hS Y.1) _ fun ⟨A, hA⟩ => ?_
  have hj := isEtale_chartToSpace B S hS Y A
  refine (NatIso.isIso_map_iff (smallEtaleDerivedModulePullbackIsoEtale B S hS _ hj) _).2 ?_
  have sq := isPullback_chartBaseChangeInclusion B S hS f A
  have hi : IsEtale B S hS (chartBaseChangeInclusion B S hS f A).hom :=
    isEtale_of_isPullback B S hS _ _ _ f sq.flip hj
  let Gj := (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y A) hj).mapDerivedCategory
  let Gi := (etaleModulePullback.{u, u} B S hS (chartBaseChangeInclusion B S hS f A)
    hi).mapDerivedCategory
  let R' := derivedModulePushforward B S hS (chartBaseChangeProjection B S hS f A)
  have : PreservesColimitsOfShape (Discrete I) Gj :=
    (etaleDerivedModuleAdjunction B S hS _ hj).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I) Gi :=
    (etaleDerivedModuleAdjunction B S hS _ hi).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimit (Discrete.functor (Gi.obj ∘ E)) R' :=
    preservesColimit_derivedModulePushforward_of_isAffineSpace B S hS _
      (isQuasiCompact_chartBaseChangeProjection B S hS f A hfqc)
      (isQuasiSeparated_chartBaseChangeProjection B S hS f A hfqs)
      (isAffineSpace_chartSpace B S hS Y A hA) _
      fun i => derivedQuasicoherent_etaleModulePullback B S hS _ hi (E i) (hE i)
  have : PreservesColimit (Discrete.functor E ⋙ Gi) R' :=
    preservesColimit_of_iso_diagram R' (Discrete.compNatIsoDiscrete E Gi).symm
  have : PreservesColimit (Discrete.functor E) Gi := inferInstance
  have : PreservesColimit (Discrete.functor E) (Gi ⋙ R') := comp_preservesColimit Gi R'
  have : PreservesColimit (Discrete.functor E) (R ⋙ Gj) := ⟨fun hc =>
    ⟨IsColimit.mapCoconeEquiv (derivedPushforwardEtaleBaseChangeIso B S hS sq hj).symm
      (isColimitOfPreserves (Gi ⋙ R') hc)⟩⟩
  have hcomp : sigmaComparison (R ⋙ Gj) E =
      sigmaComparison Gj (fun i => R.obj (E i)) ≫ Gj.map (sigmaComparison R E) := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [ι_comp_sigmaComparison]
    show Gj.map (R.map (Sigma.ι E i)) = Sigma.ι (fun b => Gj.obj (R.obj (E b))) i ≫ _
    rw [ι_comp_sigmaComparison_assoc, ← Gj.map_comp, ι_comp_sigmaComparison]
  have h₁ : IsIso (sigmaComparison (R ⋙ Gj) E) := inferInstance
  have h₂ : IsIso (sigmaComparison Gj fun i => R.obj (E i)) := inferInstance
  rw [hcomp] at h₁
  exact IsIso.of_isIso_comp_left (sigmaComparison Gj fun i => R.obj (E i)) _

/-- **Stacks 08FB.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic
spaces. Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with direct sums. -/
theorem preservesCoproducts_quasicoherentDerivedPushforward (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (quasicoherentDerivedPushforward B S hS f hfqc hfqs) := by
  have := isClosedUnderColimitsOfShape_qcohDerived B S hS X I
  have := isClosedUnderColimitsOfShape_qcohDerived B S hS Y I
  refine ⟨fun {K} => ?_⟩
  suffices ∀ E : I → QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      PreservesColimit (Discrete.functor E)
        (quasicoherentDerivedPushforward B S hS f hfqc hfqs) from
    preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm
  intro E
  let ιX := (QcohDerived B S hS X).ι
  let ιY := (QcohDerived B S hS Y).ι
  have : PreservesColimit (Discrete.functor (ιX.obj ∘ E)) (derivedModulePushforward B S hS f) :=
    preservesColimit_derivedModulePushforward B S hS f hfqc hfqs _ fun i => (E i).property
  have : PreservesColimit (Discrete.functor E ⋙ ιX) (derivedModulePushforward B S hS f) :=
    preservesColimit_of_iso_diagram _ (Discrete.compNatIsoDiscrete E ιX).symm
  have : PreservesColimit (Discrete.functor E)
      (quasicoherentDerivedPushforward B S hS f hfqc hfqs ⋙ ιY) :=
    preservesColimit_of_natIso _ (quasicoherentDerivedPushforwardCompιIso B S hS f hfqc hfqs).symm
  exact preservesColimit_of_reflects_of_preserves _ ιY

end AlgebraicGeometry.Space

end
