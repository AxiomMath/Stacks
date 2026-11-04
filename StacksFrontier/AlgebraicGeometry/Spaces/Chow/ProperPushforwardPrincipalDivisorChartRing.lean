module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisorChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisorReading
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldEvaluation
public import StacksFrontier.RingTheory.OrderOfVanishing.NormBranches

/-!
# The rings of the chart of Stacks 0EQ4

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- A point of an étale chart whose local ring is a field lies over a point of the space whose
local ring has dimension zero. -/
theorem localRingDimension_chartSchemeToPoints_eq_zero
    {F : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace D.site D.base D.base_mem F) (V : SmallEtale D.site D.base D.base_mem F)
    (w : chartScheme V) (hw : IsField ((chartScheme V).presheaf.stalk w)) :
    localRingDimension D.site D.base D.base_mem
      (chartSchemeToPoints D.site D.base D.base_mem F V w) = 0 := by
  refine (localRingDimension_eq_iff_hasChartLocalRingDimension D.site D.base D.base_mem hF _ 0).mpr
    ⟨V.obj.left, V.obj.hom, w, V.property,
      chartPoint_chartSchemeToPoints D.site D.base D.base_mem ⟨F, hF⟩ V w, ?_⟩
  exact (ringKrullDim_eq_zero_of_isField hw).trans rfl

section Chart

variable {p : X ⟶ Y} (d : ChartDiagram D.site D.base D.base_mem X Y p)

/-- The `Γ(V)`-algebra structure of `Γ(U)` along the chart `U ⟶ V`. -/
@[reducible] def chartRingAlgebra :
    Algebra Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤) :=
  ((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).appTop.hom.toAlgebra

attribute [local instance] chartRingAlgebra

variable [IsAffine d.U.obj.left.left.1] [IsAffine d.V.obj.left.left.1]
  [IsReduced d.U.obj.left.left.1] [IsReduced d.V.obj.left.left.1]
  [IsLocallyNoetherian d.U.obj.left.left.1] [IsLocallyNoetherian d.V.obj.left.left.1]

/-- On an affine scheme every prime of the ring of global sections is the prime of a point. -/
theorem exists_primeIdealOf_eq (T : Scheme.{u}) [IsAffine T] (y : PrimeSpectrum Γ(T, ⊤)) :
    ∃ x : (⊤ : T.Opens), (isAffineOpen_top T).primeIdealOf x = y := by
  obtain ⟨x, hx⟩ := (isAffineOpen_top T).isoSpec.hom.surjective y
  exact ⟨x, hx⟩

/-- At a point of an affine reduced scheme whose prime is minimal, the local ring is a field. -/
theorem isField_stalk_of_mem_minimalPrimes (T : Scheme.{u}) [IsAffine T] [IsReduced T]
    (x : (⊤ : T.Opens))
    (hx : ((isAffineOpen_top T).primeIdealOf x).asIdeal ∈ minimalPrimes Γ(T, ⊤)) :
    IsField (T.presheaf.stalk x.1) := by
  let := T.presheaf.algebra_section_stalk x
  have := (isAffineOpen_top T).isLocalization_stalk x
  exact (IsLocalization.algEquiv ((isAffineOpen_top T).primeIdealOf x).asIdeal.primeCompl
    (T.presheaf.stalk x.1)
    (Localization.AtPrime ((isAffineOpen_top T).primeIdealOf x).asIdeal)).toMulEquiv.isField
    (isField_localizationAtPrime_of_minimal Γ(T, ⊤) _ hx)

/-- At a point of an affine scheme whose local ring is a field, the residue field, with the
evaluation of global sections, is the localization at the prime of the point. -/
theorem isLocalization_residueField_of_isField (T : Scheme.{u}) [IsAffine T]
    (x : (⊤ : T.Opens)) (hx : IsField (T.presheaf.stalk x.1)) :
    letI := (T.Γevaluation x.1).hom.toAlgebra
    IsLocalization.AtPrime (T.residueField x.1) ((isAffineOpen_top T).primeIdealOf x).asIdeal := by
  let := (T.Γevaluation x.1).hom.toAlgebra
  let := T.presheaf.algebra_section_stalk x
  have := (isAffineOpen_top T).isLocalization_stalk x
  let e : T.presheaf.stalk x.1 ≃+* T.residueField x.1 :=
    RingEquiv.ofBijective (T.residue x.1).hom (Scheme.bijective_residue_of_isField hx)
  let e' : T.presheaf.stalk x.1 ≃ₐ[Γ(T, ⊤)] T.residueField x.1 :=
    { e with commutes' := fun a => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e'

include hintY in
omit [IsReduced d.U.obj.left.left.1] [IsLocallyNoetherian d.U.obj.left.left.1] in
/-- **The generic fibre of the chart at a generic point `w` of `V`, as two cocartesian squares of
rings.** The fibre `G = U ×_V Spec κ(w)` has global sections the base change of `R(X)/R(Y)`
along `R(Y) → κ(w)`, and the base change of `Γ(V) → Γ(U)` along `Γ(V) → κ(w)`; the homomorphism
`R(Y) → κ(w)` is the reading of rational functions at `w`. -/
theorem exists_isPushout_chartGenericFibre (hpB : p ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY)
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      deltaDimensionClosed D sY hY Set.univ isClosed_univ)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) p d.V.1.hom) (w : chartScheme d.V)
    (hw : IsField ((chartScheme d.V).presheaf.stalk w)) :
    ∃ (φ : residueField D.site D.base D.base_mem Y hintY.2.1
          (pointsMap D.site D.base D.base_mem X p
            (genericPoint D.site D.base D.base_mem hX.1 hintX)) →+*
          (chartScheme d.V).residueField w)
      (r : chartGenericFibre D d w ⟶ (residueFieldRepresentative D.site D.base D.base_mem X
          hintX.2.1 (genericPoint D.site D.base D.base_mem hX.1 hintX)).1.siteObject
          D.site D.base D.base_mem X),
      IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (residueFieldHom D.site D.base
          D.base_mem X Y hY.1 hintX.2.1 hintY.2.1 p
          (genericPoint D.site D.base D.base_mem hX.1 hintX)))
        ((Scheme.ΓSpecIso (CommRingCat.of ((chartScheme d.V).residueField w))).inv ≫
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map
            (Limits.pullback.snd d.g (fibreChartFieldPoint D d w).siteHom)).appTop)
        ((Scheme.ΓSpecIso (CommRingCat.of (residueField D.site D.base D.base_mem X hintX.2.1
            (genericPoint D.site D.base D.base_mem hX.1 hintX)))).inv ≫
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map r).appTop) ∧
      IsPushout ((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).appTop
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map
            (fibreChartFieldPoint D d w).siteHom).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of ((chartScheme d.V).residueField w))).hom)
        ((BigFppfOver.toScheme D.site D.base D.base_mem).map
          (Limits.pullback.fst d.g (fibreChartFieldPoint D d w).siteHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ((chartScheme d.V).residueField w))).inv ≫
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map
            (Limits.pullback.snd d.g (fibreChartFieldPoint D d w).siteHom)).appTop) ∧
      yoneda.map r ≫ residueFieldMorphism D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX) =
        yoneda.map (Limits.pullback.fst d.g (fibreChartFieldPoint D d w).siteHom) ≫
          d.U.1.hom ∧
      ∀ g : rationalFunctions D.site D.base D.base_mem hY.1,
        φ (evalRingHom D.site D.base D.base_mem hY.1 hintY
            (residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1
              (pointsMap D.site D.base D.base_mem X p
                (genericPoint D.site D.base D.base_mem hX.1 hintX))).1
            ((residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1 _).2.1.trans hgen)
            g) =
          Scheme.totalFractionRingToResidueField (T := d.V.obj.left.left.1) w hw
            (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hY.1 d.V.obj.left
              d.V.obj.hom ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem
                d.V.obj.hom).2 d.V.property) g) := by
  have hwgen : chartSchemeToPoints D.site D.base D.base_mem Y d.V w =
      pointsMap D.site D.base D.base_mem X p (genericPoint D.site D.base D.base_mem hX.1 hintX) :=
    (eq_genericPoint_of_localRingDimension_eq_zero D hintY hY.1
      (localRingDimension_chartSchemeToPoints_eq_zero D hY.1 d.V w hw)).trans hgen.symm
  obtain ⟨g0, f, r, hg0, hf, hr, hcart⟩ := exists_isPullback_chartFibre D sX hX sY hY hintX
    hintY d hpB hproper hgen hdim hd w hwgen
  obtain ⟨φ, hφ⟩ := exists_eq_specMap_of_hom_siteObject D.site D.base D.base_mem f
  have hψ := eq_specMap_residueFieldHom D.site D.base D.base_mem hY.1 hintX.2.1 hintY.2.1 p
    (genericPoint D.site D.base D.base_mem hX.1 hintX) hg0
  refine ⟨φ, r, ?_, ?_, hr, ?_⟩
  · refine isPushout_of_isPullback_specMap φ _ ?_
    have h0 := (IsPullback.of_map_of_faithful yoneda hcart).map
      (BigFppfOver.toScheme D.site D.base D.base_mem)
    rwa [show (BigFppfOver.toScheme D.site D.base D.base_mem).map g0 =
        Spec.map (CommRingCat.ofHom (residueFieldHom D.site D.base D.base_mem X Y hY.1 hintX.2.1
          hintY.2.1 p (genericPoint D.site D.base D.base_mem hX.1 hintX))) from hψ,
      show (BigFppfOver.toScheme D.site D.base D.base_mem).map f =
        Spec.map (CommRingCat.ofHom φ) from hφ] at h0
  · have : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
        ((SmallEtale.toOver D.site D.base D.base_mem X).obj d.U)) := ‹IsAffine d.U.obj.left.left.1›
    have : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
        ((SmallEtale.toOver D.site D.base D.base_mem Y).obj d.V)) := ‹IsAffine d.V.obj.left.left.1›
    exact isPushout_appTop_of_isPullback_yoneda_fieldValuedPoint D.site D.base D.base_mem
      ((IsPullback.of_hasPullback d.g (fibreChartFieldPoint D d w).siteHom).map yoneda)
  · intro g
    have hfac : yoneda.map f ≫ fieldMorphism D.site D.base D.base_mem Y
        (residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1
          (pointsMap D.site D.base D.base_mem X p
            (genericPoint D.site D.base D.base_mem hX.1 hintX))).1 =
        fieldMorphism D.site D.base D.base_mem Y
          (chartSchemeFieldValuedPoint D.site D.base D.base_mem Y d.V w) :=
      hf.symm.trans (fieldMorphism_map_yoneda D.site D.base D.base_mem _ _ _).symm
    have hcls : (chartSchemeFieldValuedPoint D.site D.base D.base_mem Y d.V w).class D.site D.base
        D.base_mem Y = genericPoint D.site D.base D.base_mem hY.1 hintY := hwgen.trans hgen
    refine (evalRingHom_eq_of_factor D.site D.base D.base_mem hY.1 hintY _ _ hcls _ f hfac φ hφ
      g).symm.trans ?_
    exact evalRingHom_chartSchemeFieldValuedPoint D.site D.base D.base_mem hY.1 hintY d.V w hw
      hcls g

end Chart

end AlgebraicGeometry.Space

end
