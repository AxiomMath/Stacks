module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import
  StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.DegreeZeroHypercohomology
public import
  StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.OpenImmersionCovariance
public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerKrullIntersection
public import StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Restriction

/-!
# Degree-zero compactly supported cohomology of a connective complex

Let `X` be a proper scheme over a field `k`, let `K ∈ D^b_{Coh}(𝒪_X)` with `H^i(K) = 0` for
`i < 0`, set `𝓕 = H^0(K)`, and let `U = X ∖ Z` for a closed `Z ⊆ X`. Then
`H^0_c(U, K|_U) ⊂ H^0(X, 𝓕)` is given by the global sections of `𝓕` vanishing on an open
neighbourhood of `Z`.

## Main definitions

* `AlgebraicGeometry.structureSheafBoundedCoherent`: `𝒪_Y` in degree `0`, in `D^b_{Coh}(𝒪_Y)`.
* `AlgebraicGeometry.degreeZeroCompactSupport`: `H^0_c(U, K) = Hom_{Pro}(𝒪_Y, Rg_! K)` for `X`
  proper over `Y` the compactification of `U`; for a Deligne system `(K_n)` with value `K` this is
  `lim_n H^0(X, K_n)`, the definition of [Stacks, Section 0G59].
* `AlgebraicGeometry.degreeZeroCompactSupportMap`: the map `H^0_c(U, K|_U) ⟶ H^0(X, H^0(K))`
  induced by the map `Rg_!(K|_U) ⟶ Rp_* K` of [Stacks, Tag 0G56] with `X` its own
  compactification.

## Main results

* `AlgebraicGeometry.exists_isCoherent_complex_isStrictlyGE_zero_iso`: a connective object of
  `D^b_{Coh}(𝒪_X)` is a bounded complex of coherent modules vanishing in negative degrees.
* `AlgebraicGeometry.degreeZeroCompactSupportMap_injective` and
  `AlgebraicGeometry.range_degreeZeroCompactSupportMap`: the two halves of the statement, over a
  Noetherian base.
* `AlgebraicGeometry.degreeZeroCompactSupportMap_injective_and_range`: for `X` proper over a
  field, `H^0_c(U, K|_U) ⟶ H^0(X, 𝓕)` is injective, with image the global sections of `𝓕`
  vanishing on an open neighbourhood of `Z`.

## References

* [Stacks Project, Tag 0G5C](https://stacks.math.columbia.edu/tag/0G5C)
* [Stacks Project, Tag 0G56](https://stacks.math.columbia.edu/tag/0G56)
* [Stacks Project, Section 0G59](https://stacks.math.columbia.edu/tag/0G59)
* [Stacks Project, Tag 00IP](https://stacks.math.columbia.edu/tag/00IP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u


namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A connective object of `D^b_{Coh}(𝒪_X)` is a bounded complex of coherent modules in degrees
`≥ 0`**, on a Noetherian scheme. -/
public theorem exists_isCoherent_complex_isStrictlyGE_zero_iso {X : Scheme.{u}} [IsNoetherian X]
    (K : BoundedCoherentDerived X) (hK : K.obj.IsGE 0) :
    ∃ (F : CochainComplex X.Modules ℤ) (b : ℤ), (∀ i, (F.X i).IsCoherent) ∧ F.IsStrictlyGE 0 ∧
      F.IsStrictlyLE b ∧ Nonempty (DerivedCategory.Q.obj F ≅ K.obj) := by
  let Y := (coherentToModulesDerivedBounded X).objPreimage K
  have eY : ((coherentToModulesDerivedBounded X).obj Y).obj ≅ K.obj :=
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι.mapIso
      ((coherentToModulesDerivedBounded X).objObjPreimageIso K)
  obtain ⟨b, hb⟩ := Y.property.2
  have hY : Y.obj.IsGE 0 := (DerivedCategory.isGE_iff _ 0).2 fun i hi ↦
    ((coherentInModules X).ι.isZero_homologyFunctor_obj_mapDerivedCategory_obj_iff Y.obj i).1
      ((K.obj.isZero_of_isGE 0 i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eY))
  obtain ⟨F', hGE', hLE', ⟨eF⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE Y.obj 0 b
  refine ⟨((coherentInModules X).ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj F', b,
    fun i ↦ (F'.X i).property, ?_, ?_,
    ⟨((coherentInModules X).ι.mapDerivedCategoryFactors.app F').symm ≪≫
      (coherentInModules X).ι.mapDerivedCategory.mapIso eF.symm ≪≫ eY⟩⟩
  · exact (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦
      Functor.map_isZero (coherentInModules X).ι (F'.isZero_of_isStrictlyGE 0 i hi)
  · exact (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi ↦
      Functor.map_isZero (coherentInModules X).ι (F'.isZero_of_isStrictlyLE b i hi)

namespace DegreeZeroCompactSupport

/-- The vanishing ideal of the closed complement of an open. -/
public noncomputable def complementIdeal {X : Scheme.{u}} (U : X.Opens) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩

/-- The ideal of `X ∖ U` cuts out `X ∖ U`. -/
public lemma coe_support_complementIdeal {X : Scheme.{u}} (U : X.Opens) :
    ((complementIdeal U).support : Set X) = (Set.range U.ι.base)ᶜ := by
  rw [complementIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι]
  rfl

end DegreeZeroCompactSupport

/-- `𝒪_Y` placed in degree `0`, as an object of `D^b_{Coh}(𝒪_Y)`. -/
public noncomputable def structureSheafBoundedCoherent (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    BoundedCoherentDerived Y :=
  ⟨(DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf), by
    let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
    have e : ∀ i : ℤ, (DerivedCategory.homologyFunctor Y.Modules i).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj O) ≅
        ((CochainComplex.singleFunctor Y.Modules 0).obj O).homology i := fun i ↦
      (DerivedCategory.homologyFunctor Y.Modules i).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ Y.Modules 0).app O) ≪≫
        (DerivedCategory.homologyFunctorFactors Y.Modules i).app _
    have hzero : ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj O)) := fun i hi ↦
      (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi).of_iso (e i)
    refine ⟨⟨⟨0, fun i hi ↦ hzero i (by omega)⟩, ⟨0, fun i hi ↦ hzero i (by omega)⟩⟩,
      fun i ↦ ?_⟩
    rcases eq_or_ne i 0 with rfl | hi
    · exact (coherentInModules Y).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).app O).symm
        (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit : O.IsCoherent)
    · exact (coherentInModules Y).prop_of_isZero (hzero i hi)⟩

section CompactSupport

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Y) [IsProper p]

/-- **Degree-zero compactly supported cohomology** `H^0_c(U, K)` of `K ∈ D^b_{Coh}(𝒪_U)`, for an
open `U` of a scheme `X` proper over a Noetherian `Y`, with `X` the compactification of `U` over
`Y`: the morphisms `𝒪_Y ⟶ Rg_! K` in `Pro-D^b_{Coh}(𝒪_Y)`, where `g : U ⟶ Y` and
`Rg_! = Rp_* ∘ Rj_!` is the functor of [Stacks, Section 0G4Z] for this compactification. If
`(K_n)` is a Deligne system with value `K`, then `Rg_! K` is given by `(Rp_* K_n)` and this is
`lim_n Hom(𝒪_Y, Rp_* K_n) = lim_n H^0(X, K_n)`, the definition of [Stacks, Section 0G59]. -/
public abbrev degreeZeroCompactSupport (U : X.Opens) (K : BoundedCoherentDerived U) : Type _ :=
  ProSeq.const.obj (structureSheafBoundedCoherent Y) ⟶
    (CompactificationData.ofOpenImmersion U.ι p).shriekImage.obj K

/-- `X` as a compactification of its open `U` over `Y`: the open immersion `U ⟶ X` and the proper
`p : X ⟶ Y`. -/
public def openCompactification (U : X.Opens) : CompactificationOf (Over.mk (U.ι ≫ p)) :=
  ⟨StructuredArrow.mk (T := 𝟭 (Over Y)) (Over.homMk (V := Over.mk p) U.ι rfl),
    ⟨inferInstanceAs (IsOpenImmersion U.ι), inferInstanceAs (IsProper p)⟩⟩

/-- `H^0_c(U, K)` is defined through the functor `Rg_!` of [Stacks, Section 0G4Z],
`AlgebraicGeometry.lowerShriek`, of the morphism `g : U ⟶ Y` of `FTS_Y` and the compactification
`X` of `U`. -/
public lemma degreeZeroCompactSupport_eq_lowerShriek (U : X.Opens)
    (K : BoundedCoherentDerived U) :
    degreeZeroCompactSupport p U K =
      (ProSeq.const.obj (structureSheafBoundedCoherent Y) ⟶
        (lowerShriek (X₁ := FTS.mk (U.ι ≫ p)) (Y₁ := FTS.mk (𝟙 Y))
          (MorphismProperty.Over.homMk (U.ι ≫ p) (Category.comp_id _) trivial)
          (openCompactification p U)).obj K) :=
  rfl

/-- **The map `H^0_c(U, K|_U) ⟶ H^0(X, K) = Γ(X, H^0(K))`** of [Stacks, Tag 0G5C]: composition
with the map `Rg_!(K|_U) ⟶ Rp_* K` of [Stacks, Tag 0G56] for `X` its own compactification
(`AlgebraicGeometry.lowerShriekToProperPushforward`), followed by
`Hom(𝒪_Y, Rp_* K) = Γ(X, H^0(K))` for `K` without cohomology in negative degrees. -/
public noncomputable def degreeZeroCompactSupportMap (U : X.Opens) (K : BoundedCoherentDerived X)
    (hK : K.obj.IsGE 0) :
    degreeZeroCompactSupport p U ((restrictBoundedCoherentLift U.ι).obj K) →
      Γ((DerivedCategory.homologyFunctor X.Modules 0).obj K.obj, ⊤) :=
  fun s ↦ derivedPushforwardHomEquiv p K.obj hK
    (ProSeq.homConstEquiv _ _ (s ≫ lowerShriekToProperPushforward p U K)).hom

end CompactSupport

namespace DegreeZeroCompactSupport

/-- `homologyZeroToX` on global sections is natural in the complex. -/
private lemma homologyZeroToX_app_top_map {X : Scheme.{u}} {G G' : CochainComplex X.Modules ℤ}
    [G.IsStrictlyGE 0] [G'.IsStrictlyGE 0] (φ : G ⟶ G')
    (τ : Γ((DerivedCategory.homologyFunctor X.Modules 0).obj (DerivedCategory.Q.obj G), ⊤)) :
    (DerivedCategory.homologyZeroToX G').app ⊤
      (((DerivedCategory.homologyFunctor X.Modules 0).map (DerivedCategory.Q.map φ)).app ⊤ τ) =
    (φ.f 0).app ⊤ ((DerivedCategory.homologyZeroToX G).app ⊤ τ) := by
  have h := congrArg (fun ψ ↦ Scheme.Modules.Hom.app ψ ⊤ τ)
    (DerivedCategory.homologyZeroToX_naturality φ)
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h

section Setup

variable {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens) (K : BoundedCoherentDerived X)
  (F : CochainComplex X.Modules ℤ) (b : ℤ) [F.IsStrictlyGE 0] [F.IsStrictlyLE b]
  (hF : ∀ i, (F.X i).IsCoherent) (e : DerivedCategory.Q.obj F ≅ K.obj)

/-- The Deligne system `(𝓘^n 𝓕^•)` of `𝓕^•` for the ideal of `X ∖ U`. -/
public noncomputable abbrev idealSystem : DeligneSystem U.ι :=
  DeligneTriangle.deligneSystemOfComplex U.ι (complementIdeal U) (coe_support_complementIdeal U) F
    ⟨0, inferInstance⟩ ⟨b, inferInstance⟩ hF

/-- Its value `K|_U`, through `e`. -/
public noncomputable abbrev idealValue : (idealSystem U F b hF).Value :=
  DeligneSystem.ofComplexValue (j := U.ι) (complementIdeal U) (coe_support_complementIdeal U) F
    ⟨0, inferInstance⟩ ⟨b, inferInstance⟩ hF ((restrictBoundedCoherentLift U.ι).obj K)
    ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.mapIso e)

/-- The inclusion `𝓘^n 𝓕^• ⟶ 𝓕^• ≅ K`, in `D^b_{Coh}(𝒪_X)`. -/
public noncomputable def idealInclusion (n : ℕ) : (idealSystem U F b hF).system.obj (op n) ⟶ K :=
  ObjectProperty.homMk
    (DerivedCategory.Q.map ((idealPowerComplexSystem (complementIdeal U) F).inclusion n) ≫ e.hom)

/-- Under `Hom_U(K|_U, L|_U) = colim_n Hom(𝓘^n 𝓕^•, L)` the identity of `K|_U` is the class of
the inclusion `𝓕^• ⟶ K` at stage `0`. -/
public lemma idealValue_pointsIso_hom_app_id :
    (idealValue U K F b hF e).pointsIso.hom.app K (𝟙 _) =
      (Pro.seqHomColimIso _).inv.app K
        (Pro.seqStage (idealSystem U F b hF).system (n := 0) (idealInclusion U K F b hF e 0)) := by
  have h : (idealValue U K F b hF e).pointsIso.inv.app K ((Pro.seqHomColimIso _).inv.app K
      (Pro.seqStage (idealSystem U F b hF).system (n := 0) (idealInclusion U K F b hF e 0))) =
        𝟙 _ := by
    rw [ProSeq.seqHomColimIso_inv_app_seqStage]
    refine (DeligneSystem.Value.pointsIso_inv_app_ι (idealValue U K F b hF e)
      (ProSeq.liftedStage 0) K
      (idealInclusion U K F b hF e 0)).trans ?_
    apply ObjectProperty.hom_ext
    change _ ≫ (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map
      (DerivedCategory.Q.map ((idealPowerComplexSystem (complementIdeal U) F).inclusion 0) ≫
        e.hom) = 𝟙 _
    rw [Functor.map_comp]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map e.hom)
      (DeligneSystem.ofComplexValue_constIso_inv_app_comp (j := U.ι) (complementIdeal U)
        (coe_support_complementIdeal U) F ⟨0, inferInstance⟩ ⟨b, inferInstance⟩ hF _ _ 0)).trans ?_
    exact ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.mapIso e).inv_hom_id
  rw [← h]
  exact Iso.inv_hom_id_app_apply _ _ _

variable {Y : Scheme.{u}} [IsNoetherian Y] (p : X ⟶ Y) [IsProper p]

/-- `Rg_!(K|_U)` is the pro-object of `(Rp_*(𝓘^n 𝓕^•))`. -/
public noncomputable def idealShriekIso :
    ProSeq.of ((idealSystem U F b hF).system ⋙ properPushforwardBoundedCoherent p) ≅
      (CompactificationData.ofOpenImmersion U.ι p).shriekImage.obj
        ((restrictBoundedCoherentLift U.ι).obj K) :=
  (ProSeq.mapOfIso _ _).symm ≪≫ (ProSeq.map _).mapIso (idealValue U K F b hF e).extensionByZeroIso

/-- Under `Rg_!(K|_U) = (Rp_*(𝓘^n 𝓕^•))` the map of [Stacks, Tag 0G56] is the class of
`Rp_*(𝓕^• ⟶ K)` at stage `0`. -/
public lemma homConstEquiv_idealShriekIso_hom_comp :
    ProSeq.homConstEquiv _ _ ((idealShriekIso U K F b hF e p).hom ≫
        lowerShriekToProperPushforward p U K) =
      (Pro.seqHomColimIso _).inv.app _ (Pro.seqStage
        ((idealSystem U F b hF).system ⋙ properPushforwardBoundedCoherent p) (n := 0)
          ((properPushforwardBoundedCoherent p).map (idealInclusion U K F b hF e 0))) := by
  refine (ProSeq.homConstEquiv_comp _ _).trans ?_
  refine (congrArg ((idealShriekIso U K F b hF e p).hom.unop.hom.app _)
    ((ProSeq.homConstEquiv_mapConst (properPushforwardBoundedCoherent p)
      (extensionByZeroCounit U K)).trans
        (congrArg _ (extensionByZeroHomEquiv_extensionByZeroCounit U K)))).trans ?_
  refine (congrArg ((ProSeq.mapOfIso (properPushforwardBoundedCoherent p)
    (idealSystem U F b hF).system).inv.unop.hom.app _)
      (ProSeq.lan_map_app_lanUnit_app (properPushforwardBoundedCoherent p)
        (idealValue U K F b hF e).extensionByZeroIso.hom.unop.hom K (𝟙 _))).trans ?_
  refine (congrArg ((ProSeq.mapOfIso (properPushforwardBoundedCoherent p)
    (idealSystem U F b hF).system).inv.unop.hom.app _)
      (congrArg (ConcreteCategory.hom (((properPushforwardBoundedCoherent p).lanUnit.app
          (ProSeq.of (idealSystem U F b hF).system).points).app K))
        (idealValue_pointsIso_hom_app_id U K F b hF e))).trans ?_
  exact ProSeq.mapOfIso_inv_app_lanUnit_app _ _ _

/-- The global section `H^0(Rp_*(𝓘^n 𝓕^•))` attached to the `n`-th component of a morphism into
`(Rp_*(𝓘^n 𝓕^•))`. -/
public noncomputable def idealSection
    (y : ProSeq.const.obj (structureSheafBoundedCoherent Y) ⟶
      ProSeq.of ((idealSystem U F b hF).system ⋙ properPushforwardBoundedCoherent p)) (n : ℕ) :
    Γ((DerivedCategory.homologyFunctor X.Modules 0).obj (DerivedCategory.Q.obj
      ((idealPowerComplexSystem (complementIdeal U) F).complex n)), ⊤) :=
  haveI := (DeligneTriangle.idealPowerComplex_bounds (complementIdeal U) F 0 b inferInstance
    inferInstance n).1
  derivedPushforwardHomEquiv p _ inferInstance (ProSeq.constHomComponent y n).hom

/-- The `n`-th ideal-power subcomplex. -/
public noncomputable abbrev idealComplex (n : ℕ) : CochainComplex X.Modules ℤ :=
  (idealPowerComplexSystem (complementIdeal U) F).complex n

include b in
omit [IsNoetherian X] in
/-- The ideal-power subcomplexes of `𝓕^•` vanish in negative degrees. -/
public lemma isStrictlyGE_idealComplex (n : ℕ) : (idealComplex U F n).IsStrictlyGE 0 :=
  (DeligneTriangle.idealPowerComplex_bounds (complementIdeal U) F 0 b inferInstance
    inferInstance n).1

include b in
/-- `ν_n : Γ(H^0(𝓘^n 𝓕^•)) ⟶ Γ(𝓕^0)`: degree-zero cohomology is the kernel of `d^0`, followed by
the inclusion `𝓘^n 𝓕^0 ⊆ 𝓕^0`. -/
public noncomputable def idealSectionToTerm (n : ℕ)
    (τ : Γ((DerivedCategory.homologyFunctor X.Modules 0).obj
      (DerivedCategory.Q.obj (idealComplex U F n)), ⊤)) : Γ(F.X 0, ⊤) :=
  haveI := isStrictlyGE_idealComplex U F b n
  (((idealPowerComplexSystem (complementIdeal U) F).inclusion n).f 0).app ⊤
    ((DerivedCategory.homologyZeroToX (idealComplex U F n)).app ⊤ τ)

include b in
omit [IsNoetherian X] in
/-- `ν_n` is injective. -/
public lemma idealSectionToTerm_injective (n : ℕ) :
    Function.Injective (idealSectionToTerm U F b n) := by
  have := isStrictlyGE_idealComplex U F b n
  have : Mono (((idealPowerComplexSystem (complementIdeal U) F).inclusion n).f 0) :=
    inferInstanceAs (Mono (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
      (complementIdeal U) n (F.X 0)).ι)
  exact (Stacks.AlgebraicGeometry.RelativeMayerVietoris.injective_app_of_mono _ ⊤).comp
    (Stacks.AlgebraicGeometry.RelativeMayerVietoris.injective_app_of_mono _ ⊤)

include b in
omit [IsNoetherian X] in
/-- The maps `ν_n` are compatible with the transitions `𝓘^{n+1} 𝓕^• ⟶ 𝓘^n 𝓕^•`. -/
public lemma idealSectionToTerm_transition (n : ℕ)
    (τ : Γ((DerivedCategory.homologyFunctor X.Modules 0).obj
      (DerivedCategory.Q.obj (idealComplex U F (n + 1))), ⊤)) :
    idealSectionToTerm U F b n (((DerivedCategory.homologyFunctor X.Modules 0).map
      (DerivedCategory.Q.map ((idealPowerComplexSystem (complementIdeal U) F).transition n))).app
        ⊤ τ) = idealSectionToTerm U F b (n + 1) τ := by
  have := isStrictlyGE_idealComplex U F b n
  have := isStrictlyGE_idealComplex U F b (n + 1)
  change (((idealPowerComplexSystem (complementIdeal U) F).inclusion n).f 0).app ⊤ _ = _
  rw [homologyZeroToX_app_top_map, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, ← HomologicalComplex.comp_f,
    (idealPowerComplexSystem (complementIdeal U) F).transition_include n]
  rfl

/-- `ρ : Γ(H^0(K)) ⟶ Γ(𝓕^0)` through `H^0(K) ≅ H^0(𝓕^•) = ker d^0 ⊆ 𝓕^0`. -/
public noncomputable def sectionToTerm
    (σ : Γ((DerivedCategory.homologyFunctor X.Modules 0).obj K.obj, ⊤)) :
    Γ(F.X 0, ⊤) :=
  (DerivedCategory.homologyZeroToX F).app ⊤
    (((DerivedCategory.homologyFunctor X.Modules 0).map e.inv).app ⊤ σ)

/-- The transitions of `(Rp_*(𝓘^n 𝓕^•))` are `Rp_*` of the inclusions `𝓘^{n+1} 𝓕^• ⟶ 𝓘^n 𝓕^•`. -/
public lemma idealSystem_comp_map_succ_hom (n : ℕ) :
    (((idealSystem U F b hF).system ⋙ properPushforwardBoundedCoherent p).map
      (homOfLE (Nat.le_succ n)).op).hom = (derivedPushforwardModules p).map
        (DerivedCategory.Q.map ((idealPowerComplexSystem (complementIdeal U) F).transition n)) := by
  change (derivedPushforwardModules p).map (DerivedCategory.Q.map
    ((DeligneTriangle.idealPowerComplexFunctor (complementIdeal U) F).map
      (homOfLE (Nat.le_succ n)).op)) = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

include b in
/-- The sections attached to a compatible family are compatible with the transitions. -/
public lemma idealSection_succ
    (y : ProSeq.const.obj (structureSheafBoundedCoherent Y) ⟶
      ProSeq.of ((idealSystem U F b hF).system ⋙ properPushforwardBoundedCoherent p)) (n : ℕ) :
    idealSection U F b hF p y n = ((DerivedCategory.homologyFunctor X.Modules 0).map
      (DerivedCategory.Q.map ((idealPowerComplexSystem (complementIdeal U) F).transition n))).app
        ⊤ (idealSection U F b hF p y (n + 1)) := by
  have := isStrictlyGE_idealComplex U F b n
  have := isStrictlyGE_idealComplex U F b (n + 1)
  have h := congrArg (fun φ ↦ φ.hom) (ProSeq.constHomComponent_comp_tr y (Nat.le_succ n))
  rw [ObjectProperty.FullSubcategory.comp_hom,
    show (InverseSequence.tr ((idealSystem U F b hF).system ⋙ properPushforwardBoundedCoherent p)
      (Nat.le_succ n)).hom = _ from idealSystem_comp_map_succ_hom U F b hF p n] at h
  unfold idealSection
  rw [← h]
  exact derivedPushforwardHomEquiv_comp p _ _ _ _

include b in
/-- All the `ν_n` of a compatible family give the same section of `𝓕^0`. -/
public lemma idealSectionToTerm_idealSection
    (y : ProSeq.const.obj (structureSheafBoundedCoherent Y) ⟶
      ProSeq.of ((idealSystem U F b hF).system ⋙ properPushforwardBoundedCoherent p)) (n : ℕ) :
    idealSectionToTerm U F b n (idealSection U F b hF p y n) =
      idealSectionToTerm U F b 0 (idealSection U F b hF p y 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih, idealSection_succ U F b hF p y n, idealSectionToTerm_transition]

include b in
/-- The image of `s ∈ H^0_c(U, K|_U)` in `Γ(𝓕^0)` is `ν_0` of its `0`-th component. -/
public lemma sectionToTerm_degreeZeroCompactSupportMap (hK : K.obj.IsGE 0)
    (s : degreeZeroCompactSupport p U ((restrictBoundedCoherentLift U.ι).obj K)) :
    sectionToTerm K F e (degreeZeroCompactSupportMap p U K hK s) =
      idealSectionToTerm U F b 0
        (idealSection U F b hF p (s ≫ (idealShriekIso U K F b hF e p).inv) 0) := by
  have := isStrictlyGE_idealComplex U F b 0
  set y := s ≫ (idealShriekIso U K F b hF e p).inv with hy
  have hs : s = y ≫ (idealShriekIso U K F b hF e p).hom := by
    rw [hy, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h1 : ProSeq.homConstEquiv _ _ (s ≫ lowerShriekToProperPushforward p U K) =
      ProSeq.constHomComponent y 0 ≫
        (properPushforwardBoundedCoherent p).map (idealInclusion U K F b hF e 0) := by
    rw [hs, Category.assoc, ProSeq.homConstEquiv_comp, homConstEquiv_idealShriekIso_hom_comp]
    exact ProSeq.constHom_app_seqStage y _
  have h2 : degreeZeroCompactSupportMap p U K hK s =
      ((DerivedCategory.homologyFunctor X.Modules 0).map
        (DerivedCategory.Q.map ((idealPowerComplexSystem (complementIdeal U) F).inclusion 0) ≫
          e.hom)).app ⊤ (idealSection U F b hF p y 0) := by
    unfold degreeZeroCompactSupportMap
    rw [h1]
    exact derivedPushforwardHomEquiv_comp p _ _ _ _
  rw [h2]
  have h4 : ((DerivedCategory.homologyFunctor X.Modules 0).map e.inv).app ⊤
      (((DerivedCategory.homologyFunctor X.Modules 0).map
        (DerivedCategory.Q.map ((idealPowerComplexSystem (complementIdeal U) F).inclusion 0) ≫
          e.hom)).app ⊤ (idealSection U F b hF p y 0)) =
      ((DerivedCategory.homologyFunctor X.Modules 0).map
        (DerivedCategory.Q.map ((idealPowerComplexSystem (complementIdeal U) F).inclusion 0))).app
          ⊤ (idealSection U F b hF p y 0) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← Functor.map_comp,
      Category.assoc, e.hom_inv_id, Category.comp_id]
  change (DerivedCategory.homologyZeroToX F).app ⊤ _ = _
  rw [h4, homologyZeroToX_app_top_map]
  rfl

omit [IsNoetherian X] [F.IsStrictlyLE b] in
/-- `ρ` is injective. -/
public lemma sectionToTerm_injective :
    Function.Injective (sectionToTerm K F e) :=
  (Stacks.AlgebraicGeometry.RelativeMayerVietoris.injective_app_of_mono _ ⊤).comp
    (Stacks.AlgebraicGeometry.RelativeMayerVietoris.injective_app_of_mono _ ⊤)

include F b hF e in
/-- Injectivity of `H^0_c(U, K|_U) ⟶ Γ(X, H^0(K))`, for a chosen complex `𝓕^•`. -/
public lemma degreeZeroCompactSupportMap_injective_aux (hK : K.obj.IsGE 0) :
    Function.Injective (degreeZeroCompactSupportMap p U K hK) := by
  intro s s' h
  have h0 := congrArg (sectionToTerm K F e) h
  rw [sectionToTerm_degreeZeroCompactSupportMap U K F b hF e p,
    sectionToTerm_degreeZeroCompactSupportMap U K F b hF e p] at h0
  suffices hy : s ≫ (idealShriekIso U K F b hF e p).inv =
      s' ≫ (idealShriekIso U K F b hF e p).inv from
    (cancel_mono (idealShriekIso U K F b hF e p).inv).1 hy
  refine ProSeq.constHom_ext fun n ↦ ?_
  have hn := (idealSectionToTerm_idealSection U F b hF p _ n).trans
    (h0.trans (idealSectionToTerm_idealSection U F b hF p _ n).symm)
  have := isStrictlyGE_idealComplex U F b n
  exact ObjectProperty.hom_ext _ ((derivedPushforwardHomEquiv p _ _).injective
    (idealSectionToTerm_injective U F b n hn))

include b in
omit [IsNoetherian X] in
/-- The image of `ν_n` lies in the sections of `𝓘^n 𝓕^0`. -/
public lemma mem_idealPowerMultiple_idealSectionToTerm (n : ℕ)
    (τ : Γ((DerivedCategory.homologyFunctor X.Modules 0).obj
      (DerivedCategory.Q.obj (idealComplex U F n)), ⊤)) :
    idealSectionToTerm U F b n τ ∈ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
      (complementIdeal U) n (F.X 0)).toSubmodule.obj (op ⊤) := by
  rw [← range_submodule_ι_app]
  exact ⟨_, rfl⟩

include b in
omit [IsNoetherian X] in
/-- A cycle of `𝓕^0` lying in `Γ(𝓘^n 𝓕^0)` is `ν_n` of a degree-zero class of `𝓘^n 𝓕^•`. -/
public lemma exists_idealSectionToTerm_eq (n : ℕ) (v : Γ(F.X 0, ⊤))
    (hd : (F.d 0 1).app ⊤ v = 0)
    (hv : v ∈ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
      (complementIdeal U) n (F.X 0)).toSubmodule.obj (op ⊤)) :
    ∃ τ, idealSectionToTerm U F b n τ = v := by
  have := isStrictlyGE_idealComplex U F b n
  rw [← range_submodule_ι_app] at hv
  obtain ⟨u₀, hu⟩ := hv
  let u : Γ((idealComplex U F n).X 0, ⊤) := u₀
  have hmono : Mono (((idealPowerComplexSystem (complementIdeal U) F).inclusion n).f 1) :=
    inferInstanceAs (Mono (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
      (complementIdeal U) n (F.X 1)).ι)
  have hdu : ((idealComplex U F n).d 0 1).app ⊤ u = 0 := by
    apply Stacks.AlgebraicGeometry.RelativeMayerVietoris.injective_app_of_mono
      (((idealPowerComplexSystem (complementIdeal U) F).inclusion n).f 1) ⊤
    have hc := congrArg (fun φ ↦ Scheme.Modules.Hom.app φ ⊤ u)
      (((idealPowerComplexSystem (complementIdeal U) F).inclusion n).comm 0 1)
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hc
    rw [map_zero, ← hc]
    change (F.d 0 1).app ⊤ ((((idealPowerComplexSystem (complementIdeal U) F).inclusion
      n).f 0).app ⊤ u) = 0
    rwa [show (((idealPowerComplexSystem (complementIdeal U) F).inclusion n).f 0).app ⊤ u =
      v from hu]
  obtain ⟨τ, hτ⟩ := (mem_range_homologyZeroToX_app_top_iff _ u).2 hdu
  refine ⟨τ, ?_⟩
  change (((idealPowerComplexSystem (complementIdeal U) F).inclusion n).f 0).app ⊤
    ((DerivedCategory.homologyZeroToX (idealComplex U F n)).app ⊤ τ) = _
  rwa [hτ]

include b in
/-- A family of degree-zero classes of the `𝓘^n 𝓕^•` with a common image in `Γ(𝓕^0)` is the
family of components of a morphism into `(Rp_*(𝓘^n 𝓕^•))`. -/
public lemma exists_idealSection_eq_of_compatible
    (τ : ∀ n : ℕ, Γ((DerivedCategory.homologyFunctor X.Modules 0).obj
      (DerivedCategory.Q.obj (idealComplex U F n)), ⊤))
    (v : Γ(F.X 0, ⊤)) (hτ : ∀ n, idealSectionToTerm U F b n (τ n) = v) :
    ∃ y, idealSection U F b hF p y 0 = τ 0 := by
  have hGE : ∀ n, (DerivedCategory.Q.obj (idealComplex U F n)).IsGE 0 := fun n ↦
    have := isStrictlyGE_idealComplex U F b n
    inferInstance
  let x : ∀ n : ℕ, structureSheafBoundedCoherent Y ⟶
      ((idealSystem U F b hF).system ⋙ properPushforwardBoundedCoherent p).obj (op n) :=
    fun n ↦ ObjectProperty.homMk
      ((derivedPushforwardHomEquiv p (DerivedCategory.Q.obj (idealComplex U F n)) (hGE n)).symm
        (τ n))
  have hsec : ∀ n, derivedPushforwardHomEquiv p (DerivedCategory.Q.obj (idealComplex U F n))
      (hGE n) (x n).hom = τ n := fun n ↦ Equiv.apply_symm_apply _ _
  have hx : ∀ n : ℕ, x (n + 1) ≫
      ((idealSystem U F b hF).system ⋙ properPushforwardBoundedCoherent p).map
        (homOfLE (Nat.le_succ n)).op = x n := by
    intro n
    apply ObjectProperty.hom_ext
    apply (derivedPushforwardHomEquiv p (DerivedCategory.Q.obj (idealComplex U F n))
      (hGE n)).injective
    rw [ObjectProperty.FullSubcategory.comp_hom, idealSystem_comp_map_succ_hom]
    refine (derivedPushforwardHomEquiv_comp p (hGE (n + 1)) (hGE n) _ _).trans ?_
    rw [hsec, hsec]
    apply idealSectionToTerm_injective U F b n
    rw [idealSectionToTerm_transition, hτ, hτ]
  refine ⟨ProSeq.constHomMk x hx, ?_⟩
  change derivedPushforwardHomEquiv p _ _
    (ProSeq.constHomComponent (ProSeq.constHomMk x hx) 0).hom = _
  rw [ProSeq.constHomComponent_constHomMk]
  exact hsec 0

include b hF in
/-- **The image of `H^0_c(U, K|_U)`**: a section of `H^0(K)` is in the image if and only if its
image in `Γ(𝓕^0)` lies in every `Γ(𝓘^n 𝓕^0)`. -/
public lemma range_degreeZeroCompactSupportMap_aux (hK : K.obj.IsGE 0)
    (σ : Γ((DerivedCategory.homologyFunctor X.Modules 0).obj K.obj, ⊤)) :
    σ ∈ Set.range (degreeZeroCompactSupportMap p U K hK) ↔
      ∀ n : ℕ, sectionToTerm K F e σ ∈ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
        (complementIdeal U) n (F.X 0)).toSubmodule.obj (op ⊤) := by
  refine ⟨?_, fun hσ ↦ ?_⟩
  · rintro ⟨s, rfl⟩ n
    rw [sectionToTerm_degreeZeroCompactSupportMap U K F b hF e p,
      ← idealSectionToTerm_idealSection U F b hF p _ n]
    exact mem_idealPowerMultiple_idealSectionToTerm U F b n _
  · have hd : (F.d 0 1).app ⊤ (sectionToTerm K F e σ) = 0 :=
      (mem_range_homologyZeroToX_app_top_iff F _).1 ⟨_, rfl⟩
    choose τ hτ using fun n ↦ exists_idealSectionToTerm_eq U F b n _ hd (hσ n)
    obtain ⟨y, hy⟩ := exists_idealSection_eq_of_compatible U F b hF p τ _ hτ
    refine ⟨y ≫ (idealShriekIso U K F b hF e p).hom, sectionToTerm_injective K F e ?_⟩
    rw [sectionToTerm_degreeZeroCompactSupportMap U K F b hF e p, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, hy, hτ 0]

end Setup

end DegreeZeroCompactSupport

end AlgebraicGeometry

namespace AlgebraicGeometry

open DegreeZeroCompactSupport

attribute [local instance 10000] HasDerivedCategory.standard

/-- A monomorphism of modules detects the vanishing of a global section on an open. -/
public lemma presheaf_map_eq_zero_iff_of_mono {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    [Mono φ]
    {V : X.Opens} (σ : Γ(M, ⊤)) :
    M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ = 0 ↔
      N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (φ.app ⊤ σ) = 0 := by
  have hnat : φ.app V (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ) =
      N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (φ.app ⊤ σ) :=
    NatTrans.naturality_apply φ.mapPresheaf (homOfLE (le_top : V ≤ ⊤)).op σ
  rw [← hnat]
  exact ⟨fun h ↦ by rw [h, map_zero], fun h ↦
    Stacks.AlgebraicGeometry.RelativeMayerVietoris.injective_app_of_mono φ V (by rw [h, map_zero])⟩

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Y) [IsProper p]

/-- The map `H^0_c(U, K|_U) ⟶ Γ(X, H^0(K))` is injective. -/
public theorem degreeZeroCompactSupportMap_injective (U : X.Opens) (K : BoundedCoherentDerived X)
    (hK : K.obj.IsGE 0) : Function.Injective (degreeZeroCompactSupportMap p U K hK) := by
  obtain ⟨F, b, hF, hGE, hLE, ⟨e⟩⟩ := exists_isCoherent_complex_isStrictlyGE_zero_iso K hK
  exact degreeZeroCompactSupportMap_injective_aux U K F b hF e p hK

/-- The image of `H^0_c(U, K|_U) ⟶ Γ(X, H^0(K))` consists of the global sections vanishing on a
neighbourhood of `X ∖ U`. -/
public theorem range_degreeZeroCompactSupportMap (U : X.Opens) (K : BoundedCoherentDerived X)
    (hK : K.obj.IsGE 0) :
    Set.range (degreeZeroCompactSupportMap p U K hK) =
      {σ | ∃ V : X.Opens, (U : Set X)ᶜ ⊆ V ∧
        ((DerivedCategory.homologyFunctor X.Modules 0).obj K.obj).presheaf.map
          (homOfLE (le_top : V ≤ ⊤)).op σ = 0} := by
  obtain ⟨F, b, hF, hGE, hLE, ⟨e⟩⟩ := exists_isCoherent_complex_isStrictlyGE_zero_iso K hK
  have := hF 0
  ext σ
  rw [range_degreeZeroCompactSupportMap_aux U K F b hF e p hK,
    forall_mem_idealPowerMultiple_top_iff, DegreeZeroCompactSupport.coe_support_complementIdeal,
    Scheme.Opens.range_ι, Set.mem_ofPred_eq]
  have hσ : sectionToTerm K F e σ = ((DerivedCategory.homologyFunctor X.Modules 0).map e.inv ≫
      DerivedCategory.homologyZeroToX F).app ⊤ σ := by
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    rfl
  rw [hσ]
  exact exists_congr fun V ↦ and_congr_right fun _ ↦
    (presheaf_map_eq_zero_iff_of_mono _ σ).symm

/-- Let `X` be a proper scheme over a field `k`. Let
`K ∈ D^b_{Coh}(𝒪_X)` with `H^i(K) = 0` for `i < 0`, and set `𝓕 = H^0(K)`. Let `Z ⊆ X` be closed
with complement `U = X ∖ Z`. Then

`H^0_c(U, K|_U) ⊂ H^0(X, 𝓕)`

is given by those global sections of `𝓕` which vanish in an open neighbourhood of `Z`.

Here `H^0_c(U, K|_U)` is `AlgebraicGeometry.degreeZeroCompactSupport`: the morphisms
`𝒪_{Spec k} ⟶ Rg_!(K|_U)` in `Pro-D^b_{Coh}(𝒪_{Spec k})`, for `g : U ⟶ Spec k` and the functor
`Rg_! = Rp_* ∘ Rj_!` of [Stacks, Section 0G4Z] attached to the compactification `j : U ⟶ X`
(which is `lim_n H^0(X, K_n)` for a Deligne system `(K_n)` with value `K|_U`,
[Stacks, Section 0G59]); the map `H^0_c(U, K|_U) ⟶ H^0(X, 𝓕)` is
`AlgebraicGeometry.degreeZeroCompactSupportMap`, induced by the map `Rg_!(K|_U) ⟶ Rp_* K` of
[Stacks, Tag 0G56] for `X` its own compactification and `H^0(X, K) = Γ(X, H^0(K))`. The statement
is that this map is injective with exactly that image. -/
@[stacks 0G5C]
public theorem degreeZeroCompactSupportMap_injective_and_range {k : Type u} [Field k]
    {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (K : BoundedCoherentDerived X)
    (hK : ∀ i < 0, IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K.obj))
    (Z : TopologicalSpace.Closeds X) :
    letI : IsNoetherian X := @IsNoetherian.mk X (LocallyOfFiniteType.isLocallyNoetherian p)
      (QuasiCompact.compactSpace_of_compactSpace p)
    Function.Injective (degreeZeroCompactSupportMap p Z.compl K
        ((DerivedCategory.isGE_iff K.obj 0).2 hK)) ∧
      Set.range (degreeZeroCompactSupportMap p Z.compl K
        ((DerivedCategory.isGE_iff K.obj 0).2 hK)) =
        {σ | ∃ V : X.Opens, (Z : Set X) ⊆ V ∧
          ((DerivedCategory.homologyFunctor X.Modules 0).obj K.obj).presheaf.map
            (homOfLE (le_top : V ≤ ⊤)).op σ = 0} := by
  let : IsNoetherian X := @IsNoetherian.mk X (LocallyOfFiniteType.isLocallyNoetherian p)
    (QuasiCompact.compactSpace_of_compactSpace p)
  refine ⟨degreeZeroCompactSupportMap_injective p _ K _, ?_⟩
  rw [range_degreeZeroCompactSupportMap]
  simp only [TopologicalSpace.Closeds.coe_compl, compl_compl]

end AlgebraicGeometry

end
