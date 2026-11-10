module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineOverBaseDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineViewOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartGlobalFunctionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitEqualizerPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSectionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationGlobalFunctionsDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsChartSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsTerminalIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.RingTheory.Etale.DirectedColimitEtaleStage
public import StacksFrontier.RingTheory.MvPolynomial.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DescentSituationCategory

/-!
# Global functions and spectra of affine algebraic spaces

Preliminaries for Stacks 07SQ: restriction of global functions to an affine surjective étale
chart, the `u`-models of the rings of global functions of a descent situation, the
identification of an affine algebraic space with the spectrum of a model of its global
functions (Stacks 05Z1), polynomial presentations at a later stage of a directed system of
rings, morphisms out of an algebraic space determined on a surjective étale chart, and
invertibility of a base change to the limit from two Cartesian squares.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine surjective étale chart of an affine algebraic space is étale over the global
functions, with surjective spectrum.** Over a terminal base scheme, let `X` be an affine
algebraic space, let `A` be a `u`-model of its ring of global functions and let `V` be a
surjective étale scheme chart of `X` whose total scheme is affine. Then the homomorphism
`A ⟶ Γ(V, 𝒪_V)` given by restriction of global functions to `V` is étale and its spectrum is
surjective. -/
theorem etale_globalFunctionsChartRestriction (hterminal : IsTerminal S)
    (X : AlgebraicSpaces B S hS) (M : GlobalFunctionsModel B S hS X.obj)
    (hX : IsAffineSpace B S hS X.obj) (V : SmallEtale B S hS X.obj)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.obj).obj V)))
    (hVsurj : IsSurjective B S hS V.obj.hom) :
    RingHom.Etale ((globalFunctionsChartRestriction B S hS X V).comp M.equiv.toRingHom) ∧
      Function.Surjective (PrimeSpectrum.comap
        ((globalFunctionsChartRestriction B S hS X V).comp M.equiv.toRingHom)) := by
  have := hVaff
  set ZA := specGlobalFunctions B S hS X M hterminal with hZA
  set tsg := toSpecGlobalFunctions B S hS X M hterminal with htsgdef
  have htsg : IsIso tsg := isIso_toSpecGlobalFunctions B S hS hterminal X M hX
  have htsgh : IsIso tsg.hom := inferInstance
  set gmap : (SmallEtale.toOver B S hS X.obj).obj V ⟶ ZA :=
    yoneda.preimage (V.obj.hom ≫ tsg.hom) with hgmapdef
  have hgmapY : yoneda.map gmap = V.obj.hom ≫ tsg.hom := yoneda.map_preimage _
  set rinf := (globalFunctionsChartRestriction B S hS X V).comp M.equiv.toRingHom with hrinf
  have hdelta : (BigFppfOver.toScheme B S hS).map gmap
      = affineChartMap B S hS X ZA hterminal
          (specGlobalFunctionsGamma B S hS X M hterminal) V := by
    rw [← pullbackToGlobalFunctions_toSpecGlobalFunctions B S hS X M hterminal,
      affineChartMap_eq_pullback B S hS X ZA hterminal tsg V]
  have hdeltaTop : ((BigFppfOver.toScheme B S hS).map gmap).appTop
      = CommRingCat.ofHom (rinf.comp (Scheme.ΓSpecIso M.ring).hom.hom) := by
    rw [hdelta]
    refine (affineChartMap_appTop B S hS X ZA hterminal _ V).trans ?_
    refine congrArg CommRingCat.ofHom ?_
    rw [hrinf]
    rfl
  have hEt0 : IsEtale B S hS (yoneda.map gmap) := by
    rw [hgmapY]
    exact isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).2 V.property)
      (isEtale_of_isIso B S hS tsg.hom)
  have hEt : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map gmap) :=
    (presheaf_yoneda_map_etale_iff B S hS gmap).1
      ((isEtale_iff_presheaf_of_yoneda B S hS _).1 hEt0)
  have hSu0 : IsSurjective B S hS (yoneda.map gmap) := by
    rw [hgmapY]
    exact isSurjective_comp B S hS hVsurj (isSurjective_of_isIso B S hS tsg.hom)
  have hSu : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map gmap) :=
    surjective_of_surjective_pointsMap_yoneda_map B S hS gmap hSu0
  have hbetaid : (Scheme.ΓSpecIso M.ring).hom.hom.comp (Scheme.ΓSpecIso M.ring).inv.hom
      = RingHom.id M.ring := by
    have h := (Scheme.ΓSpecIso M.ring).inv_hom_id
    calc (Scheme.ΓSpecIso M.ring).hom.hom.comp (Scheme.ΓSpecIso M.ring).inv.hom
        = ((Scheme.ΓSpecIso M.ring).inv ≫ (Scheme.ΓSpecIso M.ring).hom).hom := rfl
      _ = (𝟙 M.ring : M.ring ⟶ M.ring).hom := by rw [h]
      _ = RingHom.id M.ring := rfl
  refine ⟨?_, ?_⟩
  · have h0 : RingHom.Etale (((BigFppfOver.toScheme B S hS).map gmap).appTop).hom :=
      HasRingHomProperty.appTop (@AlgebraicGeometry.Etale.{u}) _ hEt
    rw [hdeltaTop] at h0
    have h0' : RingHom.Etale (rinf.comp (Scheme.ΓSpecIso M.ring).hom.hom) := h0
    have h2 : RingHom.Etale ((Scheme.ΓSpecIso M.ring).inv.hom) :=
      RingHom.Etale.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso M.ring).inv)
    have h3 : RingHom.Etale ((rinf.comp (Scheme.ΓSpecIso M.ring).hom.hom).comp
        (Scheme.ΓSpecIso M.ring).inv.hom) :=
      RingHom.Etale.stableUnderComposition _ _ h2 h0'
    have h4 : (rinf.comp (Scheme.ΓSpecIso M.ring).hom.hom).comp
          (Scheme.ΓSpecIso M.ring).inv.hom
        = rinf.comp ((Scheme.ΓSpecIso M.ring).hom.hom.comp
            (Scheme.ΓSpecIso M.ring).inv.hom) := rfl
    rw [h4, hbetaid] at h3
    exact h3
  · have hinj : Function.Injective
        (PrimeSpectrum.comap (Scheme.ΓSpecIso M.ring).hom.hom) := by
      have : IsIso (Spec.map (Scheme.ΓSpecIso M.ring).hom) := inferInstance
      exact (Spec.map (Scheme.ΓSpecIso M.ring).hom).homeomorph.injective
    have := hSu
    have hnat := Scheme.isoSpec_hom_naturality ((BigFppfOver.toScheme B S hS).map gmap)
    have hleft : AlgebraicGeometry.Surjective
        ((BigFppfOver.toScheme B S hS).map gmap ≫
          (Scheme.isoSpec ((BigFppfOver.toScheme B S hS).obj ZA)).hom) := inferInstance
    rw [← hnat] at hleft
    have := hleft
    have hs2 : AlgebraicGeometry.Surjective
        (Spec.map ((BigFppfOver.toScheme B S hS).map gmap).appTop) :=
      AlgebraicGeometry.Surjective.of_comp
        ((Scheme.isoSpec ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.obj).obj V))).hom) _
    rw [hdeltaTop] at hs2
    have hs3 : Function.Surjective
        (PrimeSpectrum.comap (rinf.comp (Scheme.ΓSpecIso M.ring).hom.hom)) := hs2.surj
    intro q
    obtain ⟨r, hr⟩ := hs3 (PrimeSpectrum.comap (Scheme.ΓSpecIso M.ring).hom.hom q)
    exact ⟨r, hinj hr⟩


/-! ### The `u`-models of the rings of global functions of a descent situation -/

section ModelSystem

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- The identification of the `u`-model of the ring of global functions of a stage with that
ring, read on `AlgebraicGeometry.Space.globalFunctions'`.

This is `AlgebraicGeometry.Space.globalFunctionsModelEquiv`, whose target is the same ring read
as `AlgebraicGeometry.Space.globalFunctions`. The two spellings are equal, by
`AlgebraicGeometry.Space.globalFunctions_eq_globalFunctions'`, but not *reducibly* so, and
`AlgebraicGeometry.Space.globalFunctionsMap` — the transition map of the system below — is
stated on the primed one. -/
def stageModelEquiv (i : I) :
    globalFunctionsModel B S hS (D.stage i) ≃+* globalFunctions' B S hS (D.stage i).obj :=
  globalFunctionsModelEquiv B S hS (D.stage i)

/-- The same identification at the limit. -/
def limitModelEquiv :
    globalFunctionsModel B S hS D.limitSpace ≃+* globalFunctions' B S hS D.limitSpace.obj :=
  globalFunctionsModelEquiv B S hS D.limitSpace

/-- **The `u`-models of the rings of global functions of the stages form a directed system.**
The transition map is the one of
`AlgebraicGeometry.Space.DescentSituation.transition` conjugated by the models'
identifications. -/
theorem directedSystem_globalFunctionsModel :
    DirectedSystem (fun i : I => globalFunctionsModel B S hS (D.stage i))
      (fun i j (h : i ≤ j) x => (stageModelEquiv D j).symm
        (globalFunctionsMap B S hS (D.transition h) (stageModelEquiv D i x))) := by
  constructor
  · intro i x
    have hid : D.transition (le_refl i) = 𝟙 (D.stage i) := by
      apply CategoryTheory.ObjectProperty.hom_ext
      change D.system.map (CategoryTheory.homOfLE (le_refl i)).op = _
      rw [Subsingleton.elim (CategoryTheory.homOfLE (le_refl i)).op (𝟙 (op i)),
        D.system.map_id]
      rfl
    change (stageModelEquiv D i).symm
      (globalFunctionsMap B S hS (D.transition (le_refl i)) _) = x
    rw [hid, globalFunctionsMap_id]
    exact (stageModelEquiv D i).symm_apply_apply x
  · intro k j i hij hjk x
    simp only [RingEquiv.apply_symm_apply]
    rw [← RingHom.comp_apply, ← globalFunctionsMap_comp, D.transition_comp hij hjk]

/-- **Stacks 07SI for the structure sheaf, read on `u`-models.** The ring of global regular
functions of the limit of a descent situation is the filtered colimit of those of the stages,
and so is its `u`-model the filtered colimit of theirs.

`AlgebraicGeometry.Space.globalFunctions` lives in `Type (u + 1)`, while the proof of Stacks
07SQ must take `Spec` of the colimit ring and of the stage rings and so needs them in the
universe of the site. `AlgebraicGeometry.Space.globalFunctionsModel` is the `u`-model, available
because the ring is `u`-small, and this is the colimit assertion transported to it: the three
clauses of `Stacks.IsStagesColimit` are the hypothesis package of the commutative-algebra core
`MvPolynomial.exists_ge_etale_surjective_quotient_of_directed`, through
`Stacks.IsStagesColimit.hφ`, `.hsurj` and `.hzero`.

The size hypothesis is the one of
`AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit`, that is, the bound of
Stacks 07SF; it is consumed there and nowhere else here. -/
theorem isStagesColimit_globalFunctionsModel (hI : #I < B.cutoff.ord.cof) :
    Stacks.IsStagesColimit
      (G := fun i : I => globalFunctionsModel B S hS (D.stage i))
      (T := globalFunctionsModel B S hS D.limitSpace)
      (fun i j (h : i ≤ j) x => (stageModelEquiv D j).symm
        (globalFunctionsMap B S hS (D.transition h) (stageModelEquiv D i x)))
      (fun i x => (limitModelEquiv D).symm
        (globalFunctionsMap B S hS (D.projection i) (stageModelEquiv D i x))) := by
  obtain ⟨hphi, hsurj, hzero⟩ :=
    D.ringPackage_of_isGlobalFunctionsColimit (D.isGlobalFunctionsColimit hI)
  refine ⟨?_, ?_, ?_⟩
  · intro i j h x
    simp only [RingEquiv.apply_symm_apply]
    rw [hphi]
  · intro t
    obtain ⟨i, s, hs⟩ := hsurj (limitModelEquiv D t)
    refine ⟨i, (stageModelEquiv D i).symm s, ?_⟩
    simp only [RingEquiv.apply_symm_apply]
    rw [hs, RingEquiv.symm_apply_apply]
  · intro i s s' hss
    have h0 : globalFunctionsMap B S hS (D.projection i) (stageModelEquiv D i s)
        = globalFunctionsMap B S hS (D.projection i) (stageModelEquiv D i s') :=
      (limitModelEquiv D).symm.injective hss
    obtain ⟨j, hij, hj⟩ :=
      Stacks.IsStagesColimit.exists_trans_eq
        (D.isGlobalFunctionsColimit hI) i _ _ h0
    exact ⟨j, hij, congrArg (stageModelEquiv D j).symm hj⟩

end ModelSystem

/-! ### Chart restriction against pullback of global functions -/

section ChartRestrictionCoherence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Chart restriction intertwines pullback of global functions with restriction along a
morphism of charts.** Let `f : V ⟶ U` be a morphism of algebraic spaces, `W` an étale chart of
`V`, `W'` an étale chart of `U`, and `c` a morphism of the site making the square of the two
charts over `f` commute. Then restricting to `W` the pullback along `f` of a global function on
`U` is restricting that function to `W'` and then along `c`.

This is `AlgebraicGeometry.Space.globalFunctionsMap_val_of_chartHom` read on
`AlgebraicGeometry.Space.globalFunctionsChartRestriction`, the morphism of charts being
assembled from `c`. It is the coherence the descent of the coordinates of a presentation
consumes, at the Cartesian square of a chart system for `f` a projection of the limit and at the
naturality square for `f` a transition morphism. -/
theorem globalFunctionsChartRestriction_globalFunctionsMap
    {U V : AlgebraicSpaces B S hS} (f : V ⟶ U) (W : SmallEtale B S hS V.obj)
    (W' : SmallEtale B S hS U.obj) (c : W.obj.left ⟶ W'.obj.left)
    (hc : yoneda.map c ≫ W'.obj.hom = W.obj.hom ≫ f.hom)
    (s : globalFunctions B S hS U.obj) :
    globalFunctionsChartRestriction B S hS V W (globalFunctionsMap B S hS f s)
      = ((BigFppfOver.toScheme B S hS).map c).appTop.hom
          (globalFunctionsChartRestriction B S hS U W' s) :=
  globalFunctionsMap_val_of_chartHom B S hS f s W W' (CostructuredArrow.homMk c hc)

end ChartRestrictionCoherence

/-! ### The identification of an affine algebraic space with the spectrum of its functions -/

section SpecIdentification

/-- **The action on global functions of the morphism to a spectrum attached to a homomorphism
into them.** The morphism `Y ⟶ Spec A` of `AlgebraicGeometry.Space.specMapOfGlobalHom` pulls a
regular function on `Spec A` back by the `Γ`–`Spec` unit followed by the given homomorphism. -/
theorem specMapOfGlobalHom_appTop {Y : Scheme.{u}} (A : Type u) [CommRing A]
    (ψ : A →+* Γ(Y, ⊤)) :
    (specMapOfGlobalHom A ψ).appTop
      = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ := by
  have h1 : (specMapOfGlobalHom A ψ).appTop
      = (Spec.map (CommRingCat.ofHom ψ)).appTop ≫ (Scheme.ΓSpecIso Γ(Y, ⊤)).hom := by
    rw [specMapOfGlobalHom, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  exact h1.trans (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))

/-- **The morphism to a spectrum attached to a homomorphism into the global functions, composed
with the spectrum of a homomorphism of the coefficients.** -/
theorem specMapOfGlobalHom_comp_Spec_map {Y : Scheme.{u}} (A A' : Type u) [CommRing A]
    [CommRing A'] (ψ : A →+* Γ(Y, ⊤)) (φ : A' →+* A) :
    specMapOfGlobalHom A ψ ≫ Spec.map (CommRingCat.ofHom φ)
      = specMapOfGlobalHom A' (ψ.comp φ) := by
  rw [specMapOfGlobalHom, specMapOfGlobalHom, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine algebraic space over a terminal base is the functor of points of the spectrum of
a model of its global functions, by the canonical morphism of Stacks 05Z1.** For an affine
algebraic space `X` over a terminal base scheme and a `u`-ring `A` identified with the global
functions of `X` and whose spectrum lies in the site, there is an *isomorphism*
`X ⟶ Spec A` of presheaves whose restriction to every étale scheme chart `V` is the morphism of
schemes the `Γ`–`Spec` adjunction attaches to restriction of global functions to `V`.

The morphism is `AlgebraicGeometry.Space.toSpecGlobalFunctions` — Stacks 05Z1 — followed by the
comparison `AlgebraicGeometry.Space.schemePointsUnit` of the two functors of points of its
target, both of which are isomorphisms here: the first by
`AlgebraicGeometry.Space.isIso_toSpecGlobalFunctions`, the second because the base is terminal.
The chart formula is the one `AlgebraicGeometry.Space.commSq_chart_specOfGlobalFunctions` —
Stacks 084U — asks of its left vertical, so this is what makes that square's left-hand edge
invertible over the limit in the proof of Stacks 07SQ. -/
theorem exists_isIso_specMapOfGlobalHom_of_isAffineSpace (hterminal : IsTerminal S)
    (X : AlgebraicSpaces B S hS) (A : Type u) [CommRing A]
    (hA : B.Contains (Spec (CommRingCat.of A)))
    (e : A ≃+* globalFunctions B S hS X.obj) (hX : IsAffineSpace B S hS X.obj) :
    ∃ p : X.obj ⟶ schemePoints B S hS (Spec (CommRingCat.of A)), IsIso p ∧
      ∀ V : SmallEtale B S hS X.obj, yonedaEquiv (V.obj.hom ≫ p)
        = specMapOfGlobalHom A
            ((globalFunctionsChartRestriction B S hS X V).comp e.toRingHom) := by
  set M : GlobalFunctionsModel B S hS X.obj := ⟨CommRingCat.of A, hA, e⟩ with hM
  refine ⟨(affineSpaceIsoSchemePoints B S hS hterminal X M hX).hom, inferInstance, fun V => ?_⟩
  change yonedaEquiv (V.obj.hom ≫ (toSpecGlobalFunctions B S hS X M hterminal).hom ≫
      schemePointsUnit B S hS (specGlobalFunctions B S hS X M hterminal))
    = specMapOfGlobalHom A ((globalFunctionsChartRestriction B S hS X V).comp e.toRingHom)
  set gmap := yoneda.preimage (V.obj.hom ≫ (toSpecGlobalFunctions B S hS X M hterminal).hom)
    with hgmapdef
  have hgmapY : yoneda.map gmap
      = V.obj.hom ≫ (toSpecGlobalFunctions B S hS X M hterminal).hom := yoneda.map_preimage _
  have hstep : V.obj.hom ≫ (toSpecGlobalFunctions B S hS X M hterminal).hom ≫
        schemePointsUnit B S hS (specGlobalFunctions B S hS X M hterminal)
      = yoneda.map gmap ≫
        schemePointsUnit B S hS (specGlobalFunctions B S hS X M hterminal) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫
        schemePointsUnit B S hS (specGlobalFunctions B S hS X M hterminal)) hgmapY.symm)
  have hu : yonedaEquiv (yoneda.map gmap ≫
        schemePointsUnit B S hS (specGlobalFunctions B S hS X M hterminal))
      = (BigFppfOver.toScheme B S hS).map gmap := by
    rw [← commSq_schemePointsUnit B S hS gmap, yonedaEquiv_comp_schemePointsMap,
      yonedaEquiv_schemePointsUnit]
    exact Category.id_comp _
  refine (congrArg yonedaEquiv hstep).trans (hu.trans ?_)
  refine ext_of_isAffine ?_
  refine Eq.trans ?_ (specMapOfGlobalHom_appTop A
    ((globalFunctionsChartRestriction B S hS X V).comp e.toRingHom)).symm
  refine CommRingCat.hom_ext (RingHom.ext fun t => ?_)
  exact (toSpecGlobalFunctions_chart B S hS X M hterminal V t).symm

/-- **The morphism to the functor of points of a spectrum attached to a bijective homomorphism
into the global functions of an affine object of the site is an isomorphism.** Over a terminal
base the two functors of points of an object of the site agree, and the morphism of schemes the
`Γ`–`Spec` adjunction attaches to a bijective homomorphism out of a ring is an isomorphism when
the source scheme is affine.

This is what makes the upper edge of the square of Stacks 084U invertible over the limit in the
proof of Stacks 07SQ: there the homomorphism is
`AlgebraicGeometry.Space.coordinateHom`, bijective by
`AlgebraicGeometry.Space.bijective_coordinateHom_of_algEquiv`. -/
theorem isIso_yonedaEquiv_symm_specMapOfGlobalHom (hterminal : IsTerminal S)
    (W : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (A : Type u) [CommRing A]
    (χ : A →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) (hχ : Function.Bijective χ) :
    IsIso (yonedaEquiv.symm (specMapOfGlobalHom A χ) :
      yoneda.obj W ⟶ schemePoints B S hS (Spec (CommRingCat.of A))) := by
  have : IsIso (CommRingCat.ofHom χ) :=
    (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom χ)).mpr hχ
  have : IsIso (specMapOfGlobalHom A χ) := by
    rw [specMapOfGlobalHom]
    infer_instance
  have : IsIso (schemePointsUnit B S hS W) := isIso_schemePointsUnit B S hS hterminal W
  rw [← schemePointsUnit_comp_schemePointsMap B S hS W
    (yonedaEquiv.symm (specMapOfGlobalHom A χ)), Equiv.apply_symm_apply]
  infer_instance

end SpecIdentification

/-! ### A polynomial presentation at a later stage of a directed system of rings -/

section PresentationStage

/-- The relations of a polynomial presentation lie in the preimage, along the base change of
coefficients, of the relations of the base-changed presentation. This is the hypothesis of
`AlgebraicGeometry.Space.isPushout_presentationAlgebra_baseChange`. -/
theorem span_range_le_comap_map_span_range {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {n : ℕ} (g : Fin n → MvPolynomial (Fin n) R) :
    Ideal.span (Set.range g) ≤
      Ideal.comap (MvPolynomial.map φ)
        (Ideal.span (Set.range fun k => MvPolynomial.map φ (g k))) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact Ideal.mem_comap.mpr (Ideal.subset_span (Set.mem_range_self (f := fun k =>
    MvPolynomial.map φ (g k)) k))

/-- **Surjectivity on spectra of a polynomial presentation is stable under base change of the
coefficients.** A presentation and its base change form a pushout of commutative rings,
`AlgebraicGeometry.Space.isPushout_presentationAlgebra_baseChange`, so their spectra form a
Cartesian square of schemes, and surjectivity is stable under base change. -/
theorem surjective_comap_presentationStructureHom_map {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {n : ℕ} (g : Fin n → MvPolynomial (Fin n) R)
    (hsurj : Function.Surjective
      (PrimeSpectrum.comap (presentationStructureHom g))) :
    Function.Surjective (PrimeSpectrum.comap
      (presentationStructureHom fun k => MvPolynomial.map φ (g k))) := by
  have hpb := ((isPushout_presentationAlgebra_baseChange φ g
    (span_range_le_comap_map_span_range φ g)).op).map Scheme.Spec
  have hS : AlgebraicGeometry.Surjective
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g))) := ⟨hsurj⟩
  have hT : AlgebraicGeometry.Surjective
      (Spec.map (CommRingCat.ofHom
        (presentationStructureHom fun k => MvPolynomial.map φ (g k)))) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hpb hS
  exact hT.surj

variable {ι : Type*} [Preorder ι] {G : ι → Type u} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j}

/-- **Étaleness of a polynomial presentation over a stage of a directed system passes to a later
stage.** The family of relations read at the later stage presents the base change of the
presentation along the transition map — `MvPolynomial.nonempty_quotientSpanEquiv_tensor_of_le` —
and étaleness is stable under base change and transported by an algebra isomorphism. -/
theorem etale_presentationAlgebra_map_of_le {i j : ι} (h : i ≤ j) {n : ℕ}
    (q : Fin n → MvPolynomial (Fin n) (G i))
    (hetale : Algebra.Etale (G i)
      (MvPolynomial (Fin n) (G i) ⧸ Ideal.span (Set.range q))) :
    Algebra.Etale (G j) (MvPolynomial (Fin n) (G j) ⧸
      Ideal.span (Set.range fun k => MvPolynomial.map (f i j h) (q k))) := by
  let := (f i j h).toAlgebra
  have := hetale
  obtain ⟨ebc⟩ := MvPolynomial.nonempty_quotientSpanEquiv_tensor_of_le (f := f) h q
  exact Algebra.Etale.of_equiv ebc

end PresentationStage

/-! ### The coordinates of a presentation read through an algebra isomorphism -/

section Coordinates

/-- **The coordinates of a presentation, read through an algebra isomorphism onto the presented
algebra, annihilate the relations.** If `R` is an `A`-algebra isomorphic to
`A[x₁, …, xₙ]/(g₁, …, gₙ)`, then the images in `R` of the classes of the variables satisfy the
relations `g`.

This is how the proof of Stacks 07SQ obtains the global functions `h₁, …, hₙ` on the chart of
the limit that the square of Stacks 084U needs: the commutative-algebra core
`MvPolynomial.exists_ge_etale_surjective_quotient_of_directed` returns exactly such an algebra
isomorphism. -/
theorem eval₂_mk_X_eq_zero {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] {n : ℕ}
    (g : Fin n → MvPolynomial (Fin n) A)
    (e : R ≃ₐ[A] MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range g)) (l : Fin n) :
    MvPolynomial.eval₂ (algebraMap A R)
        (fun k => e.symm (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X k)))
        (g l) = 0 := by
  have hcomp : (MvPolynomial.eval₂Hom (algebraMap A R)
          (fun k => e.symm (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X k))) :
          MvPolynomial (Fin n) A →+* R)
      = (e.symm : (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range g)) →ₐ[A] R).toRingHom.comp
          (Ideal.Quotient.mk (Ideal.span (Set.range g))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · have h1 : (MvPolynomial.eval₂Hom (algebraMap A R)
            (fun k => e.symm (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X k))) :
            MvPolynomial (Fin n) A →+* R) (MvPolynomial.C a) = algebraMap A R a := by simp
      rw [h1, RingHom.comp_apply]
      exact (AlgEquiv.commutes e.symm a).symm
    · simp
  refine (RingHom.congr_fun hcomp (g l)).trans ?_
  change e.symm (Ideal.Quotient.mk (Ideal.span (Set.range g)) (g l)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self (f := g) l)),
    map_zero]

end Coordinates

/-- **The homomorphism out of a presentation determined by coordinates coming from an algebra
isomorphism onto the presented algebra is bijective.** The homomorphism and the inverse of the
isomorphism agree on the constants and on the classes of the variables, and a homomorphism out of
a quotient of a polynomial ring is determined there.

The family of relations is allowed to differ from the one the isomorphism presents by an
equation, because the proof of Stacks 07SQ meets it in two spellings: as the base change to the
limit of the family lifted to a stage, and as the family the commutative-algebra core
returns. -/
theorem bijective_coordinateHom_of_algEquiv {A R : Type u} [CommRing A] [CommRing R]
    [Algebra A R] {n : ℕ} {g g₀ : Fin n → MvPolynomial (Fin n) A}
    (e : R ≃ₐ[A] MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range g₀)) (hg : g₀ = g)
    (h : Fin n → R)
    (hh : ∀ k, h k = e.symm (Ideal.Quotient.mk (Ideal.span (Set.range g₀)) (MvPolynomial.X k)))
    (hrel : ∀ l, MvPolynomial.eval₂ (algebraMap A R) h (g l) = 0) :
    Function.Bijective (coordinateHom g (algebraMap A R) h hrel) := by
  subst hg
  have hco : coordinateHom g₀ (algebraMap A R) h hrel
      = (e.symm : (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range g₀)) →ₐ[A] R).toRingHom := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_))
    · exact (RingHom.congr_fun
        (coordinateHom_comp_presentationStructureHom g₀ (algebraMap A R) h hrel) a).trans
        (AlgEquiv.commutes e.symm a).symm
    · exact (coordinateHom_mk_X g₀ (algebraMap A R) h hrel k).trans (hh k)
  rw [hco]
  exact e.symm.bijective

/-! ### Morphisms out of an algebraic space are determined on a surjective étale chart -/

section HomExt

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism from an algebraic space to a sheaf is determined by its restriction to a
surjective étale chart.** The chart exhibits the algebraic space as the coequalizer of its own
kernel pair in fppf sheaves of sets, which is Stacks 0262, part (3), so restriction along it is
injective on morphisms into a sheaf. -/
theorem hom_ext_of_etale_surjective_chart {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ F)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    {u v : F ⟶ G} (h : a ≫ u = a ≫ v) : u = v := by
  classical
  have hrep : yoneda.relativelyRepresentable a := hF.diagonal_representable.of_diag a
  obtain ⟨hRsh, hUsh, hc⟩ := isCoequalizer_of_surjectiveEtale B S hS a
    (hrep.fst' a) (hrep.snd a) (hrep.isPullback' a) hF hsurj hetale
  have hco := Classical.choice hc
  refine congrArg (fun k : (⟨F, hF.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
    ⟨G, hG⟩ => k.hom) (Cofork.IsColimit.hom_ext hco ?_)
  exact Sheaf.hom_ext h

end HomExt

/-! ### Invertibility of a base change to the limit from two Cartesian squares -/

section MapLimit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_SpecGlobalFunctions :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_SpecGlobalFunctions
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_SpecGlobalFunctions (B := B) (S := S) (hS := hS)).has_limit _

/-- Pasting the pullback square of `f` and `g` onto a pullback square on `g`. -/
private theorem isPullback_pullback_fst_snd_comp {C : Type*} [Category C] {X Y T W Z : C}
    (f : X ⟶ Y) (g : T ⟶ Y) (q : T ⟶ W) (pZ : Y ⟶ Z) (aW : W ⟶ Z) [HasPullback f g]
    (hq : IsPullback g q pZ aW) :
    IsPullback (pullback.fst f g) (pullback.snd f g ≫ q) (f ≫ pZ) aW :=
  ((IsPullback.of_hasPullback f g).flip.paste_horiz hq.flip).flip

/-- **A base change to the limit is an isomorphism when source and target are exhibited as fibre
products over one cospan.** In the situation of Stacks 084W, suppose the target `Y₀` of the
morphism to be descended is the fibre product of the distinguished stage with a presheaf `W` over
a presheaf `Z`, and suppose the source over the limit is the fibre product of the limit with `W`
over `Z` through the composite of the morphism to be descended with the projection to `W`. Then
the base change `f : X ⟶ Y` of `f₀` to the limit is an isomorphism, since both `X` and `Y` are
fibre products of the same cospan and `f` respects the two projections.

This is the step of the proof of Stacks 07SQ at which the square of Stacks 084U, Cartesian over
the limit, makes the morphism of display 70.5.10.1 invertible there, so that Stacks 084S
applies. -/
theorem MorphismDescentSystem.isIso_mapLimit_of_isPullback
    (M : MorphismDescentSystem B S hS hZ I)
    {W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (pZ : M.base.obj (op M.initial) ⟶ Z) (aW : W ⟶ Z)
    (q : M.target₀ ⟶ W) (hq : IsPullback M.targetToBase q pZ aW)
    (cS : M.source₀ ⟶ W) (hcS : M.map₀ ≫ q = cS)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {α : P ⟶ limit M.base} {γ : P ⟶ M.source₀}
    (hPstage : IsPullback α γ (limit.π M.base (op M.initial)) M.sourceToBase)
    (hP : IsPullback α (γ ≫ cS) (limit.π M.base (op M.initial) ≫ pZ) aW) :
    IsIso M.mapLimit := by
  have htgt : IsPullback (pullback.fst (limit.π M.base (op M.initial)) M.targetToBase)
      (pullback.snd (limit.π M.base (op M.initial)) M.targetToBase ≫ q)
      (limit.π M.base (op M.initial) ≫ pZ) aW :=
    isPullback_pullback_fst_snd_comp _ _ q pZ aW hq
  have hsrc : IsPullback (pullback.fst (limit.π M.base (op M.initial)) M.sourceToBase)
      (pullback.snd (limit.π M.base (op M.initial)) M.sourceToBase ≫ cS)
      (limit.π M.base (op M.initial) ≫ pZ) aW := by
    refine hP.of_iso (hPstage.isoIsPullback _ _
      (IsPullback.of_hasPullback (limit.π M.base (op M.initial)) M.sourceToBase))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans
        (IsPullback.isoIsPullback_hom_fst _ _ hPstage _).symm
    · exact (Category.comp_id _).trans
        ((congrArg (fun z => z ≫ cS)
          (IsPullback.isoIsPullback_hom_snd _ _ hPstage _).symm).trans
          (Category.assoc _ _ _))
    · simp
    · simp
  have hmap : M.mapLimit = (hsrc.isoIsPullback _ _ htgt).hom := by
    refine htgt.hom_ext ?_ ?_
    · exact M.mapLimit_fst.trans
        (IsPullback.isoIsPullback_hom_fst _ _ hsrc htgt).symm
    · refine (Category.assoc _ _ _).symm.trans ?_
      refine ((congrArg (fun z => z ≫ q) M.mapLimit_snd).trans
        (Category.assoc _ _ _)).trans ?_
      refine (congrArg (fun z => pullback.snd (limit.π M.base (op M.initial))
        M.sourceToBase ≫ z) hcS).trans ?_
      exact (IsPullback.isoIsPullback_hom_snd _ _ hsrc htgt).symm
  rw [hmap]
  exact (inferInstance : IsIso (hsrc.isoIsPullback (limit M.base) W htgt).hom)

/-- **A stage of a morphism descent system is affine once the base change of the morphism there
is an isomorphism.** In the situation of Stacks 084W, suppose the target `Y₀` of the morphism to
be descended is the fibre product of the distinguished stage with an affine object `W` of the
site over an affine algebraic space `Z`, the morphism `h_W ⟶ Z` being surjective and étale.
If the base change `f_k` of `f₀` to a stage `k` is an isomorphism and the base change `X_k` of
`X₀` there is affine, then the stage `B_k` of the system is an affine algebraic space.

This is the last step of the proof of Stacks 07SQ: the étale covering `Spec B_i ⟶ Spec A_i`
descends affineness of `X_i ⟶ Spec A_i` by the implication (4) ⇒ (2) of Stacks 03WG, and the
source of an affine morphism with affine target is affine. -/
theorem MorphismDescentSystem.isAffineSpace_base_obj_of_isIso_mapAt
    (M : MorphismDescentSystem B S hS hZ I)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (pZ : M.base.obj (op M.initial) ⟶ Z)
    {W : BigFppfOver B S hS} (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (aW : yoneda.obj W ⟶ Z) (haWsurj : IsSurjective B S hS aW)
    (haWetale : IsEtale B S hS aW) (hZalg : IsAlgebraicSpace B S hS Z)
    (hZaff : IsAffineSpace B S hS Z) (q : M.target₀ ⟶ yoneda.obj W)
    (hq : IsPullback M.targetToBase q pZ aW) {k : I} (hk : M.initial ≤ k)
    (hsrcAff : IsAffineSpace B S hS (M.sourceAt k hk)) (hkiso : IsIso (M.mapAt k hk)) :
    IsAffineSpace B S hS (M.base.obj (op k)) := by
  have := hkiso
  have htgtAff : IsAffineSpace B S hS (M.targetAt k hk) :=
    hsrcAff.of_iso (asIso (M.mapAt k hk))
  have h4 : IsPullback (pullback.fst (M.baseAtToInitial k hk) M.targetToBase)
      (pullback.snd (M.baseAtToInitial k hk) M.targetToBase ≫ q)
      (M.baseAtToInitial k hk ≫ pZ) aW :=
    isPullback_pullback_fst_snd_comp _ _ q pZ aW hq
  have hpbAff : IsAffineSpace B S hS (pullback (M.baseAtToInitial k hk ≫ pZ) aW) :=
    htgtAff.of_iso (h4.isoIsPullback _ _
      (IsPullback.of_hasPullback (M.baseAtToInitial k hk ≫ pZ) aW))
  exact (isAffineHom_of_isAffineSpace_pullback_of_etaleChart B S hS
    (M.base_isAlgebraicSpace k) hZalg (M.baseAtToInitial k hk ≫ pZ) hW aW haWsurj haWetale
    hpbAff).isAffineSpace_source hZaff

end MapLimit

end AlgebraicGeometry.Space

end
