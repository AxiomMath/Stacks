module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.EtaleRestrictionInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.RestrictionAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.DerivedPushforwardBound
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseTerminalChartIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicExactnessLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedIdealSheafOfClosedSet
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.NoetherianDerivedEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel

/-!
# The restriction unit of an injective quasi-coherent module is surjective after direct image

Let `U` be the algebraic space represented by an affine scheme with Noetherian ring of global
functions, and let `𝒥` be an injective object of `QCoh(𝒪_U)`.  This file proves
`AlgebraicGeometry.Space.RestrictionUnitPushforwardEpi` for `𝒥`: for every affine algebraic space
`V` étale over `U`, every quasi-compact open subspace `k : P ⟶ V` and every morphism `b` from `V`
to an affine algebraic space `T`, the direct image `b_*` carries the restriction unit
`𝒥|_V ⟶ k_*(𝒥|_P)` to an epimorphism.

The argument:

* `𝒥|_V` is an injective object of `QCoh(𝒪_V)`
  (`AlgebraicGeometry.Space.injective_etaleModulePullback_of_isAffineSpace`).
* By the Hom form of Stacks 07UM (`AlgebraicGeometry.Space.exists_homRestrict_eq`) every morphism
  `𝒪_P ⟶ 𝒥|_P` extends to a morphism `ℐⁿ ⟶ 𝒥|_V`, where `ℐ` is the reduced ideal sheaf of the
  complement of `P`; injectivity of `𝒥|_V` extends it to `𝒪_V`.  So every section of `𝒥` over `P`
  extends to `V`.
* Through the adjunctions `b^* ⊣ b_*` and `k^* ⊣ k_*` that says every morphism
  `𝒪_T ⟶ b_* k_* k^* 𝒥|_V` factors through `b_*` of the unit.
* On an affine algebraic space a morphism of quasi-coherent modules with that lifting property for
  the structure sheaf is an epimorphism: it is surjective on the sections over a terminal affine
  chart, hence by Descent, Proposition 03DX (2) over every affine chart.

## Main results

* `AlgebraicGeometry.Space.epi_of_forall_unit_lift`: the epimorphism criterion on an affine space.
* `AlgebraicGeometry.Space.exists_etaleModulePullback_map_eq_of_injective`: sections of an
  injective quasi-coherent module over a quasi-compact open subspace extend.
* `AlgebraicGeometry.Space.restrictionUnitPushforwardEpi_of_injective`: the conclusion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- A formal step: if every morphism `L X ⟶ L N` is `L s` for some `s : X ⟶ N`, then every
morphism `O ⟶ R' (R (L N))` factors through `R'` of the unit `N ⟶ R (L N)`, for adjunctions
`L ⊣ R` and `L' ⊣ R'` and an isomorphism `L' O ≅ X`. -/
theorem exists_comp_map_unit_eq_of_forall_exists_map_eq {C D E : Type*} [Category C]
    [Category D] [Category E] {L' : C ⥤ D} {R' : D ⥤ C} (adj' : L' ⊣ R') {L : D ⥤ E}
    {R : E ⥤ D} (adj : L ⊣ R) {O : C} {X N : D} (c : L'.obj O ≅ X)
    (H : ∀ u : L.obj X ⟶ L.obj N, ∃ s : X ⟶ N, L.map s = u)
    (t : O ⟶ R'.obj (R.obj (L.obj N))) :
    ∃ r : O ⟶ R'.obj N, r ≫ R'.map (adj.unit.app N) = t := by
  obtain ⟨s, hs⟩ := H ((adj.homEquiv _ _).symm (c.inv ≫ (adj'.homEquiv _ _).symm t))
  have hs' : s ≫ adj.unit.app N = c.inv ≫ (adj'.homEquiv _ _).symm t := by
    have h := congrArg (adj.homEquiv _ _) hs
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit] at h
    rw [← h]
    exact adj.unit.naturality s
  refine ⟨adj'.homEquiv _ _ (c.hom ≫ s), ?_⟩
  rw [← Adjunction.homEquiv_naturality_right, Category.assoc, hs', Iso.hom_inv_id_assoc]
  exact Equiv.apply_symm_apply _ t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Surjectivity on the sections over a terminal affine chart propagates to every affine chart,
for a morphism of quasi-coherent modules. -/
theorem surjective_val_app_of_surjective_val_app_isTerminal (Y : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (_hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) (hV₀aff : IsAffineChart B S hS Y.1 V₀)
    (V : SmallEtale B S hS Y.1) (hV : IsAffineChart B S hS Y.1 V)
    (h : Function.Surjective (φ.val.app (op V₀)).hom) :
    Function.Surjective (φ.val.app (op V)).hom := by
  let f : V ⟶ V₀ := hV₀.from V
  let _ := chartAlgebra (hF := Y.2) f
  have hcomp : Function.Surjective
      (fun z => (φ.val.app (op V)).hom (sectionsBaseChange M f z)) := by
    rw [show (fun z => (φ.val.app (op V)).hom (sectionsBaseChange M f z)) =
        fun z => sectionsBaseChange N f
          (LinearMap.lTensor (chartRing B S hS Y.1 Y.2 V) (φ.val.app (op V₀)).hom z) from
      funext (app_sectionsBaseChange φ f)]
    exact (bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS Y.1 Y.2 N hN hV₀aff hV
      f).2.comp (LinearMap.lTensor_surjective _ h)
  exact hcomp.of_comp

/-- **The epimorphism criterion on an affine algebraic space.**  A morphism `φ : M ⟶ Q` of
quasi-coherent modules on an affine algebraic space is an epimorphism as soon as every morphism
`𝒪 ⟶ Q` factors through `φ`. -/
theorem epi_of_forall_unit_lift (Y : AlgebraicSpaces B S hS) (hY : IsAffineSpace B S hS Y.1)
    {M Q : Modules.{u, u} B S hS Y.1 Y.2} (hM : M.IsQuasicoherentOnSite)
    (hQ : Q.IsQuasicoherentOnSite) (φ : M ⟶ Q)
    (h : ∀ t : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ Q,
      ∃ r, r ≫ φ = t) :
    Epi φ := by
  obtain ⟨V₀, ⟨hV₀⟩, hV₀aff⟩ := exists_isTerminal_isAffine_chart B S hS Y hY
  have h₀ : Function.Surjective (φ.val.app (op V₀)).hom := by
    intro x
    obtain ⟨r, hr⟩ := h (Q.unitHomEquiv.symm
      ((Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal Q hV₀).symm x))
    refine ⟨Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M hV₀
      (M.unitHomEquiv r), ?_⟩
    have h1 := congrArg (fun t =>
      Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal Q hV₀ (Q.unitHomEquiv t)) hr
    simp only [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply] at h1
    exact h1
  refine (modules_epi_iff_exists_covering B S hS _ _ φ).2 fun U s => ?_
  obtain ⟨R, hR, hRaff⟩ := isCoveringFamily_isAffineChart B S hS Y U
  refine ⟨Sieve.generate R, hR, fun V g hg => ?_⟩
  obtain ⟨Z, k, f, hf, rfl⟩ := hg
  obtain ⟨t, ht⟩ := surjective_val_app_of_surjective_val_app_isTerminal B S hS Y hM hQ φ hV₀
    hV₀aff Z (hRaff hf) h₀ (Q.val.map f.op s)
  exact ⟨M.val.map k.op t, (PresheafOfModules.naturality_apply φ.val k.op t).trans
    ((congrArg (fun z => Q.val.map k.op z) ht).trans
      (PresheafOfModules.map_comp_apply Q.val f.op k.op s).symm)⟩

/-- **Morphisms out of the structure sheaf extend from the complement of a sheaf of ideals**, into
an injective quasi-coherent module on a Noetherian algebraic space.  By Stacks 07UM a morphism
`𝒪_U ⟶ 𝒩|_U`, `U = X ∖ V(ℐ)`, is the restriction of a morphism `ℐⁿ ⟶ 𝒩`, and injectivity of `𝒩`
in `QCoh(𝒪_X)` extends that along `ℐⁿ ⊆ 𝒪_X`. -/
theorem exists_restrictToIdealComplement_map_eq_of_injective (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (I : IdealSheaves B S hS X.1 X.2) (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (𝒩 : Modules.{u, u} B S hS X.1 X.2) (h𝒩 : 𝒩.IsQuasicoherentOnSite)
    (hinj : Injective (⟨𝒩, h𝒩⟩ : QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
    (u : (restrictToIdealComplement B S hS X I).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⟶
      (restrictToIdealComplement B S hS X I).obj 𝒩) :
    ∃ s : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⟶ 𝒩,
      (restrictToIdealComplement B S hS X I).map s = u := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  have hG := isCoherent_structureSheaf B S hS X.1 X.2
  obtain ⟨n, Ψ, hΨ⟩ := exists_homRestrict_eq B S hS X I
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 I.toSheafOfModules hIq)
    _ 𝒩 u hZ hN hIq h𝒩 hG
  have hq := isQuasicoherentOnSite_idealPowModule (B := B) (S := S) (hS := hS) (X := X) (I := I)
    (G := SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    hZ hN hIq hG n
  let A : QuasicoherentSheaves.{u, u} B S hS X.1 X.2 := ⟨_, hq⟩
  let O : QuasicoherentSheaves.{u, u} B S hS X.1 X.2 :=
    ⟨_, SheafOfModules.isQuasicoherentOnSite_unit _⟩
  let ι' : A ⟶ O := ObjectProperty.homMk (idealPowModuleι I n _)
  have : Mono ι' := (ObjectProperty.ι _).mono_of_mono_map
    (show Mono (idealPowModuleι I n _) from inferInstance)
  let ψ := Injective.factorThru (ObjectProperty.homMk Ψ : A ⟶ ⟨𝒩, h𝒩⟩) ι'
  have hfac : idealPowModuleι I n _ ≫ ψ.hom = Ψ :=
    congrArg (fun f => f.hom) (Injective.comp_factorThru (ObjectProperty.homMk Ψ : A ⟶ ⟨𝒩, h𝒩⟩) ι')
  refine ⟨ψ.hom, ?_⟩
  rw [← hΨ, ← hfac]
  unfold homRestrict
  rw [Functor.map_comp, ← idealPowRestrictIso_hom, Iso.inv_hom_id_assoc]

/-- An open immersion `k : P ⟶ X` of algebraic spaces is isomorphic over `X` to the open
complement of the reduced sheaf of ideals of the closed complement of its image. -/
theorem exists_iso_idealComplement_of_isOpenImmersion (X : AlgebraicSpaces B S hS)
    {P : AlgebraicSpaces B S hS} (k : P ⟶ X) (hko : IsOpenImmersion B S hS k.hom) :
    ∃ (I : IdealSheaves B S hS X.1 X.2) (_ : I.toSheafOfModules.IsQuasicoherentOnSite)
      (φ : P ≅ idealComplement B S hS X I), φ.hom ≫ idealComplementι B S hS X I = k := by
  have hopen := isOpen_range_pointsMap_of_isOpenImmersion B S hS k.hom hko
  let I : IdealSheaves B S hS X.1 X.2 := reducedIdealSheaf B S hS X _ hopen.isClosed_compl
  have hunit : idealUnitLocus B S hS X I = Set.range (pointsMap B S hS P.1 k.hom) :=
    compl_injective (idealZeroLocus_reducedIdealSheaf B S hS X _ hopen.isClosed_compl)
  have hrange : Set.range (pointsMap B S hS (idealComplementSubfunctor B S hS X I).toFunctor
      (idealComplementSubfunctor B S hS X I).ι) = Set.range (pointsMap B S hS P.1 k.hom) := by
    rw [← hunit]
    exact range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hU := isOpenSubspace_idealComplementSubfunctor B S hS X I
  obtain ⟨a, ha⟩ := (factorsThrough_openSubspace_iff_points B S hS X.2 P.2 _ hU k.hom).2
    hrange.symm.le
  have : Mono k.hom := mono_of_isOpenImmersion B S hS k.hom hko
  obtain ⟨b, hb⟩ := (factorsThrough_openSubspace_iff_points B S hS X.2 hU.1 (Subfunctor.range k.hom)
    (isOpenSubspace_subfunctorRange B S hS P.2 hko) (idealComplementSubfunctor B S hS X I).ι).2 (by
      rw [hrange]
      rintro _ ⟨y, rfl⟩
      refine ⟨pointsMap B S hS _ (Subfunctor.toRange k.hom) y, ?_⟩
      rw [← pointsMap_comp_apply, Subfunctor.toRange_ι])
  let a' : (idealComplementSubfunctor B S hS X I).toFunctor ⟶ P.1 :=
    b ≫ inv (Subfunctor.toRange k.hom)
  have ha' : a' ≫ k.hom = (idealComplementSubfunctor B S hS X I).ι := by
    calc a' ≫ k.hom = b ≫ inv (Subfunctor.toRange k.hom) ≫ Subfunctor.toRange k.hom ≫
          (Subfunctor.range k.hom).ι := by rw [Subfunctor.toRange_ι, Category.assoc]
      _ = _ := by rw [IsIso.inv_hom_id_assoc, hb]
  refine ⟨I, isQuasicoherentOnSite_reducedIdealSheaf B S hS X _ hopen.isClosed_compl,
    { hom := ObjectProperty.homMk a
      inv := ObjectProperty.homMk a'
      hom_inv_id := ?_
      inv_hom_id := ?_ }, ?_⟩
  · ext1
    change a ≫ a' = 𝟙 P.1
    rw [← cancel_mono k.hom, Category.assoc, ha', ha, Category.id_comp]
  · ext1
    change a' ≫ a = 𝟙 (idealComplementSubfunctor B S hS X I).toFunctor
    rw [← cancel_mono (idealComplementSubfunctor B S hS X I).ι, Category.assoc, ha, ha',
      Category.id_comp]
  · ext1
    exact ha

/-- **Sections of an injective quasi-coherent module extend from an open subspace**, in the form
of morphisms out of the structure sheaf: for a Noetherian algebraic space `X`, an injective object
`𝒩` of `QCoh(𝒪_X)` and an open immersion `k : P ⟶ X`, every morphism `𝒪_P ⟶ 𝒩|_P` is the
restriction of a morphism `𝒪_X ⟶ 𝒩`. -/
theorem exists_etaleModulePullback_map_eq_of_injective (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (𝒩 : Modules.{u, u} B S hS X.1 X.2) (h𝒩 : 𝒩.IsQuasicoherentOnSite)
    (hinj : Injective (⟨𝒩, h𝒩⟩ : QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
    {P : AlgebraicSpaces B S hS} (k : P ⟶ X) (hk : IsEtale B S hS k.hom)
    (hko : IsOpenImmersion B S hS k.hom)
    (u : (etaleModulePullback.{u, u} B S hS k hk).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⟶
      (etaleModulePullback.{u, u} B S hS k hk).obj 𝒩) :
    ∃ s : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⟶ 𝒩,
      (etaleModulePullback.{u, u} B S hS k hk).map s = u := by
  obtain ⟨I, hIq, φ, hφ⟩ := exists_iso_idealComplement_of_isOpenImmersion B S hS X k hko
  let α := etaleModulePullbackFactorIso B S hS φ.hom (idealComplementι B S hS X I)
    (isEtale_of_isIso B S hS φ.hom.hom) (isEtale_idealComplementι B S hS X I) hφ hk
  let E := etaleModulePullbackEquivalence B S hS φ
  let O := SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  obtain ⟨s, hs⟩ := exists_restrictToIdealComplement_map_eq_of_injective B S hS hZ X hN I hIq 𝒩 h𝒩
    hinj (E.fullyFaithfulFunctor.preimage (α.hom.app O ≫ u ≫ α.inv.app 𝒩))
  refine ⟨s, ?_⟩
  have hmap : E.functor.map ((restrictToIdealComplement B S hS X I).map s) =
      α.hom.app O ≫ u ≫ α.inv.app 𝒩 := by
    rw [hs]
    exact E.fullyFaithfulFunctor.map_preimage _
  have key := (α.hom.naturality s).symm.trans (congrArg (· ≫ α.hom.app 𝒩) hmap)
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at key
  exact (Iso.cancel_iso_hom_left (α.app O) _ _).1 key

/-- **The restriction unit of an injective quasi-coherent module is surjective after direct image
to an affine space.**  Let `V` be a Noetherian affine algebraic space, `𝒩` an injective object of
`QCoh(𝒪_V)`, `k : P ⟶ V` a quasi-compact open subspace and `b : V ⟶ T` a morphism to an affine
algebraic space.  Then `b_*` of the unit `𝒩 ⟶ k_*(𝒩|_P)` is an epimorphism. -/
theorem epi_modulePushforward_map_unit_of_injective (hZ : B.Contains (⊤_ Scheme.{u}))
    {V P T : AlgebraicSpaces B S hS} (hV : IsAffineSpace B S hS V.1)
    (hVN : IsNoetherian B S hS hZ V.1) (𝒩 : Modules.{u, u} B S hS V.1 V.2)
    (h𝒩 : 𝒩.IsQuasicoherentOnSite)
    (hinj : Injective (⟨𝒩, h𝒩⟩ : QuasicoherentSheaves.{u, u} B S hS V.1 V.2))
    (k : P ⟶ V) (hk : IsEtale B S hS k.hom) (hko : IsOpenImmersion B S hS k.hom)
    (hPqc : IsQuasiCompactSpace B S hS P.1) (b : V ⟶ T) (hT : IsAffineSpace B S hS T.1) :
    Epi ((modulePushforward B S hS b).map
      ((etaleModulePullbackAdjunction B S hS k hk).unit.app 𝒩)) := by
  have hkqc : IsQuasiCompact B S hS k.hom := isQuasiCompact_of_isQuasiCompactSpace B S hS hZ V.2
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hV) hPqc k.hom
  have hkqs : IsQuasiSeparated B S hS k.hom :=
    isQuasiSeparated_of_isSeparated B S hS
      (isSeparated_of_mono (B := B) (S := S) (hS := hS) k.hom
        (mono_of_isOpenImmersion B S hS k.hom hko))
  have hb : IsAffineHom B S hS b.hom := isAffineHom_of_isAffineSpace B S hS b.hom hV hT
  have hM := isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS b hb 𝒩 h𝒩
  have hQ := isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS b hb _
    (isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS k hkqc hkqs _
      (isQuasicoherentOnSite_etaleModulePullback B S hS k hk 𝒩 h𝒩))
  exact epi_of_forall_unit_lift B S hS T hT hM hQ _
    (exists_comp_map_unit_eq_of_forall_exists_map_eq (modulePullbackAdjunction B S hS b)
      (etaleModulePullbackAdjunction B S hS k hk) (modulePullbackUnitIso B S hS b)
      (exists_etaleModulePullback_map_eq_of_injective B S hS hZ V hVN 𝒩 h𝒩 hinj k hk hko))

/-- **The restriction unit of an injective quasi-coherent module on a Noetherian affine space is
surjective after direct image to an affine space.**  Let `W` be an object of the big fppf site
whose underlying scheme is affine with Noetherian ring of global functions, with `schemeSpace W`
Noetherian, and let `𝒥` be an injective object of `QCoh(𝒪_W)`.  Then `𝒥` has the property
`AlgebraicGeometry.Space.RestrictionUnitPushforwardEpi`. -/
theorem restrictionUnitPushforwardEpi_of_injective (hZ : B.Contains (⊤_ Scheme.{u}))
    (W : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)]
    (hWN : IsNoetherian B S hS hZ (schemeSpace W).1)
    (J : QuasicoherentSheaves.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2)
    (hJ : Injective J) : RestrictionUnitPushforwardEpi B S hS J.obj := by
  intro V P T e he k hk b hV hko hPqc hT
  convert epi_modulePushforward_map_unit_of_injective B S hS hZ hV
    (isNoetherian_of_isEtale_of_isAffineSpace B S hS hZ V.2 (schemeSpace W).2 e.hom he hV hWN.2.2)
    _ (isQuasicoherentOnSite_etaleModulePullback B S hS e he J.obj J.2)
    (injective_etaleModulePullback_of_isAffineSpace B S hS W J hJ hV e he) k hk hko hPqc b hT
    using 3

end AlgebraicGeometry.Space

end
