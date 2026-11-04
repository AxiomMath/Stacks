module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentLocusComparisonModel
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# The affine core of Tag 0BF1

Let `f : X ⟶ Spec A` and `f' : X' ⟶ Spec A` be proper and of finite presentation, `a : X' ⟶ X`
a morphism over `Spec A`, `L` an `𝒪_X`-module of finite presentation flat over `A` with `a^* L`
of finite presentation and flat over `A`, and let `χ₀ : A → K₀` be a field-valued point at which
`L` is trivial, the fibres have `Γ(𝒪) = K₀`, and `H¹(X₀, 𝒪) → H¹(X'₀, 𝒪)` is injective. This file
proves the commutative-algebra core of [Stacks, Tag 0BF1] in the form it is used: there are
`g ∉ ker χ₀` and finitely many `c_k ∈ ker χ₀` such that over `D(g)`

* if `a^* L` becomes trivial over an `A`-algebra `B` whose fibre has `Γ(𝒪) = B`, then all
  `c_k` vanish in `B`, and
* if all `c_k` vanish in `B`, then `L_B` has a global section that is nonzero on every fibre of
  `X_B ⟶ Spec B` over a field.

This is the source's "after shrinking `S` … `d' = 0`, hence `d = 0`, so the trivializing section
of `L_s` lifts to a section of `L`".

## Main results

* `AlgebraicGeometry.DescentLocusComparison.exists_vanishing_family`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.DescentLocusComparison

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Injectivity of the pullback map on cohomology depends only on the isomorphism class of the
module.** -/
theorem injective_moduleCohomologyPullbackMap_of_iso {Y Z : RingedSpace.{u, u}} (g : Y ⟶ Z)
    (i : ℤ) {G G' : SheafOfModules.{u} (structureSheafRing Z)} (e : G' ≅ G)
    (h : Function.Injective (Stacks.Cohomology.moduleCohomologyPullbackMap g i G)) :
    Function.Injective (Stacks.Cohomology.moduleCohomologyPullbackMap g i G') := by
  have hnat := Stacks.Cohomology.moduleCohomologyPullbackMap_naturality g i e.hom
  have h1 : Function.Injective ((Stacks.Cohomology.spaceModuleCohomology Z i).map e.hom) :=
    ((Stacks.Cohomology.spaceModuleCohomology Z i).mapIso e).toLinearEquiv.injective
  have key := fun z => congr($hnat z)
  simp only [ConcreteCategory.comp_apply] at key
  intro x y hxy
  exact h1 (h (by rw [key x, key y, hxy]))

section Model

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
  {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] {fY : Y ⟶ Spec (.of B)}
  {g : Y ⟶ X} (hsq : IsPullback g fY f (Spec.map (CommRingCat.ofHom φ)))
  (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [Fintype I] [LinearOrder I]
  (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {P : CochainComplex (ModuleCat.{u} A) ℤ} (u : P ⟶ baseAlternatingCechComplex f U hU F)
  [QuasiIso u] [∀ n : ℤ, Module.Flat A (P.X n)] (hflat : IsFlatOver f.toLRSHom.toShHom F)
  (b : ℤ) [P.IsStrictlyLE b]

/-- **`H⁰` of the base change of a model is the module of global sections of the base change.** -/
def homologyZeroModelEquiv :
    letI := Stacks.Cech.sectionsModule fY ((Scheme.Modules.pullback g).obj F) ⊤
    (extendScalarsComplex φ P).homology 0 ≃ₗ[B] Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
  letI := Stacks.Cech.sectionsModule fY ((Scheme.Modules.pullback g).obj F) ⊤
  have := quasiIso_baseChangeChainComparison φ hsq F U hU hUaff u hflat b
  (asIso (HomologicalComplex.homologyMap
      (baseChangeChainComparison φ hsq F U hU hUaff u) 0)).toLinearEquiv.trans
    (homologyZeroBaseEquivSections fY (fun j => g ⁻¹ᵁ U j) (top_eq_iSup_preimage g U hU)
      ((Scheme.Modules.pullback g).obj F))

omit [LinearOrder I] in
include hsq hU hUaff u hflat b in
/-- **The base change of a model has no `H⁻¹`.** -/
theorem subsingleton_homology_neg_one :
    Subsingleton ((extendScalarsComplex φ P).homology (-1)) := by
  have := quasiIso_baseChangeChainComparison φ hsq F U hU hUaff u hflat b
  refine ModuleCat.subsingleton_of_isZero (IsZero.of_iso ?_
    (asIso (HomologicalComplex.homologyMap (baseChangeChainComparison φ hsq F U hU hUaff u) (-1))))
  exact isZero_homology_baseAlternatingCechComplex_neg_one fY (fun j => g ⁻¹ᵁ U j)
    (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F)

omit [LinearOrder I] in
include hsq hU hUaff u hflat b in
/-- **A degree-zero cocycle of the base change of a model is a global section, and its class
dies on a fibre exactly where that section does.** If `σ` is a cocycle of `P ⊗_A B`, there is a
global section `s` of the base change of `F` such that for every further base change
`Z ⟶ Y` along `B → K` on which `s` pulls back to zero, the image of `σ` in `P ⊗_A K` is a
coboundary. -/
theorem exists_section_of_cycle (σ : (extendScalarsComplex φ P).X 0)
    (hσ : (extendScalarsComplex φ P).d 0 1 σ = 0) :
    ∃ s : Γ((Scheme.Modules.pullback g).obj F, ⊤),
      ∀ (K : Type u) [CommRing K] (χ : B →+* K) {Z : Scheme.{u}} {fZ : Z ⟶ Spec (.of K)}
        {gZ : Z ⟶ Y} (_ : IsPullback gZ fZ fY (Spec.map (CommRingCat.ofHom χ))),
        Stacks.Cech.pullbackSections gZ ((Scheme.Modules.pullback g).obj F) ⊤ s = 0 →
        ∃ τ : (extendScalarsComplex (χ.comp φ) P).X (-1),
          (extendScalarsComplex (χ.comp φ) P).d (-1) 0 τ =
            (ModuleCat.extendScalarsComp φ χ).inv.app (P.X 0)
              (StacksDraft.Perfect.etm χ 1 σ) := by
  have : IsSeparated fY := isSeparated_of_isPullback φ hsq
  set FY := (Scheme.Modules.pullback g).obj F
  set UY : I → Y.Opens := fun j => g ⁻¹ᵁ U j
  set hUY := top_eq_iSup_preimage g U hU
  set Φ := baseChangeChainComparison φ hsq F U hU hUaff u
  have hc := congr($(Φ.comm 0 1) σ)
  simp only [ConcreteCategory.comp_apply] at hc
  have hx : (baseAlternatingCechComplex fY UY hUY FY).d 0 1 (Φ.f 0 σ) = 0 := by
    rw [hc, hσ, map_zero]
  set x := Φ.f 0 σ
  let := Stacks.Cech.sectionsModule fY FY ⊤
  let := Stacks.Cech.cochainModule fY UY FY 0
  let := Stacks.Cech.cochainModule fY UY FY 1
  have hy1 : (Stacks.Cech.alternatingCechModuleComplex fY UY FY).d 0 (0 + 1)
      ((baseAlternatingCechComplexXIso fY UY hUY FY 0).hom x) = 0 := by
    have h := congr($(d_comp_baseAlternatingCechComplexXIso_hom fY UY hUY FY 0) x)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    have hx' : (baseAlternatingCechComplex fY UY hUY FY).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) x = 0 :=
      hx
    rw [← h, hx', map_zero]
  rw [Stacks.Cech.alternatingCechModuleComplex_d] at hy1
  obtain ⟨s, hs⟩ : (baseAlternatingCechComplexXIso fY UY hUY FY 0).hom x ∈
      LinearMap.range (Stacks.Cech.sectionsToAlternatingₗ fY UY FY (fun _ => le_top)) := by
    rwa [Stacks.Cech.range_sectionsToAlternatingₗ fY UY FY (fun _ => le_top) hUY.le]
  refine ⟨s, fun K _ χ Z fZ gZ hsqZ hs0 => ?_⟩
  set ΦK := baseChangeChainComparison (χ.comp φ)
    (Stacks.Cech.isPullback_comp_specMap φ χ f fY fZ g gZ hsq hsqZ) F U hU hUaff u
  have hq : QuasiIso ΦK := quasiIso_baseChangeChainComparison _ _ F U hU hUaff u hflat b
  set yK := (ModuleCat.extendScalarsComp φ χ).inv.app (P.X 0) (StacksDraft.Perfect.etm χ 1 σ)
  -- the image of `x` in the Čech model of the fibre vanishes
  have hbc : (baseAlternatingCechComplexBaseChangeIso χ hsqZ FY UY hUY
      (isAffineOpen_preimage φ hsq U hUaff)).hom.f 0 (StacksDraft.Perfect.etm χ 1 x) = 0 := by
    have h1 := fibreTransport_one_tmul χ hsqZ FY UY hUY (isAffineOpen_preimage φ hsq U hUaff) 0 x
    have h2 := Stacks.Cech.alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ fY UY FY
      (W := ⊤) (fun _ => le_top) gZ (fun j => gZ ⁻¹ᵁ UY j) (Equiv.refl I)
      (preimage_eq_preimage_equivRefl gZ UY) χ fZ
      (fun V => Stacks.Cech.baseRingHom_comp_app χ fY fZ gZ hsqZ V) s
    rw [← hs, h2, hs0, map_zero] at h1
    have hinj : Function.Injective (baseAlternatingCechComplexXIso fZ (fun j => gZ ⁻¹ᵁ UY j)
        (top_eq_iSup_preimage gZ UY hUY) ((Scheme.Modules.pullback gZ).obj FY) 0).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    exact hinj (by rwa [map_zero, StacksDraft.Perfect.etm_eq_tmul])
  have hcomp := congr($(HomologicalComplex.congr_hom
    (baseChangeChainComparison_comp φ χ hsq hsqZ F U hU hUaff u) 0)
      (StacksDraft.Perfect.etm χ 1 σ))
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    Functor.mapHomologicalComplex_map_f] at hcomp
  have hΦK : ΦK.f 0 yK = 0 := by
    have e1 : ΦK.f 0 yK = ΦK.f 0 (((extendScalarsComplexCompIso φ χ).hom.app P).f 0
        (StacksDraft.Perfect.etm χ 1 σ)) := rfl
    rw [e1, ← hcomp]
    have h3 : (ModuleCat.extendScalars.{u, u, u} χ).map (Φ.f 0) (StacksDraft.Perfect.etm χ 1 σ) =
        StacksDraft.Perfect.etm χ 1 x := StacksDraft.Perfect.map_etm _ _ _ _
    rw [h3]
    exact (congrArg (fun v => (baseAlternatingCechComplexMapIso fZ (fun j => (gZ ≫ g) ⁻¹ᵁ U j)
      (top_eq_iSup_preimage (gZ ≫ g) U hU)
      ((Scheme.Modules.pullbackComp gZ g).app F)).hom.f 0 v) hbc).trans (map_zero _)
  have hyK : (extendScalarsComplex (χ.comp φ) P).d 0 1 yK = 0 := by
    have h := congr($(((extendScalarsComplexCompIso φ χ).hom.app P).comm 0 1)
      (StacksDraft.Perfect.etm χ 1 σ))
    simp only [ConcreteCategory.comp_apply, Functor.comp_obj,
      Functor.mapHomologicalComplex_obj_d] at h
    refine h.trans ?_
    rw [StacksDraft.Perfect.map_etm]
    have hσ' : (ModuleCat.extendScalars.{u, u, u} φ).map (P.d 0 1) σ = 0 := hσ
    rw [hσ', show StacksDraft.Perfect.etm χ (1 : K)
      (0 : (extendScalarsComplex φ P).X 1) = 0 by simp,
      map_zero]
  have hmono : Mono (HomologicalComplex.homologyMap ΦK 0) := inferInstance
  rw [HomologicalComplex.mono_homologyMap_iff_elementwise _ (-1) 0 1 (by simp) (by simp)] at hmono
  exact hmono yK hyK 0 (by rw [hΦK, map_zero])

end Model

section Core

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} (a : X' ⟶ X)
  (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A)) (ha : a ≫ f = f')
  [IsProper f] [LocallyOfFinitePresentation f] [IsProper f'] [LocallyOfFinitePresentation f']
  (L : X.Modules) [L.IsFinitePresentation] (hL : IsFlatOver f.toLRSHom.toShHom L)
  (hL' : IsFlatOver f'.toLRSHom.toShHom ((Scheme.Modules.pullback a).obj L))

include ha hL hL' in
/-- **The affine core of [Stacks, Tag 0BF1].** Let `f`, `f'` be proper and of finite
presentation over `Spec A`, `a : X' ⟶ X` a morphism over `Spec A` and `L` of finite
presentation and flat over `A`, with `a^* L` flat over `A`. Let `χ₀ : A → K₀` be a point with
fibres `X₀`, `X'₀` and fibre morphism `a₀` such that `L` is trivial on `X₀`, both fibres have
`Γ(𝒪) = K₀`, and `H¹(X₀, 𝒪) → H¹(X'₀, 𝒪)` is injective. Then there are `g` with `χ₀ g ≠ 0` and
finitely many `c_k` with `χ₀ c_k = 0` such that for every `A`-algebra `B` in which `g` is
invertible:

* if the base change of `a^* L` to `X'_B` is trivial and `Γ(X'_B, 𝒪) = B`, then every `c_k`
  vanishes in `B`;
* if every `c_k` vanishes in `B`, then `L_B` has a global section whose pullback to every fibre
  of `X_B` over a field is nonzero.

The proof is the source's: the two Čech complexes are represented by finite complexes of finite
projective modules, the pullback along `a` by a chain map between them, and
`StacksDraft.Perfect.exists_vanishing_family_of_mono_homologyMap_one` does the linear algebra. -/
theorem exists_vanishing_family {K₀ : Type u} [Field K₀] (χ₀ : A →+* K₀)
    {X₀ X'₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of K₀)} {f'₀ : X'₀ ⟶ Spec (.of K₀)}
    {q₀ : X₀ ⟶ X} {q'₀ : X'₀ ⟶ X'}
    (hsq₀ : IsPullback q₀ f₀ f (Spec.map (CommRingCat.ofHom χ₀)))
    (hsq'₀ : IsPullback q'₀ f'₀ f' (Spec.map (CommRingCat.ofHom χ₀)))
    (a₀ : X'₀ ⟶ X₀) (ha₀ : a₀ ≫ f₀ = f'₀) (hcomm : a₀ ≫ q₀ = q'₀ ≫ a)
    (hL₀ : Nonempty ((Scheme.Modules.pullback q₀).obj L ≅ SheafOfModules.unit X₀.ringCatSheaf))
    (hΓ₀ : Function.Bijective (Stacks.Cech.baseRingHom f₀ ⊤).hom)
    (hΓ'₀ : Function.Bijective (Stacks.Cech.baseRingHom f'₀ ⊤).hom)
    (hH1 : Function.Injective (Stacks.Cohomology.moduleCohomologyPullbackMap
      a₀.toLRSHom.toShHom 1 (SheafOfModules.unit X₀.ringCatSheaf))) :
    ∃ g : A, χ₀ g ≠ 0 ∧ ∃ (n : ℕ) (c : Fin n → A), (∀ k, χ₀ (c k) = 0) ∧
      (∀ (B : Type u) [CommRing B] (φ : A →+* B), IsUnit (φ g) →
        ∀ {Y' : Scheme.{u}} {p' : Y' ⟶ X'} {h' : Y' ⟶ Spec (.of B)},
          IsPullback p' h' f' (Spec.map (CommRingCat.ofHom φ)) →
          Function.Bijective (Stacks.Cech.baseRingHom h' ⊤).hom →
          Nonempty ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback a).obj L) ≅
            SheafOfModules.unit Y'.ringCatSheaf) →
          ∀ k, φ (c k) = 0) ∧
      (∀ (B : Type u) [CommRing B] (φ : A →+* B), IsUnit (φ g) → (∀ k, φ (c k) = 0) →
        ∀ {Y : Scheme.{u}} {p : Y ⟶ X} {h : Y ⟶ Spec (.of B)},
          IsPullback p h f (Spec.map (CommRingCat.ofHom φ)) →
          ∃ σ : Γ((Scheme.Modules.pullback p).obj L, ⊤),
            ∀ (K : Type u) [Field K] (χ : B →+* K) {Z : Scheme.{u}} {e : Z ⟶ Spec (.of K)}
              {r : Z ⟶ Y}, IsPullback r e h (Spec.map (CommRingCat.ofHom χ)) →
              Stacks.Cech.pullbackSections r ((Scheme.Modules.pullback p).obj L) ⊤ σ ≠ 0) := by
  classical
  have := RingHom.ker_isPrime χ₀
  have : L.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation L
  -- covers of `X` and `X'`
  obtain ⟨I, _, _, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  obtain ⟨I', _, _, W, π, hWU, hW, hWaff, haff'⟩ := exists_affine_refinement a f' U hU
  -- finite projective models of the two Čech complexes
  obtain ⟨P, lo, hi, hGE, hLE, hfin, hproj, u, hu⟩ :=
    exists_finiteProjectiveModel_quasiIso_of_finitePresentation f U hU L haff hL
  obtain ⟨P', lo', hi', hGE', hLE', hfin', hproj', u', hu'⟩ :=
    exists_finiteProjectiveModel_quasiIso_of_finitePresentation f' W hW _ haff' hL'
  have := hGE
  have := hLE
  have := hGE'
  have := hLE'
  have hflatP : ∀ {Q : CochainComplex (ModuleCat.{u} A) ℤ}, (∀ i, Module.Projective A (Q.X i)) →
      ∀ n, Module.Flat A (Q.X n) := fun h n =>
    have := h n
    inferInstance
  have := hflatP hproj
  have := hflatP hproj'
  have : ∀ n, Module.Flat A ((baseAlternatingCechComplex f U hU L).X n) :=
    flat_baseAlternatingCechComplex_X f U hU L hUaff hL
  have : ∀ n, Module.Flat A ((baseAlternatingCechComplex f' W hW
      ((Scheme.Modules.pullback a).obj L)).X n) :=
    flat_baseAlternatingCechComplex_X f' W hW _ hWaff hL'
  -- the chain map of models
  set ψ := cechModelPullbackMap a f f' ha U hU W hW π hWU L
  obtain ⟨ψP, ⟨H⟩⟩ := StacksDraft.Perfect.exists_homotopy_comp_quasiIso hi u' (u ≫ ψ)
  -- the fibre over `χ₀`
  obtain ⟨e₀⟩ := hL₀
  let e'₀ : (Scheme.Modules.pullback q'₀).obj ((Scheme.Modules.pullback a).obj L) ≅
      SheafOfModules.unit X'₀.ringCatSheaf :=
    (Stacks.Cech.pullbackSquareIso a q₀ q'₀ a₀ hcomm L).symm ≪≫
      (Scheme.Modules.pullback a₀).mapIso e₀ ≪≫ Scheme.Modules.pullbackUnitIso a₀
  have hm : Module.finrank K₀ ((StacksDraft.Perfect.baseChangeComplex χ₀ P).homology (-1)) = 0 :=
    have := subsingleton_homology_neg_one χ₀ hsq₀ L U hU hUaff u hL hi
    Module.finrank_zero_of_subsingleton
  have hm' : Module.finrank K₀ ((StacksDraft.Perfect.baseChangeComplex χ₀ P').homology (-1)) =
      0 :=
    have := subsingleton_homology_neg_one χ₀ hsq'₀ _ W hW hWaff u' hL' hi'
    Module.finrank_zero_of_subsingleton
  have h0 : Module.finrank K₀ ((StacksDraft.Perfect.baseChangeComplex χ₀ P).homology 0) = 1 :=
    ((homologyZeroModelEquiv χ₀ hsq₀ L U hU hUaff u hL hi).trans
      (sectionsEquivOfIsoUnit f₀ e₀ hΓ₀)).finrank_eq.trans (Module.finrank_self K₀)
  have h0' : Module.finrank K₀ ((StacksDraft.Perfect.baseChangeComplex χ₀ P').homology 0) = 1 :=
    ((homologyZeroModelEquiv χ₀ hsq'₀ _ W hW hWaff u' hL' hi').trans
      (sectionsEquivOfIsoUnit f'₀ e'₀ hΓ'₀)).finrank_eq.trans (Module.finrank_self K₀)
  have hinj := Stacks.Cech.injective_rightDerived_unitAb a₀ ((Scheme.Modules.pullback q₀).obj L)
    (injective_moduleCohomologyPullbackMap_of_iso a₀.toLRSHom.toShHom 1 e₀ hH1)
  have hψ := mono_homologyMap_one_cechModelPullbackMap χ₀ a ha hsq₀ hsq'₀ a₀ ha₀ hcomm U hU
    hUaff W hW hWaff π hWU L hinj
  let E := (ModuleCat.extendScalars.{u, u, u} χ₀).mapHomologicalComplex (ComplexShape.up ℤ)
  have hEu : QuasiIso (E.map u) :=
    StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat χ₀ hi (Fintype.card I : ℤ) u
  have hEu' : QuasiIso (E.map u') :=
    StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat χ₀ hi' (Fintype.card I' : ℤ) u'
  have hsqH : HomologicalComplex.homologyMap (E.map ψP) 1 ≫
      HomologicalComplex.homologyMap (E.map u') 1 =
      HomologicalComplex.homologyMap (E.map u) 1 ≫ HomologicalComplex.homologyMap (E.map ψ) 1 := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← E.map_comp, ← E.map_comp]
    exact ((ModuleCat.extendScalars.{u, u, u} χ₀).mapHomotopy H).homologyMap_eq 1
  have h1 : Mono (HomologicalComplex.homologyMap (E.map ψP) 1) := by
    have : Mono (HomologicalComplex.homologyMap (E.map ψP) 1 ≫
        HomologicalComplex.homologyMap (E.map u') 1) := by
      rw [hsqH]
      infer_instance
    exact mono_of_mono _ (HomologicalComplex.homologyMap (E.map u') 1)
  -- the linear algebra
  obtain ⟨g, hg, n, c, hc, hI, hII⟩ :=
    StacksDraft.Perfect.exists_vanishing_family_of_mono_homologyMap_one χ₀ P P' lo hi lo' hi'
      hfin hproj hfin' hproj' ψP hm hm' h0 h0' h1
  refine ⟨g, hg, n, c, hc, ?_, ?_⟩
  · intro B _ φ hφ Y' p' h' hsq' hbij ⟨e⟩
    exact hI B φ hφ ⟨(homologyZeroModelEquiv φ hsq' _ W hW hWaff u' hL' hi').trans
      (sectionsEquivOfIsoUnit h' e hbij)⟩
  · intro B _ φ hφ hc0 Y p h hsq
    obtain ⟨σ, hσ, hnb⟩ := hII B φ hφ hc0
    obtain ⟨s, hs⟩ := exists_section_of_cycle φ hsq L U hU hUaff u hL hi σ hσ
    exact ⟨s, fun K _ χ Z e r hsqZ hzero => (hs K χ hsqZ hzero).elim (hnb K χ)⟩

end Core

end AlgebraicGeometry.DescentLocusComparison

end
