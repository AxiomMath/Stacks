module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisorChartRing
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsMeromorphicChartFraction

/-!
# The generic fibres of the chart of Stacks 0EQ4, as the data of the algebraic identity

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-- **A cocartesian square of commutative rings along a localization is a localization.** If
`A ⟶ F` is a localization at `M` and the square `A ⟶ C`, `A ⟶ F`, `C ⟶ T`, `F ⟶ T` is a pushout,
then `C ⟶ T` is the localization of `C` at the image of `M`. -/
theorem isLocalization_of_isPushout_commRingCat {A F C T : CommRingCat.{u}} (a : A ⟶ C)
    (b : A ⟶ F) (c : C ⟶ T) (d : F ⟶ T) (h : IsPushout a b c d) (M : Submonoid A)
    (hF : letI := b.hom.toAlgebra; IsLocalization M F) :
    letI := c.hom.toAlgebra
    IsLocalization (M.map a.hom) T := by
  let : Algebra A C := a.hom.toAlgebra
  let : Algebra A F := b.hom.toAlgebra
  let : Algebra C T := c.hom.toAlgebra
  let : Algebra F T := d.hom.toAlgebra
  let : Algebra A T := (c.hom.comp a.hom).toAlgebra
  have : IsScalarTower A C T := .of_algebraMap_eq' rfl
  have hw : c.hom.comp a.hom = d.hom.comp b.hom := by
    simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom h.w
  have : IsScalarTower A F T := .of_algebraMap_eq' hw
  have := hF
  have h' : IsPushout (CommRingCat.ofHom (algebraMap A C)) (CommRingCat.ofHom (algebraMap A F))
      (CommRingCat.ofHom (algebraMap C T)) (CommRingCat.ofHom (algebraMap F T)) := h
  exact (Algebra.isLocalization_iff_isPushout M F (T := C) (B := T)).mpr
    (CommRingCat.isPushout_iff_isPushout.mp h')

end AlgebraicGeometry

namespace Stacks.NormBranches

section FibreData

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (𝔭 : Ideal A) [𝔭.IsPrime]

local notation "Aₚ" => Localization.AtPrime 𝔭
local notation "Cₚ" => Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl)

omit [𝔭.IsPrime] in
/-- For a minimal prime `Q` of `A_𝔭` and `a ∈ A`, the images of `a` in the fibre ring `D_Q` via
the fibre field `O_Q` and via `C` agree. -/
theorem algebraMap_fibreField_fibreRing_algebraMap [𝔭.IsPrime] (Q : minimalPrimes Aₚ) (a : A) :
    algebraMap (fibreField Q) (fibreRing (D := Cₚ) Q) (algebraMap A (fibreField Q) a) =
      algebraMap C (fibreRing (D := Cₚ) Q) (algebraMap A C a) := by
  have := Q.2.1.1
  rw [IsScalarTower.algebraMap_apply A Aₚ (fibreField Q),
    ← IsScalarTower.algebraMap_apply Aₚ (fibreField Q) (fibreRing (D := Cₚ) Q),
    IsScalarTower.algebraMap_apply Aₚ Cₚ (fibreRing (D := Cₚ) Q),
    IsScalarTower.algebraMap_apply C Cₚ (fibreRing (D := Cₚ) Q),
    ← IsScalarTower.algebraMap_apply A Aₚ Cₚ, ← IsScalarTower.algebraMap_apply A C Cₚ]

/-- **A generic fibre given by two cocartesian squares is the generic fibre `D_Q` of the
localization.** Let `F` be the localization of `A` at the contraction `Q'` of a minimal prime `Q`
of `A_𝔭`, and suppose the squares `A ⟶ C, A ⟶ F, C ⟶ T, F ⟶ T` and `K ⟶ F, K ⟶ L, F ⟶ T, L ⟶ T`
are pushouts. Then `F ≃ O_Q` over `A`, `T ≃ D_Q` over `C`, and `L/K` base changes along
`K ⟶ F ≃ O_Q` to `D_Q/O_Q`. -/
theorem exists_ringEquiv_fibre_of_isPushout (Q : minimalPrimes Aₚ) {F T K L : Type u}
    [CommRing F] [CommRing T] [CommRing K] [CommRing L] (b : A →+* F)
    (hF : letI := b.toAlgebra; haveI := Q.2.1.1;
      IsLocalization (Q.1.comap (algebraMap A Aₚ)).primeCompl F)
    (c : C →+* T) (dF : F →+* T)
    (h2 : IsPushout (CommRingCat.ofHom (algebraMap A C)) (CommRingCat.ofHom b)
      (CommRingCat.ofHom c) (CommRingCat.ofHom dF))
    (φ : K →+* F) (ψ : K →+* L) (j : L →+* T)
    (h1 : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ) (CommRingCat.ofHom dF)
      (CommRingCat.ofHom j)) :
    ∃ (ε : F ≃+* fibreField Q) (ε' : T ≃+* fibreRing (D := Cₚ) Q),
      (∀ a, ε (b a) = algebraMap A (fibreField Q) a) ∧
      (∀ x, ε' (c x) = algebraMap C (fibreRing (D := Cₚ) Q) x) ∧
      IsPushout (CommRingCat.ofHom (ε.toRingHom.comp φ)) (CommRingCat.ofHom ψ)
        (CommRingCat.ofHom (algebraMap (fibreField Q) (fibreRing (D := Cₚ) Q)))
        (CommRingCat.ofHom (ε'.toRingHom.comp j)) := by
  have := Q.2.1.1
  let : Algebra A F := b.toAlgebra
  let : Algebra C T := c.toAlgebra
  have hT : IsLocalization (Algebra.algebraMapSubmonoid C (Q.1.comap (algebraMap A Aₚ)).primeCompl)
      T :=
    AlgebraicGeometry.isLocalization_of_isPushout_commRingCat _ _ _ _ h2 _ hF
  have := isLocalization_fibreRing (C := C) 𝔭 Q
  let ε : F ≃ₐ[A] fibreField Q :=
    IsLocalization.algEquiv (Q.1.comap (algebraMap A Aₚ)).primeCompl _ _
  let ε' : T ≃ₐ[C] fibreRing (D := Cₚ) Q :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid C (Q.1.comap (algebraMap A Aₚ)).primeCompl)
      _ _
  have hε : ∀ a, ε (b a) = algebraMap A (fibreField Q) a := ε.commutes
  have hε' : ∀ x, ε' (c x) = algebraMap C (fibreRing (D := Cₚ) Q) x := ε'.commutes
  refine ⟨ε.toRingEquiv, ε'.toRingEquiv, hε, hε', ?_⟩
  refine h1.of_iso (Iso.refl _) ε.toRingEquiv.toCommRingCatIso (Iso.refl _)
    ε'.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · ext1
    refine IsLocalization.ringHom_ext (Q.1.comap (algebraMap A Aₚ)).primeCompl (S := F) ?_
    ext a
    have hw := congrArg (fun f => f.hom a) h2.w
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hw
    show ε' (dF (b a)) =
      algebraMap (fibreField Q) (fibreRing (D := Cₚ) Q) (ε (b a))
    rw [← hw, hε', hε, algebraMap_fibreField_fibreRing_algebraMap]
  · rfl

omit [𝔭.IsPrime] in
/-- Reading a fraction of `A` in the field `O_Q` through any model `F` of `O_Q`. -/
theorem locFracO_fracMapOfLocalization_eq [𝔭.IsPrime] [IsReduced A] (Q : minimalPrimes Aₚ)
    {F : Type u} [CommRing F] (b : A →+* F) (ε : F ≃+* fibreField Q)
    (hε : ∀ a, ε (b a) = algebraMap A (fibreField Q) a) (ρ : FractionRing A →+* F)
    (hρ : ∀ a, ρ (algebraMap A (FractionRing A) a) = b a) (z : FractionRing A) :
    locFracO Q (fracMapOfLocalization 𝔭.primeCompl Aₚ z) = ε (ρ z) := by
  have h : (locFracO Q).comp (fracMapOfLocalization 𝔭.primeCompl Aₚ) = ε.toRingHom.comp ρ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [IsLocalization.map_eq, locFracO_algebraMap, hρ, hε]
    exact (IsScalarTower.algebraMap_apply A Aₚ (fibreField Q) a).symm
  exact RingHom.congr_fun h z

omit [𝔭.IsPrime] in
/-- **A model `T` of the generic fibre `D_Q` receives the total ring of fractions of `C`**,
compatibly with the reading `Q(C) → Q(C_𝔭) → D_Q`. -/
theorem exists_ringHom_fractionRing_of_ringEquiv_fibreRing [𝔭.IsPrime] [Module.Finite A C]
    [IsNoetherianRing A] [IsNoetherianRing C] [IsReduced A] [IsReduced C]
    (htf : ∀ P ∈ minimalPrimes C, P.comap (algebraMap A C) ∈ minimalPrimes A)
    (Q : minimalPrimes Aₚ) [Ring.KrullDimLE 1 Cₚ] {T : Type u} [CommRing T] (c : C →+* T)
    (ε' : T ≃+* fibreRing (D := Cₚ) Q)
    (hε' : ∀ x, ε' (c x) = algebraMap C (fibreRing (D := Cₚ) Q) x) :
    ∃ ρ : FractionRing C →+* T, (∀ x, ρ (algebraMap C (FractionRing C) x) = c x) ∧
      ∀ z, locFracD (comap_mem_minimalPrimes_localization 𝔭 htf) Q
        (fracMapOfLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) Cₚ z) = ε' (ρ z) := by
  refine ⟨ε'.symm.toRingHom.comp ((locFracD (comap_mem_minimalPrimes_localization 𝔭 htf) Q).comp
    (fracMapOfLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) Cₚ)), fun x => ?_,
    fun z => ?_⟩
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [IsLocalization.map_eq, locFracD_algebraMap, ← IsScalarTower.algebraMap_apply, ← hε',
      RingEquiv.symm_apply_apply]
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply]

end FibreData

end Stacks.NormBranches

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism into an affine object of the site factors through the spectrum of its total ring
of fractions as soon as the nonzerodivisors become units.** Given `ρ : Q(Γ(U)) → Γ(G)` extending
`u^*`, the morphism `G ⟶ U` factors through `Spec Q(Γ(U)) ⟶ U` by a morphism of the site whose
pullback on global sections is `ρ`. -/
theorem exists_hom_totalFractionObject {G U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj G)] [IsAffine U.left.1] (u : G ⟶ U)
    (ρ : FractionRing Γ(U.left.1, ⊤) →+* Γ((BigFppfOver.toScheme B S hS).obj G, ⊤))
    (hρ : ∀ c : Γ(U.left.1, ⊤),
      ρ (algebraMap _ _ c) = ((BigFppfOver.toScheme B S hS).map u).appTop c) :
    ∃ k : G ⟶ totalFractionObject B S hS U, k ≫ totalFractionObjectMap B S hS U = u ∧
      ∀ y, ((BigFppfOver.toScheme B S hS).map k).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).inv y) = ρ y := by
  let ρc : CommRingCat.of (FractionRing Γ(U.left.1, ⊤)) ⟶
      Γ((BigFppfOver.toScheme B S hS).obj G, ⊤) := CommRingCat.ofHom ρ
  let kₛ : (BigFppfOver.toScheme B S hS).obj G ⟶
      Spec (CommRingCat.of (FractionRing Γ(U.left.1, ⊤))) :=
    ((BigFppfOver.toScheme B S hS).obj G).toSpecΓ ≫ Spec.map ρc
  have happ : ∀ y, kₛ.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).inv y) = ρ y := by
    intro y
    have h1 : kₛ.appTop =
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).hom ≫ ρc := by
      simp only [kₛ, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
      exact Scheme.ΓSpecIso_naturality ρc
    rw [h1, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  have hcomp : kₛ ≫ U.left.1.fromSpecTotalFractionRing = (BigFppfOver.toScheme B S hS).map u := by
    refine ext_of_isAffine ?_
    ext c
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    have h3 : U.left.1.fromSpecTotalFractionRing.appTop c =
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).inv
          (algebraMap Γ(U.left.1, ⊤) (FractionRing Γ(U.left.1, ⊤)) c) := by
      rw [← ΓSpecIso_hom_fromSpecTotalFractionRing_appTop U.left.1 c, Iso.hom_inv_id_apply]
    rw [h3, happ, hρ]
  have hw' : kₛ ≫ B.inclusion.map (totalFractionObject B S hS U).hom =
      B.inclusion.map G.hom := by
    have hu : B.inclusion.map (u.left ≫ U.hom) = B.inclusion.map G.hom := by rw [Over.w u]
    rw [Functor.map_comp] at hu
    refine Eq.trans ?_ hu
    have ht : B.inclusion.map (totalFractionObject B S hS U).hom =
        U.left.1.fromSpecTotalFractionRing ≫ B.inclusion.map U.hom := rfl
    rw [ht, ← Category.assoc, hcomp]
    rfl
  obtain ⟨k, hk⟩ := exists_siteHom_toScheme_map_eq B S hS (A := G)
    (A' := totalFractionObject B S hS U) kₛ hw'
  refine ⟨k, ?_, fun y => by rw [hk]; exact happ y⟩
  apply (BigFppfOver.toScheme B S hS).map_injective
  rwa [Functor.map_comp, hk, toScheme_map_totalFractionObjectMap]

attribute [local instance] pointTopology

section Chart

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    {p : X ⟶ Y} (d : ChartDiagram D.site D.base D.base_mem X Y p)

attribute [local instance] chartRingAlgebra

variable [IsAffine d.U.obj.left.left.1] [IsAffine d.V.obj.left.left.1]
  [IsReduced d.U.obj.left.left.1] [IsReduced d.V.obj.left.left.1]
  [IsLocallyNoetherian d.U.obj.left.left.1] [IsLocallyNoetherian d.V.obj.left.left.1]

/-- The generic fibre `U ×_V Spec κ(w)` of an affine chart is affine. -/
theorem isAffine_toScheme_chartGenericFibre (w : chartScheme d.V) :
    IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj (chartGenericFibre D d w)) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme D.site D.base D.base_mem) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  exact @IsAffine.of_isIso _ _
    (PreservesPullback.iso (BigFppfOver.toScheme D.site D.base D.base_mem)
      d.g (fibreChartFieldPoint D d w).siteHom).hom inferInstance
    (@Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _ _ _ _
      ‹IsAffine d.U.obj.left.left.1›
      (inferInstanceAs (IsAffine (Spec (CommRingCat.of _)))) ‹IsAffine d.V.obj.left.left.1›)

/-- **The reading of `R(Y)` in the field `O_Q` at a minimal prime of `Γ(V)_𝔭`**, through any
identification `κ(w) ≃ O_Q` over `Γ(V)` at the generic point `w` of `V` cut out by `Q`. -/
theorem locFracO_rationalFunctionsToTotalFractionRing_eq (𝔭 : Ideal Γ(chartScheme d.V, ⊤))
    [𝔭.IsPrime] [_root_.IsReduced Γ(chartScheme d.V, ⊤)]
    (Q : minimalPrimes (Localization.AtPrime 𝔭))
    (w : chartScheme d.V) (hw : IsField ((chartScheme d.V).presheaf.stalk w))
    (ε : (chartScheme d.V).residueField w ≃+* Stacks.NormBranches.fibreField Q)
    (hε : ∀ a, ε ((chartScheme d.V).Γevaluation w a) =
      algebraMap Γ(chartScheme d.V, ⊤) (Stacks.NormBranches.fibreField Q) a)
    (g : rationalFunctions D.site D.base D.base_mem hY.1) :
    Stacks.NormBranches.locFracO Q
        (Stacks.NormBranches.fracMapOfLocalization 𝔭.primeCompl (Localization.AtPrime 𝔭)
          (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hY.1 d.V.obj.left
            d.V.obj.hom ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem
              d.V.obj.hom).2 d.V.property) g)) =
      ε (Scheme.totalFractionRingToResidueField (T := d.V.obj.left.left.1) w hw
        (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hY.1 d.V.obj.left
          d.V.obj.hom ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem
            d.V.obj.hom).2 d.V.property) g)) :=
  Stacks.NormBranches.locFracO_fracMapOfLocalization_eq 𝔭 Q _ ε hε
    (Scheme.totalFractionRingToResidueField (T := d.V.obj.left.left.1) w hw)
    (fun a => Scheme.totalFractionRingToResidueField_algebraMap (T := d.V.obj.left.left.1) w hw a) _

/-- **The reading of `R(X)` in the generic fibre `D_Q` at a minimal prime of `Γ(V)_𝔭`**, through
any identification of the global sections of `U ×_V Spec κ(w)` with `D_Q` over `Γ(U)`. -/
theorem locFracD_rationalFunctionsToTotalFractionRing_eq
    [Module.Finite Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)]
    [IsNoetherianRing Γ(chartScheme d.V, ⊤)] [IsNoetherianRing Γ(chartScheme d.U, ⊤)]
    [_root_.IsReduced Γ(chartScheme d.V, ⊤)] [_root_.IsReduced Γ(chartScheme d.U, ⊤)]
    (htf : ∀ P ∈ minimalPrimes Γ(chartScheme d.U, ⊤),
      P.comap (algebraMap Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)) ∈
        minimalPrimes Γ(chartScheme d.V, ⊤))
    (𝔭 : Ideal Γ(chartScheme d.V, ⊤)) [𝔭.IsPrime] (Q : minimalPrimes (Localization.AtPrime 𝔭))
    [Ring.KrullDimLE 1 (Localization (Algebra.algebraMapSubmonoid
      Γ(chartScheme d.U, ⊤) 𝔭.primeCompl))]
    (w : chartScheme d.V)
    (r : chartGenericFibre D d w ⟶ (residueFieldRepresentative D.site D.base D.base_mem X
      hintX.2.1 (genericPoint D.site D.base D.base_mem hX.1 hintX)).1.siteObject
        D.site D.base D.base_mem X)
    (hr : yoneda.map r ≫ residueFieldMorphism D.site D.base D.base_mem X hintX.2.1
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      yoneda.map (Limits.pullback.fst d.g (fibreChartFieldPoint D d w).siteHom) ≫ d.U.1.hom)
    (ε' : Γ((BigFppfOver.toScheme D.site D.base D.base_mem).obj (chartGenericFibre D d w), ⊤) ≃+*
      Stacks.NormBranches.fibreRing (D := Localization (Algebra.algebraMapSubmonoid
        Γ(chartScheme d.U, ⊤) 𝔭.primeCompl)) Q)
    (hε' : ∀ x, ε' (((BigFppfOver.toScheme D.site D.base D.base_mem).map
        (Limits.pullback.fst d.g (fibreChartFieldPoint D d w).siteHom)).appTop x) =
      algebraMap Γ(chartScheme d.U, ⊤) (Stacks.NormBranches.fibreRing (D := Localization
        (Algebra.algebraMapSubmonoid Γ(chartScheme d.U, ⊤) 𝔭.primeCompl)) Q) x)
    (f : rationalFunctions D.site D.base D.base_mem hX.1) :
    Stacks.NormBranches.locFracD (Stacks.NormBranches.comap_mem_minimalPrimes_localization 𝔭
        htf) Q
      (Stacks.NormBranches.fracMapOfLocalization
        (Algebra.algebraMapSubmonoid Γ(chartScheme d.U, ⊤) 𝔭.primeCompl) _
        (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hX.1 d.U.obj.left
          d.U.obj.hom ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem
            d.U.obj.hom).2 d.U.property) f)) =
      ε' (((BigFppfOver.toScheme D.site D.base D.base_mem).map r).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (residueField D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX)))).inv
          (evalRingHom D.site D.base D.base_mem hX.1 hintX
            (residueFieldRepresentative D.site D.base D.base_mem X hintX.2.1
              (genericPoint D.site D.base D.base_mem hX.1 hintX)).1
            (residueFieldRepresentative D.site D.base D.base_mem X hintX.2.1 _).2.1 f))) := by
  have := isAffine_toScheme_chartGenericFibre D d w
  obtain ⟨ρ, hρ, hρread⟩ :=
    Stacks.NormBranches.exists_ringHom_fractionRing_of_ringEquiv_fibreRing
      (C := Γ(chartScheme d.U, ⊤)) 𝔭 htf Q
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map
        (Limits.pullback.fst d.g (fibreChartFieldPoint D d w).siteHom)).appTop.hom ε' hε'
  obtain ⟨k, hk1, hk2⟩ := exists_hom_totalFractionObject D.site D.base D.base_mem
    (G := chartGenericFibre D d w) (U := d.U.obj.left)
    (Limits.pullback.fst d.g (fibreChartFieldPoint D d w).siteHom) ρ hρ
  have hcomm : yoneda.map (k ≫ totalFractionObjectMap D.site D.base D.base_mem d.U.obj.left) ≫
      d.U.obj.hom = yoneda.map r ≫ fieldMorphism D.site D.base D.base_mem X
        (residueFieldRepresentative D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX)).1 := by
    rw [hk1]
    exact hr.symm
  have hread := appTop_evalRingHom_eq_appTop_rationalFunctionsToTotalFractionRing D.site D.base
    D.base_mem hX.1 hintX d.U.obj.left d.U.obj.hom ((isEtale_iff_presheaf_of_yoneda D.site
      D.base D.base_mem d.U.obj.hom).2 d.U.property) k _
    (residueFieldRepresentative D.site D.base D.base_mem X hintX.2.1
      (genericPoint D.site D.base D.base_mem hX.1 hintX)).2.1 r hcomm f
  exact (hρread _).trans (congrArg ε' ((hk2 _).symm.trans hread.symm))

/-- Pulling back global sections along the field point `Spec κ(w) ⟶ V` is evaluation at `w`. -/
theorem appTop_map_fibreChartFieldPoint_siteHom_comp_ΓSpecIso_hom (w : chartScheme d.V) :
    ((BigFppfOver.toScheme D.site D.base D.base_mem).map
      (fibreChartFieldPoint D d w).siteHom).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of ((chartScheme d.V).residueField w))).hom =
      (chartScheme d.V).Γevaluation w := by
  have hmap : (BigFppfOver.toScheme D.site D.base D.base_mem).map
      (fibreChartFieldPoint D d w).siteHom = (chartScheme d.V).fromSpecResidueField w :=
    map_siteFieldPointOfSchemeMap_value_left _ _ _ _ _ _
  rw [hmap]
  exact fromSpecResidueField_appTop w

include hintY in
/-- **The generic fibres of the chart at the minimal primes of `Γ(V)_𝔭`, as the data of the
algebraic identity `Stacks.NormBranches.ordTotalFracInt_atPrime_eq_finsum`.** -/
theorem exists_fibreData (hpB : p ≫ sY = sX) (hproper : IsProper D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY)
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      deltaDimensionClosed D sY hY Set.univ isClosed_univ)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) p d.V.1.hom)
    [Module.Finite Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)]
    [IsNoetherianRing Γ(chartScheme d.V, ⊤)] [IsNoetherianRing Γ(chartScheme d.U, ⊤)]
    [_root_.IsReduced Γ(chartScheme d.V, ⊤)] [_root_.IsReduced Γ(chartScheme d.U, ⊤)]
    (htf : ∀ P ∈ minimalPrimes Γ(chartScheme d.U, ⊤),
      P.comap (algebraMap Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)) ∈
        minimalPrimes Γ(chartScheme d.V, ⊤))
    (𝔭 : Ideal Γ(chartScheme d.V, ⊤)) [𝔭.IsPrime]
    [Ring.KrullDimLE 1 (Localization.AtPrime 𝔭)]
    (Q : minimalPrimes (Localization.AtPrime 𝔭)) :
    haveI : Ring.KrullDimLE 1 (Localization (Algebra.algebraMapSubmonoid
        Γ(chartScheme d.U, ⊤) 𝔭.primeCompl)) :=
      Stacks.Chow.krullDimLE_one_of_isIntegral (Localization.AtPrime 𝔭) _
    ∃ (κQ : residueField D.site D.base D.base_mem Y hintY.2.1
          (pointsMap D.site D.base D.base_mem X p
            (genericPoint D.site D.base D.base_mem hX.1 hintX)) →+*
          Stacks.NormBranches.fibreField Q)
      (lamQ : residueField D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX) →+*
          Stacks.NormBranches.fibreRing (D := Localization (Algebra.algebraMapSubmonoid
            Γ(chartScheme d.U, ⊤) 𝔭.primeCompl)) Q),
      IsPushout (CommRingCat.ofHom κQ) (CommRingCat.ofHom (residueFieldHom D.site D.base
          D.base_mem X Y hY.1 hintX.2.1 hintY.2.1 p
          (genericPoint D.site D.base D.base_mem hX.1 hintX)))
        (CommRingCat.ofHom (algebraMap (Stacks.NormBranches.fibreField Q)
          (Stacks.NormBranches.fibreRing (D := Localization (Algebra.algebraMapSubmonoid
            Γ(chartScheme d.U, ⊤) 𝔭.primeCompl)) Q)))
        (CommRingCat.ofHom lamQ) ∧
      (∀ g : rationalFunctions D.site D.base D.base_mem hY.1,
        Stacks.NormBranches.locFracO Q
          (Stacks.NormBranches.fracMapOfLocalization 𝔭.primeCompl (Localization.AtPrime 𝔭)
            (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hY.1 d.V.obj.left
              d.V.obj.hom ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem
                d.V.obj.hom).2 d.V.property) g)) =
          κQ (evalRingHom D.site D.base D.base_mem hY.1 hintY
            (residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1
              (pointsMap D.site D.base D.base_mem X p
                (genericPoint D.site D.base D.base_mem hX.1 hintX))).1
            ((residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1 _).2.1.trans hgen)
            g)) ∧
      (∀ f : rationalFunctions D.site D.base D.base_mem hX.1,
        Stacks.NormBranches.locFracD (Stacks.NormBranches.comap_mem_minimalPrimes_localization 𝔭
            htf) Q
          (Stacks.NormBranches.fracMapOfLocalization
            (Algebra.algebraMapSubmonoid Γ(chartScheme d.U, ⊤) 𝔭.primeCompl) _
            (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hX.1 d.U.obj.left
              d.U.obj.hom ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem
                d.U.obj.hom).2 d.U.property) f)) =
          lamQ (evalRingHom D.site D.base D.base_mem hX.1 hintX
            (residueFieldRepresentative D.site D.base D.base_mem X hintX.2.1
              (genericPoint D.site D.base D.base_mem hX.1 hintX)).1
            (residueFieldRepresentative D.site D.base D.base_mem X hintX.2.1 _).2.1 f)) := by
  have : Ring.KrullDimLE 1 (Localization (Algebra.algebraMapSubmonoid
      Γ(chartScheme d.U, ⊤) 𝔭.primeCompl)) :=
    Stacks.Chow.krullDimLE_one_of_isIntegral (Localization.AtPrime 𝔭) _
  have := Q.2.1.1
  have hVaff : IsAffine (chartScheme d.V) := ‹IsAffine d.V.obj.left.left.1›
  have hUaff : IsAffine (chartScheme d.U) := ‹IsAffine d.U.obj.left.left.1›
  have hVred : IsReduced (chartScheme d.V) := ‹IsReduced d.V.obj.left.left.1›
  -- the minimal prime `Q'` of `Γ(V)` below `Q`, and the generic point `w` of `V` it cuts out
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Ideal Γ(chartScheme d.V, ⊤),
      Q.1.comap (algebraMap _ (Localization.AtPrime 𝔭)) = Q' := ⟨_, rfl⟩
  have hQ'min : Q' ∈ minimalPrimes Γ(chartScheme d.V, ⊤) := hQ' ▸
    Stacks.MinimalPrimeResidueLocalization.under_mem_minimalPrimes _ 𝔭.primeCompl _ Q.2
  have hQ'p : Q'.IsPrime := hQ'min.1.1
  obtain ⟨x, hx⟩ := exists_primeIdealOf_eq (chartScheme d.V) ⟨Q', hQ'p⟩
  have hxQ : ((isAffineOpen_top (chartScheme d.V)).primeIdealOf x).asIdeal = Q' := by rw [hx]
  have hw : IsField ((chartScheme d.V).presheaf.stalk x.1) :=
    isField_stalk_of_mem_minimalPrimes (chartScheme d.V) x (by rwa [hxQ])
  have key := @exists_isPushout_chartGenericFibre D X Y sX hX sY hY
    hintX hintY p d ‹_› ‹_› ‹_› ‹_› hpB hproper hgen hdim hd x.1 hw
  obtain ⟨φ, key⟩ := key
  obtain ⟨r, hP1, hP2, hr, hφread⟩ := key
  -- the field `κ(w)` as the localization of `Γ(V)` at `Q'`
  rw [appTop_map_fibreChartFieldPoint_siteHom_comp_ΓSpecIso_hom D d x.1] at hP2
  have hcongr : ∀ {S : Type u} [CommRing S] [Algebra Γ(chartScheme d.V, ⊤) S]
      (I J : Ideal Γ(chartScheme d.V, ⊤)) [I.IsPrime] [J.IsPrime], I = J →
        IsLocalization I.primeCompl S → IsLocalization J.primeCompl S := by
    rintro S _ _ I J _ _ rfl h
    exact h
  have hF : let := ((chartScheme d.V).Γevaluation x.1).hom.toAlgebra
      IsLocalization (Q.1.comap (algebraMap _ (Localization.AtPrime 𝔭))).primeCompl
        ((chartScheme d.V).residueField x.1) :=
    let := ((chartScheme d.V).Γevaluation x.1).hom.toAlgebra
    hcongr _ _ (hxQ.trans hQ'.symm)
      (isLocalization_residueField_of_isField (chartScheme d.V) x hw)
  have key := Stacks.NormBranches.exists_ringEquiv_fibre_of_isPushout
    (C := Γ(chartScheme d.U, ⊤)) 𝔭 Q ((chartScheme d.V).Γevaluation x.1).hom hF
    ((BigFppfOver.toScheme D.site D.base D.base_mem).map
      (Limits.pullback.fst d.g (fibreChartFieldPoint D d x.1).siteHom)).appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of ((chartScheme d.V).residueField x.1))).inv ≫
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map
        (Limits.pullback.snd d.g (fibreChartFieldPoint D d x.1).siteHom)).appTop).hom
    hP2 φ (residueFieldHom D.site D.base D.base_mem X Y hY.1 hintX.2.1 hintY.2.1 p
      (genericPoint D.site D.base D.base_mem hX.1 hintX))
    ((Scheme.ΓSpecIso (CommRingCat.of (residueField D.site D.base D.base_mem X hintX.2.1
        (genericPoint D.site D.base D.base_mem hX.1 hintX)))).inv ≫
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map r).appTop).hom hP1
  obtain ⟨ε, key⟩ := key
  obtain ⟨ε', hε, hε', hpush⟩ := key
  exact ⟨ε.toRingHom.comp φ, ε'.toRingHom.comp _, hpush,
    fun g => (locFracO_rationalFunctionsToTotalFractionRing_eq D sY hY d 𝔭 Q x.1 hw ε hε
      g).trans (congrArg ε (hφread g).symm),
    fun f => locFracD_rationalFunctionsToTotalFractionRing_eq D sX hX hintX d htf 𝔭 Q x.1 r hr
      ε' hε' f⟩

end Chart

end Space

end AlgebraicGeometry

end
