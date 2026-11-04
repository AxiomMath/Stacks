module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocalContractionStage
public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocalContractionCompleteSite
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessNoetherianLocal
public import StacksFrontier.RingTheory.Smoothing.ApproximationGRingEtale
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.BaseChangeStageApproximation
public import StacksFrontier.RingTheory.Dualizing.RelativeHomothetyColimit

/-!
# Extending a contraction of a fibre étale locally on a Noetherian base

Let `R` be a Noetherian ring and `𝔭 ⊂ R` a prime such that `R_𝔭` is a G-ring, and let
`f : X ⟶ Spec R` be a flat proper algebraic space of finite presentation over `Spec R` (in a big
fppf site). Let `k : Spec K ⟶ Spec R` be the point `𝔭` with `K ≅ κ(𝔭)`, let the fibre of `X` over
`k` be presented by a scheme `F` of dimension at most one, and let `h₀ : F ⟶ Y₀` be a morphism over
`K` to a proper scheme of dimension at most one with `𝒪_{Y₀} ≅ h₀,*𝒪_F` and `R¹h₀,*𝒪_F = 0`. Then
there are an étale `e : U ⟶ Spec R` through which `k` factors, a family of curves `Y ⟶ U` and a
morphism `h : X_U ⟶ Y` over `U` whose fibre over the point of `U` is `h₀`.

This is the Noetherian case of the proof of [Stacks, Tag 0E7C]. The Stacks proof passes to the
henselization `𝒪^h_{S,s}`, which is a G-ring, and approximates by Smoothing Ring Maps, Theorem
07QY; here the approximation is Stacks 0CAU over `R` directly
(`StacksDraft.ArtinApproximation.exists_etaleApproximation`, with Stacks 0CAR given by
`StacksDraft.ArtinApproximation.artinApproximationGRing`), which produces the étale neighbourhood
at once:

* over the completion `Λ = (R_𝔭)^∧` the contraction extends, by the complete case
  (`AlgebraicGeometry.EtaleLocalContraction.exists_contraction_of_isAdicComplete_of_siteObject`);
* `Λ` is the filtered colimit of its finitely generated `R`-subalgebras `C`, so the family of
  curves and the morphism over `Λ` descend to some `C`
  (`AlgebraicGeometry.Space.exists_stage_family_hom`, [Stacks, Tags 07SK, 08K0, 08K1, 0D4K]);
* the inclusion `C ⟶ Λ` is approximated by an `R`-algebra map `C ⟶ A'` to an étale `R`-algebra
  `A'` at a prime `𝔭'` over `𝔭` with the same residue field, inducing the same map
  `C ⟶ κ(𝔭)` (0CAU), and the base change along `Spec A' ⟶ Spec C` is the answer.

## Main definitions

* `AlgebraicGeometry.EtaleLocalContraction.HasEtaleLocalExtension`: the conclusion of
  [Stacks, Tag 0E7C] for a space over an object of the site, at a point.

## Main results

* `AlgebraicGeometry.EtaleLocalContraction.residue_toCarrier_eq`: the approximating map induces
  the same map to the residue field.
* `AlgebraicGeometry.EtaleLocalContraction.hasEtaleLocalExtension_of_isNoetherianRing`: the
  statement above.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 0CAU](https://stacks.math.columbia.edu/tag/0CAU)
* [Stacks Project, Tag 07QY](https://stacks.math.columbia.edu/tag/07QY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite StacksDraft.ArtinApproximation

universe u

namespace AlgebraicGeometry.EtaleLocalContraction

/-! ### The residue field of the approximation -/

section Residue

variable {R C : Type u} [CommRing R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
  {𝔭 : Ideal R} [𝔭.IsPrime] {q : Ideal C} [q.IsPrime]
  {φ : Localization.AtPrime q →+* Completion 𝔭}

/-- The comparison of completions along an étale extension is a local homomorphism. -/
theorem isLocalHom_completionComparison {A : Type u} [CommRing A] (g : R →+* A) (𝔭' : Ideal A)
    [𝔭'.IsPrime] (h : 𝔭 = 𝔭'.comap g) [IsNoetherianRing (Localization.AtPrime 𝔭')] :
    IsLocalHom (completionComparison 𝔭 𝔭' g h) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  exact (mem_maximalIdeal _).mp (completionComparison_mem_maximalIdeal 𝔭 𝔭' g h
    ((mem_maximalIdeal _).mpr hna)) ha

/-- The residue field equivalence of a Noetherian local ring sends `residue y` to the residue of
the image of `y` in the completion. -/
private theorem completionResidueFieldEquiv_residue {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (y : A) :
    Space.completionResidueFieldEquiv A (residue A y) =
      residue (AdicCompletion (maximalIdeal A) A) (algebraMap A _ y) :=
  ResidueField.map_residue _ y

/-- **The approximating map induces the same map to the residue field.** For an approximation `E`
to first order of `φ : C_𝔮 ⟶ (R_𝔭)^∧` by `C ⟶ A'` (Stacks 0CAU), the two maps `C ⟶ κ(𝔭)` — through
`φ` and the residue field of the completion, and through `A'` and its residue field at `𝔭'`,
identified with `κ(𝔭)` — agree. -/
theorem residue_toCarrier_eq (E : EtaleApproximation R R C 𝔭 q 1 φ)
    [IsNoetherianRing (Localization.AtPrime E.prime)] (x : C) :
    (Space.completionResidueFieldEquiv (Localization.AtPrime 𝔭)).symm
        (residue _ (φ (algebraMap C (Localization.AtPrime q) x))) =
      (RingEquiv.ofBijective _ E.residueField_bijective).symm
        (residue (Localization.AtPrime E.prime)
          (algebraMap E.carrier (Localization.AtPrime E.prime) (E.toCarrier x))) := by
  set Λ := Localization.AtPrime 𝔭
  set Λ' := Localization.AtPrime E.prime
  set e₁ := Space.completionResidueFieldEquiv Λ
  set e₂ := Space.completionResidueFieldEquiv Λ'
  set β := RingEquiv.ofBijective _ E.residueField_bijective
  set Γ := completionComparison 𝔭 E.prime (algebraMap R E.carrier) E.comap_prime
  have := isLocalHom_completionComparison (algebraMap R E.carrier) E.prime E.comap_prime
  -- the residue map of the comparison
  have hΓ : ∀ w : Completion 𝔭, residue (Completion E.prime) (Γ w) =
      e₂ (β (e₁.symm (residue (Completion 𝔭) w))) := by
    intro w
    rw [← ResidueField.map_residue Γ w]
    obtain ⟨y, hy⟩ := e₁.surjective (residue (Completion 𝔭) w)
    rw [← hy, RingEquiv.symm_apply_apply]
    obtain ⟨y, rfl⟩ := residue_surjective y
    rw [completionResidueFieldEquiv_residue y, ResidueField.map_residue,
      completionComparison_ofLocalization,
      ← completionResidueFieldEquiv_residue (Localization.localRingHom 𝔭 E.prime
        (algebraMap R E.carrier) E.comap_prime y)]
    rfl
  -- the agreement modulo the maximal ideal
  have hagree := E.agree (algebraMap C (Localization.AtPrime q) x)
  have hmem : completionIdeal E.prime 1 ≤ maximalIdeal (Completion E.prime) := by
    unfold completionIdeal
    rw [pow_one, AdicCompletion.maximalIdeal_eq_map]
  have hres : residue (Completion E.prime) (Γ (φ (algebraMap C (Localization.AtPrime q) x))) =
      residue (Completion E.prime) (ofLocalization E.prime
        (Localization.localRingHom q E.prime E.toCarrier E.comap_toCarrier
          (algebraMap C (Localization.AtPrime q) x))) :=
    Ideal.Quotient.eq.mpr (hmem hagree)
  rw [Localization.localRingHom_to_map, hΓ] at hres
  rw [← completionResidueFieldEquiv_residue] at hres
  rw [← e₂.injective hres, RingEquiv.symm_apply_apply]

end Residue

/-! ### The conclusion of the tag -/

section Statement

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **The conclusion of [Stacks, Tag 0E7C]** for an algebraic space `f : X ⟶ T` over an object of
the big fppf site of the integers, at a point `k : K ⟶ T` at which the fibre of `X` is presented by
`tX : F ⟶ K` (through `iX`), for a morphism `h₀ : F ⟶ Y₀` over `K`: there are an étale
`e : U ⟶ T` through which `k` factors as `ū ≫ e`, a flat proper morphism `g : Y ⟶ U` of finite
presentation and relative dimension at most one, and a morphism `h : X_U ⟶ Y` over `U` from the
base change `X_U` of `X`, such that the fibre of `Y` over `ū` is presented by `tG : G ⟶ K` with
`G ≅ Y₀` over `K` and the fibre of `h` over `ū` is `h₀` (through this identification and the
presentation `F` of the fibre of `X_U`). -/
def HasEtaleLocalExtension {T K F : BigFppfOver B integerBase hZ}
    {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T) (k : K ⟶ T)
    (tX : F ⟶ K) (iX : yoneda.obj F ⟶ X) {Y₀ : Scheme.{u}} (pY₀ : Y₀ ⟶ (𝒯).obj K)
    (h₀ : (𝒯).obj F ⟶ Y₀) : Prop :=
  ∃ (U : BigFppfOver B integerBase hZ) (e : U ⟶ T) (ū : K ⟶ U), Etale ((𝒯).map e) ∧ ū ≫ e = k ∧
    ∃ (Y XU : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) (g : Y ⟶ yoneda.obj U)
      (pXU : XU ⟶ X) (fXU : XU ⟶ yoneda.obj U) (h : XU ⟶ Y),
      IsAlgebraicSpace B integerBase hZ Y ∧ IsAlgebraicSpace B integerBase hZ XU ∧
      Space.IsFlat B integerBase hZ g ∧ Space.IsProper B integerBase hZ g ∧
      Space.IsFinitePresentation B integerBase hZ g ∧
      Space.HasRelativeDimensionLE 1 B integerBase hZ g ∧
      IsPullback pXU fXU f (yoneda.map e) ∧ h ≫ g = fXU ∧
      ∃ (iXU : yoneda.obj F ⟶ XU) (G : BigFppfOver B integerBase hZ) (tG : G ⟶ K)
        (iG : yoneda.obj G ⟶ Y) (φ : (𝒯).obj G ≅ Y₀) (a : F ⟶ G),
        IsPullback iXU (yoneda.map tX) fXU (yoneda.map ū) ∧ iXU ≫ pXU = iX ∧
        IsPullback iG (yoneda.map tG) g (yoneda.map ū) ∧ φ.hom ≫ pY₀ = (𝒯).map tG ∧
        a ≫ tG = tX ∧ iXU ≫ h = yoneda.map a ≫ iG ∧ (𝒯).map a ≫ φ.hom = h₀

end Statement

/-! ### The Noetherian case -/

section Noetherian

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

variable (B) in
/-- The spectrum of a localization of a ring whose spectrum is in the site is in the site. -/
theorem contains_spec_localization {R : Type u} [CommRing R] (hR : B.Contains (Spec (.of R)))
    (M : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization M L] :
    B.Contains (Spec (.of L)) := by
  show (Spec (.of L)).size < B.cutoff
  have h : (Spec (.of R)).size < B.cutoff := hR
  rw [Scheme.size_Spec] at h ⊢
  exact lt_of_le_of_lt (max_le_max le_rfl (IsLocalization.cardinalMk_le (L := L) M)) h

variable (B) in
/-- The spectrum of a finite type algebra over a ring whose spectrum is in the site is in the
site. -/
theorem contains_spec_of_finiteType {R : Type u} [CommRing R] (hR : B.Contains (Spec (.of R)))
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    B.Contains (Spec (.of A)) := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) hR

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **[Stacks, Tag 0E7C] over a Noetherian base whose local ring at the point is a G-ring.** Let
`R` be a Noetherian ring, `𝔭 ⊂ R` a prime with `R_𝔭` a G-ring and `ψ : κ(𝔭) ≅ K`, and let
`k : Spec K ⟶ Spec R` be the corresponding point. Let `f : X ⟶ Spec R` be a flat proper algebraic
space of finite presentation whose fibre over `k` is presented by `tX : F ⟶ Spec K` with
`dim F ≤ 1`, and let `h₀ : F ⟶ Y₀` be a morphism over `K` to a proper scheme of dimension at most
one with `𝒪_{Y₀} ≅ h₀,*𝒪_F` and `R¹h₀,*𝒪_F = 0`. Then the conclusion of the tag holds at `k`. -/
theorem hasEtaleLocalExtension_of_isNoetherianRing (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : B.Contains (Spec (.of R))) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hG : IsGRing (Localization.AtPrime 𝔭)) (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (ψ : 𝔭.ResidueField ≃+* K)
    {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B integerBase hZ X)
    (f : X ⟶ yoneda.obj (integerSiteObject B hZ hR)) (hfl : Space.IsFlat B integerBase hZ f)
    (hpr : Space.IsProper B integerBase hZ f) (hfp : Space.IsFinitePresentation B integerBase hZ f)
    {F : BigFppfOver B integerBase hZ} (tX : F ⟶ integerSiteObject B hZ hK)
    (iX : yoneda.obj F ⟶ X)
    (hiX : IsPullback iX (yoneda.map tX) f (yoneda.map (integerSiteMap B hZ hK hR
      (Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (algebraMap R 𝔭.ResidueField)))))))
    (hdimF : topologicalKrullDim ((𝒯).obj F) ≤ 1)
    {Y₀ : Scheme.{u}} (pY₀ : Y₀ ⟶ Spec (.of K)) [IsProper pY₀]
    (hdimY : topologicalKrullDim Y₀ ≤ 1) (h₀ : (𝒯).obj F ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = (𝒯).map tX)
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR1 : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit ((𝒯).obj F).ringCatSheaf))) :
    HasEtaleLocalExtension f (integerSiteMap B hZ hK hR
      (Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (algebraMap R 𝔭.ResidueField)))))
      tX iX pY₀ h₀ := by
  classical
  -- the completion `Λc` of the local ring `Λ = R_𝔭`
  have : IsNoetherianRing (Localization.AtPrime 𝔭) :=
    IsLocalization.isNoetherianRing 𝔭.primeCompl _ inferInstance
  obtain ⟨hNc, -, -, hcc, -⟩ :=
    AdicCompletion.noetherian_completeLocal_faithfullyFlat (Localization.AtPrime 𝔭)
  have : IsNoetherianRing (Completion 𝔭) := hNc
  have : IsAdicComplete (maximalIdeal (Completion 𝔭)) (Completion 𝔭) := hcc
  have hΛ : B.Contains (Spec (.of (Localization.AtPrime 𝔭))) :=
    contains_spec_localization B hR 𝔭.primeCompl _
  have hΛc : B.Contains (Spec (.of (Completion 𝔭))) := B.contains_spec_adicCompletion hΛ _
  let κR : R →+* K := ψ.toRingHom.comp (algebraMap R 𝔭.ResidueField)
  let w : integerSiteObject B hZ hΛc ⟶ integerSiteObject B hZ hR :=
    integerSiteMap B hZ hΛc hR (Spec.map (CommRingCat.ofHom (toCompletion 𝔭)))
  -- the closed point of `W`, over `k`
  let e₁ := Space.completionResidueFieldEquiv (Localization.AtPrime 𝔭)
  let ψc : ResidueField (Completion 𝔭) ≃+* K := e₁.symm.trans ψ
  let κW : Completion 𝔭 →+* K := ψc.toRingHom.comp (residue (Completion 𝔭))
  let kW : integerSiteObject B hZ hK ⟶ integerSiteObject B hZ hΛc :=
    integerSiteMap B hZ hK hΛc (Spec.map (CommRingCat.ofHom κW))
  have hκW : κW.comp (toCompletion 𝔭) = κR := by
    ext r
    have h := RingHom.congr_fun
      (Space.completionResidueFieldEquiv_residue_algebraMap (Localization.AtPrime 𝔭))
      (algebraMap R (Localization.AtPrime 𝔭) r)
    exact congrArg ψ h
  have hkW : kW ≫ w = integerSiteMap B hZ hK hR (Spec.map (CommRingCat.ofHom κR)) := by
    rw [integerSiteMap_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hκW]
  let ι : Spec (.of (ResidueField (Completion 𝔭))) ≅ (𝒯).obj (integerSiteObject B hZ hK) :=
    Scheme.Spec.mapIso ψc.symm.toCommRingCatIso.op
  have hιhom : ι.hom = Spec.map (CommRingCat.ofHom ψc.symm.toRingHom) := rfl
  have hkWmap : (𝒯).map kW = Spec.map (CommRingCat.ofHom κW) := rfl
  have hι : ι.hom ≫ (𝒯).map kW ≫ (Iso.refl ((𝒯).obj (integerSiteObject B hZ hΛc))).hom =
      ContractionUniquenessComplete.closedPoint (Completion 𝔭) := by
    have key : Spec.map (CommRingCat.ofHom ψc.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom κW) =
          ContractionUniquenessComplete.closedPoint (Completion 𝔭) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      simp [κW]
    simp only [Iso.refl_hom, Category.comp_id]
    exact key
  -- the base change `P` of `X` to `W`, and the presentation of its closed fibre
  have hWa := isAlgebraicSpace_yoneda B integerBase hZ (integerSiteObject B hZ hΛc)
  have hTa := isAlgebraicSpace_yoneda B integerBase hZ (integerSiteObject B hZ hR)
  have hP := isAlgebraicSpace_pullback B integerBase hZ f (yoneda.map w) hX hWa hTa
  obtain ⟨hflP, hprP, -⟩ := Space.isFlat_isProper_isFinitePresentation_of_isPullback B
    integerBase hZ (IsPullback.of_hasPullback f (yoneda.map w)) hX hP hfl hpr hfp
  have hkW' : yoneda.map kW ≫ yoneda.map w =
      yoneda.map (integerSiteMap B hZ hK hR (Spec.map (CommRingCat.ofHom κR))) := by
    rw [← Functor.map_comp, hkW]
  have hiP := Space.isPullback_lift_of_isPullback_of_fac B integerBase hZ hiX (yoneda.map kW)
    (yoneda.map w) hkW'
  -- the complete case over `W`
  let pY₀' : Y₀ ⟶ (𝒯).obj (integerSiteObject B hZ hK) := pY₀
  have : IsProper pY₀' := ‹IsProper pY₀›
  obtain ⟨Q, q, c, hprq, hflq, hfpq, hdq, hcq, G, tG, iG, φ, a, hiG, hφ, hat, hia, ha⟩ :=
    exists_contraction_of_isAdicComplete_of_siteObject B integerBase hZ (Completion 𝔭)
      (integerSiteObject B hZ hΛc) (Iso.refl _) hP (pullback.snd f (yoneda.map w)) hprP hflP kW ι
      hι tX _ hiP hdimF pY₀' hdimY h₀ hh₀ h0 hR1
  -- the completion as the limit of the spectra of its finitely generated `R`-subalgebras
  let Fg := forget₂ (CommAlgCat.{u} R) CommRingCat.{u}
  let cc := Fg.mapCocone (Dualizing.fgSubalgebraCocone R (Completion 𝔭))
  have hρ : IsColimit cc :=
    isColimitOfPreserves Fg (Dualizing.fgSubalgebraCoconeIsColimit R (Completion 𝔭))
  let Rd := Dualizing.fgSubalgebraDiagram R (Completion 𝔭) ⋙ Fg
  have hft : ∀ i : Dualizing.FGSubalgebra R (Completion 𝔭), Algebra.FiniteType R i.1 :=
    fun i => (Subalgebra.fg_iff_finiteType _).mp i.2
  have hRd : ∀ i, B.Contains (Spec (Rd.obj i)) := fun i => by
    have := hft i
    exact contains_spec_of_finiteType B hR i.1
  let ε : (𝒯).obj (integerSiteObject B hZ hΛc) ≅ Spec cc.pt := Iso.refl _
  let D := Space.specStageDiagram (hZ := hZ) Rd hRd
  let cn := Space.specStageCone Rd hRd cc.ι ε
  have hcn : IsLimit ((𝒯).mapCone cn) := Space.isLimitSpecStageCone Rd hRd cc.ι hρ ε
  have hD : ∀ j, IsAffine ((𝒯).obj (D.obj j)) := fun j =>
    inferInstanceAs (IsAffine (Spec (Rd.obj j.unop)))
  let τ : ∀ j, D.obj j ⟶ integerSiteObject B hZ hR := fun j =>
    integerSiteMap B hZ (hRd j.unop) hR (Spec.map (CommRingCat.ofHom (algebraMap R j.unop.1)))
  have hτ : ∀ {i j : (Dualizing.FGSubalgebra R (Completion 𝔭))ᵒᵖ} (e : i ⟶ j),
      D.map e ≫ τ j = τ i := by
    intro i j e
    refine (integerSiteMap_comp _ _).trans ?_
    congr 1
    rw [← Spec.map_comp]
    congr 1
  have hw : ∀ j, cn.π.app j ≫ τ j = w := by
    intro j
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show (𝟙 _ ≫ Spec.map (cc.ι.app j.unop)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R j.unop.1)) =
        Spec.map (CommRingCat.ofHom (toCompletion 𝔭))
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1
  -- the family and the morphism at a stage
  let l : Dualizing.FGSubalgebra R (Completion 𝔭) := ⟨⊥, Subalgebra.fg_bot⟩
  have sqP : IsPullback (pullback.fst f (yoneda.map w)) (pullback.snd f (yoneda.map w)) f
      (yoneda.map (cn.π.app (op l) ≫ τ (op l))) := by
    convert IsPullback.of_hasPullback f (yoneda.map w) using 2
    exact hw (op l)
  obtain ⟨M, XM, YM, fM, gM, pM, qXM, qYM, cM, hXM, hYM, sqXM, hflM, hprM, hfpM, hdM, hcM,
      sqqXM, hqXMp, sqqYM, hcomp⟩ :=
    Space.exists_stage_family_hom D hD cn hcn τ hτ hX hP
      (isAlgebraicSpace_yoneda B integerBase hZ Q) f hfp (pullback.snd f (yoneda.map w))
      (pullback.fst f (yoneda.map w)) l sqP (yoneda.map q) hflq hprq hfpq hdq c hcq
  let πM : integerSiteObject B hZ hΛc ⟶ D.obj M := cn.π.app M
  have sqqXM' : IsPullback qXM (pullback.snd f (yoneda.map w)) fM (yoneda.map πM) := sqqXM
  have sqqYM' : IsPullback qYM (yoneda.map q) gM (yoneda.map πM) := sqqYM
  -- the approximation of the inclusion of the stage into the completion (Stacks 0CAU)
  have := hft M.unop
  let ρ' : M.unop.1 →+* Completion 𝔭 := M.unop.1.val.toRingHom
  have hρ' : ρ'.comp (algebraMap R M.unop.1) = toCompletion 𝔭 :=
    RingHom.ext fun r => M.unop.1.val.commutes r
  obtain ⟨q', hq', -, φa, hφa, ⟨E⟩⟩ :=
    exists_etaleApproximation_of_ringHom_completion 𝔭 hG 1 le_rfl ρ' hρ'
  have : Algebra.FiniteType R E.carrier := inferInstance
  have : IsNoetherianRing E.carrier := Algebra.FiniteType.isNoetherianRing R E.carrier
  have : IsNoetherianRing (Localization.AtPrime E.prime) :=
    IsLocalization.isNoetherianRing E.prime.primeCompl _ inferInstance
  have hU : B.Contains (Spec (.of E.carrier)) := contains_spec_of_finiteType B hR E.carrier
  let U := integerSiteObject B hZ hU
  let e : U ⟶ integerSiteObject B hZ hR :=
    integerSiteMap B hZ hU hR (Spec.map (CommRingCat.ofHom (algebraMap R E.carrier)))
  have he : Etale ((𝒯).map e) := E.etale_specToBase
  let β := RingEquiv.ofBijective _ E.residueField_bijective
  let κU : E.carrier →+* K := ψ.toRingHom.comp (β.symm.toRingHom.comp
    ((residue (Localization.AtPrime E.prime)).comp
      (algebraMap E.carrier (Localization.AtPrime E.prime))))
  let ū : integerSiteObject B hZ hK ⟶ U :=
    integerSiteMap B hZ hK hU (Spec.map (CommRingCat.ofHom κU))
  have hū : ū ≫ e = integerSiteMap B hZ hK hR (Spec.map (CommRingCat.ofHom κR)) := by
    rw [integerSiteMap_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext r
    show ψ (β.symm (algebraMap E.carrier E.prime.ResidueField (algebraMap R E.carrier r))) =
      ψ (algebraMap R 𝔭.ResidueField r)
    congr 1
    rw [RingEquiv.symm_apply_eq]
    exact (Ideal.ResidueField.map_algebraMap 𝔭 E.prime (algebraMap R E.carrier) E.comap_prime
      r).symm
  let σ : U ⟶ D.obj M :=
    integerSiteMap B hZ hU (hRd M.unop) (Spec.map (CommRingCat.ofHom E.toCarrier))
  have hσring : Spec.map (CommRingCat.ofHom E.toCarrier) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R M.unop.1)) =
        Spec.map (CommRingCat.ofHom (algebraMap R E.carrier)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact E.toCarrier_base
  have hσ : σ ≫ τ M = e := (integerSiteMap_comp _ _).trans (congrArg _ hσring)
  have hring : (CommRingCat.ofHom E.toCarrier ≫ CommRingCat.ofHom κU :
      CommRingCat.of M.unop.1 ⟶ CommRingCat.of K) =
        CommRingCat.ofHom ρ' ≫ CommRingCat.ofHom κW := by
    ext x
    have h := residue_toCarrier_eq E x
    rw [hφa] at h
    show ψ (β.symm _) = ψ (e₁.symm (residue (Completion 𝔭) (ρ' x)))
    rw [h]
    rfl
  have hkeyS : Spec.map (CommRingCat.ofHom κU) ≫ Spec.map (CommRingCat.ofHom E.toCarrier) =
      Spec.map (CommRingCat.ofHom κW) ≫ Spec.map (CommRingCat.ofHom ρ') := by
    rw [← Spec.map_comp, ← Spec.map_comp, hring]
  have hkey : ū ≫ σ = kW ≫ πM := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    refine hkeyS.trans ?_
    show _ = Spec.map (CommRingCat.ofHom κW) ≫ 𝟙 _ ≫ Spec.map (cc.ι.app M.unop)
    rw [Category.id_comp]
    rfl
  -- the base change along `σ : U ⟶ D M`
  have hUa := isAlgebraicSpace_yoneda B integerBase hZ U
  have hDMa := isAlgebraicSpace_yoneda B integerBase hZ (D.obj M)
  have hYU := isAlgebraicSpace_pullback B integerBase hZ gM (yoneda.map σ) hYM hUa hDMa
  have hXU := isAlgebraicSpace_pullback B integerBase hZ fM (yoneda.map σ) hXM hUa hDMa
  obtain ⟨hflU, hprU, hfpU, hdU⟩ := Space.curveFamilyConditions_of_isPullback B integerBase hZ
    (IsPullback.of_hasPullback gM (yoneda.map σ)) hYM hYU hflM hprM hfpM hdM
  have sqXU : IsPullback (pullback.fst fM (yoneda.map σ) ≫ pM) (pullback.snd fM (yoneda.map σ)) f
      (yoneda.map e) := by
    have h := (IsPullback.of_hasPullback fM (yoneda.map σ)).paste_horiz sqXM
    rwa [← Functor.map_comp, hσ] at h
  let h : pullback fM (yoneda.map σ) ⟶ pullback gM (yoneda.map σ) :=
    pullback.map fM (yoneda.map σ) gM (yoneda.map σ) cM (𝟙 _) (𝟙 _) (by simp [hcM]) (by simp)
  have hh : h ≫ pullback.snd gM (yoneda.map σ) = pullback.snd fM (yoneda.map σ) := by
    simp [h]
  -- the fibre of `X_U` over `ū`
  have hūk : yoneda.map ū ≫ yoneda.map e =
      yoneda.map (integerSiteMap B hZ hK hR (Spec.map (CommRingCat.ofHom κR))) := by
    rw [← Functor.map_comp, hū]
  let iXU : yoneda.obj F ⟶ pullback fM (yoneda.map σ) :=
    sqXU.lift iX (yoneda.map tX ≫ yoneda.map ū) (by rw [Category.assoc, hūk, hiX.w])
  have hiXUp : iXU ≫ pullback.fst fM (yoneda.map σ) ≫ pM = iX := sqXU.lift_fst _ _ _
  have hiXUs : iXU ≫ pullback.snd fM (yoneda.map σ) = yoneda.map tX ≫ yoneda.map ū :=
    sqXU.lift_snd _ _ _
  have hiXU : IsPullback iXU (yoneda.map tX) (pullback.snd fM (yoneda.map σ)) (yoneda.map ū) := by
    refine IsPullback.of_right ?_ hiXUs sqXU
    rw [hiXUp, hūk]
    exact hiX
  -- the fibre of `Y` over `ū`
  have hGM : IsPullback (yoneda.map iG ≫ qYM) (yoneda.map tG) gM
      (yoneda.map ū ≫ yoneda.map σ) := by
    have h := hiG.paste_horiz sqqYM'
    rwa [← Functor.map_comp, ← hkey, Functor.map_comp] at h
  let iG' := pullback.lift (yoneda.map iG ≫ qYM) (yoneda.map tG ≫ yoneda.map ū)
    (hGM.w.trans (Category.assoc _ _ _).symm)
  have hiG' := Space.isPullback_lift_of_isPullback_of_fac B integerBase hZ hGM (yoneda.map ū)
    (yoneda.map σ) rfl
  -- compatibility of the fibre of `h` with `h₀`
  have hfibX : iXU ≫ pullback.fst fM (yoneda.map σ) =
      pullback.lift iX (yoneda.map tX ≫ yoneda.map kW)
        (by rw [Category.assoc, hkW', hiX.w]) ≫ qXM := by
    apply sqXM.hom_ext
    · rw [Category.assoc, hiXUp, Category.assoc, hqXMp, pullback.lift_fst]
    · rw [Category.assoc, pullback.condition, reassoc_of% hiXUs, Category.assoc, sqqXM'.w,
        pullback.lift_snd_assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hkey,
        Functor.map_comp, Functor.map_comp]
  have hcompat : iXU ≫ h = yoneda.map a ≫ iG' := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst,
        ← Category.assoc, hfibX, Category.assoc, ← hcomp, ← Category.assoc, hia, Category.assoc]
    · rw [Category.assoc, Category.assoc, hh, hiXUs, pullback.lift_snd,
        ← Category.assoc (yoneda.map a), ← Functor.map_comp yoneda a tG, hat]
  exact ⟨U, e, ū, he, hū, _, _, pullback.snd gM (yoneda.map σ),
    pullback.fst fM (yoneda.map σ) ≫ pM, pullback.snd fM (yoneda.map σ), h, hYU, hXU, hflU, hprU,
    hfpU, hdU, sqXU, hh, iXU, G, tG, iG', φ, a, hiXU, hiXUp, hiG', hφ, hat, hcompat, ha⟩

end Noetherian

end AlgebraicGeometry.EtaleLocalContraction

end
