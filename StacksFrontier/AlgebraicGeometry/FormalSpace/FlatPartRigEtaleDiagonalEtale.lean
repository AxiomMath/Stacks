module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Over
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartRigEtaleDiagonalCharts
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.UnramifiedStages

/-!
# Charts of a flat formal algebraic space with rig-étale rig-surjective diagonal are étale

For a complete discrete valuation ring `A` and `q : X' ⟶ Spf A` flat and locally of finite type
with rig-étale rig-surjective relative diagonal, every Noetherian affine chart `U ⟶ X'` is
representable étale over `Spf A`: its stage maps `A ⧸ I → B ⧸ I B` are flat, of finite presentation
and formally unramified, the last because the kernel of the diagonal is idempotent.

## Main results

* `AlgebraicGeometry.FormalSpace.etale_quotientMap_map_of_flat`
* `isRepresentableEtale_comp_of_isRigEtale_of_isRigSurjective_diagonal`, in the namespace
  `AlgebraicGeometry.FormalSpace`

## References

* [Stacks Project, Tag 0GD9](https://stacks.math.columbia.edu/tag/0GD9)
* [Stacks Project, Tag 08WD](https://stacks.math.columbia.edu/tag/08WD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section StageEtale

/-- **A flat, topologically finite type, unramified stage map is étale.** Let `c : A → B` be a
flat ring map into a topological ring which is topologically of finite type, and let `I` be an
ideal of the Noetherian ring `A` with `I B` open. If `B ⧸ I B` is formally unramified over
`A ⧸ I`, then the stage map `A ⧸ I → B ⧸ I B` is étale: it is flat by base change, of finite
presentation because a polynomial ring with dense image in `B` surjects onto the discrete
quotient `B ⧸ I B`, and étale by Stacks 08WD. -/
theorem etale_quotientMap_map_of_flat {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsNoetherianRing A] (c : A →+* B)
    (hflat : c.Flat) (hft : TopologicalRing.IsTopologicallyOfFiniteType c) (I : Ideal A)
    (hK : IsOpen ((I.map c : Ideal B) : Set B))
    (hunr : letI : Algebra (A ⧸ I) (B ⧸ I.map c) :=
        (Ideal.quotientMap (I.map c) c Ideal.le_comap_map).toAlgebra
      Algebra.FormallyUnramified (A ⧸ I) (B ⧸ I.map c)) :
    (Ideal.quotientMap (I.map c) c Ideal.le_comap_map).Etale := by
  let : Algebra A B := c.toAlgebra
  have : Module.Flat A B := hflat
  -- the algebra structure of the statement is Mathlib's on `B ⧸ I B`
  have hinst : (Ideal.quotientMap (I.map c) c Ideal.le_comap_map).toAlgebra =
      (Ideal.Quotient.algebraQuotientMapQuotient (p := I) : Algebra (A ⧸ I)
        (B ⧸ I.map (algebraMap A B))) :=
    Algebra.algebra_ext _ _ fun r => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      rfl
  have hunr' : Algebra.FormallyUnramified (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := hinst ▸ hunr
  have hfl : Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv
  have hfin : Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
    obtain ⟨n, f, hfC, hdense⟩ := hft
    let mk := Ideal.Quotient.mk (I.map (algebraMap A B))
    let g : MvPolynomial (Fin n) (A ⧸ I) →ₐ[A ⧸ I] B ⧸ I.map (algebraMap A B) :=
      MvPolynomial.aeval fun i => mk (f (MvPolynomial.X i))
    have hg : (g : MvPolynomial (Fin n) (A ⧸ I) →+* B ⧸ I.map (algebraMap A B)).comp
        (MvPolynomial.map (Ideal.Quotient.mk I)) = mk.comp f := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · simp only [RingHom.comp_apply, MvPolynomial.map_C, RingHom.coe_coe]
        rw [show g (MvPolynomial.C (Ideal.Quotient.mk I a)) =
          algebraMap (A ⧸ I) _ (Ideal.Quotient.mk I a) from MvPolynomial.aeval_C _ _,
          ← RingHom.comp_apply f, hfC]
        rfl
      · simp [g]
    refine Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr ⟨n, g, fun y => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hmem : b ∈ (b + ·) '' ((I.map (algebraMap A B) : Ideal B) : Set B) :=
      ⟨0, Submodule.zero_mem _, add_zero b⟩
    obtain ⟨p, k, hk, hkp⟩ := hdense.exists_mem_open (isOpenMap_add_left b _ hK) ⟨b, hmem⟩
    refine ⟨MvPolynomial.map (Ideal.Quotient.mk I) p, ?_⟩
    have := congrArg (fun φ => φ p) hg
    simp only [RingHom.comp_apply, RingHom.coe_coe] at this
    rw [this]
    change mk (f p) = mk b
    rw [← hkp, map_add, show mk k = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hk, add_zero]
  have : Algebra.FinitePresentation (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    Algebra.FinitePresentation.of_finiteType.mp hfin
  have het : Algebra.Etale (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    Algebra.Etale.of_formallyUnramified_of_flat
  change @Algebra.Etale _ _ _ _ (Ideal.quotientMap (I.map c) c Ideal.le_comap_map).toAlgebra
  rw [hinst]
  exact het

end StageEtale

section ChartEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A] (D : QuotientSystem B S hS A)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The Noetherian charts of a flat space with rig-étale rig-surjective diagonal are étale over
the base.** Let `A` be a complete discrete valuation ring with its maximal-adic topology and let
`q : X' ⟶ Spf A` be flat and locally of finite type, with `X'` locally Noetherian and relative
diagonal rig-étale and rig-surjective. Then for every affine representable étale chart
`a : U ⟶ X'` the composite `U ⟶ Spf A` is representable étale.

Write `U = Spf B` and `B` as an `A`-algebra by the presenting homomorphism `c`. The kernel of the
diagonal `B ⊗̂_A B → B` is idempotent
(`isIdempotentElem_ker_of_isRigEtale_of_isRigSurjective_diagonal`, transported along the
identification of the chart ring of `U ×_{Spf A} U` with `B ⊗̂_A B` of Stacks 0AN3), so every
stage `A ⧸ I → B ⧸ I B` is formally unramified
(`TopologicalRing.formallyUnramified_quotient_of_isIdempotentElem_ker`); it is flat because `c`
is, and of finite presentation because `c` is topologically of finite type; so it is étale, and
`Spf c` is representable étale by `isRepresentableEtale_formalSpectrumMap_of_etale_stageMap`. -/
theorem isRepresentableEtale_comp_of_isRigEtale_of_isRigSurjective_diagonal
    (hAadic : _root_.IsAdic (IsLocalRing.maximalIdeal A))
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A) {X' U : FppfSheaf B S hS}
    (q : X' ⟶ formalSpectrum D) (hX' : IsLocallyNoetherian B S hS X')
    (hq : IsLocallyOfFiniteType B S hS q) (hqflat : IsFlat B S hS q)
    (hdiagE : IsRigEtale B S hS (pullback.diagonal q))
    (hdiagS : IsRigSurjective B S hS (pullback.diagonal q)) (a : U ⟶ X')
    (hU : IsAffineFormalAlgebraicSpace B S hS U) (ha : IsRepresentableEtale B S hS a) :
    IsRepresentableEtale B S hS (a ≫ q) := by
  classical
  have hAN : TopologicalRing.IsAdic A :=
    topologicalRingIsAdic_of_isAdic_of_isAdicComplete hAadic hAc
  have hAw := hAN.isWeaklyAdmissible
  obtain ⟨Bu, _, _, _, _, EU, hBu, ⟨eU⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX' a hU ha)
  obtain ⟨hPaff, -, hPn⟩ := isAffine_and_isNoetherian_pullback_charts B S hS D hAN q hX' hq hU hU
    ha ha
  obtain ⟨R, _, _, _, _, EP, hR, ⟨eP⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS hPn
  have _ : IsNoetherianRing R := hR.2
  have _ : IsNoetherianRing Bu := hBu.2
  have hRw := hR.1.isWeaklyAdmissible
  have hBuw := hBu.1.isWeaklyAdmissible
  obtain ⟨μ, hμ, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hRw hBuw
    (eU.inv ≫ pullback.diagonal (a ≫ q) ≫ eP.hom)
  obtain ⟨ρ₁, hρ₁, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hBuw hRw
    (eP.inv ≫ pullback.fst (a ≫ q) (a ≫ q) ≫ eU.hom)
  obtain ⟨ρ₂, hρ₂, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hBuw hRw
    (eP.inv ≫ pullback.snd (a ≫ q) (a ≫ q) ≫ eU.hom)
  have hidem := isIdempotentElem_ker_of_isRigEtale_of_isRigSurjective_diagonal B S hS D hAadic hAc
    q hX' hq hqflat hdiagE hdiagS a hU ha hBu hR eU eP μ hμ ρ₁ ρ₂ hρ₁ hρ₂
  -- the presenting homomorphism `c : A → Bu` of `U ⟶ Spf A`
  obtain ⟨c, hc, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hAw hBuw (eU.inv ≫ a ≫ q)
  have hEUaff := isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hBu.1 EU
    (Iso.refl _)
  have hDaff := isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hAN D
    (Iso.refl _)
  have haqlft : IsLocallyOfFiniteType B S hS (a ≫ q) := IsLocallyOfFiniteType.comp B S hS a q
    (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS a ha) hq
  obtain ⟨hrepi, heti⟩ := isRepresentableEtale_of_isIso B S hS eU.inv
  obtain ⟨hrep1, het1⟩ := isRepresentableEtale_id B S hS (formalSpectrum D)
  have hsq : eU.inv ≫ a ≫ q = (eU.inv ≫ a ≫ q) ≫ 𝟙 _ := (Category.comp_id _).symm
  have hct : eU.inv ≫ a ≫ q = (Iso.refl _).hom ≫ formalSpectrumMap hAw c ≫ (Iso.refl _).inv := by
    simp [hc]
  -- `c` is flat, topologically of finite type and taut
  have hcflat : c.toRingHom.Flat := (isFlat_comp_of_isRepresentableEtale B S hS ha hqflat)
    (formalSpectrum EU) (formalSpectrum D) hEUaff hDaff eU.inv (𝟙 _) (eU.inv ≫ a ≫ q) hrepi
    hrep1 heti het1 hsq A Bu hAN hBu.1 hAw D EU (Iso.refl _) (Iso.refl _) c hct
  have hft := ((hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_of_isFlat B S hS
    (a ≫ q) (isFlat_comp_of_isRepresentableEtale B S hS ha hqflat) haqlft) (formalSpectrum EU)
    (formalSpectrum D) eU.inv (𝟙 _) (eU.inv ≫ a ≫ q) hEUaff hDaff
    ⟨hrepi, heti⟩ ⟨hrep1, het1⟩ hsq
    A Bu ⟨hAN, inferInstance⟩ hBu hAw D EU (Iso.refl _) (Iso.refl _) c hct).2.2
  have hcrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hAw c).hom := by
    rw [hc]
    exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _ hrepi haqlft.1
  have htaut := isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine B S hS
    hAw hBuw D EU hDaff hEUaff c hcrep
  -- the identification of the chart ring of `U ×_{Spf A} U` with `Bu ⊗̂_A Bu`
  let : Algebra A Bu := c.toRingHom.toAlgebra
  have heq : a ≫ q = eU.hom ≫ formalSpectrumMap hAw c := by simp [hc]
  have hmap : (a ≫ q) ≫ 𝟙 _ = eU.hom ≫ formalSpectrumMap hAw c := (Category.comp_id _).trans heq
  let m := pullback.map (a ≫ q) (a ≫ q) (formalSpectrumMap hAw c) (formalSpectrumMap hAw c)
    eU.hom eU.hom (𝟙 _) hmap hmap
  let epres : pullback (formalSpectrumMap hAw c) (formalSpectrumMap hAw c) ≅ formalSpectrum EP :=
    (asIso m).symm ≪≫ eP
  have hepres₁ : formalSpectrumMap hBuw ρ₁ =
      epres.inv ≫ pullback.fst (formalSpectrumMap hAw c) (formalSpectrumMap hAw c) := by
    simp only [epres, m, Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc, pullback.lift_fst,
      hρ₁]
  have hepres₂ : formalSpectrumMap hBuw ρ₂ =
      epres.inv ≫ pullback.snd (formalSpectrumMap hAw c) (formalSpectrumMap hAw c) := by
    simp only [epres, m, Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc, pullback.lift_snd,
      hρ₂]
  obtain ⟨ε, hεc, -, hε⟩ := exists_continuous_ringEquiv_completedTensorProduct_pullback B S hS
    hAw hBuw hBuw D EU EU c c rfl rfl hRw EP epres
  obtain ⟨hε₁, hε₂⟩ := hε ρ₁ ρ₂ hepres₁ hepres₂
  let μ' := μ.toRingHom.comp ε.toRingHom
  have hμ'c : Continuous μ' := μ.continuous.comp hεc
  have hμε : ∀ (ρ : ContinuousHom EU EP) (pr : pullback (a ≫ q) (a ≫ q) ⟶ U)
      (ι : Bu →+* _),
      pullback.diagonal (a ≫ q) ≫ pr = 𝟙 U →
      formalSpectrumMap hBuw ρ = eP.inv ≫ pr ≫ eU.hom →
      ε.toRingHom.comp ι = ρ.toRingHom → μ'.comp ι = RingHom.id Bu := by
    intro ρ pr ι hpr hρ hει
    have hcomp : formalSpectrumMap hBuw (ContinuousHom.comp hRw hBuw μ ρ) =
        formalSpectrumMap hBuw (ContinuousHom.id EU) := by
      rw [formalSpectrumMap_id hBuw (ContinuousHom.id EU) rfl, ← formalSpectrumMap_comp_eq, hμ, hρ]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc (pullback.diagonal (a ≫ q)), hpr]
      simp
    have := congrArg ContinuousHom.toRingHom
      (ContinuousHom.eq_of_formalSpectrumMap_eq B S hS hBuw hBuw hcomp)
    change μ.toRingHom.comp (ε.toRingHom.comp ι) = _
    rwa [hει]
  have hl := hμε ρ₁ _ _ (pullback.diagonal_fst _) hρ₁ hε₁
  have hr := hμε ρ₂ _ _ (pullback.diagonal_snd _) hρ₂ hε₂
  have hJ' : IsIdempotentElem (RingHom.ker μ') := by
    have hk : RingHom.ker μ' = (RingHom.ker μ.toRingHom).map ε.symm := by
      rw [Ideal.map_symm]
      exact (RingHom.comap_ker μ.toRingHom ε.toRingHom).symm
    rw [hk]
    change (RingHom.ker μ.toRingHom).map ε.symm * (RingHom.ker μ.toRingHom).map ε.symm = _
    rw [← Ideal.map_mul, hidem.eq]
  -- every ideal of `Bu` is closed
  have hcl : ∀ J : Ideal Bu, Ideal.closure J = J := by
    obtain ⟨⟨K, -, hKadic⟩, hT2, hCompl⟩ := hBu.1
    let _ : UniformSpace Bu := IsTopologicalAddGroup.rightUniformSpace Bu
    have _ : IsUniformAddGroup Bu := isUniformAddGroup_of_addCommGroup
    have _ : CompleteSpace Bu := hCompl
    have _ : T2Space Bu := hT2
    intro J
    exact SetLike.coe_injective
      (TopologicalRing.isClosed_ideal_of_isAdic_of_isNoetherianRing hKadic J).closure_eq
  have hspf := isRepresentableEtale_formalSpectrumMap_of_etale_stageMap B S hS hAw D hBuw EU
    (hasLargeSite_of_mk_lt_cutoff EU (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hBu.1 EU))
    c htaut (fun I ⟨K, hKw⟩ h hK => by
      simp only at hK h ⊢
      rw [hcl] at hK
      subst hK
      exact etale_quotientMap_map_of_flat c.toRingHom hcflat hft I.1 hKw.1
        (TopologicalRing.formallyUnramified_quotient_of_isIdempotentElem_ker μ' hμ'c hl hr hJ'
          I.1 (I.1.map c.toRingHom) hKw.1 h))
  rw [heq]
  exact IsRepresentableEtale.comp B S hS (isRepresentableEtale_of_isIso B S hS eU.hom) hspf

end ChartEtale

end AlgebraicGeometry.FormalSpace

end
