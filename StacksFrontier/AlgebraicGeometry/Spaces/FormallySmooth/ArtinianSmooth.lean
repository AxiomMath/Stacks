module

public import StacksFrontier.AlgebraicGeometry.Sites.GaloisDescentFppf
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ArtinianChartPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.GaloisInvariantLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjectsAlong
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.RingTheory.Artinian.GaloisResidueLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smooth morphisms of algebraic spaces lift along Artinian thickenings

Let `f : X ⟶ h_V` be a smooth morphism from an algebraic space to a representable presheaf on the
big fppf site of a scheme `S`, and let `T ⊆ T'` be a square-zero closed immersion of affine objects
of the site whose larger member is the spectrum of an Artinian local ring. Every lifting problem
for `f` against `T ⊆ T'` has a solution: `f` is formally smooth along the spectra of Artinian local
rings, `AlgebraicGeometry.Space.FormallySmoothAlong`.

This is the implication of Stacks 04AM from smoothness to formal smoothness, at the test objects
that the predeformation categories of Stacks 07WJ see; it is exactly what case (3) of Stacks 07WK,
and the representable-and-smooth clause of Stacks 07XW, consume.

## Main results

* `AlgebraicGeometry.Space.exists_isLift_of_isSmooth_of_isSpecArtinianLocal`: the lifting
  property.
* `AlgebraicGeometry.Space.formallySmoothAlong_isSpecArtinianLocal_of_isSmooth`: the same as a
  statement of `AlgebraicGeometry.Space.FormallySmoothAlong`.

## Implementation notes

The proof is Galois descent of an averaged lift. Let `R` be the Artinian local ring of `T'`, with
residue field `k`, and pull the problem back to `T`'s chart.

1. An étale chart `a : h_U ⟶ X` and a finite separable extension `L / k` are found over which
   the given section over `T` lifts to the chart after every Artinian extension of `T` whose
   residue field receives `L`, `AlgebraicGeometry.Space.exists_etale_chart_lift_of_isArtinianLocal`.
2. A finite Galois `K / k` containing `L` is lifted to a finite étale Galois `R`-algebra `A` with
   residue field `K` and group `G = Gal(K/k)`, `Stacks.ArtinianGaloisLift.Lift`.
3. Over `Spec A` the problem has a solution through the chart, by formal smoothness of the
   (smooth) morphism of schemes underlying the chart, and then a `G`-invariant solution in `X`,
   `AlgebraicGeometry.Space.GaloisLift.exists_invariant_lift`.
4. The invariant solution descends to `T'`, `AlgebraicGeometry.bijective_galoisRestriction`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

open SquareZeroLift

/-- **A first-order thickening of the spectrum of a ring is the spectrum of a square-zero
quotient**: `IsClosedImmersion.Spec_iff`, with the square-zero condition read off the kernel on
global sections. -/
theorem exists_iso_specQuotient_of_isFirstOrderThickening {T : Scheme.{u}} {R : CommRingCat.{u}}
    (j : T ⟶ Spec R) (hj : Stacks.Thickenings.IsFirstOrderThickening j) :
    ∃ (J : Ideal R) (_ : J ^ 2 = ⊥) (e : T ≅ Spec (CommRingCat.of (R ⧸ J))),
      j = e.hom ≫ reduction J := by
  have : IsClosedImmersion j := hj.1
  obtain ⟨J, e, he⟩ := IsClosedImmersion.Spec_iff.mp ‹_›
  refine ⟨J, ?_, e, he⟩
  have hsq := Stacks.Smooth.ker_appTop_sq_eq_bot hj
  have hker : RingHom.ker j.appTop.hom = J.comap (Scheme.ΓSpecIso R).hom.hom := by
    have hj' : j.appTop = (reduction J).appTop ≫ e.hom.appTop := by
      rw [he, Scheme.Hom.comp_appTop]
    have : IsIso e.hom.appTop := by
      show IsIso (e.hom.app ⊤)
      infer_instance
    have hinj : Function.Injective e.hom.appTop.hom :=
      (ConcreteCategory.bijective_of_isIso e.hom.appTop).1
    rw [hj', CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj]
    have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
    have hinj' : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom :=
      (ConcreteCategory.bijective_of_isIso _).1
    ext a
    simp only [RingHom.mem_ker, Ideal.mem_comap]
    rw [← map_eq_zero_iff _ hinj']
    have := congrArg (fun φ => φ.hom a) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [this, Ideal.Quotient.eq_zero_iff_mem]
    exact Iff.rfl
  rw [hker] at hsq
  let ρ := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have hsq' : (J.comap (ρ : Γ(Spec R, ⊤) →+* R)) ^ 2 = ⊥ := hsq
  calc J ^ 2 = (Ideal.map (ρ : Γ(Spec R, ⊤) →+* R) (J.comap (ρ : Γ(Spec R, ⊤) →+* R))) ^ 2 := by
        rw [Ideal.map_comap_of_surjective (ρ : Γ(Spec R, ⊤) →+* R) ρ.surjective]
    _ = Ideal.map (ρ : Γ(Spec R, ⊤) →+* R) ((J.comap (ρ : Γ(Spec R, ⊤) →+* R)) ^ 2) := by
        rw [Ideal.map_pow]
    _ = ⊥ := by rw [hsq', Ideal.map_bot]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The lifting property at a spectrum of an Artinian local ring**, with the larger member of
the thickening presented as `Spec R` in the site. A smooth morphism `f : X ⟶ h_W` from an
algebraic space solves every lifting problem against a square-zero closed immersion
`T ⟶ Spec R` with `R` Artinian local. The proof is the Galois descent of an averaged lift
described in the module docstring. -/
theorem exists_isLift_of_isSmooth_of_spec
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {W : BigFppfOver B S hS} (f : X ⟶ yoneda.obj W) (hf : IsSmooth B S hS f)
    {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S)
    {T : BigFppfOver B S hS} (i : T ⟶ galoisBaseObj B S hS hR s)
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : X.obj (op T))
    (y : galoisBaseObj B S hS hR s ⟶ W) (hxy : f.app (op T) x = i ≫ y) :
    ∃ z : X.obj (op (galoisBaseObj B S hS hR s)), X.map i.op z = x ∧
      f.app (op (galoisBaseObj B S hS hR s)) z = y := by
  classical
  -- the closed point `T` of `T'`
  obtain ⟨J, hJ, eT, heT⟩ := exists_iso_specQuotient_of_isFirstOrderThickening
    (R := CommRingCat.of R) ((BigFppfOver.toScheme B S hS).map i) hi
  have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso eT.hom
  let := AlgebraicGeometry.SquareZeroLift.isLocalRing_quotient J hJ
  let ΓT : (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) ≃+* (R ⧸ J) :=
    ((Scheme.Γ.mapIso eT.op).symm ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).commRingCatIsoToRingEquiv
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := ΓT.surjective.nontrivial
  have : IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    IsLocalRing.of_surjective' (ΓT.symm : R ⧸ J →+* _) ΓT.symm.surjective
  have : IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    ΓT.symm.isArtinianRing
  -- the chart and the separable extension
  obtain ⟨U, a, L, _, _, ha, hLfin, hLsep, hlift⟩ :=
    exists_etale_chart_lift_of_isArtinianLocal hX x
  -- the residue fields of `R` and of `Γ(T)`
  let φT : R →+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ((BigFppfOver.toScheme B S hS).map i).appTop).hom
  have hφT : Function.Surjective φT := by
    have h1 := Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening (T' := Spec (.of R)) hi
    exact h1.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
  have : IsLocalHom φT := IsLocalHom.of_surjective φT hφT
  let α : ResidueField R →+* ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    ResidueField.map φT
  have hαsurj : Function.Surjective α := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨r, rfl⟩ := hφT b
    exact ⟨residue R r, ResidueField.map_residue φT r⟩
  let : Algebra (ResidueField R) L := ((algebraMap _ L).comp α).toAlgebra
  let : Algebra (ResidueField R) (ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :=
    α.toAlgebra
  have : IsScalarTower (ResidueField R)
      (ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite (ResidueField R)
      (ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) hαsurj
  have : FiniteDimensional (ResidueField R) L := Module.Finite.trans
    (ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) L
  have : Algebra.IsSeparable (ResidueField R)
      (ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) := ⟨fun y => by
    obtain ⟨r, rfl⟩ := hαsurj y
    exact isSeparable_algebraMap (K := ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) r⟩
  have : Algebra.IsSeparable (ResidueField R) L := Algebra.IsSeparable.trans
    (ResidueField R) (ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) L
  -- a finite Galois extension containing `L`
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField R) L
  let p := minpoly (ResidueField R) pb.gen
  let K := p.SplittingField
  have : IsGalois (ResidueField R) K :=
    IsGalois.of_separable_splitting_field (Algebra.IsSeparable.isSeparable _ pb.gen)
  obtain ⟨β, hβ⟩ := (Polynomial.SplittingField.splits p).exists_eval_eq_zero (by
    rw [Polynomial.degree_map]
    exact (minpoly.degree_pos pb.isIntegral_gen).ne')
  let ιLK : L →ₐ[ResidueField R] K := pb.lift β (by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hβ)
  -- the Galois cover of `R` with residue field `K`
  have hnil : IsNilpotent (maximalIdeal R) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  let A := Stacks.ArtinianGaloisLift.Lift R K
  let ρ := Stacks.ArtinianGaloisLift.galoisAction hnil K
  have hGal := Stacks.ArtinianGaloisLift.bijective_galoisTensorPi hnil K
  obtain ⟨c, hc⟩ := Stacks.ArtinianGaloisLift.exists_sum_galoisAction_eq_one hnil K
  have hA : B.Contains (Spec (.of A)) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R A hR
  let T'K := galoisCoverObj (R := R) B S hS hA s
  let π : T'K ⟶ galoisBaseObj B S hS hR s := galoisCoverMap B S hS hR hA s
  -- the thickening `T_K` of `T'_K`
  let TK := pullback i π
  let iK : TK ⟶ T'K := pullback.snd i π
  let πT : TK ⟶ T := pullback.fst i π
  have hiK : IsSquareZeroClosedImmersion B S hS iK := by
    let := preservesLimitsOfShape_walkingCospan_toScheme B S hS
    have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map πT)
        ((BigFppfOver.toScheme B S hS).map iK) ((BigFppfOver.toScheme B S hS).map i)
        ((BigFppfOver.toScheme B S hS).map π) :=
      (IsPullback.of_hasPullback i π).map (BigFppfOver.toScheme B S hS)
    exact Stacks.Thickenings.isFirstOrderThickening_of_isPullback hsq.flip hi
  obtain ⟨JK, hJK, eK, heK⟩ := exists_iso_specQuotient_of_isFirstOrderThickening
    (R := CommRingCat.of A) ((BigFppfOver.toScheme B S hS).map iK) hiK
  have hTKaff : IsAffine ((BigFppfOver.toScheme B S hS).obj TK) := IsAffine.of_isIso eK.hom
  let := AlgebraicGeometry.SquareZeroLift.isLocalRing_quotient JK hJK
  let ΓTK : (Γ((BigFppfOver.toScheme B S hS).obj TK, ⊤) : Type u) ≃+* (A ⧸ JK) :=
    ((Scheme.Γ.mapIso eK.op).symm ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (A ⧸ JK))).commRingCatIsoToRingEquiv
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj TK, ⊤) := ΓTK.surjective.nontrivial
  have : IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj TK, ⊤) :=
    IsLocalRing.of_surjective' (ΓTK.symm : A ⧸ JK →+* _) ΓTK.symm.surjective
  have : IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj TK, ⊤) :=
    ΓTK.symm.isArtinianRing
  -- the residue field of `T_K` receives `L`
  let φK : A →+* Γ((BigFppfOver.toScheme B S hS).obj TK, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ((BigFppfOver.toScheme B S hS).map iK).appTop).hom
  have hφK : Function.Surjective φK := by
    have h1 := Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening (T' := Spec (.of A)) hiK
    exact h1.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have : IsLocalHom φK := IsLocalHom.of_surjective φK hφK
  let ι : L →+* ResidueField Γ((BigFppfOver.toScheme B S hS).obj TK, ⊤) :=
    (ResidueField.map φK).comp
      (((Stacks.ArtinianGaloisLift.residueFieldEquiv R K).symm : K →+* ResidueField A).comp
        (ιLK : L →+* K))
  have hsqΓ : ∀ r : R, ((BigFppfOver.toScheme B S hS).map πT).appTop.hom (φT r) =
      φK (algebraMap R A r) := by
    intro r
    have hcond : (BigFppfOver.toScheme B S hS).map πT ≫ (BigFppfOver.toScheme B S hS).map i =
        (BigFppfOver.toScheme B S hS).map iK ≫ (BigFppfOver.toScheme B S hS).map π := by
      rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
    have h := congrArg (fun m => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ m.appTop).hom r) hcond
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
    have hπ : (BigFppfOver.toScheme B S hS).map π =
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl
    have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R A))
    have hnat' := congrArg (fun m => m.hom r) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat'
    simp only [φT, φK, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [h, hπ, hnat']
  have hcompat : (ι.comp (algebraMap _ L)).comp (residue _) =
      (residue _).comp ((BigFppfOver.toScheme B S hS).map πT).appTop.hom := by
    ext b
    obtain ⟨r, rfl⟩ := hφT b
    simp only [RingHom.comp_apply]
    rw [hsqΓ, ← ResidueField.map_residue φT r]
    show ι (algebraMap (ResidueField R) L (residue R r)) = _
    simp only [ι, RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.commutes]
    show ResidueField.map φK ((Stacks.ArtinianGaloisLift.residueFieldEquiv R K).symm
      (algebraMap _ K (residue R r))) = _
    rw [AlgEquiv.commutes, ResidueField.algebraMap_residue, ResidueField.map_residue]
  obtain ⟨g, hg⟩ := hlift TK πT ι hcompat
  -- the smooth morphism of schemes underlying the chart, and a lift through it
  let ψ : U ⟶ W := yoneda.preimage (a ≫ f)
  have hψ : a ≫ f = yoneda.map ψ := (yoneda.map_preimage _).symm
  have hψsm : Smooth ((BigFppfOver.toScheme B S hS).map ψ) :=
    hf U W a (𝟙 _) ψ ha (presheaf_etale_of_iso B S hS (Iso.refl _)) (by
      rw [Category.comp_id, hψ])
  have hψF : FormallySmooth (yoneda.map ψ) :=
    formallySmooth_yoneda_map_of_formallySmoothScheme
      (hψ := Stacks.Smooth.formallySmoothScheme_of_smooth _)
  have hT'Kaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T'K) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hnatf : ∀ {V₁ V₂ : BigFppfOver B S hS} (m : V₁ ⟶ V₂) (z : X.obj (op V₂)),
      f.app (op V₁) (X.map m.op z) = m ≫ f.app (op V₂) z := fun m z =>
    NatTrans.naturality_apply f m.op z
  have hfa : ∀ {V₁ : BigFppfOver B S hS} (ℓ : V₁ ⟶ U), f.app (op V₁) (a.app (op V₁) ℓ) = ℓ ≫ ψ :=
    fun ℓ => by
      have := congrArg (fun φ => φ.app (op _) ℓ) hψ
      simpa using this
  obtain ⟨ℓ₀, hℓ₀, hℓ₀y⟩ := hψF TK T'K hTKaff hT'Kaff iK hiK g (π ≫ y) (by
    show g ≫ ψ = iK ≫ π ≫ y
    rw [← hfa, hg, hnatf, hxy, ← Category.assoc, pullback.condition, Category.assoc])
  change iK ≫ ℓ₀ = g at hℓ₀
  change ℓ₀ ≫ ψ = π ≫ y at hℓ₀y
  -- the Galois-invariant lift over `T'_K`
  let ρ' : (K ≃ₐ[ResidueField R] K) →* (A ≃+* A) :=
    { toFun := fun σ => (ρ σ).toRingEquiv
      map_one' := by ext; simp
      map_mul' := fun σ τ => by ext; simp }
  let t : (K ≃ₐ[ResidueField R] K) → (TK ⟶ TK) := fun σ =>
    pullback.map i π i π (𝟙 T) (galoisCoverAut ρ B S hS hA s σ) (𝟙 _) (by simp)
      (by rw [Category.comp_id, galoisCoverAut_comp_galoisCoverMap])
  have htT : ∀ σ, t σ ≫ πT = πT := fun σ => by
    simp only [t, πT, pullback.map, pullback.lift_fst, Category.comp_id]
  have ht : ∀ σ, t σ ≫ iK = iK ≫ galoisCoverAut ρ B S hS hA s σ := fun σ => by
    simp only [t, iK, pullback.map, pullback.lift_snd]
  obtain ⟨zK, hzK₁, hzK₂, hzK₃⟩ := GaloisLift.exists_invariant_lift (hJ := hJK) (e := eK)
    (e' := Iso.refl _) (i := iK) (hi := by rw [heK]; simp; rfl) a ρ'
    (galoisCoverAut ρ B S hS hA s) (fun σ => by simp; rfl) t ht c hc ha
    f ψ hψ (X.map πT.op x)
    (fun σ => by rw [← FunctorToTypes.map_comp_apply, ← op_comp, htT])
    (π ≫ y) (fun σ => by rw [← Category.assoc, galoisCoverAut_comp_galoisCoverMap])
    g hg ℓ₀ hℓ₀ hℓ₀y hiK
  -- descent to `T'`
  obtain ⟨z, hz⟩ := (bijective_galoisRestriction ρ B S hS hR hA s hGal hX.isSheaf).2 ⟨zK, hzK₃⟩
  have hz' : X.map π.op z = zK := congrArg Subtype.val hz
  refine ⟨z, ?_, ?_⟩
  · have hcov := (BigFppfOver.topology B S hS).pullback_stable i
      (galoisCoverMap_mem_topology B S hS hR hA s)
    have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf _ hcov).isSeparatedFor
    refine hsep.ext fun V h hh => ?_
    obtain ⟨Y', q, π', hπ', hfac⟩ := hh
    obtain ⟨⟩ := hπ'
    have hlift : pullback.lift h q hfac.symm ≫ πT = h := pullback.lift_fst _ _ _
    have hlift' : pullback.lift h q hfac.symm ≫ iK = q := pullback.lift_snd _ _ _
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← hfac, op_comp, FunctorToTypes.map_comp_apply,
      hz', ← hlift, op_comp, FunctorToTypes.map_comp_apply, ← hzK₁, ← FunctorToTypes.map_comp_apply,
      ← op_comp, hlift']
  · refine (bijective_galoisRestriction ρ B S hS hR hA s hGal
      (isAlgebraicSpace_yoneda B S hS W).isSheaf).1 (Subtype.ext ?_)
    simp only [galoisRestriction_coe]
    show π ≫ f.app (op (galoisBaseObj B S hS hR s)) z = π ≫ y
    rw [← hnatf π z, hz', hzK₂]

/-- **A smooth morphism to a representable presheaf lifts along a square-zero thickening of the
spectrum of an Artinian local ring.** -/
theorem exists_isLift_of_isSmooth_of_isSpecArtinianLocal
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {W : BigFppfOver B S hS} (f : X ⟶ yoneda.obj W) (hf : IsSmooth B S hS f)
    {T T' : BigFppfOver B S hS} (hT' : BigFppfOver.IsSpecArtinianLocal B S hS T') (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : X.obj (op T)) (y : T' ⟶ W)
    (hxy : f.app (op T) x = i ≫ y) :
    ∃ z : X.obj (op T'), X.map i.op z = x ∧ f.app (op T') z = y := by
  obtain ⟨R, hRloc, hRart, ⟨e₀⟩⟩ := hT'
  have hR : B.Contains (Spec (.of R)) := by
    show (Spec R).size < B.cutoff
    rw [← Scheme.size_congr e₀]
    exact T'.left.2
  let s : Spec (.of R) ⟶ S := e₀.inv ≫ B.inclusion.map T'.hom
  let Φ : galoisBaseObj B S hS hR s ≅ T' :=
    { hom := Over.homMk (ObjectProperty.homMk e₀.inv) rfl
      inv := Over.homMk (ObjectProperty.homMk e₀.hom) (by
        ext : 1
        show e₀.hom ≫ e₀.inv ≫ B.inclusion.map T'.hom = B.inclusion.map T'.hom
        rw [Iso.hom_inv_id_assoc])
      hom_inv_id := by ext : 2; exact e₀.inv_hom_id
      inv_hom_id := by ext : 2; exact e₀.hom_inv_id }
  have hi' : IsSquareZeroClosedImmersion B S hS (i ≫ Φ.inv) := by
    have : IsIso ((BigFppfOver.toScheme B S hS).map Φ.hom) :=
      ((BigFppfOver.toScheme B S hS).mapIso Φ).isIso_hom
    have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map (i ≫ Φ.inv)) (𝟙 _)
        ((BigFppfOver.toScheme B S hS).map Φ.hom) ((BigFppfOver.toScheme B S hS).map i) :=
      IsPullback.of_vert_isIso ⟨by rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, Category.id_comp]⟩
    exact Stacks.Thickenings.isFirstOrderThickening_of_isPullback hsq hi
  obtain ⟨z, hz₁, hz₂⟩ := exists_isLift_of_isSmooth_of_spec B S hS hX f hf hR s (i ≫ Φ.inv) hi' x
    (Φ.hom ≫ y) (by rw [hxy, Category.assoc, Iso.inv_hom_id_assoc])
  refine ⟨X.map Φ.inv.op z, ?_, ?_⟩
  · rw [← FunctorToTypes.map_comp_apply, ← op_comp, hz₁]
  · rw [NatTrans.naturality_apply f Φ.inv.op z]
    have : f.app (op (galoisBaseObj B S hS hR s)) z = Φ.hom ≫ y := hz₂
    show Φ.inv ≫ f.app (op (galoisBaseObj B S hS hR s)) z = y
    rw [this, Iso.inv_hom_id_assoc]

/-- **Stacks 04AM, smooth implies formally smooth, along the spectra of Artinian local rings.** A
smooth morphism from an algebraic space to a representable presheaf on the big fppf site is
formally smooth along the objects whose underlying scheme is the spectrum of an Artinian local
ring. -/
@[sga "1 III 3.1" "(i)⇒(iii)"]
theorem formallySmoothAlong_isSpecArtinianLocal_of_isSmooth
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {W : BigFppfOver B S hS} (f : X ⟶ yoneda.obj W) (hf : IsSmooth B S hS f) :
    FormallySmoothAlong (BigFppfOver.IsSpecArtinianLocal B S hS) f :=
  fun _ _ _ _ hT' i hi x y hxy =>
    exists_isLift_of_isSmooth_of_isSpecArtinianLocal B S hS hX f hf hT' i hi x y hxy

end AlgebraicGeometry.Space

end
