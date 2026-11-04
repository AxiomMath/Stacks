module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicIntegralDirectImageCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupportComparison

/-!
# `Hⁱ_c` of a smooth curve does not depend on the compactification

Let `U` be a smooth connected curve over a finite field `k` and `j₁ : U ⟶ Ū₁`, `j₂ : U ⟶ Ū₂`
two compactifications over `k`. Then `RΓ_c(U_k̄, -)` computed through `j₁` and through `j₂` are
isomorphic, compatibly with the geometric Frobenius; for an ℓ-adic sheaf the geometric
Frobenius endomorphisms of the two `Hⁱ_c(U_k̄, F ⊗ ℚ_ℓ)` have the same characteristic polynomial.
This is the case of curves of [Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I) (independence
of the compactification).

The smooth projective compactification `j : U ⟶ Ū` of `U` over `j₁`
(`AlgebraicGeometry.CoverCompactification` for the identity of `U`) has finite complement made of
closed points with discrete valuation local rings, so the morphism `j₂` extends to `Ū ⟶ Ū₂`
(`AlgebraicGeometry.exists_extension_of_finite_compl_valuationRing_stalk`); the extension is
proper and quasi-finite, hence finite, with `U = Ū ×_{Ū₂} U`
(`AlgebraicGeometry.CoverCompactification.exists_finite_extension`). The integral morphisms
`Ū ⟶ Ū₁` and `Ū ⟶ Ū₂` both compute `RΓ_c`
(`Stacks.EtaleCohomology.compactSupportFrobeniusFunctorIntegralIso`).

## Main results

* `AlgebraicGeometry.CoverCompactification.exists_finite_extension`: a cover compactification
  maps finitely to every compactification of the base.
* `Stacks.EtaleCohomology.exists_compactification_finite_finite`: a third compactification
  finite over two given ones.
* In the namespace `Stacks.EtaleCohomology.LAdicSheaf`,
  `charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isCurve` and
  `finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_isCurve`: independence
  of the compactification for `Hⁱ_c(U_k̄, F ⊗ ℚ_ℓ)` with its Frobenius.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CoverCompactification

variable {k : Type u} [Field k] [PerfectField k] {U Ub V : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  [IsCurve k pU] [Smooth pU] {pUb : Ub ⟶ Spec (.of k)} [IsProper pUb] {jU : U ⟶ Ub}
  [IsOpenImmersion jU] {f : V ⟶ U} [IsFinite f] [Etale f] [ConnectedSpace V]
  (C : CoverCompactification k pUb jU f)

include C in
/-- **A cover compactification maps finitely to every compactification of the base.** If
`j' : U ⟶ Ū'` is another open immersion into a proper `k`-scheme over `k`, the morphism
`f ≫ j'` extends to a finite `f̄' : V̄ ⟶ Ū'` over `k` with `V = V̄ ×_{Ū'} U`. -/
theorem exists_finite_extension (hjU : jU ≫ pUb = pU) {Ub' : Scheme.{u}}
    (pUb' : Ub' ⟶ Spec (.of k)) [IsProper pUb'] (jU' : U ⟶ Ub') [IsOpenImmersion jU']
    (hjU' : jU' ≫ pUb' = pU) :
    ∃ fb : C.Vb ⟶ Ub', C.j ≫ fb = f ≫ jU' ∧ fb ≫ pUb' = C.q ∧ IsFinite fb ∧
      IsPullback C.j f fb jU' := by
  have hdense : Dense ((C.j.opensRange : C.Vb.Opens) : Set C.Vb) := C.j.denseRange
  have hfin' : (((C.j.opensRange : C.Vb.Opens) : Set C.Vb)ᶜ).Finite := by
    simpa [Scheme.Hom.coe_opensRange] using C.finite_compl
  have hstalk : ∀ z : C.Vb, z ∉ ((C.j.opensRange : C.Vb.Opens) : Set C.Vb) →
      ∃ _ : IsDomain (C.Vb.presheaf.stalk z), ValuationRing (C.Vb.presheaf.stalk z) := by
    intro z hz
    have := IsCurve.isDiscreteValuationRing_stalk_of_isClosed k C.q
      (C.isClosed_compl z (by simpa [Scheme.Hom.coe_opensRange] using hz))
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨fb, hfbq, hfb⟩ := exists_extension_of_finite_compl_valuationRing_stalk C.q pUb'
    C.j.opensRange hdense hfin' hstalk (C.j.isoOpensRange.inv ≫ f ≫ jU') (by
      rw [Category.assoc, Category.assoc, hjU', ← C.j_comp_q pU hjU, ← Category.assoc,
        Scheme.Hom.isoOpensRange_inv_comp])
  have hjfb : C.j ≫ fb = f ≫ jU' := by
    rw [← Scheme.Hom.isoOpensRange_hom_ι C.j, Category.assoc, hfb, Iso.hom_inv_id_assoc]
  have hpre := preimage_opensRange_eq_of_comp_eq k pUb' jU' f C.q C.j fb hjfb hfbq
  have : IsProper (fb ≫ pUb') := hfbq ▸ inferInstance
  have : IsProper fb := IsProper.of_comp fb pUb'
  have hcomm : ∀ v, fb.base (C.j.base v) = jU'.base (f.base v) :=
    fun v => congr_arg (fun h => h.base v) hjfb
  have : LocallyQuasiFinite fb := by
    refine (locallyQuasiFinite_iff_finite_preimage_singleton).2 fun x => ?_
    by_cases hx : x ∈ Set.range jU'.base
    · obtain ⟨u, rfl⟩ := hx
      refine ((f.finite_preimage_singleton u).image C.j.base).subset ?_
      intro z hz
      have hz' : z ∈ (fb ⁻¹ᵁ jU'.opensRange : Set C.Vb) := ⟨u, (Set.mem_preimage.1 hz).symm⟩
      rw [hpre] at hz'
      obtain ⟨v, rfl⟩ := hz'
      exact ⟨v, jU'.isOpenEmbedding.injective <| (hcomm v).symm.trans hz, rfl⟩
    · refine C.finite_compl.subset ?_
      rintro z hz ⟨v, rfl⟩
      exact hx ⟨_, (hcomm v).symm.trans hz⟩
  exact ⟨fb, hjfb, hfbq, IsFinite.of_isProper_of_locallyQuasiFinite fb,
    (IsOpenImmersion.isPullback f C.j jU' fb hjfb hpre).flip⟩

end AlgebraicGeometry.CoverCompactification

/-! ### ℓ-adic cohomology of a smooth curve through two compactifications -/

open AlgebraicGeometry AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {U : B.Scheme} [IsNoetherian U.1] [ConnectedSpace U.1]
  {k : Type u} [Field k] [Fintype k]
  (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  [IsCurve k f] [Smooth f] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The tower of levels of `F` is its direct image along the identity. -/
def LAdicSheaf.padicTowerDirectImageIdIso (F : LAdicSheaf B U ℓ) :
    LAdicSheaf.padicTower B U ℓ F ≅
      LAdicSheaf.padicTower B U ℓ F ⋙ etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (𝟙 U.1) :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleDirectImageIdIso ℤ_[ℓ] U.1).symm

/-- **The smooth projective compactification of a smooth connected curve, together with finite
morphisms to two given compactifications**: a compactification `W` and finite morphisms
`W ⟶ Ū₁`, `W ⟶ Ū₂` over `k` restricting to the identity of `U`, with `U = W ×_{Ūᵢ} U`. -/
theorem exists_compactification_finite_finite (j₁ j₂ : CompactificationOf (Over.mk f)) :
    ∃ (W : CompactificationOf (Over.mk f)) (φ₁ : W.space ⟶ j₁.space) (φ₂ : W.space ⟶ j₂.space),
      IsFinite φ₁ ∧ IsFinite φ₂ ∧ φ₁ ≫ j₁.toBase = W.toBase ∧ φ₂ ≫ j₂.toBase = W.toBase ∧
      IsPullback (𝟙 U.1) W.immersion j₁.immersion φ₁ ∧
      IsPullback (𝟙 U.1) W.immersion j₂.immersion φ₂ := by
  have : PerfectField k := inferInstance
  have hj₁ := CompactificationOf.immersion_toBase j₁
  let C := (nonempty_coverCompactification k f j₁.toBase j₁.immersion hj₁ (𝟙 U.1)).some
  have hW : C.j ≫ C.q = f := (C.j_comp_q f hj₁).trans (Category.id_comp f)
  let W : CompactificationOf (Over.mk f) :=
    ⟨StructuredArrow.mk (Y := Over.mk C.q)
      (Over.homMk (U := Over.mk f) (V := Over.mk C.q) C.j hW), ⟨C.isOpenImmersion, C.isProper⟩⟩
  obtain ⟨φ₂, -, hφ₂q, hφ₂f, hφ₂pb⟩ := C.exists_finite_extension hj₁ j₂.toBase j₂.immersion
    (CompactificationOf.immersion_toBase j₂)
  exact ⟨W, C.fb, φ₂, C.isFinite, hφ₂f, C.hq, hφ₂q, C.isPullback.flip, hφ₂pb.flip⟩

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **`Hⁱ_c(U_k̄, F ⊗ ℚ_ℓ)` through `j₂` is finite dimensional when it is through `j₁`**, for a
smooth connected curve `U`. -/
theorem LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_isCurve
    (j₁ j₂ : CompactificationOf (Over.mk f)) (F : LAdicSheaf B U ℓ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j₁ kbar F i)] :
    FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j₂ kbar F i) := by
  obtain ⟨W, φ₁, φ₂, h₁, h₂, hq₁, hq₂, sq₁, sq₂⟩ := exists_compactification_finite_finite B f j₁ j₂
  have : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f W kbar F i) :=
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_integral' B ℓ
      f W f j₁ (𝟙 U.1) φ₁ hq₁ sq₁ kbar F F (LAdicSheaf.padicTowerDirectImageIdIso B ℓ F) i
  exact LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_integral B ℓ
    f W f j₂ (𝟙 U.1) φ₂ hq₂ sq₂ kbar F F (LAdicSheaf.padicTowerDirectImageIdIso B ℓ F) i

/-- **`Hⁱ_c(U_k̄, F ⊗ ℚ_ℓ)` does not depend on the compactification**, for a smooth connected
curve `U` over a finite field: the geometric Frobenius endomorphisms through two compactifications
have the same characteristic polynomial (the case of curves of
[Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I), read on the Frobenius). -/
theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isCurve
    (j₁ j₂ : CompactificationOf (Over.mk f)) (F : LAdicSheaf B U ℓ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j₁ kbar F i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j₂ kbar F i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j₁ kbar p q hcard F
        i).hom.charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j₂ kbar p q hcard F
        i).hom.charpoly := by
  obtain ⟨W, φ₁, φ₂, h₁, h₂, hq₁, hq₂, sq₁, sq₂⟩ := exists_compactification_finite_finite B f j₁ j₂
  have : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f W kbar F i) :=
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_integral' B ℓ
      f W f j₁ (𝟙 U.1) φ₁ hq₁ sq₁ kbar F F (LAdicSheaf.padicTowerDirectImageIdIso B ℓ F) i
  rw [LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_integral B ℓ f W f j₁
      (𝟙 U.1) φ₁ hq₁ sq₁ kbar F F (LAdicSheaf.padicTowerDirectImageIdIso B ℓ F) p q hcard i,
    LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_integral B ℓ f W f j₂
      (𝟙 U.1) φ₂ hq₂ sq₂ kbar F F (LAdicSheaf.padicTowerDirectImageIdIso B ℓ F) p q hcard i]

end Stacks.EtaleCohomology

end
