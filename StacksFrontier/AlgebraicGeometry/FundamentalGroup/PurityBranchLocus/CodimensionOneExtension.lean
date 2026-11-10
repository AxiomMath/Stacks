module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PuncturedDiscreteValuationSpectrum
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullback
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
public import StacksFrontier.RingTheory.DiscreteValuationRing.UnramifiedEtaleModel

/-!
# Extending a cover unramified at a codimension-one point

Let `X` be a scheme, `U ⊆ X` an open and `x ∉ U` a point whose local ring `R = 𝒪_{X, x}` is a
discrete valuation ring and such that the preimage of `U` in `Spec R` is the punctured spectrum.
A finite étale cover `Y ⟶ U` which is unramified over `R` in the sense of [Stacks, Tag 09E9] at
all field factors of its generic fibre over `x` has a restriction to the punctured spectrum
which extends to a finite étale cover of `Spec R`.

## Main results

* `AlgebraicGeometry.exists_ringEquiv_residueField_of_surjectiveOnStalks`: a morphism from the
  spectrum of a field which is surjective on stalks identifies the field with a residue field.
* `AlgebraicGeometry.exists_finiteEtale_stalk_extension_of_isUnramified`: the extension.

## References

* [Stacks Project, Tag 0H2W](https://stacks.math.columbia.edu/tag/0H2W)
* [Stacks Project, Tag 09E9](https://stacks.math.columbia.edu/tag/09E9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- A morphism from the spectrum of a field which is surjective on stalks identifies the field
with the residue field at the image of the point. -/
lemma exists_ringEquiv_residueField_of_surjectiveOnStalks {K : Type u} [Field K]
    {Y : Scheme.{u}} (v : Spec (.of K) ⟶ Y) [SurjectiveOnStalks v] :
    ∃ e : Y.residueField (v (closedPoint K)) ≃+* K,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.fromSpecResidueField (v (closedPoint K)) =
        v := by
  let k := Y.descResidueField (Scheme.stalkClosedPointTo v)
  have hst : Function.Surjective (Scheme.stalkClosedPointTo v) :=
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp
      (v.stalkMap_surjective (closedPoint K))
  have hsurj : Function.Surjective k := by
    intro a
    obtain ⟨b, rfl⟩ := hst a
    exact ⟨Y.residue _ b, by
      rw [← CommRingCat.comp_apply, Scheme.residue_descResidueField]⟩
  exact ⟨RingEquiv.ofBijective k.hom ⟨k.hom.injective, hsurj⟩,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y v⟩

/-- In a discrete valuation ring with uniformizer `ϖ`, the punctured spectrum is the basic open
`D(ϖ)`. -/
lemma puncturedSpectrum_eq_basicOpen_of_irreducible (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) :
    Stacks.puncturedSpectrum R = PrimeSpectrum.basicOpen ϖ := by
  ext p
  change p ≠ closedPoint R ↔ ϖ ∉ p.asIdeal
  constructor
  · refine fun hp hϖp ↦ hp (PrimeSpectrum.ext ?_)
    have hne : p.asIdeal ≠ ⊥ := fun h ↦ hϖ.ne_zero (by simpa [h] using hϖp)
    exact (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp inferInstance |>.2
      |>.unique ⟨hne, p.isPrime⟩ ⟨IsDiscreteValuationRing.not_a_field R,
        (maximalIdeal.isMaximal R).isPrime⟩
  · rintro hϖp rfl
    exact hϖp hϖ.not_isUnit

/-- The global sections of an affine scheme étale over `Spec A` form an étale `A`-algebra. -/
lemma etale_ΓSpecIso_inv_comp_appTop {A : Type u} [CommRing A] {P : Scheme.{u}} [IsAffine P]
    (f : P ⟶ Spec (.of A)) [Etale f] :
    RingHom.Etale ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom :=
  have h : RingHom.Etale (Scheme.ΓSpecIso (.of A)).inv.hom :=
    RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _)
  RingHom.Etale.stableUnderComposition _ _ h
    ((HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance)

/-- **A cover unramified at a codimension-one point extends across it.** Let `x ∉ U` be a point
of `X` whose local ring `R` is a discrete valuation ring and such that the preimage of `U` in
`Spec R` is the punctured spectrum. If every field factor of the generic fibre of the finite étale
cover `E ⟶ U` over `x` is unramified with respect to `R`, then the restriction of `E` to the
punctured spectrum of `R` extends to a finite étale cover of `Spec R`. -/
theorem exists_finiteEtale_stalk_extension_of_isUnramified
    {X : Scheme.{u}} (U : X.Opens) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hOpen : (X.fromSpecStalk x) ⁻¹ᵁ U = Stacks.puncturedSpectrum (X.presheaf.stalk x))
    (E : FiniteEtaleOver U.toScheme)
    (hunr : ∀ (K L : Type u) [Field K] [Field L] [Algebra (X.presheaf.stalk x) K]
      [IsFractionRing (X.presheaf.stalk x) K] [Algebra K L] [FiniteDimensional K L]
      [Algebra.IsSeparable K L] [Algebra (X.presheaf.stalk x) L]
      [IsScalarTower (X.presheaf.stalk x) K L],
      Stacks.FundamentalGroup.IsFieldFactorAt U.ι E.hom x K L →
        IsDiscreteValuationRing.IsUnramifiedWithRespectTo (X.presheaf.stalk x) K L) :
    ∃ L : FiniteEtaleOver (Spec (X.presheaf.stalk x)),
      Nonempty ((finiteEtaleBaseChange ((X.fromSpecStalk x) ⁻¹ᵁ U).ι).obj L ≅
        (finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ U)).obj E) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  let R := X.presheaf.stalk x
  let K := Localization.Away ϖ
  have : IsFractionRing R K := isFractionRing_localizationAway_of_irreducible R hϖ
  let V := (X.fromSpecStalk x) ⁻¹ᵁ U
  let ι : Spec (.of K) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsOpenImmersion ι := Scheme.isOpenImmersion_SpecMap_localizationAway ϖ
  let : Field K := IsFractionRing.toField R
  have hιrange : Set.range ι = (V : Set (Spec R)) := by
    rw [show V = Stacks.puncturedSpectrum R from hOpen,
      puncturedSpectrum_eq_basicOpen_of_irreducible R hϖ,
      ← Scheme.Hom.opensRange_localizationAway (R := R) ϖ]
    rfl
  let eK : Spec (.of K) ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq ι V.ι (by rw [hιrange, Scheme.Opens.range_ι])
  have heK : eK.hom ≫ V.ι = ι := IsOpenImmersion.isoOfRangeEq_hom_fac ι V.ι _
  let r : V.toScheme ⟶ U.toScheme := (X.fromSpecStalk x) ∣_ U
  let w : Spec (.of K) ⟶ U.toScheme := eK.hom ≫ r
  have hw : w ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ X.fromSpecStalk x := by
    simp only [w, r, Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, heK]
    rfl
  let P := pullback E.hom w
  obtain ⟨_, _⟩ := E.prop
  have : IsAffine P := isAffine_of_isAffineHom (pullback.snd E.hom w)
  let C := Γ(P, ⊤)
  let φ : CommRingCat.of K ⟶ C := (Scheme.ΓSpecIso (.of K)).inv ≫ (pullback.snd E.hom w).appTop
  let : Algebra K C := φ.hom.toAlgebra
  have : Algebra.Etale K C := etale_ΓSpecIso_inv_comp_appTop (pullback.snd E.hom w)
  have hsnd : P.isoSpec.inv ≫ pullback.snd E.hom w = Spec.map φ := by
    rw [Iso.inv_comp_eq, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  have : IsPreimmersion w := inferInstanceAs (IsPreimmersion (eK.hom ≫ r))
  obtain ⟨B, _, _, hBet, hBfin, ⟨τ⟩⟩ :=
    IsDiscreteValuationRing.exists_finite_etale_model_of_isUnramifiedWithRespectTo R K C <| by
      rintro L _ _ _ _ _ _ ⟨ψ, hψ⟩
      apply hunr K L
      have : IsClosedImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
        IsClosedImmersion.spec_of_surjective _ hψ
      refine ⟨w, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ P.isoSpec.inv ≫
        pullback.fst E.hom w, hw, ?_, exists_ringEquiv_residueField_of_surjectiveOnStalks _⟩
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv,
        hsnd, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext k
      exact ψ.commutes k
  let sB : Spec (.of B) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let F : FiniteEtaleOver (Spec R) := MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) sB
    ⟨(IsFinite.SpecMap_iff (f := CommRingCat.ofHom (algebraMap R B))).mpr
      (RingHom.finite_algebraMap.mpr hBfin),
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hBet)⟩
  let σ : (B ⊗[R] K) ≃+* C :=
    (Algebra.TensorProduct.comm R B K).toRingEquiv.trans τ.toRingEquiv
  have hσ : φ ≫ CommRingCat.ofHom σ.symm.toRingHom = CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := K)).toRingHom := by
    ext k
    change (Algebra.TensorProduct.comm R B K).symm (τ.symm (algebraMap K C k)) = 1 ⊗ₜ k
    rw [AlgEquiv.commutes]
    simp [Algebra.TensorProduct.algebraMap_apply]
  let e₀ : pullback sB ι ≅ Spec (.of (B ⊗[R] K)) := pullbackSpecIso R B K
  let eP : pullback sB ι ≅ P :=
    e₀ ≪≫ Scheme.Spec.mapIso (σ.symm.toCommRingCatIso).op ≪≫ P.isoSpec.symm
  have heP : eP.hom ≫ pullback.snd E.hom w = pullback.snd sB ι := by
    simp only [eP, Iso.trans_hom, Iso.symm_hom, Category.assoc, hsnd]
    change e₀.hom ≫ Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ Spec.map φ = _
    rw [← Spec.map_comp, hσ]
    exact pullbackSpecIso_hom_snd R B K
  let iK : (finiteEtaleBaseChange ι).obj F ≅ (finiteEtaleBaseChange w).obj E :=
    MorphismProperty.Over.isoMk eP heP
  have : (finiteEtaleBaseChange eK.hom).IsEquivalence :=
    (CategoryTheory.Equivalence.mk (finiteEtaleBaseChange eK.hom) (finiteEtaleBaseChange eK.inv)
      (finiteEtaleBaseChangeId.symm ≪≫
        finiteEtaleBaseChangeComp eK.inv eK.hom (𝟙 _) eK.inv_hom_id.symm)
      ((finiteEtaleBaseChangeComp eK.hom eK.inv (𝟙 _) eK.hom_inv_id.symm).symm ≪≫
        finiteEtaleBaseChangeId)).isEquivalence_functor
  exact ⟨F, ⟨(finiteEtaleBaseChange eK.hom).preimageIso <|
    ((finiteEtaleBaseChangeComp eK.hom V.ι ι heK.symm).app F).symm ≪≫ iK ≪≫
      (finiteEtaleBaseChangeComp eK.hom r w rfl).app E⟩⟩

end AlgebraicGeometry
