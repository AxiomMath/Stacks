module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.StrictSystemFour

/-!
# System (2) of Stacks 0GA5, as a derived tensor product, is strictly pro-isomorphic to (1)

Let `I` be an ideal of a Noetherian ring `A` and `M` a bounded complex of finite `A`-modules.
In `StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.StrictSystemFour` the system
(2) `M ⊗ᴸ_A A/Iⁿ` of Stacks 0GA5 is formed with the derived tensor product over `A` of the
change-of-rings construction of [Stacks, Tag 06Y6]; in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.StrictDerivedReduction` it is
computed by the reductions `P/IⁿP` of a resolution `P ⟶ M` by finite flat modules.  This file
identifies the two, compatibly with the natural maps to the system (1) `M/IⁿM`, and so carries
the strict pro-isomorphism from (2) to (1) over to the derived-tensor model of (2).  With it,
system (4) is strictly pro-isomorphic to system (1) whenever it is strictly pro-isomorphic to
(2).

## Main definitions

* `Stacks.LocalCohomology.UniformityII.resolutionSystem`: an inverse system of projective
  resolutions of an inverse system of modules.
* `Stacks.LocalCohomology.UniformityII.systemTwoToOne`: the natural map from
  `M ⊗ᴸ_A A/Iⁿ⁺¹` to `M/Iⁿ⁺¹M`.

## Main results

* `Stacks.LocalCohomology.UniformityII.isIso_alphaG_app_of_kFlat`: the counit of the derived
  tensor product over `A` of a change-of-rings construction is invertible on K-flat complexes.
* `Stacks.LocalCohomology.UniformityII.hasUniformInverses_systemTwoToOne`: **the map from (2) to
  (1) is a strict pro-isomorphism.**
* `Stacks.LocalCohomology.UniformityII.hasUniformInverses_systemFourToOne`: hence, if `P → A` is
  finite, (4) is strictly pro-isomorphic to (1).

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
* [Stacks Project, Tag 0G9M](https://stacks.math.columbia.edu/tag/0G9M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.InverseSequence
  CategoryTheory.MonoidalCategory Stacks.AdicSystem.DerivedReductionProIso LiftAcyclic

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.LocalCohomology.UniformityII

universe u

/-! ### Systems of resolutions -/

section Resolutions

variable {P : Type u} [CommRing P]

/-- An inverse system of chosen projective resolutions of an inverse system of modules, with the
chosen lifts of the transition maps. -/
noncomputable def resolutionSystem (X : ℕᵒᵖ ⥤ ModuleCat.{u} P) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} P) ℤ :=
  Functor.ofOpSequence (X := fun n ↦ (ProjectiveResolution.of (X.obj (op n))).cochainComplex)
    (fun n ↦ resolutionLift (X.map (homOfLE (Nat.le_succ n)).op))

/-- The augmentations of `resolutionSystem`. -/
noncomputable def resolutionSystemπ (X : ℕᵒᵖ ⥤ ModuleCat.{u} P) :
    NatTrans (resolutionSystem X) (X ⋙ CochainComplex.singleFunctor (ModuleCat.{u} P) 0) :=
  NatTrans.ofOpSequence (fun n ↦ (ProjectiveResolution.of (X.obj (op n))).π') (fun n ↦ by
    unfold resolutionSystem
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact resolutionLift_comm _)

/-- The component of `resolutionSystemπ X` at `n` is the augmentation of the chosen projective
resolution of `X.obj (op n)`. -/
theorem resolutionSystemπ_app (X : ℕᵒᵖ ⥤ ModuleCat.{u} P) (n : ℕ) :
    (resolutionSystemπ X).app (op n) = (ProjectiveResolution.of (X.obj (op n))).π' := rfl

/-- Every term of `resolutionSystem X` is a K-flat complex. -/
theorem kFlat_resolutionSystem_obj (X : ℕᵒᵖ ⥤ ModuleCat.{u} P) (n : ℕᵒᵖ) :
    ((resolutionSystem X).obj n).KFlat :=
  CochainComplex.KFlat.kFlat_projectiveResolution _

/-- Each component of `resolutionSystemπ X` is a quasi-isomorphism. -/
instance (X : ℕᵒᵖ ⥤ ModuleCat.{u} P) (n : ℕᵒᵖ) : QuasiIso ((resolutionSystemπ X).app n) := by
  change QuasiIso (ProjectiveResolution.of (X.obj (op n.unop))).π'
  infer_instance

end Resolutions

/-! ### The counit of the derived tensor product over `A` -/

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}
  {M : CochainComplex (ModuleCat.{u} A) ℤ}

/-- Extension of scalars along the identity, on complexes, is the identity functor. -/
noncomputable def extendScalarsLargeIdIso :
    CochainComplex.extendScalarsLarge.{u, u, u} (RingHom.id A) ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId A) _ ≪≫
    Functor.mapHomologicalComplexIdIso _ _

/-- **The counit of the derived tensor product over `A` of a change-of-rings construction is
invertible on K-flat complexes.** -/
theorem isIso_alphaG_app_of_kFlat
    (T : CochainComplex.DerivedTensor.DerivedTensorChangeOfRings.{u, u, u} f M)
    (X : CochainComplex (ModuleCat.{u} A) ℤ) (hX : X.KFlat) : IsIso (T.alphaG.app X) := by
  let T' := changeOfRings (RingHom.id A) M
  let τ : CochainComplex.tensorRightLarge.{u, u} M ⋙ DerivedCategory.Q ≅
      T'.directTensor ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight extendScalarsLargeIdIso.symm _ ≪≫
        T'.directTensorComparison.symm) DerivedCategory.Q
  let e := Functor.leftDerivedNatIso T.G T'.F T.alphaG T'.alphaF
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) τ
  have h := Functor.leftDerivedNatTrans_app T.G T'.F T.alphaG T'.alphaF
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) τ.hom X
  have := T'.isIso_alphaF X hX
  have he : IsIso ((Functor.leftDerivedNatTrans T.G T'.F T.alphaG T'.alphaF
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) τ.hom).app
        (DerivedCategory.Q.obj X)) :=
    inferInstanceAs (IsIso (e.hom.app (DerivedCategory.Q.obj X)))
  have h' : T.alphaG.app X = (Functor.leftDerivedNatTrans T.G T'.F T.alphaG T'.alphaF
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) τ.hom).app
        (DerivedCategory.Q.obj X) ≫ T'.alphaF.app X ≫ τ.inv.app X := by
    rw [reassoc_of% h, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [h']
  infer_instance

/-! ### The comparison of the two models of (2) -/

variable (f M)

/-- Tensoring `(A/J)[0]` with a complex `K` is its degreewise reduction. -/
noncomputable def singleQuotientTrightIso (J : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (TrightCochain K).obj ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of A (A ⧸ J))) ≅
      (reduceComplex J).obj K :=
  singleQuotientTensorIsoReduction J K

/-- Tensoring `(A/Iⁿ⁺¹)[0]` with a complex `K` is its degreewise reduction, naturally in `n`. -/
noncomputable def quotientSingleSystemTensorIso (I : Ideal A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    quotientSingleSystem I ⋙ TrightCochain K ≅ reductionComplexSystem I K :=
  NatIso.ofComponents (fun n ↦ singleQuotientTrightIso (I ^ (n.unop + 1)) K)
    (fun {n m} g ↦ by
      have h : m.unop ≤ n.unop := leOfHom g.unop
      obtain rfl : g = (homOfLE h).op := Subsingleton.elim _ _
      rw [Functor.comp_map, quotientSingleSystem_map]
      exact singleQuotientTensorIsoReduction_naturality _ K)

/-- **The natural map from system (2) to system (1)** of Stacks 0GA5: the counit
`M ⊗ᴸ_A A/Iⁿ⁺¹ ⟶ M ⊗_A A/Iⁿ⁺¹ = M/Iⁿ⁺¹M` of the derived tensor product. -/
noncomputable def systemTwoToOne (I : Ideal A) :
    NatTrans (systemTwo f M I) (reductionComplexSystem I M ⋙ DerivedCategory.Q) :=
  Functor.whiskerLeft (quotientSingleSystem I) (changeOfRings f M).alphaG ≫
    Functor.whiskerRight (quotientSingleSystemTensorIso I M).hom DerivedCategory.Q

/-- The identification of `(A/J)[0] ⊗ K` with the degreewise reduction of `K` is natural in `K`. -/
theorem singleQuotientTensorIsoReduction_hom_comp_map (J : Ideal A)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (p : K ⟶ L) :
    (singleQuotientTensorIsoReduction J K).hom ≫ (reduceComplex J).map p =
      HomologicalComplex.tensorHom (𝟙 _) p ≫ (singleQuotientTensorIsoReduction J L).hom := by
  have h := singleQuotientTensorIsoReduction_inv_naturality (le_refl J) p
  have h₁ : (NatTrans.mapHomologicalComplex (reductionNatTrans (le_refl J))
      (ComplexShape.up ℤ)).app K = 𝟙 _ := by
    ext i x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule A (K.X i))) x
    rfl
  have h₂ : quotientModuleMap (le_refl J) = 𝟙 _ :=
    ModuleCat.hom_ext (Submodule.linearMap_qext _ rfl)
  rw [h₁, h₂, CategoryTheory.Functor.map_id] at h
  have h' := (congrArg (· ≫ (singleQuotientTensorIsoReduction J L).inv)
    (Category.id_comp ((reduceComplex J).map p))).symm.trans h
  rw [(Iso.comp_inv_eq _).1 h', Category.assoc, Iso.hom_inv_id_assoc]

/-- A morphism of inverse systems which is an isomorphism at each level has uniform inverses. -/
theorem hasUniformInverses_of_isIso_app {C : Type*} [Category C] {X Y : ℕᵒᵖ ⥤ C}
    (α : NatTrans X Y)
    (h : ∀ n, IsIso (α.app n)) : HasUniformInverses α :=
  have := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ α h
  HasUniformInverses.of_isIso α

/-- A morphism of inverse systems of complexes which is a quasi-isomorphism at each level has
uniform inverses in the derived category. -/
private theorem hasUniformInverses_whiskerRight_Q_of_quasiIso
    {F G : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ} (α : NatTrans F G)
    (h : ∀ n, QuasiIso (α.app n)) : HasUniformInverses (Functor.whiskerRight α DerivedCategory.Q) :=
  hasUniformInverses_of_isIso_app _ fun n ↦ (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (h n)

/-- For `P` the chosen projective resolutions of the quotients `A/Iⁿ⁺¹`, the maps
`P ⊗ M ⟶ M/Iⁿ⁺¹M` in the derived category have inverses over a shift independent of `n`, when
`A` is Noetherian and `M` is a bounded complex of finite `A`-modules. -/
theorem hasUniformInverses_tensorResolution_reduction [IsNoetherianRing A] (I : Ideal A)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    HasUniformInverses
      (Functor.whiskerRight (resolutionSystemπ (quotientModuleSystem I))
          (TrightCochain M ⋙ DerivedCategory.Q (C := ModuleCat.{u} A)) ≫
        Functor.whiskerRight (quotientSingleSystemTensorIso I M).hom
          (DerivedCategory.Q (C := ModuleCat.{u} A))) := by
  obtain ⟨Pc, p, ⟨b, hPb⟩, hPfin, hp, -, -⟩ :=
    derivedReduction_proIsomorphic_adicReduction I M hMbounded hMfinite
  have hPflat : ∀ i, Module.Finite A (Pc.X i) ∧ Module.Flat A (Pc.X i) := fun i ↦ by
    have := (hPfin i).2
    exact ⟨(hPfin i).1, inferInstance⟩
  have : ∀ i, Module.Flat A (Pc.X i) := fun i ↦ (hPflat i).2
  have hPk : Pc.KFlat := CochainComplex.KFlat.kFlat_of_flat Pc b
  have hq : QuasiIso p := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).1 hp
  let X := quotientModuleSystem I
  let S := quotientSingleSystem I
  let Rs := resolutionSystem X
  let π := resolutionSystemπ X
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let trp : NatTrans (TrightCochain Pc) (TrightCochain M) :=
    (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex.flip.map p
  let n₃ : NatTrans (Rs ⋙ TrightCochain Pc ⋙ Q) (Rs ⋙ TrightCochain M ⋙ Q) :=
    Functor.whiskerLeft Rs (Functor.whiskerRight trp Q)
  let γ :=
    Functor.whiskerRight π (TrightCochain Pc ⋙ Q) ≫
      Functor.whiskerRight (quotientSingleSystemTensorIso I Pc).hom Q ≫
        Functor.whiskerRight (reductionComplexSystemMap I p) Q
  let δ :=
    Functor.whiskerRight π (TrightCochain M ⋙ Q) ≫
      Functor.whiskerRight (quotientSingleSystemTensorIso I M).hom Q
  have hn₃ : HasUniformInverses n₃ :=
    hasUniformInverses_whiskerRight_Q_of_quasiIso (Functor.whiskerLeft Rs trp) fun n ↦
      CochainComplex.DerivedTensor.quasiIso_tleft_map_of_kFlat.{u, u} (Rs.obj n)
        (kFlat_resolutionSystem_obj X n) p
  have hγ : HasUniformInverses γ := by
    have h₄ : HasUniformInverses (Functor.whiskerRight π (TrightCochain Pc ⋙ Q)) :=
      hasUniformInverses_whiskerRight_Q_of_quasiIso (Functor.whiskerRight π (TrightCochain Pc))
        fun n ↦ CochainComplex.DerivedTensor.quasiIso_tright_map.{u, u} Pc hPk (π.app n)
    exact h₄.comp ((HasUniformInverses.of_isIso _).comp
      (derivedReduction_hasUniformInverses I M hMbounded hMfinite p ⟨b, hPb⟩ hPflat hp))
  have hcan : ∀ n : ℕᵒᵖ, (quotientSingleSystemTensorIso I Pc).hom.app n ≫
      (reductionComplexSystemMap I p).app n =
        trp.app (S.obj n) ≫ (quotientSingleSystemTensorIso I M).hom.app n :=
    fun n ↦ singleQuotientTensorIsoReduction_hom_comp_map (I ^ (n.unop + 1)) p
  have hE : γ = n₃ ≫ δ := by
    ext n
    show Q.map ((TrightCochain Pc).map (π.app n)) ≫
        Q.map ((quotientSingleSystemTensorIso I Pc).hom.app n) ≫
          Q.map ((reductionComplexSystemMap I p).app n) =
      Q.map (trp.app (Rs.obj n)) ≫ Q.map ((TrightCochain M).map (π.app n)) ≫
        Q.map ((quotientSingleSystemTensorIso I M).hom.app n)
    simp only [← Q.map_comp]
    rw [hcan]
    exact congrArg Q.map (trp.naturality_assoc _ _)
  exact HasUniformInverses.of_comp hn₃ (hE ▸ hγ)

/-- **The natural map from (2) to (1) is a strict pro-isomorphism**, for the derived-tensor model
of (2). Let `I` be an ideal of a Noetherian ring `A` and `M` a bounded complex of finite
`A`-modules. The counits `M ⊗ᴸ_A A/Iⁿ⁺¹ ⟶ M/Iⁿ⁺¹M` have inverses over a shift independent of
`n`. -/
@[stacks 0GA5 "the natural map from (2) to (1) is a strict pro-isomorphism, for (2) formed with \
the derived tensor product"]
theorem hasUniformInverses_systemTwoToOne [IsNoetherianRing A] (I : Ideal A)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    HasUniformInverses (systemTwoToOne f M I) := by
  let T := changeOfRings f M
  let X := quotientModuleSystem I
  let S := quotientSingleSystem I
  let Rs := resolutionSystem X
  let π := resolutionSystemπ X
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let n₁ : NatTrans (Rs ⋙ Q ⋙ T.G) (S ⋙ Q ⋙ T.G) :=
    Functor.whiskerRight (Functor.whiskerRight π Q) T.G
  let n₂ : NatTrans (Rs ⋙ Q ⋙ T.G) (Rs ⋙ TrightCochain M ⋙ Q) := Functor.whiskerLeft Rs T.alphaG
  let δ :=
    Functor.whiskerRight π (TrightCochain M ⋙ Q) ≫
      Functor.whiskerRight (quotientSingleSystemTensorIso I M).hom Q
  have hn₁ : HasUniformInverses n₁ := hasUniformInverses_of_isIso_app _ fun n ↦ by
    show IsIso (T.G.map (Q.map (π.app n)))
    infer_instance
  have hn₂ : HasUniformInverses n₂ := hasUniformInverses_of_isIso_app _ fun n ↦
    isIso_alphaG_app_of_kFlat T _ (kFlat_resolutionSystem_obj X n)
  have hδ : HasUniformInverses δ :=
    hasUniformInverses_tensorResolution_reduction M I hMbounded hMfinite
  have hE : n₁ ≫ systemTwoToOne f M I = n₂ ≫ δ := by
    ext n
    show T.G.map (Q.map (π.app n)) ≫ T.alphaG.app (S.obj n) ≫
        Q.map ((quotientSingleSystemTensorIso I M).hom.app n) =
      T.alphaG.app (Rs.obj n) ≫ Q.map ((TrightCochain M).map (π.app n)) ≫
        Q.map ((quotientSingleSystemTensorIso I M).hom.app n)
    exact T.alphaG.naturality_assoc (π.app n) _
  exact HasUniformInverses.of_comp hn₁ (hE ▸ hn₂.comp hδ)

/-- **If `P → A` is finite, system (4) is strictly pro-isomorphic to system (1).**  The
composite of the strict pro-isomorphisms (4) ⟶ (2) and (2) ⟶ (1). -/
theorem hasUniformInverses_systemFourToOne {P : Type u} [CommRing P] [IsNoetherianRing P]
    [IsNoetherianRing A] (f : P →+* A) (hf : f.Finite) (J : Ideal P) (I : Ideal A)
    (hI : I = J.map f) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    HasUniformInverses (systemFourToTwo f M J I hI ≫ systemTwoToOne f M I) :=
  (hasUniformInverses_systemFourToTwo f M hf J I hI).comp
    (hasUniformInverses_systemTwoToOne f M I hMbounded hMfinite)

end Stacks.LocalCohomology.UniformityII

end
