module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulPowerDefs
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.ProZero
public import StacksFrontier.RingTheory.Tor.Balancing
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
import StacksFrontier.Homology.HomComplex.DerivedAdjunction
import StacksFrontier.Homology.Tor.BaseChangeTensorIso
import StacksFrontier.Homology.Tor.DerivedExtensionScalars
import StacksFrontier.CategoryTheory.Triangulated.Elementary
import StacksFrontier.Homology.KFlat.QuasiIso
import StacksFrontier.Homology.KFlat.Flat
import StacksFrontier.Homology.KFlat.LargeUniverse
import StacksFrontier.Homology.KFlat.Resolution
import StacksFrontier.Homology.TensorComplex.Monoidal
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

section




/-!
# Cohomology of derived completion over a Noetherian ring

Let `I` be an ideal in a Noetherian ring `A`. The cohomology of derived `I`-adic
completion is described by a Milnor short exact sequence. For a module, its outer terms are
the inverse limit of the corresponding Tor groups and the first derived inverse limit of the
Tor groups one degree higher. The same description applies to bounded-above derived objects.

## Main definitions

* `AdicCompletionTor.idealPowerQuotientModuleSystem` is the inverse system `A/Iⁿ` of modules.
* `AdicCompletionTor.torIdealPowerSystem` is the resulting inverse system of Tor modules.
* `AdicCompletionTor.firstDerivedInverseLimit` is the cokernel model for `R¹ lim` of a countable
  inverse system.
* `AdicCompletionTor.derivedTensorHomologySystem` is the cohomology system of
  `K ⊗ᴸ[A] A/Iⁿ`.

## Main results

* `AdicCompletionTor.derivedCompletion_homology_shortExact` gives the Tor short exact sequences for
  modules and the corresponding cohomology short exact sequences for derived objects.

## Implementation notes

Positive ideal powers are indexed by `n : ℕ` as `I^(n+1)`, a cofinal reindexing of the
positive integers used in the source. For a countable inverse system, `R¹ lim` is represented
by the cokernel of the Milnor difference map on the product. The derived-object assertion is
stated for every object of `D(A)`, which strengthens the source's bounded-above case.

## References

* [The Stacks Project, Tag 0EET](https://stacks.math.columbia.edu/tag/0EET)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AdicCompletionTor

/-- The inverse system of modules `A/I^(n+1)`. -/
public noncomputable def idealPowerQuotientModuleSystem
    {A : Type u} [CommRing A] (I : Ideal A) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  Functor.ofOpSequence (X := fun n ↦ ModuleCat.of A (A ⧸ I ^ (n + 1)))
    (fun n ↦ NoetherianAdicCompletion.idealPowerQuotientTransition I (n + 1) n (Nat.le_succ n))

/-- The `n`-th term of `AdicCompletionTor.idealPowerQuotientModuleSystem I` is `A/I^(n+1)`. -/
@[simp]
public theorem idealPowerQuotientModuleSystem_obj
    {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    (idealPowerQuotientModuleSystem I).obj (Opposite.op n) =
      ModuleCat.of A (A ⧸ I ^ (n + 1)) := rfl

/-- The transition `A/I^(n+2) ⟶ A/I^(n+1)` of the tower of ideal-power quotients. -/
private theorem idealPowerQuotientModuleSystem_map_succ
    {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    (idealPowerQuotientModuleSystem I).map (homOfLE (n.le_add_right 1)).op =
      NoetherianAdicCompletion.idealPowerQuotientTransition I (n + 1) n (Nat.le_succ n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The inverse system `Tor_i^A(M, A/I^(n+1))`. -/
public noncomputable def torIdealPowerSystem
    {A : Type u} [CommRing A] (I : Ideal A) (M : ModuleCat.{u} A) (i : ℕ) :
    ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  idealPowerQuotientModuleSystem I ⋙ (Tor' (ModuleCat.{u} A) i).obj M

/-- The tower `n ↦ M/Iⁿ⁺¹M` of adic quotients, indexed from the first positive power of `I`. -/
public def adicQuotientSystem {A : Type u} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) : ℕᵒᵖ ⥤ ModuleCat.{u} A where
  obj n := ModuleCat.of A (M ⧸ (I ^ (n.unop + 1) • ⊤ : Submodule A M))
  map f := ModuleCat.ofHom (AdicCompletion.transitionMap I M
    (Nat.add_le_add_right (leOfHom f.unop) 1))
  map_id _ := ModuleCat.hom_ext (Submodule.mapQ_id _)
  map_comp f g := ModuleCat.hom_ext (Submodule.factor_comp
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1)))
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right
      (Nat.add_le_add_right (leOfHom g.unop) 1)))).symm

/-- **The transitions of the adic quotient tower are surjective.** `M/Iⁿ⁺²M ⟶ M/Iⁿ⁺¹M` is a
quotient factorization, so it is surjective. -/
public theorem surjective_adicQuotientSystem_map_succ {A : Type u} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    Function.Surjective ((adicQuotientSystem I M).map (homOfLE (Nat.le_succ n)).op).hom := by
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- A general transition of the tower of ideal-power quotients is the quotient factorization. -/
public theorem idealPowerQuotientModuleSystem_map
    {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} (h : n ≤ m) :
    (idealPowerQuotientModuleSystem I).map (homOfLE h).op =
      torProZeroTransition I (Nat.add_le_add_right h 1) := by
  refine NoetherianAdicCompletion.ofOpSequence_map_eq _
    (fun m n h => torProZeroTransition I (Nat.add_le_add_right h 1)) ?_ ?_ m n h <;>
  · intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro a
    rfl

/-- Tensoring the tower of ideal-power quotients with `M` is the tower of adic quotients of
`M`, by `M ⊗ A/Iⁿ⁺¹ ≅ M/Iⁿ⁺¹M`. -/
public def adicQuotientSystemTensorIso {A : Type u} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) :
    adicQuotientSystem I M ≅
      idealPowerQuotientModuleSystem I ⋙ MonoidalCategory.tensorLeft M := by
  refine NatIso.ofComponents (fun n =>
    (TensorProduct.tensorQuotEquivQuotSMul M (I ^ (n.unop + 1))).symm.toModuleIso) ?_
  intro n m f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  change (TensorProduct.tensorQuotEquivQuotSMul M (I ^ (m.unop + 1))).symm
      (Submodule.Quotient.mk x) =
    (((idealPowerQuotientModuleSystem I).map f).hom.lTensor M)
      ((TensorProduct.tensorQuotEquivQuotSMul M (I ^ (n.unop + 1))).symm
        (Submodule.Quotient.mk x))
  simp only [TensorProduct.tensorQuotEquivQuotSMul_symm_mk]
  congr 1
  have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
  rw [hf, idealPowerQuotientModuleSystem_map]
  rfl

/-- A uniform shift killing the transitions of `Tor_i(Q, A/Iⁿ)` kills those of the tower
`Tor_i(Q, A/Iⁿ⁺¹)` at every level. -/
public theorem torIdealPowerSystem_uniform_proZero
    {A : Type u} [CommRing A] (I : Ideal A) (Q : ModuleCat.{u} A)
    (i c : ℕ)
    (hQ : ∀ n : ℕ, c ≤ n → ((Tor (ModuleCat.{u} A) i).obj Q).map
      (torProZeroTransition I (Nat.sub_le n c)) = 0) :
    ∀ n : ℕ, (torIdealPowerSystem I Q i).map
      (homOfLE (Nat.le_add_right n c)).op = 0 := by
  intro n
  change ((Tor' (ModuleCat.{u} A) i).obj Q).map _ = 0
  rw [idealPowerQuotientModuleSystem_map]
  let e := (Tor_iso_Tor' A i).app Q
  apply (cancel_epi (e.hom.app (torProZeroQuot I (n + c + 1)))).mp
  have hz : ((Tor (ModuleCat.{u} A) i).obj Q).map
      (torProZeroTransition I (Nat.add_le_add_right (Nat.le_add_right n c) 1)) = 0 := by
    have transfer (k m : ℕ) (hk : c ≤ k) (he : k - c = m) (hm : m ≤ k) :
        ((Tor (ModuleCat.{u} A) i).obj Q).map (torProZeroTransition I hm) = 0 := by
      subst m
      exact hQ k hk
    exact transfer (n + c + 1) (n + 1) (by omega) (by omega) _
  refine (e.hom.naturality
    (torProZeroTransition I (Nat.add_le_add_right (Nat.le_add_right n c) 1))).symm.trans ?_
  rw [hz, zero_comp]
  exact comp_zero.symm

/-- The cokernel model for the first derived inverse limit of a countable inverse system in
an abelian category. -/
public noncomputable def firstDerivedInverseLimit
    {C : Type u} [Category.{v} C] [Abelian C] [HasProductsOfShape ℕ C]
    (F : ℕᵒᵖ ⥤ C) : C :=
  cokernel (Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n -
      Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) (n + 1) ≫
        F.map (homOfLE (Nat.le_succ n)).op)

/-- The inverse system whose `n`th term is `H^p(K ⊗ᴸ A/I^(n+1))`. -/
public noncomputable def derivedTensorHomologySystem
    {A : Type u} [CommRing A] (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) p

end AdicCompletionTor
end

end

section


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AdicCompletionTor

variable {R : Type u} [CommRing R]

/-- The cochain complex of the chosen projective resolution of a module is K-flat. -/
public lemma cochainComplex_kFlat (M : ModuleCat.{u} R) :
    (ProjectiveResolution.of M).cochainComplex.KFlat := by
  let P := (ProjectiveResolution.of M).cochainComplex
  let : ∀ n : ℤ, Module.Flat R (P.X n) := fun n => inferInstance
  exact (CochainComplex.KFlat.kFlat_of_flat P 0)

/-- Tensoring on the left with a K-flat complex preserves quasi-isomorphisms. -/
public lemma quasiIso_tensorLeft_map (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    {P S : CochainComplex (ModuleCat.{u} R) ℤ} (q : P ⟶ S) [QuasiIso q] :
    QuasiIso (K ◁ q) := by
  let := Classical.choose (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R)
  have hqR : QuasiIso ((TrightCochain K).map q) := by
    have hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
        ((HomotopyCategory.quotient _ _).map q) :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 ‹QuasiIso q›
    have hh := (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK)
      ((HomotopyCategory.quotient _ _).map q) hf
    change HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _ ⋙ Tright K).map q) at hh
    unfold Tright at hh
    rw [descendF_comp_quotient] at hh
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 hh
  have heq : (K ◁ q) ≫ (β_ K S).hom = (β_ K P).hom ≫ (TrightCochain K).map q := by
    change (K ◁ q) ≫ (β_ K S).hom = (β_ K P).hom ≫ (q ⊗ₘ 𝟙 K)
    rw [BraidedCategory.braiding_naturality_right, tensorHom_id]
  have hβP : QuasiIso (β_ K P).hom := quasiIso_of_isIso _
  have hβS : QuasiIso (β_ K S).hom := quasiIso_of_isIso _
  have hc : QuasiIso ((K ◁ q) ≫ (β_ K S).hom) := by
    rw [heq]
    exact quasiIso_comp (hφ := hβP) (hφ' := hqR) _ _
  exact (quasiIso_iff_comp_right (hφ' := hβS) _ _).1 hc

/-- Tensoring on the left with a K-flat complex, followed by the localization functor to the
derived category, inverts quasi-isomorphisms. -/
public lemma tensorLeft_inverts (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
      (TleftCochain K ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : QuasiIso f := hf
  have := quasiIso_tensorLeft_map K hK f
  exact Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso _ _) _ (show QuasiIso (K ◁ f) from this)

/-- Tensoring on the left with a K-flat complex, descended to the derived category. -/
public abbrev liftedTensorLeft (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (TleftCochain K ⋙ DerivedCategory.Q) (tensorLeft_inverts K hK)
    DerivedCategory.Q

attribute [local instance] CochainComplex.DerivedTensor.kFlatHomotopyQ_isLocalization

set_option backward.isDefEq.respectTransparency false in
/-- On K-flat complexes, the derived tensor product with a K-flat complex `K` agrees with
`AdicCompletionTor.liftedTensorLeft`, tensoring on the left with `K` descended to the derived
category. -/
public def tensorKFlatComparison (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) :
    CochainComplex.DerivedTensor.kFlatHomotopyQ R ⋙ T.tensor.obj (DerivedCategory.Q.obj K) ≅
      CochainComplex.DerivedTensor.kFlatHomotopyQ R ⋙ liftedTensorLeft K hK := by
  let qc := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  let fac := Localization.fac (TleftCochain K ⋙ DerivedCategory.Q) (tensorLeft_inverts K hK)
    DerivedCategory.Q
  refine NatIso.ofComponents (fun X =>
    (T.tensor.obj (DerivedCategory.Q.obj K)).mapIso (qc.app X.obj.as) ≪≫
    T.comparison K X.obj.as hK X.property ≪≫ (fac.app X.obj.as).symm ≪≫
    (liftedTensorLeft K hK).mapIso (qc.app X.obj.as).symm) ?_
  rintro ⟨⟨X⟩, hX⟩ ⟨⟨Y⟩, hY⟩ ⟨⟨g⟩⟩
  change CochainComplex.KFlat X at hX
  change CochainComplex.KFlat Y at hY
  change X ⟶ Y at g
  have hn : (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
      (T.comparison K Y hK hY).hom =
    (T.comparison K X hK hX).hom ≫ DerivedCategory.Q.map (K ◁ g) := by
    have h := T.comparison_naturality (𝟙 K) g hK hK hX hY
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h
    rw [h]
    exact congrArg (fun f => (T.comparison K X hK hX).hom ≫ DerivedCategory.Q.map f)
      (id_tensorHom K g)
  have hf := fac.inv.naturality g
  dsimp only [Functor.comp_map] at hf
  change (T.tensor.obj (DerivedCategory.Q.obj K)).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map g)) ≫ _ =
    _ ≫ (liftedTensorLeft K hK).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map g))
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  rw [← Functor.map_comp_assoc, DerivedCategory.quotientCompQhIso_hom_naturality,
    Functor.map_comp_assoc, reassoc_of% hn]
  erw [reassoc_of% hf]
  rw [← Functor.map_comp, ← Functor.map_comp, DerivedCategory.quotientCompQhIso_inv_naturality]

/-- For a K-flat complex `K`, the derived tensor product with `K` is isomorphic to
`AdicCompletionTor.liftedTensorLeft`, tensoring on the left with `K` descended to the derived
category. -/
public def tensorKFlatIso (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) :
    T.tensor.obj (DerivedCategory.Q.obj K) ≅ liftedTensorLeft K hK :=
  (Localization.fullyFaithfulWhiskeringLeft (CochainComplex.DerivedTensor.kFlatHomotopyQ R)
    (CochainComplex.DerivedTensor.kFlatHomotopyQuasiIso R) _).preimageIso
    (tensorKFlatComparison T K hK)

variable (R) in
/-- `N ↦ K ⊗ N`, applied termwise to a complex `K`. -/
public def complexTensorRight {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) :
    ModuleCat.{u} R ⥤ HomologicalComplex (ModuleCat.{u} R) c where
  obj N := (((tensoringRight _).obj N).mapHomologicalComplex c).obj K
  map g := (NatTrans.mapHomologicalComplex ((tensoringRight _).map g) c).app K
  map_id N := by ext; simp
  map_comp f g := by ext; simp

/-- Termwise tensoring with a module commutes with extending a complex along an embedding of
complex shapes. -/
public def complexTensorRightExtendIso {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (e : c.Embedding c') (K : HomologicalComplex (ModuleCat.{u} R) c) :
    complexTensorRight R (K.extend e) ≅ complexTensorRight R K ⋙ e.extendFunctor _ :=
  NatIso.ofComponents
    (fun N => (HomologicalComplex.mapHomologicalComplexExtendIso
      ((tensoringRight _).obj N) K e).symm)
    (fun g => HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality_functor
      _ K ((tensoringRight _).map g) e)

/-- For a projective resolution `P` of `M`, the homology in degree `j` of the termwise tensor
product `P ⊗ N` is `Tor'_j(M, N)`, naturally in `N`. -/
public def torIsoHomology (M : ModuleCat.{u} R) (P : ProjectiveResolution M) (j : ℕ) :
    complexTensorRight R P.complex ⋙ HomologicalComplex.homologyFunctor _ _ j ≅
      (Tor' (ModuleCat.{u} R) j).obj M :=
  NatIso.ofComponents (fun N => (P.isoLeftDerivedObj ((tensoringRight _).obj N) j).symm) (by
    intro N N' g
    rw [Tor'_obj_map, ProjectiveResolution.leftDerived_app_eq _ P]
    simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, Iso.symm_hom]
    exact (Iso.inv_hom_id_assoc _ _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Placing a module in degree zero of a chain complex and extending along
`ComplexShape.embeddingDownNat` gives the cochain complex concentrated in degree zero. -/
public def singleExtendIso :
    ChainComplex.single₀ (ModuleCat.{u} R) ⋙ ComplexShape.embeddingDownNat.extendFunctor _ ≅
      CochainComplex.singleFunctor (ModuleCat.{u} R) 0 :=
  NatIso.ofComponents (fun N => HomologicalComplex.extendSingleIso _ N 0 0 (by simp)) (by
    intro N N' g
    apply HomologicalComplex.to_single_hom_ext
    simp only [Functor.comp_obj, HomologicalComplex.single, ↓dreduceIte,
      CochainComplex.singleFunctor,
      Functor.comp_map,
      ComplexShape.Embedding.extendFunctor_map, HomologicalComplex.comp_f,
      HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := 0) (i' := 0) (by simp),
      ChainComplex.single₀_obj_zero, ChainComplex.single₀_map_f_zero,
      HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      Category.comp_id, Category.assoc, ↓reduceDIte, eqToHom_refl, Category.id_comp]
    erw [Iso.inv_hom_id, Category.comp_id]
    rfl)

/-- The inclusion of the termwise tensor product `K ⊗ N` into the total tensor product of `K`
with the module `N` placed in degree zero. -/
public def tensorSingleInclusion (N : ModuleCat.{u} R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (complexTensorRight R K).obj N ⟶
      (TleftCochain K).obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) where
  f n := HomologicalComplex.ιTensorObj K
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) n 0 n (add_zero n)
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    change HomologicalComplex.ιMapBifunctor K _ (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ) n 0 n (add_zero n) ≫
      (HomologicalComplex.mapBifunctor K _ (curriedTensor (ModuleCat.{u} R))
        (ComplexShape.up ℤ)).d n (n + 1) = _
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show n + 1 = n + 1 from rfl) 0 (n + 1) (add_zero _),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ n (show (0 : ℤ) + 1 = 1 from rfl) (n + 1) rfl]
    simp
    rfl

/-- The inclusion `AdicCompletionTor.tensorSingleInclusion` is an isomorphism: the total tensor
product of a complex with a module placed in degree zero is the termwise tensor product. -/
public lemma tensorSingleInclusion_isIso (N : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) : IsIso (tensorSingleInclusion N K) := by
  have hn : ∀ n, IsIso ((tensorSingleInclusion N K).f n) := by
    intro n
    let p : ((TleftCochain K).obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)).X n ⟶
        K.X n ⊗ N :=
      HomologicalComplex.mapBifunctorDesc (K₁ := K)
        (K₂ := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)
        (F := curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ) (fun i j h =>
        if hj : j = 0 then eqToHom (by
          subst hj
          have hi : i = n := by simpa using h
          subst hi
          rfl)
        else 0)
    have hp : (tensorSingleInclusion N K).f n ≫ p = 𝟙 _ := by
      dsimp [tensorSingleInclusion, p, HomologicalComplex.ιTensorObj]
      erw [HomologicalComplex.ι_mapBifunctorDesc]
      simp
      rfl
    refine ⟨p, hp, ?_⟩
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    by_cases hj : j = 0
    · subst hj
      have hi : i = n := by simpa using h
      subst hi
      change (tensorSingleInclusion N K).f i ≫ p ≫ _ = _
      erw [← Category.assoc, hp, Category.id_comp]
    · exact (((tensoringLeft (ModuleCat.{u} R)).obj (K.X i)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N j hj)).eq_of_src _ _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Termwise tensoring of a complex `K` with a module is naturally isomorphic to the total tensor
product of `K` with that module placed in degree zero. -/
public def tensorSingleIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    complexTensorRight R K ≅ CochainComplex.singleFunctor (ModuleCat.{u} R) 0 ⋙ TleftCochain K := by
  have := fun N => tensorSingleInclusion_isIso N K
  refine NatIso.ofComponents (fun N => asIso (tensorSingleInclusion N K)) ?_
  intro N N' g
  ext n : 1
  dsimp [tensorSingleInclusion, complexTensorRight, TleftCochain, HomologicalComplex.ιTensorObj]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp [CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]
  rfl

/-- The tower `A/I^(n+1)` in the derived category,
`NoetherianAdicCompletion.idealPowerQuotientSystem I`, is the module tower
`AdicCompletionTor.idealPowerQuotientModuleSystem I` placed in degree zero. -/
public def quotientSystemIso {A : Type u} [CommRing A] (I : Ideal A) :
    NoetherianAdicCompletion.idealPowerQuotientSystem I ≅ idealPowerQuotientModuleSystem I ⋙
      (ChainComplex.single₀ (ModuleCat.{u} A) ⋙
        ComplexShape.embeddingDownNat.extendFunctor _ ⋙ DerivedCategory.Q) := by
  let φ : NoetherianAdicCompletion.idealPowerQuotientSystem I ⟶ idealPowerQuotientModuleSystem I ⋙
      (ChainComplex.single₀ (ModuleCat.{u} A) ⋙
        ComplexShape.embeddingDownNat.extendFunctor _ ⋙ DerivedCategory.Q) :=
    NatTrans.ofOpSequence (fun n => 𝟙 _) (by
      intro n
      erw [Category.comp_id, Category.id_comp]
      simp only [Functor.comp_map]
      unfold NoetherianAdicCompletion.idealPowerQuotientSystem idealPowerQuotientModuleSystem
      rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
      rfl)
  have : ∀ n, IsIso (φ.app n) := fun n => by
    change IsIso (𝟙 _)
    infer_instance
  have := NatIso.isIso_of_isIso_app φ
  exact asIso φ

/-- The cohomology of `M ⊗^𝐋 N` in the cohomological degree `q` of the homological degree `j`,
with `N` placed in degree zero through chain complexes, is `Tor'_j(M, N)`, naturally in `N`. -/
public def derivedTensorTorIso (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (M : ModuleCat.{u} R) (j : ℕ) (q : ℤ)
    (hq : ComplexShape.embeddingDownNat.f j = q) :
    (ChainComplex.single₀ (ModuleCat.{u} R) ⋙
        ComplexShape.embeddingDownNat.extendFunctor _ ⋙ DerivedCategory.Q) ⋙
      T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R) q ≅
      (Tor' (ModuleCat.{u} R) j).obj M := by
  let P := ProjectiveResolution.of M
  let Pc := P.cochainComplex
  have hPc : Pc.KFlat := cochainComplex_kFlat M
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) q
  let eS : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M ≅ DerivedCategory.Q.obj Pc :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M ≪≫
      (asIso (DerivedCategory.Q.map P.π')).symm
  let fac := Localization.fac (TleftCochain Pc ⋙ DerivedCategory.Q) (tensorLeft_inverts Pc hPc)
    DerivedCategory.Q
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerRight singleExtendIso DerivedCategory.Q)
      (T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⋙ H) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor (ModuleCat.{u} R) 0 ⋙ DerivedCategory.Q)
      (Functor.isoWhiskerRight (T.tensor.mapIso eS) H) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor (ModuleCat.{u} R) 0 ⋙ DerivedCategory.Q)
      (Functor.isoWhiskerRight (tensorKFlatIso T Pc hPc) H) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor (ModuleCat.{u} R) 0)
      (Functor.isoWhiskerRight fac H) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor (ModuleCat.{u} R) 0 ⋙ TleftCochain Pc)
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) q) ≪≫
    Functor.isoWhiskerRight (tensorSingleIso Pc).symm
      (HomologicalComplex.homologyFunctor _ _ q) ≪≫
    Functor.isoWhiskerRight (complexTensorRightExtendIso ComplexShape.embeddingDownNat P.complex)
      (HomologicalComplex.homologyFunctor _ _ q) ≪≫
    Functor.isoWhiskerLeft (complexTensorRight R P.complex)
      (Stacks.DerivedIndexing.extendHomologyNatIso ComplexShape.embeddingDownNat hq) ≪≫
    torIsoHomology M P j

/-- **`H^{-j}(M ⊗^𝐋_R N) ≅ Tor'_j(M, N)`.** The derived tensor product of two modules, each
placed in degree zero, has the `Tor` modules of the pair as its cohomology: in cohomological
degree `-j` it is `Tor'_j(M, N)`, the `j`-th left derived functor of `- ⊗_R N` evaluated at `M`.

This is the single-module reading of `AdicCompletionTor.derivedTensorTorIso`, whose two
arguments are placed in degree zero by `CochainComplex.singleFunctor _ 0` rather than, as there,
by `ChainComplex.single₀` followed by the extension of `ComplexShape.embeddingDownNat`.

The isomorphism is produced rather than named because the comparison it is assembled from is
local to this file. -/
public theorem nonempty_derivedTensorSingleHomology_iso_Tor'
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (M N : ModuleCat.{u} R) (j : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(j : ℤ))).obj
        ((T.tensor.obj (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))).obj
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N))) ≅
      ((Tor' (ModuleCat.{u} R) j).obj M).obj N) :=
  ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(j : ℤ))).mapIso
      (Iso.app (T.tensor.mapIso
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M).symm) _ ≪≫
        (T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).mapIso
          (DerivedCategory.Q.mapIso (singleExtendIso.app N)).symm) ≪≫
    (derivedTensorTorIso T M j (-(j : ℤ)) (by simp)).app N⟩

/-- The cohomology in degree `q = -j` of the tower `M ⊗^𝐋 A/I^(n+1)` is the Tor tower
`AdicCompletionTor.torIdealPowerSystem I M j`. -/
public def torTowerIso {A : Type u} [CommRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A) (M : ModuleCat.{u} A) (j : ℕ) (q : ℤ)
    (hq : -(j : ℤ) = q) :
    (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) q ≅ torIdealPowerSystem I M j :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerRight (quotientSystemIso I) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (idealPowerQuotientModuleSystem I)
      (Functor.associator _ _ _ ≪≫ derivedTensorTorIso T M j q (by simpa using hq))

private def firstDerivedInverseLimitIso
    {C : Type*} [Category* C] [Abelian C] [HasProductsOfShape ℕ C]
    {F G : ℕᵒᵖ ⥤ C} (e : F ≅ G) :
    firstDerivedInverseLimit F ≅ firstDerivedInverseLimit G := by
  have hcomm : ∀ {F G : ℕᵒᵖ ⥤ C} (α : F ⟶ G),
      (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) ≫ Limits.Pi.map (fun n => α.app (Opposite.op n)) =
      Limits.Pi.map (fun n => α.app (Opposite.op n)) ≫
        (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj (Opposite.op n)) n -
          Pi.π (fun n : ℕ ↦ G.obj (Opposite.op n)) (n + 1) ≫
            G.map (homOfLE (Nat.le_succ n)).op) := by
    intro F G α
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π, Preadditive.sub_comp,
      Preadditive.comp_sub, Pi.map_π_assoc]
    rw [α.naturality]
  refine
    { hom := cokernel.map _ _ (Limits.Pi.map fun n => e.hom.app _)
        (Limits.Pi.map fun n => e.hom.app _) (hcomm e.hom)
      inv := cokernel.map _ _ (Limits.Pi.map fun n => e.inv.app _)
        (Limits.Pi.map fun n => e.inv.app _) (hcomm e.inv)
      hom_inv_id := ?_
      inv_hom_id := ?_ } <;>
  · dsimp only [firstDerivedInverseLimit]
    ext
    simp only [cokernel.π_desc_assoc, cokernel.map, Category.assoc, cokernel.π_desc,
      Category.comp_id]
    rw [← Category.assoc, Limits.Pi.map_comp_map]
    simp

private lemma exists_shortExact_of_iso {C : Type*} [Category* C] [Abelian C]
    {X₁ Y₁ X₂ X₃ Y₃ : C} (e₁ : X₁ ≅ Y₁) (e₃ : X₃ ≅ Y₃)
    (h : ∃ (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) :
    ∃ (a : Y₁ ⟶ X₂) (b : X₂ ⟶ Y₃) (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  obtain ⟨a, b, w, hs⟩ := h
  refine ⟨e₁.inv ≫ a, b ≫ e₃.hom, by simp [reassoc_of% w], ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ hs
  exact ShortComplex.isoMk e₁ (Iso.refl _) e₃ (by simp) (by simp)

private theorem homology_shortExact_of_isDerivedLimit
    (A : Type u) [CommRing A]
    (F : CategoryTheory.Functor ℕᵒᵖ (DerivedCategory (ModuleCat.{u} A)))
    [HasProduct fun n : ℕ ↦ F.obj (Opposite.op n)]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDerivedLimit F K) (p : ℤ) :
    let H := fun q ↦ F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) q
    ∃ (a : firstDerivedInverseLimit (H (p - 1)) ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K)
      (b : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K ⟶ limit (H p))
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  dsimp
  obtain ⟨a, b, hT, h⟩ :=
    DerivedCategory.isDerivedLimit_homology_shortExact F K hK
  obtain ⟨e, i, q, w, he, hi, hq, hs⟩ := h p
  exact ⟨i, q, w, hs⟩

private theorem module_homology_shortExact
    (A : Type u) [CommRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (M : ModuleCat.{u} A) (i : ℕ)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDerivedLimit
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) K) :
    ∃ (a : firstDerivedInverseLimit (torIdealPowerSystem I M (i + 1)) ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).obj K)
      (b : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).obj K ⟶
        limit (torIdealPowerSystem I M i)) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact := by
  exact exists_shortExact_of_iso
    (firstDerivedInverseLimitIso (torTowerIso I T M (i + 1) (-(i : ℤ) - 1) (by push_cast; ring)))
    (HasLimit.isoOfNatIso (torTowerIso I T M i (-(i : ℤ)) rfl))
    (homology_shortExact_of_isDerivedLimit A _ K hK (-(i : ℤ)))

private noncomputable def quotientPowEquiv
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    A ⧸ I ^ (n + 1) ≃+*
      ULift.{u} A ⧸ (I.comap ULift.ringEquiv.toRingHom) ^ (n + 1) :=
  Ideal.quotientEquiv (I ^ (n + 1))
    ((I.comap ULift.ringEquiv.toRingHom) ^ (n + 1))
    (ULift.ringEquiv.symm : A ≃+* ULift.{u} A) (by
      rw [Ideal.map_pow, Ideal.map_comap_of_equiv]
      rfl)


private theorem quotientPowEquiv_transition
    (A : Type u) [CommRing A] (I : Ideal A)
    (m n : ℕ) (h : n ≤ m) :
    (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) :
        (ULift.{u} A ⧸ (I.comap ULift.ringEquiv.toRingHom) ^ (m + 1)) →+*
        (ULift.{u} A ⧸ (I.comap ULift.ringEquiv.toRingHom) ^ (n + 1))).comp
      (quotientPowEquiv A I m).toRingHom =
    (quotientPowEquiv A I n).toRingHom.comp
      (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))) := by
  apply RingHom.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ a =>
    rfl


private noncomputable def quotientModuleMap
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ((AdicKoszul.moduleUniverseLift.{u,u} A).obj
      (ModuleCat.of A (A ⧸ I ^ (n + 1)))) ⟶
      ModuleCat.of (ULift.{u} A)
        (ULift.{u} A ⧸ (I.comap ULift.ringEquiv.toRingHom) ^ (n + 1)) := by
  let e := quotientPowEquiv A I n
  refine ModuleCat.ofHom {
    toFun := fun x => e x.down
    map_add' := fun x y => by
      change e (x.down + y.down) = e x.down + e y.down
      exact e.map_add _ _
    map_smul' := fun r x => by
      change e (r.down • x.down) = r • e x.down
      change e ((Ideal.Quotient.mk (I ^ (n + 1)) r.down) * x.down) =
        (Ideal.Quotient.mk ((I.comap ULift.ringEquiv.toRingHom) ^ (n + 1)) r) * e x.down
      rw [e.map_mul]
      rfl
  }


private noncomputable def quotientModuleIso
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ((AdicKoszul.moduleUniverseLift.{u,u} A).obj
      (ModuleCat.of A (A ⧸ I ^ (n + 1)))) ≅
      ModuleCat.of (ULift.{u} A)
        (ULift.{u} A ⧸ (I.comap ULift.ringEquiv.toRingHom) ^ (n + 1)) := by
  haveI : IsIso (quotientModuleMap A I n) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨fun _ _ h => congrArg ULift.up ((quotientPowEquiv A I n).injective h),
        fun y => ⟨ULift.up ((quotientPowEquiv A I n).symm y),
          (quotientPowEquiv A I n).apply_symm_apply y⟩⟩
  exact asIso (quotientModuleMap A I n)


-- unfolding the quotient-by-a-power transition maps termwise is expensive
set_option backward.isDefEq.respectTransparency false in
private theorem quotientModuleMap_transition
    (A : Type u) [CommRing A] (I : Ideal A)
    (m n : ℕ) (h : n ≤ m) :
    (AdicKoszul.moduleUniverseLift.{u,u} A).map
        (NoetherianAdicCompletion.idealPowerQuotientTransition I m n h) ≫
      quotientModuleMap A I n =
    quotientModuleMap A I m ≫
      ModuleCat.ofHom ((Ideal.Quotient.factorₐ (ULift.{u} A)
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).toLinearMap) := by
  ext x
  exact (RingHom.congr_fun (quotientPowEquiv_transition A I m n h) x.down).symm


private noncomputable def quotientModuleSystemIso
    (A : Type u) [CommRing A] (I : Ideal A) :
    AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙
      AdicKoszul.moduleUniverseLift.{u,u} A ≅
    AdicCompletionTor.idealPowerQuotientModuleSystem
      (I.comap ULift.ringEquiv.toRingHom) := by
  let α : AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙
      AdicKoszul.moduleUniverseLift.{u,u} A ⟶
      AdicCompletionTor.idealPowerQuotientModuleSystem
        (I.comap ULift.ringEquiv.toRingHom) :=
    NatTrans.ofOpSequence (fun n => quotientModuleMap A I n) (by
      intro n
      rw [Functor.comp_map, idealPowerQuotientModuleSystem_map_succ,
        idealPowerQuotientModuleSystem_map_succ]
      exact quotientModuleMap_transition A I (n + 1) n (Nat.le_succ n))
  haveI (n : ℕᵒᵖ) : IsIso (α.app n) :=
    inferInstanceAs (IsIso (quotientModuleIso A I n.unop).hom)
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α


private noncomputable def uliftModuleIdIso (A : Type u) [CommRing A] :
    ModuleCat.uliftFunctor.{u,u} A ≅ 𝟭 (ModuleCat.{u} A) := by
  refine NatIso.ofComponents (fun M => {
    hom := ModuleCat.ofHom (ULift.moduleEquiv (R := A) (M := M)).toLinearMap
    inv := ModuleCat.ofHom (ULift.moduleEquiv (R := A) (M := M)).symm.toLinearMap
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl
  }) fun _ => by ext; rfl

private theorem uliftModuleIsEquivalence (A : Type u) [CommRing A] :
    (ModuleCat.uliftFunctor.{u,u} A).IsEquivalence :=
  Functor.isEquivalence_of_iso (uliftModuleIdIso A).symm


private theorem liftedModuleIsEquivalence (A : Type u) [CommRing A] :
    (AdicKoszul.moduleUniverseLift.{u,u} A).IsEquivalence := by
  let : (ModuleCat.uliftFunctor.{u,u} A).IsEquivalence := uliftModuleIsEquivalence A
  let : (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom).IsEquivalence := by
    change (StacksDraft.DerivedHom.uliftModuleEquivalence.{u,u,u} A).inverse.IsEquivalence
    infer_instance
  change (ModuleCat.uliftFunctor.{u,u} A ⋙ ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom).IsEquivalence
  infer_instance


private theorem liftedDerivedIsEquivalence (A : Type u) [CommRing A] :
    (AdicKoszul.derivedUniverseLift.{u,u} A).IsEquivalence := by
  let : (AdicKoszul.moduleUniverseLift.{u,u} A).IsEquivalence :=
    liftedModuleIsEquivalence A
  exact Stacks.Injectives.mapDerivedCategory_isEquivalence
    (AdicKoszul.moduleUniverseLift.{u,u} A)



/-- Any two derived tensor products agree after fixing their first argument: both compute the
total tensor product of a K-flat resolution. -/
public noncomputable def tensorFunctorIso
    (A : Type u) [CommRing A]
    (T U : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    T.tensor.obj K ≅ U.tensor.obj K := by
  classical
  let resolution :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage K)
  let P := Classical.choose resolution
  let f := Classical.choose (Classical.choose_spec resolution)
  let hP : P.KFlat := (Classical.choose_spec (Classical.choose_spec resolution)).1
  let hf : QuasiIso f := (Classical.choose_spec (Classical.choose_spec resolution)).2.2.1
  letI : QuasiIso f := hf
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let comparison : T.tensor.obj (DerivedCategory.Q.obj P) ≅
      U.tensor.obj (DerivedCategory.Q.obj P) :=
    ModuleSystemRlimTensor.derivedTensorComplexIso A T P hP ≪≫
      (ModuleSystemRlimTensor.derivedTensorComplexIso A U P hP).symm
  exact T.tensor.mapIso e.symm ≪≫ comparison ≪≫ U.tensor.mapIso e

private noncomputable def tensorPowerTowerIso
    (A : Type u) [CommRing A] (I : Ideal A)
    (T U : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ≅
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ U.tensor.obj K) :=
  Functor.isoWhiskerLeft _ (tensorFunctorIso A T U K)

private theorem liftedReflector
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)
    let U := AdicKoszul.derivedUniverseLift.{u,u} A
    let J := I.comap ULift.ringEquiv.toRingHom
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun K ↦ IsDerivedComplete I K
    ∃ L : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory,
      Nonempty (L ⊣ P.ι) ∧ ∀ K,
        IsDerivedLimit
            (NoetherianAdicCompletion.idealPowerQuotientSystem J ⋙ T.tensor.obj (U.obj K))
          (U.obj ((L ⋙ P.ι).obj K)) := by
  dsimp
  obtain ⟨L, adj, π, hlim, _⟩ :=
    NoetherianAdicCompletion.idealPowerDerivedLimit_isLeftAdjoint.{u,u} A I
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A))
  exact ⟨L, ⟨adj⟩, fun K ↦ (hlim K).isDerivedLimit⟩

private noncomputable def quotientSystemSingleIso
    (A : Type u) [CommRing A] (I : Ideal A) :
    NoetherianAdicCompletion.idealPowerQuotientSystem I ≅
      idealPowerQuotientModuleSystem I ⋙
        DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 :=
  quotientSystemIso I ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (singleExtendIso (R := A)) DerivedCategory.Q) ≪≫
    Functor.isoWhiskerLeft _
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).symm


-- this composite of six whiskered isomorphisms of towers is expensive to elaborate
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def quotientDerivedSystemIso
    (A : Type u) [CommRing A] (I : Ideal A) :
    NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        AdicKoszul.derivedUniverseLift.{u,u} A ≅
      NoetherianAdicCompletion.idealPowerQuotientSystem
        (I.comap (ULift.ringEquiv.{u,u} (R := A)).toRingHom) := by
  let F := AdicKoszul.moduleUniverseLift.{u,u} A
  let U := AdicKoszul.derivedUniverseLift.{u,u} A
  let J : Ideal (ULift.{u} A) :=
    I.comap (ULift.ringEquiv.{u,u} (R := A)).toRingHom
  let X := idealPowerQuotientModuleSystem I
  let Y := idealPowerQuotientModuleSystem J
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let S' := DerivedCategory.singleFunctor (ModuleCat.{u} (ULift.{u} A)) 0
  let e₁ : (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ U) ≅ (X ⋙ S) ⋙ U :=
    Functor.isoWhiskerRight (quotientSystemSingleIso A I) U
  let e₂ : (X ⋙ S) ⋙ U ≅ X ⋙ (S ⋙ U) := Functor.associator X S U
  let e₃ : X ⋙ (S ⋙ U) ≅ X ⋙ (F ⋙ S') :=
    Functor.isoWhiskerLeft X (F.mapDerivedCategorySingleFunctor 0)
  let e₄ : X ⋙ (F ⋙ S') ≅ (X ⋙ F) ⋙ S' := (Functor.associator X F S').symm
  let e₅ : (X ⋙ F) ⋙ S' ≅ Y ⋙ S' :=
    Functor.isoWhiskerRight (quotientModuleSystemIso A I) S'
  let e₆ : Y ⋙ S' ≅ NoetherianAdicCompletion.idealPowerQuotientSystem J :=
    (quotientSystemSingleIso (ULift.{u} A) J).symm
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆



private noncomputable def extensionScalarsUliftModuleIso
    (A : Type u) [CommRing A] :
    ModuleCat.extendScalars.{u,u,u}
        (ULift.ringEquiv.{u,u} (R := A)).symm.toRingHom ≅
      AdicKoszul.moduleUniverseLift.{u,u} A := by
  let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv.{u,u} (R := A))
  let f := (ULift.ringEquiv.{u,u} (R := A)).symm.toRingHom
  let a : ModuleCat.extendScalars.{u,u,u} f ⊣ e.inverse :=
    ModuleCat.extendRestrictScalarsAdj f
  let b : e.functor ⊣ e.inverse := e.toAdjunction
  exact Adjunction.leftAdjointUniq a b ≪≫
    (Functor.isoWhiskerRight (uliftModuleIdIso A) e.functor ≪≫
      Functor.leftUnitor _).symm


-- identifying the chosen derived extension of scalars with the universe lift is expensive
private noncomputable def totalDerivedUliftIso
    (A : Type u) [CommRing A] :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u,u,u}
      (ULift.ringEquiv.{u,u} (R := A)).symm.toRingHom).functor ≅
      AdicKoszul.derivedUniverseLift.{u,u} A := by
  let f := (ULift.ringEquiv.{u,u} (R := A)).symm.toRingHom
  let F := ModuleCat.extendScalars.{u,u,u} f
  let G := AdicKoszul.moduleUniverseLift.{u,u} A
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u,u,u} f
  letI : G.IsEquivalence := liftedModuleIsEquivalence A
  letI : F.IsEquivalence :=
    Functor.isEquivalence_of_iso (extensionScalarsUliftModuleIso A).symm
  haveI : PreservesFiniteLimits F := inferInstance
  haveI : PreservesFiniteColimits F := inferInstance
  let hF := F.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso (ComplexShape.up ℤ)
  haveI : IsIso D.comparison :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts
      D.functor D.comparison hF
  let e₁ : DerivedCategory.Q ⋙ D.functor ≅
      DerivedCategory.Q ⋙ F.mapDerivedCategory :=
    asIso D.comparison ≪≫ F.mapDerivedCategoryFactors.symm
  let e₂ : DerivedCategory.Q ⋙ F.mapDerivedCategory ≅
      DerivedCategory.Q ⋙ G.mapDerivedCategory :=
    F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (extensionScalarsUliftModuleIso A)
          (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      G.mapDerivedCategoryFactors.symm
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    _ _ _ _ (e₁ ≪≫ e₂)


-- transporting the base-change isomorphism along the universe lift is expensive
private noncomputable def tensorUliftBifunctorIso
    (A : Type u) [CommRing A] (T : CochainComplex.DerivedTensor.DerivedTensorProduct A) :
    (Functor.uncurry.obj T.tensor) ⋙ AdicKoszul.derivedUniverseLift.{u,u} A ≅
      (AdicKoszul.derivedUniverseLift.{u,u} A).prod
        (AdicKoszul.derivedUniverseLift.{u,u} A) ⋙
          Functor.uncurry.obj
            (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
              (ULift.{u} A)).tensor := by
  let f := (ULift.ringEquiv.{u,u} (R := A)).symm.toRingHom
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u,u,u} f
  let U := AdicKoszul.derivedUniverseLift.{u,u} A
  let e : D.functor ≅ U := totalDerivedUliftIso A
  let C := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)
  let h := (CochainComplex.DerivedTensor.derivedExtensionScalarsTensorIso.{u,u,u}
    f T.toGeneral C.toGeneral D).iso
  exact Functor.isoWhiskerLeft (Functor.uncurry.obj T.tensor) e.symm ≪≫
    h.symm ≪≫
    Functor.isoWhiskerRight (NatIso.prod e e) (Functor.uncurry.obj C.tensor)


private noncomputable def tensorUliftFunctorIso
    (A : Type u) [CommRing A] (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    T.tensor.obj K ⋙ AdicKoszul.derivedUniverseLift.{u,u} A ≅
      AdicKoszul.derivedUniverseLift.{u,u} A ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)).tensor.obj
          ((AdicKoszul.derivedUniverseLift.{u,u} A).obj K) := by
  let e := tensorUliftBifunctorIso A T
  refine NatIso.ofComponents (fun X => e.app (K, X)) ?_
  intro X Y g
  have h := e.hom.naturality (show (K, X) ⟶ (K, Y) from (𝟙 K, g))
  simpa [Functor.comp_map] using h


/-- **The universe-lift comparison for the derived tensor product**, as a natural isomorphism of
functors: tensoring with a fixed object and then enlarging the universe is enlarging the universe
and then tensoring with its image. Only the existence of such a natural isomorphism is exported;
the chosen one is assembled from the base-change comparison for the derived tensor product, which
is not available outside this file. -/
public theorem nonempty_tensorUliftFunctorIso
    (A : Type u) [CommRing A] (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty (T.tensor.obj K ⋙ AdicKoszul.derivedUniverseLift.{u, u} A ≅
      AdicKoszul.derivedUniverseLift.{u, u} A ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)).tensor.obj
          ((AdicKoszul.derivedUniverseLift.{u, u} A).obj K)) :=
  ⟨tensorUliftFunctorIso A T K⟩


-- reflecting a derived limit along an equivalence needs a large triangle computation
/-- **A derived limit is reflected along an equivalence.** If `U` is a triangulated equivalence
preserving countable products and `U X` is a derived limit of the transported tower `F ⋙ U`, then
`X` is a derived limit of `F`.

This is the converse of `ModuleSystemRlimTensor.isDerivedLimit_map_of_iso`, which pushes a derived
limit *along* a product-preserving triangulated functor. The two together carry a derived limit
across the universe enlargement `AdicKoszul.derivedUniverseLift`, which is an equivalence exactly
when the module universe and the ring universe agree
(`AdicCompletionTor.liftedDerivedIsEquivalence`). -/
private theorem isDerivedLimit_reflect_of_equivalence
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (U : C ⥤ D) [U.IsEquivalence] [U.CommShift ℤ] [U.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) U]
    (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    [HasProduct fun n : ℕ => (F ⋙ U).obj ⟨n⟩]
    (X : C) (h : IsDerivedLimit (F ⋙ U) (U.obj X)) :
    IsDerivedLimit F X := by
  let P := ∏ᶜ fun n : ℕ => F.obj ⟨n⟩
  let Q := ∏ᶜ fun n : ℕ => (F ⋙ U).obj ⟨n⟩
  let p (n : ℕ) : U.obj P ⟶ U.obj (F.obj ⟨n⟩) :=
    U.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) n)
  have hp : IsLimit (Fan.mk (U.obj P) p) :=
    Fan.isLimitMapConeEquiv U _ _ (isLimitOfPreserves U (productIsProduct _))
  have hq : IsLimit (Fan.mk Q (fun n : ℕ => Pi.π (fun n : ℕ =>
      (F ⋙ U).obj ⟨n⟩) n)) := productIsProduct _
  let e : U.obj P ≅ Q := hp.conePointUniqueUpToIso hq
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = p n :=
    hp.conePointUniqueUpToIso_hom_comp hq ⟨n⟩
  have he' (n : ℕ) : e.inv ≫ p n = Pi.π _ n := by
    rw [← he n, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨a, δ, ha⟩ := h
  let dF : P ⟶ P := Pi.lift fun n : ℕ =>
    Pi.π _ n - Pi.π _ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let dG : Q ⟶ Q := Pi.lift fun n : ℕ =>
    Pi.π _ n - Pi.π _ (n + 1) ≫ (F ⋙ U).map (homOfLE (Nat.le_succ n)).op
  have hd : U.map dF ≫ e.hom = e.hom ≫ dG := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he n, Category.assoc, Pi.lift_comp_π,
      Preadditive.comp_sub, he n, ← Category.assoc, he (n + 1)]
    dsimp only [p, dF]
    rw [← U.map_comp, Pi.lift_comp_π, U.map_sub, U.map_comp]
    rfl
  let f : X ⟶ P := U.preimage (a ≫ e.inv)
  have hf : U.map f ≫ e.hom = a := by
    rw [U.map_preimage, Category.assoc, e.inv_hom_id, Category.comp_id]
  let g : P ⟶ X⟦(1 : ℤ)⟧ := U.preimage
    (e.hom ≫ δ ≫ (U.commShiftIso (1 : ℤ)).inv.app X)
  have hg : e.hom ≫ δ = U.map g ≫ (U.commShiftIso (1 : ℤ)).hom.app X := by
    rw [U.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  have hT : (Triangle.mk f dF g) ∈ distTriang C := by
    apply (U.map_distinguished_iff (Triangle.mk f dF g)).1
    let T : Triangle D := U.mapTriangle.obj (Triangle.mk f dF g)
    let S : Triangle D := Triangle.mk a dG δ
    have hTS : T ≅ S := Triangle.isoMk _ _ (Iso.refl _) e e
      (by
        change U.map f ≫ e.hom = 𝟙 _ ≫ a
        simpa using hf)
      hd
      (by
        change (U.map g ≫ (U.commShiftIso (1 : ℤ)).hom.app X) ≫
          (shiftFunctor D 1).map (𝟙 _) = e.hom ≫ δ
        simpa using hg.symm)
    exact Pretriangulated.isomorphic_distinguished S ha T hTS
  exact ⟨f, g, hT⟩

private noncomputable def tensorQuotientSystemIso
    (A : Type u) [CommRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
        AdicKoszul.derivedUniverseLift.{u,u} A ≅
      NoetherianAdicCompletion.idealPowerQuotientSystem
          (I.comap (ULift.ringEquiv.{u,u} (R := A)).toRingHom) ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)).tensor.obj
          ((AdicKoszul.derivedUniverseLift.{u,u} A).obj K) := by
  let F := NoetherianAdicCompletion.idealPowerQuotientSystem I
  let U := AdicKoszul.derivedUniverseLift.{u,u} A
  let V := (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
    (ULift.{u} A)).tensor.obj (U.obj K)
  exact Functor.associator F (T.tensor.obj K) U ≪≫
    Functor.isoWhiskerLeft F (tensorUliftFunctorIso A T K) ≪≫
    (Functor.associator F U V).symm ≪≫
    Functor.isoWhiskerRight (quotientDerivedSystemIso A I) V

-- assembling the reflector from the lifted one is expensive to elaborate
private theorem completion_reflector
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun K ↦ IsDerivedComplete I K
    ∃ L : CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} A)) P.FullSubcategory,
      Nonempty (L ⊣ P.ι) ∧
        ∀ K, IsDerivedLimit
          (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K)
          ((L ⋙ P.ι).obj K) := by
  dsimp
  let U := AdicKoszul.derivedUniverseLift.{u,u} A
  let J := I.comap (ULift.ringEquiv.{u,u} (R := A)).toRingHom
  let C := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)
  let : U.IsEquivalence := liftedDerivedIsEquivalence A
  let : PreservesLimitsOfShape (Discrete ℕ) U := inferInstance
  obtain ⟨L, adj, hlim⟩ := liftedReflector A I
  refine ⟨L, adj, ?_⟩
  intro K
  let F := NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K
  let G := NoetherianAdicCompletion.idealPowerQuotientSystem J ⋙ C.tensor.obj (U.obj K)
  let X := (L ⋙ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
    fun M => IsDerivedComplete I M).ι).obj K
  let : HasProduct (fun n : ℕ => G.obj ⟨n⟩) := inferInstance
  let e : F ⋙ U ≅ G := tensorQuotientSystemIso A I T K
  obtain ⟨hprod, hU⟩ := ModuleSystemRlimTensor.isDerivedLimit_map_of_iso
    (𝟭 _) G (F ⋙ U) e.symm (U.obj X) (hlim K)
  let : HasProduct (fun n : ℕ => (F ⋙ U).obj ⟨n⟩) := hprod
  exact isDerivedLimit_reflect_of_equivalence U F X hU

end AdicCompletionTor


end



end

section


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AdicCompletionTor

/-- **Stacks 0EET.** Over a Noetherian ring, derived completion has Milnor short exact
sequences. For a module these read
`0 ⟶ R¹ lim Tor_(i+1)(M, A/Iⁿ) ⟶ H^(-i)(M^∧) ⟶ lim Tor_i(M, A/Iⁿ) ⟶ 0`.
For a derived object, the Tor systems are replaced by the cohomology systems of its derived
tensors with `A/Iⁿ`. The latter assertion is valid for every derived object, and in particular
for every object of `D⁻(A)`. -/
@[stacks 0EET]
public theorem derivedCompletion_homology_shortExact
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun K ↦ IsDerivedComplete I K
    ∃ L : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory,
      Nonempty (L ⊣ P.ι) ∧
        (∀ K, IsDerivedLimit
          (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K)
          ((L ⋙ P.ι).obj K)) ∧
        (∀ (M : ModuleCat.{u} A) (i : ℕ),
          let M₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
          let Mhat := (L ⋙ P.ι).obj M₀
          let R1limTor := firstDerivedInverseLimit (torIdealPowerSystem I M (i + 1))
          let HminusI := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).obj Mhat
          let limTor := limit (torIdealPowerSystem I M i)
          ∃ (a : R1limTor ⟶ HminusI) (b : HminusI ⟶ limTor) (w : a ≫ b = 0),
            (ShortComplex.mk a b w).ShortExact) ∧
        (∀ (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ),
          let Khat := (L ⋙ P.ι).obj K
          let H := derivedTensorHomologySystem T I K
          let R1limH := firstDerivedInverseLimit (H (p - 1))
          let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj Khat
          let limH := limit (H p)
          ∃ (a : R1limH ⟶ Hp) (b : Hp ⟶ limH) (w : a ≫ b = 0),
            (ShortComplex.mk a b w).ShortExact) := by
  dsimp
  obtain ⟨L, adj, hlim⟩ := completion_reflector A I T
  refine ⟨L, adj, hlim, ?_, ?_⟩
  · intro M i
    exact module_homology_shortExact A I T M i _ (hlim _)
  · intro K p
    exact homology_shortExact_of_isDerivedLimit A _ _ (hlim K) p

end AdicCompletionTor

end



end
