module

public import Mathlib
public import StacksFrontier.Algebra.Homology.FiniteFreeComplex
public import StacksFrontier.Algebra.Module.Projective.Nakayama
public import StacksFrontier.Algebra.Module.Projective.StablyFreeLift
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Perfect.FibreCriterion
public import StacksFrontier.Homology.Perfect.Lifting
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Minimal representatives: splitting off elementary complexes

Two bounded complexes of finite projective modules with isomorphic images in the derived category
are homotopy equivalent, and stay so after extension of scalars to a localization. Over a local
ring a bounded complex of finite free modules is isomorphic to the direct sum of a complex whose
differential entries lie in the maximal ideal and finitely many elementary two-term complexes, and
each elementary complex is the mapping cone of the identity of a rank-one free module concentrated
in one degree (`cochainComplex_exists_iso_biprod_mappingCone_single`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

open scoped TensorProduct ChangeOfRings

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

private theorem homotopyEquivOfDerivedIso
    {R : Type u} [CommRing R]
    (M N : CochainComplex (ModuleCat.{max v u} R) ℤ)
    [M.IsKProjective] [N.IsKProjective]
    (e : (DerivedCategory.Q).obj M ≅ (DerivedCategory.Q).obj N) :
    Nonempty (HomotopyEquiv M N) := by
  let E : (DerivedCategory.Qh).obj ((HomotopyCategory.quotient _ _).obj M) ≅
      (DerivedCategory.Qh).obj ((HomotopyCategory.quotient _ _).obj N) :=
    (DerivedCategory.quotientCompQhIso _).app M ≪≫ e ≪≫
      ((DerivedCategory.quotientCompQhIso _).app N).symm
  obtain ⟨f, hf⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective M
      ((HomotopyCategory.quotient _ _).obj N)).surjective E.hom
  obtain ⟨g, hg⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective N
      ((HomotopyCategory.quotient _ _).obj M)).surjective E.inv
  have hfg : f ≫ g = 𝟙 _ :=
    (CochainComplex.IsKProjective.Qh_map_bijective M
      ((HomotopyCategory.quotient _ _).obj M)).injective (by
      rw [Functor.map_comp, hf, hg, E.hom_inv_id]
      simp)
  have hgf : g ≫ f = 𝟙 _ :=
    (CochainComplex.IsKProjective.Qh_map_bijective N
      ((HomotopyCategory.quotient _ _).obj N)).injective (by
      rw [Functor.map_comp, hg, hf, E.inv_hom_id]
      simp)
  exact ⟨HomotopyCategory.homotopyEquivOfIso
    { hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }⟩

private theorem homotopyEquivOfDerivedIsoOfBoundedProjective
    {R : Type u} [CommRing R]
    (M N : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hNbounded : ∃ a b : ℤ, N.IsStrictlyGE a ∧ N.IsStrictlyLE b)
    (hMterms : ∀ i, Projective (M.X i))
    (hNterms : ∀ i, Projective (N.X i))
    (e : (DerivedCategory.Q).obj M ≅ (DerivedCategory.Q).obj N) :
    Nonempty (HomotopyEquiv M N) := by
  obtain ⟨_, b, _, hb⟩ := hMbounded
  obtain ⟨_, c, _, hc⟩ := hNbounded
  let : M.IsStrictlyLE b := hb
  let : N.IsStrictlyLE c := hc
  let : ∀ i, Projective (M.X i) := hMterms
  let : ∀ i, Projective (N.X i) := hNterms
  let : M.IsKProjective := CochainComplex.isKProjective_of_projective M b
  let : N.IsKProjective := CochainComplex.isKProjective_of_projective N c
  exact homotopyEquivOfDerivedIso M N e

private theorem free_atPrime_of_finite_projective
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : ModuleCat.{max v u} R)
    (hfinite : Module.Finite R P) (hprojective : Projective P) :
    Module.Free (Localization.AtPrime p) (LocalizedModule.AtPrime p P) := by
  let : Module.Finite R P := hfinite
  let : Projective P := hprojective
  let : Module.Projective R P := ModuleCat.projective_of_module_projective P
  exact Module.free_of_flat_of_isLocalRing

private theorem exists_free_away_of_finite_projective
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : ModuleCat.{max v u} R)
    (hfinite : Module.Finite R P) (hprojective : Projective P) :
    ∃ f : R, f ∉ p ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away f P) := by
  let : Module.Finite R P := hfinite
  let : Projective P := hprojective
  let : Module.Projective R P := ModuleCat.projective_of_module_projective P
  let : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  have hfree : Module.Free (Localization.AtPrime p)
      (LocalizedModule.AtPrime p P) :=
    free_atPrime_of_finite_projective p P hfinite hprojective
  obtain ⟨f, hf, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl P)
      (Localization.AtPrime p)
  exact ⟨f, hf, hfree⟩

private theorem homotopyEquiv_away
    {R : Type u} [CommRing R]
    (M N : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (e : HomotopyEquiv M N) (f : R) :
    let S := Localization.Away f
    let F := (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.up ℤ)
    Nonempty (HomotopyEquiv (F.obj M) (F.obj N)) := by
  let := extendScalars_additive (algebraMap R (Localization.Away f))
  exact ⟨(ModuleCat.extendScalars.{u, u, max v u}
    (algebraMap R (Localization.Away f))).mapHomotopyEquiv e⟩

private theorem free_terms_atPrime_of_finite_projective
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (M : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hterms : ∀ i, Module.Finite R (M.X i) ∧ Projective (M.X i)) :
    ∀ i, Module.Free (Localization.AtPrime p)
      (LocalizedModule.AtPrime p (M.X i)) := by
  intro i
  exact free_atPrime_of_finite_projective p (M.X i) (hterms i).1 (hterms i).2

private theorem restrictScalars_preservesEpimorphisms
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.restrictScalars.{max v u, u, u} f).PreservesEpimorphisms :=
  ⟨fun g hg => (ModuleCat.epi_iff_surjective _).mpr
    ((ModuleCat.epi_iff_surjective g).mp hg)⟩

private theorem projective_extendScalars
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : ModuleCat.{max v u} R) (hprojective : Projective P) :
    Projective ((ModuleCat.extendScalars.{u, u, max v u} f).obj P) := by
  let := restrictScalars_preservesEpimorphisms.{u, v} f
  exact (ModuleCat.extendRestrictScalarsAdj f).map_projective P hprojective

private theorem finite_extendScalars
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : ModuleCat.{max v u} R) (hfinite : Module.Finite R P) :
    Module.Finite S ((ModuleCat.extendScalars.{u, u, max v u} f).obj P) := by
  let : Module.Finite R P := hfinite
  let : Algebra R S := f.toAlgebra
  have heq : (inferInstance : Module R S) = Module.compHom S f :=
    Module.ext' _ _ (by intro r s; rfl)
  cases heq
  exact Module.Finite.base_change R S P

private theorem free_extendScalars_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : ModuleCat.{max v u} R)
    (hfinite : Module.Finite R P) (hprojective : Projective P) :
    Module.Free (Localization.AtPrime p)
      ((ModuleCat.extendScalars.{u, u, max v u}
        (algebraMap R (Localization.AtPrime p))).obj P) := by
  let f := algebraMap R (Localization.AtPrime p)
  let : Module.Finite (Localization.AtPrime p)
      ((ModuleCat.extendScalars.{u, u, max v u} f).obj P) :=
    finite_extendScalars f P hfinite
  let : Projective ((ModuleCat.extendScalars.{u, u, max v u} f).obj P) :=
    projective_extendScalars f P hprojective
  let : Module.Projective (Localization.AtPrime p)
      ((ModuleCat.extendScalars.{u, u, max v u} f).obj P) :=
    ModuleCat.projective_of_module_projective _
  exact Module.free_of_flat_of_isLocalRing

private theorem free_terms_atPrime_extendScalars
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (M : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hterms : ∀ i, Module.Finite R (M.X i) ∧ Projective (M.X i)) :
    let F := (ModuleCat.extendScalars.{u, u, max v u}
      (algebraMap R (Localization.AtPrime p))).mapHomologicalComplex (ComplexShape.up ℤ)
    ∀ i, Module.Free (Localization.AtPrime p) ((F.obj M).X i) := by
  dsimp only
  intro i
  exact free_extendScalars_atPrime p (M.X i) (hterms i).1 (hterms i).2

private theorem finite_projective_terms_extendScalars
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hterms : ∀ i, Module.Finite R (M.X i) ∧ Projective (M.X i)) :
    let F := (ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∀ i, Module.Finite S ((F.obj M).X i) ∧ Projective ((F.obj M).X i) := by
  dsimp only
  intro i
  exact ⟨finite_extendScalars f (M.X i) (hterms i).1,
    projective_extendScalars f (M.X i) (hterms i).2⟩

private theorem bounded_extendScalars
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b) :
    let F := (ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∃ a b : ℤ, CochainComplex.IsStrictlyGE (F.obj M) a ∧
      CochainComplex.IsStrictlyLE (F.obj M) b := by
  let := extendScalars_additive.{u, u, max v u} f
  dsimp only
  obtain ⟨a, b, ha, hb⟩ := hbounded
  let : M.IsStrictlyGE a := ha
  let : M.IsStrictlyLE b := hb
  exact ⟨a, b, inferInstance, inferInstance⟩

private theorem homotopyEquiv_atPrime_of_derivedIso
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (M N : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hNbounded : ∃ a b : ℤ, N.IsStrictlyGE a ∧ N.IsStrictlyLE b)
    (hMterms : ∀ i, Module.Finite R (M.X i) ∧ Projective (M.X i))
    (hNterms : ∀ i, Module.Finite R (N.X i) ∧ Projective (N.X i))
    (e : (DerivedCategory.Q).obj M ≅ (DerivedCategory.Q).obj N) :
    let S := Localization.AtPrime p
    let F := (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.up ℤ)
    Nonempty (HomotopyEquiv (F.obj M) (F.obj N)) := by
  let := extendScalars_additive.{u, u, max v u} (algebraMap R (Localization.AtPrime p))
  obtain ⟨h⟩ := homotopyEquivOfDerivedIsoOfBoundedProjective M N hMbounded hNbounded
    (fun i => (hMterms i).2) (fun i => (hNterms i).2) e
  exact ⟨(ModuleCat.extendScalars.{u, u, max v u}
    (algebraMap R (Localization.AtPrime p))).mapHomotopyEquiv h⟩

private theorem exists_iso_biprod_product_fin_zero
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasFiniteProducts C]
    [HasBinaryBiproducts C] (X : C) (F : Fin 0 → C) :
    Nonempty (X ≅ X ⊞ ∏ᶜ F) := by
  refine ⟨⟨biprod.inl, biprod.fst, by simp, ?_⟩⟩
  apply biprod.hom_ext
  · simp
  · exact Pi.hom_ext _ _ fun i => i.elim0

set_option backward.isDefEq.respectTransparency false in
private theorem exists_iso_biprod_product_fin_cons
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasFiniteProducts C]
    [HasBinaryBiproducts C] {n : ℕ} (X : C) (F : Fin n → C) :
    Nonempty (X ⊞ ∏ᶜ F ≅ ∏ᶜ (Fin.cons X F)) := by
  refine ⟨{
    hom := Pi.lift (Fin.cases biprod.fst (fun i => biprod.snd ≫ Pi.π F i))
    inv := biprod.lift (Pi.π (Fin.cons X F) 0)
      (Pi.lift fun i => Pi.π (Fin.cons X F) i.succ)
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩
  · apply biprod.hom_ext
    · simp
    · apply Pi.hom_ext
      intro i
      simp
  · apply Pi.hom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Fin.cases_zero,
        Category.id_comp]
      exact biprod.lift_fst _ _
    · simp

private theorem freeComplex_exists_iso_biprod_elementary_of_finite_support
    {R : Type*} [CommRing R] (C : FreeComplex R)
    (s : Finset ℤ) (hs : ∀ i, i ∉ s → C.n i = 0) :
    ∃ (D : FreeComplex R) (n : ℕ) (degree : Fin n → ℤ),
      (∀ i, D.n i ≤ C.n i) ∧ (∀ i, ¬ FreeComplex.HasInvertibleCoeff D i) ∧
      Nonempty (C.toComplex ≅ D.toComplex ⊞
        ∏ᶜ fun j => (FreeComplex.elementaryComplex R (degree j)).toComplex) := by
  classical
  generalize hn : ∑ i ∈ s, C.n i = m
  induction m using Nat.strong_induction_on generalizing C with
  | h m ih =>
    by_cases hC : ∀ i, ¬ FreeComplex.HasInvertibleCoeff C i
    · exact ⟨C, 0, Fin.elim0, fun _ => le_rfl, hC,
        exists_iso_biprod_product_fin_zero _ _⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hC
      have hi' : FreeComplex.HasInvertibleCoeff C i := not_not.mp hi
      obtain ⟨hni, _, D, hD, ⟨e⟩⟩ := exists_splitOff_elementaryComplex_of_hasInvertibleCoeff C i hi'
      have hle (j : ℤ) : D.n j ≤ C.n j := by
        rw [hD j]
        split_ifs with h₁ h₂
        · subst j; omega
        · subst j; omega
        · exact le_rfl
      have hDs (j : ℤ) (hj : j ∉ s) : D.n j = 0 :=
        Nat.eq_zero_of_le_zero ((hle j).trans_eq (hs j hj))
      have himem : i ∈ s := by
        by_contra his
        have := hs i his
        omega
      have hlt : ∑ j ∈ s, D.n j < m := by
        rw [← hn]
        apply Finset.sum_lt_sum (fun j _ => hle j)
        refine ⟨i, himem, ?_⟩
        rw [hD i, ite_eq_left rfl]
        omega
      obtain ⟨E, n, degree, hE, hmin, ⟨eD⟩⟩ := ih _ hlt D hDs rfl
      let T := fun j => (FreeComplex.elementaryComplex R (degree j)).toComplex
      let U := (FreeComplex.elementaryComplex R i).toComplex
      let degree' : Fin (n + 1) → ℤ := Fin.cons i degree
      obtain ⟨eprod⟩ := exists_iso_biprod_product_fin_cons U T
      have eprod' : U ⊞ ∏ᶜ T ≅
          ∏ᶜ fun j => (FreeComplex.elementaryComplex R (degree' j)).toComplex := by
        convert eprod using 1
        congr 1
        funext j
        refine Fin.cases ?_ (fun k => ?_) j <;> rfl
      refine ⟨E, n + 1, degree', fun j => (hE j).trans (hle j), hmin, ⟨?_⟩⟩
      exact e ≪≫ biprod.mapIso eD (Iso.refl U) ≪≫
        biprod.associator E.toComplex (∏ᶜ T) U ≪≫
        biprod.mapIso (Iso.refl E.toComplex) (biprod.braiding (∏ᶜ T) U ≪≫ eprod')

private lemma isIso_of_isIso_reduction
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : ∀ x ∈ I, IsUnit (1 + x))
    {M N : ModuleCat.{max v u} R}
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M ⟶ N) [IsIso ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f)] :
    IsIso f := by
  rw [ConcreteCategory.isIso_iff_bijective]
  apply lift_iso_of_quot_iso I hI f.hom
  let eM := TensorProduct.quotTensorEquivQuotSMul M I
  let eN := TensorProduct.quotTensorEquivQuotSMul N I
  have h : inducedQuot I f.hom =
      eN.toLinearMap ∘ₗ
        ((f.hom.baseChange (R ⧸ I)).restrictScalars R) ∘ₗ
          eM.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [eM, eN, inducedQuot]
  rw [h]
  have ht : Function.Bijective (f.hom.baseChange (R ⧸ I)) :=
    (ConcreteCategory.isIso_iff_bijective
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f)).mp inferInstance
  exact eN.bijective.comp (ht.comp eM.symm.bijective)

private theorem isIso_homotopyEquiv_hom_of_zero_differentials
    {ι : Type*} {C : Type*} [Category C] [Preadditive C]
    {c : ComplexShape ι} {M N : HomologicalComplex C c}
    (e : HomotopyEquiv M N)
    (hM : ∀ i j, M.d i j = 0) (hN : ∀ i j, N.d i j = 0) :
    IsIso e.hom := by
  have hMN : e.hom ≫ e.inv = 𝟙 M := by
    ext i
    simpa [dNext, prevD, hM] using e.homotopyHomInvId.comm i
  have hNM : e.inv ≫ e.hom = 𝟙 N := by
    ext i
    simpa [dNext, prevD, hN] using e.homotopyInvHomId.comm i
  exact ⟨e.inv, hMN, hNM⟩

private theorem isIso_homotopyEquiv_hom_of_zero_differentials_reduction
    {ι : Type*} {R : Type u} [CommRing R] {c : ComplexShape ι}
    (I : Ideal R) (hI : ∀ x ∈ I, IsUnit (1 + x))
    {M N : HomologicalComplex (ModuleCat.{max v u} R) c}
    (hM : ∀ i, Module.Finite R (M.X i) ∧ Projective (M.X i))
    (hN : ∀ i, Module.Finite R (N.X i) ∧ Projective (N.X i))
    (e : HomotopyEquiv M N)
    (hdM : ∀ i j, (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map (M.d i j) = 0)
    (hdN : ∀ i j, (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map (N.d i j) = 0) :
    IsIso e.hom := by
  let F := ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)
  let := extendScalars_additive.{u, u, max v u} (Ideal.Quotient.mk I)
  have hred : IsIso (F.mapHomotopyEquiv e).hom :=
    isIso_homotopyEquiv_hom_of_zero_differentials (F.mapHomotopyEquiv e) hdM hdN
  have hi (i : ι) : IsIso (e.hom.f i) := by
    let := (hM i).1
    let := (hM i).2
    let := (hN i).1
    let := (hN i).2
    let : Module.Projective R (M.X i) := ModuleCat.projective_of_module_projective _
    let : Module.Projective R (N.X i) := ModuleCat.projective_of_module_projective _
    have : IsIso (F.map (e.hom.f i)) :=
      (HomologicalComplex.eval _ _ i).map_isIso (F.mapHomotopyEquiv e).hom
    exact isIso_of_isIso_reduction I hI (e.hom.f i)
  exact HomologicalComplex.Hom.isIso_of_components e.hom

private theorem freeComplex_exists_iso_biprod_elementary_of_finite_support_isLocalRing
    {R : Type*} [CommRing R] [IsLocalRing R] (C : FreeComplex R)
    (s : Finset ℤ) (hs : ∀ i, i ∉ s → C.n i = 0) :
    ∃ (D : FreeComplex R) (n : ℕ) (degree : Fin n → ℤ),
      (∀ i, D.n i ≤ C.n i) ∧
      (∀ (i : ℤ) (a : Fin (D.n i)) (b : Fin (D.n (i + 1))),
        D.d i a b ∈ IsLocalRing.maximalIdeal R) ∧
      Nonempty (C.toComplex ≅ D.toComplex ⊞
        ∏ᶜ fun j => (FreeComplex.elementaryComplex R (degree j)).toComplex) := by
  obtain ⟨D, n, degree, hle, hmin, e⟩ :=
    freeComplex_exists_iso_biprod_elementary_of_finite_support C s hs
  refine ⟨D, n, degree, hle, ?_, e⟩
  intro i a b
  rw [IsLocalRing.mem_maximalIdeal]
  intro hunit
  apply hmin (i + 1)
  unfold FreeComplex.HasInvertibleCoeff
  rw [show i + 1 - 1 = i by omega]
  exact ⟨a, b, hunit⟩

private theorem exists_iso_biprod_of_iso_biprod
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {M N K L P Q : C} (eM : M ≅ K ⊞ P) (eN : N ≅ L ⊞ Q) (e : K ≅ L) :
    Nonempty (M ⊞ Q ≅ N ⊞ P) :=
  ⟨biprod.mapIso eM (Iso.refl Q) ≪≫ biprod.associator K P Q ≪≫
    biprod.mapIso e (biprod.braiding P Q) ≪≫ (biprod.associator L Q P).symm ≪≫
    biprod.mapIso eN.symm (Iso.refl P)⟩

private theorem chainComplex_exists_freeComplex
    {R : Type u} [CommRing R] [Nontrivial R]
    (M : ChainComplex (ModuleCat.{max v u} R) ℤ)
    (hfin : ∀ i, Module.Finite R (M.X i))
    (hfree : ∀ i, Module.Free R (M.X i)) :
    ∃ C : FreeComplex R, (∀ i, C.n i = Module.finrank R (M.X i)) ∧
      Nonempty (((ModuleCat.uliftFunctor.{v} R).mapHomologicalComplex
        (ComplexShape.down ℤ)).obj C.toComplex ≅ M) := by
  classical
  let := hfin
  let := hfree
  let b i := Module.finBasis R (M.X i)
  let C : FreeComplex R := {
    n i := Module.finrank R (M.X i)
    d i := LinearMap.toMatrix (b (i + 1)) (b i) (M.d (i + 1) i).hom
    dd i := by
      rw [← LinearMap.toMatrix_comp]
      have h : (M.d (i + 1) i).hom.comp (M.d (i + 1 + 1) (i + 1)).hom = 0 :=
        congrArg ModuleCat.Hom.hom (M.d_comp_d (i + 1 + 1) (i + 1) i)
      rw [h, map_zero] }
  refine ⟨C, fun _ => rfl, ⟨HomologicalComplex.Hom.isoOfComponents
    (fun i => (ULift.moduleEquiv.trans (b i).equivFun.symm).toModuleIso) ?_⟩⟩
  intro i j hij
  have hi : i = j + 1 := by simpa [ComplexShape.down, eq_comm] using hij
  subst i
  apply ModuleCat.hom_ext
  ext x
  show (M.d (j + 1) j).hom ((b (j + 1)).equivFun.symm x.down) =
    (b j).equivFun.symm ((C.toComplex.d (j + 1) j).hom x.down)
  rw [FreeComplex.toComplex_d_succ]
  apply (b j).equivFun.injective
  simp only [LinearEquiv.apply_symm_apply]
  show (b j).equivFun ((M.d (j + 1) j).hom ((b (j + 1)).equivFun.symm x.down)) =
    (C.d j).mulVec x.down
  have h := LinearMap.toMatrix_mulVec_repr (b (j + 1)) (b j)
    (M.d (j + 1) j).hom ((b (j + 1)).equivFun.symm x.down)
  change (C.d j).mulVec ((b (j + 1)).equivFun
    ((b (j + 1)).equivFun.symm x.down)) =
      (b j).equivFun ((M.d (j + 1) j).hom ((b (j + 1)).equivFun.symm x.down)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- An additive functor preserving finite biproducts carries a biproduct-with-product splitting
to the corresponding splitting of the images. -/
private theorem exists_iso_biprod_product_map
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteBiproducts F]
    {X A : C} {n : ℕ} {T : Fin n → C} [HasProduct T] [HasProduct fun j => F.obj (T j)]
    (e : X ≅ A ⊞ ∏ᶜ T) :
    Nonempty (F.obj X ≅ F.obj A ⊞ ∏ᶜ fun j => F.obj (T j)) := by
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  exact ⟨F.mapIso e ≪≫ F.mapBiprod _ _ ≪≫
    biprod.mapIso (Iso.refl _) (asIso (piComparison F _))⟩

private theorem chainComplex_exists_iso_biprod_elementary
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ChainComplex (ModuleCat.{max v u} R) ℤ)
    (hfin : ∀ i, Module.Finite R (M.X i))
    (hfree : ∀ i, Module.Free R (M.X i))
    (s : Finset ℤ) (hs : ∀ i, i ∉ s → IsZero (M.X i)) :
    let U := (ModuleCat.uliftFunctor.{v} R).mapHomologicalComplex (ComplexShape.down ℤ)
    ∃ (D : FreeComplex R) (n : ℕ) (degree : Fin n → ℤ),
      (∀ i, D.n i ≤ Module.finrank R (M.X i)) ∧
      (∀ (i : ℤ) (a : Fin (D.n i)) (b : Fin (D.n (i + 1))),
        D.d i a b ∈ IsLocalRing.maximalIdeal R) ∧
      Nonempty (M ≅ U.obj D.toComplex ⊞
        ∏ᶜ fun j => U.obj (FreeComplex.elementaryComplex R (degree j)).toComplex) := by
  classical
  let U := (ModuleCat.uliftFunctor.{v} R).mapHomologicalComplex (ComplexShape.down ℤ)
  let : U.Additive := inferInstance
  let : PreservesFiniteBiproducts U := inferInstance
  obtain ⟨C, hC, ⟨eC⟩⟩ := chainComplex_exists_freeComplex M hfin hfree
  have hCs (i : ℤ) (hi : i ∉ s) : C.n i = 0 := by
    rw [hC i]
    let := hfree i
    let := ModuleCat.subsingleton_of_isZero (hs i hi)
    exact Module.finrank_eq_zero_of_subsingleton R (M.X i)
  obtain ⟨D, n, degree, hle, hmin, ⟨eD⟩⟩ :=
    freeComplex_exists_iso_biprod_elementary_of_finite_support_isLocalRing C s hCs
  obtain ⟨e⟩ := exists_iso_biprod_product_map U eD
  exact ⟨D, n, degree, fun i => (hle i).trans_eq (hC i), hmin, ⟨eC.symm ≪≫ e⟩⟩

private abbrev liftChainComplexFunctor (R : Type u) [CommRing R] :=
  ((ModuleCat.uliftFunctor.{v} R).mapHomologicalComplex (ComplexShape.down ℤ)) ⋙
    (ChainComplex.cochainComplexEquivalence (ModuleCat.{max v u} R)).functor

private theorem cochainComplex_exists_iso_biprod_elementary
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hfin : ∀ i, Module.Finite R (M.X i))
    (hfree : ∀ i, Module.Free R (M.X i))
    (hbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b) :
    let U := liftChainComplexFunctor.{u, v} R
    ∃ (D : FreeComplex R) (n : ℕ) (degree : Fin n → ℤ),
      (∀ i, D.n i ≤ Module.finrank R (M.X (-i))) ∧
      (∀ (i : ℤ) (a : Fin (D.n i)) (b : Fin (D.n (i + 1))),
        D.d i a b ∈ IsLocalRing.maximalIdeal R) ∧
      Nonempty (M ≅ U.obj D.toComplex ⊞
        ∏ᶜ fun j => U.obj (FreeComplex.elementaryComplex R (degree j)).toComplex) := by
  classical
  let E := ChainComplex.cochainComplexEquivalence (ModuleCat.{max v u} R)
  obtain ⟨a, b, ha, hb⟩ := hbounded
  let := ha
  let := hb
  have hs (i : ℤ) (hi : i ∉ Finset.Icc (-b) (-a)) : IsZero ((E.inverse.obj M).X i) := by
    show IsZero (M.X (-i))
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact M.isZero_of_isStrictlyLE b (-i) (by omega)
    · exact M.isZero_of_isStrictlyGE a (-i) (by omega)
  obtain ⟨D, n, degree, hle, hmin, ⟨e⟩⟩ :=
    chainComplex_exists_iso_biprod_elementary (E.inverse.obj M)
      (fun i => hfin (-i)) (fun i => hfree (-i)) (Finset.Icc (-b) (-a)) hs
  let : E.functor.Additive := by
    show (ComplexShape.embeddingUpIntDownInt.restrictionFunctor _).Additive
    infer_instance
  let : PreservesFiniteBiproducts E.functor := inferInstance
  obtain ⟨e'⟩ := exists_iso_biprod_product_map E.functor e
  exact ⟨D, n, degree, hle, hmin, ⟨(E.counitIso.app M).symm ≪≫ e'⟩⟩

private theorem cochainComplex_iso_of_two_term
    {C : Type*} [Category C] [HasZeroMorphisms C]
    (M N : CochainComplex C ℤ) (a b : ℤ) (hab : a + 1 = b)
    (hM : ∀ i, i ≠ a → i ≠ b → IsZero (M.X i))
    (hN : ∀ i, i ≠ a → i ≠ b → IsZero (N.X i))
    [IsIso (M.d a b)] [IsIso (N.d a b)] (e : M.X a ≅ N.X a) :
    Nonempty (M ≅ N) := by
  classical
  let E (i : ℤ) : M.X i ≅ N.X i :=
    if hia : i = a then (M.XIsoOfEq hia) ≪≫ e ≪≫ (N.XIsoOfEq hia).symm
    else if hib : i = b then (M.XIsoOfEq hib) ≪≫ (asIso (M.d a b)).symm ≪≫ e ≪≫
      asIso (N.d a b) ≪≫ (N.XIsoOfEq hib).symm
    else (hM i hia hib).iso (hN i hia hib)
  refine ⟨HomologicalComplex.Hom.isoOfComponents E ?_⟩
  intro i j hij
  have hij' : i + 1 = j := hij
  by_cases hia : i = a
  · subst i
    have hjb : j = b := by omega
    clear hij hij'
    subst j
    simp [E, show b ≠ a by omega, HomologicalComplex.XIsoOfEq]
  · by_cases hib : i = b
    · apply (hN j (by omega) (by omega)).eq_of_tgt
    · apply (hM i hia hib).eq_of_src

private theorem cochainComplex_isIso_d_of_contractible_two_term
    {C : Type*} [Category C] [Preadditive C]
    (M : CochainComplex C ℤ) (a b : ℤ) (hab : a + 1 = b)
    (hM : ∀ i, i ≠ a → i ≠ b → IsZero (M.X i))
    (h : Homotopy (𝟙 M) 0) : IsIso (M.d a b) := by
  have hleft : M.d a b ≫ h.hom b a = 𝟙 _ := by
    have hd : M.d (a - 1) a = 0 :=
      (hM (a - 1) (by omega) (by omega)).eq_of_src _ _
    have hh := h.comm a
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel a b from hab),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (a - 1) a by change a - 1 + 1 = a; omega)] at hh
    simpa [hd] using hh.symm
  have hright : h.hom b a ≫ M.d a b = 𝟙 _ := by
    have hd : M.d b (b + 1) = 0 :=
      (hM (b + 1) (by omega) (by omega)).eq_of_tgt _ _
    have hh := h.comm b
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel a b from hab)] at hh
    simpa [hd] using hh.symm
  exact ⟨h.hom b a, hleft, hright⟩

private theorem elementaryComplex_isIso_d
    (R : Type u) [CommRing R] (i t : ℤ) (hi : i = t + 1) :
    IsIso ((FreeComplex.elementaryComplex R i).toComplex.d i t) := by
  subst i
  rw [ConcreteCategory.isIso_iff_bijective]
  show Function.Bijective
    ((FreeComplex.elementaryComplex R (t + 1)).toComplex.d (t + 1) t).hom
  have hd : ((FreeComplex.elementaryComplex R (t + 1)).toComplex.d (t + 1) t).hom =
      Matrix.toLin' ((FreeComplex.elementaryComplex R (t + 1)).d t) := by
    ext x
    exact FreeComplex.toComplex_d_succ _ _ x
  rw [hd]
  have hr₀ : FreeComplex.elemRank (t + 1) t = 1 := by simp [FreeComplex.elemRank]
  have hr₁ : FreeComplex.elemRank (t + 1) (t + 1) = 1 := by simp [FreeComplex.elemRank]
  show Function.Bijective (Matrix.toLin'
    (if t = t + 1 - 1 then
      (Matrix.of fun (_ : Fin (FreeComplex.elemRank (t + 1) t))
        (_ : Fin (FreeComplex.elemRank (t + 1) (t + 1))) => (1 : R)) else 0))
  rw [ite_eq_left (by omega), hr₀, hr₁]
  have hmat : (Matrix.of fun (_ _ : Fin 1) => (1 : R)) = 1 := by
    ext i j; fin_cases i; fin_cases j; rfl
  rw [hmat, Matrix.toLin'_one]
  exact Function.bijective_id

private theorem elementaryCochain_isZero_X
    (R : Type u) [CommRing R] (i k : ℤ) (h₀ : k ≠ -i) (h₁ : k ≠ 1 - i) :
    IsZero (((liftChainComplexFunctor.{u, v} R).obj
      (FreeComplex.elementaryComplex R i).toComplex).X k) := by
  have hr : FreeComplex.elemRank i (-k) = 0 := by
    simp only [FreeComplex.elemRank]
    rw [ite_eq_right (by omega)]
  show IsZero (ModuleCat.of R (ULift.{v} (Fin (FreeComplex.elemRank i (-k)) → R)))
  rw [hr]
  exact ModuleCat.isZero_of_subsingleton _

private theorem elementaryCochain_isIso_d
    (R : Type u) [CommRing R] (i : ℤ) :
    IsIso (((liftChainComplexFunctor.{u, v} R).obj
      (FreeComplex.elementaryComplex R i).toComplex).d (-i) (1 - i)) := by
  show IsIso ((ModuleCat.uliftFunctor.{v} R).map
    ((FreeComplex.elementaryComplex R i).toComplex.d (- -i) (-(1 - i))))
  have hh : ∀ a b, a = i → b = i - 1 →
      IsIso ((FreeComplex.elementaryComplex R i).toComplex.d a b) := by
    intro a b ha hb
    subst a b
    exact elementaryComplex_isIso_d R i (i - 1) (by omega)
  let := hh (- -i) (-(1 - i)) (by omega) (by omega)
  exact (ModuleCat.uliftFunctor.{v} R).map_isIso _

private theorem mappingCone_single_isZero_X
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    (X : C) (a b : ℤ) (hab : a + 1 = b) (k : ℤ) (h₀ : k ≠ a) (h₁ : k ≠ b) :
    IsZero ((CochainComplex.mappingCone
      (𝟙 ((CochainComplex.singleFunctor C b).obj X))).X k) := by
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
    HomologicalComplex.isZero_single_obj_X _ _ _ _ h₁⟩

private theorem elementaryCochain_iso_mappingCone_single
    (R : Type u) [CommRing R] (i : ℤ) :
    Nonempty ((liftChainComplexFunctor.{u, v} R).obj
      (FreeComplex.elementaryComplex R i).toComplex ≅
        CochainComplex.mappingCone (𝟙 ((CochainComplex.singleFunctor
          (ModuleCat.{max v u} R) (1 - i)).obj (ModuleCat.of R (ULift.{v} R))))) := by
  let M := (liftChainComplexFunctor.{u, v} R).obj
    (FreeComplex.elementaryComplex R i).toComplex
  let S := (CochainComplex.singleFunctor (ModuleCat.{max v u} R) (1 - i)).obj
    (ModuleCat.of R (ULift.{v} R))
  let N := CochainComplex.mappingCone (𝟙 S)
  have hM := elementaryCochain_isZero_X.{u, v} R i
  have hN := mappingCone_single_isZero_X (ModuleCat.of R (ULift.{v} R))
    (-i) (1 - i) (by omega)
  let : IsIso (M.d (-i) (1 - i)) := elementaryCochain_isIso_d R i
  let : IsIso (N.d (-i) (1 - i)) :=
    cochainComplex_isIso_d_of_contractible_two_term N (-i) (1 - i) (by omega)
      hN (CochainComplex.mappingCone.homotopyToZeroOfId S)
  have eM : Nonempty (M.X (-i) ≅ ModuleCat.of R (ULift.{v} R)) := by
    show Nonempty (ModuleCat.of R (ULift.{v} (Fin (FreeComplex.elemRank i (- -i)) → R)) ≅ _)
    have hr : FreeComplex.elemRank i (- -i) = 1 := by simp [FreeComplex.elemRank]
    rw [hr]
    exact ⟨(ULift.moduleEquiv.trans ((LinearEquiv.funUnique (Fin 1) R R).trans
      ULift.moduleEquiv.symm)).toModuleIso⟩
  have hzero : IsZero (S.X (-i)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have : IsIso (biprod.inl : S.X (1 - i) ⟶ S.X (1 - i) ⊞ S.X (-i)) :=
    (CategoryTheory.Biprod.isIso_inl_iff_isZero _ _).mpr hzero
  let eN : N.X (-i) ≅ ModuleCat.of R (ULift.{v} R) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 S) (-i) (1 - i)
      (by change -i + 1 = 1 - i; omega) ≪≫
      (asIso (biprod.inl : S.X (1 - i) ⟶ _)).symm ≪≫
        HomologicalComplex.singleObjXSelf _ _ _
  exact cochainComplex_iso_of_two_term M N (-i) (1 - i) (by omega) hM hN
    (eM.some ≪≫ eN.symm)

private theorem homotopy_id_zero_of_iso
    {ι : Type*} {C : Type*} [Category C] [Preadditive C] {c : ComplexShape ι}
    {M N : HomologicalComplex C c} (e : M ≅ N) (h : Homotopy (𝟙 N) 0) :
    Nonempty (Homotopy (𝟙 M) 0) :=
  ⟨by simpa using (h.compLeft e.hom).compRight e.inv⟩

private theorem homotopy_id_zero_biprod
    {ι : Type*} {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {c : ComplexShape ι} {M N : HomologicalComplex C c}
    (hM : Homotopy (𝟙 M) 0) (hN : Homotopy (𝟙 N) 0) :
    Nonempty (Homotopy (𝟙 (M ⊞ N)) 0) := by
  have h₀ := (hM.compLeft (biprod.fst : M ⊞ N ⟶ M)).compRight (biprod.inl : M ⟶ M ⊞ N)
  have h₁ := (hN.compLeft (biprod.snd : M ⊞ N ⟶ N)).compRight (biprod.inr : N ⟶ M ⊞ N)
  exact ⟨by simpa using h₀.add h₁⟩

private theorem homotopy_id_zero_product
    {ι : Type*} {C : Type*} [Category C] [Preadditive C]
    [HasFiniteProducts C] [HasBinaryBiproducts C] {c : ComplexShape ι}
    (n : ℕ) (P : Fin n → HomologicalComplex C c)
    (hP : ∀ j, Nonempty (Homotopy (𝟙 (P j)) 0)) :
    Nonempty (Homotopy (𝟙 (∏ᶜ P)) 0) := by
  let : HasFiniteProducts (HomologicalComplex C c) := ⟨fun _ => inferInstance⟩
  let : HasBinaryBiproducts (HomologicalComplex C c) := ⟨fun _ _ => inferInstance⟩
  induction n with
  | zero =>
    exact ⟨Homotopy.ofEq (by apply Pi.hom_ext; intro j; exact j.elim0)⟩
  | succ n ih =>
    obtain ⟨htail⟩ := ih (fun j => P j.succ) (fun j => hP j.succ)
    obtain ⟨h⟩ := homotopy_id_zero_biprod (hP 0).some htail
    obtain ⟨e⟩ := exists_iso_biprod_product_fin_cons (P 0) (fun j => P j.succ)
    have hc : Fin.cons (P 0) (fun j => P j.succ) = P := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    rw [hc] at e
    exact homotopy_id_zero_of_iso e.symm h

private theorem homotopyEquiv_biprod_of_contractible
    {ι : Type*} {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {c : ComplexShape ι} (M N : HomologicalComplex C c)
    (hN : Homotopy (𝟙 N) 0) : Nonempty (HomotopyEquiv (M ⊞ N) M) := by
  refine ⟨{
    hom := biprod.fst
    inv := biprod.inl
    homotopyHomInvId := ?_
    homotopyInvHomId := Homotopy.ofEq (by simp) }⟩
  have h := (hN.compLeft (biprod.snd : M ⊞ N ⟶ N)).compRight (biprod.inr : N ⟶ M ⊞ N)
  have h' := (Homotopy.refl (biprod.fst ≫ biprod.inl)).add h
  simpa using h'.symm

private theorem cochainComplex_exists_iso_biprod_mappingCone_single
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hfin : ∀ i, Module.Finite R (M.X i))
    (hfree : ∀ i, Module.Free R (M.X i))
    (hbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b) :
    let U := liftChainComplexFunctor.{u, v} R
    ∃ (D : FreeComplex R) (n : ℕ) (degree : Fin n → ℤ),
      (∀ i, D.n i ≤ Module.finrank R (M.X (-i))) ∧
      (∀ (i : ℤ) (a : Fin (D.n i)) (b : Fin (D.n (i + 1))),
        D.d i a b ∈ IsLocalRing.maximalIdeal R) ∧
      Nonempty (M ≅ U.obj D.toComplex ⊞
        ∏ᶜ fun j => CochainComplex.mappingCone (𝟙 ((CochainComplex.singleFunctor
          (ModuleCat.{max v u} R) (degree j)).obj (ModuleCat.of R (ULift.{v} R))))) := by
  classical
  obtain ⟨D, n, degree, hle, hmin, ⟨e⟩⟩ :=
    cochainComplex_exists_iso_biprod_elementary.{u, v} M hfin hfree hbounded
  refine ⟨D, n, fun j => 1 - degree j, hle, hmin, ⟨?_⟩⟩
  let et (j : Fin n) :
      (liftChainComplexFunctor.{u, v} R).obj
        (FreeComplex.elementaryComplex R (degree j)).toComplex ≅
      CochainComplex.mappingCone (𝟙 ((CochainComplex.singleFunctor
        (ModuleCat.{max v u} R) (1 - degree j)).obj (ModuleCat.of R (ULift.{v} R)))) :=
    (elementaryCochain_iso_mappingCone_single.{u, v} R (degree j)).some
  refine e ≪≫ ?_
  refine biprod.mapIso (Iso.refl _) ?_
  refine {
    hom := Pi.lift (fun j => Pi.π _ j ≫ (et j).hom)
    inv := Pi.lift (fun j => Pi.π _ j ≫ (et j).inv)
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply Pi.hom_ext
    intro j
    simp
  · apply Pi.hom_ext
    intro j
    simp

end StacksDraft.Perfect
