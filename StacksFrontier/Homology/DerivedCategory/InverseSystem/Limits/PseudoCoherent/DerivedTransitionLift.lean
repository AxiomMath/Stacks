module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent.FiniteFreeLift

/-!
# Pseudo-coherence of a derived inverse limit: lifting derived transition maps

Pseudo-coherence along derived base-change comparisons, the Milnor triangle of a degreewise
surjective tower of cochain complexes, and bounded-above finite free and projective lifts across a
surjection with nilpotent kernel retaining a prescribed derived transition map.

## Main results

* `StacksDraft.DerivedInverseLimit.exists_projective_lift_of_derived_transition`: a bounded-above
  projective lift across a surjection with nilpotent kernel retaining a prescribed derived
  transition map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open scoped TensorProduct

namespace StacksDraft.DerivedInverseLimit

universe u v w w'

attribute [local instance] HasDerivedCategory.standard

private lemma isPseudoCoherent_of_derivedBaseChangeComparison
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {K : DerivedCategory (ModuleCat.{max u v} R)}
    {L : DerivedCategory (ModuleCat.{max u v} S)}
    (g : K ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj L)
    [IsIso (derivedBaseChangeComparison f g)] (hK : PseudoCoherence.IsPseudoCoherent K) :
    PseudoCoherence.IsPseudoCoherent L := by
  refine PseudoCoherence.IsPseudoCoherent.ofIso ?_
    (asIso (derivedBaseChangeComparison f g))
  exact (StacksDraft.PseudoCoherence.totalDerivedExtensionScalars_preserves_pseudoCoherent
    f K).2 hK

private lemma isPseudoCoherent_iff_of_derivedBaseChangeComparison
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hI : IsNilpotent (RingHom.ker f))
    {K : DerivedCategory (ModuleCat.{max u v} R)}
    {L : DerivedCategory (ModuleCat.{max u v} S)}
    (g : K ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj L)
    [IsIso (derivedBaseChangeComparison f g)] :
    PseudoCoherence.IsPseudoCoherent K ↔ PseudoCoherence.IsPseudoCoherent L := by
  constructor
  · exact isPseudoCoherent_of_derivedBaseChangeComparison f g
  · exact fun hL ↦ (StacksDraft.Perfect.isPseudoCoherent_derivedExtensionScalars_iff f hf hI K).mp
      (hL.ofIso (asIso (derivedBaseChangeComparison f g)).symm)

lemma isPseudoCoherent_all_of_eventually_nilpotent
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (f : ∀ n, R (n + 1) →+* R n)
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (R n)))
    (g : ∀ n, K (n + 1) ⟶ (ModuleCat.restrictScalars (f n)).mapDerivedCategory.obj (K n))
    (hf : ∀ n, Function.Surjective (f n))
    (hg : ∀ n, IsIso (derivedBaseChangeComparison (f n) (g n)))
    (n₀ : ℕ) (hK : PseudoCoherence.IsPseudoCoherent (K n₀))
    (hI : ∀ n, n₀ ≤ n → IsNilpotent (RingHom.ker (f n))) :
    ∀ n, PseudoCoherence.IsPseudoCoherent (K n) := by
  have hdown : ∀ n, PseudoCoherence.IsPseudoCoherent (K (n + 1)) → PseudoCoherence.IsPseudoCoherent
    (K n) := by
    intro n h
    have := hg n
    exact isPseudoCoherent_of_derivedBaseChangeComparison (f n) (g n) h
  have hbelow : ∀ m n, m ≤ n → PseudoCoherence.IsPseudoCoherent (K n) →
    PseudoCoherence.IsPseudoCoherent (K m) := by
    intro m n hmn
    induction hmn with
    | refl => exact id
    | @step n hmn ih => exact fun h ↦ ih (hdown n h)
  intro n
  rcases le_total n n₀ with hn | hn
  · exact hbelow n n₀ hn hK
  · induction n, hn using Nat.le_induction with
    | base => exact hK
    | succ n hn ih =>
      have := hg n
      exact (isPseudoCoherent_iff_of_derivedBaseChangeComparison
        (f n) (hf n) (hI n hn) (g n)).mpr ih

lemma isKProjective_of_boundedAboveFiniteFree
    {R : Type u} [Ring R] (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : PseudoCoherence.IsBoundedAboveFiniteFree P) : P.IsKProjective := by
  obtain ⟨b, hb⟩ := hP.upperBound
  have hp (i : ℤ) : Projective (P.X i) := by
    have := (hP.finiteFree i).2
    infer_instance
  exact CochainComplex.isKProjective_of_projective P b

set_option backward.isDefEq.respectTransparency false in
/-- Lifting a quasi-isomorphism reduction along `R → R ⧸ I`, given a lift of the isomorphism
`e` through terms satisfying a predicate that forces projectivity. -/
private lemma exists_lift_of_reduction_quasiIso_of_lift
    {R : Type u} [CommRing R] (I : Ideal R)
    (T : CochainComplex (ModuleCat.{max u v} R) ℤ) (c : ℤ) [T.IsStrictlyLE c]
    (p : CochainComplex (ModuleCat.{max u v} R) ℤ → Prop)
    (hp : ∀ P, p P → ∀ i, Projective (P.X i)) (hT : p T)
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) [E.IsStrictlyLE b]
    (a : ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).mapHomologicalComplex (.up
      ℤ)).obj T ⟶ E)
    [QuasiIso a]
    (hlift : ∀ e : DerivedCategory.Q.obj E ≅
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          (Ideal.Quotient.mk I)).functor.obj (DerivedCategory.Q.obj T),
      ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ, P.IsStrictlyLE b ∧ p P ∧
        ∃ eRed : ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk
          I)).mapHomologicalComplex (.up ℤ)).obj P ≅ E,
        ∃ eT : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj T,
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
            (Ideal.Quotient.mk I)).comparison.app P ≫ DerivedCategory.Q.map eRed.hom ≫ e.hom =
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
            (Ideal.Quotient.mk I)).functor.map eT.hom) :
    letI : (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v} (Ideal.Quotient.mk I)).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).Additive :=
      CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
        (by change PreservesFiniteColimits _; infer_instance)
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.IsStrictlyLE b ∧ p P ∧
      ∃ eRed : ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk
        I)).mapHomologicalComplex (.up ℤ)).obj P ≅ E,
      ∃ eT : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj T,
        DerivedCategory.Q.map
          ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v}
            (Ideal.Quotient.mk I))
            (.up ℤ)).homEquiv _ _ eRed.hom) =
          eT.hom ≫ DerivedCategory.Q.map
            ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v}
              (Ideal.Quotient.mk I))
              (.up ℤ)).homEquiv _ _ a) := by
  let F := ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)
  let G := ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I)
  let adj := ModuleCat.extendRestrictScalarsAdj.{max u v} (Ideal.Quotient.mk I)
  let : F.IsLeftAdjoint := adj.isLeftAdjoint
  let : F.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits _; infer_instance)
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
    (Ideal.Quotient.mk I)
  have hcomp (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (c : ℤ) [P.IsStrictlyLE c]
      (hP : p P) : IsIso (D.comparison.app P) := by
    have := hp P hP
    exact D.comparison_isIso_of_projective P c
  have := hcomp T c hT
  let e : DerivedCategory.Q.obj E ≅ D.functor.obj (DerivedCategory.Q.obj T) :=
    (asIso (DerivedCategory.Q.map a)).symm ≪≫ (asIso (D.comparison.app T)).symm
  obtain ⟨P, hbP, hPp, eRed, eT, he⟩ := hlift e
  have := hp P hPp
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  have : IsIso (D.comparison.app P) := hcomp P b hPp
  have hFP : CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    have hp' (i : ℤ) : Projective (((F.mapHomologicalComplex (.up ℤ)).obj P).X i) :=
      adj.map_projective _ (hp P hPp i)
    exact CochainComplex.isKProjective_of_projective _ b
  obtain ⟨β, hβ⟩ := exists_chainMap_of_isKProjective P T eT.hom
  have hred : DerivedCategory.Q.map eRed.hom =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map β ≫ a) := by
    apply (cancel_epi (D.comparison.app P)).mp
    change D.comparison.app P ≫ DerivedCategory.Q.map eRed.hom ≫ e.hom =
      D.functor.map eT.hom at he
    have he' := congrArg (fun k ↦ k ≫ e.inv) he
    rw [Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id] at he'
    change D.comparison.app P ≫ DerivedCategory.Q.map eRed.hom =
      D.functor.map eT.hom ≫ (D.comparison.app T ≫ DerivedCategory.Q.map a) at he'
    rw [← hβ, ← Category.assoc] at he'
    have hn := D.comparison.naturality β
    change D.functor.map (DerivedCategory.Q.map β) ≫ D.comparison.app T =
      D.comparison.app P ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map β) at hn
    rw [hn, Category.assoc, ← Functor.map_comp] at he'
    exact he'
  refine ⟨P, hbP, hPp, eRed, eT, ?_⟩
  have h := congrArg (derivedAdjunctionHomEquiv adj P E) hred
  rw [derivedAdjunctionHomEquiv_map, derivedAdjunctionHomEquiv_map] at h
  have h' := (cancel_mono (G.mapDerivedCategoryFactors.inv.app E)).mp h
  rw [Adjunction.homEquiv_naturality_left, Functor.map_comp, hβ] at h'
  exact h'

private lemma exists_finiteFree_lift_of_reduction_quasiIso
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.IsLocallyNilpotent)
    (T : CochainComplex (ModuleCat.{max u v} R) ℤ) (hT : PseudoCoherence.IsBoundedAboveFiniteFree T)
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) [E.IsStrictlyLE b]
    (hE : ∀ i, Module.Finite (R ⧸ I) (E.X i) ∧ Module.Free (R ⧸ I) (E.X i))
    (a : ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).mapHomologicalComplex (.up
      ℤ)).obj T ⟶ E)
    [QuasiIso a] :
    letI : (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v} (Ideal.Quotient.mk I)).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).Additive :=
      CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
        (by change PreservesFiniteColimits _; infer_instance)
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.IsStrictlyLE b ∧ (∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) ∧
      ∃ eRed : ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk
        I)).mapHomologicalComplex (.up ℤ)).obj P ≅ E,
      ∃ eT : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj T,
        DerivedCategory.Q.map
          ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v}
            (Ideal.Quotient.mk I))
            (.up ℤ)).homEquiv _ _ eRed.hom) =
          eT.hom ≫ DerivedCategory.Q.map
            ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v}
              (Ideal.Quotient.mk I))
              (.up ℤ)).homEquiv _ _ a) := by
  obtain ⟨c, hc⟩ := hT.upperBound
  exact exists_lift_of_reduction_quasiIso_of_lift I T c _
    (fun P h i ↦ by have := (h i).2; infer_instance) hT.finiteFree E b a
    fun e ↦ exists_finiteFree_lift_representing_iso_with_bound I hI (DerivedCategory.Q.obj T) E b
      hE e ⟨T, hT, ⟨Iso.refl _⟩⟩

/-- An additive functor carries the difference map of a tower to the difference map of the
image tower, compatibly with the product comparison. -/
lemma map_pi_difference_comp_piComparison
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (M : ℕ → C) (g : ∀ n, M (n + 1) ⟶ M n)
    [HasProduct M] [HasProduct fun n ↦ F.obj (M n)] :
    F.map (Pi.lift fun n ↦ Pi.π M n - Pi.π M (n + 1) ≫ g n) ≫ piComparison F M =
      piComparison F M ≫ Pi.lift (fun n ↦ Pi.π (fun n ↦ F.obj (M n)) n -
        Pi.π (fun n ↦ F.obj (M n)) (n + 1) ≫ F.map (g n)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.lift_π, Preadditive.comp_sub]
  rw [piComparison_comp_π, ← F.map_comp, Pi.lift_π, F.map_sub, F.map_comp]
  rw [← Category.assoc, piComparison_comp_π]

/-- The complex-level form of `epi_pi_difference_of_surjective`: for a tower of cochain
complexes that is degreewise surjective, the difference map is an epimorphism. -/
lemma epi_complex_pi_difference_of_surjective
    {R : Type u} [Ring R] (M : ℕ → CochainComplex (ModuleCat.{max u v} R) ℤ)
    (g : ∀ n, M (n + 1) ⟶ M n)
    (hg : ∀ n i, Function.Surjective ((g n).f i)) :
    Epi (Pi.lift fun n ↦ Pi.π M n - Pi.π M (n + 1) ≫ g n) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  let F := HomologicalComplex.eval (ModuleCat.{max u v} R) (.up ℤ) i
  have : Epi (Pi.lift fun n ↦ Pi.π (fun n ↦ F.obj (M n)) n -
      Pi.π (fun n ↦ F.obj (M n)) (n + 1) ≫ F.map (g n)) :=
    epi_pi_difference_of_surjective _ _ (fun n ↦ hg n i)
  have h := map_pi_difference_comp_piComparison F M g
  have hδ : Epi (F.map (Pi.lift fun n ↦ Pi.π M n - Pi.π M (n + 1) ≫ g n) ≫
      piComparison F M) := by rw [h]; infer_instance
  exact (epi_comp_iff_of_isIso _ (piComparison F M)).mp hδ

set_option backward.isDefEq.respectTransparency false in
/-- The Milnor distinguished triangle of a degreewise surjective tower of cochain complexes:
the derived limit sits in a triangle with the product of the terms and their difference map. -/
lemma exists_distTriang_of_degreewise_surjective
    {R : Type u} [Ring R] (M : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hg : ∀ n i, Function.Surjective ((M.map (homOfLE (Nat.le_succ n)).op).f i))
    [HasProduct fun n : ℕ ↦ DerivedCategory.Q.obj (M.obj (op n))] :
    let X := fun n : ℕ ↦ DerivedCategory.Q.obj (M.obj (op n))
    ∃ δ : ∏ᶜ X ⟶ (DerivedCategory.Q.obj (limit M))⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk
        (Pi.lift fun n ↦ DerivedCategory.Q.map (limit.π M (op n)))
        (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫
          DerivedCategory.Q.map (M.map (homOfLE (Nat.le_succ n)).op)) δ ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} R)) := by
  intro X
  have : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} R) :=
    HasExactLimitsOfShape.domain_of_functor (Discrete ℕ)
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
  have := Stacks.DerivedProducts.preservesLimitsOfShape_Q (A := ModuleCat.{max u v} R) (I := ℕ)
  let N := fun n : ℕ ↦ M.obj (op n)
  let d := Pi.lift fun n ↦ Pi.π N n - Pi.π N (n + 1) ≫
    M.map (homOfLE (Nat.le_succ n)).op
  let p := Pi.lift fun n : ℕ ↦ limit.π M (op n)
  have hpd : p ≫ d = 0 := (inverseSystemLimitKernelFork M).condition
  let S := ShortComplex.mk p d hpd
  have hker : IsLimit (KernelFork.ofι p hpd) := inverseSystemLimitKernelForkIsLimit M
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel hker)
      (mono_of_isLimit_fork hker) (epi_complex_pi_difference_of_surjective N _ hg)
  let e := asIso (piComparison (DerivedCategory.Q (C := ModuleCat.{max u v} R)) N)
  refine ⟨e.inv ≫ DerivedCategory.triangleOfSESδ hS, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · show (Pi.lift fun n ↦ DerivedCategory.Q.map (limit.π M (op n))) ≫ e.inv =
      𝟙 _ ≫ DerivedCategory.Q.map p
    rw [Category.id_comp, Iso.comp_inv_eq]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_π]
    show _ = DerivedCategory.Q.map p ≫ piComparison DerivedCategory.Q N ≫ Pi.π X n
    rw [piComparison_comp_π, ← Functor.map_comp]
    simp [p, N, X]
  · show (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫
      DerivedCategory.Q.map (M.map (homOfLE (Nat.le_succ n)).op)) ≫ e.inv =
      e.inv ≫ DerivedCategory.Q.map d
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, e.inv_hom_id]
    rw [show DerivedCategory.Q.map d ≫ e.hom = e.hom ≫
        (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫
          DerivedCategory.Q.map (M.map (homOfLE (Nat.le_succ n)).op)) from
      map_pi_difference_comp_piComparison DerivedCategory.Q N _]
    simp only [← Category.assoc, e.inv_hom_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · show (e.inv ≫ DerivedCategory.triangleOfSESδ hS) ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{max u v} R)) (1 : ℤ)).map
        (𝟙 (DerivedCategory.Q.obj (limit M))) = e.inv ≫ DerivedCategory.triangleOfSESδ hS
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _

/-- Extension of scalars is additive, as the left adjoint of additive restriction. -/
public lemma extendScalarsGeneral_additive
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, w, max w v} f).Additive := by
  have : (ModuleCat.extendScalars.{u, w, max w v} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{v} f).isLeftAdjoint
  exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits _; infer_instance)

attribute [local instance] extendScalarsGeneral_additive

private lemma finiteFree_restrictScalars_ringEquiv
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] (e : R ≃+* S)
    (M : ModuleCat.{v} S) [Module.Finite S M] [Module.Free S M] :
    Module.Finite R ((ModuleCat.restrictScalars e.toRingHom).obj M) ∧
      Module.Free R ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  have h₁ : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  have h₂ : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let l : LinearEquiv e.symm.toRingHom (σ' := e.toRingHom)
      M ((ModuleCat.restrictScalars e.toRingHom).obj M) :=
    { Equiv.refl M with
      map_add' := fun _ _ => rfl
      map_smul' := fun s x => by
        show s • x = e (e.symm s) • x
        rw [e.apply_symm_apply] }
  exact ⟨Module.Finite.of_surjective l.toLinearMap l.surjective, Module.Free.of_equiv l⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lift a finite free reduction along a surjection, retaining the prescribed derived chain map. -/
public lemma exists_finiteFree_lift_of_surjective_reduction
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hI : (RingHom.ker f).IsLocallyNilpotent)
    (T : CochainComplex (ModuleCat.{max u v w} R) ℤ) (hT : PseudoCoherence.IsBoundedAboveFiniteFree
      T)
    (E : CochainComplex (ModuleCat.{max u v w} S) ℤ) (b : ℤ) [E.IsStrictlyLE b]
    (hE : ∀ i, Module.Finite S (E.X i) ∧ Module.Free S (E.X i))
    (a : ((ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex (.up ℤ)).obj T ⟶ E)
    [QuasiIso a] :
    ∃ P : CochainComplex (ModuleCat.{max u v w} R) ℤ,
      P.IsStrictlyLE b ∧ (∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) ∧
      ∃ eRed : ((ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex (.up ℤ)).obj P ≅
        E,
      ∃ eT : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj T,
        DerivedCategory.Q.map
          ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f)
            (.up ℤ)).homEquiv _ _ eRed.hom) =
          eT.hom ≫ DerivedCategory.Q.map
            ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f)
              (.up ℤ)).homEquiv _ _ a) := by
  let q := Ideal.Quotient.mk (RingHom.ker f)
  let e := RingHom.quotientKerEquivOfSurjective hf
  let : (ModuleCat.extendScalars.{u, u, max u v w} q).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v w} q).left_adjoint_additive
  let H := (ModuleCat.restrictScalars.{max u v w} e.toRingHom).mapHomologicalComplex (.up ℤ)
  let F := (ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex (.up ℤ)
  let Fq := (ModuleCat.extendScalars.{u, u, max u v w} q).mapHomologicalComplex (.up ℤ)
  let z : Fq ≅ F ⋙ H := (Functor.mapHomologicalComplexCompIso
    (extendScalarsQuotientKerIso.{u, v, w} f hf).symm (.up ℤ)).symm
  let a' : Fq.obj T ⟶ H.obj E := z.hom.app T ≫ H.map a
  have : QuasiIso a' := by dsimp [a']; infer_instance
  have hE' (i : ℤ) : Module.Finite (R ⧸ RingHom.ker f) ((H.obj E).X i) ∧
      Module.Free (R ⧸ RingHom.ker f) ((H.obj E).X i) := by
    have := (hE i).1
    have := (hE i).2
    exact finiteFree_restrictScalars_ringEquiv e (E.X i)
  obtain ⟨P, hbP, hP, eRed', eT, heT⟩ :=
    exists_finiteFree_lift_of_reduction_quasiIso.{u, max v w} (RingHom.ker f) hI T hT
      (H.obj E) b hE' a'
  let eRed : F.obj P ≅ E := H.preimageIso ((z.app P).symm ≪≫ eRed')
  have heRed : z.hom.app P ≫ H.map eRed.hom = eRed'.hom := by
    simp [eRed]
  let G := (ModuleCat.restrictScalars.{max u v w} f).mapHomologicalComplex (.up ℤ)
  let Gq := (ModuleCat.restrictScalars.{max u v w} q).mapHomologicalComplex (.up ℤ)
  let w : H ⋙ Gq ≅ G := Functor.mapHomologicalComplexCompIso
    (ModuleCat.restrictScalarsComp' q e.toRingHom f (by ext x; rfl)).symm (.up ℤ)
  have hw (V : CochainComplex (ModuleCat.{max u v w} R) ℤ)
      (k : F.obj V ⟶ E) :
      ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} q) (.up
        ℤ)).homEquiv
        _ _ (z.hom.app V ≫ H.map k)) ≫ w.hom.app E =
      (mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f) (.up
        ℤ)).homEquiv
        _ _ k := by
    ext i x
    show k.f i ((extendScalarsQuotientKerIso.{u, v, w} f hf).hom.app (V.X i)
      ((ModuleCat.extendRestrictScalarsAdj.{max u v w} q).unit.app (V.X i) x)) =
      k.f i ((ModuleCat.extendRestrictScalarsAdj.{max u v w} f).unit.app (V.X i) x)
    exact congrArg (fun x => k.f i x)
      (extendScalarsQuotientKerIso_one_tmul.{u, v, w} f hf (V.X i) x)
  refine ⟨P, hbP, hP, eRed, eT, ?_⟩
  have h := congrArg (fun k => k ≫ DerivedCategory.Q.map (w.hom.app E)) heT
  rw [← Functor.map_comp, ← heRed, hw] at h
  rw [Category.assoc, ← Functor.map_comp, hw] at h
  exact h

lemma isKProjective_extendScalars_of_boundedAboveFiniteFree
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hP : PseudoCoherence.IsBoundedAboveFiniteFree P) :
    CochainComplex.IsKProjective
      (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨b, hb⟩ := hP.upperBound
  have hp (i : ℤ) : Projective (P.X i) := by
    have := (hP.finiteFree i).2
    infer_instance
  have hp' (i : ℤ) : Projective
      ((((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj P).X i) :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v} f).map_projective _ (hp i)
  exact CochainComplex.isKProjective_of_projective _ b

set_option backward.isDefEq.respectTransparency false in
/-- Lift a reduction retaining a prescribed derived transition map, given a lifting of the
chain-level reduction through terms satisfying a predicate `p`. -/
private lemma exists_lift_of_derived_transition_of_lift
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (K : DerivedCategory (ModuleCat.{max u v w} R))
    (L : DerivedCategory (ModuleCat.{max u v w} S))
    (φ : K ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj L)
    (hφ : IsIso (derivedBaseChangeComparison.{u, v, w} f φ))
    (E : CochainComplex (ModuleCat.{max u v w} S) ℤ) (b : ℤ)
    (eE : DerivedCategory.Q.obj E ≅ L) (T : CochainComplex (ModuleCat.{max u v w} R) ℤ)
    [T.IsKProjective]
    [CochainComplex.IsKProjective
      (((ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex (.up ℤ)).obj T)]
    (eT : DerivedCategory.Q.obj T ≅ K)
    (p : CochainComplex (ModuleCat.{max u v w} R) ℤ → Prop)
    (hlift : ∀ a : ((ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex
        (.up ℤ)).obj T ⟶ E, QuasiIso a →
      ∃ P : CochainComplex (ModuleCat.{max u v w} R) ℤ, P.IsStrictlyLE b ∧ p P ∧
      ∃ eRed : ((ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex
          (.up ℤ)).obj P ≅ E,
      ∃ eT : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj T,
        DerivedCategory.Q.map
          ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f)
            (.up ℤ)).homEquiv _ _ eRed.hom) =
          eT.hom ≫ DerivedCategory.Q.map
            ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f)
              (.up ℤ)).homEquiv _ _ a)) :
    ∃ P : CochainComplex (ModuleCat.{max u v w} R) ℤ,
      P.IsStrictlyLE b ∧ p P ∧
      ∃ eP : DerivedCategory.Q.obj P ≅ K,
      ∃ g : P ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj E,
        IsIso (((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f)
          (.up ℤ)).homEquiv _ _).symm g) ∧
        DerivedCategory.Q.map g ≫ (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app E
          ≫
          (ModuleCat.restrictScalars f).mapDerivedCategory.map eE.hom = eP.hom ≫ φ := by
  let G := ModuleCat.restrictScalars.{max u v w} f
  let adj := mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f) (.up
    ℤ)
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w} f
  let adjD := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, w, v}
    R S _ _ f _ _ D.functor D.comparison D.isLeftDerived

  obtain ⟨g, hg⟩ := exists_chainMap_of_isKProjective T _
    (eT.hom ≫ φ ≫ G.mapDerivedCategory.map eE.inv ≫ G.mapDerivedCategoryFactors.hom.app E)
  let a := (adj.homEquiv _ _).symm g
  have hga : adj.homEquiv _ _ a = g := (adj.homEquiv _ _).apply_symm_apply g
  have hqg : DerivedCategory.Q.map g ≫ G.mapDerivedCategoryFactors.inv.app E =
      eT.hom ≫ φ ≫ G.mapDerivedCategory.map eE.inv := by rw [hg]; simp
  have hqa : QuasiIso a := by
    apply (isIso_derived_transpose_iff (ModuleCat.extendRestrictScalarsAdj.{max u v w} f) adjD T E
      a).mp
    rw [hga, hqg, Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_right_symm]
    show IsIso (D.functor.map eT.hom ≫ derivedBaseChangeComparison.{u, v, w} f φ ≫ eE.inv)
    infer_instance
  obtain ⟨P, hbP, hP, eRed, ePT, hePT⟩ := hlift a hqa
  let gP := adj.homEquiv _ _ eRed.hom
  refine ⟨P, hbP, hP, ePT ≪≫ eT, gP, ?_, ?_⟩
  · show IsIso ((adj.homEquiv _ _).symm (adj.homEquiv _ _ eRed.hom))
    rw [Equiv.symm_apply_apply]
    infer_instance
  · show DerivedCategory.Q.map gP ≫ G.mapDerivedCategoryFactors.inv.app E ≫
        G.mapDerivedCategory.map eE.hom = (ePT.hom ≫ eT.hom) ≫ φ
    rw [show DerivedCategory.Q.map gP = ePT.hom ≫ DerivedCategory.Q.map g from by
      change DerivedCategory.Q.map (adj.homEquiv _ _ eRed.hom) =
        ePT.hom ≫ DerivedCategory.Q.map (adj.homEquiv _ _ a) at hePT
      rw [hga] at hePT
      exact hePT]
    rw [Category.assoc, ← Category.assoc (DerivedCategory.Q.map g), hqg]
    simp only [Category.assoc, ← G.mapDerivedCategory.map_comp, eE.inv_hom_id,
      G.mapDerivedCategory.map_id]
    exact congrArg (fun k => ePT.hom ≫ eT.hom ≫ k) (Category.comp_id φ)

lemma exists_finiteFree_lift_of_derived_transition
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hI : (RingHom.ker f).IsLocallyNilpotent)
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : PseudoCoherence.IsPseudoCoherent K)
    (L : DerivedCategory (ModuleCat.{max u v} S))
    (φ : K ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj L)
    (hφ : IsIso (derivedBaseChangeComparison f φ))
    (E : CochainComplex (ModuleCat.{max u v} S) ℤ) (b : ℤ) [E.IsStrictlyLE b]
    (hE : ∀ i, Module.Finite S (E.X i) ∧ Module.Free S (E.X i))
    (eE : DerivedCategory.Q.obj E ≅ L) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.IsStrictlyLE b ∧ (∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) ∧
      ∃ eP : DerivedCategory.Q.obj P ≅ K,
      ∃ g : P ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj E,
        IsIso (((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v} f)
          (.up ℤ)).homEquiv _ _).symm g) ∧
        DerivedCategory.Q.map g ≫ (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app E
          ≫
          (ModuleCat.restrictScalars f).mapDerivedCategory.map eE.hom = eP.hom ≫ φ := by
  obtain ⟨T, hT, ⟨eT⟩⟩ := hK
  have : T.IsKProjective := isKProjective_of_boundedAboveFiniteFree T hT
  have := isKProjective_extendScalars_of_boundedAboveFiniteFree f T hT
  exact exists_lift_of_derived_transition_of_lift.{u, v, u} f K L φ hφ E b eE T eT
    (fun P ↦ ∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i))
    fun a _ ↦ exists_finiteFree_lift_of_surjective_reduction.{u, v, u} f hf hI T hT E b hE a

private lemma exists_projective_lift_representing_iso_with_bound
    {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) [E.IsStrictlyLE b]
    (hEprojective : ∀ i, Module.Projective (R ⧸ I) (E.X i))
    (e : DerivedCategory.Q.obj E ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        (Ideal.Quotient.mk I)).functor.obj K)
    (hKrep : ∃ T : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∀ i, Module.Projective R (T.X i)) ∧ (∃ c, T.IsStrictlyLE c) ∧
        Nonempty (DerivedCategory.Q.obj T ≅ K)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.IsStrictlyLE b ∧ (∀ i, Module.Projective R (P.X i)) ∧
      ∃ eRed : ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk
        I)).mapHomologicalComplex
          (.up ℤ)).obj P ≅ E,
      ∃ eK : DerivedCategory.Q.obj P ≅ K,
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          (Ideal.Quotient.mk I)).comparison.app P ≫
          DerivedCategory.Q.map eRed.hom ≫ e.hom =
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          (Ideal.Quotient.mk I)).functor.map eK.hom := by
  classical
  let F := ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)
  have hsum (M N : ModuleCat.{max u v} R) :
      (Module.Projective R M ∧ Module.Projective R ↑(M ⊞ N)) ↔
        (Module.Projective R M ∧ Module.Projective R N) := by
    constructor
    · rintro ⟨hM, hMN⟩
      have := hMN
      have : Projective (M ⊞ N) := inferInstance
      have : Projective N := (show Retract N (M ⊞ N) from
        ⟨biprod.inr, biprod.snd, biprod.inr_snd⟩).projective
      exact ⟨hM, inferInstance⟩
    · rintro ⟨hM, hN⟩
      have := hM
      have := hN
      have : Projective M := inferInstance
      have : Projective N := inferInstance
      exact ⟨hM, inferInstance⟩
  have hsurj (M N : ModuleCat.{max u v} R) (f : M ⟶ N)
      (_ : Module.Projective R M) (_ : Module.Projective R N)
      (hf : Function.Surjective (F.map f).hom) : Function.Surjective f.hom := by
    apply LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent I f.hom hI
    let q := TensorProduct.quotTensorEquivQuotSMul N I
    let η := (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).unit.app M
    have hη : Function.Surjective η.hom := by
      let qM := TensorProduct.quotTensorEquivQuotSMul M I
      intro z
      obtain ⟨x, hx⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective (qM z)
      refine ⟨x, qM.injective ?_⟩
      show qM ((1 : R ⧸ I) ⊗ₜ[R] x) = qM z
      simpa [qM] using hx
    intro y
    obtain ⟨z, hz⟩ := hf (q.symm y)
    obtain ⟨x, rfl⟩ := hη z
    refine ⟨x, ?_⟩
    have h := congrArg q hz
    change q ((1 : R ⧸ I) ⊗ₜ[R] f x) = q (q.symm y) at h
    simpa [q] using h
  have hterms (i : ℤ) : ∃ M : ModuleCat.{max u v} R,
      Module.Projective R M ∧ Nonempty (E.X i ≅ F.obj M) := by
    have := hEprojective i
    obtain ⟨M, _, _, hM, ⟨e⟩⟩ :=
      Module.exists_projective_quotient_smul_top_linearEquiv_of_isNilpotent
        (R := R) (I := I) (Q := E.X i) hI
    let q : TensorProduct R (R ⧸ I) M ≃ₗ[R ⧸ I]
        (M ⧸ I • (⊤ : Submodule R M)) :=
      (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective
    exact ⟨ModuleCat.of R M, hM, ⟨(q.trans e).toModuleIso.symm⟩⟩
  obtain ⟨P, hP, _, eRed, eK, he⟩ := StacksDraft.Perfect.exists_boundedAbove_lift_representing_iso
    I (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
      (Ideal.Quotient.mk I)) (fun M => Module.Projective R M) K E (fun _ h => h) hsum hsurj
      ⟨b, inferInstance⟩ hterms e hKrep
  refine ⟨P, (CochainComplex.isStrictlyLE_iff P b).mpr ?_, hP, eRed, eK, he⟩
  intro i hi
  have hz : IsZero (F.obj (P.X i)) :=
    (CochainComplex.isZero_of_isStrictlyLE E b i hi).of_iso
      ((HomologicalComplex.eval _ _ i).mapIso eRed)
  have : Subsingleton ((R ⧸ I) ⊗[R] (P.X i)) := ModuleCat.subsingleton_of_isZero hz
  have : Subsingleton (P.X i ⧸ I • (⊤ : Submodule R (P.X i))) :=
    (TensorProduct.quotTensorEquivQuotSMul (P.X i) I).surjective.subsingleton
  have htop : I • (⊤ : Submodule R (P.X i)) = ⊤ := Submodule.Quotient.subsingleton_iff.mp
    inferInstance
  have hbot : (⊤ : Submodule R (P.X i)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_isNilpotent I ⊤ hI (by rw [htop])
  have : Subsingleton (P.X i) := subsingleton_of_forall_eq 0 fun x ↦
    (show x ∈ (⊥ : Submodule R (P.X i)) from hbot ▸ Submodule.mem_top)
  exact ModuleCat.isZero_of_subsingleton _

set_option backward.isDefEq.respectTransparency false in
private lemma exists_projective_lift_of_reduction_quasiIso
    {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    (T : CochainComplex (ModuleCat.{max u v} R) ℤ) (hT : ∃ c, T.IsStrictlyLE c)
    (hTprojective : ∀ i, Module.Projective R (T.X i))
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) [E.IsStrictlyLE b]
    (hE : ∀ i, Module.Projective (R ⧸ I) (E.X i))
    (a : ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).mapHomologicalComplex (.up
      ℤ)).obj T ⟶ E)
    [QuasiIso a] :
    letI : (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v} (Ideal.Quotient.mk I)).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).Additive :=
      CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
        (by change PreservesFiniteColimits _; infer_instance)
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.IsStrictlyLE b ∧ (∀ i, Module.Projective R (P.X i)) ∧
      ∃ eRed : ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk
        I)).mapHomologicalComplex (.up ℤ)).obj P ≅ E,
      ∃ eT : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj T,
        DerivedCategory.Q.map
          ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v}
            (Ideal.Quotient.mk I))
            (.up ℤ)).homEquiv _ _ eRed.hom) =
          eT.hom ≫ DerivedCategory.Q.map
            ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v}
              (Ideal.Quotient.mk I))
              (.up ℤ)).homEquiv _ _ a) := by
  obtain ⟨c, hc⟩ := hT
  exact exists_lift_of_reduction_quasiIso_of_lift I T c _
    (fun P h i ↦ by have := h i; infer_instance) hTprojective E b a
    fun e ↦ exists_projective_lift_representing_iso_with_bound I hI (DerivedCategory.Q.obj T) E b
      hE e ⟨T, hTprojective, ⟨c, hc⟩, ⟨Iso.refl _⟩⟩


set_option backward.isDefEq.respectTransparency false in
/-- Lift a projective reduction along a surjection with nilpotent kernel, retaining the
prescribed derived chain map and its upper bound. -/
public lemma exists_projective_lift_of_surjective_reduction
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hI : IsNilpotent (RingHom.ker f))
    (T : CochainComplex (ModuleCat.{max u v w} R) ℤ) (hT : ∃ c, T.IsStrictlyLE c)
    (hTprojective : ∀ i, Module.Projective R (T.X i))
    (E : CochainComplex (ModuleCat.{max u v w} S) ℤ) (b : ℤ) [E.IsStrictlyLE b]
    (hE : ∀ i, Module.Projective S (E.X i))
    (a : ((ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex (.up ℤ)).obj T ⟶ E)
    [QuasiIso a] :
    ∃ P : CochainComplex (ModuleCat.{max u v w} R) ℤ,
      P.IsStrictlyLE b ∧ (∀ i, Module.Projective R (P.X i)) ∧
      ∃ eRed : ((ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex (.up ℤ)).obj P ≅
        E,
      ∃ eT : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj T,
        DerivedCategory.Q.map
          ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f)
            (.up ℤ)).homEquiv _ _ eRed.hom) =
          eT.hom ≫ DerivedCategory.Q.map
            ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f)
              (.up ℤ)).homEquiv _ _ a) := by
  let q := Ideal.Quotient.mk (RingHom.ker f)
  let e := RingHom.quotientKerEquivOfSurjective hf
  let : (ModuleCat.extendScalars.{u, u, max u v w} q).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v w} q).left_adjoint_additive
  let H := (ModuleCat.restrictScalars.{max u v w} e.toRingHom).mapHomologicalComplex (.up ℤ)
  let F := (ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex (.up ℤ)
  let Fq := (ModuleCat.extendScalars.{u, u, max u v w} q).mapHomologicalComplex (.up ℤ)
  let z : Fq ≅ F ⋙ H := (Functor.mapHomologicalComplexCompIso
    (extendScalarsQuotientKerIso.{u, v, w} f hf).symm (.up ℤ)).symm
  let a' : Fq.obj T ⟶ H.obj E := z.hom.app T ≫ H.map a
  have : QuasiIso a' := by dsimp [a']; infer_instance
  have hE' (i : ℤ) : Module.Projective (R ⧸ RingHom.ker f) ((H.obj E).X i) := by
    have := hE i
    have hp : Projective (E.X i) := inferInstance
    have : Projective ((H.obj E).X i) :=
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).toAdjunction.map_projective _ hp
    infer_instance
  obtain ⟨P, hbP, hP, eRed', eT, heT⟩ :=
    exists_projective_lift_of_reduction_quasiIso.{u, max v w} (RingHom.ker f) hI T hT hTprojective
      (H.obj E) b hE' a'
  let eRed : F.obj P ≅ E := H.preimageIso ((z.app P).symm ≪≫ eRed')
  have heRed : z.hom.app P ≫ H.map eRed.hom = eRed'.hom := by
    simp [eRed]
  let G := (ModuleCat.restrictScalars.{max u v w} f).mapHomologicalComplex (.up ℤ)
  let Gq := (ModuleCat.restrictScalars.{max u v w} q).mapHomologicalComplex (.up ℤ)
  let w : H ⋙ Gq ≅ G := Functor.mapHomologicalComplexCompIso
    (ModuleCat.restrictScalarsComp' q e.toRingHom f (by ext x; rfl)).symm (.up ℤ)
  have hw (V : CochainComplex (ModuleCat.{max u v w} R) ℤ)
      (k : F.obj V ⟶ E) :
      ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} q) (.up
        ℤ)).homEquiv
        _ _ (z.hom.app V ≫ H.map k)) ≫ w.hom.app E =
      (mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f) (.up
        ℤ)).homEquiv
        _ _ k := by
    ext i x
    show k.f i ((extendScalarsQuotientKerIso.{u, v, w} f hf).hom.app (V.X i)
      ((ModuleCat.extendRestrictScalarsAdj.{max u v w} q).unit.app (V.X i) x)) =
      k.f i ((ModuleCat.extendRestrictScalarsAdj.{max u v w} f).unit.app (V.X i) x)
    exact congrArg (fun x => k.f i x)
      (extendScalarsQuotientKerIso_one_tmul.{u, v, w} f hf (V.X i) x)
  refine ⟨P, hbP, hP, eRed, eT, ?_⟩
  have h := congrArg (fun k => k ≫ DerivedCategory.Q.map (w.hom.app E)) heT
  rw [← Functor.map_comp, ← heRed, hw] at h
  rw [Category.assoc, ← Functor.map_comp, hw] at h
  exact h


set_option backward.isDefEq.respectTransparency false in
/-- Lift a bounded-above projective representative across a nilpotent surjection with the
chosen transition map. Its chain-level adjoint is an isomorphism, and its localization agrees
with the prescribed derived transition under the chosen representative isomorphisms. -/
public lemma exists_projective_lift_of_derived_transition
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hI : IsNilpotent (RingHom.ker f))
    (K : DerivedCategory (ModuleCat.{max u v w} R))
    (L : DerivedCategory (ModuleCat.{max u v w} S))
    (φ : K ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj L)
    (hφ : IsIso (derivedBaseChangeComparison.{u, v, w} f φ))
    (E : CochainComplex (ModuleCat.{max u v w} S) ℤ) (b : ℤ) [E.IsStrictlyLE b]
    (hE : ∀ i, Module.Projective S (E.X i))
    (eE : DerivedCategory.Q.obj E ≅ L) :
    ∃ P : CochainComplex (ModuleCat.{max u v w} R) ℤ,
      P.IsStrictlyLE b ∧ (∀ i, Module.Projective R (P.X i)) ∧
      ∃ eP : DerivedCategory.Q.obj P ≅ K,
      ∃ g : P ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj E,
        IsIso (((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v w} f)
          (.up ℤ)).homEquiv _ _).symm g) ∧
        DerivedCategory.Q.map g ≫ (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app E
          ≫
          (ModuleCat.restrictScalars f).mapDerivedCategory.map eE.hom = eP.hom ≫ φ := by
  obtain ⟨T, hT, hTprojective, ⟨eT⟩, _⟩ :=
    StacksDraft.Perfect.exists_boundedAbove_projective_lift_representing_of_surjective.{u, v, w} f
      hf E K
      ⟨b, inferInstance⟩ hE ⟨eE ≪≫ (asIso (derivedBaseChangeComparison.{u, v, w} f φ)).symm⟩ hI
  obtain ⟨c, hc⟩ := hT
  have hp (i : ℤ) : Projective (T.X i) := by
    have := hTprojective i
    infer_instance
  have : T.IsKProjective := CochainComplex.isKProjective_of_projective T c
  have hp' (i : ℤ) : Projective
      ((((ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex (.up ℤ)).obj T).X i) :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v w} f).map_projective _ (hp i)
  have : CochainComplex.IsKProjective
      (((ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex (.up ℤ)).obj T) :=
    CochainComplex.isKProjective_of_projective _ c
  exact exists_lift_of_derived_transition_of_lift.{u, v, w} f K L φ hφ E b eE T eT
    (fun P ↦ ∀ i, Module.Projective R (P.X i)) fun a _ ↦
      exists_projective_lift_of_surjective_reduction.{u, v, w} f hf hI T ⟨c, hc⟩ hTprojective E b hE
        a

end StacksDraft.DerivedInverseLimit

end
