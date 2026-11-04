module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative.ElementarySplitting
import all StacksFrontier.Homology.Perfect.MinimalRepresentative.ElementarySplitting

/-!
# Minimal representatives over a local ring

Derived base change preserves pseudo-coherence and perfectness, a stably free bounded above
representative lifts through a quotient, and over a field a complex has a representative with zero
differentials. Over a local ring this gives the rank-minimal bounded above free representative and
its uniqueness: `exists_unique_boundedAbove_free_complex_representing` ([stacks 0BCC]) and its
general form `exists_unique_boundedAbove_free_complex_representing_of_datum`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

open scoped TensorProduct ChangeOfRings

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-! ### Base change along a total derived extension of scalars -/

/-- Termwise extension of scalars along a homomorphism of rings in a common universe is additive,
which is what makes the induced functor on cochain complexes available. -/
private instance extendScalarsAdditive {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} : (ModuleCat.extendScalars.{u, u, max v u} f).Additive :=
  extendScalars_additive.{u, u, max v u} f

/-- Extension of scalars carries a free module to a free module. -/
private theorem free_extendScalars
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : ModuleCat.{max v u} R) (hfree : Module.Free R P) :
    Module.Free S ((ModuleCat.extendScalars.{u, u, max v u} f).obj P) := by
  let : Module.Free R P := hfree
  let : Algebra R S := f.toAlgebra
  have heq : (inferInstance : Module R S) = Module.compHom S f :=
    Module.ext' _ _ (by intro r s; rfl)
  cases heq
  show Module.Free S (TensorProduct R S P)
  infer_instance

/-- On a bounded above complex of projectives, the total derived extension of scalars is computed
by termwise extension of scalars. -/
private noncomputable def comparisonIso {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}
    (D : TotalDerivedExtensionScalars.{u, v, u} f) (P : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (b : ℤ) [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] :
    D.functor.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  @asIso _ _ _ _ (D.comparison.app P) (D.comparison_isIso_of_projective P b)

/-- A total derived extension of scalars preserves pseudo-coherence: this is the
pseudo-coherence half of [stacks 0650], in the form the minimal representative needs. -/
private theorem isPseudoCoherent_totalDerived
    {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}
    (D : TotalDerivedExtensionScalars.{u, v, u} f)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (D.functor.obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  let F := ModuleCat.extendScalars.{u, u, max v u} f
  let : E.IsStrictlyLE b := hb
  have hproj (i : ℤ) : Projective (E.X i) := by
    let := (hE.finiteFree i).2
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
  let := hproj
  let E' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E
  have hLE : CochainComplex.IsStrictlyLE E' b := by dsimp only [E']; infer_instance
  refine ⟨E', ⟨⟨b, hLE⟩, fun i => ⟨?_, ?_⟩⟩, ⟨?_⟩⟩
  · exact finite_extendScalars.{u, v} f (E.X i) (hE.finiteFree i).1
  · exact free_extendScalars.{u, v} f (E.X i) (hE.finiteFree i).2
  · exact (comparisonIso.{u, v} D E b).symm ≪≫ D.functor.mapIso e

/-- A perfect object is represented by a bounded complex of finite terms that are projective
objects of the category of modules. -/
private theorem exists_projective_complex_of_isPerfect
    {R : Type u} [CommRing R] {K : DerivedCategory (ModuleCat.{max v u} R)} (hK : IsPerfect K) :
    ∃ (P : CochainComplex (ModuleCat.{max v u} R) ℤ) (a b : ℤ), P.IsStrictlyGE a ∧
      P.IsStrictlyLE b ∧ (∀ i, Module.Finite R (P.X i)) ∧ (∀ i, Projective (P.X i)) ∧
      Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨P, a, b, ha, hb, hfinite, hprojective, e⟩ := hK
  exact ⟨P, a, b, ha, hb, hfinite, fun i => by
    let := hprojective i
    infer_instance, e⟩

/-- A total derived extension of scalars preserves perfectness: this is [stacks 066W] in the
form the minimal representative needs. -/
private theorem isPerfect_totalDerived
    {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}
    (D : TotalDerivedExtensionScalars.{u, v, u} f)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : IsPerfect K) : IsPerfect (D.functor.obj K) := by
  obtain ⟨P, a, b, ha, hb, hfinite, hproj, ⟨e⟩⟩ :=
    exists_projective_complex_of_isPerfect.{u, v} hK
  let F := ModuleCat.extendScalars.{u, u, max v u} f
  let := ha
  let := hb
  let := hproj
  let P' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  refine ⟨P', a, b, ?_, ?_, fun i => ?_, fun i => ?_, ⟨?_⟩⟩
  · dsimp only [P']; infer_instance
  · dsimp only [P']; infer_instance
  · exact finite_extendScalars.{u, v} f (P.X i) (hfinite i)
  · let := projective_extendScalars.{u, v} f (P.X i) (hproj i)
    show Module.Projective A (F.obj (P.X i))
    exact ModuleCat.projective_of_module_projective (F.obj (P.X i))
  · exact D.functor.mapIso e ≪≫ comparisonIso.{u, v} D P b

/-- Two successive total derived extensions of scalars agree with the total derived extension of
scalars along the composite, on perfect objects. -/
private theorem totalDerived_comp_of_isPerfect
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] {f : R →+* A} {g : A →+* B}
    (Df : TotalDerivedExtensionScalars.{u, v, u} f)
    (Dg : TotalDerivedExtensionScalars.{u, v, u} g)
    (Dgf : TotalDerivedExtensionScalars.{u, v, u} (g.comp f))
    {K : DerivedCategory (ModuleCat.{max v u} R)} (hK : IsPerfect K) :
    Nonempty (Dg.functor.obj (Df.functor.obj K) ≅ Dgf.functor.obj K) := by
  obtain ⟨P, a, b, ha, hb, hfinite, hproj, ⟨e⟩⟩ :=
    exists_projective_complex_of_isPerfect.{u, v} hK
  let := hb
  let := hproj
  let F := ModuleCat.extendScalars.{u, u, max v u} f
  let PA := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hPA : CochainComplex.IsStrictlyLE PA b := by dsimp only [PA]; infer_instance
  have hPAproj (i : ℤ) : Projective (PA.X i) :=
    projective_extendScalars.{u, v} f (P.X i) (hproj i)
  let := hPAproj
  exact ⟨Dg.functor.mapIso (Df.functor.mapIso e ≪≫ comparisonIso.{u, v} Df P b) ≪≫
    comparisonIso.{u, v} Dg PA b ≪≫
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, max v u} f g)
        (ComplexShape.up ℤ)) DerivedCategory.Q).symm.app P ≪≫
    (comparisonIso.{u, v} Dgf P b).symm ≪≫ (Dgf.functor.mapIso e).symm⟩

/-! ### Lifting a stably free representative through a quotient -/

/-- Regrouping `B × C × (A × E)` as `((A × B) × C) × E`. -/
private def prodShuffleFour {R : Type*} [CommRing R] (A B C E : Type*)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup E] [Module R E] :
    (B × C × (A × E)) ≃ₗ[R] ((A × B) × C) × E where
  toFun x := (((x.2.2.1, x.1), x.2.1), x.2.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := (y.1.1.2, (y.1.2, (y.1.1.1, y.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regrouping `(A × B) × (C × E)` as `(A × C) × (B × E)`. -/
private def prodShuffleTwoTwo {R : Type*} [CommRing R] (A B C E : Type*)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup E] [Module R E] :
    ((A × B) × (C × E)) ≃ₗ[R] (A × C) × (B × E) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Being finite and stably free passes between a binary biproduct and its second summand, once
the first summand is known to be finite and stably free. This is the closure property that the
lifting theorem [stacks 0BCA] requires of the class of modules it lifts. -/
private theorem finite_isStablyFree_biprod_iff {R : Type u} [CommRing R]
    (M₁ M₂ : ModuleCat.{max v u} R) :
    ((Module.Finite R M₁ ∧ Module.IsStablyFree R M₁) ∧
        (Module.Finite R (M₁ ⊞ M₂ : ModuleCat.{max v u} R) ∧
          Module.IsStablyFree R (M₁ ⊞ M₂ : ModuleCat.{max v u} R))) ↔
      ((Module.Finite R M₁ ∧ Module.IsStablyFree R M₁) ∧
        (Module.Finite R M₂ ∧ Module.IsStablyFree R M₂)) := by
  let eb := (ModuleCat.biprodIsoProd M₁ M₂).toLinearEquiv
  constructor
  · rintro ⟨⟨hf₁, hs₁⟩, hf, hs⟩
    have : Module.Finite R (M₁ × M₂) := Module.Finite.equiv eb
    have : Module.IsStablyFree R (M₁ × M₂) := hs.equiv eb
    refine ⟨⟨hf₁, hs₁⟩, Module.Finite.of_surjective (LinearMap.snd R M₁ M₂)
      LinearMap.snd_surjective, ?_⟩
    obtain ⟨N₁, _, _, _, _, hF₁⟩ := Module.IsStablyFree.exist_free_prod R M₁
    obtain ⟨N, _, _, _, _, hG⟩ := Module.IsStablyFree.exist_free_prod R (M₁ × M₂)
    have : Module.Free R (M₂ × N × (M₁ × N₁)) :=
      Module.Free.of_equiv (prodShuffleFour (R := R) M₁ M₂ N N₁).symm
    exact Module.IsStablyFree.of_free_prod R M₂ (N × (M₁ × N₁))
  · rintro ⟨⟨hf₁, hs₁⟩, hf₂, hs₂⟩
    refine ⟨⟨hf₁, hs₁⟩, Module.Finite.equiv eb.symm, ?_⟩
    obtain ⟨N₁, _, _, _, _, hF₁⟩ := Module.IsStablyFree.exist_free_prod R M₁
    obtain ⟨N₂, _, _, _, _, hF₂⟩ := Module.IsStablyFree.exist_free_prod R M₂
    have : Module.Free R ((M₁ × M₂) × (N₁ × N₂)) :=
      Module.Free.of_equiv (prodShuffleTwoTwo (R := R) M₁ N₁ M₂ N₂)
    exact (Module.IsStablyFree.of_free_prod R (M₁ × M₂) (N₁ × N₂)).equiv eb.symm

/-- Reduction modulo `I`, as extension of scalars, agrees with the quotient by `I • ⊤`. -/
private noncomputable def quotTensorEquiv {R : Type u} [CommRing R] (I : Ideal R)
    (M : ModuleCat.{max v u} R) :
    TensorProduct R (R ⧸ I) M ≃ₗ[R ⧸ I] (M ⧸ I • (⊤ : Submodule R M)) :=
  (TensorProduct.quotTensorEquivQuotSMul (R := R) M I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- Surjectivity of a homomorphism of finite modules is detected after reduction modulo an ideal
whose elements make `1 + x` a unit. -/
private theorem surjective_of_surjective_extendScalars {R : Type u} [CommRing R] (I : Ideal R)
    (hI : ∀ x : R, x ∈ I → IsUnit (1 + x))
    {M N : ModuleCat.{max v u} R} [Module.Finite R N] (f : M ⟶ N)
    (hf : Function.Surjective
      (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom)) :
    Function.Surjective f.hom := by
  apply surj_aux I hI f.hom
  let e₁ := quotTensorEquiv.{u, v} I M
  let e₂ := quotTensorEquiv.{u, v} I N
  have hnat (z : TensorProduct R (R ⧸ I) M) :
      inducedQuot I f.hom (e₁ z) =
        e₂ (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom z) := by
    dsimp [e₁, e₂, quotTensorEquiv]
    induction z using TensorProduct.induction_on with
    | zero =>
      calc
        inducedQuot I f.hom 0 = 0 := map_zero _
        _ = _ := (map_zero _).symm.trans (congrArg _ (map_zero _).symm)
    | tmul x y =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      show Submodule.Quotient.mk (f.hom (r • y)) = Submodule.Quotient.mk (r • f.hom y)
      simp
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      exact (map_add _ _ _).symm.trans (congrArg _ (map_add _ _ _).symm)
  intro y
  obtain ⟨x, hx⟩ := hf (e₂.symm y)
  exact ⟨e₁ x, (hnat x).trans (by rw [hx, e₂.apply_symm_apply])⟩

/-- **Stacks 0BCB** in the form the minimal representative consumes: a bounded above complex of
finite stably free `R ⧸ I`-modules representing the derived reduction of a pseudo-coherent object
lifts to a bounded above complex of finite stably free `R`-modules representing that object, and
the lift is free in every degree in which the given complex is free. -/
private theorem exists_boundedAbove_isStablyFree_lift
    {R : Type u} [CommRing R] (I : Ideal R)
    (D : TotalDerivedExtensionScalars.{u, v, u} (Ideal.Quotient.mk I))
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i, Module.Finite (R ⧸ I) (E.X i) ∧ Module.IsStablyFree (R ⧸ I) (E.X i))
    (hErep : Nonempty ((DerivedCategory.Q).obj E ≅ D.functor.obj K))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hI : ∀ x : R, x ∈ I → IsUnit (1 + x)) :
    ∃ P : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, Module.Finite R (P.X i) ∧ Module.IsStablyFree R (P.X i)) ∧
      (∃ b, P.IsStrictlyLE b) ∧
      ∃ _ : ((ModuleCat.extendScalars.{u, u, max v u}
          (Ideal.Quotient.mk I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ E,
        Nonempty ((DerivedCategory.Q).obj P ≅ K) ∧
          ∀ i, Module.Free (R ⧸ I) (E.X i) → Module.Free R (P.X i) := by
  classical
  let Pcls : ModuleCat.{max v u} R → Prop := fun M =>
    Module.Finite R M ∧ Module.IsStablyFree R M
  obtain ⟨KC, hKC, hKCiso⟩ := hK
  have hKrep : ∃ KC : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, Pcls (KC.X i)) ∧ (∃ b, KC.IsStrictlyLE b) ∧
        Nonempty ((DerivedCategory.Q).obj KC ≅ K) := by
    refine ⟨KC, fun i => ?_, hKC.upperBound, hKCiso⟩
    let := (hKC.finiteFree i).2
    exact ⟨(hKC.finiteFree i).1, inferInstance⟩
  obtain ⟨P, hPterms, hPbdd, ⟨eRed⟩, ⟨eK⟩⟩ :=
    exists_boundedAbove_lift_representing_of_datum.{u, v} I D Pcls K E
      (fun M hM => by let := hM.2; infer_instance)
      (fun M₁ M₂ => finite_isStablyFree_biprod_iff.{u, v} M₁ M₂)
      (fun M₁ M₂ f _ hM₂ hf => by
        let := hM₂.1
        exact surjective_of_surjective_extendScalars.{u, v} I hI f hf)
      hEbdd
      (fun i => by
        let := (hEterms i).1
        let := (hEterms i).2
        obtain ⟨M, hMfin, hMstable, ⟨e⟩⟩ :=
          exists_isStablyFree_lift.{u, max v u} I hI (E := E.X i)
        exact ⟨M, ⟨hMfin, hMstable⟩,
          ⟨(e.symm.trans (quotTensorEquiv.{u, v} I M).symm).toModuleIso⟩⟩)
      hErep hKrep
  refine ⟨P, hPterms, hPbdd, eRed, ⟨eK⟩, fun i hEfree => ?_⟩
  let := (hPterms i).1
  let := (hPterms i).2
  let : Module.Projective R (P.X i) := inferInstance
  let := (hEterms i).1
  let : Module.Free (R ⧸ I) (E.X i) := hEfree
  by_cases hq : Nontrivial (R ⧸ I)
  · let : Nontrivial (R ⧸ I) := hq
    let ι := Module.Free.ChooseBasisIndex (R ⧸ I) (E.X i)
    let bE := Module.Free.chooseBasis (R ⧸ I) (E.X i)
    let : Finite ι := Module.Finite.finite_basis bE
    let Fr := ModuleCat.of R (ι →₀ R)
    let : Module.Finite R Fr := inferInstance
    let : Module.Free R Fr := inferInstance
    let : Module.Projective R Fr := Module.Projective.of_free
    let ei := ((HomologicalComplex.eval _ _ i).mapIso eRed).toLinearEquiv
    let bR := Finsupp.basisSingleOne (R := R) (ι := ι)
    let eF : ((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj Fr) ≃ₗ[R ⧸ I]
        E.X i :=
      (Algebra.TensorProduct.equivFinsuppOfBasis (R ⧸ I) bR).trans bE.repr.symm
    have hquot : Nonempty ((P.X i ⧸ I • (⊤ : Submodule R (P.X i))) ≃ₗ[R]
        (Fr ⧸ I • (⊤ : Submodule R Fr))) :=
      ⟨(((quotTensorEquiv.{u, v} I (P.X i)).symm.trans ei).trans
        (eF.symm.trans (quotTensorEquiv.{u, v} I Fr))).restrictScalars R⟩
    obtain ⟨ePF⟩ := quot_iso_lift I hI hquot
    exact Module.Free.of_equiv ePF.symm
  · have hminus : (-1 : R) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact @Subsingleton.elim (R ⧸ I) (not_nontrivial_iff_subsingleton.mp hq) _ _
    have hzero : IsUnit (0 : R) := by simpa using hI (-1) hminus
    let : Subsingleton R := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hzero)
    exact Module.Free.of_subsingleton' R (P.X i)

/-! ### Zero-differential representatives over a field -/

/-- A complex whose homology is projective in every degree receives a quasi-isomorphism from the
complex of its own homology modules, taken with zero differentials. -/
public theorem exists_zero_differential_representative
    {C : Type*} [Category C] [Abelian C] (Dc : CochainComplex C ℤ)
    [∀ i, Projective (Dc.homology i)] :
    ∃ (E : CochainComplex C ℤ) (f : E ⟶ Dc),
      (∀ i j, E.d i j = 0) ∧ (∀ i, Nonempty (E.X i ≅ Dc.homology i)) ∧ QuasiIso f := by
  classical
  let E : CochainComplex C ℤ :=
    { X := fun i => Dc.homology i
      d := fun _ _ => 0
      shape := by intros; rfl
      d_comp_d' := by intros; simp }
  let s (i : ℤ) := Projective.factorThru (𝟙 (Dc.homology i)) (Dc.homologyπ i)
  have hs (i : ℤ) : s i ≫ Dc.homologyπ i = 𝟙 _ := Projective.factorThru_comp _ _
  let f : E ⟶ Dc :=
    { f := fun i => s i ≫ Dc.iCycles i
      comm' := by intros; dsimp [E]; simp }
  refine ⟨E, f, fun _ _ => rfl, fun _ => ⟨Iso.refl _⟩, ?_⟩
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hi : IsIso (E.iCycles i) := E.isIso_iCycles _ _ rfl rfl
  have hp : IsIso (E.homologyπ i) := E.isIso_homologyπ _ _ rfl rfl
  have hc : HomologicalComplex.cyclesMap f i = E.iCycles i ≫ s i := by
    apply (cancel_mono (Dc.iCycles i)).1
    simp [HomologicalComplex.cyclesMap_i, f]
  have he : E.homologyπ i ≫ HomologicalComplex.homologyMap f i = E.iCycles i := by
    rw [HomologicalComplex.homologyπ_naturality, hc, Category.assoc, hs, Category.comp_id]
  have : IsIso (E.homologyπ i ≫ HomologicalComplex.homologyMap f i) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left (E.homologyπ i) _

/-- Over a Noetherian ring, a complex with a finite term has finite homology in that degree. -/
private theorem finite_homology_of_finite_term {k : Type u} [Ring k] [IsNoetherianRing k]
    (Dc : CochainComplex (ModuleCat.{max v u} k) ℤ) (i : ℤ)
    (hfin : Module.Finite k (Dc.X i)) : Module.Finite k (Dc.homology i) := by
  let := hfin
  have : Module.Finite k (Dc.cycles i) :=
    Module.Finite.of_injective (Dc.iCycles i).hom
      (ModuleCat.mono_iff_injective _ |>.mp inferInstance)
  exact Module.Finite.of_surjective (Dc.homologyπ i).hom
    (ModuleCat.epi_iff_surjective _ |>.mp inferInstance)

/-- Over a field, a pseudo-coherent object has finite-dimensional cohomology in every degree, and
is represented by a bounded above complex with zero differentials whose terms are those
cohomology spaces. -/
private theorem field_representative {k : Type u} [Field k]
    (Kk : DerivedCategory (ModuleCat.{max v u} k))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent Kk) :
    (∀ i, Module.Finite k ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj Kk)) ∧
    ∃ (b : ℤ) (E : CochainComplex (ModuleCat.{max v u} k) ℤ),
      E.IsStrictlyLE b ∧ (∀ i j, E.d i j = 0) ∧
      (∀ i, Nonempty
        (E.X i ≅ (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj Kk)) ∧
      Nonempty (DerivedCategory.Q.obj E ≅ Kk) := by
  obtain ⟨Dc, hD, ⟨eD⟩⟩ := hK
  obtain ⟨b, hb⟩ := hD.upperBound
  let e (i : ℤ) : Dc.homology i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj Kk :=
    ((DerivedCategory.homologyFunctorFactors _ i).app Dc).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).mapIso eD
  have hfin (i : ℤ) : Module.Finite k (Dc.homology i) :=
    finite_homology_of_finite_term.{u, v} Dc i (hD.finiteFree i).1
  refine ⟨fun i => Module.Finite.equiv (e i).toLinearEquiv, ?_⟩
  have hproj (i : ℤ) : Projective (Dc.homology i) := by
    let := hfin i
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis k _)
  let := hproj
  obtain ⟨E, f, hz, hi, hf⟩ := exists_zero_differential_representative Dc
  let := hf
  refine ⟨b, E, (CochainComplex.isStrictlyLE_iff E b).2 ?_, hz,
    fun i => ⟨(hi i).some ≪≫ e i⟩, ⟨asIso (DerivedCategory.Q.map f) ≪≫ eD⟩⟩
  intro i hi'
  exact (HomologicalComplex.ExactAt.of_isZero
    (Dc.isZero_of_isStrictlyLE b i hi')).isZero_homology.of_iso (hi i).some

/-! ### Minimal free representatives over a local ring -/

/-- Over a local ring, every element of `1 + 𝔪` is a unit. -/
private theorem isUnit_one_add_of_mem_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R] :
    ∀ x : R, x ∈ IsLocalRing.maximalIdeal R → IsUnit (1 + x) := by
  intro x hx
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro h
  have hone : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    simpa using (IsLocalRing.maximalIdeal R).sub_mem h hx
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 hone)

set_option backward.isDefEq.respectTransparency false in
/-- Extension of scalars does not change the rank of a free module. -/
private theorem finrank_extendScalars {R A : Type u} [CommRing R] [CommRing A]
    [Nontrivial R] [Nontrivial A] (f : R →+* A) (M : ModuleCat.{max v u} R) [Module.Free R M] :
    Module.finrank A ((ModuleCat.extendScalars.{u, u, max v u} f).obj M) =
      Module.finrank R M := by
  let := f.toAlgebra
  exact Module.finrank_baseChange

/-- A finite free module is isomorphic to the standard free module on its rank. -/
private theorem finite_free_iso {R : Type u} [CommRing R] [Nontrivial R]
    (M : ModuleCat.{max v u} R) [Module.Finite R M] [Module.Free R M] :
    Nonempty (M ≅ ModuleCat.of R (ULift.{v} (Fin (Module.finrank R M) → R))) :=
  ⟨((Module.finBasis R M).equivFun.trans ULift.moduleEquiv.symm).toModuleIso⟩

/-- A homotopy equivalence onto a complex with zero differentials is a termwise isomorphism as
soon as the ranks agree, because its termwise components are split surjections. -/
private theorem isIso_homotopyEquiv_hom_f_of_zero_differentials {k : Type u} [Field k]
    {Fc E : CochainComplex (ModuleCat.{max v u} k) ℤ} (e : HomotopyEquiv Fc E)
    (hz : ∀ i j, E.d i j = 0) (i : ℤ)
    [Module.Finite k (Fc.X i)] [Module.Finite k (E.X i)]
    (hrank : Module.finrank k (Fc.X i) = Module.finrank k (E.X i)) :
    IsIso (e.hom.f i) := by
  have h : e.inv.f i ≫ e.hom.f i = 𝟙 _ := by
    simpa [dNext, prevD, hz] using e.homotopyInvHomId.comm i
  have hs : Function.Surjective (e.hom.f i).hom := by
    intro x
    exact ⟨e.inv.f i x, congrArg (fun g : E.X i ⟶ E.X i => g x) h⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hs, hs⟩

set_option backward.isDefEq.respectTransparency false in
/-- The general form of [stacks 0BCC], for an arbitrary total derived extension-of-scalars datum
`D` along the residue map of a local ring: let `K` be a pseudo-coherent object of the derived
category of a commutative local ring `R` with residue field `κ`. The cohomology of `D.functor.obj
K` is finite dimensional in every degree and vanishes above some degree `b`. Moreover `K` is
represented by a complex vanishing above `b` whose term in degree `i` is free of rank
`dim_κ Hⁱ(D.functor.obj K)`, and any two complexes with these prescribed terms representing `K`
are isomorphic as complexes.

The source statement, for the canonical datum, is
`StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing`. -/
theorem exists_unique_boundedAbove_free_complex_representing_of_datum
    {R : Type u} [CommRing R] [IsLocalRing R]
    (D : TotalDerivedExtensionScalars.{u, v, u} (IsLocalRing.residue R))
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    let k := IsLocalRing.ResidueField R
    let H := fun i : ℤ =>
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj (D.functor.obj K)
    let IsModel := fun P : CochainComplex (ModuleCat.{max v u} R) ℤ =>
      (∀ i, Nonempty (P.X i ≅
        ModuleCat.of R (ULift.{v} (Fin (Module.finrank k (H i)) → R)))) ∧
      Nonempty ((DerivedCategory.Q).obj P ≅ K)
    (∀ i, Module.Finite k (H i)) ∧
      ∃ b : ℤ, (∀ i, b < i → IsZero (H i)) ∧
        ∃ P : CochainComplex (ModuleCat.{max v u} R) ℤ,
          P.IsStrictlyLE b ∧ IsModel P ∧
            ∀ F G, IsModel F → IsModel G → Nonempty (F ≅ G) := by
  classical
  dsimp only
  let k := IsLocalRing.ResidueField R
  let H (i : ℤ) := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj
    (D.functor.obj K)
  obtain ⟨hHfin, b, E, hEb, hEd, hEH, ⟨hEK⟩⟩ :=
    field_representative.{u, v} (D.functor.obj K) (isPseudoCoherent_totalDerived.{u, v} D hK)
  have hEfin (i : ℤ) : Module.Finite k (E.X i) :=
    Module.Finite.equiv (hEH i).some.toLinearEquiv.symm
  have hI := isUnit_one_add_of_mem_maximalIdeal (R := R)
  obtain ⟨P, hPterms, ⟨c, hPc⟩, hPE, ⟨hPK⟩, hPfree⟩ :=
    exists_boundedAbove_isStablyFree_lift.{u, v} (IsLocalRing.maximalIdeal R) D K E ⟨b, hEb⟩
      (fun i => ⟨hEfin i, by
        let := hEfin i
        show Module.IsStablyFree k (E.X i)
        infer_instance⟩) ⟨hEK⟩ hK hI
  have hPfin (i : ℤ) : Module.Finite R (P.X i) := (hPterms i).1
  have hPfr (i : ℤ) : Module.Free R (P.X i) :=
    hPfree i (by change Module.Free k (E.X i); infer_instance)
  let := hPfin
  let := hPfr
  let red := ModuleCat.extendScalars.{u, u, max v u} (IsLocalRing.residue R)
  let redC := red.mapHomologicalComplex (ComplexShape.up ℤ)
  have hPrank (i : ℤ) : Module.finrank R (P.X i) = Module.finrank k (H i) := by
    rw [← finrank_extendScalars.{u, v} (IsLocalRing.residue R) (P.X i)]
    exact ((HomologicalComplex.eval (ModuleCat.{max v u} k) _ i).mapIso hPE ≪≫
      (hEH i).some).toLinearEquiv.finrank_eq
  have hPiso (i : ℤ) : Nonempty (P.X i ≅
      ModuleCat.of R (ULift.{v} (Fin (Module.finrank k (H i)) → R))) := by
    rw [← hPrank i]
    exact finite_free_iso.{u, v} (P.X i)
  refine ⟨hHfin, max b c, ?_, P,
    CochainComplex.isStrictlyLE_of_le P c (max b c) (le_max_right _ _),
    ⟨hPiso, ⟨hPK⟩⟩, ?_⟩
  · intro i hi
    exact (E.isZero_of_isStrictlyLE b i (lt_of_le_of_lt (le_max_left _ _) hi)).of_iso
      (hEH i).some.symm
  · have hcompare : ∀ Fc : CochainComplex (ModuleCat.{max v u} R) ℤ,
        (∀ i, Nonempty (Fc.X i ≅
          ModuleCat.of R (ULift.{v} (Fin (Module.finrank k (H i)) → R)))) →
        Nonempty (DerivedCategory.Q.obj Fc ≅ K) → Nonempty (Fc ≅ P) := by
      intro Fc hFiso hFKn
      obtain ⟨hFK⟩ := hFKn
      let eFP (i : ℤ) : Fc.X i ≅ P.X i := (hFiso i).some ≪≫ (hPiso i).some.symm
      have hFfin (i : ℤ) : Module.Finite R (Fc.X i) :=
        Module.Finite.equiv (eFP i).symm.toLinearEquiv
      have hFfr (i : ℤ) : Module.Free R (Fc.X i) :=
        Module.Free.of_equiv (eFP i).symm.toLinearEquiv
      let := hFfin
      let := hFfr
      have hFLE : Fc.IsStrictlyLE c := (CochainComplex.isStrictlyLE_iff Fc c).2
        (fun i hi => (P.isZero_of_isStrictlyLE c i hi).of_iso (eFP i))
      let := hFLE
      have hKproj (X : CochainComplex (ModuleCat.{max v u} R) ℤ) [∀ i, Module.Free R (X.X i)]
          [X.IsStrictlyLE c] : X.IsKProjective :=
        have (i : ℤ) : Projective (X.X i) :=
          ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
        CochainComplex.isKProjective_of_projective X c
      let := hKproj Fc
      let := hKproj P
      obtain ⟨e⟩ := homotopyEquivOfDerivedIso.{u, v} Fc P (hFK ≪≫ hPK.symm)
      let er : HomotopyEquiv (redC.obj Fc) E :=
        (red.mapHomotopyEquiv e).trans (HomotopyEquiv.ofIso hPE)
      have hiso (i : ℤ) : IsIso (e.hom.f i) := by
        have hredfin : Module.Finite k ((redC.obj Fc).X i) :=
          finite_extendScalars.{u, v} (IsLocalRing.residue R) (Fc.X i) (hFfin i)
        let := hredfin
        let := hEfin i
        have hrank : Module.finrank k ((redC.obj Fc).X i) = Module.finrank k (E.X i) := by
          show Module.finrank k (red.obj (Fc.X i)) = _
          rw [finrank_extendScalars.{u, v} (IsLocalRing.residue R) (Fc.X i),
            (eFP i).toLinearEquiv.finrank_eq, hPrank i]
          exact (hEH i).some.toLinearEquiv.finrank_eq.symm
        have heiso := isIso_homotopyEquiv_hom_f_of_zero_differentials.{u, v} er hEd i hrank
        let ePi : red.obj (P.X i) ≅ E.X i := HomologicalComplex.Hom.isoApp hPE i
        have h₁ : IsIso (red.map (e.hom.f i) ≫ ePi.hom) := heiso
        have h₂ : IsIso (red.map (e.hom.f i)) := IsIso.of_isIso_comp_right _ ePi.hom
        have h₃ : IsIso ((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal R))).map (e.hom.f i)) := h₂
        let := h₃
        let : Module.Projective R (Fc.X i) := Module.Projective.of_free
        let : Module.Projective R (P.X i) := Module.Projective.of_free
        exact isIso_of_isIso_reduction.{u, v} (IsLocalRing.maximalIdeal R) hI (e.hom.f i)
      let := hiso
      have : IsIso e.hom := HomologicalComplex.Hom.isIso_of_components e.hom
      exact ⟨asIso e.hom⟩
    intro Fc G hF hG
    exact ⟨(hcompare Fc hF.1 hF.2).some ≪≫ (hcompare G hG.1 hG.2).some.symm⟩

/-- **Stacks 0BCC.** Let `K` be a pseudo-coherent object of the derived category of a commutative
local ring `R` with residue field `κ`. Its cohomology after derived extension of scalars to `κ` is
finite dimensional in every degree and vanishes above some degree `b`. Moreover `K` is represented
by a complex vanishing above `b` whose term in degree `i` is free of rank
`dim_κ Hⁱ(K ⊗ᴸ_R κ)`, and any two complexes with these prescribed terms representing `K` are
isomorphic as complexes. -/
@[stacks 0BCC]
theorem exists_unique_boundedAbove_free_complex_representing
    {R : Type u} [CommRing R] [IsLocalRing R]
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    let k := IsLocalRing.ResidueField R
    let H := fun i : ℤ =>
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj
        ((totalDerivedExtensionScalars.{u, u, v} (IsLocalRing.residue R)).functor.obj K)
    let IsModel := fun P : CochainComplex (ModuleCat.{max v u} R) ℤ =>
      (∀ i, Nonempty (P.X i ≅
        ModuleCat.of R (ULift.{v} (Fin (Module.finrank k (H i)) → R)))) ∧
      Nonempty ((DerivedCategory.Q).obj P ≅ K)
    (∀ i, Module.Finite k (H i)) ∧
      ∃ b : ℤ, (∀ i, b < i → IsZero (H i)) ∧
        ∃ P : CochainComplex (ModuleCat.{max v u} R) ℤ,
          P.IsStrictlyLE b ∧ IsModel P ∧
            ∀ F G, IsModel F → IsModel G → Nonempty (F ≅ G) :=
  exists_unique_boundedAbove_free_complex_representing_of_datum.{u, v}
    (totalDerivedExtensionScalars.{u, u, v} (IsLocalRing.residue R)) K hK

end StacksDraft.Perfect
