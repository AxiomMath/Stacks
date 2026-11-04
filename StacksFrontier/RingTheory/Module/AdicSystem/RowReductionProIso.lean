module

public import StacksFrontier.RingTheory.Module.AdicSystem.RowReductionHomology
public import StacksFrontier.Homology.DerivedComplete.NoetherianKoszulProIso

/-!
# Reductions of a complex with torsion cohomology form a pro-constant system

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `P` a complex of finite `A`-modules whose
cohomology is annihilated by a power `Iᵗ`. Then the reductions `P → P/IⁿP` are an isomorphism
of pro-objects from the constant system `P`. On cohomology this is the Artin–Rees lemma: a
cycle lying in `IⁿP` lies in `Iⁿ⁻ᶜ` times the cycles, hence is a boundary for `n` large, so the
maps `Hⁱ(P) → Hⁱ(P/IⁿP)` are eventually injective; and a class of `Hⁱ(P/IᵐP)` is represented
by `x` with `dx ∈ IᵐP ∩ dP ⊆ d(IⁿP)` for `m` large, so modulo `Iⁿ` it comes from a cycle.

## Main results

* `Stacks.PseudoCoherent.AdicCompletion.exists_concreteHomologyIdealTransition_proInverse`:
  the cohomological statement, in the concrete presentation of the cohomology of reductions.
* `Stacks.PseudoCoherent.AdicCompletion.exists_proInverse_rowComplexMapRight_mkQ`: for a bounded
  complex `P` of finite modules with `Iᵗ`-torsion cohomology, the maps
  `P ⊗_A A → P ⊗_A A/Iⁿ` are a pro-isomorphism in `D(A)` from the constant system; this is
  deduced from the cohomological statement by [Stacks, Tag 0G3D].

## References

* [Stacks Project, Tag 0G3D](https://stacks.math.columbia.edu/tag/0G3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory LiftAcyclic CochainComplex.KFlatBifunctor
open scoped TensorProduct

universe u

namespace Stacks.PseudoCoherent.AdicCompletion

open Stacks.AdicSystem.DerivedReductionProIso

variable {A : Type u} [CommRing A]

/-- The ideal transitions of the concrete cohomology of reductions compose. -/
theorem concreteHomologyIdealTransition_comp {J K L : Ideal A} (hJK : J ≤ K) (hKL : K ≤ L)
    {L₁ L₂ L₃ : ModuleCat.{u} A} (α : L₁ ⟶ L₂) (β : L₂ ⟶ L₃) (h : α ≫ β = 0) :
    concreteHomologyIdealTransition hKL α β h ∘ₗ concreteHomologyIdealTransition hJK α β h =
      concreteHomologyIdealTransition (hJK.trans hKL) α β h := by
  ext x
  rfl

/-- The reduction from the zero ideal to `J` is injective on concrete cohomology as soon as the
cycles lying in `J • L₂` are boundaries. -/
theorem injective_concreteHomologyIdealTransition_bot {J : Ideal A}
    {L₁ L₂ L₃ : ModuleCat.{u} A} (α : L₁ ⟶ L₂) (β : L₂ ⟶ L₃) (h : α ≫ β = 0)
    (hJ : J • (⊤ : Submodule A L₂) ⊓ LinearMap.ker β.hom ≤ LinearMap.range α.hom) :
    Function.Injective (concreteHomologyIdealTransition (bot_le : ⊥ ≤ J) α β h) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H x =>
  rw [LinearMap.mem_ker, concreteHomologyIdealTransition_mk,
    Submodule.Quotient.mk_eq_zero] at hq
  rw [Submodule.Quotient.mk_eq_zero]
  change (x : L₂) ∈ LinearMap.range α.hom ⊔ (⊥ : Ideal A) • ⊤
  change (x : L₂) ∈ LinearMap.range α.hom ⊔ J • ⊤ at hq
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hq
  have hx0 : β.hom (x : L₂) = 0 := by simpa [Submodule.mem_comap] using x.2
  have hβz : β.hom z = 0 := by
    obtain ⟨w, rfl⟩ := hy
    have hαβ : β.hom (α.hom w) = 0 := by simpa using congrArg (fun φ ↦ φ.hom w) h
    rwa [← hyz, map_add, hαβ, zero_add] at hx0
  rw [← hyz]
  exact Submodule.mem_sup_left (Submodule.add_mem _ hy (hJ ⟨hz, hβz⟩))

/-- If `J • L₃ ∩ β(L₂) ⊆ β(K • L₂)`, then every class in the image of the transition from `J` to
`K` on concrete cohomology comes from the cohomology itself. -/
theorem range_concreteHomologyIdealTransition_le_range_bot {J K : Ideal A} (hJK : J ≤ K)
    {L₁ L₂ L₃ : ModuleCat.{u} A} (α : L₁ ⟶ L₂) (β : L₂ ⟶ L₃) (h : α ≫ β = 0)
    (hc : J • (⊤ : Submodule A L₃) ⊓ LinearMap.range β.hom ≤ Submodule.map β.hom (K • ⊤)) :
    LinearMap.range (concreteHomologyIdealTransition hJK α β h) ≤
      LinearMap.range (concreteHomologyIdealTransition (bot_le : ⊥ ≤ K) α β h) := by
  intro q hq
  obtain ⟨q', rfl⟩ := hq
  induction q' using Submodule.Quotient.induction_on with
  | H x =>
  have hβx : β.hom (x : L₂) ∈ J • (⊤ : Submodule A L₃) ⊓ LinearMap.range β.hom :=
    ⟨x.2, ⟨x, rfl⟩⟩
  obtain ⟨y, hy, hxy⟩ := hc hβx
  have hcyc : (x : L₂) - y ∈ ((⊥ : Ideal A) • (⊤ : Submodule A L₃)).comap β.hom := by
    simp [map_sub, hxy]
  refine ⟨Submodule.Quotient.mk ⟨_, hcyc⟩, ?_⟩
  rw [concreteHomologyIdealTransition_mk, concreteHomologyIdealTransition_mk]
  apply (Submodule.Quotient.eq _).mpr
  change ((x : L₂) - y) - x ∈ LinearMap.range α.hom ⊔ K • ⊤
  rw [sub_sub_cancel_left]
  exact Submodule.mem_sup_right (Submodule.neg_mem _ hy)

/-- **Artin–Rees for the concrete cohomology of reductions.** Let `L₁ → L₂ → L₃` be a complex of
finite modules over a Noetherian ring whose cohomology is killed by `Iᵗ`. For every `n` there are
`m ≥ n` and a map from the cohomology of the reduction modulo `Iᵐ` to the cohomology itself,
inverse to the reduction map up to the transition maps. -/
theorem exists_concreteHomologyIdealTransition_proInverse [IsNoetherianRing A] (I : Ideal A)
    {L₁ L₂ L₃ : ModuleCat.{u} A} [Module.Finite A L₂] [Module.Finite A L₃]
    (α : L₁ ⟶ L₂) (β : L₂ ⟶ L₃) (h : α ≫ β = 0) (t : ℕ)
    (ht : I ^ t • LinearMap.ker β.hom ≤ LinearMap.range α.hom) (n : ℕ) :
    ∃ (m : ℕ) (hnm : n ≤ m) (s : _ →ₗ[A] _),
      s ∘ₗ concreteHomologyIdealTransition (bot_le : ⊥ ≤ I ^ m) α β h = LinearMap.id ∧
        concreteHomologyIdealTransition (bot_le : ⊥ ≤ I ^ n) α β h ∘ₗ s =
          concreteHomologyIdealTransition (Ideal.pow_le_pow_right hnm) α β h := by
  obtain ⟨k, hk⟩ := NoetherianKoszulProIso.artinRees_cycles_bound (I ^ t)
    (LinearMap.ker β.hom) (LinearMap.range α.hom) ht
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range β.hom)
  let p := max n (t * k)
  have hp : Function.Injective
      (concreteHomologyIdealTransition (bot_le : ⊥ ≤ I ^ p) α β h) :=
    injective_concreteHomologyIdealTransition_bot α β h fun z hz ↦ by
      refine hk ⟨?_, hz.2⟩
      rw [← pow_mul]
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right _ _)) hz.1
  have hrange := range_concreteHomologyIdealTransition_le_range_bot
    (Ideal.pow_le_pow_right (I := I) (Nat.le_add_right p c)) α β h (by
      rw [hc (p + c) (Nat.le_add_left c p), Nat.add_sub_cancel, Submodule.map_smul'',
        Submodule.map_top]
      exact smul_mono_right _ inf_le_right)
  let v := concreteHomologyIdealTransition (bot_le : ⊥ ≤ I ^ p) α β h
  let u := concreteHomologyIdealTransition
    (Ideal.pow_le_pow_right (I := I) (Nat.le_add_right p c)) α β h
  let s := (LinearEquiv.ofInjective v hp).symm.toLinearMap ∘ₗ u.codRestrict (LinearMap.range v)
    (fun q ↦ hrange ⟨q, rfl⟩)
  have hvs : v ∘ₗ s = u := by
    refine LinearMap.ext fun q ↦ ?_
    change v ((LinearEquiv.ofInjective v hp).symm (u.codRestrict (LinearMap.range v) _ q)) = u q
    rw [← LinearEquiv.ofInjective_apply (h := hp), LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨p + c, (le_max_left _ _).trans (Nat.le_add_right p c), s, ?_, ?_⟩
  · refine LinearMap.ext fun q ↦ hp ?_
    change v (s (concreteHomologyIdealTransition (bot_le : ⊥ ≤ I ^ (p + c)) α β h q)) = v q
    rw [← LinearMap.comp_apply v s, hvs]
    change (u ∘ₗ concreteHomologyIdealTransition (bot_le : ⊥ ≤ I ^ (p + c)) α β h) q = v q
    rw [concreteHomologyIdealTransition_comp]
  · have hpn : n ≤ p := le_max_left _ _
    rw [← concreteHomologyIdealTransition_comp (bot_le : ⊥ ≤ I ^ p)
      (Ideal.pow_le_pow_right (I := I) hpn), LinearMap.comp_assoc]
    change concreteHomologyIdealTransition (Ideal.pow_le_pow_right (I := I) hpn) α β h ∘ₗ
      (v ∘ₗ s) = _
    rw [hvs, concreteHomologyIdealTransition_comp]

/-- `N ⊗_A A ≅ N/0`. -/
def tensorBotQuotientEquiv (N : ModuleCat.{u} A) :
    N ⊗[A] A ≃ₗ[A] N ⧸ ((⊥ : Ideal A) • ⊤ : Submodule A N) :=
  (TensorProduct.rid A N).trans (Submodule.quotEquivOfEqBot _ (Submodule.bot_smul _)).symm

/-- `tensorBotQuotientEquiv` sends `x ⊗ r` to the class of `r • x`. -/
theorem tensorBotQuotientEquiv_tmul (N : ModuleCat.{u} A) (x : N) (r : A) :
    tensorBotQuotientEquiv N (x ⊗ₜ[A] r) = Submodule.Quotient.mk (r • x) :=
  rfl

/-- The termwise tensor product `P ⊗_A A` is the reduction of `P` modulo the zero ideal. -/
def rowComplexUnitBotIso (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    rowComplex (curriedTensor (ModuleCat.{u} A)) P (ModuleCat.of A A) ≅
      (reduceComplex (⊥ : Ideal A)).obj P :=
  HomologicalComplex.Hom.isoOfComponents (fun p => (tensorBotQuotientEquiv (P.X p)).toModuleIso)
    (fun p q _ => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x r
      change ((redFunctor (⊥ : Ideal A)).map (P.d p q)).hom
          (tensorBotQuotientEquiv (P.X p) (x ⊗ₜ[A] r)) =
        tensorBotQuotientEquiv (P.X q) ((P.d p q).hom x ⊗ₜ[A] r)
      rw [tensorBotQuotientEquiv_tmul, tensorBotQuotientEquiv_tmul]
      exact congrArg Submodule.Quotient.mk (map_smul (P.d p q).hom r x))

/-- The quotient map `A → A/Iⁿ`, with target the `n`-th term of the adic quotient tower. -/
abbrev adicQuotientMkQ (I : Ideal A) (n : ℕ) :
    ModuleCat.of A A ⟶
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).obj
        (Opposite.op n) :=
  ModuleCat.ofHom (I ^ n • (⊤ : Submodule A A)).mkQ

/-- The reductions `P ⊗_A A → P ⊗_A A/Iⁿ` are the reductions `P/0 → P/IⁿP`. -/
theorem rowComplexMapRight_mkQ_comp_rowComplexAdicQuotientIso (I : Ideal A) (n : ℕ)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    rowComplexMapRight (curriedTensor (ModuleCat.{u} A)) P
        (adicQuotientMkQ I n) ≫ (rowComplexAdicQuotientIso I n P).hom =
      (rowComplexUnitBotIso P).hom ≫
        (NatTrans.mapHomologicalComplex (reductionNatTrans (bot_le : ⊥ ≤ I ^ n))
          (ComplexShape.up ℤ)).app P := by
  ext p : 2
  apply TensorProduct.ext'
  intro x r
  change tensorAdicQuotientEquiv (P.X p) (I ^ n) (x ⊗ₜ[A] Submodule.Quotient.mk r) =
    ((reductionNatTrans (bot_le : ⊥ ≤ I ^ n)).app (P.X p)).hom
      (tensorBotQuotientEquiv (P.X p) (x ⊗ₜ[A] r))
  rw [tensorAdicQuotientEquiv_tmul, tensorBotQuotientEquiv_tmul]
  rfl

/-- The transition maps of the concrete system of cohomology of the adic reductions. -/
theorem adicReductionHomologySystem_map (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) {n m : ℕ} (h : n ≤ m) :
    (adicReductionHomologySystem I P i).map (homOfLE h).op =
      ModuleCat.ofHom (concreteHomologyIdealTransition (Ideal.pow_le_pow_right h)
        (P.sc i).f (P.sc i).g (P.sc i).zero) := by
  refine NoetherianAdicCompletion.ofOpSequence_map_eq _
    (fun m n h ↦ ModuleCat.ofHom (concreteHomologyIdealTransition (Ideal.pow_le_pow_right h)
      (P.sc i).f (P.sc i).g (P.sc i).zero)) (fun n ↦ ?_) (fun m n h ↦ ?_) m n h <;>
  · ext x
    rfl

variable [HasDerivedCategory (ModuleCat.{u} A)]

/-- `reducedHomologyConcreteEquiv` as an isomorphism out of the cohomology functor. -/
def reducedHomologyConcreteIso (J : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i).obj
        ((reduceComplex J).obj P) ≅
      ModuleCat.of A (((J • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom) ⧸
        (LinearMap.range (P.sc i).f.hom ⊔ J • (⊤ : Submodule A (P.sc i).X₂)).comap
          ((J • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom).subtype) :=
  (reducedHomologyConcreteEquiv J P i).symm.toModuleIso

omit [HasDerivedCategory (ModuleCat.{u} A)] in
/-- For `J ≤ K`, the map `Hⁱ(P/JP) → Hⁱ(P/KP)` induced by the reduction is, in the concrete
presentations of `reducedHomologyConcreteIso`, the map `concreteHomologyIdealTransition`. -/
theorem homologyFunctor_map_reductionNatTrans_comp_reducedHomologyConcreteIso {J K : Ideal A}
    (hJK : J ≤ K) (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i).map
        ((NatTrans.mapHomologicalComplex (reductionNatTrans hJK) (ComplexShape.up ℤ)).app P) ≫
        (reducedHomologyConcreteIso K P i).hom =
      (reducedHomologyConcreteIso J P i).hom ≫ ModuleCat.ofHom
        (concreteHomologyIdealTransition hJK (P.sc i).f (P.sc i).g (P.sc i).zero) :=
  homologyMap_reductionNatTrans_comp_concreteEquiv_symm hJK P i

/-- The cohomology of `P ⊗_A A/Iⁿ` in the derived category, in its concrete presentation. -/
def derivedAdicQuotientRowHomologyHom (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) (n : ℕ) :
    (DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj
        (rowComplex (curriedTensor (ModuleCat.{u} A)) P
          ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).obj
            (Opposite.op n)))) ⟶
      ModuleCat.of A ((((I ^ n) • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom) ⧸
        (LinearMap.range (P.sc i).f.hom ⊔ (I ^ n) • (⊤ : Submodule A (P.sc i).X₂)).comap
          (((I ^ n) • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom).subtype) :=
  (DerivedCategory.homologyFunctorFactors _ i).hom.app _ ≫
    (HomologicalComplex.homologyFunctor _ _ i).map (rowComplexAdicQuotientIso I n P).hom ≫
      (reducedHomologyConcreteIso (I ^ n) P i).hom

/-- `derivedAdicQuotientRowHomologyHom` is an isomorphism. -/
instance isIso_derivedAdicQuotientRowHomologyHom (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) (n : ℕ) :
    IsIso (derivedAdicQuotientRowHomologyHom I P i n) := by
  unfold derivedAdicQuotientRowHomologyHom
  infer_instance

/-- The cohomology of `P ⊗_A A` in the derived category, in its concrete presentation. -/
def derivedRowHomologyBotHom (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj
        (rowComplex (curriedTensor (ModuleCat.{u} A)) P (ModuleCat.of A A))) ⟶
      ModuleCat.of A ((((⊥ : Ideal A) • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom) ⧸
        (LinearMap.range (P.sc i).f.hom ⊔ (⊥ : Ideal A) • (⊤ : Submodule A (P.sc i).X₂)).comap
          (((⊥ : Ideal A) • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom).subtype) :=
  (DerivedCategory.homologyFunctorFactors _ i).hom.app _ ≫
    (HomologicalComplex.homologyFunctor _ _ i).map (rowComplexUnitBotIso P).hom ≫
      (reducedHomologyConcreteIso ⊥ P i).hom

/-- `derivedRowHomologyBotHom` is an isomorphism. -/
instance isIso_derivedRowHomologyBotHom (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    IsIso (derivedRowHomologyBotHom P i) := by
  unfold derivedRowHomologyBotHom
  infer_instance

/-- A square of complexes comparing with the reductions `P/JP → P/KP` gives, on cohomology in
`D(A)` and in the concrete presentations, the map `concreteHomologyIdealTransition`. -/
private theorem homologyFunctor_map_Q_map_comp_eq_transition {J K : Ideal A} (hJK : J ≤ K)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) {X Y : CochainComplex (ModuleCat.{u} A) ℤ}
    (φ : X ⟶ Y) (eX : X ⟶ (reduceComplex J).obj P) (eY : Y ⟶ (reduceComplex K).obj P)
    (hsq : φ ≫ eY =
      eX ≫ (NatTrans.mapHomologicalComplex (reductionNatTrans hJK) (ComplexShape.up ℤ)).app P) :
    (DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map φ) ≫
        ((DerivedCategory.homologyFunctorFactors _ i).hom.app Y ≫
          (HomologicalComplex.homologyFunctor _ _ i).map eY ≫
            (reducedHomologyConcreteIso K P i).hom) =
      ((DerivedCategory.homologyFunctorFactors _ i).hom.app X ≫
          (HomologicalComplex.homologyFunctor _ _ i).map eX ≫
            (reducedHomologyConcreteIso J P i).hom) ≫ ModuleCat.ofHom
        (concreteHomologyIdealTransition hJK (P.sc i).f (P.sc i).g (P.sc i).zero) := by
  have hn := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).hom.naturality φ
  simp only [Functor.comp_map] at hn
  have hsq' := congrArg (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) _ i).map hsq
  simp only [Functor.map_comp] at hsq'
  rw [reassoc_of% hn, Category.assoc, Category.assoc, cancel_epi, reassoc_of% hsq']
  exact (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·)
      (homologyFunctor_map_reductionNatTrans_comp_reducedHomologyConcreteIso _ P i)))

/-- On cohomology in `D(A)`, the reduction `P ⊗_A A → P ⊗_A A/Iⁿ` is, in the concrete
presentations, the map `concreteHomologyIdealTransition` from the zero ideal to `Iⁿ`. -/
theorem homologyFunctor_map_rowComplexMapRight_mkQ (I : Ideal A) (n : ℕ)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map
        (rowComplexMapRight (curriedTensor (ModuleCat.{u} A)) P
          (adicQuotientMkQ I n))) ≫
        derivedAdicQuotientRowHomologyHom I P i n =
      derivedRowHomologyBotHom P i ≫ ModuleCat.ofHom (concreteHomologyIdealTransition
        (bot_le : ⊥ ≤ I ^ n) (P.sc i).f (P.sc i).g (P.sc i).zero) :=
  homologyFunctor_map_Q_map_comp_eq_transition _ P i _ _ _
    (rowComplexMapRight_mkQ_comp_rowComplexAdicQuotientIso I n P)

/-- For `n ≤ m`, the transition `P ⊗_A A/Iᵐ → P ⊗_A A/Iⁿ` is, on cohomology in `D(A)` and in the
concrete presentations, the map `concreteHomologyIdealTransition` from `Iᵐ` to `Iⁿ`. -/
theorem derivedAdicQuotientRowHomologyHom_naturality (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) {n m : ℕ} (h : n ≤ m) :
    (DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map
        (rowComplexMapRight (curriedTensor (ModuleCat.{u} A)) P
          ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).map
            (homOfLE h).op))) ≫ derivedAdicQuotientRowHomologyHom I P i n =
      derivedAdicQuotientRowHomologyHom I P i m ≫ ModuleCat.ofHom
        (concreteHomologyIdealTransition (Ideal.pow_le_pow_right h) (P.sc i).f (P.sc i).g
          (P.sc i).zero) :=
  homologyFunctor_map_Q_map_comp_eq_transition _ P i _ _ _
    (rowComplexAdicQuotientIso_naturality I h P)

/-- The derived cohomology of `P ⊗_A M` vanishes outside the range `[a, b]` of `P`. -/
theorem isZero_homology_rowComplex_of_lt_or_lt (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b] (M : ModuleCat.{u} A) {i : ℤ}
    (hi : i < a ∨ b < i) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (DerivedCategory.Q.obj (rowComplex (curriedTensor (ModuleCat.{u} A)) P M))) := by
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ i).app _)
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
  change IsZero ((tensorRight M).obj (P.X i))
  rcases hi with hi | hi
  · exact (tensorRight M).map_isZero (P.isZero_of_isStrictlyGE a i hi)
  · exact (tensorRight M).map_isZero (P.isZero_of_isStrictlyLE b i hi)

/-- **The reductions of a complex with `I`-power torsion cohomology are pro-constant.** Let `P`
be a bounded complex of finite modules over a Noetherian ring whose cohomology is killed by
`Iᵗ`. Then the reductions `P ⊗_A A → P ⊗_A A/Iⁿ` are an isomorphism of pro-objects of `D(A)`
from the constant system: for every `n` there are `m ≥ n` and a map back from level `m`
inverse to the reductions up to the transition maps. -/
theorem exists_proInverse_rowComplexMapRight_mkQ [IsNoetherianRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : ∀ i, Module.Finite A (P.X i)) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (t : ℕ)
    (ht : ∀ i, I ^ t ≤ Module.annihilator A (P.homology i)) (n : ℕ) :
    ∃ (m : ℕ) (hnm : n ≤ m) (s : DerivedCategory.Q.obj
        (rowComplex (curriedTensor (ModuleCat.{u} A)) P
          ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).obj
            (Opposite.op m))) ⟶
        DerivedCategory.Q.obj (rowComplex (curriedTensor (ModuleCat.{u} A)) P (ModuleCat.of A A))),
      DerivedCategory.Q.map (rowComplexMapRight (curriedTensor (ModuleCat.{u} A)) P
          (adicQuotientMkQ I m)) ≫ s = 𝟙 _ ∧
        s ≫ DerivedCategory.Q.map (rowComplexMapRight (curriedTensor (ModuleCat.{u} A)) P
          (adicQuotientMkQ I n)) =
          DerivedCategory.Q.map (rowComplexMapRight (curriedTensor (ModuleCat.{u} A)) P
            ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).map
              (homOfLE hnm).op)) := by
  let Ψ := rowFunctor (curriedTensor (ModuleCat.{u} A)) P ⋙ DerivedCategory.Q
  let T := AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)
  let α : (Functor.const ℕᵒᵖ).obj (Ψ.obj (ModuleCat.of A A)) ⟶ T ⋙ Ψ :=
    NatTrans.ofOpSequence (fun n ↦ Ψ.map (adicQuotientMkQ I n))
      (fun n ↦ by
        have hmk : adicQuotientMkQ I n =
            adicQuotientMkQ I (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op := by
          rw [show T.map (homOfLE (Nat.le_succ n)).op = _ from
            AlgebraicGeometry.ProEtale.adicQuotientModuleSystem_map I (ModuleCat.of A A)
              (Nat.le_succ n)]
          ext
          rfl
        exact (Category.id_comp _).trans ((congrArg Ψ.map hmk).trans (Ψ.map_comp _ _)))
  obtain ⟨k, f, s, hs₁, hs₂⟩ := DerivedCategory.exists_proInverse_of_proInverse_homology α a b
    (fun i hi _ ↦ isZero_homology_rowComplex_of_lt_or_lt P a b _ hi)
    (fun i hi j ↦ isZero_homology_rowComplex_of_lt_or_lt P a b _ hi) (fun i j ↦ by
      have : Module.Finite A (P.sc i).X₂ := hP i
      have : Module.Finite A (P.sc i).X₃ := hP _
      obtain ⟨m, hnm, sc, hsc₁, hsc₂⟩ := exists_concreteHomologyIdealTransition_proInverse I
        (P.sc i).f (P.sc i).g (P.sc i).zero t
        (NoetherianKoszulProIso.ideal_smul_ker_le_range_of_annihilator (P.sc i) (I ^ t) (ht i))
        j.unop
      let eB : ∀ m : ℕ, (DerivedCategory.homologyFunctor _ i).obj ((T ⋙ Ψ).obj (Opposite.op m)) ⟶
          ModuleCat.of A ((((I ^ m) • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom) ⧸
            (LinearMap.range (P.sc i).f.hom ⊔ (I ^ m) • (⊤ : Submodule A (P.sc i).X₂)).comap
              (((I ^ m) • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom).subtype) :=
        fun m ↦ derivedAdicQuotientRowHomologyHom I P i m
      let eA : (DerivedCategory.homologyFunctor _ i).obj (Ψ.obj (ModuleCat.of A A)) ⟶
          ModuleCat.of A ((((⊥ : Ideal A) • (⊤ : Submodule A (P.sc i).X₃)).comap
              (P.sc i).g.hom) ⧸
            (LinearMap.range (P.sc i).f.hom ⊔
                (⊥ : Ideal A) • (⊤ : Submodule A (P.sc i).X₂)).comap
              (((⊥ : Ideal A) • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom).subtype) :=
        derivedRowHomologyBotHom P i
      have : IsIso eA := isIso_derivedRowHomologyBotHom P i
      have : ∀ m, IsIso (eB m) := fun m ↦ isIso_derivedAdicQuotientRowHomologyHom I P i m
      have hsq : ∀ m : ℕ, (DerivedCategory.homologyFunctor _ i).map (α.app (Opposite.op m)) ≫
          eB m = eA ≫ ModuleCat.ofHom (concreteHomologyIdealTransition
            (bot_le : ⊥ ≤ I ^ m) (P.sc i).f (P.sc i).g (P.sc i).zero) :=
        fun m ↦ homologyFunctor_map_rowComplexMapRight_mkQ I m P i
      have hnat : ∀ {n m : ℕ} (h : n ≤ m), (DerivedCategory.homologyFunctor _ i).map
          ((T ⋙ Ψ).map (homOfLE h).op) ≫ eB n =
            eB m ≫ ModuleCat.ofHom (concreteHomologyIdealTransition
              (Ideal.pow_le_pow_right h) (P.sc i).f (P.sc i).g (P.sc i).zero) := fun h ↦
        derivedAdicQuotientRowHomologyHom_naturality I P i h
      refine ⟨Opposite.op m, (homOfLE hnm).op, eB m ≫ ModuleCat.ofHom sc ≫ inv eA, ?_, ?_⟩
      · rw [reassoc_of% (hsq m), ← Category.assoc (ModuleCat.ofHom _)
          (ModuleCat.ofHom sc), ← ModuleCat.ofHom_comp, hsc₁]
        simp
      · rw [← cancel_mono (eB j.unop)]
        change (eB m ≫ ModuleCat.ofHom sc ≫ inv eA) ≫
            (DerivedCategory.homologyFunctor _ i).map (α.app (Opposite.op j.unop)) ≫ eB j.unop =
          (DerivedCategory.homologyFunctor _ i).map ((T ⋙ Ψ).map (homOfLE hnm).op) ≫ eB j.unop
        rw [hsq, hnat, Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc,
          ← ModuleCat.ofHom_comp, hsc₂]) (Opposite.op n)
  exact ⟨k.unop, leOfHom f.unop, s, hs₁, hs₂⟩

end Stacks.PseudoCoherent.AdicCompletion
