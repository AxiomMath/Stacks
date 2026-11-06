module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution.FiniteIntegralClosure

/-!
# Tag 09II from Epp's theorem: the finite-stage descent

Part 6 of the development of Stacks Tag 09II from Epp's theorem (Tag 09F9) in
`StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution`. It contains
the finite-stage descent of the wild case: generation and bijectivity of lifts along directed
ranges, tensor products over surjective scalars, finiteness of integral closures of tensor
products, and formal smoothness and separability transported along bijective base changes.
-/

@[expose] public section

universe uA uB uK uL v uK₁ uL₁ uA₁ uB₁

namespace Stacks.EliminateRamification

open IsLocalRing
open scoped TensorProduct

/-- A finite type algebra is generated over its base by one member of a directed ring cover. -/
private theorem exists_adjoin_range_eq_top_of_directed_ranges
    (R C : Type*) [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.FiniteType R C] {ι : Type*} [Preorder ι]
    [IsDirectedOrder ι] [Nonempty ι] (S : ι → Type*)
    [∀ i, CommRing (S i)] (f : ∀ i, S i →+* C)
    (hmono : Monotone fun i => (f i).range)
    (hcover : ∀ x : C, ∃ i, x ∈ (f i).range) :
    ∃ i, ∀ j, i ≤ j → Algebra.adjoin R (Set.range (f j)) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := C)
  choose g hg using fun x : s => hcover x.val
  obtain ⟨i, hi⟩ := Finite.exists_le g
  refine ⟨i, fun j hij => top_unique ?_⟩
  rw [← hs]
  apply Algebra.adjoin_mono
  intro x hx
  exact hmono ((hi ⟨x, hx⟩).trans hij) (hg ⟨x, hx⟩)

/-- Generators in the image of an algebra map give surjectivity of its scalar extension. -/
private theorem surjective_liftEquiv_of_adjoin_range_eq_top
    (R S A C : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing C]
    [Algebra R S] [Algebra R A] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
    (f : A →ₐ[R] C) (h : Algebra.adjoin S (Set.range f) = ⊤) :
    Function.Surjective (AlgHom.liftEquiv R S A C f) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← h, Algebra.adjoin_le_iff]
  rintro _ ⟨a, rfl⟩
  exact ⟨1 ⊗ₜ[R] a, by simp⟩

/-- Reduction commutes with scalar extension when its nilradical extends to the whole nilradical.
-/
private theorem bijective_liftEquiv_reduction_of_nilradical_map_eq
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (hn : (nilradical T).map
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T) =
        nilradical (S ⊗[R] T)) :
    Function.Bijective (AlgHom.liftEquiv R S
      (ReducedTensorTower.Reduction T)
      (ReducedTensorTower.Reduction (S ⊗[R] T))
      (ReducedTensorTower.reductionMap
        (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T))) := by
  let e := (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S T S (nilradical T)).trans
    (Ideal.quotientEquivAlgOfEq S hn)
  have he : (AlgHom.liftEquiv R S (ReducedTensorTower.Reduction T)
      (ReducedTensorTower.Reduction (S ⊗[R] T))
      (ReducedTensorTower.reductionMap
        (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T))) = e.toAlgHom := by
    ext t
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective t
    show (AlgHom.liftEquiv R S _ _
      (ReducedTensorTower.reductionMap
        (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)))
          (1 ⊗ₜ[R] Ideal.Quotient.mk _ x) = e (1 ⊗ₜ[R] Ideal.Quotient.mk _ x)
    rw [AlgHom.liftEquiv_tmul, one_smul, ReducedTensorTower.reductionMap_mk]
    show Ideal.Quotient.mk _ (1 ⊗ₜ[R] x) =
      Ideal.quotientEquivAlgOfEq S hn
        (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S T S (nilradical T)
          (1 ⊗ₜ[R] Ideal.Quotient.mk _ x))
    rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
      Ideal.quotientEquivAlgOfEq_mk]
  rw [he]
  exact e.bijective

/-- Injectivity of a tensor map follows from a compatible injective map on generic algebras. -/
theorem injective_tensorProduct_lift_of_injective_generic
    (R K S E C T U : Type*) [CommRing R] [CommRing K] [CommRing S]
    [CommRing E] [CommRing C] [CommRing T] [CommRing U]
    [Algebra R K] [Algebra R S] [Algebra R E] [Algebra S E]
    [IsScalarTower R S E] [Algebra K E] [IsScalarTower R K E]
    [Algebra R C] [Algebra R T] [Algebra K T] [IsScalarTower R K T]
    [Algebra K U]
    [Module.Flat R E] [Module.Flat R C]
    (M : Submonoid R) [IsLocalization M K]
    (j : C →ₐ[R] T) (hj : Function.Injective j)
    (hS : Function.Injective (algebraMap S E))
    (g : E ⊗[K] T →ₐ[K] U) (hg : Function.Injective g)
    (f : S ⊗[R] C →+* U)
    (hfg : ∀ s c, f (s ⊗ₜ[R] c) = g (algebraMap S E s ⊗ₜ[K] j c)) :
    Function.Injective f := by
  let i := Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S E) j
  have hi : Function.Injective i :=
    TensorProduct.map_injective_of_flat_flat
      (IsScalarTower.toAlgHom R S E).toLinearMap j.toLinearMap hS hj
  let e := IsLocalization.algebraTensorEquiv M K E T
  have he : f = (g.toRingHom.comp e.symm.toRingHom).comp i.toRingHom := by
    apply DFunLike.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul s c => exact hfg s c
  rw [he]
  exact hg.comp (e.symm.injective.comp hi)

/-- A tensor equivalence remains an equivalence after quotienting both scalar rings. -/
private noncomputable def tensorProductEquivOfSurjectiveScalars
    (R S K E A B : Type*) [CommSemiring R] [CommSemiring S]
    [CommSemiring K] [CommSemiring E] [CommSemiring A] [CommSemiring B]
    [Algebra R S] [Algebra R K] [Algebra R E] [Algebra S E] [Algebra K E]
    [IsScalarTower R S E] [IsScalarTower R K E]
    [Algebra R A] [Algebra K A] [IsScalarTower R K A]
    [Algebra R B] [Algebra S B] [Algebra E B]
    [IsScalarTower R S B] [IsScalarTower S E B]
    (hR : Function.Surjective (algebraMap R K))
    (hS : Function.Surjective (algebraMap S E))
    (e : S ⊗[R] A ≃ₐ[S] B) : E ⊗[K] A ≃ₐ[E] B := by
  have : TensorProduct.CompatibleSMul R K E A :=
    .of_algebraMap_surjective E A hR
  have : TensorProduct.CompatibleSMul S E E B :=
    .of_algebraMap_surjective E B hS
  exact (Algebra.TensorProduct.equivOfCompatibleSMul R K E E A).trans
    ((Algebra.TensorProduct.cancelBaseChange R S E E A).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E) e).trans
        ((Algebra.TensorProduct.equivOfCompatibleSMul S E E E B).symm.trans
          (Algebra.TensorProduct.lid E B))))
private theorem tensorProductEquivOfSurjectiveScalars_tmul
    (R S K E A B : Type*) [CommSemiring R] [CommSemiring S]
    [CommSemiring K] [CommSemiring E] [CommSemiring A] [CommSemiring B]
    [Algebra R S] [Algebra R K] [Algebra R E] [Algebra S E] [Algebra K E]
    [IsScalarTower R S E] [IsScalarTower R K E]
    [Algebra R A] [Algebra K A] [IsScalarTower R K A]
    [Algebra R B] [Algebra S B] [Algebra E B]
    [IsScalarTower R S B] [IsScalarTower S E B]
    (hR : Function.Surjective (algebraMap R K))
    (hS : Function.Surjective (algebraMap S E))
    (e : S ⊗[R] A ≃ₐ[S] B)
    (x : E) (a : A) :
    tensorProductEquivOfSurjectiveScalars R S K E A B hR hS e (x ⊗ₜ[K] a) =
      x • e (1 ⊗ₜ[R] a) := by
  rfl

/-- Finiteness of normalization over a semilocal model over a Dedekind domain. -/
private theorem finite_integralClosure_of_isDedekindDomain
    (R K S T : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra K T] [IsScalarTower R K T] [Algebra.EssFiniteType S T]
    [Algebra.IsGeometricallyReduced K T] [Finite (MaximalSpectrum S)]
    (hn : ∀ (q : Ideal S) [q.IsMaximal], q.comap (algebraMap R S) ≠ ⊥) :
    Module.Finite S (integralClosure S T) := by
  apply finite_integralClosure_of_isLocalized_maximal S T
  intro q hq
  exact finite_integralClosure_localization_of_isDedekindDomain R K S T q (hn q)

/-- A maximal ideal above a local integral extension has nonzero contraction to
any intermediate algebra containing the original discrete valuation ring. -/
private theorem comap_ne_bot_of_integral_tower
    (A B R C : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [CommRing R] [Algebra A R] [FaithfulSMul A R]
    [CommRing C] [Algebra B C] [Algebra.IsIntegral B C]
    [Algebra A C] [IsScalarTower A B C] [Algebra R C] [IsScalarTower A R C]
    (q : Ideal C) [q.IsMaximal] : q.comap (algebraMap R C) ≠ ⊥ := by
  have hB : q.comap (algebraMap B C) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) q)
  have hA : q.comap (algebraMap A C) = IsLocalRing.maximalIdeal A := by
    rw [IsScalarTower.algebraMap_eq A B C, ← Ideal.comap_comap, hB,
      IsLocalRing.maximalIdeal_comap]
  intro h
  have he : q.comap (algebraMap A C) = ⊥ := by
    rw [IsScalarTower.algebraMap_eq A R C, ← Ideal.comap_comap, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective A R)
  exact IsDiscreteValuationRing.not_a_field A (hA.symm.trans he)

-- The tensor model has compatible scalar actions from both original base rings.
theorem finite_integralClosure_tensorProduct_of_isGeometricallyReduced
    (A B R K T C : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [CommRing R] [IsDedekindDomain R] [Algebra A R] [FaithfulSMul A R]
    [Algebra.IsIntegral A R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing T] [Algebra B T] [Algebra R T] [Algebra K T]
    [IsScalarTower R K T] [Algebra.IsGeometricallyReduced K T]
    [Algebra.EssFiniteType R T]
    [CommRing C] [Algebra A C] [Algebra B C] [Algebra R C] [Algebra C T]
    [IsScalarTower A B C] [IsScalarTower A R C]
    [IsScalarTower B C T] [IsScalarTower R C T] [IsIntegralClosure C B T] :
    let f := AlgHom.liftEquiv A R B C (IsScalarTower.toAlgHom A B C)
    letI := f.toAlgebra
    Module.Finite (R ⊗[A] B) C := by
  classical
  let S := R ⊗[A] B
  let f := AlgHom.liftEquiv A R B C (IsScalarTower.toAlgHom A B C)
  let := f.toAlgebra
  let : Algebra B S := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower A B S := inferInstance
  have : Algebra.IsIntegral B S :=
    Algebra.IsIntegral.of_surjective
      (Algebra.TensorProduct.commRight A B R).toAlgHom
      (Algebra.TensorProduct.commRight A B R).surjective
  have : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq fun r =>
    (f.commutes r).symm
  have : IsScalarTower B S C := IsScalarTower.of_algebraMap_eq fun b => by
    show algebraMap B C b = f (1 ⊗ₜ[A] b)
    simp [f]
  let : Algebra S T := ((algebraMap C T).comp f.toRingHom).toAlgebra
  have : IsScalarTower S C T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B S T := IsScalarTower.to₁₂₄ B S C T
  have : IsScalarTower R S T := IsScalarTower.to₁₂₄ R S C T
  have : Algebra.EssFiniteType R S := inferInstance
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  have : Algebra.EssFiniteType S T := Algebra.EssFiniteType.of_comp R S T
  have : Finite (PrimeSpectrum B) :=
    IsDiscreteValuationRing.finite_primeSpectrum_of_dimensionLEOne B
  have : Finite (PrimeSpectrum S) :=
    finite_primeSpectrum_of_isIntegral_of_isNoetherianRing B S
  have : Finite (MaximalSpectrum S) := Finite.of_injective
    (fun q : MaximalSpectrum S => (⟨q.asIdeal, q.isMaximal.isPrime⟩ : PrimeSpectrum S))
    (fun _ _ h => MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal h))
  have : Module.Finite S (integralClosure S T) :=
    finite_integralClosure_of_isDedekindDomain R K S T
      (fun q _ => comap_ne_bot_of_integral_tower A B R S q)
  have : IsIntegralClosure C S T := IsIntegralClosure.tower_top (R := B) (A := S)
  exact Module.Finite.equiv (IsIntegralClosure.equiv S C T (integralClosure S T)).symm.toLinearEquiv

/-- At a finite stage capturing the nilradical, reduction commutes with extension to the limit
field. -/
theorem exists_reducedTensorProductScalarExtensionEquiv
    (K F E A : Type*) [Field K] [Field F] [Field E] [CommRing A]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] [Algebra K A]
    (hn : (nilradical (A ⊗[K] F)).map
      (Algebra.TensorProduct.map (AlgHom.id A A) (IsScalarTower.toAlgHom K F E)).toRingHom =
        nilradical (A ⊗[K] E)) :
    letI : Algebra F (A ⊗[K] F) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra E (A ⊗[K] E) := Algebra.TensorProduct.rightAlgebra
    ∃ e : E ⊗[F] ReducedTensorTower.Reduction (A ⊗[K] F) ≃ₐ[E]
        ReducedTensorTower.Reduction (A ⊗[K] E),
      ∀ x, e (1 ⊗ₜ[F] x) = (ReducedTensorTower.reductionMap
        (Algebra.TensorProduct.map (AlgHom.id A A) (IsScalarTower.toAlgHom K F E))) x := by
  let : Algebra E (A ⊗[K] E) := Algebra.TensorProduct.rightAlgebra
  let : Algebra F (A ⊗[K] F) := Algebra.TensorProduct.rightAlgebra
  let e : E ⊗[F] (A ⊗[K] F) ≃ₐ[E] A ⊗[K] E :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E)
      (Algebra.TensorProduct.commRight K F A).symm).trans
        ((Algebra.TensorProduct.cancelBaseChange K F E E A).trans
          (Algebra.TensorProduct.commRight K E A))
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : A ⊗[K] F →ₐ[F] E ⊗[F] (A ⊗[K] F)).toRingHom =
        (Algebra.TensorProduct.map (AlgHom.id A A) (IsScalarTower.toAlgHom K F E)).toRingHom := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a f =>
      show e (1 ⊗ₜ[F] (a ⊗ₜ[K] f)) = a ⊗ₜ[K] algebraMap F E f
      simp only [e, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, AlgEquiv.coe_refl, AlgEquiv.coe_toAlgHom,
        Algebra.TensorProduct.commRight_symm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.commRight_tmul, Algebra.smul_def, id_eq, mul_one]
  have hnil : (nilradical (A ⊗[K] F)).map
      (Algebra.TensorProduct.includeRight : A ⊗[K] F →ₐ[F] E ⊗[F] (A ⊗[K] F)).toRingHom =
        nilradical (E ⊗[F] (A ⊗[K] F)) := by
    apply Function.LeftInverse.injective
      (fun I => Ideal.comap_map_of_bijective e.toRingHom e.bijective (I := I))
    rw [Ideal.map_map, he, hn]
    show nilradical (A ⊗[K] E) = (Ideal.map e.toRingHom (⊥ : Ideal _).radical)
    rw [Ideal.map_radical_of_surjective e.surjective
      (le_of_eq ((RingHom.injective_iff_ker_eq_bot _).mp e.injective)), Ideal.map_bot]
    rfl
  let e₁ := AlgEquiv.ofBijective _
    (bijective_liftEquiv_reduction_of_nilradical_map_eq F E (A ⊗[K] F) hnil)
  let e₂ := ReducedTensorTower.reductionEquiv e
  refine ⟨e₁.trans e₂, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  show e₂ (AlgHom.liftEquiv F E _ _
      (ReducedTensorTower.reductionMap
        (Algebra.TensorProduct.includeRight : A ⊗[K] F →ₐ[F] E ⊗[F] (A ⊗[K] F)))
      (1 ⊗ₜ[F] Ideal.Quotient.mk _ y)) = _
  rw [AlgHom.liftEquiv_tmul, one_smul, ReducedTensorTower.reductionMap_mk]
  show Ideal.Quotient.mk _ (e (1 ⊗ₜ[F] y)) =
    Ideal.Quotient.mk _ (Algebra.TensorProduct.map (AlgHom.id A A)
      (IsScalarTower.toAlgHom K F E) y)
  exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun he y)

theorem exists_adjoin_range_eq_top_integralClosure_reducedTensor_finite_stage
    (B K L E R : Type*) [CommRing B] [Field K] [CommRing L] [Field E] [CommRing R]
    [Algebra K L] [Algebra K E] [Algebra B L] [Algebra.IsAlgebraic K E]
    [Algebra R (integralClosure B (ReducedTensorTower.Reduction (L ⊗[K] E)))]
    [Algebra.FiniteType R (integralClosure B (ReducedTensorTower.Reduction (L ⊗[K] E)))] :
    ∃ F : IntermediateField K E, Module.Finite K F ∧
      ∀ G : IntermediateField K E, Module.Finite K G → F ≤ G →
        Algebra.adjoin R (Set.range (integralClosureReducedTensorMap B K L G)) = ⊤ := by
  let ι := {F : IntermediateField K E // Module.Finite K F}
  have : Nonempty ι := ⟨⟨⊥, inferInstance⟩⟩
  have : IsDirectedOrder ι := ⟨fun F G => by
    have := F.property
    have := G.property
    exact ⟨⟨F.val ⊔ G.val, inferInstance⟩,
      show F.val ≤ F.val ⊔ G.val from le_sup_left,
      show G.val ≤ F.val ⊔ G.val from le_sup_right⟩⟩
  obtain ⟨F, hF⟩ := exists_adjoin_range_eq_top_of_directed_ranges R
    (integralClosure B (ReducedTensorTower.Reduction (L ⊗[K] E)))
    (fun F : ι => integralClosure B (ReducedTensorTower.Reduction (L ⊗[K] F.val)))
    (fun F => (integralClosureReducedTensorMap B K L F.val).toRingHom)
    (fun _ _ h => monotone_integralClosureReducedTensorMap_range B K L E h)
    (fun x => by
      obtain ⟨F, hF, hx⟩ := exists_mem_integralClosureReducedTensorMap_range B K L E x
      exact ⟨⟨F, hF⟩, hx⟩)
  exact ⟨F.val, F.property, fun G hG hFG => hF ⟨G, hG⟩ hFG⟩

private theorem bijective_liftEquiv_of_bijective_of_ker_eq_map
    (R S A B A' B' : Type*) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    [Algebra R A'] [Algebra R B'] [Algebra S B'] [IsScalarTower R S B']
    (f : A →ₐ[R] B) (g : A' →ₐ[R] B')
    (p : A →ₐ[R] A') (q : B →ₐ[S] B')
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hfg : g.comp p = (q.restrictScalars R).comp f)
    (hf : Function.Bijective (AlgHom.liftEquiv R S A B f))
    (hker : RingHom.ker q = (RingHom.ker p).map f) :
    Function.Bijective (AlgHom.liftEquiv R S A' B' g) := by
  let F := AlgHom.liftEquiv R S A B f
  let G := AlgHom.liftEquiv R S A' B' g
  let P := Algebra.TensorProduct.map (AlgHom.id S S) p
  have hP : Function.Surjective P := Algebra.TensorProduct.map_surjective _ _
    Function.surjective_id hp
  have hcomp : G.comp P = q.comp F := by
    ext a
    simpa [F, G, P] using DFunLike.congr_fun hfg a
  have hinc : F.toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom = f.toRingHom := by
    ext a
    simp [F, Algebra.TensorProduct.includeRight]
  have hkerP : RingHom.ker P = (RingHom.ker q).comap F := by
    have hkp : RingHom.ker P = (RingHom.ker p).map
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) := by
      show RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) p) = _
      exact Algebra.TensorProduct.lTensor_ker p hp
    rw [hkp, hker]
    have he : (RingHom.ker p).map f =
        ((RingHom.ker p).map
          (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)).map F := by
      show (RingHom.ker p).map f.toRingHom =
        ((RingHom.ker p).map
          (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom).map F.toRingHom
      rw [Ideal.map_map]
      exact congrArg (fun j : A →+* B => (RingHom.ker p).map j) hinc.symm
    rw [he]
    exact (Ideal.comap_map_of_bijective F.toRingHom hf).symm
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot _).mpr
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨x, rfl⟩ := hP y
    have hx : x ∈ RingHom.ker P := by
      rw [hkerP]
      show q (F x) = 0
      exact (DFunLike.congr_fun hcomp x).symm.trans hy
    exact hx
  · exact Function.Surjective.of_comp (f := G) (g := P)
      (show Function.Surjective (G ∘ P) from by
        show Function.Surjective (G.comp P)
        rw [hcomp]
        exact hq.comp hf.surjective)
theorem surjective_of_adjoin_eq_top
    (S C D : Type*) [CommRing S] [CommRing C] [CommRing D] [Algebra S C]
    (f : D →+* C) (s : Set C) (h : Algebra.adjoin S s = ⊤)
    (hS : ∀ x : S, algebraMap S C x ∈ f.range) (hs : s ⊆ f.range) :
    Function.Surjective f := by
  let T : Subalgebra S C := { f.range with algebraMap_mem' := hS }
  have ht : Algebra.adjoin S s ≤ T := Algebra.adjoin_le_iff.mpr hs
  have he : T = ⊤ := top_unique (h ▸ ht)
  intro x
  have hx : x ∈ T := he ▸ Algebra.mem_top
  exact hx

private theorem faithfullyFlat_of_injective_of_isDiscreteValuationRing
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Injective f) :
    letI := f.toAlgebra
    Module.FaithfullyFlat R S := by
  let := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hf
  have : Module.IsTorsionFree R S := inferInstance
  have : Module.Flat R S := inferInstance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

private theorem map_maximalIdeal_eq_of_faithfullyFlat_square
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    (f : R →+* S) (a : R →+* R') (b : S →+* S') (f' : R' →+* S')
    (hcomm : b.comp f = f'.comp a)
    (hflat : letI := b.toAlgebra; Module.FaithfullyFlat S S')
    (ha : (maximalIdeal R).map a = maximalIdeal R')
    (hb : (maximalIdeal S).map b = maximalIdeal S')
    (hf : (maximalIdeal R').map f' = maximalIdeal S') :
    (maximalIdeal R).map f = maximalIdeal S := by
  let := b.toAlgebra
  have := hflat
  apply Ideal.map_injective_of_faithfullyFlat (B := S')
  show ((maximalIdeal R).map f).map b = (maximalIdeal S).map b
  rw [Ideal.map_map, hcomm, ← Ideal.map_map, ha, hb, hf]

private theorem localRingHom_injective_of_comp_injective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (q : Ideal S) [q.IsPrime]
    (hf : Function.Injective ((algebraMap S (Localization.AtPrime q)).comp f)) :
    Function.Injective (Localization.localRingHom (q.comap f) q f rfl) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (q.comap f).primeCompl _).mpr
  intro x y
  constructor
  · exact congrArg _
  · intro h
    apply congrArg (algebraMap R (Localization.AtPrime (q.comap f)))
    apply hf
    simpa only [Localization.localRingHom_to_map, RingHom.comp_apply] using h

/-- The algebra structure on localizations given by `localRingHom` is compatible with the base. -/
private theorem isScalarTower_localRingHom
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (q : Ideal S)
    [p.IsPrime] [q.IsPrime] (hpq : p = q.comap (algebraMap R S)) :
    letI := (Localization.localRingHom p q (algebraMap R S) hpq).toAlgebra
    IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := by
  let := (Localization.localRingHom p q (algebraMap R S) hpq).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun r =>
    (IsScalarTower.algebraMap_apply R S (Localization.AtPrime q) r).trans
      (Localization.localRingHom_to_map p q (algebraMap R S) hpq r).symm

private theorem isSeparableExtension_residueField_of_bijective_tensorProduct
    (R S R' S' : Type*) [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra R' S'] [IsScalarTower R R' S']
    (b : S →ₐ[R] S') (hb : Function.Bijective (AlgHom.liftEquiv R R' S S' b))
    (p : Ideal R) (q : Ideal S) (p' : Ideal R') (q' : Ideal S')
    [p.IsMaximal] [q.IsMaximal] [p'.IsMaximal] [q'.IsMaximal]
    (hpq : p = q.comap (algebraMap R S))
    (hp'q' : p' = q'.comap (algebraMap R' S'))
    (hpp' : p = p'.comap (algebraMap R R'))
    (hqq' : q = q'.comap b.toRingHom) (hquot : q.map b.toRingHom = q')
    (hsep : letI := (Localization.localRingHom p' q' (algebraMap R' S') hp'q').toAlgebra
      letI : IsLocalHom (algebraMap (Localization.AtPrime p') (Localization.AtPrime q')) :=
        Localization.isLocalHom_localRingHom p' q' (algebraMap R' S') hp'q'
      Algebra.IsSeparableExtension p'.ResidueField q'.ResidueField) :
    letI := (Localization.localRingHom p q (algebraMap R S) hpq).toAlgebra
    letI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
      Localization.isLocalHom_localRingHom p q (algebraMap R S) hpq
    Algebra.IsSeparableExtension p.ResidueField q.ResidueField := by
  let f := Localization.localRingHom p q (algebraMap R S) hpq
  let f' := Localization.localRingHom p' q' (algebraMap R' S') hp'q'
  let a := Localization.localRingHom p p' (algebraMap R R') hpp'
  let := f.toAlgebra
  let := f'.toAlgebra
  let := a.toAlgebra
  have hfLocal : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom p q (algebraMap R S) hpq
  have hfLocal' : IsLocalHom (algebraMap (Localization.AtPrime p') (Localization.AtPrime q')) :=
    Localization.isLocalHom_localRingHom p' q' (algebraMap R' S') hp'q'
  have haLocal : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime p')) :=
    Localization.isLocalHom_localRingHom p p' (algebraMap R R') hpp'
  have := isScalarTower_localRingHom R S p q hpq
  have := isScalarTower_localRingHom R' S' p' q' hp'q'
  have := isScalarTower_localRingHom R R' p p' hpp'
  have : IsScalarTower R R' q'.ResidueField :=
    IsScalarTower.to₁₂₄ R R' S' q'.ResidueField
  let g := Ideal.ResidueField.mapₐ q q' b hqq'
  let π := IsScalarTower.toAlgHom R S q.ResidueField
  let π' := IsScalarTower.toAlgHom R' S' q'.ResidueField
  have hfg : g.comp π = (π'.restrictScalars R).comp b := by
    ext x
    show Ideal.ResidueField.map q q' b hqq' (algebraMap S q.ResidueField x) =
      algebraMap S' q'.ResidueField (b x)
    exact Ideal.ResidueField.map_algebraMap q q' b hqq' x
  have hker : RingHom.ker π' = (RingHom.ker π).map b := by
    show RingHom.ker (algebraMap S' q'.ResidueField) =
      (RingHom.ker (algebraMap S q.ResidueField)).map b.toRingHom
    rw [Ideal.ker_algebraMap_residueField, Ideal.ker_algebraMap_residueField, hquot]
  have hbij := bijective_liftEquiv_of_bijective_of_ker_eq_map R R' S S'
    q.ResidueField q'.ResidueField b g π π'
    q.algebraMap_residueField_surjective q'.algebraMap_residueField_surjective hfg hb hker
  let e := AlgEquiv.ofBijective _ hbij
  let e' := tensorProductEquivOfSurjectiveScalars R R' p.ResidueField p'.ResidueField
    q.ResidueField q'.ResidueField p.algebraMap_residueField_surjective
    p'.algebraMap_residueField_surjective e
  have : Algebra.IsSeparableExtension p'.ResidueField q'.ResidueField := hsep
  exact isSeparableExtension_of_injective_tensorProduct p.ResidueField p'.ResidueField
    q.ResidueField q'.ResidueField e'.toAlgHom e'.injective

theorem nilradical_map_eq_of_le_intermediateField
    (K L E : Type*) [Field K] [CommRing L] [Field E] [Algebra K L] [Algebra K E]
    (F G : IntermediateField K E) (hFG : F ≤ G)
    (hn : (nilradical (L ⊗[K] F)).map
      (Algebra.TensorProduct.map (.id L L) F.val).toRingHom = nilradical (L ⊗[K] E)) :
    (nilradical (L ⊗[K] G)).map
      (Algebra.TensorProduct.map (.id L L) G.val).toRingHom = nilradical (L ⊗[K] E) := by
  let f := (Algebra.TensorProduct.map (.id L L) G.val).toRingHom
  have hle : (nilradical (L ⊗[K] G)).map f ≤ nilradical (L ⊗[K] E) :=
    Ideal.map_le_iff_le_comap.mpr (nilradical_le_comap f)
  apply le_antisymm hle
  rw [← hn]
  let i := (Algebra.TensorProduct.map (.id L L) (IntermediateField.inclusion hFG)).toRingHom
  have hi : (Algebra.TensorProduct.map (.id L L) F.val).toRingHom = f.comp i := by
    ext <;> rfl
  rw [hi, ← Ideal.map_map]
  exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr (nilradical_le_comap i))

theorem formallySmoothNAdic_localRingHom_of_bijective_tensorProduct
    (R : Type uA) (S : Type uB) (R' : Type uK) (S' : Type uL)
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra R' S'] [IsScalarTower R R' S']
    (b : S →ₐ[R] S') (hb : Function.Bijective (AlgHom.liftEquiv R R' S S' b))
    (p : Ideal R) (q : Ideal S) (p' : Ideal R') (q' : Ideal S')
    [p.IsMaximal] [q.IsMaximal] [p'.IsMaximal] [q'.IsMaximal]
    (hpq : p = q.comap (algebraMap R S))
    (hp'q' : p' = q'.comap (algebraMap R' S'))
    (hpp' : p = p'.comap (algebraMap R R'))
    (hqq' : q = q'.comap b.toRingHom)
    [IsDomain (Localization.AtPrime p)] [IsDiscreteValuationRing (Localization.AtPrime p)]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)]
    [IsDomain (Localization.AtPrime p')] [IsDiscreteValuationRing (Localization.AtPrime p')]
    [IsDomain (Localization.AtPrime q')] [IsDiscreteValuationRing (Localization.AtPrime q')]
    (hfinj : Function.Injective (Localization.localRingHom p q (algebraMap R S) hpq))
    (hf'inj : Function.Injective (Localization.localRingHom p' q' (algebraMap R' S') hp'q'))
    (hbinj : Function.Injective (Localization.localRingHom q q' b.toRingHom hqq'))
    (ha : p.map (algebraMap R R') = p') (hquot : q.map b.toRingHom = q')
    (hsmooth : RingHom.FormallySmoothNAdic.{max uK uL}
      (Localization.localRingHom p' q' (algebraMap R' S') hp'q')
      (maximalIdeal (Localization.AtPrime q'))) :
    RingHom.FormallySmoothNAdic.{max uA uB}
      (Localization.localRingHom p q (algebraMap R S) hpq)
      (maximalIdeal (Localization.AtPrime q)) := by
  rcases hpp' with rfl
  rcases hqq' with rfl
  let f := Localization.localRingHom _ _ (algebraMap R S) hpq
  let f' := Localization.localRingHom p' q' (algebraMap R' S') hp'q'
  let a := Localization.localRingHom _ p' (algebraMap R R') rfl
  let b' := Localization.localRingHom _ q' b.toRingHom rfl
  let := f.toAlgebra
  let := f'.toAlgebra
  have : IsLocalHom (algebraMap (Localization.AtPrime (p'.comap (algebraMap R R')))
      (Localization.AtPrime (q'.comap b.toRingHom))) :=
    Localization.isLocalHom_localRingHom _ _ (algebraMap R S) hpq
  have : IsLocalHom (algebraMap (Localization.AtPrime p') (Localization.AtPrime q')) :=
    Localization.isLocalHom_localRingHom _ _ (algebraMap R' S') hp'q'
  have : FaithfulSMul (Localization.AtPrime (p'.comap (algebraMap R R')))
      (Localization.AtPrime (q'.comap b.toRingHom)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hfinj
  have : IsDiscreteValuationRing.IsExtension (Localization.AtPrime (p'.comap (algebraMap R R')))
      (Localization.AtPrime (q'.comap b.toRingHom)) := {}
  have : FaithfulSMul (Localization.AtPrime p') (Localization.AtPrime q') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hf'inj
  have : IsDiscreteValuationRing.IsExtension (Localization.AtPrime p')
    (Localization.AtPrime q') := {}
  have htop := (IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension
    (Localization.AtPrime p') (Localization.AtPrime q')).mp hsmooth
  have ha' := map_maximalIdeal_localRingHom_of_map_comap_eq (algebraMap R R') p' ha
  have hb' := map_maximalIdeal_localRingHom_of_map_comap_eq b.toRingHom q' hquot
  have hf' := (IsDiscreteValuationRing.weaklyUnramified_iff_map_maximalIdeal
    (Localization.AtPrime p') (Localization.AtPrime q')).mp htop.1
  have hcomm : b'.comp f = f'.comp a := by
    apply IsLocalization.ringHom_ext (p'.comap (algebraMap R R')).primeCompl
    ext r
    simp only [RingHom.comp_apply, f, f', a, b', Localization.localRingHom_to_map]
    exact congrArg (algebraMap S' (Localization.AtPrime q'))
      ((b.commutes r).trans (IsScalarTower.algebraMap_apply R R' S' r))
  have hflat := faithfullyFlat_of_injective_of_isDiscreteValuationRing b' hbinj
  have hmax := map_maximalIdeal_eq_of_faithfullyFlat_square f a b' f' hcomm hflat ha' hb' hf'
  have hweak := (IsDiscreteValuationRing.weaklyUnramified_iff_map_maximalIdeal
    (Localization.AtPrime (p'.comap (algebraMap R R')))
    (Localization.AtPrime (q'.comap b.toRingHom))).mpr hmax
  have hsep := isSeparableExtension_residueField_of_bijective_tensorProduct R S R' S' b hb
    (p'.comap (algebraMap R R')) (q'.comap b.toRingHom) p' q'
    hpq hp'q' rfl rfl hquot htop.2
  exact (IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension
    (Localization.AtPrime (p'.comap (algebraMap R R')))
    (Localization.AtPrime (q'.comap b.toRingHom))).mpr ⟨hweak, hsep⟩

theorem localRingHom_injective_of_primeSpectrum_comap_injective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (hi : f.IsIntegral)
    (hsp : Function.Injective (PrimeSpectrum.comap f))
    (q : Ideal S) [q.IsPrime] :
    Function.Injective (Localization.localRingHom (q.comap f) q f rfl) := by
  let := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hf
  have : Algebra.IsIntegral R S := ⟨hi⟩
  have hq : (q.comap f).primesOver S = {q} := by
    ext r
    constructor
    · rintro ⟨hr, hcomap⟩
      have he : (⟨r, hr⟩ : PrimeSpectrum S) = ⟨q, inferInstance⟩ := by
        apply hsp
        apply PrimeSpectrum.ext
        exact hcomap.over.symm
      exact congrArg PrimeSpectrum.asIdeal he
    · rintro rfl
      exact ⟨inferInstance, ⟨rfl⟩⟩
  exact Localization.localRingHom_injective_of_primesOver_eq_singleton hq

theorem integralClosure_localRingHom_isDiscreteValuationRing_and_injective
    (A B R L T : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B]
    [CommRing R] [IsDedekindDomain R] [Algebra A R] [Algebra.IsIntegral A R]
    [FaithfulSMul A R]
    [Field L] [Algebra B L] [FaithfulSMul B L]
    [CommRing T] [Algebra L T] [Algebra B T] [IsScalarTower B L T]
    [IsArtinianRing T] [IsReduced T]
    [IsNoetherianRing (integralClosure B T)]
    [Algebra A (integralClosure B T)] [IsScalarTower A B (integralClosure B T)]
    [Algebra R (integralClosure B T)] [IsScalarTower A R (integralClosure B T)]
    (q : Ideal (integralClosure B T)) [q.IsMaximal] :
    (q.comap (algebraMap R (integralClosure B T))).IsMaximal ∧
    ∃ (_ : IsDomain (Localization.AtPrime q))
      (_ : IsDiscreteValuationRing (Localization.AtPrime q)),
      IsDiscreteValuationRing
        (Localization.AtPrime (q.comap (algebraMap R (integralClosure B T)))) ∧
      Function.Injective (Localization.localRingHom
        (q.comap (algebraMap R (integralClosure B T))) q
        (algebraMap R (integralClosure B T)) rfl) := by
  have hp := comap_ne_bot_of_integral_tower A B R (integralClosure B T) q
  have hpmax := (Ideal.IsPrime.comap (algebraMap R (integralClosure B T))).isMaximal hp
  obtain ⟨hqdom, hqdvr⟩ := isDiscreteValuationRing_integralClosure_localization B L T q
  have : IsDiscreteValuationRing
      (Localization.AtPrime (q.comap (algebraMap R (integralClosure B T)))) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp _
  have : FaithfulSMul B (Localization.AtPrime q) :=
    faithfulSMul_integralClosure_localization B L T q
  have : FaithfulSMul A (Localization.AtPrime q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime q)]
      exact (FaithfulSMul.algebraMap_injective B _).comp (FaithfulSMul.algebraMap_injective A B))
  have : IsScalarTower A R (Localization.AtPrime q) :=
    IsScalarTower.to₁₂₄ A R (integralClosure B T) (Localization.AtPrime q)
  have : FaithfulSMul R (Localization.AtPrime q) :=
    faithfulSMul_of_isIntegral_tower A R (Localization.AtPrime q)
  refine ⟨hpmax, hqdom, hqdvr, inferInstance, ?_⟩
  apply localRingHom_injective_of_comp_injective
  show Function.Injective ((algebraMap (integralClosure B T) (Localization.AtPrime q)).comp
    (algebraMap R (integralClosure B T)))
  rw [← IsScalarTower.algebraMap_eq R (integralClosure B T) (Localization.AtPrime q)]
  exact FaithfulSMul.algebraMap_injective R _

private theorem isSeparableExtension_of_ringEquiv
    (k K k' K' : Type*) [Field k] [Field K] [Field k'] [Field K']
    [Algebra k K] [Algebra k' K'] [Algebra.IsSeparableExtension k K]
    (e : k' ≃+* k) (e' : K' ≃+* K)
    (he : e'.toRingHom.comp (algebraMap k' K') = (algebraMap k K).comp e.toRingHom) :
    Algebra.IsSeparableExtension k' K' := by
  let : Algebra k' k := e.toRingHom.toAlgebra
  let : Algebra k K' := (e'.symm.toRingHom.comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k' k K' := IsScalarTower.of_algebraMap_eq fun x => by
    apply e'.injective
    show e' (algebraMap k' K' x) = e' (e'.symm (algebraMap k K (e x)))
    rw [e'.apply_symm_apply]
    exact DFunLike.congr_fun he x
  have : TensorProduct.CompatibleSMul k' k k K' :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective k K' e.surjective
  let g : K' ≃ₐ[k] K := { __ := e', commutes' := fun x => e'.apply_symm_apply _ }
  let t := (Algebra.TensorProduct.equivOfCompatibleSMul k' k k k K').symm.trans
    ((Algebra.TensorProduct.lid k K').trans g)
  exact isSeparableExtension_of_injective_tensorProduct k' k K' K t.toAlgHom t.injective

private theorem formallySmoothNAdic_of_weaklyUnramified_and_isSeparableExtension
    (A : Type uA) (B : Type uB)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B]
    [Algebra.IsSeparableExtension (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (h : IsDiscreteValuationRing.IsWeaklyUnramified A B) :
    RingHom.FormallySmoothNAdic.{v} (algebraMap A B)
      (IsLocalRing.maximalIdeal B) := by
  let A' := ULift.{v} A
  let B' := ULift.{v} B
  let eA : A' ≃+* A := ULift.ringEquiv
  let eB : B' ≃+* B := ULift.ringEquiv
  have : IsDomain A' := eA.injective.isDomain eA
  have : IsDomain B' := eB.injective.isDomain eB
  have : IsDiscreteValuationRing A' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eA.symm
  have : IsDiscreteValuationRing B' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eB.symm
  let : Algebra A' B' := ULift.algebra' A B'
  let φ := algebraMap A' B'
  have : FaithfulSMul A' B' := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (eB.symm.injective.comp ((FaithfulSMul.algebraMap_injective A B).comp eA.injective))
  have : IsLocalHom φ := ⟨fun a ha => by
    have hb : IsUnit (algebraMap A B (eA a)) := ha.map eB.toRingHom
    have ha' : IsUnit (eA a) := isUnit_of_map_unit (algebraMap A B) _ hb
    simpa using ha'.map eA.symm.toRingHom⟩
  have : IsDiscreteValuationRing.IsExtension A' B' := {}
  have hA := IsLocalRing.map_maximalIdeal_of_surjective eA.symm.toRingHom eA.symm.surjective
  have hB := IsLocalRing.map_maximalIdeal_of_surjective eB.symm.toRingHom eB.symm.surjective
  let eRA := Ideal.quotientEquiv (IsLocalRing.maximalIdeal A') (IsLocalRing.maximalIdeal A)
    eA (IsLocalRing.map_maximalIdeal_of_surjective eA.toRingHom eA.surjective).symm
  let eRB := Ideal.quotientEquiv (IsLocalRing.maximalIdeal B') (IsLocalRing.maximalIdeal B)
    eB (IsLocalRing.map_maximalIdeal_of_surjective eB.toRingHom eB.surjective).symm
  have : Algebra.IsSeparableExtension (IsLocalRing.ResidueField A') (IsLocalRing.ResidueField B') :=
    isSeparableExtension_of_ringEquiv (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField A') (IsLocalRing.ResidueField B') eRA eRB (by
        apply RingHom.ext
        intro x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        show eRB (Ideal.Quotient.mk _ (φ a)) =
          Ideal.Quotient.mk _ (algebraMap A B (eA a))
        exact Ideal.quotientEquiv_mk _ _ _ _ _)
  have hφ : IsDiscreteValuationRing.IsWeaklyUnramified A' B' := by
    apply (IsDiscreteValuationRing.weaklyUnramified_iff_map_maximalIdeal A' B').2
    rw [← hA, Ideal.map_map]
    have he : φ.comp eA.symm.toRingHom = eB.symm.toRingHom.comp (algebraMap A B) := by
      ext a
      rfl
    show (IsLocalRing.maximalIdeal A).map (φ.comp eA.symm.toRingHom) = _
    rw [he, ← Ideal.map_map,
      (IsDiscreteValuationRing.weaklyUnramified_iff_map_maximalIdeal A B).1 h, hB]
  have hs := (IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension
    A' B').mpr
    ⟨hφ, inferInstance⟩
  apply formallySmoothNAdic_of_ulift_testRing.{v, max uA uB}
  apply formallySmoothNAdic_of_ringEquiv φ (algebraMap A B) eA eB _ hs
  ext a
  rfl

theorem formallySmoothNAdic_of_formallySmoothNAdic_sameUniverse
    {A : Type uA} {B : Type uB}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : Function.Injective f)
    (hs : RingHom.FormallySmoothNAdic.{max uA uB} f (IsLocalRing.maximalIdeal B)) :
    RingHom.FormallySmoothNAdic.{v} f (IsLocalRing.maximalIdeal B) := by
  let := f.toAlgebra
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom f)
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  have : IsDiscreteValuationRing.IsExtension A B := {}
  obtain ⟨hw, hsep⟩ :=
    (IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A B).mp hs
  have := hsep
  exact formallySmoothNAdic_of_weaklyUnramified_and_isSeparableExtension A B hw

theorem localRingHom_injective_of_eq_comap
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hp : p = q.comap f)
    (hf : Function.Injective (Localization.localRingHom (q.comap f) q f rfl)) :
    Function.Injective (Localization.localRingHom p q f hp) := by
  subst p
  exact hf

end Stacks.EliminateRamification
