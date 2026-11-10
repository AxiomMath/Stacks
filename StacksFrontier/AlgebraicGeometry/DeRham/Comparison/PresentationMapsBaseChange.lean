module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsIndependence

/-!
# The maps of Remark 0FL9 along base change and localization

Let `A → B` be syntomic with a square relative global complete intersection presentation, and let
`(A, B) → (A', B')` be a square of rings which is good for the naive cotangent complex. This file
proves that the maps of Remark 0FL9 with values in `det(NL)` (`Stacks.DeRham.presentationDetNLMap`)
of `B/A` and of `B'/A'` are compatible, for any two presentations, with the maps on forms and the
base change map of determinants (`NaiveCotangent.detNLMap`), in the following cases:

* `B'` is the pushout `A' ⊗_A B` (`presentationDetNLMap_naturality_of_isPushout`);
* `A' = A` and `B'` is a localization `B[1/g]`
  (`presentationDetNLMap_naturality_of_isLocalizationAway`);
* `B'` is a localization `(A' ⊗_A B)[1/g]` of the pushout
  (`presentationDetNLMap_naturality_of_isPushout_of_isLocalizationAway`);
* `A' = A[1/a]` and `B' = B[1/g]`
  (`presentationDetNLMap_naturality_of_isLocalizationAway_of_isLocalizationAway`).

## References

* [Stacks Project, Tag 0H9F](https://stacks.math.columbia.edu/tag/0H9F)
* [Stacks Project, Tag 0H9H](https://stacks.math.columbia.edu/tag/0H9H)
* [Stacks Project, Tag 00SS](https://stacks.math.columbia.edu/tag/00SS)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Stacks.DeRham

/-- A linear map which carries a basis to a basis of a module over a larger ring induces an
isomorphism of the base change with the target. -/
theorem bijective_liftBaseChange_of_basis {R S M N ι : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (f : M →ₗ[R] N) (b : Module.Basis ι R M) (b' : Module.Basis ι S N)
    (h : ∀ i, f (b i) = b' i) : Function.Bijective (f.liftBaseChange S) := by
  let b₁ := Algebra.TensorProduct.basis S b
  let e := b₁.equiv b' (Equiv.refl _)
  have : f.liftBaseChange S = e.toLinearMap := by
    refine b₁.ext fun i => ?_
    have he : e (b₁ i) = b' i := by
      rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    rw [LinearEquiv.coe_coe, he, Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul,
      one_smul]
    exact h i
  rw [this]
  exact e.bijective

/-- `aeval` of the variables of a polynomial ring over a larger ring is the map of
coefficients. -/
theorem aeval_X_eq_map {σ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : MvPolynomial σ R) :
    MvPolynomial.aeval (R := R) (MvPolynomial.X : σ → MvPolynomial σ S) p =
      MvPolynomial.map (algebraMap R S) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X]

section Pushout

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A B A' B'] {n : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin n))

variable (A' B')

/-- The base change of a presentation of `B` over `A` to a presentation of the pushout
`B' = A' ⊗_A B` over `A'`. -/
noncomputable def pushoutPresentation : Algebra.Presentation A' B' (Fin n) (Fin n) :=
  haveI : Algebra.IsPushout A A' B B' := Algebra.IsPushout.symm inferInstance
  (P.baseChange A').ofAlgEquiv (Algebra.IsPushout.equiv A A' B B')

/-- The variables of the base changed presentation evaluate to the images in `B'` of the values
of the variables of `P`. -/
theorem pushoutPresentation_val (i : Fin n) :
    (pushoutPresentation A' B' P).val i = algebraMap B B' (P.val i) := by
  have : Algebra.IsPushout A A' B B' := Algebra.IsPushout.symm inferInstance
  change Algebra.IsPushout.equiv A A' B B' (1 ⊗ₜ P.val i) = _
  rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]

/-- The relations of the base changed presentation are the images of the relations of `P` under
the map of coefficients `A → A'`. -/
theorem pushoutPresentation_relation (i : Fin n) :
    (pushoutPresentation A' B' P).relation i = MvPolynomial.map (algebraMap A A') (P.relation i) :=
  rfl

/-- The morphism from a presentation to its base change to the pushout. -/
noncomputable def pushoutHom : P.toGenerators.Hom (pushoutPresentation A' B' P).toGenerators where
  val := MvPolynomial.X
  aeval_val i := by
    rw [MvPolynomial.aeval_X, pushoutPresentation_val]

/-- On polynomial rings, the morphism `pushoutHom` is the map of coefficients `A → A'`. -/
theorem pushoutHom_toRingHom (q : P.toExtension.Ring) :
    (pushoutHom A' B' P).toExtensionHom.toRingHom q = MvPolynomial.map (algebraMap A A') q :=
  aeval_X_eq_map q

/-- The morphism `pushoutHom` carries each relation of `P` to the corresponding relation of the
base changed presentation. -/
theorem pushoutHom_relation (i : Fin n) :
    (pushoutHom A' B' P).toExtensionHom.toRingHom (P.relation i) =
      (pushoutPresentation A' B' P).relation i :=
  pushoutHom_toRingHom A' B' P _

/-- The base change of a square relative global complete intersection presentation is a relative
global complete intersection. -/
instance [P.IsRelativeGlobalCompleteIntersection] :
    (pushoutPresentation A' B' P).IsRelativeGlobalCompleteIntersection := by
  have : Algebra.QuasiFinite A B := Algebra.QuasiFinite.of_square_presentation
    (P := P) inferInstance rfl
  have : Algebra.IsPushout A A' B B' := Algebra.IsPushout.symm inferInstance
  have : Algebra.QuasiFinite A' B' :=
    (Algebra.QuasiFinite.iff_of_algEquiv (Algebra.IsPushout.equiv A A' B B')).mp inferInstance
  exact Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_quasiFinite _ rfl

variable {A' B'}

omit [Algebra.IsPushout A B A' B'] in
/-- A morphism of presentations sending variables to variables induces an isomorphism of the
base changed cotangent space with the cotangent space. -/
theorem bijective_liftBaseChange_cotangentSpaceMap_of_X
    {P : Algebra.Presentation A B (Fin n) (Fin n)}
    {P' : Algebra.Presentation A' B' (Fin n) (Fin n)} (Φ : P.toGenerators.Hom P'.toGenerators)
    (hΦ : ∀ i, Φ.val i = MvPolynomial.X i) :
    Function.Bijective ((Algebra.Extension.CotangentSpace.map Φ.toExtensionHom).liftBaseChange
      B') := by
  refine bijective_liftBaseChange_of_basis _ (Algebra.Generators.cotangentSpaceBasis P.toGenerators)
    (Algebra.Generators.cotangentSpaceBasis P'.toGenerators) fun i => ?_
  rw [Algebra.Generators.cotangentSpaceBasis_apply, Algebra.Generators.cotangentSpaceBasis_apply]
  refine (Algebra.Extension.CotangentSpace.map_tmul Φ.toExtensionHom (1 : B)
    (MvPolynomial.X i : P.toExtension.Ring)).trans ?_
  rw [map_one]
  exact congrArg (fun q => (1 : B') ⊗ₜ[P'.toExtension.Ring] KaehlerDifferential.D A'
    P'.toExtension.Ring q) ((Algebra.Generators.Hom.toAlgHom_X Φ i).trans (hΦ i))

variable (A' B')

variable [P.IsRelativeGlobalCompleteIntersection]

/-- The map of conormal modules induced by `pushoutHom` becomes an isomorphism after base change
to `B'`. -/
theorem bijective_liftBaseChange_cotangentMap_pushoutHom :
    Function.Bijective ((Algebra.Extension.Cotangent.map (pushoutHom A' B' P).toExtensionHom
      ).liftBaseChange B') :=
  bijective_liftBaseChange_cotangentMap (pushoutHom_relation A' B' P)

omit [P.IsRelativeGlobalCompleteIntersection] in
/-- The map of cotangent spaces induced by `pushoutHom` becomes an isomorphism after base change
to `B'`. -/
theorem bijective_liftBaseChange_cotangentSpaceMap_pushoutHom :
    Function.Bijective ((Algebra.Extension.CotangentSpace.map (pushoutHom A' B' P).toExtensionHom
      ).liftBaseChange B') :=
  bijective_liftBaseChange_cotangentSpaceMap_of_X _ fun _ => rfl

include P in
variable (A B) in
/-- The square of a pushout `B' = A' ⊗_A B` of an algebra with a square relative global complete
intersection presentation is good for the naive cotangent complex. -/
theorem isGoodSquare_of_isPushout : NaiveCotangent.IsGoodSquare A B A' B' :=
  NaiveCotangent.isGoodSquare_of_isQuasiIso P.toExtension (pushoutPresentation A' B' P).toExtension
    (P.toGenerators.defaultHom (Algebra.Generators.self A B)).toExtensionHom
    ((pushoutPresentation A' B' P).toGenerators.defaultHom (Algebra.Generators.self A' B')
      ).toExtensionHom (pushoutHom A' B' P).toExtensionHom
    (NaiveCotangent.isQuasiIso_of_bijective _
      (bijective_liftBaseChange_cotangentMap_pushoutHom A' B' P)
      (bijective_liftBaseChange_cotangentSpaceMap_pushoutHom A' B' P))

variable [Algebra.Syntomic A B] [Algebra.Syntomic A' B']

/-- **The maps of Remark 0FL9 commute with base change** (Stacks, proof of Lemma 0H9H): for
the pushout `B' = A' ⊗_A B` and any square relative global complete intersection presentations `P`
of `B` over `A` and `P'` of `B'` over `A'`, the maps of Remark 0FL9 with values in `det(NL)`
commute with the maps on forms and the base change map of determinants. -/
theorem presentationDetNLMap_naturality_of_isPushout (hsq : NaiveCotangent.IsGoodSquare A B A' B')
    {n' : ℕ} (P' : Algebra.Presentation A' B' (Fin n') (Fin n'))
    [P'.IsRelativeGlobalCompleteIntersection] (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]) :
    presentationDetNLMap P' p (ExteriorAlgebra.powMapₛₗ p (algebraMap B B') (kaehlerMapₛₗ B B') η) =
      TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ p (algebraMap B B') (formsBaseChangeMapₛₗ A B A' B'))
        (NaiveCotangent.detNLMap hsq) (presentationDetNLMap P p η) := by
  rw [presentationDetNLMap_eq P' (pushoutPresentation A' B' P)]
  exact presentationDetNLMap_naturality hsq (Φ := (pushoutHom A' B' P).toExtensionHom)
    (bijective_liftBaseChange_cotangentMap_pushoutHom A' B' P)
    (bijective_liftBaseChange_cotangentSpaceMap_pushoutHom A' B' P) p η

end Pushout

/-- A chain map of two-term complexes which is a quasi-isomorphism and bijective in degree `0` is
bijective in degree `1`. -/
theorem bijective_f₁_of_isQuasiIso {S : Type*} [CommRing S] {X Y : NaiveCotangent.TwoTerm S}
    (f : NaiveCotangent.ChainMap X Y) (hq : NaiveCotangent.IsQuasiIso f)
    (h₀ : Function.Bijective f.f₀) : Function.Bijective f.f₁ := by
  refine ⟨fun x x' hxx' => ?_, fun y => ?_⟩
  · have hd : X.d (x - x') = 0 := by
      apply h₀.1
      rw [← NaiveCotangent.chainMap_comm_apply, map_sub, hxx', sub_self, map_zero, map_zero]
    have hk : f.onH₁ ⟨x - x', hd⟩ = 0 := Subtype.ext (by
      rw [NaiveCotangent.onH₁_apply_coe]
      change f.f₁ (x - x') = 0
      rw [map_sub, hxx', sub_self])
    have := congrArg Subtype.val ((map_eq_zero_iff _ hq.1.1).mp hk)
    exact sub_eq_zero.mp this
  · obtain ⟨z, hz⟩ := h₀.2 (Y.d y)
    have hzq : f.onH₀ (Submodule.Quotient.mk z) = 0 := by
      rw [NaiveCotangent.onH₀_mk, hz, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, rfl⟩
    have hz0 := (map_eq_zero_iff _ hq.2.1).mp hzq
    rw [Submodule.Quotient.mk_eq_zero] at hz0
    obtain ⟨x, rfl⟩ := hz0
    have hk : Y.d (f.f₁ x - y) = 0 := by
      rw [map_sub, NaiveCotangent.chainMap_comm_apply, hz, sub_self]
    obtain ⟨w, hw⟩ := hq.1.2 ⟨f.f₁ x - y, hk⟩
    have hw' : f.f₁ (w : X.X₁) = f.f₁ x - y := by
      rw [← NaiveCotangent.onH₁_apply_coe, hw]
    exact ⟨x - w, by rw [map_sub, hw', sub_sub_cancel]⟩

section Localization

variable {R C C' : Type u} [CommRing R] [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C']
  [Algebra C C'] [IsScalarTower R C C'] (g : C) [IsLocalization.Away g C'] {n : ℕ}
  (Q : Algebra.Presentation R C (Fin n) (Fin n))

/-- The presentation `R[t, x_1, …, x_n]/(t - 1, f_1, …, f_n)` of `C` with a redundant variable,
from a presentation `R[x_1, …, x_n]/(f_1, …, f_n)`. -/
noncomputable def addVariablePresentation : Algebra.Presentation R C (Fin (1 + n)) (Fin (1 + n)) :=
  ((selfPresentation (fun _ : Fin 1 => (1 : C))).comp Q).reindex finSumFinEquiv.symm
    finSumFinEquiv.symm

/-- The redundant variable `t` of `addVariablePresentation Q` evaluates to `1`, and the others to
the values of the variables of `Q`. -/
theorem addVariablePresentation_val (k : Fin (1 + n)) :
    (addVariablePresentation Q).val k = Sum.elim (fun _ => 1) Q.val (finSumFinEquiv.symm k) := by
  change ((selfPresentation (fun _ : Fin 1 => (1 : C))).toGenerators.comp Q.toGenerators).val
    (finSumFinEquiv.symm k) = _
  rcases finSumFinEquiv.symm k with j | i <;> rfl

/-- The equivalence `Fin (1 + n) ≃ Unit ⊕ Fin n`. -/
def finOneAddEquiv : Fin (1 + n) ≃ Unit ⊕ Fin n :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.equivPUnit (Fin 1)) (Equiv.refl _))

variable (C') in
/-- The presentation `R[t, x_1, …, x_n]/(g t - 1, f_1, …, f_n)` of the localization `C[1/g]`. -/
noncomputable def localizationPresentation :
    Algebra.Presentation R C' (Fin (1 + n)) (Fin (1 + n)) :=
  ((Algebra.Presentation.localizationAway C' g).comp Q).reindex finOneAddEquiv finOneAddEquiv

/-- The variable `t` of `localizationPresentation C' g Q` evaluates to `1/g`, and the others to
the images in `C'` of the values of the variables of `Q`. -/
theorem localizationPresentation_val (k : Fin (1 + n)) :
    (localizationPresentation C' g Q).val k =
      Sum.elim (fun _ => IsLocalization.Away.invSelf g) (fun i => algebraMap C C' (Q.val i))
        (finOneAddEquiv k) := by
  change ((Algebra.Presentation.localizationAway C' g).toGenerators.comp Q.toGenerators).val
    (finOneAddEquiv k) = _
  rcases finOneAddEquiv k with j | i <;> rfl

/-- The lift of `g` to the polynomial ring of the presentation of `C[1/g]` evaluates to `g`. -/
theorem aeval_localizationPresentation_rename_σ :
    MvPolynomial.aeval (localizationPresentation C' g Q).val
      (MvPolynomial.rename (fun i => finOneAddEquiv.symm (Sum.inr i)) (Q.σ g)) =
      algebraMap C C' g := by
  rw [MvPolynomial.aeval_rename]
  have hv : ((localizationPresentation C' g Q).val ∘ fun i => finOneAddEquiv.symm (Sum.inr i)) =
      ⇑(IsScalarTower.toAlgHom R C C') ∘ Q.val := funext fun i => by
    simp [localizationPresentation_val]
  have := (MvPolynomial.comp_aeval_apply (f := Q.val) (IsScalarTower.toAlgHom R C C')
    (Q.σ g)).symm
  rw [Q.aeval_val_σ, IsScalarTower.coe_toAlgHom'] at this
  rw [hv]
  exact this

/-- The morphism of presentations `t ↦ g t`, `x_i ↦ x_i` from the presentation of `C` with a
redundant variable to the presentation of `C[1/g]`. -/
noncomputable def localizationHom :
    (addVariablePresentation Q).toGenerators.Hom
      (localizationPresentation C' g Q).toGenerators where
  val k := Sum.elim
    (fun _ => MvPolynomial.rename (fun i => finOneAddEquiv.symm (Sum.inr i)) (Q.σ g) *
      MvPolynomial.X (finOneAddEquiv.symm (Sum.inl ())))
    (fun i => MvPolynomial.X (finOneAddEquiv.symm (Sum.inr i))) (finSumFinEquiv.symm k)
  aeval_val k := by
    rw [addVariablePresentation_val]
    rcases finSumFinEquiv.symm k with j | i
    · rw [Sum.elim_inl, map_mul, aeval_localizationPresentation_rename_σ, MvPolynomial.aeval_X,
        localizationPresentation_val, Equiv.apply_symm_apply, Sum.elim_inl,
        IsLocalization.Away.mul_invSelf, Sum.elim_inl, map_one]
    · simp only [Sum.elim_inr, MvPolynomial.aeval_X, localizationPresentation_val,
        Equiv.apply_symm_apply]

/-- A surjective linear map between free modules with bases indexed by the same finite type is
bijective. -/
theorem bijective_of_surjective_of_basis {S M N ι : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module S N] [Finite ι] (b : Module.Basis ι S M)
    (b' : Module.Basis ι S N) (F : M →ₗ[S] N) (hF : Function.Surjective F) :
    Function.Bijective F := by
  have : Module.Finite S M := Module.Finite.of_basis b
  let ε := b'.equiv b (Equiv.refl ι)
  have h := OrzechProperty.injective_of_surjective_endomorphism (ε.toLinearMap ∘ₗ F)
    (ε.surjective.comp hF)
  exact ⟨fun x y hxy => h (by simp [hxy]), hF⟩

/-- The map of cotangent spaces induced by `localizationHom` becomes an isomorphism after base
change to `C'`. -/
theorem bijective_liftBaseChange_cotangentSpaceMap_localizationHom :
    Function.Bijective ((Algebra.Extension.CotangentSpace.map
      (localizationHom (C' := C') g Q).toExtensionHom).liftBaseChange C') := by
  classical
  set b₁ := Algebra.Generators.cotangentSpaceBasis (addVariablePresentation Q).toGenerators
  set b₂ := Algebra.Generators.cotangentSpaceBasis (localizationPresentation C' g Q).toGenerators
  set F := (Algebra.Extension.CotangentSpace.map
    (localizationHom (C' := C') g Q).toExtensionHom).liftBaseChange C'
  have hF : ∀ k, F (1 ⊗ₜ b₁ k) = Algebra.Extension.CotangentSpace.map
      (localizationHom (C' := C') g Q).toExtensionHom (b₁ k) := fun k => by
    rw [LinearMap.liftBaseChange_tmul, one_smul]
  set k₀ : Fin (1 + n) := finOneAddEquiv.symm (Sum.inl ())
  have hinr : ∀ i : Fin n, b₂ (finOneAddEquiv.symm (Sum.inr i)) ∈ LinearMap.range F := by
    intro i
    refine ⟨1 ⊗ₜ b₁ (finSumFinEquiv (Sum.inr i)), ?_⟩
    rw [hF]
    refine b₂.repr.injective (Finsupp.ext fun j => ?_)
    rw [Algebra.Generators.repr_CotangentSpaceMap, Module.Basis.repr_self]
    simp only [localizationHom, Equiv.symm_apply_apply, Sum.elim_inr, MvPolynomial.pderiv_X]
    by_cases hj : j = finOneAddEquiv.symm (Sum.inr i)
    · subst hj; simp
    · simp [hj, Ne.symm hj]
  have hv : b₂.repr (F (1 ⊗ₜ b₁ (finSumFinEquiv (Sum.inl 0)))) k₀ = algebraMap C C' g := by
    rw [hF, Algebra.Generators.repr_CotangentSpaceMap]
    simp only [localizationHom, Equiv.symm_apply_apply, Sum.elim_inl]
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, mul_one,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars, zero_mul, zero_add]
    · exact aeval_localizationPresentation_rename_σ g Q
    · intro hk
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (MvPolynomial.vars_rename _ _ hk)
      exact Sum.inr_ne_inl (finOneAddEquiv.symm.injective hi)
  have hk₀ : b₂ k₀ ∈ LinearMap.range F := by
    set v := F (1 ⊗ₜ b₁ (finSumFinEquiv (Sum.inl 0))) with hvdef
    have hsum := b₂.sum_repr v
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀), hv] at hsum
    have hrest : ∑ j ∈ Finset.univ.erase k₀, b₂.repr v j • b₂ j ∈ LinearMap.range F := by
      refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
      have hj' : j ≠ k₀ := Finset.ne_of_mem_erase hj
      obtain ⟨i, rfl⟩ : ∃ i, finOneAddEquiv.symm (Sum.inr i) = j := by
        rcases h : finOneAddEquiv j with u | i
        · exact absurd (by rw [← finOneAddEquiv.symm_apply_apply j, h]) hj'
        · exact ⟨i, by rw [← h, Equiv.symm_apply_apply]⟩
      exact hinr i
    have hmem : algebraMap C C' g • b₂ k₀ ∈ LinearMap.range F := by
      have : algebraMap C C' g • b₂ k₀ = v - ∑ j ∈ Finset.univ.erase k₀, b₂.repr v j • b₂ j := by
        rw [eq_sub_iff_add_eq, hsum]
      rw [this]
      exact Submodule.sub_mem _ ⟨_, rfl⟩ hrest
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := C') g
    have := Submodule.smul_mem _ (↑u⁻¹ : C') hmem
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at this
  have hall : ∀ k, b₂ k ∈ LinearMap.range F := by
    intro k
    rcases h : finOneAddEquiv k with u | i
    · have : k = k₀ := by rw [← finOneAddEquiv.symm_apply_apply k, h]
      rw [this]; exact hk₀
    · rw [← finOneAddEquiv.symm_apply_apply k, h]; exact hinr i
  refine bijective_of_surjective_of_basis (Algebra.TensorProduct.basis C' b₁) b₂ F ?_
  rw [← LinearMap.range_eq_top, eq_top_iff, ← b₂.span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact hall k

/-- Adding a redundant variable to a square relative global complete intersection presentation
gives a relative global complete intersection. -/
instance [Q.IsRelativeGlobalCompleteIntersection] :
    (addVariablePresentation Q).IsRelativeGlobalCompleteIntersection :=
  haveI : Algebra.QuasiFinite R C := Algebra.QuasiFinite.of_square_presentation
    (P := Q) inferInstance rfl
  Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_quasiFinite _ rfl

/-- If `C[1/g]` is quasi-finite over `R`, its presentation `localizationPresentation C' g Q` is a
relative global complete intersection. -/
instance [Algebra.QuasiFinite R C'] :
    (localizationPresentation C' g Q).IsRelativeGlobalCompleteIntersection :=
  Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_quasiFinite _ rfl

variable [Q.IsRelativeGlobalCompleteIntersection] [Algebra.QuasiFinite R C']
  [Algebra.Syntomic R C] [Algebra.Syntomic R C']

include g in
/-- **The maps of Remark 0FL9 commute with localization of the algebra**: for `C' = C[1/g]` and any
square relative global complete intersection presentations `Q` of `C` and `Q'` of `C'` over `R`,
the maps of Remark 0FL9 with values in `det(NL)` commute with the maps on forms and the base change
map of determinants. -/
theorem presentationDetNLMap_naturality_of_isLocalizationAway
    (hsq : NaiveCotangent.IsGoodSquare R C R C') {n' : ℕ}
    (Q' : Algebra.Presentation R C' (Fin n') (Fin n')) [Q'.IsRelativeGlobalCompleteIntersection]
    (p : ℕ) (η : ⋀[C]^p Ω[C⁄ℤ]) :
    presentationDetNLMap Q' p (ExteriorAlgebra.powMapₛₗ p (algebraMap C C') (kaehlerMapₛₗ C C') η) =
      TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ p (algebraMap C C') (formsBaseChangeMapₛₗ R C R C'))
        (NaiveCotangent.detNLMap hsq) (presentationDetNLMap Q p η) := by
  rw [presentationDetNLMap_eq Q' (localizationPresentation C' g Q),
    presentationDetNLMap_eq Q (addVariablePresentation Q)]
  have hzero := bijective_liftBaseChange_cotangentSpaceMap_localizationHom (C' := C') g Q
  have hq := NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_isGoodSquare hsq
    (addVariablePresentation Q).toExtension (localizationPresentation C' g Q).toExtension
    ((addVariablePresentation Q).toGenerators.defaultHom (Algebra.Generators.self R C)
      ).toExtensionHom
    ((localizationPresentation C' g Q).toGenerators.defaultHom (Algebra.Generators.self R C')
      ).toExtensionHom (localizationHom g Q).toExtensionHom
  exact presentationDetNLMap_naturality hsq (Φ := (localizationHom g Q).toExtensionHom)
    (bijective_f₁_of_isQuasiIso _ hq hzero) hzero p η

end Localization

/-! ### Composing compatibilities -/

/-- Tensor products of semilinear maps compose. -/
theorem map_map_eq_map {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
    {σ₁ : R₀ →+* R₁} {σ₂ : R₁ →+* R₂} {σ : R₀ →+* R₂}
    {M₀ T₀ : Type*} [AddCommGroup M₀] [Module R₀ M₀] [AddCommGroup T₀] [Module R₀ T₀]
    {M₁ T₁ : Type*} [AddCommGroup M₁] [Module R₁ M₁] [AddCommGroup T₁] [Module R₁ T₁]
    {M₂ T₂ : Type*} [AddCommGroup M₂] [Module R₂ M₂] [AddCommGroup T₂] [Module R₂ T₂]
    (f₁ : M₀ →ₛₗ[σ₁] M₁) (g₁ : T₀ →ₛₗ[σ₁] T₁) (f₂ : M₁ →ₛₗ[σ₂] M₂) (g₂ : T₁ →ₛₗ[σ₂] T₂)
    (f : M₀ →ₛₗ[σ] M₂) (g : T₀ →ₛₗ[σ] T₂) (hf : ∀ x, f₂ (f₁ x) = f x) (hg : ∀ t, g₂ (g₁ t) = g t)
    (u : M₀ ⊗[R₀] T₀) :
    TensorProduct.map f₂ g₂ (TensorProduct.map f₁ g₁ u) = TensorProduct.map f g u := by
  induction u using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x t => rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, hf, hg]

/-- The maps `Ω[B⁄ℤ] → Ω[B'⁄ℤ]` compose along towers. -/
theorem kaehlerMapₛₗ_comp {B C B' : Type u} [CommRing B] [CommRing C] [CommRing B'] [Algebra B C]
    [Algebra C B'] [Algebra B B'] [IsScalarTower B C B'] (y : Ω[B⁄ℤ]) :
    kaehlerMapₛₗ C B' (kaehlerMapₛₗ B C y) = kaehlerMapₛₗ B B' y := by
  have hy : y ∈ Submodule.span B (Set.range (KaehlerDifferential.D ℤ B)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    rw [kaehlerMapₛₗ_D, kaehlerMapₛₗ_D, kaehlerMapₛₗ_D, ← IsScalarTower.algebraMap_apply]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul a x _ hx => rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hx, ← IsScalarTower.algebraMap_apply]

/-- The maps of base changed differentials compose along two squares. -/
theorem formsBaseChangeMapₛₗ_comp {A B A₁ B₁ A₂ B₂ : Type u} [CommRing A] [CommRing B]
    [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂] [Algebra A B] [Algebra A₁ B₁]
    [Algebra A₂ B₂] [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [IsScalarTower A A₁ B₁]
    [IsScalarTower A B B₁] [Algebra A₁ A₂] [Algebra B₁ B₂] [Algebra A₁ B₂] [IsScalarTower A₁ A₂ B₂]
    [IsScalarTower A₁ B₁ B₂] [Algebra A A₂] [Algebra B B₂] [Algebra A B₂] [IsScalarTower A A₂ B₂]
    [IsScalarTower A B B₂] [IsScalarTower A A₁ A₂] [IsScalarTower B B₁ B₂]
    (x : B ⊗[A] Ω[A⁄ℤ]) :
    formsBaseChangeMapₛₗ A₁ B₁ A₂ B₂ (formsBaseChangeMapₛₗ A B A₁ B₁ x) =
      formsBaseChangeMapₛₗ A B A₂ B₂ x := by
  refine tensorKaehler_induction (R := A) (S := B) (motive := fun x =>
    formsBaseChangeMapₛₗ A₁ B₁ A₂ B₂ (formsBaseChangeMapₛₗ A B A₁ B₁ x) =
      formsBaseChangeMapₛₗ A B A₂ B₂ x) x (by simp only [map_zero])
    (fun x y hx hy => by simp only [map_add, hx, hy]) (fun b a => ?_)
  rw [formsBaseChangeMapₛₗ_tmul, KaehlerDifferential.map_D, formsBaseChangeMapₛₗ_tmul,
    KaehlerDifferential.map_D, formsBaseChangeMapₛₗ_tmul, KaehlerDifferential.map_D,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- Compatibilities of maps out of tensor products compose. -/
theorem compat_comp {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
    {σ₁ : R₀ →+* R₁} {σ₂ : R₁ →+* R₂} {σ : R₀ →+* R₂}
    {H₀ M₀ T₀ : Type*} [AddCommGroup H₀] [Module R₀ H₀] [AddCommGroup M₀] [Module R₀ M₀]
    [AddCommGroup T₀] [Module R₀ T₀]
    {H₁ M₁ T₁ : Type*} [AddCommGroup H₁] [Module R₁ H₁] [AddCommGroup M₁] [Module R₁ M₁]
    [AddCommGroup T₁] [Module R₁ T₁]
    {H₂ M₂ T₂ : Type*} [AddCommGroup H₂] [Module R₂ H₂] [AddCommGroup M₂] [Module R₂ M₂]
    [AddCommGroup T₂] [Module R₂ T₂]
    (c₀ : H₀ → M₀ ⊗[R₀] T₀) (c₁ : H₁ → M₁ ⊗[R₁] T₁) (c₂ : H₂ → M₂ ⊗[R₂] T₂)
    (k₁ : H₀ → H₁) (k₂ : H₁ → H₂) (k : H₀ → H₂)
    (f₁ : M₀ →ₛₗ[σ₁] M₁) (g₁ : T₀ →ₛₗ[σ₁] T₁) (f₂ : M₁ →ₛₗ[σ₂] M₂) (g₂ : T₁ →ₛₗ[σ₂] T₂)
    (f : M₀ →ₛₗ[σ] M₂) (g : T₀ →ₛₗ[σ] T₂)
    (h₁ : ∀ η, c₁ (k₁ η) = TensorProduct.map f₁ g₁ (c₀ η))
    (h₂ : ∀ ξ, c₂ (k₂ ξ) = TensorProduct.map f₂ g₂ (c₁ ξ)) (hk : ∀ η, k₂ (k₁ η) = k η)
    (hf : ∀ x, f₂ (f₁ x) = f x) (hg : ∀ t, g₂ (g₁ t) = g t) (η : H₀) :
    c₂ (k η) = TensorProduct.map f g (c₀ η) := by
  rw [← hk, h₂, h₁, map_map_eq_map f₁ g₁ f₂ g₂ f g hf hg]

/-- The naturality of the maps of Remark 0FL9 composes along two good squares. -/
private theorem presentationDetNLMap_naturality_comp
    {A B A₁ B₁ A₂ B₂ : Type u} [CommRing A] [CommRing B] [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A B] [Algebra A₁ B₁] [Algebra A₂ B₂] [Algebra A A₁]
    [Algebra B B₁] [Algebra A B₁] [IsScalarTower A A₁ B₁] [IsScalarTower A B B₁] [Algebra A₁ A₂]
    [Algebra B₁ B₂] [Algebra A₁ B₂] [IsScalarTower A₁ A₂ B₂] [IsScalarTower A₁ B₁ B₂]
    [Algebra A A₂] [Algebra B B₂] [Algebra A B₂] [IsScalarTower A A₂ B₂] [IsScalarTower A B B₂]
    [IsScalarTower A A₁ A₂] [IsScalarTower B B₁ B₂] [Algebra.Syntomic A B]
    [Algebra.Syntomic A₁ B₁] [Algebra.Syntomic A₂ B₂] {n₀ n₁ n₂ : ℕ}
    (P₀ : Algebra.Presentation A B (Fin n₀) (Fin n₀))
    (P₁ : Algebra.Presentation A₁ B₁ (Fin n₁) (Fin n₁))
    (P₂ : Algebra.Presentation A₂ B₂ (Fin n₂) (Fin n₂))
    [P₀.IsRelativeGlobalCompleteIntersection] [P₁.IsRelativeGlobalCompleteIntersection]
    [P₂.IsRelativeGlobalCompleteIntersection]
    (hsq₁ : NaiveCotangent.IsGoodSquare A B A₁ B₁)
    (hsq₂ : NaiveCotangent.IsGoodSquare A₁ B₁ A₂ B₂) (hsq : NaiveCotangent.IsGoodSquare A B A₂ B₂)
    (p : ℕ)
    (h₁ : ∀ η : ⋀[B]^p Ω[B⁄ℤ], presentationDetNLMap P₁ p
      (ExteriorAlgebra.powMapₛₗ p (algebraMap B B₁) (kaehlerMapₛₗ B B₁) η) = TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ p (algebraMap B B₁) (formsBaseChangeMapₛₗ A B A₁ B₁))
        (NaiveCotangent.detNLMap hsq₁) (presentationDetNLMap P₀ p η))
    (h₂ : ∀ η : ⋀[B₁]^p Ω[B₁⁄ℤ], presentationDetNLMap P₂ p
      (ExteriorAlgebra.powMapₛₗ p (algebraMap B₁ B₂) (kaehlerMapₛₗ B₁ B₂) η) = TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ p (algebraMap B₁ B₂) (formsBaseChangeMapₛₗ A₁ B₁ A₂ B₂))
        (NaiveCotangent.detNLMap hsq₂) (presentationDetNLMap P₁ p η))
    (η : ⋀[B]^p Ω[B⁄ℤ]) :
    presentationDetNLMap P₂ p
      (ExteriorAlgebra.powMapₛₗ p (algebraMap B B₂) (kaehlerMapₛₗ B B₂) η) =
      TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ p (algebraMap B B₂) (formsBaseChangeMapₛₗ A B A₂ B₂))
        (NaiveCotangent.detNLMap hsq) (presentationDetNLMap P₀ p η) :=
  compat_comp (presentationDetNLMap P₀ p) (presentationDetNLMap P₁ p) (presentationDetNLMap P₂ p)
    (ExteriorAlgebra.powMapₛₗ p (algebraMap B B₁) (kaehlerMapₛₗ B B₁))
    (ExteriorAlgebra.powMapₛₗ p (algebraMap B₁ B₂) (kaehlerMapₛₗ B₁ B₂))
    (ExteriorAlgebra.powMapₛₗ p (algebraMap B B₂) (kaehlerMapₛₗ B B₂))
    (ExteriorAlgebra.powMapₛₗ p (algebraMap B B₁) (formsBaseChangeMapₛₗ A B A₁ B₁))
    (NaiveCotangent.detNLMap hsq₁)
    (ExteriorAlgebra.powMapₛₗ p (algebraMap B₁ B₂) (formsBaseChangeMapₛₗ A₁ B₁ A₂ B₂))
    (NaiveCotangent.detNLMap hsq₂)
    (ExteriorAlgebra.powMapₛₗ p (algebraMap B B₂) (formsBaseChangeMapₛₗ A B A₂ B₂))
    (NaiveCotangent.detNLMap hsq) h₁ h₂
    (fun η => (ExteriorAlgebra.powMapₛₗ_eq_comp p _ _ _
      (fun r => IsScalarTower.algebraMap_apply B B₁ B₂ r)
      (fun m => (kaehlerMapₛₗ_comp m).symm) η).symm)
    (fun x => (ExteriorAlgebra.powMapₛₗ_eq_comp p _ _ _
      (fun r => IsScalarTower.algebraMap_apply B B₁ B₂ r)
      (fun m => (formsBaseChangeMapₛₗ_comp m).symm) x).symm)
    (fun t => NaiveCotangent.detNLMap_detNLMap hsq₁ hsq₂ hsq t) η

/-! ### Localizations of pushouts -/

/-- A square whose lower right corner is a localization of the upper right corner, over the same
base, is good for the naive cotangent complex. -/
theorem isGoodSquare_of_isLocalizationAway {R C C' : Type u} [CommRing R] [CommRing C]
    [CommRing C'] [Algebra R C] [Algebra R C'] [Algebra C C'] [IsScalarTower R C C'] (g : C)
    [IsLocalization.Away g C'] : NaiveCotangent.IsGoodSquare R C R C' := by
  have : IsLocalization (⊥ : Submonoid R) R := IsLocalization.self bot_le
  intro k
  exact NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization_of_isLocalization
    (Submonoid.powers g) (⊥ : Submonoid R) k

section PushoutLocalization

variable {A B A' C B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing C]
  [CommRing B'] [Algebra A B] [Algebra A A'] [Algebra A' C] [Algebra B C] [Algebra A C]
  [IsScalarTower A A' C] [IsScalarTower A B C] [Algebra.IsPushout A B A' C]
  [Algebra C B'] [Algebra A' B'] [IsScalarTower A' C B'] (g : C) [IsLocalization.Away g B']
  [Algebra B B'] [IsScalarTower B C B'] [Algebra A B'] [IsScalarTower A A' B']
  [IsScalarTower A B B'] {n : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin n))
  [P.IsRelativeGlobalCompleteIntersection] [Algebra.Syntomic A B] [Algebra.Syntomic A' B']
  [Algebra.QuasiFinite A' B']

include g P in
omit [Algebra.Syntomic A' B'] [Algebra.QuasiFinite A' B'] in
/-- A localization `(A' ⊗_A B)[1/g]` of a pushout of an algebra with a square relative global
complete intersection presentation gives a good square for the naive cotangent complex. -/
theorem isGoodSquare_of_isPushout_of_isLocalizationAway :
    NaiveCotangent.IsGoodSquare A B A' B' := by
  have : Algebra.Syntomic A' C :=
    have : Algebra.IsRelativeGlobalCompleteIntersection A' C :=
      ⟨⟨n, n, pushoutPresentation A' C P, inferInstance⟩⟩
    Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection A' C
  exact (isGoodSquare_of_isPushout A B A' C P).trans (isGoodSquare_of_isLocalizationAway g)

include g in
/-- **The maps of Remark 0FL9 along a localization of a pushout** (Stacks, proof of Lemma 0H9H):
for `B' = (A' ⊗_A B)[1/g]` and any square relative global complete intersection presentations `P`
of `B` over `A` and `P'` of `B'` over `A'`, the maps of Remark 0FL9 with values in `det(NL)`
commute with the maps on forms and the base change map of determinants. -/
theorem presentationDetNLMap_naturality_of_isPushout_of_isLocalizationAway
    (hsq : NaiveCotangent.IsGoodSquare A B A' B') {n' : ℕ}
    (P' : Algebra.Presentation A' B' (Fin n') (Fin n')) [P'.IsRelativeGlobalCompleteIntersection]
    (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]) :
    presentationDetNLMap P' p (ExteriorAlgebra.powMapₛₗ p (algebraMap B B') (kaehlerMapₛₗ B B') η) =
      TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ p (algebraMap B B') (formsBaseChangeMapₛₗ A B A' B'))
        (NaiveCotangent.detNLMap hsq) (presentationDetNLMap P p η) := by
  have : Algebra.Syntomic A' C :=
    have : Algebra.IsRelativeGlobalCompleteIntersection A' C :=
      ⟨⟨n, n, pushoutPresentation A' C P, inferInstance⟩⟩
    Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection A' C
  have hsq₁ := isGoodSquare_of_isPushout A B A' C P
  have hsq₂ := isGoodSquare_of_isLocalizationAway (R := A') (C' := B') g
  exact presentationDetNLMap_naturality_comp P (pushoutPresentation A' C P) P' hsq₁ hsq₂ hsq p
    (presentationDetNLMap_naturality_of_isPushout A' C P hsq₁ (pushoutPresentation A' C P) p)
    (presentationDetNLMap_naturality_of_isLocalizationAway g (pushoutPresentation A' C P) hsq₂ P' p)
    η

end PushoutLocalization

/-! ### Localizations of the base and of the algebra -/

section Refinement

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] (a : A) [IsLocalization.Away a A'] (g : B)
  [IsLocalization.Away g B'] {n : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin n))
  [P.IsRelativeGlobalCompleteIntersection] [Algebra.Syntomic A B] [Algebra.Syntomic A' B']
  [Algebra.QuasiFinite A' B']

include a in
omit [Algebra.Syntomic A' B'] [Algebra.QuasiFinite A' B'] in
/-- If `A → A'` is a localization away from `a`, then an `A'`-algebra `B'` is its own pushout
`A' ⊗_A B'`. -/
theorem isPushout_self_of_isLocalizationAway : Algebra.IsPushout A B' A' B' := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B' (Submonoid.powers a)) B' := by
    refine IsLocalization.self ?_
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    rw [map_pow, IsScalarTower.algebraMap_apply A A' B']
    exact ((IsLocalization.Away.algebraMap_isUnit (S := A') a).map _).pow k
  exact Algebra.isPushout_of_isLocalization (Submonoid.powers a) A' B' B'

include a g in
omit [Algebra.QuasiFinite A' B'] in
/-- **The maps of Remark 0FL9 along localizations of the base and of the algebra**: for
`A' = A[1/a]`, `B' = B[1/g]` and any square relative global complete intersection presentations `P`
of `B` over `A` and `P'` of `B'` over `A'`, the maps of Remark 0FL9 with values in `det(NL)`
commute with the maps on forms and the base change map of determinants. -/
theorem presentationDetNLMap_naturality_of_isLocalizationAway_of_isLocalizationAway
    (hsq : NaiveCotangent.IsGoodSquare A B A' B') {n' : ℕ}
    (P' : Algebra.Presentation A' B' (Fin n') (Fin n')) [P'.IsRelativeGlobalCompleteIntersection]
    (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]) :
    presentationDetNLMap P' p (ExteriorAlgebra.powMapₛₗ p (algebraMap B B') (kaehlerMapₛₗ B B') η) =
      TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ p (algebraMap B B') (formsBaseChangeMapₛₗ A B A' B'))
        (NaiveCotangent.detNLMap hsq) (presentationDetNLMap P p η) := by
  have : Algebra.QuasiFinite A B' :=
    have : Algebra.QuasiFinite A B := Algebra.QuasiFinite.of_square_presentation
      (P := P) inferInstance rfl
    Algebra.QuasiFinite.of_isLocalization (Submonoid.powers g)
  have : Algebra.Syntomic A B' :=
    have : Algebra.IsRelativeGlobalCompleteIntersection A B' :=
      ⟨⟨1 + n, 1 + n, localizationPresentation B' g P, inferInstance⟩⟩
    Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection A B'
  have := isPushout_self_of_isLocalizationAway (B' := B') (A' := A') a
  let Q := localizationPresentation B' g P
  have hsq₁ := isGoodSquare_of_isLocalizationAway (R := A) (C' := B') g
  have hsq₂ := isGoodSquare_of_isPushout A B' A' B' Q
  exact presentationDetNLMap_naturality_comp P Q P' hsq₁ hsq₂ hsq p
    (presentationDetNLMap_naturality_of_isLocalizationAway g P hsq₁ Q p)
    (presentationDetNLMap_naturality_of_isPushout A' B' Q hsq₂ P' p) η

end Refinement

end Stacks.DeRham

end
