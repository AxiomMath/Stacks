module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsNaturality
public import StacksFrontier.AlgebraicGeometry.Duality.FunnyMapSurjectiveNaturality
public import StacksFrontier.AlgebraicGeometry.ImmersionEvaluationSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFinite

/-!
# The maps of Remark 0FL9 do not depend on the presentation

Let `B` be an `A`-algebra with square presentations `P` and `Q` which are relative global complete
intersections. The maps of Remark 0FL9 with values in `det(NL_{B/A})`
(`Stacks.DeRham.presentationDetNLMap`) attached to `P` and to `Q` agree.

The proof compares both with a common refinement `T` (`Stacks.DeRham.joinPresentation`), whose
variables are those of `Q` followed by those of `P`, along the two surjections of polynomial rings
`T → P` and `T → Q`. A surjective morphism of presentations is a morphism of the diagrams of
Tag 0FL8 which is an isomorphism on `B ⊗_A Ω_{A/ℤ}` and a degreewise surjective
quasi-isomorphism on the naive cotangent complexes, so the canonical maps are compatible
(`Stacks.DeRham.funnyMap_naturality_of_surjectiveQuasiIso`) through the isomorphism of
determinant lines of Tag 0FJJ, and that isomorphism is the one the identifications with
`det(NL_{B/A})` induce.

## Main definitions

* `Stacks.DeRham.selfPresentation`: the presentation `B[y]/(y_j - b_j)` of `B` over itself.
* `Stacks.DeRham.joinPresentation`: the common refinement of two presentations.

## Main results

* `Stacks.DeRham.funnyMapOfEquiv_naturality_of_surjectiveQuasiIso`: the naturality of the maps of
  Tag 0FL8 under surjective quasi-isomorphisms, read through identifications of the cokernels.
* `Stacks.DeRham.presentationDetNLMap_eq_of_surjective`: invariance under surjective morphisms of
  presentations.
* `Stacks.DeRham.presentationDetNLMap_eq`: **independence of the presentation**.

## References

* [Stacks Project, Tag 0FL9](https://stacks.math.columbia.edu/tag/0FL9)
* [Stacks Project, Tag 0FL8](https://stacks.math.columbia.edu/tag/0FL8)
* [Stacks Project, Tag 0FJJ](https://stacks.math.columbia.edu/tag/0FJJ)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Stacks.DeRham

section Generic

variable {R : Type*} [CommRing R]
variable {K' L' Mneg' Mzero' K L Mneg Mzero H : Type*}
variable [AddCommGroup K'] [Module R K'] [AddCommGroup L'] [Module R L']
variable [AddCommGroup Mneg'] [Module R Mneg'] [Module.Finite R Mneg'] [Module.Projective R Mneg']
variable [AddCommGroup Mzero'] [Module R Mzero'] [Module.Finite R Mzero']
  [Module.Projective R Mzero']
variable [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
variable [AddCommGroup Mneg] [Module R Mneg] [Module.Finite R Mneg] [Module.Projective R Mneg]
variable [AddCommGroup Mzero] [Module R Mzero] [Module.Finite R Mzero] [Module.Projective R Mzero]
variable [AddCommGroup H] [Module R H]

/-- **The naturality of the maps of Tag 0FL8 under surjective quasi-isomorphisms, read through
identifications of the two cokernels with the same module `H`.** -/
theorem funnyMapOfEquiv_naturality_of_surjectiveQuasiIso (n' n p : ℕ)
    (i' : K' →ₗ[R] L') (π' : L' →ₗ[R] Mzero') (d' : Mneg' →ₗ[R] L') (dM' : Mneg' →ₗ[R] Mzero')
    (i : K →ₗ[R] L) (π : L →ₗ[R] Mzero) (d : Mneg →ₗ[R] L) (dM : Mneg →ₗ[R] Mzero)
    (hi' : Function.Injective i') (hexact' : Function.Exact i' π')
    (hπ' : Function.Surjective π') (hsquare' : π'.comp d' = dM')
    (hzero' : Nonempty (Module.Basis (Fin n') R Mzero'))
    (hneg' : Nonempty (Module.Basis (Fin n') R Mneg'))
    (hi : Function.Injective i) (hexact : Function.Exact i π)
    (hπ : Function.Surjective π) (hsquare : π.comp d = dM)
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg))
    (e' : (L' ⧸ LinearMap.range d') ≃ₗ[R] H) (e : (L ⧸ LinearMap.range d) ≃ₗ[R] H)
    (κ : K' ≃ₗ[R] K) (l : L' →ₗ[R] L) (μ : TwoTermComplex.Hom dM' dM)
    (hs : μ.IsDegreewiseSurjective) (hq : μ.IsQuasiIso)
    (hli : ∀ x, l (i' x) = i (κ x)) (hπl : ∀ x, π (l x) = μ.zero (π' x))
    (hld : ∀ x, l (d' x) = d (μ.neg x))
    (he : ∀ x, e (Submodule.Quotient.mk (l x)) = e' (Submodule.Quotient.mk x))
    (η : ⋀[R]^p H) :
    TensorProduct.map (exteriorPower.map p κ.toLinearMap)
        (twoTermDeterminantEquivOfSurjectiveQuasiIso n' n dM' dM hzero' hneg' hzero hneg μ hs
          hq).toLinearMap
        (funnyMapOfEquiv n' i' π' d' dM' hi' hexact' hπ' hsquare' hzero' hneg' e' p η) =
      funnyMapOfEquiv n i π d dM hi hexact hπ hsquare hzero hneg e p η := by
  have hl : LinearMap.range d' ≤ (LinearMap.range d).comap l := by
    rintro _ ⟨x, rfl⟩
    exact ⟨μ.neg x, (hld x).symm⟩
  have hq' : ((LinearMap.range d').mapQ (LinearMap.range d) l hl).comp e'.symm.toLinearMap =
      e.symm.toLinearMap := by
    refine LinearMap.ext fun h => ?_
    obtain ⟨w, rfl⟩ := e'.surjective h
    induction w using Submodule.Quotient.induction_on with
    | _ x =>
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        Submodule.mapQ_apply, LinearEquiv.coe_coe, ← he, LinearEquiv.symm_apply_apply]
  rw [funnyMapOfEquiv_apply, funnyMapOfEquiv_apply,
    funnyMap_naturality_of_surjectiveQuasiIso n' n p i' π' d' dM' i π d dM hi' hexact' hπ'
      hsquare' hzero' hneg' hi hexact hπ hsquare hzero hneg κ l μ hs hq hli hπl hld hl,
    ← LinearMap.comp_apply (exteriorPower.map p _), ← exteriorPower.map_comp, hq']

/-- Moving `1 ⊗ e` across the determinant lines of a surjective quasi-isomorphism: if
`e ∘ Θ = e'` then `(1 ⊗ e) ∘ (1 ⊗ Θ) = 1 ⊗ e'`. -/
theorem lTensor_map_id_eq {K T₁ T₂ D : Type*} [AddCommGroup K] [Module R K] [AddCommGroup T₁]
    [Module R T₁] [AddCommGroup T₂] [Module R T₂] [AddCommGroup D] [Module R D] (p : ℕ)
    (Θ : T₁ ≃ₗ[R] T₂) (e₁ : T₁ ≃ₗ[R] D) (e₂ : T₂ ≃ₗ[R] D) (h : ∀ t, e₂ (Θ t) = e₁ t)
    (u : (⋀[R]^p K) ⊗[R] T₁) :
    e₂.toLinearMap.lTensor _ (TensorProduct.map
        (exteriorPower.map p (LinearEquiv.refl R K).toLinearMap) Θ.toLinearMap u) =
      e₁.toLinearMap.lTensor _ u := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x t =>
    rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      LinearEquiv.refl_toLinearMap, exteriorPower.map_id, LinearMap.id_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, h]

end Generic

section Surjective

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {m n : ℕ}
  {T : Algebra.Presentation A B (Fin m) (Fin m)} [T.IsRelativeGlobalCompleteIntersection]
  {P : Algebra.Presentation A B (Fin n) (Fin n)} [P.IsRelativeGlobalCompleteIntersection]
  (Φ : T.toExtension.Hom P.toExtension)

variable (A B) in
/-- Along the identity square, the map `B ⊗[A] Ω[A⁄ℤ] → B ⊗[A] Ω[A⁄ℤ]` is the identity. -/
theorem formsBaseChangeMapₛₗ_self (x : B ⊗[A] Ω[A⁄ℤ]) : formsBaseChangeMapₛₗ A B A B x = x := by
  refine tensorKaehler_induction (R := A) (S := B)
    (motive := fun x => formsBaseChangeMapₛₗ A B A B x = x) x (map_zero _)
    (fun x y hx hy => by rw [map_add, hx, hy]) (fun b a => ?_)
  rw [formsBaseChangeMapₛₗ_tmul, KaehlerDifferential.map_D]
  rfl

variable (B) in
/-- Along the identity of `B`, the map `Ω[B⁄ℤ] → Ω[B⁄ℤ]` is the identity. -/
theorem kaehlerMapₛₗ_self (y : Ω[B⁄ℤ]) : kaehlerMapₛₗ B B y = y := by
  have hy : y ∈ Submodule.span B (Set.range (KaehlerDifferential.D ℤ B)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact kaehlerMapₛₗ_D B B b
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smulₛₗ, hx]; rfl

/-- The `B`-linear map `B ⊗[A[x]] Ω[A[x]⁄ℤ] → B ⊗[A[y]] Ω[A[y]⁄ℤ]` induced by a morphism of
presentations of `B` over `A`. -/
noncomputable def polynomialFormsMap :
    B ⊗[T.toExtension.Ring] Ω[T.toExtension.Ring⁄ℤ] →ₗ[B]
      B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ] where
  toFun := polynomialFormsMapₛₗ T P Φ
  map_add' := map_add _
  map_smul' b x := map_smulₛₗ (polynomialFormsMapₛₗ T P Φ) b x

omit [T.IsRelativeGlobalCompleteIntersection] [P.IsRelativeGlobalCompleteIntersection] in
/-- `polynomialFormsMap` is `polynomialFormsMapₛₗ` along the identity of `B`. -/
theorem polynomialFormsMap_apply (x : B ⊗[T.toExtension.Ring] Ω[T.toExtension.Ring⁄ℤ]) :
    polynomialFormsMap Φ x = polynomialFormsMapₛₗ T P Φ x :=
  rfl

omit [T.IsRelativeGlobalCompleteIntersection] [P.IsRelativeGlobalCompleteIntersection] in
/-- A surjective morphism of presentations of `B` over `A` induces a surjection of conormal
modules. -/
theorem surjective_cotangentMap (hΦ : Function.Surjective Φ.toRingHom) :
    Function.Surjective (Algebra.Extension.Cotangent.map Φ) := by
  refine Algebra.Extension.Cotangent.map_surjective_of_comap_eq hΦ ?_
  have hcomap : P.toExtension.ker.comap Φ.toRingHom = T.toExtension.ker := by
    ext x
    simp only [Ideal.mem_comap, RingHom.mem_ker, Algebra.Extension.Hom.algebraMap_toRingHom,
      Algebra.algebraMap_self_apply]
  rw [hcomap, eq_comm, sup_eq_right]
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  have h := Φ.algebraMap_toRingHom x
  rwa [hx, map_zero, Algebra.algebraMap_self_apply, eq_comm] at h

omit [T.IsRelativeGlobalCompleteIntersection] [P.IsRelativeGlobalCompleteIntersection] in
/-- A surjective morphism of presentations of `B` over `A` induces a surjection of cotangent
spaces. -/
theorem surjective_cotangentSpaceMap (hΦ : Function.Surjective Φ.toRingHom) :
    Function.Surjective (Algebra.Extension.CotangentSpace.map Φ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro y -
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul b ω =>
    have hω : ω ∈ Submodule.span P.toExtension.Ring
        (Set.range (KaehlerDifferential.D A P.toExtension.Ring)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hω using Submodule.span_induction generalizing b with
    | mem ω hω =>
      obtain ⟨q, rfl⟩ := hω
      obtain ⟨r, rfl⟩ := hΦ q
      refine ⟨b ⊗ₜ KaehlerDifferential.D A T.toExtension.Ring r, ?_⟩
      rw [Algebra.Extension.CotangentSpace.map_tmul, Algebra.Extension.Hom.toAlgHom_apply]
      rfl
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ (hx b) (hy b)
    | smul a x _ hx => rw [← TensorProduct.smul_tmul]; exact hx _

variable [Algebra.Syntomic A B]

/-- The morphism of two-term complexes `NL(T) → NL(P)` of a morphism of presentations. -/
noncomputable abbrev nlHom : TwoTermComplex.Hom T.toExtension.cotangentComplex
    P.toExtension.cotangentComplex :=
  (NaiveCotangent.nlExtensionMap Φ).toHom

omit [T.IsRelativeGlobalCompleteIntersection] [P.IsRelativeGlobalCompleteIntersection]
  [Algebra.Syntomic A B] in
/-- A surjective morphism of presentations is degreewise surjective on naive cotangent
complexes. -/
theorem isDegreewiseSurjective_nlHom (hΦ : Function.Surjective Φ.toRingHom) :
    (nlHom Φ).IsDegreewiseSurjective :=
  ⟨surjective_cotangentMap Φ hΦ, surjective_cotangentSpaceMap Φ hΦ⟩

omit [T.IsRelativeGlobalCompleteIntersection] [P.IsRelativeGlobalCompleteIntersection]
  [Algebra.Syntomic A B] in
/-- A morphism of presentations of `B` over `A` is a quasi-isomorphism of naive cotangent
complexes. -/
theorem isQuasiIso_nlHom : (nlHom Φ).IsQuasiIso :=
  NaiveCotangent.ChainMap.isQuasiIso_toHom (NaiveCotangent.nlExtensionMap_isQuasiIso Φ
    (P.toGenerators.defaultHom T.toGenerators).toExtensionHom)

/-- The identifications of the determinant lines of `T` and `P` with `det(NL_{B/A})` are
compatible with the isomorphism of determinant lines of the surjective quasi-isomorphism
`NL(T) → NL(P)` (Tag 0FJJ). -/
theorem presentationDetNLEquiv_twoTermDeterminantEquivOfSurjectiveQuasiIso
    (hΦ : Function.Surjective Φ.toRingHom)
    (t : twoTermDeterminant B m T.toExtension.Cotangent T.toExtension.CotangentSpace) :
    presentationDetNLEquiv P (twoTermDeterminantEquivOfSurjectiveQuasiIso m n
        T.toExtension.cotangentComplex P.toExtension.cotangentComplex
        (nonempty_basis_cotangentSpace T) (nonempty_basis_cotangent T)
        (nonempty_basis_cotangentSpace P) (nonempty_basis_cotangent P) (nlHom Φ)
        (isDegreewiseSurjective_nlHom Φ hΦ) (isQuasiIso_nlHom Φ) t) =
      presentationDetNLEquiv T t := by
  apply (NaiveCotangent.detNLEquiv P.toExtension
    (P.toGenerators.defaultHom (Algebra.Generators.self A B)).toExtensionHom).injective
  have h1 := detNLEquiv_presentationDetNLEquiv P (twoTermDeterminantEquivOfSurjectiveQuasiIso m n
        T.toExtension.cotangentComplex P.toExtension.cotangentComplex
        (nonempty_basis_cotangentSpace T) (nonempty_basis_cotangent T)
        (nonempty_basis_cotangentSpace P) (nonempty_basis_cotangent P) (nlHom Φ)
        (isDegreewiseSurjective_nlHom Φ hΦ) (isQuasiIso_nlHom Φ) t)
  have h2 := twoTermDeterminantEquivDeterminantLine_twoTermDeterminantEquivOfSurjectiveQuasiIso m n
        T.toExtension.cotangentComplex P.toExtension.cotangentComplex
        (nonempty_basis_cotangentSpace T) (nonempty_basis_cotangent T)
        (nonempty_basis_cotangentSpace P) (nonempty_basis_cotangent P) (nlHom Φ)
        (isDegreewiseSurjective_nlHom Φ hΦ) (isQuasiIso_nlHom Φ) t
  have h3 := NaiveCotangent.detNLEquiv_apply_of_hom T.toExtension
    (T.toGenerators.defaultHom (Algebra.Generators.self A B)).toExtensionHom P.toExtension
    (P.toGenerators.defaultHom (Algebra.Generators.self A B)).toExtensionHom Φ
    (P.toGenerators.defaultHom T.toGenerators).toExtensionHom (presentationDetNLEquiv T t)
  have h4 := NaiveCotangent.detTransport_eq_detEquiv (NaiveCotangent.nlExtensionMap Φ)
    (NaiveCotangent.nlExtensionMap_isQuasiIso Φ
      (P.toGenerators.defaultHom T.toGenerators).toExtensionHom)
    (surjective_cotangentMap Φ hΦ) (surjective_cotangentSpaceMap Φ hΦ)
  have h5 := detNLEquiv_presentationDetNLEquiv T t
  refine h1.trans (h2.trans ?_)
  refine Eq.trans ?_ h3.symm
  refine Eq.trans ?_ (LinearEquiv.congr_fun h4 _).symm
  exact congrArg _ h5.symm

/-- **The maps of Remark 0FL9 are invariant under surjective morphisms of presentations.** If
`Φ : T → P` is a morphism of square relative global complete intersection presentations of `B`
over `A` which is surjective on polynomial rings, then the maps of Remark 0FL9 with values in
`det(NL_{B/A})` attached to `T` and to `P` agree. -/
theorem presentationDetNLMap_eq_of_surjective (hΦ : Function.Surjective Φ.toRingHom) (p : ℕ) :
    presentationDetNLMap T p = presentationDetNLMap P p := by
  refine LinearMap.ext fun η => ?_
  have Hc := funnyMapOfEquiv_naturality_of_surjectiveQuasiIso m n p (cotangentDiagram T).i
    (cotangentDiagram T).π (cotangentDiagram T).d T.toExtension.cotangentComplex
    (cotangentDiagram P).i (cotangentDiagram P).π (cotangentDiagram P).d
    P.toExtension.cotangentComplex (cotangentDiagram T).hi (cotangentDiagram T).hexact
    (cotangentDiagram T).hπ (cotangentDiagram T).hsquare (nonempty_basis_cotangentSpace T)
    (nonempty_basis_cotangent T) (cotangentDiagram P).hi (cotangentDiagram P).hexact
    (cotangentDiagram P).hπ (cotangentDiagram P).hsquare (nonempty_basis_cotangentSpace P)
    (nonempty_basis_cotangent P) (cotangentDiagram T).quotientEquiv
    (cotangentDiagram P).quotientEquiv (LinearEquiv.refl B _) (polynomialFormsMap Φ) (nlHom Φ)
    (isDegreewiseSurjective_nlHom Φ hΦ) (isQuasiIso_nlHom Φ)
    (fun x => (polynomialFormsMapₛₗ_i x).trans
      (congrArg (cotangentDiagram P).i (formsBaseChangeMapₛₗ_self A B x)))
    (fun x => (cotangentSpaceMapₛₗ_π x).symm) (fun x => polynomialFormsMapₛₗ_d x)
    (fun x => (kaehlerMapₛₗ_quotientEquiv x).symm.trans (kaehlerMapₛₗ_self B _)) η
  exact (lTensor_map_id_eq p _ (presentationDetNLEquiv T) (presentationDetNLEquiv P)
    (presentationDetNLEquiv_twoTermDeterminantEquivOfSurjectiveQuasiIso Φ hΦ) _).symm.trans
    (congrArg ((presentationDetNLEquiv P).toLinearMap.lTensor _) Hc)

end Surjective

/-! ### A common refinement of two presentations -/

section Join

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {m n : ℕ}

/-- The presentation `B[y_1, …, y_m]/(y_j - b_j)` of `B` over itself, for elements
`b_1, …, b_m` of `B`. -/
noncomputable def selfPresentation (b : Fin m → B) : Algebra.Presentation B B (Fin m) (Fin m) where
  toGenerators := Algebra.Generators.ofSurjective b fun x => ⟨MvPolynomial.C x, by simp⟩
  relation j := MvPolynomial.X j - MvPolynomial.C (b j)
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    exact (MvPolynomial.ker_eval_eq_span_X_sub_C b).symm

/-- A surjection `A[z_1, …, z_k] → A[x_1, …, x_n]` onto a polynomial ring: every variable is in
the image. -/
theorem aeval_surjective_of_X_mem_range {ι κ R : Type*} [CommRing R]
    (f : κ → MvPolynomial ι R) (hf : ∀ i, MvPolynomial.X i ∈ Set.range f) :
    Function.Surjective (MvPolynomial.aeval (R := R) f) := by
  rw [← AlgHom.range_eq_top, MvPolynomial.aeval_range, eq_top_iff,
    ← MvPolynomial.adjoin_range_X]
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨i, rfl⟩
  exact hf i

variable (P : Algebra.Presentation A B (Fin n) (Fin n))
  (Q : Algebra.Presentation A B (Fin m) (Fin m))

/-- **A common refinement of two presentations** `P` (variables `x`) and `Q` (variables `y`) of `B`
over `A`: the presentation in the variables `y, x` whose relations are the relations of `P` and
lifts of the `y_j - Q.val j`. It is square when `P` and `Q` are. -/
noncomputable def joinPresentation : Algebra.Presentation A B (Fin (m + n)) (Fin (m + n)) :=
  ((selfPresentation Q.val).comp P).reindex finSumFinEquiv.symm finSumFinEquiv.symm

/-- The values of the variables of the common refinement. -/
theorem joinPresentation_val (k : Fin (m + n)) :
    (joinPresentation P Q).val k = Sum.elim Q.val P.val (finSumFinEquiv.symm k) := by
  show ((selfPresentation Q.val).toGenerators.comp P.toGenerators).val
    (finSumFinEquiv.symm k) = _
  rcases finSumFinEquiv.symm k with j | i <;> rfl

/-- The common refinement of a square relative global complete intersection presentation is a
square relative global complete intersection presentation. -/
instance [P.IsRelativeGlobalCompleteIntersection] :
    (joinPresentation P Q).IsRelativeGlobalCompleteIntersection :=
  haveI : Algebra.QuasiFinite A B := Algebra.QuasiFinite.of_square_presentation
    (P := P) inferInstance rfl
  Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_quasiFinite _ rfl

/-- The morphism from the common refinement to `P`: the variables `x` go to themselves and the
variables `y` to lifts of their values. -/
noncomputable def joinHomLeft : (joinPresentation P Q).toGenerators.Hom P.toGenerators where
  val k := Sum.elim (fun j => P.σ (Q.val j)) MvPolynomial.X (finSumFinEquiv.symm k)
  aeval_val k := by
    rw [joinPresentation_val]
    rcases finSumFinEquiv.symm k with j | i
    · exact P.aeval_val_σ _
    · exact MvPolynomial.aeval_X _ _

/-- The morphism from the common refinement to `Q`: the variables `y` go to themselves and the
variables `x` to lifts of their values. -/
noncomputable def joinHomRight : (joinPresentation P Q).toGenerators.Hom Q.toGenerators where
  val k := Sum.elim MvPolynomial.X (fun i => Q.σ (P.val i)) (finSumFinEquiv.symm k)
  aeval_val k := by
    rw [joinPresentation_val]
    rcases finSumFinEquiv.symm k with j | i
    · exact MvPolynomial.aeval_X _ _
    · exact Q.aeval_val_σ _

/-- The morphism from the common refinement to `P` is surjective. -/
theorem surjective_joinHomLeft : Function.Surjective (joinHomLeft P Q).toExtensionHom.toRingHom :=
  aeval_surjective_of_X_mem_range _ fun i =>
    ⟨finSumFinEquiv (Sum.inr i), by simp [joinHomLeft]⟩

/-- The morphism from the common refinement to `Q` is surjective. -/
theorem surjective_joinHomRight :
    Function.Surjective (joinHomRight P Q).toExtensionHom.toRingHom :=
  aeval_surjective_of_X_mem_range _ fun j =>
    ⟨finSumFinEquiv (Sum.inl j), by simp [joinHomRight]⟩

variable [P.IsRelativeGlobalCompleteIntersection] [Q.IsRelativeGlobalCompleteIntersection]
  [Algebra.Syntomic A B]

/-- **The maps of Remark 0FL9 with values in `det(NL_{B/A})` do not depend on the
presentation**: they agree for any two square relative global complete intersection
presentations of `B` over `A`. -/
theorem presentationDetNLMap_eq (p : ℕ) : presentationDetNLMap P p = presentationDetNLMap Q p :=
  (presentationDetNLMap_eq_of_surjective _ (surjective_joinHomLeft P Q) p).symm.trans
    (presentationDetNLMap_eq_of_surjective _ (surjective_joinHomRight P Q) p)

end Join

end Stacks.DeRham

end
