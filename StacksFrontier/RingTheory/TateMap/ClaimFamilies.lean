module

public import StacksFrontier.RingTheory.TateMap.ClaimMoves
public import StacksFrontier.RingTheory.TateMap.Nice
public import StacksFrontier.RingTheory.TateMap.ChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.JacobianDualizingModule

/-!
# Parameter extensions of a localized square presentation

Let `C = S[x_1, …, x_n, 1/h]/(f_1, …, f_n)` and let `σ` be a set of parameters. For a polynomial
`g` in `x_1, …, x_n` over `S[σ]`, the *parameter extension*

`Z = S[σ][x_1, …, x_n, 1/(h g)]/(f_1, …, f_n)`

is the localization of `C[σ]` away from the image of `g`.

## Main definitions

* `Stacks.TateMap.paramEquiv`: `S[σ][x, 1/h]/(f) ≅ C[σ]` over `S[σ]`.
* `Stacks.TateMap.paramExtEquiv`: `Z ≅ C[σ]_g` over `S[σ]`.

## Main results

* `Stacks.TateMap.isLocalization_paramExt`: `Z` is the localization of `C[σ]` away from the image
  of `g`.
* `Stacks.TateMap.isNiceChart_paramExt`: if `C` is a domain, a flat quasi-finite relative global
  complete intersection of finite type over the Noetherian ring `S`, unramified at one prime, and
  `g` does not vanish in `C[σ]`, then `Z` is nice over `S[σ]`, and has the same properties.
* `Stacks.TateMap.exists_presentation_of_chartBaseChange`: a localization away from one element of
  `A ⊗_S S[x, 1/h]/(f)` is isomorphic to `A[x, 1/(h p)]/(f)` for some polynomial `p` over `A`.
-/

@[expose] public section

open MvPolynomial Stacks.Discriminant
open scoped TensorProduct

universe u

namespace Stacks.TateMap

attribute [local instance] MvPolynomial.algebraMvPolynomial

section ParamExt

variable {S : Type u} [CommRing S] {n : ℕ} (h : MvPolynomial (Fin n) S)
  (f : Fin n → MvPolynomial (Fin n) S) (σ : Type)

/-- The base change of `h` to the parameter ring `S[σ]`. -/
noncomputable abbrev paramH : MvPolynomial (Fin n) (MvPolynomial σ S) :=
  MvPolynomial.map (algebraMap S (MvPolynomial σ S)) h

/-- The base change of the relations `f` to the parameter ring `S[σ]`. -/
noncomputable abbrev paramF : Fin n → MvPolynomial (Fin n) (MvPolynomial σ S) :=
  fun i ↦ MvPolynomial.map (algebraMap S (MvPolynomial σ S)) (f i)

/-- `S[σ][x, 1/h]/(f) ≅ C[σ]` for `C = S[x, 1/h]/(f)`, over `S[σ]`. -/
noncomputable def paramEquiv :
    localizedCompleteIntersection (MvPolynomial σ S) n (paramH h σ) (paramF f σ)
      ≃ₐ[MvPolynomial σ S] MvPolynomial σ (localizedCompleteIntersection S n h f) :=
  letI : Algebra (localizedCompleteIntersection S n h f)
      (localizedCompleteIntersection (MvPolynomial σ S) n (paramH h σ) (paramF f σ)) :=
    (localizedCompleteIntersectionMap S (MvPolynomial σ S) n h f).toRingHom.toAlgebra
  haveI : @IsScalarTower S (localizedCompleteIntersection S n h f)
      (localizedCompleteIntersection (MvPolynomial σ S) n (paramH h σ) (paramF f σ))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r ↦
      ((localizedCompleteIntersectionMap S (MvPolynomial σ S) n h f).commutes r).symm
  haveI := isPushout_localizedCompleteIntersection S (MvPolynomial σ S) n h f
  (Algebra.IsPushout.equiv S (MvPolynomial σ S) (localizedCompleteIntersection S n h f)
      (localizedCompleteIntersection (MvPolynomial σ S) n (paramH h σ) (paramF f σ))).symm.trans
    (Algebra.IsPushout.equiv S (MvPolynomial σ S) (localizedCompleteIntersection S n h f)
      (MvPolynomial σ (localizedCompleteIntersection S n h f)))

/-- `paramEquiv` sends the class of `x_i` to the constant `x_i`. -/
theorem paramEquiv_lciMk_X (i : Fin n) :
    paramEquiv h f σ (lciMk _ _ (X i)) = MvPolynomial.C (lciMk h f (X i)) := by
  let : Algebra (localizedCompleteIntersection S n h f)
      (localizedCompleteIntersection (MvPolynomial σ S) n (paramH h σ) (paramF f σ)) :=
    (localizedCompleteIntersectionMap S (MvPolynomial σ S) n h f).toRingHom.toAlgebra
  have : @IsScalarTower S (localizedCompleteIntersection S n h f)
      (localizedCompleteIntersection (MvPolynomial σ S) n (paramH h σ) (paramF f σ))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r ↦
      ((localizedCompleteIntersectionMap S (MvPolynomial σ S) n h f).commutes r).symm
  have := isPushout_localizedCompleteIntersection S (MvPolynomial σ S) n h f
  have hX : lciMk (paramH h σ) (paramF f σ) (X i) =
      algebraMap (localizedCompleteIntersection S n h f) _ (lciMk h f (X i)) := by
    change _ = localizedCompleteIntersectionMap S (MvPolynomial σ S) n h f
      (algebraMap (MvPolynomial (Fin n) S) _ (X i))
    rw [localizedCompleteIntersectionMap_algebraMap, MvPolynomial.map_X]
    rfl
  rw [paramEquiv, AlgEquiv.trans_apply, hX, Algebra.IsPushout.equiv_symm_algebraMap_right,
    Algebra.IsPushout.equiv_tmul, map_one, one_mul]
  rfl

/-- `paramEquiv` sends the class of a polynomial `p` over `S[σ]` to `p` evaluated at the constant
classes of the variables. -/
theorem paramEquiv_lciMk (p : MvPolynomial (Fin n) (MvPolynomial σ S)) :
    paramEquiv h f σ (lciMk _ _ p) =
      aeval (fun i ↦ MvPolynomial.C (lciMk h f (X i))) p := by
  have : (paramEquiv h f σ).toAlgHom.comp (lciMk _ _) =
      aeval (fun i ↦ MvPolynomial.C (lciMk h f (X i))) :=
    MvPolynomial.algHom_ext fun i ↦ by
      rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, paramEquiv_lciMk_X, aeval_X]
  exact AlgHom.congr_fun this p

variable (g : MvPolynomial (Fin n) (MvPolynomial σ S))

/-- The parameter extension `S[σ][x, 1/(h g)]/(f)`. -/
noncomputable abbrev ParamExt : Type u :=
  localizedCompleteIntersection (MvPolynomial σ S) n (paramH h σ * g) (paramF f σ)

/-- The image of `g` in `C[σ]`. -/
noncomputable abbrev paramImage : MvPolynomial σ (localizedCompleteIntersection S n h f) :=
  paramEquiv h f σ (lciMk _ _ g)

/-- The algebra structure of the parameter extension over `C[σ]`. -/
noncomputable abbrev paramExtAlgebra :
    Algebra (MvPolynomial σ (localizedCompleteIntersection S n h f)) (ParamExt h f σ g) :=
  ((lciAwayHom (paramH h σ) g (paramF f σ)).toRingHom.comp
    (paramEquiv h f σ).symm.toRingEquiv.toRingHom).toAlgebra

/-- The parameter extension `S[σ][x, 1/(h g)]/(f)` is the localization of `C[σ]` away from the
image of `g`. -/
theorem isLocalization_paramExt :
    letI := paramExtAlgebra h f σ g
    IsLocalization.Away (paramImage h f σ g) (ParamExt h f σ g) := by
  let := (lciAwayHom (paramH h σ) g (paramF f σ)).toRingHom.toAlgebra
  have := isLocalization_lciAwayHom (paramH h σ) g (paramF f σ)
  have := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers (lciMk _ _ g))
    (ParamExt h f σ g) (paramEquiv h f σ).toRingEquiv
  rwa [Submonoid.map_powers] at this

/-- The tower `S[σ] → C[σ] → Z`. -/
theorem paramExt_algebraMap_eq (c : MvPolynomial σ S) :
    algebraMap (MvPolynomial σ S) (ParamExt h f σ g) c =
      @algebraMap _ _ _ _ (paramExtAlgebra h f σ g)
        (algebraMap (MvPolynomial σ S)
          (MvPolynomial σ (localizedCompleteIntersection S n h f)) c) := by
  change _ = lciAwayHom (paramH h σ) g (paramF f σ)
    ((paramEquiv h f σ).symm (algebraMap _ _ c))
  rw [AlgEquiv.commutes, AlgHom.commutes]

/-- `Z ≅ C[σ]_g` over `S[σ]`. -/
noncomputable def paramExtEquiv :
    ParamExt h f σ g ≃ₐ[MvPolynomial σ S] Localization.Away (paramImage h f σ g) :=
  letI := paramExtAlgebra h f σ g
  haveI := isLocalization_paramExt h f σ g
  let e := IsLocalization.algEquiv (Submonoid.powers (paramImage h f σ g)) (ParamExt h f σ g)
    (Localization.Away (paramImage h f σ g))
  AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun c ↦ by
    rw [paramExt_algebraMap_eq]
    change e (algebraMap _ _ _) = _
    rw [AlgEquiv.commutes]
    exact (IsScalarTower.algebraMap_apply _ _ _ c).symm

end ParamExt

section Nice

variable {S : Type u} [CommRing S] [IsNoetherianRing S] {n : ℕ} (h : MvPolynomial (Fin n) S)
  (f : Fin n → MvPolynomial (Fin n) S) (σ : Type) [Finite σ]
  (g : MvPolynomial (Fin n) (MvPolynomial σ S))
  [IsNoetherianRing (localizedCompleteIntersection S n h f)]
  [Module.Flat S (localizedCompleteIntersection S n h f)]
  [Algebra.QuasiFinite S (localizedCompleteIntersection S n h f)]
  [IsDomain (localizedCompleteIntersection S n h f)]
  [Algebra.FiniteType S (localizedCompleteIntersection S n h f)]
  [Algebra.IsRelativeGlobalCompleteIntersection S (localizedCompleteIntersection S n h f)]

omit [IsNoetherianRing (localizedCompleteIntersection S n h f)] in
/-- **Niceness of a parameter extension.** Let `C = S[x, 1/h]/(f)` be a domain which is a flat
quasi-finite relative global complete intersection of finite type over the Noetherian ring `S`,
unramified at one prime. If `g` does not vanish in `C[σ]`, then the parameter extension
`S[σ][x, 1/(h g)]/(f)` is Noetherian, flat, quasi-finite and of finite type over `S[σ]`, and
nice. -/
theorem isNiceChart_paramExt (hg : paramImage h f σ g ≠ 0)
    (q : Ideal (localizedCompleteIntersection S n h f)) [q.IsPrime] [Algebra.IsUnramifiedAt S q] :
    ∃ (_ : IsNoetherianRing (ParamExt h f σ g))
      (_ : Module.Flat (MvPolynomial σ S) (ParamExt h f σ g))
      (_ : Algebra.QuasiFinite (MvPolynomial σ S) (ParamExt h f σ g)),
      Algebra.FiniteType (MvPolynomial σ S) (ParamExt h f σ g) ∧
        IsNiceChart (MvPolynomial σ S) (ParamExt h f σ g) := by
  obtain ⟨_, hflat, hqf, hft, _, hnoeth, -, hnice⟩ :=
    isNiceChart_localization_mvPolynomial (R := S) σ (paramImage h f σ g) hg q
  let e := paramExtEquiv h f σ g
  have : Algebra.QuasiFinite (MvPolynomial σ S) (ParamExt h f σ g) :=
    (Algebra.QuasiFinite.iff_of_algEquiv e).mpr hqf
  have : Algebra.FinitePresentation (MvPolynomial σ S) (ParamExt h f σ g) :=
    finitePresentation_localizedCompleteIntersection _ n _ _
  have : IsNoetherianRing (ParamExt h f σ g) :=
    Algebra.FiniteType.isNoetherianRing (MvPolynomial σ S) _
  have : Module.Flat (MvPolynomial σ S) (ParamExt h f σ g) :=
    flat_localizedCompleteIntersection _ n _ _
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hnice.of_algEquiv e.symm⟩

end Nice

end Stacks.TateMap

namespace Stacks.TateMap

section PresentationBaseChange

variable {S : Type u} [CommRing S] {n : ℕ}

/-- Every element of `S[x, 1/h]/(f)` is the class of a polynomial divided by a power of `h`. -/
theorem exists_mul_pow_eq_lciMk (h : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S)
    (z : localizedCompleteIntersection S n h f) :
    ∃ (p : MvPolynomial (Fin n) S) (k : ℕ), z * lciMk h f h ^ k = lciMk h f p := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨k, a, hw⟩ := IsLocalization.Away.surj h w
  refine ⟨a, k, ?_⟩
  have := congrArg (Ideal.Quotient.mk (Ideal.span (Set.range (localizedRelations S n h f)))) hw
  rwa [map_mul, map_pow] at this

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra S A] {h : MvPolynomial (Fin n) S}
  {f : Fin n → MvPolynomial (Fin n) S} [Algebra A B]
  [Algebra (localizedCompleteIntersection S n h f) B]

/-- If `B` is the localization of
`A ⊗_S S[x, 1/h]/(f)` away from one element, then `B ≅ A[x, 1/(h p)]/(f)` for some polynomial `p`
over `A`, compatibly with the images of the variables. -/
theorem exists_presentation_of_chartBaseChange
    (D : ChartBaseChange S (localizedCompleteIntersection S n h f) A B) :
    ∃ (p : MvPolynomial (Fin n) A) (e : B ≃ₐ[A] localizedCompleteIntersection A n
        (MvPolynomial.map (algebraMap S A) h * p)
          (fun i ↦ MvPolynomial.map (algebraMap S A) (f i))),
      ∀ q : MvPolynomial (Fin n) S,
        e (algebraMap _ B (lciMk h f q)) = lciMk _ _ (MvPolynomial.map (algebraMap S A) q) := by
  let := D.algebra
  have := D.isLocalization
  set H := MvPolynomial.map (algebraMap S A) h
  set F := fun i ↦ MvPolynomial.map (algebraMap S A) (f i)
  set T := localizedCompleteIntersection A n H F
  let φ := localizedCompleteIntersectionBaseChange S A n h f
  obtain ⟨p, k, hp⟩ := exists_mul_pow_eq_lciMk _ _ (φ D.elt)
  let algTB : Algebra T B :=
    ((algebraMap (A ⊗[S] localizedCompleteIntersection S n h f) B).comp
      φ.symm.toRingEquiv.toRingHom).toAlgebra
  have h1 := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers D.elt) B
    φ.toRingEquiv
  rw [Submonoid.map_powers] at h1
  have : IsLocalization.Away (φ D.elt) B := h1
  have hassoc : Associated (φ D.elt) (lciMk _ _ p) := by
    rw [← hp]
    exact associated_mul_unit_right _ _ ((isUnit_lciMk _ _).pow k)
  have : IsLocalization.Away (lciMk _ _ p) B :=
    (IsLocalization.Away.iff_of_associated hassoc).mp inferInstance
  set Z := localizedCompleteIntersection A n (H * p) F
  let algTZ : Algebra T Z := (lciAwayHom H p F).toRingHom.toAlgebra
  have := isLocalization_lciAwayHom H p F
  let e₀ := IsLocalization.algEquiv (Submonoid.powers (lciMk H F p)) B Z
  have hA : ∀ a : A, algebraMap A B a = algebraMap T B (algebraMap A T a) := by
    intro a
    change _ = algebraMap (A ⊗[S] localizedCompleteIntersection S n h f) B
      (φ.symm (algebraMap A T a))
    rw [AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, D.base_left]
  have hX : ∀ q : MvPolynomial (Fin n) S,
      algebraMap _ B (lciMk h f q) =
        algebraMap T B (lciMk _ _ (MvPolynomial.map (algebraMap S A) q)) := by
    intro q
    change _ = algebraMap (A ⊗[S] localizedCompleteIntersection S n h f) B
      (φ.symm (lciMk _ _ (MvPolynomial.map (algebraMap S A) q)))
    rw [← D.base_right]
    congr 1
    rw [AlgEquiv.eq_symm_apply, localizedCompleteIntersectionBaseChange_tmul, one_smul,
      lciMk_apply, localizedCompleteIntersectionMap_algebraMap]
    rfl
  have he : ∀ t : T, e₀ (algebraMap T B t) = lciAwayHom _ p _ t := e₀.commutes
  refine ⟨p, AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) fun a ↦ ?_, fun q ↦ ?_⟩
  · rw [hA]
    exact (he _).trans ((lciAwayHom _ p _).commutes a)
  · rw [hX]
    exact (he _).trans (lciAwayHom_lciMk _ p _ _)

end PresentationBaseChange

end Stacks.TateMap
