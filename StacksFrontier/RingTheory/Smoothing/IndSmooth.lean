module

public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.Smoothing.ProductOfFilteredColimits

/-!
# Filtered colimits of smooth algebras

A ring map `R → Λ` is *ind-smooth* when `Λ` is a filtered colimit of smooth `R`-algebras. This
file records that property in the spelling of Lemma `07C3`, its ring-theoretic reformulation as a
factorization property, and its stability under ring isomorphisms and finite products.

## Main definitions

* `Stacks.Smoothing.IndSmooth`: `Λ` is a filtered colimit of smooth `R`-algebras.

## Main results

* `Stacks.Smoothing.indSmooth_iff_exists_factorization`: ind-smoothness is equivalent to every
  map to `Λ` from a finitely presented `R`-algebra factoring through a smooth `R`-algebra.
* `Stacks.Smoothing.indSmooth_prod`, `Stacks.Smoothing.indSmooth_pi_fin`: ind-smoothness is
  stable under binary and finite products.

## Implementation notes

The product statements are the universe-polymorphic form of Lemma `07F3`. They are proved through
the factorization criterion `07C3` and the smoothness of a product of smooth algebras
(`Algebra.Smooth.prod`), so no interchange of filtered colimits with products is needed.

## References

* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
-/

open scoped TensorProduct

@[expose] public section

namespace Stacks.Smoothing

open CategoryTheory CategoryTheory.Limits

universe u

/-- `Λ` is a filtered colimit of smooth `R`-algebras, in the spelling of Lemma `07C3`. -/
abbrev IndSmooth (R : Type u) [CommRing R] (Λ : Type u) [CommRing Λ] [Algebra R Λ] : Prop :=
  ObjectProperty.ind.{u}
    (fun B : Under (CommRingCat.of R) ↦ B.hom.hom.Smooth)
    (Under.mk (CommRingCat.ofHom (algebraMap R Λ)))

section Basic

variable (R Λ : Type u) [CommRing R] [CommRing Λ] [Algebra R Λ]

/-- An object of `Under (CommRingCat.of R)` whose structure map is smooth has a structure map of
finite presentation. -/
theorem smooth_le_finitePresentation :
    (fun X : Under (CommRingCat.of R) ↦ X.hom.hom.Smooth) ≤
      (fun X : Under (CommRingCat.of R) ↦ X.hom.hom.FinitePresentation) :=
  fun _ hA ↦ hA.finitePresentation

/-- A smooth algebra is a filtered colimit of smooth algebras. -/
theorem indSmooth_of_smooth (h : Algebra.Smooth R Λ) : IndSmooth R Λ := by
  refine ObjectProperty.le_ind _ _ ?_
  change (algebraMap R Λ).Smooth
  exact RingHom.smooth_algebraMap.mpr h

/-- **Ind-smoothness as a factorization property (Lemma `07C3`).** `Λ` is a filtered colimit of
smooth `R`-algebras if and only if every `R`-algebra map to `Λ` from an `R`-algebra of finite
presentation factors through a smooth `R`-algebra. -/
theorem indSmooth_iff_exists_factorization :
    IndSmooth R Λ ↔
      ∀ (A : Type u) (_ : CommRing A) (alg : Algebra R A),
        letI := alg
        Algebra.FinitePresentation R A → ∀ φ : A →ₐ[R] Λ,
          ∃ (B : Type u) (_ : CommRing B) (algB : Algebra R B),
            letI := algB
            Algebra.Smooth R B ∧ ∃ (g : A →ₐ[R] B) (k : B →ₐ[R] Λ), k.comp g = φ := by
  refine Iff.trans (CommRingCat.ind_under_iff_exists_factorization _
    (smooth_le_finitePresentation R)) ?_
  refine ⟨fun h A _ alg hfp φ ↦ ?_, fun h A hA f ↦ ?_⟩
  · let := alg
    let AU : Under (CommRingCat.of R) := Under.mk (CommRingCat.ofHom (algebraMap R A))
    have hAfp : AU.hom.hom.FinitePresentation := by
      change (algebraMap R A).FinitePresentation
      exact RingHom.finitePresentation_algebraMap.mpr hfp
    let fU : AU ⟶ Under.mk (CommRingCat.ofHom (algebraMap R Λ)) :=
      Under.homMk (CommRingCat.ofHom φ.toRingHom) (by ext r; exact φ.commutes r)
    obtain ⟨BU, g, k, hgk, hBs⟩ := h AU hAfp fU
    let algB : Algebra R BU.right := BU.hom.hom.toAlgebra
    refine ⟨BU.right, inferInstance, algB, RingHom.smooth_algebraMap.mp hBs,
      { toRingHom := g.right.hom
        commutes' := fun r ↦ congrArg (fun q ↦ q.hom r) g.w },
      { toRingHom := k.right.hom
        commutes' := fun r ↦ congrArg (fun q ↦ q.hom r) k.w }, ?_⟩
    ext a
    exact congrArg (fun m ↦ m.right.hom a) hgk
  · let : Algebra R A.right := A.hom.hom.toAlgebra
    have hfp : Algebra.FinitePresentation R A.right := hA
    let φ : A.right →ₐ[R] Λ :=
      { toRingHom := f.right.hom
        commutes' := fun r ↦ congrArg (fun q ↦ q.hom r) f.w }
    obtain ⟨B, instB, algB, hBs, g, k, hgk⟩ := h A.right inferInstance inferInstance hfp φ
    let := instB
    let := algB
    refine ⟨Under.mk (CommRingCat.ofHom (algebraMap R B)),
      Under.homMk (CommRingCat.ofHom g.toRingHom) (by ext r; exact g.commutes r),
      Under.homMk (CommRingCat.ofHom k.toRingHom) (by ext r; exact k.commutes r), ?_, ?_⟩
    · ext a
      exact congrArg (fun m ↦ m a) hgk
    · change (algebraMap R B).Smooth
      exact RingHom.smooth_algebraMap.mpr hBs

end Basic

/-- Ind-smoothness transports along a pair of ring isomorphisms compatible with the structure
maps. -/
theorem indSmooth_of_ringEquiv (R S A B : Type u) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (eR : R ≃+* S) (eA : A ≃+* B)
    (he : ∀ r, eA (algebraMap R A r) = algebraMap S B (eR r))
    (h : IndSmooth R A) : IndSmooth S B := by
  let baseIso : CommRingCat.of S ≅ CommRingCat.of R :=
    { hom := CommRingCat.ofHom eR.symm.toRingHom
      inv := CommRingCat.ofHom eR.toRingHom
      hom_inv_id := by ext x; simp
      inv_hom_id := by ext x; simp }
  let E := Under.mapIso baseIso
  have hTarget : E.functor.obj (Under.mk (CommRingCat.ofHom (algebraMap R A))) ≅
      Under.mk (CommRingCat.ofHom (algebraMap S B)) := by
    let eAi : CommRingCat.of A ≅ CommRingCat.of B :=
      { hom := CommRingCat.ofHom eA.toRingHom
        inv := CommRingCat.ofHom eA.symm.toRingHom
        hom_inv_id := by ext x; simp
        inv_hom_id := by ext x; simp }
    refine Under.isoMk eAi ?_
    ext x
    change eA (algebraMap R A (eR.symm x)) = algebraMap S B x
    simpa using he (eR.symm x)
  obtain ⟨J, hJ, hFilt, pres, hF⟩ := h
  refine ⟨J, hJ, hFilt, (pres.map E.functor).ofIso hTarget, fun j ↦ ?_⟩
  have hX : ((pres.diag.obj j).hom.hom).Smooth := hF j
  change ((baseIso.hom ≫ (pres.diag.obj j).hom).hom).Smooth
  have : RingHom.Smooth (((pres.diag.obj j).hom.hom).comp (eR.symm : S →+* R)) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective eR.symm.bijective) hX
  simpa [baseIso] using this

section Products

/-- A localization away from one element is smooth. -/
private theorem smooth_of_isLocalization_away (S T : Type u) [CommRing S] [CommRing T]
    [Algebra S T] (e : S) [IsLocalization.Away e T] : Algebra.Smooth S T :=
  { formallySmooth := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers e)
    finitePresentation := IsLocalization.Away.finitePresentation e }

/-- A factor of a product ring is a smooth algebra over the product. -/
private theorem smooth_fst (R₁ R₂ : Type u) [CommRing R₁] [CommRing R₂] :
    letI : Algebra (R₁ × R₂) R₁ := (RingHom.fst R₁ R₂).toAlgebra
    Algebra.Smooth (R₁ × R₂) R₁ := by
  let : Algebra (R₁ × R₂) R₁ := (RingHom.fst R₁ R₂).toAlgebra
  have : IsLocalization.Away ((1 : R₁), (0 : R₂)) R₁ := IsLocalization.away_fst
  exact smooth_of_isLocalization_away _ _ ((1 : R₁), (0 : R₂))

private theorem smooth_snd (R₁ R₂ : Type u) [CommRing R₁] [CommRing R₂] :
    letI : Algebra (R₁ × R₂) R₂ := (RingHom.snd R₁ R₂).toAlgebra
    Algebra.Smooth (R₁ × R₂) R₂ := by
  let : Algebra (R₁ × R₂) R₂ := (RingHom.snd R₁ R₂).toAlgebra
  have : IsLocalization.Away ((0 : R₁), (1 : R₂)) R₂ := IsLocalization.away_snd
  exact smooth_of_isLocalization_away _ _ ((0 : R₁), (1 : R₂))

/-- If `k ∘ g` is the base change of `φ`, then `k (g (1 ⊗ a)) = φ a`. -/
private theorem apply_includeRight_of_comp_eq_liftEquiv (P R A Λ B : Type u) [CommRing P]
    [CommRing R] [CommRing A] [CommRing Λ] [CommRing B] [Algebra P R] [Algebra P A]
    [Algebra P Λ] [Algebra R Λ] [IsScalarTower P R Λ] [Algebra R B]
    (φ : A →ₐ[P] Λ) (g : R ⊗[P] A →ₐ[R] B) (k : B →ₐ[R] Λ)
    (hgk : k.comp g = AlgHom.liftEquiv P R A Λ φ) (a : A) :
    k (g (Algebra.TensorProduct.includeRight a)) = φ a := by
  have := congrArg (AlgHom.liftEquiv P R A Λ).symm hgk
  rw [Equiv.symm_apply_apply] at this
  exact congrArg (fun m ↦ m a) this

/-- **Products of ind-smooth maps (Lemma `07F3`).** If `Λᵢ` is a filtered colimit of smooth
`Rᵢ`-algebras for `i = 1, 2`, then `Λ₁ × Λ₂` is a filtered colimit of smooth
`(R₁ × R₂)`-algebras. -/
theorem indSmooth_prod (R₁ R₂ Λ₁ Λ₂ : Type u) [CommRing R₁] [CommRing R₂]
    [CommRing Λ₁] [CommRing Λ₂] [Algebra R₁ Λ₁] [Algebra R₂ Λ₂]
    (h₁ : IndSmooth R₁ Λ₁) (h₂ : IndSmooth R₂ Λ₂) :
    letI : Algebra (R₁ × R₂) (Λ₁ × Λ₂) :=
      ((algebraMap R₁ Λ₁).prodMap (algebraMap R₂ Λ₂)).toAlgebra
    IndSmooth (R₁ × R₂) (Λ₁ × Λ₂) := by
  let : Algebra (R₁ × R₂) (Λ₁ × Λ₂) :=
    ((algebraMap R₁ Λ₁).prodMap (algebraMap R₂ Λ₂)).toAlgebra
  let : Algebra (R₁ × R₂) R₁ := (RingHom.fst R₁ R₂).toAlgebra
  let : Algebra (R₁ × R₂) R₂ := (RingHom.snd R₁ R₂).toAlgebra
  let : Algebra (R₁ × R₂) Λ₁ := ((algebraMap R₁ Λ₁).comp (RingHom.fst R₁ R₂)).toAlgebra
  let : Algebra (R₁ × R₂) Λ₂ := ((algebraMap R₂ Λ₂).comp (RingHom.snd R₁ R₂)).toAlgebra
  let : IsScalarTower (R₁ × R₂) R₁ Λ₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower (R₁ × R₂) R₂ Λ₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [indSmooth_iff_exists_factorization] at h₁ h₂ ⊢
  intro A instA algA hfp φ
  let := algA
  let : Algebra.FinitePresentation (R₁ × R₂) A := hfp
  -- the two components of `φ`
  let p₁ : (Λ₁ × Λ₂) →ₐ[R₁ × R₂] Λ₁ :=
    { toRingHom := RingHom.fst Λ₁ Λ₂, commutes' := fun _ ↦ rfl }
  let p₂ : (Λ₁ × Λ₂) →ₐ[R₁ × R₂] Λ₂ :=
    { toRingHom := RingHom.snd Λ₁ Λ₂, commutes' := fun _ ↦ rfl }
  -- base change of `A` to the two factors
  let : Algebra R₁ (R₁ ⊗[R₁ × R₂] A) := Algebra.TensorProduct.leftAlgebra
  let : Algebra R₂ (R₂ ⊗[R₁ × R₂] A) := Algebra.TensorProduct.leftAlgebra
  have : Algebra.FinitePresentation R₁ (R₁ ⊗[R₁ × R₂] A) :=
    Algebra.FinitePresentation.baseChange R₁
  have : Algebra.FinitePresentation R₂ (R₂ ⊗[R₁ × R₂] A) :=
    Algebra.FinitePresentation.baseChange R₂
  let ψ₁ : (R₁ ⊗[R₁ × R₂] A) →ₐ[R₁] Λ₁ :=
    AlgHom.liftEquiv (R₁ × R₂) R₁ A Λ₁ (p₁.comp φ)
  let ψ₂ : (R₂ ⊗[R₁ × R₂] A) →ₐ[R₂] Λ₂ :=
    AlgHom.liftEquiv (R₁ × R₂) R₂ A Λ₂ (p₂.comp φ)
  obtain ⟨B₁, instB₁, algB₁, hB₁s, g₁, k₁, hgk₁⟩ :=
    h₁ (R₁ ⊗[R₁ × R₂] A) inferInstance inferInstance inferInstance ψ₁
  obtain ⟨B₂, instB₂, algB₂, hB₂s, g₂, k₂, hgk₂⟩ :=
    h₂ (R₂ ⊗[R₁ × R₂] A) inferInstance inferInstance inferInstance ψ₂
  let := instB₁
  let := algB₁
  let := instB₂
  let := algB₂
  let : Algebra (R₁ × R₂) B₁ := ((algebraMap R₁ B₁).comp (RingHom.fst R₁ R₂)).toAlgebra
  let : Algebra (R₁ × R₂) B₂ := ((algebraMap R₂ B₂).comp (RingHom.snd R₁ R₂)).toAlgebra
  let : IsScalarTower (R₁ × R₂) R₁ B₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower (R₁ × R₂) R₂ B₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let algB : Algebra (R₁ × R₂) (B₁ × B₂) :=
    ((algebraMap R₁ B₁).prodMap (algebraMap R₂ B₂)).toAlgebra
  -- the two legs into the factors, and their product
  let γ₁ : A →ₐ[R₁ × R₂] B₁ :=
    (g₁.restrictScalars (R₁ × R₂)).comp Algebra.TensorProduct.includeRight
  let γ₂ : A →ₐ[R₁ × R₂] B₂ :=
    (g₂.restrictScalars (R₁ × R₂)).comp Algebra.TensorProduct.includeRight
  refine ⟨B₁ × B₂, inferInstance, algB,
    Algebra.Smooth.prod R₁ B₁ R₂ B₂ hB₁s hB₂s,
    { toRingHom := γ₁.toRingHom.prod γ₂.toRingHom
      commutes' := fun r ↦ Prod.ext (γ₁.commutes r) (γ₂.commutes r) },
    { toRingHom := k₁.toRingHom.prodMap k₂.toRingHom
      commutes' := fun r ↦ Prod.ext (k₁.commutes r.1) (k₂.commutes r.2) }, ?_⟩
  ext a
  · exact apply_includeRight_of_comp_eq_liftEquiv _ _ _ _ _ _ g₁ k₁ hgk₁ a
  · exact apply_includeRight_of_comp_eq_liftEquiv _ _ _ _ _ _ g₂ k₂ hgk₂ a

/-- Splitting off the last factor of a finite product of rings. -/
private def piFinSuccRingEquiv (n : ℕ) (R : Fin (n + 1) → Type u) [∀ i, CommRing (R i)] :
    (∀ i, R i) ≃+* (R (Fin.last n) × (∀ i : Fin n, R i.castSucc)) where
  toFun f := (f (Fin.last n), fun i ↦ f i.castSucc)
  invFun p := Fin.lastCases p.1 p.2
  left_inv f := by
    funext i
    induction i using Fin.lastCases <;> simp [Fin.lastCases]
  right_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · simp [Fin.lastCases]
    · funext i; simp [Fin.lastCases]
  map_mul' f g := by ext <;> rfl
  map_add' f g := by ext <;> rfl

/-- **Finite products of ind-smooth maps.** If `Λ i` is a filtered colimit of smooth
`R i`-algebras for each `i`, then `∀ i, Λ i` is a filtered colimit of smooth
`(∀ i, R i)`-algebras. -/
theorem indSmooth_pi_fin : ∀ (n : ℕ) (R Λ : Fin n → Type u) [∀ i, CommRing (R i)]
    [∀ i, CommRing (Λ i)] [∀ i, Algebra (R i) (Λ i)],
    (∀ i, IndSmooth (R i) (Λ i)) → IndSmooth (∀ i, R i) (∀ i, Λ i) := by
  intro n
  induction n with
  | zero =>
      intro R Λ _ _ _ _
      have : Subsingleton (∀ i : Fin 0, R i) := inferInstance
      have : Subsingleton (∀ i : Fin 0, Λ i) := inferInstance
      have hb : Function.Bijective (algebraMap (∀ i : Fin 0, R i) (∀ i : Fin 0, Λ i)) :=
        ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
      exact indSmooth_of_smooth _ _
        (RingHom.smooth_algebraMap.mp (RingHom.Smooth.of_bijective hb))
  | succ n ih =>
      intro R Λ _ _ _ h
      let R₀ := R (Fin.last n)
      let Λ₀ := Λ (Fin.last n)
      let R' : Fin n → Type u := fun i ↦ R i.castSucc
      let Λ' : Fin n → Type u := fun i ↦ Λ i.castSucc
      let : ∀ i, CommRing (R' i) := fun _ ↦ inferInstance
      let : ∀ i, CommRing (Λ' i) := fun _ ↦ inferInstance
      let : ∀ i, Algebra (R' i) (Λ' i) := fun _ ↦ inferInstance
      let : Algebra (R₀ × (∀ i, R' i)) (Λ₀ × (∀ i, Λ' i)) :=
        ((algebraMap R₀ Λ₀).prodMap (algebraMap (∀ i, R' i) (∀ i, Λ' i))).toAlgebra
      have hprod : IndSmooth (R₀ × (∀ i, R' i)) (Λ₀ × (∀ i, Λ' i)) :=
        indSmooth_prod R₀ (∀ i, R' i) Λ₀ (∀ i, Λ' i) (h (Fin.last n))
          (ih R' Λ' fun i ↦ h i.castSucc)
      have hfwd : ∀ f : (∀ i, R i),
          piFinSuccRingEquiv n Λ (algebraMap (∀ i, R i) (∀ i, Λ i) f) =
            algebraMap (R₀ × (∀ i, R' i)) (Λ₀ × (∀ i, Λ' i)) (piFinSuccRingEquiv n R f) :=
        fun _ ↦ rfl
      refine indSmooth_of_ringEquiv _ _ _ _
        (piFinSuccRingEquiv n R).symm (piFinSuccRingEquiv n Λ).symm (fun x ↦ ?_) hprod
      apply (piFinSuccRingEquiv n Λ).injective
      rw [RingEquiv.apply_symm_apply, hfwd ((piFinSuccRingEquiv n R).symm x),
        RingEquiv.apply_symm_apply]

end Products

end Stacks.Smoothing

end
