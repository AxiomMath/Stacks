module

public import Mathlib
public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotientCompletionMap
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Tactic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuasiFinite
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.Kaehler.SmoothRingMapsInTheNoetherianCase
public import StacksFrontier.RingTheory.FormalFibres.RingMapProperty.QuasiFiniteFormalFibres

@[expose] public section

/-!
# A criterion for rings with prescribed formal fibres

Stacks Project, Chapter 15 "More on Algebra", Tag 0BIS.

Let `P` be an isomorphism-invariant property of ring maps. For a Noetherian ring `R`, requiring
`P` for every formal fibre of every local ring `Rₚ` is equivalent to requiring it for the
fibres obtained by first passing to `R / q`, localizing at `p`, and completing, for every pair
of prime ideals `q ≤ p`.

## Main definitions

There are no new definitions.

## Main results

* `propertyRing_iff_quotientCompletion_fibers`: the quotient-completion criterion
  for a `P`-ring.

## Implementation notes

The localization `(R / q)ₚ` is represented by localization at the image of the complement of
`p`. The map on the right is the canonical inclusion of the residue field into the tensor
product. Isomorphism-invariance, implicit in the source's phrase "property of ring maps", is
part of `RingMapProperty`.

## References

* [Stacks Project, Tag 0BIS](https://stacks.math.columbia.edu/tag/0BIS)

-/

/-! ### Stacks Tag 0BIS -/

section

section

open IsLocalRing TensorProduct
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

/-- Completion commutes with a quotient, as an algebra over the quotient ring. -/
private noncomputable def completionQuotientAlgEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    let C := AdicCompletion (maximalIdeal R) R
    let J := I.map (algebraMap R C)
    (C ⧸ J) ≃ₐ[R ⧸ I]
      AdicCompletion (maximalIdeal (R ⧸ I)) (R ⧸ I) := by
  let C := AdicCompletion (maximalIdeal R) R
  let J := I.map (algebraMap R C)
  let f := adicCompletionMapQuotient I
  let g : (C ⧸ J) ≃+* AdicCompletion (maximalIdeal (R ⧸ I)) (R ⧸ I) :=
    (Ideal.quotEquivOfEq (ker_adicCompletionMapQuotient I).symm).trans
      (RingHom.quotientKerEquivOfSurjective
        (adicCompletionMapQuotient_surjective I))
  exact AlgEquiv.ofRingEquiv (f := g) (by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change g (algebraMap (R ⧸ I) (C ⧸ J) (Ideal.Quotient.mk I r)) =
      algebraMap (R ⧸ I) (AdicCompletion (maximalIdeal (R ⧸ I)) (R ⧸ I))
        (Ideal.Quotient.mk I r)
    simp only [g, RingEquiv.trans_apply]
    exact completionQuotientMap_algebraMap I r)

/-- Tensoring a quotient algebra with an algebra of the quotient can be performed over either
the original ring or the quotient. -/
private noncomputable def tensorQuotientBaseChangeEquiv
    {R : Type*} [CommRing R] (I : Ideal R)
    (C : Type*) [CommRing C] [Algebra R C]
    (K : Type*) [CommRing K] [Algebra (R ⧸ I) K] [Algebra R K]
    [IsScalarTower R (R ⧸ I) K] :
    (C ⊗[R] K) ≃ₐ[K]
      ((C ⧸ I.map (algebraMap R C)) ⊗[R ⧸ I] K) :=
  (Algebra.TensorProduct.commRight R K C).symm.trans
    ((Algebra.TensorProduct.cancelBaseChange R (R ⧸ I) K K C).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl)
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I).symm).trans
        (Algebra.TensorProduct.commRight (R ⧸ I) K
          (C ⧸ I.map (algebraMap R C)))))

/-- Extension of scalars carries an isomorphism of algebras to an isomorphism of the tensor
products, preserving the inclusion of the right tensor factor. -/
private noncomputable def tensorCongrRight
    {Q : Type*} [CommRing Q] {C D : Type*} [CommRing C] [CommRing D]
    [Algebra Q C] [Algebra Q D] (K : Type*) [CommRing K] [Algebra Q K]
    (e : C ≃ₐ[Q] D) :
    (C ⊗[Q] K) ≃ₐ[K] (D ⊗[Q] K) :=
  (Algebra.TensorProduct.commRight Q K C).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl) e).trans
      (Algebra.TensorProduct.commRight Q K D))

/-- Tensoring two algebras over a localization agrees with tensoring them over the original
ring. The equivalence is linear over the right tensor factor. -/
private noncomputable def tensorLocalizationEquiv
    {R : Type*} [CommRing R] (M : Submonoid R)
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization M A]
    (C K : Type*) [CommRing C] [CommRing K]
    [Algebra A C] [Algebra A K] [Algebra R C] [Algebra R K]
    [IsScalarTower R A C] [IsScalarTower R A K] :
    (C ⊗[A] K) ≃ₐ[K] (C ⊗[R] K) := by
  letI : TensorProduct.CompatibleSMul R A K C :=
    IsLocalization.tensorProduct_compatibleSMul M A K C
  letI : TensorProduct.CompatibleSMul A R K C := by infer_instance
  exact (Algebra.TensorProduct.commRight A K C).symm.trans
    ((Algebra.TensorProduct.equivOfCompatibleSMul R A K K C).trans
      (Algebra.TensorProduct.commRight R K C))

/-- Localization does not change the residue field at a prime lying below the localizing prime. -/
private noncomputable def residueFieldAlgEquivLocalization
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    (q : PrimeSpectrum R) (r : PrimeSpectrum A)
    (hqr : q.asIdeal = r.asIdeal.comap (algebraMap R A)) :
    q.asIdeal.ResidueField ≃ₐ[R] r.asIdeal.ResidueField :=
  AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ q.asIdeal r.asIdeal (Algebra.ofId R A) hqr)
    (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_isLocalization M A)
      q.asIdeal r.asIdeal hqr)

/-! ### Localization of a prime quotient -/

/-- The image of a prime in a quotient by a smaller prime. -/
private def quotientPrime {R : Type*} [CommRing R] (p q : PrimeSpectrum R)
    (hqp : q.asIdeal ≤ p.asIdeal) : PrimeSpectrum (R ⧸ q.asIdeal) :=
  ⟨p.asIdeal.map (Ideal.Quotient.mk q.asIdeal),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      simpa [Ideal.mk_ker] using hqp)⟩

/-- The image of the complement of `p` in `R / q` is the complement of `p / q`. -/
private theorem map_primeCompl_eq_primeCompl_quotientPrime
    {R : Type*} [CommRing R] (p q : PrimeSpectrum R)
    (hqp : q.asIdeal ≤ p.asIdeal) :
    Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl =
      (quotientPrime p q hqp).asIdeal.primeCompl := by
  have hpbar : (quotientPrime p q hqp).asIdeal.comap
      (Ideal.Quotient.mk q.asIdeal) = p.asIdeal := by
    change (p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).comap
      (Ideal.Quotient.mk q.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqp
  calc
    Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl =
        Submonoid.map (Ideal.Quotient.mk q.asIdeal)
          ((quotientPrime p q hqp).asIdeal.primeCompl.comap
            (Ideal.Quotient.mk q.asIdeal)) := by
              congr 1
              ext r
              simp [Ideal.mem_primeCompl_iff, ← Ideal.mem_comap, hpbar]
    _ = (quotientPrime p q hqp).asIdeal.primeCompl :=
      Submonoid.map_comap_eq_of_surjective Ideal.Quotient.mk_surjective _

/-- The localization of `R / q` at the image of the complement of `p` is the localization at
the prime `p / q`. -/
private theorem isLocalization_atPrime_quotientLocalization
    {R : Type*} [CommRing R] (p q : PrimeSpectrum R)
    (hqp : q.asIdeal ≤ p.asIdeal) :
    IsLocalization.AtPrime
      (Localization (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl))
      (quotientPrime p q hqp).asIdeal := by
  change IsLocalization (quotientPrime p q hqp).asIdeal.primeCompl
    (Localization (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl))
  rw [← map_primeCompl_eq_primeCompl_quotientPrime p q hqp]
  infer_instance

/-- The localization of `R / q` at the image of the complement of `p` is local. -/
private theorem isLocalRing_quotientLocalization
    {R : Type*} [CommRing R] (p q : PrimeSpectrum R)
    (hqp : q.asIdeal ≤ p.asIdeal) :
    IsLocalRing (Localization
      (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)) :=
  have := isLocalization_atPrime_quotientLocalization p q hqp
  IsLocalization.AtPrime.isLocalRing _ (quotientPrime p q hqp).asIdeal

/-- The ideal used to complete `(R / q)ₚ` is its maximal ideal. -/
private theorem quotientLocalization_maximalIdeal
    {R : Type*} [CommRing R] (p q : PrimeSpectrum R)
    (hqp : q.asIdeal ≤ p.asIdeal) :
    let Q := R ⧸ q.asIdeal
    let S := Localization
      (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
    (p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).map (algebraMap Q S) =
      @maximalIdeal S _ (isLocalRing_quotientLocalization p q hqp) := by
  let := isLocalRing_quotientLocalization p q hqp
  have := isLocalization_atPrime_quotientLocalization p q hqp
  change (quotientPrime p q hqp).asIdeal.map _ = maximalIdeal _
  exact IsLocalization.AtPrime.map_eq_maximalIdeal _ _

/-- Localization commutes with taking the quotient by a prime below the localizing prime. -/
private noncomputable def quotientLocalizationAlgEquiv
    {R : Type*} [CommRing R] (p q : PrimeSpectrum R) :
    let Q := R ⧸ q.asIdeal
    let S := Localization
      (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
    let A := Localization.AtPrime p.asIdeal
    let J := q.asIdeal.map (algebraMap R A)
    S ≃ₐ[Q] A ⧸ J := by
  dsimp
  letI : IsLocalization
      (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
      (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap R (Localization.AtPrime p.asIdeal))) := by
    change IsLocalization
      (Algebra.algebraMapSubmonoid (R ⧸ q.asIdeal) p.asIdeal.primeCompl)
      (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap R (Localization.AtPrime p.asIdeal)))
    infer_instance
  exact IsLocalization.algEquiv
    (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
    (Localization
      (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl))
    (Localization.AtPrime p.asIdeal ⧸
      q.asIdeal.map (algebraMap R (Localization.AtPrime p.asIdeal)))

/-- A formal fiber over a localization is the same tensor product over the original ring,
after identifying the residue fields. -/
private noncomputable def localizedFiberRingEquiv
    {R : Type*} [CommRing R] (p : PrimeSpectrum R)
    (r : PrimeSpectrum (Localization.AtPrime p.asIdeal))
    (q : PrimeSpectrum R)
    (hqr : q.asIdeal = r.asIdeal.comap
      (algebraMap R (Localization.AtPrime p.asIdeal))) :
    let A := Localization.AtPrime p.asIdeal
    let C := AdicCompletion (maximalIdeal A) A
    (C ⊗[A] r.asIdeal.ResidueField) ≃+*
      (C ⊗[R] q.asIdeal.ResidueField) := by
  let A := Localization.AtPrime p.asIdeal
  let C := AdicCompletion (maximalIdeal A) A
  let e : q.asIdeal.ResidueField ≃ₐ[R] r.asIdeal.ResidueField :=
    residueFieldAlgEquivLocalization p.asIdeal.primeCompl q r hqr
  let E₁ : (C ⊗[A] r.asIdeal.ResidueField) ≃ₐ[r.asIdeal.ResidueField]
      (C ⊗[R] r.asIdeal.ResidueField) :=
    tensorLocalizationEquiv p.asIdeal.primeCompl A C r.asIdeal.ResidueField
  let E₂ : (C ⊗[R] r.asIdeal.ResidueField) ≃ₐ[R]
      (C ⊗[R] q.asIdeal.ResidueField) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl) e.symm
  exact E₁.toRingEquiv.trans E₂.toRingEquiv

/-- The localization comparison carries the canonical residue field map to the canonical
residue field map after identifying the two fields. -/
private theorem localizedFiberRingEquiv_includeRight
    {R : Type*} [CommRing R] (p : PrimeSpectrum R)
    (r : PrimeSpectrum (Localization.AtPrime p.asIdeal))
    (q : PrimeSpectrum R)
    (hqr : q.asIdeal = r.asIdeal.comap
      (algebraMap R (Localization.AtPrime p.asIdeal)))
    (x : q.asIdeal.ResidueField) :
    let A := Localization.AtPrime p.asIdeal
    let C := AdicCompletion (maximalIdeal A) A
    localizedFiberRingEquiv p r q hqr
      (Algebra.TensorProduct.includeRight (R := A) (A := C)
        (B := r.asIdeal.ResidueField)
        ((residueFieldAlgEquivLocalization p.asIdeal.primeCompl q r hqr) x)) =
      Algebra.TensorProduct.includeRight (R := R) (A := C)
        (B := q.asIdeal.ResidueField) x := by
  simp [localizedFiberRingEquiv, tensorLocalizationEquiv,
    Algebra.TensorProduct.equivOfCompatibleSMul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.includeRight_apply]

/-- The two presentations of a formal fiber admit an equivalence over the residue field. -/
private theorem quotientFormalFiberAlgEquiv_nonempty
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p q : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    let Q := R ⧸ q.asIdeal
    let S := Localization
      (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
    let C := AdicCompletion
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (Localization.AtPrime p.asIdeal)
    Nonempty ((C ⊗[R] q.asIdeal.ResidueField) ≃ₐ[q.asIdeal.ResidueField]
      ((AdicCompletion
        ((p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).map (algebraMap Q S)) S)
        ⊗[Q] q.asIdeal.ResidueField)) := by
  classical
  let Q := R ⧸ q.asIdeal
  let S := Localization
    (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
  let A := Localization.AtPrime p.asIdeal
  let J := q.asIdeal.map (algebraMap R A)
  let C := AdicCompletion (maximalIdeal A) A
  let K := q.asIdeal.ResidueField
  have hJle : J ≤ maximalIdeal A := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hqp
  have hJne : J ≠ ⊤ := by
    intro h
    exact (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hJle))
  let : IsLocalRing (A ⧸ J) := isLocalRing_quotient hJne
  let : IsLocalRing S := isLocalRing_quotientLocalization p q hqp
  let e : S ≃ₐ[Q] A ⧸ J := quotientLocalizationAlgEquiv p q
  have he : maximalIdeal (A ⧸ J) = (maximalIdeal S).map (e : S →+* A ⧸ J) :=
    (IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv).symm
  let F := Classical.choice (AdicCompletion.nonempty_algEquiv_of_algEquiv e
    (maximalIdeal S) (maximalIdeal (A ⧸ J)) he)
  have hmap : q.asIdeal.map (algebraMap R C) = J.map (algebraMap A C) := by
    change q.asIdeal.map (algebraMap R C) =
      (q.asIdeal.map (algebraMap R A)).map (algebraMap A C)
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A C]
  let : Algebra Q (C ⧸ J.map (algebraMap A C)) :=
    Algebra.compHom _ (algebraMap Q (A ⧸ J))
  let : IsScalarTower Q (A ⧸ J) (C ⧸ J.map (algebraMap A C)) :=
    .of_algebraMap_eq' rfl
  let G : (C ⧸ J.map (algebraMap A C)) ≃ₐ[Q]
      AdicCompletion (maximalIdeal S) S :=
    (completionQuotientAlgEquiv J).restrictScalars Q |>.trans F.symm
  let H₀ : (C ⧸ q.asIdeal.map (algebraMap R C)) ≃ₐ[Q]
      (C ⧸ J.map (algebraMap A C)) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq hmap) (by
      intro x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
  let H : (C ⧸ q.asIdeal.map (algebraMap R C)) ≃ₐ[Q]
      AdicCompletion (maximalIdeal S) S := H₀.trans G
  have E : (C ⊗[R] K) ≃ₐ[K]
      (AdicCompletion (maximalIdeal S) S ⊗[Q] K) :=
    (tensorQuotientBaseChangeEquiv q.asIdeal C K).trans
      (tensorCongrRight K H)
  change Nonempty ((C ⊗[R] K) ≃ₐ[K]
    (AdicCompletion
      ((p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).map (algebraMap Q S)) S ⊗[Q] K))
  rw [quotientLocalization_maximalIdeal p q hqp]
  exact ⟨E⟩

/-- The canonical algebra equivalence between the two formal-fiber presentations. -/
private noncomputable def quotientFormalFiberAlgEquiv
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p q : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    let Q := R ⧸ q.asIdeal
    let S := Localization
      (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
    let C := AdicCompletion
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (Localization.AtPrime p.asIdeal)
    (C ⊗[R] q.asIdeal.ResidueField) ≃ₐ[q.asIdeal.ResidueField]
      ((AdicCompletion
        ((p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).map (algebraMap Q S)) S)
        ⊗[Q] q.asIdeal.ResidueField) :=
  Classical.choice (quotientFormalFiberAlgEquiv_nonempty p q hqp)

attribute [local irreducible] quotientFormalFiberAlgEquiv

/-- The right tensor inclusion is the algebra map for the right tensor factor. -/
private theorem includeRight_toRingHom_eq_algebraMap
    {R A K : Type*} [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] :
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K)).toRingHom =
      algebraMap K (A ⊗[R] K) := rfl

/-- Pointwise form of the right tensor inclusion identity. -/
private theorem includeRight_apply_eq_algebraMap
    {R A K : Type*} [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] (x : K) :
    Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K) x =
      algebraMap K (A ⊗[R] K) x :=
  congrArg (fun f : K →+* (A ⊗[R] K) => f x)
    includeRight_toRingHom_eq_algebraMap

/-- An isomorphism-invariant property of ring maps has the same truth value on isomorphic
arrows. -/
private theorem ringMapProperty_iff_of_equiv
    (P : RingMapProperty.{u, u})
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : C →+* D)
    (e : C ≃+* A) (E : B ≃+* D)
    (h : g = E.toRingHom.comp (f.comp e.toRingHom)) :
    P f ↔ P g := by
  constructor
  · intro hf
    rw [h]
    exact P.respectsIso.2 (E.toRingHom.comp f) e
      (P.respectsIso.1 f E hf)
  · intro hg
    have h₁ : P (g.comp e.symm.toRingHom) :=
      P.respectsIso.2 g e.symm hg
    have h₂ : P (E.symm.toRingHom.comp (g.comp e.symm.toRingHom)) :=
      P.respectsIso.1 _ E.symm h₁
    convert h₂ using 1
    rw [h]
    ext x
    simp

-- The two compatible fiber isomorphisms give a large dependent ring-map comparison.
/-- The property of a formal fiber is equivalent to the property of the quotient-completion
presentation of that fiber. -/
private theorem formalFiber_property_iff_quotientCompletion
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (P : RingMapProperty.{u, u})
    (p q : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal)
    (r : PrimeSpectrum (Localization.AtPrime p.asIdeal))
    (hqr : q.asIdeal = r.asIdeal.comap
      (algebraMap R (Localization.AtPrime p.asIdeal))) :
    let A := Localization.AtPrime p.asIdeal
    let C := AdicCompletion (maximalIdeal A) A
    let Q := R ⧸ q.asIdeal
    let S := Localization
      (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
    P (Algebra.TensorProduct.includeRight (R := A) (A := C)
      (B := r.asIdeal.ResidueField)).toRingHom ↔
    P (Algebra.TensorProduct.includeRight (R := Q)
      (A := AdicCompletion
        ((p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).map (algebraMap Q S)) S)
      (B := q.asIdeal.ResidueField)).toRingHom := by
  dsimp only
  let A := Localization.AtPrime p.asIdeal
  let C := AdicCompletion (maximalIdeal A) A
  let Q := R ⧸ q.asIdeal
  let S := Localization
    (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
  let D := AdicCompletion
    ((p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).map (algebraMap Q S)) S
  let K := q.asIdeal.ResidueField
  let e : K ≃ₐ[R] r.asIdeal.ResidueField :=
    residueFieldAlgEquivLocalization p.asIdeal.primeCompl q r hqr
  let E₁ : (C ⊗[A] r.asIdeal.ResidueField) ≃+* (C ⊗[R] K) :=
    localizedFiberRingEquiv p r q hqr
  let E₂ : (C ⊗[R] K) ≃ₐ[K] (D ⊗[Q] K) :=
    quotientFormalFiberAlgEquiv p q hqp
  have h₁ : (Algebra.TensorProduct.includeRight (R := R) (A := C)
      (B := K)).toRingHom = E₁.toRingHom.comp
      ((Algebra.TensorProduct.includeRight (R := A) (A := C)
        (B := r.asIdeal.ResidueField)).toRingHom.comp e.toRingEquiv.toRingHom) := by
    exact RingHom.ext fun x => (localizedFiberRingEquiv_includeRight p r q hqr x).symm
  have h₂ : (Algebra.TensorProduct.includeRight (R := Q) (A := D)
      (B := K)).toRingHom = E₂.toRingEquiv.toRingHom.comp
      ((Algebra.TensorProduct.includeRight (R := R) (A := C)
        (B := K)).toRingHom.comp (RingEquiv.refl K).toRingHom) := by
    apply RingHom.ext
    intro x
    change Algebra.TensorProduct.includeRight (R := Q) (A := D) (B := K) x =
      E₂ (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := K) x)
    rw [includeRight_apply_eq_algebraMap, includeRight_apply_eq_algebraMap]
    exact (E₂.commutes x).symm
  exact (ringMapProperty_iff_of_equiv P _ _ e.toRingEquiv E₁ h₁).trans
    (ringMapProperty_iff_of_equiv P _ _ (RingEquiv.refl K) E₂.toRingEquiv h₂)

/-- **Stacks 0BIS.** A Noetherian ring has property `P` on all the formal fibres of its
localizations at prime ideals if and only if the corresponding completed localizations of
its prime quotients have property `P` after extension to the residue field. -/
@[stacks 0BIS]
public theorem propertyRing_iff_quotientCompletion_fibers
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (P : RingMapProperty.{u, u}) :
    IsPRing P R ↔
    (∀ (p q : PrimeSpectrum R) (_hqp : q.asIdeal ≤ p.asIdeal),
      let Q := R ⧸ q.asIdeal
      let S := Localization
        (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
      P (Algebra.TensorProduct.includeRight (R := Q)
        (A := AdicCompletion
          ((p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).map (algebraMap Q S)) S)
        (B := q.asIdeal.ResidueField)).toRingHom) := by
  constructor
  · intro h p q hqp
    let e := IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime p.asIdeal) p.asIdeal
    let r : PrimeSpectrum (Localization.AtPrime p.asIdeal) := e.symm ⟨q, hqp⟩
    have hqr : q.asIdeal = r.asIdeal.comap
        (algebraMap R (Localization.AtPrime p.asIdeal)) :=
      (congrArg (fun x : Set.Iic p => x.val.asIdeal) (e.apply_symm_apply ⟨q, hqp⟩)).symm
    exact (formalFiber_property_iff_quotientCompletion P p q hqp r hqr).mp (h.2 p r)
  · intro h
    refine ⟨inferInstance, ?_⟩
    intro p r
    let e := IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime p.asIdeal) p.asIdeal
    let q : PrimeSpectrum R := (e r).val
    have hqp : q.asIdeal ≤ p.asIdeal := (e r).property
    have hqr : q.asIdeal = r.asIdeal.comap
        (algebraMap R (Localization.AtPrime p.asIdeal)) := rfl
    exact (formalFiber_property_iff_quotientCompletion P p q hqp r hqr).mpr (h p q hqp)

end

end

end
