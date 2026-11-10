module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Quotients of a ring map by an extended ideal

Let `g : A →+* A'` be a ring map and let `I` be an ideal of `A`. Since `I ≤ (I.map g).comap g`,
the map `g` descends to a ring map `A ⧸ I →+* A' ⧸ I.map g`, namely
`Ideal.quotientMap (I.map g) g`. This descended map inherits any property of ring maps that is
stable under base change, since `A' ⧸ I.map g` is the base change `(A ⧸ I) ⊗[A] A'` of `A'` along
`A → A ⧸ I`.

## Main results

* `RingHom.IsStableUnderBaseChange.quotientMap`: if a property `P` of ring maps is stable under
  base change and respects isomorphisms, and `g` satisfies `P`, then so does the induced map
  `A ⧸ I →+* A' ⧸ I.map g`.
* `RingHom.FiniteType.quotientMap`, `RingHom.FinitePresentation.quotientMap`,
  `RingHom.FaithfullyFlat.quotientMap`: the instances of the above for finite type, finite
  presentation and faithful flatness.
* `RingHom.Etale.finitePresentation`: an étale ring map is of finite presentation.
-/

@[expose] public section

universe u

open TensorProduct

namespace RingHom

/-- If `P` is stable under base change and respects isomorphisms, then `P (algebraMap A A')`
implies `P (algebraMap (A ⧸ I) (A' ⧸ I.map (algebraMap A A')))`. -/
private theorem IsStableUnderBaseChange.algebraMap_quotient
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hP : RingHom.IsStableUnderBaseChange @P) (hiso : RingHom.RespectsIso @P)
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A'] (hg : P (algebraMap A A'))
    (I : Ideal A) :
    P (algebraMap (A ⧸ I) (A' ⧸ I.map (algebraMap A A'))) := by
  have h1 : P (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] A')) := hP.tensorProduct (A ⧸ I) hg
  have h2 := hiso.1 (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] A'))
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A' I).symm.toRingEquiv h1
  have key : RingHom.comp
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A' I).symm.toRingEquiv.toRingHom
      (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] A'))
      = algebraMap (A ⧸ I) (A' ⧸ I.map (algebraMap A A')) := by
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A' I).symm
        (Ideal.Quotient.mk I a ⊗ₜ[A] 1) = _
    rw [AlgEquiv.symm_apply_eq, Ideal.Quotient.algebraMap_quotient_map_quotient,
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Algebra.algebraMap_eq_smul_one,
      ← smul_tmul, ← Algebra.algebraMap_eq_smul_one, Ideal.Quotient.algebraMap_eq]
  rwa [key] at h2

/-- If a property `P` of ring maps is stable under base change and respects isomorphisms, then
it passes from `g : A →+* A'` to the induced map `A ⧸ I →+* A' ⧸ I.map g` on quotients by an
ideal `I` of `A` and its extension along `g`. -/
theorem IsStableUnderBaseChange.quotientMap
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hP : RingHom.IsStableUnderBaseChange @P) (hiso : RingHom.RespectsIso @P)
    {A A' : Type u} [CommRing A] [CommRing A'] (g : A →+* A') (hg : P g) (I : Ideal A) :
    P (Ideal.quotientMap (I.map g) g (Ideal.map_le_iff_le_comap.mp le_rfl)) := by
  algebraize [g]
  exact hP.algebraMap_quotient hiso (by rwa [g.algebraMap_toAlgebra]) I

/-- If `g : A →+* A'` is of finite type and `I` is an ideal of `A`, then the induced map
`A ⧸ I →+* A' ⧸ I.map g` is of finite type. -/
theorem FiniteType.quotientMap {A A' : Type u} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : g.FiniteType) (I : Ideal A) :
    (Ideal.quotientMap (I.map g) g (Ideal.map_le_iff_le_comap.mp le_rfl)).FiniteType :=
  RingHom.finiteType_isStableUnderBaseChange.quotientMap RingHom.finiteType_respectsIso g hg I

/-- If `g : A →+* A'` is of finite presentation and `I` is an ideal of `A`, then the induced map
`A ⧸ I →+* A' ⧸ I.map g` is of finite presentation. -/
theorem FinitePresentation.quotientMap {A A' : Type u} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : g.FinitePresentation) (I : Ideal A) :
    (Ideal.quotientMap (I.map g) g (Ideal.map_le_iff_le_comap.mp le_rfl)).FinitePresentation :=
  RingHom.finitePresentation_isStableUnderBaseChange.quotientMap
    RingHom.finitePresentation_respectsIso g hg I

/-- If `g : A →+* A'` is faithfully flat and `I` is an ideal of `A`, then the induced map
`A ⧸ I →+* A' ⧸ I.map g` is faithfully flat. -/
theorem FaithfullyFlat.quotientMap {A A' : Type u} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : g.FaithfullyFlat) (I : Ideal A) :
    (Ideal.quotientMap (I.map g) g (Ideal.map_le_iff_le_comap.mp le_rfl)).FaithfullyFlat :=
  RingHom.FaithfullyFlat.isStableUnderBaseChange.quotientMap
    RingHom.FaithfullyFlat.respectsIso g hg I

/-- An étale ring map is of finite presentation. -/
theorem Etale.finitePresentation {A A' : Type*} [CommRing A] [CommRing A'] {g : A →+* A'}
    (hg : g.Etale) : g.FinitePresentation :=
  (RingHom.Etale.iff_flat_and_formallyUnramified.mp hg).2.2

end RingHom

end
