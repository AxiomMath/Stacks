module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation

/-!
# Étale and faithfully flat algebras are stable under finite coproducts

Being étale over `A`, and having faithfully flat structure map, are properties of an object of
`CommAlgCat A` that are invariant under isomorphism and stable under finite coproducts. The
binary case is the tensor product, the general finite case follows by induction on `Fin n` after
transporting along an equivalence with `Fin n`.

An étale algebra is moreover a finitely presentable object of `CommAlgCat A`, which is what makes
a filtered colimit of étale algebras an ind-object of the étale ones.

## Main results

* `AlgebraicGeometry.ProEtale.etale_finite_coproduct`
* `AlgebraicGeometry.ProEtale.faithfullyFlat_finite_coproduct`
* `AlgebraicGeometry.ProEtale.etale_isFinitelyPresentable`
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- Being étale over `A` is invariant under isomorphism of `A`-algebras. -/
lemma etaleObject_of_iso {A : Type u} [CommRing A]
    {X Y : CommAlgCat.{u} A} (e : X ≅ Y) (h : Algebra.Etale A X) :
    Algebra.Etale A Y :=
  Algebra.Etale.of_equiv (CommAlgCat.algEquivOfIso e)

/-- Having faithfully flat structure map is invariant under isomorphism of `A`-algebras. -/
lemma faithfullyFlatObject_of_iso {A : Type u} [CommRing A]
    {X Y : CommAlgCat.{u} A} (e : X ≅ Y)
    (h : (algebraMap A X).FaithfullyFlat) :
    (algebraMap A Y).FaithfullyFlat := by
  have : Module.FaithfullyFlat A X := (RingHom.faithfullyFlat_algebraMap_iff).mp h
  exact (RingHom.faithfullyFlat_algebraMap_iff).mpr
    (Module.FaithfullyFlat.of_linearEquiv A X
      (CommAlgCat.algEquivOfIso e).symm.toLinearEquiv)

/-- The tensor product of two étale `A`-algebras is étale. -/
lemma etale_tensor (A : Type u) [CommRing A] (X Y : CommAlgCat.{u} A)
    (hX : Algebra.Etale A X) (hY : Algebra.Etale A Y) :
    Algebra.Etale A (X ⊗[A] Y) := by
  have : Algebra.Etale A X := hX
  have : Algebra.Etale A Y := hY
  have : Algebra.Etale X (X ⊗[A] Y) := Algebra.Etale.baseChange A Y X
  exact Algebra.Etale.comp A X (X ⊗[A] Y)

/-- The tensor product of two faithfully flat `A`-algebras is faithfully flat. -/
lemma faithfullyFlat_tensor (A : Type u) [CommRing A] (X Y : CommAlgCat.{u} A)
    (hX : (algebraMap A X).FaithfullyFlat)
    (hY : (algebraMap A Y).FaithfullyFlat) :
    (algebraMap A (X ⊗[A] Y)).FaithfullyFlat := by
  have : Module.FaithfullyFlat A X := (RingHom.faithfullyFlat_algebraMap_iff).mp hX
  have : Module.FaithfullyFlat A Y := (RingHom.faithfullyFlat_algebraMap_iff).mp hY
  have hXY : Module.FaithfullyFlat X (X ⊗[A] Y) := inferInstance
  exact (RingHom.faithfullyFlat_algebraMap_iff).mpr
    (Module.FaithfullyFlat.trans A X (X ⊗[A] Y))

/-- The binary coproduct of two étale `A`-algebras is étale. -/
lemma etale_coprod (A : Type u) [CommRing A] (X Y : CommAlgCat.{u} A)
    (hX : Algebra.Etale A X) (hY : Algebra.Etale A Y) :
    Algebra.Etale A ((X ⨿ Y : CommAlgCat.{u} A) : Type u) := by
  let e : X ⨿ Y ≅ CommAlgCat.of A (X ⊗[A] Y) :=
    (coprodIsCoprod X Y).coconePointUniqueUpToIso
      (CommAlgCat.binaryCofanIsColimit X Y)
  exact etaleObject_of_iso e.symm (etale_tensor A X Y hX hY)

/-- The binary coproduct of two faithfully flat `A`-algebras is faithfully flat. -/
lemma faithfullyFlat_coprod (A : Type u) [CommRing A]
    (X Y : CommAlgCat.{u} A)
    (hX : (algebraMap A X).FaithfullyFlat)
    (hY : (algebraMap A Y).FaithfullyFlat) :
    (algebraMap A ((X ⨿ Y : CommAlgCat.{u} A) : Type u)).FaithfullyFlat := by
  let e : X ⨿ Y ≅ CommAlgCat.of A (X ⊗[A] Y) :=
    (coprodIsCoprod X Y).coconePointUniqueUpToIso
      (CommAlgCat.binaryCofanIsColimit X Y)
  exact faithfullyFlatObject_of_iso e.symm (faithfullyFlat_tensor A X Y hX hY)

/-- A property of `A`-algebras stable under isomorphism and binary coproducts and holding for `A`
holds for finite coproducts. -/
private theorem finite_coproduct_of {A : Type u} [CommRing A] (P : CommAlgCat.{u} A → Prop)
    (hiso : ∀ {X Y : CommAlgCat.{u} A}, (X ≅ Y) → P X → P Y)
    (hcoprod : ∀ X Y, P X → P Y → P (X ⨿ Y)) (hinit : P (CommAlgCat.of A A))
    {J : Type*} [Finite J] (f : J → CommAlgCat.{u} A) (h : ∀ j, P (f j)) : P (∐ f) := by
  have key : ∀ (n : ℕ) (f : Fin n → CommAlgCat.{u} A), (∀ i, P (f i)) → P (∐ f) := by
    intro n
    induction n with
    | zero =>
        intro f _
        let h : IsInitial (∐ f : CommAlgCat.{u} A) :=
          (isColimitEquivIsInitialOfIsEmpty (CommAlgCat.{u} A)
            (colimit.cocone (Discrete.functor f))) (colimit.isColimit _)
        exact hiso (h.uniqueUpToIso (CommAlgCat.isInitialSelf (R := A))).symm hinit
    | succ n ih =>
        intro f hf
        let g : Fin n → CommAlgCat.{u} A := fun i ↦ f i.succ
        let e : (∐ f : CommAlgCat.{u} A) ≅ f 0 ⨿ ∐ g :=
          (colimit.isColimit (Discrete.functor f)).coconePointUniqueUpToIso
            (extendCofanIsColimit f (coproductIsCoproduct g)
              (coprodIsCoprod (f 0) (∐ g)))
        exact hiso e.symm (hcoprod _ _ (hf 0) (ih g (fun i ↦ hf i.succ)))
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  exact hiso (Sigma.reindex e.symm f) (key n _ (fun i ↦ h (e.symm i)))

/-- A coproduct of `n` étale `A`-algebras is étale. -/
lemma etale_fin_coproduct (A : Type u) [CommRing A] :
    ∀ (n : ℕ) (f : Fin n → CommAlgCat.{u} A),
      (∀ i, Algebra.Etale A (f i)) →
      Algebra.Etale A ((∐ f : CommAlgCat.{u} A) : Type u) :=
  fun _ f h ↦ finite_coproduct_of (fun X : CommAlgCat.{u} A ↦ Algebra.Etale A X)
    etaleObject_of_iso (etale_coprod A) inferInstance f h

/-- A coproduct of `n` faithfully flat `A`-algebras is faithfully flat. -/
lemma faithfullyFlat_fin_coproduct (A : Type u) [CommRing A] :
    ∀ (n : ℕ) (f : Fin n → CommAlgCat.{u} A),
      (∀ i, (algebraMap A (f i)).FaithfullyFlat) →
      (algebraMap A ((∐ f : CommAlgCat.{u} A) : Type u)).FaithfullyFlat :=
  fun _ f h ↦ finite_coproduct_of
    (fun X : CommAlgCat.{u} A ↦ (algebraMap A X).FaithfullyFlat)
    faithfullyFlatObject_of_iso (faithfullyFlat_coprod A)
    ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance) f h

/-- A coproduct of finitely many étale `A`-algebras is étale. -/
lemma etale_finite_coproduct (A : Type u) [CommRing A]
    {J : Type u} [Finite J] (f : J → CommAlgCat.{u} A)
    (h : ∀ j, Algebra.Etale A (f j)) :
    Algebra.Etale A ((∐ f : CommAlgCat.{u} A) : Type u) :=
  finite_coproduct_of (fun X : CommAlgCat.{u} A ↦ Algebra.Etale A X)
    etaleObject_of_iso (etale_coprod A) inferInstance f h

/-- A coproduct of finitely many faithfully flat `A`-algebras is faithfully flat. -/
lemma faithfullyFlat_finite_coproduct (A : Type u) [CommRing A]
    {J : Type u} [Finite J] (f : J → CommAlgCat.{u} A)
    (h : ∀ j, (algebraMap A (f j)).FaithfullyFlat) :
    (algebraMap A ((∐ f : CommAlgCat.{u} A) : Type u)).FaithfullyFlat :=
  finite_coproduct_of (fun X : CommAlgCat.{u} A ↦ (algebraMap A X).FaithfullyFlat)
    faithfullyFlatObject_of_iso (faithfullyFlat_coprod A)
    ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance) f h

/-- An étale `A`-algebra is a finitely presentable object of `CommAlgCat A`. -/
lemma etale_isFinitelyPresentable (A : Type u) [CommRing A]
    (X : CommAlgCat.{u} A) (h : Algebra.Etale A X) :
    IsFinitelyPresentable.{u} X := by
  have := Cardinal.fact_isRegular_aleph0.{u}
  have : Algebra.Etale A X := h
  rw [IsFinitelyPresentable, ← isCardinalPresentable_iff_of_isEquivalence X _
    (commAlgCatEquivUnder (CommRingCat.of A)).functor]
  exact CommRingCat.isFinitelyPresentable_under (CommRingCat.of A) _
    ((RingHom.finitePresentation_algebraMap (A := A) (B := X)).mpr inferInstance)

end AlgebraicGeometry.ProEtale

end
