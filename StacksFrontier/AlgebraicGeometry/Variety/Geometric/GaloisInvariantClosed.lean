module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Invariant.Profinite
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent of Galois-invariant closed subsets

A closed subset of the base change of a scheme along a Galois field extension descends
when it is invariant under every element of the Galois group.

## Main definitions

* `AlgebraicGeometry.galoisBaseChangeMap` is the self-map of a scalar extension induced by a
  field automorphism.
* `AlgebraicGeometry.tensorGaloisAut` is the algebra automorphism of `A ⊗[k] K` obtained by
  letting a `k`-automorphism of `K` act on the second factor.

## Main results

* `AlgebraicGeometry.exists_closed_subset_with_preimage_eq_of_galois_invariant` descends a
  Galois-invariant closed subset.
* `AlgebraicGeometry.galoisBaseChangeMap_pullbackSpecIso` identifies the self-map of the base
  change of an affine scheme with the spectrum of `tensorGaloisAut`.

## Implementation notes

The scalar extension is represented by the categorical pullback of the structure morphism
along the map of spectra. Invariance is written using inverse images under the induced
self-maps; since the hypothesis ranges over the whole Galois group, this is equivalent to
invariance under the corresponding direct action.

The descended set is the image of the invariant closed set under the projection, which is
closed because the projection is integral. That its inverse image is the original set comes
from the Galois group acting transitively on each fibre of the projection, which is checked on
an affine neighbourhood by `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` applied
to the Galois action on `A ⊗[k] K`.

## References

* [Stacks Project, Tag 038B](https://stacks.math.columbia.edu/tag/038B)
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- The self-map of `X ×_{Spec k} Spec K` induced by a `k`-automorphism of `K`. -/
public noncomputable def galoisBaseChangeMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (σ : K ≃ₐ[k] K) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    f (Spec.map (CommRingCat.ofHom (algebraMap k K))) (𝟙 X)
    (Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom)) (𝟙 _)
    (by simp) (by
      have h : (CommRingCat.ofHom (algebraMap k K)) ≫
          CommRingCat.ofHom σ.toRingEquiv.toRingHom =
          CommRingCat.ofHom (algebraMap k K) := by
        ext x
        exact σ.commutes x
      rw [Category.comp_id, ← Spec.map_comp, h])

/-- The induced self-map of a base change leaves the projection to the original scheme
unchanged. -/
public theorem galoisBaseChangeMap_fst
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (σ : K ≃ₐ[k] K) :
    galoisBaseChangeMap k K X f σ ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  dsimp only [galoisBaseChangeMap, pullback.map]
  rw [pullback.lift_fst, Category.comp_id]

/-- On the projection to the spectrum of the extension field, the induced self-map of a base
change is the spectrum of the given automorphism. -/
public theorem galoisBaseChangeMap_snd
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (σ : K ≃ₐ[k] K) :
    galoisBaseChangeMap k K X f σ ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
        Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) := by
  dsimp only [galoisBaseChangeMap, pullback.map]
  exact pullback.lift_snd _ _ _

section GaloisHelpers

open scoped TensorProduct Pointwise

/-- The projection from a base change along a Galois extension is a closed map, because that
extension is integral. -/
private theorem galoisBaseChangeProjection_isClosedMap
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    IsClosedMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have : Algebra.IsAlgebraic k K := Algebra.IsSeparable.isAlgebraic k K
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (IsIntegralHom.SpecMap_iff).2
      (algebraMap_isIntegral_iff.mpr Algebra.IsAlgebraic.isIntegral)
  exact Scheme.Hom.isClosedMap _

/-- A set stable under a group action whose orbits are the fibres of a map is the inverse image
of its own image. -/
private theorem preimage_image_eq_of_fiber_orbits
    {X Y G : Type*} (q : Y → X) (g : G → Y → Y) (T : Set Y)
    (hstable : ∀ a, (g a) ⁻¹' T = T)
    (horbit : ∀ y z, q y = q z → ∃ a, g a y = z) :
    q ⁻¹' (q '' T) = T := by
  ext y
  refine ⟨?_, fun hy => ⟨y, hy, rfl⟩⟩
  rintro ⟨z, hz, hyz⟩
  obtain ⟨a, rfl⟩ := horbit y z hyz.symm
  rw [← hstable a]
  exact hz

/-- A `k`-automorphism of `K` acting on the second factor of `A ⊗[k] K`. -/
public noncomputable def tensorGaloisAut
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (σ : K ≃ₐ[k] K) :
    (A ⊗[k] K) ≃ₐ[A] (A ⊗[k] K) :=
  Algebra.TensorProduct.congr .refl σ

/-- The Galois action on `A ⊗[k] K` is the tensor product of the identity of `A` with the given
automorphism. -/
public theorem tensorGaloisAut_apply
    {k K A : Type u} [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (σ : K ≃ₐ[k] K) (x : A ⊗[k] K) :
    tensorGaloisAut k K A σ x = Algebra.TensorProduct.map (AlgHom.id A A) σ x := rfl

/-- The Galois action on `A ⊗[k] K` as a monoid homomorphism to its `A`-algebra
automorphisms. -/
private noncomputable def tensorGaloisAutHom
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] :
    (K ≃ₐ[k] K) →* ((A ⊗[k] K) ≃ₐ[A] (A ⊗[k] K)) where
  toFun := tensorGaloisAut k K A
  map_one' := Algebra.TensorProduct.congr_refl
  map_mul' σ τ := by
    change Algebra.TensorProduct.congr .refl (τ.trans σ) =
      (Algebra.TensorProduct.congr .refl τ).trans (Algebra.TensorProduct.congr .refl σ)
    convert (Algebra.TensorProduct.congr_trans
      (.refl : A ≃ₐ[A] A) (.refl : A ≃ₐ[A] A) τ σ) using 1
    rfl

/-- The Galois group of `K/k` acts on `A ⊗[k] K` by ring automorphisms. -/
private noncomputable instance tensorGaloisAction
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] : MulSemiringAction (K ≃ₐ[k] K) (A ⊗[k] K) :=
  MulSemiringAction.compHom (A ⊗[k] K) (tensorGaloisAutHom k K A)

/-- A chosen `k`-basis of `A`. -/
private noncomputable def tensorGaloisBasis
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] :
    Module.Basis (Module.Free.ChooseBasisIndex k A) k A :=
  Module.Free.chooseBasis k A

/-- Coordinates on `A ⊗[k] K` with respect to a chosen `k`-basis of `A`. -/
private noncomputable def tensorGaloisCoordinates
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] :
    (A ⊗[k] K) ≃ₗ[k] (Module.Free.ChooseBasisIndex k A →₀ K) :=
  TensorProduct.equivFinsuppOfBasisLeft (tensorGaloisBasis k K A)

/-- The Galois action on `A ⊗[k] K` acts coordinatewise on the chosen coordinates. -/
private theorem tensorGaloisCoordinates_aut
    {k K A : Type u} [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (σ : K ≃ₐ[k] K) (x : A ⊗[k] K)
    (i : Module.Free.ChooseBasisIndex k A) :
    tensorGaloisCoordinates k K A (tensorGaloisAut k K A σ x) i =
      σ (tensorGaloisCoordinates k K A x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [tensorGaloisCoordinates]
  | tmul a b =>
    simp only [tensorGaloisAut_apply, Algebra.TensorProduct.map_tmul,
      tensorGaloisCoordinates, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    show (tensorGaloisBasis k K A).repr a i • σ b =
      σ ((tensorGaloisBasis k K A).repr a i • b)
    simp only [Algebra.smul_def, map_mul, σ.commutes]
  | add x y hx hy =>
    simp only [tensorGaloisAut_apply, map_add] at *
    simp only [Finsupp.add_apply, hx, hy, map_add]

/-- An element of a Galois extension fixed by the whole Galois group lies in the base field. -/
private theorem galois_fixed_element_mem_range
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (x : K) (hx : ∀ σ : K ≃ₐ[k] K, σ x = x) :
    ∃ a : k, algebraMap k K a = x := by
  have hx' : x ∈ IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K)) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ _ => hx σ
  rw [InfiniteGalois.fixedField_bot] at hx'
  exact IntermediateField.mem_bot.mp hx'

/-- The coordinates of an element of the image of `A` are the images of its basis
coordinates. -/
private theorem tensorGaloisCoordinates_includeLeft
    {k K A : Type u} [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (a : A) :
    tensorGaloisCoordinates k K A
      (Algebra.TensorProduct.includeLeft (R := k) (A := A) (B := K) (S := A) a) =
      Finsupp.mapRange (algebraMap k K) (by simp) ((tensorGaloisBasis k K A).repr a) := by
  ext i
  simp [tensorGaloisCoordinates, Algebra.TensorProduct.includeLeft_apply,
    tensorGaloisBasis, Algebra.algebraMap_eq_smul_one]

/-- The invariants of the Galois action on `A ⊗[k] K` are the image of `A`. -/
private theorem tensorGalois_invariant
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] [IsGalois k K]
    (x : A ⊗[k] K)
    (hx : ∀ σ : K ≃ₐ[k] K, σ • x = x) :
    ∃ a : A, algebraMap A (A ⊗[k] K) a = x := by
  let b := tensorGaloisBasis k K A
  let c := tensorGaloisCoordinates k K A x
  have hfixed (i : Module.Free.ChooseBasisIndex k A) (σ : K ≃ₐ[k] K) :
      σ (c i) = c i := by
    have hc := tensorGaloisCoordinates_aut σ x i
    rw [show tensorGaloisAut k K A σ x = x from hx σ] at hc
    exact hc.symm
  choose p hp using fun i => galois_fixed_element_mem_range k K (c i) (hfixed i)
  classical
  let d : Module.Free.ChooseBasisIndex k A →₀ k :=
    Finsupp.onFinset c.support p fun i hi => by simpa [← hp i] using hi
  have hc : Finsupp.mapRange (algebraMap k K) (by simp) d = c := by
    ext i
    simp [d, Finsupp.onFinset_apply, hp]
  let a : A := b.repr.symm d
  have hmap : algebraMap A (A ⊗[k] K) a =
      Algebra.TensorProduct.includeLeft (R := k) (A := A) (B := K) (S := A) a := by
    simp [Algebra.TensorProduct.algebraMap_def]
  refine ⟨a, (tensorGaloisCoordinates k K A).injective ?_⟩
  have hrepr : b.repr a = d := by simp [a]
  rw [hmap, tensorGaloisCoordinates_includeLeft, hrepr, hc]

/-- The Galois action on `A ⊗[k] K` is `A`-linear. -/
private instance tensorGaloisSMulCommClass
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] : SMulCommClass (K ≃ₐ[k] K) A (A ⊗[k] K) where
  smul_comm σ a x := by
    change tensorGaloisAut k K A σ (a • x) = a • tensorGaloisAut k K A σ x
    simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes]

/-- The Galois action on `A ⊗[k] K` is continuous for the Krull topology, because the
stabilizer of an element fixes the finitely generated subextension spanned by its
coordinates. -/
private theorem tensorGaloisContinuousSMul
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] [IsGalois k K]
    [TopologicalSpace (A ⊗[k] K)] [DiscreteTopology (A ⊗[k] K)] :
    ContinuousSMul (K ≃ₐ[k] K) (A ⊗[k] K) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  classical
  let c := tensorGaloisCoordinates k K A x
  let S : Set K := c.support.image c
  let E : IntermediateField k K := IntermediateField.adjoin k S
  have : Finite S := (c.support.image c).finite_toSet.to_subtype
  have : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin fun a _ =>
      Algebra.IsAlgebraic.isIntegral.isIntegral a
  apply Subgroup.isOpen_mono ?_ E.fixingSubgroup_isOpen
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff]
  apply (tensorGaloisCoordinates k K A).injective
  ext i
  show tensorGaloisCoordinates k K A
      (tensorGaloisAut k K A σ x) i = tensorGaloisCoordinates k K A x i
  rw [tensorGaloisCoordinates_aut]
  by_cases hi : i ∈ c.support
  · exact (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ (c i)
      (IntermediateField.subset_adjoin k S (Finset.mem_image_of_mem c hi))
  · rw [Finsupp.notMem_support_iff.mp hi, map_zero]

/-- The Galois group acts transitively on the primes of `A ⊗[k] K` lying over a fixed prime
of `A`. -/
private theorem exists_tensorPrime_smul_eq
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] [IsGalois k K]
    (P Q : Ideal (A ⊗[k] K)) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under A = Q.under A) :
    ∃ σ : K ≃ₐ[k] K, Q = σ • P := by
  let : TopologicalSpace (A ⊗[k] K) := ⊥
  have : DiscreteTopology (A ⊗[k] K) := ⟨rfl⟩
  have : ContinuousSMul (K ≃ₐ[k] K) (A ⊗[k] K) :=
    tensorGaloisContinuousSMul k K A
  have : Algebra.IsInvariant A (A ⊗[k] K) (K ≃ₐ[k] K) :=
    ⟨tensorGalois_invariant k K A⟩
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite P Q hPQ

/-- The Galois action on `A ⊗[k] K` fixes the image of the first factor. -/
private theorem includeLeft_comp_tensorGaloisAut
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (σ : K ≃ₐ[k] K) :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := K)) ≫
        CommRingCat.ofHom (tensorGaloisAut k K A σ).toRingEquiv.toRingHom =
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := K)) := by
  apply CommRingCat.hom_ext
  ext x
  show tensorGaloisAut k K A σ (x ⊗ₜ[k] (1 : K)) = x ⊗ₜ[k] (1 : K)
  rw [tensorGaloisAut_apply]
  simp [Algebra.TensorProduct.map_tmul]

/-- The Galois action on `A ⊗[k] K` intertwines the inclusion of the second factor with the
automorphism of `K`. -/
private theorem includeRight_comp_tensorGaloisAut
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (σ : K ≃ₐ[k] K) :
    CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := K))) ≫
        CommRingCat.ofHom (tensorGaloisAut k K A σ).toRingEquiv.toRingHom =
      CommRingCat.ofHom σ.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := K))) := by
  apply CommRingCat.hom_ext
  ext x
  show tensorGaloisAut k K A σ ((1 : A) ⊗ₜ[k] x) =
    (1 : A) ⊗ₜ[k] σ x
  rw [tensorGaloisAut_apply]
  simp [Algebra.TensorProduct.map_tmul]

/-- The two self-maps of the base change of `Spec A` agree on the first projection. -/
private theorem galoisBaseChangeMap_pullbackSpecIso_fst
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (σ : K ≃ₐ[k] K) :
    galoisBaseChangeMap k K (Spec (.of A))
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) σ ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      ((pullbackSpecIso k A K).hom ≫
          Spec.map (CommRingCat.ofHom
            (tensorGaloisAut k K A σ).toRingEquiv.toRingHom) ≫
          (pullbackSpecIso k A K).inv) ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  rw [galoisBaseChangeMap_fst, Category.assoc, Category.assoc, pullbackSpecIso_inv_fst,
    ← Spec.map_comp, includeLeft_comp_tensorGaloisAut, pullbackSpecIso_hom_fst]

/-- The two self-maps of the base change of `Spec A` agree on the second projection. -/
private theorem galoisBaseChangeMap_pullbackSpecIso_snd
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (σ : K ≃ₐ[k] K) :
    galoisBaseChangeMap k K (Spec (.of A))
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) σ ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      ((pullbackSpecIso k A K).hom ≫
          Spec.map (CommRingCat.ofHom
            (tensorGaloisAut k K A σ).toRingEquiv.toRingHom) ≫
          (pullbackSpecIso k A K).inv) ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  rw [galoisBaseChangeMap_snd, Category.assoc, Category.assoc, pullbackSpecIso_inv_snd,
    ← Spec.map_comp, includeRight_comp_tensorGaloisAut, Spec.map_comp, ← Category.assoc,
    pullbackSpecIso_hom_snd]

/-- On the spectrum of a `k`-algebra, the induced self-map of the base change is the spectrum
of the Galois action on the tensor product. -/
public theorem galoisBaseChangeMap_pullbackSpecIso
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (σ : K ≃ₐ[k] K) :
    galoisBaseChangeMap k K (Spec (.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) σ =
      (pullbackSpecIso k A K).hom ≫
        Spec.map (CommRingCat.ofHom
          (tensorGaloisAut k K A σ).toRingEquiv.toRingHom) ≫
        (pullbackSpecIso k A K).inv :=
  pullback.hom_ext (galoisBaseChangeMap_pullbackSpecIso_fst k K A σ)
    (galoisBaseChangeMap_pullbackSpecIso_snd k K A σ)

/-- Two points of the base change of `Spec R` with the same image in `Spec R` are in one orbit
of the Galois group. -/
private theorem galoisBaseChangeMap_Spec_fiber_orbit
    (k K R : Type u) [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R]
    [IsGalois k K]
    (y z : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hyz : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) y =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) z) :
    ∃ σ : K ≃ₐ[k] K, galoisBaseChangeMap k K (Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) σ y = z := by
  let e := pullbackSpecIso k R K
  let p : PrimeSpectrum (R ⊗[k] K) := e.hom.base y
  let p' : PrimeSpectrum (R ⊗[k] K) := e.hom.base z
  have hfirst (w) : PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom
      (R := k) (A := R) (B := K)) (e.hom.base w) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) w := by
    show ((e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := R) (B := K)))).base w) = _
    rw [pullbackSpecIso_hom_fst k R K]
  have hpq : p.asIdeal.under R = p'.asIdeal.under R := by
    show (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := k)
      (A := R) (B := K)) p).asIdeal =
      (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := k)
        (A := R) (B := K)) p').asIdeal
    exact congrArg PrimeSpectrum.asIdeal ((hfirst y).trans (hyz.trans (hfirst z).symm))
  obtain ⟨σ, hp⟩ := exists_tensorPrime_smul_eq k K R p.asIdeal p'.asIdeal hpq
  have hpSpec : PrimeSpectrum.comap
      (tensorGaloisAut k K R σ.symm).toRingEquiv.toRingHom p = p' := by
    apply PrimeSpectrum.ext
    show Ideal.comap (tensorGaloisAut k K R σ.symm).toRingEquiv.toRingHom p.asIdeal =
      p'.asIdeal
    rw [hp, Ideal.pointwise_smul_eq_comap]
    rfl
  refine ⟨σ.symm, ?_⟩
  apply e.hom.isEmbedding.injective
  rw [galoisBaseChangeMap_pullbackSpecIso k K R σ.symm]
  have hinv : e.inv.base (PrimeSpectrum.comap
      (tensorGaloisAut k K R σ.symm).toRingEquiv.toRingHom p) = z := by
    simpa [p'] using congrArg e.inv.base hpSpec
  exact congrArg e.hom.base hinv

/-- The induced self-maps of two base changes commute with the map between them induced by a
morphism over `Spec k`. -/
private theorem pullbackMap_comp_galoisBaseChangeMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (f' : Y ⟶ Spec (.of k)) (i : Y ⟶ X)
    (h : f' = i ≫ f) (σ : K ≃ₐ[k] K) :
    pullback.map f' (Spec.map (CommRingCat.ofHom (algebraMap k K))) f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) i (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, h]) (by simp) ≫ galoisBaseChangeMap k K X f σ =
      galoisBaseChangeMap k K Y f' σ ≫
        pullback.map f' (Spec.map (CommRingCat.ofHom (algebraMap k K))) f
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) i (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, h]) (by simp) := by
  apply pullback.hom_ext
  · rw [Category.assoc, galoisBaseChangeMap_fst, Category.assoc]
    dsimp only [galoisBaseChangeMap, pullback.map]
    simp only [Category.comp_id]
    rw [pullback.lift_fst, pullback.lift_fst_assoc]
  · rw [Category.assoc, galoisBaseChangeMap_snd, Category.assoc]
    dsimp only [galoisBaseChangeMap, pullback.map]
    simp only [Category.comp_id]
    rw [pullback.lift_snd_assoc, pullback.lift_snd, pullback.lift_snd]

/-- Two points of the base change with the same image are in one orbit of the Galois group. -/
private theorem galoisBaseChangeMap_fiber_orbit
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (y z : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hyz : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) y =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) z) :
    ∃ σ : K ≃ₐ[k] K,
      galoisBaseChangeMap k K X f σ y = z := by
  let x := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) y
  obtain ⟨R, i, hi, a, ha⟩ := Scheme.exists_Spec_apply_eq x
  let φ : CommRingCat.of k ⟶ CommRingCat.of R := Spec.preimage (i ≫ f)
  have hφ : Spec.map φ = i ≫ f := Spec.map_preimage _
  let : Algebra k R := φ.hom.toAlgebra
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap k R)) = i ≫ f := by
    rw [show CommRingCat.ofHom (algebraMap k R) = φ from rfl, hφ]
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let q := pullback.fst f g
  let qR := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) g
  let m : pullback (Spec.map (CommRingCat.ofHom (algebraMap k R))) g ⟶ pullback f g :=
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k R))) g f g i (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, hbase]) (by simp)
  have hmap : Set.range m.base = q ⁻¹' Set.range i := by
    show Set.range (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k R))) g f g
      i (𝟙 _) (𝟙 _) _ _) = _
    rw [Scheme.Pullback.range_map]
    simp [q, g]
  have hlift (w) (hw : q w = q y) : w ∈ Set.range m.base := by
    rw [hmap, Set.mem_preimage, hw]
    exact ⟨a, by simpa [x, q] using ha⟩
  obtain ⟨yR, hyR⟩ := hlift y rfl
  obtain ⟨zR, hzR⟩ := hlift z hyz.symm
  have hmFst : m ≫ q = qR ≫ i := by
    dsimp [m, q, qR, pullback.map]
    rw [pullback.lift_fst]
  have hfst (w) : i.base (qR w) = q (m.base w) := by
    have hh := congrArg (fun h : Scheme.Hom _ _ => h.base w) hmFst
    change q (m w) = i (qR w) at hh
    exact hh.symm
  have hqR : qR yR = qR zR := by
    apply i.isEmbedding.injective
    rw [hfst, hfst, hyR, hzR, hyz]
  obtain ⟨τ, hpoint⟩ := galoisBaseChangeMap_Spec_fiber_orbit k K R yR zR hqR
  have hcomm : m ≫ galoisBaseChangeMap k K X f τ =
      galoisBaseChangeMap k K (Spec (.of R)) (Spec.map (CommRingCat.ofHom
        (algebraMap k R))) τ ≫ m :=
    pullbackMap_comp_galoisBaseChangeMap k K f _ i hbase τ
  refine ⟨τ, ?_⟩
  rw [← hyR, ← hzR, ← hpoint]
  simpa [Scheme.Hom.comp_apply] using congrArg (fun h : Scheme.Hom _ _ => h.base yR) hcomm

end GaloisHelpers

/-- **Stacks Project, Tag 038B.** A closed subset of a scheme after base change by a
Galois field extension descends if it is invariant under the Galois group. -/
@[stacks 038B]
public theorem exists_closed_subset_with_preimage_eq_of_galois_invariant
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (Tbar : Set (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hTbar : IsClosed Tbar)
    (hstable : ∀ σ : K ≃ₐ[k] K,
      (galoisBaseChangeMap k K X f σ) ⁻¹' Tbar = Tbar) :
    ∃ T : Set X, IsClosed T ∧
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹' T = Tbar := by
  let q := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  refine ⟨q '' Tbar, (galoisBaseChangeProjection_isClosedMap k K X f) _ hTbar, ?_⟩
  exact preimage_image_eq_of_fiber_orbits q (fun σ y => galoisBaseChangeMap k K X f σ y) Tbar
    hstable (galoisBaseChangeMap_fiber_orbit k K X f)

end AlgebraicGeometry
