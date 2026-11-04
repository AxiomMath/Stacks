module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.FiberCriterion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# The square-cube universal homeomorphism

If two elements `x` and `y` of a ring satisfy `x ^ 3 = y ^ 2`, adjoining an element whose
square is `x` and whose cube is `y` gives a universal homeomorphism on spectra and does not
change residue fields. This is one of the two standard examples of a universal homeomorphism
that is not an isomorphism.

## Main definitions

* `AlgebraicGeometry.SquareCubeAlgebra` is the quotient `A[t] / (t ^ 2 - x, t ^ 3 - y)`.
* `AlgebraicGeometry.squareCubeSpecMap` is its canonical morphism to `Spec A`.

## Main results

* `AlgebraicGeometry.squareCubeSpecMap_universalHomeomorphism`: this morphism is a universal
  homeomorphism.
* `AlgebraicGeometry.isIso_residueFieldMap_squareCubeSpecMap`: all its residue field maps are
  isomorphisms.

## Implementation notes

The bijections on residue fields are expressed by `IsIso` for the canonical residue field
morphisms attached to the morphism of affine schemes. Both conclusions are obtained from the
fibre criterion by exhibiting, over any field-valued point, a unique square-and-cube root.

## References

* [Stacks Project, Tag 0EUI](https://stacks.math.columbia.edu/tag/0EUI)
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The algebra `A[t] / (t ^ 2 - x, t ^ 3 - y)`. -/
public abbrev SquareCubeAlgebra (A : Type u) [CommRing A] (x y : A) :=
  Polynomial A ⧸ Ideal.span
    ({Polynomial.X ^ 2 - Polynomial.C x, Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A))

/-- The canonical morphism from the spectrum of the square-cube algebra to `Spec(A)`. -/
public abbrev squareCubeSpecMap (A : Type u) [CommRing A] (x y : A) :
    Spec (.of (SquareCubeAlgebra A x y)) ⟶ Spec (.of A) :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (SquareCubeAlgebra A x y))).op

private lemma squareCubeAlgebra_aeval_root (A : Type u) [CommRing A] (x y : A) :
    Polynomial.aeval (Ideal.Quotient.mk _ Polynomial.X : SquareCubeAlgebra A x y) =
      Ideal.Quotient.mkₐ A _ :=
  Polynomial.algHom_ext (by simp)

private lemma squareCubeAlgebra_adjoin_root (A : Type u) [CommRing A] (x y : A) :
    Algebra.adjoin A
      ({(Ideal.Quotient.mk _ Polynomial.X : SquareCubeAlgebra A x y)} :
        Set (SquareCubeAlgebra A x y)) = ⊤ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, squareCubeAlgebra_aeval_root, AlgHom.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective A _

private lemma squareCubeAlgebra_isIntegral (A : Type u) [CommRing A] (x y : A) :
    Algebra.IsIntegral A (SquareCubeAlgebra A x y) := by
  let B := SquareCubeAlgebra A x y
  let t : B := Ideal.Quotient.mk _ Polynomial.X
  have ht : _root_.IsIntegral A t := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C x, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C x (by decide)
    · show Polynomial.aeval t (Polynomial.X ^ 2 - Polynomial.C x) = 0
      rw [squareCubeAlgebra_aeval_root]
      show Ideal.Quotient.mk _ (Polynomial.X ^ 2 - Polynomial.C x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
  have htop : Algebra.adjoin A ({t} : Set B) = ⊤ := by
    simpa [t, B] using squareCubeAlgebra_adjoin_root A x y
  rw [← (Subalgebra.topEquiv (R := A) (A := B)).isIntegral_iff, ← htop]
  exact Algebra.IsIntegral.adjoin (by simpa using ht)

private lemma squareCubeFiber_adjoin_root (A : Type u) [CommRing A] (x y : A)
    (k : Type u) [Field k] (g : A →+* k) :
    letI : Algebra A k := g.toAlgebra
    let B := SquareCubeAlgebra A x y
    letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := k);
    Algebra.adjoin k
      ({(Ideal.Quotient.mk _ Polynomial.X : B) ⊗ₜ[A] (1 : k)} : Set (B ⊗[A] k)) = ⊤ := by
  let : Algebra A k := g.toAlgebra
  let B := SquareCubeAlgebra A x y
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := k)
  let t : B := Ideal.Quotient.mk _ Polynomial.X
  let e := Algebra.TensorProduct.commRight A k B
  have hsrc : Algebra.adjoin k ({(1 : k) ⊗ₜ[A] t} : Set (k ⊗[A] B)) = ⊤ := by
    simpa using Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (R := A) (A := k) (B := B) ({t} : Set B) (by
        simpa [t, B] using squareCubeAlgebra_adjoin_root A x y)
  have hmap := AlgHom.map_adjoin e.toAlgHom ({(1 : k) ⊗ₜ[A] t} : Set (k ⊗[A] B))
  have heq : e '' ({(1 : k) ⊗ₜ[A] t} : Set (k ⊗[A] B)) =
      ({t ⊗ₜ[A] (1 : k)} : Set (B ⊗[A] k)) := by
    rw [Set.image_singleton]
    simp [e]
  have htop : Subalgebra.map e.toAlgHom ⊤ = ⊤ :=
    (Algebra.map_top e.toAlgHom).trans ((AlgHom.range_eq_top _).mpr e.surjective)
  rw [hsrc, htop] at hmap
  simpa [heq] using hmap.symm

private lemma field_exists_square_cube_root (k : Type u) [Field k] (a b : k)
    (h : a ^ 3 = b ^ 2) : ∃ l : k, l ^ 2 = a ∧ l ^ 3 = b := by
  by_cases ha : a = 0
  · subst a
    obtain rfl : b = 0 := by simpa using h.symm
    exact ⟨0, by simp, by simp⟩
  · refine ⟨b / a, ?_, ?_⟩
    · rw [div_pow]
      field_simp [ha]
      exact h.symm
    · rw [div_pow]
      field_simp [ha]
      rw [h]
      ring

private lemma squareCubeFiber_nontrivial (A : Type u) [CommRing A] (x y : A)
    (hxy : x ^ 3 = y ^ 2) (k : Type u) [Field k] (g : A →+* k) :
    letI : Algebra A k := g.toAlgebra
    Nontrivial (SquareCubeAlgebra A x y ⊗[A] k) := by
  let : Algebra A k := g.toAlgebra
  let B := SquareCubeAlgebra A x y
  let D := B ⊗[A] k
  obtain ⟨l, hl2, hl3⟩ := field_exists_square_cube_root k (g x) (g y) (by
    simpa using congrArg g hxy)
  let I : Ideal (Polynomial A) := Ideal.span
    ({Polynomial.X ^ 2 - Polynomial.C x, Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A))
  let ev : Polynomial A →ₐ[A] k := Polynomial.aeval l
  have hker : I ≤ RingHom.ker ev.toRingHom := by
    show Ideal.span
        ({Polynomial.X ^ 2 - Polynomial.C x,
          Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A)) ≤
      RingHom.ker ev.toRingHom
    rw [Ideal.span_le]
    rintro p (rfl | rfl)
    · show Polynomial.eval₂ (algebraMap A k) l
        (Polynomial.X ^ 2 - Polynomial.C x) = 0
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      rw [show algebraMap A k = g from rfl, hl2]
      ring
    · show Polynomial.eval₂ (algebraMap A k) l
        (Polynomial.X ^ 3 - Polynomial.C y) = 0
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      rw [show algebraMap A k = g from rfl, hl3]
      ring
  let f : B →ₐ[A] k := Ideal.Quotient.liftₐ I ev fun p hp => hker hp
  let g' : k →ₐ[A] k := AlgHom.id A k
  have hfg : ∀ a b, Commute (f a) (g' b) := fun a b => mul_comm (f a) (g' b)
  let φ : D →ₐ[A] k := Algebra.TensorProduct.lift f g' hfg
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨Algebra.TensorProduct.includeRight c, ?_⟩
    show (Algebra.TensorProduct.lift f g' hfg).comp Algebra.TensorProduct.includeRight c = c
    rw [Algebra.TensorProduct.lift_comp_includeRight']
    rfl
  exact hsurj.nontrivial

private lemma squareCubeAlgebra_root_square (A : Type u) [CommRing A] (x y : A) :
    let B := SquareCubeAlgebra A x y
    let t : B := Ideal.Quotient.mk _ Polynomial.X
    t ^ 2 = algebraMap A B x := by
  let B := SquareCubeAlgebra A x y
  let I : Ideal (Polynomial A) := Ideal.span
    ({Polynomial.X ^ 2 - Polynomial.C x, Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A))
  let t : B := Ideal.Quotient.mk I Polynomial.X
  have hr : (Ideal.Quotient.mkₐ A I) (Polynomial.X ^ 2 - Polynomial.C x) = 0 := by
    show Ideal.Quotient.mk I (Polynomial.X ^ 2 - Polynomial.C x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  show t ^ 2 = algebraMap A B x
  have hh := sub_eq_zero.mp (by simpa [map_sub, map_pow, t, B, I] using hr)
  exact hh

private lemma squareCubeAlgebra_root_cube (A : Type u) [CommRing A] (x y : A) :
    let B := SquareCubeAlgebra A x y
    let t : B := Ideal.Quotient.mk _ Polynomial.X
    t ^ 3 = algebraMap A B y := by
  let B := SquareCubeAlgebra A x y
  let I : Ideal (Polynomial A) := Ideal.span
    ({Polynomial.X ^ 2 - Polynomial.C x, Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A))
  let t : B := Ideal.Quotient.mk I Polynomial.X
  have hr : (Ideal.Quotient.mkₐ A I) (Polynomial.X ^ 3 - Polynomial.C y) = 0 := by
    show Ideal.Quotient.mk I (Polynomial.X ^ 3 - Polynomial.C y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  show t ^ 3 = algebraMap A B y
  have hh := sub_eq_zero.mp (by simpa [map_sub, map_pow, t, B, I] using hr)
  exact hh

private lemma squareCubeFiber_root_square (A : Type u) [CommRing A] (x y : A)
    (k : Type u) [Field k] (g : A →+* k) :
    letI : Algebra A k := g.toAlgebra
    let B := SquareCubeAlgebra A x y
    letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := k);
    ((Ideal.Quotient.mk _ Polynomial.X : B) ⊗ₜ[A] (1 : k)) ^ 2 =
      Algebra.TensorProduct.includeRight (g x) := by
  let : Algebra A k := g.toAlgebra
  let B := SquareCubeAlgebra A x y
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := k)
  let t : B := Ideal.Quotient.mk _ Polynomial.X
  show ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := k) t) ^ 2) =
    Algebra.TensorProduct.includeRight (g x)
  rw [← map_pow (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := k)),
    squareCubeAlgebra_root_square]
  exact ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] k).commutes x).trans
    ((Algebra.TensorProduct.includeRight : k →ₐ[A] B ⊗[A] k).commutes x).symm

private lemma squareCubeFiber_root_cube (A : Type u) [CommRing A] (x y : A)
    (k : Type u) [Field k] (g : A →+* k) :
    letI : Algebra A k := g.toAlgebra
    let B := SquareCubeAlgebra A x y
    letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := k);
    ((Ideal.Quotient.mk _ Polynomial.X : B) ⊗ₜ[A] (1 : k)) ^ 3 =
      Algebra.TensorProduct.includeRight (g y) := by
  let : Algebra A k := g.toAlgebra
  let B := SquareCubeAlgebra A x y
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := k)
  let t : B := Ideal.Quotient.mk _ Polynomial.X
  show ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := k) t) ^ 3) =
    Algebra.TensorProduct.includeRight (g y)
  rw [← map_pow (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := k)),
    squareCubeAlgebra_root_cube]
  exact ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] k).commutes y).trans
    ((Algebra.TensorProduct.includeRight : k →ₐ[A] B ⊗[A] k).commutes y).symm

private lemma field_square_cube_root_unique (k K : Type u) [Field k] [Field K] [Algebra k K]
    (a b l : k) (_h : a ^ 3 = b ^ 2) (hl2 : l ^ 2 = a) (hl3 : l ^ 3 = b)
    (z : K) (hz2 : z ^ 2 = algebraMap k K a) (hz3 : z ^ 3 = algebraMap k K b) :
    z = algebraMap k K l := by
  have hla : l * a = b := by
    rw [← hl2, ← hl3]
    ring
  have hzprod : z ^ 2 * (z - algebraMap k K l) = 0 := by
    rw [show z ^ 2 * (z - algebraMap k K l) =
      z ^ 3 - algebraMap k K l * z ^ 2 by ring, hz2, hz3, ← map_mul, hla, sub_self]
  rcases mul_eq_zero.mp hzprod with hz | hz
  · have ha : a = 0 := (FaithfulSMul.algebraMap_injective k K) (by
      simpa [hz2] using hz)
    have hl : l = 0 := by simpa [ha] using hl2
    have hz' : z = 0 := by simpa using hz
    simp [hl, hz']
  · exact sub_eq_zero.mp hz

private lemma field_square_cube_root_unique_ringHom (k K : Type u) [Field k] [Field K]
    (ι : k →+* K) (a b l : k) (h : a ^ 3 = b ^ 2) (hl2 : l ^ 2 = a)
    (hl3 : l ^ 3 = b) (z : K) (hz2 : z ^ 2 = ι a) (hz3 : z ^ 3 = ι b) :
    z = ι l := by
  let : Algebra k K := ι.toAlgebra
  change z ^ 2 = algebraMap k K a at hz2
  change z ^ 3 = algebraMap k K b at hz3
  exact field_square_cube_root_unique k K a b l h hl2 hl3 z hz2 hz3

private lemma squareCubeFiber_root_residue_aux (A : Type u) [CommRing A]
    (x y : A) (hxy : x ^ 3 = y ^ 2) (k : Type u) [Field k]
    (g : A →+* k) (l : k) (hl2 : l ^ 2 = g x) (hl3 : l ^ 3 = g y)
    (K : Type u) [Field K] (ι : k →+* K) (z : K)
    (hz2 : z ^ 2 = ι (g x)) (hz3 : z ^ 3 = ι (g y)) : z = ι l :=
  field_square_cube_root_unique_ringHom k K ι (g x) (g y) l
    (by simpa using congrArg g hxy) hl2 hl3 z hz2 hz3

private lemma squareCubeFiber_map_root (A : Type u) [CommRing A] (x y : A)
    (hxy : x ^ 3 = y ^ 2) (k : Type u) [Field k] (g : A →+* k) (l : k) (hl2 : l ^ 2 = g x)
    (hl3 : l ^ 3 = g y) (K : Type u) [Field K] :
    letI : Algebra A k := g.toAlgebra
    ∀ ψ : SquareCubeAlgebra A x y ⊗[A] k →+* K,
      ψ ((Ideal.Quotient.mk _ Polynomial.X : SquareCubeAlgebra A x y) ⊗ₜ[A] (1 : k)) =
        ψ ((Algebra.TensorProduct.includeRight : k →ₐ[A] SquareCubeAlgebra A x y ⊗[A] k) l) := by
  let : Algebra A k := g.toAlgebra
  intro ψ
  let B := SquareCubeAlgebra A x y
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := k)
  let t : B ⊗[A] k := (Ideal.Quotient.mk _ Polynomial.X : B) ⊗ₜ[A] (1 : k)
  let j : k →+* K := ψ.comp (Algebra.TensorProduct.includeRight : k →ₐ[A] B ⊗[A] k).toRingHom
  have hsq : t ^ 2 = Algebra.TensorProduct.includeRight (g x) := by
    simpa [B, t] using squareCubeFiber_root_square A x y k g
  have hcu : t ^ 3 = Algebra.TensorProduct.includeRight (g y) := by
    simpa [B, t] using squareCubeFiber_root_cube A x y k g
  exact squareCubeFiber_root_residue_aux A x y hxy k g l hl2 hl3 K j (ψ t)
    ((map_pow ψ t 2).symm.trans (congrArg ψ hsq)) ((map_pow ψ t 3).symm.trans (congrArg ψ hcu))

private lemma algebraMap_quotient_surjective_of_adjoin {k D : Type u} [Field k] [CommRing D]
    [Algebra k D] (t : D) (hgen : Algebra.adjoin k ({t} : Set D) = ⊤) (I : Ideal D) (l : k)
    (hl : Ideal.Quotient.mkₐ k I t = algebraMap k (D ⧸ I) l) :
    Function.Surjective (algebraMap k (D ⧸ I)) := by
  let Q := D ⧸ I
  let q : D →ₐ[k] Q := Ideal.Quotient.mkₐ k I
  have hmaptop : Subalgebra.map q ⊤ = ⊤ :=
    (Algebra.map_top q).trans ((AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective k I))
  have hgenQ : Algebra.adjoin k ({q t} : Set Q) = ⊤ := by
    have hm := AlgHom.map_adjoin q ({t} : Set D)
    rw [hgen, hmaptop] at hm
    simpa using hm.symm
  let f : k →ₐ[k] Q := Algebra.ofId k Q
  have hle : Algebra.adjoin k ({q t} : Set Q) ≤ f.range :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ⟨l, hl.symm⟩)
  have hrange : f.range = ⊤ := top_unique (hgenQ.symm.le.trans hle)
  intro z
  obtain ⟨a, ha⟩ := (AlgHom.range_eq_top f).mp hrange z
  exact ⟨a, by simpa [f] using ha⟩

private lemma fiber_residueField_bijective {k D : Type u} [Field k] [CommRing D]
    [Algebra k D] (t : D) (hgen : Algebra.adjoin k ({t} : Set D) = ⊤)
    (p : PrimeSpectrum D) (i : k →+* p.asIdeal.ResidueField)
    (hi : i = (algebraMap D p.asIdeal.ResidueField).comp (algebraMap k D))
    (l : k) (hroot : algebraMap D p.asIdeal.ResidueField t = i l) :
    Function.Bijective i := by
  let I := p.asIdeal
  let Q := D ⧸ I
  let K := I.ResidueField
  have hres : (algebraMap Q K).comp (algebraMap D Q) = algebraMap D K := by
    ext z
    simp [Q, K, I, Ideal.algebraMap_quotient_residueField_mk]
  have hcompK : (algebraMap Q K).comp (algebraMap k Q) = i := by
    ext a
    rw [hi]
    exact (congrArg (algebraMap Q K)
      (RingHom.congr_fun (IsScalarTower.algebraMap_eq k D Q).symm a)).symm.trans
      (RingHom.congr_fun hres (algebraMap k D a))
  have hqroot : Ideal.Quotient.mkₐ k I t = algebraMap k Q l := by
    apply I.injective_algebraMap_quotient_residueField
    simpa [Q, K, I] using hroot.trans (RingHom.congr_fun hcompK l).symm
  have hbijQ : Function.Bijective (algebraMap k Q) :=
    ⟨FaithfulSMul.algebraMap_injective k Q,
      algebraMap_quotient_surjective_of_adjoin t hgen I l hqroot⟩
  have : I.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mpr
    ((RingEquiv.ofBijective (algebraMap k Q) hbijQ).symm.toMulEquiv.isField (Field.toIsField k))
  rw [← hcompK]
  exact I.bijective_algebraMap_quotient_residueField.comp hbijQ

private lemma squareCubeFiber_residueField_bijective
    (A : Type u) [CommRing A] (x y : A) (hxy : x ^ 3 = y ^ 2)
    (k : Type u) [Field k] (g : A →+* k) :
    letI : Algebra A k := g.toAlgebra
    letI : CommSemiring (SquareCubeAlgebra A x y ⊗[A] k) := CommRing.toCommSemiring
    letI := Algebra.TensorProduct.rightAlgebra (R := A)
      (A := SquareCubeAlgebra A x y) (B := k)
    ∀ p : PrimeSpectrum (SquareCubeAlgebra A x y ⊗[A] k),
      Function.Bijective
        ((algebraMap (SquareCubeAlgebra A x y ⊗[A] k) p.asIdeal.ResidueField).comp
          (Algebra.TensorProduct.includeRight : k →ₐ[A]
            SquareCubeAlgebra A x y ⊗[A] k).toRingHom) := by
  let : Algebra A k := g.toAlgebra
  obtain ⟨l, hl2, hl3⟩ := field_exists_square_cube_root k (g x) (g y) (by
    simpa using congrArg g hxy)
  intro p
  let B := SquareCubeAlgebra A x y
  let D := B ⊗[A] k
  let : CommSemiring D := CommRing.toCommSemiring
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := k)
  let t : D := (Ideal.Quotient.mk _ Polynomial.X : B) ⊗ₜ[A] (1 : k)
  let ι : k →+* p.asIdeal.ResidueField :=
    (algebraMap D p.asIdeal.ResidueField).comp
      (Algebra.TensorProduct.includeRight : k →ₐ[A] D).toRingHom
  have hgen : Algebra.adjoin k ({t} : Set D) = ⊤ := by
    simpa [t, D, B] using squareCubeFiber_adjoin_root A x y k g
  exact fiber_residueField_bijective t hgen p ι rfl l
    (squareCubeFiber_map_root A x y hxy k g l hl2 hl3 _ (algebraMap D p.asIdeal.ResidueField))

private lemma exists_algHom_apply_eq_and_ker_eq {k D : Type u} [Field k] [CommRing D]
    [Algebra k D] (p : PrimeSpectrum D)
    (hi : Function.Bijective ((algebraMap D p.asIdeal.ResidueField).comp (algebraMap k D)))
    (t : D) (l : k)
    (ht : algebraMap D p.asIdeal.ResidueField t =
      (algebraMap D p.asIdeal.ResidueField).comp (algebraMap k D) l) :
    ∃ φ : D →ₐ[k] k, φ t = l ∧ RingHom.ker φ.toRingHom = p.asIdeal := by
  let K := p.asIdeal.ResidueField
  let i : k →+* K := (algebraMap D K).comp (algebraMap k D)
  let : Algebra k K := i.toAlgebra
  have : IsScalarTower k D K := .of_algebraMap_eq' rfl
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K) (by
    convert hi using 1
    rfl)
  refine ⟨e.symm.toAlgHom.comp (IsScalarTower.toAlgHom k D K), ?_, ?_⟩
  · show e.symm (algebraMap D K t) = l
    rw [ht]
    exact e.symm_apply_apply l
  · show RingHom.ker (e.symm.toRingHom.comp (algebraMap D K)) = p.asIdeal
    rw [RingHom.ker_comp_of_injective _ e.symm.injective]
    exact Ideal.ker_algebraMap_residueField (R := D) (I := p.asIdeal)

private lemma squareCubeFiber_subsingleton
    (A : Type u) [CommRing A] (x y : A) (hxy : x ^ 3 = y ^ 2)
    (k : Type u) [Field k] (g : A →+* k) :
    letI : Algebra A k := g.toAlgebra
    letI : CommSemiring (SquareCubeAlgebra A x y ⊗[A] k) := CommRing.toCommSemiring
    Subsingleton (PrimeSpectrum (SquareCubeAlgebra A x y ⊗[A] k)) := by
  let : Algebra A k := g.toAlgebra
  let : CommSemiring (SquareCubeAlgebra A x y ⊗[A] k) := CommRing.toCommSemiring
  obtain ⟨l, hl2, hl3⟩ := field_exists_square_cube_root k (g x) (g y) (by
    simpa using congrArg g hxy)
  let B := SquareCubeAlgebra A x y
  let D := B ⊗[A] k
  let : CommSemiring D := CommRing.toCommSemiring
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := k)
  let t : D := (Ideal.Quotient.mk _ Polynomial.X : B) ⊗ₜ[A] (1 : k)
  have hgen : Algebra.adjoin k ({t} : Set D) = ⊤ := by
    simpa [t, D, B] using squareCubeFiber_adjoin_root A x y k g
  have key : ∀ r : PrimeSpectrum D,
      ∃ φ : D →ₐ[k] k, φ t = l ∧ RingHom.ker φ.toRingHom = r.asIdeal := by
    intro r
    let ir : k →+* r.asIdeal.ResidueField :=
      (algebraMap D r.asIdeal.ResidueField).comp
        (Algebra.TensorProduct.includeRight : k →ₐ[A] D).toRingHom
    have hir : Function.Bijective ir := by
      simpa [ir, D, B] using squareCubeFiber_residueField_bijective A x y hxy k g r
    exact exists_algHom_apply_eq_and_ker_eq r hir t l
      (squareCubeFiber_map_root A x y hxy k g l hl2 hl3 _ (algebraMap D r.asIdeal.ResidueField))
  refine ⟨fun p q => ?_⟩
  obtain ⟨φp, htp, hkerP⟩ := key p
  obtain ⟨φq, htq, hkerQ⟩ := key q
  have hφ : φp = φq :=
    AlgHom.ext_of_adjoin_eq_top hgen fun z hz => by
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact htp.trans htq.symm
  apply PrimeSpectrum.ext
  rw [← hkerP, ← hkerQ, hφ]

private lemma squareCubeFiber_purelyInseparable
    (A : Type u) [CommRing A] (x y : A) (hxy : x ^ 3 = y ^ 2)
    (k : Type u) [Field k] (g : A →+* k) :
    letI : Algebra A k := g.toAlgebra
    letI : CommSemiring (SquareCubeAlgebra A x y ⊗[A] k) := CommRing.toCommSemiring
    letI := Algebra.TensorProduct.rightAlgebra (R := A)
      (A := SquareCubeAlgebra A x y) (B := k)
    ∀ p : PrimeSpectrum (SquareCubeAlgebra A x y ⊗[A] k),
      let ι : k →+* p.asIdeal.ResidueField :=
        (algebraMap (SquareCubeAlgebra A x y ⊗[A] k) p.asIdeal.ResidueField).comp
          (Algebra.TensorProduct.includeRight : k →ₐ[A]
            SquareCubeAlgebra A x y ⊗[A] k).toRingHom
      letI : Algebra k p.asIdeal.ResidueField := ι.toAlgebra
      IsPurelyInseparable k p.asIdeal.ResidueField := by
  let : Algebra A k := g.toAlgebra
  intro p
  let D := SquareCubeAlgebra A x y ⊗[A] k
  let : CommSemiring D := CommRing.toCommSemiring
  let ι : k →+* p.asIdeal.ResidueField :=
    (algebraMap D p.asIdeal.ResidueField).comp
      (Algebra.TensorProduct.includeRight : k →ₐ[A] D).toRingHom
  let : Algebra k p.asIdeal.ResidueField := ι.toAlgebra
  have hbij : Function.Bijective ι := by
    simpa [ι, D] using squareCubeFiber_residueField_bijective A x y hxy k g p
  have hbijAlg : Function.Bijective (Algebra.ofId k p.asIdeal.ResidueField) := by
    convert hbij using 1
    rfl
  exact (AlgEquiv.ofBijective (Algebra.ofId k p.asIdeal.ResidueField) hbijAlg).isPurelyInseparable

/-- The square-cube extension induces a universal homeomorphism on spectra. -/
@[stacks 0EUI "square_cube"]
public lemma squareCubeSpecMap_universalHomeomorphism
    (A : Type u) [CommRing A] (x y : A) (hxy : x ^ 3 = y ^ 2) :
    UniversalHomeomorphism (squareCubeSpecMap A x y) := by
  have : Algebra.IsIntegral A (SquareCubeAlgebra A x y) :=
    squareCubeAlgebra_isIntegral A x y
  exact universalHomeomorphism_specMap_of_integral_of_fiber_unique_prime_isPurelyInseparable
    (A := A) (C := SquareCubeAlgebra A x y) fun k _ g => by
      let : Algebra A k := g.toAlgebra
      exact ⟨⟨PrimeSpectrum.nonempty_iff_nontrivial.mpr (squareCubeFiber_nontrivial A x y hxy k g),
        squareCubeFiber_subsingleton A x y hxy k g⟩,
        squareCubeFiber_purelyInseparable A x y hxy k g⟩

/-- The square-cube extension induces an isomorphism on the residue field at every point. -/
@[stacks 0EUI "square_cube"]
public lemma isIso_residueFieldMap_squareCubeSpecMap
    (A : Type u) [CommRing A] (x y : A) (hxy : x ^ 3 = y ^ 2)
    (z : Spec (.of (SquareCubeAlgebra A x y))) :
    IsIso ((squareCubeSpecMap A x y).residueFieldMap z) :=
  isIso_residueFieldMap_specMap_of_fiber_residueField_bijective
    (A := A) (C := SquareCubeAlgebra A x y) (fun k _ g => by
      let : Algebra A k := g.toAlgebra
      exact squareCubeFiber_residueField_bijective A x y hxy k g)
    z

end AlgebraicGeometry

end

end
