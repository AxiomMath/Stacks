module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Tor.Vanishing

/-!
# First Tor of a quotient ring with itself

For a surjective homomorphism of commutative rings, the first Tor of the quotient ring with
itself is the conormal module of its kernel. This is the first-order part of Quillen's spectral
sequence for the cotangent complex.

## Main results

* `RingHom.torOneSelfIsoCotangent`: the first Tor of a quotient ring with itself is the kernel
  modulo its square.

## Implementation notes

`Ideal.Cotangent I` is Mathlib's quotient module `I/I²`. The isomorphism is stated in the
category of modules over the source ring; both sides are annihilated by the kernel and thus
naturally modules over the quotient ring. Mathlib's monoidal category structure on `ModuleCat`
currently requires the module objects to live in the same universe as the base ring.

The construction splits the computation into the vanishing of `Tor₁(B, A)`, the long exact
sequence of `0 → I → A → B → 0` tensored with `B`, and the identification
`B ⊗[A] I ≅ I/I²`; isolating the last of these as its own linear equivalence keeps the
elaboration of the nested quotient and tensor identifications small.

## References

* [Stacks Project, Tag 08RG](https://stacks.math.columbia.edu/tag/08RG)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits
open scoped TensorProduct

universe u

namespace RingHom

private lemma isZero_leftDerived_succ_obj_of_exact
    {C : Type*} [Category* C] [Abelian C] [HasProjectiveResolutions C]
    {D : Type*} [Category* D] [Abelian D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (n : ℕ) (X : C) : IsZero ((G.leftDerived (n + 1)).obj X) := by
  refine IsZero.of_iso ?_ ((projectiveResolution X).isoLeftDerivedObj G (n + 1))
  have h : ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (projectiveResolution X).complex).ExactAt (n + 1) :=
    ((projectiveResolution X).complex_exactAt_succ n).map G
  simpa only [HomologicalComplex.homologyFunctor_obj] using
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp h

/-- Tensoring on the right with a flat module is exact, so its first left derived functor
vanishes. -/
lemma isZero_Tor'_one_of_flat_right {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) [Module.Flat R N] :
    IsZero (((Tor' (ModuleCat.{u} R) 1).obj M).obj N) :=
  isZero_leftDerived_succ_obj_of_exact ((tensoringRight (ModuleCat.{u} R)).obj N) 0 M

/-- For a surjective ring map `f : A → B` with kernel `I`, the `A`-module `A ⧸ I` is the
module `B`. -/
noncomputable def quotKerLinearEquiv {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    letI : Algebra A B := f.toAlgebra
    (A ⧸ RingHom.ker f) ≃ₗ[A] B :=
  letI : Algebra A B := f.toAlgebra
  (Submodule.quotEquivOfEq (RingHom.ker f) (Algebra.linearMap A B).ker (by ext; rfl)).trans
    (LinearMap.quotKerEquivOfSurjective (Algebra.linearMap A B) hf)

/-- For a surjective ring map `f : A → B` with kernel `I`, base change of `I` to `B` is the
conormal module `I ⧸ I²`. -/
noncomputable def tensorKerLinearEquiv {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    letI : Algebra A B := f.toAlgebra
    (B ⊗[A] (RingHom.ker f)) ≃ₗ[A] (RingHom.ker f).Cotangent :=
  letI : Algebra A B := f.toAlgebra
  (TensorProduct.congr (quotKerLinearEquiv f hf).symm (LinearEquiv.refl A _)).trans
    (TensorProduct.quotTensorEquivQuotSMul (RingHom.ker f) (RingHom.ker f))

/-- The object `B ⊗ I` of the module category over `A`, identified with the conormal module of
`I = ker f`. -/
noncomputable def quotientTensorCotangentIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    letI : Algebra A B := f.toAlgebra
    ModuleCat.of A B ⊗ ModuleCat.of A (RingHom.ker f) ≅
      ModuleCat.of A (RingHom.ker f).Cotangent :=
  letI : Algebra A B := f.toAlgebra
  (tensorKerLinearEquiv f hf).toModuleIso

/-- **Stacks 08RG**, the clause `Tor_1^A(B, B) = I/I²`: for a surjective ring map `f : A → B`
with kernel `I`, the first Tor of `B` with itself over `A` is the conormal module `I/I²`.

The route is the vanishing of `Tor_1^A(B, A)`, the long exact sequence of
`0 → I → A → B → 0` tensored with `B`, and the identification `B ⊗_A I = I/I²`. -/
@[stacks 08RG "the clause Tor_1^A(B, B) = I/I² for a surjective ring map f : A → B with \
  I = ker f: the first Tor of B with itself over A is Ideal.Cotangent I, which is Mathlib's \
  I/I². Tor is Mathlib's monoidal Tor on ModuleCat A, the left derived functor of the tensor \
  product, so both sides are read as A-modules; each is annihilated by I and hence a B-module. \
  The route is the vanishing of Tor_1^A(B, A), the long exact sequence of 0 → I → A → B → 0 \
  tensored with B, and B ⊗_A I = I/I². No hypothesis beyond the remark's own surjectivity of \
  A → B"]
noncomputable def torOneSelfIsoCotangent
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    letI : Algebra A B := f.toAlgebra
    ((Tor (ModuleCat.{u} A) 1).obj
      (ModuleCat.of A B)).obj (ModuleCat.of A B) ≅
        ModuleCat.of A (RingHom.ker f).Cotangent := by
  letI : Algebra A B := f.toAlgebra
  let I : Ideal A := RingHom.ker f
  let M : ModuleCat A := ModuleCat.of A B
  let lm : A →ₗ[A] B := Algebra.linearMap A B
  let sf : I →ₗ[A] A := I.subtype
  let S : ShortComplex (ModuleCat A) := ShortComplex.mk (ModuleCat.ofHom sf)
    (ModuleCat.ofHom lm) (by ext x; exact x.2)
  have hexlin : Function.Exact sf lm := by
    apply LinearMap.exact_iff.mpr
    rw [Submodule.range_subtype]
    ext
    rfl
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hexlin I.injective_subtype hf
  let hseq := (hS.exists_Tor'_one_composableArrows_exact_and_epi M).1
  let δ := Classical.choose hseq
  have hex := Classical.choose_spec hseq
  have hprev : (((Tor' (ModuleCat A) 1).obj M).map S.g) = 0 :=
    IsZero.eq_of_src (isZero_Tor'_one_of_flat_right M (ModuleCat.of A A)) _ _
  have hmapzero : M ◁ S.f = 0 := by
    apply ModuleCat.hom_ext
    change LinearMap.lTensor B sf = 0
    have hcomp : (TensorProduct.rid A B).toLinearMap.comp (LinearMap.lTensor B sf) = 0 := by
      ext b i
      change f i * b = 0
      rw [i.2, zero_mul]
    exact LinearMap.ext fun z => (TensorProduct.rid A B).injective
      (by simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcomp z)
  haveI : Mono δ := (hex.exact' 1 2 3).mono_g hprev
  haveI : Epi δ := (hex.exact' 2 3 4).epi_f hmapzero
  let eSym : Tor (ModuleCat A) 1 ≅ (Tor (ModuleCat A) 1).flip :=
    Classical.choice (tor_symm_canonically_iso (R := A) 1)
  let eTor : ((Tor (ModuleCat A) 1).obj M).obj M ≅ ((Tor' (ModuleCat A) 1).obj M).obj M :=
    ((eSym.app M).app M).trans (((torFlip_iso_Tor' A 1).app M).app M)
  haveI : IsIso δ := isIso_of_mono_of_epi δ
  exact eTor.trans ((asIso δ).trans (quotientTensorCotangentIso f hf))

end RingHom

end
