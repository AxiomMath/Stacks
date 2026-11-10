module

public import StacksFrontier.Homology.TwoTermComplex.DeterminantTransportBaseChange

/-!
# The determinant of a perfect two-term object commutes with flat base change

Let `φ : R → A` be a flat homomorphism of commutative rings and let `K` be a perfect object of
`D(R)` of Tor-amplitude in `[-1, 0]`. Its total derived extension of scalars is again perfect of
Tor-amplitude in `[-1, 0]`, and the determinant of More on Algebra, Section 0FJI commutes with
the base change: `A ⊗_R det_R(K) ≅ det_A(A ⊗^L_R K)`. The canonical element of a rank-zero
object is carried to the canonical element of its base change.

## Main definitions

* `TwoTermDeterminant.detBaseChange`: **the comparison `A ⊗_R det_R(K) ≅ det_A(A ⊗^L_R K)`.**

## Main results

* `TwoTermDeterminant.presentationDeterminantBaseChange_apply_delta`: the comparison of the
  determinant lines of a presentation and of its base change carries the canonical element of a
  rank-zero presentation to the canonical element of the base-changed one.
* `TwoTermDeterminant.detBaseChange_one_tmul`: the comparison is computed by *any* two-term
  finite-projective presentation of `K`, not only by the one the determinant functor was built
  from.
* `TwoTermDeterminant.isRankZero_baseChange`: rank zero survives base change.
* `TwoTermDeterminant.detBaseChange_one_tmul_delta`: **the comparison carries the canonical
  element `δ(K)` of a rank-zero object to `δ(A ⊗^L_R K)`.**

## Implementation notes

`TwoTermDeterminant.det` is `TwoTermDeterminant.determinantFunctor` at the chosen presentations
`TwoTermDeterminant.presentation`, so its value at `K` *is* the determinant line of
`presentation R K`. The comparison is therefore
`TwoTermDeterminant.presentationDeterminantBaseChange` at that presentation, followed by the
transport `TwoTermDeterminant.presentationTransport` over `A` from the base-changed presentation
to the chosen presentation of the base-changed object.

The algebra structure on `A` is the one `φ` defines, and flatness is carried as a hypothesis
stated under that `letI`, because the type of the comparison mentions `A ⊗[R] -` and so depends
on it. It cannot be mixed with an ambient `[Algebra R A]`: `(algebraMap R A).toAlgebra` and an
ambient algebra structure have different `smul` fields and are not definitionally equal.

## References

* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 15.124.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

namespace TwoTermDeterminant

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] (φ : R →+* A)

/-- The comparison between the determinant line of a presentation and that of its base change
carries the canonical element of a rank-zero presentation to the canonical element of the
base-changed presentation. -/
theorem presentationDeterminantBaseChange_apply_delta
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K) (hP : P.IsRankZero) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    presentationDeterminantBaseChange φ hφ P (1 ⊗ₜ[R] presentationDelta P hP) =
      presentationDelta (P.baseChange φ) (P.baseChange_isRankZero φ hP) := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  exact TwoTermComplex.determinantLineBaseChange_one_tmul_delta R A hP

/-- Transporting along identities through an intermediate presentation is transporting directly. -/
private theorem presentationTransport_trans_refl {S : Type u} [CommRing S]
    {K : DerivedCategory (ModuleCat.{u} S)} (P Q T : TwoTermPresentation K) :
    (presentationTransport P Q (Iso.refl K)).trans (presentationTransport Q T (Iso.refl K)) =
      presentationTransport P T (Iso.refl K) :=
  (presentationTransport_comp P Q T (Iso.refl K) (Iso.refl K)).trans
    (congrArg (presentationTransport P T) (Iso.refl_trans (Iso.refl K)))

/-- **The determinant commutes with flat base change**: `A ⊗_R det_R(K) ≅ det_A(A ⊗^L_R K)`.

It is the base change of the determinant line of the chosen presentation of `K`, followed by the
transport over `A` from that base-changed presentation to the chosen presentation of the
base-changed object. -/
def detBaseChange (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (K : PerfectTwoTermComplex R) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    A ⊗[R] ((det R).obj ⟨K⟩).of.obj ≃ₗ[A]
      ((det A).obj ⟨PerfectTwoTermComplex.baseChange φ K⟩).of.obj :=
  letI : Algebra R A := φ.toAlgebra
  haveI : Module.Flat R A := hφ
  presentationDeterminantBaseChange φ hφ (presentation R K) ≪≫ₗ
    presentationTransport ((presentation R K).baseChange φ)
      (presentation A (PerfectTwoTermComplex.baseChange φ K)) (Iso.refl _)

/-- **The comparison is computed by any two-term finite-projective presentation of `K`.** Carry a
section of the determinant to the determinant line of `P`, base change there, and transport to
the chosen presentation downstairs: the result is the comparison. -/
theorem detBaseChange_one_tmul (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj)
    (x : presentationDeterminant (presentation R K)) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    detBaseChange φ hφ K (1 ⊗ₜ[R] x) =
      presentationTransport (P.baseChange φ)
        (presentation A (PerfectTwoTermComplex.baseChange φ K)) (Iso.refl _)
        (presentationDeterminantBaseChange φ hφ P (1 ⊗ₜ[R] detPresentationIso K P x)) := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  have key := LinearMap.congr_fun
    (presentationTransport_baseChange φ hφ (presentation R K) P (Iso.refl K.obj)) (1 ⊗ₜ[R] x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
    Functor.mapIso_refl] at key
  have hcomp := presentationTransport_trans_refl ((presentation R K).baseChange φ)
    (P.baseChange φ) (presentation A (PerfectTwoTermComplex.baseChange φ K))
  change presentationTransport ((presentation R K).baseChange φ)
      (presentation A (PerfectTwoTermComplex.baseChange φ K)) (Iso.refl _)
      (presentationDeterminantBaseChange φ hφ (presentation R K) (1 ⊗ₜ[R] x)) =
    presentationTransport (P.baseChange φ)
      (presentation A (PerfectTwoTermComplex.baseChange φ K)) (Iso.refl _)
      (presentationDeterminantBaseChange φ hφ P
        (1 ⊗ₜ[R] presentationTransport (presentation R K) P (Iso.refl K.obj) x))
  erw [← hcomp, LinearEquiv.trans_apply, key]
  rfl

/-- **Rank zero survives flat base change.** A rank-zero presentation of `K` base changes to a
rank-zero presentation of `A ⊗^L_R K`. -/
theorem isRankZero_baseChange {K : PerfectTwoTermComplex R} (hK : IsRankZero K.obj) :
    IsRankZero (PerfectTwoTermComplex.baseChange φ K).obj :=
  ⟨hK.choose.baseChange φ,
    TwoTermPresentation.baseChange_isRankZero φ hK.choose hK.choose_spec⟩

/-- **The comparison carries the canonical element of a rank-zero object to the canonical element
of its base change.** -/
theorem detBaseChange_one_tmul_delta
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (K : PerfectTwoTermComplex R) (hK : IsRankZero K.obj) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    detBaseChange φ hφ K (1 ⊗ₜ[R] delta K hK) =
      delta (PerfectTwoTermComplex.baseChange φ K) (isRankZero_baseChange φ hK) := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  have hR : IsRankZero (PerfectTwoTermComplex.baseChange φ K).obj := isRankZero_baseChange φ hK
  have hcomp := presentationTransport_trans_refl (hK.choose.baseChange φ)
    (presentation A (PerfectTwoTermComplex.baseChange φ K)) hR.choose
  refine (detPresentationIso (PerfectTwoTermComplex.baseChange φ K) hR.choose).injective ?_
  rw [detPresentationIso_delta (PerfectTwoTermComplex.baseChange φ K) hR.choose hR.choose_spec,
    detBaseChange_one_tmul φ hφ K hK.choose (delta K hK),
    detPresentationIso_delta K hK.choose hK.choose_spec]
  change (presentationTransport (presentation A (PerfectTwoTermComplex.baseChange φ K))
      hR.choose (Iso.refl _))
      (presentationTransport (hK.choose.baseChange φ)
        (presentation A (PerfectTwoTermComplex.baseChange φ K)) (Iso.refl _)
        (presentationDeterminantBaseChange φ hφ hK.choose
          (1 ⊗ₜ[R] presentationDelta hK.choose hK.choose_spec))) = _
  erw [← LinearEquiv.trans_apply, hcomp,
    presentationDeterminantBaseChange_apply_delta φ hφ hK.choose hK.choose_spec]
  exact presentationTransport_apply_delta _ _ _ _ hR.choose_spec

end TwoTermDeterminant

end
