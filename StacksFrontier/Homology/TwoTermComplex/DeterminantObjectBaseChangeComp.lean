module

public import StacksFrontier.Algebra.Module.Projective.Determinant.BaseChangeComp
public import StacksFrontier.Homology.TwoTermComplex.DeterminantObjectBaseChange

/-!
# Flat base change of the determinant of a perfect two-term object is transitive

Let `R → A → B` be a tower of flat homomorphisms of commutative rings and let `K` be a perfect
object of `D(R)` of Tor-amplitude in `[-1, 0]`. Its determinant can be carried down to `B` in one
step or in two, and `TwoTermDeterminant.detBaseChange` provides a comparison for each step. This
file proves that the two routes agree: base changing a section of `det_R(K)` to `A` and then to
`B` gives the same thing as base changing it to `B` at once.

The two routes land in the determinants of two different objects of `D(B)`, namely the twofold
derived extension of scalars `B ⊗^L_A (A ⊗^L_R K)` and the single one `B ⊗^L_R K`. Both are
computed by the base change of one and the same two-term presentation `P` of `K`, whose two
presenting complexes have terms `B ⊗_A (A ⊗_R P^i)` and `B ⊗_R P^i`; these differ by the
cancellation `TensorProduct.AlgebraTensorModule.cancelBaseChange`, and the comparison of the
determinants is accordingly conjugation by the determinants of the cancellations.

## Main results

* `TwoTermDeterminant.detPresentationIso_presentationTransport`: the comparison of the
  determinant of an object with the determinant line of a two-term presentation of it undoes the
  transport from that presentation to the chosen one.
* `TwoTermDeterminant.detPresentationIso_detBaseChange_comp`: **flat base change of the
  determinant of a perfect two-term object is transitive.** Read in the determinant line of the
  base change of a presentation `P` of `K`, the twofold comparison is the single comparison
  conjugated by the determinants of the cancellations
  `B ⊗_A (A ⊗_R P^i) ≅ B ⊗_R P^i`.

## Implementation notes

Both sides of the main statement are read in the determinant line of a base-changed presentation,
through `TwoTermDeterminant.detPresentationIso`, rather than transported into one another by the
determinant of a canonical isomorphism `B ⊗^L_R K ≅ B ⊗^L_A (A ⊗^L_R K)` of objects of `D(B)`.
This is deliberate. The determinant functor acts on an isomorphism by
`TwoTermDeterminant.presentationTransport`, which is defined through a surjective span and is only
accessible through the characterization of
`TwoTermComplex.determinantEquivOfSurjectiveQuasiIso` by its determinant diagram; computing it at
the degreewise isomorphism given by the cancellations is a separate matter, and no comparison of
that shape is available. Reading both sides in the determinant line of the presenting complex
needs none of it: the comparison `TwoTermDeterminant.detPresentationIso` is a transport along the
identity isomorphism, so by `TwoTermDeterminant.presentationTransport_comp` it undoes the
transport along the identity that `TwoTermDeterminant.detBaseChange_one_tmul` produces, and what
is left is exactly `TwoTermComplex.determinantLineBaseChange_comp`.

The statement holds for *any* two-term finite-projective presentation `P` of `K`, not only the
chosen one, because `TwoTermDeterminant.detBaseChange_one_tmul` computes the comparison from any
presentation. It is applied three times, once for each of the three flat ring maps.

The algebra structures are the ones the three ring homomorphisms define, as they are in
`TwoTermDeterminant.detBaseChange`; the scalar tower is then definitional, the algebra map of
`RingHom.comp` being the composite of the two algebra maps. Flatness of each of the three is
carried as a hypothesis stated under the corresponding `letI`, flatness over `R` of `B` not being
a consequence of the other two in the generality in which `TwoTermComplex.determinantLine`
requires it.

## References

* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 15.124.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.DerivedExtensionScalars
open scoped TensorProduct
open TensorProduct.AlgebraTensorModule (cancelBaseChange)

universe u

namespace TwoTermDeterminant

attribute [local instance] HasDerivedCategory.standard

/-- **The comparison with a two-term presentation undoes the transport to the chosen
presentation.** Both `TwoTermDeterminant.detPresentationIso` and the transport in question are
transports along the identity isomorphism of the presented object, so they compose to the
transport along the identity, which is the identity. -/
theorem detPresentationIso_presentationTransport {R : Type u} [CommRing R]
    (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj)
    (v : presentationDeterminant P) :
    detPresentationIso K P
        (presentationTransport P (presentation R K) (Iso.refl K.obj) v) = v := by
  have h := (presentationTransport_comp P (presentation R K) P (Iso.refl K.obj)
      (Iso.refl K.obj)).trans
    (congrArg (fun c => presentationTransport P P c) (Iso.refl_trans (Iso.refl K.obj)))
  show presentationTransport (presentation R K) P (Iso.refl K.obj)
    (presentationTransport P (presentation R K) (Iso.refl K.obj) v) = v
  rw [← LinearEquiv.trans_apply, h, presentationTransport_id]
  rfl

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] {B : Type u} [CommRing B]
  (φ : R →+* A) (ψ : A →+* B)

/-- The comparison of a base-changed determinant with the determinant line of the base change of a
presentation `P` sends `1 ⊗ x` to the base change of the image of `x` in the line of `P`. -/
private theorem detPresentationIso_detBaseChange
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj)
    (x : presentationDeterminant (presentation R K)) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    detPresentationIso (PerfectTwoTermComplex.baseChange φ K) (P.baseChange φ)
        (detBaseChange φ hφ K ((1 : A) ⊗ₜ[R] x)) =
      presentationDeterminantBaseChange φ hφ P ((1 : A) ⊗ₜ[R] detPresentationIso K P x) := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  rw [detBaseChange_one_tmul φ hφ K P x]
  exact detPresentationIso_presentationTransport _ _ _

/-- **Flat base change of the determinant of a perfect two-term object is transitive.**

Let `R → A → B` be a tower of flat ring homomorphisms, let `K` be a perfect object of `D(R)` of
Tor-amplitude in `[-1, 0]` and let `P` be a two-term finite-projective presentation of `K`. Read
in the determinant line of the base change of `P`, the comparison obtained by base changing a
section of `det_R(K)` first to `A` and then to `B` is the comparison obtained by base changing it
to `B` in one step, conjugated by the determinants of the cancellations
`B ⊗_A (A ⊗_R P^i) ≅ B ⊗_R P^i`. -/
theorem detPresentationIso_detBaseChange_comp
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (hψ : letI : Algebra A B := ψ.toAlgebra; Module.Flat A B)
    (hφψ : letI : Algebra R B := (ψ.comp φ).toAlgebra; Module.Flat R B)
    (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj)
    (x : ((det R).obj ⟨K⟩).of.obj) :
    letI : Algebra R A := φ.toAlgebra
    letI : Algebra A B := ψ.toAlgebra
    letI : Algebra R B := (ψ.comp φ).toAlgebra
    haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Flat R A := hφ
    haveI : Module.Flat A B := hψ
    haveI : Module.Flat R B := hφψ
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    detPresentationIso
        (PerfectTwoTermComplex.baseChange ψ (PerfectTwoTermComplex.baseChange φ K))
        ((P.baseChange φ).baseChange ψ)
        (detBaseChange ψ hψ (PerfectTwoTermComplex.baseChange φ K)
          ((1 : B) ⊗ₜ[A] detBaseChange φ hφ K ((1 : A) ⊗ₜ[R] x))) =
      (ProjectiveDeterminant.mapEquiv
            (cancelBaseChange R A B B (P.complex.X 0 : Type u))).symm.toLinearMap ∘ₗ
        detPresentationIso (PerfectTwoTermComplex.baseChange (ψ.comp φ) K)
            (P.baseChange (ψ.comp φ))
            (detBaseChange (ψ.comp φ) hφψ K ((1 : B) ⊗ₜ[R] x)) ∘ₗ
          (ProjectiveDeterminant.mapEquiv
            (cancelBaseChange R A B B (P.complex.X (-1) : Type u))).toLinearMap := by
  let : Algebra R A := φ.toAlgebra
  let : Algebra A B := ψ.toAlgebra
  let : Algebra R B := (ψ.comp φ).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat R A := hφ
  have : Module.Flat A B := hψ
  have : Module.Flat R B := hφψ
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  have hy := detPresentationIso_detBaseChange φ hφ K P x
  have hL := detPresentationIso_detBaseChange ψ hψ (PerfectTwoTermComplex.baseChange φ K)
    (P.baseChange φ) (detBaseChange φ hφ K ((1 : A) ⊗ₜ[R] x))
  rw [hy] at hL
  have hR := detPresentationIso_detBaseChange (ψ.comp φ) hφψ K P x
  have key : presentationDeterminantBaseChange ψ hψ (P.baseChange φ)
        ((1 : B) ⊗ₜ[A] presentationDeterminantBaseChange φ hφ P
          ((1 : A) ⊗ₜ[R] detPresentationIso K P x)) =
      (ProjectiveDeterminant.mapEquiv
            (cancelBaseChange R A B B (P.complex.X 0 : Type u))).symm.toLinearMap ∘ₗ
        presentationDeterminantBaseChange (ψ.comp φ) hφψ P
            ((1 : B) ⊗ₜ[R] detPresentationIso K P x) ∘ₗ
          (ProjectiveDeterminant.mapEquiv
            (cancelBaseChange R A B B (P.complex.X (-1) : Type u))).toLinearMap :=
    TwoTermComplex.determinantLineBaseChange_comp R A B (P.complex.d (-1) 0).hom
      (detPresentationIso K P x)
  rw [← hR] at key
  exact hL.trans key

end TwoTermDeterminant

end
