module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionDeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDividedPowerForms

/-!
# The degree-zero term of the complex `M ⊗^∧_D Ω^*_D`

The proof of [Stacks, Proposition 60.21.3, Tag 07LG] runs over a double complex whose terms are
`M ⊗̂ Ω^a_{D(b)}`, and both of its edges are read in exterior degree zero: the column `a = 0` is
the complex `M(0) → M(1) → M(2) → ⋯` of [Stacks, Proposition 60.20.1, Tag 07JN], and the degree
zero term of the row `b = 0` is the degree zero term of `M ⊗^∧_D Ω^*_D`.  Both identifications
rest on one piece of algebra, which this module supplies: **in exterior degree zero the forms are
the ring and the completed tensor product is the module itself.**

## The two steps

`Crystalline.completedDividedPowerForms` is by definition the `p`-adic completion of
`Crystalline.dividedPowerDifferentialForms`, which is an exterior power, so in degree zero it is
the `p`-adic completion of `⋀⁰_B Ω_{B/A,δ} ≅ B`, that is the ring `D` itself:
`Crystalline.completedDividedPowerFormsZeroEquiv`.  This is an identification over `D`, not
merely of abelian groups, because `Mathlib`'s `exteriorPower.zeroEquiv` is `B`-linear and
`AdicCompletion.congr` carries a `B`-linear equivalence to a `D`-linear one.

Given that, `Crystalline.CompletedTensor` in degree zero is the `p`-adic completion of
`M ⊗_D D ≅ M`, so it is the completion `M̂` of `M`
(`Crystalline.completedTensorUnitEquiv`); and if `M` is already `p`-adically complete — which the
module of [Stacks, Tag 07JG] is, being an inverse limit over the levels — the completion is `M`
(`Crystalline.completedTensorUnitAddEquivOfComplete`).  So the degree zero term of
`Crystalline.CompletedDeRham.complex` is `M`, which is
`Crystalline.CompletedDeRham.complexXZeroIso`.

## Main definitions

* `Crystalline.completedTensorUnitEquiv` — **`M ⊗̂_D Ω ≅ M̂` for a forms module `Ω` which is free
  of rank one on its unit**, that is for a `D`-linear equivalence `Ω ≃ D`.
* `Crystalline.completedTensorUnitAddEquivOfComplete` — **`M ⊗̂_D Ω ≅ M`** when moreover `M` is
  `p`-adically complete.
* `Crystalline.completedDividedPowerFormsZeroEquiv` — **`Ω^0_D ≅ D`**, the degree zero completed
  divided power forms are the ring.
* `Crystalline.CompletedDeRham.complexXZeroIso` — **the degree zero term of `M ⊗^∧_D Ω^*_D` is
  `M`**, as an isomorphism of `AddCommGrpCat`.

## Main results

* `Crystalline.completedTensorUnitEquiv_of_tmul` — the identification carries `m ⊗ ω` to the
  image of `e ω • m`, which pins it down: the pure tensors span and their images are
  `p`-adically dense.
* `Crystalline.completedDividedPowerFormsZeroEquiv_of` — and the degree zero identification
  carries the image of a zero-form to the image of its scalar.

No tag attribute is placed: the degree-zero identification is a step inside the proof of
[Stacks, Tag 07LG] and is not the statement of a tag.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public section

open DividedPowers
open scoped TensorProduct

universe u v w

namespace Crystalline

/-! ### Tensoring with a forms module of rank one -/

section Unit

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M]

/-- **`M ⊗̂_D Ω ≅ M̂` for a module of forms `Ω` identified with `D`.**

The completed tensor product is the `p`-adic completion of `M ⊗_D Ω`; the identification
`e : Ω ≃ D` turns that into `M ⊗_D D`, which is `M`.  The result is linear over the completion
`D̂` of `D`, which is the ring the completed tensor product is a module over. -/
public noncomputable def completedTensorUnitEquiv (e : Omega ≃ₗ[D] D) :
    CompletedTensor p D Omega M ≃ₗ[AdicCompletion (pAdicIdeal (A := D) p) D]
      AdicCompletion (pAdicIdeal (A := D) p) M :=
  AdicCompletion.congr (pAdicIdeal (A := D) p)
    ((TensorProduct.congr (LinearEquiv.refl D M) e).trans (TensorProduct.rid D M))

/-- **The identification carries `m ⊗ ω` to `e ω • m`.**  The images of the pure tensors are
`p`-adically dense, so this equation pins the identification down. -/
public theorem completedTensorUnitEquiv_of_tmul (e : Omega ≃ₗ[D] D) (m : M) (omega : Omega) :
    completedTensorUnitEquiv p D Omega M e (toCompletedTensor p D Omega M (m ⊗ₜ[D] omega)) =
      AdicCompletion.of (pAdicIdeal (A := D) p) M (e omega • m) := by
  rw [completedTensorUnitEquiv, AdicCompletion.congr_apply, AdicCompletion.map_of]
  rfl

/-- **The canonical map into the `p`-adic completion of a complete module is an isomorphism.** -/
public noncomputable def adicCompletionOfAddEquiv [IsAdicComplete (pAdicIdeal (A := D) p) M] :
    M ≃+ AdicCompletion (pAdicIdeal (A := D) p) M :=
  AddEquiv.ofBijective (AdicCompletion.of (pAdicIdeal (A := D) p) M).toAddMonoidHom
    (AdicCompletion.of_bijective (pAdicIdeal (A := D) p) M)

/-- The isomorphism `adicCompletionOfAddEquiv` sends `m` to its image
`AdicCompletion.of (pAdicIdeal p) M m` in the `p`-adic completion. -/
@[simp] public theorem adicCompletionOfAddEquiv_apply
    [IsAdicComplete (pAdicIdeal (A := D) p) M] (m : M) :
    adicCompletionOfAddEquiv p D M m = AdicCompletion.of (pAdicIdeal (A := D) p) M m := rfl

/-- **`M ⊗̂_D Ω ≅ M` for a module of forms `Ω` identified with `D` and a `p`-adically complete
`M`.**  The module of [Stacks, Tag 07JG] is `p`-adically complete, being the inverse limit of the
sections over the levels, so this is the shape the degree-zero edge of the double complex of
[Stacks, Tag 07LG] is read in.  It is stated additively because the identification of the edge
of the double complex happens in `AddCommGrpCat`. -/
public noncomputable def completedTensorUnitAddEquivOfComplete (e : Omega ≃ₗ[D] D)
    [IsAdicComplete (pAdicIdeal (A := D) p) M] : CompletedTensor p D Omega M ≃+ M :=
  (completedTensorUnitEquiv p D Omega M e).toAddEquiv.trans
    (adicCompletionOfAddEquiv p D M).symm

/-- The identification with a complete `M` carries `m ⊗ ω` to `e ω • m`. -/
public theorem completedTensorUnitAddEquivOfComplete_of_tmul (e : Omega ≃ₗ[D] D)
    [IsAdicComplete (pAdicIdeal (A := D) p) M] (m : M) (omega : Omega) :
    completedTensorUnitAddEquivOfComplete p D Omega M e
        (toCompletedTensor p D Omega M (m ⊗ₜ[D] omega)) = e omega • m := by
  refine (adicCompletionOfAddEquiv p D M).injective ?_
  change (adicCompletionOfAddEquiv p D M) ((adicCompletionOfAddEquiv p D M).symm
    (completedTensorUnitEquiv p D Omega M e
      (toCompletedTensor p D Omega M (m ⊗ₜ[D] omega)))) = _
  rw [AddEquiv.apply_symm_apply, completedTensorUnitEquiv_of_tmul,
    adicCompletionOfAddEquiv_apply]

end Unit

/-! ### The completed divided power forms in degree zero -/

section Forms

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J)

/-- **`Ω^0_D ≅ D`**: the completed divided power forms in exterior degree zero are the completed
ring.  `Crystalline.dividedPowerDifferentialForms` is an exterior power, whose degree zero is the
base ring by `exteriorPower.zeroEquiv`, and `p`-adic completion carries that `B`-linear
equivalence to a `D`-linear one. -/
public noncomputable def completedDividedPowerFormsZeroEquiv :
    completedDividedPowerForms p A hJ 0 ≃ₗ[completedDividedPowerRing p (B := B)]
      completedDividedPowerRing p (B := B) :=
  AdicCompletion.congr (pAdicIdeal (A := B) p)
    (exteriorPower.zeroEquiv B (dividedPowerDifferentials (A := A) hJ))

/-- The degree zero identification carries the image of a zero-form to the image of its
scalar. -/
public theorem completedDividedPowerFormsZeroEquiv_of
    (omega : dividedPowerDifferentialForms (A := A) hJ 0) :
    completedDividedPowerFormsZeroEquiv p A hJ
        (AdicCompletion.of (pAdicIdeal (A := B) p) _ omega) =
      AdicCompletion.of (pAdicIdeal (A := B) p) B
        (exteriorPower.zeroEquiv B (dividedPowerDifferentials (A := A) hJ) omega) :=
  AdicCompletion.map_of (pAdicIdeal (A := B) p)
    (exteriorPower.zeroEquiv B (dividedPowerDifferentials (A := A) hJ)).toLinearMap omega

/-! ### Functoriality in degree zero -/

variable {C : Type*} [CommRing C] [Algebra A C] {Kid : Ideal C} (epsilon : DividedPowers Kid)
  (f : B →ₐ[A] C) (hf : DividedPowers.IsDPMorphism hJ epsilon f.toRingHom)

/-- **In exterior degree zero the comparison of forms along a divided power morphism is the
morphism itself.**

The module documentation of `Crystalline.mapDifferentialFormsOfDPMorphism` says so; this is the
equation.  Degree zero of an exterior power is spanned by the empty wedge, the comparison carries
the empty wedge to the empty wedge, and it is semilinear over `f`, so on `r · 1` it is
`f r · 1`. -/
public theorem mapDifferentialFormsOfDPMorphism_zero
    (omega : dividedPowerDifferentialForms (A := A) hJ 0) :
    exteriorPower.zeroEquiv C (dividedPowerDifferentials (A := A) epsilon)
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf 0 omega) =
      f (exteriorPower.zeroEquiv B (dividedPowerDifferentials (A := A) hJ) omega) := by
  set r := exteriorPower.zeroEquiv B (dividedPowerDifferentials (A := A) hJ) omega with hr
  have hsplit : omega = r • exteriorPower.ιMulti B 0 (fun i ↦ Fin.elim0 i) := by
    refine (exteriorPower.zeroEquiv B (dividedPowerDifferentials (A := A) hJ)).injective ?_
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one, ← hr]
  rw [hsplit, map_smulₛₗ, map_smul,
    mapDifferentialFormsOfDPMorphism_ιMulti (A := A) (J := J) (delta := hJ) epsilon f hf 0,
    exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  rfl

/-- **The degree zero identification `Ω^0_D ≅ D` intertwines the comparison of completed forms
with the completion of the divided power morphism**, on the `p`-adically dense image of the
uncompleted forms.

This is the degree zero edge of the bigraded family `Ω^a_{D(b)}` of
[Stacks, Proposition 60.21.3, Tag 07LG]: in exterior degree zero the transition maps of the
forms in the cosimplicial direction are the transition maps of the cosimplicial ring `D(*)`
itself, so the column `a = 0` of the double complex is `M(•) ⊗̂_{D(•)} D(•)`. -/
public theorem completedDividedPowerFormsZeroEquiv_completedMap_of
    (omega : dividedPowerDifferentialForms (A := A) hJ 0) :
    completedDividedPowerFormsZeroEquiv p A epsilon
        (completedMapDifferentialForms p A hJ epsilon f hf 0
          (AdicCompletion.of (pAdicIdeal (A := B) p) _ omega)) =
      AdicCompletion.of (pAdicIdeal (A := C) p) C
        (f (exteriorPower.zeroEquiv B (dividedPowerDifferentials (A := A) hJ) omega)) := by
  rw [completedMapDifferentialForms_of, completedDividedPowerFormsZeroEquiv_of,
    mapDifferentialFormsOfDPMorphism_zero]

end Forms

/-! ### The degree-zero term of the complex -/

namespace CompletedDeRham

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type w) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)

/-- **The degree-zero term of `M ⊗^∧_D Ω^*_D` is `M`.**

The hypotheses are the two of `Crystalline.completedTensorUnitAddEquivOfComplete`: the forms in
exterior degree zero are the ring, which for the completed divided power forms is
`Crystalline.completedDividedPowerFormsZeroEquiv`, and `M` is `p`-adically complete, which the
module of [Stacks, Tag 07JG] is.  This is the identification the edge `b = 0` of the double
complex of [Stacks, Tag 07LG] is read through in exterior degree zero. -/
public noncomputable def complexXZeroIso (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (e : Om 0 ≃ₗ[D] D) [IsAdicComplete (pAdicIdeal (A := D) p) M] :
    (complex p D Om wedge deRham M nabla hleib hsq).X 0 ≅ AddCommGrpCat.of M where
  hom := AddCommGrpCat.ofHom (completedTensorUnitAddEquivOfComplete p D (Om 0) M e).toAddMonoidHom
  inv := AddCommGrpCat.ofHom
    (completedTensorUnitAddEquivOfComplete p D (Om 0) M e).symm.toAddMonoidHom
  hom_inv_id := AddCommGrpCat.ext fun x =>
    (completedTensorUnitAddEquivOfComplete p D (Om 0) M e).symm_apply_apply x
  inv_hom_id := AddCommGrpCat.ext fun x =>
    (completedTensorUnitAddEquivOfComplete p D (Om 0) M e).apply_symm_apply x

end CompletedDeRham

end Crystalline

end
