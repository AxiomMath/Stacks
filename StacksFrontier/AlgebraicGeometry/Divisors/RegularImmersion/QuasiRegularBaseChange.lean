module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Algebra

/-!
# Base change of a relative quasi-regular sequence

Let `A → B` be a ring map and `f₁, …, f_r ∈ B` a quasi-regular sequence whose quotient
`B/(f₁, …, f_r)` is flat over `A`.  For every `A`-algebra `A'` the base-changed sequence
`f₁ ⊗ 1, …, f_r ⊗ 1` is quasi-regular in `B' = B ⊗_A A'`, and its length — hence the
codimension of a relative quasi-regular immersion, when that codimension is constant — is
unchanged.  If moreover `A → B` is flat and of finite presentation, the base-changed sequence is
even a *regular* sequence in the local ring `B'_{q'}` at every prime `q'` of `B'` containing it.
The base-changed sequence is `KoszulH1.fp f`, the family `i ↦ f i ⊗ 1` of `B ⊗_A A'`.

## Main results

* `Koszul.quasiRegular_and_h1Regular_baseChange_of_quotient_flat`: quasi-regularity, and with it
  the length, after base change.
* `AlgebraicGeometry.flat_quotient_span_range_baseChange`: flatness of the quotient by the
  base-changed sequence.
* `AlgebraicGeometry.isRegular_atPrime_baseChange_of_isQuasiRegular`: regularity in the local
  rings along the zero locus of the base-changed sequence.

## References

* [Stacks Project, Tag 0FUD](https://stacks.math.columbia.edu/tag/0FUD)
* [Stacks Project, Tag 0CEP](https://stacks.math.columbia.edu/tag/0CEP)
* [Stacks Project, Tag 063U](https://stacks.math.columbia.edu/tag/063U)
-/

@[expose] public section

open RingTheory.Sequence
open scoped TensorProduct

add_to_stacks 0FUD "quasi-regularity and constant length after base change"
  Koszul.quasiRegular_and_h1Regular_baseChange_of_quotient_flat

namespace AlgebraicGeometry

/-- If `R` is flat over `A`, then `R ⊗[A] A'` is flat over `A'`. -/
private theorem flat_tensor_right {A R A' : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [CommRing A'] [Algebra A A'] [Module.Flat A R] :
    letI : Algebra A' (R ⊗[A] A') := Algebra.TensorProduct.rightAlgebra
    Module.Flat A' (R ⊗[A] A') := by
  let : Algebra A' (R ⊗[A] A') := Algebra.TensorProduct.rightAlgebra
  let ec : A' ⊗[A] R ≃ₐ[A'] R ⊗[A] A' :=
    { (Algebra.TensorProduct.comm A A' R).toRingEquiv with commutes' := fun a => rfl }
  have _ : Module.Flat A' (A' ⊗[A] R) := Module.Flat.baseChange A A' R
  exact Module.Flat.of_linearEquiv ec.symm.toLinearEquiv

/-- **The quotient by a base-changed sequence stays flat.**  If `B/(f₁, …, f_r)` is flat over
`A`, then `B' / (f₁ ⊗ 1, …, f_r ⊗ 1)` is flat over `A'`, where `B' = B ⊗_A A'`. -/
theorem flat_quotient_span_range_baseChange
    {A B A' : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing A'] [Algebra A A']
    {r : ℕ} (f : Fin r → B) (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f))) :
    letI : Algebra A' (B ⊗[A] A') := Algebra.TensorProduct.rightAlgebra
    Module.Flat A' ((B ⊗[A] A') ⧸
      Ideal.span (Set.range (KoszulH1.fp (A := A) (A' := A') f))) := by
  let C := B ⊗[A] A'
  let I : Ideal B := Ideal.span (Set.range f)
  let j : B →ₐ[A] C := Algebra.TensorProduct.includeLeft (R := A) (A := B) (B := A')
  have hmap : I.map j.toRingHom = Ideal.span (Set.range (KoszulH1.fp (A := A) (A' := A') f)) := by
    simp only [I, j, Ideal.map_span, ← Set.range_comp, Algebra.TensorProduct.includeLeft]
    exact congrArg Ideal.span (congrArg Set.range (funext fun i => rfl))
  let _ : Algebra A' C := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra A' (C ⧸ I.map j.toRingHom) := Ideal.Quotient.algebra A'
  let _ : Algebra A' ((B ⧸ I) ⊗[A] A') := Algebra.TensorProduct.rightAlgebra
  have _ : Module.Flat A' ((B ⧸ I) ⊗[A] A') := flat_tensor_right
  let e₁ : (B ⧸ I) ⊗[A] A' ≃ₐ[A] C ⧸ I.map j.toRingHom :=
    Algebra.TensorProduct.quotientTensorEquiv (R := A) (S := A) (T := A') (A := B) I
  let e₁A : ((B ⧸ I) ⊗[A] A') ≃ₐ[A'] (C ⧸ I.map j.toRingHom) :=
    { e₁.toRingEquiv with
      commutes' := by
        intro a
        change Algebra.TensorProduct.quotientTensorEquiv (R := A) (S := A) (T := A')
            (A := B) I (Ideal.Quotient.mk I (1 : B) ⊗ₜ[A] a) =
          Ideal.Quotient.mk (I.map j.toRingHom) ((1 : B) ⊗ₜ[A] a)
        rw [Algebra.TensorProduct.quotientTensorEquiv_apply_tmul]
        rfl }
  rw [← hmap]
  exact Module.Flat.of_linearEquiv e₁A.toLinearEquiv.symm

/-- Let `A → B` be flat and of finite presentation and let `f₁, …, f_r ∈ B` be a quasi-regular
sequence whose quotient is flat over `A`.  For any `A`-algebra `A'` and any prime `q` of
`B' = B ⊗_A A'` containing the base-changed sequence, that sequence is regular in the local ring
`B'_q`. -/
@[stacks 0FUD "regularity at primes after base change"]
theorem isRegular_atPrime_baseChange_of_isQuasiRegular
    {A B A' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing A'] [Algebra A A'] [Module.Flat A B]
    [Algebra.FinitePresentation A B] {r : ℕ} (f : Fin r → B)
    (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (hf : IsQuasiRegular B (List.ofFn f))
    (q : Ideal (B ⊗[A] A')) [q.IsPrime]
    (hq : Ideal.span (Set.range (KoszulH1.fp (A := A) (A' := A') f)) ≤ q) :
    IsRegular (Localization.AtPrime q)
      ((List.ofFn (KoszulH1.fp (A := A) (A' := A') f)).map
        (algebraMap (B ⊗[A] A') (Localization.AtPrime q))) := by
  let C := B ⊗[A] A'
  let g := KoszulH1.fp (A := A) (A' := A') f
  let _ : Algebra A' C := Algebra.TensorProduct.rightAlgebra
  let eC : (A' ⊗[A] B) ≃ₐ[A'] C :=
    { (Algebra.TensorProduct.comm A A' B).toRingEquiv with commutes' := fun a => rfl }
  have _ : Module.Flat A' C := flat_tensor_right (A := A) (R := B) (A' := A')
  let _ : Algebra.FinitePresentation A' (A' ⊗[A] B) :=
    Algebra.FinitePresentation.baseChange (R := A) (A := B) A'
  let _ : Algebra.FinitePresentation A' C := Algebra.FinitePresentation.equiv eC
  have hqr : IsQuasiRegular C (List.ofFn g) :=
    (Koszul.quasiRegular_and_h1Regular_baseChange_of_quotient_flat f hflat).1 hf
  have hflatC : Module.Flat A' (C ⧸ Ideal.span (Set.range g)) :=
    flat_quotient_span_range_baseChange f hflat
  have hmem : ∀ i, g i ∈ q := fun i => hq (Ideal.subset_span (Set.mem_range_self i))
  have hreg :=
    (Stacks.RingTheory.RelativeQuasiRegular.isRegular_localization_and_flat_quotients
      (R := A') (S := C) g hqr hflatC q hmem).1
  simpa only [List.map_ofFn, Function.comp_def] using hreg

end AlgebraicGeometry

end
