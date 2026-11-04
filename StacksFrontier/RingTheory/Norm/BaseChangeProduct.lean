module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Norm.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The norm of a product algebra, and the norm under base change along a separable extension

Let `K` be a field, `L/K` a finite extension and `M/K` a finite separable extension. Then
`M ⊗_K L` is a finite-dimensional reduced `M`-algebra, hence a finite product of fields `∏ Mᵢ`,
and for `t ∈ L` with images `tᵢ ∈ Mᵢ` one has

`Nm_{L/K}(t) = ∏ᵢ Nm_{Mᵢ/M}(tᵢ)` in `M`.

This is the field-theoretic step at the end of the proof of **Stacks 0EQ4**, where the source
states it and writes "we omit the proof". It is the one piece of that proof the Stacks project
does not supply, and it is proved here.

The route is the obvious one. The norm commutes with base change because the determinant does
(`LinearMap.det_baseChange`), so `Nm_{M ⊗_K L / M}(1 ⊗ t)` is the image of `Nm_{L/K}(t)`. The
norm of a finite product algebra is the product of the norms, because the determinant of a
product of endomorphisms is the product of the determinants. And `M ⊗_K L` is reduced when
`M/K` is separable (`Algebra.FormallyUnramified.isReduced_of_field`), so being also
finite-dimensional over a field it is Artinian and reduced, hence the product of its quotients
by its maximal ideals (`IsArtinianRing.equivPi`).

## Main results

* `Stacks.Norm.norm_tmul_one`: the norm commutes with base change, `Nm_{A ⊗_R S / A}(1 ⊗ s)` is
  the image of `Nm_{S/R}(s)`, for `S` finite free over `R`.
* `Stacks.Norm.norm_prod_apply`: the norm of a pair in a product of two finite free algebras is
  the product of the two norms.
* `Stacks.Norm.norm_pi_apply`: the norm of a section of a finite family of finite free algebras
  is the product of the norms of its components.
* `Stacks.Norm.norm_eq_prod_quotient`: on a finite-dimensional reduced algebra over a field the
  norm is the product of the norms of the images in the quotients by the maximal ideals.
* `Stacks.Norm.norm_baseChange_eq_prod_quotient`: **the omitted step of Stacks 0EQ4.** For
  `L/K` finite and `M/K` finite separable, the image in `M` of `Nm_{L/K}(t)` is the product over
  the maximal ideals of `M ⊗_K L` of the norms over `M` of the images of `1 ⊗ t`.

## Implementation notes

The decomposition `M ⊗_K L = ∏ Mᵢ` is not produced as a separate statement: the family of
factors is taken to be the family of quotients of `M ⊗_K L` by its maximal ideals, indexed by
`MaximalSpectrum (M ⊗_K L)`, which is the form `IsArtinianRing.equivPi` delivers and the form in
which the conclusion is used. Finiteness of that index set is an instance hypothesis
`Fintype (MaximalSpectrum (M ⊗_K L))` rather than being derived, so that no choice of
decomposition is baked in.

`Stacks.Norm.norm_pi_apply` is proved by induction on the index type with
`Fintype.induction_empty_option` rather than from `LinearMap.det_pi`, because the latter is
stated for a family of endomorphisms of a *single* module and the family of factors here is
heterogeneous.

Mathlib's `Algebra.norm` is `1` by convention on an algebra that is not finite free, so every
statement below carries freeness and finiteness hypotheses on the factors; over a field they are
automatic from finite-dimensionality. The parallel norm for finite *projective* algebras in
`StacksFrontier.RingTheory.Norm.Projective` already has the base-change statement
`Algebra.projectiveNorm_baseChange`, but no product statement, and it is restricted to a
single universe, so `Stacks.Norm.norm_tmul_one` is proved here directly from
`LinearMap.det_baseChange`.

## References

* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Norm

/-- **The norm commutes with base change.** For `S` a finite free `R`-algebra and `A` any
`R`-algebra, the norm over `A` of `1 ⊗ s` in `A ⊗_R S` is the image in `A` of the norm over `R`
of `s`.

Multiplication by `1 ⊗ s` on `A ⊗_R S` is the base change along `R → A` of multiplication by
`s` on `S`, and the determinant commutes with base change. -/
theorem norm_tmul_one {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Module.Free R S] [Module.Finite R S] (s : S) :
    Algebra.norm A (1 ⊗ₜ[R] s : A ⊗[R] S) = algebraMap R A (Algebra.norm R s) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  ext a
  simp

/-- **The norm of a product of two algebras is the product of the norms.** Multiplication by a
pair on `S × T` is the product of the two multiplications, and the determinant of a product of
endomorphisms is the product of the determinants. -/
theorem norm_prod_apply {R S T : Type*} [CommRing R] [Ring S] [Ring T] [Algebra R S] [Algebra R T]
    [Module.Free R S] [Module.Finite R S] [Module.Free R T] [Module.Finite R T] (s : S × T) :
    Algebra.norm R s = Algebra.norm R s.1 * Algebra.norm R s.2 := by
  simp only [Algebra.norm_apply]
  rw [← LinearMap.det_prodMap]
  rfl

/-- **The norm of a finite product of algebras is the product of the norms.** For a finite family
`S i` of finite free `R`-algebras the norm over `R` of a section `s` of `∀ i, S i` is the product
over `i` of the norms of its components.

The induction is on the index type, through `Fintype.induction_empty_option`: the empty case is
the norm on a subsingleton algebra, and the step adds one factor and applies
`Stacks.Norm.norm_prod_apply`. -/
theorem norm_pi_apply {R : Type*} [CommRing R] : ∀ {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, Ring (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] (s : ∀ i, S i),
    Algebra.norm R s = ∏ i, Algebra.norm R (s i) := by
  classical
  apply Fintype.induction_empty_option
  · intro ι κ _ e ih S _ _ _ _ s
    let : Fintype ι := Fintype.ofEquiv κ e.symm
    rw [← Algebra.norm_eq_of_algEquiv (AlgEquiv.piCongrLeft R S e).symm, ih]
    exact e.prod_comp (fun i => Algebra.norm R (s i))
  · intro S _ _ _ _ s
    simp [Algebra.norm_apply, LinearMap.det_eq_one_of_subsingleton]
  · intro ι _ ih S _ _ _ _ s
    let e : (∀ i, S i) ≃ₐ[R] S none × (∀ i, S (some i)) :=
      { RingEquiv.piOptionEquivProd with commutes' := fun _ => rfl }
    rw [← Algebra.norm_eq_of_algEquiv e, norm_prod_apply, ih]
    simp [e, Fintype.prod_option]

/-- **The norm on a finite-dimensional reduced algebra over a field is the product of the norms
of the components.** A finite-dimensional algebra over a field is Artinian, and a reduced
Artinian ring is the product of its quotients by its maximal ideals, so the norm is the product
of the norms of the images there. -/
theorem norm_eq_prod_quotient {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [IsReduced A] [Fintype (MaximalSpectrum A)] (a : A) :
    Algebra.norm K a =
      ∏ p : MaximalSpectrum A, Algebra.norm K (Ideal.Quotient.mk p.asIdeal a) := by
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  let e := (IsArtinianRing.equivPi A).restrictScalars K
  rw [← Algebra.norm_eq_of_algEquiv e, norm_pi_apply]
  rfl

/-- **The field-theoretic step of Stacks 0EQ4, whose proof the source omits.** Let `K` be a
field, `L/K` a finite extension and `M/K` a finite *separable* extension. Then `M ⊗_K L` is a
finite product of fields `∏ᵢ Mᵢ` — concretely, the product of its quotients by its maximal
ideals — and for `t ∈ L` the image in `M` of `Nm_{L/K}(t)` is the product of the norms over `M`
of the images `tᵢ` of `1 ⊗ t`:

`Nm_{L/K}(t) = ∏ᵢ Nm_{Mᵢ/M}(tᵢ)` in `M`.

Separability of `M/K` is what makes `M ⊗_K L` reduced, and being also finite-dimensional over
`M` it is then the product of its residue fields. The identity itself is base change of the norm
followed by multiplicativity over the factors. -/
@[stacks 0EQ4 "the field-theoretic norm compatibility at the end of the proof, for which the
source says 'we omit the proof': for L/K finite and M/K finite separable, M ⊗_K L = ∏ M_i and
Nm_{L/K}(t) = ∏ Nm_{M_i/M}(t_i)"]
theorem norm_baseChange_eq_prod_quotient {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [FiniteDimensional K L] [FiniteDimensional K M]
    [Algebra.IsSeparable K M] [Fintype (MaximalSpectrum (M ⊗[K] L))] (t : L) :
    algebraMap K M (Algebra.norm K t) =
      ∏ p : MaximalSpectrum (M ⊗[K] L),
        Algebra.norm M (Ideal.Quotient.mk p.asIdeal (1 ⊗ₜ[K] t)) := by
  have : Algebra.FormallyUnramified K M := Algebra.FormallyUnramified.of_isSeparable K M
  have : IsReduced (L ⊗[K] M) := Algebra.FormallyUnramified.isReduced_of_field L _
  have : IsReduced (M ⊗[K] L) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K M L)
      (Algebra.TensorProduct.comm K M L).injective
  rw [← norm_tmul_one, norm_eq_prod_quotient]

end Stacks.Norm

end
