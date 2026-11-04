module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberDivisor
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.StepAssembly
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection

/-!
# Lowering an intersection number along a first difference

Let `k` be a field, let `X` be a proper scheme over `k`, let `i : Z ⟶ X` be a closed subscheme
of dimension at most `d + 1`, let `j : W ⟶ X` be a closed subscheme of dimension at most `d`
and let `𝓛_1, …, 𝓛_{d+1}` be invertible `𝒪_X`-modules.  If the Euler characteristics of the
twists of `𝒪_Z` satisfy the first-difference relation

`χ(Z, 𝓛_2^{⊗ n_2} ⊗ ⋯ |_Z) - χ(Z, 𝓛_1^{⊗ -1} ⊗ 𝓛_2^{⊗ n_2} ⊗ ⋯ |_Z)
  = χ(W, 𝓛_2^{⊗ n_2} ⊗ ⋯ |_W)`

at the indicator tuples, and if a rational polynomial of total degree at most `d + 1` takes the
Euler characteristics of the twists of `𝒪_Z` as its values, then

`(𝓛_1 ⋯ 𝓛_{d+1} · Z) = (𝓛_2 ⋯ 𝓛_{d+1} · W)`.

This is the numerical content of [Stacks, Tag 0BEU], separated from the geometry that supplies
the first-difference relation.  There `W` is an effective Cartier divisor `D ⊂ Z` with
`𝓛_1|_Z ≅ 𝒪_Z(D)`, and the relation comes from the exact sequence
`0 ⟶ 𝒪_Z(-D) ⟶ 𝒪_Z ⟶ 𝒪_D ⟶ 0` twisted by `𝓛_2^{⊗ n_2} ⊗ ⋯ ⊗ 𝓛_{d+1}^{⊗ n_{d+1}}`, through
additivity of the Euler characteristic.

## Main results

* `AlgebraicGeometry.intersectionNumber_eq_of_sub_eulerCharacteristic_eq`: the displayed
  implication, with the interpolating polynomial carried.
* `AlgebraicGeometry.intersectionNumber_eq_of_sub_eulerCharacteristic_eq_of_finiteDimensional`:
  the same with the polynomial supplied by [Stacks, Tag 02O6], leaving exactly that tag and the
  first-difference relation as hypotheses.

## Implementation notes

**Why the first difference is taken between `n_1 = 0` and `n_1 = -1`.**  The intersection number
of `StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersection.lean` is the mixed finite
difference of the numerical function at the indicator tuples, so the difference in the first
variable it reads off is the one between `n_1 = 1` and `n_1 = 0`.  Taking it instead between
`n_1 = 0` and `n_1 = -1` makes the third term of the twisted divisor sequence carry
`𝓛_1^{⊗ 0}`, so that it is the twist of `𝒪_D` by `𝓛_2, …, 𝓛_{d+1}` alone — exactly the module
whose Euler characteristics define `(𝓛_2 ⋯ 𝓛_{d+1} · D)`.  That the two differences agree is
`MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one`, and its independence of the base
point is the degree bound `hPdeg`; this is the same device as on algebraic spaces, where the
corresponding statement is
`AlgebraicGeometry.Space.intersectionNumber_eq_of_sub_eulerCharacteristic_eq`.

**Why the polynomial is a hypothesis.**  [Stacks, Tag 0BEM], the existence of a rational
polynomial of total degree at most `dim Supp ℱ` interpolating the Euler characteristics of the
twists, is reduced in this library to [Stacks, Tag 02O6] alone, by
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology`.  The
polynomial is nevertheless carried here, exactly as it is by the neighbouring
`AlgebraicGeometry.intersectionNumber_eq_coeff`, whose hypotheses `P`, `hP` and `hPdeg` are
reproduced verbatim, so that this file's numerical argument stays independent of how the
polynomial is obtained.  **No `@[stacks 0BEU]` attribute is attached**: the statements below have
hypotheses the tag does not, namely `P`, `hP`, `hPdeg` and `hdiff`.  The tag sits on
`AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor` in
`StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersections/DivisorIntersectionProper.lean`,
where every one of them is discharged; Tag 02O6 itself is proved in this library, as
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`.

**Where the monomial computation comes from.**  The identity
`MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one` is pure algebra and is already
proved, in `StacksFrontier/AlgebraicGeometry/Spaces/IntersectionNumberDivisor.lean`, where the
same argument is run for algebraic spaces.  It is imported rather than restated: a second copy
of it would be the only difference between the two files' numerical halves.

**Why `W` is an arbitrary closed subscheme of `X`.**  Tag 0BEU's divisor `D` is a closed
subscheme of `Z`, and its intersection number is computed along the composite closed immersion
`D ⟶ Z ⟶ X`; stating the numerical implication for an arbitrary closed immersion `j : W ⟶ X`
costs nothing and lets the geometric supplier choose that composite.

## References

* [Stacks Project, Tag 0BEU](https://stacks.math.columbia.edu/tag/0BEU)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The numerical content of [Stacks, Tag 0BEU].**  Let `i : Z ⟶ X` be a closed subscheme of
dimension at most `d + 1` of a scheme `X` proper over a field `k`, let `j : W ⟶ X` be a closed
subscheme of dimension at most `d`, and let `𝓛_1, …, 𝓛_{d+1}` be invertible `𝒪_X`-modules.
Suppose a rational polynomial `P` of total degree at most `d + 1` takes the Euler
characteristics `χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_{d+1}^{⊗ n_{d+1}}|_Z)` as its values at the integral
tuples, and that for every `S ⊆ {2, …, d + 1}`

`χ(Z, ⨂_{t ∈ S} 𝓛_t|_Z) - χ(Z, 𝓛_1^{⊗ -1} ⊗ ⨂_{t ∈ S} 𝓛_t|_Z) = χ(W, ⨂_{t ∈ S} 𝓛_t|_W)`.

Then `(𝓛_1 ⋯ 𝓛_{d+1} · Z) = (𝓛_2 ⋯ 𝓛_{d+1} · W)`.

The hypothesis `hdiff` is what the twisted divisor sequence of an effective Cartier divisor
`D ⊂ Z` with `𝓛_1|_Z ≅ 𝒪_Z(D)` supplies, through additivity of the Euler characteristic, and
`P` is [Stacks, Tag 0BEM]; neither is proved here, so no tag attribute is attached. -/
public theorem intersectionNumber_eq_of_sub_eulerCharacteristic_eq (k : Type u) [Field k]
    {X Z W : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (j : W ⟶ X) [IsClosedImmersion j] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (hdW : topologicalKrullDim W ≤ d)
    (L : Fin (d + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)]
    (P : MvPolynomial (Fin (d + 1)) ℚ)
    (hP : ∀ n : Fin (d + 1) → ℤ, MvPolynomial.eval (fun t => (n t : ℚ)) P =
      ((@eulerCharacteristic k _ Z (i ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj (L t)) n)
        (isCoherent_twistedSheafUnitPullback k f i L n) : ℤ) : ℚ))
    (hPdeg : P.totalDegree ≤ d + 1)
    (hdiff : ∀ S : Finset (Fin d),
      (@eulerCharacteristic k _ Z (i ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun t => (Scheme.Modules.pullback i).obj (L t))
            (Fin.cons 0 fun t => if t ∈ S then 1 else 0))
          (isCoherent_twistedSheafUnitPullback k f i L
            (Fin.cons 0 fun t => if t ∈ S then 1 else 0)) : ℤ) -
        (@eulerCharacteristic k _ Z (i ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun t => (Scheme.Modules.pullback i).obj (L t))
            (Fin.cons (-1) fun t => if t ∈ S then 1 else 0))
          (isCoherent_twistedSheafUnitPullback k f i L
            (Fin.cons (-1) fun t => if t ∈ S then 1 else 0)) : ℤ) =
      (@eulerCharacteristic k _ W (j ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit W.ringCatSheaf)
          (fun t : Fin d => (Scheme.Modules.pullback j).obj (L t.succ))
          (fun t => if t ∈ S then 1 else 0))
        (isCoherent_twistedSheafUnitPullback k f j (fun t : Fin d => L t.succ)
          fun t => if t ∈ S then 1 else 0) : ℤ)) :
    intersectionNumber k f i (d + 1) hd L =
      intersectionNumber k f j d hdW fun t : Fin d => L t.succ := by
  classical
  have hcast : ∀ (m : ℤ) (S : Finset (Fin d)),
      (fun t : Fin (d + 1) =>
          (((Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0 : Fin (d + 1) → ℤ) t : ℤ) : ℚ)) =
        (Fin.cons (m : ℚ) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) := by
    intro m S
    refine funext fun t => ?_
    refine Fin.cases ?_ (fun l => ?_) t
    · simp
    · simp only [Fin.cons_succ]
      split_ifs <;> simp
  have hval : ∀ (m : ℤ) (q : ℚ) (S : Finset (Fin d)), q = m →
      MvPolynomial.eval
          (Fin.cons q fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) P =
        ((@eulerCharacteristic k _ Z (i ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun t => (Scheme.Modules.pullback i).obj (L t))
            (Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0))
          (isCoherent_twistedSheafUnitPullback k f i L
            (Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0)) : ℤ) : ℚ) := by
    rintro m _ S rfl
    have h := hP (Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0)
    rwa [hcast m S] at h
  have hZ : ((intersectionNumber k f i (d + 1) hd L : ℤ) : ℚ) =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) :=
    intersectionNumber_eq_coeff k f i (d + 1) hd L P hP hPdeg
  have hshift := MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one P hPdeg 0
  have hmain : ((intersectionNumber k f i (d + 1) hd L : ℤ) : ℚ) =
      ((intersectionNumber k f j d hdW (fun t : Fin d => L t.succ) : ℤ) : ℚ) := by
    rw [hZ, ← hshift,
      intersectionNumber_eq_sum_eulerCharacteristic k f j d hdW fun t : Fin d => L t.succ]
    push_cast
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← hdiff S, hval 0 0 S (by norm_num), hval (-1) (0 - 1) S (by norm_num)]
    push_cast
    ring
  exact Int.cast_injective hmain

/-- **The numerical content of [Stacks, Tag 0BEU], with the interpolating polynomial supplied by
[Stacks, Tag 02O6].**  In the situation of
`AlgebraicGeometry.intersectionNumber_eq_of_sub_eulerCharacteristic_eq`, the polynomial `P` of
[Stacks, Tag 0BEM] is produced from finite-dimensionality over `k` of the cohomology of a
coherent module on `Z`, by
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology`, which
reduces Tag 0BEM to that one statement.  So the hypotheses here are exactly Tag 02O6 for `Z`
and the first-difference relation `hdiff` that the twisted divisor sequence supplies.

The degree bound comes from the dimension of `Z`: the support of `𝒪_Z` is a subspace of `Z`, so
its dimension is at most `topologicalKrullDim Z`, which `hd` bounds by `d + 1`.  The zero
polynomial, which is the other alternative Tag 0BEM allows, has total degree `0`.

**No `@[stacks 0BEU]` attribute is attached**: `hfin` is Tag 02O6 and `hdiff` is the twisted
divisor sequence, neither of which is part of the tag's data, and the sequence is not constructed
here.  Both are discharged in
`StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersections/DivisorIntersectionProper.lean`,
which is where the attribute sits. -/
public theorem intersectionNumber_eq_of_sub_eulerCharacteristic_eq_of_finiteDimensional
    (k : Type u) [Field k] {X Z W : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : W ⟶ X) [IsClosedImmersion j] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (hdW : topologicalKrullDim W ≤ d)
    (L : Fin (d + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)]
    (hfin : ∀ G : Z.Modules, _root_.SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k (i ≫ f) G m))
    (hdiff : ∀ S : Finset (Fin d),
      (@eulerCharacteristic k _ Z (i ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun t => (Scheme.Modules.pullback i).obj (L t))
            (Fin.cons 0 fun t => if t ∈ S then 1 else 0))
          (isCoherent_twistedSheafUnitPullback k f i L
            (Fin.cons 0 fun t => if t ∈ S then 1 else 0)) : ℤ) -
        (@eulerCharacteristic k _ Z (i ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun t => (Scheme.Modules.pullback i).obj (L t))
            (Fin.cons (-1) fun t => if t ∈ S then 1 else 0))
          (isCoherent_twistedSheafUnitPullback k f i L
            (Fin.cons (-1) fun t => if t ∈ S then 1 else 0)) : ℤ) =
      (@eulerCharacteristic k _ W (j ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit W.ringCatSheaf)
          (fun t : Fin d => (Scheme.Modules.pullback j).obj (L t.succ))
          (fun t => if t ∈ S then 1 else 0))
        (isCoherent_twistedSheafUnitPullback k f j (fun t : Fin d => L t.succ)
          fun t => if t ∈ S then 1 else 0) : ℤ)) :
    intersectionNumber k f i (d + 1) hd L =
      intersectionNumber k f j d hdW fun t : Fin d => L t.succ := by
  have hunit : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  obtain ⟨P, hdeg, hP⟩ :=
    exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology k (i ≫ f)
      (fun t => (Scheme.Modules.pullback i).obj (L t)) hfin
      (SheafOfModules.unit Z.ringCatSheaf) hunit
  refine intersectionNumber_eq_of_sub_eulerCharacteristic_eq k f i j d hd hdW L P hP ?_ hdiff
  rcases hdeg with h | h
  · rw [h]
    simp
  · have hsupp : topologicalKrullDim
        (_root_.SheafOfModules.supp (SheafOfModules.unit Z.ringCatSheaf)) ≤ (d + 1 : ℕ) :=
      le_trans (topologicalKrullDim_subspace_le _ _) hd
    exact_mod_cast le_trans h hsupp

end AlgebraicGeometry

end
