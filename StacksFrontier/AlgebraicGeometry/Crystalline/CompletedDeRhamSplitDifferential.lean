module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionDeRham

/-!
# Splitting the differential of `M ⊗^∧_D Ω^*` into a relative and a base part

`Crystalline.CompletedDeRham.differential` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionDeRham.lean` is the differential

`D (m ⊗ ω) = ∇ m ∧ ω + m ⊗ d ω`

of the complex `M ⊗^∧_D Ω^*` of a module `M` with a completed connection `∇` over `D` and a graded
family of forms `Ω^*` with a de Rham differential `d` satisfying the Leibniz rule.  In the proof of
[Stacks, Lemma 60.21.2, Tag 07LD] that complex is taken for the forms of the *larger* ring
`D' = B⟨x_w⟩^∧`, whose de Rham differential splits into the part differentiating the variables and
the part differentiating the coefficients,

`d = d_{D'/D} + d_base`,

and correspondingly the differential of `M ⊗̂_D Ω^*_{D'}` splits as

`D = D_rel + D_base`,  `D_rel = 1_M ⊗ d_{D'/D}`,  `D_base (m ⊗ ω) = ∇ m ∧ ω + m ⊗ d_base ω`.

This module proves that splitting and the three identities `D_rel² = 0`, `D_base² = 0` and
`D_rel D_base + D_base D_rel = 0` that make the two parts the two differentials of a double
complex.

## The hypothesis on the relative part is `D`-linearity

`d_{D'/D}` is carried here as a **`D`-linear** map `drel` of the forms, while the base part and the
total differential are merely additive.  That is the mathematical content of "relative": the
relative differential kills the coefficients, `d_{D'/D} f = 0` for `f ∈ D`, so its Leibniz rule
degenerates to `D`-linearity, and therefore `1_M ⊗ d_{D'/D}` is defined on the tensor product over
`D` and is the `AdicCompletion.map` of a `D`-linear map.  The total differential is not, and the
base part is not: each moves a scalar across the tensor sign, which is exactly
`Crystalline.CompletedDeRham.IsGradedLeibniz`.  This is also why the relative homotopy of
`Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_identity` tensors up with `M`
while the full one does not.

Only the splitting itself is assumed about the three differentials of the forms: the Leibniz rule
for the base part is a *consequence*
(`Crystalline.CompletedDeRham.isGradedLeibniz_base_of_split`), since the relative part is linear
and absorbs none of the exact one-form.

## Which identities are proved and which are carried

`D² = 0` is not a theorem of this library — it is the vanishing of the curvature of the completed
connection, carried as `Crystalline.CompletedDeRham.IsSquareZero`, and without it there is no
complex at all.  Given it, the three identities above are not independent: `D²` is the sum of the
three, so any two of them give the third.  The two taken as given here are

* `D² = 0`, the library's own `IsSquareZero` for the total differential — the hypothesis
  `Crystalline.CompletedDeRham.complex` already consumes, so it is available wherever the complex
  is;
* `D_base² = 0`, the same `IsSquareZero` for the base part — the square-zero of the base-direction
  differential, which is again a curvature statement about `∇` and so cannot be derived here;

and the two proved are

* `D_rel² = 0`, from `d_{D'/D}² = 0` alone, with no hypothesis about `M` or `∇`: the relative
  differential being `D`-linear, `D_rel` is the completion of `1_M ⊗ d_{D'/D}` and functoriality
  does the whole job;
* **`D_rel D_base + D_base D_rel = 0`**, the cross-term identity, which is what the perturbation
  argument of [Stacks, Lemma 60.21.2, Tag 07LD] needs and which nothing else in the library
  supplies.

The converse reading is available as
`Crystalline.CompletedDeRham.isSquareZero_base_of_cross`, so a consumer holding the cross-term
identity instead of `D_base² = 0` can start from that end.

**On the sign.**  No sign convention is chosen anywhere below, and none has to be: the cross term
comes out as the *anticommutator* `D_rel D_base + D_base D_rel`, with a plus, because it is what
`D² = 0` leaves once the two squares are removed.  A relative sign between the two parts would
appear only if `D_rel` or `D_base` were redefined with one, and neither is: both are the library's
existing differentials, taken at the two parts of `d`.

## What is deliberately not claimed

* **No bigraded decomposition is used.**  That `D_rel` raises the number of variable
  differentials and `D_base` the number of coefficient differentials is a statement about the
  bidegree decomposition, proved separately in
  `StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/BidegreeFiltration.lean`; nothing here
  refers to it, and in particular the three identities are *not* obtained from `D² = 0` by
  comparing bidegrees, which would need that decomposition carried as data.
* **`Ω^*` is the carried graded family**, as in `CompletedConnectionDeRham`, and is not identified
  with the completed divided power forms of any particular ring; the splitting of its differential
  is data supplied by whoever applies this.
* **Neither part is a complex on its own in the statement.**  `D_rel² = 0` and `D_base² = 0` are
  identities of additive maps; no `CochainComplex` is assembled from them here.

## Main definitions

* `Crystalline.CompletedDeRham.relDifferential` — **`D_rel = 1_M ⊗ d_{D'/D}`**, the `D`-linear
  relative part of the differential of `M ⊗^∧_D Ω^*`.

## Main results

* `Crystalline.CompletedDeRham.isGradedLeibniz_base_of_split` — the base part inherits the Leibniz
  rule from the total differential, the relative part being linear.
* `Crystalline.CompletedDeRham.differential_eq_relDifferential_add` — **`D = D_rel + D_base`.**
* `Crystalline.CompletedDeRham.relDifferential_relDifferential` — **`D_rel² = 0`**, from
  `d_{D'/D}² = 0`.
* `Crystalline.CompletedDeRham.relDifferential_baseDifferential_add_eq_zero` — **the cross-term
  identity `D_rel D_base + D_base D_rel = 0`.**
* `Crystalline.CompletedDeRham.isSquareZero_base_of_cross` — the cross-term identity and
  `D_rel² = 0` give `D_base² = 0`, which is the other way round the same reduction.

## References

* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u v w

namespace Crystalline

namespace CompletedDeRham

/-! ### The relative part of the differential -/

section Relative

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (drel : ∀ i, Om i →ₗ[D] Om (i + 1)) (M : Type w) [AddCommGroup M]
  [Module D M]

/-- **The relative part `D_rel = 1_M ⊗ d_{D'/D}` of the differential of `M ⊗^∧_D Ω^*`**: the
completion of `1_M ⊗ d_{D'/D}`, where the relative differential of the forms is carried as a
`D`-linear map.

Unlike `Crystalline.CompletedDeRham.differential` this *is* an `AdicCompletion.map`, and is
`D`-linear: the relative differential kills the coefficients, so its Leibniz rule degenerates to
`D`-linearity and no connection enters. -/
public def relDifferential (i : ℕ) :
    CompletedTensor p D (Om i) M →ₗ[D] CompletedTensor p D (Om (i + 1)) M :=
  (AdicCompletion.map (pAdicIdeal (A := D) p)
    (LinearMap.lTensor M (drel i))).restrictScalars D

/-- The relative part at the level `pⁿ`, which is how it is compared with the differential of the
complex: both are determined by their values at the levels. -/
public theorem relDifferential_val (i n : ℕ) (x : CompletedTensor p D (Om i) M) :
    (relDifferential p D Om drel M i x).val n =
      (LinearMap.lTensor M (drel i)).reduceModIdeal ((pAdicIdeal (A := D) p) ^ n) (x.val n) :=
  rfl

/-- **`D_rel (m ⊗ ω) = m ⊗ d_{D'/D} ω`**: the relative part leaves the coefficient alone. -/
public theorem relDifferential_of_tmul (i : ℕ) (m : M) (ω : Om i) :
    relDifferential p D Om drel M i (toCompletedTensor p D (Om i) M (m ⊗ₜ[D] ω)) =
      toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] drel i ω) := by
  show AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M (drel i))
      (AdicCompletion.of (pAdicIdeal (A := D) p) (M ⊗[D] Om i) (m ⊗ₜ[D] ω)) = _
  rw [AdicCompletion.map_of, LinearMap.lTensor_tmul]

/-- **`D_rel² = 0`**, from `d_{D'/D}² = 0` and nothing else: the relative part is the completion of
`1_M ⊗ d_{D'/D}`, and both the completion and `1_M ⊗ −` are functorial, so the vanishing is
inherited from the forms.  No hypothesis about `M`, about `∇` or about the curvature appears. -/
public theorem relDifferential_relDifferential
    (hdrel : ∀ i : ℕ, (drel (i + 1)).comp (drel i) = 0) (i : ℕ)
    (x : CompletedTensor p D (Om i) M) :
    relDifferential p D Om drel M (i + 1) (relDifferential p D Om drel M i x) = 0 := by
  show AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M (drel (i + 1)))
      (AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M (drel i)) x) = 0
  rw [AdicCompletion.map_comp_apply, ← LinearMap.lTensor_comp, hdrel i, LinearMap.lTensor_zero,
    AdicCompletion.map_zero]
  rfl

/-- `D_rel² = 0` as an identity of additive maps. -/
public theorem relDifferential_comp_relDifferential
    (hdrel : ∀ i : ℕ, (drel (i + 1)).comp (drel i) = 0) (i : ℕ) :
    (relDifferential p D Om drel M (i + 1)).toAddMonoidHom.comp
        (relDifferential p D Om drel M i).toAddMonoidHom = 0 :=
  AddMonoidHom.ext fun x ↦ relDifferential_relDifferential p D Om drel M hdrel i x

end Relative

/-! ### The splitting of the differential -/

section Split

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (drel : ∀ i, Om i →ₗ[D] Om (i + 1))
  (dbase : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M] [Module D M]
  (nabla : CompletedConnection p D (Om 1) dmap M)

/-- **The base part of the de Rham differential of the forms inherits the Leibniz rule.**  The
relative part is `D`-linear, so it absorbs none of the exact one-form `d f`, and the whole of it
stays with the base part.  This is why only the splitting of the differential has to be assumed and
not the Leibniz rule for each piece. -/
public theorem isGradedLeibniz_base_of_split
    (hleib : IsGradedLeibniz D Om wedge deRham dmap)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω) :
    IsGradedLeibniz D Om wedge dbase dmap := by
  intro i f ω
  have h := hleib i f ω
  rw [hsplit i (f • ω), hsplit i ω, map_smul, smul_add] at h
  exact add_left_cancel (a := f • drel i ω) (by rw [h]; abel)

/-- **The de Rham formula splits on the uncompleted tensor product**:
`∇ (m ⊗ ω) = m ⊗ d_{D'/D} ω + (∇ m ∧ ω + m ⊗ d_base ω)`.  Both sides are additive, so it is enough
to check it on pure tensors, where it is the splitting of `d` and the additivity of `⊗`. -/
public theorem rawDifferential_eq_lTensor_add
    (hleib : IsGradedLeibniz D Om wedge deRham dmap)
    (hleibBase : IsGradedLeibniz D Om wedge dbase dmap)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω) (i : ℕ)
    (y : M ⊗[D] Om i) :
    rawDifferential p D Om wedge deRham M nabla hleib i y =
      toCompletedTensor p D (Om (i + 1)) M (LinearMap.lTensor M (drel i) y) +
        rawDifferential p D Om wedge dbase M nabla hleibBase i y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero, add_zero]
  | tmul m ω =>
    rw [rawDifferential_tmul, rawDifferential_tmul, LinearMap.lTensor_tmul, hsplit i ω,
      TensorProduct.tmul_add, map_add]
    abel
  | add y z hy hz =>
    simp only [map_add]
    rw [hy, hz]
    abel

/-- **`D = D_rel + D_base`**, read as an identity of additive maps on the completed tensor
product.

Both sides are determined by their values at the levels `pⁿ`
(`Crystalline.CompletedDeRham.differential_eq_of_val`), and at each level the identity is the
splitting of the de Rham formula on the uncompleted tensor product,
`Crystalline.CompletedDeRham.rawDifferential_eq_lTensor_add`. -/
public theorem relDifferential_add_differential_eq
    (hleib : IsGradedLeibniz D Om wedge deRham dmap)
    (hleibBase : IsGradedLeibniz D Om wedge dbase dmap)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω) (i : ℕ) :
    (relDifferential p D Om drel M i).toAddMonoidHom +
        differential p D Om wedge dbase M nabla hleibBase i =
      differential p D Om wedge deRham M nabla hleib i := by
  refine differential_eq_of_val p D Om wedge deRham M nabla hleib i _ ?_
  intro n x y hxy
  have hrel : (relDifferential p D Om drel M i x).val n =
      (toCompletedTensor p D (Om (i + 1)) M (LinearMap.lTensor M (drel i) y)).val n := by
    rw [relDifferential_val, hxy]
    rfl
  have hbase : (differential p D Om wedge dbase M nabla hleibBase i x).val n =
      (rawDifferential p D Om wedge dbase M nabla hleibBase i y).val n := by
    rw [differential_val, hxy, levelDifferential_mk]
  show (relDifferential p D Om drel M i x +
      differential p D Om wedge dbase M nabla hleibBase i x).val n = _
  rw [AdicCompletion.val_add_apply, hrel, hbase,
    rawDifferential_eq_lTensor_add p D Om wedge deRham drel dbase M nabla hleib hleibBase hsplit
      i y, AdicCompletion.val_add_apply]

/-- **`D (x) = D_rel (x) + D_base (x)`**, read on an element. -/
public theorem differential_eq_relDifferential_add
    (hleib : IsGradedLeibniz D Om wedge deRham dmap)
    (hleibBase : IsGradedLeibniz D Om wedge dbase dmap)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω) (i : ℕ)
    (x : CompletedTensor p D (Om i) M) :
    differential p D Om wedge deRham M nabla hleib i x =
      relDifferential p D Om drel M i x +
        differential p D Om wedge dbase M nabla hleibBase i x :=
  (DFunLike.congr_fun (relDifferential_add_differential_eq p D Om wedge deRham drel dbase M nabla
    hleib hleibBase hsplit i) x).symm

/-! ### The cross-term identity -/

/-- **The expansion of `D²` into the two squares and the cross term.**  With `D = D_rel + D_base`
the square of the differential is

`D² = D_rel² + (D_rel D_base + D_base D_rel) + D_base²`,

which is the whole algebra behind the three identities: any two of them give the third. -/
public theorem differential_differential_eq_add
    (hleib : IsGradedLeibniz D Om wedge deRham dmap)
    (hleibBase : IsGradedLeibniz D Om wedge dbase dmap)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω) (i : ℕ)
    (x : CompletedTensor p D (Om i) M) :
    differential p D Om wedge deRham M nabla hleib (i + 1)
        (differential p D Om wedge deRham M nabla hleib i x) =
      relDifferential p D Om drel M (i + 1) (relDifferential p D Om drel M i x) +
          (relDifferential p D Om drel M (i + 1)
              (differential p D Om wedge dbase M nabla hleibBase i x) +
            differential p D Om wedge dbase M nabla hleibBase (i + 1)
              (relDifferential p D Om drel M i x)) +
        differential p D Om wedge dbase M nabla hleibBase (i + 1)
          (differential p D Om wedge dbase M nabla hleibBase i x) := by
  rw [differential_eq_relDifferential_add p D Om wedge deRham drel dbase M nabla hleib hleibBase
      hsplit i x,
    map_add (differential p D Om wedge deRham M nabla hleib (i + 1)),
    differential_eq_relDifferential_add p D Om wedge deRham drel dbase M nabla hleib hleibBase
      hsplit (i + 1) (relDifferential p D Om drel M i x),
    differential_eq_relDifferential_add p D Om wedge deRham drel dbase M nabla hleib hleibBase
      hsplit (i + 1) (differential p D Om wedge dbase M nabla hleibBase i x)]
  abel

/-- From `D² = 0` and `D_rel² = 0`, the cross term plus `D_base²` vanishes. -/
private theorem cross_add_base_sq_eq_zero
    (hleib : IsGradedLeibniz D Om wedge deRham dmap)
    (hleibBase : IsGradedLeibniz D Om wedge dbase dmap)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω)
    (hdrel : ∀ i : ℕ, (drel (i + 1)).comp (drel i) = 0)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib) (i : ℕ)
    (x : CompletedTensor p D (Om i) M) :
    (relDifferential p D Om drel M (i + 1)
            (differential p D Om wedge dbase M nabla hleibBase i x) +
          differential p D Om wedge dbase M nabla hleibBase (i + 1)
            (relDifferential p D Om drel M i x)) +
        differential p D Om wedge dbase M nabla hleibBase (i + 1)
          (differential p D Om wedge dbase M nabla hleibBase i x) = 0 := by
  have hexp := differential_differential_eq_add p D Om wedge deRham drel dbase M nabla hleib
    hleibBase hsplit i x
  erw [DFunLike.congr_fun (hsq i) x] at hexp
  rw [relDifferential_relDifferential p D Om drel M hdrel i x, zero_add] at hexp
  exact hexp.symm

/-- **The cross-term identity `D_rel D_base + D_base D_rel = 0`.**

This is the identity the perturbation argument of [Stacks, Lemma 60.21.2, Tag 07LD] runs on, and
it is a consequence of the two square-zero statements it is given rather than a new input: by
`Crystalline.CompletedDeRham.differential_differential_eq_add` the square `D²` is the sum of the
two squares and the cross term, so `D² = 0`, `D_rel² = 0` and `D_base² = 0` force the cross term
to vanish.  `D_rel² = 0` is proved from `d_{D'/D}² = 0` by
`Crystalline.CompletedDeRham.relDifferential_relDifferential`, so of the three hypotheses only
the two curvature statements are carried.

No sign convention is involved: the plus sign is what the expansion of `D²` leaves. -/
public theorem relDifferential_baseDifferential_add_eq_zero
    (hleib : IsGradedLeibniz D Om wedge deRham dmap)
    (hleibBase : IsGradedLeibniz D Om wedge dbase dmap)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω)
    (hdrel : ∀ i : ℕ, (drel (i + 1)).comp (drel i) = 0)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hsqbase : IsSquareZero p D Om wedge dbase M nabla hleibBase) (i : ℕ)
    (x : CompletedTensor p D (Om i) M) :
    relDifferential p D Om drel M (i + 1)
          (differential p D Om wedge dbase M nabla hleibBase i x) +
        differential p D Om wedge dbase M nabla hleibBase (i + 1)
          (relDifferential p D Om drel M i x) = 0 := by
  have h := cross_add_base_sq_eq_zero p D Om wedge deRham drel dbase M nabla hleib hleibBase
    hsplit hdrel hsq i x
  erw [DFunLike.congr_fun (hsqbase i) x, add_zero] at h
  exact h

/-- **The other way round the same reduction**: given the cross-term identity and `D_rel² = 0`, the
square-zero of the base part follows from that of the total differential.  A consumer holding the
cross-term identity rather than `D_base² = 0` can start from here; see the module docstring on why
any two of the three identities give the third. -/
public theorem isSquareZero_base_of_cross
    (hleib : IsGradedLeibniz D Om wedge deRham dmap)
    (hleibBase : IsGradedLeibniz D Om wedge dbase dmap)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω)
    (hdrel : ∀ i : ℕ, (drel (i + 1)).comp (drel i) = 0)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hcross : ∀ (i : ℕ) (x : CompletedTensor p D (Om i) M),
      relDifferential p D Om drel M (i + 1)
            (differential p D Om wedge dbase M nabla hleibBase i x) +
          differential p D Om wedge dbase M nabla hleibBase (i + 1)
            (relDifferential p D Om drel M i x) = 0) :
    IsSquareZero p D Om wedge dbase M nabla hleibBase := by
  intro i
  refine AddMonoidHom.ext fun x ↦ ?_
  show differential p D Om wedge dbase M nabla hleibBase (i + 1)
    (differential p D Om wedge dbase M nabla hleibBase i x) = 0
  have h := cross_add_base_sq_eq_zero p D Om wedge deRham drel dbase M nabla hleib hleibBase
    hsplit hdrel hsq i x
  rwa [hcross i x, zero_add] at h

end Split

end CompletedDeRham

end Crystalline

end
