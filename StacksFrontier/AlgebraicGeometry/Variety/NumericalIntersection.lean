module

public import StacksFrontier.Algebra.Polynomial.Numerical
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksCore.Tactic.StacksAttribute

/-!
# Numerical intersection numbers on a proper scheme over a field

Let `k` be a field, let `X` be a proper scheme over `k`, let `i : Z ⟶ X` be a closed subscheme
of dimension at most `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.  The intersection
number `(𝓛_1 ⋯ 𝓛_d · Z)` is the coefficient of `n_1 ⋯ n_d` in the numerical polynomial

`χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_d^{⊗ n_d}|_Z)`.

The coefficient of the squarefree monomial `n_1 ⋯ n_d` in a polynomial of total degree at most
`d` is the `d`-fold mixed finite difference `∑_{T ⊆ {1, …, d}} (-1)^{d - |T|} P(1_T)` of its
values at the indicator functions `1_T`, so the intersection number is *defined* here by that
alternating sum of Euler characteristics.  It is therefore an honest integer, with no choice of
data from an existence statement and no appeal to polynomiality, and the source's own
description is recovered as a theorem.

Specialising to a single invertible module repeated `d = dim Z` times gives the degree
`deg_𝓛(Z)` of a closed subscheme with respect to an ample module, and in dimension one both
numbers are the degree of `𝓛|_Z` in the sense of the previous section.

## Main definitions

* `AlgebraicGeometry.intersectionNumber`: **Stacks 0BEP**, the intersection number
  `(𝓛_1 ⋯ 𝓛_d · Z)`, as the `d`-fold mixed finite difference of
  `n ↦ χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_d^{⊗ n_d}|_Z)`.
* `AlgebraicGeometry.selfIntersectionNumber`: **Stacks 0BEP**, the special case `(𝓛^d · Z)` of
  a single invertible module repeated `d` times.
* `AlgebraicGeometry.degreeWithRespectTo`: **Stacks 0BEW**, the degree `deg_𝓛(Z)` of a closed
  subscheme with respect to an ample invertible module, namely `(𝓛^d · Z)` for `d = dim Z`.

## Main results

* `AlgebraicGeometry.intersectionNumber_eq_sum`: the defining alternating sum.
* `AlgebraicGeometry.intersectionNumber_eq_sum_eulerCharacteristic`: the same sum written with
  `AlgebraicGeometry.eulerCharacteristic`, which is the source's displayed formula.  The
  coherence of each twist is not a hypothesis: it is proved, in
  `AlgebraicGeometry.isCoherent_twistedSheafUnitPullback`.
* `AlgebraicGeometry.intersectionNumber_eq_coeff`: **Stacks 0BEP, the source's own description
  of the intersection number.**  Whenever a rational polynomial of total degree at most `d`
  takes the Euler characteristics of the twists as its values at integral tuples, the
  intersection number is its coefficient of `n_1 ⋯ n_d`.  There is no hypothesis beyond those
  two, and in particular the existence of such a polynomial — which is Stacks 0BEM — is not
  assumed.
* `AlgebraicGeometry.intersectionNumber_zero`: the degenerate case `d = 0`, where the empty
  intersection number is `χ(Z, 𝒪_Z)`.
* `AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree`: **Stacks 0BEY**,
  `(𝓛 · Z) = deg(𝓛|_Z)` for `Z` of dimension at most one.
* `AlgebraicGeometry.degreeWithRespectTo_eq_invertibleCurveDegree`: **Stacks 0BEY, the ample
  case**, `deg_𝓛(Z) = deg(𝓛|_Z)`.

## Implementation notes

**Why the finite difference is the definition.**  Evaluating a monomial `n^a` at the indicator
function of `T ⊆ {1, …, d}` gives `1` precisely when the support of `a` is contained in `T`, and
`0` in every other case, so the alternating sum `∑_T (-1)^{d - |T|} P(1_T)` is the sum of the
coefficients of the `a` of full support; a total degree of at most `d` forces such an `a` to be
`(1, …, 1)`.  That monomial computation is pure algebra and is
`MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one`.  The resulting formula uses only
finitely many values of the function, so it makes sense before polynomiality is known, and it is
manifestly integral, which is why the intersection number is `ℤ`-valued here rather than
`ℚ`-valued — as Stacks 0BEQ says it must be.

Defining the number instead as the coefficient of a polynomial chosen from Stacks 0BEM would
make the *definition* conditional on that tag, which is not proved in this library; worse, every
route to it passes through the finite-dimensionality of coherent cohomology (Stacks 02O6), which
is not proved either.  Nothing below depends on either.

**Why the Euler characteristics are taken on `Z`.**  The source gives the numerical polynomial
in two shapes, `χ(X, i_*𝒪_Z ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯)` and `χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯|_Z)`, and asserts
their equality.  The second is used here.  It needs only the pullback of modules along `i` and
invariance of the Euler characteristic under isomorphism, whereas the first would additionally
need the comparison of cohomology along a closed immersion (Stacks 089W) before it could be
compared with the degree of a module on a curve, which is itself defined on `Z`.

**The definition carries no coherence hypothesis.**  Like `AlgebraicGeometry.curveDegree`, the
alternating sum of dimensions of cohomology groups is written out in the body rather than
through `AlgebraicGeometry.eulerCharacteristic`, so no coherence instance appears in the
signature and the definition is total.  Coherence is nonetheless available — the structure sheaf
of a scheme proper over a field is coherent and every twist of a coherent module by invertible
modules is coherent — and `intersectionNumber_eq_sum_eulerCharacteristic` is the comparison,
which holds by `rfl`.

**The dimension hypothesis.**  The source states the definition for a closed subscheme of
dimension `d`; the hypothesis carried here is `topologicalKrullDim Z ≤ d`, which is the weaker
one and therefore defines the number on more data.  The weaker form is forced by Stacks 0BEY,
which uses `(𝓛 · Z)` — that is, `d = 1` — for a closed subscheme of dimension *at most* one.  It
is also the shape `AlgebraicGeometry.invertibleCurveDegree` already uses for Stacks 0AYR.  The
hypothesis is not used in the body, which is a finite sum of Euler characteristics for every
family of `d` invertible modules; it is kept, as are properness and the closed immersion, so
that the entity defined is the one of the tag.

**The dimension convention in `degreeWithRespectTo`.**  Stacks 0BEW sets `deg_𝓛(Z) = (𝓛^d · Z)`
with `d = dim(Z)`, which presupposes that `dim(Z)` is a natural number.
`topologicalKrullDim Z` lives in `WithBot ℕ∞`, so the dimension is passed as a natural number
`d` together with the hypothesis `topologicalKrullDim Z = d`.  Nothing is then silently wrong in
the two cases where the source's `d` does not exist: an empty `Z` has dimension `⊥` and an
infinite-dimensional one has dimension `⊤`, and neither is `(d : WithBot ℕ∞)` for any `d : ℕ`,
so the degree is simply not defined for them.  Reducing `⊥` and `⊤` to `0` instead — as
`((topologicalKrullDim Z).unbotD 0).toNat` does — would silently define `deg_𝓛` of an empty or
of an infinite-dimensional subscheme to be `χ(Z, 𝒪_Z)`, which is not the source's number.
Since `d` is determined by the hypothesis, the degree does not depend on which `d` is supplied.

**The ample case of Stacks 0BEY needs dimension exactly one.**  The source's second conclusion,
`deg_𝓛(Z) = deg(𝓛|_Z)` for `Z` of dimension at most one, is false as stated when `Z` is
nonempty of dimension zero: there `deg_𝓛(Z) = (𝓛^0 · Z) = χ(Z, 𝒪_Z) = dim_k Γ(Z, 𝒪_Z) ≠ 0`,
while `deg(𝓛|_Z) = χ(Z, 𝓛|_Z) - χ(Z, 𝒪_Z) = 0`.  The degenerate value is
`AlgebraicGeometry.intersectionNumber_zero`, so the discrepancy can be checked rather than taken
on trust.  `degreeWithRespectTo_eq_invertibleCurveDegree` is therefore stated at
`topologicalKrullDim Z = 1`, which is where `deg_𝓛(Z)` is `(𝓛 · Z)`.  The first conclusion,
`(𝓛 · Z) = deg(𝓛|_Z)`, is the one with content and it keeps the source's `≤ 1`
(`intersectionNumber_one_eq_invertibleCurveDegree`); it is in fact true for every `Z`.

**Ampleness.**  `AlgebraicGeometry.Scheme.Modules.IsAmple` is the spelling of Stacks 01PS used,
rather than `Stacks.Ample.IsAmple`: it is the one carrying the repository's ampleness theory
(`StacksFrontier/AlgebraicGeometry/Ample/`), and it is the one the previous section already names,
in the implementation notes of `AlgebraicGeometry.invertibleCurveDegree`.  Both accept exactly
the invertibility class used here, so the choice costs no bridging either way.  The hypothesis
is inert in `degreeWithRespectTo` — the source needs it only so that `deg_𝓛` is a degree — and
is carried because it is the source's.

**Invertibility.**  `AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2`
is the class taken by `AlgebraicGeometry.twistedSheaf` and by
`AlgebraicGeometry.invertibleCurveDegree`, so it is the one used.  Its stability under pullback
is Stacks 0B8L, available as `Stacks.InvertiblePullback.isInvertibleModule_pullback` at the
`RingedSpaceModuleAdjunction.modulePullback` spelling of the pullback;
`AlgebraicGeometry.isInvertible_pullbackObj` below re-registers it at the
`AlgebraicGeometry.Scheme.Modules.pullback` spelling, which is the one that reads as `𝓛|_Z`.

## References

* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEQ](https://stacks.math.columbia.edu/tag/0BEQ)
* [Stacks Project, Tag 0BEW](https://stacks.math.columbia.edu/tag/0BEW)
* [Stacks Project, Tag 0BEY](https://stacks.math.columbia.edu/tag/0BEY)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules.Invertible

/-! ### The restriction of an invertible module to a subscheme -/

/-- **The pullback of an invertible module along a morphism of schemes is invertible**, at the
`AlgebraicGeometry.Scheme.Modules.pullback` spelling of the pullback.  This is Stacks 0B8L,
`Stacks.InvertiblePullback.isInvertibleModule_pullback`, which proves it for the definitionally
equal `RingedSpaceModuleAdjunction.modulePullback` spelling; the tag is carried there and not
repeated here. -/
instance isInvertible_pullbackObj {X Z : Scheme.{u}} (i : Z ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj L) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback i L

/-! ### The intersection number -/

/-- **Stacks 0BEP.** The intersection number `(𝓛_1 ⋯ 𝓛_d · Z)` of `d` invertible
`𝒪_X`-modules against a closed subscheme `i : Z ⟶ X` of dimension at most `d` of a proper
scheme `X` over a field `k`: the coefficient of `n_1 ⋯ n_d` in the numerical polynomial
`χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_d^{⊗ n_d}|_Z)`, computed as the `d`-fold mixed finite difference

`∑_{T ⊆ {1, …, d}} (-1)^{d - |T|} χ(Z, ⨂_{j ∈ T} 𝓛_j|_Z)`

of that function.  This is an honest integer, which is Stacks 0BEQ: only finitely many values of
the function are used, so neither polynomiality nor a choice of representing polynomial enters.
The Euler characteristic is written out as the alternating sum of the dimensions of the
cohomology groups, so that no coherence hypothesis is needed to state the definition;
`AlgebraicGeometry.intersectionNumber_eq_sum_eulerCharacteristic` is the comparison with
`AlgebraicGeometry.eulerCharacteristic`. -/
@[stacks 0BEP, sga "6 XIII 2.1", sga "6 X 4.4" "defn of (L_1..L_d;F)"]
public noncomputable def intersectionNumber (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (_hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] : ℤ :=
  ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank k (cohomologyOverField k (i ≫ f)
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun j => (Scheme.Modules.pullback i).obj (L j))
          (fun j => if j ∈ T then 1 else 0)) n) : ℤ)

/-- The defining alternating sum of the intersection number. -/
public theorem intersectionNumber_eq_sum (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f i d hd L =
      ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          (Module.finrank k (cohomologyOverField k (i ≫ f)
            (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
              (fun j => (Scheme.Modules.pullback i).obj (L j))
              (fun j => if j ∈ T then 1 else 0)) n) : ℤ) := rfl

/-- **Every twist of `𝒪_Z` by restrictions of invertible `𝒪_X`-modules is coherent.** The
structure sheaf of `Z` is coherent because `Z` is proper over the field `k`
(`Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit`), and
`AlgebraicGeometry.twistedSheaf_isCoherent` propagates coherence through the twists.  No
hypothesis is needed. -/
public theorem isCoherent_twistedSheafUnitPullback (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] (n : Fin d → ℤ) :
    (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
      (fun j => (Scheme.Modules.pullback i).obj (L j)) n).IsCoherent :=
  have : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  twistedSheaf_isCoherent _ _ n

/-- **The source's displayed formula for the intersection number**: the `d`-fold mixed finite
difference of the Euler characteristics `χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_d^{⊗ n_d}|_Z)` at the
indicator functions.  The coherence that `AlgebraicGeometry.eulerCharacteristic` demands is
supplied by `AlgebraicGeometry.isCoherent_twistedSheafUnitPullback` rather than assumed, so this
is unconditional. -/
public theorem intersectionNumber_eq_sum_eulerCharacteristic (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f i d hd L =
      ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        @eulerCharacteristic k _ Z (i ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun j => (Scheme.Modules.pullback i).obj (L j))
            (fun j => if j ∈ T then 1 else 0))
          (isCoherent_twistedSheafUnitPullback k f i L fun j => if j ∈ T then 1 else 0) := rfl

/-- **Stacks 0BEP, the coefficient of `n_1 ⋯ n_d`.**  If a rational polynomial `P` in `d`
variables of total degree at most `d` takes the Euler characteristics
`χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_d^{⊗ n_d}|_Z)` as its values at the integral tuples, then the
intersection number `(𝓛_1 ⋯ 𝓛_d · Z)` is the coefficient of `n_1 ⋯ n_d` in `P`.

This is the source's own description of the intersection number.  The existence of such a `P`,
which is Stacks 0BEM, is not assumed: the statement is unconditional in `P`, and the proof is
the monomial computation
`MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one`. -/
@[stacks 0BEP "the coefficient of n_1 ⋯ n_d",
  sga "6 XIII 2.1" "coeff of n_1⋯n_s",
  sga "6 X 4.4" "defn of (L_1..L_d;F)"]
public theorem intersectionNumber_eq_coeff (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (P : MvPolynomial (Fin d) ℚ)
    (hP : ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic k _ Z (i ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun j => (Scheme.Modules.pullback i).obj (L j)) n)
        (isCoherent_twistedSheafUnitPullback k f i L n) : ℤ) : ℚ))
    (hdeg : P.totalDegree ≤ d) :
    ((intersectionNumber k f i d hd L : ℤ) : ℚ) =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  have hval : ∀ T : Finset (Fin d),
      MvPolynomial.eval (fun j => if j ∈ T then (1 : ℚ) else 0) P =
        ((@eulerCharacteristic k _ Z (i ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun j => (Scheme.Modules.pullback i).obj (L j))
            (fun j => if j ∈ T then 1 else 0))
          (isCoherent_twistedSheafUnitPullback k f i L
            fun j => if j ∈ T then 1 else 0) : ℤ) : ℚ) := by
    intro T
    have h := hP fun j => if j ∈ T then (1 : ℤ) else 0
    rw [show (fun j : Fin d => (((if j ∈ T then (1 : ℤ) else 0) : ℤ) : ℚ)) =
        fun j : Fin d => if j ∈ T then (1 : ℚ) else 0 from
      funext fun j => by split_ifs <;> simp] at h
    exact h
  rw [← MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one P hdeg,
    intersectionNumber_eq_sum_eulerCharacteristic]
  push_cast
  exact Finset.sum_congr rfl fun T _ => by rw [hval T]

/-- **The empty intersection number is the Euler characteristic of the structure sheaf**:
`(· Z) = χ(Z, 𝒪_Z)`.  This is the degenerate case `d = 0` of Stacks 0BEP, recorded because it
is what pins down the value of `deg_𝓛(Z)` for a subscheme of dimension zero. -/
public theorem intersectionNumber_zero (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : topologicalKrullDim Z ≤ (0 : ℕ)) (L : Fin 0 → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f i 0 hd L =
      @eulerCharacteristic k _ Z (i ≫ f) inferInstance (SheafOfModules.unit Z.ringCatSheaf)
        (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)) := by
  have huniv : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by decide
  rw [intersectionNumber_eq_sum, huniv, Finset.sum_singleton]
  simp only [Finset.card_empty, Nat.sub_self, pow_zero, one_mul]
  rfl

/-- **Stacks 0BEP, the self-intersection notation `(𝓛^d · Z)`.**  The intersection number of a
single invertible `𝒪_X`-module `𝓛` repeated `d` times against a closed subscheme `i : Z ⟶ X` of
dimension at most `d`. -/
@[stacks 0BEP "the self-intersection notation (L^d · Z)", sga "6 XIII 2.1" "all L_i equal"]
public noncomputable def selfIntersectionNumber (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : ℤ :=
  intersectionNumber k f i d hd fun _ => L

/-- The self-intersection number is the intersection number of the constant family. -/
public theorem selfIntersectionNumber_eq_intersectionNumber (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    selfIntersectionNumber k f i d hd L = intersectionNumber k f i d hd (fun _ => L) := rfl

/-! ### The degree of a closed subscheme with respect to an ample module -/

/-- **Stacks 0BEW.** The degree `deg_𝓛(Z)` of a closed subscheme `i : Z ⟶ X` of a proper scheme
`X` over a field `k` with respect to an ample invertible `𝒪_X`-module `𝓛`: the intersection
number `(𝓛^d · Z)` for `d` the dimension of `Z`.

The dimension is passed as a natural number `d` together with the hypothesis
`topologicalKrullDim Z = d`, which is what makes `d` the source's `dim(Z)`; `d` is therefore
determined by the data and the degree does not depend on which `d` is supplied.  An empty `Z` has
dimension `⊥` and an infinite-dimensional `Z` has dimension `⊤`, neither of which is
`(d : WithBot ℕ∞)` for a natural number `d`, so no value is assigned to them — see the
implementation notes.  Ampleness is not used in the body: the source requires it so that
`deg_𝓛` deserves the name of a degree, and it is carried for that reason. -/
@[stacks 0BEW]
public noncomputable def degreeWithRespectTo (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z = d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (_hample : Scheme.Modules.IsAmple X L) : ℤ :=
  selfIntersectionNumber k f i d hd.le L

/-- The degree with respect to an ample module is the self-intersection number `(𝓛^d · Z)`. -/
public theorem degreeWithRespectTo_eq_selfIntersectionNumber (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z = d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hample : Scheme.Modules.IsAmple X L) :
    degreeWithRespectTo k f i d hd L hample = selfIntersectionNumber k f i d hd.le L := rfl

/-! ### Intersection numbers in dimension one -/

/-- **Stacks 0BEY.** For a closed subscheme `Z ⊂ X` of dimension at most one of a proper scheme
`X` over a field `k` and an invertible `𝒪_X`-module `𝓛`, the intersection number `(𝓛 · Z)` is
the degree `deg(𝓛|_Z)` of Stacks 0AYR.

The source's proof is that `n ↦ χ(Z, 𝓛|_Z^{⊗ n})` has degree one, so its leading coefficient is
the difference of consecutive values.  With the finite difference as the definition that
difference *is* the intersection number: the sum over `Finset (Fin 1)` has the two terms
`-χ(Z, 𝒪_Z)` and `χ(Z, 𝓛|_Z)`, the first twist being the trivial one
(`AlgebraicGeometry.twistedSheafZeroIso`) and the second `𝓛|_Z` itself
(`Stacks.SheafOfModules.Invertible.tensorPowerOneIso` and the left unitor), and
`AlgebraicGeometry.invertibleCurveDegree` is by definition their difference.  Neither
polynomiality nor a degree computation is needed, so the statement keeps the source's `≤ 1`;
it is in fact true for every `Z`. -/
@[stacks 0BEY]
public theorem intersectionNumber_one_eq_invertibleCurveDegree (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hdim : topologicalKrullDim Z ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    intersectionNumber k f i 1 hdim (fun _ => L) =
      invertibleCurveDegree k (i ≫ f) hdim ((Scheme.Modules.pullback i).obj L) := by
  classical
  have e₁ : twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
      (fun _ : Fin 1 => (Scheme.Modules.pullback i).obj L) (fun _ => (1 : ℤ)) ≅
        (Scheme.Modules.pullback i).obj L :=
    tensorProductIso Z.presheaf Z.ringCatSheaf.2 (Iso.refl _)
        (tensorPowerOneIso Z.presheaf Z.ringCatSheaf.2
          ((Scheme.Modules.pullback i).obj L)) ≪≫
      tensorProductLeftUnitor Z.presheaf Z.ringCatSheaf.2
        ((Scheme.Modules.pullback i).obj L)
  have key : ∀ M N : Z.Modules, (M ≅ N) →
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          (Module.finrank k (cohomologyOverField k (i ≫ f) M n) : ℤ)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          (Module.finrank k (cohomologyOverField k (i ≫ f) N n) : ℤ) :=
    fun _ _ e => finsum_congr fun n => by
      rw [finrank_cohomologyOverField_eq_of_iso k (i ≫ f) e n]
  have huniv : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  have hmem : (∅ : Finset (Fin 1)) ∉ ({{0}} : Finset (Finset (Fin 1))) := by decide
  have hzero : (fun j : Fin 1 => if j ∈ (∅ : Finset (Fin 1)) then (1 : ℤ) else 0) = 0 := by
    funext j
    simp
  have hone : (fun j : Fin 1 => if j ∈ ({0} : Finset (Fin 1)) then (1 : ℤ) else 0) =
      fun _ => (1 : ℤ) := by
    funext j
    simp [Subsingleton.elim j 0]
  have hdeg : invertibleCurveDegree k (i ≫ f) hdim ((Scheme.Modules.pullback i).obj L) =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k (i ≫ f)
          ((Scheme.Modules.pullback i).obj L) n) : ℤ)) -
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k (i ≫ f)
          (SheafOfModules.unit Z.ringCatSheaf) n) : ℤ) := rfl
  refine (intersectionNumber_eq_sum k f i 1 hdim fun _ => L).trans ?_
  rw [huniv, Finset.sum_insert hmem, Finset.sum_singleton, hzero, hone,
    key _ _ (twistedSheafZeroIso (SheafOfModules.unit Z.ringCatSheaf)
      (fun _ : Fin 1 => (Scheme.Modules.pullback i).obj L)), key _ _ e₁, hdeg]
  simp only [Finset.card_empty, Finset.card_singleton]
  ring

/-- **Stacks 0BEY, the ample case.** For a closed subscheme `Z ⊂ X` of dimension one of a proper
scheme `X` over a field `k` and an ample invertible `𝒪_X`-module `𝓛`, the degree `deg_𝓛(Z)` of
Stacks 0BEW is the degree `deg(𝓛|_Z)` of Stacks 0AYR.

The source states this for `Z` of dimension at most one, but at dimension zero the two numbers
differ: `deg_𝓛(Z)` is then `(𝓛^0 · Z) = χ(Z, 𝒪_Z)`
(`AlgebraicGeometry.intersectionNumber_zero`) while `deg(𝓛|_Z)` is `χ(Z, 𝓛|_Z) - χ(Z, 𝒪_Z)`,
and for a nonempty zero-dimensional `Z` the first is the positive integer `dim_k Γ(Z, 𝒪_Z)` and
the second is `0`.  The hypothesis is therefore `topologicalKrullDim Z = 1`, which is where
`deg_𝓛(Z)` is the intersection number `(𝓛 · Z)`; the conclusion is then
`AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree`, which does keep the
source's `≤ 1`. -/
@[stacks 0BEY "the ample case"]
public theorem degreeWithRespectTo_eq_invertibleCurveDegree (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : topologicalKrullDim Z = 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hample : Scheme.Modules.IsAmple X L) :
    degreeWithRespectTo k f i 1 hd L hample =
      invertibleCurveDegree k (i ≫ f) hd.le ((Scheme.Modules.pullback i).obj L) :=
  intersectionNumber_one_eq_invertibleCurveDegree k f i hd.le L

end AlgebraicGeometry

end
