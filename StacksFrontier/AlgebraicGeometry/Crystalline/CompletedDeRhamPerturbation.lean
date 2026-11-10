module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSplitDifferential
public import StacksFrontier.AlgebraicGeometry.Crystalline.FinitePerturbation

/-!
# The completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] for a module with a connection

Let `D` be the `p`-adic completion of a divided power ring `B` over `A`, let
`D' = B⟨x_w : w ∈ W⟩^∧` and let `M` be a `p`-adically complete `D`-module with a completed
connection.  `Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_identity` proves
the clause of [Stacks, Lemma 60.21.2, Tag 07LD] for `M = D`: the comparison
`Ω̂^*_D → Ω̂^*_{D'}` is a homotopy equivalence.  That homotopy does **not** tensor up with `M`,
because the differential of `M ⊗̂_D Ω^*_{D'}` is the connection-twisted
`∇ m ∧ ω + m ⊗ d ω` and not `1_M ⊗ d`; what tensors up is the homotopy against the *relative*
differential only.  This module makes up the difference and proves the clause with the module:

**the comparison `M ⊗̂_D Ω^*_D → M ⊗̂_D Ω^*_{D'}` is a homotopy equivalence for the
connection-twisted differential, with the perturbed `1_M ⊗ ε̂` as its retraction.**

## The route, and why no spectral sequence appears

The source filters `Ω^*_{P/A,δ'}` by `F^k = σ_{≥k}Ω^*_B ∧ Ω^*_P`, shows that the comparison
induces a quasi-isomorphism on graded pieces, and concludes by the spectral sequence of a filtered
complex.  That machinery is not needed, because the filtration is **finite in each exterior
degree**: a form of degree `n` has at most `n` coefficient differentials.  Write the differential
of `M ⊗̂_D Ω^*_{D'}` as `D = D_rel + D_base` — the splitting of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamSplitDifferential.lean` — and let `h`
be the completed relative homotopy tensored with `M`.  Then

* `h` preserves the number of coefficient differentials and lowers the number of variable
  differentials by one;
* `D_base` raises the number of coefficient differentials by one;

so `N = D_base ∘ h` raises it by one, and in exterior degree `n` there are only `n + 1`
bidegrees: `N^{n+1} = 0`.  The perturbation series `H = h ∘ Σ_k (-N)^k` is therefore a *finite*
sum in each degree, and `Crystalline.FinitePerturbation.exists_perturbedContraction` — the basic
perturbation lemma — turns the contraction of `D_rel` into a contraction of `D`.  No limit is
taken and no spectral sequence is used.

## The bridge this module supplies

`CompletedDeRhamSplitDifferential` deliberately does not say that `D_rel` raises the variable
degree and `D_base` the coefficient degree: that is a statement about the bidegree decomposition,
which has to be carried as data for the abstract family `Om`.  Carrying it is the first half of
this module.  The decomposition is carried **as a family of projections** `proj n i : Ω^n → Ω^n`,
one for each bidegree `(i, n - i)`, subject to `∑_{i ≤ n} proj n i = id`; the raising statements
are then

* `proj (n+1) l ∘ d_base ∘ proj n i = 0` for `l ≤ i`,
* `proj (n+1) l ∘ (− ∧ proj 1 1 η) ∘ proj n i = 0` for `l ≤ i` — the wedge with a base one-form
  raises the coefficient degree too, which is what makes the `∇ m ∧ ω` half of `D_base` raise it;
* `proj 1 1 ∘ ∇ = ∇`, the connection taking its values in the coefficient one-forms;
* `ĥ ∘ proj (n+1) i = proj n i ∘ ĥ`, the homotopy preserving the coefficient degree.

Projections rather than a direct sum decomposition, for two reasons.  `M ⊗̂_D Ω^n_{D'}` is a
*completion of a tensor product*: it is the direct sum of the completed bidegree summands only
through the finite-index comparison of `AdicCompletion` with direct sums, whereas each projection
completes termwise with no comparison at all; and the operator whose nilpotence is wanted is only
**additive**, the base differential obeying the Leibniz rule and not `D`-linearity, so no
submodule of the completed tensor product is stable under it and the span filtration of
`Crystalline.DividedPowerPolynomial.antidiagonalCoefficientFiltration` cannot be used.  The
finiteness itself is
`Crystalline.DividedPowerPolynomial.iterate_eq_zero_of_raisesProjectionDegree`, which is that
filtration's statement in projection form.

## What is carried and what is proved

Carried, besides the bidegree data: `D² = 0` for the total differential
(`Crystalline.CompletedDeRham.IsSquareZero`), which is the vanishing of the curvature of the
completed connection and is a hypothesis everywhere in this library, including on
`Crystalline.CompletedDeRham.complex` itself; `d_rel² = 0` on the forms; the splitting
`d = d_rel + d_base`; and the contraction of the relative differential on the forms, which is
`Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_identity` read as an identity
of `D`-linear maps.  `D_base² = 0` is **not** needed: the perturbation lemma consumes only the
cross-term identity `D_base D + D_rel D_base = 0`, which is derived here from `D² = 0` and
`D_rel² = 0` alone.

Proved: that the relative contraction tensors up with `M`, as do the side conditions of a special
deformation retract; that `D_base ∘ h` is nilpotent in each degree; the contraction of the twisted
differential; and, with the side conditions, that the comparison with the retract is a homotopy
equivalence.

## Two conclusions, with and without the retract

`Crystalline.CompletedDeRham.exists_twistedContraction` asks nothing of `ĥ` beyond the contraction
and concludes that the identity of `M ⊗̂_D Ω^*_{D'}` is chain homotopic to `Q`, a perturbation of
`1_M ⊗ ψ̂ ε̂`.  `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` adds the side conditions
`ĥ² = 0`, `ĥ ψ̂ = 0`, `ε̂ ĥ = 0` of a *special* deformation retract — which the completed
homotopy of
`Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_identity` satisfies, by
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/RelativePoincareSpecial.lean` — and
concludes the full statement of the source: `M ⊗̂_D Ω^*_D` carries a differential for which the
comparison `ι'` is a map of complexes with a map of complexes `π'` back, `π' ι' = 1` and
`ι' π'` chain homotopic to the identity, i.e. `ι'` is a **homotopy equivalence** and in particular
a quasi-isomorphism.

## What is deliberately not claimed

* **No `CochainComplex`.**  The conclusions are identities between additive maps, in the degreewise
  form in which the library states the differential; nothing is assembled into
  `HomologicalComplex` language, and the word quasi-isomorphism appears only as a consequence of
  the homotopy equivalence and not as a statement about `homologyMap`.
* **`Ω^*` is the carried graded family**, as in `CompletedConnectionDeRham`, and is not identified
  with the completed divided power forms of any particular ring; the bidegree projections are
  data supplied by whoever applies this.  The genuine completed divided power forms of
  `D' = B⟨x_w⟩^∧` are supplied in
  `StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/RelativeSplitDifferential.lean`, by
  `Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_completedPolynomialForms`.

## Main definitions

* `Crystalline.CompletedDeRham.completedLTensor` — `1_M ⊗ f` on completed tensor products, for a
  `D`-linear map `f` of the forms, with its functoriality.  Every map in the bidegree bridge is
  of this shape, which is exactly why they all tensor up with `M`.

## Main results

* `Crystalline.CompletedDeRham.completedLTensor_differential_completedLTensor_eq_zero` — **the
  bridge: the base part of the differential raises the coefficient degree** on
  `M ⊗̂_D Ω^*`, from the corresponding statements for `d_base`, for the wedge and for `∇`.
* `Crystalline.CompletedDeRham.iterate_differential_relHomotopy_eq_zero` — **`(D_base ∘ h)^{n+2}`
  vanishes in degree `n + 1`**, the nilpotence that makes the perturbation series finite.
* `Crystalline.CompletedDeRham.relContraction_zero` and
  `Crystalline.CompletedDeRham.relContraction` — the contraction of the relative differential
  tensored up with `M`.
* `Crystalline.CompletedDeRham.differential_relDifferential_cross` — the cross-term identity
  `D_base D + D_rel D_base = 0`, from `D² = 0` and `d_rel² = 0`.
* `Crystalline.CompletedDeRham.exists_twistedContraction` — the identity of `M ⊗̂_D Ω^*_{D'}` is
  chain homotopic, for the twisted differential, to a perturbation of `1_M ⊗ ψ̂ ε̂`, with no side
  condition on `ĥ`.
* `Crystalline.CompletedDeRham.completedLTensor_comp_eq_zero` and `..._completedLTensor_comp_eq_id`
  — how the side conditions of a special deformation retract tensor up with `M`.
* `Crystalline.CompletedDeRham.differential_completedLTensor` — **a graded comparison of the
  forms compatible with the wedge and the de Rham differential is a map of the twisted de Rham
  complexes**, the connection on the target being the pushforward of the one on the source.  This
  is what names the comparison map of the source's statement.
* `Crystalline.CompletedDeRham.completedLTensor_hhat_differential_iota_eq_zero` and
  `..._exists_twistedHomotopyEquivOfInclusion` — **the homotopy equivalence with `1_M ⊗ ψ` itself
  as the equivalence**, the perturbation of `1_M ⊗ ψ` being trivial because `ψ` lands in the top
  coefficient degree.
* `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` — **the completed clause of
  [Stacks, Lemma 60.21.2, Tag 07LD] for a module with a connection**: for a special deformation
  retract the comparison `M ⊗̂_D Ω^*_D → M ⊗̂_D Ω^*_{D'}` is a homotopy equivalence of the twisted
  de Rham complexes, hence a quasi-isomorphism.
* `Crystalline.CompletedDeRham.isGradedLeibniz_of_ringHom` and
  `Crystalline.CompletedDeRham.bilinearOfRingHom` — the Leibniz rule and the wedge product under
  a restriction of scalars, which is what lets a family of forms whose own ring of scalars is
  `D'` be read as a de Rham complex over `D`.
* `Crystalline.CompletedDeRham.pushforwardConnection` and
  `Crystalline.CompletedDeRham.completedLTensor_pushforwardConnection` — pushing a connection
  along a linear map of the forms, and the resulting `hnabla`.

## References

* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u v v₁ v₂ v' w

namespace Crystalline

namespace CompletedDeRham

/-! ### The Leibniz rule under a restriction of scalars -/

section RestrictScalars

universe u₁

variable (D : Type u) [CommRing D] (D' : Type u₁) [CommRing D'] (g : D →+* D')
  (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)] [∀ i, Module D' (Om i)] [∀ i, Module D (Om i)]
  (wedge' : ∀ i, Om i →ₗ[D'] Om 1 →ₗ[D'] Om (i + 1))
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1)) (deRham : ∀ i, Om i →+ Om (i + 1))
  (dmap' : D' → Om 1)

/-- **The Leibniz rule survives a restriction of scalars.**

If a graded family of `D'`-modules of forms satisfies
`Crystalline.CompletedDeRham.IsGradedLeibniz` over `D'`, and `D` acts through a ring map
`g : D → D'`, then it satisfies the Leibniz rule over `D` for the universal differential
`d ∘ g`.

This is what makes the completed divided power forms of `D' = B⟨x_w⟩^∧` a de Rham complex over
the completion `D` of the base `B`: the Leibniz rule they satisfy is the one over their own ring
`D'`, by `Crystalline.isGradedLeibniz_completedDividedPower`, and the perturbation argument of
[Stacks, Lemma 60.21.2, Tag 07LD] needs it over `D`.  The restricted wedge is supplied as a
separate map with an equation rather than as a `LinearMap.restrictScalars`, so that no
compatibility instance has to exist before the statement can be made. -/
public theorem isGradedLeibniz_of_ringHom
    (hsmul : ∀ (i : ℕ) (c : D) (x : Om i), c • x = g c • x)
    (hwedge : ∀ (i : ℕ) (x : Om i) (y : Om 1), wedge i x y = wedge' i x y)
    (h : IsGradedLeibniz D' Om wedge' deRham dmap') :
    IsGradedLeibniz D Om wedge deRham fun c ↦ dmap' (g c) := by
  intro i f omega
  rw [hsmul i f omega, h i (g f) omega, hsmul (i + 1) f (deRham i omega),
    hwedge i omega (dmap' (g f))]

/-- **A `D'`-bilinear wedge product is `D`-bilinear** when `D` acts through a ring map
`g : D → D'`.

This is the `wedge` of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` at a family of
forms whose own ring of scalars is `D'` and which is read as a `D`-module by restriction of
scalars.  The underlying function is unchanged, by
`Crystalline.CompletedDeRham.bilinearOfRingHom_apply`; it is the two linearities that are
re-recorded. -/
public def bilinearOfRingHom (hsmul : ∀ (i : ℕ) (c : D) (x : Om i), c • x = g c • x) (i : ℕ) :
    Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1) :=
  LinearMap.mk₂ D (fun x y ↦ wedge' i x y)
    (fun x x' y ↦ by rw [map_add, LinearMap.add_apply])
    (fun c x y ↦ by
      rw [hsmul i c x, hsmul (i + 1) c (wedge' i x y), map_smul, LinearMap.smul_apply])
    (fun x y y' ↦ map_add (wedge' i x) y y')
    (fun c x y ↦ by rw [hsmul 1 c y, hsmul (i + 1) c (wedge' i x y), map_smul])

/-- The restricted wedge product is the original one. -/
@[simp] public theorem bilinearOfRingHom_apply
    (hsmul : ∀ (i : ℕ) (c : D) (x : Om i), c • x = g c • x) (i : ℕ) (x : Om i) (y : Om 1) :
    bilinearOfRingHom D D' g Om wedge' hsmul i x y = wedge' i x y :=
  rfl

end RestrictScalars

/-! ### `1_M ⊗ f` on completed tensor products -/

section LTensor

variable (p : ℕ) (D : Type u) [CommRing D] (M : Type w) [AddCommGroup M] [Module D M]
  {X : Type v} {Y : Type v₁} {Z : Type v₂} [AddCommGroup X] [Module D X] [AddCommGroup Y]
  [Module D Y] [AddCommGroup Z] [Module D Z]

/-- **`1_M ⊗ f` on completed tensor products**, for a `D`-linear map `f` of the forms: the
`p`-adic completion of `1_M ⊗ f`.

This is the shape of every map in the bidegree bridge below — the relative differential, the
relative homotopy, the retraction and each bidegree projection — and it is exactly why they all
tensor up with `M` while the total differential does not: a `D`-linear map of the forms induces a
map of the tensor product over `D`, and an additive one, obeying the Leibniz rule, does not. -/
public def completedLTensor (f : X →ₗ[D] Y) :
    CompletedTensor p D X M →+ CompletedTensor p D Y M :=
  (AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M f)).toAddMonoidHom

/-- The value of `1_M ⊗ f` at the level `pᵏ`. -/
public theorem completedLTensor_val (f : X →ₗ[D] Y) (k : ℕ) (x : CompletedTensor p D X M) :
    (completedLTensor p D M f x).val k =
      (LinearMap.lTensor M f).reduceModIdeal ((pAdicIdeal (A := D) p) ^ k) (x.val k) :=
  rfl

/-- The level-`k` value of `1_M ⊗ f` on `x` is `1_M ⊗ f` of any representative of `x.val k`. -/
private theorem completedLTensor_val_mk (f : X →ₗ[D] Y) (x : CompletedTensor p D X M) (k : ℕ)
    (y : M ⊗[D] X) (hy : Submodule.Quotient.mk y = x.val k) :
    (completedLTensor p D M f x).val k = Submodule.Quotient.mk (LinearMap.lTensor M f y) := by
  rw [completedLTensor_val, ← hy]
  rfl

/-- `1_M ⊗ −` is functorial. -/
public theorem completedLTensor_comp (f : X →ₗ[D] Y) (g : Y →ₗ[D] Z)
    (x : CompletedTensor p D X M) :
    completedLTensor p D M g (completedLTensor p D M f x) =
      completedLTensor p D M (g ∘ₗ f) x := by
  change AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M g)
    (AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M f) x) = _
  rw [AdicCompletion.map_comp_apply, ← LinearMap.lTensor_comp]
  rfl

/-- `1_M ⊗ id = id`. -/
public theorem completedLTensor_id (x : CompletedTensor p D X M) :
    completedLTensor p D M (LinearMap.id : X →ₗ[D] X) x = x := by
  change AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M LinearMap.id) x = x
  simp

/-- **`1_M ⊗ f` is linear over `D`**, not merely additive: it is `AdicCompletion.map` of a
`D`-linear map, and the scalar tower `D → D^∧ → M ⊗̂_D Ω` makes its `D^∧`-linearity give
`D`-linearity. -/
public theorem completedLTensor_smul (f : X →ₗ[D] Y) (c : D) (x : CompletedTensor p D X M) :
    completedLTensor p D M f (c • x) = c • completedLTensor p D M f x :=
  ((AdicCompletion.map (pAdicIdeal (A := D) p)
    (LinearMap.lTensor M f)).restrictScalars D).map_smul c x

/-- **`1_M ⊗ f` on the image of a pure tensor.** -/
public theorem completedLTensor_toCompletedTensor_tmul (f : X →ₗ[D] Y) (m : M) (omega : X) :
    completedLTensor p D M f (toCompletedTensor p D X M (m ⊗ₜ[D] omega)) =
      toCompletedTensor p D Y M (m ⊗ₜ[D] f omega) := by
  change AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M f)
      (AdicCompletion.of (pAdicIdeal (A := D) p) (M ⊗[D] X) (m ⊗ₜ[D] omega)) = _
  rw [AdicCompletion.map_of, LinearMap.lTensor_tmul]

/-- `1_M ⊗ 0 = 0`. -/
public theorem completedLTensor_zero (x : CompletedTensor p D X M) :
    completedLTensor p D M (0 : X →ₗ[D] Y) x = 0 := by
  change AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M 0) x = 0
  rw [LinearMap.lTensor_zero, AdicCompletion.map_zero]
  rfl

/-- `1_M ⊗ −` is additive in the map. -/
public theorem completedLTensor_add (f g : X →ₗ[D] Y) (x : CompletedTensor p D X M) :
    completedLTensor p D M (f + g) x =
      completedLTensor p D M f x + completedLTensor p D M g x := by
  change AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M (f + g)) x = _
  rw [LinearMap.lTensor_add, map_add]
  rfl

/-- `1_M ⊗ −` takes a finite sum of maps to the sum of their completions.  This is what makes the
bidegree projections of the forms complete to a family summing to the identity. -/
public theorem completedLTensor_sum {ι : Type*} (s : Finset ι) (f : ι → (X →ₗ[D] Y))
    (x : CompletedTensor p D X M) :
    completedLTensor p D M (∑ i ∈ s, f i) x = ∑ i ∈ s, completedLTensor p D M (f i) x := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact completedLTensor_zero p D M x
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, completedLTensor_add, ih]

/-- **A composite of forms maps that vanishes stays vanishing after `1_M ⊗ −`.**  This is how the
side conditions `ĥ² = 0`, `ĥ ψ̂ = 0` and `ε̂ ĥ = 0` of a special deformation retract tensor up. -/
public theorem completedLTensor_comp_eq_zero (f : X →ₗ[D] Y) (g : Y →ₗ[D] Z) (hfg : g ∘ₗ f = 0)
    (x : CompletedTensor p D X M) :
    completedLTensor p D M g (completedLTensor p D M f x) = 0 := by
  rw [completedLTensor_comp, hfg]
  exact completedLTensor_zero p D M x

/-- **A composite of forms maps that is the identity stays the identity after `1_M ⊗ −`.**  This
is how the side condition `ε̂ ψ̂ = id` tensors up. -/
public theorem completedLTensor_comp_eq_id (f : X →ₗ[D] Y) (g : Y →ₗ[D] X)
    (hfg : g ∘ₗ f = LinearMap.id) (x : CompletedTensor p D X M) :
    completedLTensor p D M g (completedLTensor p D M f x) = x := by
  rw [completedLTensor_comp, hfg]
  exact completedLTensor_id p D M x

/-- `1_M ⊗ f` on the image of a pure tensor. -/
public theorem completedLTensor_of (f : X →ₗ[D] Y) (m : M) (ω : X) :
    completedLTensor p D M f (toCompletedTensor p D X M (m ⊗ₜ[D] ω)) =
      toCompletedTensor p D Y M (m ⊗ₜ[D] f ω) :=
  completedLTensor_toCompletedTensor_tmul p D M f m ω

/-! ### Pushing a completed connection along a linear map of the forms -/

/-- **The pushforward of a completed connection along a `D`-linear map of the forms** which
carries the one universal differential to the other.

This is what produces a connection with values in `M ⊗̂_D Ω̂¹_{D'}` from one with values in
`M ⊗̂_D Ω̂¹_D`, which is the shape [Stacks, Lemma 60.21.2, Tag 07LD] starts from: there `M` is a
module over the completion `D` of the base with a connection of its own, and the comparison
`ψ̂ : Ω̂¹_D → Ω̂¹_{D'}` pushes it into the forms of the polynomial algebra.  Its values then lie in
coefficient degree one, which is the `hnabla` hypothesis of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`. -/
public def pushforwardConnection (f : X →ₗ[D] Y) {dX : D → X} {dY : D → Y}
    (hf : ∀ c : D, f (dX c) = dY c) (nabla : CompletedConnection p D X dX M) :
    CompletedConnection p D Y dY M where
  toFun m := completedLTensor p D M f (nabla m)
  map_add' m n := by rw [CompletedConnection.map_add, map_add]
  leibniz' c m := by
    rw [nabla.leibniz c m, map_add, completedLTensor_smul,
      completedLTensor_toCompletedTensor_tmul, hf]

/-- The pushforward of `nabla` along `f` sends `m` to `(1_M ⊗ f) (nabla m)`. -/
@[simp] public theorem pushforwardConnection_apply (f : X →ₗ[D] Y) {dX : D → X} {dY : D → Y}
    (hf : ∀ c : D, f (dX c) = dY c) (nabla : CompletedConnection p D X dX M) (m : M) :
    pushforwardConnection p D M f hf nabla m = completedLTensor p D M f (nabla m) :=
  rfl

/-- **A pushed-forward connection takes its values in the image of the map it is pushed along**,
read through a projection which fixes that image: this is the `hnabla` hypothesis of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`. -/
public theorem completedLTensor_pushforwardConnection (f : X →ₗ[D] Y) {dX : D → X} {dY : D → Y}
    (hf : ∀ c : D, f (dX c) = dY c) (nabla : CompletedConnection p D X dX M)
    (proj : Y →ₗ[D] Y) (hproj : proj ∘ₗ f = f) (m : M) :
    completedLTensor p D M proj (pushforwardConnection p D M f hf nabla m) =
      pushforwardConnection p D M f hf nabla m := by
  rw [pushforwardConnection_apply, completedLTensor_comp, hproj]

end LTensor

/-! ### The bridge: the base differential raises the coefficient degree -/

section Bidegree

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (dbase : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M] [Module D M]
  (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleibBase : IsGradedLeibniz D Om wedge dbase dmap)

/-- **The base part of the de Rham formula raises the coefficient degree, on the uncompleted
tensor product.**  Both halves of `∇(m ⊗ ω) = ∇ m ∧ ω + m ⊗ d_base ω` do: the first because the
connection takes its values in the coefficient one-forms and the wedge with a coefficient one-form
raises the coefficient degree, the second because `d_base` does.  It is enough to check this on
pure tensors, where it is the two hypotheses. -/
public theorem completedLTensor_rawDifferential_eq_zero (proj : ∀ n _i, Om n →ₗ[D] Om n)
    (hnabla : ∀ m : M, completedLTensor p D M (proj 1 1) (nabla m) = nabla m)
    (hprojwedge : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n,
      proj (n + 1) l ∘ₗ wedge n (proj n i ω) ∘ₗ proj 1 1 = 0)
    (hprojbase : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n, proj (n + 1) l (dbase n (proj n i ω)) = 0)
    (n l i : ℕ) (hli : l ≤ i) (y : M ⊗[D] Om n) :
    completedLTensor p D M (proj (n + 1) l)
        (rawDifferential p D Om wedge dbase M nabla hleibBase n
          (LinearMap.lTensor M (proj n i) y)) = 0 := by
  induction y using TensorProduct.inductionOn with
  | tmul m ω =>
    rw [LinearMap.lTensor_tmul, rawDifferential_tmul, map_add]
    have hw : completedLTensor p D M (proj (n + 1) l)
        (wedgeMap p D Om wedge M n (proj n i ω) (nabla m)) = 0 := by
      calc completedLTensor p D M (proj (n + 1) l)
            (wedgeMap p D Om wedge M n (proj n i ω) (nabla m))
          = completedLTensor p D M (proj (n + 1) l)
              (completedLTensor p D M (wedge n (proj n i ω))
                (completedLTensor p D M (proj 1 1) (nabla m))) := by rw [hnabla m]; rfl
        _ = completedLTensor p D M
              (proj (n + 1) l ∘ₗ wedge n (proj n i ω) ∘ₗ proj 1 1) (nabla m) := by
              rw [completedLTensor_comp p D M (proj 1 1) (wedge n (proj n i ω)),
                completedLTensor_comp]
        _ = 0 := by rw [hprojwedge n l i hli ω]; exact completedLTensor_zero p D M (nabla m)
    have hb : completedLTensor p D M (proj (n + 1) l)
        (toCompletedTensor p D (Om (n + 1)) M (m ⊗ₜ[D] dbase n (proj n i ω))) = 0 := by
      rw [completedLTensor_of, hprojbase n l i hli ω, TensorProduct.tmul_zero, map_zero]
    rw [hw, hb, add_zero]
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, add_zero]

/-- **The bridge: the base part of the differential of `M ⊗̂_D Ω^*` raises the coefficient
degree.**

`D_base` is determined by the de Rham formula at each level `pᵏ`, and each bidegree projection is
the completion of `1_M ⊗ proj`, so the statement reduces at every level to
`Crystalline.CompletedDeRham.completedLTensor_rawDifferential_eq_zero` on a representative in the
uncompleted tensor product.  This is the statement
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamSplitDifferential.lean` leaves open and
the perturbation argument needs. -/
public theorem completedLTensor_differential_completedLTensor_eq_zero
    (proj : ∀ n _i, Om n →ₗ[D] Om n)
    (hnabla : ∀ m : M, completedLTensor p D M (proj 1 1) (nabla m) = nabla m)
    (hprojwedge : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n,
      proj (n + 1) l ∘ₗ wedge n (proj n i ω) ∘ₗ proj 1 1 = 0)
    (hprojbase : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n, proj (n + 1) l (dbase n (proj n i ω)) = 0)
    (n l i : ℕ) (hli : l ≤ i) (x : CompletedTensor p D (Om n) M) :
    completedLTensor p D M (proj (n + 1) l)
        (differential p D Om wedge dbase M nabla hleibBase n
          (completedLTensor p D M (proj n i) x)) = 0 := by
  refine AdicCompletion.ext fun k ↦ ?_
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective
    ((pAdicIdeal (A := D) p) ^ k • ⊤ : Submodule D (M ⊗[D] Om n)) (x.val k)
  have hstep := completedLTensor_rawDifferential_eq_zero p D Om wedge dbase M nabla hleibBase
    proj hnabla hprojwedge hprojbase n l i hli y
  have hval := completedLTensor_val_mk p D M (proj n i) x k y hy
  calc (completedLTensor p D M (proj (n + 1) l)
        (differential p D Om wedge dbase M nabla hleibBase n
          (completedLTensor p D M (proj n i) x))).val k
      = (LinearMap.lTensor M (proj (n + 1) l)).reduceModIdeal ((pAdicIdeal (A := D) p) ^ k)
          (levelDifferential p D Om wedge dbase M nabla hleibBase n k
            ((completedLTensor p D M (proj n i) x).val k)) := rfl
    _ = (LinearMap.lTensor M (proj (n + 1) l)).reduceModIdeal ((pAdicIdeal (A := D) p) ^ k)
          ((rawDifferential p D Om wedge dbase M nabla hleibBase n
            (LinearMap.lTensor M (proj n i) y)).val k) := by
        rw [hval, levelDifferential_mk]
    _ = (completedLTensor p D M (proj (n + 1) l)
          (rawDifferential p D Om wedge dbase M nabla hleibBase n
            (LinearMap.lTensor M (proj n i) y))).val k := rfl
    _ = (0 : CompletedTensor p D (Om (n + 1)) M).val k := by rw [hstep]

/-- **The bidegree projections of `M ⊗̂_D Ω^n` sum to the identity**, there being `n + 1` of them
in exterior degree `n`.  This is the completion of the corresponding statement on the forms, by
the additivity of `1_M ⊗ −` in the map. -/
public theorem completedLTensor_proj_sum (proj : ∀ n _i, Om n →ₗ[D] Om n)
    (hprojsum : ∀ (n : ℕ) (ω : Om n), ∑ i ∈ Finset.range (n + 1), proj n i ω = ω) (n : ℕ)
    (x : CompletedTensor p D (Om n) M) :
    ∑ i ∈ Finset.range (n + 1), completedLTensor p D M (proj n i) x = x := by
  have hid : ∑ i ∈ Finset.range (n + 1), proj n i = LinearMap.id (R := D) (M := Om n) :=
    LinearMap.ext fun ω ↦ by rw [LinearMap.sum_apply]; exact hprojsum n ω
  rw [← completedLTensor_sum, hid, completedLTensor_id]

/-- **`D_base ∘ h` is nilpotent in each degree**: in exterior degree `n + 1` it dies after
`n + 2` steps.

`h = 1_M ⊗ ĥ` preserves the coefficient degree and `D_base` raises it, so the composite raises it;
and in exterior degree `n + 1` there are only `n + 2` bidegrees.  This is the finiteness of the
perturbation series, and it is what the source obtains a limit for instead. -/
public theorem iterate_differential_relHomotopy_eq_zero (proj : ∀ n _i, Om n →ₗ[D] Om n)
    (hhat : ∀ n, Om (n + 1) →ₗ[D] Om n)
    (hprojsum : ∀ (n : ℕ) (ω : Om n), ∑ i ∈ Finset.range (n + 1), proj n i ω = ω)
    (hnabla : ∀ m : M, completedLTensor p D M (proj 1 1) (nabla m) = nabla m)
    (hprojwedge : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n,
      proj (n + 1) l ∘ₗ wedge n (proj n i ω) ∘ₗ proj 1 1 = 0)
    (hprojbase : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n, proj (n + 1) l (dbase n (proj n i ω)) = 0)
    (hprojhhat : ∀ (n i : ℕ), hhat n ∘ₗ proj (n + 1) i = proj n i ∘ₗ hhat n) (n : ℕ)
    (x : CompletedTensor p D (Om (n + 1)) M) :
    (fun y ↦ differential p D Om wedge dbase M nabla hleibBase n
      (completedLTensor p D M (hhat n) y))^[n + 2] x = 0 := by
  refine DividedPowerPolynomial.iterate_eq_zero_of_raisesProjectionDegree (n + 2)
    (fun j ↦ completedLTensor p D M (proj (n + 1) j))
    ((differential p D Om wedge dbase M nabla hleibBase n).comp
      (completedLTensor p D M (hhat n)))
    (completedLTensor_proj_sum p D Om M proj hprojsum (n + 1)) ?_ x
  intro l j hlj y
  change completedLTensor p D M (proj (n + 1) l)
    (differential p D Om wedge dbase M nabla hleibBase n
      (completedLTensor p D M (hhat n)
        (completedLTensor p D M (proj (n + 1) j) y))) = 0
  rw [completedLTensor_comp, hprojhhat n j, ← completedLTensor_comp]
  exact completedLTensor_differential_completedLTensor_eq_zero p D Om wedge dbase M nabla
    hleibBase proj hnabla hprojwedge hprojbase n l j hlj _

end Bidegree

/-! ### A comparison of the forms is a map of the twisted de Rham complexes -/

section ChainMap

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (Om' : ℕ → Type v') [∀ i, AddCommGroup (Om' i)]
  [∀ i, Module D (Om' i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D] Om' 1 →ₗ[D] Om' (i + 1)) (deRham : ∀ i, Om i →+ Om (i + 1))
  (deRham' : ∀ i, Om' i →+ Om' (i + 1)) {dmap : D → Om 1} {dmap' : D → Om' 1} (M : Type w)
  [AddCommGroup M] [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)
  (hleib' : IsGradedLeibniz D Om' wedge' deRham' dmap') (psi : ∀ i, Om i →ₗ[D] Om' i)
  (hpsi1 : ∀ c : D, psi 1 (dmap c) = dmap' c)
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge' i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham' i (psi i ω))

include hleib hleib' hpsi_wedge hpsi_deRham in
/-- **A graded comparison of the forms commutes with the de Rham formula**, on the uncompleted
tensor product: `1_M ⊗ ψ` carries `∇ m ∧ ω + m ⊗ d ω` to `∇' m ∧ ψ ω + m ⊗ d' (ψ ω)`, the pushed
connection `∇' = (1_M ⊗ ψ) ∇` being used on the right.  On a pure tensor the first term is the
compatibility of `ψ` with the wedge and the second its compatibility with the de Rham
differential. -/
public theorem rawDifferential_lTensor (i : ℕ) (y : M ⊗[D] Om i) :
    rawDifferential p D Om' wedge' deRham' M
        (pushforwardConnection p D M (psi 1) hpsi1 nabla) hleib' i
        (LinearMap.lTensor M (psi i) y) =
      completedLTensor p D M (psi (i + 1))
        (rawDifferential p D Om wedge deRham M nabla hleib i y) := by
  induction y using TensorProduct.inductionOn with
  | tmul m ω =>
    rw [LinearMap.lTensor_tmul, rawDifferential_tmul, rawDifferential_tmul, map_add,
      completedLTensor_of, hpsi_deRham i ω]
    refine congrArg (fun z : CompletedTensor p D (Om' (i + 1)) M ↦
      z + toCompletedTensor p D (Om' (i + 1)) M (m ⊗ₜ[D] deRham' i (psi i ω))) ?_
    change completedLTensor p D M (wedge' i (psi i ω))
        (completedLTensor p D M (psi 1) (nabla m)) =
      completedLTensor p D M (psi (i + 1)) (completedLTensor p D M (wedge i ω) (nabla m))
    rw [completedLTensor_comp, completedLTensor_comp]
    exact congrArg (fun f : Om 1 →ₗ[D] Om' (i + 1) ↦ completedLTensor p D M f (nabla m))
      (LinearMap.ext fun η ↦ (hpsi_wedge i ω η).symm)
  | add a b ha hb => simp only [map_add, ha, hb]

include hleib hleib' hpsi_wedge hpsi_deRham in
/-- **A graded comparison of the forms is a map of the twisted de Rham complexes**:
`d' ((1_M ⊗ ψ) z) = (1_M ⊗ ψ) (d z)`, the connection on the target being the pushforward of the
connection on the source along `ψ`.

Both differentials are determined by the de Rham formula at every level `pᵏ`, and `1_M ⊗ ψ` is
computed at the levels by `1_M ⊗ ψ` on representatives, so this reduces to
`Crystalline.CompletedDeRham.rawDifferential_lTensor`.  It is what makes the canonical comparison
of [Stacks, Lemma 60.20.2, Tag 07LD] a map of complexes, and with it the differential produced by
the perturbation argument is pinned: `1_M ⊗ ψ` is injective whenever it has a left inverse. -/
public theorem differential_completedLTensor (i : ℕ) (x : CompletedTensor p D (Om i) M) :
    differential p D Om' wedge' deRham' M
        (pushforwardConnection p D M (psi 1) hpsi1 nabla) hleib' i
        (completedLTensor p D M (psi i) x) =
      completedLTensor p D M (psi (i + 1))
        (differential p D Om wedge deRham M nabla hleib i x) := by
  refine AdicCompletion.ext fun k ↦ ?_
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective
    ((pAdicIdeal (A := D) p) ^ k • ⊤ : Submodule D (M ⊗[D] Om i)) (x.val k)
  have hval := completedLTensor_val_mk p D M (psi i) x k y hy
  have hraw := rawDifferential_lTensor p D Om Om' wedge wedge' deRham deRham' M nabla hleib
    hleib' psi hpsi1 hpsi_wedge hpsi_deRham i y
  calc (differential p D Om' wedge' deRham' M
          (pushforwardConnection p D M (psi 1) hpsi1 nabla) hleib' i
          (completedLTensor p D M (psi i) x)).val k
      = (rawDifferential p D Om' wedge' deRham' M
          (pushforwardConnection p D M (psi 1) hpsi1 nabla) hleib' i
          (LinearMap.lTensor M (psi i) y)).val k := by
        change levelDifferential p D Om' wedge' deRham' M
            (pushforwardConnection p D M (psi 1) hpsi1 nabla) hleib' i k
            ((completedLTensor p D M (psi i) x).val k) = _
        rw [hval, levelDifferential_mk]
    _ = (completedLTensor p D M (psi (i + 1))
          (rawDifferential p D Om wedge deRham M nabla hleib i y)).val k := by rw [hraw]
    _ = (completedLTensor p D M (psi (i + 1))
          (differential p D Om wedge deRham M nabla hleib i x)).val k := by
        change (LinearMap.lTensor M (psi (i + 1))).reduceModIdeal ((pAdicIdeal (A := D) p) ^ k)
            ((rawDifferential p D Om wedge deRham M nabla hleib i y).val k) =
          (LinearMap.lTensor M (psi (i + 1))).reduceModIdeal ((pAdicIdeal (A := D) p) ^ k)
            (levelDifferential p D Om wedge deRham M nabla hleib i k (x.val k))
        rw [← hy, levelDifferential_mk]

end ChainMap

/-! ### The contraction of the twisted differential -/

section Twisted

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (drel : ∀ i, Om i →ₗ[D] Om (i + 1))
  (dbase : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M] [Module D M]
  (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)
  (hleibBase : IsGradedLeibniz D Om wedge dbase dmap)

/-- **The degree-zero relative contraction, tensored up with `M`**: `h (D_rel x) + q x = x` on
`M ⊗̂_D Ω^0`.  All three maps are completions of `1_M ⊗ −` of a `D`-linear map of the forms, so
this is the forms-level identity with one additive functor applied to it. -/
public theorem relContraction_zero (hhat : ∀ n, Om (n + 1) →ₗ[D] Om n)
    (qform : ∀ n, Om n →ₗ[D] Om n) (hcon0form : hhat 0 ∘ₗ drel 0 + qform 0 = LinearMap.id)
    (x : CompletedTensor p D (Om 0) M) :
    completedLTensor p D M (hhat 0) (relDifferential p D Om drel M 0 x) +
        completedLTensor p D M (qform 0) x = x := by
  rw [show relDifferential p D Om drel M 0 x = completedLTensor p D M (drel 0) x from rfl,
    completedLTensor_comp, ← completedLTensor_add, hcon0form, completedLTensor_id]

/-- **The relative contraction in a positive degree, tensored up with `M`**:
`D_rel (h x) + h (D_rel x) + q x = x` on `M ⊗̂_D Ω^{n+1}`.

This is the completed relative divided power Poincaré lemma
`Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_identity` with the module put
back in.  It tensors up precisely because the relative differential is `D`-linear; the total
differential is not, which is the whole reason the perturbation argument is needed. -/
public theorem relContraction (hhat : ∀ n, Om (n + 1) →ₗ[D] Om n) (qform : ∀ n, Om n →ₗ[D] Om n)
    (hconform : ∀ n : ℕ,
      drel n ∘ₗ hhat n + hhat (n + 1) ∘ₗ drel (n + 1) + qform (n + 1) = LinearMap.id)
    (n : ℕ) (x : CompletedTensor p D (Om (n + 1)) M) :
    relDifferential p D Om drel M n (completedLTensor p D M (hhat n) x) +
          completedLTensor p D M (hhat (n + 1)) (relDifferential p D Om drel M (n + 1) x) +
        completedLTensor p D M (qform (n + 1)) x = x := by
  rw [show relDifferential p D Om drel M n (completedLTensor p D M (hhat n) x) =
      completedLTensor p D M (drel n) (completedLTensor p D M (hhat n) x) from rfl,
    show relDifferential p D Om drel M (n + 1) x = completedLTensor p D M (drel (n + 1)) x
      from rfl,
    completedLTensor_comp, completedLTensor_comp, ← completedLTensor_add,
    ← completedLTensor_add, hconform n, completedLTensor_id]

/-- **The cross-term identity `D_base D + D_rel D_base = 0`**, from `D² = 0` and `d_rel² = 0`
alone.

This is the one hypothesis the basic perturbation lemma needs beyond the contraction of the
relative differential, and it is weaker than the pair of square-zero statements of
`Crystalline.CompletedDeRham.relDifferential_baseDifferential_add_eq_zero`: expanding `D²` and
removing `D_rel²` leaves `D_rel D_base + D_base D` with no term in `D_base²`, so no curvature
statement about the base direction has to be carried. -/
public theorem differential_relDifferential_cross
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω)
    (hdrel : ∀ i : ℕ, (drel (i + 1)).comp (drel i) = 0)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib) (i : ℕ)
    (x : CompletedTensor p D (Om i) M) :
    differential p D Om wedge dbase M nabla hleibBase (i + 1)
          (differential p D Om wedge deRham M nabla hleib i x) +
        relDifferential p D Om drel M (i + 1)
          (differential p D Om wedge dbase M nabla hleibBase i x) = 0 := by
  have htot : differential p D Om wedge deRham M nabla hleib (i + 1)
      (differential p D Om wedge deRham M nabla hleib i x) = 0 :=
    DFunLike.congr_fun (hsq i) _
  rw [differential_eq_relDifferential_add p D Om wedge deRham drel dbase M nabla hleib hleibBase
    hsplit (i + 1) (differential p D Om wedge deRham M nabla hleib i x)] at htot
  have h1 : relDifferential p D Om drel M (i + 1)
        (differential p D Om wedge deRham M nabla hleib i x) =
      relDifferential p D Om drel M (i + 1)
        (differential p D Om wedge dbase M nabla hleibBase i x) := by
    rw [differential_eq_relDifferential_add p D Om wedge deRham drel dbase M nabla hleib
      hleibBase hsplit i x, map_add, relDifferential_relDifferential p D Om drel M hdrel i x,
      zero_add]
  rw [h1] at htot
  exact (add_comm _ _).trans htot

include hleibBase in
/-- **The completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] for a module with a connection.**

For `M` a `p`-adically complete `D`-module with a completed connection whose de Rham differential
on `M ⊗̂_D Ω^*` squares to zero, and for a graded family of forms whose de Rham differential
splits as `d = d_rel + d_base` with `d_rel` relative — `D`-linear — and contractible by `ĥ` onto
`ψ̂ ε̂`, and which carries a bidegree decomposition in which `d_base` and the wedge with a
coefficient one-form raise the coefficient degree while `ĥ` preserves it: the identity of
`M ⊗̂_D Ω^*` is chain homotopic, for the connection-twisted differential, to a perturbation `Q`
of `1_M ⊗ ψ̂ ε̂`.

The homotopy is `H = h ∘ Σ_k (-D_base h)^k` and `Q` is `1_M ⊗ ψ̂ ε̂` conjugated by the same
series; both are **finite sums in each degree**, by
`Crystalline.CompletedDeRham.iterate_differential_relHomotopy_eq_zero`.  That finiteness is what
replaces the source's spectral sequence of a filtered complex: see the module docstring.

No tag attribute is placed here.  [Stacks, Lemma 60.21.2, Tag 07LD] has several items, the
`M = D` case of this one is already tagged on
`Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_identity`, and what is proved
below is the contraction identity and not yet the quasi-isomorphism: `Q` is not identified with a
composite `ι' ∘ π'` through `M ⊗̂_D Ω^*_D`, for which the side conditions of a special deformation
retract would have to be added. -/
public theorem exists_twistedContraction (proj : ∀ n _i, Om n →ₗ[D] Om n)
    (hhat : ∀ n, Om (n + 1) →ₗ[D] Om n) (qform : ∀ n, Om n →ₗ[D] Om n)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω)
    (hdrel : ∀ i : ℕ, (drel (i + 1)).comp (drel i) = 0)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hcon0form : hhat 0 ∘ₗ drel 0 + qform 0 = LinearMap.id)
    (hconform : ∀ n : ℕ,
      drel n ∘ₗ hhat n + hhat (n + 1) ∘ₗ drel (n + 1) + qform (n + 1) = LinearMap.id)
    (hprojsum : ∀ (n : ℕ) (ω : Om n), ∑ i ∈ Finset.range (n + 1), proj n i ω = ω)
    (hnabla : ∀ m : M, completedLTensor p D M (proj 1 1) (nabla m) = nabla m)
    (hprojwedge : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n,
      proj (n + 1) l ∘ₗ wedge n (proj n i ω) ∘ₗ proj 1 1 = 0)
    (hprojbase : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n, proj (n + 1) l (dbase n (proj n i ω)) = 0)
    (hprojhhat : ∀ (n i : ℕ), hhat n ∘ₗ proj (n + 1) i = proj n i ∘ₗ hhat n) :
    ∃ (H : ∀ i, CompletedTensor p D (Om (i + 1)) M →+ CompletedTensor p D (Om i) M)
      (Q : ∀ i, CompletedTensor p D (Om i) M →+ CompletedTensor p D (Om i) M),
      (∀ x : CompletedTensor p D (Om 0) M,
          H 0 (differential p D Om wedge deRham M nabla hleib 0 x) + Q 0 x = x) ∧
        ∀ (n : ℕ) (x : CompletedTensor p D (Om (n + 1)) M),
          differential p D Om wedge deRham M nabla hleib n (H n x) +
              H (n + 1) (differential p D Om wedge deRham M nabla hleib (n + 1) x) +
            Q (n + 1) x = x :=
  FinitePerturbation.exists_perturbedContraction
    (C := fun i ↦ CompletedTensor p D (Om i) M)
    (fun i ↦ (relDifferential p D Om drel M i).toAddMonoidHom)
    (fun i ↦ differential p D Om wedge dbase M nabla hleibBase i)
    (fun i ↦ differential p D Om wedge deRham M nabla hleib i)
    (fun i ↦ completedLTensor p D M (hhat i)) (fun i ↦ completedLTensor p D M (qform i))
    (fun i x ↦ differential_eq_relDifferential_add p D Om wedge deRham drel dbase M nabla hleib
      hleibBase hsplit i x)
    (fun x ↦ relContraction_zero p D Om drel M hhat qform hcon0form x)
    (fun n x ↦ relContraction p D Om drel M hhat qform hconform n x)
    (fun i x ↦ differential_relDifferential_cross p D Om wedge deRham drel dbase M nabla hleib
      hleibBase hsplit hdrel hsq i x)
    (fun i ↦ i + 2)
    (fun i x ↦ iterate_differential_relHomotopy_eq_zero p D Om wedge dbase M nabla hleibBase
      proj hhat hprojsum hnabla hprojwedge hprojbase hprojhhat i x)

end Twisted

/-! ### The comparison with the retract is a homotopy equivalence -/

section TwistedRetract

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (OmL : ℕ → Type v') [∀ i, AddCommGroup (OmL i)]
  [∀ i, Module D (OmL i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (drel : ∀ i, Om i →ₗ[D] Om (i + 1))
  (dbase : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M] [Module D M]
  (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)
  (hleibBase : IsGradedLeibniz D Om wedge dbase dmap)

/-- The degree-zero relative contraction, with `q = ι π` applied as two successive maps. -/
private theorem relContraction_zero_comp (hhat : ∀ n, Om (n + 1) →ₗ[D] Om n)
    (iotaForm : ∀ i, OmL i →ₗ[D] Om i) (piForm : ∀ i, Om i →ₗ[D] OmL i)
    (hcon0form : hhat 0 ∘ₗ drel 0 + iotaForm 0 ∘ₗ piForm 0 = LinearMap.id)
    (x : CompletedTensor p D (Om 0) M) :
    completedLTensor p D M (hhat 0) (relDifferential p D Om drel M 0 x) +
      completedLTensor p D M (iotaForm 0) (completedLTensor p D M (piForm 0) x) = x := by
  rw [completedLTensor_comp p D M (piForm 0) (iotaForm 0) x]
  exact relContraction_zero p D Om drel M hhat (fun i ↦ iotaForm i ∘ₗ piForm i) hcon0form x

/-- The positive-degree relative contraction, with `q = ι π` applied as two successive maps. -/
private theorem relContraction_comp (hhat : ∀ n, Om (n + 1) →ₗ[D] Om n)
    (iotaForm : ∀ i, OmL i →ₗ[D] Om i) (piForm : ∀ i, Om i →ₗ[D] OmL i)
    (hconform : ∀ n : ℕ, drel n ∘ₗ hhat n + hhat (n + 1) ∘ₗ drel (n + 1) +
      iotaForm (n + 1) ∘ₗ piForm (n + 1) = LinearMap.id)
    (n : ℕ) (x : CompletedTensor p D (Om (n + 1)) M) :
    relDifferential p D Om drel M n (completedLTensor p D M (hhat n) x) +
        completedLTensor p D M (hhat (n + 1)) (relDifferential p D Om drel M (n + 1) x) +
      completedLTensor p D M (iotaForm (n + 1))
        (completedLTensor p D M (piForm (n + 1)) x) = x := by
  rw [completedLTensor_comp p D M (piForm (n + 1)) (iotaForm (n + 1)) x]
  exact relContraction p D Om drel M hhat (fun i ↦ iotaForm i ∘ₗ piForm i) hconform n x

include hleibBase in
/-- **The completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] for a module with a connection, as
a homotopy equivalence of complexes.**

Let `M` be a `p`-adically complete `D`-module with a completed connection whose de Rham
differential on `M ⊗̂_D Ω^*` squares to zero.  Let `Ω^*` be a graded family of `D`-modules whose
de Rham differential splits as `d = d_rel + d_base` with `d_rel` relative — `D`-linear — and
squaring to zero, let `Ω^*_L` be a graded family with `D`-linear `ψ : Ω^*_L → Ω^*` and
`ε : Ω^* → Ω^*_L`, and let `ĥ` contract `d_rel` onto `ψ ε` as a *special* deformation retract:

`ĥ d_rel + ψ ε = 1` in degree `0`,   `d_rel ĥ + ĥ d_rel + ψ ε = 1` above it,
`ĥ ĥ = 0`,   `ĥ ψ = 0`,   `ε ĥ = 0`,   `ε ψ = 1`.

Let finally `Ω^*` carry a bidegree decomposition in which `d_base` and the wedge with a
coefficient one-form raise the coefficient degree while `ĥ` preserves it.  Then `M ⊗̂_D Ω^*_L`
carries a differential `d_L` squaring to zero for which the perturbed comparison maps
`ι' : M ⊗̂_D Ω^*_L → M ⊗̂_D Ω^*` and `π'` are maps of complexes, with `π' ι' = 1` and `ι' π'` chain
homotopic to the identity.

So `ι'` is a homotopy equivalence of the twisted de Rham complexes, and in particular a
quasi-isomorphism, which is the assertion of the source's second clause.  `ι'` is the perturbation
of `1_M ⊗ ψ` and `π'` of `1_M ⊗ ε`; both are finite sums in every degree, by
`Crystalline.CompletedDeRham.iterate_differential_relHomotopy_eq_zero`, and that finiteness is
what replaces the source's spectral sequence of a filtered complex.  See the module docstring.

This is the clause with the module in it; the case `M = D` at the genuine completed divided power
forms is `Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_identity`, whose `ĥ`
satisfies the three side conditions above by
`Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_completedRelativeFormsHomotopy`
and its two companions.

This theorem is the perturbation machine, stated for an arbitrary graded family of forms with the
identities the perturbation needs listed as hypotheses, `hsq` among them.  The source's own
hypothesis in place of `hsq` is integrability of the connection, [Stacks, Tag 07JD], from which
`hsq` follows at the genuine forms; the tag is registered on the statement with the source's
hypotheses,
`Crystalline.DividedPowerPolynomial.exists_homotopyEquiv_isIntegrable`, which is
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquivOfInclusion` instantiated at `Ω̂^*_{D'}`
and `Ω̂^*_D`. -/
public theorem exists_twistedHomotopyEquiv (proj : ∀ n _i, Om n →ₗ[D] Om n)
    (hhat : ∀ n, Om (n + 1) →ₗ[D] Om n) (iotaForm : ∀ i, OmL i →ₗ[D] Om i)
    (piForm : ∀ i, Om i →ₗ[D] OmL i)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω)
    (hdrel : ∀ i : ℕ, (drel (i + 1)).comp (drel i) = 0)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hcon0form : hhat 0 ∘ₗ drel 0 + iotaForm 0 ∘ₗ piForm 0 = LinearMap.id)
    (hconform : ∀ n : ℕ, drel n ∘ₗ hhat n + hhat (n + 1) ∘ₗ drel (n + 1) +
      iotaForm (n + 1) ∘ₗ piForm (n + 1) = LinearMap.id)
    (hhhform : ∀ i : ℕ, hhat i ∘ₗ hhat (i + 1) = 0)
    (hhiotaform : ∀ i : ℕ, hhat i ∘ₗ iotaForm (i + 1) = 0)
    (hpihform : ∀ i : ℕ, piForm i ∘ₗ hhat i = 0)
    (hpiiotaform : ∀ i : ℕ, piForm i ∘ₗ iotaForm i = LinearMap.id)
    (hprojsum : ∀ (n : ℕ) (ω : Om n), ∑ i ∈ Finset.range (n + 1), proj n i ω = ω)
    (hnabla : ∀ m : M, completedLTensor p D M (proj 1 1) (nabla m) = nabla m)
    (hprojwedge : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n,
      proj (n + 1) l ∘ₗ wedge n (proj n i ω) ∘ₗ proj 1 1 = 0)
    (hprojbase : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n, proj (n + 1) l (dbase n (proj n i ω)) = 0)
    (hprojhhat : ∀ (n i : ℕ), hhat n ∘ₗ proj (n + 1) i = proj n i ∘ₗ hhat n) :
    ∃ (dL : ∀ i, CompletedTensor p D (OmL i) M →+ CompletedTensor p D (OmL (i + 1)) M)
      (iota' : ∀ i, CompletedTensor p D (OmL i) M →+ CompletedTensor p D (Om i) M)
      (pi' : ∀ i, CompletedTensor p D (Om i) M →+ CompletedTensor p D (OmL i) M)
      (H : ∀ i, CompletedTensor p D (Om (i + 1)) M →+ CompletedTensor p D (Om i) M),
      (∀ (i : ℕ) (x : CompletedTensor p D (OmL i) M), dL (i + 1) (dL i x) = 0) ∧
        (∀ (i : ℕ) (x : CompletedTensor p D (OmL i) M), pi' i (iota' i x) = x) ∧
          (∀ (i : ℕ) (x : CompletedTensor p D (OmL i) M),
              differential p D Om wedge deRham M nabla hleib i (iota' i x) =
                iota' (i + 1) (dL i x)) ∧
            (∀ (i : ℕ) (z : CompletedTensor p D (Om i) M),
                pi' (i + 1) (differential p D Om wedge deRham M nabla hleib i z) =
                  dL i (pi' i z)) ∧
              (∀ x : CompletedTensor p D (Om 0) M,
                  H 0 (differential p D Om wedge deRham M nabla hleib 0 x) +
                    iota' 0 (pi' 0 x) = x) ∧
                ∀ (n : ℕ) (x : CompletedTensor p D (Om (n + 1)) M),
                  differential p D Om wedge deRham M nabla hleib n (H n x) +
                      H (n + 1) (differential p D Om wedge deRham M nabla hleib (n + 1) x) +
                    iota' (n + 1) (pi' (n + 1) x) = x := by
  exact FinitePerturbation.exists_perturbedHomotopyEquiv
    (C := fun i ↦ CompletedTensor p D (Om i) M)
    (L := fun i ↦ CompletedTensor p D (OmL i) M)
    (fun i ↦ (relDifferential p D Om drel M i).toAddMonoidHom)
    (fun i ↦ differential p D Om wedge dbase M nabla hleibBase i)
    (fun i ↦ differential p D Om wedge deRham M nabla hleib i)
    (fun i ↦ completedLTensor p D M (hhat i))
    (fun i ↦ completedLTensor p D M (iotaForm i))
    (fun i ↦ completedLTensor p D M (piForm i))
    (fun i x ↦ differential_eq_relDifferential_add p D Om wedge deRham drel dbase M nabla hleib
      hleibBase hsplit i x)
    (fun i x ↦ DFunLike.congr_fun (hsq i) x)
    (relContraction_zero_comp p D Om OmL drel M hhat iotaForm piForm hcon0form)
    (relContraction_comp p D Om OmL drel M hhat iotaForm piForm hconform)
    (fun i x ↦ differential_relDifferential_cross p D Om wedge deRham drel dbase M nabla hleib
      hleibBase hsplit hdrel hsq i x)
    (fun i y ↦ completedLTensor_comp_eq_zero p D M (hhat (i + 1)) (hhat i) (hhhform i) y)
    (fun i x ↦ completedLTensor_comp_eq_zero p D M (iotaForm (i + 1)) (hhat i) (hhiotaform i) x)
    (fun i y ↦ completedLTensor_comp_eq_zero p D M (hhat i) (piForm i) (hpihform i) y)
    (fun i x ↦ completedLTensor_comp_eq_id p D M (iotaForm i) (piForm i) (hpiiotaform i) x)
    (fun i ↦ i + 2)
    (fun i x ↦ iterate_differential_relHomotopy_eq_zero p D Om wedge dbase M nabla hleibBase
      proj hhat hprojsum hnabla hprojwedge hprojbase hprojhhat i x)

include hleibBase in
/-- **`ĥ` kills the base part of the differential on the image of `1_M ⊗ ψ`.**

This is the hypothesis `hhtiota` of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquivOfInclusion`, derived from the bidegree
bookkeeping together with two further facts about the decomposition: that `ψ` lands in the top
coefficient degree (`hprojiota`), and that in exterior degree `n` there is no coefficient degree
`n + 1` (`hprojtop`).

`1_M ⊗ ψ x` sits in coefficient degree `i`, so by
`Crystalline.CompletedDeRham.completedLTensor_differential_completedLTensor_eq_zero` the base
part of its differential has no component in coefficient degree `l ≤ i`; of the `i + 2`
coefficient degrees available in exterior degree `i + 1` only `i + 1` is left, and `ĥ` carries
that one into coefficient degree `i + 1` of an `i`-form, which is zero. -/
public theorem completedLTensor_hhat_differential_iota_eq_zero (proj : ∀ n _i, Om n →ₗ[D] Om n)
    (hhat : ∀ n, Om (n + 1) →ₗ[D] Om n) (iotaForm : ∀ i, OmL i →ₗ[D] Om i)
    (hprojsum : ∀ (n : ℕ) (ω : Om n), ∑ i ∈ Finset.range (n + 1), proj n i ω = ω)
    (hnabla : ∀ m : M, completedLTensor p D M (proj 1 1) (nabla m) = nabla m)
    (hprojwedge : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n,
      proj (n + 1) l ∘ₗ wedge n (proj n i ω) ∘ₗ proj 1 1 = 0)
    (hprojbase : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n, proj (n + 1) l (dbase n (proj n i ω)) = 0)
    (hprojhhat : ∀ (n i : ℕ), hhat n ∘ₗ proj (n + 1) i = proj n i ∘ₗ hhat n)
    (hprojiota : ∀ i : ℕ, proj i i ∘ₗ iotaForm i = iotaForm i)
    (hprojtop : ∀ n : ℕ, proj n (n + 1) = 0) (i : ℕ) (x : CompletedTensor p D (OmL i) M) :
    completedLTensor p D M (hhat i)
        (differential p D Om wedge dbase M nabla hleibBase i
          (completedLTensor p D M (iotaForm i) x)) = 0 := by
  have hpw : completedLTensor p D M (proj i i) (completedLTensor p D M (iotaForm i) x) =
      completedLTensor p D M (iotaForm i) x := by
    rw [completedLTensor_comp, hprojiota i]
  have hsum := completedLTensor_proj_sum p D Om M proj hprojsum (i + 1)
    (differential p D Om wedge dbase M nabla hleibBase i
      (completedLTensor p D M (iotaForm i) x))
  rw [← hsum, map_sum]
  refine Finset.sum_eq_zero fun l hl ↦ ?_
  rcases Nat.lt_succ_iff_lt_or_eq.1 (Finset.mem_range.1 hl) with hli | rfl
  · have hzero : completedLTensor p D M (proj (i + 1) l)
        (differential p D Om wedge dbase M nabla hleibBase i
          (completedLTensor p D M (iotaForm i) x)) = 0 := by
      rw [← hpw]
      exact completedLTensor_differential_completedLTensor_eq_zero p D Om wedge dbase M nabla
        hleibBase proj hnabla hprojwedge hprojbase i l i (Nat.lt_succ_iff.1 hli) _
    rw [hzero, map_zero]
  · rw [completedLTensor_comp, hprojhhat i (i + 1), hprojtop i, LinearMap.zero_comp]
    exact completedLTensor_zero p D M _

include hleibBase in
/-- **The completed clause of [Stacks, Lemma 60.20.2, Tag 07LD] with the comparison map named.**

`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` quantifies over the comparison `ι'`,
which is a perturbation of `1_M ⊗ ψ`, so its conclusion does not say which map is the homotopy
equivalence.  Under the one extra hypothesis

`ĥ (d_base (1_M ⊗ ψ) x) = 0`,

the perturbation of `1_M ⊗ ψ` is trivial, and the conclusion is about `1_M ⊗ ψ` itself: the
perturbed `π'` is a map of complexes and a retraction of it, and `(1_M ⊗ ψ) π'` is chain
homotopic to the identity.  So `1_M ⊗ ψ` is a homotopy equivalence, and in particular a
quasi-isomorphism, which is the assertion of the source about the canonical comparison of de Rham
complexes.

The extra hypothesis holds for the genuine forms: `1_M ⊗ ψ̂` lands in the top coefficient degree,
`d_base` and the wedge with the coefficient one-form `∇ m` raise it past the exterior degree, and
`ĥ` preserves it, so nothing of that degree survives in `Ω̂^n_{D'}`.  See
`Crystalline.DividedPowerPolynomial.completedLTensor_completedRelativeFormsHomotopy_base_eq_zero`.

The differential `d_L` of `M ⊗̂_D Ω^*_L` is a parameter here, with the hypothesis `hchainform`
that `1_M ⊗ ψ` is a map of complexes for it; that pins it, `1_M ⊗ ψ` being injective, so nothing
is existentially quantified but the homotopy inverse `π'` and the homotopy `H`.  Every other
hypothesis is that of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`. -/
public theorem exists_twistedHomotopyEquivOfInclusion (proj : ∀ n _i, Om n →ₗ[D] Om n)
    (hhat : ∀ n, Om (n + 1) →ₗ[D] Om n) (iotaForm : ∀ i, OmL i →ₗ[D] Om i)
    (piForm : ∀ i, Om i →ₗ[D] OmL i)
    (dL : ∀ i, CompletedTensor p D (OmL i) M →+ CompletedTensor p D (OmL (i + 1)) M)
    (hsplit : ∀ (i : ℕ) (ω : Om i), deRham i ω = drel i ω + dbase i ω)
    (hdrel : ∀ i : ℕ, (drel (i + 1)).comp (drel i) = 0)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hcon0form : hhat 0 ∘ₗ drel 0 + iotaForm 0 ∘ₗ piForm 0 = LinearMap.id)
    (hconform : ∀ n : ℕ, drel n ∘ₗ hhat n + hhat (n + 1) ∘ₗ drel (n + 1) +
      iotaForm (n + 1) ∘ₗ piForm (n + 1) = LinearMap.id)
    (hhhform : ∀ i : ℕ, hhat i ∘ₗ hhat (i + 1) = 0)
    (hhiotaform : ∀ i : ℕ, hhat i ∘ₗ iotaForm (i + 1) = 0)
    (hpihform : ∀ i : ℕ, piForm i ∘ₗ hhat i = 0)
    (hpiiotaform : ∀ i : ℕ, piForm i ∘ₗ iotaForm i = LinearMap.id)
    (hprojsum : ∀ (n : ℕ) (ω : Om n), ∑ i ∈ Finset.range (n + 1), proj n i ω = ω)
    (hnabla : ∀ m : M, completedLTensor p D M (proj 1 1) (nabla m) = nabla m)
    (hprojwedge : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n,
      proj (n + 1) l ∘ₗ wedge n (proj n i ω) ∘ₗ proj 1 1 = 0)
    (hprojbase : ∀ (n l i : ℕ), l ≤ i → ∀ ω : Om n, proj (n + 1) l (dbase n (proj n i ω)) = 0)
    (hprojhhat : ∀ (n i : ℕ), hhat n ∘ₗ proj (n + 1) i = proj n i ∘ₗ hhat n)
    (hhtiota : ∀ (i : ℕ) (x : CompletedTensor p D (OmL i) M),
      completedLTensor p D M (hhat i)
        (differential p D Om wedge dbase M nabla hleibBase i
          (completedLTensor p D M (iotaForm i) x)) = 0)
    (hchainform : ∀ (i : ℕ) (x : CompletedTensor p D (OmL i) M),
      differential p D Om wedge deRham M nabla hleib i
          (completedLTensor p D M (iotaForm i) x) =
        completedLTensor p D M (iotaForm (i + 1)) (dL i x)) :
    ∃ (pi' : ∀ i, CompletedTensor p D (Om i) M →+ CompletedTensor p D (OmL i) M)
      (H : ∀ i, CompletedTensor p D (Om (i + 1)) M →+ CompletedTensor p D (Om i) M),
      (∀ (i : ℕ) (x : CompletedTensor p D (OmL i) M),
          pi' i (completedLTensor p D M (iotaForm i) x) = x) ∧
        (∀ (i : ℕ) (z : CompletedTensor p D (Om i) M),
            pi' (i + 1) (differential p D Om wedge deRham M nabla hleib i z) =
              dL i (pi' i z)) ∧
          (∀ x : CompletedTensor p D (Om 0) M,
              H 0 (differential p D Om wedge deRham M nabla hleib 0 x) +
                completedLTensor p D M (iotaForm 0) (pi' 0 x) = x) ∧
            ∀ (n : ℕ) (x : CompletedTensor p D (Om (n + 1)) M),
              differential p D Om wedge deRham M nabla hleib n (H n x) +
                  H (n + 1) (differential p D Om wedge deRham M nabla hleib (n + 1) x) +
                completedLTensor p D M (iotaForm (n + 1)) (pi' (n + 1) x) = x := by
  exact FinitePerturbation.exists_homotopyEquivOfInclusion_of_chainMap
    (C := fun i ↦ CompletedTensor p D (Om i) M)
    (L := fun i ↦ CompletedTensor p D (OmL i) M)
    (fun i ↦ (relDifferential p D Om drel M i).toAddMonoidHom)
    (fun i ↦ differential p D Om wedge dbase M nabla hleibBase i)
    (fun i ↦ differential p D Om wedge deRham M nabla hleib i)
    (fun i ↦ completedLTensor p D M (hhat i))
    (fun i ↦ completedLTensor p D M (iotaForm i))
    (fun i ↦ completedLTensor p D M (piForm i)) dL
    (fun i x ↦ differential_eq_relDifferential_add p D Om wedge deRham drel dbase M nabla hleib
      hleibBase hsplit i x)
    (fun i x ↦ DFunLike.congr_fun (hsq i) x)
    (relContraction_zero_comp p D Om OmL drel M hhat iotaForm piForm hcon0form)
    (relContraction_comp p D Om OmL drel M hhat iotaForm piForm hconform)
    (fun i x ↦ differential_relDifferential_cross p D Om wedge deRham drel dbase M nabla hleib
      hleibBase hsplit hdrel hsq i x)
    (fun i y ↦ completedLTensor_comp_eq_zero p D M (hhat (i + 1)) (hhat i) (hhhform i) y)
    (fun i x ↦ completedLTensor_comp_eq_zero p D M (iotaForm (i + 1)) (hhat i) (hhiotaform i) x)
    (fun i y ↦ completedLTensor_comp_eq_zero p D M (hhat i) (piForm i) (hpihform i) y)
    (fun i x ↦ completedLTensor_comp_eq_id p D M (iotaForm i) (piForm i) (hpiiotaform i) x)
    hhtiota hchainform
    (fun i ↦ i + 2)
    (fun i x ↦ iterate_differential_relHomotopy_eq_zero p D Om wedge dbase M nabla hleibBase
      proj hhat hprojsum hnabla hprojwedge hprojbase hprojhhat i x)

end TwistedRetract

end CompletedDeRham

end Crystalline

end
