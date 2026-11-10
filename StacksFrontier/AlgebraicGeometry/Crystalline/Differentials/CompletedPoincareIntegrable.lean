module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZeroFinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsUnitZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential

/-!
# The completed divided power Poincaré lemma for an integrable connection

[Stacks, Lemma 60.19.2, Tag 07LD] has two clauses; the one over the `p`-adic completions — for a
`D`-module `M` with an integrable connection `∇ : M → M ⊗̂_D Ω̂¹_D`, the comparison
`M ⊗̂_D Ω̂^*_D → M ⊗̂_D Ω̂^*_{D'}` is a quasi-isomorphism — is
`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/CompletedPoincareCurvature.lean`, for
integrability in the sense of [Stacks, Tag 07I0].  This module proves the homotopy equivalence
behind it, `Crystalline.DividedPowerPolynomial.exists_homotopyEquiv_pushedConnection`, and its
form for a connection given in finitely many coordinates,
`Crystalline.DividedPowerPolynomial.exists_homotopyEquiv_isIntegrable`.

The first statement asks for the square-zero identity
`Crystalline.CompletedDeRham.IsSquareZero` of the twisted differential on `M ⊗̂_D Ω̂^*_{D'}`.  The
second derives it from integrability in coordinates, [Stacks, Tag 07JD], for finitely many
coordinates.

The source's map is the canonical comparison of de Rham complexes, so the statement has to name
it: the perturbation argument of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` produces a comparison existentially,
as a perturbation of `1_M ⊗ ψ̂`, and a differential on `M ⊗̂_D Ω̂^*_D` with it.  Both are pinned
here.  The perturbation of `1_M ⊗ ψ̂` is trivial because `ψ̂` lands in the top coefficient degree
while the base differential raises it past the exterior degree, and the differential is then
pinned by `1_M ⊗ ψ̂` being an injective map of complexes for the de Rham differential of
`M ⊗̂_D Ω̂^*_D` itself.  So the conclusion below is about the two genuine complexes and the
canonical map between them.

## How the square-zero identity is derived

`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` derives it from integrability together
with the exterior identities `Crystalline.CompletedDeRham.IsGradedExterior` of the family of
forms, a coordinate expansion `∇ m = Σ_j θ_j m ⊗ d x_j`, and closedness of the coordinate
differentials.  All three of the extra inputs are available at the genuine forms:

* the exterior identities are
  `Crystalline.isGradedExterior_completedDividedPower` for the divided power polynomial algebra
  `P`, read over `D` rather than over `D'` — that is
  `Crystalline.DividedPowerPolynomial.isGradedExterior_completedPolynomialForms`, the wedge
  product and the de Rham differential being literally the same maps;
* the coordinate expansion of the pushed connection is the coordinate expansion of `∇` itself
  carried along `ψ̂`, by
  `Crystalline.CompletedDeRham.isFiniteCoordinateExpansion_pushforwardConnection`, and the
  coordinate differentials of `D` go to those of `D'` because `ψ̂` carries the universal
  differential of `D` to that of `D'`
  (`Crystalline.DividedPowerPolynomial.completedCoefficientFormsMapₗ_completedFormsDifferential`);
* closedness is `Crystalline.deRham_completedFormsDifferential`, that an exact one-form of a
  completed divided power ring is closed, applied in `D'`.  This is why the coordinates are taken
  to be differentials `d x_j` of elements `x_j` of `D` and not arbitrary one-forms: for exact
  one-forms closedness is a theorem rather than a hypothesis.

Integrability enters as `Crystalline.IsIntegrable` for `∇` itself, on the forms of `D`, which is
where the source puts it.  It is used through the family of coordinate operators at hand:
`Crystalline.CompletedDeRham.isSquareZero_of_commute` is
`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` with integrability replaced by the
commutation of the one family of operators that the expansion provides, which is all the
computation uses and which is what the connection on `D'` inherits from the connection on `D`.

## The coordinates

`Crystalline.IsCoordinateExpansion` — the existence of coordinate operators for a finite family
of coordinates of `D` — is a hypothesis of the theorems below, and it is not one of the source's.
It comes from `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable`, whose computation of
`∇²` substitutes the expansion twice and cancels the term `(j, k)` against the term `(k, j)`; the
data the carried family of forms comes with — a wedge product `Ωⁱ × Ω¹ → Ω^{i+1}` by one-forms
only — cannot express the curvature `∇² : M → M ⊗̂ Ω²` wedged with a form of degree `i`, which is
what a coordinate-free derivation would need.  It is the hypothesis under which this library
derives the square-zero identity everywhere, including in
`Crystalline.CompletedDeRham.complexOfIsIntegrable`, and it holds in the situation
[Stacks, Proposition 60.21.3, Tag 07LG] applies this lemma in: there `D` is the `p`-adic
completion of the divided power envelope of a polynomial algebra on a finite presentation and the
coordinates are its variables, a pair's worth of data recorded in the field
`Crystalline.Pair.hasCoordinateOperators`.

## Main results

* `Crystalline.CompletedDeRham.isSquareZero_of_commute` — the square-zero identity from the
  commutation of one family of coordinate operators.
* `Crystalline.CompletedDeRham.isFiniteCoordinateExpansion_pushforwardConnection` — a finite
  coordinate expansion is carried along a pushforward of the connection.
* `Crystalline.DividedPowerPolynomial.isGradedExterior_completedPolynomialForms` — the exterior
  identities of `Ω̂^*_{D'}`, read over `D`.
* `Crystalline.DividedPowerPolynomial.isSquareZero_pushedConnection` and
  `..._isSquareZero_completedDividedPowerForms` — **the two twisted de Rham differentials square
  to zero**, that of `M ⊗̂_D Ω̂^*_{D'}` for the connection of `M` pushed in from `Ω̂¹_D` and that
  of `M ⊗̂_D Ω̂^*_D` for the connection itself, from integrability.
* `Crystalline.DividedPowerPolynomial.moduleCoefficientFormsMap` — **the canonical comparison
  `1_M ⊗ ψ̂`** of the two complexes, and
  `..._polynomialDeRhamDifferential_moduleCoefficientFormsMap`, that it is a map of complexes.
* `Crystalline.DividedPowerPolynomial.exists_homotopyEquiv_isIntegrable` — for a `D`-module `M`
  with a connection `∇ : M → M ⊗̂_D Ω̂¹_D` integrable in finitely many coordinates, the canonical
  comparison
  `1_M ⊗ ψ̂ : M ⊗̂_D Ω̂^*_D → M ⊗̂_D Ω̂^*_{D'}` is a homotopy equivalence of the twisted de Rham
  complexes, with an explicit homotopy inverse.

## References

* [Stacks Project, Lemma 60.20.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u v v₁ w uI uA uB uW uM

namespace Crystalline

namespace CompletedDeRham

/-! ### The square-zero identity from the commutation of one family of operators -/

section Commute

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap) {ι : Type uI} (dx : ι → Om 1)
  (theta : ι → (M → M)) (s : Finset ι)

/-- **`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` with integrability replaced by
the commutation of the family of coordinate operators at hand.**

`Crystalline.IsIntegrable` asks that *every* family of operators realizing the expansion commute,
and the proof of the square-zero identity uses that for the single family `theta` the expansion
`hexp` names.  This is the same theorem with that single commutation as the hypothesis, which is
what a connection pushed along a map of the forms inherits: the pushed connection is expanded by
the same operators, while its own `Crystalline.IsIntegrable` quantifies over operators of the
larger module of forms and is not available.

Every other hypothesis is unchanged; see
`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` for what they are. -/
theorem isSquareZero_of_commute (hext : IsGradedExterior D Om wedge deRham)
    (hexp : IsFiniteCoordinateExpansion p D (Om 1) dx nabla theta s)
    (hdx : ∀ j, deRham 1 (dx j) = 0)
    (hcomm : ∀ j k, theta j ∘ theta k = theta k ∘ theta j) :
    IsSquareZero p D Om wedge deRham M nabla hleib := by
  intro i
  refine AddMonoidHom.ext fun x ↦ ?_
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective
    ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Om i)) (x.val n)
  have hxz : x.val n = (toCompletedTensor p D (Om i) M z).val n := hz.symm
  rw [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, AdicCompletion.val_zero_apply,
    differential_val_congr p D Om wedge deRham M nabla hleib (i + 1) n _ _
      (differential_val_congr p D Om wedge deRham M nabla hleib i n x _ hxz),
    differential_differential_toCompletedTensor p D Om wedge deRham M nabla hleib dx theta s
      hext hexp hdx hcomm i z, AdicCompletion.val_zero_apply]

end Commute

/-! ### A finite coordinate expansion travels along a pushforward of the connection -/

section Pushforward

variable (p : ℕ) (D : Type u) [CommRing D] (M : Type w) [AddCommGroup M] [Module D M]
  {X : Type v} {Y : Type v₁} [AddCommGroup X] [Module D X] [AddCommGroup Y] [Module D Y]
  {ι : Type uI}

/-- **A finite coordinate expansion is carried along a pushforward of the connection.**

If `∇ m = Σ_{j ∈ s} θ_j m ⊗ d x_j` in `M ⊗̂_D X` and `f : X → Y` carries `d x_j` to `d y_j`, then
the pushed connection `Crystalline.CompletedDeRham.pushforwardConnection` is expanded by the same
operators `θ_j` in the coordinates `d y_j`.  `1_M ⊗ f` is additive and takes the image of a pure
tensor to the image of a pure tensor, which is the whole proof. -/
theorem isFiniteCoordinateExpansion_pushforwardConnection (f : X →ₗ[D] Y) {dX : D → X}
    {dY : D → Y} (hf : ∀ c : D, f (dX c) = dY c) (nabla : CompletedConnection p D X dX M)
    {dx : ι → X} {dy : ι → Y} (hdxy : ∀ j, f (dx j) = dy j) (theta : ι → (M → M))
    (s : Finset ι) (hexp : IsFiniteCoordinateExpansion p D X dx nabla theta s) :
    IsFiniteCoordinateExpansion p D Y dy (pushforwardConnection p D M f hf nabla) theta s where
  sum_eq m := by
    rw [pushforwardConnection_apply, hexp.sum_eq m, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [completedLTensor_toCompletedTensor_tmul, hdxy]
  eq_zero_of_notMem j hj m := by
    rw [← hdxy j, ← completedLTensor_toCompletedTensor_tmul,
      hexp.eq_zero_of_notMem j hj m, map_zero]

end Pushforward

end CompletedDeRham

namespace DividedPowerPolynomial

/-! ### The exterior identities of the completed forms of `D'`, read over `D` -/

section Exterior

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  (p : ℕ)

/-- **The exterior identities of `Ω̂^*_{D'}`, read over `D`**: the de Rham differential squares to
zero, the wedge product is alternating on one-forms, and the graded Leibniz rule holds against a
closed one-form.

This is `Crystalline.isGradedExterior_completedDividedPower` for the divided power polynomial
algebra `P = B⟨x_w : w ∈ W⟩`.  The three identities are equations between elements of
`Ω̂^*_{D'}`, and the `D`-bilinear wedge product
`Crystalline.DividedPowerPolynomial.completedPolynomialFormsWedge` is the `D'`-bilinear one with
its ring of bilinearity restricted along `D → D'` and the same underlying function, by
`Crystalline.DividedPowerPolynomial.completedPolynomialFormsWedge_apply`, so the equations are
the same equations. -/
theorem isGradedExterior_completedPolynomialForms :
    CompletedDeRham.IsGradedExterior (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
      (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) where
  deRham_deRham := (isGradedExterior_completedDividedPower p A
    (setIndexedDividedPowerPolynomialDividedPowers B W)).deRham_deRham
  wedge_self := (isGradedExterior_completedDividedPower p A
    (setIndexedDividedPowerPolynomialDividedPowers B W)).wedge_self
  deRham_wedge := (isGradedExterior_completedDividedPower p A
    (setIndexedDividedPowerPolynomialDividedPowers B W)).deRham_wedge

end Exterior

/-! ### The comparison `ψ̂` of the two families of completed forms -/

section Comparison

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  (p : ℕ)

/-- **`ψ̂` respects the wedge product**: `ψ̂ (ω ∧ η) = ψ̂ ω ∧ ψ̂ η`, with the wedge of `Ω̂^*_{D'}`
read `D`-bilinearly.

`Crystalline.DividedPowerPolynomial.completedCoefficientFormsMap` *is*
`Crystalline.completedMapDifferentialForms` at the coefficient inclusion, so this is
`Crystalline.completedMapDifferentialForms_wedge`; only the two re-readings of the maps — `ψ̂` as
`D`-linear and the wedge as `D`-bilinear — have to be unwound, and both leave the underlying
function alone. -/
theorem completedCoefficientFormsMapₗ_completedDividedPowerWedge (i : ℕ)
    (omega : completedDividedPowerForms p A B.dividedPowers i)
    (eta : completedDividedPowerForms p A B.dividedPowers 1) :
    completedCoefficientFormsMapₗ A B W p (i + 1)
        (completedDividedPowerWedge p A B.dividedPowers i omega eta) =
      completedPolynomialFormsWedge A B W p i (completedCoefficientFormsMapₗ A B W p i omega)
        (completedCoefficientFormsMapₗ A B W p 1 eta) := by
  have h := completedMapDifferentialForms_wedge p A B.dividedPowers
    (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
    (coefficientAlgHom_isDPMorphism A B W) i omega eta
  simp only [completedCoefficientFormsMapₗ_apply]
  exact h

/-- **`ψ̂` is a map of de Rham complexes**: `ψ̂ (d ω) = d (ψ̂ ω)` in every degree.  This is
`Crystalline.completedMapDifferentialForms_deRham` at the coefficient inclusion. -/
theorem completedCoefficientFormsMapₗ_completedDividedPowerDeRham (i : ℕ)
    (omega : completedDividedPowerForms p A B.dividedPowers i) :
    completedCoefficientFormsMapₗ A B W p (i + 1)
        (completedDividedPowerDeRham p A B.dividedPowers i omega) =
      completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W) i
        (completedCoefficientFormsMapₗ A B W p i omega) := by
  rw [completedCoefficientFormsMapₗ_apply, completedCoefficientFormsMapₗ_apply]
  exact completedMapDifferentialForms_deRham p A B.dividedPowers
    (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
    (coefficientAlgHom_isDPMorphism A B W) i omega

/-- **Above the exterior degree there is no coefficient degree to project onto**, after
completion: `π̂_{n, n+1} = 0` on `Ω̂^n_{D'}`.  The completion of the zero map is zero, and the
uncompleted projection is zero by
`Crystalline.DividedPowerPolynomial.formsBidegreeProjection_of_lt`. -/
theorem completedFormsBidegreeProjectionₗ_eq_zero (n : ℕ) :
    completedFormsBidegreeProjectionₗ A B W p n (n + 1) = 0 := by
  have h0 : (formsBidegreeProjection A B W n (n + 1)).toAddMonoidHom = 0 := by
    rw [formsBidegreeProjection_of_lt A B W (Nat.lt_succ_self n)]
    rfl
  refine LinearMap.ext fun z ↦ ?_
  rw [LinearMap.zero_apply]
  change PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
      (setIndexedDividedPowerPolynomialAlgebra B W)
      (formsBidegreeProjection A B W n (n + 1)).toAddMonoidHom z = 0
  rw [h0, PAdicCompletion.mapAddHom_zero, AddMonoidHom.zero_apply]

end Comparison

/-! ### The two twisted de Rham complexes, and the canonical comparison between them -/

section Inclusion

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  (p : ℕ) [LinearOrder W]

/-- **The de Rham differential of `M ⊗̂_D Ω̂^*_D` twisted by a connection of `M`**, that is
`Crystalline.CompletedDeRham.differential` at the genuine completed divided power forms of `D`:
`∇(m ⊗ ω) = ∇ m ∧ ω + m ⊗ d ω`.  The Leibniz rule it needs of the forms is
`Crystalline.isGradedLeibniz_completedDividedPower`; the name abbreviates nothing else. -/
def coefficientDeRhamDifferential (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M) (i : ℕ) :
    CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedDividedPowerForms p A B.dividedPowers i) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedDividedPowerForms p A B.dividedPowers (i + 1)) M :=
  CompletedDeRham.differential p (completedDividedPowerRing p (B := (B : Type uB)))
    (completedDividedPowerForms p A B.dividedPowers)
    (completedDividedPowerWedge p A B.dividedPowers)
    (completedDividedPowerDeRham p A B.dividedPowers) M nabla
    (isGradedLeibniz_completedDividedPower p A B.dividedPowers) i

/-- **The de Rham differential of `M ⊗̂_D Ω̂^*_{D'}` twisted by a connection of `M` with values in
the forms of `D'`**, that is `Crystalline.CompletedDeRham.differential` at the genuine completed
divided power forms of `D' = B⟨x_w⟩^∧`, read over `D`.  The Leibniz rule it needs of the forms is
`Crystalline.DividedPowerPolynomial.isGradedLeibniz_completedPolynomialForms`; the name
abbreviates nothing else. -/
def polynomialDeRhamDifferential (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p 1)
      (completedPolynomialFormsDifferential A B W p) M) (i : ℕ) :
    CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedPolynomialForms A B W p i) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedPolynomialForms A B W p (i + 1)) M :=
  CompletedDeRham.differential p (completedDividedPowerRing p (B := (B : Type uB)))
    (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M nabla
    (isGradedLeibniz_completedPolynomialForms A B W p) i

/-- **The canonical comparison `M ⊗̂_D Ω̂^i_D → M ⊗̂_D Ω̂^i_{D'}`**, that is `1_M ⊗ ψ̂`: the map of
[Stacks, Lemma 60.20.2, Tag 07LD] whose being a quasi-isomorphism is the assertion of the source's
second clause.  Nothing is added to `Crystalline.CompletedDeRham.completedLTensor` of the
`D`-linear comparison `ψ̂` of the forms; the name is here so that the statements below say which
map they are about. -/
def moduleCoefficientFormsMap (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M] (i : ℕ) :
    CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedDividedPowerForms p A B.dividedPowers i) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedPolynomialForms A B W p i) M :=
  CompletedDeRham.completedLTensor p (completedDividedPowerRing p (B := (B : Type uB))) M
    (completedCoefficientFormsMapₗ A B W p i)

/-- **`1_M ⊗ ψ̂` is a map of the twisted de Rham complexes**: it carries the de Rham differential
of `M ⊗̂_D Ω̂^*_D` to that of `M ⊗̂_D Ω̂^*_{D'}`, the connection of the target being the connection
of `M` pushed in along `ψ̂`.

This is `Crystalline.CompletedDeRham.differential_completedLTensor` at `ψ̂`, whose three
compatibilities are
`Crystalline.DividedPowerPolynomial.completedCoefficientFormsMapₗ_completedFormsDifferential`,
`..._completedCoefficientFormsMapₗ_completedDividedPowerWedge` and
`..._completedCoefficientFormsMapₗ_completedDividedPowerDeRham`. -/
theorem polynomialDeRhamDifferential_moduleCoefficientFormsMap (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M) (i : ℕ)
    (z : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers i) M) :
    polynomialDeRhamDifferential A B W p M (pushedConnection A B W p M nabla) i
        (moduleCoefficientFormsMap A B W p M i z) =
      moduleCoefficientFormsMap A B W p M (i + 1)
        (coefficientDeRhamDifferential A B p M nabla i z) :=
  CompletedDeRham.differential_completedLTensor p (completedDividedPowerRing p (B := (B : Type uB)))
    (completedDividedPowerForms p A B.dividedPowers) (completedPolynomialForms A B W p)
    (completedDividedPowerWedge p A B.dividedPowers) (completedPolynomialFormsWedge A B W p)
    (completedDividedPowerDeRham p A B.dividedPowers)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M nabla
    (isGradedLeibniz_completedDividedPower p A B.dividedPowers)
    (isGradedLeibniz_completedPolynomialForms A B W p) (completedCoefficientFormsMapₗ A B W p)
    (completedCoefficientFormsMapₗ_completedFormsDifferential A B W p)
    (completedCoefficientFormsMapₗ_completedDividedPowerWedge A B W p)
    (completedCoefficientFormsMapₗ_completedDividedPowerDeRham A B W p) i z

end Inclusion

/-! ### The two differentials square to zero, from integrability -/

section SquareZero

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  (p : ℕ) [LinearOrder W]

/-- **The twisted de Rham differential of `M ⊗̂_D Ω̂^*_{D'}` squares to zero**, for the connection
of a `D`-module `M` pushed into the forms of `D'` along `ψ̂`, given that the connection is
integrable and expanded by coordinate operators in finitely many coordinates of `D`.

This is the hypothesis `hsq` of
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_pushedConnection`, discharged.
Its three inputs beyond integrability are all theorems here: the exterior identities are
`Crystalline.DividedPowerPolynomial.isGradedExterior_completedPolynomialForms`; the pushed
connection is expanded in the coordinates `d x_j` read in `Ω̂¹_{D'}`, by
`Crystalline.CompletedDeRham.isFiniteCoordinateExpansion_pushforwardConnection` together with
`Crystalline.DividedPowerPolynomial.completedCoefficientFormsMapₗ_completedFormsDifferential`;
and those coordinate differentials are closed because they are exact, by
`Crystalline.deRham_completedFormsDifferential`.

Integrability is used for the family `theta` that `hco` names, through
`Crystalline.CompletedDeRham.isSquareZero_of_commute`: the operators of `∇` on `Ω̂¹_D` are the
operators of the pushed connection on `Ω̂¹_{D'}`, so their commutation is what is inherited. -/
theorem isSquareZero_pushedConnection (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M)
    {iota : Type uI} [Finite iota]
    (x : iota → completedDividedPowerRing p (B := (B : Type uB))) (theta : iota → (M → M))
    (hco : IsCoordinateExpansion p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (fun j ↦ completedFormsDifferential p A B.dividedPowers (x j)) nabla theta)
    (hint : IsIntegrable p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (fun j ↦ completedFormsDifferential p A B.dividedPowers (x j)) nabla) :
    CompletedDeRham.IsSquareZero p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
      (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M
      (pushedConnection A B W p M nabla)
      (isGradedLeibniz_completedPolynomialForms A B W p) := by
  have := Fintype.ofFinite iota
  exact CompletedDeRham.isSquareZero_of_commute p
    (completedDividedPowerRing p (B := (B : Type uB)))
    (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M
    (pushedConnection A B W p M nabla) (isGradedLeibniz_completedPolynomialForms A B W p)
    (fun j ↦ completedPolynomialFormsDifferential A B W p (x j)) theta Finset.univ
    (isGradedExterior_completedPolynomialForms A B W p)
    (CompletedDeRham.isFiniteCoordinateExpansion_pushforwardConnection p
      (completedDividedPowerRing p (B := (B : Type uB))) M
      (completedCoefficientFormsMapₗ A B W p 1)
      (completedCoefficientFormsMapₗ_completedFormsDifferential A B W p) nabla
      (fun j ↦ completedCoefficientFormsMapₗ_completedFormsDifferential A B W p (x j)) theta
      Finset.univ
      (isFiniteCoordinateExpansion_univ_of_isCoordinateExpansion p
        (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers 1) hco))
    (fun j ↦ deRham_completedFormsDifferential p A
      (setIndexedDividedPowerPolynomialDividedPowers B W)
      (completedCoefficientRingHom A B W p (x j)))
    (hint theta hco)

/-- **The twisted de Rham differential of `M ⊗̂_D Ω̂^*_D` squares to zero**, from integrability of
the connection, the coordinates being finite in number.

This is `Crystalline.CompletedDeRham.isSquareZero_of_commute` at the genuine completed divided
power forms of `D`: the exterior identities are
`Crystalline.isGradedExterior_completedDividedPower`, the expansion is the given one read as a
finite sum over `Finset.univ` by
`Crystalline.isFiniteCoordinateExpansion_univ_of_isCoordinateExpansion`, and the coordinate
differentials are closed because they are exact, by
`Crystalline.deRham_completedFormsDifferential`. -/
theorem isSquareZero_completedDividedPowerForms (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M)
    {iota : Type uI} [Finite iota] (x : iota → (completedDividedPowerRing p (B := (B : Type uB))))
    (theta : iota → (M → M))
    (hco : IsCoordinateExpansion p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (fun j ↦ completedFormsDifferential p A B.dividedPowers (x j)) nabla theta)
    (hint : IsIntegrable p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (fun j ↦ completedFormsDifferential p A B.dividedPowers (x j)) nabla) :
    CompletedDeRham.IsSquareZero p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers)
      (completedDividedPowerWedge p A B.dividedPowers)
      (completedDividedPowerDeRham p A B.dividedPowers) M nabla
      (isGradedLeibniz_completedDividedPower p A B.dividedPowers) := by
  have := Fintype.ofFinite iota
  exact CompletedDeRham.isSquareZero_of_commute p
    (completedDividedPowerRing p (B := (B : Type uB)))
    (completedDividedPowerForms p A B.dividedPowers)
    (completedDividedPowerWedge p A B.dividedPowers)
    (completedDividedPowerDeRham p A B.dividedPowers) M nabla
    (isGradedLeibniz_completedDividedPower p A B.dividedPowers)
    (fun j ↦ completedFormsDifferential p A B.dividedPowers (x j)) theta Finset.univ
    (isGradedExterior_completedDividedPower p A B.dividedPowers)
    (isFiniteCoordinateExpansion_univ_of_isCoordinateExpansion p
      (completedDividedPowerRing p (B := (B : Type uB)))
          (completedDividedPowerForms p A B.dividedPowers 1) hco)
    (fun j ↦ deRham_completedFormsDifferential p A B.dividedPowers (x j)) (hint theta hco)

end SquareZero

/-! ### The completed clause of the divided power Poincaré lemma -/

section Poincare

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  (p : ℕ) [LinearOrder W]

/-- **The canonical comparison is a homotopy equivalence of the two twisted de Rham
complexes.**

This is `Crystalline.CompletedDeRham.exists_twistedHomotopyEquivOfInclusion` instantiated at the
genuine completed divided power forms, as
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_completedPolynomialForms`
instantiates the version whose comparison map and target differential are existentially
quantified.  Its two extra hypotheses are discharged here: that `ĥ` kills the base part of the
differential on the image of `1_M ⊗ ψ̂`, by
`Crystalline.CompletedDeRham.completedLTensor_hhat_differential_iota_eq_zero` from
`..._completedFormsBidegreeProjectionₗ_comp_completedCoefficientFormsMapₗ` and
`..._completedFormsBidegreeProjectionₗ_eq_zero`; and that `1_M ⊗ ψ̂` is a map of complexes for the
de Rham differential of `M ⊗̂_D Ω̂^*_D`, which is
`..._polynomialDeRhamDifferential_moduleCoefficientFormsMap`.  The second is what makes the
differential of the source complex the genuine one rather than an unspecified differential.

So `1_M ⊗ ψ̂` has a homotopy inverse `π'`: a map of complexes with `π' (1_M ⊗ ψ̂) = 1` and
`(1_M ⊗ ψ̂) π'` chain homotopic to the identity by `H`.  The one hypothesis carried is the
vanishing of the curvature of the pushed connection, discharged from integrability in
`Crystalline.DividedPowerPolynomial.exists_homotopyEquiv_isIntegrable`. -/
theorem exists_homotopyEquiv_pushedConnection (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M)
    (hsq : CompletedDeRham.IsSquareZero p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
      (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M
      (pushedConnection A B W p M nabla)
      (isGradedLeibniz_completedPolynomialForms A B W p)) :
    ∃ (pi' : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p i) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedDividedPowerForms p A B.dividedPowers i) M)
      (H : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedPolynomialForms A B W p (i + 1)) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedPolynomialForms A B W p i) M),
      (∀ (i : ℕ) (z : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedDividedPowerForms p A B.dividedPowers i) M),
          pi' i (moduleCoefficientFormsMap A B W p M i z) = z) ∧
        (∀ (i : ℕ) (w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p i) M),
            pi' (i + 1) (polynomialDeRhamDifferential A B W p M
                (pushedConnection A B W p M nabla) i w) =
              coefficientDeRhamDifferential A B p M nabla i (pi' i w)) ∧
          (∀ w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
              (completedPolynomialForms A B W p 0) M,
              H 0 (polynomialDeRhamDifferential A B W p M
                  (pushedConnection A B W p M nabla) 0 w) +
                moduleCoefficientFormsMap A B W p M 0 (pi' 0 w) = w) ∧
            ∀ (n : ℕ) (w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                (completedPolynomialForms A B W p (n + 1)) M),
              polynomialDeRhamDifferential A B W p M
                    (pushedConnection A B W p M nabla) n (H n w) +
                  H (n + 1) (polynomialDeRhamDifferential A B W p M
                    (pushedConnection A B W p M nabla) (n + 1) w) +
                moduleCoefficientFormsMap A B W p M (n + 1) (pi' (n + 1) w) = w := by
  refine CompletedDeRham.exists_twistedHomotopyEquivOfInclusion p
    (completedDividedPowerRing p (B := (B : Type uB))) (completedPolynomialForms A B W p)
    (completedDividedPowerForms p A B.dividedPowers) (completedPolynomialFormsWedge A B W p)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W))
    (completedFormsRelDifferentialₗ A B W p) (completedFormsBaseDifferential A B W p) M
    (pushedConnection A B W p M nabla)
    (isGradedLeibniz_completedPolynomialForms A B W p)
    (isGradedLeibniz_completedFormsBaseDifferential A B W p)
    (completedFormsBidegreeProjectionₗ A B W p) (completedRelativeFormsHomotopyₗ A B W p)
    (completedCoefficientFormsMapₗ A B W p) (completedRelativeFormsRetractionₗ A B W p)
    (coefficientDeRhamDifferential A B p M nabla)
    (completedDividedPowerDeRham_eq_completedFormsRelDifferential_add A B W p)
    (fun i ↦ LinearMap.ext
        (completedFormsRelDifferential_completedFormsRelDifferential A B W p i))
    hsq ?_ ?_
    (fun i ↦ LinearMap.ext
        (completedRelativeFormsHomotopy_completedRelativeFormsHomotopy A B W p i))
    (fun i ↦ LinearMap.ext fun z ↦
      (congrArg (fun w : completedPolynomialForms A B W p (i + 1) ↦
          completedRelativeFormsHomotopyₗ A B W p i w)
        (completedCoefficientFormsMapₗ_apply A B W p (i + 1) z)).trans
        (completedRelativeFormsHomotopy_completedCoefficient A B W p i z))
    (fun i ↦ LinearMap.ext
        (completedRelativeFormsRetraction_completedRelativeFormsHomotopy A B W p i))
    (fun i ↦ LinearMap.ext fun z ↦
      (congrArg (fun w : completedPolynomialForms A B W p i ↦
          completedRelativeFormsRetractionₗ A B W p i w)
        (completedCoefficientFormsMapₗ_apply A B W p i z)).trans
        (completedRelativeFormsRetraction_completedCoefficient A B W p i z))
    (completedFormsBidegreeProjection_sum A B W p)
    (completedLTensor_pushedConnection A B W p M nabla)
    (fun n l i hli omega ↦ LinearMap.ext
        (completedFormsBidegreeProjection_wedge_eq_zero A B W p n l i hli omega))
    (fun n l i hli omega ↦
      completedFormsBidegreeProjection_completedFormsBaseDifferential_eq_zero A B W p n hli omega)
    (fun n i ↦ LinearMap.ext
        (completedRelativeFormsHomotopy_completedFormsBidegreeProjection A B W p n i))
    (fun i x ↦ CompletedDeRham.completedLTensor_hhat_differential_iota_eq_zero p
      (completedDividedPowerRing p (B := (B : Type uB))) (completedPolynomialForms A B W p)
      (completedDividedPowerForms p A B.dividedPowers) (completedPolynomialFormsWedge A B W p)
      (completedFormsBaseDifferential A B W p) M (pushedConnection A B W p M nabla)
      (isGradedLeibniz_completedFormsBaseDifferential A B W p)
      (completedFormsBidegreeProjectionₗ A B W p) (completedRelativeFormsHomotopyₗ A B W p)
      (completedCoefficientFormsMapₗ A B W p)
      (completedFormsBidegreeProjection_sum A B W p)
      (completedLTensor_pushedConnection A B W p M nabla)
      (fun n l j hlj omega ↦ LinearMap.ext
        (completedFormsBidegreeProjection_wedge_eq_zero A B W p n l j hlj omega))
      (fun n l j hlj omega ↦
        completedFormsBidegreeProjection_completedFormsBaseDifferential_eq_zero A B W p n hlj
          omega)
      (fun n j ↦ LinearMap.ext
        (completedRelativeFormsHomotopy_completedFormsBidegreeProjection A B W p n j))
      (completedFormsBidegreeProjectionₗ_comp_completedCoefficientFormsMapₗ A B W p)
      (completedFormsBidegreeProjectionₗ_eq_zero A B W p) i x)
    (polynomialDeRhamDifferential_moduleCoefficientFormsMap A B W p M nabla)
  · refine LinearMap.ext fun z ↦ ?_
    refine Eq.trans ?_ (DFunLike.congr_fun
      (completedRelativeFormsRelContraction_addHom_zero A B W p) z)
    exact congrArg (fun w : completedPolynomialForms A B W p 0 ↦
        completedRelativeFormsHomotopyₗ A B W p 0
          (completedFormsRelDifferentialₗ A B W p 0 z) + w)
      (completedRelativeFormsProjection_eq_comp A B W p 0 z).symm
  · intro n
    refine LinearMap.ext fun z ↦ ?_
    refine Eq.trans ?_ (DFunLike.congr_fun
      (completedRelativeFormsRelContraction_addHom A B W p n) z)
    exact congrArg (fun w : completedPolynomialForms A B W p (n + 1) ↦
        completedFormsRelDifferentialₗ A B W p n (completedRelativeFormsHomotopyₗ A B W p n z) +
          completedRelativeFormsHomotopyₗ A B W p (n + 1)
            (completedFormsRelDifferentialₗ A B W p (n + 1) z) + w)
      (completedRelativeFormsProjection_eq_comp A B W p (n + 1) z).symm

/-- **The completed comparison is a homotopy equivalence, for a connection integrable in
coordinates.**

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let
`P = B⟨x_w : w ∈ W⟩`, let `D` and `D'` be the `p`-adic completions of `B` and `P`, and let `M` be
a `D`-module with a connection `∇ : M → M ⊗̂_D Ω̂¹_D` which admits coordinate operators in a finite
family of coordinates `x_j ∈ D` and is integrable in the coordinate sense
`Crystalline.IsIntegrable` (the operators commute).  Then both twisted de Rham differentials square
to zero, `1_M ⊗ ψ̂` is a map of complexes, and it has a homotopy inverse `π'` with
`π' (1_M ⊗ ψ̂) = 1` and `(1_M ⊗ ψ̂) π'` chain homotopic to the identity by `H`.

This is the form of the clause of [Stacks, Tag 07LD] over the completions for a connection given
in coordinates, as the pairs of [Stacks, Tag 07JG] are.  The clause itself, for an arbitrary
`D`-module with a connection integrable in the sense of [Stacks, Tag 07I0] and no coordinates, is
`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`. -/
theorem exists_homotopyEquiv_isIntegrable (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M)
    {iota : Type uI} [Finite iota] (x : iota → (completedDividedPowerRing p (B := (B : Type uB))))
    (hco : ∃ theta : iota → (M → M), IsCoordinateExpansion p
      (completedDividedPowerRing p (B := (B : Type uB)))
          (completedDividedPowerForms p A B.dividedPowers 1)
      (fun j ↦ completedFormsDifferential p A B.dividedPowers (x j)) nabla theta)
    (hint : IsIntegrable p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (fun j ↦ completedFormsDifferential p A B.dividedPowers (x j)) nabla) :
    CompletedDeRham.IsSquareZero p (completedDividedPowerRing p (B := (B : Type uB)))
        (completedDividedPowerForms p A B.dividedPowers)
        (completedDividedPowerWedge p A B.dividedPowers)
        (completedDividedPowerDeRham p A B.dividedPowers) M nabla
        (isGradedLeibniz_completedDividedPower p A B.dividedPowers) ∧
      CompletedDeRham.IsSquareZero p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
          (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M
          (pushedConnection A B W p M nabla)
          (isGradedLeibniz_completedPolynomialForms A B W p) ∧
        (∀ (i : ℕ) (z : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers i) M),
            polynomialDeRhamDifferential A B W p M (pushedConnection A B W p M nabla) i
                (moduleCoefficientFormsMap A B W p M i z) =
              moduleCoefficientFormsMap A B W p M (i + 1)
                (coefficientDeRhamDifferential A B p M nabla i z)) ∧
          ∃ (pi' : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
              (completedPolynomialForms A B W p i) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedDividedPowerForms p A B.dividedPowers i) M)
            (H : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                (completedPolynomialForms A B W p (i + 1)) M →+
      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedPolynomialForms A B W p i) M),
            (∀ (i : ℕ) (z : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                (completedDividedPowerForms p A B.dividedPowers i) M),
                pi' i (moduleCoefficientFormsMap A B W p M i z) = z) ∧
              (∀ (i : ℕ) (w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                  (completedPolynomialForms A B W p i) M),
                  pi' (i + 1) (polynomialDeRhamDifferential A B W p M
                      (pushedConnection A B W p M nabla) i w) =
                    coefficientDeRhamDifferential A B p M nabla i (pi' i w)) ∧
                (∀ w : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                    (completedPolynomialForms A B W p 0) M,
                    H 0 (polynomialDeRhamDifferential A B W p M
                        (pushedConnection A B W p M nabla) 0 w) +
                      moduleCoefficientFormsMap A B W p M 0 (pi' 0 w) = w) ∧
                  ∀ (n : ℕ) (w :
                      CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                          (completedPolynomialForms A B W p (n + 1)) M),
                    polynomialDeRhamDifferential A B W p M
                          (pushedConnection A B W p M nabla) n (H n w) +
                        H (n + 1) (polynomialDeRhamDifferential A B W p M
                          (pushedConnection A B W p M nabla) (n + 1) w) +
                      moduleCoefficientFormsMap A B W p M (n + 1) (pi' (n + 1) w) = w := by
  obtain ⟨theta, hco⟩ := hco
  have hsq := isSquareZero_pushedConnection A B W p M nabla x theta hco hint
  exact ⟨isSquareZero_completedDividedPowerForms A B p M nabla x theta hco hint, hsq,
    polynomialDeRhamDifferential_moduleCoefficientFormsMap A B W p M nabla,
    exists_homotopyEquiv_pushedConnection A B W p M nabla hsq⟩

end Poincare

end DividedPowerPolynomial

end Crystalline

end
