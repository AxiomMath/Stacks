module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincareContraction

/-!
# The relative divided power Poincaré lemma: `d h + h d = id - ψ ∘ ε`

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W`
index a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩`.
`StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincareContraction` builds the
homotopy `h` of `Ω^*_{P/A,δ'}`, the coefficient retraction `ε : Ω^*_{P/A,δ'} → Ω^*_{B/A,δ}` and
the projection `ψ ∘ ε`.  This module proves the contraction identity those were built for.

## What the statement is, and is not

`Ω^*_{P/A,δ'}` is **not** contractible for a nontrivial divided power ideal `I`: the sector of
the zero multi-index is `Ω^*_{B/A,δ}` read through `ψ`, and that is not killed by anything.
What is true is that

`ψ : Ω^*_{B/A,δ} → Ω^*_{P/A,δ'}`

is a homotopy equivalence with retraction `ε`, i.e. `d h + h d = id - ψ ∘ ε`.  For `B = A` and
`I = ⊥` the coefficient complex is concentrated in degree zero and this collapses to
`Crystalline.augmentedDividedPowerDeRhamComplex_contractible`.

## The computation

On the generator indexed by `(i, j + 1, J, L)` the decomposition puts the generator in the
sector `K = L + 1_J`, where the de Rham differential is the total differential `D_hor + κ` of
the bicomplex `Kos(supp K) ⊗_B Ω^*_{B/A,δ}`.  So `d h + h d` splits as

`[D_hor h + h D_hor] + [κ h + h κ]`,

the first bracket at bidegree `(i + 1, j)` and the second at bidegree `(i, j + 1)`.  The first
vanishes by
`Crystalline.DividedPowerPolynomial.relativeSectorHomotopy_coefficientDifferential` and the
second is the identity by
`Crystalline.DividedPowerPolynomial.relativeSectorKoszul_homotopy`.  The generators with no
variable differential are killed by `h`, and there the degree-zero Koszul identity
`Crystalline.DividedPowerPolynomial.relativeSectorKoszul_homotopy_zero` does the whole job —
except on the single generator with no variable differential and the trivial monomial, which
is `ψ(ω)` and is exactly the `ψ ∘ ε` term.

## The ext principle

Every identity here is proved on the generators of the decomposition, so what is needed is
that two `A`-linear maps out of `Ωⁿ_{P/A,δ'}` agreeing on them are equal.  The decomposition is
a composite of an `exteriorPowerCongr` with a Künneth isomorphism, and anything that forces
either open — surjectivity of the inverse, an induction on the image, an equality of maps fed
to `DFunLike.congr_fun` — exceeds the heartbeat limit.  So the ext principle is proved once,
`Crystalline.DividedPowerPolynomial.linearMap_ext_directSum_finsupp`, over an abstract
surjection onto the module and abstract surjections onto the summands, where nothing can
unfold, and instantiated in a single application.

## Main results

* `Crystalline.DividedPowerPolynomial.linearMap_ext_directSum_finsupp` — the generic ext
  principle for a module presented as a direct sum of modules spanned by pairs.
* `Crystalline.DividedPowerPolynomial.dividedPowerPolynomialForms_linearMap_ext` — its
  instance for `Ωⁿ_{P/A,δ'}`: two `A`-linear maps out of it agree as soon as they agree on the
  sector generators.
* `Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_identity_zero` — the degree-zero
  identity `h₀ (d₀ x) = x - ψ (ε x)`.
* `Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_identity` —
  **`d (h x) + h (d x) = x - ψ (ε x)`** in every positive degree.

## References

* [Stacks Project, Lemma 60.19.1, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW

namespace Crystalline

namespace DividedPowerPolynomial

/-! ### An ext principle for a direct sum of modules spanned by pairs -/

/-- **Two linear maps out of a direct sum of modules spanned by pairs agree as soon as they
agree on the generators.**

`E` is any surjection onto the module from the direct sum and `G i` any surjection onto the
`i`-th summand from a free module on pairs; both are variables, which is the point.  The
instance below has for `E` the inverse of a composite of an `exteriorPowerCongr` with a Künneth
isomorphism, and every element-level argument that forces that composite open — rewriting an
element as `E.symm z` and inducting on `z`, or feeding an equality of maps to
`DFunLike.congr_fun` — runs past the heartbeat limit, because the motive still mentions the
composite.  Here nothing can unfold. -/
theorem linearMap_ext_directSum_finsupp
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {iota : Type*} [DecidableEq iota]
    {S : iota → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)]
    {alpha : iota → Type*} {beta : iota → Type*} {C : iota → Type*}
    [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    (E : DirectSum iota S →ₗ[R] M) (hE : Function.Surjective E)
    (G : ∀ i, (alpha i →₀ (beta i →₀ C i)) →ₗ[R] S i)
    (hG : ∀ i, Function.Surjective (G i))
    {f g : M →ₗ[R] N}
    (h : ∀ (i : iota) (a : alpha i) (b : beta i) (c : C i),
      f (E (DirectSum.lof R iota S i (G i (Finsupp.single a (Finsupp.single b c))))) =
        g (E (DirectSum.lof R iota S i (G i (Finsupp.single a (Finsupp.single b c)))))) :
    f = g := by
  have hcomp : f ∘ₗ E = g ∘ₗ E := by
    refine DirectSum.linearMap_ext (R := R) fun i ↦ ?_
    have hGi : ((f ∘ₗ E) ∘ₗ DirectSum.lof R iota S i) ∘ₗ G i =
        ((g ∘ₗ E) ∘ₗ DirectSum.lof R iota S i) ∘ₗ G i := by
      refine Finsupp.lhom_ext' fun a ↦ Finsupp.lhom_ext fun b c ↦ ?_
      simpa only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply]
        using h i a b c
    refine LinearMap.ext fun s ↦ ?_
    obtain ⟨t, rfl⟩ := hG i s
    exact DFunLike.congr_fun hGi t
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := hE x
  exact DFunLike.congr_fun hcomp y

section Contraction

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W]

/-- **The generator of the decomposition indexed by `(i, j, J, L)`, read in degree `n`.**  It is
the sector generator `x^{[L]} · ψ(ω) ∧ d x_J`, transported along `i + j = n` so that the whole
contraction computation stays in one type. -/
def decompositionGenerator (i j n : ℕ) (hij : i + j = n) (L : W →₀ ℕ)
    (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    dividedPowerPolynomialForms A B W n :=
  exteriorPower.degCongr hij
    (sectorGenerator A B W L i omega j fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm J k)

/-- The generator in its own degree carries no transport. -/
theorem decompositionGenerator_self (i j : ℕ) (L : W →₀ ℕ) (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    decompositionGenerator A B W i j (i + j) rfl L J omega =
      sectorGenerator A B W L i omega j fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm J k :=
  rfl

/-- **The ext principle for `Ωⁿ_{P/A,δ'}`**: two `A`-linear maps out of the forms of the divided
power polynomial algebra are equal as soon as they agree on the generators of the
decomposition.  This is the relative replacement for `Module.Basis.ext` on the absolute basis;
there is no basis, because the coefficient module `Ωⁱ_{B/A,δ}` is an arbitrary `B`-module. -/
theorem dividedPowerPolynomialForms_linearMap_ext {N : Type*} [AddCommGroup N] [Module A N]
    (n : ℕ) {f g : dividedPowerPolynomialForms A B W n →ₗ[A] N}
    (h : ∀ (i j : ℕ) (hij : i + j = n) (L : W →₀ ℕ) (J : Set.powersetCard W j)
      (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i),
      f (decompositionGenerator A B W i j n hij L J omega) =
        g (decompositionGenerator A B W i j n hij L J omega)) :
    f = g := by
  refine linearMap_ext_directSum_finsupp
    (alpha := fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} ↦ Set.powersetCard W ij.1.2)
    (beta := fun _ ↦ (W →₀ ℕ))
    (C := fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} ↦
      dividedPowerDifferentialForms (A := A) B.dividedPowers ij.1.1)
    (((dividedPowerPolynomialFormsEquiv A B W n).symm.toLinearMap).restrictScalars A)
    (dividedPowerPolynomialFormsEquiv A B W n).symm.surjective
    (fun ij ↦ (((polynomialBidegreeFormsMonomialEquiv A B W ij.1.1
      ij.1.2).symm.toLinearMap).restrictScalars A))
    (fun ij ↦ (polynomialBidegreeFormsMonomialEquiv A B W ij.1.1 ij.1.2).symm.surjective)
    ?_
  rintro ⟨⟨i, j⟩, hij⟩ J L omega
  obtain rfl : i + j = n := hij
  simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  have hgen : (dividedPowerPolynomialFormsEquiv A B W (i + j)).symm
      (DirectSum.lof A {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
        (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(i, j), rfl⟩
        ((polynomialBidegreeFormsMonomialEquiv A B W i j).symm
          (Finsupp.single J (Finsupp.single L omega)))) =
      decompositionGenerator A B W i j (i + j) rfl L J omega := by
    refine Eq.trans (congrArg (fun z : DirectSum {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
        (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ↦
      (dividedPowerPolynomialFormsEquiv A B W (i + j)).symm z)
      (lof_eq_lof A B W (i + j) ⟨(i, j), rfl⟩ _).symm) ?_
    exact dividedPowerPolynomialFormsEquiv_symm_lof_single A B W i j L J omega
  rw [hgen]
  exact h i j rfl L J omega

/-! ### The decomposition and the retraction on a generator -/

/-- **The decomposition on a generator**, read forwards: it lands in the single summand
indexed by the bidegree, at the slot indexed by the subset and the exponent vector. -/
theorem dividedPowerPolynomialFormsEquiv_decompositionGenerator (i j n : ℕ) (hij : i + j = n)
    (L : W →₀ ℕ) (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    dividedPowerPolynomialFormsEquiv A B W n
        (decompositionGenerator A B W i j n hij L J omega) =
      DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
        {ij : ℕ × ℕ // ij.1 + ij.2 = n}
        (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(i, j), hij⟩
        ((polynomialBidegreeFormsMonomialEquiv A B W i j).symm
          (Finsupp.single J (Finsupp.single L omega))) := by
  subst hij
  exact (((dividedPowerPolynomialFormsEquiv A B W (i + j)).symm_apply_eq).mp
    (dividedPowerPolynomialFormsEquiv_symm_lof_single A B W i j L J omega)).symm

/-- The projection is the comparison map after the retraction. -/
theorem relativeFormsProjection_apply (n : ℕ) (x : dividedPowerPolynomialForms A B W n) :
    relativeFormsProjection A B W n x =
      coefficientFormsMap A B W n (relativeFormsRetraction A B W n x) :=
  rfl

/-- **The retraction kills a generator carrying a variable differential**: its summand is the
bidegree `(i, j + 1)`, and the retraction reads the bidegree `(n, 0)`. -/
theorem relativeFormsRetraction_decompositionGenerator_succ (i j n : ℕ)
    (hij : i + (j + 1) = n) (L : W →₀ ℕ) (J : Set.powersetCard W (j + 1))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeFormsRetraction A B W n
        (decompositionGenerator A B W i (j + 1) n hij L J omega) = 0 := by
  have hne : (⟨(i, j + 1), hij⟩ : {ij : ℕ × ℕ // ij.1 + ij.2 = n}) ≠ ⟨(n, 0), rfl⟩ := fun hc ↦
    Nat.succ_ne_zero j (congrArg Prod.snd (Subtype.ext_iff.mp hc))
  have hcomp : DirectSum.component A {ij : ℕ × ℕ // ij.1 + ij.2 = n}
        (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(n, 0), rfl⟩
        (dividedPowerPolynomialFormsEquiv A B W n
          (decompositionGenerator A B W i (j + 1) n hij L J omega)) = 0 := by
    rw [dividedPowerPolynomialFormsEquiv_decompositionGenerator, lof_eq_lof,
      DirectSum.component.of, dif_neg hne]
  simp only [relativeFormsRetraction, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, hcomp, map_zero]

/-- The retraction of a generator with no variable differential reads the slot of the trivial
monomial. -/
private theorem relativeFormsRetraction_decompositionGenerator_zero_apply (n : ℕ)
    (hn : n + 0 = n) (L : W →₀ ℕ) (J : Set.powersetCard W 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    relativeFormsRetraction A B W n
        (decompositionGenerator A B W n 0 n hn L J omega) =
      (Finsupp.single L omega : (W →₀ ℕ) →₀ _) 0 := by
  classical
  have hJ : J = emptyPowersetCard W := Subtype.ext (Finset.card_eq_zero.mp J.property)
  have hcomp : DirectSum.component A {ij : ℕ × ℕ // ij.1 + ij.2 = n}
        (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(n, 0), rfl⟩
        (dividedPowerPolynomialFormsEquiv A B W n
          (decompositionGenerator A B W n 0 n hn L J omega)) =
      (polynomialBidegreeFormsMonomialEquiv A B W n 0).symm
        (Finsupp.single J (Finsupp.single L omega)) := by
    rw [dividedPowerPolynomialFormsEquiv_decompositionGenerator, lof_eq_lof,
      DirectSum.component.lof_self]
  simp only [relativeFormsRetraction, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, hcomp,
    LinearEquiv.apply_symm_apply, Finsupp.lapply_apply]
  rw [hJ, Finsupp.single_eq_same]

/-- **The retraction reads off the coefficient form of the generator with no variable
differential and the trivial monomial.** -/
theorem relativeFormsRetraction_decompositionGenerator_zero (n : ℕ) (hn : n + 0 = n)
    (J : Set.powersetCard W 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    relativeFormsRetraction A B W n
        (decompositionGenerator A B W n 0 n hn (0 : W →₀ ℕ) J omega) = omega := by
  rw [relativeFormsRetraction_decompositionGenerator_zero_apply, Finsupp.single_eq_same]

/-- **The retraction kills the generator with no variable differential and a nontrivial
monomial**: the retraction reads the slot of the trivial monomial. -/
theorem relativeFormsRetraction_decompositionGenerator_monomial (n : ℕ) (hn : n + 0 = n)
    (L : W →₀ ℕ) (hL : L ≠ 0) (J : Set.powersetCard W 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    relativeFormsRetraction A B W n
        (decompositionGenerator A B W n 0 n hn L J omega) = 0 := by
  rw [relativeFormsRetraction_decompositionGenerator_zero_apply,
    Finsupp.single_eq_of_ne (Ne.symm hL)]

/-! ### The generator with no variable differential and the trivial monomial -/

omit [LinearOrder W] in
/-- Wedging a form with the empty wedge of variable differentials changes nothing. -/
theorem wedgeMul_variableWedge_zero (i : ℕ) (x : dividedPowerPolynomialForms A B W i)
    (v : Fin 0 → W) :
    exteriorPower.wedgeMul i 0 x (variableWedge A B W 0 v) = x :=
  Subtype.ext (by
    rw [exteriorPower.wedgeMul_apply_coe, variableWedge, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one])

omit [LinearOrder W] in
/-- **The generator with no variable differential and the trivial monomial is `ψ(ω)`.**  This
is the one slot of the decomposition the retraction sees, and so the one the projection
`ψ ∘ ε` reproduces. -/
theorem sectorGenerator_zero_zero (n : ℕ) (v : Fin 0 → W)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    sectorGenerator A B W (0 : W →₀ ℕ) n omega 0 v = coefficientFormsMap A B W n omega := by
  have hmono : dividedPowerPolynomialMonomial (B : Type uB) (0 : W →₀ ℕ) = 1 := by
    simp [dividedPowerPolynomialMonomial]
  show dividedPowerPolynomialMonomial (B : Type uB) (0 : W →₀ ℕ) •
      exteriorPower.wedgeMul n 0 (coefficientFormsMap A B W n omega)
        (variableWedge A B W 0 v) = _
  rw [hmono, one_smul, wedgeMul_variableWedge_zero]

/-- The same, read on the generator of the decomposition. -/
theorem decompositionGenerator_zero_zero (n : ℕ) (hn : n + 0 = n) (J : Set.powersetCard W 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    decompositionGenerator A B W n 0 n hn (0 : W →₀ ℕ) J omega =
      coefficientFormsMap A B W n omega :=
  sectorGenerator_zero_zero A B W n _ omega

/-- **The homotopy kills the differential of `ψ(ω)`**: `ψ` is a map of complexes, so `d (ψ ω)`
is again a generator with no variable differential, and there the homotopy is zero. -/
theorem relativeFormsHomotopy_dividedPowerDeRham_coefficientFormsMap (n : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    relativeFormsHomotopy A B W n
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (coefficientFormsMap A B W n omega)) = 0 := by
  rw [← coefficientFormsMap_dividedPowerDeRham,
    ← sectorGenerator_zero_zero A B W (n + 1)
      (fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm (emptyPowersetCard W) k)]
  exact relativeFormsHomotopy_sectorGenerator_zero A B W 0 n (emptyPowersetCard W) _

/-! ### The contraction identity on a sector -/

omit [LinearOrder W] in
/-- The total multi-index of a generator carrying a variable differential is nonzero, which is
the hypothesis of the Koszul contraction. -/
theorem add_finsetMultiIndex_ne_zero (L : W →₀ ℕ) (j : ℕ)
    (J : Set.powersetCard W (j + 1)) : L + finsetMultiIndex J.val ≠ 0 := by
  obtain ⟨w, hw⟩ : J.val.Nonempty := Finset.card_pos.mp (by rw [J.property]; omega)
  intro hc
  have hmem : w ∈ (L + finsetMultiIndex J.val).support :=
    subset_support_add_finsetMultiIndex J.val L hw
  rw [hc] at hmem
  simp at hmem

omit [LinearOrder W] in
/-- A generator with no variable differential has the exponent vector for its total
multi-index. -/
theorem add_finsetMultiIndex_powersetCard_zero (L : W →₀ ℕ) (J : Set.powersetCard W 0) :
    L + finsetMultiIndex J.val = L := by
  rw [Finset.card_eq_zero.mp J.property, finsetMultiIndex, Finset.sum_empty, add_zero]

/-- **The sector map of `K = L + 1_J` carries the sector basis vector of `J` to the generator
of the decomposition**, in a named degree. -/
theorem relativeSectorMapDeg_sectorExteriorBasis (i j n : ℕ) (hij : i + j = n) (L : W →₀ ℕ)
    (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeSectorMapDeg A B W (L + finsetMultiIndex J.val) i j n hij
        (sectorExteriorBasis B W (L + finsetMultiIndex J.val) j
            (sectorLiftSubset W (L + finsetMultiIndex J.val) j J
              (subset_support_add_finsetMultiIndex J.val L)) ⊗ₜ[(B : Type uB)] omega) =
      decompositionGenerator A B W i j n hij L J omega :=
  congrArg (fun z : dividedPowerPolynomialForms A B W (i + j) ↦
      exteriorPower.degCongr hij z)
    (relativeSectorMap_sectorLiftSubset A B W L i j J omega)

/-- **The contraction identity on the image of a sector in bidegree `(i, j + 1)`.**

Through the sector map the de Rham differential is the total differential `D_hor + κ`, so
`d h + h d` splits into `[D_hor h + h D_hor]` at bidegree `(i + 1, j)` and `[κ h + h κ]` at
bidegree `(i, j + 1)`.  The first bracket is zero and the second is the identity. -/
theorem relativeFormsHomotopy_identity_relativeSectorMapDeg (K : W →₀ ℕ) (hK : K ≠ 0)
    (i j : ℕ) (y : sectorModule A B W K i (j + 1)) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j)
          (relativeFormsHomotopy A B W (i + j)
            (relativeSectorMapDeg A B W K i (j + 1) (i + j + 1) rfl y)) +
        relativeFormsHomotopy A B W (i + j + 1)
          (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j + 1)
            (relativeSectorMapDeg A B W K i (j + 1) (i + j + 1) rfl y)) =
      relativeSectorMapDeg A B W K i (j + 1) (i + j + 1) rfl y := by
  have hhor : (i + 1) + j = i + j + 1 := by omega
  have e1 := relativeFormsHomotopy_relativeSectorMapDeg A B W K i j (i + j) rfl y
  have e2 := relativeSectorMapDeg_dividedPowerDeRham A B W K i j (i + j) rfl
    (relativeSectorHomotopy A B W K i j y)
  have e3 := relativeSectorMapDeg_dividedPowerDeRham A B W K i (j + 1) (i + j + 1) rfl y
  have e4 := relativeFormsHomotopy_relativeSectorMapDeg A B W K (i + 1) j (i + j + 1) hhor
    (relativeSectorCoefficientDifferential A B W K i (j + 1) y)
  have e5 := relativeFormsHomotopy_relativeSectorMapDeg A B W K i (j + 1) (i + j + 1) rfl
    (relativeSectorKoszulDifferential A B W K i (j + 1) y)
  refine Eq.trans (congrArg₂ (· + ·)
    (congrArg (fun z : dividedPowerPolynomialForms A B W (i + j) ↦
      dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j) z) e1)
    (congrArg (fun z : dividedPowerPolynomialForms A B W (i + j + 1 + 1) ↦
      relativeFormsHomotopy A B W (i + j + 1) z) e3)) ?_
  refine Eq.trans (congrArg₂ (· + ·) e2
    (Eq.trans (map_add (relativeFormsHomotopy A B W (i + j + 1)) _ _)
      (congrArg₂ (· + ·) e4 e5))) ?_
  refine Eq.trans (add_add_add_comm _ _ _ _) ?_
  refine Eq.trans (congrArg₂ (· + ·)
    (Eq.trans (map_add (relativeSectorMapDeg A B W K (i + 1) j (i + j + 1) hhor) _ _).symm
      (Eq.trans (congrArg (fun z : sectorModule A B W K (i + 1) j ↦
          relativeSectorMapDeg A B W K (i + 1) j (i + j + 1) hhor z)
        (relativeSectorHomotopy_coefficientDifferential A B W K i j y)) (map_zero _)))
    (Eq.trans (map_add (relativeSectorMapDeg A B W K i (j + 1) (i + j + 1) rfl) _ _).symm
      (congrArg (fun z : sectorModule A B W K i (j + 1) ↦
          relativeSectorMapDeg A B W K i (j + 1) (i + j + 1) rfl z)
        (relativeSectorKoszul_homotopy A B W K hK i j y)))) ?_
  exact zero_add _

/-- **The contraction identity on the image of a nonzero sector in bidegree `(n, 0)`.**  There
is no outgoing homotopy, and the whole of the identity is the degree-zero Koszul contraction. -/
theorem relativeFormsHomotopy_identity_relativeSectorMapDeg_zero (K : W →₀ ℕ) (hK : K ≠ 0)
    (n : ℕ) (y : sectorModule A B W K n 0) :
    relativeFormsHomotopy A B W n
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (relativeSectorMapDeg A B W K n 0 n rfl y)) =
      relativeSectorMapDeg A B W K n 0 n rfl y := by
  rw [relativeSectorMapDeg_dividedPowerDeRham A B W K n 0 n rfl y, map_add,
    relativeFormsHomotopy_relativeSectorMapDeg_zero A B W K n
      (relativeSectorCoefficientDifferential A B W K n 0 y),
    relativeFormsHomotopy_relativeSectorMapDeg A B W K n 0 n rfl
      (relativeSectorKoszulDifferential A B W K n 0 y), zero_add,
    relativeSectorKoszul_homotopy_zero A B W K hK n y]

/-! ### The contraction identity on a generator -/

/-- **The contraction identity on a generator with no variable differential.**  There is no
outgoing homotopy here, and the two cases of the exponent vector are the two halves of the
statement: a nontrivial monomial is contracted, and the trivial one is the `ψ ∘ ε` term. -/
theorem relativeFormsHomotopy_identity_decompositionGenerator_zero (n : ℕ) (hn : n + 0 = n)
    (L : W →₀ ℕ) (J : Set.powersetCard W 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    relativeFormsHomotopy A B W n
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (decompositionGenerator A B W n 0 n hn L J omega)) =
      decompositionGenerator A B W n 0 n hn L J omega -
        relativeFormsProjection A B W n (decompositionGenerator A B W n 0 n hn L J omega) := by
  by_cases hL : L = 0
  · subst hL
    have hproj : relativeFormsProjection A B W n
        (decompositionGenerator A B W n 0 n hn (0 : W →₀ ℕ) J omega) =
          decompositionGenerator A B W n 0 n hn (0 : W →₀ ℕ) J omega := by
      rw [relativeFormsProjection_apply, relativeFormsRetraction_decompositionGenerator_zero,
        decompositionGenerator_zero_zero]
    rw [hproj, sub_self, decompositionGenerator_zero_zero]
    exact relativeFormsHomotopy_dividedPowerDeRham_coefficientFormsMap A B W n omega
  · have hproj : relativeFormsProjection A B W n
        (decompositionGenerator A B W n 0 n hn L J omega) = 0 := by
      rw [relativeFormsProjection_apply,
        relativeFormsRetraction_decompositionGenerator_monomial A B W n hn L hL J omega,
        map_zero]
    have hKne : L + finsetMultiIndex J.val ≠ 0 := by
      rw [add_finsetMultiIndex_powersetCard_zero]
      exact hL
    rw [hproj, sub_zero,
      ← relativeSectorMapDeg_sectorExteriorBasis A B W n 0 n hn L J omega]
    exact relativeFormsHomotopy_identity_relativeSectorMapDeg_zero A B W _ hKne n _

/-- **The homotopy kills a generator with no variable differential.** -/
theorem relativeFormsHomotopy_decompositionGenerator_zero (n : ℕ) (hn : n + 1 + 0 = n + 1)
    (L : W →₀ ℕ) (J : Set.powersetCard W 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers (n + 1)) :
    relativeFormsHomotopy A B W n
        (decompositionGenerator A B W (n + 1) 0 (n + 1) hn L J omega) = 0 :=
  relativeFormsHomotopy_sectorGenerator_zero A B W L n J omega

/-- **The contraction identity on a generator with no variable differential, in a positive
degree.**  The homotopy kills such a generator, so only the incoming half survives, and that
is the previous statement. -/
theorem relativeFormsHomotopy_identity_decompositionGenerator_const (n : ℕ)
    (hn : n + 1 + 0 = n + 1) (L : W →₀ ℕ) (J : Set.powersetCard W 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers (n + 1)) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (relativeFormsHomotopy A B W n
            (decompositionGenerator A B W (n + 1) 0 (n + 1) hn L J omega)) +
        relativeFormsHomotopy A B W (n + 1)
          (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1)
            (decompositionGenerator A B W (n + 1) 0 (n + 1) hn L J omega)) =
      decompositionGenerator A B W (n + 1) 0 (n + 1) hn L J omega -
        relativeFormsProjection A B W (n + 1)
          (decompositionGenerator A B W (n + 1) 0 (n + 1) hn L J omega) := by
  rw [relativeFormsHomotopy_decompositionGenerator_zero A B W n hn L J omega,
    dividedPowerDeRham_zero, zero_add]
  exact relativeFormsHomotopy_identity_decompositionGenerator_zero A B W (n + 1) hn L J omega

/-- **The contraction identity on a generator carrying a variable differential.**  The
generator is the sector map of `K = L + 1_J` on a sector basis vector, and the identity is the
contraction of that sector; the projection term vanishes because the generator sits in a
bidegree the retraction does not read. -/
theorem relativeFormsHomotopy_identity_decompositionGenerator_succ (i j : ℕ)
    (hij : i + (j + 1) = i + j + 1) (L : W →₀ ℕ) (J : Set.powersetCard W (j + 1))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j)
          (relativeFormsHomotopy A B W (i + j)
            (decompositionGenerator A B W i (j + 1) (i + j + 1) hij L J omega)) +
        relativeFormsHomotopy A B W (i + j + 1)
          (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (i + j + 1)
            (decompositionGenerator A B W i (j + 1) (i + j + 1) hij L J omega)) =
      decompositionGenerator A B W i (j + 1) (i + j + 1) hij L J omega -
        relativeFormsProjection A B W (i + j + 1)
          (decompositionGenerator A B W i (j + 1) (i + j + 1) hij L J omega) := by
  have hproj : relativeFormsProjection A B W (i + j + 1)
      (decompositionGenerator A B W i (j + 1) (i + j + 1) hij L J omega) = 0 := by
    rw [relativeFormsProjection_apply,
      relativeFormsRetraction_decompositionGenerator_succ A B W i j (i + j + 1) hij L J omega,
      map_zero]
  rw [hproj, sub_zero,
    ← relativeSectorMapDeg_sectorExteriorBasis A B W i (j + 1) (i + j + 1) hij L J omega]
  exact relativeFormsHomotopy_identity_relativeSectorMapDeg A B W _
    (add_finsetMultiIndex_ne_zero W L j J) i j _

/-! ### The contraction identity -/

/-- **The degree-zero half of the contraction identity**: `h₀ (d₀ x) = x - ψ (ε x)`. -/
theorem relativeFormsHomotopy_identity_zero (x : dividedPowerPolynomialForms A B W 0) :
    relativeFormsHomotopy A B W 0
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) 0 x) =
      x - relativeFormsProjection A B W 0 x := by
  have key : (relativeFormsHomotopy A B W 0).comp
        (dividedPowerDeRhamLinearMap (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W) 0) =
      (LinearMap.id : dividedPowerPolynomialForms A B W 0 →ₗ[A]
          dividedPowerPolynomialForms A B W 0) -
        relativeFormsProjection A B W 0 := by
    refine dividedPowerPolynomialForms_linearMap_ext A B W 0 ?_
    intro i j hij L J omega
    obtain rfl : j = 0 := by omega
    obtain rfl : i = 0 := by omega
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
      dividedPowerDeRhamLinearMap_apply]
    exact relativeFormsHomotopy_identity_decompositionGenerator_zero A B W 0 hij L J omega
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
    dividedPowerDeRhamLinearMap_apply] using DFunLike.congr_fun key x

/-- **The relative divided power Poincaré lemma, as a homotopy equivalence.**

`d (h x) + h (d x) = x - ψ (ε x)`: the comparison map `ψ : Ω^*_{B/A,δ} → Ω^*_{P/A,δ'}` of the
divided power polynomial algebra `P = B⟨x_w : w ∈ W⟩` is a homotopy equivalence with retraction
the coefficient retraction `ε`.  The divided power ideal `I` of the base is arbitrary; for
`B = A` and `I = ⊥` the coefficient complex is concentrated in degree zero and this is the
contractibility of `Crystalline.augmentedDividedPowerDeRhamComplex_contractible`. -/
theorem relativeFormsHomotopy_identity (n : ℕ)
    (x : dividedPowerPolynomialForms A B W (n + 1)) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (relativeFormsHomotopy A B W n x) +
        relativeFormsHomotopy A B W (n + 1)
          (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1) x) =
      x - relativeFormsProjection A B W (n + 1) x := by
  have key : (dividedPowerDeRhamLinearMap (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W) n).comp
          (relativeFormsHomotopy A B W n) +
        (relativeFormsHomotopy A B W (n + 1)).comp
          (dividedPowerDeRhamLinearMap (A := A)
            (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1)) =
      (LinearMap.id : dividedPowerPolynomialForms A B W (n + 1) →ₗ[A]
          dividedPowerPolynomialForms A B W (n + 1)) -
        relativeFormsProjection A B W (n + 1) := by
    refine dividedPowerPolynomialForms_linearMap_ext A B W (n + 1) ?_
    intro i j hij L J omega
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_coe, id_eq, dividedPowerDeRhamLinearMap_apply]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      obtain rfl : i = n + 1 := hij
      exact relativeFormsHomotopy_identity_decompositionGenerator_const A B W n _ L J omega
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
      obtain rfl : i + j = n := by omega
      exact relativeFormsHomotopy_identity_decompositionGenerator_succ A B W i j _ L J omega
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_coe, id_eq, dividedPowerDeRhamLinearMap_apply] using DFunLike.congr_fun key x

end Contraction

end DividedPowerPolynomial

end Crystalline

end
