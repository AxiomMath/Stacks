module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedRelativePoincare

/-!
# The relative divided power Poincaré homotopy is a *special* deformation retract

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W` index
a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩`.
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/RelativePoincareHomotopy.lean` proves the
contraction identity `d h + h d = id - ψ ε` on `Ω^*_{P/A,δ'}`, and
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/CompletedRelativePoincare.lean` carries
it across the `p`-adic completion.  A contraction is not enough for the perturbation argument of
[Stacks, Lemma 60.21.2, Tag 07LD]: that argument needs the homotopy to be a **special** deformation
retract, which is the contraction together with the three side conditions

`h ∘ h = 0`,   `h ∘ ψ = 0`,   `ε ∘ h = 0`.

This module proves all three, uncompleted and completed.  With them,
`Crystalline.FinitePerturbation.exists_perturbedHomotopyEquiv` turns a contraction of the relative
differential into a *homotopy equivalence* for the connection-twisted differential, and not merely
into a chain homotopy between the identity and an idempotent.

## Where each one comes from

The homotopy is the sector map of the Koszul contraction `ι_φ` against a coordinate functional of
`supp K`, with the sign `(-1)^i` of the coefficient degree; see
`Crystalline.DividedPowerPolynomial.relativeSectorHomotopy`.  So:

* `h ∘ h = 0` is `ι_φ ∘ ι_φ = 0`, which is
  `StacksFrontier.LinearAlgebra.ExteriorPower.Koszul`'s `exteriorPower.contraction_comp_contraction`,
  the two signs squaring to `1`.  The two bidegrees with too few variable differentials for a
  second contraction are killed by `h` outright, and the sector is the same for both applications
  — `h` lowers the number of variable differentials and leaves the total multi-index alone — which
  is what makes the statement reduce to the sector at all.
* `h ∘ ψ = 0` because `ψ(ω)` is the generator with no variable differential and the trivial
  monomial, and `h` kills every generator with no variable differential.
* `ε ∘ h = 0` because `h` keeps a generator inside its own sector `K = L + 1_J`, which is nonzero
  as soon as a variable differential is present, while `ε` reads the slot of the sector `K = 0`.
  This is the one of the three that is not about the Koszul direction at all: it is about the
  monomial, and it is why the homotopy *raises* the divided power degree.

## What is deliberately not claimed

* **No statement about the base direction.**  `D_hor h + h D_hor = 0` is already
  `Crystalline.DividedPowerPolynomial.relativeSectorHomotopy_coefficientDifferential` and is not
  repeated here; the three identities below involve no differential at all.
* **Nothing is said about a module with a connection.**  These are identities of maps of the forms
  themselves, which is exactly the shape in which they tensor up:
  `Crystalline.CompletedDeRham.completedLTensor_comp_eq_zero` applies `1_M ⊗ −` to them.

## Main results

* `Crystalline.DividedPowerPolynomial.relativeSectorHomotopy_relativeSectorHomotopy` — `ι_φ² = 0`
  on a sector.
* `Crystalline.DividedPowerPolynomial.eq_zero_of_sectorExteriorBasis` — an additive map killing
  the image of every sector basis vector kills the image of the sector; the induction the three
  statements share.
* `Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_relativeFormsHomotopy` — **`h² = 0`.**
* `Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_coefficientFormsMap` —
  **`h ∘ ψ = 0`.**
* `Crystalline.DividedPowerPolynomial.relativeFormsRetraction_relativeFormsHomotopy` —
  **`ε ∘ h = 0`.**
* `completedRelativeFormsHomotopy_completedRelativeFormsHomotopy`,
  `completedRelativeFormsHomotopy_completedCoefficient` and
  `completedRelativeFormsRetraction_completedRelativeFormsHomotopy`, in the namespace
  `Crystalline.DividedPowerPolynomial` — **the same three for the completed homotopy `ĥ`**, by the
  additive functoriality of `Crystalline.PAdicCompletion.mapAddHom`.

## References

* [Stacks Project, Lemma 60.19.1, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW

namespace Crystalline

/-! ### Transporting a vanishing composite across the `p`-adic completion -/

namespace PAdicCompletion

section TransportZero

variable (p : ℕ) (R : Type*) [CommRing R] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
  {X Y Z : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module S Y] [AddCommGroup Z]
  [Module T Z]

/-- **A vanishing composite of additive maps stays vanishing across the `p`-adic completion**, the
three modules living over three different base rings: `g ∘ f = 0` becomes `G ∘ F = 0`.  As in
`Crystalline.PAdicCompletion.mapAddHom_contraction_zero`, the completed maps are variables with
equations so that nothing has to unfold at the application site. -/
theorem mapAddHom_comp_eq_zero (f : X →+ Y) (g : Y →+ Z)
    (F : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := S) p) Y)
    (G : AdicCompletion (pAdicIdeal (A := S) p) Y →+ AdicCompletion (pAdicIdeal (A := T) p) Z)
    (hF : F = mapAddHom p R S f) (hG : G = mapAddHom p S T g) (hzero : g.comp f = 0) :
    G.comp F = 0 := by
  subst hF hG
  rw [← mapAddHom_comp p R S T f g, hzero, mapAddHom_zero]

end TransportZero

end PAdicCompletion

namespace DividedPowerPolynomial

section Special

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W]

/-! ### The Koszul contraction of a sector squares to zero -/

/-- **The contracting homotopy of a sector squares to zero.**  It is `(-1)^i (1 ⊗ ι_φ)`, the two
signs square to `1`, and the Koszul contraction squares to zero by
`exteriorPower.contraction_comp_contraction`; tensoring on the right by the coefficient module
changes nothing. -/
theorem relativeSectorHomotopy_relativeSectorHomotopy (K : W →₀ ℕ) (i j : ℕ)
    (x : sectorModule A B W K i (j + 1 + 1)) :
    relativeSectorHomotopy A B W K i j (relativeSectorHomotopy A B W K i (j + 1) x) = 0 := by
  have hsq : ((-1 : (B : Type uB)) ^ i) * ((-1 : (B : Type uB)) ^ i) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hplain : relativeSectorHomotopy A B W K i j (relativeSectorHomotopy A B W K i (j + 1) x) =
      LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
        (exteriorPower.contraction (sectorFunctional B W K) j)
        (LinearMap.rTensor (dividedPowerDifferentialForms (A := A) B.dividedPowers i)
          (exteriorPower.contraction (sectorFunctional B W K) (j + 1)) x) := by
    rw [relativeSectorHomotopy, relativeSectorHomotopy, LinearMap.smul_apply,
      LinearMap.smul_apply, map_smul, smul_smul, hsq, one_smul]
  rw [hplain, ← LinearMap.rTensor_comp_apply,
    exteriorPower.contraction_comp_contraction (sectorFunctional B W K) j,
    LinearMap.rTensor_zero, LinearMap.zero_apply]

/-! ### An induction over a sector -/

/-- **An additive map that kills the image of every sector basis vector kills the image of the
whole sector.**

The sector module is the tensor product of the exterior power of the free module on `supp K` with
the coefficient forms, so an element of it is a finite sum of basis vectors with coefficients in
the forms; this is that induction, run through
`Crystalline.DividedPowerPolynomial.sectorModuleEquiv`.  It is isolated because the three side
conditions below all need it, and because nothing in the composite defining the sector module may
be allowed to unfold — the ambient equivalence is a `TensorProduct.congr` of a basis
representation with a `Finsupp` comparison. -/
theorem eq_zero_of_sectorExteriorBasis {N : Type*} [AddCommGroup N] (K : W →₀ ℕ) (i j n : ℕ)
    (hn : i + j = n) (f : dividedPowerPolynomialForms A B W n →+ N)
    (hf : ∀ (I : Set.powersetCard (K.support : Type uW) j)
      (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i),
      f (relativeSectorMapDeg A B W K i j n hn
        (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega)) = 0)
    (x : sectorModule A B W K i j) : f (relativeSectorMapDeg A B W K i j n hn x) = 0 := by
  classical
  have key : ∀ (g : Set.powersetCard (K.support : Type uW) j →₀
        dividedPowerDifferentialForms (A := A) B.dividedPowers i)
      (y : sectorModule A B W K i j), (sectorModuleEquiv A B W K i j).symm g = y →
      f (relativeSectorMapDeg A B W K i j n hn y) = 0 := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero =>
        intro y hy
        have hy0 : y = 0 := by rw [← hy, map_zero]
        subst hy0
        simp only [map_zero]
    | add g₁ g₂ hg₁ hg₂ =>
        intro y hy
        have hy2 : y = (sectorModuleEquiv A B W K i j).symm g₁ +
            (sectorModuleEquiv A B W K i j).symm g₂ := by rw [← hy, map_add]
        subst hy2
        simp only [map_add]
        exact Eq.trans (congrArg₂ (· + ·) (hg₁ _ rfl) (hg₂ _ rfl)) (add_zero 0)
    | single I omega =>
        intro y hy
        have hy2 : y = sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega := by
          rw [← hy, sectorModuleEquiv_symm_single]
        subst hy2
        exact hf I omega
  exact key (sectorModuleEquiv A B W K i j x) x ((sectorModuleEquiv A B W K i j).symm_apply_apply x)

/-- A linear map out of the forms vanishes if it kills every generator with no variable
differential and the image of every sector with at least one. -/
private theorem eq_zero_of_decompositionGenerator {N : Type*} [AddCommGroup N] [Module A N] (m : ℕ)
    (f : dividedPowerPolynomialForms A B W m →ₗ[A] N)
    (h0 : ∀ (L : W →₀ ℕ) (J : Set.powersetCard W 0)
      (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers m),
      f (decompositionGenerator A B W m 0 m (add_zero m) L J omega) = 0)
    (hs : ∀ (i k : ℕ) (L : W →₀ ℕ) (J : Set.powersetCard W (k + 1)) (hn : i + (k + 1) = m)
      (y : sectorModule A B W (L + finsetMultiIndex J.val) i (k + 1)),
      f (relativeSectorMapDeg A B W (L + finsetMultiIndex J.val) i (k + 1) m hn y) = 0)
    (x : dividedPowerPolynomialForms A B W m) : f x = 0 := by
  have key : f = 0 := by
    refine dividedPowerPolynomialForms_linearMap_ext A B W m fun i j hij L J omega ↦ ?_
    rw [LinearMap.zero_apply]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · obtain rfl : i = m := hij
      exact h0 L J omega
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
      rw [← relativeSectorMapDeg_sectorExteriorBasis A B W i (k + 1) m hij L J omega]
      exact hs i k L J hij _
  rw [key, LinearMap.zero_apply]

/-! ### `ε ∘ h = 0`: the homotopy leaves the zero sector -/

/-- **The retraction kills a generator with no variable differential and a nonzero sector.**  The
sector of such a generator is its monomial, so the monomial is nontrivial and the retraction,
which reads the trivial one, does not see it. -/
theorem relativeFormsRetraction_decompositionGenerator_const_ne_zero (n : ℕ) (hn : n + 0 = n)
    (L : W →₀ ℕ) (J : Set.powersetCard W 0) (hLJ : L + finsetMultiIndex J.val ≠ 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    relativeFormsRetraction A B W n (decompositionGenerator A B W n 0 n hn L J omega) = 0 := by
  refine relativeFormsRetraction_decompositionGenerator_monomial A B W n hn L ?_ J omega
  rw [add_finsetMultiIndex_powersetCard_zero] at hLJ
  exact hLJ

/-- **The retraction kills a generator whose sector is nonzero.**  Either the generator carries a
variable differential, and then it sits in a bidegree the retraction does not read, or it does not,
and then the previous statement applies. -/
theorem relativeFormsRetraction_decompositionGenerator_ne_zero (i j n : ℕ) (hn : i + j = n)
    (L : W →₀ ℕ) (J : Set.powersetCard W j) (hLJ : L + finsetMultiIndex J.val ≠ 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeFormsRetraction A B W n (decompositionGenerator A B W i j n hn L J omega) = 0 := by
  subst hn
  cases j with
  | zero =>
    exact relativeFormsRetraction_decompositionGenerator_const_ne_zero A B W i rfl L J hLJ omega
  | succ j =>
    exact relativeFormsRetraction_decompositionGenerator_succ A B W i j _ rfl L J omega

/-- **The retraction kills the image of a nonzero sector.**  Through the sector map a basis vector
of the sector is the generator indexed by `(K - 1_J, J)`, whose sector is `K` again, and the
previous statement applies. -/
theorem relativeFormsRetraction_relativeSectorMapDeg (K : W →₀ ℕ) (hK : K ≠ 0) (i j n : ℕ)
    (hn : i + j = n) (x : sectorModule A B W K i j) :
    relativeFormsRetraction A B W n (relativeSectorMapDeg A B W K i j n hn x) = 0 := by
  refine eq_zero_of_sectorExteriorBasis A B W K i j n hn
    (relativeFormsRetraction A B W n).toAddMonoidHom (fun I omega ↦ ?_) x
  have hgen : relativeSectorMapDeg A B W K i j n hn
        (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega) =
      decompositionGenerator A B W i j n hn
        (K - finsetMultiIndex (sectorSubsetDown W K j I).val)
        (sectorSubsetDown W K j I) omega := by
    rw [relativeSectorMapDeg_apply, relativeSectorMap_sectorBasis]
    rfl
  show relativeFormsRetraction A B W n (relativeSectorMapDeg A B W K i j n hn
    (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega)) = 0
  rw [hgen]
  refine relativeFormsRetraction_decompositionGenerator_ne_zero A B W i j n hn _ _ ?_ omega
  rw [finsetMultiIndex_sub_add _ K (sectorSubsetDown_subset W K j I)]
  exact hK

/-- **`ε ∘ h = 0`**: the homotopy raises the divided power degree, so its image misses the slot of
the zero sector, which is the one the retraction reads.

The generators with no variable differential are killed by `h` outright, and a generator carrying
one is the sector map of its own sector `K = L + 1_J`, which the homotopy does not leave and which
is nonzero. -/
theorem relativeFormsRetraction_relativeFormsHomotopy (n : ℕ)
    (x : dividedPowerPolynomialForms A B W (n + 1)) :
    relativeFormsRetraction A B W n (relativeFormsHomotopy A B W n x) = 0 := by
  exact eq_zero_of_decompositionGenerator A B W (n + 1)
    ((relativeFormsRetraction A B W n).comp (relativeFormsHomotopy A B W n))
    (fun L J omega ↦ Eq.trans (congrArg (fun z ↦ relativeFormsRetraction A B W n z)
      (relativeFormsHomotopy_decompositionGenerator_zero A B W n _ L J omega)) (map_zero _))
    (fun i k L J hn2 _ ↦ by
      have hn3 : i + k = n := by omega
      rw [LinearMap.comp_apply, relativeFormsHomotopy_relativeSectorMapDeg A B W _ i k n hn3]
      exact relativeFormsRetraction_relativeSectorMapDeg A B W _
        (add_finsetMultiIndex_ne_zero W L k J) i k n hn3 _) x

/-! ### `h ∘ ψ = 0`: the homotopy kills the coefficient forms -/

/-- **`h ∘ ψ = 0`**: `ψ(ω)` is the generator with no variable differential and the trivial
monomial, and the homotopy kills every generator with no variable differential — there is no Koszul
direction to contract there. -/
theorem relativeFormsHomotopy_coefficientFormsMap (n : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers (n + 1)) :
    relativeFormsHomotopy A B W n (coefficientFormsMap A B W (n + 1) omega) = 0 := by
  rw [← sectorGenerator_zero_zero A B W (n + 1)
    (fun k ↦ Set.powersetCard.ofFinEmbEquiv.symm (emptyPowersetCard W) k)]
  exact relativeFormsHomotopy_sectorGenerator_zero A B W 0 n (emptyPowersetCard W) omega

/-! ### `h ∘ h = 0`: the Koszul contraction squares to zero -/

/-- **The homotopy applied twice kills the image of a sector.**

The homotopy does not leave the sector — it lowers the number of variable differentials and leaves
the total multi-index alone — so applying it twice to the image of the sector `K` is applying the
Koszul contraction of that sector twice, which vanishes.  The two bidegrees with too few variable
differentials for a second contraction are killed outright: `(n + 2, 0)` by the first application
and `(n + 1, 0)` by the second. -/
theorem relativeFormsHomotopy_relativeFormsHomotopy_relativeSectorMapDeg (K : W →₀ ℕ)
    (i j n : ℕ) (hn : i + j = n + 1 + 1) (y : sectorModule A B W K i j) :
    relativeFormsHomotopy A B W n (relativeFormsHomotopy A B W (n + 1)
      (relativeSectorMapDeg A B W K i j (n + 1 + 1) hn y)) = 0 := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    obtain rfl : i = n + 1 + 1 := hn
    exact Eq.trans (congrArg (fun z ↦ relativeFormsHomotopy A B W n z)
      (relativeFormsHomotopy_relativeSectorMapDeg_zero A B W K (n + 1) y)) (map_zero _)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hn2 : i + k = n + 1 := by omega
    rw [relativeFormsHomotopy_relativeSectorMapDeg A B W K i k (n + 1) hn2]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      obtain rfl : i = n + 1 := by omega
      exact relativeFormsHomotopy_relativeSectorMapDeg_zero A B W K n _
    · obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      have hn3 : i + l = n := by omega
      rw [relativeFormsHomotopy_relativeSectorMapDeg A B W K i l n hn3,
        relativeSectorHomotopy_relativeSectorHomotopy A B W K i l y, map_zero]

/-- **`h² = 0`**: the homotopy squares to zero, so it is a *special* deformation retract and not
merely a contraction.

A generator with no variable differential is killed at once; a generator with one is the sector map
of its own sector, and the previous statement applies. -/
theorem relativeFormsHomotopy_relativeFormsHomotopy (n : ℕ)
    (x : dividedPowerPolynomialForms A B W (n + 1 + 1)) :
    relativeFormsHomotopy A B W n (relativeFormsHomotopy A B W (n + 1) x) = 0 := by
  exact eq_zero_of_decompositionGenerator A B W (n + 1 + 1)
    ((relativeFormsHomotopy A B W n).comp (relativeFormsHomotopy A B W (n + 1)))
    (fun L J omega ↦ Eq.trans (congrArg (fun z ↦ relativeFormsHomotopy A B W n z)
      (relativeFormsHomotopy_decompositionGenerator_zero A B W (n + 1) _ L J omega)) (map_zero _))
    (fun i k _ _ hn2 _ ↦
      relativeFormsHomotopy_relativeFormsHomotopy_relativeSectorMapDeg A B W _ i (k + 1) n hn2 _) x

/-! ### The three side conditions, as identities of additive maps -/

/-- `h ∘ h = 0`, as an identity of additive maps; this is the shape the completion consumes. -/
theorem relativeFormsHomotopy_comp_relativeFormsHomotopy (n : ℕ) :
    (relativeFormsHomotopy A B W n).toAddMonoidHom.comp
        (relativeFormsHomotopy A B W (n + 1)).toAddMonoidHom = 0 :=
  AddMonoidHom.ext fun x ↦ relativeFormsHomotopy_relativeFormsHomotopy A B W n x

/-- `h ∘ ψ = 0`, as an identity of additive maps. -/
theorem relativeFormsHomotopy_comp_coefficientFormsMap (n : ℕ) :
    (relativeFormsHomotopy A B W n).toAddMonoidHom.comp
        (coefficientFormsMap A B W (n + 1)).toAddMonoidHom = 0 :=
  AddMonoidHom.ext fun x ↦ relativeFormsHomotopy_coefficientFormsMap A B W n x

/-- `ε ∘ h = 0`, as an identity of additive maps. -/
theorem relativeFormsRetraction_comp_relativeFormsHomotopy (n : ℕ) :
    (relativeFormsRetraction A B W n).toAddMonoidHom.comp
        (relativeFormsHomotopy A B W n).toAddMonoidHom = 0 :=
  AddMonoidHom.ext fun x ↦ relativeFormsRetraction_relativeFormsHomotopy A B W n x

/-! ### The three side conditions for the completed homotopy -/

variable (p : ℕ)

/-- **`ĥ² = 0`**: the completed homotopy squares to zero.  One additive functor applied to
`Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_comp_relativeFormsHomotopy`. -/
theorem completedRelativeFormsHomotopy_comp_completedRelativeFormsHomotopy (n : ℕ) :
    (completedRelativeFormsHomotopy A B W p n).comp
        (completedRelativeFormsHomotopy A B W p (n + 1)) = 0 :=
  PAdicCompletion.mapAddHom_comp_eq_zero p (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (relativeFormsHomotopy A B W (n + 1)).toAddMonoidHom
    (relativeFormsHomotopy A B W n).toAddMonoidHom
    (completedRelativeFormsHomotopy A B W p (n + 1))
    (completedRelativeFormsHomotopy A B W p n)
    (completedRelativeFormsHomotopy_eq A B W p (n + 1))
    (completedRelativeFormsHomotopy_eq A B W p n)
    (relativeFormsHomotopy_comp_relativeFormsHomotopy A B W n)

/-- `ĥ (ĥ y) = 0`, read on an element. -/
theorem completedRelativeFormsHomotopy_completedRelativeFormsHomotopy (n : ℕ)
    (y : completedPolynomialForms A B W p (n + 1 + 1)) :
    completedRelativeFormsHomotopy A B W p n
        (completedRelativeFormsHomotopy A B W p (n + 1) y) = 0 :=
  DFunLike.congr_fun
    (completedRelativeFormsHomotopy_comp_completedRelativeFormsHomotopy A B W p n) y

/-- **`ĥ ψ̂ = 0`**: the completed homotopy kills the completed coefficient forms. -/
theorem completedRelativeFormsHomotopy_comp_completedCoefficient (n : ℕ) :
    (completedRelativeFormsHomotopy A B W p n).comp
        (completedCoefficientFormsMap A B W p (n + 1)).toAddMonoidHom = 0 :=
  PAdicCompletion.mapAddHom_comp_eq_zero p (B : Type uB)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (coefficientFormsMap A B W (n + 1)).toAddMonoidHom
    (relativeFormsHomotopy A B W n).toAddMonoidHom
    (completedCoefficientFormsMap A B W p (n + 1)).toAddMonoidHom
    (completedRelativeFormsHomotopy A B W p n)
    (completedCoefficientFormsMap_toAddMonoidHom A B W p (n + 1))
    (completedRelativeFormsHomotopy_eq A B W p n)
    (relativeFormsHomotopy_comp_coefficientFormsMap A B W n)

/-- `ĥ (ψ̂ x) = 0`, read on an element. -/
theorem completedRelativeFormsHomotopy_completedCoefficient (n : ℕ)
    (x : completedDividedPowerForms p A B.dividedPowers (n + 1)) :
    completedRelativeFormsHomotopy A B W p n
        (completedCoefficientFormsMap A B W p (n + 1) x) = 0 :=
  DFunLike.congr_fun (completedRelativeFormsHomotopy_comp_completedCoefficient A B W p n) x

/-- **`ε̂ ĥ = 0`**: the completed retraction kills the image of the completed homotopy. -/
theorem completedRelativeFormsRetraction_comp_completedRelativeFormsHomotopy (n : ℕ) :
    (completedRelativeFormsRetraction A B W p n).comp
        (completedRelativeFormsHomotopy A B W p n) = 0 :=
  PAdicCompletion.mapAddHom_comp_eq_zero p (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W) (B : Type uB)
    (relativeFormsHomotopy A B W n).toAddMonoidHom
    (relativeFormsRetraction A B W n).toAddMonoidHom
    (completedRelativeFormsHomotopy A B W p n)
    (completedRelativeFormsRetraction A B W p n)
    (completedRelativeFormsHomotopy_eq A B W p n)
    (completedRelativeFormsRetraction_eq A B W p n)
    (relativeFormsRetraction_comp_relativeFormsHomotopy A B W n)

/-- `ε̂ (ĥ y) = 0`, read on an element. -/
theorem completedRelativeFormsRetraction_completedRelativeFormsHomotopy (n : ℕ)
    (y : completedPolynomialForms A B W p (n + 1)) :
    completedRelativeFormsRetraction A B W p n
        (completedRelativeFormsHomotopy A B W p n y) = 0 :=
  DFunLike.congr_fun
    (completedRelativeFormsRetraction_comp_completedRelativeFormsHomotopy A B W p n) y

end Special

end DividedPowerPolynomial

end Crystalline

end
