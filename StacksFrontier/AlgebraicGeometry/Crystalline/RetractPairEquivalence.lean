module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BaseChangeRetractPair
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionCurvatureBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorRoundTrip
public import StacksFrontier.AlgebraicGeometry.Crystalline.ThetaMonomialFamily

/-!
# The equivalence of categories of pairs along a retract of divided power rings

Let `a : D → D'` and `b : D' → D` be maps of rings with `a ∘ b = id_{D'}`, where `D` is a
`p`-adically complete divided power ring whose module of differentials `Ω` is free on the
differentials `d x_i` of finitely many coordinates.  The proof of
[Stacks, Lemma 60.17.5, Tag 07L5] considers the base change functors

`F : (M, ∇) ↦ (M ⊗^∧_{D, a} D', ∇')`   and   `G : (M', ∇') ↦ (M' ⊗^∧_{D', b} D, ∇)`

and shows they are quasi-inverse equivalences between the pairs over `D` satisfying
[Stacks, Tag 07JB], [Stacks, Tag 07JC], [Stacks, Tag 07JD] and [Stacks, Tag 07JE] and the pairs
over `D'` satisfying the same four conditions, where — the footnote of the statement says the
last one "is tricky to formulate for `(M', ∇')` over `D'`" — the proof's definition is used:
"Let us say that `(M', ∇')` has property (07JE) if this is true for `G(M', ∇')`."

This module carries that out.

* The category over `D'` is `Crystalline.RetractPair`: a `p`-adically complete `D'`-module
  ([Stacks, Tag 07JB]) with a completed connection ([Stacks, Tag 07JC]) whose curvature vanishes
  ([Stacks, Tag 07JD], in the form of Remark [Stacks, Tag 07I0], which needs no coordinates) and
  whose base change along `b` is topologically quasi-nilpotent ([Stacks, Tag 07JE]) in the
  coordinates `x_i` of `D`, as the proof defines that condition.
* (07JD) passes along both base changes: the curvature of a base change is the base change of the
  curvature (`Crystalline.CompletedDeRham.isCurvatureZero_baseChange`), and over `D`
  vanishing curvature is commutation of the coordinate operators
  (`Crystalline.CompletedCoordinateData.isCurvatureZero_iff`).
* `F ∘ G ≅ 𝟭` is the collapse of the round trip along `a ∘ b = id`,
  `Crystalline.CompletedConnection.retractComparisonEquiv` — the source's "Since `a ∘ b = id_{D'}`
  we see that `F ∘ G` is the identity functor".
* `G ∘ F ≅ 𝟭` is the Taylor comparison `c_{id_D, b ∘ a}`, `Crystalline.taylorRoundTripEquiv`,
  whose horizontality — the step the source omits — is
  `Crystalline.coordOp_taylorRoundTrip`.

The data `Crystalline.CompletedCoordinateData` and `Crystalline.RetractData` are properties of
the rings, of their forms and of the maps, never of the pairs: Taylor's formula for `ρ = b ∘ a`
modulo every `p^n`, the divided power chain rule for `d`, the compatibilities of the comparisons
of forms, and the reading of the curvature in coordinates.  For the completed envelopes of the
lemma all of them are proved, in
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetractPairs.lean`.

## Main definitions

* `Crystalline.RetractPair` — the category of pairs over `D'`.
* `Crystalline.retractForwardFunctor` — the functor `F`.
* `Crystalline.retractBackFunctor` — the functor `G`.
* `Crystalline.retractPairEquivalence` — **the equivalence of categories**.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

/-! ### Preliminaries -/

section Preliminaries

/-- **Composite coordinate operators commute with every map commuting with the single ones.** -/
theorem IsThetaMonomialFamily.map_comm {M N : Type u} {ι : Type u} {theta : ι → (M → M)}
    {thetaPow : (ι →₀ ℕ) → (M → M)} {theta' : ι → (N → N)} {thetaPow' : (ι →₀ ℕ) → (N → N)}
    (h : IsThetaMonomialFamily M theta thetaPow) (h' : IsThetaMonomialFamily N theta' thetaPow')
    (φ : M → N) (hφ : ∀ i y, theta' i (φ y) = φ (theta i y)) (K : ι →₀ ℕ) (y : M) :
    thetaPow' K (φ y) = φ (thetaPow K y) := by
  classical
  induction K using Finsupp.induction generalizing y with
  | zero => rw [h.apply_zero, h'.apply_zero]; rfl
  | single_add a b K _ hb ih =>
    rw [add_comm, h.add_single, h'.add_single]
    simp only [Function.comp_apply]
    rw [ih]
    generalize thetaPow K y = z
    clear hb
    induction b with
    | zero => rfl
    | succ b ihb => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihb, hφ]

variable (p : ℕ) (D : DividedPowerRing.{u}) {ι : Type u} [DecidableEq ι]
  {M M₂ : Type u} [AddCommGroup M] [Module (D : Type u) M] [AddCommGroup M₂]
  [Module (D : Type u) M₂] {N : Type u} [AddCommGroup N] [Module (D : Type u) N]
  {thetaPow : (ι →₀ ℕ) → (M → M)} {thetaPow₂ : (ι →₀ ℕ) → (M₂ → M₂)}
  (hfin : ∀ (n : ℕ) (m : M),
    {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite)
  (hfin₂ : ∀ (n : ℕ) (m : M₂),
    {K : ι →₀ ℕ | thetaPow₂ K m ∉ pPowSmul p (D : Type u) M₂ n}.Finite)
  (hN : IsAdicComplete (pAdicIdeal (A := (D : Type u)) p) N)

omit [DecidableEq ι] in
/-- **A Taylor sum precomposed with a map commuting with the operators** is the Taylor sum of the
composite. -/
theorem taylorSum_precomp (incl : M₂ →+ N) (zeta : ι → (D : Type u)) (φ : M →+ M₂)
    (hφ : ∀ K y, thetaPow₂ K (φ y) = φ (thetaPow K y)) (m : M) :
    completeTaylorSum p D thetaPow₂ incl zeta hfin₂ hN (φ m) =
      completeTaylorSum p D thetaPow (incl.comp φ) zeta hfin hN m := by
  refine eq_taylorSum_of_forall p D thetaPow _ zeta hfin hN m _ fun n S hS ↦ ?_
  have hS₂ : ∀ K ∉ S, thetaPow₂ K (φ m) ∈ pPowSmul p (D : Type u) M₂ n := fun K hK ↦ by
    rw [hφ]; exact map_mem_pPowSmul_of_addMonoidHom p φ (hS K hK)
  have h := taylorSum_sub_sum_mem p D thetaPow₂ incl zeta hfin₂ hN (φ m) n S hS₂
  simpa [taylorSumTerm, hφ] using h

end Preliminaries

/-! ### Isomorphisms of pairs from horizontal equivalences -/

section PairIso

variable (p : ℕ) {D : Type u} [CommRing D] {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] {ι : Type u} {dx : ι → Omega} {d : D → Omega}

/-- The inverse of a horizontal linear equivalence is horizontal. -/
theorem horizontal_symm {M N : Type u} [AddCommGroup M] [Module D M] [AddCommGroup N]
    [Module D N] {nablaM : CompletedConnection p D Omega d M}
    {nablaN : CompletedConnection p D Omega d N} (e : M ≃ₗ[D] N)
    (he : ∀ m, nablaN (e m) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map e.toLinearMap (LinearMap.id (R := D) (M := Omega))) (nablaM m))
    (z : N) :
    nablaM (e.symm z) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map e.symm.toLinearMap (LinearMap.id (R := D) (M := Omega))) (nablaN z) := by
  obtain ⟨m, rfl⟩ := e.surjective z
  rw [he, ← CompletedConnection.valuesMap_eq, ← CompletedConnection.valuesMap_eq,
    ← CompletedConnection.valuesMap_comp, e.symm_apply_apply]
  have : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := by ext; simp
  rw [this]
  simp [CompletedConnection.valuesMap_eq]

/-- **An isomorphism of pairs from a horizontal linear equivalence.** -/
def Pair.isoOfHorizontalEquiv {P Q : Pair.{u, u, u, u} p D Omega dx d}
    (e : P.carrier ≃ₗ[D] Q.carrier)
    (he : ∀ m, Q.nabla (e m) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map e.toLinearMap (LinearMap.id (R := D) (M := Omega))) (P.nabla m)) :
    P ≅ Q where
  hom := ⟨e.toLinearMap, he⟩
  inv := ⟨e.symm.toLinearMap, horizontal_symm p e he⟩
  hom_inv_id := PairHom.ext (LinearMap.ext fun m ↦ e.symm_apply_apply m)
  inv_hom_id := PairHom.ext (LinearMap.ext fun m ↦ e.apply_symm_apply m)

end PairIso

/-! ### The data -/

/-- **Coordinates on a `p`-adically complete divided power ring**: a module `Ω` of differentials
with a divided power derivation `d : D → Ω` and a finite basis `d x_i` on the differentials of
finitely many elements `x_i`, together with the composite operators `∂_K = ∏_i ∂_i^{k_i}` of the
coordinate derivations `∂_i a = (d a)_i`.  This is the shape of the `p`-adically completed divided
power envelope `D` of a polynomial presentation and its `Ω_D` of [Stacks, Tag 07J9]. -/
structure CompletedCoordinateData (p : ℕ) (D : DividedPowerRing.{u}) where
  /-- The modules of forms `Ω^i`. -/
  Om : ℕ → Type u
  /-- Their additive group structures. -/
  [addCommGroup : ∀ i, AddCommGroup (Om i)]
  /-- Their `D`-module structures. -/
  [module : ∀ i, Module (D : Type u) (Om i)]
  /-- The wedge product `Ω^i × Ω^1 → Ω^{i+1}`. -/
  wedge : ∀ i, Om i →ₗ[(D : Type u)] Om 1 →ₗ[(D : Type u)] Om (i + 1)
  /-- The de Rham differential of the forms. -/
  deRham : ∀ i, Om i →+ Om (i + 1)
  /-- The differential `d : D → Ω^1`. -/
  diff : D.carrier → Om 1
  /-- `d` is additive. -/
  diff_add : ∀ x y : (D : Type u), diff (x + y) = diff x + diff y
  /-- `d` obeys the Leibniz rule. -/
  diff_mul : ∀ x y : (D : Type u), diff (x * y) = x • diff y + y • diff x
  /-- `d` obeys the divided power chain rule. -/
  diff_dpow : ∀ (n : ℕ), 0 < n → ∀ x ∈ D.ideal,
    diff (D.dividedPowers.dpow n x) = D.dividedPowers.dpow (n - 1) x • diff x
  /-- The Leibniz rule `d (f ω) = f d ω + ω ∧ d f` of the forms. -/
  isGradedLeibniz : CompletedDeRham.IsGradedLeibniz (D : Type u) Om wedge deRham diff
  /-- The wedge product of one-forms is antisymmetric. -/
  wedge_anti : ∀ η ζ : Om 1, wedge 1 η ζ + wedge 1 ζ η = 0
  /-- Exact one-forms are closed. -/
  deRham_diff : ∀ c : (D : Type u), deRham 1 (diff c) = 0
  /-- The index type of the coordinates. -/
  ι : Type u
  /-- The coordinates are finitely many. -/
  [fintype : Fintype ι]
  /-- Decidable equality of coordinates. -/
  [decEq : DecidableEq ι]
  /-- The coordinates `x_i`. -/
  coord : ι → (D : Type u)
  /-- The basis `d x_i` of `Ω^1`. -/
  basis : Module.Basis ι (D : Type u) (Om 1)
  /-- The basis vectors are the differentials of the coordinates. -/
  basis_eq : ∀ i, basis i = diff (coord i)
  /-- The composite coordinate derivations `∂_K`. -/
  deltaPow : (ι →₀ ℕ) → (D.carrier → D.carrier)
  /-- `∂_K = ∏_i ∂_i^{k_i}` for the coordinate derivations `∂_i a = (d a)_i`. -/
  isThetaMonomialFamily : IsThetaMonomialFamily (D : Type u) (fun i a ↦ basis.repr (diff a) i)
    deltaPow
  /-- In the coordinates, integrability in the sense of Remark [Stacks, Tag 07I0] — the
  vanishing of the curvature — is the commutation of the coordinate operators. -/
  isCurvatureZero_iff : ∀ {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
    (hM : IsPAdicallyComplete p D M) (nabla : CompletedConnection p D (Om 1) diff M),
    CompletedDeRham.IsCurvatureZero p (D : Type u) Om wedge deRham M nabla isGradedLeibniz ↔
      ∀ j k, coordOp p basis hM nabla j ∘ coordOp p basis hM nabla k =
        coordOp p basis hM nabla k ∘ coordOp p basis hM nabla j

attribute [instance] CompletedCoordinateData.addCommGroup CompletedCoordinateData.module
  CompletedCoordinateData.fintype CompletedCoordinateData.decEq

namespace CompletedCoordinateData

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateData p D)

/-- The module of one-forms `Ω = Ω^1`. -/
abbrev forms : Type u := C.Om 1

/-- The family `d x_i` of differentials of the coordinates. -/
abbrev dx : C.ι → C.forms := fun i ↦ C.diff (C.coord i)

/-- The basis is the family `d x_i`. -/
theorem dx_eq (i : C.ι) : C.dx i = C.basis i := (C.basis_eq i).symm

/-- `d` as a divided power derivation over `ℤ`. -/
def toDividedPowerDerivation : DividedPowerDerivation ℤ D (Int.castRingHom D) C.forms where
  toDerivation := Derivation.mk' (AddMonoidHom.mk' C.diff C.diff_add).toIntLinearMap C.diff_mul
  map_ringHom' a := by
    change C.diff ((a : ℤ) : (D : Type u)) = 0
    have h1 : C.diff 1 = 0 := by simpa using C.diff_mul 1 1
    have h := (AddMonoidHom.mk' C.diff C.diff_add).map_zsmul a (1 : (D : Type u))
    simp only [AddMonoidHom.mk'_apply, zsmul_eq_mul, mul_one] at h
    rw [h, h1, smul_zero]
  map_dpow' n hn x hx := C.diff_dpow n hn x hx

/-- **The divided power derivative of a divided power monomial**,
`d(ξ^{[K]}) = ∑_i ξ^{[K - e_i]} d ξ_i`. -/
theorem diff_taylorMonomial {xi : C.ι → (D : Type u)} (hxi : ∀ i, xi i ∈ D.ideal)
    (K : C.ι →₀ ℕ) :
    C.diff (taylorMonomial D xi K) =
      ∑ i ∈ K.support, taylorMonomial D xi (K - Finsupp.single i 1) • C.diff (xi i) :=
  dividedPowerDerivation_taylorMonomial C.toDividedPowerDerivation hxi K

end CompletedCoordinateData

/-- **A retract `a ∘ b = id` of rings with differentials** over the coordinates `C` of `D`:
ring maps `a : D → D'` and `b : D' → D` with `a ∘ b = id_{D'}`, a module `Ω'` of differentials of
`D'` with its differential, the comparisons `ψ_a : Ω → Ω'` and `ψ_b : Ω' → Ω` of Remark
[Stacks, Tag 07KJ] with `ψ_a ∘ ψ_b = id`, and, for the round trip `ρ = b ∘ a`, its compatibility
with the augmentation and **Taylor's formula** `a = ∑_J ρ(∂_J a) ξ^{[J]}`,
`ρ(a) = ∑_J ∂_J(a) (-ξ)^{[J]}` for `ξ_i = x_i - ρ(x_i)`, modulo every `p^n`. -/
structure RetractData (p : ℕ) (D : DividedPowerRing.{u}) (C : CompletedCoordinateData p D) where
  /-- The ring `D'`. -/
  ring : Type u
  /-- Its ring structure. -/
  [commRing : CommRing ring]
  /-- The map `a : D → D'`. -/
  [algebraA : Algebra (D : Type u) ring]
  /-- The map `b : D' → D`. -/
  [algebraB : Algebra ring (D : Type u)]
  /-- `a ∘ b = id_{D'}`. -/
  [retract : IsScalarTower ring (D : Type u) ring]
  /-- The modules of forms `Ω'^i` of `D'`. -/
  Om : ℕ → Type u
  /-- Their additive group structures. -/
  [addCommGroup : ∀ i, AddCommGroup (Om i)]
  /-- Their `D'`-module structures. -/
  [module : ∀ i, Module ring (Om i)]
  /-- The wedge product of the forms of `D'`. -/
  wedge : ∀ i, Om i →ₗ[ring] Om 1 →ₗ[ring] Om (i + 1)
  /-- The de Rham differential of the forms of `D'`. -/
  deRham : ∀ i, Om i →+ Om (i + 1)
  /-- The differential `d' : D' → Ω'^1`. -/
  diff : ring → Om 1
  /-- `d'` is additive. -/
  diff_add : ∀ x y : ring, diff (x + y) = diff x + diff y
  /-- `d'` obeys the Leibniz rule. -/
  diff_mul : ∀ x y : ring, diff (x * y) = x • diff y + y • diff x
  /-- The Leibniz rule of the forms of `D'`. -/
  isGradedLeibniz : CompletedDeRham.IsGradedLeibniz ring Om wedge deRham diff
  /-- The wedge product of one-forms of `D'` is antisymmetric. -/
  wedge_anti : ∀ η ζ : Om 1, wedge 1 η ζ + wedge 1 ζ η = 0
  /-- Exact one-forms of `D'` are closed. -/
  deRham_diff : ∀ c : ring, deRham 1 (diff c) = 0
  /-- The comparisons `ψ_a : Ω^i → Ω'^i` along `a`. -/
  psiA : ∀ i, C.Om i →ₛₗ[algebraMap (D : Type u) ring] Om i
  /-- The comparisons `ψ_b : Ω'^i → Ω^i` along `b`. -/
  psiB : ∀ i, Om i →ₛₗ[algebraMap ring (D : Type u)] C.Om i
  /-- `ψ_a (d x) = d' (a x)`. -/
  psiA_diff : ∀ x : (D : Type u), psiA 1 (C.diff x) = diff (algebraMap (D : Type u) ring x)
  /-- `ψ_b (d' x) = d (b x)`. -/
  psiB_diff : ∀ x : ring, psiB 1 (diff x) = C.diff (algebraMap ring (D : Type u) x)
  /-- `ψ_a` is multiplicative for the wedge product. -/
  psiA_wedge : ∀ (i : ℕ) (ω : C.Om i) (η : C.Om 1),
    psiA (i + 1) (C.wedge i ω η) = wedge i (psiA i ω) (psiA 1 η)
  /-- `ψ_b` is multiplicative for the wedge product. -/
  psiB_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psiB (i + 1) (wedge i ω η) = C.wedge i (psiB i ω) (psiB 1 η)
  /-- `ψ_a` commutes with the de Rham differentials. -/
  psiA_deRham : ∀ (i : ℕ) (ω : C.Om i), psiA (i + 1) (C.deRham i ω) = deRham i (psiA i ω)
  /-- `ψ_b` commutes with the de Rham differentials. -/
  psiB_deRham : ∀ (i : ℕ) (ω : Om i), psiB (i + 1) (deRham i ω) = C.deRham i (psiB i ω)
  /-- `ψ_a ∘ ψ_b = id` on one-forms. -/
  psiA_psiB : ∀ ω : Om 1, psiA 1 (psiB 1 ω) = ω
  /-- The round trip `ρ = b ∘ a` moves elements within the divided power ideal. -/
  rho_sub_mem : ∀ y : (D : Type u),
    algebraMap ring (D : Type u) (algebraMap (D : Type u) ring y) - y ∈ D.ideal
  /-- Taylor's formula `a = ∑_J ρ(∂_J a) ξ^{[J]}` modulo every `p^n`. -/
  taylor : ∀ (a : (D : Type u)) (n : ℕ), ∃ T : Finset (C.ι →₀ ℕ),
    (∀ J ∉ T, C.deltaPow J a ∈ pAdicIdeal (A := (D : Type u)) p ^ n) ∧
      a - ∑ J ∈ T, algebraMap ring (D : Type u) (algebraMap (D : Type u) ring (C.deltaPow J a)) *
        taylorMonomial D (fun i ↦ C.coord i -
          algebraMap ring (D : Type u) (algebraMap (D : Type u) ring (C.coord i))) J ∈
        pAdicIdeal (A := (D : Type u)) p ^ n
  /-- Taylor's formula `ρ(a) = ∑_J ∂_J(a) (-ξ)^{[J]}` modulo every `p^n`. -/
  taylor' : ∀ (a : (D : Type u)) (n : ℕ), ∃ T : Finset (C.ι →₀ ℕ),
    (∀ J ∉ T, C.deltaPow J a ∈ pAdicIdeal (A := (D : Type u)) p ^ n) ∧
      algebraMap ring (D : Type u) (algebraMap (D : Type u) ring a) -
        ∑ J ∈ T, C.deltaPow J a * taylorMonomial D (-fun i ↦ C.coord i -
          algebraMap ring (D : Type u) (algebraMap (D : Type u) ring (C.coord i))) J ∈
        pAdicIdeal (A := (D : Type u)) p ^ n

attribute [instance] RetractData.commRing RetractData.algebraA RetractData.algebraB
  RetractData.retract RetractData.addCommGroup RetractData.module

/-- The module of one-forms `Ω' = Ω'^1` of `D'`. -/
abbrev RetractData.forms {p : ℕ} {D : DividedPowerRing.{u}} {C : CompletedCoordinateData p D}
    (R : RetractData p D C) : Type u :=
  R.Om 1

/-! ### The category of pairs over `D'` -/

section Category

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateData p D)
  (R : RetractData p D C)

/-- **A pair over `D'`** in the sense of [Stacks, Lemma 60.17.5, Tag 07L5]: a `p`-adically
complete `D'`-module ([Stacks, Tag 07JB]) with a completed connection
`∇' : M' → M' ⊗̂_{D'} Ω'` ([Stacks, Tag 07JC]) which is integrable — its curvature
`M' → M' ⊗̂ Ω'^2` vanishes, Remark [Stacks, Tag 07I0], [Stacks, Tag 07JD] — and topologically
quasi-nilpotent in the sense the proof of the lemma gives the condition over `D'`: "Let us say
that `(M', ∇')` has property (07JE) if this is true for `G(M', ∇')`", `G` being the base change
along `b : D' → D`.  The footnote of the statement records why: (07JE) "is tricky to formulate
for `(M', ∇')` over `D'`", the module `Ω'` having no coordinates of its own. -/
structure RetractPair where
  /-- The underlying module `M'`. -/
  carrier : Type u
  /-- Its additive group structure. -/
  [addCommGroup : AddCommGroup carrier]
  /-- Its `D'`-module structure. -/
  [module : Module R.ring carrier]
  /-- The module is `p`-adically complete. -/
  isPAdicallyComplete : IsPAdicallyComplete p R.ring carrier
  /-- The connection `∇' : M' → M' ⊗̂_{D'} Ω'`. -/
  nabla : CompletedConnection p R.ring R.forms R.diff carrier
  /-- The connection is integrable: its curvature vanishes (Remark [Stacks, Tag 07I0]). -/
  isIntegrable : CompletedDeRham.IsCurvatureZero p R.ring R.Om R.wedge R.deRham carrier nabla
    R.isGradedLeibniz
  /-- The base change of the connection along `b` is topologically quasi-nilpotent. -/
  isTopologicallyQuasiNilpotent_back : IsTopologicallyQuasiNilpotent p D C.forms C.dx
    (CompletedConnection.baseChange p R.ring D carrier R.forms C.forms C.diff (R.psiB 1) nabla
      C.diff_add C.diff_mul R.psiB_diff)

attribute [instance] RetractPair.addCommGroup RetractPair.module

/-- A morphism of pairs over `D'`: a horizontal `D'`-linear map. -/
@[ext] structure RetractPairHom (P Q : RetractPair C R) where
  /-- The underlying `D'`-linear map. -/
  toLinearMap : P.carrier →ₗ[R.ring] Q.carrier
  /-- Horizontality: the map commutes with the two connections. -/
  horizontal : ∀ m : P.carrier, Q.nabla (toLinearMap m) =
    AdicCompletion.map (pAdicIdeal (A := R.ring) p)
      (TensorProduct.map toLinearMap (LinearMap.id (R := R.ring) (M := R.forms))) (P.nabla m)

/-- The pairs over `D'` and their horizontal maps form a category. -/
instance : Category (RetractPair C R) where
  Hom P Q := RetractPairHom C R P Q
  id P := ⟨LinearMap.id, by intro m; simp⟩
  comp {P Q R'} f g := ⟨g.toLinearMap ∘ₗ f.toLinearMap, by
    intro m
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [g.horizontal, f.horizontal, AdicCompletion.map_comp_apply, ← TensorProduct.map_comp]
    simp⟩
  id_comp f := by apply RetractPairHom.ext; simp
  comp_id f := by apply RetractPairHom.ext; simp
  assoc f g h := by apply RetractPairHom.ext; simp [LinearMap.comp_assoc]

/-- The underlying map of an identity morphism of pairs over `D'`. -/
@[simp] theorem RetractPair.id_toLinearMap (P : RetractPair C R) :
    RetractPairHom.toLinearMap (𝟙 P) = LinearMap.id := rfl

/-- The underlying map of a composite of morphisms of pairs over `D'`. -/
@[simp] theorem RetractPair.comp_toLinearMap {P Q Q' : RetractPair C R} (f : P ⟶ Q)
    (g : Q ⟶ Q') : RetractPairHom.toLinearMap (f ≫ g) = g.toLinearMap ∘ₗ f.toLinearMap := rfl

/-- **An isomorphism of pairs over `D'` from a horizontal linear equivalence.** -/
def RetractPair.isoOfHorizontalEquiv {P Q : RetractPair C R} (e : P.carrier ≃ₗ[R.ring] Q.carrier)
    (he : ∀ m, Q.nabla (e m) = AdicCompletion.map (pAdicIdeal (A := R.ring) p)
      (TensorProduct.map e.toLinearMap (LinearMap.id (R := R.ring) (M := R.forms))) (P.nabla m)) :
    P ≅ Q where
  hom := ⟨e.toLinearMap, he⟩
  inv := ⟨e.symm.toLinearMap, horizontal_symm p e he⟩
  hom_inv_id := RetractPairHom.ext (LinearMap.ext fun m ↦ e.symm_apply_apply m)
  inv_hom_id := RetractPairHom.ext (LinearMap.ext fun m ↦ e.apply_symm_apply m)

/-- The underlying map of an identity morphism of pairs over `D`. -/
@[simp] theorem Pair.id_toLinearMap' {Omega : Type u} [AddCommGroup Omega]
    [Module (D : Type u) Omega] {ι' : Type u} {dx' : ι' → Omega} {d : D.carrier → Omega}
    (P : Pair.{u, u, u, u} p D Omega dx' d) :
    PairHom.toLinearMap (𝟙 P) = LinearMap.id := rfl

/-- The underlying map of a composite of morphisms of pairs over `D`. -/
@[simp] theorem Pair.comp_toLinearMap' {Omega : Type u} [AddCommGroup Omega]
    [Module (D : Type u) Omega] {ι' : Type u} {dx' : ι' → Omega} {d : D.carrier → Omega}
    {P Q Q' : Pair.{u, u, u, u} p D Omega dx' d} (f : P ⟶ Q) (g : Q ⟶ Q') :
    PairHom.toLinearMap (f ≫ g) = g.toLinearMap ∘ₗ f.toLinearMap := rfl

end Category

/-! ### The functor `G` -/

section Back

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateData p D)
  (R : RetractData p D C)

/-- **The functor `G` on objects**: the base change of a pair over `D'` along `b`. -/
def retractBack (P : RetractPair C R) : Pair.{u, u, u, u} p D C.forms C.dx C.diff where
  carrier := CompletedConnection.baseChangeCarrier p R.ring D P.carrier
  isPAdicallyComplete := CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _
  nabla := CompletedConnection.baseChange p R.ring D P.carrier R.forms C.forms C.diff (R.psiB 1)
    P.nabla C.diff_add C.diff_mul R.psiB_diff
  hasCoordinateOperators := ⟨_, isCoordinateExpansion_coordOp p C.basis
    (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _) _ C.dx_eq⟩
  isIntegrable := by
    intro theta hco i j
    have hN := CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D P.carrier
    rw [eq_coordOp_of_isCoordinateExpansion p C.basis hN _ C.dx_eq hco]
    exact (C.isCurvatureZero_iff hN _).mp (CompletedDeRham.isCurvatureZero_baseChange p
      R.ring D P.carrier R.Om C.Om R.psiB R.wedge C.wedge R.deRham C.deRham C.diff P.nabla
      C.diff_add C.diff_mul R.psiB_diff R.isGradedLeibniz C.isGradedLeibniz R.psiB_wedge
      R.psiB_deRham C.wedge_anti C.deRham_diff P.isIntegrable) i j
  isTopologicallyQuasiNilpotent := P.isTopologicallyQuasiNilpotent_back

/-- **The functor `G`**: base change of pairs along `b : D' → D`. -/
def retractBackFunctor : RetractPair C R ⥤ Pair.{u, u, u, u} p D C.forms C.dx C.diff where
  obj P := retractBack C R P
  map {P Q} f :=
    { toLinearMap := CompletedConnection.baseChangeModuleMap p R.ring D P.carrier Q.carrier
        f.toLinearMap
      horizontal := fun x ↦ by
        have h := CompletedConnection.baseChange_baseChangeModuleMap p R.ring D P.carrier
          Q.carrier R.forms C.forms C.diff (R.psiB 1) P.nabla Q.nabla C.diff_add C.diff_mul
          R.psiB_diff f.toLinearMap
          (fun m ↦ by rw [f.horizontal m, CompletedConnection.valuesMap_eq]) x
        rwa [CompletedConnection.valuesMap_eq] at h }
  map_id P := PairHom.ext (CompletedConnection.baseChangeModuleMap_id p R.ring D P.carrier)
  map_comp f g := PairHom.ext (LinearMap.ext fun x ↦
    CompletedConnection.baseChangeModuleMap_comp p R.ring D _ _ _ f.toLinearMap g.toLinearMap x)

end Back

/-- Two linear maps out of a twice completed base change agree when they agree on
`m ↦ 1 ⊗ (1 ⊗ m)`. -/
private theorem baseChangeCarrier_baseChangeCarrier_ext (p : ℕ) (D₀ D₁ D₂ : Type u) [CommRing D₀]
    [CommRing D₁] [CommRing D₂] [Algebra D₀ D₁] [Algebra D₁ D₂] (M : Type u) [AddCommGroup M]
    [Module D₀ M] {N : Type u} [AddCommGroup N] [Module D₂ N]
    (hN : IsHausdorff (pAdicIdeal (A := D₂) p) N)
    (f g : CompletedConnection.baseChangeCarrier p D₁ D₂
      (CompletedConnection.baseChangeCarrier p D₀ D₁ M) →ₗ[D₂] N)
    (h : ∀ m, f (CompletedConnection.baseChangeInclusion p D₁ D₂ _
        (CompletedConnection.baseChangeInclusion p D₀ D₁ M m)) =
      g (CompletedConnection.baseChangeInclusion p D₁ D₂ _
        (CompletedConnection.baseChangeInclusion p D₀ D₁ M m))) : f = g := by
  have h₁ : ∀ y, f (CompletedConnection.baseChangeInclusion p D₁ D₂ _ y) =
      g (CompletedConnection.baseChangeInclusion p D₁ D₂ _ y) := fun y ↦
    DFunLike.congr_fun (CompletedConnection.baseChangeCarrier_ext p D₀ D₁ M (algebraMap D₁ D₂) hN
      (ψ := f.toAddMonoidHom.comp
        (CompletedConnection.baseChangeInclusion p D₁ D₂ _).toAddMonoidHom)
      (ψ' := g.toAddMonoidHom.comp
        (CompletedConnection.baseChangeInclusion p D₁ D₂ _).toAddMonoidHom)
      (fun c x ↦ by
        change f (CompletedConnection.baseChangeInclusion p D₁ D₂ _ (c • x)) = _
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smul]; rfl)
      (fun c x ↦ by
        change g (CompletedConnection.baseChangeInclusion p D₁ D₂ _ (c • x)) = _
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smul]; rfl) h) y
  exact LinearMap.ext fun z ↦ DFunLike.congr_fun (CompletedConnection.baseChangeCarrier_ext p D₁ D₂
    (CompletedConnection.baseChangeCarrier p D₀ D₁ M) (RingHom.id _) hN
    (ψ := f.toAddMonoidHom) (ψ' := g.toAddMonoidHom) (fun c x ↦ by simp) (fun c x ↦ by simp) h₁) z

/-! ### The round trip -/

section RoundTrip

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateData p D)
  (R : RetractData p D C)

/-- The round trip `ρ = b ∘ a : D → D`. -/
abbrev RetractData.rho : (D : Type u) →+* (D : Type u) :=
  (algebraMap R.ring (D : Type u)).comp (algebraMap (D : Type u) R.ring)

/-- The coordinate differences `ξ_i = x_i - ρ(x_i)`. -/
abbrev RetractData.xi (i : C.ι) : (D : Type u) := C.coord i - R.rho C (C.coord i)

/-- The coordinate differences `ξ_i` lie in the divided power ideal. -/
theorem RetractData.xi_mem (i : C.ι) : R.xi C i ∈ D.ideal := by
  simpa [RetractData.xi] using D.ideal.neg_mem (R.rho_sub_mem (C.coord i))

/-- The twice base-changed module `G(F(M))`. -/
abbrev roundTripCarrier (M : Type u) [AddCommGroup M] [Module (D : Type u) M] : Type u :=
  CompletedConnection.baseChangeCarrier p R.ring D
    (CompletedConnection.baseChangeCarrier p D R.ring M)

/-- The twice base-changed connection of `G(F(M, ∇))`. -/
abbrev roundTripNabla {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
    (nabla : CompletedConnection p D C.forms C.diff M) :
    CompletedConnection p D C.forms C.diff (roundTripCarrier C R M) :=
  CompletedConnection.baseChange p R.ring D _ R.forms C.forms C.diff (R.psiB 1)
    (CompletedConnection.baseChange p D R.ring M C.forms R.forms R.diff (R.psiA 1) nabla R.diff_add
      R.diff_mul R.psiA_diff) C.diff_add C.diff_mul R.psiB_diff

/-- The `ρ`-semilinear inclusion `m ↦ 1 ⊗ (1 ⊗ m)` of `M` into `G(F(M))`. -/
def roundTripIncl (M : Type u) [AddCommGroup M] [Module (D : Type u) M] :
    M →ₛₗ[R.rho C] roundTripCarrier C R M where
  toFun m := CompletedConnection.baseChangeInclusion p R.ring D _
    (CompletedConnection.baseChangeInclusion p D R.ring M m)
  map_add' m m' := by rw [map_add, map_add]
  map_smul' c m := by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]; rfl

/-- The inclusion `m ↦ 1 ⊗ (1 ⊗ m)` as a formula. -/
theorem roundTripIncl_apply (M : Type u) [AddCommGroup M] [Module (D : Type u) M] (m : M) :
    roundTripIncl C R M m = CompletedConnection.baseChangeInclusion p R.ring D _
      (CompletedConnection.baseChangeInclusion p D R.ring M m) := rfl

/-- **Existence half of the universal property of `G(F(M))`** for a `ρ`-semilinear map into a
`p`-adically complete module. -/
theorem roundTrip_exists_lift (M : Type u) [AddCommGroup M] [Module (D : Type u) M]
    {N : Type u} [AddCommGroup N] [Module (D : Type u) N] (hN : IsPAdicallyComplete p D N)
    (φ : M →+ N) (hφ : ∀ (c : (D : Type u)) (m : M), φ (c • m) = R.rho C c • φ m) :
    ∃ ψ : roundTripCarrier C R M →ₗ[(D : Type u)] N, ∀ m, ψ (roundTripIncl C R M m) = φ m := by
  obtain ⟨ψ₁, hψ₁, hψ₁i⟩ := CompletedConnection.exists_baseChange_lift p D R.ring M
    (algebraMap R.ring (D : Type u)) hN φ hφ
  obtain ⟨ψ₂, hψ₂, hψ₂i⟩ := CompletedConnection.exists_baseChange_lift p R.ring D
    (CompletedConnection.baseChangeCarrier p D R.ring M) (RingHom.id _) hN ψ₁ hψ₁
  refine ⟨{ toFun := ψ₂, map_add' := map_add ψ₂, map_smul' := hψ₂ }, fun m ↦ ?_⟩
  change ψ₂ (CompletedConnection.baseChangeInclusion p R.ring D _
    (CompletedConnection.baseChangeInclusion p D R.ring M m)) = φ m
  rw [hψ₂i, hψ₁i]

/-- **Uniqueness half of the universal property of `G(F(M))`**. -/
theorem roundTrip_ext (M : Type u) [AddCommGroup M] [Module (D : Type u) M]
    {N : Type u} [AddCommGroup N] [Module (D : Type u) N] (hN : IsPAdicallyComplete p D N)
    (f g : roundTripCarrier C R M →ₗ[(D : Type u)] N)
    (h : ∀ m, f (roundTripIncl C R M m) = g (roundTripIncl C R M m)) : f = g := by
  exact baseChangeCarrier_baseChangeCarrier_ext p D R.ring D M hN.toIsHausdorff f g h

/-- **The connection of `G(F(M, ∇))` on `1 ⊗ (1 ⊗ m)`** is `∑_i ι(θ_i m) ⊗ d ρ(x_i)`. -/
theorem roundTripNabla_incl {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
    (hM : IsPAdicallyComplete p D M) (nabla : CompletedConnection p D C.forms C.diff M) (m : M) :
    roundTripNabla C R nabla (roundTripIncl C R M m) =
      toCompletedTensor p D C.forms (roundTripCarrier C R M)
        (∑ i, roundTripIncl C R M (coordOp p C.basis hM nabla i m) ⊗ₜ[(D : Type u)]
          C.diff (R.rho C (C.coord i))) := by
  rw [roundTripIncl_apply, CompletedConnection.baseChange_inclusion,
    CompletedConnection.baseChange_inclusion, nabla_eq_sum_coordOp p C.basis hM nabla, map_sum,
    map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [CompletedConnection.baseChangeValues_of_tmul, CompletedConnection.baseChangeValues_of_tmul,
    C.basis_eq, R.psiA_diff, R.psiB_diff, roundTripIncl_apply]
  rfl

/-- The composite coordinate operators of a pair over `D`. -/
theorem Pair.exists_thetaPow (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    ∃ thetaPow : (C.ι →₀ ℕ) → (P.carrier → P.carrier),
      IsThetaMonomialFamily P.carrier (coordOp p C.basis P.isPAdicallyComplete P.nabla)
        thetaPow :=
  exists_isThetaMonomialFamily _ (P.isIntegrable _
    (isCoordinateExpansion_coordOp p C.basis P.isPAdicallyComplete P.nabla C.dx_eq))

/-- **The composite coordinate operators `θ_K = ∏_i θ_i^{k_i}` of a pair over `D`.** -/
def Pair.thetaPow (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    (C.ι →₀ ℕ) → (P.carrier → P.carrier) :=
  (Pair.exists_thetaPow C P).choose

/-- The operators `Crystalline.Pair.thetaPow` are a composite coordinate operator family. -/
theorem Pair.isThetaMonomialFamily_thetaPow (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    IsThetaMonomialFamily P.carrier (coordOp p C.basis P.isPAdicallyComplete P.nabla)
      (Pair.thetaPow C P) :=
  (Pair.exists_thetaPow C P).choose_spec

/-- **Item (07JE) of a pair over `D`, at every level**: only finitely many composite operators
take a given element outside `p^n M`. -/
theorem Pair.finite_thetaPow (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) (n : ℕ)
    (m : P.carrier) :
    {K : C.ι →₀ ℕ | Pair.thetaPow C P K m ∉ pPowSmul p (D : Type u) P.carrier n}.Finite :=
  finite_thetaPow_notMem_pPowSmul p (D : Type u) P.carrier
    (Pair.isThetaMonomialFamily_thetaPow C P)
    (coordOp_add p C.basis P.isPAdicallyComplete P.nabla)
    (fun i m ↦ by
      have h := P.isTopologicallyQuasiNilpotent _
        (isCoordinateExpansion_coordOp p C.basis P.isPAdicallyComplete P.nabla C.dx_eq) m
      exact (h.preimage (f := fun k : ℕ ↦ (i, k)) fun _ _ _ _ h ↦ by
        simpa using h).subset fun k hk ↦ hk)
    (Set.toFinite _)

/-- **The comparison `c_{id_D, b ∘ a} : M ≃ G(F(M))`** of a pair over `D`, with its
horizontality and its formula.  This is `Crystalline.taylorRoundTripEquiv` for the round trip
`ρ = b ∘ a`, the inclusion `m ↦ 1 ⊗ (1 ⊗ m)` and the coordinate differences
`ξ_i = x_i - ρ(x_i)`; its horizontality, the step the source omits, is
`Crystalline.coordOp_taylorRoundTrip`. -/
theorem Pair.exists_roundTripEquiv (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    ∃ e : P.carrier ≃ₗ[(D : Type u)] roundTripCarrier C R P.carrier,
      (∀ m, roundTripNabla C R P.nabla (e m) = AdicCompletion.map (pAdicIdeal (A := (D : Type u)) p)
            (TensorProduct.map e.toLinearMap (LinearMap.id (R := (D : Type u)) (M := C.forms)))
            (P.nabla m)) ∧
        ∀ m, e m = completeTaylorSum p D (Pair.thetaPow C P)
          (roundTripIncl C R P.carrier).toAddMonoidHom (R.xi C) (Pair.finite_thetaPow C P)
          (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _) m := by
  have hM := P.isPAdicallyComplete
  have hN : IsPAdicallyComplete p D (roundTripCarrier C R P.carrier) :=
    CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _
  refine ⟨taylorRoundTripEquiv p D C.basis hM P.nabla (Pair.isThetaMonomialFamily_thetaPow C P)
    (Pair.finite_thetaPow C P) hN (R.rho C) (roundTripIncl C R P.carrier) (R.xi C) (R.xi_mem C)
    C.isThetaMonomialFamily (fun _ _ ↦ rfl) R.taylor R.taylor'
    (roundTrip_exists_lift C R P.carrier hM) (roundTrip_ext C R P.carrier hN), ?_,
    fun m ↦ rfl⟩
  intro m
  refine horizontal_of_coordOp p C.basis hM P.nabla hN _ _ (fun j m ↦ ?_) m
  exact coordOp_taylorRoundTrip p D C.basis hM P.nabla (Pair.isThetaMonomialFamily_thetaPow C P)
    (Pair.finite_thetaPow C P) hN _ (R.rho C) (roundTripIncl C R P.carrier) C.coord C.basis_eq
    (R.xi C) (fun i ↦ by rw [← C.diff_add, add_sub_cancel]) (C.diff_taylorMonomial (R.xi_mem C))
    (roundTripNabla_incl C R hM P.nabla) j m

/-- **The comparison `c_{id_D, b ∘ a} : M ≃ G(F(M))`** of a pair over `D`. -/
def Pair.roundTripEquiv (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    P.carrier ≃ₗ[(D : Type u)] roundTripCarrier C R P.carrier :=
  (Pair.exists_roundTripEquiv C R P).choose

/-- **The comparison is horizontal**, the step the proof of [Stacks, Lemma 60.17.5, Tag 07L5]
omits. -/
theorem Pair.roundTripEquiv_horizontal (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff)
    (m : P.carrier) :
    roundTripNabla C R P.nabla (Pair.roundTripEquiv C R P m) =
      AdicCompletion.map (pAdicIdeal (A := (D : Type u)) p)
        (TensorProduct.map (Pair.roundTripEquiv C R P).toLinearMap
          (LinearMap.id (R := (D : Type u)) (M := C.forms))) (P.nabla m) :=
  (Pair.exists_roundTripEquiv C R P).choose_spec.1 m

/-- **The comparison is the Taylor sum** `m ↦ ∑_K ξ^{[K]} ⊗ θ_K(m)`. -/
theorem Pair.roundTripEquiv_apply (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff)
    (m : P.carrier) :
    Pair.roundTripEquiv C R P m = completeTaylorSum p D (Pair.thetaPow C P)
      (roundTripIncl C R P.carrier).toAddMonoidHom (R.xi C) (Pair.finite_thetaPow C P)
      (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _) m :=
  (Pair.exists_roundTripEquiv C R P).choose_spec.2 m

end RoundTrip

/-! ### The functor `F` and the equivalence -/

section Equivalence

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateData p D)
  (R : RetractData p D C)

/-- **The functor `F` on objects**: the base change of a pair over `D` along `a`.  Its curvature
vanishes because that of the pair does, the pair's coordinate operators commuting; its base
change back along `b` is topologically quasi-nilpotent because it is isomorphic to the pair itself
by the horizontal comparison `Crystalline.Pair.roundTripEquiv`. -/
def retractForward (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) : RetractPair C R where
  carrier := CompletedConnection.baseChangeCarrier p D R.ring P.carrier
  isPAdicallyComplete := CompletedConnection.isPAdicallyComplete_baseChangeCarrier p D R.ring _
  nabla := CompletedConnection.baseChange p D R.ring P.carrier C.forms R.forms R.diff (R.psiA 1)
    P.nabla R.diff_add R.diff_mul R.psiA_diff
  isIntegrable := CompletedDeRham.isCurvatureZero_baseChange p D R.ring P.carrier C.Om
    R.Om (R.psiA) C.wedge R.wedge C.deRham R.deRham R.diff P.nabla R.diff_add R.diff_mul
    R.psiA_diff C.isGradedLeibniz R.isGradedLeibniz R.psiA_wedge R.psiA_deRham R.wedge_anti
    R.deRham_diff ((C.isCurvatureZero_iff P.isPAdicallyComplete P.nabla).mpr fun j k ↦
      P.isIntegrable _ (isCoordinateExpansion_coordOp p C.basis P.isPAdicallyComplete P.nabla
        C.dx_eq) j k)
  isTopologicallyQuasiNilpotent_back := (Pair.ofHorizontalEquiv p C.basis C.dx_eq P
    (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _)
    (roundTripNabla C R P.nabla) (Pair.roundTripEquiv C R P)
    (Pair.roundTripEquiv_horizontal C R P)).isTopologicallyQuasiNilpotent

/-- **The functor `F`**: base change of pairs along `a : D → D'`. -/
def retractForwardFunctor : Pair.{u, u, u, u} p D C.forms C.dx C.diff ⥤ RetractPair C R where
  obj P := retractForward C R P
  map {P Q} f :=
    { toLinearMap := CompletedConnection.baseChangeModuleMap p D R.ring P.carrier Q.carrier
        f.toLinearMap
      horizontal := fun x ↦ by
        have h := CompletedConnection.baseChange_baseChangeModuleMap p D R.ring P.carrier
          Q.carrier C.forms R.forms R.diff (R.psiA 1) P.nabla Q.nabla R.diff_add R.diff_mul
          R.psiA_diff f.toLinearMap
          (fun m ↦ by rw [f.horizontal m, CompletedConnection.valuesMap_eq]) x
        rwa [CompletedConnection.valuesMap_eq] at h }
  map_id P := RetractPairHom.ext (CompletedConnection.baseChangeModuleMap_id p D R.ring P.carrier)
  map_comp f g := RetractPairHom.ext (LinearMap.ext fun x ↦
    CompletedConnection.baseChangeModuleMap_comp p D R.ring _ _ _ f.toLinearMap g.toLinearMap x)

/-- **The comparison of `G(F(M))` with `M` is natural in `M`.** -/
theorem roundTripEquiv_naturality {P Q : Pair.{u, u, u, u} p D C.forms C.dx C.diff} (f : P ⟶ Q)
    (m : P.carrier) :
    Pair.roundTripEquiv C R Q (f.toLinearMap m) =
      CompletedConnection.baseChangeModuleMap p R.ring D _ _
        (CompletedConnection.baseChangeModuleMap p D R.ring P.carrier Q.carrier f.toLinearMap)
        (Pair.roundTripEquiv C R P m) := by
  have hcomm : ∀ i y, coordOp p C.basis Q.isPAdicallyComplete Q.nabla i (f.toLinearMap y) =
      f.toLinearMap (coordOp p C.basis P.isPAdicallyComplete P.nabla i y) :=
    coordOp_map p C.basis P.isPAdicallyComplete P.nabla Q.isPAdicallyComplete Q.nabla
      f.toLinearMap f.horizontal
  have hK := IsThetaMonomialFamily.map_comm (Pair.isThetaMonomialFamily_thetaPow C P)
    (Pair.isThetaMonomialFamily_thetaPow C Q) f.toLinearMap hcomm
  rw [Pair.roundTripEquiv_apply, Pair.roundTripEquiv_apply]
  refine (taylorSum_precomp p D (Pair.finite_thetaPow C P) (Pair.finite_thetaPow C Q)
    (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _) _ _
    f.toLinearMap.toAddMonoidHom hK m).trans ?_
  refine Eq.trans ?_ (map_taylorSum p D (Pair.finite_thetaPow C P)
    (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _)
    (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _) _ _ _ m).symm
  congr 1

/-- **`G ∘ F ≅ 𝟭`**: the comparison `c_{id_D, b ∘ a}` of every pair over `D`. -/
def retractUnitIso :
    𝟭 (Pair.{u, u, u, u} p D C.forms C.dx C.diff) ≅
      retractForwardFunctor C R ⋙ retractBackFunctor C R :=
  NatIso.ofComponents
    (fun P ↦ Pair.isoOfHorizontalEquiv p (Q := (retractForwardFunctor C R ⋙
      retractBackFunctor C R).obj P) (Pair.roundTripEquiv C R P)
      (Pair.roundTripEquiv_horizontal C R P))
    fun f ↦ PairHom.ext (LinearMap.ext fun m ↦ roundTripEquiv_naturality C R f m)

/-- **The collapse `F(G(M')) → M'` is natural in `M'`.** -/
theorem retractComparison_naturality {P Q : RetractPair C R} (f : P ⟶ Q)
    (z : CompletedConnection.baseChangeCarrier p D R.ring
      (CompletedConnection.baseChangeCarrier p R.ring D P.carrier)) :
    CompletedConnection.retractComparison p R.ring D Q.carrier Q.isPAdicallyComplete
        (CompletedConnection.baseChangeModuleMap p D R.ring _ _
          (CompletedConnection.baseChangeModuleMap p R.ring D P.carrier Q.carrier f.toLinearMap)
          z) =
      f.toLinearMap (CompletedConnection.retractComparison p R.ring D P.carrier
        P.isPAdicallyComplete z) := by
  have hQ := Q.isPAdicallyComplete
  exact DFunLike.congr_fun (baseChangeCarrier_baseChangeCarrier_ext p R.ring D R.ring P.carrier
    hQ.toIsHausdorff
    ((CompletedConnection.retractComparison p R.ring D Q.carrier Q.isPAdicallyComplete) ∘ₗ
      (CompletedConnection.baseChangeModuleMap p D R.ring _ _
        (CompletedConnection.baseChangeModuleMap p R.ring D P.carrier Q.carrier f.toLinearMap)))
    (f.toLinearMap ∘ₗ (CompletedConnection.retractComparison p R.ring D P.carrier
      P.isPAdicallyComplete))
    (fun m ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [CompletedConnection.baseChangeModuleMap_inclusion,
        CompletedConnection.baseChangeModuleMap_inclusion,
        CompletedConnection.retractComparison_inclusion,
        CompletedConnection.retractComparison_inclusion])) z

/-- **`F ∘ G ≅ 𝟭`**: the collapse of the round trip along `a ∘ b = id_{D'}`, "Since
`a ∘ b = id_{D'}` we see that `F ∘ G` is the identity functor". -/
def retractCounitIso : retractBackFunctor C R ⋙ retractForwardFunctor C R ≅ 𝟭 (RetractPair C R) :=
  NatIso.ofComponents
    (fun P ↦ RetractPair.isoOfHorizontalEquiv C R (P := (retractBackFunctor C R ⋙
      retractForwardFunctor C R).obj P)
      (CompletedConnection.retractComparisonEquiv p R.ring D P.carrier P.isPAdicallyComplete)
      (fun x ↦ by
        rw [← CompletedConnection.valuesMap_eq]
        exact CompletedConnection.baseChange_retractComparison p R.ring D P.carrier R.forms C.forms
          C.diff (R.psiB 1) (R.psiA 1) P.nabla P.isPAdicallyComplete R.diff_add R.diff_mul
          C.diff_add C.diff_mul R.psiB_diff R.psiA_diff R.psiA_psiB x))
    fun {P Q} f ↦ RetractPairHom.ext (LinearMap.ext fun z ↦
      retractComparison_naturality C R f z)

/-- **The equivalence of categories of [Stacks, Lemma 60.17.5, Tag 07L5]**, between the pairs
over `D` satisfying (07JB)–(07JE) and the pairs over `D'` satisfying them, induced by the base
change functors `F` along `a` and `G` along `b`. -/
def retractPairEquivalence :
    Pair.{u, u, u, u} p D C.forms C.dx C.diff ≌ RetractPair C R :=
  CategoryTheory.Equivalence.mk (retractForwardFunctor C R) (retractBackFunctor C R)
    (retractUnitIso C R) (retractCounitIso C R)

/-- The functor of `Crystalline.retractPairEquivalence` is the base change along `a`. -/
theorem retractPairEquivalence_functor :
    (retractPairEquivalence C R).functor = retractForwardFunctor C R := rfl

/-- The inverse of `Crystalline.retractPairEquivalence` is the base change along `b`. -/
theorem retractPairEquivalence_inverse :
    (retractPairEquivalence C R).inverse = retractBackFunctor C R := rfl

/-- **The functors towards the pairs over `D` and towards the pairs over `D'` are equivalences
together**: a functor `Φ` into the pairs over `D` is an equivalence exactly when `Φ ⋙ F` is,
`F` being an equivalence.  This is the last sentence of [Stacks, Lemma 60.17.5, Tag 07L5]: the
equivalence of categories of [Stacks, Proposition 60.17.4, Tag 07JH] also holds for the
corresponding functor towards pairs over `D'`. -/
theorem isEquivalence_comp_retractForwardFunctor_iff.{w, w'} {𝒞 : Type w} [Category.{w'} 𝒞]
    (Φ : 𝒞 ⥤ Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    Φ.IsEquivalence ↔ (Φ ⋙ retractForwardFunctor C R).IsEquivalence := by
  have : (retractForwardFunctor C R).IsEquivalence :=
    (retractPairEquivalence C R).isEquivalence_functor
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ Functor.isEquivalence_of_comp_right Φ
    (retractForwardFunctor C R)⟩

end Equivalence

end Crystalline

end
