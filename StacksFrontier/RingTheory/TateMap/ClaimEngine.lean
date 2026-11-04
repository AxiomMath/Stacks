module

public import StacksFrontier.RingTheory.TateMap.ClaimFamilies
public import StacksFrontier.RingTheory.TateMap.UniversalFamily
public import StacksFrontier.RingTheory.TateMap.Pullback
public import StacksFrontier.RingTheory.TateMap.GenericPolynomial
public import StacksFrontier.RingTheory.TateMap.UniversalTate
public import StacksFrontier.RingTheory.TateMap.Classification

/-!
# Rigidity of classifications by the universal family

A classification of a chart by a basic chart of the universal family is determined by two ring
maps: the map out of the coefficient ring, which is determined by the images of the universal
polynomials, and the map out of the chart, which is then determined by the images of the
variables.

## Main results

* `Stacks.TateMap.univBase_ringHom_ext`: a ring map out of `univBase n d` is determined by the
  images of the universal polynomials.
* `Stacks.TateMap.lci_ringHom_ext`: a ring map out of `S[x, 1/h]/(f)` is determined by its
  restriction to `S` and the images of the variables.
-/

@[expose] public section

open MvPolynomial Stacks.Discriminant AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.TateMap

/-- The coefficient of `x^E` in the universal polynomial `f_i` is the universal coefficient
`a_{i, E}`. -/
theorem coeff_univPoly {n d : ℕ} (i : Fin n) (E : MultiIndex n d) :
    coeff (multiIndexExponent n d E) (univPoly.{u} n d i) = X (i, E) := by
  classical
  rw [univPoly, coeff_map, universalPolynomial, coeff_sum, Finset.sum_eq_single E]
  · simp [universalCoefficient, univBaseMap]
  · intro F _ hFE
    rw [coeff_monomial, ite_eq_right fun he ↦ hFE (multiIndexExponent_injective n d he)]
  · exact fun h ↦ absurd (Finset.mem_univ _) h

/-- A ring map out of the universal coefficient ring is determined by the images of the universal
polynomials. -/
theorem univBase_ringHom_ext {n d : ℕ} {T : Type*} [CommRing T] {φ φ' : univBase.{u} n d →+* T}
    (H : ∀ i, MvPolynomial.map φ (univPoly n d i) = MvPolynomial.map φ' (univPoly n d i)) :
    φ = φ' := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
  · exact RingHom.congr_fun (RingHom.ext_int
      ((φ.comp MvPolynomial.C).comp ULift.ringEquiv.symm.toRingHom)
      ((φ'.comp MvPolynomial.C).comp ULift.ringEquiv.symm.toRingHom)) r.down
  · obtain ⟨i, E⟩ := j
    have := congrArg (coeff (multiIndexExponent n d E)) (H i)
    rwa [coeff_map, coeff_map, coeff_univPoly] at this

/-- A ring map out of a localized complete intersection is determined by its restriction to the
base and the images of the variables. -/
theorem lci_ringHom_ext {S : Type u} [CommRing S] {n : ℕ} {h : MvPolynomial (Fin n) S}
    {f : Fin n → MvPolynomial (Fin n) S} {T : Type*} [CommRing T]
    {ψ ψ' : localizedCompleteIntersection S n h f →+* T}
    (hS : ∀ s, ψ (algebraMap S _ s) = ψ' (algebraMap S _ s))
    (hX : ∀ i, ψ (lciMk h f (X i)) = ψ' (lciMk h f (X i))) : ψ = ψ' := by
  let : Algebra S T := (ψ.comp (algebraMap S _)).toAlgebra
  let α : localizedCompleteIntersection S n h f →ₐ[S] T :=
    { ψ with commutes' := fun _ ↦ rfl }
  let α' : localizedCompleteIntersection S n h f →ₐ[S] T :=
    { ψ' with commutes' := fun s ↦ (hS s).symm }
  exact RingHom.ext (AlgHom.congr_fun (lci_algHom_ext (φ := α) (ψ := α') hX))

section Local

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]
  [IsNoetherianRing A] {F : FiniteOpenFactorization.{u, u, u} A B}

/-- Let `s` be a set of elements of `B` generating the unit ideal, and for each `b ∈ s` let `D b`
be a chart base change from `A → B` to some `A_b → B_b` with `B_b` the localization of `B` away
from `b`. If two isomorphisms `e, e' : det(NL_{B/A}) ≅ ω_{B/A}` have the same pullbacks along
every `D b`, then `e = e'`. -/
theorem eq_of_pullbackTate_eq (s : Set B) (hs : Ideal.span s = ⊤)
    (A' B' : s → Type u) [∀ b, CommRing (A' b)] [∀ b, CommRing (B' b)] [∀ b, Algebra A (A' b)]
    [∀ b, Algebra (A' b) (B' b)] [∀ b, Algebra B (B' b)] [∀ b, Algebra.Syntomic (A' b) (B' b)]
    [∀ b, IsNoetherianRing (A' b)] [∀ b : s, IsLocalization.Away (b : B) (B' b)]
    (D : ∀ b, ChartBaseChange A B (A' b) (B' b))
    (G : ∀ b, FiniteOpenFactorization.{u, u, u} (A' b) (B' b))
    (e e' : detNL A B ≃ₗ[B] dualizingModule F)
    (H : ∀ b, pullbackTate (D b) e (G b) = pullbackTate (D b) e' (G b)) : e = e' := by
  refine LinearEquiv.ext fun x ↦ ?_
  rw [← sub_eq_zero]
  set y := e x - e' x
  have hloc : ∀ b : s, ∃ k : ℕ, (b : B) ^ k • y = 0 := by
    intro b
    have h1 := congrArg (fun φ : detNL (A' b) (B' b) ≃ₗ[B' b] dualizingModule (G b) ↦
      φ (detNLBaseChange (D b) (1 ⊗ₜ x))) (H b)
    simp only [pullbackTate_detNLBaseChange_one_tmul] at h1
    have h2 : (1 : B' b) ⊗ₜ[B] y = 0 := by
      rw [TensorProduct.tmul_sub, (omegaBaseChange (D b) F (G b)).injective h1, sub_self]
    let mk := TensorProduct.mk B (B' b) (dualizingModule F) 1
    have hl : IsLocalizedModule (Submonoid.powers (b : B)) mk := inferInstance
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (b : B))
      (f := mk) (x₁ := y) (x₂ := 0) (by rwa [map_zero])
    exact ⟨k, by simpa [Submonoid.smul_def] using hc⟩
  let J : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B (dualizingModule F) y)
  have hrad : J.radical = ⊤ := by
    rw [eq_top_iff, ← hs, Ideal.span_le]
    intro b hb
    obtain ⟨k, hk⟩ := hloc ⟨b, hb⟩
    exact ⟨k, by simpa [J] using hk⟩
  simpa [J] using (Ideal.eq_top_iff_one _).mp (Ideal.radical_eq_top.mp hrad)

end Local

section Degree

/-- The coefficient of `x^m` in the universal polynomial `f_i` of degree bound `d`. -/
theorem coeff_univPoly_eq {n d : ℕ} (i : Fin n) (m : Fin n →₀ ℕ) :
    coeff m (univPoly.{u} n d i) =
      if hm : ∑ j, m j ≤ d then X (i, MultiIndex.ofFinsupp m hm) else 0 := by
  classical
  split_ifs with hm
  · have := coeff_univPoly.{u} (d := d) i (MultiIndex.ofFinsupp m hm)
    rwa [multiIndexExponent_ofFinsupp] at this
  · rw [univPoly, coeff_map, universalPolynomial, coeff_sum, map_sum]
    refine Finset.sum_eq_zero fun E _ ↦ ?_
    rw [coeff_monomial, ite_eq_right, map_zero]
    rintro rfl
    exact hm (by simpa [multiIndexExponent] using E.2)

/-- The truncation `univBase n D → univBase n d`, `d ≤ D`, killing the universal coefficients of
the monomials of degree above `d`. -/
noncomputable def univTrunc (n : ℕ) {d D : ℕ} : univBase.{u} n D →+* univBase.{u} n d :=
  (aeval fun iE : Fin n × MultiIndex n D ↦
    if hm : ∑ j, multiIndexExponent n D iE.2 j ≤ d then
      (X (iE.1, MultiIndex.ofFinsupp _ hm) : univBase.{u} n d) else 0).toRingHom

/-- The inclusion `univBase n d → univBase n D`, `d ≤ D`. -/
noncomputable def univIncl (n : ℕ) {d D : ℕ} (hdD : d ≤ D) :
    univBase.{u} n d →+* univBase.{u} n D :=
  (rename fun iE : Fin n × MultiIndex n d ↦
    (iE.1, MultiIndex.ofFinsupp (multiIndexExponent n d iE.2)
      ((by simpa [multiIndexExponent] using iE.2.2 : ∑ j, multiIndexExponent n d iE.2 j ≤ d).trans
        hdD))).toRingHom

/-- The bounded multi-index read off from the exponent of a bounded multi-index `E` is `E`. -/
theorem ofFinsupp_multiIndexExponent {n d : ℕ} (E : MultiIndex n d)
    (h : ∑ j, multiIndexExponent n d E j ≤ d) :
    MultiIndex.ofFinsupp (multiIndexExponent n d E) h = E :=
  multiIndexExponent_injective n d (multiIndexExponent_ofFinsupp _ _)

/-- Truncation carries the universal polynomials of degree bound `D` to those of degree bound
`d`. -/
theorem map_univTrunc_univPoly (n : ℕ) {d D : ℕ} (hdD : d ≤ D) (i : Fin n) :
    MvPolynomial.map (univTrunc.{u} n (d := d) (D := D)) (univPoly n D i) = univPoly n d i := by
  classical
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  rw [coeff_map, coeff_univPoly_eq, coeff_univPoly_eq]
  split_ifs with hD hm hm <;>
    first | exact absurd (hm.trans hdD) hD | simp [univTrunc, hm]

/-- Truncation is a retraction of the inclusion. -/
theorem univTrunc_comp_univIncl (n : ℕ) {d D : ℕ} (hdD : d ≤ D) :
    (univTrunc.{u} n (d := d) (D := D)).comp (univIncl.{u} n hdD) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun iE ↦ ?_)
  · simp [univTrunc, univIncl]
  · obtain ⟨i, E⟩ := iE
    have hE : ∑ j, multiIndexExponent n d E j ≤ d := by
      simpa [multiIndexExponent] using E.2
    simp only [univTrunc, univIncl, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, rename_X, aeval_X, multiIndexExponent_ofFinsupp, dite_eq_left hE,
      ofFinsupp_multiIndexExponent, RingHom.id_apply]

end Degree

section TateOf

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]
  [IsNoetherianRing A] {n d : ℕ} (k : MvPolynomial (Fin n) (univBase.{u} n d))
  [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)]

/-- For a classification `D` of `A → B` by
the basic chart `univChart n d k`, with the two ring maps `univBase n d → A` and
`univChart n d k → B` given by the algebra structures `instR` and `instC`, the pullback along `D`
of the Tate map of the universal chart. -/
noncomputable def tateOf (instR : Algebra (univBase.{u} n d) A)
    (instC : Algebra (univChart n d k) B)
    (D : ChartBaseChange (univBase.{u} n d) (univChart n d k) A B)
    (G : FiniteOpenFactorization.{u, u, u} A B) : detNL A B ≃ₗ[B] dualizingModule G :=
  pullbackTate D (cUniv n d k (nonempty_finiteOpenFactorization.{u, u}
    (A := univBase.{u} n d) (B := univChart n d k)).some) G

/-- The pullback `tateOf` depends only on the two ring maps of the classification. -/
theorem tateOf_congr (instR instR' : Algebra (univBase.{u} n d) A)
    (instC instC' : Algebra (univChart n d k) B)
    (hR : ∀ x, @algebraMap _ _ _ _ instR x = @algebraMap _ _ _ _ instR' x)
    (hC : ∀ x, @algebraMap _ _ _ _ instC x = @algebraMap _ _ _ _ instC' x)
    (D : @ChartBaseChange (univBase.{u} n d) (univChart n d k) A B _ _ _ _ _ instR _ instC)
    (D' : @ChartBaseChange (univBase.{u} n d) (univChart n d k) A B _ _ _ _ _ instR' _ instC')
    (G : FiniteOpenFactorization.{u, u, u} A B) :
    tateOf k instR instC D G = tateOf k instR' instC' D' G := by
  obtain rfl : instR = instR' := Algebra.algebra_ext _ _ hR
  obtain rfl : instC = instC' := Algebra.algebra_ext _ _ hC
  exact pullbackTate_congr _ _ _ _

/-- `tateOf` carries `δ(NL_{B/A})` to `τ_{B/A}`. -/
theorem tateOf_deltaNL [Algebra.QuasiFinite A B] [IsNoetherianRing B]
    (instR : Algebra (univBase.{u} n d) A) (instC : Algebra (univChart n d k) B)
    (D : ChartBaseChange (univBase.{u} n d) (univChart n d k) A B)
    (G : FiniteOpenFactorization.{u, u, u} A B) :
    tateOf k instR instC D G (deltaNL A B) = dualizingModule.traceElement G :=
  pullbackTate_deltaNL D _ G (cUniv_deltaNL n d k _)

/-- The pullback along a chart base change
`D'` of the Tate map of a classification `D` is the Tate map of any classification with the
composite ring maps, for instance `D'.comp D`. -/
theorem tateOf_pullbackTate {A' B' : Type u} [CommRing A'] [CommRing B'] [Algebra A A']
    [Algebra A' B'] [Algebra B B'] [Algebra.Syntomic A' B'] [IsNoetherianRing A']
    (instR : Algebra (univBase.{u} n d) A) (instC : Algebra (univChart n d k) B)
    (D : ChartBaseChange (univBase.{u} n d) (univChart n d k) A B)
    (D' : ChartBaseChange A B A' B')
    (D'' : @ChartBaseChange (univBase.{u} n d) (univChart n d k) A' B' _ _ _ _ _
      ((algebraMap A A').comp (@algebraMap _ _ _ _ instR)).toAlgebra _
      ((algebraMap B B').comp (@algebraMap _ _ _ _ instC)).toAlgebra)
    (G : FiniteOpenFactorization.{u, u, u} A B) (G' : FiniteOpenFactorization.{u, u, u} A' B') :
    pullbackTate D' (tateOf k instR instC D G) G' =
      tateOf k ((algebraMap A A').comp (@algebraMap _ _ _ _ instR)).toAlgebra
        ((algebraMap B B').comp (@algebraMap _ _ _ _ instC)).toAlgebra D'' G' := by
  let iR' : Algebra (univBase.{u} n d) A' :=
    ((algebraMap A A').comp (@algebraMap _ _ _ _ instR)).toAlgebra
  let iC' : Algebra (univChart n d k) B' :=
    ((algebraMap B B').comp (@algebraMap _ _ _ _ instC)).toAlgebra
  have : @IsScalarTower (univBase.{u} n d) A A' instR.toSMul Algebra.toSMul iR'.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : @IsScalarTower (univChart n d k) B B' instC.toSMul Algebra.toSMul iC'.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact (pullbackTate_comp D D' D'' _ G G').symm

end TateOf

section ClassificationMaps

variable {A P : Type u} [CommRing A] [CommRing P] {n : ℕ} {F : Fin n → MvPolynomial (Fin n) P}
  (k : MvPolynomial (Fin n) P) (φ : P →+* A) (h : MvPolynomial (Fin n) A)
  (f : Fin n → MvPolynomial (Fin n) A) (hf : ∀ i, MvPolynomial.map φ (F i) = f i)
  (B' : Type u) [CommRing B'] [Algebra A B'] [Algebra (localizedCompleteIntersection A n h f) B']
  [IsScalarTower A (localizedCompleteIntersection A n h f) B']

/-- The chart map of a classification restricts to `φ` on the coefficient ring. -/
theorem classificationAlgebra_algebraMap_base (hk : IsUnit (algebraMap
      (localizedCompleteIntersection A n h f) B'
      (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k)))) (c : P) :
    @algebraMap _ _ _ _ (classificationAlgebra k φ h f hf B' hk)
        (algebraMap P (localizedCompleteIntersection P n k F) c) = algebraMap A B' (φ c) := by
  rw [IsScalarTower.algebraMap_apply P (MvPolynomial (Fin n) P), MvPolynomial.algebraMap_eq,
    classificationAlgebra_algebraMap, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply A (MvPolynomial (Fin n) A)
      (localizedCompleteIntersection A n h f),
    ← IsScalarTower.algebraMap_apply A (localizedCompleteIntersection A n h f) B']

/-- The chart map of a classification sends the class of `x_i` to the class of `x_i`. -/
theorem classificationAlgebra_lciMk_X (hk : IsUnit (algebraMap
      (localizedCompleteIntersection A n h f) B'
      (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k)))) (i : Fin n) :
    @algebraMap _ _ _ _ (classificationAlgebra k φ h f hf B' hk) (lciMk k F (X i)) =
      algebraMap (localizedCompleteIntersection A n h f) B' (lciMk h f (X i)) := by
  rw [lciMk_apply, classificationAlgebra_algebraMap, MvPolynomial.map_X]
  rfl

/-- A ring map `P[x, 1/k]/(F) → B'` restricting to `φ` on `P` and sending `x_i` to `x_i` is the
chart map of the classification. -/
theorem eq_classificationAlgebra (hk : IsUnit (algebraMap
      (localizedCompleteIntersection A n h f) B'
      (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k))))
    (ψ : localizedCompleteIntersection P n k F →+* B')
    (hψ : ∀ c, ψ (algebraMap P _ c) = algebraMap A B' (φ c))
    (hX : ∀ i, ψ (lciMk k F (X i)) =
      algebraMap (localizedCompleteIntersection A n h f) B' (lciMk h f (X i))) :
    ∀ x, ψ x = @algebraMap _ _ _ _ (classificationAlgebra k φ h f hf B' hk) x := by
  exact RingHom.congr_fun (lci_ringHom_ext (ψ := ψ)
    (ψ' := @algebraMap _ _ _ _ (classificationAlgebra k φ h f hf B' hk))
    (fun c ↦ by rw [hψ, classificationAlgebra_algebraMap_base])
    (fun i ↦ by rw [hX, classificationAlgebra_lciMk_X]))

end ClassificationMaps

end Stacks.TateMap
