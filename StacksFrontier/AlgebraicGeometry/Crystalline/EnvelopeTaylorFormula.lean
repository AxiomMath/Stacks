module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedEnvelopeFactorizationForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorFormulaMonomials

/-!
# Taylor's formula for the divided power envelope of a polynomial presentation

Let `(A, I, γ)` be a divided power ring, let `P = A[x_i : i ∈ ι]` be a polynomial algebra over
it, let `J ⊆ P` be an ideal containing `I P` and let
`E = D_{P,γ}(J)` be the divided power envelope of [Stacks, Tag 07H8], with coordinates
`y_i ∈ E`, the images of the variables.  This file proves **Taylor's formula** for `E`, the
statement the proof of [Stacks, Lemma 60.17.5, Tag 07L5] (and of [Stacks, Tag 07JH]) runs on.

## The construction

Let `E⟨t⟩ = E⟨t_i : i ∈ ι⟩` be the divided power polynomial algebra over `E` of
[Stacks, Tag 07H6].  By the universal property of the envelope there is a divided power morphism
`σ : E → E⟨t⟩` over `A` with `σ(y_i) = y_i + t_i`: the `A`-algebra map `P → E⟨t⟩` with
`x_i ↦ y_i + t_i` carries `J` into the divided power ideal, because modulo that ideal it agrees
with `P → E → E⟨t⟩`.  The coefficients of `σ(a)` in the basis of divided power monomials
`t^{[K]}` are the **Taylor coefficients** `θ_K(a) = Crystalline.presentationTaylorCoeff E K a`.

## Main results

* `Crystalline.envelopeTaylor_formula` — **Taylor's formula, for any target**: for two divided
  power morphisms `F, G : E → B` over `A` with `F(y_i) - G(y_i)` in the divided power ideal of
  `B`, `F(a) = ∑_K G(θ_K a) (F(y) - G(y))^{[K]}`, over the finite support of the coefficients of
  `a`.  The proof is the uniqueness half of the universal property of `E`: the map
  `E⟨t⟩ → B` extending `G` with `t_i ↦ F(y_i) - G(y_i)`, composed with `σ`, agrees with `F` on
  `A` and on the `y_i`.
* `Crystalline.presentationTaylorCoeff_zero` and `Crystalline.presentationTaylorCoeff_add` —
  `θ_0 = id`
  and the cocycle `θ_{K + L} = θ_K ∘ θ_L`; hence the operators `δ_i = θ_{e_i}` commute
  (`Crystalline.envelopeDelta_comm`) and the `θ_K` are their composites
  (`Crystalline.isThetaMonomialFamily_presentationTaylorCoeff`).
* `Crystalline.envelopeDelta_coord` — `δ_i(y_j) = [i = j]`.
* `Crystalline.envelopeTaylor_derivation` — **a divided power derivation of `E` is determined by
  its values on the coordinates**: `∂(a) = ∑_i δ_i(a) ∂(y_i)`, Taylor's formula into the
  first-order thickening `R ⊕ M`.

## References

* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public noncomputable section

namespace Crystalline

open DividedPowers Finset.HasAntidiagonal

universe u

/-- Divided power morphisms are ring homomorphisms, for the `map_*` lemmas. -/
theorem dpMorphismRingHomClass {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}
    {K : Ideal S} {γ : DividedPowers I} {δ : DividedPowers K} :
    RingHomClass (DPMorphism γ δ) R S where
  map_add f := f.toRingHom.map_add
  map_mul f := f.toRingHom.map_mul
  map_one f := f.toRingHom.map_one
  map_zero f := f.toRingHom.map_zero

attribute [local instance] dpMorphismRingHomClass

/-! ### The universal property of the envelope, at a polynomial presentation -/

section Universal

variable {A : DividedPowerRing.{u}} {ι : Type u} {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ)

/-- **The coordinate `y_i` of the envelope**: the image of the polynomial variable `x_i` under
`P → E`. -/
def envelopeCoord (i : ι) : E.object :=
  E.algebraMap.toRingHom (MvPolynomial.X i)

/-- The coordinate `x_i` of the completion `D` is the image of the coordinate `y_i` of `E`. -/
theorem envelopeCompletionCoord_eq (p : ℕ)
    (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object))) (i : ι) :
    envelopeCompletionCoord E p hp i = envelopeCompletionInclusion E p hp (envelopeCoord E i) :=
  rfl

/-- `P → E` restricts to the structure map `A → E` on constants. -/
private theorem envelope_algebraMap_C (r : A) :
    E.algebraMap.toRingHom (MvPolynomial.C r) = E.structureMap.toRingHom r :=
  congrArg (fun s : A →+* E.object => s r) E.algebraMap_comp

/-- **Uniqueness in the universal property of the envelope**: two divided power morphisms out
of `E` agreeing on `A` and on the coordinates `y_i` are equal. -/
theorem envelope_dpMorphism_ext {C : DividedPowerRing.{u}}
    (q q' : DPMorphism E.object.dividedPowers C.dividedPowers)
    (hA : q.comp E.structureMap = q'.comp E.structureMap)
    (hy : ∀ i, q (envelopeCoord E i) = q' (envelopeCoord E i)) : q = q' := by
  have key : E.homEquiv C (q'.comp E.structureMap) ⟨q, hA⟩ =
      E.homEquiv C (q'.comp E.structureMap) ⟨q', rfl⟩ := by
    apply Subtype.ext
    apply IdealPair.Hom.ext_toRingHom
    rw [E.homEquiv_apply C _ ⟨q, hA⟩, E.homEquiv_apply C _ ⟨q', rfl⟩]
    show q.toRingHom.comp E.algebraMap.toRingHom = q'.toRingHom.comp E.algebraMap.toRingHom
    apply MvPolynomial.ringHom_ext
    · intro r
      show q (E.algebraMap.toRingHom (MvPolynomial.C r)) =
        q' (E.algebraMap.toRingHom (MvPolynomial.C r))
      rw [envelope_algebraMap_C]
      exact congrArg (fun s : DPMorphism A.dividedPowers C.dividedPowers => s r) hA
    · exact hy
  exact congrArg Subtype.val ((E.homEquiv C (q'.comp E.structureMap)).injective key)

/-- **Existence in the universal property of the envelope**: a divided power morphism
`a : A → C` and values `v_i ∈ C` for which `x_i ↦ v_i` carries `J` into the divided power ideal
of `C` extend to a divided power morphism `E → C`. -/
theorem exists_envelope_dpMorphism (C : DividedPowerRing.{u})
    (a : DPMorphism A.dividedPowers C.dividedPowers) (v : ι → C)
    (hv : J.map (MvPolynomial.eval₂Hom a.toRingHom v) ≤ C.ideal) :
    ∃ q : DPMorphism E.object.dividedPowers C.dividedPowers,
      q.comp E.structureMap = a ∧ ∀ i, q (envelopeCoord E i) = v i := by
  classical
  have hcomp : (MvPolynomial.eval₂Hom a.toRingHom v).comp
      (algebraMap A (MvPolynomial ι A)) = a.toRingHom := by
    ext x
    simp
  set t : IdealPair.HomOver (IdealPair.Hom.ofRingHom (algebraMap A (MvPolynomial ι A)) hJ)
      (IdealPair.Hom.ofDPMorphism a) :=
    ⟨IdealPair.Hom.ofRingHom (MvPolynomial.eval₂Hom a.toRingHom v) hv,
      IdealPair.Hom.ext_toRingHom _ _ hcomp⟩ with htdef
  set q := (E.homEquiv C a).symm t with hqdef
  have hq : E.homEquiv C a q = t := by
    rw [hqdef]
    exact (E.homEquiv C a).apply_symm_apply t
  have hqalg : q.1.toRingHom.comp E.algebraMap.toRingHom =
      MvPolynomial.eval₂Hom a.toRingHom v := by
    have hval := E.homEquiv_apply C a q
    rw [hq] at hval
    exact (congrArg IdealPair.Hom.toRingHom hval).symm
  refine ⟨q.1, q.2, fun i => ?_⟩
  have h3 := congrArg (fun r : MvPolynomial ι A →+* C => r (MvPolynomial.X i)) hqalg
  have h4 : q.1 (E.algebraMap.toRingHom (MvPolynomial.X i)) = v i := by simpa using h3
  exact h4

/-- **The compatibility the universal property of `E` asks for is automatic for values
differing from those of an existing morphism by elements of the divided power ideal.** -/
theorem envelope_eval₂Hom_map_le_of_sub_mem (C : DividedPowerRing.{u})
    (m : DPMorphism E.object.dividedPowers C.dividedPowers) (v : ι → C)
    (hv : ∀ i, v i - m (envelopeCoord E i) ∈ C.ideal) :
    J.map (MvPolynomial.eval₂Hom (m.comp E.structureMap).toRingHom v) ≤ C.ideal := by
  classical
  set w : MvPolynomial ι A →+* C := m.toRingHom.comp E.algebraMap.toRingHom with hwdef
  have hwC : ∀ r : A, w (MvPolynomial.C r) = (m.comp E.structureMap) r := by
    intro r
    show m (E.algebraMap.toRingHom (MvPolynomial.C r)) = m (E.structureMap r)
    rw [envelope_algebraMap_C]
    rfl
  have hwJ : ∀ x ∈ J, w x ∈ C.ideal := fun x hx =>
    m.ideal_comp (Ideal.mem_map_of_mem _ (E.algebraMap.ideal_comp (Ideal.mem_map_of_mem _ hx)))
  have hmod : (Ideal.Quotient.mk C.ideal).comp
      (MvPolynomial.eval₂Hom (m.comp E.structureMap).toRingHom v) =
      (Ideal.Quotient.mk C.ideal).comp w := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show Ideal.Quotient.mk C.ideal (MvPolynomial.eval₂Hom (m.comp E.structureMap).toRingHom v
        (MvPolynomial.C r)) = Ideal.Quotient.mk C.ideal (w (MvPolynomial.C r))
      rw [hwC r]
      simp only [MvPolynomial.eval₂Hom_C]
      rfl
    · intro i
      show Ideal.Quotient.mk C.ideal (MvPolynomial.eval₂Hom (m.comp E.structureMap).toRingHom v
        (MvPolynomial.X i)) = Ideal.Quotient.mk C.ideal (m (envelopeCoord E i))
      rw [MvPolynomial.eval₂Hom_X']
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hv i)
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hdiff : MvPolynomial.eval₂Hom (m.comp E.structureMap).toRingHom v x - w x ∈ C.ideal :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      (congrArg (fun s : MvPolynomial ι A →+* C ⧸ C.ideal => s x) hmod)
  have := C.ideal.add_mem hdiff (hwJ x hx)
  simpa using this

end Universal

/-! ### The Taylor map `σ : E → E⟨t⟩` and the Taylor coefficients -/

section TaylorMap

variable {A : DividedPowerRing.{u}} {ι : Type u} [DecidableEq ι] {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ)

/-- **The divided power polynomial algebra `E⟨t_i : i ∈ ι⟩`** over the envelope, with its
divided power ideal `I_E E⟨t⟩ + E⟨t⟩_+` of [Stacks, Tag 07H6]. -/
abbrev envelopeTaylorRing : DividedPowerRing.{u} :=
  setIndexedDividedPowerPolynomialDividedPowerRing E.object ι

/-- The coefficient map `E → E⟨t⟩`, a divided power morphism. -/
abbrev envelopeTaylorNu :
    DPMorphism E.object.dividedPowers (envelopeTaylorRing E).dividedPowers :=
  setIndexedDividedPowerPolynomialCoefficientDPMorphism E.object ι

/-- The variable `t_i` of `E⟨t⟩`. -/
abbrev envelopeTaylorVar (i : ι) : envelopeTaylorRing E :=
  dividedPowerPolynomialVariable (E.object : Type u) i

omit [DecidableEq ι] in
/-- The variables `t_i` lie in the divided power ideal of `E⟨t⟩`. -/
theorem envelopeTaylorVar_mem (i : ι) : envelopeTaylorVar E i ∈ (envelopeTaylorRing E).ideal :=
  variable_mem_polynomialIdeal E.object i

omit [DecidableEq ι] in
/-- **The Taylor map `σ : E → E⟨t⟩` exists**: a divided power morphism over `A` with
`σ(y_i) = y_i + t_i`. -/
theorem exists_envelopeTaylorMap :
    ∃ s : DPMorphism E.object.dividedPowers (envelopeTaylorRing E).dividedPowers,
      s.comp E.structureMap = (envelopeTaylorNu E).comp E.structureMap ∧
        ∀ i, s (envelopeCoord E i) =
          envelopeTaylorNu E (envelopeCoord E i) + envelopeTaylorVar E i :=
  exists_envelope_dpMorphism E _ _ _ (envelope_eval₂Hom_map_le_of_sub_mem E _ (envelopeTaylorNu E)
    _ fun i => by simpa using envelopeTaylorVar_mem E i)

/-- **The Taylor map `σ : E → E⟨t⟩`**, `y_i ↦ y_i + t_i`, a divided power morphism over `A`. -/
def envelopeTaylorMap :
    DPMorphism E.object.dividedPowers (envelopeTaylorRing E).dividedPowers :=
  (exists_envelopeTaylorMap E).choose

omit [DecidableEq ι] in
/-- `σ` is a morphism over `A`. -/
theorem envelopeTaylorMap_comp_structureMap :
    (envelopeTaylorMap E).comp E.structureMap = (envelopeTaylorNu E).comp E.structureMap :=
  (exists_envelopeTaylorMap E).choose_spec.1

omit [DecidableEq ι] in
/-- `σ(y_i) = y_i + t_i`. -/
theorem envelopeTaylorMap_coord (i : ι) :
    envelopeTaylorMap E (envelopeCoord E i) =
      envelopeTaylorNu E (envelopeCoord E i) + envelopeTaylorVar E i :=
  (exists_envelopeTaylorMap E).choose_spec.2 i

/-- `E⟨t⟩` is an `E`-algebra through its coefficient map.  Stated as an instance because
`DividedPowers.setIndexedDividedPowerPolynomialDividedPowerRing` is not reducible for instance
search. -/
@[instance_reducible]
def algebraEnvelopeTaylorRing : Algebra (E.object : Type u) (envelopeTaylorRing E : Type u) :=
  inferInstanceAs (Algebra (E.object : Type u)
    (DividedPowerAlgebra (E.object : Type u) (ι →₀ (E.object : Type u))))

attribute [instance] algebraEnvelopeTaylorRing

/-- The basis of divided power monomials `t^{[K]}` of `E⟨t⟩` over `E`. -/
abbrev envelopeTaylorBasis :
    Module.Basis (ι →₀ ℕ) (E.object : Type u) (envelopeTaylorRing E : Type u) :=
  dividedPowerPolynomialMonomialBasis (E.object : Type u) ι

omit [DecidableEq ι] in
/-- The basis vectors are the divided power monomials `t^{[K]}`. -/
theorem taylorMonomial_envelopeTaylorVar (K : ι →₀ ℕ) :
    taylorMonomial (envelopeTaylorRing E) (envelopeTaylorVar E) K = envelopeTaylorBasis E K := by
  classical
  exact (taylorMonomial_variable E.object K).trans
    (dividedPowerPolynomialMonomialBasis_apply (E.object : Type u) K).symm

/-- **The Taylor coefficient `θ_K : E → E`**: the coefficient of the divided power monomial
`t^{[K]}` in `σ(a)`, as an additive map. -/
def presentationTaylorCoeff (K : ι →₀ ℕ) : E.object →+ E.object :=
  (Finsupp.lapply (R := (E.object : Type u)) K).toAddMonoidHom.comp
    ((envelopeTaylorBasis E).repr.toAddMonoidHom.comp
      (envelopeTaylorMap E).toRingHom.toAddMonoidHom)

omit [DecidableEq ι] in
/-- The Taylor coefficients of `a` are the coordinates of `σ(a)`. -/
theorem presentationTaylorCoeff_apply (K : ι →₀ ℕ) (a : E.object) :
    presentationTaylorCoeff E K a = (envelopeTaylorBasis E).repr (envelopeTaylorMap E a) K :=
  rfl

/-- **The finite support of the Taylor expansion of `a`**: the multi-indices outside it have
vanishing Taylor coefficient. -/
def envelopeTaylorSupport (a : E.object) : Finset (ι →₀ ℕ) :=
  ((envelopeTaylorBasis E).repr (envelopeTaylorMap E a)).support

omit [DecidableEq ι] in
/-- The Taylor coefficients vanish outside the support. -/
theorem presentationTaylorCoeff_eq_zero_of_notMem {K : ι →₀ ℕ} {a : E.object}
    (hK : K ∉ envelopeTaylorSupport E a) : presentationTaylorCoeff E K a = 0 :=
  Finsupp.notMem_support_iff.mp hK

omit [DecidableEq ι] in
/-- **The Taylor expansion of `σ(a)`** in the monomial basis. -/
theorem envelopeTaylorMap_eq_sum (a : E.object) :
    envelopeTaylorMap E a = ∑ K ∈ envelopeTaylorSupport E a,
      envelopeTaylorNu E (presentationTaylorCoeff E K a) *
        taylorMonomial (envelopeTaylorRing E) (envelopeTaylorVar E) K := by
  have hrepr := (envelopeTaylorBasis E).linearCombination_repr (envelopeTaylorMap E a)
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
  refine hrepr.symm.trans (Finset.sum_congr rfl fun K _ => ?_)
  rw [Algebra.smul_def, ← taylorMonomial_envelopeTaylorVar]
  rfl

/-! ### Taylor's formula -/

omit [DecidableEq ι] in
/-- **Taylor's formula for the divided power envelope, for any target.**  Let `F, G : E → B` be
divided power morphisms agreeing on `A`, with `F(y_i) - G(y_i)` in the divided power ideal of
`B` for every `i`.  Then for every `a ∈ E`

`F(a) = ∑_K G(θ_K a) · (F(y) - G(y))^{[K]}`,

the sum running over the finite support of the Taylor coefficients of `a`, outside which they
vanish (`Crystalline.presentationTaylorCoeff_eq_zero_of_notMem`). -/
theorem envelopeTaylor_formula (B : DividedPowerRing.{u})
    (F G : DPMorphism E.object.dividedPowers B.dividedPowers)
    (hFG : F.comp E.structureMap = G.comp E.structureMap)
    (hxi : ∀ i, F (envelopeCoord E i) - G (envelopeCoord E i) ∈ B.ideal) (a : E.object) :
    F a = ∑ K ∈ envelopeTaylorSupport E a, G (presentationTaylorCoeff E K a) *
      taylorMonomial B (fun i => F (envelopeCoord E i) - G (envelopeCoord E i)) K := by
  classical
  obtain ⟨h, ⟨hh1, hh2⟩, -⟩ := existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
    E.object ι B G (fun i => ⟨F (envelopeCoord E i) - G (envelopeCoord E i), hxi i⟩)
  let h' : DPMorphism (envelopeTaylorRing E).dividedPowers B.dividedPowers := h
  have hnu : ∀ c, h' (envelopeTaylorNu E c) = G c := fun c =>
    congrArg (fun r : DPMorphism E.object.dividedPowers B.dividedPowers => r c) hh1
  have hσ : h'.comp (envelopeTaylorMap E) = F := by
    refine envelope_dpMorphism_ext E _ _ ?_ fun i => ?_
    · refine DFunLike.ext _ _ fun r => ?_
      have h1 := congrArg (fun s : DPMorphism A.dividedPowers (envelopeTaylorRing E).dividedPowers
        => s r) (envelopeTaylorMap_comp_structureMap E)
      have h2 := congrArg (fun s : DPMorphism A.dividedPowers B.dividedPowers => s r) hFG
      show h' (envelopeTaylorMap E (E.structureMap r)) = F (E.structureMap r)
      change envelopeTaylorMap E (E.structureMap r) = envelopeTaylorNu E (E.structureMap r) at h1
      change F (E.structureMap r) = G (E.structureMap r) at h2
      rw [h1, hnu, h2]
    · show h' (envelopeTaylorMap E (envelopeCoord E i)) = F (envelopeCoord E i)
      rw [envelopeTaylorMap_coord, map_add, hnu]
      show G (envelopeCoord E i) + h (dividedPowerPolynomialVariable (E.object : Type u) i) = _
      rw [hh2 i]
      exact add_sub_cancel _ _
  have hmono : ∀ K, h' (taylorMonomial (envelopeTaylorRing E) (envelopeTaylorVar E) K) =
      taylorMonomial B (fun i => F (envelopeCoord E i) - G (envelopeCoord E i)) K := by
    intro K
    rw [map_taylorMonomial h' (envelopeTaylorVar_mem E) K]
    congr 1
    funext i
    exact hh2 i
  calc F a = h' (envelopeTaylorMap E a) :=
        (congrArg (fun r : DPMorphism E.object.dividedPowers B.dividedPowers => r a) hσ).symm
    _ = _ := by
      rw [envelopeTaylorMap_eq_sum, map_sum]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [map_mul, hnu, hmono]

/-! ### The Taylor coefficients at the empty multi-index -/

omit [DecidableEq ι] in
/-- A divided power monomial in the zero family vanishes off the empty multi-index. -/
private theorem taylorMonomial_const_zero (B : DividedPowerRing.{u}) {K : ι →₀ ℕ} (hK : K ≠ 0) :
    taylorMonomial B (fun _ : ι => (0 : B)) K = 0 := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hK
  exact Finset.prod_eq_zero hi (B.dividedPowers.dpow_eval_zero (Finsupp.mem_support_iff.mp hi))

omit [DecidableEq ι] in
/-- **`θ_0 = id`**: the constant term of the Taylor expansion of `a` is `a`. -/
theorem presentationTaylorCoeff_zero : ⇑(presentationTaylorCoeff E 0) = id := by
  funext a
  have h := envelopeTaylor_formula E E.object (DPMorphism.id E.object.dividedPowers)
    (DPMorphism.id E.object.dividedPowers) rfl (fun i => by
      show envelopeCoord E i - envelopeCoord E i ∈ _
      rw [sub_self]
      exact E.object.ideal.zero_mem) a
  change a = ∑ K ∈ envelopeTaylorSupport E a, presentationTaylorCoeff E K a *
      taylorMonomial E.object (fun i => envelopeCoord E i - envelopeCoord E i) K at h
  simp_rw [sub_self] at h
  rw [Finset.sum_eq_single 0 (fun K _ hK => by rw [taylorMonomial_const_zero _ hK, mul_zero])
    (fun h0 => by rw [presentationTaylorCoeff_eq_zero_of_notMem E h0, zero_mul]),
    taylorMonomial_zero, mul_one] at h
  exact h.symm

/-! ### The cocycle identity -/

/-- The divided power polynomial algebra `E⟨t⟩⟨s⟩` in a second set of variables. -/
private abbrev taylorRing₂ : DividedPowerRing.{u} :=
  setIndexedDividedPowerPolynomialDividedPowerRing (envelopeTaylorRing E) ι

/-- The coefficient map `E⟨t⟩ → E⟨t⟩⟨s⟩`. -/
private abbrev taylorNu₂ :
    DPMorphism (envelopeTaylorRing E).dividedPowers (taylorRing₂ E).dividedPowers :=
  setIndexedDividedPowerPolynomialCoefficientDPMorphism (envelopeTaylorRing E) ι

/-- The variable `s_i` of `E⟨t⟩⟨s⟩`. -/
private abbrev taylorVar₂ (i : ι) : taylorRing₂ E :=
  dividedPowerPolynomialVariable (envelopeTaylorRing E : Type u) i

/-- `E⟨t⟩⟨s⟩` as an algebra over `E⟨t⟩`. -/
@[instance_reducible]
private def algebraTaylorRing₂ :
    Algebra (envelopeTaylorRing E : Type u) (taylorRing₂ E : Type u) :=
  inferInstanceAs (Algebra (envelopeTaylorRing E : Type u)
    (DividedPowerAlgebra (envelopeTaylorRing E : Type u) (ι →₀ (envelopeTaylorRing E : Type u))))

attribute [local instance] algebraTaylorRing₂

/-- The monomial basis of `E⟨t⟩⟨s⟩` over `E⟨t⟩`. -/
private abbrev taylorBasis₂ :
    Module.Basis (ι →₀ ℕ) (envelopeTaylorRing E : Type u) (taylorRing₂ E : Type u) :=
  dividedPowerPolynomialMonomialBasis (envelopeTaylorRing E : Type u) ι

omit [DecidableEq ι] in
private theorem taylorVar₂_mem (i : ι) : taylorVar₂ E i ∈ (taylorRing₂ E).ideal :=
  variable_mem_polynomialIdeal (envelopeTaylorRing E) i

omit [DecidableEq ι] in
private theorem taylorMonomial_taylorVar₂ (L : ι →₀ ℕ) :
    taylorMonomial (taylorRing₂ E) (taylorVar₂ E) L = taylorBasis₂ E L := by
  classical
  exact (taylorMonomial_variable (envelopeTaylorRing E) L).trans
    (dividedPowerPolynomialMonomialBasis_apply (envelopeTaylorRing E : Type u) L).symm

/-- The coordinate functional `z ↦ [t^{[K₀]} s^{[L₀]}] z` of `E⟨t⟩⟨s⟩`. -/
private def taylorCoord₂ (K₀ L₀ : ι →₀ ℕ) : taylorRing₂ E →+ E.object :=
  (Finsupp.lapply (R := (E.object : Type u)) K₀).toAddMonoidHom.comp
    ((envelopeTaylorBasis E).repr.toAddMonoidHom.comp
      ((Finsupp.lapply (R := (envelopeTaylorRing E : Type u)) L₀).toAddMonoidHom.comp
        (taylorBasis₂ E).repr.toAddMonoidHom))

/-- The coordinates of `c • b K` in a basis `b` are `c` at `K` and `0` elsewhere. -/
private theorem basis_repr_smul_basis {R S κ : Type*} [DecidableEq κ] [Semiring R] [AddCommMonoid S]
    [Module R S]
    (b : Module.Basis κ R S) (c : R) (K K₀ : κ) :
    b.repr (c • b K) K₀ = if K = K₀ then c else 0 := by
  rw [LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs <;> simp

private theorem taylorCoord₂_apply (K₀ L₀ : ι →₀ ℕ) (x : envelopeTaylorRing E) (L : ι →₀ ℕ) :
    taylorCoord₂ E K₀ L₀ (taylorNu₂ E x * taylorBasis₂ E L) =
      if L = L₀ then (envelopeTaylorBasis E).repr x K₀ else 0 := by
  have h1 : taylorNu₂ E x * taylorBasis₂ E L = x • taylorBasis₂ E L := by
    rw [Algebra.smul_def]
    rfl
  rw [h1]
  show (envelopeTaylorBasis E).repr ((taylorBasis₂ E).repr (x • taylorBasis₂ E L) L₀) K₀ = _
  rw [basis_repr_smul_basis]
  split_ifs <;> simp

private theorem envelopeTaylorBasis_repr_nu_mul (c : E.object) (K K₀ : ι →₀ ℕ) :
    (envelopeTaylorBasis E).repr (envelopeTaylorNu E c * envelopeTaylorBasis E K) K₀ =
      if K = K₀ then c else 0 := by
  have h1 : envelopeTaylorNu E c * envelopeTaylorBasis E K = c • envelopeTaylorBasis E K := by
    rw [Algebra.smul_def]
    rfl
  rw [h1, basis_repr_smul_basis]

omit [DecidableEq ι] in
/-- **The cocycle identity `θ_{K + L} = θ_K ∘ θ_L`**: the Taylor coefficient map of a sum of
multi-indices is the composite of the Taylor coefficient maps of the summands. -/
theorem presentationTaylorCoeff_add (K₀ L₀ : ι →₀ ℕ) :
    ⇑(presentationTaylorCoeff E (K₀ + L₀)) =
      presentationTaylorCoeff E K₀ ∘ presentationTaylorCoeff E L₀ := by
  classical
  funext a
  set G : DPMorphism E.object.dividedPowers (taylorRing₂ E).dividedPowers :=
    (taylorNu₂ E).comp (envelopeTaylorMap E) with hG
  set H : DPMorphism E.object.dividedPowers (taylorRing₂ E).dividedPowers :=
    (taylorNu₂ E).comp (envelopeTaylorNu E) with hH
  obtain ⟨F, hF1, hF2⟩ := exists_envelope_dpMorphism E (taylorRing₂ E) (G.comp E.structureMap)
    (fun i => G (envelopeCoord E i) + taylorVar₂ E i)
    (envelope_eval₂Hom_map_le_of_sub_mem E _ G _ fun i => by
      simpa using taylorVar₂_mem E i)
  have hGH : G.comp E.structureMap = H.comp E.structureMap := by
    refine DFunLike.ext _ _ fun r => ?_
    have h1 := congrArg (fun s : DPMorphism A.dividedPowers (envelopeTaylorRing E).dividedPowers
      => s r) (envelopeTaylorMap_comp_structureMap E)
    show taylorNu₂ E (envelopeTaylorMap E (E.structureMap r)) =
      taylorNu₂ E (envelopeTaylorNu E (E.structureMap r))
    exact congrArg (taylorNu₂ E) h1
  have hFG : ∀ i, F (envelopeCoord E i) - G (envelopeCoord E i) = taylorVar₂ E i := fun i => by
    rw [hF2, add_sub_cancel_left]
  have hFH : ∀ i, F (envelopeCoord E i) - H (envelopeCoord E i) =
      taylorNu₂ E (envelopeTaylorVar E i) + taylorVar₂ E i := fun i => by
    rw [hF2]
    show taylorNu₂ E (envelopeTaylorMap E (envelopeCoord E i)) + taylorVar₂ E i -
      taylorNu₂ E (envelopeTaylorNu E (envelopeCoord E i)) = _
    rw [envelopeTaylorMap_coord, map_add]
    abel
  have hnuvar : ∀ i, taylorNu₂ E (envelopeTaylorVar E i) ∈ (taylorRing₂ E).ideal := fun i =>
    map_mem_ideal (taylorNu₂ E) (envelopeTaylorVar_mem E i)
  have hexp1 := envelopeTaylor_formula E (taylorRing₂ E) F G hF1
    (fun i => by rw [hFG]; exact taylorVar₂_mem E i) a
  have hexp2 := envelopeTaylor_formula E (taylorRing₂ E) F H (hF1.trans hGH)
    (fun i => by rw [hFH]; exact Ideal.add_mem _ (hnuvar i) (taylorVar₂_mem E i)) a
  have hfun1 : (fun i => F (envelopeCoord E i) - G (envelopeCoord E i)) = taylorVar₂ E :=
    funext hFG
  have hfun2 : (fun i => F (envelopeCoord E i) - H (envelopeCoord E i)) =
      (fun i => taylorNu₂ E (envelopeTaylorVar E i)) + taylorVar₂ E := funext hFH
  rw [hfun1] at hexp1
  rw [hfun2] at hexp2
  set S := envelopeTaylorSupport E a with hS
  -- the coefficient of `t^{[K₀]} s^{[L₀]}` in the first expansion
  have hc1 : taylorCoord₂ E K₀ L₀ (F a) =
      presentationTaylorCoeff E K₀ (presentationTaylorCoeff E L₀ a) := by
    rw [hexp1, map_sum]
    simp_rw [taylorMonomial_taylorVar₂]
    show ∑ L ∈ S, taylorCoord₂ E K₀ L₀ (taylorNu₂ E (envelopeTaylorMap E
      (presentationTaylorCoeff E L a)) * taylorBasis₂ E L) = _
    simp_rw [taylorCoord₂_apply]
    rw [Finset.sum_ite_eq']
    split_ifs with hL
    · rfl
    · rw [presentationTaylorCoeff_eq_zero_of_notMem E hL, map_zero]
  -- the coefficient of `t^{[K₀]} s^{[L₀]}` in the second expansion
  have hc2 : taylorCoord₂ E K₀ L₀ (F a) = presentationTaylorCoeff E (K₀ + L₀) a := by
    rw [hexp2, map_sum]
    have hterm : ∀ M : ι →₀ ℕ, taylorCoord₂ E K₀ L₀ (H (presentationTaylorCoeff E M a) *
        taylorMonomial (taylorRing₂ E)
          ((fun i => taylorNu₂ E (envelopeTaylorVar E i)) + taylorVar₂ E) M) =
        if K₀ + L₀ = M then presentationTaylorCoeff E M a else 0 := by
      intro M
      rw [taylorMonomial_add _ _ _ hnuvar (taylorVar₂_mem E) M, Finset.mul_sum, map_sum]
      have hx : ∀ x : (ι →₀ ℕ) × (ι →₀ ℕ),
          H (presentationTaylorCoeff E M a) *
              (taylorMonomial (taylorRing₂ E) (fun i => taylorNu₂ E (envelopeTaylorVar E i)) x.1 *
                taylorMonomial (taylorRing₂ E) (taylorVar₂ E) x.2) =
            taylorNu₂ E (envelopeTaylorNu E (presentationTaylorCoeff E M a) *
              envelopeTaylorBasis E x.1) * taylorBasis₂ E x.2 := by
        intro x
        rw [← map_taylorMonomial (taylorNu₂ E) (envelopeTaylorVar_mem E),
          taylorMonomial_envelopeTaylorVar, taylorMonomial_taylorVar₂, map_mul, mul_assoc]
        rfl
      simp_rw [hx, taylorCoord₂_apply, envelopeTaylorBasis_repr_nu_mul]
      have hite : ∀ x : (ι →₀ ℕ) × (ι →₀ ℕ),
          (if x.2 = L₀ then (if x.1 = K₀ then presentationTaylorCoeff E M a else 0) else 0) =
            if (K₀, L₀) = x then presentationTaylorCoeff E M a else 0 := by
        rintro ⟨K, L⟩
        by_cases hK : K = K₀
        · by_cases hL : L = L₀
          · subst hK hL
            simp
          · simp [hL, Ne.symm hL]
        · simp [hK, Ne.symm hK]
      simp_rw [hite]
      rw [Finset.sum_ite_eq]
      simp only [mem_antidiagonal]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq]
    split_ifs with hM
    · rfl
    · rw [presentationTaylorCoeff_eq_zero_of_notMem E hM]
  exact hc2.symm.trans hc1

/-- **The first-order Taylor operators `δ_i = θ_{e_i}`** of the envelope. -/
def envelopeDelta (i : ι) : E.object →+ E.object :=
  presentationTaylorCoeff E (Finsupp.single i 1)

omit [DecidableEq ι] in
/-- **The operators `δ_i` commute**, by the cocycle identity. -/
theorem envelopeDelta_comm (i j : ι) :
    ⇑(envelopeDelta E i) ∘ ⇑(envelopeDelta E j) = ⇑(envelopeDelta E j) ∘ ⇑(envelopeDelta E i) := by
  rw [envelopeDelta, envelopeDelta, ← presentationTaylorCoeff_add,
    ← presentationTaylorCoeff_add, add_comm]

omit [DecidableEq ι] in
/-- **The Taylor coefficients are the composites of the `δ_i`**: `θ_0 = id` and
`θ_{K + e_i} = δ_i ∘ θ_K`. -/
theorem isThetaMonomialFamily_presentationTaylorCoeff :
    IsThetaMonomialFamily (E.object : Type u) (fun i => ⇑(envelopeDelta E i))
      (fun K => ⇑(presentationTaylorCoeff E K)) :=
  ⟨presentationTaylorCoeff_zero E, fun i K => by
    show ⇑(presentationTaylorCoeff E (K + Finsupp.single i 1)) =
      ⇑(envelopeDelta E i) ∘ ⇑(presentationTaylorCoeff E K)
    rw [add_comm, presentationTaylorCoeff_add]
    rfl⟩

/-- **`δ_i(y_j) = [i = j]`.** -/
theorem envelopeDelta_coord (i j : ι) :
    envelopeDelta E i (envelopeCoord E j) = if i = j then 1 else 0 := by
  have h0 : envelopeTaylorNu E (envelopeCoord E j) =
      envelopeTaylorNu E (envelopeCoord E j) * envelopeTaylorBasis E 0 := by
    rw [← taylorMonomial_envelopeTaylorVar, taylorMonomial_zero, mul_one]
  have h1 : envelopeTaylorVar E j =
      envelopeTaylorNu E 1 * envelopeTaylorBasis E (Finsupp.single j 1) := by
    rw [map_one, one_mul, ← taylorMonomial_envelopeTaylorVar]
    show envelopeTaylorVar E j = ∏ k ∈ (Finsupp.single j 1).support, _
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.prod_singleton,
      Finsupp.single_eq_same, (envelopeTaylorRing E).dividedPowers.dpow_one
        (envelopeTaylorVar_mem E j)]
  show (envelopeTaylorBasis E).repr (envelopeTaylorMap E (envelopeCoord E j))
    (Finsupp.single i 1) = _
  rw [envelopeTaylorMap_coord, h0, h1, map_add, Finsupp.add_apply, envelopeTaylorBasis_repr_nu_mul,
    envelopeTaylorBasis_repr_nu_mul, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm, zero_add]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (fun h => hij (Finsupp.single_left_injective one_ne_zero h).symm), if_neg hij]

end TaylorMap

/-! ### Divided power derivations of the envelope -/

section FirstOrder

variable {ι : Type u} [DecidableEq ι] [Fintype ι] (R : DividedPowerRing.{u}) (M : Type u)
  [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

/-- The first-order thickening `R ⊕ M` as a divided power ring. -/
private abbrev firstOrderRing : DividedPowerRing.{u} :=
  .of (firstOrderExtension R M) (firstOrderExtensionIdeal R M) (firstOrderDividedPowers R M)

private theorem inr_mem_firstOrderRing (m : M) :
    (TrivSqZeroExt.inr m : firstOrderExtension R M) ∈ (firstOrderRing R M).ideal :=
  (mem_firstOrderExtensionIdeal_iff R M _).mpr (by
    rw [firstOrderEquiv_apply, TrivSqZeroExt.fst_inr]
    exact R.ideal.zero_mem)

private theorem firstOrderRing_dpow_inr (n : ℕ) (m : M) :
    (firstOrderRing R M).dividedPowers.dpow (n + 2) (TrivSqZeroExt.inr m) = 0 := by
  show squareZeroDpow R.dividedPowers (firstOrderEquiv R M) (firstOrderExtensionIdeal R M)
    (n + 1 + 1) (TrivSqZeroExt.inr m) = 0
  rw [squareZeroDpow_succ _ _ _ (n + 1) (inr_mem_firstOrderRing R M m), firstOrderEquiv_apply,
    TrivSqZeroExt.fst_inr, R.dividedPowers.dpow_eval_zero (by omega),
    R.dividedPowers.dpow_eval_zero (by omega), zero_smul]
  exact map_zero (firstOrderEquiv R M).symm

private theorem firstOrderRing_dpow_one_inr (m : M) :
    (firstOrderRing R M).dividedPowers.dpow 1 (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr m :=
  (firstOrderRing R M).dividedPowers.dpow_one (inr_mem_firstOrderRing R M m)

/-- **The `M`-component of a divided power monomial of a square-zero family**, summed over any
finset of coordinates containing every `j` with `K = e_j`: it is `m_j` at `K = e_j` and `0`
otherwise.  No finiteness of the coordinates is needed. -/
private theorem firstOrderRing_taylorMonomial_snd_finset {ι : Type u} [DecidableEq ι]
    (m : ι → M) (K : ι →₀ ℕ) (T : Finset ι) (hT : ∀ j, K = Finsupp.single j 1 → j ∈ T) :
    TrivSqZeroExt.snd (R := R) (M := M)
        (taylorMonomial (firstOrderRing R M) (fun i => TrivSqZeroExt.inr (m i)) K) =
      ∑ i ∈ T, if K = Finsupp.single i 1 then m i else 0 := by
  classical
  by_cases h0 : K = 0
  · subst h0
    rw [taylorMonomial_zero]
    refine (TrivSqZeroExt.snd_one).trans (Finset.sum_eq_zero fun i _ => ?_).symm
    exact ite_eq_right_of_eq_false _ _ (eq_false (Finsupp.single_ne_zero.mpr one_ne_zero).symm)
  by_cases hs : ∃ j, K = Finsupp.single j 1
  · obtain ⟨j, rfl⟩ := hs
    rw [Finset.sum_eq_single_of_mem j (hT j rfl) (fun i _ hij => ite_eq_right_of_eq_false _ _
        (eq_false fun h => hij (Finsupp.single_left_injective one_ne_zero h).symm)),
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    change TrivSqZeroExt.snd (R := R) (M := M) (∏ k ∈ (Finsupp.single j 1).support,
      (firstOrderRing R M).dividedPowers.dpow (Finsupp.single j 1 k) (TrivSqZeroExt.inr (m k))) =
        m j
    rw [Finsupp.support_single _ one_ne_zero, Finset.prod_singleton, Finsupp.single_eq_same,
      firstOrderRing_dpow_one_inr, TrivSqZeroExt.snd_inr]
  push Not at hs
  rw [Finset.sum_eq_zero fun i _ => ite_eq_right_of_eq_false _ _ (eq_false (hs i))]
  suffices h : taylorMonomial (firstOrderRing R M) (fun i => TrivSqZeroExt.inr (m i)) K = 0 by
    rw [h]
    rfl
  by_cases hbig : ∃ i ∈ K.support, 2 ≤ K i
  · obtain ⟨i, hi, h2⟩ := hbig
    refine Finset.prod_eq_zero hi ?_
    obtain ⟨n, hn⟩ : ∃ n, K i = n + 2 := ⟨K i - 2, by omega⟩
    rw [hn]
    exact firstOrderRing_dpow_inr R M n (m i)
  push Not at hbig
  have hone : ∀ i ∈ K.support, K i = 1 := fun i hi => by
    have := Finsupp.mem_support_iff.mp hi
    have := hbig i hi
    omega
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr h0
  obtain ⟨l, hl, hlj⟩ : ∃ l ∈ K.support, l ≠ j := by
    by_contra hcon
    push Not at hcon
    refine hs j (Finsupp.ext fun k => ?_)
    by_cases hk : k = j
    · subst hk
      rw [Finsupp.single_eq_same, hone k hj]
    · rw [Finsupp.single_eq_of_ne hk]
      exact Finsupp.notMem_support_iff.mp fun hk' => hk (hcon k hk')
  change ∏ k ∈ K.support, _ = 0
  rw [← Finset.mul_prod_erase _ _ hj,
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hlj, hl⟩), hone j hj, hone l hl,
    firstOrderRing_dpow_one_inr, firstOrderRing_dpow_one_inr, ← mul_assoc,
    TrivSqZeroExt.inr_mul_inr, zero_mul]

/-- **The divided power monomials of a square-zero family**: in `R ⊕ M`, the monomial
`(0, m)^{[K]}` is `1` at `K = 0`, `(0, m_i)` at `K = e_i` and `0` otherwise; its `M`-component
is therefore the sum below. -/
private theorem firstOrderRing_taylorMonomial_snd (m : ι → M) (K : ι →₀ ℕ) :
    TrivSqZeroExt.snd (R := R) (M := M)
        (taylorMonomial (firstOrderRing R M) (fun i => TrivSqZeroExt.inr (m i)) K) =
      ∑ i, if K = Finsupp.single i 1 then m i else 0 :=
  firstOrderRing_taylorMonomial_snd_finset R M m K Finset.univ fun j _ => Finset.mem_univ j

end FirstOrder

section DerivationFinset

variable {A : DividedPowerRing.{u}} {ι : Type u} {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ)

/-- **A divided power derivation of the envelope is determined by its values on the
coordinates, for any family of variables**: for a divided power morphism `φ : E → R` and a divided
power derivation `∂ : R → M` over `A`, every `a ∈ E` has a finite set `T` of coordinates outside
which `δ_i(a) = 0`, and `∂(φ a) = ∑_{i ∈ T} φ(δ_i a) · ∂(φ y_i)`.

This is `Crystalline.envelopeTaylor_derivation` with the sum over all coordinates, which needs
finitely many of them, replaced by the sum over the coordinates occurring in the Taylor support
of `a`. -/
theorem envelopeTaylor_derivation_finset (R : DividedPowerRing.{u})
    (φ : DPMorphism E.object.dividedPowers R.dividedPowers) (M : Type u) [AddCommGroup M]
    [Module R M] (dd : DividedPowerDerivation (A : Type u) R (φ.comp E.structureMap).toRingHom M)
    (a : E.object) :
    ∃ T : Finset ι, (∀ i ∉ T, envelopeDelta E i a = 0) ∧
      dd (φ a) = ∑ i ∈ T, φ (envelopeDelta E i a) • dd (φ (envelopeCoord E i)) := by
  classical
  set T : Finset ι := (envelopeTaylorSupport E a).biUnion fun K => K.support with hT
  have hsingle : ∀ i, Finsupp.single i 1 ∈ envelopeTaylorSupport E a → i ∈ T := fun i hi =>
    Finset.mem_biUnion.mpr ⟨_, hi, by simp⟩
  refine ⟨T, fun i hi => presentationTaylorCoeff_eq_zero_of_notMem E fun h => hi (hsingle i h),
    ?_⟩
  let : Module Rᵐᵒᵖ M := Module.compHom M (RingEquiv.toOpposite R).symm.toRingHom
  have : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  let P₁ : DPMorphism R.dividedPowers (firstOrderRing R M).dividedPowers :=
    DPMorphism.mk' (firstOrderP₁_isDPMorphism (A : Type u) R (φ.comp E.structureMap).toRingHom M dd)
  let P₀ : DPMorphism R.dividedPowers (firstOrderRing R M).dividedPowers :=
    DPMorphism.mk' (firstOrderP₀_isDPMorphism R M)
  have hP : ∀ x, P₁ x - P₀ x = TrivSqZeroExt.inr (dd x) :=
    firstOrderP₁_sub_P₀ (A : Type u) R (φ.comp E.structureMap).toRingHom M dd
  have hFG : (P₁.comp φ).comp E.structureMap = (P₀.comp φ).comp E.structureMap := by
    refine DFunLike.ext _ _ fun r => ?_
    have h1 := hP (φ (E.structureMap r))
    rw [show dd (φ (E.structureMap r)) = 0 from dd.map_ringHom r, TrivSqZeroExt.inr_zero] at h1
    exact sub_eq_zero.mp h1
  have hxi : ∀ i, (P₁.comp φ) (envelopeCoord E i) - (P₀.comp φ) (envelopeCoord E i) =
      TrivSqZeroExt.inr (dd (φ (envelopeCoord E i))) := fun i => hP _
  have h := envelopeTaylor_formula E (firstOrderRing R M) (P₁.comp φ) (P₀.comp φ) hFG
    (fun i => by rw [hxi]; exact inr_mem_firstOrderRing R M _) a
  rw [show (fun i => (P₁.comp φ) (envelopeCoord E i) - (P₀.comp φ) (envelopeCoord E i)) =
    fun i => TrivSqZeroExt.inr (dd (φ (envelopeCoord E i))) from funext hxi] at h
  have h' := congrArg TrivSqZeroExt.snd h
  change (firstOrderP₁ (A : Type u) R (φ.comp E.structureMap).toRingHom M dd (φ a)).snd = _
    at h'
  rw [firstOrderP₁_snd, TrivSqZeroExt.snd_sum] at h'
  rw [h']
  have hterm : ∀ K ∈ envelopeTaylorSupport E a, ((P₀.comp φ) (presentationTaylorCoeff E K a) *
      taylorMonomial (firstOrderRing R M)
        (fun i => TrivSqZeroExt.inr (dd (φ (envelopeCoord E i)))) K).snd =
      ∑ i ∈ T, if K = Finsupp.single i 1 then
        φ (presentationTaylorCoeff E K a) • dd (φ (envelopeCoord E i)) else 0 := by
    intro K hK
    change (algebraMap R (firstOrderExtension R M) (φ (presentationTaylorCoeff E K a)) * _).snd = _
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_eq_smul, TrivSqZeroExt.snd_smul,
      firstOrderRing_taylorMonomial_snd_finset R M _ K T (fun j hj => hsingle j (hj ▸ hK)),
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_ite, smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq']
  split_ifs with hi
  · rfl
  · rw [show envelopeDelta E i a = 0 from presentationTaylorCoeff_eq_zero_of_notMem E hi,
      show φ 0 = 0 from map_zero φ.toRingHom, zero_smul]

end DerivationFinset

section Derivation

variable {A : DividedPowerRing.{u}} {ι : Type u} [DecidableEq ι] [Fintype ι]
  {J : Ideal (MvPolynomial ι A)} {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ)

omit [DecidableEq ι] in
/-- **A divided power derivation of the envelope is determined by its values on the
coordinates**: for a divided power morphism `φ : E → R` and a divided power derivation
`∂ : R → M` over `A`,

`∂(φ a) = ∑_i φ(δ_i a) · ∂(φ y_i)`.

This is Taylor's formula `Crystalline.envelopeTaylor_formula` for the two maps
`a ↦ (φ a, ∂ φ a)` and `a ↦ (φ a, 0)` into the first-order thickening `R ⊕ M`, read in the
`M`-component, where only the monomials of degree one survive. -/
theorem envelopeTaylor_derivation (R : DividedPowerRing.{u})
    (φ : DPMorphism E.object.dividedPowers R.dividedPowers) (M : Type u) [AddCommGroup M]
    [Module R M] (dd : DividedPowerDerivation (A : Type u) R (φ.comp E.structureMap).toRingHom M)
    (a : E.object) :
    dd (φ a) = ∑ i, φ (envelopeDelta E i a) • dd (φ (envelopeCoord E i)) := by
  classical
  let : Module Rᵐᵒᵖ M := Module.compHom M (RingEquiv.toOpposite R).symm.toRingHom
  have : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  let P₁ : DPMorphism R.dividedPowers (firstOrderRing R M).dividedPowers :=
    DPMorphism.mk' (firstOrderP₁_isDPMorphism (A : Type u) R (φ.comp E.structureMap).toRingHom M dd)
  let P₀ : DPMorphism R.dividedPowers (firstOrderRing R M).dividedPowers :=
    DPMorphism.mk' (firstOrderP₀_isDPMorphism R M)
  have hP : ∀ x, P₁ x - P₀ x = TrivSqZeroExt.inr (dd x) :=
    firstOrderP₁_sub_P₀ (A : Type u) R (φ.comp E.structureMap).toRingHom M dd
  have hFG : (P₁.comp φ).comp E.structureMap = (P₀.comp φ).comp E.structureMap := by
    refine DFunLike.ext _ _ fun r => ?_
    have h1 := hP (φ (E.structureMap r))
    rw [show dd (φ (E.structureMap r)) = 0 from dd.map_ringHom r, TrivSqZeroExt.inr_zero] at h1
    exact sub_eq_zero.mp h1
  have hxi : ∀ i, (P₁.comp φ) (envelopeCoord E i) - (P₀.comp φ) (envelopeCoord E i) =
      TrivSqZeroExt.inr (dd (φ (envelopeCoord E i))) := fun i => hP _
  have h := envelopeTaylor_formula E (firstOrderRing R M) (P₁.comp φ) (P₀.comp φ) hFG
    (fun i => by rw [hxi]; exact inr_mem_firstOrderRing R M _) a
  rw [show (fun i => (P₁.comp φ) (envelopeCoord E i) - (P₀.comp φ) (envelopeCoord E i)) =
    fun i => TrivSqZeroExt.inr (dd (φ (envelopeCoord E i))) from funext hxi] at h
  have h' := congrArg TrivSqZeroExt.snd h
  change (firstOrderP₁ (A : Type u) R (φ.comp E.structureMap).toRingHom M dd (φ a)).snd = _
    at h'
  rw [firstOrderP₁_snd, TrivSqZeroExt.snd_sum] at h'
  rw [h']
  have hterm : ∀ K : ι →₀ ℕ, ((P₀.comp φ) (presentationTaylorCoeff E K a) *
      taylorMonomial (firstOrderRing R M)
        (fun i => TrivSqZeroExt.inr (dd (φ (envelopeCoord E i)))) K).snd =
      ∑ i, if K = Finsupp.single i 1 then
        φ (presentationTaylorCoeff E K a) • dd (φ (envelopeCoord E i)) else 0 := by
    intro K
    show (algebraMap R (firstOrderExtension R M) (φ (presentationTaylorCoeff E K a)) * _).snd = _
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_eq_smul, TrivSqZeroExt.snd_smul,
      firstOrderRing_taylorMonomial_snd, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_ite, smul_zero]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq']
  split_ifs with hi
  · rfl
  · rw [show envelopeDelta E i a = 0 from presentationTaylorCoeff_eq_zero_of_notMem E hi,
      show φ 0 = 0 from map_zero φ.toRingHom, zero_smul]

end Derivation

end Crystalline
