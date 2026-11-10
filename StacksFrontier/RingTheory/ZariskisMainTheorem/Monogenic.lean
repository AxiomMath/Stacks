module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Zariski's Main Theorem for a monogenic algebra
-/

/-!
# Zariski's Main Theorem for a monogenic algebra

Stacks tag 00Q8 (Lemma 10.123.11), part of the section on Zariski's Main Theorem.

Let `R` be a commutative ring, let `I ⊆ R[x]` be an ideal of the univariate
polynomial ring, and set `S = R[x] / I` with the canonical finite type ring map
`R → S`. Let `q ⊂ S` be a prime ideal and assume that `R → S` is quasi-finite at
`q`. Let `S' ⊆ S` be the integral closure of `R` in `S`. Then there exists an
element `g ∈ S'`, `g ∉ q`, such that the canonical induced ring map `S'_g → S_g` is
an isomorphism.

The hypothesis that `S` is *monogenic* over `R`, i.e. a quotient of the one-variable
polynomial ring `R[x]`, is essential; the corresponding statement for polynomial
rings in several variables is false in general.

## Conventions

Throughout, `q ⊂ S` is a prime ideal and its contraction to `R` is the prime
`p = (algebraMap R S)⁻¹(q) = q.comap (algebraMap R S)`. For a prime ideal `p` of a
ring `R`, the residue field `κ(p) = Frac(R/p) = R_p / p R_p` is
`Ideal.ResidueField p`.

Quasi-finiteness at `q` is used here in the form of Stacks tag 00PK condition (2):
`S_q / p S_q` is a finite-dimensional vector space over `κ(p)`, where
`S_q = Localization.AtPrime q` and `p S_q = p.map (algebraMap R S_q)`. Expressing
this needs the canonical ring map `κ(p) → S_q / p S_q` that makes `S_q / p S_q` a
`κ(p)`-algebra; it exists because the composite `R → S_q → S_q / p S_q` sends `p`
to zero and sends every element of `R \ p` to a unit, hence factors through
`R_p / p R_p = κ(p)`.
-/

@[expose] public section

open Polynomial

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- The composite ring map `R → S_q → S_q / p S_q`, where `p = q.comap (algebraMap R S)`. -/
noncomputable def QF.cmap (q : Ideal S) [q.IsPrime] :
    R →+* (Localization.AtPrime q ⧸
      (Ideal.map (algebraMap R (Localization.AtPrime q)) (q.comap (algebraMap R S)))) :=
  (Ideal.Quotient.mk _).comp (algebraMap R (Localization.AtPrime q))

/-- Every element of `R \ p` is sent to a unit by `QF.cmap`. -/
theorem QF.cmap_unit (q : Ideal S) [q.IsPrime] (r : R) (hr : r ∉ q.comap (algebraMap R S)) :
    IsUnit (QF.cmap q r) := by
  have hr' : algebraMap R S r ∉ q := fun h => hr (Ideal.mem_comap.mpr h)
  have hu : IsUnit (algebraMap R (Localization.AtPrime q) r) := by
    have heq : algebraMap R (Localization.AtPrime q) r
        = algebraMap S (Localization.AtPrime q) (algebraMap R S r) := by
      rw [← IsScalarTower.algebraMap_apply]
    rw [heq]
    exact IsLocalization.map_units (Localization.AtPrime q) (⟨algebraMap R S r, hr'⟩ : q.primeCompl)
  exact hu.map (Ideal.Quotient.mk _)

/-- Every element of `p` is sent to zero by `QF.cmap`. -/
theorem QF.cmap_kills (q : Ideal S) [q.IsPrime] (x : R) (hx : x ∈ q.comap (algebraMap R S)) :
    QF.cmap q x = 0 := by
  unfold QF.cmap
  simp only [RingHom.comp_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hx

/-- The induced ring map `R_p → S_q / p S_q` obtained from `QF.cmap` by the universal
property of localization. -/
noncomputable def QF.liftLoc (q : Ideal S) [q.IsPrime] :
    Localization.AtPrime (q.comap (algebraMap R S)) →+*
      (Localization.AtPrime q ⧸
        (Ideal.map (algebraMap R (Localization.AtPrime q)) (q.comap (algebraMap R S)))) :=
  IsLocalization.lift (M := (q.comap (algebraMap R S)).primeCompl) (g := QF.cmap q)
    (fun y => QF.cmap_unit q y.val y.property)

/-- `QF.liftLoc` extends `QF.cmap` along the localization map: for `x : R`, the
lift applied to the image of `x` in `R_p` is `QF.cmap q x`. -/
theorem QF.liftLoc_comp (q : Ideal S) [q.IsPrime] (x : R) :
    QF.liftLoc q (algebraMap R (Localization.AtPrime (q.comap (algebraMap R S))) x)
      = QF.cmap q x := by
  unfold QF.liftLoc
  rw [IsLocalization.lift_eq]

/-- The canonical ring map `κ(p) → S_q / p S_q`.  This is the structure map exhibiting
`S_q / p S_q` as a `κ(p)`-vector space. -/
noncomputable def QF.kappaMap (q : Ideal S) [q.IsPrime] :
    (q.comap (algebraMap R S)).ResidueField →+*
      (Localization.AtPrime q ⧸
        (Ideal.map (algebraMap R (Localization.AtPrime q)) (q.comap (algebraMap R S)))) := by
  refine Ideal.Quotient.lift _ (QF.liftLoc q) ?_
  intro a ha
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨y, hy, rfl⟩
    rw [QF.liftLoc_comp]
    exact QF.cmap_kills q y hy
  · simp
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro c x _ hx; simp [hx]

/-- `R → S` is quasi-finite at the prime `q` if `S_q / p S_q` is a finite
`κ(p)`-module, where `p = q.comap (algebraMap R S)` and the `κ(p)`-module structure
is the canonical one given by `QF.kappaMap`. -/
@[ega "0 7.4.1" "special case", ega "0 7.4.4"]
def QuasiFiniteAt (q : Ideal S) [q.IsPrime] : Prop :=
  letI : Algebra (q.comap (algebraMap R S)).ResidueField
      (Localization.AtPrime q ⧸
        (Ideal.map (algebraMap R (Localization.AtPrime q)) (q.comap (algebraMap R S)))) :=
    (QF.kappaMap q).toAlgebra
  Module.Finite (q.comap (algebraMap R S)).ResidueField
    (Localization.AtPrime q ⧸
      (Ideal.map (algebraMap R (Localization.AtPrime q)) (q.comap (algebraMap R S))))

/-!
### The integral closure and the induced localization map

The integral closure of `R` in `S` is `integralClosure R S : Subalgebra R S`, the
subring of elements of `S` integral over the image of `R`.

For `g ∈ S'`, we view `g` as an element of `S'` and `(g : S)` as its image in `S`.
The inclusion `S' ↪ S`, namely `Subalgebra.val`, together with the universal
property of localization, induces a ring map `S'_g → S_g` from
`Localization.Away g`, the localization of `S'` at the powers of `g`, to
`Localization.Away (g : S)`, the localization of `S` at the powers of `(g : S)`.
-/

/-- The submonoid inclusion needed to form the induced localization map: the powers of
`g` in `S'` map into the powers of `(g : S)` in `S` under the inclusion `S' ↪ S`. -/
theorem QF.powers_le (g : integralClosure R S) :
    Submonoid.powers g ≤
      Submonoid.comap ((integralClosure R S).val : (integralClosure R S) →+* S)
        (Submonoid.powers ((integralClosure R S).val g)) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

/-- The canonical induced ring map `S'_g → S_g`, where `S' = integralClosure R S`,
`S'_g = Localization.Away g` and `S_g = Localization.Away (g : S)`. -/
noncomputable def QF.locMap (g : integralClosure R S) :
    Localization.Away g →+* Localization.Away ((integralClosure R S).val g) :=
  IsLocalization.map (Localization.Away ((integralClosure R S).val g))
    (Subalgebra.val (integralClosure R S) : (integralClosure R S) →+* S)
    (QF.powers_le g)

/-!
## The theorem and its three ingredients

With `S = R[x]/I` and the canonical finite type map `R → S`, if `q ⊂ S` is prime,
`R → S` is quasi-finite at `q`, and `S' ⊆ S` is the integral closure of `R` in `S`,
then there exists `g ∈ S'`, `g ∉ q`, such that the induced map `S'_g → S_g` is an
isomorphism.

Write `x = mk I X ∈ S = R[X]/I` for the canonical generator,
`p = q.comap (algebraMap R S)` for the contracted prime, and
`S' = integralClosure R S`. The proof has three parts.

First, quasi-finiteness at `q` forces the existence of `f ∈ I` having *some*
coefficient outside `p`, equivalently with `algebraMap R S (f.coeff j) ∉ q`. This is
the only step that uses quasi-finiteness. Indeed, if every `f ∈ I` had all
coefficients in `p` then `I ⊆ p·R[X]`, so the fibre ring
`S ⊗_R κ(p) = κ(p)[x]/(I·κ(p)[x]) = κ(p)[x]` would be a polynomial ring over the
residue field, and localizing at `q` would make `S_q/pS_q` an infinite-dimensional
`κ(p)`-vector space, since it contains all the `κ(p)`-linearly independent powers
`x^n`, contradicting `Module.Finite`.

Second, given any relation `∑_{j≤m} b_j x^j = 0` in `S` with `b_j ∈ S'` and at least
one `b_j ∉ q`, there is `g ∈ S'`, `g ∉ q`, with `g·x ∈ S'`. Induct on `m`. Stacks
tag 00PQ gives integrality of `b_m·x` over `S'`, hence over `R` by transitivity, so
`b_m·x ∈ S'`. If `b_m ∉ q`, take `g = b_m`. If `b_m ∈ q`, set
`b'_{m-1} = b_m·x + b_{m-1} ∈ S'`; then
`b'_{m-1} x^{m-1} + ∑_{j<m-1} b_j x^j = ∑_{j≤m} b_j x^j = 0` is a shorter relation,
the witnessing `b_j ∉ q` survives — if its index was `m-1`, note
`b'_{m-1} ≡ b_{m-1} (mod q)` because `b_m·x ∈ q` — and one recurses. The base case
`m = 0` is vacuous, since `b_0 = 0 ∈ q` contradicts `b_0 ∉ q`.

Third, for `g ∈ S'` with `g ∉ q` and `g·x ∈ S'`, the map `QF.locMap g : S'_g → S_g`
is bijective. It is injective because `S' ↪ S` is injective and localization
preserves injectivity, matching the target localization at
`Submonoid.map val (powers g) = powers (val g)`. For surjectivity, every element of
`S_g = Localization.Away (g:S)` is `s/g^n` with `s ∈ S`; since `S` is generated as
an `R`-algebra by `x` and the image of `QF.locMap g` is a subring containing
`algebraMap R`, the inverse of `g`, and `algebraMap S _ x` — because
`x = (g·x)·g⁻¹` in `S_g` with `g·x ∈ S'` — every `s/1` and hence every `s/g^n` lies
in the image.

### The first part, stated over an abstract prime

The relation coming from quasi-finiteness is obtained through helper lemmas phrased
over a *general* `q : Ideal S` rather than the concrete `q : Ideal (R[X]⧸I)`,
mirroring the `QF.*` vocabulary, and `S := R[X]⧸I` is only substituted at the very
end. This keeps instance resolution tractable: over `Ideal (R[X]⧸I)` the searches
for `HasQuotient (Localization.AtPrime q) _` and for the semiring structure on the
quotient do not terminate quickly.

For abstract `q : Ideal S` we abbreviate, with `p = q.comap (algebraMap R S)`:

* `B q := Localization.AtPrime q ⧸ (p.map (algebraMap R (Localization.AtPrime q)))`,
  the `κ(p)`-vector space appearing in the definition of quasi-finiteness, with its
  `κ(p)`-algebra structure `(QF.kappaMap q).toAlgebra`;
* `QF.toB q : S →+* B q`, the composite `S → S_q → B q`.

Then `Module.Finite κ(p) (B q)` makes the powers `β^n` of `β = QF.toB q t` linearly
dependent, so some *nonzero* `P : κ(p)[X]` satisfies `aeval β P = 0` in `B q`, i.e.
`∑ Pₖ • β^k = 0`. Descending such a relation to honest `R`-data, by clearing
denominators of the `κ(p)`-coefficients, landing in `p·S` via the localization
membership criterion, and using the fibre identification `S/pS ≅ (R/p)[X]`, reads off
from the nonzero top coefficient of `P` an `f ∈ I` with a coefficient outside `p`.
-/

/-- `B q` — the `κ(p)`-vector space `S_q / p S_q` of Definition 2, for abstract `q : Ideal S`. -/
abbrev QF.B (q : Ideal S) [q.IsPrime] : Type _ :=
  Localization.AtPrime q ⧸
    (Ideal.map (algebraMap R (Localization.AtPrime q)) (q.comap (algebraMap R S)))

/-- The `κ(p)`-algebra instance on `QF.B q`. -/
noncomputable instance QF.instAlgebraResidueFieldB (q : Ideal S) [q.IsPrime] :
    Algebra (q.comap (algebraMap R S)).ResidueField (QF.B (R := R) q) :=
  (QF.kappaMap q).toAlgebra

/-- The composite ring map `S → S_q → B q`. -/
noncomputable def QF.toB (q : Ideal S) [q.IsPrime] : S →+* QF.B (R := R) q :=
  (Ideal.Quotient.mk _).comp (algebraMap S (Localization.AtPrime q))

/-- The structure map `κ(p) → B q` agrees with `S → B q` on the image of `R`: for `r : R`,
`kappaMap (algebraMap R κ(p) r) = QF.toB q (algebraMap R S r)`. -/
theorem QF.kappaMap_algebraMap (q : Ideal S) [q.IsPrime] (r : R) :
    QF.kappaMap q (algebraMap R (q.comap (algebraMap R S)).ResidueField r)
      = QF.toB (R := R) q (algebraMap R S r) := by
  change QF.kappaMap q (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime _) r)) = _
  have hlift : QF.kappaMap q (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime (q.comap
      (algebraMap R S))) r))
      = QF.liftLoc q (algebraMap R (Localization.AtPrime (q.comap (algebraMap R S))) r) := by
    unfold QF.kappaMap
    rfl
  rw [hlift, QF.liftLoc_comp]
  unfold QF.cmap QF.toB
  simp only [RingHom.comp_apply]
  congr 1

/-- If `R → S` is quasi-finite at `q`, then for every `t : S` there is a *nonzero*
polynomial `P` over `κ(p)` with `aeval (QF.toB q t) P = 0` in `B q`, equivalently
`∑ₖ Pₖ • β^k = 0` for `β = QF.toB q t`. Finiteness of `B q` over `κ(p)` makes it an
integral `κ(p)`-algebra, so `β` satisfies a monic polynomial. -/
theorem relation_polynomial_of_quasiFinite (q : Ideal S) [q.IsPrime]
    (hqf : QuasiFiniteAt (R := R) q) (t : S) :
    ∃ P : Polynomial (q.comap (algebraMap R S)).ResidueField, P ≠ 0 ∧
      (Polynomial.aeval (QF.toB (R := R) q t)) P = 0 := by
  -- `hqf` says `Module.Finite κ(p) (B q)`, so `B q` is an integral `κ(p)`-algebra and
  -- `β = QF.toB q t` satisfies a monic polynomial over `κ(p)`; a monic polynomial is
  -- nonzero, which is exactly what is required.
  have hfin : Module.Finite (q.comap (algebraMap R S)).ResidueField (QF.B (R := R) q) := hqf
  have hint : Algebra.IsIntegral (q.comap (algebraMap R S)).ResidueField (QF.B (R := R) q) :=
    Algebra.IsIntegral.of_finite _ _
  have hβ : IsIntegral (q.comap (algebraMap R S)).ResidueField (QF.toB (R := R) q t) :=
    Algebra.IsIntegral.isIntegral _
  obtain ⟨P, hmonic, hP⟩ := hβ
  exact ⟨P, hmonic.ne_zero, hP⟩

/-- The quotient map `R[X] → R[X]/I` is evaluation at the class of `X`. -/
private theorem mk_eq_aeval_mk_X {R : Type*} [CommRing R] {I : Ideal R[X]} (g : R[X]) :
    Ideal.Quotient.mk I g = Polynomial.aeval (Ideal.Quotient.mk I X : R[X] ⧸ I) g := by
  rw [← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_X_left_apply g, aeval_algHom_apply]
  simp

-- this proof's elaboration needs more than the default heartbeat budget
/-- Descent of the relation to `R`. Specializing to `q : Ideal (R[X]⧸I)` and
`t = x = mk I X`, a *nonzero* `κ(p)[X]`-relation `aeval (QF.toB q x) P = 0` descends
to an honest `f ∈ I` having a coefficient outside `p = q.comap (algebraMap R S)`.

Argue by contraposition: if every `f ∈ I` has all coefficients in `p` then reduction
of coefficients modulo `p` kills `I`, so it factors through a ring map
`ψ : S → (R/p)[X]`, and every `s ∉ q` has nonzero image under `ψ`. Composing with
`(R/p)[X] → Frac((R/p)[X])` therefore extends over the localization `S_q` and, since
`p` is killed, over `B q = S_q/pS_q`, giving `Φ : B q → Frac((R/p)[X])` with
`Φ β = X`. As `X` is transcendental over `R/p`, hence over `κ(p)`, the relation
`aeval β P = 0` forces `P = 0`, contradicting `P ≠ 0`. -/
theorem relation_descends_to_R (R : Type*) [CommRing R] (I : Ideal (R[X]))
    (q : Ideal (R[X] ⧸ I)) [q.IsPrime]
    (P : Polynomial (q.comap (algebraMap R (R[X] ⧸ I))).ResidueField) (hP : P ≠ 0)
    (hrel : (Polynomial.aeval (QF.toB (R := R) q (Ideal.Quotient.mk I X))) P = 0) :
    ∃ f : R[X], f ∈ I ∧ ∃ j : ℕ, algebraMap R (R[X] ⧸ I) (f.coeff j) ∉ q := by
  by_contra hcon
  push Not at hcon
  set Sr := R[X] ⧸ I with hSr
  set p := q.comap (algebraMap R Sr) with hp
  have hpprime : p.IsPrime := Ideal.IsPrime.comap _
  have hH : ∀ f ∈ I, ∀ j, f.coeff j ∈ p := fun f hf j => hcon f hf j
  -- KEY: all coeffs of g in p ⟹ mk I g ∈ q
  have keymem : ∀ g : R[X], (∀ j, g.coeff j ∈ p) → Ideal.Quotient.mk I g ∈ q := by
    intro g hg
    rw [mk_eq_aeval_mk_X, aeval_eq_sum_range]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_comap.mp (hg j))
  let : IsDomain ((R ⧸ p)[X]) := by infer_instance
  let F := FractionRing ((R ⧸ p)[X])
  -- ψ : Sr → (R/p)[X]
  let φ : R[X] →+* (R ⧸ p)[X] := Polynomial.mapRingHom (Ideal.Quotient.mk p)
  have hker : I ≤ RingHom.ker φ := by
    intro f hf
    rw [RingHom.mem_ker]
    change (mapRingHom (Ideal.Quotient.mk p)) f = 0
    rw [Polynomial.coe_mapRingHom]; ext n
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hH f hf n)
  let ψ : Sr →+* (R ⧸ p)[X] := Ideal.Quotient.lift I φ (fun a ha => by
    rw [← RingHom.mem_ker]; exact hker ha)
  have hψmk : ∀ g : R[X], ψ (Ideal.Quotient.mk I g) = φ g := fun g => Ideal.Quotient.lift_mk I φ _
  -- ψ on algebraMap R Sr
  have hψalg : ∀ r : R, ψ (algebraMap R Sr r) = C (Ideal.Quotient.mk p r) := by
    intro r
    have he : algebraMap R Sr r = Ideal.Quotient.mk I (C r) := by
      change (algebraMap R (R[X] ⧸ I)) r = Ideal.Quotient.mk I (C r)
      rw [IsScalarTower.algebraMap_apply R (R[X]) (R[X] ⧸ I) r, Ideal.Quotient.algebraMap_eq]
      congr 1
    rw [he, hψmk (C r)]
    change (mapRingHom (Ideal.Quotient.mk p)) (C r) = C (Ideal.Quotient.mk p r)
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C]
  have hψp : ∀ r ∈ p, ψ (algebraMap R Sr r) = 0 := by
    intro r hr
    rw [hψalg r, show (Ideal.Quotient.mk p r) = 0 from (Ideal.Quotient.eq_zero_iff_mem).mpr hr,
        map_zero]
  let ψF : Sr →+* F := (algebraMap ((R ⧸ p)[X]) F).comp ψ
  have hunit : ∀ s : q.primeCompl, IsUnit (ψF (s : Sr)) := by
    intro s
    rw [isUnit_iff_ne_zero]
    intro hzero
    apply s.property
    have hψs : ψ (s : Sr) = 0 := by
      have hinj := IsFractionRing.injective ((R ⧸ p)[X]) F
      apply hinj; rw [map_zero]; exact hzero
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (s : Sr)
    rw [← hg] at hψs ⊢
    rw [hψmk g] at hψs
    have hcoeff : ∀ n, g.coeff n ∈ p := by
      intro n
      have := congrArg (fun (t : (R ⧸ p)[X]) => t.coeff n) hψs
      simp only [φ, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero] at this
      exact (Ideal.Quotient.eq_zero_iff_mem).mp this
    exact keymem g hcoeff
  let Λ : Localization.AtPrime q →+* F := IsLocalization.lift (M := q.primeCompl) hunit
  have hΛmk : ∀ y : Sr, Λ (algebraMap Sr (Localization.AtPrime q) y) = ψF y :=
    fun y => IsLocalization.lift_eq hunit y
  have hkill : Ideal.map (algebraMap R (Localization.AtPrime q)) p ≤ RingHom.ker Λ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    rw [IsScalarTower.algebraMap_apply R Sr (Localization.AtPrime q) r, hΛmk]
    change (algebraMap ((R ⧸ p)[X]) F).comp ψ (algebraMap R Sr r) = 0
    rw [RingHom.comp_apply, hψp r hr, map_zero]
  let Φ : QF.B (R := R) q →+* F :=
    Ideal.Quotient.lift _ Λ (fun a ha => by rw [← RingHom.mem_ker]; exact hkill ha)
  -- Φ on QF.toB
  have hΦtoB : ∀ s : Sr, Φ (QF.toB (R := R) q s) = ψF s := by
    intro s
    change Ideal.Quotient.lift _ Λ _ (Ideal.Quotient.mk _ (algebraMap Sr (Localization.AtPrime q)
        s)) = ψF s
    rw [Ideal.Quotient.lift_mk, hΛmk]
  -- ξ = Φ β
  let β := QF.toB (R := R) q (Ideal.Quotient.mk I X)
  have hβξ : Φ β = algebraMap ((R ⧸ p)[X]) F (X) := by
    change Φ (QF.toB (R := R) q (Ideal.Quotient.mk I X)) = _
    rw [hΦtoB]
    change (algebraMap ((R ⧸ p)[X]) F).comp ψ (Ideal.Quotient.mk I X) = _
    rw [RingHom.comp_apply, hψmk X]
    change algebraMap ((R ⧸ p)[X]) F ((mapRingHom (Ideal.Quotient.mk p)) X) = _
    rw [Polynomial.coe_mapRingHom, Polynomial.map_X]
  -- equip F with κ(p)-algebra structure τ.toAlgebra where τ = Φ ∘ kappaMap
  let algF : Algebra p.ResidueField F := (Φ.comp (QF.kappaMap q)).toAlgebra
  have hτalg : (algebraMap p.ResidueField F) = Φ.comp (QF.kappaMap q) := rfl
  have hτinj : Function.Injective (algebraMap p.ResidueField F) :=
    (algebraMap p.ResidueField F).injective
  -- IsScalarTower (R⧸p) κ(p) F
  have : IsScalarTower (R ⧸ p) p.ResidueField F := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hL : algebraMap (R ⧸ p) F (Ideal.Quotient.mk p r)
        = algebraMap ((R ⧸ p)[X]) F (C (Ideal.Quotient.mk p r)) := by
      rw [IsScalarTower.algebraMap_apply (R ⧸ p) ((R ⧸ p)[X]) F (Ideal.Quotient.mk p r)]
      congr 1
    have hRmid : algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r)
        = algebraMap R p.ResidueField r := by
      rw [show (Ideal.Quotient.mk p r) = algebraMap R (R ⧸ p) r from rfl,
        ← IsScalarTower.algebraMap_apply]
    rw [hL, hRmid, hτalg, RingHom.comp_apply, QF.kappaMap_algebraMap q r, hΦtoB]
    change _ = (algebraMap ((R ⧸ p)[X]) F).comp ψ (algebraMap R Sr r)
    rw [RingHom.comp_apply, hψalg r]
  -- Transcendental over R⧸p, then over κ(p)
  have htrans_base : Transcendental (R ⧸ p) (algebraMap ((R ⧸ p)[X]) F X) := by
    rw [transcendental_algebraMap_iff (IsFractionRing.injective ((R ⧸ p)[X]) F)]
    exact transcendental_X (R ⧸ p)
  have htrans : Transcendental p.ResidueField (algebraMap ((R ⧸ p)[X]) F X) :=
    htrans_base.extendScalars p.ResidueField
  -- Φ (aeval β P) = aeval ξ P = 0 ⟹ P = 0, contradiction with hP
  rw [transcendental_iff] at htrans
  apply hP
  apply htrans
  have hcompute : (Polynomial.aeval (algebraMap ((R ⧸ p)[X]) F X)) P = Φ ((Polynomial.aeval β)
      P) := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
    rw [← hβξ]
    congr 1
  rw [hcompute, hrel, map_zero]

/-- Quasi-finiteness at `q` forces some `f ∈ I` to have a coefficient outside
`p = q.comap (algebraMap R S)`, i.e. with `algebraMap R S (f.coeff j) ∉ q`. -/
theorem relation_from_quasiFinite (R : Type*) [CommRing R] (I : Ideal (R[X]))
    (q : Ideal (R[X] ⧸ I)) [q.IsPrime] (hqf : QuasiFiniteAt (R := R) q) :
    ∃ f : R[X], f ∈ I ∧ ∃ j : ℕ, algebraMap R (R[X] ⧸ I) (f.coeff j) ∉ q := by
  -- quasi-finiteness ⇒ a nonzero κ(p)[X]-relation on β = image of x in B q.
  obtain ⟨P, hP, hrel⟩ :=
    relation_polynomial_of_quasiFinite (R := R) q hqf (Ideal.Quotient.mk I X)
  -- descend that relation to an honest f ∈ I with a coefficient outside p.
  exact relation_descends_to_R R I q P hP hrel

/-- Downward induction producing a good `g` (Stacks tag 00PQ plus induction). Given
a relation `∑_{j ≤ m} (b j) x^j = 0` in `S` with all `b j ∈ S' = integralClosure R S`
and some `(b j : S) ∉ q`, there is `g ∈ S'`, `g ∉ q`, with `(g : S) * x ∈ S'`.

The argument is an induction on `m`.
* `m = 0`: the relation reads `(b 0 : S) = 0`, so `b 0 ∈ q` (as `0 ∈ q`), contradicting the
  witness (whose only possible index is `0`).
* `m+1`: form the polynomial `P : S'[X]` with `P.coeff j = b j` for `j ≤ m+1`, so that
  `eval₂ (Subalgebra.val S') x P = ∑_{j ≤ m+1} (b j) x^j = 0`.  Apply
  `RingHom.isIntegralElem_leadingCoeff_mul (Subalgebra.val S') P x` to get that
  `(b (m+1) : S) * x` is integral over `S'`; by `isIntegral_trans` (S' integral over R) it is
  integral over `R`, i.e. `(b (m+1) : S) * x ∈ S'`.  Let `c := ⟨(b (m+1):S)*x, …⟩ ∈ S'`.
  - If `(b (m+1) : S) ∉ q`: take `g = b (m+1)`; `(g:S)*x = (c:S) ∈ S'`.  Done.
  - If `(b (m+1) : S) ∈ q`: set `b' : ℕ → S'` by `b' m := c + b m` and `b' j := b j` for
    `j ≠ m`.  Then `∑_{j ≤ m} (b' j) x^j = ∑_{j ≤ m+1} (b j) x^j = 0` (since
    `(b' m) x^m = (b (m+1) x) x^m + b m x^m = b (m+1) x^{m+1} + b m x^m`).  The witness
    `(b j : S) ∉ q` has index `j ≤ m` (index `m+1` is excluded by the case assumption); if
    `j < m` it is unchanged, and if `j = m` then `(b' m : S) = b (m+1) x + b m ≡ b m (mod q)`
    (because `b (m+1) ∈ q` ⇒ `b (m+1) x ∈ q`), so `(b' m : S) ∉ q`.  Recurse with `m`. -/
theorem good_g_from_relation (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (x : S) (q : Ideal S) [q.IsPrime]
    (m : ℕ) (b : ℕ → integralClosure R S)
    (hrel : ∑ j ∈ Finset.range (m + 1), ((b j : S)) * x ^ j = 0)
    (hne : ∃ j ≤ m, (b j : S) ∉ q) :
    ∃ g : integralClosure R S, (g : S) ∉ q ∧ (g : S) * x ∈ integralClosure R S := by
  induction m generalizing b with
  | zero =>
    exfalso
    obtain ⟨j, hjle, hjq⟩ := hne
    have hj0 : j = 0 := Nat.le_zero.mp hjle
    subst hj0
    rw [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
      mul_one] at hrel
    exact hjq (hrel ▸ Ideal.zero_mem q)
  | succ m ih =>
    -- central integrality: (b (m+1) : S) * x ∈ integralClosure R S
    have hc : (b (m+1) : S) * x ∈ integralClosure R S := by
      by_cases hbm : (b (m+1)) = 0
      · simp only [hbm, ZeroMemClass.coe_zero, zero_mul]
        exact Subalgebra.zero_mem _
      · set P : Polynomial (integralClosure R S) :=
          ∑ j ∈ Finset.range (m+1+1), Polynomial.C (b j) * Polynomial.X ^ j with hP
        have hev : Polynomial.eval₂ ((integralClosure R S).val : (integralClosure R S) →+* S) x P
            = 0 := by
          rw [hP, Polynomial.eval₂_finsetSum, ← hrel]
          apply Finset.sum_congr rfl
          intro j _
          rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]; rfl
        have hcoeff : ∀ j, j ≤ m+1 → P.coeff j = b j := by
          intro j hj
          rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
          · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]; simp
          · intro i _ hij; rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]; simp [Ne.symm hij]
          · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) h
        have hdeg : P.natDegree = m+1 := by
          have hd : P.natDegree ≤ m+1 := by
            rw [hP]
            apply Polynomial.natDegree_sum_le_of_forall_le
            intro i hi
            calc (Polynomial.C (b i) * Polynomial.X ^ i).natDegree
                ≤ i := by
                  apply le_trans (Polynomial.natDegree_mul_le)
                  simp only [Polynomial.natDegree_C, zero_add]
                  exact Polynomial.natDegree_X_pow_le i
              _ ≤ m+1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          exact le_antisymm hd (Polynomial.le_natDegree_of_ne_zero (by rwa [hcoeff (m+1) le_rfl]))
        have hlead : P.leadingCoeff = b (m+1) := by
          rw [Polynomial.leadingCoeff, hdeg, hcoeff (m+1) le_rfl]
        have hint := RingHom.isIntegralElem_leadingCoeff_mul
          ((integralClosure R S).val : (integralClosure R S) →+* S) P x hev
        rw [hlead] at hint
        have : Algebra.IsIntegral R (integralClosure R S) := inferInstance
        have hS' : IsIntegral (integralClosure R S) ((integralClosure R S).val (b (m+1)) * x) :=
          hint
        rw [mem_integralClosure_iff]
        exact isIntegral_trans _ hS'
    by_cases hbmq : (b (m+1) : S) ∈ q
    · -- reduce
      set c : integralClosure R S := ⟨(b (m+1) : S) * x, hc⟩
      have hcval : (c : S) = (b (m+1) : S) * x := rfl
      set b' : ℕ → integralClosure R S := fun j => if j = m then c + b m else b j with hb'
      have hrel' : ∑ j ∈ Finset.range (m + 1), ((b' j : S)) * x ^ j = 0 := by
        rw [Finset.sum_range_succ] at hrel ⊢
        have hlow : ∀ j ∈ Finset.range m, (b' j : S) * x^j = (b j : S) * x^j := by
          intro j hj
          simp only [Finset.mem_range] at hj
          rw [hb']; simp only; rw [ite_eq_right (Nat.ne_of_lt hj)]
        rw [Finset.sum_congr rfl hlow]
        have hbm' : (b' m : S) = (b (m+1) : S) * x + (b m : S) := by
          rw [hb']; simp only [ite_eq_left]; push_cast; rw [hcval]
        rw [hbm']
        rw [Finset.sum_range_succ] at hrel
        linear_combination hrel
      have hne' : ∃ j ≤ m, (b' j : S) ∉ q := by
        obtain ⟨j, hjle, hjq⟩ := hne
        have hcq : (c : S) ∈ q := by rw [hcval]; exact Ideal.mul_mem_right _ _ hbmq
        have hjne : j ≠ m + 1 := by intro h; rw [h] at hjq; exact hjq hbmq
        have hjm : j ≤ m := by omega
        refine ⟨j, hjm, ?_⟩
        by_cases hjeq : j = m
        · subst hjeq
          rw [hb']; simp only [ite_eq_left]; push_cast
          intro hmem
          apply hjq
          have := Ideal.sub_mem q hmem hcq
          simpa using this
        · rw [hb']; simp only; rw [ite_eq_right hjeq]; exact hjq
      exact ih b' hrel' hne'
    · exact ⟨b (m+1), hbmq, hc⟩

/-- A good `g` makes `QF.locMap g` bijective: if `g ∈ S'`, `(g:S) ∉ q`, and
`(g:S) * x ∈ S'`, with `S` generated as an `R`-algebra by `x`, then `QF.locMap g` is
bijective.

* *Injectivity*: `Subalgebra.val (integralClosure R S)` is injective (`Subtype.val_injective`),
  and `QF.locMap g` is `IsLocalization.map` along it, so
  `IsLocalization.map_injective_of_injective` applies — provided the target
  `Localization.Away (val g)` is the localization at `Submonoid.map val (Submonoid.powers g)`,
  which holds by `Submonoid.map_powers`.
* *Surjectivity*: every `z : Localization.Away (val g)` is `IsLocalization.mk' _ s ⟨(val g)^n, _⟩`
  with `s : S`, `n : ℕ` (`IsLocalization.mk'_surjective` / `IsLocalization.surj` on
  `Submonoid.powers (val g)`).  The range of `QF.locMap g` is a subring `T`; it contains
  `IsLocalization.Away.invSelf (val g)` (image of `invSelf g`) and `algebraMap S _ s` for all
  `s ∈ S'`.  Show `algebraMap S _ x ∈ T`: since `(g:S)*x ∈ S'`, `algebraMap S _ ((g:S)*x) ∈ T`,
  and `algebraMap S _ x = algebraMap S _ ((g:S)*x) * invSelf (val g)` (clear denominator using
  `IsLocalization.Away.mul_invSelf`), so `x ∈ T`.  As `T` contains `algebraMap` of `R` and of
  `x`, and `Algebra.adjoin R {x} = ⊤`, `T` contains `algebraMap S _ s` for every `s : S`
  (`Algebra.adjoin_induction` on `hgen`).  Combined with `invSelf ∈ T`, `T` contains every
  `mk' s ⟨(val g)^n,_⟩`, i.e. `T = ⊤`.  Hence surjective.  Bijective = injective ∧ surjective. -/
theorem locMap_bijective_of_good_g (R : Type*) [CommRing R] {S : Type*} [CommRing S]
    [Algebra R S] (x : S) (q : Ideal S) [q.IsPrime]
    (hgen : Algebra.adjoin R {x} = ⊤)
    (g : integralClosure R S) (hgx : (g : S) * x ∈ integralClosure R S) :
    Function.Bijective (QF.locMap g) := by
  refine ⟨?_, ?_⟩
  · -- Injectivity
    unfold QF.locMap
    have hval : Function.Injective ((integralClosure R S).val : (integralClosure R S) →+* S) :=
      Subtype.val_injective
    have : IsLocalization (Submonoid.map ((integralClosure R S).val : (integralClosure R S) →+* S)
        (Submonoid.powers g)) (Localization.Away ((integralClosure R S).val g)) := by
      rw [Submonoid.map_powers]
      exact Localization.isLocalization
    exact IsLocalization.map_injective_of_injective (Submonoid.powers g) (Localization.Away g)
      (Localization.Away ((integralClosure R S).val g)) hval
  · -- Surjectivity
    set T := (QF.locMap g).range with hT
    have hS' : ∀ s' : integralClosure R S,
        algebraMap S (Localization.Away ((integralClosure R S).val g)) ((integralClosure R S).val
            s') ∈ T := by
      intro s'
      refine ⟨algebraMap (integralClosure R S) (Localization.Away g) s', ?_⟩
      change QF.locMap g _ = _
      unfold QF.locMap
      rw [IsLocalization.map_eq]
      rfl
    have hinv : IsLocalization.Away.invSelf (S := Localization.Away ((integralClosure R S).val g))
        ((integralClosure R S).val g) ∈ T := by
      refine ⟨IsLocalization.Away.invSelf (S := Localization.Away g) g, ?_⟩
      change QF.locMap g _ = _
      unfold QF.locMap IsLocalization.Away.invSelf
      rw [IsLocalization.map_mk']
      simp
    have hx : algebraMap S (Localization.Away ((integralClosure R S).val g)) x ∈ T := by
      have hxeq : algebraMap S (Localization.Away ((integralClosure R S).val g)) x
          = algebraMap S (Localization.Away ((integralClosure R S).val g)) (((integralClosure R
              S).val g) * x)
            * IsLocalization.Away.invSelf (S := Localization.Away ((integralClosure R S).val g))
                ((integralClosure R S).val g) := by
        rw [map_mul, mul_assoc, mul_comm (algebraMap S (Localization.Away ((integralClosure R
            S).val g)) x),
          ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
      rw [hxeq]
      refine Subring.mul_mem _ ?_ hinv
      have heq : ((integralClosure R S).val g) * x
          = (integralClosure R S).val ⟨((integralClosure R S).val g) * x, hgx⟩ := rfl
      rw [heq]
      exact hS' _
    have hall : ∀ s : S, algebraMap S (Localization.Away ((integralClosure R S).val g)) s ∈ T := by
      intro s
      have hmem : s ∈ Algebra.adjoin R {x} := hgen ▸ Algebra.mem_top
      induction hmem using Algebra.adjoin_induction with
      | mem y hy => rw [Set.mem_singleton_iff] at hy; subst hy; exact hx
      | algebraMap r => exact hS' ⟨algebraMap R S r, (integralClosure R S).algebraMap_mem r⟩
      | add a b _ _ ha hb => rw [map_add]; exact Subring.add_mem _ ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact Subring.mul_mem _ ha hb
    intro z
    obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hsurj⟩ :=
      IsLocalization.surj (Submonoid.powers ((integralClosure R S).val g)) z
    simp only at hsurj
    have hzeq : z = algebraMap S (Localization.Away ((integralClosure R S).val g)) s
        * (IsLocalization.Away.invSelf (S := Localization.Away ((integralClosure R S).val g))
            ((integralClosure R S).val g))^n := by
      have hu : algebraMap S (Localization.Away ((integralClosure R S).val g)) (((integralClosure R
          S).val g)^n)
          * (IsLocalization.Away.invSelf (S := Localization.Away ((integralClosure R S).val g))
              ((integralClosure R S).val g))^n = 1 := by
        rw [map_pow, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
      rw [← hsurj, mul_assoc, hu, mul_one]
    rw [hzeq]
    exact Subring.mul_mem _ (hall s) (Subring.pow_mem _ hinv n)

/-- Stacks tag 00Q8 (Lemma 10.123.11). For `S = R[X]/I` monogenic over `R` and a
prime `q ⊂ S` at which `R → S` is quasi-finite, there is an element `g` of the
integral closure `S'` of `R` in `S` with `g ∉ q` such that the induced map
`S'_g → S_g` is an isomorphism. -/
@[stacks 00Q8]
theorem main_theorem_00q8 (R : Type*) [CommRing R] (I : Ideal (R[X]))
    (q : Ideal (R[X] ⧸ I)) [q.IsPrime]
    (hqf : QuasiFiniteAt (R := R) q) :
    ∃ g : integralClosure R (R[X] ⧸ I), (g : R[X] ⧸ I) ∉ q ∧
      Function.Bijective (QF.locMap (R := R) g) := by
  -- Notation: `x = mk I X`, `S = R[X]/I`.
  -- The quotient map equals `aeval x` (both are `R`-algebra homs sending `X ↦ x`).
  -- The generator `x` generates `S` as an `R`-algebra.
  have hgen : Algebra.adjoin R {(Ideal.Quotient.mk I X : R[X] ⧸ I)} = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mk_eq_aeval_mk_X p]
    exact Polynomial.aeval_mem_adjoin_singleton R _ (p := p)
  -- The image of any `r : R` is integral over `R`, i.e. lies in `S'`.
  have hRint : ∀ r : R, algebraMap R (R[X] ⧸ I) r ∈ integralClosure R (R[X] ⧸ I) := fun r =>
    (integralClosure R (R[X] ⧸ I)).algebraMap_mem r
  -- a relation from quasi-finiteness
  obtain ⟨f, hfI, j0, hj0⟩ := relation_from_quasiFinite R I q hqf
  -- Package `f`'s coefficients (mapped into `S`, lifted into `S'`) as `b : ℕ → S'`.
  set b : ℕ → integralClosure R (R[X] ⧸ I) :=
    fun j => ⟨algebraMap R (R[X] ⧸ I) (f.coeff j), hRint _⟩ with hb
  -- The relation `∑_{j ≤ natDegree f} b_j x^j = 0` since `aeval x f = 0` for `f ∈ I`.
  have hrel : ∑ j ∈ Finset.range (f.natDegree + 1),
      ((b j : R[X] ⧸ I)) * (Ideal.Quotient.mk I X) ^ j = 0 := by
    have haeval : (Polynomial.aeval (Ideal.Quotient.mk I X : R[X] ⧸ I)) f = 0 :=
      (mk_eq_aeval_mk_X f).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hfI)
    rw [← haeval, aeval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [Algebra.smul_def]
  -- The witness index `j0` satisfies `j0 ≤ natDegree f` (else coeff = 0 ∈ q).
  have hj0le : j0 ≤ f.natDegree := by
    by_contra h
    rw [not_le] at h
    exact hj0 (by rw [f.coeff_eq_zero_of_natDegree_lt h]; simp)
  have hne : ∃ j ≤ f.natDegree, (b j : R[X] ⧸ I) ∉ q := ⟨j0, hj0le, hj0⟩
  -- downward induction yields a good `g`
  obtain ⟨g, hgq, hgx⟩ :=
    good_g_from_relation R (Ideal.Quotient.mk I X) q f.natDegree b hrel hne
  -- this `g` makes `QF.locMap g` bijective
  exact ⟨g, hgq, locMap_bijective_of_good_g R (Ideal.Quotient.mk I X) q hgen g hgx⟩

end
