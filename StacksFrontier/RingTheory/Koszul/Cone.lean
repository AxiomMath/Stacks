module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public meta import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Koszul.Defs
public import StacksFrontier.LinearAlgebra.ExteriorAlgebra.Prod

/-!
# The Koszul complex of `phi'` as a cone

Let `R` be a commutative ring, `phi : E → R` an `R`-linear map (an element of `Module.Dual R E`)
and `f ∈ R`. Let `E' = E ⊕ R` and `phi' : E' → R`, `phi'(e, r) = phi(e) + f r`. Then the Koszul
complex `K(phi')` is isomorphic to the cone `C(f)` of multiplication by `f` on `K(phi)`, by the
isomorphism `Θ` with components `Θₙ : C(f)ₙ → Kₙ(phi')` given on the two summands by
`Θₙ(e₁ ∧ ⋯ ∧ eₙ, 0) = e₁ ∧ ⋯ ∧ eₙ` and `Θₙ(0, e₁ ∧ ⋯ ∧ e_{n-1}) = e₀ ∧ e₁ ∧ ⋯ ∧ e_{n-1}`,
where `e₀ = (0, 1) ∈ E ⊕ R`.

## Main definitions

* `Stacks.MappingCone.NatIndexed.coneComplex`: the cone `C(g)` of a chain map `g : A ⟶ B`, with
  `C(g)₀ = B₀`, `C(g)_{n+1} = B_{n+1} ⊕ Aₙ` and differential `(b, a) ↦ (d_B b + g a, - d_A a)`.
* `Stacks.MappingCone.NatIndexed.mulByF`: multiplication by `f` on a chain complex.
* `Stacks.MappingCone.NatIndexed.phiPrime`: the functional `phi'` on `E × R`.

## Main results

* `Stacks.MappingCone.NatIndexed.koszulComplex_phiPrime_iso_cone`: `C(f) ≅ K(phi')`, with the
  prescribed components `Θₙ`.
* `Koszul.seqComplex_snoc_iso_cone`: the Koszul complex of `Fin.snoc f a` is isomorphic to the
  cone of multiplication by `a` on the Koszul complex of `f`.

## Implementation notes

The Koszul differential is the contraction `CliffordAlgebra.contractLeft phi` on
`ExteriorAlgebra R E`, the Clifford algebra of the zero quadratic form; the graded differential
and the Koszul complex are `Koszul.d` and `Koszul.complex`.

Chain complexes are `ChainComplex (ModuleCat R) ℕ`. With `ℕ`-indexing, `A_{-1} = 0`, so the cone
satisfies `C(g)₀ = B₀` and `C(g)_{n+1} = B_{n+1} ⊕ Aₙ`. The cone agrees with
`HomologicalComplex.homotopyCofiber g` up to the order of the two summands: here the target
summand comes first, as in the prescribed components of `Θ`.

## References

* [Stacks Project, Tag 0627](https://stacks.math.columbia.edu/tag/0627)
* [Stacks Project, Tag 0628](https://stacks.math.columbia.edu/tag/0628)
* [Stacks Project, Tag 0629](https://stacks.math.columbia.edu/tag/0629)
-/

@[expose] public section

-- The cone objects `coneX` are `ModuleCat.of R (B.X (n+1) × A.X n)`, so recognizing an
-- element of `coneX … (n+1)` as a pair requires unfolding `coneX` and `ModuleCat.of`;
-- the `rw`/`simpa` steps in the `thetaLin` bijectivity proofs rely on that unfolding.
set_option backward.isDefEq.respectTransparency false

open scoped ExteriorAlgebra
open CategoryTheory

namespace Stacks.MappingCone.NatIndexed

universe u v w

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-! ## The cone of a chain map

The cone of a chain map `g : A ⟶ B` between two `ℕ`-indexed chain complexes has objects
`C(g)₀ = B₀` and `C(g)_{n+1} = B_{n+1} ⊕ Aₙ`, and differential the matrix
`((d_B, g), (0, -d_A))`. -/

section Cone

variable (A B : ChainComplex (ModuleCat.{w} R) ℕ) (g : A ⟶ B)

/-- Objects of the cone complex: `C(g)₀ = B₀`, `C(g)_{n+1} = B_{n+1} ⊕ Aₙ`. -/
noncomputable def coneX : ℕ → ModuleCat.{w} R
  | 0 => B.X 0
  | (n+1) => ModuleCat.of R (B.X (n+1) × A.X n)

/-- The cone differential in degree `0`: `(b, a) ↦ d_B b + g a`. -/
noncomputable def coneD0lin : (B.X 1 × A.X 0) →ₗ[R] B.X 0 :=
  (B.d 1 0).hom.comp (LinearMap.fst R (B.X 1) (A.X 0)) +
  (g.f 0).hom.comp (LinearMap.snd R (B.X 1) (A.X 0))

/-- The cone differential in degree `n+1`: `(b, a) ↦ (d_B b + g a, - d_A a)`. -/
noncomputable def coneDSlin (n : ℕ) :
    (B.X (n+2) × A.X (n+1)) →ₗ[R] (B.X (n+1) × A.X n) :=
  LinearMap.prod
    ((B.d (n+2) (n+1)).hom.comp (LinearMap.fst R (B.X (n+2)) (A.X (n+1))) +
     (g.f (n+1)).hom.comp (LinearMap.snd R (B.X (n+2)) (A.X (n+1))))
    (-((A.d (n+1) n).hom.comp (LinearMap.snd R (B.X (n+2)) (A.X (n+1)))))

/-- The cone differential as a morphism `C(g)_{n+1} ⟶ C(g)ₙ`. -/
noncomputable def coneD : (n : ℕ) → (coneX A B (n+1) ⟶ coneX A B n)
  | 0 => ModuleCat.ofHom (coneD0lin A B g)
  | (n+1) => ModuleCat.ofHom (coneDSlin A B g n)

private theorem dB_dB (i j k : ℕ) (x) : (B.d j k).hom ((B.d i j).hom x) = 0 := by
  rw [← ModuleCat.comp_apply, B.d_comp_d i j k]; rfl

private theorem dA_dA (i j k : ℕ) (x) : (A.d j k).hom ((A.d i j).hom x) = 0 := by
  rw [← ModuleCat.comp_apply, A.d_comp_d i j k]; rfl

private theorem gcomm (i j : ℕ) (x) :
    (B.d i j).hom ((g.f i).hom x) = (g.f j).hom ((A.d i j).hom x) := by
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, g.comm i j]

/-- The cone differential squares to zero. -/
theorem coneD_comp (n : ℕ) : coneD A B g (n+1) ≫ coneD A B g n = 0 := by
  ext x
  cases n with
  | zero =>
    obtain ⟨b, a⟩ := x
    change coneD0lin A B g (coneDSlin A B g 0 (b, a)) = 0
    simp only [coneD0lin, coneDSlin, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.prod_apply, Function.prod_apply,
      LinearMap.neg_apply, map_add, map_neg]
    rw [gcomm A B g 1 0, dB_dB B 2 1 0]
    abel
  | succ m =>
    obtain ⟨b, a⟩ := x
    change coneDSlin A B g m (coneDSlin A B g (m+1) (b, a)) = 0
    simp only [coneDSlin, LinearMap.prod_apply, Function.prod_apply, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.neg_apply, map_add, map_neg, Prod.mk_eq_zero]
    refine ⟨?_, ?_⟩
    · rw [gcomm A B g (m+2) (m+1), dB_dB B (m+1+2) (m+2) (m+1)]
      abel
    · rw [dA_dA A (m+1+1) (m+1) m]
      abel

/-- The cone `C(g)` of a chain map `g : A ⟶ B`, as a chain complex. -/
noncomputable def coneComplex : ChainComplex (ModuleCat.{w} R) ℕ :=
  ChainComplex.of (coneX A B) (coneD A B g) (coneD_comp A B g)

end Cone

/-! ## Multiplication by `f`, and the functional `phi'` on `E' = E ⊕ R` -/

/-- Multiplication by `f ∈ R` on a chain complex, as a chain map (`f • 𝟙`).  Its
component in each degree `n` is `a ↦ f • a`. -/
noncomputable def mulByF (K : ChainComplex (ModuleCat.{w} R) ℕ) (f : R) : K ⟶ K :=
  f • 𝟙 K

/-- In degree `n`, `mulByF K f` acts by `x ↦ f • x`. -/
@[simp] theorem mulByF_f (K : ChainComplex (ModuleCat.{w} R) ℕ) (f : R) (n : ℕ) (x : K.X n) :
    (mulByF K f).f n x = f • x := rfl

/-- The dual map `phi' : E ⊕ R → R`, `phi'(e, r) = phi(e) + f • r`. -/
noncomputable def phiPrime (φ : Module.Dual R E) (f : R) : Module.Dual R (E × R) :=
  φ.comp (LinearMap.fst R E R) + f • (LinearMap.snd R E R)

/-- The value of `phiPrime φ f` at `(e, r)` is `φ e + f * r`. -/
@[simp] theorem phiPrime_apply (φ : Module.Dual R E) (f : R) (e : E) (r : R) :
    phiPrime φ f (e, r) = φ e + f * r := by
  simp [phiPrime]

/-! ## The degreewise comparison maps `Θₙ`

The components `Θₙ : C(f)ₙ → Kₙ(phi')` are made of two maps into `⋀ⁿ E' = ⋀ⁿ(E ⊕ R)`:

* the inclusion `inclPow` induced by `E ↪ E' = E ⊕ R`, on the first summand `⋀ⁿ E`, and
* `wedgeE0Pow`, wedging with `e₀ = (0,1)`: `x ↦ e₀ ∧ x`, on the second summand `⋀^{n-1} E`. -/

/-- The algebra inclusion `⋀ E → ⋀ E'` induced by `E ↪ E' = E ⊕ R`. -/
noncomputable def inclAlg : ExteriorAlgebra R E →ₐ[R] ExteriorAlgebra R (E × R) :=
  ExteriorAlgebra.map (LinearMap.inl R E R)

/-- `inclAlg` sends the generator `ι e` to `ι (e, 0)`. -/
@[simp] theorem inclAlg_ι (e : E) :
    inclAlg (E := E) (ExteriorAlgebra.ι R e) = ExteriorAlgebra.ι R ((e, 0) : E × R) := by
  rw [inclAlg, ExteriorAlgebra.map_apply_ι]; rfl

/-- `Θ` on the first summand: the degree-`n` restriction `⋀ⁿ E → ⋀ⁿ E'` of `inclAlg`. -/
noncomputable def inclPow (n : ℕ) : (⋀[R]^n E) →ₗ[R] (⋀[R]^n (E × R)) :=
  ((inclAlg (E := E)).toLinearMap.domRestrict (⋀[R]^n E)).codRestrict
    (⋀[R]^n (E × R)) fun x => by
      have h := (exteriorPower.map n (LinearMap.inl R E R) x).2
      rwa [exteriorPower.coe_map] at h

/-- The underlying element of `inclPow n x` in `⋀ E'` is `inclAlg x`. -/
@[simp] theorem inclPow_coe (n : ℕ) (x : ⋀[R]^n E) :
    (inclPow n x : ExteriorAlgebra R (E × R)) = inclAlg (E := E) x := rfl

/-- The element `e₀ = (0, 1) ∈ E ⊕ R`, regarded inside `⋀¹ E'`. -/
noncomputable def e0 : ExteriorAlgebra R (E × R) := ExteriorAlgebra.ι R ((0, 1) : E × R)

/-- `⋀^{n+1} E'` is spanned by products of a generator with an element of `⋀ⁿ E'`. -/
private theorem exteriorPower_succ_eq_range_mul (n : ℕ) :
    ⋀[R]^(n+1) (E × R) = (ExteriorAlgebra.ι R).range * ⋀[R]^n (E × R) := pow_succ' _ _

/-- Wedging with `e₀` raises exterior degree by one: it maps `⋀^{n} E` (included into
`⋀ⁿ E'`) into `⋀^{n+1} E'`. -/
theorem e0_wedge_grade (n : ℕ) :
    (⋀[R]^n (E × R)).map ((LinearMap.mulLeft R (e0 (R := R) (E := E)))) ≤
      ⋀[R]^(n+1) (E × R) := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap]
  change e0 (R := R) (E := E) * x ∈ _
  rw [exteriorPower_succ_eq_range_mul]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) hx

/-- `Θ` on the second summand: the map `⋀^{n-1} E → ⋀ⁿ E'`, `x ↦ e₀ ∧ (incl x)`. -/
noncomputable def wedgeE0Pow (n : ℕ) : (⋀[R]^(n-1) E) →ₗ[R] (⋀[R]^n (E × R)) :=
  match n with
  | 0 => 0
  | (m+1) =>
    (((LinearMap.mulLeft R (e0 (R := R) (E := E))).domRestrict
        (⋀[R]^m (E × R))).codRestrict
        (⋀[R]^(m+1) (E × R))
        (fun x => e0_wedge_grade m (Submodule.mem_map_of_mem x.2))).comp (inclPow m)

/-- In degree `m + 1`, `wedgeE0Pow` sends `x` to `e₀ * x` in `⋀ E'`. -/
theorem wedgeE0Pow_succ_coe (m : ℕ) (x : ⋀[R]^m E) :
    (wedgeE0Pow (m+1) x : ExteriorAlgebra R (E × R))
      = e0 (R := R) (E := E) * inclAlg (E := E) x := rfl

/-! ## Projection and contraction by the `R`-coordinate -/

/-- Involution-graded Leibniz rule for the Koszul contraction. -/
theorem contraction_leibniz {F : Type*} [AddCommGroup F] [Module R F]
    (φ : Module.Dual R F) (x : ExteriorAlgebra R F) :
    ∀ y : ExteriorAlgebra R F,
      Koszul.contraction φ (x * y)
        = Koszul.contraction φ x * y + CliffordAlgebra.involute x * Koszul.contraction φ y := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    intro y
    rw [CliffordAlgebra.contractLeft_algebraMap, zero_mul, zero_add,
      AlgHom.commutes, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  | ι v =>
    intro y
    rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι,
      CliffordAlgebra.involute_ι, ← Algebra.smul_def, neg_mul]
    abel
  | mul a b ha hb =>
    intro y
    rw [mul_assoc, ha (b * y), hb y, ha b, map_mul (CliffordAlgebra.involute)]
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc, add_mul]
    abel
  | add a b ha hb =>
    intro y
    rw [add_mul, map_add, map_add, map_add, ha, hb, add_mul, add_mul]
    abel

/-- The algebra projection `⋀ E' → ⋀ E` induced by `fst : E' = E ⊕ R → E`. -/
noncomputable def projAlg : ExteriorAlgebra R (E × R) →ₐ[R] ExteriorAlgebra R E :=
  ExteriorAlgebra.map (LinearMap.fst R E R)

/-- `projAlg` sends the generator `ι (e, r)` to `ι e`. -/
@[simp] theorem projAlg_ι (er : E × R) :
    projAlg (ExteriorAlgebra.ι R er) = ExteriorAlgebra.ι R er.1 := by
  rw [projAlg, ExteriorAlgebra.map_apply_ι]; rfl

/-- `projAlg` is a left inverse of `inclAlg`. -/
@[simp] theorem projAlg_inclAlg (x : ExteriorAlgebra R E) :
    projAlg (inclAlg (E := E) x) = x := by
  have hcomp : (projAlg (E := E)).comp (inclAlg (E := E)) = AlgHom.id R _ := by
    apply ExteriorAlgebra.hom_ext
    ext e
    simp [projAlg, inclAlg]
  exact AlgHom.congr_fun hcomp x

/-- Contraction by the `R`-coordinate functional `snd : E' = E ⊕ R → R`. -/
noncomputable def cContr : ExteriorAlgebra R (E × R) →ₗ[R] ExteriorAlgebra R (E × R) :=
  Koszul.contraction (LinearMap.snd R E R)

/-- Contraction by the `R`-coordinate satisfies
`cContr (ι v * x) = v.2 • x - ι v * cContr x`. -/
theorem cContr_ι_mul (v : E × R) (x : ExteriorAlgebra R (E × R)) :
    cContr (ExteriorAlgebra.ι R v * x) = v.2 • x - ExteriorAlgebra.ι R v * cContr x :=
  CliffordAlgebra.contractLeft_ι_mul (LinearMap.snd R E R) v x

/-- Contraction by the `R`-coordinate vanishes on scalars. -/
@[simp] theorem cContr_algebraMap (r : R) :
    cContr (algebraMap R (ExteriorAlgebra R (E × R)) r) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap _ (LinearMap.snd R E R) r

/-- Contraction by the `R`-coordinate sends `ι v` to the scalar `v.2`. -/
theorem cContr_ι (v : E × R) :
    cContr (ExteriorAlgebra.ι R v) = algebraMap R _ v.2 :=
  CliffordAlgebra.contractLeft_ι _ (LinearMap.snd R E R) v

/-- Involution-graded Leibniz rule for `cContr`. -/
theorem cContr_leibniz (x y : ExteriorAlgebra R (E × R)) :
    cContr (x * y) = cContr x * y + CliffordAlgebra.involute x * cContr y :=
  contraction_leibniz (LinearMap.snd R E R) x y

/-- The contraction by the second coordinate annihilates everything in the image of
`inclAlg`. -/
theorem cContr_inclAlg (y : ExteriorAlgebra R E) :
    cContr (inclAlg (E := E) y) = 0 := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, cContr_algebraMap]
  | ι e =>
    rw [inclAlg_ι, cContr_ι]; simp
  | mul a b ha hb =>
    rw [map_mul, cContr_leibniz, ha, hb, zero_mul, mul_zero, add_zero]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, add_zero]

/-! ## Intertwining the Koszul differentials -/

/-- `inclAlg` commutes with the grade involution. -/
theorem inclAlg_involute (x : ExteriorAlgebra R E) :
    inclAlg (E := E) (CliffordAlgebra.involute x)
      = CliffordAlgebra.involute (inclAlg (E := E) x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
  | ι e =>
    rw [CliffordAlgebra.involute_ι, map_neg, inclAlg_ι, CliffordAlgebra.involute_ι]
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, map_add, ha, hb]

/-- The Koszul contraction `φ'` intertwines with `inclAlg`:
`contract_{φ'} ∘ inclAlg = inclAlg ∘ contract_{φ}`. -/
theorem contraction_phiPrime_inclAlg (φ : Module.Dual R E) (f : R)
    (y : ExteriorAlgebra R E) :
    Koszul.contraction (phiPrime φ f) (inclAlg (E := E) y)
      = inclAlg (E := E) (Koszul.contraction φ y) := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap,
      CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | ι e =>
    rw [inclAlg_ι, CliffordAlgebra.contractLeft_ι, CliffordAlgebra.contractLeft_ι, phiPrime_apply,
      AlgHom.commutes]
    simp
  | mul a b ha hb =>
    rw [map_mul, contraction_leibniz, contraction_leibniz, ha, hb,
      ← inclAlg_involute, ← map_mul, ← map_mul, ← map_add]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb, ← map_add]

/-! ## The isomorphism `K(phi') ≅ C(f)` -/

/-- The degreewise comparison map `Θₙ : C(f)ₙ → ⋀ⁿ E'` as an `R`-linear map. In degree `0`,
`coneX … 0 = ⋀⁰E` and `Θ₀ = inclPow 0`; in degree `n+1`, `coneX … (n+1) = ⋀^{n+1}E × ⋀ⁿE` and
`Θ_{n+1}` is the coproduct of `inclPow (n+1)` and `wedgeE0Pow (n+1)`. -/
noncomputable def thetaLin (φ : Module.Dual R E) :
    (n : ℕ) →
      (coneX (Koszul.complex φ) (Koszul.complex φ) n) →ₗ[R] (⋀[R]^n (E × R))
  | 0 => inclPow 0
  | (n+1) => LinearMap.coprod (inclPow (n+1)) (wedgeE0Pow (n+1))

/-- In degree `0`, `thetaLin φ 0` is `inclPow 0`. -/
@[simp] theorem thetaLin_zero (φ : Module.Dual R E) (x : ⋀[R]^0 E) :
    thetaLin φ 0 x = inclPow 0 x := rfl

/-- In degree `n + 1`, `thetaLin φ (n + 1)` sends `(b, a)` to
`inclPow (n + 1) b + wedgeE0Pow (n + 1) a`. -/
@[simp] theorem thetaLin_succ (φ : Module.Dual R E) (n : ℕ)
    (b : ⋀[R]^(n + 1) E) (a : ⋀[R]^n E) :
    thetaLin φ (n+1) (b, a) = inclPow (n+1) b + wedgeE0Pow (n+1) a := rfl

/-- The projection `projAlg` kills `e₀`. -/
theorem projAlg_e0 : projAlg (e0 (R := R) (E := E)) = 0 := by
  simp [e0]

/-- `inclAlg (projAlg (ι v)) = ι v - v.2 • e₀`. -/
theorem inclAlg_projAlg_ι (v : E × R) :
    inclAlg (E := E) (projAlg (ExteriorAlgebra.ι R v))
      = ExteriorAlgebra.ι R v - v.2 • e0 (R := R) (E := E) := by
  rw [projAlg_ι, inclAlg_ι, e0, ← map_smul, ← map_sub]
  congr 1
  ext <;> simp

/-- `e₀ * e₀ = 0`. -/
theorem e0_mul_e0 : e0 (R := R) (E := E) * e0 (R := R) (E := E) = 0 :=
  ExteriorAlgebra.ι_sq_zero _

/-- `e₀` anticommutes with the generators of `⋀ E'`. -/
theorem e0_mul_ι (v : E × R) :
    e0 (R := R) (E := E) * ExteriorAlgebra.ι R v
      = -(ExteriorAlgebra.ι R v * e0 (R := R) (E := E)) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

private theorem mul_decomp_aux {A : Type*} [Ring A] [Algebra R A] (ι e P Cy y : A) (t : R)
    (hee : e * e = 0) (hanti : e * ι = -(ι * e)) (hy : P + e * Cy = y) :
    (ι - t • e) * P + e * (t • P - (ι - t • e) * Cy) = ι * y := by
  rw [← hy, sub_mul, show (ι - t • e) * Cy = ι * Cy - t • (e * Cy) by rw [sub_mul, smul_mul_assoc],
    mul_sub, mul_sub, mul_smul_comm, mul_smul_comm, ← mul_assoc e e Cy, hee, zero_mul, smul_zero,
    sub_zero, ← mul_assoc e ι Cy, hanti, neg_mul, smul_mul_assoc, mul_add, mul_assoc ι e Cy]
  abel

private noncomputable def decomp (ω : ExteriorAlgebra R (E × R)) :
    ExteriorAlgebra R (E × R) :=
  inclAlg (E := E) (projAlg ω) + e0 (R := R) (E := E) * inclAlg (E := E) (projAlg (cContr ω))

private theorem decomp_add (a b : ExteriorAlgebra R (E × R)) :
    decomp (a + b) = decomp a + decomp b := by
  simp only [decomp, map_add, mul_add]
  abel

private theorem decomp_smul (r : R) (a : ExteriorAlgebra R (E × R)) :
    decomp (r • a) = r • decomp a := by
  simp only [decomp, map_smul, mul_smul_comm, smul_add]

private theorem decomp_ι_mul (v : E × R) {y : ExteriorAlgebra R (E × R)}
    (hy : decomp y = y) : decomp (ExteriorAlgebra.ι R v * y) = ExteriorAlgebra.ι R v * y := by
  rw [decomp, map_mul, map_mul, inclAlg_projAlg_ι, cContr_ι_mul, map_sub, map_smul, map_sub,
    map_smul, map_mul, map_mul, inclAlg_projAlg_ι]
  exact mul_decomp_aux _ _ _ _ y v.2 e0_mul_e0 (e0_mul_ι v) hy

/-- Every `ω ∈ ⋀ E'` decomposes as `inclAlg (projAlg ω) + e₀ * inclAlg (projAlg (cContr ω))`. -/
theorem inclAlg_projAlg_add_e0_mul (ω : ExteriorAlgebra R (E × R)) :
    inclAlg (E := E) (projAlg ω) + e0 (R := R) (E := E) * inclAlg (E := E) (projAlg (cContr ω))
      = ω := by
  have h1 : decomp (1 : ExteriorAlgebra R (E × R)) = 1 := by
    rw [decomp, ← map_one (algebraMap R (ExteriorAlgebra R (E × R))), cContr_algebraMap]
    simp
  suffices key : ∀ y, decomp y = y → decomp (ω * y) = ω * y by
    simpa only [decomp, mul_one] using key 1 h1
  induction ω using CliffordAlgebra.induction with
  | algebraMap r => intro y hy; rw [← Algebra.smul_def, decomp_smul, hy]
  | ι v => exact fun y hy => decomp_ι_mul v hy
  | mul a b ha hb => intro y hy; rw [mul_assoc]; exact ha _ (hb y hy)
  | add a b ha hb => intro y hy; rw [add_mul, decomp_add, ha y hy, hb y hy]

/-- Elements of `⋀⁰ M` are scalars. -/
theorem exists_algebraMap_of_mem_exteriorPower_zero {M : Type*} [AddCommGroup M] [Module R M]
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^0 M) : ∃ r, algebraMap R _ r = x :=
  Submodule.mem_one.mp (by simpa only [pow_zero] using hx)

/-- `projAlg` preserves exterior degree: it maps `⋀ᵐ E'` into `⋀ᵐ E`. -/
theorem projAlg_grade (m : ℕ) :
    (⋀[R]^m (E × R)).map (projAlg (E := E)).toLinearMap ≤ ⋀[R]^m E := by
  rintro _ ⟨x, hx, rfl⟩
  have h := (exteriorPower.map m (LinearMap.fst R E R) ⟨x, hx⟩).2
  rwa [exteriorPower.coe_map] at h

/-- Contraction by the `R`-coordinate vanishes on `⋀⁰ E'`. -/
private theorem cContr_eq_zero_of_mem_exteriorPower_zero {x : ExteriorAlgebra R (E × R)}
    (hx : x ∈ ⋀[R]^0 (E × R)) : cContr x = 0 := by
  obtain ⟨r, rfl⟩ := exists_algebraMap_of_mem_exteriorPower_zero hx
  rw [cContr_algebraMap]

/-- Contraction by the `R`-coordinate lowers exterior degree by one. -/
theorem cContr_grade (m : ℕ) :
    (⋀[R]^m (E × R)).map (cContr (E := E)) ≤ ⋀[R]^(m - 1) (E × R) := by
  induction m with
  | zero =>
    rintro _ ⟨x, hx, rfl⟩
    rw [cContr_eq_zero_of_mem_exteriorPower_zero hx]
    exact zero_mem _
  | succ k ih =>
    rw [Nat.add_sub_cancel, exteriorPower_succ_eq_range_mul, Submodule.map_le_iff_le_comap,
      Submodule.mul_le]
    rintro _ ⟨v, rfl⟩ b hb
    rw [Submodule.mem_comap, cContr_ι_mul]
    refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) ?_
    rcases k with _ | j
    · rw [cContr_eq_zero_of_mem_exteriorPower_zero hb, mul_zero]
      exact zero_mem _
    · rw [exteriorPower_succ_eq_range_mul]
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v)
        (by simpa using ih (Submodule.mem_map_of_mem hb))

/-- `cContr (e₀ * inclAlg a) = inclAlg a`. -/
theorem cContr_e0_mul_inclAlg (a : ExteriorAlgebra R E) :
    cContr (e0 (R := R) (E := E) * inclAlg (E := E) a) = inclAlg (E := E) a := by
  rw [e0, cContr_ι_mul, cContr_inclAlg, mul_zero, sub_zero, one_smul]

/-- `Θ₀` is bijective. -/
theorem thetaLin_zero_bijective (φ : Module.Dual R E) : Function.Bijective (thetaLin φ 0) := by
  refine ⟨fun x y hxy => Subtype.ext ?_, fun ω => ⟨⟨projAlg (E := E) ω,
    projAlg_grade 0 (Submodule.mem_map_of_mem ω.2)⟩, Subtype.ext ?_⟩⟩
  · simpa using congrArg (projAlg (E := E) ∘ Subtype.val) hxy
  · simpa [cContr_eq_zero_of_mem_exteriorPower_zero ω.2] using
      inclAlg_projAlg_add_e0_mul (ω : ExteriorAlgebra R (E × R))

/-- `Θ_{m+1}` is bijective. -/
theorem thetaLin_succ_bijective (φ : Module.Dual R E) (m : ℕ) :
    Function.Bijective (thetaLin φ (m+1)) := by
  refine ⟨?_, fun ω => ?_⟩
  · rintro ⟨b, a⟩ ⟨b', a'⟩ hxy
    have key := congrArg Subtype.val hxy
    rw [thetaLin_succ, thetaLin_succ, AddSubmonoid.coe_add, AddSubmonoid.coe_add, inclPow_coe,
      wedgeE0Pow_succ_coe, inclPow_coe, wedgeE0Pow_succ_coe] at key
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa [projAlg_e0] using congrArg (projAlg (E := E)) key
    · simpa [cContr_inclAlg, cContr_e0_mul_inclAlg] using congrArg (projAlg (E := E) ∘ cContr) key
  · have hωc : cContr (ω : ExteriorAlgebra R (E × R)) ∈ ⋀[R]^m (E × R) := by
      simpa only [Nat.add_sub_cancel] using cContr_grade (m+1) (Submodule.mem_map_of_mem ω.2)
    refine ⟨(⟨projAlg (E := E) ω, projAlg_grade (m+1) (Submodule.mem_map_of_mem ω.2)⟩,
        ⟨projAlg (E := E) (cContr ω), projAlg_grade m (Submodule.mem_map_of_mem hωc)⟩),
      Subtype.ext ?_⟩
    rw [thetaLin_succ, AddSubmonoid.coe_add, inclPow_coe, wedgeE0Pow_succ_coe]
    exact inclAlg_projAlg_add_e0_mul _

/-- Each `Θₙ` is bijective.  Inside `⋀ E'` there is a canonical splitting
`⋀ⁿ(E ⊕ R) ≅ ⋀ⁿ E ⊕ (e₀ ∧ ⋀^{n-1} E)`, with inverse
`ω ↦ (projAlg ω, projAlg (cContr ω))`; `Θₙ` is the corresponding isomorphism. -/
theorem thetaLin_bijective (φ : Module.Dual R E) (n : ℕ) :
    Function.Bijective (thetaLin φ n) := by
  cases n with
  | zero => exact thetaLin_zero_bijective φ
  | succ m => exact thetaLin_succ_bijective φ m

/-- `Θ_{n+1}(b, a) = inclAlg b + e₀ * inclAlg a` inside `⋀ E'`. -/
theorem thetaLin_succ_coe (φ : Module.Dual R E) (n : ℕ) (b : ⋀[R]^(n + 1) E) (a : ⋀[R]^n E) :
    (thetaLin φ (n+1) (b, a) : ExteriorAlgebra R (E × R))
      = inclAlg (E := E) b + e0 (R := R) (E := E) * inclAlg (E := E) a := rfl

/-- The Koszul contraction of `φ'` sends `e₀` to `f`. -/
theorem contraction_phiPrime_e0 (φ : Module.Dual R E) (f : R) :
    Koszul.contraction (phiPrime φ f) (e0 (R := R) (E := E))
      = algebraMap R (ExteriorAlgebra R (E × R)) f := by
  rw [e0, CliffordAlgebra.contractLeft_ι, phiPrime_apply]
  simp

/-- The grade involution negates `e₀`. -/
theorem involute_e0 : CliffordAlgebra.involute (e0 (R := R) (E := E)) = -e0 (R := R) (E := E) :=
  CliffordAlgebra.involute_ι _

/-- The Koszul contraction of `φ'` on `inclAlg x + e₀ * inclAlg y`. -/
theorem contraction_phiPrime_inclAlg_add_e0_mul (φ : Module.Dual R E) (f : R)
    (x y : ExteriorAlgebra R E) :
    Koszul.contraction (phiPrime φ f)
        (inclAlg (E := E) x + e0 (R := R) (E := E) * inclAlg (E := E) y)
      = inclAlg (E := E) (Koszul.contraction φ x + f • y)
        + e0 (R := R) (E := E) * inclAlg (E := E) (-Koszul.contraction φ y) := by
  rw [map_add, contraction_leibniz, contraction_phiPrime_inclAlg, contraction_phiPrime_inclAlg,
    contraction_phiPrime_e0, involute_e0, ← Algebra.smul_def, map_add, map_smul, map_neg, mul_neg,
    neg_mul]
  abel

/-- The Koszul contraction vanishes on `⋀⁰`. -/
theorem contraction_eq_zero_of_mem_exteriorPower_zero {F : Type*} [AddCommGroup F] [Module R F]
    (φ : Module.Dual R F) {x : ExteriorAlgebra R F} (hx : x ∈ ⋀[R]^0 F) :
    Koszul.contraction φ x = 0 := by
  obtain ⟨r, rfl⟩ := exists_algebraMap_of_mem_exteriorPower_zero (R := R) (M := F) hx
  rw [CliffordAlgebra.contractLeft_algebraMap]

-- The `change` steps below reduce the categorical differentials of `Koszul.complex` and
-- of the cone to their underlying linear maps; unfolding `Koszul.complex` through
-- `coneX`/`coneD` exceeds the default heartbeat budget.
/-- The family `(Θₙ)` is a chain map: it intertwines the cone differential with the
Koszul differential of `φ'`. -/
theorem thetaLin_comm (φ : Module.Dual R E) (f : R) (n : ℕ) :
    (ModuleCat.ofHom (thetaLin φ (n+1))) ≫
        (Koszul.complex (phiPrime φ f)).d (n+1) n
      = (coneComplex (Koszul.complex φ) (Koszul.complex φ)
            (mulByF (Koszul.complex φ) f)).d (n+1) n ≫
        (ModuleCat.ofHom (thetaLin φ n)) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  simp only [Koszul.complex, coneComplex, ChainComplex.of_d]
  cases n with
  | zero =>
    apply LinearMap.ext
    rintro ⟨b, a⟩
    apply Subtype.ext
    change (Koszul.d (phiPrime φ f) 0 (thetaLin φ (0+1) (b, a)) : ExteriorAlgebra R (E × R))
      = (thetaLin φ 0 (coneD0lin (Koszul.complex φ) (Koszul.complex φ)
          (mulByF (Koszul.complex φ) f) (b, a)) : ExteriorAlgebra R (E × R))
    rw [thetaLin_zero, Koszul.d_apply_coe, thetaLin_succ_coe,
      contraction_phiPrime_inclAlg_add_e0_mul]
    change _ = inclAlg (E := E) ((Koszul.d φ 0 b : ExteriorAlgebra R E)
      + f • (a : ExteriorAlgebra R E))
    rw [Koszul.d_apply_coe, contraction_eq_zero_of_mem_exteriorPower_zero φ a.2, neg_zero,
      map_zero, mul_zero, add_zero]
  | succ m =>
    apply LinearMap.ext
    rintro ⟨b, a⟩
    apply Subtype.ext
    change (Koszul.d (phiPrime φ f) (m + 1) (thetaLin φ (m+1+1) (b, a)) :
        ExteriorAlgebra R (E × R))
      = ((LinearMap.coprod (inclPow (m+1)) (wedgeE0Pow (m+1))
          (coneDSlin (Koszul.complex φ) (Koszul.complex φ) (mulByF (Koszul.complex φ) f) m (b, a)))
          : ExteriorAlgebra R (E × R))
    rw [Koszul.d_apply_coe, thetaLin_succ_coe, contraction_phiPrime_inclAlg_add_e0_mul,
      LinearMap.coprod_apply, AddSubmonoid.coe_add, inclPow_coe, wedgeE0Pow_succ_coe]
    have hd2 : (Koszul.complex φ).d (m + 2) (m + 1)
        = ModuleCat.ofHom (Koszul.d φ (m + 1)) := Koszul.complex_d φ (m + 1)
    have hd1 : (Koszul.complex φ).d (m + 1) m
        = ModuleCat.ofHom (Koszul.d φ m) := Koszul.complex_d φ m
    congr 2
    · simp only [coneDSlin, LinearMap.prod_apply, Function.prod_apply, LinearMap.add_apply,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, hd2,
        ModuleCat.hom_ofHom, mulByF_f]
      rfl
    · congr 1
      simp only [coneDSlin, LinearMap.prod_apply, Function.prod_apply, LinearMap.neg_apply,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply, hd1, ModuleCat.hom_ofHom]
      rfl

/-- The degreewise isomorphism `C(f)ₙ ≅ Kₙ(phi')` whose forward map is `thetaLin φ n`. -/
noncomputable def thetaIsoX (φ : Module.Dual R E) (f : R) (n : ℕ) :
    (coneComplex (Koszul.complex φ) (Koszul.complex φ) (mulByF (Koszul.complex φ) f)).X n ≅
      (Koszul.complex (phiPrime φ f)).X n :=
  LinearEquiv.toModuleIso (LinearEquiv.ofBijective (thetaLin φ n) (thetaLin_bijective φ n))

/-- The forward map of `thetaIsoX φ f n` is `thetaLin φ n`. -/
@[simp] theorem thetaIsoX_hom (φ : Module.Dual R E) (f : R) (n : ℕ) :
    (thetaIsoX φ f n).hom = ModuleCat.ofHom (thetaLin φ n) := rfl

/-- The cone of multiplication by `f` on the Koszul complex of `phi` is isomorphic, as a chain
complex of `R`-modules, to the Koszul complex of `phi' : E ⊕ R → R`, by an isomorphism with the
prescribed components `Θₙ`: the inclusion on the `⋀ⁿ E` summand and wedging with `e₀ = (0,1)` on
the `⋀^{n-1} E` summand. -/
@[stacks 0628]
theorem koszulComplex_phiPrime_iso_cone (φ : Module.Dual R E) (f : R) :
    ∃ Θ : coneComplex (Koszul.complex φ) (Koszul.complex φ) (mulByF (Koszul.complex φ) f) ≅
        Koszul.complex (phiPrime φ f),
      (∀ x : (⋀[R]^0 E),
        (Θ.hom.f 0).hom (show ((Koszul.complex φ).X 0 : Type (max u v)) from x) = inclPow 0 x) ∧
      (∀ (n : ℕ) (b : (⋀[R]^(n+1) E)) (a : (⋀[R]^n E)),
        (Θ.hom.f (n+1)).hom
            (show ((Koszul.complex φ).X (n+1) × (Koszul.complex φ).X n : Type (max u v))
              from (b, a))
          = inclPow (n+1) b + wedgeE0Pow (n+1) a) := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun n => thetaIsoX φ f n) ?_,
    fun _ => rfl, fun _ _ _ => rfl⟩
  intro i j hij
  obtain rfl : j + 1 = i := hij
  simpa only [thetaIsoX_hom] using thetaLin_comm φ f j

end Stacks.MappingCone.NatIndexed

/-!
## The mapping-cone differential and the Koszul complex of an appended element

Mathlib's `HomologicalComplex.homotopyCofiber` is the mapping cone of a morphism of homological
complexes. The four equations `HomologicalComplex.homotopyCofiber.{d_fstX, d_sndX, inlX_d, inrX_d}`
give the block-matrix description of its differential: its first and second projections, and its
restrictions to the two summands. Mathlib orders the terms of the homotopy cofiber as shifted
source, then target.

The Koszul complex `K_•(f₁, …, f_r)` of a finite sequence of elements of `R` is isomorphic to the
cone of multiplication by `f_r` on `K_•(f₁, …, f_{r-1})`. A sequence with a distinguished final
element is `Fin.snoc f a`, and under the linear equivalence
`(Fin r → R) × R ≃ₗ[R] (Fin (r + 1) → R)` given by `Fin.snoc`, `Koszul.seqDual (Fin.snoc f a)`
becomes `phiPrime (Koszul.seqDual f) a`.
-/

add_to_stacks 0627 "first projection of the mapping-cone differential"
  HomologicalComplex.homotopyCofiber.d_fstX
add_to_stacks 0627 "second projection of the mapping-cone differential"
  HomologicalComplex.homotopyCofiber.d_sndX
add_to_stacks 0627 "restriction to the first summand"
  HomologicalComplex.homotopyCofiber.inlX_d
add_to_stacks 0627 "restriction to the second summand"
  HomologicalComplex.homotopyCofiber.inrX_d

namespace Koszul

universe u

/-- The linear equivalence `(Fin r → R) × R ≃ₗ[R] (Fin (r + 1) → R)` appending the
second coordinate to the sequence. -/
noncomputable def snocLinearEquiv {R : Type u} [CommRing R] (r : ℕ) :
    ((Fin r → R) × R) ≃ₗ[R] (Fin (r + 1) → R) where
  toFun x := Fin.snoc x.1 x.2
  invFun y := (fun i => y i.castSucc, y (Fin.last r))
  map_add' x y := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  left_inv x := by ext <;> simp
  right_inv y := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Under `snocLinearEquiv`, the functional of an appended sequence is the functional
`phiPrime` of the initial segment and the appended element. -/
theorem seqDual_comp_snocLinearEquiv {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (a : R) :
    (Koszul.seqDual (Fin.snoc f a)).comp (snocLinearEquiv r).toLinearMap =
      Stacks.MappingCone.NatIndexed.phiPrime (Koszul.seqDual f) a := by
  apply LinearMap.ext
  rintro ⟨x, b⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Koszul.seqDual_apply,
    Stacks.MappingCone.NatIndexed.phiPrime_apply]
  rw [Fin.sum_univ_castSucc]
  simp [snocLinearEquiv, mul_comm]

/-- `exteriorPower.map` agrees with `ExteriorAlgebra.map` on underlying elements. -/
theorem exteriorPower_map_coe {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (n : ℕ) (x : ⋀[R]^n M) :
    ((exteriorPower.map n g x : ExteriorAlgebra R N)) =
      ExteriorAlgebra.map g (x : ExteriorAlgebra R M) := by
  have key : ∀ m : Fin n → M,
      ((exteriorPower.map n g (exteriorPower.ιMulti R n m) : ExteriorAlgebra R N)) =
        ExteriorAlgebra.map g
          ((exteriorPower.ιMulti R n m : ExteriorAlgebra R M)) := by
    intro m
    rw [exteriorPower.map_apply_ιMulti, exteriorPower.ιMulti_apply_coe,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]
  let L₁ : (⋀[R]^n M) →ₗ[R] ExteriorAlgebra R N :=
    (Submodule.subtype _).comp (exteriorPower.map n g)
  let L₂ : (⋀[R]^n M) →ₗ[R] ExteriorAlgebra R N :=
    (ExteriorAlgebra.map g).toLinearMap.comp (Submodule.subtype _)
  have hL : L₁ = L₂ := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span R n M)
    rintro _ ⟨m, rfl⟩
    exact key m
  exact congrFun (congrArg DFunLike.coe hL) x

/-- A linear equivalence of modules induces a linear equivalence of exterior powers. -/
noncomputable def exteriorPowerLinearEquiv {R : Type u} [CommRing R]
    (n : ℕ) {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    (⋀[R]^n M) ≃ₗ[R] (⋀[R]^n N) :=
  LinearEquiv.ofLinearMap (exteriorPower.map n e.toLinearMap)
    (exteriorPower.map n e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp]; simp)
    (by rw [← exteriorPower.map_comp]; simp)

/-- A linear equivalence `e : M ≃ₗ[R] N` identifies the Koszul complex of `φ ∘ e` with
the Koszul complex of `φ`. -/
noncomputable def complexLinearEquiv {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (φ : Module.Dual R N) :
    Koszul.complex (φ.comp e.toLinearMap) ≅ Koszul.complex φ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => LinearEquiv.toModuleIso (exteriorPowerLinearEquiv n e)) (by
      intro i j hij
      obtain rfl : j + 1 = i := hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (⋀[R]^(j + 1) M) at x
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, Koszul.complex_d, Koszul.complex_d]
      simp only [LinearEquiv.toModuleIso_hom, exteriorPowerLinearEquiv]
      change Koszul.d φ j (exteriorPower.map (j + 1) e.toLinearMap x) =
        exteriorPower.map j e.toLinearMap (Koszul.d (φ.comp e.toLinearMap) j x)
      apply Subtype.ext
      rw [Koszul.d_apply_coe, exteriorPower_map_coe, exteriorPower_map_coe, Koszul.d_apply_coe]
      exact (map_contractLeft_pow e.toLinearMap φ (j + 1) x x.2).symm)

/-- The Koszul complex of a sequence obtained by appending `a` is isomorphic to the cone of
multiplication by `a` on the Koszul complex of the original sequence. -/
@[stacks 0629]
public theorem seqComplex_snoc_iso_cone {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (a : R) :
    Nonempty
      (Koszul.seqComplex (Fin.snoc f a) ≅
        Stacks.MappingCone.NatIndexed.coneComplex (Koszul.seqComplex f) (Koszul.seqComplex f)
          (Stacks.MappingCone.NatIndexed.mulByF (Koszul.seqComplex f) a)) := by
  obtain ⟨Θ, -, -⟩ :=
    Stacks.MappingCone.NatIndexed.koszulComplex_phiPrime_iso_cone (Koszul.seqDual f) a
  have h := complexLinearEquiv (snocLinearEquiv (R := R) r) (Koszul.seqDual (Fin.snoc f a))
  rw [seqDual_comp_snocLinearEquiv] at h
  exact ⟨h.symm ≪≫ Θ.symm⟩

end Koszul
