module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Invariance of the conormal module

Throughout, `R` and `S` are commutative rings and `R → S` is a ring map of finite type.

A presentation of finite type of `S` over `R` is a surjective `R`-algebra homomorphism
`α : R[x₁, …, xₙ] → S` from a polynomial `R`-algebra in finitely many variables, with
kernel `I = Ker α`. The conormal module `I/I²` is annihilated by `I`, hence carries a
natural `S`-module structure via `R[x₁, …, xₙ]/I = S`.

## Main results

* `schanuel00S3`: two homotopy-equivalent two-term complexes of `S`-modules
  `A₁ → A₀` and `B₁ → B₀` have stably isomorphic terms, `A₁ ⊕ B₀ ≅ B₁ ⊕ A₀`.
* `conormal_stable_iso`: for two presentations `α : R[x₁, …, xₙ] → S` with kernel `I`
  and `β : R[y₁, …, y_m] → S` with kernel `J`, there is an isomorphism of `S`-modules
  `I/I² ⊕ S^{⊕m} ≅ J/J² ⊕ S^{⊕n}`.

So although `I/I²` depends on the chosen presentation, it is well defined up to addition
of a free `S`-module: passing from a presentation with `n` variables to one with `m`
variables changes `I/I²` only by free summands.

## Implementation notes

* A presentation of finite type of `S` over `R` by finitely many variables is modelled by
  `Algebra.Generators R S (Fin n)`: a family `val : Fin n → S` of generators together with
  the evaluation `R`-algebra homomorphism `MvPolynomial (Fin n) R → S`, which is
  automatically surjective since every `s : S` admits a polynomial preimage. The chosen
  number of variables `n` may differ from `m`.
* The conormal module `I/I²` of such a presentation is `P.toExtension.Cotangent`, with its
  canonical `S`-module structure `Algebra.Extension.Cotangent.module`.
* The free `S`-module `S^{⊕k}` of rank `k` is modelled by `Fin k → S`, the direct sum of
  two `S`-modules by their product, and an isomorphism of `S`-modules by
  `Nonempty (M ≃ₗ[S] N)`.
* `[Algebra.FiniteType R S]` records the hypothesis that `R → S` is of finite type. The
  existence of the finite-variable presentations `P`, `Q` already forces it, but the
  hypothesis is kept to stay faithful to the source statement.
-/

@[expose] public section

namespace NaiveCotangent.Conormal

section Ring

variable {S : Type*} [Ring S]

/-!
## Schanuel's lemma for two-term complexes

A presentation `P` gives rise to the naive cotangent complex, the two-term complex of
`S`-modules `NL(P) : Cotangent P →[d] CotangentSpace P` whose kernel is the first naive
cotangent cohomology `H₁` and whose cokernel is the module of Kähler differentials `Ω`,
and whose degree-`0` term `CotangentSpace P` is free of rank the number of variables.

Two presentations of the same `S` yield homotopy-equivalent naive cotangent complexes,
the chain maps and homotopy operators being supplied by the functoriality of the
cotangent complex (`Algebra.Extension.Cotangent.map`,
`Algebra.Extension.CotangentSpace.map`, together with the homotopy lemmas
`Algebra.Extension.Cotangent.map_sub_map` and
`Algebra.Extension.CotangentSpace.map_sub_map`).

The elementary block-matrix form of Schanuel's lemma below (Stacks 00S3,
Lemma 10.134.14) turns such a homotopy equivalence between two-term complexes
`A₁ →[dA] A₀` and `B₁ →[dB] B₀` into a stable isomorphism `A₁ ⊕ B₀ ≅ B₁ ⊕ A₀`.
Combined with the freeness of the two cotangent spaces this gives 00S5, so no `Ext²`
and no projectivity argument is needed.
-/

section Schanuel

variable {A₁ A₀ B₁ B₀ : Type*}
  [AddCommGroup A₁] [Module S A₁] [AddCommGroup A₀] [Module S A₀]
  [AddCommGroup B₁] [Module S B₁] [AddCommGroup B₀] [Module S B₀]
  {dA : A₁ →ₗ[S] A₀} {dB : B₁ →ₗ[S] B₀}
  {φ₁ : A₁ →ₗ[S] B₁} {φ₀ : A₀ →ₗ[S] B₀} {ψ₁ : B₁ →ₗ[S] A₁} {ψ₀ : B₀ →ₗ[S] A₀}
  {hA : A₀ →ₗ[S] A₁} {hB : B₀ →ₗ[S] B₁}

/-- The correction term `ψ₁ ∘ hB - hA ∘ ψ₀` vanishes on the image of `dB`. -/
theorem schanuel00S3_correction_comp_d (eψ : ∀ u, ψ₀ (dB u) = dA (ψ₁ u))
    (eA1 : ∀ x, x - ψ₁ (φ₁ x) = hA (dA x)) (eB1 : ∀ u, u - φ₁ (ψ₁ u) = hB (dB u)) (b : B₁) :
    ψ₁ (hB (dB b)) - hA (ψ₀ (dB b)) = 0 := by
  have t2 : ψ₁ (hB (dB b)) = ψ₁ b - ψ₁ (φ₁ (ψ₁ b)) := by rw [← eB1 b, map_sub]
  have t3 : hA (ψ₀ (dB b)) = ψ₁ b - ψ₁ (φ₁ (ψ₁ b)) := by rw [eψ b, ← eA1 (ψ₁ b)]
  rw [t2, t3, sub_self]

/-- The first coordinate of the composite `Θ ∘ Ξ` in `schanuel00S3` is the identity. -/
theorem schanuel00S3_right_inv_fst (eφ : ∀ x, φ₀ (dA x) = dB (φ₁ x))
    (eψ : ∀ u, ψ₀ (dB u) = dA (ψ₁ u))
    (eA1 : ∀ x, x - ψ₁ (φ₁ x) = hA (dA x)) (eA0 : ∀ x, x - ψ₀ (φ₀ x) = dA (hA x))
    (eB1 : ∀ u, u - φ₁ (ψ₁ u) = hB (dB u)) (eB0 : ∀ u, u - φ₀ (ψ₀ u) = dB (hB u))
    (u : B₁) (v : A₀) :
    φ₁ (ψ₁ u + hA v - (ψ₁ (hB (dB u - φ₀ v)) - hA (ψ₀ (dB u - φ₀ v)))) +
      hB (dB u - φ₀ v) = u := by
  have hRdB : φ₁ (ψ₁ (hB (dB u))) - φ₁ (hA (ψ₀ (dB u))) = 0 := by
    rw [← map_sub, schanuel00S3_correction_comp_d eψ eA1 eB1 u, map_zero]
  have hdiag : φ₁ (ψ₁ u) + hB (dB u) = u := by
    rw [← eB1 u]
    abel
  have kR2 : ∀ a : A₁, φ₁ (hA (dA a)) - hB (φ₀ (dA a)) = 0 := by
    intro a
    have t1 : φ₁ (hA (dA a)) = φ₁ a - φ₁ (ψ₁ (φ₁ a)) := by rw [← eA1 a, map_sub]
    have t2 : hB (φ₀ (dA a)) = φ₁ a - φ₁ (ψ₁ (φ₁ a)) := by rw [eφ a, ← eB1 (φ₁ a)]
    rw [t1, t2, sub_self]
  have c1 : φ₁ (hA v) - φ₁ (hA (ψ₀ (φ₀ v))) = φ₁ (hA (dA (hA v))) := by
    rw [← map_sub, ← map_sub, eA0 v]
  have c3 : hB (φ₀ (dA (hA v))) = hB (φ₀ v) - hB (φ₀ (ψ₀ (φ₀ v))) := by
    rw [← eA0 v]
    simp only [map_sub]
  have t : φ₁ (ψ₁ (hB (φ₀ v))) = hB (φ₀ v) - hB (dB (hB (φ₀ v))) := by
    rw [← eB1 (hB (φ₀ v))]
    abel
  have s : hB (dB (hB (φ₀ v))) = hB (φ₀ v) - hB (φ₀ (ψ₀ (φ₀ v))) := by
    rw [← eB0 (φ₀ v)]
    simp only [map_sub]
  simp only [map_sub, map_add]
  linear_combination (norm := abel) hdiag - hRdB + c1 + kR2 (hA v) + c3 + t - s

/-- The second coordinate of the composite `Θ ∘ Ξ` in `schanuel00S3` is the identity. -/
theorem schanuel00S3_right_inv_snd (eψ : ∀ u, ψ₀ (dB u) = dA (ψ₁ u))
    (eA0 : ∀ x, x - ψ₀ (φ₀ x) = dA (hA x)) (eB0 : ∀ u, u - φ₀ (ψ₀ u) = dB (hB u))
    (u : B₁) (v : A₀) :
    dA (ψ₁ u + hA v - (ψ₁ (hB (dB u - φ₀ v)) - hA (ψ₀ (dB u - φ₀ v)))) -
      ψ₀ (dB u - φ₀ v) = v := by
  have hd : dA (ψ₁ u) - ψ₀ (dB u) = 0 := by
    rw [eψ u, sub_self]
  have hd2 : dA (hA v) + ψ₀ (φ₀ v) = v := by
    rw [← eA0 v]
    abel
  have kR : ∀ b : B₀, dA (ψ₁ (hB b)) - dA (hA (ψ₀ b)) = 0 := by
    intro b
    have a1 : dA (ψ₁ (hB b)) = ψ₀ b - ψ₀ (φ₀ (ψ₀ b)) := by rw [← eψ, ← eB0 b, map_sub]
    have a3 : dA (hA (ψ₀ b)) = ψ₀ b - ψ₀ (φ₀ (ψ₀ b)) := by rw [← eA0 (ψ₀ b)]
    rw [a1, a3, sub_self]
  simp only [map_sub, map_add]
  linear_combination (norm := abel) hd + hd2 - kR (dB u) + kR (φ₀ v)

/-- The first coordinate of the composite `Ξ ∘ Θ` in `schanuel00S3` is the identity. -/
theorem schanuel00S3_left_inv_fst (eφ : ∀ x, φ₀ (dA x) = dB (φ₁ x))
    (eψ : ∀ u, ψ₀ (dB u) = dA (ψ₁ u))
    (eA1 : ∀ x, x - ψ₁ (φ₁ x) = hA (dA x))
    (eB1 : ∀ u, u - φ₁ (ψ₁ u) = hB (dB u)) (eB0 : ∀ u, u - φ₀ (ψ₀ u) = dB (hB u))
    (x : A₁) (y : B₀) :
    ψ₁ (φ₁ x + hB y) + hA (dA x - ψ₀ y) -
      (ψ₁ (hB (dB (φ₁ x + hB y) - φ₀ (dA x - ψ₀ y))) -
        hA (ψ₀ (dB (φ₁ x + hB y) - φ₀ (dA x - ψ₀ y)))) = x := by
  have kdB := schanuel00S3_correction_comp_d eψ eA1 eB1
  have k3 : ψ₁ (hB (φ₀ (dA x))) - hA (ψ₀ (φ₀ (dA x))) = 0 := by
    rw [eφ x]
    exact kdB (φ₁ x)
  have hdiag : ψ₁ (φ₁ x) + hA (dA x) = x := by
    rw [← eA1 x]
    abel
  have e1 : ψ₁ (hB y) - ψ₁ (hB (φ₀ (ψ₀ y))) = ψ₁ (hB (dB (hB y))) := by
    rw [← map_sub, ← map_sub, eB0 y]
  have e2 : hA (ψ₀ y) - hA (ψ₀ (φ₀ (ψ₀ y))) = hA (ψ₀ (dB (hB y))) := by
    rw [← map_sub, ← map_sub, eB0 y]
  simp only [map_sub, map_add]
  linear_combination (norm := abel) hdiag + e1 - e2 - kdB (φ₁ x) + k3

/-- The second coordinate of the composite `Ξ ∘ Θ` in `schanuel00S3` is the identity. -/
theorem schanuel00S3_left_inv_snd (eφ : ∀ x, φ₀ (dA x) = dB (φ₁ x))
    (eB0 : ∀ u, u - φ₀ (ψ₀ u) = dB (hB u)) (x : A₁) (y : B₀) :
    dB (φ₁ x + hB y) - φ₀ (dA x - ψ₀ y) = y := by
  have hd2 : dB (hB y) + φ₀ (ψ₀ y) = y := by
    rw [← eB0 y]
    abel
  simp only [map_sub, map_add]
  linear_combination (norm := abel) hd2 - eφ x

end Schanuel

/-- **Stacks 00S3 (Lemma 10.134.14), elementary block-matrix form.**
Two homotopy-equivalent two-term complexes `A₁ →[dA] A₀` and `B₁ →[dB] B₀`
(with chain maps `φ = (φ₁, φ₀)`, `ψ = (ψ₁, ψ₀)` and homotopies `ψ∘φ ≃ id_A`,
`φ∘ψ ≃ id_B`) have stably isomorphic terms: `A₁ × B₀ ≃ₗ[S] B₁ × A₀`.

The homotopy data: `hA : A₀ →ₗ A₁` with `id − ψ₁∘φ₁ = hA∘dA` (degree 1) and
`id − ψ₀∘φ₀ = dA∘hA` (degree 0); symmetrically `hB`. -/
theorem schanuel00S3 {A₁ A₀ B₁ B₀ : Type*}
    [AddCommGroup A₁] [Module S A₁] [AddCommGroup A₀] [Module S A₀]
    [AddCommGroup B₁] [Module S B₁] [AddCommGroup B₀] [Module S B₀]
    (dA : A₁ →ₗ[S] A₀) (dB : B₁ →ₗ[S] B₀) (φ₁ : A₁ →ₗ[S] B₁) (φ₀ : A₀ →ₗ[S] B₀)
    (ψ₁ : B₁ →ₗ[S] A₁) (ψ₀ : B₀ →ₗ[S] A₀) (hφ : φ₀ ∘ₗ dA = dB ∘ₗ φ₁) (hψ : ψ₀ ∘ₗ dB = dA ∘ₗ ψ₁)
    (hA : A₀ →ₗ[S] A₁) (hA1 : LinearMap.id - ψ₁ ∘ₗ φ₁ = hA ∘ₗ dA)
    (hA0 : LinearMap.id - ψ₀ ∘ₗ φ₀ = dA ∘ₗ hA) (hB : B₀ →ₗ[S] B₁)
    (hB1 : LinearMap.id - φ₁ ∘ₗ ψ₁ = hB ∘ₗ dB) (hB0 : LinearMap.id - φ₀ ∘ₗ ψ₀ = dB ∘ₗ hB) :
    Nonempty ((A₁ × B₀) ≃ₗ[S] (B₁ × A₀)) := by
  have eφ : ∀ x, φ₀ (dA x) = dB (φ₁ x) := LinearMap.congr_fun hφ
  have eψ : ∀ u, ψ₀ (dB u) = dA (ψ₁ u) := LinearMap.congr_fun hψ
  have eA1 : ∀ x, x - ψ₁ (φ₁ x) = hA (dA x) := LinearMap.congr_fun hA1
  have eA0 : ∀ x, x - ψ₀ (φ₀ x) = dA (hA x) := LinearMap.congr_fun hA0
  have eB1 : ∀ u, u - φ₁ (ψ₁ u) = hB (dB u) := LinearMap.congr_fun hB1
  have eB0 : ∀ u, u - φ₀ (ψ₀ u) = dB (hB u) := LinearMap.congr_fun hB0
  let R1 : B₀ →ₗ[S] A₁ := ψ₁ ∘ₗ hB - hA ∘ₗ ψ₀
  let Θ : (A₁ × B₀) →ₗ[S] (B₁ × A₀) :=
    LinearMap.prod
      (φ₁ ∘ₗ LinearMap.fst S A₁ B₀ + hB ∘ₗ LinearMap.snd S A₁ B₀)
      (dA ∘ₗ LinearMap.fst S A₁ B₀ - ψ₀ ∘ₗ LinearMap.snd S A₁ B₀)
  let Ξbot : (B₁ × A₀) →ₗ[S] B₀ := dB ∘ₗ LinearMap.fst S B₁ A₀ - φ₀ ∘ₗ LinearMap.snd S B₁ A₀
  let Ξ : (B₁ × A₀) →ₗ[S] (A₁ × B₀) :=
    LinearMap.prod
      (ψ₁ ∘ₗ LinearMap.fst S B₁ A₀ + hA ∘ₗ LinearMap.snd S B₁ A₀ - R1 ∘ₗ Ξbot)
      Ξbot
  refine ⟨LinearEquiv.ofLinearMap Θ Ξ ?_ ?_⟩
  · refine LinearMap.ext fun ⟨u, v⟩ => ?_
    exact Prod.ext (schanuel00S3_right_inv_fst eφ eψ eA1 eA0 eB1 eB0 u v)
      (schanuel00S3_right_inv_snd eψ eA0 eB0 u v)
  · refine LinearMap.ext fun ⟨x, y⟩ => ?_
    exact Prod.ext (schanuel00S3_left_inv_fst eφ eψ eA1 eB1 eB0 x y)
      (schanuel00S3_left_inv_snd eφ eB0 x y)

end Ring

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The conormal module `I/I²` of a finite-type presentation
`P : Algebra.Generators R S (Fin n)`, viewed as an `S`-module. Here
`I = Ker(MvPolynomial (Fin n) R → S)` is the kernel of the (surjective)
evaluation map associated to `P`. -/
abbrev Conormal {n : ℕ} (P : Algebra.Generators R S (Fin n)) : Type _ :=
  P.toExtension.Cotangent

/-- The free `S`-module `S^{⊕k}` of rank `k`. -/
abbrev FreeModule (S : Type*) [CommRing S] (k : ℕ) : Type _ := Fin k → S

/-- The homotopy identity on `Cotangent` for two maps of extensions `f : E → E'`, `g : E' → E`. -/
private theorem cotangent_id_sub_map_comp {E E' : Algebra.Extension R S}
    (f : E.Hom E') (g : E'.Hom E) :
    (LinearMap.id : E.Cotangent →ₗ[S] E.Cotangent) -
        Algebra.Extension.Cotangent.map g ∘ₗ Algebra.Extension.Cotangent.map f =
      (Algebra.Extension.Hom.id E).sub (g.comp f) ∘ₗ E.cotangentComplex := by
  refine LinearMap.ext fun x => ?_
  simpa only [Algebra.Extension.Cotangent.map_id, Algebra.Extension.Cotangent.map_comp,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    LinearMap.sub_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (Algebra.Extension.Cotangent.map_sub_map
      (Algebra.Extension.Hom.id E) (g.comp f)) x

/-- The homotopy identity on `CotangentSpace` for maps of extensions `f : E → E'`, `g : E' → E`. -/
private theorem cotangentSpace_id_sub_map_comp {E E' : Algebra.Extension R S}
    (f : E.Hom E') (g : E'.Hom E) :
    (LinearMap.id : E.CotangentSpace →ₗ[S] E.CotangentSpace) -
        Algebra.Extension.CotangentSpace.map g ∘ₗ Algebra.Extension.CotangentSpace.map f =
      E.cotangentComplex ∘ₗ (Algebra.Extension.Hom.id E).sub (g.comp f) := by
  refine LinearMap.ext fun x => ?_
  simpa only [Algebra.Extension.CotangentSpace.map_id, Algebra.Extension.CotangentSpace.map_comp,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    LinearMap.sub_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (Algebra.Extension.CotangentSpace.map_sub_map
      (Algebra.Extension.Hom.id E) (g.comp f)) x

/-- **Stacks Tag 00S5 (Lemma 10.134.15).** Let `R → S` be a ring map of finite
type, and let
  `P : Algebra.Generators R S (Fin n)` (with kernel `I`) and
  `Q : Algebra.Generators R S (Fin m)` (with kernel `J`)
be two finite-type presentations of `S` over `R`. Then there is an isomorphism
of `S`-modules
  `I/I² ⊕ S^{⊕m} ≅ J/J² ⊕ S^{⊕n}`. -/
@[stacks 00S5]
theorem conormal_stable_iso [Algebra.FiniteType R S]
    {n m : ℕ} (P : Algebra.Generators R S (Fin n)) (Q : Algebra.Generators R S (Fin m)) :
    Nonempty ((Conormal P × FreeModule S m) ≃ₗ[S] (Conormal Q × FreeModule S n)) := by
  set EP := P.toExtension
  set EQ := Q.toExtension
  -- **The honest Stacks route (00S1 + 00S3).** The naive cotangent complexes
  -- `NL(P) : Cotangent P →[d] CotangentSpace P` and
  -- `NL(Q) : Cotangent Q →[d] CotangentSpace Q` are homotopy-equivalent 2-term
  -- complexes; we obtain the chain maps and homotopies directly from Mathlib's
  -- cotangent-complex functoriality, then apply the elementary block-matrix
  -- lemma `schanuel00S3`.
  -- The two functorial presentation morphisms (both lifting `id_S`).
  let f : EP.Hom EQ := (P.defaultHom Q).toExtensionHom
  let g : EQ.Hom EP := (Q.defaultHom P).toExtensionHom
  -- The chain maps `φ = (φ₁, φ₀) : NL(P) → NL(Q)` and `ψ = (ψ₁, ψ₀)` reversed.
  let φ₁ : EP.Cotangent →ₗ[S] EQ.Cotangent := Algebra.Extension.Cotangent.map f
  let φ₀ : EP.CotangentSpace →ₗ[S] EQ.CotangentSpace := Algebra.Extension.CotangentSpace.map f
  let ψ₁ : EQ.Cotangent →ₗ[S] EP.Cotangent := Algebra.Extension.Cotangent.map g
  let ψ₀ : EQ.CotangentSpace →ₗ[S] EP.CotangentSpace := Algebra.Extension.CotangentSpace.map g
  -- Chain-map identities (`CotangentSpace.map_cotangentComplex`).
  have hφ : φ₀ ∘ₗ EP.cotangentComplex = EQ.cotangentComplex ∘ₗ φ₁ := by
    ext x; exact Algebra.Extension.CotangentSpace.map_cotangentComplex f x
  have hψ : ψ₀ ∘ₗ EQ.cotangentComplex = EP.cotangentComplex ∘ₗ ψ₁ := by
    ext x; exact Algebra.Extension.CotangentSpace.map_cotangentComplex g x
  -- The homotopy operators: `g∘f` and `id_P` both lift `id_S`, so they are
  -- chain-homotopic via `Hom.sub`; same for `f∘g` and `id_Q`. The four
  -- identities come from `Cotangent.map_sub_map` / `CotangentSpace.map_sub_map`,
  -- together with `map_id` and `map_comp`. For the `CotangentSpace` lemmas we
  -- must use `refine LinearMap.ext fun x => ?_` rather than `ext x`: the latter
  -- would fire `TensorProduct.ext` (`CotangentSpace = S ⊗[P.Ring] Ω[P.Ring/R]`)
  -- and introduce a base-ring scalar variable instead of the intended
  -- `CotangentSpace` element. `restrictScalars` is normalized away by
  -- `LinearMap.coe_restrictScalars` (a `rfl`-simp lemma).
  let hA : EP.CotangentSpace →ₗ[S] EP.Cotangent :=
    (Algebra.Extension.Hom.id EP).sub (g.comp f)
  let hB : EQ.CotangentSpace →ₗ[S] EQ.Cotangent :=
    (Algebra.Extension.Hom.id EQ).sub (f.comp g)
  have hA1 := cotangent_id_sub_map_comp f g
  have hA0 := cotangentSpace_id_sub_map_comp f g
  have hB1 := cotangent_id_sub_map_comp g f
  have hB0 := cotangentSpace_id_sub_map_comp g f
  -- Apply Stacks 00S3 (block matrix) to the homotopy equivalence, then identify the
  -- cotangent spaces with the free modules `S^m`, `S^n`.
  obtain ⟨e⟩ :=
    schanuel00S3 EP.cotangentComplex EQ.cotangentComplex φ₁ φ₀ ψ₁ ψ₀ hφ hψ hA hA1 hA0 hB hB1 hB0
  exact ⟨(((LinearEquiv.refl S EP.Cotangent).prodCongr Q.cotangentSpaceBasis.equivFun.symm).trans
    e).trans ((LinearEquiv.refl S EQ.Cotangent).prodCongr P.cotangentSpaceBasis.equivFun)⟩

end NaiveCotangent.Conormal

-- ===== merged from StacksDraft.Ch10.Sec134.Tag065V =====

/-!
# The conormal sequence of a surjection of rings

Let `A → B → C` be ring maps forming a scalar tower, and set `I = ker (A → C)` and
`J = ker (B → C)`. Assume `A → C` is surjective, so that `B → C` is surjective as well.
Writing
  `ι : I/I² → J/J²`,  `δ : J/J² → C ⊗_B Ω[B⁄A]`
for the two natural maps described below, the sequence
  `I/I² --ι--> J/J² --δ--> Ω[B⁄A] ⊗_B B/J --> 0`
is exact; concretely, `im ι = ker δ` and `δ` is surjective.

## Main results

* `exact_mapCotangent_kerCotangentToTensor_and_surjective`: exactness of
  `I/I² → J/J² → C ⊗_B Ω[B⁄A]` at `J/J²`, together with surjectivity of `δ`.
* `range_iota_smul_mem`, `span_iota_eq`, `retraction_exists`: the three ingredients of the
  one nontrivial inclusion `ker δ ⊆ range ι`.

## Implementation notes

The two maps and the conormal modules are Mathlib's.

* For a commutative ring `R` and an ideal `K ⊆ R`, the conormal module `K/K²` is
  `Ideal.Cotangent`, with canonical `R`-linear surjection `Ideal.toCotangent : K → K/K²`.
* `Ideal.mapCotangent` is its functoriality: given ideals `I₁ ⊆ A` and `I₂ ⊆ B`, an
  algebra map `f : A → B` and a proof of `I₁ ≤ Ideal.comap f I₂`, an induced linear map
  `I₁/I₁² → I₂/I₂²`, `x̄ ↦ f x`. Taking `f = Algebra.ofId A B`, `I₁ = I` and `I₂ = J`
  gives the first map `ι`. The side condition `I ≤ Ideal.comap (Algebra.ofId A B) J`
  holds because `A → C` factors through `B`; it is carried as a hypothesis so that
  `Ideal.mapCotangent` is well-formed.
* `Ω[B⁄A] = KaehlerDifferential A B` is the module of Kähler differentials, with
  universal derivation `KaehlerDifferential.D A B`.
* `KaehlerDifferential.kerCotangentToTensor` is the second map
  `δ : J/J² → C ⊗_B Ω[B⁄A]`, `x̄ ↦ 1 ⊗ d_{B/A} x`. Its target is the base change of
  `Ω[B⁄A]` along `B → C`, which is canonically `Ω[B⁄A] ⊗_B B/J`.
* Surjectivity of `A → C` entails surjectivity of `B → C`, and is what makes both halves
  of the conclusion hold.

## Proof outline

Only the inclusion `ker δ ⊆ range ι` is nontrivial: surjectivity of `δ` and the inclusion
`range ι ⊆ ker δ` are immediate. Write `f = algebraMap A B` and `g = algebraMap B C`. The
argument is an elementary, self-contained "retraction derivation" construction, using only
the universal property of `Ω[B⁄A]` and ideal arithmetic.

* Step 1 (`range ι` is a `B`-submodule). `range ι` is by construction an `A`-submodule of
  `J/J²`. In fact it is closed under multiplication by every `b ∈ B`: given `a ∈ I` and
  `b ∈ B`, surjectivity of `A → C` gives `a' ∈ A` with `algebraMap A C a' = g b`, so
  `b - f a' ∈ J`. Since `a ∈ I ⊆ f⁻¹ J` we have `f a ∈ J`, hence `(b - f a')·(f a) ∈ J²`,
  i.e. `̄(b · f a) = ̄(f a' · f a) = ̄(f (a'·a))` in `J/J²`, and `a'·a ∈ I` (as `I` is an
  ideal). Therefore `b · ι(ā) = ι(̄(a'·a)) ∈ range ι`. This is `range_iota_smul_mem`;
  consequently `Submodule.span B (range ι)` has the same underlying set as `range ι`
  (`span_iota_eq`).

* Step 2 (the retraction `ρ`). Let `P := Submodule.span B (range ι)` and
  `N := J.Cotangent ⧸ P`, a `B`-module. We construct a `B`-linear map
  `ρ : C ⊗_B Ω[B⁄A] → N` with `ρ (1 ⊗ d_{B/A} x) = ⟦x̄⟧` for every `x ∈ J`
  (`retraction_exists`):
    - Define `θ : B → N` by `θ b = ⟦ ̄(b - f a_b) ⟧`, where `a_b ∈ A` is any element with
      `algebraMap A C a_b = g b` (it exists by surjectivity of `A → C`); note
      `b - f a_b ∈ J`. This is well defined: another choice `a_b'` differs by an element
      of `I`, and `̄(f(a_b' - a_b)) = ι(̄(a_b'-a_b)) ∈ P`, so the class in `N` is
      unchanged.
    - `θ` is an `A`-derivation `B → N`:
        · additive (choose `a_{b+b'} = a_b + a_{b'}`);
        · kills `A` (`θ (f a) = ⟦̄(f a - f a)⟧ = 0`, choosing `a_{f a} = a`), giving
          `A`-linearity;
        · Leibniz: with `u = b - f a_b, u' = b' - f a_{b'} ∈ J`, choosing
          `a_{bb'} = a_b·a_{b'}`, one has
          `bb' - f a_{bb'} = f a_b · u' + f a_{b'} · u + u u'`
          with `u u' ∈ J²`, and (since `u·u' ∈ J²`) `b·ū' = f a_b · ū'` in `J/J²`; hence
          `θ(bb') = b·θ(b') + b'·θ(b)`, the `B`-action on `N` coming from `J/J²`.
    - By the universal property of Kähler differentials
      (`Derivation.liftKaehlerDifferential`) `θ` factors as a `B`-linear
      `θ̄ : Ω[B⁄A] → N` with `θ̄ (d_{B/A} b) = θ b`.
    - Base changing `θ̄` along `B → C` gives a `B`-linear (indeed `C`-linear)
      `ρ : C ⊗_B Ω[B⁄A] → N` with `ρ (c ⊗ ω) = c • θ̄ ω`; in particular
      `ρ (1 ⊗ d_{B/A} x) = θ̄ (d x) = θ x`. For `x ∈ J`, `g x = 0`, so we may take
      `a_x = 0`, giving `θ x = ⟦x̄⟧`, which is the asserted formula. Here `N` is a
      `C`-module because `J` annihilates `J/J²` hence its quotient `N`, and that is what
      allows the base change of the `B`-linear `θ̄` to a `C`-linear `ρ`.

* Step 3 (conclusion). Take `y ∈ J.Cotangent` with `δ y = 0`. Pick `x ∈ J` with
  `y = J.toCotangent x` (`Ideal.toCotangent_surjective`). Then
  `δ y = 1 ⊗ d_{B/A} x` (`kerCotangentToTensor_toCotangent`), so by Step 2,
  `⟦y⟧ = ρ (δ y) = ρ 0 = 0` in `N`, i.e. `y ∈ P`. By Step 1, `P` and `range ι` have the
  same underlying set, so `y ∈ range ι`.
-/

@[expose] public section

open KaehlerDifferential TensorProduct

/-- Step 1 of the proof outline: `range ι` is closed under scalar multiplication by `B`.

Given `a ∈ I` (so `z = ι(ā) = ̄(f a)`) and `b ∈ B`, surjectivity of `A → C` yields
`a' ∈ A` with `algebraMap A C a' = g b`, hence `b - f a' ∈ J`. Since `f a ∈ J`, we get
`(b - f a')·f a ∈ J²`, so in `J/J²`: `b·z = ̄(b·f a) = ̄(f a' · f a) = ̄(f(a'·a)) = ι(̄(a'·a))`
with `a'·a ∈ I`; thus `b • z ∈ range ι`. -/
theorem range_iota_smul_mem
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hle : RingHom.ker (algebraMap A C) ≤
      Ideal.comap (Algebra.ofId A B) (RingHom.ker (algebraMap B C)))
    (b : B)
    (z : (RingHom.ker (algebraMap B C)).Cotangent)
    (hz : z ∈ Set.range (Ideal.mapCotangent (RingHom.ker (algebraMap A C))
      (RingHom.ker (algebraMap B C)) (Algebra.ofId A B) hle)) :
    b • z ∈ Set.range (Ideal.mapCotangent (RingHom.ker (algebraMap A C))
      (RingHom.ker (algebraMap B C)) (Algebra.ofId A B) hle) := by
  set f := algebraMap A B with hf
  set I := RingHom.ker (algebraMap A C) with hI
  set J := RingHom.ker (algebraMap B C) with hJ
  -- `z = ι w` for some `w : I.Cotangent`, and `w = I.toCotangent a`.
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective I w
  rw [Ideal.mapCotangent_toCotangent]
  -- obtain `a'` with `algebraMap A C a' = g b`.
  obtain ⟨a', ha'⟩ := hAC (algebraMap B C b)
  -- `b - f a' ∈ J`.
  have hbJ : b - f a' ∈ J := by
    rw [hJ, RingHom.mem_ker, map_sub]
    have : (algebraMap B C) (f a') = (algebraMap A C) a' := by
      rw [hf, ← IsScalarTower.algebraMap_apply]
    rw [this, ha', sub_self]
  -- `f a ∈ J`.
  have hfaJ : f a ∈ J := by
    have := hle a.property
    rwa [Ideal.mem_comap, Algebra.ofId_apply, ← hf] at this
  -- the witness: `ι (I.toCotangent (a' • a))`.
  refine ⟨I.toCotangent (a' • a), ?_⟩
  rw [Ideal.mapCotangent_toCotangent, ← LinearMap.CompatibleSMul.map_smul J.toCotangent b,
    Ideal.toCotangent_eq]
  simp only [SetLike.val_smul, smul_eq_mul]
  -- goal: `(Algebra.ofId A B) (a' * a) - b * (Algebra.ofId A B) a ∈ J^2`.
  simp only [Algebra.ofId_apply, ← hf, map_mul]
  rw [show f a' * f a - b * f a = -((b - f a') * f a) by ring, sq]
  exact neg_mem (Ideal.mul_mem_mul hbJ hfaJ)

/-- The `B`-span of `range ι` has the same underlying set as `range ι` itself.

Indeed `range ι` is an additive subgroup, being the image of an `A`-linear map, and it is
closed under multiplication by `B` by `range_iota_smul_mem`; a set with these closure
properties equals its own `B`-span. -/
theorem span_iota_eq
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hle : RingHom.ker (algebraMap A C) ≤
      Ideal.comap (Algebra.ofId A B) (RingHom.ker (algebraMap B C))) :
    (Submodule.span B (Set.range (Ideal.mapCotangent (RingHom.ker (algebraMap A C))
        (RingHom.ker (algebraMap B C)) (Algebra.ofId A B) hle)) :
        Set (RingHom.ker (algebraMap B C)).Cotangent)
      = Set.range (Ideal.mapCotangent (RingHom.ker (algebraMap A C))
        (RingHom.ker (algebraMap B C)) (Algebra.ofId A B) hle) := by
  set ι := Ideal.mapCotangent (RingHom.ker (algebraMap A C))
    (RingHom.ker (algebraMap B C)) (Algebra.ofId A B) hle with hι
  let S : Submodule B (RingHom.ker (algebraMap B C)).Cotangent :=
    { carrier := Set.range ι
      add_mem' := by
        rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u + v, map_add ι u v⟩
      zero_mem' := ⟨0, map_zero ι⟩
      smul_mem' := fun b z hz => range_iota_smul_mem A B C hAC hle b z hz }
  have hcarrier : (S : Set (RingHom.ker (algebraMap B C)).Cotangent) = Set.range ι := rfl
  have hspan : Submodule.span B (Set.range ι) = S := by
    rw [← hcarrier]; exact Submodule.span_eq S
  rw [hspan, hcarrier]

section Retraction

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- If `a ∈ A` lifts `g b ∈ C`, then `b - f a` lies in `J = ker (B → C)`. -/
theorem sub_algebraMap_mem_ker {b : B} {a : A} (ha : algebraMap A C a = algebraMap B C b) :
    b - algebraMap A B a ∈ RingHom.ker (algebraMap B C) := by
  rw [RingHom.mem_ker, map_sub, ← IsScalarTower.algebraMap_apply, ha, sub_self]

/-- The class of `b - f a_b` in `J/J²` is additive in the pair `(b, a_b)`. -/
theorem toCotangent_sub_algebraMap_add {b b' : B} {a a' : A}
    (ha : algebraMap A C a = algebraMap B C b) (ha' : algebraMap A C a' = algebraMap B C b') :
    (RingHom.ker (algebraMap B C)).toCotangent
        ⟨b + b' - algebraMap A B (a + a'), sub_algebraMap_mem_ker (by simp [ha, ha'])⟩ =
      (RingHom.ker (algebraMap B C)).toCotangent ⟨b - algebraMap A B a, sub_algebraMap_mem_ker ha⟩ +
        (RingHom.ker (algebraMap B C)).toCotangent
          ⟨b' - algebraMap A B a', sub_algebraMap_mem_ker ha'⟩ := by
  rw [← map_add (RingHom.ker (algebraMap B C)).toCotangent]
  congr 1
  ext
  simp only [map_add, Submodule.coe_add]
  ring

/-- The class of `b - f a_b` in `J/J²` is `A`-linear in the pair `(b, a_b)`. -/
theorem toCotangent_sub_algebraMap_smul {b : B} {a : A} (r : A)
    (ha : algebraMap A C a = algebraMap B C b) :
    (RingHom.ker (algebraMap B C)).toCotangent
        ⟨r • b - algebraMap A B (r * a), sub_algebraMap_mem_ker
          (by rw [map_mul, ha, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply])⟩ =
      r • (RingHom.ker (algebraMap B C)).toCotangent
        ⟨b - algebraMap A B a, sub_algebraMap_mem_ker ha⟩ := by
  rw [← LinearMap.map_smul_of_tower]
  congr 1
  ext
  simp only [map_mul, Algebra.smul_def, Submodule.coe_smul_of_tower]
  ring

/-- The class of `b - f a_b` in `J/J²` satisfies the Leibniz rule in the pair `(b, a_b)`. -/
theorem toCotangent_sub_algebraMap_mul {b b' : B} {a a' : A}
    (ha : algebraMap A C a = algebraMap B C b) (ha' : algebraMap A C a' = algebraMap B C b') :
    (RingHom.ker (algebraMap B C)).toCotangent
        ⟨b * b' - algebraMap A B (a * a'), sub_algebraMap_mem_ker (by simp [ha, ha'])⟩ =
      b • (RingHom.ker (algebraMap B C)).toCotangent
          ⟨b' - algebraMap A B a', sub_algebraMap_mem_ker ha'⟩ +
        b' • (RingHom.ker (algebraMap B C)).toCotangent
          ⟨b - algebraMap A B a, sub_algebraMap_mem_ker ha⟩ := by
  rw [← map_smul, ← map_smul, ← map_add, Ideal.toCotangent_eq]
  have hfac : b * b' - algebraMap A B (a * a') - (b * (b' - algebraMap A B a') +
      b' * (b - algebraMap A B a)) = -((b - algebraMap A B a) * (b' - algebraMap A B a')) := by
    rw [map_mul]; ring
  simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, hfac, sq]
  exact neg_mem (Ideal.mul_mem_mul (sub_algebraMap_mem_ker ha) (sub_algebraMap_mem_ker ha'))

/-- Modulo any `P ⊇ range ι`, the class of `b - f a_b` does not depend on the lift `a_b`. -/
theorem mk_toCotangent_sub_algebraMap_eq
    (hle : RingHom.ker (algebraMap A C) ≤
      Ideal.comap (Algebra.ofId A B) (RingHom.ker (algebraMap B C)))
    {P : Submodule B (RingHom.ker (algebraMap B C)).Cotangent}
    (hP : Set.range (Ideal.mapCotangent (RingHom.ker (algebraMap A C))
      (RingHom.ker (algebraMap B C)) (Algebra.ofId A B) hle) ⊆ P) {b : B} {a a' : A}
    (ha : algebraMap A C a = algebraMap B C b) (ha' : algebraMap A C a' = algebraMap B C b) :
    (Submodule.Quotient.mk ((RingHom.ker (algebraMap B C)).toCotangent
        ⟨b - algebraMap A B a, sub_algebraMap_mem_ker ha⟩) : _ ⧸ P) =
      Submodule.Quotient.mk ((RingHom.ker (algebraMap B C)).toCotangent
        ⟨b - algebraMap A B a', sub_algebraMap_mem_ker ha'⟩) := by
  have haa : a' - a ∈ RingHom.ker (algebraMap A C) := by
    rw [RingHom.mem_ker, map_sub, ha, ha', sub_self]
  have h := hP ⟨(RingHom.ker (algebraMap A C)).toCotangent ⟨a' - a, haa⟩, rfl⟩
  rw [Ideal.mapCotangent_toCotangent, SetLike.mem_coe] at h
  rw [Submodule.Quotient.eq, ← map_sub]
  convert h using 2
  ext
  simp only [Submodule.coe_sub, Algebra.ofId_apply, map_sub]
  ring

/-- The retraction derivation `θ : B → J.Cotangent ⧸ P`, `θ b = ⟦̄(b - f a_b)⟧`, for any
`P ⊇ range ι`; it sends `x ∈ J` to `⟦x̄⟧`. -/
theorem exists_derivation_mk_toCotangent (hAC : Function.Surjective (algebraMap A C))
    (hle : RingHom.ker (algebraMap A C) ≤
      Ideal.comap (Algebra.ofId A B) (RingHom.ker (algebraMap B C)))
    {P : Submodule B (RingHom.ker (algebraMap B C)).Cotangent}
    (hP : Set.range (Ideal.mapCotangent (RingHom.ker (algebraMap A C))
      (RingHom.ker (algebraMap B C)) (Algebra.ofId A B) hle) ⊆ P) :
    ∃ θ : Derivation A B ((RingHom.ker (algebraMap B C)).Cotangent ⧸ P),
      ∀ x : RingHom.ker (algebraMap B C),
        θ x = Submodule.Quotient.mk ((RingHom.ker (algebraMap B C)).toCotangent x) := by
  choose cb hcb using fun b : B => hAC (algebraMap B C b)
  have hθ := fun b a (ha : algebraMap A C a = algebraMap B C b) ↦
    mk_toCotangent_sub_algebraMap_eq hle hP (hcb b) ha
  refine ⟨Derivation.mk'
    { toFun := fun b ↦ Submodule.Quotient.mk ((RingHom.ker (algebraMap B C)).toCotangent
        ⟨b - algebraMap A B (cb b), sub_algebraMap_mem_ker (hcb b)⟩)
      map_add' := fun b b' ↦ ?_
      map_smul' := fun r b ↦ ?_ } fun b b' ↦ ?_, fun x ↦ ?_⟩
  · rw [hθ _ (cb b + cb b') (by simp [hcb]), toCotangent_sub_algebraMap_add (hcb b) (hcb b'),
      Submodule.Quotient.mk_add]
  · rw [hθ _ (r * cb b) (by simp [hcb, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]),
      toCotangent_sub_algebraMap_smul r (hcb b)]
    rfl
  · show Submodule.Quotient.mk _ = _
    rw [hθ _ (cb b * cb b') (by simp [hcb]), toCotangent_sub_algebraMap_mul (hcb b) (hcb b'),
      Submodule.Quotient.mk_add]
    rfl
  · show Submodule.Quotient.mk _ = _
    rw [hθ _ 0 (by simpa using x.2.symm)]
    congr 2
    ext
    simp

end Retraction

/-- `B → C` is surjective if `A → C` is and factors through `B`. -/
private theorem surjective_algebraMap_of_tower (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C)) : Function.Surjective (algebraMap B C) := by
  rw [IsScalarTower.algebraMap_eq A B C, RingHom.coe_comp] at hAC
  exact hAC.of_comp

/-- Step 2 of the proof outline: the retraction `ρ : C ⊗_B Ω[B⁄A] → (J.Cotangent ⧸ P)`
with `ρ (δ (J.toCotangent x)) = ⟦J.toCotangent x⟧` for `x ∈ J`. Here `P` is any submodule
containing `range ι`.

The map is the base change along `B → C` of the lift to `Ω[B⁄A]` of the retraction
derivation `θ : B → N`, `θ b = ⟦̄(b - f a_b)⟧`, where `a_b` is a lift of `g b` along the
surjection `A → C`. For `x ∈ J` one may take `a_x = 0`, whence `ρ(1 ⊗ d x) = θ x = ⟦x̄⟧`. -/
theorem retraction_exists
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hle : RingHom.ker (algebraMap A C) ≤
      Ideal.comap (Algebra.ofId A B) (RingHom.ker (algebraMap B C)))
    (P : Submodule B (RingHom.ker (algebraMap B C)).Cotangent)
    (hP : Set.range (Ideal.mapCotangent (RingHom.ker (algebraMap A C))
      (RingHom.ker (algebraMap B C)) (Algebra.ofId A B) hle) ⊆ P) :
    ∃ ρ : TensorProduct B C (Ω[B⁄A]) →ₗ[B] ((RingHom.ker (algebraMap B C)).Cotangent ⧸ P),
      ∀ x : (RingHom.ker (algebraMap B C)),
        ρ (KaehlerDifferential.kerCotangentToTensor A B C
            ((RingHom.ker (algebraMap B C)).toCotangent x))
          = Submodule.Quotient.mk ((RingHom.ker (algebraMap B C)).toCotangent x) := by
  have hBC := surjective_algebraMap_of_tower A B C hAC
  let J := RingHom.ker (algebraMap B C)
  let N := J.Cotangent ⧸ P
  -- N is annihilated by J, hence is a `C`-module via `C ≃ B/J`.
  have htor : Module.IsTorsionBySet B N ↑J := by
    intro n j
    refine Quotient.inductionOn' n fun m => ?_
    show Submodule.Quotient.mk (j.val • m) = 0
    rw [show j.val • m = (0 : J.Cotangent) from
      Ideal.isTorsionBySet_cotangent J (x := m) (a := j), Submodule.Quotient.mk_zero]
  let : Module (B ⧸ J) N := htor.module
  let e : (B ⧸ J) ≃+* C := RingHom.quotientKerEquivOfSurjective hBC
  let : Module C N := Module.compHom N (e.symm.toRingHom)
  have hkey : ∀ b : B, e (Ideal.Quotient.mk J b) = algebraMap B C b := fun b => rfl
  have hstBC : IsScalarTower B C N := by
    apply IsScalarTower.of_algebraMap_smul
    intro b n
    show e.symm (algebraMap B C b) • n = b • n
    rw [← hkey b, RingEquiv.symm_apply_apply]
    have : (Ideal.Quotient.mk J b) • n = (algebraMap B (B⧸J) b) • n := by
      rw [Ideal.Quotient.algebraMap_eq]
    rw [this, algebraMap_smul]
  obtain ⟨θ, hθ⟩ := exists_derivation_mk_toCotangent hAC hle hP
  refine ⟨(LinearMap.liftBaseChange C θ.liftKaehlerDifferential).restrictScalars B, fun x ↦ ?_⟩
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent, LinearMap.restrictScalars_apply,
    LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D, hθ]

/-- The sequence `I/I² → J/J² → Ω[B⁄A] ⊗_B B/J` is exact at `J/J²`. -/
theorem exact_mapCotangent_kerCotangentToTensor
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hle : RingHom.ker (algebraMap A C) ≤
      Ideal.comap (Algebra.ofId A B) (RingHom.ker (algebraMap B C))) :
    Function.Exact
      (Ideal.mapCotangent (RingHom.ker (algebraMap A C)) (RingHom.ker (algebraMap B C))
        (Algebra.ofId A B) hle)
      (KaehlerDifferential.kerCotangentToTensor A B C) := by
  intro y
  constructor
  · -- HARD direction: `δ y = 0 ⇒ y ∈ range ι`.  See file-header proof sketch.
    intro hy
    -- Set `P := span_B (range ι)` and `N := J.Cotangent ⧸ P`.
    set P : Submodule B (RingHom.ker (algebraMap B C)).Cotangent :=
      Submodule.span B (Set.range (Ideal.mapCotangent (RingHom.ker (algebraMap A C))
        (RingHom.ker (algebraMap B C)) (Algebra.ofId A B) hle))
    -- STEP 2: obtain the retraction ρ.
    obtain ⟨ρ, hρ⟩ := retraction_exists A B C hAC hle P Submodule.subset_span
    -- Pick a representative `x ∈ J` for `y`.
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker (algebraMap B C)) y
    -- STEP 3: `⟦y⟧ = ρ (δ y) = ρ 0 = 0` in `N`, so `y ∈ P`; then `y ∈ range ι` by STEP 1'.
    have hquot : Submodule.Quotient.mk
        ((RingHom.ker (algebraMap B C)).toCotangent x) = (0 : _ ⧸ P) := by
      rw [← hρ x, hy, map_zero]
    rw [← span_iota_eq A B C hAC hle]
    exact (Submodule.Quotient.mk_eq_zero P).mp hquot
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker (algebraMap A C)) x
    rw [Ideal.mapCotangent_toCotangent, KaehlerDifferential.kerCotangentToTensor_toCotangent]
    simp

/-- **Stacks Tag 065V (Lemma 10.134.7).** Let `A → B → C` be ring maps with `A → C`
surjective, and set `I = ker (A → C)` and `J = ker (B → C)`. Then the sequence
`I/I² → J/J² → Ω[B⁄A] ⊗_B B/J → 0` is exact: the image of `Ideal.mapCotangent` is the
kernel of `KaehlerDifferential.kerCotangentToTensor`, and the latter is surjective. -/
@[stacks 065V, ega "0 20.5.12" "(i), special case"]
theorem exact_mapCotangent_kerCotangentToTensor_and_surjective
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hle : RingHom.ker (algebraMap A C) ≤
      Ideal.comap (Algebra.ofId A B) (RingHom.ker (algebraMap B C))) :
    Function.Exact
      (Ideal.mapCotangent (RingHom.ker (algebraMap A C)) (RingHom.ker (algebraMap B C))
        (Algebra.ofId A B) hle)
      (KaehlerDifferential.kerCotangentToTensor A B C) ∧
    Function.Surjective (KaehlerDifferential.kerCotangentToTensor A B C) := by
  have hBC := surjective_algebraMap_of_tower A B C hAC
  -- `Ω[C⁄A]` is trivial since `A → C` is surjective.
  have hsub : Subsingleton (Ω[C⁄A]) := KaehlerDifferential.subsingleton_of_surjective A C hAC
  refine ⟨exact_mapCotangent_kerCotangentToTensor A B C hAC hle, ?_⟩
  -- Surjectivity of `δ`.
  rw [← LinearMap.range_eq_top, KaehlerDifferential.range_kerCotangentToTensor A B C hBC]
  ext x
  simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, Submodule.mem_top, iff_true]
  exact Subsingleton.elim _ _
