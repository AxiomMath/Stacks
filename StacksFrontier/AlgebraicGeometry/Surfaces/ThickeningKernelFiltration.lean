module

public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodMultiplicative
public import StacksFrontier.AlgebraicGeometry.Surfaces.RestrictedNegativeTwistSections

/-!
# The filtration of one infinitesimal thickening by the smaller ones

Let `D` be an ideal sheaf on a scheme `X` with infinitesimal thickenings
`Eₙ = (D ^ (n + 1)).subscheme`. Fix one of them, `E_N`, and filter its ring of global functions
by the ideals

`Kₘ = ker (Γ(E_N, 𝒪) ⟶ Γ(Eₘ, 𝒪))`,  `m ≤ N`,

the functions on `E_N` vanishing on the smaller thickening `Eₘ`. These are the global sections of
the ideal sheaf that cuts `Eₘ` out *inside* `E_N`, that is an ideal sheaf of the ring sheaf
`𝒪_{E_N}` and not of `𝒪_X`.

## Why the ambient thickening has to be fixed

`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodFiltration` filters the inverse limit
`A = lim Γ(Eₙ, 𝒪)` and is already known to be multiplicative, unconditionally
(`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodFiltration_mul_le`). What that
filtration cannot express is the *symbol* of a product. The symbol of an element of `Iₘ₊₁` is its
projection to `Γ(Eₘ₊₁, 𝒪)`, and the symbols of two elements of different filtration steps
therefore live on two different thickenings, between which there is no map in the direction
needed: restriction goes from the larger thickening to the smaller one, so `Γ(Eₘ₊₁, 𝒪)` and
`Γ(Eₙ₊₁, 𝒪)` cannot be multiplied inside `Γ(Eₘ₊ₙ₊₂, 𝒪)`. Fixing one ambient thickening `E_N`
large enough to carry all the degrees in play is what makes the product of two symbols a
well-formed expression at all, and that is what this file sets up.

The same obstruction is the reason the identification of the graded pieces cannot be read on
`X`: the unit `ℐ_{D ^ m} ⟶ i_*i^*ℐ_{D ^ m}` is only *locally* surjective, so `Γ(X, ℐ_{D ^ m})`
need not surject onto `Γ(E, i^*ℐ_{D ^ m})` — the failure the `H¹` arguments of this chapter exist
to handle. Every statement below is therefore proved on the thickenings themselves, by the sheaf
condition over an affine cover of `X`
(`AlgebraicGeometry.Scheme.IdealSheafData.mul_eq_zero_of_appTop_inclusion_eq_zero`), never by
lifting a section to `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel` — the ideal `Kₘ` of functions on
  `E_N` vanishing on `Eₘ`.
* `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts` — the symbols of the
  products of a function vanishing on `E` with a function vanishing on `Eₚ`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel_mul_le` — **the filtration is
  multiplicative**: `Kₘ · Kₙ ≤ K_{m+n+1}`, with no hypothesis on `D` at all. The index shift is
  the one in `thickening`: `Kₘ` is cut out by `D ^ (m + 1)`, so the product of `D ^ (m + 1)` and
  `D ^ (n + 1)` is `D ^ (m + n + 2)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.sub_mul_sub_mem_thickeningKernel` — **the product
  descends to the graded pieces**: changing either factor by one filtration step changes the
  product by one step of the sum, so multiplication induces a pairing
  `Kₘ / Kₘ₊₁ × Kₙ / Kₙ₊₁ ⟶ K_{m+n+1} / K_{m+n+2}`.
* `AlgebraicGeometry.Scheme.IdealSheafData.surjective_thickeningRestrictionLE` — restriction
  between arbitrary thickenings is surjective when the successive ones are.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_gradedSectionsHom_eq_of_mem_thickeningKernel`
  and `exists_mem_thickeningKernel_gradedSectionsHom` — **the graded piece of the ambient
  filtration is the sections of the twist**: for an effective Cartier divisor, restriction to
  `Eₘ₊₁` identifies `Kₘ / Kₘ₊₁` with the image of
  `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom`, that is with
  `Γ(E, i^*ℐ_{D ^ (m + 1)})`.
* `AlgebraicGeometry.Scheme.IdealSheafData.mul_eq_mul_of_thickeningRestrictionLE_eq` and
  `exists_gradedSectionsHom_eq_mul` — **the pairing of the graded pieces is an honest function
  of the two symbols.** Read in the ambient thickening `E_{m+n+2}` — one step beyond the degree
  of the product — the error term of `sub_mul_sub_mem_thickeningKernel` lies in `K_{m+n+2}`,
  which is `⊥`; so the product of a lift of a degree-`m` symbol with a lift of a degree-`n` one
  does not depend on the lifts at all, and is itself the symbol of a global section of
  `𝒪_X(-D ^ (m + n + 2))|_E`.
* `AlgebraicGeometry.Scheme.IdealSheafData`
  `.formalNeighborhoodFiltration_le_mul_sup_of_thickeningKernel_le` — **the inverse limit drops
  out of the degree-one generation problem.** The input `Iₙ₊₁ ⊆ I₁ Iₙ + Iₙ₊₂` that
  `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofExceptionalCurve` still
  asks for follows, when the transition maps are surjective, from the single statement
  `K_{p+1} ≤ K₀ · K_p` inside `Γ(E_{p+2}, 𝒪)` — one ring of functions on one thickening, with
  no inverse limit, no symbol and no twist in it.
* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel_le_mul_of_mem_closure` — **and the
  thickening drops out too.** That single statement follows in turn from degree-one generation
  of the symbols: from every global section of `𝒪_X(-D ^ (p + 2))|_E` being a finite sum of
  members of `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts`. Neither
  the rings of functions on the thickenings nor the ideal product `K₀ · K_p` occurs in that
  hypothesis.

## What this does not give, and where the rest is

Degree-one generation of the symbols is not proved here, and neither is `K_{p+1} ≤ K₀ · K_p`.
Over an affine open of `X` the latter is the triviality `I^{p+1} = I · I^p + I^{p+2}`; what it
asserts globally is that a *global* function on `E_{p+2}` vanishing on `E_{p+1}` is a finite sum
of products of global functions, and that is the surjectivity of
`H⁰(𝐏¹, 𝒪(1)) ⊗ H⁰(𝐏¹, 𝒪(p + 1)) ⟶ H⁰(𝐏¹, 𝒪(p + 2))` once the graded pieces are identified with
those spaces *compatibly with multiplication*. What the results above supply is the frame: the
pairing of the graded pieces is a function of the symbols, and degree-one generation of it is all
that is wanted. Of the identification, the half naming the pairing is proved downstream — the
pairing of `sub_mul_sub_mem_thickeningKernel` is
`Stacks.Divisors.restrictedIdealMulSections`, by
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections` in
`StacksFrontier/AlgebraicGeometry/Surfaces/GradedSectionsLocal.lean`, which also places those
products in `gradedSectionsDegreeOneProducts`. The other half is proved in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistMultiplicative.lean`: the
per-degree isomorphisms `i^*ℐ_{D ^ m} ≅ 𝒪_{𝐏¹}(m)` of
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf` are a per-degree choice of a Picard
class and carry no cross-degree information, and they are *not* made compatible; instead the
isomorphism in the degree of a product is assembled out of the two factors' choices, through
Tag 01CD and Equation 01MO, and is multiplicative by construction.
Nothing here carries a `@[stacks]` attribute: Tag 0C2K asserts the structure of `A`, not this
step of its proof.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### The filtration of a fixed thickening by the smaller ones -/

/-- **The functions on the thickening `E_N` vanishing on the smaller thickening `Eₘ`.** This is
the ideal of global sections of the ideal sheaf cutting `Eₘ` out inside `E_N`; it is an ideal of
`Γ(E_N, 𝒪)`, not of `Γ(X, 𝒪_X)`. -/
public def thickeningKernel (D : X.IdealSheafData) {m N : ℕ} (h : m ≤ N) :
    Ideal Γ(thickening D N, ⊤) :=
  RingHom.ker (thickeningRestrictionLE D h)

public theorem mem_thickeningKernel_iff (D : X.IdealSheafData) {m N : ℕ} (h : m ≤ N)
    (u : Γ(thickening D N, ⊤)) :
    u ∈ thickeningKernel D h ↔ thickeningRestrictionLE D h u = 0 :=
  RingHom.mem_ker

/-- The filtration decreases: vanishing on a larger thickening is the stronger condition. -/
public theorem thickeningKernel_le (D : X.IdealSheafData) {m m' N : ℕ} (hmm' : m ≤ m')
    (h : m' ≤ N) : thickeningKernel D h ≤ thickeningKernel D (hmm'.trans h) := by
  intro u hu
  rw [mem_thickeningKernel_iff] at hu ⊢
  rw [← thickeningRestrictionLE_comp D hmm' h, hu, map_zero]

/-- Nothing on `E_N` vanishes on `E_N` except zero. -/
public theorem thickeningKernel_self (D : X.IdealSheafData) (N : ℕ) :
    thickeningKernel D (le_refl N) = ⊥ := by
  refine le_antisymm (fun u hu ↦ ?_) bot_le
  rw [mem_thickeningKernel_iff, thickeningRestrictionLE_self] at hu
  exact hu

/-! ### Multiplicativity -/

/-- **The filtration of a fixed thickening by the smaller ones is multiplicative.**

`Kₘ · Kₙ ≤ K_{m+n+1}`: a function on `E_N` vanishing on `Eₘ` times one vanishing on `Eₙ`
vanishes on `E_{m+n+1}`. There is no hypothesis on `D` or on `X`: the two factors restrict to
sections of `D ^ (m + 1)` and of `D ^ (n + 1)` over every affine open, whose product lies in
`D ^ (m + n + 2)`, which is what cuts out `E_{m+n+1}`.

Unlike `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodFiltration_mul_le`, which says
the same thing about the inverse limit, both factors and the product live in **one** ring here,
so this is the form in which a symbol of a product can be written down. -/
public theorem thickeningKernel_mul_le (D : X.IdealSheafData) {m n N : ℕ} (hm : m ≤ N)
    (hn : n ≤ N) (h : m + n + 1 ≤ N) :
    thickeningKernel D hm * thickeningKernel D hn ≤ thickeningKernel D h := by
  have hmp : m ≤ m + n + 1 := by omega
  have hnp : n ≤ m + n + 1 := by omega
  rw [Ideal.mul_le]
  intro u hu v hv
  rw [mem_thickeningKernel_iff] at hu hv ⊢
  rw [map_mul]
  refine mul_eq_zero_of_appTop_inclusion_eq_zero (D ^ (m + 1)) (D ^ (n + 1))
    (D ^ (m + n + 1 + 1)) (pow_succ_le_pow_succ D hmp) (pow_succ_le_pow_succ D hnp)
    (ideal_pow_mul_ideal_pow_le D m n) ?_ ?_
  · change thickeningRestrictionLE D hmp (thickeningRestrictionLE D h u) = 0
    rw [thickeningRestrictionLE_comp D hmp h]
    exact hu
  · change thickeningRestrictionLE D hnp (thickeningRestrictionLE D h v) = 0
    rw [thickeningRestrictionLE_comp D hnp h]
    exact hv

/-- `AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel_mul_le` with the index of the
product a free variable and an equation, rather than the term `m + n + 1`.

A consumer whose target index is `m + n + 2` and whose factors sit in steps `m + 1` and `n`
would instead ask the elaborator to identify `m + 1 + n + 1` with `m + n + 2`, which is not a
definitional equality of `Nat` for variable `n`, and elaboration then unfolds `thickeningKernel`
through `AlgebraicGeometry.Scheme.IdealSheafData.inclusion` until the heartbeats run out. -/
public theorem thickeningKernel_mul_le_of_eq (D : X.IdealSheafData) {m n p N : ℕ} (hm : m ≤ N)
    (hn : n ≤ N) (hp : p ≤ N) (e : p = m + n + 1) :
    thickeningKernel D hm * thickeningKernel D hn ≤ thickeningKernel D hp := by
  subst e
  exact thickeningKernel_mul_le D hm hn hp

/-- **The product descends to the graded pieces.** Changing a factor by one step of the
filtration changes the product by one step of the sum, so multiplication on `Γ(E_N, 𝒪)` induces
a pairing

`Kₘ / Kₘ₊₁ × Kₙ / Kₙ₊₁ ⟶ K_{m+n+1} / K_{m+n+2}`

on the associated graded of the filtration. This is the statement in which "the symbol of a
product is the product of the symbols" becomes well formed. -/
public theorem sub_mul_sub_mem_thickeningKernel (D : X.IdealSheafData) {m n N : ℕ} (hm : m ≤ N)
    (hn : n ≤ N) (hm1 : m + 1 ≤ N) (hn1 : n + 1 ≤ N) (h : m + n + 2 ≤ N)
    {u₁ u₂ v₁ v₂ : Γ(thickening D N, ⊤)} (hu₂ : u₂ ∈ thickeningKernel D hm)
    (hv₁ : v₁ ∈ thickeningKernel D hn) (hu : u₁ - u₂ ∈ thickeningKernel D hm1)
    (hv : v₁ - v₂ ∈ thickeningKernel D hn1) :
    u₁ * v₁ - u₂ * v₂ ∈ thickeningKernel D h := by
  have hleft : (u₁ - u₂) * v₁ ∈ thickeningKernel D h :=
    thickeningKernel_mul_le_of_eq D hm1 hn h (by omega) (Ideal.mul_mem_mul hu hv₁)
  have hright : u₂ * (v₁ - v₂) ∈ thickeningKernel D h :=
    thickeningKernel_mul_le_of_eq D hm hn1 h (by omega) (Ideal.mul_mem_mul hu₂ hv)
  have hsum : u₁ * v₁ - u₂ * v₂ = (u₁ - u₂) * v₁ + u₂ * (v₁ - v₂) := by ring
  rw [hsum]
  exact Ideal.add_mem _ hleft hright

/-- A filtration step indexed by the ambient thickening itself is zero, however the inequality
`m ≤ N` was proved: only `0` vanishes on `E_N` inside `Γ(E_N, 𝒪)`. -/
public theorem thickeningKernel_eq_bot (D : X.IdealSheafData) {m N : ℕ} (h : m ≤ N)
    (h' : N ≤ m) : thickeningKernel D h = ⊥ := by
  obtain rfl := le_antisymm h h'
  exact thickeningKernel_self D m

/-- **At the ambient thickening `E_{m+n+2}` the product of two filtration steps depends on
nothing but the symbols of its factors.** Two functions vanishing on `Eₘ` that agree on `E_{m+1}`
and two vanishing on `Eₙ` that agree on `E_{n+1}` have *equal* products — not merely products
agreeing modulo the next filtration step.

This is `AlgebraicGeometry.Scheme.IdealSheafData.sub_mul_sub_mem_thickeningKernel` read at the
one ambient index where its conclusion is an equality: the error term lies in `K_{m+n+2}`, and
`K_{m+n+2}` is `⊥` inside `Γ(E_{m+n+2}, 𝒪)`. Choosing the ambient thickening exactly one step
beyond the degree of the product is therefore what turns the induced pairing of the graded
pieces into an honest function of the two symbols, with no quotient taken. -/
public theorem mul_eq_mul_of_thickeningRestrictionLE_eq (D : X.IdealSheafData) {m n : ℕ}
    (hm : m ≤ m + n + 1 + 1) (hn : n ≤ m + n + 1 + 1) (hm1 : m + 1 ≤ m + n + 1 + 1)
    (hn1 : n + 1 ≤ m + n + 1 + 1) {u u' v v' : Γ(thickening D (m + n + 1 + 1), ⊤)}
    (hu' : u' ∈ thickeningKernel D hm) (hv : v ∈ thickeningKernel D hn)
    (heu : thickeningRestrictionLE D hm1 u = thickeningRestrictionLE D hm1 u')
    (hev : thickeningRestrictionLE D hn1 v = thickeningRestrictionLE D hn1 v') :
    u * v = u' * v' := by
  have h2 : m + n + 2 ≤ m + n + 1 + 1 := by omega
  have hmem := sub_mul_sub_mem_thickeningKernel D hm hn hm1 hn1 h2 (u₁ := u) (v₂ := v') hu' hv
    (by rw [mem_thickeningKernel_iff, map_sub, heu, sub_self])
    (by rw [mem_thickeningKernel_iff, map_sub, hev, sub_self])
  rw [thickeningKernel_eq_bot D h2 (by omega), Ideal.mem_bot] at hmem
  exact sub_eq_zero.1 hmem

/-! ### Restriction between arbitrary thickenings -/

/-- **Restriction between arbitrary thickenings is surjective when the successive restrictions
are.** -/
public theorem surjective_thickeningRestrictionLE (D : X.IdealSheafData)
    (hsurj : ∀ j, Function.Surjective (thickeningRestriction D j)) {i j : ℕ} (h : i ≤ j) :
    Function.Surjective (thickeningRestrictionLE D h) := by
  induction j, h using Nat.le_induction with
  | base => exact fun a ↦ ⟨a, thickeningRestrictionLE_self D i a⟩
  | succ k hik ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨c, hc⟩ := hsurj k b
    exact ⟨c, by rw [← thickeningRestrictionLE_comp D hik (Nat.le_succ k),
      thickeningRestrictionLE_succ, hc, hb]⟩

/-! ### The graded pieces are the sections of the twists -/

/-- Restriction to `Eₘ₊₁` carries `Kₘ` into the kernel of `Γ(Eₘ₊₁, 𝒪) ⟶ Γ(Eₘ, 𝒪)`: restricting
further to `Eₘ` is restricting to `Eₘ`, which kills `Kₘ`. -/
public theorem thickeningRestrictionLE_mem_ker (D : X.IdealSheafData) {m N : ℕ} (hm1 : m + 1 ≤ N)
    {u : Γ(thickening D N, ⊤)} (hu : u ∈ thickeningKernel D ((Nat.le_succ m).trans hm1)) :
    thickeningRestrictionLE D hm1 u ∈ RingHom.ker (thickeningRestriction D m) := by
  rw [mem_thickeningKernel_iff] at hu
  rw [RingHom.mem_ker, ← thickeningRestrictionLE_succ,
    thickeningRestrictionLE_comp D (Nat.le_succ m) hm1]
  exact hu

/-- The kernel of restriction to `Eₘ₊₁` is `Kₘ₊₁`, by the definition of the filtration. Together
with the two results around it this presents `Kₘ / Kₘ₊₁` as the kernel of
`Γ(Eₘ₊₁, 𝒪) ⟶ Γ(Eₘ, 𝒪)`. -/
public theorem thickeningRestrictionLE_eq_zero_iff (D : X.IdealSheafData) {m N : ℕ}
    (hm1 : m + 1 ≤ N) (u : Γ(thickening D N, ⊤)) :
    thickeningRestrictionLE D hm1 u = 0 ↔ u ∈ thickeningKernel D hm1 :=
  (mem_thickeningKernel_iff D hm1 u).symm

/-- **The graded piece of the ambient filtration injects into the sections of the twist.** For an
effective Cartier divisor, the restriction to `Eₘ₊₁` of a function on `E_N` vanishing on `Eₘ` is
the image under `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom` of a global section
of `𝒪_X(-D ^ (m + 1))|_E`. -/
public theorem exists_gradedSectionsHom_eq_of_mem_thickeningKernel (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] {m N : ℕ} (hm1 : m + 1 ≤ N) {u : Γ(thickening D N, ⊤)}
    (hu : u ∈ thickeningKernel D ((Nat.le_succ m).trans hm1)) :
    ∃ x, gradedSectionsHom D m x = thickeningRestrictionLE D hm1 u :=
  (gradedSectionsHom_eq_iff D m _).1 (thickeningRestrictionLE_mem_ker D hm1 hu)

/-- If the restriction of `u` to `Eₘ₊₁` is a symbol, then `u` vanishes on `Eₘ`. -/
private theorem mem_thickeningKernel_of_restrictionLE_eq_symbol (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] {m N : ℕ} (hm1 : m + 1 ≤ N) {u : Γ(thickening D N, ⊤)}
    {x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1))),
      (⊤ : D.subscheme.Opens))}
    (hu : thickeningRestrictionLE D hm1 u = gradedSectionsHom D m x) :
    u ∈ thickeningKernel D ((Nat.le_succ m).trans hm1) := by
  rw [mem_thickeningKernel_iff, ← thickeningRestrictionLE_comp D (Nat.le_succ m) hm1, hu,
    thickeningRestrictionLE_succ]
  exact (gradedSectionsHom_eq_iff D m _).2 ⟨x, rfl⟩

/-- **And onto them**, when the transition maps of the tower of thickenings are surjective: every
global section of `𝒪_X(-D ^ (m + 1))|_E` is the symbol of a function on `E_N` vanishing on `Eₘ`.
-/
public theorem exists_mem_thickeningKernel_gradedSectionsHom (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (hsurj : ∀ j, Function.Surjective (thickeningRestriction D j))
    {m N : ℕ} (hm1 : m + 1 ≤ N)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1))),
      (⊤ : D.subscheme.Opens))) :
    ∃ u ∈ thickeningKernel D ((Nat.le_succ m).trans hm1),
      thickeningRestrictionLE D hm1 u = gradedSectionsHom D m x := by
  obtain ⟨u, hu⟩ := surjective_thickeningRestrictionLE D hsurj hm1 (gradedSectionsHom D m x)
  exact ⟨u, mem_thickeningKernel_of_restrictionLE_eq_symbol D hm1 hu, hu⟩

/-- A function on `E_N` whose restriction to `Eₘ₊₁` is the symbol of a section of
`𝒪_X(-D ^ (m + 1))|_E` vanishes on `Eₘ`: restricting it one step further is restricting the
symbol, and a symbol dies on `Eₘ`. -/
public theorem mem_thickeningKernel_of_thickeningRestrictionLE_eq (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] {m N : ℕ} (hm1 : m + 1 ≤ N) {u : Γ(thickening D N, ⊤)}
    {x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1))),
      (⊤ : D.subscheme.Opens))}
    (hu : thickeningRestrictionLE D hm1 u = gradedSectionsHom D m x) :
    u ∈ thickeningKernel D ((Nat.le_succ m).trans hm1) :=
  mem_thickeningKernel_of_restrictionLE_eq_symbol D hm1 hu

/-! ### The symbol of a product of two lifts -/

/-- **The product of two lifts has a symbol, and it depends only on the two symbols.**

Let `a` be a global section of `𝒪_X(-D ^ (m + 1))|_E` and `b` one of `𝒪_X(-D ^ (n + 1))|_E`. A
lift of `a` is a function `u` on `E_{q+1}` restricting on `E_{m+1}` to the symbol `a`, and
likewise for `b`; such lifts exist when the transition maps are surjective, and `u` then
vanishes on `Eₘ` and `v` on `Eₙ`, so `u v` vanishes on `E_q` and is itself the symbol of a
global section `c` of `𝒪_X(-D ^ (q + 1))|_E`. The content of the statement is that the *same*
`c` works for **every** choice of lifts: at this ambient thickening the product is already
determined, by
`AlgebraicGeometry.Scheme.IdealSheafData.mul_eq_mul_of_thickeningRestrictionLE_eq`.

This is the frame in which "the symbol of a product is the product of the symbols" is a
well-formed assertion about the sections of the twists alone. It does **not** say what `c` is;
that `c` is `Stacks.Divisors.restrictedIdealMulSections a b` is
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections`, in
`StacksFrontier/AlgebraicGeometry/Surfaces/GradedSectionsLocal.lean`.

The degree is a free variable `q` with an equation rather than the term `m + n + 1`, for the
reason recorded on
`AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel_mul_le_of_eq`: the consumer at
`m = 0` would otherwise have to identify `0 + n + 1` with `n + 1`, which is not a definitional
equality of `Nat` for variable `n`. -/
public theorem exists_gradedSectionsHom_eq_mul (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D]
    (hsurj : ∀ j, Function.Surjective (thickeningRestriction D j)) {m n q : ℕ}
    (hq : q = m + n + 1) (hm1 : m + 1 ≤ q + 1) (hn1 : n + 1 ≤ q + 1)
    (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1))),
      (⊤ : D.subscheme.Opens)))
    (b : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens))) :
    ∃ c : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (q + 1))),
        (⊤ : D.subscheme.Opens)),
      ∀ u v : Γ(thickening D (q + 1), ⊤),
        thickeningRestrictionLE D hm1 u = gradedSectionsHom D m a →
        thickeningRestrictionLE D hn1 v = gradedSectionsHom D n b →
        gradedSectionsHom D q c = u * v := by
  subst hq
  have hm : m ≤ m + n + 1 + 1 := by omega
  have hn : n ≤ m + n + 1 + 1 := by omega
  have hqq : m + n + 1 ≤ m + n + 1 + 1 := Nat.le_succ _
  obtain ⟨u₀, hu₀K, hu₀⟩ := exists_mem_thickeningKernel_gradedSectionsHom D hsurj hm1 a
  obtain ⟨v₀, hv₀K, hv₀⟩ := exists_mem_thickeningKernel_gradedSectionsHom D hsurj hn1 b
  have hprod : u₀ * v₀ ∈ thickeningKernel D hqq :=
    thickeningKernel_mul_le D hm hn hqq (Ideal.mul_mem_mul hu₀K hv₀K)
  obtain ⟨c, hc⟩ := (gradedSectionsHom_eq_iff D (m + n + 1) (u₀ * v₀)).1
    ((mem_thickeningKernel_iff D hqq _).1 hprod)
  refine ⟨c, fun u v hu hv => ?_⟩
  rw [hc]
  exact mul_eq_mul_of_thickeningRestrictionLE_eq D hm hn hm1 hn1
    (mem_thickeningKernel_of_thickeningRestrictionLE_eq D hm1 hu) hv₀K
    (hu₀.trans hu.symm) (hv₀.trans hv.symm)

/-- **The symbols of the products of a function vanishing on `E` with a function vanishing on
`Eₚ`**, as a set of global sections of `𝒪_X(-D ^ (p + 2))|_E`.

A member is a section `c` which, for one pair of symbols `a` in degree `1` and `b` in degree
`p + 1`, is the symbol of `u v` for *every* pair of lifts `u` of `a` and `v` of `b` to
`Γ(E_{p+2}, 𝒪)`; by
`AlgebraicGeometry.Scheme.IdealSheafData.exists_gradedSectionsHom_eq_mul` such a `c` exists for
every pair `(a, b)`, so this set is the image of the pairing the graded pieces carry. -/
public def gradedSectionsDegreeOneProducts (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (p : ℕ) :
    Set Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (p + 1 + 1))),
      (⊤ : D.subscheme.Opens)) :=
  {c | ∃ (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (0 + 1))),
          (⊤ : D.subscheme.Opens)))
         (b : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (p + 1))),
          (⊤ : D.subscheme.Opens))),
       ∀ u v : Γ(thickening D (p + 1 + 1), ⊤),
         thickeningRestrictionLE D (by omega : 0 + 1 ≤ p + 1 + 1) u = gradedSectionsHom D 0 a →
         thickeningRestrictionLE D (Nat.le_succ (p + 1)) v = gradedSectionsHom D p b →
         gradedSectionsHom D (p + 1) c = u * v}

/-- **Degree-one generation of the filtration of a single thickening follows from degree-one
generation of the symbols.**

`K_{p+1} ≤ K₀ · K_p` holds as soon as every global section of `𝒪_X(-D ^ (p + 2))|_E` is a finite
sum of symbols of products — members of
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts`. The passage is
immediate once the frame is set up: a function on `E_{p+2}` vanishing on `E_{p+1}` *is* the
symbol of a unique such section, by
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom_eq_iff`, the symbol map is additive,
and every symbol of a product is literally a product of an element of `K₀` with one of `K_p`.

This is the last reduction on the geometric side: what `hgenK` still needs is a statement about
the global sections of the twists `i^*ℐ_{D ^ m}` and the pairing they carry, with the rings of
functions on the thickenings and the ideal product `K₀ · K_p` no longer mentioned. -/
public theorem thickeningKernel_le_mul_of_mem_closure (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D]
    (hsurj : ∀ j, Function.Surjective (thickeningRestriction D j))
    (hgen : ∀ (p : ℕ) (x : Γ((Scheme.Modules.pullback D.subschemeι).obj
        (negativeTwist (D ^ (p + 1 + 1))), (⊤ : D.subscheme.Opens))),
      x ∈ AddSubgroup.closure (gradedSectionsDegreeOneProducts D p))
    (p : ℕ) :
    thickeningKernel D (Nat.le_succ (p + 1)) ≤
      thickeningKernel D (Nat.zero_le (p + 2)) * thickeningKernel D (Nat.le_add_right p 2) := by
  have h₀ : 0 + 1 ≤ p + 1 + 1 := by omega
  intro w hw
  obtain ⟨x, hx⟩ := (gradedSectionsHom_eq_iff D (p + 1) w).1
    ((mem_thickeningKernel_iff D (Nat.le_succ (p + 1)) w).1 hw)
  rw [← hx]
  have hle : AddSubgroup.closure (gradedSectionsDegreeOneProducts D p) ≤
      AddSubgroup.comap (gradedSectionsHom D (p + 1))
        (thickeningKernel D (Nat.zero_le (p + 2)) *
          thickeningKernel D (Nat.le_add_right p 2)).toAddSubgroup := by
    rw [AddSubgroup.closure_le]
    rintro c ⟨a, b, hab⟩
    obtain ⟨u, huK, hu⟩ := exists_mem_thickeningKernel_gradedSectionsHom D hsurj h₀ a
    obtain ⟨v, hvK, hv⟩ :=
      exists_mem_thickeningKernel_gradedSectionsHom D hsurj (Nat.le_succ (p + 1)) b
    change gradedSectionsHom D (p + 1) c ∈
      thickeningKernel D (Nat.zero_le (p + 2)) * thickeningKernel D (Nat.le_add_right p 2)
    rw [hab u v hu hv]
    exact Ideal.mul_mem_mul huK hvK
  exact hle (hgen p x)

/-! ### Degree-one generation descends from one thickening to the inverse limit -/

/-- **Degree-one generation of the projection-kernel filtration follows from degree-one
generation inside a single thickening.**

The hypothesis `hgenK` is the reverse of
`AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel_mul_le` at `m = 0`, `n = p`: in
`Γ(E_{p+2}, 𝒪)`, every function vanishing on `E_{p+1}` is a sum of products of a function
vanishing on `E` with a function vanishing on `E_p`. It is a statement about *one* ring of
functions on *one* thickening — no inverse limit, no symbol, no twist.

The conclusion is the `hgen` input of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofExceptionalCurve`, namely
`Iₙ₊₁ ⊆ I₁ Iₙ + Iₙ₊₂` for the filtration of the inverse limit.

This is a genuine reduction and not a restatement. The inverse limit disappears: a relation
among global functions on the single thickening `E_{p+2}` lifts to a relation in `A` because
the projection `A ⟶ Γ(E_{p+2}, 𝒪)` is onto and *detects the filtration* — a lift of a function
vanishing on `Eⱼ` automatically lies in `Iⱼ₊₁`, since restricting its projection to `Eⱼ` is
projecting to `Eⱼ`. What remains unproved is `hgenK` itself, which is where the projective line
enters: locally on an affine open of `X` it is the triviality
`I^{p+1} = I · I^p + I^{p+2}`, and globally it is the surjectivity of
`H⁰(𝐏¹, 𝒪(1)) ⊗ H⁰(𝐏¹, 𝒪(p + 1)) ⟶ H⁰(𝐏¹, 𝒪(p + 2))`. -/
public theorem formalNeighborhoodFiltration_le_mul_sup_of_thickeningKernel_le
    (D : X.IdealSheafData) (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m))
    (hgenK : ∀ p : ℕ, thickeningKernel D (Nat.le_succ (p + 1)) ≤
      thickeningKernel D (Nat.zero_le (p + 2)) * thickeningKernel D (Nat.le_add_right p 2))
    (n : ℕ) :
    formalNeighborhoodFiltration D (n + 1) ≤
      formalNeighborhoodFiltration D 1 * formalNeighborhoodFiltration D n ⊔
        formalNeighborhoodFiltration D (n + 2) := by
  cases n with
  | zero =>
    intro a ha
    refine Submodule.mem_sup_left ?_
    rw [formalNeighborhoodFiltration_zero, Ideal.mul_top]
    exact ha
  | succ p =>
    have hp1 : p + 1 ≤ p + 2 := Nat.le_succ _
    have hp : p ≤ p + 2 := Nat.le_add_right p 2
    have h0 : 0 ≤ p + 2 := Nat.zero_le _
    -- A function on `E_{p+2}` vanishing on `E` lifts to `I₁`, one vanishing on `Eₚ` to `I_{p+1}`.
    have hlift : ∀ (j : ℕ) (hj : j ≤ p + 2) (u : Γ(thickening D (p + 2), ⊤)),
        u ∈ thickeningKernel D hj → ∃ c : formalNeighborhoodRing D,
          c ∈ formalNeighborhoodFiltration D (j + 1) ∧
            formalNeighborhoodProjection D (p + 2) c = u := by
      intro j hj u hu
      obtain ⟨c, hc⟩ := surjective_formalNeighborhoodProjection D hsurj (p + 2) u
      refine ⟨c, ?_, hc⟩
      rw [formalNeighborhoodFiltration_succ, RingHom.mem_ker,
        ← thickeningRestrictionLE_formalNeighborhoodProjection D hj c, hc]
      exact (mem_thickeningKernel_iff D hj u).1 hu
    -- Every element of `K₀ · Kₚ` is the projection of an element of `I₁ · I_{p+1}`.
    have main : ∀ v ∈ thickeningKernel D h0 * thickeningKernel D hp,
        ∃ b ∈ formalNeighborhoodFiltration D 1 * formalNeighborhoodFiltration D (p + 1),
          formalNeighborhoodProjection D (p + 2) b = v := by
      intro v hv
      refine Submodule.mul_induction_on hv (fun u hu w hw ↦ ?_) (fun x y ↦ ?_)
      · obtain ⟨c, hc, hcu⟩ := hlift 0 h0 u hu
        obtain ⟨d, hd, hdw⟩ := hlift p hp w hw
        exact ⟨c * d, Ideal.mul_mem_mul hc hd, by rw [map_mul, hcu, hdw]⟩
      · rintro ⟨bx, hbx, hbx'⟩ ⟨by', hby, hby'⟩
        exact ⟨bx + by', Ideal.add_mem _ hbx hby, by rw [map_add, hbx', hby']⟩
    intro a ha
    have hv : formalNeighborhoodProjection D (p + 2) a ∈ thickeningKernel D hp1 := by
      rw [mem_thickeningKernel_iff, thickeningRestrictionLE_formalNeighborhoodProjection D hp1]
      exact ha
    obtain ⟨b, hb, hbv⟩ := main _ (hgenK p hv)
    refine Submodule.mem_sup.2 ⟨b, hb, a - b, ?_, by ring⟩
    change a - b ∈ RingHom.ker (formalNeighborhoodProjection D (p + 2))
    rw [RingHom.mem_ker, map_sub, hbv, sub_self]

end AlgebraicGeometry.Scheme.IdealSheafData

end
