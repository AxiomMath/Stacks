module

public import StacksFrontier.Deformation.Artin.Infinitesimal.AugmentedLiftClasses

/-!
# Lifts over the ring of sequences with a common base

Let `x` be an object of a category fibred in groupoids over the big fppf site of `S`, lying over
`Spec A`, and let `⋯ → R₂ → R₁ → R₀ = A` be a tower of `S`-algebras augmented to `A`, with
`R̃ ⊆ ∏ Rₙ` the ring of sequences with a common image in `A` (see
`Deformation.Artin.SquareZeroTower.sameBase`) and `Mₙ = Ker(Rₙ → A)`, `M = ∏ Mₙ`. This file
carries out the second step of the proof of Stacks 0CYF: given one lift of `x` to `Spec R̃` and a
lift class `bₙ` of `x` over every `Spec Rₙ`, if the lift classes over `A[M]` are the products of
those over the `A[Mₙ]` (assumption (5)(a) of the source), then some lift of `x` to `Spec R̃`
restricts to `bₙ` over every `Spec Rₙ`.

The argument uses only the functoriality of lift classes and condition (RS*) for fibre products
over `A`. For every `n` the ring isomorphism `Rₙ ×_A Rₙ ≅ Rₙ ×_A A[Mₙ]`,
`(s, t) ↦ (s, (s̄, t − s))` turns the pair `(ξ̃|_{Rₙ}, bₙ)` into a class over `Rₙ ×_A A[Mₙ]`
whose `A[Mₙ]`-component `dₙ` is the difference of the two lifts; the classes `dₙ` assemble to a
class `d` over `A[M]`, and glueing the given lift with `d` over `R̃ ×_A A[M]` and pulling back
along `R̃ ×_A A[M] → R̃`, `(r, (a, m)) ↦ r + m`, gives the corrected lift.

## Main results

* `Deformation.Artin.AugmentedSiteRing.exists_classes_map_eq_of_difference` — the correction
  step, for abstract augmented rings and morphisms satisfying the relations of the rings above.
* `Deformation.Artin.AugmentedSiteRing.classes_map_difference_eq` — the restriction to `A[M]`
  of a lift over `R̃` restricting to a compatible system of classes over the `Rₙ` is trivial.

## References

* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin.AugmentedSiteRing

variable {A : Type u} [CommRing A]
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x : X}
  {hx : p.obj x = algebraOver A B S hS toS hA} {hp : p.IsFiberedInGroupoids}

/-- Two lift classes over `P` with equal restrictions along `f₁` and `f₂` are equal, if the pair of
restrictions is injective. -/
private theorem eq_of_map_eq_of_injective {P R₁ R₂ : AugmentedSiteRing A B S hS toS hA}
    (f₁ : Hom P R₁) (f₂ : Hom P R₂)
    (h : Function.Injective fun z : classes p x hx P =>
      (map p x hx hp f₁ z, map p x hx hp f₂ z))
    {z w : classes p x hx P} (h₁ : map p x hx hp f₁ z = map p x hx hp f₁ w)
    (h₂ : map p x hx hp f₂ z = map p x hx hp f₂ w) : z = w :=
  h (Prod.ext h₁ h₂)

/-- **The correction step in the proof of Stacks 0CYF.** Let `T = R̃` with projections
`πₙ : T → Dₙ = Rₙ`, let `Q = A[M]` with projections `qₙ : Q → Qₙ = A[Mₙ]`, and assume
`Lift(x, Q) → ∏ₙ Lift(x, Qₙ)` is surjective. Let `T_Q = T ×_A Q`, `Dₙ,Q = Dₙ ×_A Qₙ` and
`Pₙ = Dₙ ×_A Dₙ`, with their projections `t₁, t₂`, `r₁ₙ, r₂ₙ` and `p₁ₙ, p₂ₙ`, a morphism
`τₙ : Pₙ → Dₙ,Q` and morphisms `σ : T_Q → T`, `σₙ : Dₙ,Q → Dₙ` with `r₁ₙ τₙ = p₁ₙ` and
`σₙ τₙ = p₂ₙ`, and the componentwise maps `ρₙ : T_Q → Dₙ,Q`, which are compatible with the
projections and with `σ` and the `σₙ`. If lift classes over `T_Q` are pairs of lift classes,
lift classes over `Dₙ,Q` are determined by their two restrictions and every pair of lift classes
over `Dₙ` comes from `Pₙ`, then for a lift class `ξ₀` over `T` and lift classes `bₙ` over the
`Dₙ` some lift class over `T` restricts to every `bₙ`. -/
public theorem exists_classes_map_eq_of_difference
    {D Qn Dq P : ℕ → AugmentedSiteRing A B S hS toS hA} {T Q Tq : AugmentedSiteRing A B S hS toS hA}
    (π : ∀ n, Hom T (D n)) (q : ∀ n, Hom Q (Qn n))
    (hQ : Function.Surjective fun d : classes p x hx Q => fun n => map p x hx hp (q n) d)
    (t₁ σ : Hom Tq T) (t₂ : Hom Tq Q)
    (hTq : Function.Surjective fun z : classes p x hx Tq =>
      (map p x hx hp t₁ z, map p x hx hp t₂ z))
    (r₁ σn : ∀ n, Hom (Dq n) (D n)) (r₂ : ∀ n, Hom (Dq n) (Qn n))
    (hDq : ∀ n, Function.Injective fun z : classes p x hx (Dq n) =>
      (map p x hx hp (r₁ n) z, map p x hx hp (r₂ n) z))
    (p₁ p₂ : ∀ n, Hom (P n) (D n))
    (hP : ∀ n, Function.Surjective fun z : classes p x hx (P n) =>
      (map p x hx hp (p₁ n) z, map p x hx hp (p₂ n) z))
    (τ : ∀ n, Hom (P n) (Dq n)) (hτ₁ : ∀ n, r₁ n ≫ τ n = p₁ n) (hτ₂ : ∀ n, σn n ≫ τ n = p₂ n)
    (ρ : ∀ n, Hom Tq (Dq n)) (hρ₁ : ∀ n, r₁ n ≫ ρ n = π n ≫ t₁)
    (hρ₂ : ∀ n, r₂ n ≫ ρ n = q n ≫ t₂) (hρσ : ∀ n, σn n ≫ ρ n = π n ≫ σ)
    (ξ₀ : classes p x hx T) (b : ∀ n, classes p x hx (D n)) :
    ∃ ξ : classes p x hx T, ∀ n, map p x hx hp (π n) ξ = b n := by
  choose z hz using fun n => hP n (map p x hx hp (π n) ξ₀, b n)
  obtain ⟨d, hd⟩ := hQ fun n => map p x hx hp (r₂ n) (map p x hx hp (τ n) (z n))
  obtain ⟨w', hw'⟩ := hTq (ξ₀, d)
  obtain ⟨hw'₁, hw'₂⟩ := Prod.mk.inj hw'
  refine ⟨map p x hx hp σ w', fun n => ?_⟩
  have hρw : map p x hx hp (ρ n) w' = map p x hx hp (τ n) (z n) := by
    refine eq_of_map_eq_of_injective _ _ (hDq n) ?_ ?_
    · rw [← map_comp, ← map_comp, hρ₁, hτ₁, map_comp, hw'₁]
      exact (congrArg Prod.fst (hz n)).symm
    · rw [← map_comp, hρ₂, map_comp, hw'₂]
      exact congrFun hd n
  rw [← map_comp, ← hρσ, map_comp, hρw, ← map_comp, hτ₂]
  exact congrArg Prod.snd (hz n)

/-- **The difference of a corrected lift is trivial, in the proof of Stacks 0CYF.** Let `T = R̃`
with projections `πₙ : T → Dₙ = Rₙ` and transition maps `fₙ : Dₙ₊₁ → Dₙ`, let `δ : T → Q = A[M]`
be the difference map, `qₙ : Q → Qₙ = A[Mₙ]` the projections, and assume
`Lift(x, Q) → ∏ₙ Lift(x, Qₙ)` is injective. Let `Pₙ = Dₙ ×_A Dₙ` with projections `p₁ₙ, p₂ₙ`
(on which lift classes are determined by their two restrictions), diagonal `Δₙ`, the map
`gₙ : T → Pₙ`, `r ↦ (fₙ(rₙ₊₁), rₙ)`, and `δₙ : Pₙ → Qₙ`, `(s, t) ↦ (s̄, s − t)`, so that
`qₙ δ = δₙ gₙ` and `δₙ Δₙ` is the augmentation `Dₙ → A₀ = A` followed by `A → Qₙ`. If a lift
class `η` over `T` restricts to classes `bₙ` over the `Dₙ` with `fₙ(bₙ₊₁) = bₙ`, all of which
restrict to the same class `c` over `A₀`, then the restriction of `η` to `Q` is the class pulled
back from `c`. -/
public theorem classes_map_difference_eq
    {D Qn P : ℕ → AugmentedSiteRing A B S hS toS hA} {T Q A₀ : AugmentedSiteRing A B S hS toS hA}
    (π : ∀ n, Hom T (D n)) (f : ∀ n, Hom (D (n + 1)) (D n)) (q : ∀ n, Hom Q (Qn n))
    (hQ : Function.Injective fun d : classes p x hx Q => fun n => map p x hx hp (q n) d)
    (δ : Hom T Q) (inl : Hom A₀ Q) (inln : ∀ n, Hom A₀ (Qn n)) (hinl : ∀ n, q n ≫ inl = inln n)
    (aug : ∀ n, Hom (D n) A₀)
    (p₁ p₂ : ∀ n, Hom (P n) (D n))
    (hP : ∀ n, Function.Injective fun z : classes p x hx (P n) =>
      (map p x hx hp (p₁ n) z, map p x hx hp (p₂ n) z))
    (Δ : ∀ n, Hom (D n) (P n)) (hΔ₁ : ∀ n, p₁ n ≫ Δ n = 𝟙 _) (hΔ₂ : ∀ n, p₂ n ≫ Δ n = 𝟙 _)
    (g : ∀ n, Hom T (P n)) (hg₁ : ∀ n, p₁ n ≫ g n = f n ≫ π (n + 1))
    (hg₂ : ∀ n, p₂ n ≫ g n = π n)
    (δn : ∀ n, Hom (P n) (Qn n)) (hδ : ∀ n, q n ≫ δ = δn n ≫ g n)
    (hδΔ : ∀ n, δn n ≫ Δ n = inln n ≫ aug n)
    (η : classes p x hx T) (b : ∀ n, classes p x hx (D n))
    (hη : ∀ n, map p x hx hp (π n) η = b n)
    (hb : ∀ n, map p x hx hp (f n) (b (n + 1)) = b n) (c : classes p x hx A₀)
    (hc : ∀ n, map p x hx hp (aug n) (b n) = c) :
    map p x hx hp δ η = map p x hx hp inl c := by
  apply hQ
  funext n
  show map p x hx hp (q n) (map p x hx hp δ η) = map p x hx hp (q n) (map p x hx hp inl c)
  have hgη : map p x hx hp (g n) η = map p x hx hp (Δ n) (b n) := by
    refine eq_of_map_eq_of_injective _ _ (hP n) ?_ ?_
    · rw [← map_comp, ← map_comp, hg₁, hΔ₁, map_id, map_comp, hη, hb]
    · rw [← map_comp, ← map_comp, hg₂, hΔ₂, map_id, hη]
  rw [← map_comp, ← map_comp, hδ, hinl, map_comp, hgη, ← map_comp, hδΔ, map_comp, hc]

end Deformation.Artin.AugmentedSiteRing
