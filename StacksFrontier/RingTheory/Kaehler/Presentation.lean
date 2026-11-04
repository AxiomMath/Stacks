module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.GroupTheory.GroupAction.Ring
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the presentation of the module of differentials

Given a commutative square of commutative unital rings
```
      φ
  S  --->  S'
  ↑         ↑
 α|         |β
  |    ψ    |
  R  --->  R'
```
that is, ring homomorphisms `α : R → S`, `β : R' → S'`, `φ : S → S'`, `ψ : R → R'` with
`φ ∘ α = β ∘ ψ`, the associated square of presentations of the modules of Kähler
differentials commutes. This is Stacks tag 0H2F (Equation 10.131.4.2).

For a ring map `α : R → S` the presentation of `Ω_{S/R}` (Stacks tag 00RM) consists of the
free `S`-modules

`P_{S/R} = (⨁_{(a,b) ∈ S²} S[(a,b)]) ⊕ (⨁_{(f,g) ∈ S²} S[(f,g)]) ⊕ (⨁_{r ∈ R} S[r])`,
`F_{S/R} = ⨁_{a ∈ S} S[a]`,

with `S`-linear presentation map `∂_{S/R} : P_{S/R} → F_{S/R}` given on basis generators by
`[(a,b)] ↦ [a+b] - [a] - [b]`, `[(f,g)] ↦ [fg] - f[g] - g[f]` and `[r] ↦ [α r]`. The
vertical maps `Φ_F : F_{S/R} → F_{S'/R'}` and `Φ_P : P_{S/R} → P_{S'/R'}` are the
`φ`-semilinear maps given on basis generators by `[a] ↦ [φ a]`,
`[(a,b)] ↦ [(φ a, φ b)]`, `[(f,g)] ↦ [(φ f, φ g)]` and `[r] ↦ [ψ r]`.

## Main definitions

* `Stacks.KaehlerDifferential.Presentation.PIdx`, `Stacks.KaehlerDifferential.Presentation.FreeF`,
  `Stacks.KaehlerDifferential.Presentation.FreeP`: the index set of the
  generators of `P_{S/R}`, and the two free modules.
* `Stacks.KaehlerDifferential.Presentation.presentationMap`: the presentation map `∂_{S/R}`.
* `Stacks.KaehlerDifferential.Presentation.freeMapₛₗ`,
  `Stacks.KaehlerDifferential.Presentation.PhiF`, `Stacks.KaehlerDifferential.Presentation.PhiP`:
    the generic
  `φ`-semilinear map between free modules induced by a map of index sets, and the two
  vertical maps.

## Main results

* `Stacks.KaehlerDifferential.Presentation.presentation_square_comm` (Stacks tag 0H2F):
  `Φ_F ∘ ∂_{S/R} = ∂_{S'/R'} ∘ Φ_P` as `φ`-semilinear maps `P_{S/R} → F_{S'/R'}`. On each
  kind of generator this is immediate from the defining formulas, the structure-map
  generators being where the commutativity hypothesis `φ ∘ α = β ∘ ψ` is used.

## Implementation notes

For a ring `T` and an index set `X`, the free `T`-module on the basis `{[x] : x ∈ X}` is
modelled by the finitely supported functions `X →₀ T`, with basis generator
`[x] = Finsupp.single x 1`; more generally `Finsupp.single x t` is `t · [x]`.

Viewing the codomains as `S`-modules by restriction of scalars along `φ` turns `Φ_F` and
`Φ_P` into honest `S`-linear maps, which is the same thing as `φ`-semilinearity.
-/

@[expose] public section

namespace Stacks.KaehlerDifferential.Presentation

/-- The index set of the basis generators of `P_{S/R}`:
* `Sum.inl (a, b)` — the additivity generators `[(a,b)]` (indexed by `S × S`);
* `Sum.inr (Sum.inl (f, g))` — the Leibniz generators `[(f,g)]` (indexed by `S × S`);
* `Sum.inr (Sum.inr r)` — the structure-map generators `[r]` (indexed by `R`). -/
abbrev PIdx (S R : Type*) := (S × S) ⊕ (S × S) ⊕ R

/-- The free `S`-module `F_{S/R} = ⨁_{a ∈ S} S[a]`. -/
abbrev FMod (S : Type*) [CommRing S] := S →₀ S

/-- The free `S`-module `P_{S/R}`, with basis indexed by `PIdx S R`. -/
abbrev PMod (S R : Type*) [CommRing S] := PIdx S R →₀ S

/-- The `S`-linear presentation map `∂_{S/R} : P_{S/R} → F_{S/R}` (Stacks Tag 00RM),
determined on basis generators by
`[(a,b)] ↦ [a+b] - [a] - [b]`, `[(f,g)] ↦ [fg] - f[g] - g[f]`, `[r] ↦ [α r]`. -/
noncomputable def presentationMap {R S : Type*} [CommRing R] [CommRing S] (α : R →+* S) :
    PMod S R →ₗ[S] FMod S :=
  Finsupp.lsum S fun
    | Sum.inl (a, b) => Finsupp.lsingle (a + b) - Finsupp.lsingle a - Finsupp.lsingle b
    | Sum.inr (Sum.inl (f, g)) =>
        Finsupp.lsingle (f * g) - f • Finsupp.lsingle g - g • Finsupp.lsingle f
    | Sum.inr (Sum.inr r) => Finsupp.lsingle (α r)

/-- The generic `φ`-semilinear map between free modules induced by a map of index sets
`g : X → Y`, sending the generator multiple `t · [x] = single x t` to
`φ t · [g x] = single (g x) (φ t)`. -/
noncomputable def freeMapₛₗ {S S' : Type*} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X Y : Type*} (g : X → Y) : (X →₀ S) →ₛₗ[φ] (Y →₀ S') :=
  (Finsupp.lmapDomain S' S' g).comp (Finsupp.mapRange.linearMap (σ₁₂ := φ) φ.toSemilinearMap)

/-- The index map underlying `Φ_P`. -/
def gPIdx {S S' R R' : Type*} (φ : S → S') (ψ : R → R') :
    PIdx S R → PIdx S' R' := fun
  | Sum.inl (a, b) => Sum.inl (φ a, φ b)
  | Sum.inr (Sum.inl (f, g)) => Sum.inr (Sum.inl (φ f, φ g))
  | Sum.inr (Sum.inr r) => Sum.inr (Sum.inr (ψ r))

/-- The right-hand vertical map `Φ_F : F_{S/R} → F_{S'/R'}`, the `φ`-semilinear map with
`[a] ↦ [φ a]`. -/
noncomputable def PhiF {S S' : Type*} [CommRing S] [CommRing S'] (φ : S →+* S') :
    FMod S →ₛₗ[φ] FMod S' :=
  freeMapₛₗ φ (φ : S → S')

/-- The left-hand vertical map `Φ_P : P_{S/R} → P_{S'/R'}`, the `φ`-semilinear map with
`[(a,b)] ↦ [(φ a, φ b)]`, `[(f,g)] ↦ [(φ f, φ g)]`, `[r] ↦ [ψ r]`. -/
noncomputable def PhiP {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (φ : S →+* S') (ψ : R →+* R') : PMod S R →ₛₗ[φ] PMod S' R' :=
  freeMapₛₗ φ (gPIdx (φ : S → S') (ψ : R → R'))

/-- `freeMapₛₗ` sends a basis multiple `single x t` to `single (g x) (φ t)`. -/
theorem freeMapₛₗ_single {S S' : Type*} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X Y : Type*} (g : X → Y) (x : X) (t : S) :
    freeMapₛₗ φ g (Finsupp.single x t) = Finsupp.single (g x) (φ t) := by
  simp only [freeMapₛₗ, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single, RingHom.coe_toSemilinearMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

/-- **Stacks Tag 0H2F.** Given a commutative square of commutative rings
`φ ∘ α = β ∘ ψ` (here phrased as `φ.comp α = β.comp ψ`), the square of presentations
of Kähler differentials commutes:
`Φ_F ∘ ∂_{S/R} = ∂_{S'/R'} ∘ Φ_P`
as `φ`-semilinear maps `P_{S/R} → F_{S'/R'}`. -/
@[stacks 0H2F]
theorem presentation_square_comm
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (α : R →+* S) (β : R' →+* S') (φ : S →+* S') (ψ : R →+* R')
    (hcomm : φ.comp α = β.comp ψ) :
    (PhiF φ).comp (presentationMap α)
      = (presentationMap β).comp (PhiP φ ψ) := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext
  intro t
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, PhiP, PhiF, freeMapₛₗ_single]
  rcases i with ⟨a, b⟩ | ⟨f, g⟩ | r
  · simp only [presentationMap, Finsupp.lsum_single, gPIdx,
      LinearMap.sub_apply, Finsupp.lsingle_apply, freeMapₛₗ_single, map_sub, map_add]
  · simp only [presentationMap, Finsupp.lsum_single, gPIdx,
      LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
      Finsupp.smul_single, smul_eq_mul, freeMapₛₗ_single, map_sub, map_mul]
  · simp only [presentationMap, Finsupp.lsum_single, gPIdx,
      Finsupp.lsingle_apply, freeMapₛₗ_single]
    have h : φ (α r) = β (ψ r) := by simpa using RingHom.congr_fun hcomm r
    rw [h]

end Stacks.KaehlerDifferential.Presentation
