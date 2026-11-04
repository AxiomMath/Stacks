module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankExtension
public import StacksFrontier.CategoryTheory.Subobject.QuotientFiltration

/-!
# Invariants of finite locally free modules along filtrations with invertible quotients

Let `X` be an algebraic space and let `ℰ` be an `𝒪_X`-module with a filtration

  `0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ`,   `ℰ_i / ℰ_{i-1} ≅ ℒ_i`

whose successive quotients are invertible. Then `ℰ` is finite locally free of rank `r`, and an
invariant `c` of finite locally free modules with `c(ℰ') = y(ℒ) c(ℱ)` on short exact sequences
`0 ⟶ ℒ ⟶ ℰ' ⟶ ℱ ⟶ 0` with invertible sub `ℒ` takes the value

  `c(ℰ) = y(ℒ_1) y(ℒ_2) ⋯ y(ℒ_r)`

on `ℰ`. The total Chern class of chapter 82 is such an invariant (Stacks 0ES8), and this is the
computation of Stacks 0ESA from it.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule`: an invertible
  `𝒪_X`-module has rank one.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_filtration`: a module with a filtration of
  length `r` with invertible quotients is finite locally free of rank `r`.
* `AlgebraicGeometry.Space.eq_prod_of_filtration_of_mul`: the product formula for an invariant
  which is multiplicative on extensions by an invertible sub.

## Implementation notes

Ranks are the rank clause of Stacks 0409 on the small étale ringed site of `X`,
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`, and invertibility is
`AlgebraicGeometry.Space.IsInvertibleModule`. The filtration is a monotone family
`F : Fin (r + 1) → Subobject ℰ` with `F 0 = ⊥` and `F r = ⊤`, together with identifications of
the successive quotients `F (i + 1) / F i` with the `ℒ i`, indexed by `Fin r`.

## References

* [Stacks Project, Tag 0ESA](https://stacks.math.columbia.edu/tag/0ESA)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

universe u w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)

/-- The abelian structure of the `𝒪_X`-modules, at the universe of the schemes. -/
local instance : Abelian (Modules.{u, u} B S hS X.1 X.2) :=
  SheafOfModules.instAbelian _

/-- **An invertible `𝒪_X`-module has rank one** (Stacks 0B8Q on the small étale site of `X`, which
is locally ringed). -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertibleModule {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : IsInvertibleModule X L) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) L 1 :=
  have : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedSite B S hS X.1 X.2).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L :=
    hL
  RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible' _ L
    (smallEtaleRingedSite_isLocallyRinged B S hS X.1 X.2)

/-- **An extension of a module of rank `r` by an invertible module has rank `r + 1`.** -/
theorem isFiniteLocallyFreeOfRank_succ_of_shortExact (r : ℕ)
    {T : ShortComplex (Modules.{u, u} B S hS X.1 X.2)} (hT : T.ShortExact)
    (h₁ : IsInvertibleModule X T.X₁)
    (h₃ : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) T.X₃ r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) T.X₂ (r + 1) := by
  rw [add_comm]
  exact RingedSite.IsFiniteLocallyFreeOfRank.of_shortExact _ hT
    (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X h₁) h₃

/-- **A module with a filtration with invertible quotients is finite locally free.** If `ℰ` has a
filtration `0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ` with `ℰ_i / ℰ_{i-1} ≅ ℒ_i` invertible, then `ℰ` is
finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_filtration {r : ℕ} {E : Modules.{u, u} B S hS X.1 X.2}
    (L : Fin r → Modules.{u, u} B S hS X.1 X.2) (hL : ∀ i, IsInvertibleModule X (L i))
    (F : Fin (r + 1) → Subobject E) (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r, cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r :=
  Abelian.Subobject.prop_of_filtration
    (fun r E ↦ RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)
    (IsInvertibleModule X) (fun _ ↦ RingedSite.isFiniteLocallyFreeOfRank_zero_of_isZero _)
    (fun r _ ↦ isFiniteLocallyFreeOfRank_succ_of_shortExact X r) L hL F hF h0
    hr e

/-- **The product formula along a filtration with invertible quotients.** Let `c r ℰ` be an
invariant, with values in a monoid, of the `𝒪_X`-modules `ℰ` of rank `r`, and `y ℒ` an element
attached to each invertible `ℒ`, such that `c 0 ℰ = 1` and `c (r + 1) ℰ = y ℒ * c r ℱ` for every
short exact sequence `0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` with `ℒ` invertible and `ℱ` of rank `r`. If `ℰ` has a
filtration `0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ` with `ℰ_i / ℰ_{i-1} ≅ ℒ_i` invertible, then

  `c r ℰ = y ℒ_1 * y ℒ_2 * ⋯ * y ℒ_r`. -/
theorem eq_prod_of_filtration_of_mul {M : Type w} [Monoid M]
    (c : ∀ (r : ℕ) (E : Modules.{u, u} B S hS X.1 X.2),
      RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r → M)
    (y : ∀ L : Modules.{u, u} B S hS X.1 X.2, IsInvertibleModule X L → M)
    (hc₀ : ∀ E hE, c 0 E hE = 1)
    (hc : ∀ (r : ℕ) (T : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) (_ : T.ShortExact)
      (h₁ : IsInvertibleModule X T.X₁) h₂ h₃, c (r + 1) T.X₂ h₂ = y T.X₁ h₁ * c r T.X₃ h₃)
    {r : ℕ} {E : Modules.{u, u} B S hS X.1 X.2}
    (hE : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)
    (L : Fin r → Modules.{u, u} B S hS X.1 X.2) (hL : ∀ i, IsInvertibleModule X (L i))
    (F : Fin (r + 1) → Subobject E) (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r, cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    c r E hE = (List.ofFn fun i ↦ y (L i) (hL i)).prod :=
  Abelian.Subobject.eq_prod_of_filtration _ (IsInvertibleModule X) c y
    (fun _ ↦ RingedSite.isFiniteLocallyFreeOfRank_zero_of_isZero _) hc₀
    (fun r _ ↦ isFiniteLocallyFreeOfRank_succ_of_shortExact X r) hc hE L hL F
    hF h0 hr e

end AlgebraicGeometry.Space

end
