module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksCore.Tactic.StacksAttribute

/-!
# Vertical composition of base change maps of topoi

Stacks tag 0F6X (Remark 7.45.3).  A morphism of topoi is an adjunction `f⁻¹ ⊣ f_*`, and for
a commutative square of topoi with vertical morphisms `u, v` the *base change map*
`β : q⁻¹ ∘ u_* ⟹ v_* ∘ p⁻¹` is the mate, under `u⁻¹ ⊣ u_*` and `v⁻¹ ⊣ v_*`, of the 2-cell
expressing commutativity.  For two such squares stacked vertically, the base change map of
the outer rectangle is the horizontal paste of the base change maps of the two squares.
This is the pasting law for mates, so the proof is `mateEquiv_hcomp`.

Commutativity 2-cells are `CategoryTheory.TwoSquare`s: `TwoSquare T L R B` is the type of
natural transformations `T ⋙ R ⟶ L ⋙ B`, and since the composition `a ∘ b` of the tag is
`b ⋙ a`, the top square's cell `k⁻¹ ∘ f⁻¹ = f'⁻¹ ∘ l⁻¹` is a
`TwoSquare lInv fInv f'Inv kInv`, whose mate is `TwoSquare fStar kInv lInv f'Star`.
-/

@[expose] public section

open CategoryTheory

namespace ToposBaseChange

universe v u

-- Sheaf categories for the 3x2 diagram of topoi.
variable {ShB' ShB ShC' ShC ShD' ShD : Type u}
variable [Category.{v} ShB'] [Category.{v} ShB]
variable [Category.{v} ShC'] [Category.{v} ShC]
variable [Category.{v} ShD'] [Category.{v} ShD]

-- Morphisms of topoi as adjunctions `pullback \dashv pushforward`.
-- `k : Sh(B') -> Sh(B)`:   `kInv = k^{-1} : Sh(B) -> Sh(B')`, `kStar = k_*`.
variable {kInv : ShB ⥤ ShB'} {kStar : ShB' ⥤ ShB}
-- `l : Sh(C') -> Sh(C)`
variable {lInv : ShC ⥤ ShC'} {lStar : ShC' ⥤ ShC}
-- `m : Sh(D') -> Sh(D)`
variable {mInv : ShD ⥤ ShD'} {mStar : ShD' ⥤ ShD}
-- `f : Sh(B) -> Sh(C)`
variable {fInv : ShC ⥤ ShB} {fStar : ShB ⥤ ShC}
-- `f' : Sh(B') -> Sh(C')`
variable {f'Inv : ShC' ⥤ ShB'} {f'Star : ShB' ⥤ ShC'}
-- `g : Sh(C) -> Sh(D)`
variable {gInv : ShD ⥤ ShC} {gStar : ShC ⥤ ShD}
-- `g' : Sh(C') -> Sh(D')`
variable {g'Inv : ShD' ⥤ ShC'} {g'Star : ShC' ⥤ ShD'}

-- The adjunctions underlying the four vertical morphisms of topoi
-- `f, f', g, g'` (which are the morphisms the base change maps are taken over).
variable (adjf : fInv ⊣ fStar) (adjf' : f'Inv ⊣ f'Star)
variable (adjg : gInv ⊣ gStar) (adjg' : g'Inv ⊣ g'Star)

/- Commutativity 2-cell of the top square on pullbacks:
`f'^{-1} \circ l^{-1} => k^{-1} \circ f^{-1}`, i.e. `lInv ⋙ f'Inv ⟶ fInv ⋙ kInv`.
For a strictly commuting square this is the identification (isomorphism) part of
the data `f \circ k = l \circ f'`. -/
variable (χtop : TwoSquare lInv fInv f'Inv kInv)

/- Commutativity 2-cell of the bottom square on pullbacks:
`g'^{-1} \circ m^{-1} => l^{-1} \circ g^{-1}`, i.e. `mInv ⋙ g'Inv ⟶ gInv ⋙ lInv`. -/
variable (χbot : TwoSquare mInv gInv g'Inv lInv)

/-- **Base change map of the top square** (Definition 1 with `p = k, q = l,
u = f, v = f'`): the mate of the commutativity 2-cell `χtop` under the vertical
adjunctions `f^{-1} \dashv f_*` and `f'^{-1} \dashv f'_*`. It is the natural
transformation `\beta_top : l^{-1} \circ f_* => f'_* \circ k^{-1}`. -/
@[sga "4 XII 6.8", sga "4 XVI 4.1", sga "4 XVIII 3.1.14" "more general"]
noncomputable def βtop : TwoSquare fStar kInv lInv f'Star :=
  mateEquiv adjf adjf' χtop

/-- **Base change map of the bottom square** (Definition 1 with `p = l, q = m,
u = g, v = g'`): `\beta_bot : m^{-1} \circ g_* => g'_* \circ l^{-1}`. -/
@[sga "4 XII 6.8", sga "4 XVI 4.1", sga "4 XVIII 3.1.14" "more general"]
noncomputable def βbot : TwoSquare gStar lInv mInv g'Star :=
  mateEquiv adjg adjg' χbot

/-- Commutativity 2-cell of the **outer rectangle** on pullbacks, obtained by
vertically pasting the two square cells. With `(g \circ f)^{-1} = f^{-1} \circ
g^{-1} = gInv ⋙ fInv` and `(g' \circ f')^{-1} = g'Inv ⋙ f'Inv`, this is
`TwoSquare mInv (gInv ⋙ fInv) (g'Inv ⋙ f'Inv) kInv`. -/
noncomputable def χrect : TwoSquare mInv (gInv ⋙ fInv) (g'Inv ⋙ f'Inv) kInv :=
  χbot.vComp χtop

/-- **Base change map of the outer rectangle** (Definition 1 with `p = k, q = m,
u = g \circ f, v = g' \circ f'`): the mate of the rectangle commutativity cell
`χrect` under the composite adjunctions `(g \circ f)^{-1} \dashv (g \circ f)_*`
and `(g' \circ f')^{-1} \dashv (g' \circ f')_*`, where the composite adjunctions
are `adjg.comp adjf : gInv ⋙ fInv ⊣ fStar ⋙ gStar`, etc. It is the natural
transformation `\beta_rect : m^{-1} \circ (g \circ f)_* => (g' \circ f')_* \circ
k^{-1}`. -/
noncomputable def βrect :
    TwoSquare (fStar ⋙ gStar) kInv mInv (f'Star ⋙ g'Star) :=
  mateEquiv (adjg.comp adjf) (adjg'.comp adjf') (χrect χtop χbot)

/-- **Tag 0F6X (vertical composition of base change maps).** The base change map
`\beta_rect` of the outer rectangle equals the pasted composite obtained from
`\beta_bot` and `\beta_top`, namely the horizontal composite of natural
transformations
```
  m^{-1} \circ g_* \circ f_*
    --> g'_* \circ l^{-1} \circ f_*     (β_bot whiskered by f_* on the right)
    --> g'_* \circ f'_* \circ k^{-1}    (β_top whiskered by g'_* on the left)
```
In Mathlib's notation this two-step whiskered composite is exactly
`(βtop).hComp (βbot)` (the horizontal composition of the two `TwoSquare`s). -/
@[stacks 0F6X, sga "4 XII 4.4" "more general"]
theorem main :
    βrect adjf adjf' adjg adjg' χtop χbot
      = (βtop adjf adjf' χtop).hComp (βbot adjg adjg' χbot) := by
  unfold βrect βtop βbot χrect
  exact mateEquiv_hcomp adjg adjg' adjf adjf' χbot χtop

end ToposBaseChange
