module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Iso

/-!
# Reassociating a chain of commuting squares, in one generic step

A composite of several morphisms is often rewritten by transporting commuting squares across
it one at a time.  When the morphisms involved are typed in two definitionally equal but
syntactically different ways, for instance at a type synonym and at the underlying category,
`rw` and `simp` cannot do this: their `Category` instance argument has to be unified at
`instances` transparency, and the goal is not type-correct there.

The lemmas below are stated in a bare category, where no such unification is needed. Applied by
`exact`, their definitional equalities are discharged by the elaborator at default
transparency.

## Main results

* `CategoryTheory.comp_congr_eq`, `comp_congr_eq_left`, `comp_congr_both`,
  `comp_assoc_congr`: rewrite one or two factors of a composite, reassociating if needed.
* `CategoryTheory.comp_iso_hom_of_eq_comp_inv`,
  `CategoryTheory.comp_iso_hom_of_eq_comp_comp_inv`,
  `CategoryTheory.comp_comp_eq_of_eq_comp_inv`: cancel an `Iso.inv` against the `hom` that
  follows it, at three bracketings.
* `CategoryTheory.comp_chain_one_square`, `comp_chain_one_square_assoc`,
  `comp_chain_two_squares`, `comp_chain_braiding_four`: transport commuting squares across a
  composite of two, four or five morphisms.
* `CategoryTheory.iso_trans_chain_square`: the same for a composite of two *isomorphisms*
  written as `Iso.trans`.
* `CategoryTheory.braiding_transport`: transport a commutativity constraint across a pair of
  comparison isomorphisms.
-/

@[expose] public section

namespace CategoryTheory

open Category

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Rewriting factors of a composite -/

/-- Rewrite both factors of a composite and conclude. -/
lemma comp_congr_eq {W X Y : C} {a a' : W ⟶ X} {b b' : X ⟶ Y} {k : W ⟶ Y}
    (ha : a = a') (hb : b = b') (h : a' ≫ b' = k) : a ≫ b = k := by
  rwa [ha, hb]

/-- Rewrite the first factor of a composite and conclude. -/
lemma comp_congr_eq_left {W X Y : C} {a a' : W ⟶ X} {b : X ⟶ Y} {k : W ⟶ Y}
    (ha : a = a') (h : a' ≫ b = k) : a ≫ b = k := by
  rwa [ha]

/-- Rewrite one factor on each side of an equation between two composites. -/
lemma comp_congr_both {W X Y Z : C} {a : W ⟶ X} {b b' : X ⟶ Y} {c c' : W ⟶ Z} {d : Z ⟶ Y}
    (hb : b = b') (hc : c = c') (h : a ≫ b' = c' ≫ d) : a ≫ b = c ≫ d := by
  rwa [hb, hc]

/-- Rewrite the third factor of a composite of four and reassociate the first one. -/
lemma comp_assoc_congr {V W X Y Z T : C} (a₁ : V ⟶ W) (a₂ : W ⟶ X) (b : X ⟶ Y)
    {c c' : Y ⟶ Z} (d : Z ⟶ T) (hc : c = c') :
    (a₁ ≫ a₂) ≫ b ≫ c ≫ d = a₁ ≫ a₂ ≫ b ≫ c' ≫ d := by
  rw [hc, assoc]

/-! ### Cancelling an inverse -/

/-- If `g` is `f` followed by the inverse of `i`, then `g` followed by `i` is `f`. -/
lemma comp_iso_hom_of_eq_comp_inv {W X Y : C} (i : X ≅ Y) {f : W ⟶ Y} {g : W ⟶ X}
    (h : g = f ≫ i.inv) : g ≫ i.hom = f := by
  rw [h, assoc, i.inv_hom_id, comp_id]

/-- The same with the trailing inverse at the end of a composite of three. -/
lemma comp_iso_hom_of_eq_comp_comp_inv {W X Y Z : C} (i : Y ≅ Z) {u : W ⟶ Y} {a : W ⟶ X}
    {v : X ⟶ Z} (h : u = a ≫ v ≫ i.inv) : u ≫ i.hom = a ≫ v := by
  rw [h]; simp only [assoc, i.inv_hom_id, comp_id]

/-- Cancel an `Iso.inv` buried in the second factor against the `hom` that follows the whole
composite. -/
lemma comp_comp_eq_of_eq_comp_inv {W X X' Y : C} (i : X' ≅ Y) (a : W ⟶ X) (b : X ⟶ X')
    {cr : X ⟶ Y} {k : W ⟶ Y} (hb : b = cr ≫ i.inv) (hk : a ≫ cr = k) :
    (a ≫ b) ≫ i.hom = k := by
  simp only [hb, assoc, Iso.inv_hom_id, comp_id, hk]

/-! ### Transporting commuting squares -/

/-- Transport one commuting square across a composite of two morphisms and finish with a
second square. -/
lemma comp_chain_one_square {W X Y S T Z : C} {v : W ⟶ X} {b₃ : X ⟶ Y} {b₄ : Y ⟶ T}
    {a₃ : W ⟶ Z} {w : Z ⟶ Y} {a₄ : Z ⟶ S} {t : S ⟶ T}
    (h₁ : v ≫ b₃ = a₃ ≫ w) (h₂ : w ≫ b₄ = a₄ ≫ t) : v ≫ b₃ ≫ b₄ = a₃ ≫ a₄ ≫ t := by
  rw [← assoc, h₁, assoc, h₂]

/-- `comp_chain_one_square` with the two transported morphisms bracketed together on the
right. -/
lemma comp_chain_one_square_assoc {W X Y S T Z : C} {v : W ⟶ X} {b₃ : X ⟶ Y} {b₄ : Y ⟶ T}
    {a₃ : W ⟶ Z} {w : Z ⟶ Y} {a₄ : Z ⟶ S} {t : S ⟶ T}
    (h₁ : v ≫ b₃ = a₃ ≫ w) (h₂ : w ≫ b₄ = a₄ ≫ t) : v ≫ b₃ ≫ b₄ = (a₃ ≫ a₄) ≫ t :=
  (comp_chain_one_square h₁ h₂).trans (assoc a₃ a₄ t).symm

/-- **Paste two naturality squares across a composite of two isomorphisms written as
`Iso.trans`.**  This is `comp_chain_one_square` with each leg the `hom` of an `Iso.trans`; the
conclusion mentions the two `Iso.trans` terms themselves, not their unfolding by
`Iso.trans_hom`. -/
lemma iso_trans_chain_square {W X Y W' X' Y' : C} (α : W ≅ X) (α' : W' ≅ X') (β : X ≅ Y)
    (β' : X' ≅ Y') {u : W ⟶ W'} {v : X ⟶ X'} {w : Y ⟶ Y'}
    (hα : u ≫ α'.hom = α.hom ≫ v) (hβ : v ≫ β'.hom = β.hom ≫ w) :
    u ≫ (α' ≪≫ β').hom = (α ≪≫ β).hom ≫ w := by
  exact comp_chain_one_square_assoc hα hβ

/-- Transport two commuting squares across a composite and cancel at the end.

The hypotheses say that `θ₀`, `θ₁`, `θ₂` are the components of one natural transformation
read at three places, that `h₁` and `h₂` are its two naturality squares, and that `h₃`
identifies the last component composed with `d`.  The conclusion rewrites the composite
`θ₀ ≫ m₁ ≫ m₂ ≫ d ≫ t` as `l₁ ≫ l₂ ≫ u ≫ t`. -/
lemma comp_chain_two_squares {P₀ P₁ P₂ R₀ R₁ R₂ S T : C}
    {θ₀ : P₀ ⟶ R₀} {θ₁ : P₁ ⟶ R₁} {θ₂ : P₂ ⟶ R₂}
    {m₁ : R₀ ⟶ R₁} {m₂ : R₁ ⟶ R₂} {d : R₂ ⟶ S} {t : S ⟶ T}
    {l₁ : P₀ ⟶ P₁} {l₂ : P₁ ⟶ P₂} {u : P₂ ⟶ S}
    (h₁ : l₁ ≫ θ₁ = θ₀ ≫ m₁) (h₂ : l₂ ≫ θ₂ = θ₁ ≫ m₂) (h₃ : θ₂ ≫ d = u) :
    θ₀ ≫ m₁ ≫ m₂ ≫ d ≫ t = l₁ ≫ l₂ ≫ u ≫ t := by
  rw [← reassoc_of% h₁, ← reassoc_of% h₂, reassoc_of% h₃]

/-- **Transport a braiding across a composite of four comparison morphisms.**

Read `s` as the braiding of the ambient structure, `b₁ ≫ b₂ ≫ b₃ ≫ b₄` and
`a₁ ≫ a₂ ≫ a₃ ≫ a₄` as one comparison written at the two orders of the factors, and `t` as
the induced map.  The three hypotheses are the braiding transported across the first factor,
across the second, and across the last two at once. -/
lemma comp_chain_braiding_four {S₀ T₀ T₁ T₂ T₃ T₄ U₁ U₂ U₃ U₄ : C}
    {s : S₀ ⟶ T₀} {b₁ : T₀ ⟶ T₁} {b₂ : T₁ ⟶ T₂} {b₃ : T₂ ⟶ T₃} {b₄ : T₃ ⟶ T₄}
    {a₁ : S₀ ⟶ U₁} {u : U₁ ⟶ T₁} {a₂ : U₁ ⟶ U₂} {v : U₂ ⟶ T₂} {a₃ : U₂ ⟶ U₃}
    {a₄ : U₃ ⟶ U₄} {t : U₄ ⟶ T₄}
    (h₁ : s ≫ b₁ = a₁ ≫ u) (h₂ : u ≫ b₂ = a₂ ≫ v) (h₃ : v ≫ b₃ ≫ b₄ = a₃ ≫ a₄ ≫ t) :
    s ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ t := by
  simp only [assoc, reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- **Transport a commutativity constraint across a pair of comparison isomorphisms.**

Read `r` and `r'` as the two components of an isomorphism of tensor bifunctors, `b` as the
braiding of the source structure, `cKL`, `cLK` as the comparisons of the target structure with
a third object, `kKL`, `kLK` as the corresponding comparisons of the source structure, and `q`
as the induced map.  Then the braiding of the target structure, written as the conjugate of `b`
by `r` and `r'`, satisfies the same commutation. -/
lemma braiding_transport {O O' P P' Z Z' : C} (r : O ≅ P) (r' : O' ≅ P')
    {b : O ⟶ O'} {cKL : P ⟶ Z} {cLK : P' ⟶ Z'} {kKL : O ⟶ Z} {kLK : O' ⟶ Z'} {q : Z ⟶ Z'}
    (hKL : r.hom ≫ cKL = kKL) (hLK : r'.hom ≫ cLK = kLK) (hb : b ≫ kLK = kKL ≫ q) :
    (r.inv ≫ b ≫ r'.hom) ≫ cLK = cKL ≫ q := by
  rw [assoc, assoc, hLK, hb, ← hKL, assoc, r.inv_hom_id_assoc]

end CategoryTheory

end
