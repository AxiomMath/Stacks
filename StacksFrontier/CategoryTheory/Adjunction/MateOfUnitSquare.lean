module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Recognising a mate from the square it makes with the two units

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions and let

```
      L₁                  R₁
   C --→ D             C ←-- D
 G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
   E --→ F             E ←-- F
      L₂                  R₂
```

be a 2-square `α : G ⋙ L₂ ⟶ L₁ ⋙ H` together with a candidate `β : R₁ ⋙ G ⟶ H ⋙ R₂` for its
mate.  `CategoryTheory.mateEquiv` identifies the two kinds of square, and
`CategoryTheory.mateEquiv_counit` computes the adjoint transpose of a mate; a candidate is
therefore recognised as the mate as soon as the *counit* identity holds.

This file provides the recognition criterion in terms of the two **units** instead: if

`adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) = G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)`

for every object `c`, then `β` is the mate of `α`.  Granting that, the counit identity comes out
as a conclusion rather than as a hypothesis.

## Main results

* `CategoryTheory.mateEquiv_eq_of_unit` and `CategoryTheory.mateEquiv_symm_eq_of_unit`: the
  recognition criterion, in both directions of `CategoryTheory.mateEquiv`.
* `CategoryTheory.map_counit_comp_of_unit`: **the counit identity, deduced from the unit
  identity.**  The transpose `L₂.map (β.app d) ≫ adj₂.counit.app _` of a component of `β` is the
  component `α.app (R₁.obj d)` of `α` followed by the image `H.map (adj₁.counit.app d)` of the
  counit of `adj₁`.
* `CategoryTheory.unit_square_whisker`: **the unit identity transports along isomorphisms of the
  two vertical functors.**  Replacing `G` and `H` by isomorphic functors and whiskering both
  squares by those isomorphisms preserves the identity, so the whiskered pair is again a mate
  pair.  This is what lets a mate identification proved at one spelling of the two vertical
  functors be read at another.
* `CategoryTheory.unit_square_iff_transpose`: **the unit identity with the unit of `adj₂`
  removed.**  Transposing both sides across `adj₂` leaves `α.app c` on the left, so the identity
  is equivalent to one mentioning only `α`, the unit of `adj₁`, `β` and the *counit* of `adj₂`.
* `CategoryTheory.unit_square_of_iso` and `CategoryTheory.unit_square_of_representatives`:
  **the unit identity transports along an isomorphism of the object it is stated at**, and
  therefore holds everywhere as soon as it holds at a family of objects every object is
  isomorphic to one of.  Both of its sides are components of a natural transformation
  `G ⟶ L₁ ⋙ H ⋙ R₂`, so this is naturality on both sides together with the transfer of an
  equation along an isomorphism.

## Implementation notes

The units of two adjunctions are often computable where the counits are not: a left adjoint
built as a composite of a sectionwise construction with a sheafification has a unit which is
read off on sections, while its counit is only characterised by a universal property.  The
criterion here is what lets such an adjunction be fed to the mates correspondence.

The proof is the triangle identity of `adj₁` together with the naturality of `β`: the adjoint
transpose of `α.app (R₁.obj d) ≫ H.map (adj₁.counit.app d)` is `adj₂.unit` followed by `R₂` of
that composite, which the unit identity rewrites into `G.map (adj₁.unit.app (R₁.obj d))`
followed by `β.app (L₁.obj (R₁.obj d)) ≫ R₂.map (H.map (adj₁.counit.app d))`; naturality of `β`
turns the latter into `G.map (R₁.map (adj₁.counit.app d)) ≫ β.app d`, and the triangle identity
collapses the two images under `G` to the identity.
-/

@[expose] public section

open CategoryTheory Category Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
variable {G G' : C ⥤ E} {H H' : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **A 2-square whose unit square commutes is the mate.**  If `α : G ⋙ L₂ ⟶ L₁ ⋙ H` and
`β : R₁ ⋙ G ⟶ H ⋙ R₂` satisfy the square made by the units of the two adjunctions, then `β` is
the mate of `α`. -/
theorem mateEquiv_eq_of_unit (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (h : ∀ c : C, adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) =
      G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)) :
    mateEquiv adj₁ adj₂ α = β := by
  refine NatTrans.ext (funext fun d => ?_)
  have key : adj₂.unit.app (G.obj (R₁.obj d)) ≫
      R₂.map (α.app (R₁.obj d) ≫ H.map (adj₁.counit.app d)) = β.app d := by
    rw [Functor.map_comp, ← assoc, h (R₁.obj d), assoc]
    have hnat := β.naturality (adj₁.counit.app d)
    dsimp at hnat ⊢
    rw [← hnat, ← Functor.map_comp_assoc, adj₁.right_triangle_components, Functor.map_id, id_comp]
  dsimp [mateEquiv]
  rw [← key]
  simp

/-- **A 2-square whose unit square commutes is the mate**, in the direction that produces the
square over the left adjoints from the square over the right adjoints. -/
theorem mateEquiv_symm_eq_of_unit (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (h : ∀ c : C, adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) =
      G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)) :
    (mateEquiv adj₁ adj₂).symm β = α := by
  rw [← mateEquiv_eq_of_unit adj₁ adj₂ α β h, Equiv.symm_apply_apply]

/-- **The counit identity for a pair of 2-squares whose unit square commutes.**  The adjoint
transpose under `adj₂` of a component of `β` is the corresponding component of `α` followed by
the image under `H` of the counit of `adj₁`.

This is `CategoryTheory.mateEquiv_counit_symm` with the mate identified by
`CategoryTheory.mateEquiv_symm_eq_of_unit`. -/
theorem map_counit_comp_of_unit (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (h : ∀ c : C, adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) =
      G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)) (d : D) :
    L₂.map (β.app d) ≫ adj₂.counit.app (H.obj d) =
      α.app (R₁.obj d) ≫ H.map (adj₁.counit.app d) := by
  rw [mateEquiv_counit_symm adj₁ adj₂ β d, mateEquiv_symm_eq_of_unit adj₁ adj₂ α β h]

/-- **The unit identity transports along isomorphisms of the two vertical functors.**  If `α`
and `β` satisfy the unit identity and `cG : G ≅ G'`, `cH : H ≅ H'`, then the squares obtained by
whiskering `α` and `β` with `cG` and `cH` satisfy it as well.

Consequently the whiskered pair is again a mate pair, by
`CategoryTheory.mateEquiv_eq_of_unit`. -/
theorem unit_square_whisker (cG : G ≅ G') (cH : H ≅ H') (α : TwoSquare G L₁ L₂ H)
    (β : TwoSquare R₁ H G R₂)
    (h : ∀ c : C, adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) =
      G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)) (c : C) :
    adj₂.unit.app (G'.obj c) ≫ R₂.map
        ((Functor.whiskerRight cG.inv L₂ ≫ α ≫ Functor.whiskerLeft L₁ cH.hom).app c) =
      G'.map (adj₁.unit.app c) ≫
        (Functor.whiskerLeft R₁ cG.inv ≫ β ≫ Functor.whiskerRight cH.hom R₂).app
          (L₁.obj c) := by
  change adj₂.unit.app (G'.obj c) ≫
      R₂.map (L₂.map (cG.inv.app c) ≫ α.app c ≫ cH.hom.app (L₁.obj c)) =
    G'.map (adj₁.unit.app c) ≫ cG.inv.app (R₁.obj (L₁.obj c)) ≫
      β.app (L₁.obj c) ≫ R₂.map (cH.hom.app (L₁.obj c))
  have hu := adj₂.unit.naturality (cG.inv.app c)
  have hnat := cG.inv.naturality (adj₁.unit.app c)
  have hh := h c
  dsimp at hu hnat hh
  rw [Functor.map_comp, Functor.map_comp, ← assoc, ← hu, assoc, reassoc_of% hh,
    reassoc_of% hnat]

/-! ### The unit identity transposed -/

/-- **The unit identity, transposed across `adj₂`.**  Both of its sides are morphisms into
`R₂.obj (H.obj (L₁.obj c))`, so the identity is equivalent to the equality of their adjoint
transposes; and the transpose of the left-hand side is `α.app c` itself, because the left-hand
side *is* the transpose of `α.app c`.

What this buys is that the unit of `adj₂` no longer occurs: the restated identity mentions only
`α`, the unit of `adj₁`, `β` and the **counit** of `adj₂`.  When — as for the derived
extension-of-scalars adjunction — the counit is computed on a distinguished family of objects
and the unit is not, this is the form to work with. -/
theorem unit_square_iff_transpose (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂) (c : C) :
    (adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) =
        G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)) ↔
      α.app c = L₂.map (G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) := by
  have hL : adj₂.homEquiv (G.obj c) (H.obj (L₁.obj c)) (α.app c) =
      adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) :=
    adj₂.homEquiv_unit _ _ _
  have hR : (adj₂.homEquiv (G.obj c) (H.obj (L₁.obj c))).symm
        (G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)) =
      L₂.map (G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) :=
    adj₂.homEquiv_counit _ _ _
  constructor
  · intro h
    rw [← hR, ← hL.trans h, Equiv.symm_apply_apply]
  · intro h
    rw [← hL, h, ← hR, Equiv.apply_symm_apply]

/-! ### Checking the unit identity at representatives -/

/-- **Both sides of the unit identity are natural in the object**, so the identity transports
along an isomorphism `e : c ≅ c'`: if it holds at `c` it holds at `c'`.

Each side is a component of a natural transformation `G ⟶ L₁ ⋙ H ⋙ R₂` — on the left the unit
of `adj₂` followed by `R₂` of `α`, on the right `G` of the unit of `adj₁` followed by `β` — and
`G.map e.hom` is invertible, so the two naturality squares carry the equation across. -/
theorem unit_square_of_iso (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂) {c c' : C}
    (e : c ≅ c')
    (h : adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) =
      G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)) :
    adj₂.unit.app (G.obj c') ≫ R₂.map (α.app c') =
      G.map (adj₁.unit.app c') ≫ β.app (L₁.obj c') := by
  have hu₁ : e.hom ≫ adj₁.unit.app c' = adj₁.unit.app c ≫ R₁.map (L₁.map e.hom) :=
    adj₁.unit.naturality e.hom
  have hu₂ : G.map e.hom ≫ adj₂.unit.app (G.obj c') =
      adj₂.unit.app (G.obj c) ≫ R₂.map (L₂.map (G.map e.hom)) :=
    adj₂.unit.naturality (G.map e.hom)
  have hα : L₂.map (G.map e.hom) ≫ α.app c' = α.app c ≫ H.map (L₁.map e.hom) :=
    α.naturality e.hom
  have hβ : G.map (R₁.map (L₁.map e.hom)) ≫ β.app (L₁.obj c') =
      β.app (L₁.obj c) ≫ R₂.map (H.map (L₁.map e.hom)) :=
    β.naturality (L₁.map e.hom)
  have hleft : G.map e.hom ≫ adj₂.unit.app (G.obj c') ≫ R₂.map (α.app c') =
      (adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c)) ≫ R₂.map (H.map (L₁.map e.hom)) := by
    rw [← assoc, hu₂, assoc, ← R₂.map_comp, hα, R₂.map_comp, assoc]
  have hright : G.map e.hom ≫ G.map (adj₁.unit.app c') ≫ β.app (L₁.obj c') =
      (G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c)) ≫ R₂.map (H.map (L₁.map e.hom)) := by
    rw [← G.map_comp_assoc, hu₁, G.map_comp_assoc, hβ, assoc]
  have : IsIso (G.map e.hom) := (G.mapIso e).isIso_hom
  rw [← cancel_epi (G.map e.hom), hleft, hright, h]

/-- **The unit identity holds everywhere as soon as it holds at representatives.**  If every
object of `C` is isomorphic to one satisfying `S`, then the unit identity at the objects
satisfying `S` already gives it at every object, and so by
`CategoryTheory.mateEquiv_eq_of_unit` identifies `β` as the mate of `α`.

This is how a mate identification whose two sides can only be computed at a restricted family —
localized complexes, or K-flat ones — is extended to the whole category. -/
theorem unit_square_of_representatives (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (S : C → Prop) (hS : ∀ c : C, ∃ s : C, S s ∧ Nonempty (s ≅ c))
    (h : ∀ s : C, S s → adj₂.unit.app (G.obj s) ≫ R₂.map (α.app s) =
      G.map (adj₁.unit.app s) ≫ β.app (L₁.obj s)) (c : C) :
    adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) =
      G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c) := by
  obtain ⟨s, hs, ⟨e⟩⟩ := hS c
  exact unit_square_of_iso adj₁ adj₂ α β e (h s hs)

end CategoryTheory

end
