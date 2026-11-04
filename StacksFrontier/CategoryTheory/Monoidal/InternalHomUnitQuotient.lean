module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Internal homs into a quotient of the monoidal unit

Let `C` be a monoidal closed category whose monoidal structure is additive, let `H` be a
quotient of the monoidal unit — an object together with an epimorphism `p : 𝟙_C ⟶ H` — and let
`j : A ⟶ 𝟙_C` be a morphism whose composite with `p` vanishes. Then restriction of internal homs
along `j`,

`(MonoidalClosed.pre j).app H : (𝟙_C ⟶[C] H) ⟶ (A ⟶[C] H)`,

is zero: every internal homomorphism out of the unit restricts to zero on `A`.

In the motivating case `C` is the category of modules over a commutative ring object, `H` is the
quotient of that ring object by an ideal `A`, and the statement is that an ideal annihilates
every homomorphism out of the ring into the quotient by it — the fact which makes the internal
endomorphisms of such a quotient be the quotient itself.

The proof is a unitor computation. Under the tensor–hom adjunction the morphism in question
transposes to `j ▷ (𝟙_C ⟶[C] H)` followed by evaluation; the internal hom out of the unit is the
identity functor, which turns evaluation into the left unitor of `H`; and tensoring on the left
by `A` preserves the epimorphism `p`, so it suffices to compute after tensoring with it, where
naturality of the two unitors and their agreement at the unit reduce the composite to
`j ≫ p = 0`.

## Main statements

* `Stacks.MonoidalClosed.uncurry_unitNatIso_app`: **the transpose of the comparison of `H` with
  the internal hom out of the unit is the left unitor of `H`.**
* `Stacks.MonoidalClosed.whiskerRight_leftUnitor_eq_zero`: a morphism into the unit whose
  composite with an epimorphism out of the unit vanishes induces, after tensoring on the right
  by the target of that epimorphism and composing with the left unitor, the zero morphism.
* `Stacks.MonoidalClosed.pre_app_eq_zero_of_unit`: **restriction of internal homs out of the
  unit along such a morphism is zero.**
* `Stacks.MonoidalClosed.pre_app_eq_zero`: the same for a morphism into any object identified
  with the unit, which is the form a concrete monoidal structure takes, its unit being the
  expected object only up to isomorphism.

## Implementation notes

The additivity hypothesis `MonoidalPreadditive` is used only to know that the transpose of a
zero morphism is zero, which is where the conclusion "is the zero morphism" rather than "is
annihilated by the epimorphism" comes from. The hypothesis that tensoring preserves the
epimorphism is not imposed: in a monoidal closed category tensoring on the left is a left
adjoint, hence preserves all colimits and in particular epimorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed

universe v u

namespace Stacks.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [CategoryTheory.MonoidalClosed C]
  [Preadditive C] [MonoidalPreadditive C]

/-- A composite out of `B ⊗ Y` vanishes after whiskering `j` on the right by `Y` once it does so
after whiskering by an `X ⟶ Y` that stays epi when whiskered on the left by the source of `j`. -/
private theorem whiskerRight_comp_eq_zero_of_whiskerLeft_epi {D : Type u} [Category.{v} D]
    [MonoidalCategory D] [Preadditive D] {A B X Y Z : D} (j : A ⟶ B) (f : X ⟶ Y) [Epi (A ◁ f)]
    (g : B ⊗ Y ⟶ Z) (h : (j ▷ X) ≫ (B ◁ f) ≫ g = 0) : (j ▷ Y) ≫ g = 0 := by
  refine (cancel_epi (A ◁ f)).1 ?_
  rw [comp_zero, ← Category.assoc, whisker_exchange, Category.assoc, h]

/-- The transpose of the zero morphism into an internal hom is zero: the transpose is
postcomposition of a whiskering with the evaluation, and whiskering an additive monoidal
structure by zero is zero. -/
theorem uncurry_eq_zero {A X Y : C} : uncurry (0 : Y ⟶ (ihom A).obj X) = 0 := by
  rw [uncurry_eq, MonoidalPreadditive.whiskerLeft_zero, zero_comp]

omit [Preadditive C] [MonoidalPreadditive C] in
/-- **The transpose of the comparison of `X` with the internal hom out of the unit is the left
unitor of `X`.** The comparison is the conjugate, along the tensor–hom adjunctions, of the
natural isomorphism between tensoring by the unit and the identity functor, and the transpose of
a conjugate is computed by the counits of the two adjunctions: the evaluation on one side and
the identity on the other. -/
theorem uncurry_unitNatIso_app (X : C) :
    uncurry (unitNatIso.app X).hom = (λ_ X).hom := by
  rw [uncurry_eq]
  exact (conjugateEquiv_counit (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom X).trans (Category.comp_id _)

omit [MonoidalPreadditive C] in
/-- A morphism `j : A ⟶ 𝟙_C` into the monoidal unit whose composite with an epimorphism
`p : 𝟙_C ⟶ H` vanishes induces the zero morphism `A ⊗ H ⟶ H` by tensoring on the right by `H`
and composing with the left unitor.

Tensoring on the left by `A` preserves the epimorphism `p`, so it is enough to compute after
tensoring with it; the two whiskerings then commute, the left unitor is natural, it agrees with
the right unitor at the unit, and the right unitor is natural, which leaves `j ≫ p`. -/
theorem whiskerRight_leftUnitor_eq_zero {A H : C} (j : A ⟶ 𝟙_ C) (p : 𝟙_ C ⟶ H) [Epi p]
    (h : j ≫ p = 0) : (j ▷ H) ≫ (λ_ H).hom = 0 := by
  have : Epi (A ◁ p) := inferInstanceAs (Epi ((tensorLeft A).map p))
  refine whiskerRight_comp_eq_zero_of_whiskerLeft_epi j p _ ?_
  rw [leftUnitor_naturality, unitors_equal, ← Category.assoc, rightUnitor_naturality,
    Category.assoc, h, comp_zero]

/-- **Restriction of internal homs out of the monoidal unit along a morphism that dies in a
quotient of the unit is zero.** Let `p : 𝟙_C ⟶ H` be an epimorphism and let `j : A ⟶ 𝟙_C`
satisfy `j ≫ p = 0`. Transposing, the restriction map becomes the whiskering of `j` followed by
evaluation; comparing the internal hom out of the unit with the identity turns that into the
left unitor of `H` precomposed with `j ▷ H`, which vanishes. -/
theorem pre_app_eq_zero_of_unit {A H : C} (j : A ⟶ 𝟙_ C) (p : 𝟙_ C ⟶ H) [Epi p]
    (h : j ≫ p = 0) : (pre j).app H = 0 := by
  refine uncurry_injective ?_
  rw [uncurry_pre, uncurry_eq_zero]
  refine whiskerRight_comp_eq_zero_of_whiskerLeft_epi j (unitNatIso.app H).hom _ ?_
  rw [← uncurry_eq, uncurry_unitNatIso_app]
  exact whiskerRight_leftUnitor_eq_zero j p h

/-- **Restriction of internal homs out of an object identified with the monoidal unit, along a
morphism that dies in a quotient of that object, is zero.** This is the previous statement for a
monoidal structure whose unit is the expected object only up to isomorphism: restriction along
the isomorphism is itself an isomorphism, so it can be cancelled. -/
theorem pre_app_eq_zero {A U H : C} (e : 𝟙_ C ≅ U) (j : A ⟶ U) (p : U ⟶ H) [Epi p]
    (h : j ≫ p = 0) : (pre j).app H = 0 := by
  have key := pre_app_eq_zero_of_unit (j ≫ e.inv) (e.hom ≫ p) (by rw [Category.assoc,
    ← Category.assoc e.inv e.hom p, e.inv_hom_id, Category.id_comp, h])
  rw [show pre j = pre e.hom ≫ pre (j ≫ e.inv) by
    rw [← pre_map, Category.assoc, e.inv_hom_id, Category.comp_id], NatTrans.comp_app, key,
    comp_zero]

end Stacks.MonoidalClosed

end
