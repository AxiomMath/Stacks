module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareAction

/-!
# The comparison identity across a square of adjunctions descends along the unit

Continue with the square of adjunctions of
`StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareAction`, with projection formulas
`pf : Lf ⋙ Rf ≅ Tens` and `pf' : Lf' ⋙ Rf' ≅ Tens'` on the two horizontal edges, an
identification `γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf'` of the two composites around it and an identification
`Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg` of the base-change mate.  The comparison of the two endofunctors across
the square is `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso`, and the equation a lax
structure map `m : Lg ⋙ TensM ⟶ Tens ⋙ Lg` has to satisfy for the mate to be a morphism of
actions — the hypothesis `ha` of
`Stacks.CategoryTheory.BaseChange.action_comp_eq_of_tensorComparisonOfIso_natTrans` — is the
**comparison identity**

`m_X ≫ tensorComparisonOfIso X = n_{Lg X}`

for a transformation `n : TensM ⟶ Tens'` of the two endofunctors over the target.

This file proves that the comparison identity **descends along the unit**: it holds at an object
`X` as soon as it holds at `Rf (Lf X)`, the value of the monad of the left adjunction, with no
hypothesis on anything.

The mechanism is a retraction.  `Stacks.CategoryTheory.BaseChange.unitRetraction` is the
composite of `Tens'` applied to the mate, the action of `Tens'` over the target, `Rf'` of `γ` and
the projection formula over `A'`; it retracts `Tens'` applied to `Lg` of the unit
(`Stacks.CategoryTheory.BaseChange.map_unit_comp_unitRetraction`), and the whole of
`tensorComparisonOfIso` at `X` factors through the same retraction from its value at `Rf (Lf X)`
(`Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_unitRetraction`).  Composing with
`m` and using that `m` and `n` are natural turns the factorization into the descent.

Both proofs are the defining property of a mate and the two triangle identities.  The retraction
identity is `CategoryTheory.mateEquiv_counit` followed by the naturality of `γ`
and the left triangle identity of `Lf ⊣ Rf`, after which `γ` cancels against itself and the
projection formula over `A'` against itself.  The factorization is
`Stacks.CategoryTheory.BaseChange.inv_app_eq_map_unit_comp_action`, which writes the inverse
projection formula as `Tens` of the unit followed by the action, and
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_comp_action`, which is the statement that
the mate is a morphism of actions.

Nothing here is about rings, modules or derived categories.  Instantiated at the base-change
square of a Tor-independent pair of ring maps it says that the keystone obligation
`Dualizing.TensorComparisonCompatibility` of [stacks 0E2A] has to be checked only at objects
restricted from `D(A)`; that is
`Dualizing.tensorComparisonCompatibility_of_restrict_extend`.

## Main definitions

* `Stacks.CategoryTheory.BaseChange.unitRetraction` — the retraction of `Tens'` applied to `Lg` of
  the unit, built from the mate, the action over the target and the projection formula there.

## Main results

* `Stacks.CategoryTheory.BaseChange.map_unit_comp_unitRetraction` — **the unit is split after
  base change and tensoring.**  Neither the comparison nor any structure map occurs: the
  statement is about the mate, `γ`, the projection formula over `A'` and the two adjunctions
  alone.
* `Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_unitRetraction` — the
  comparison at `X`, composed with a lax structure map, factors through its value at `Rf (Lf X)`
  and the retraction.  Unconditional.
* `Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_of_monad` — **the descent**:
  the comparison identity at `Rf (Lf X)` implies it at `X`.

## Implementation notes

Everything is stated over variable categories and instantiated, as
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_eq_of_values` is and for the same reason:
at a concrete square the types are computed from the arguments instead of unified against a
second spelling of a long composite.

`n` is a bare transformation, not an isomorphism: the descent needs only its naturality.  The
converse direction is false in this generality — `Tens'` of `Lg` of the unit is split monic but
not invertible — so the two halves of the statement are not interchangeable, and the content is
that the comparison identity at the monad is the stronger of the two.

The three `have`s that restate a naturality square do so with the composites `(𝟭 A).obj X` and
`(Lf ⋙ Rf).obj X` in the unit's type already reduced, since `rw` matches syntactically and the
unreduced spellings are what `CategoryTheory.NatTrans.naturality` produces.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'}

/-- **The retraction of `Tens'` applied to `Lg` of the unit.**  At an object `X` the composite of
`Tens'` applied to the base-change mate at `Lf X`, the action of `Tens'` on `Rf' (Lg' (Lf X))`,
`Rf'` applied to the comparison `γ` of the two composites around the square at `X`, and the
projection formula over `A'` at `Lg X`.

It is the last three factors of `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` at
`Rf (Lf X)` with the mate's component moved inside `Tens'`, and
`Stacks.CategoryTheory.BaseChange.map_unit_comp_unitRetraction` is that it retracts `Tens'`
applied to `Lg` of the unit at `X`. -/
def unitRetraction {Tens' : A' ⥤ A'} (adjf' : Lf' ⊣ Rf') (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg) (X : A) :
    Tens'.obj (Lg.obj (Rf.obj (Lf.obj X))) ⟶ Tens'.obj (Lg.obj X) :=
  Tens'.map (Θ.inv.app (Lf.obj X)) ≫ action adjf' pf' (Lg'.obj (Lf.obj X)) ≫
    Rf'.map (γ.hom.app X) ≫ pf'.hom.app (Lg.obj X)

/-- **The unit is split after base change and tensoring.**  `Tens'` applied to `Lg` of the unit
of `Lf ⊣ Rf` at `X` is a split monomorphism, retracted by
`Stacks.CategoryTheory.BaseChange.unitRetraction`.

Neither the comparison across the square nor any lax structure map occurs.  The proof is the
defining property `CategoryTheory.mateEquiv_counit` of the mate, which replaces
`Lf'` of the mate followed by the counit over `A'` by `γ⁻¹` followed by `Lg'` of the counit over
`A`; the naturality of `γ⁻¹` at the unit; the left triangle identity of `Lf ⊣ Rf`, which collapses
`Lf` of the unit followed by the counit to the identity; and then `γ` and the projection formula
over `A'` each cancelling against themselves. -/
theorem map_unit_comp_unitRetraction {Tens' : A' ⥤ A'} (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (X : A) :
    Tens'.map (Lg.map (adjf.unit.app X)) ≫ unitRetraction adjf' pf' γ Θ X =
      𝟙 (Tens'.obj (Lg.obj X)) := by
  have hcounit : Lf'.map (Θ.inv.app (Lf.obj X)) ≫ adjf'.counit.app (Lg'.obj (Lf.obj X)) =
      γ.inv.app (Rf.obj (Lf.obj X)) ≫ Lg'.map (adjf.counit.app (Lf.obj X)) := by
    have h := mateEquiv_counit adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) (Lf.obj X)
    rw [hα] at h
    exact h
  have hnat : Lf'.map (Lg.map (adjf.unit.app X)) ≫ γ.inv.app (Rf.obj (Lf.obj X)) =
      γ.inv.app X ≫ Lg'.map (Lf.map (adjf.unit.app X)) := by
    have h := γ.inv.naturality (adjf.unit.app X)
    dsimp only [Functor.comp_map] at h
    exact h
  have hbracket : (Lf'.map (Lg.map (adjf.unit.app X) ≫ Θ.inv.app (Lf.obj X)) ≫
      adjf'.counit.app (Lg'.obj (Lf.obj X))) ≫ γ.hom.app X = 𝟙 (Lf'.obj (Lg.obj X)) := by
    rw [Lf'.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hcounit, reassoc_of% hnat, ← Lg'.map_comp_assoc,
      adjf.left_triangle_components, Lg'.map_id, Category.id_comp]
    exact γ.inv_hom_id_app X
  have hpf := pf'.inv.naturality (Lg.map (adjf.unit.app X) ≫ Θ.inv.app (Lf.obj X))
  dsimp only [Functor.comp_map] at hpf
  rw [unitRetraction, action]
  simp only [Category.assoc]
  rw [← Tens'.map_comp_assoc, reassoc_of% hpf, ← Rf'.map_comp_assoc, ← Rf'.map_comp_assoc,
    hbracket, Rf'.map_id, Category.id_comp, pf'.inv_hom_id_app]

/-- **The comparison across the square, composed with a lax structure map, factors through its
value at the monad.**  Unconditionally, for any `m : Lg ⋙ TensM ⟶ Tens ⋙ Lg`, the composite
`m_X ≫ tensorComparisonOfIso X` is `TensM` applied to `Lg` of the unit, then the same composite at
`Rf (Lf X)`, then `Stacks.CategoryTheory.BaseChange.unitRetraction`.

Two inputs: `Stacks.CategoryTheory.BaseChange.inv_app_eq_map_unit_comp_action`, which writes the
inverse projection formula over `A` at `X` as `Tens` of the unit followed by the action on
`Rf (Lf X)`, and `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_comp_action`, the
statement that the mate is a morphism of actions, which replaces `Lg` of that action followed by
the mate by the comparison at `Rf (Lf X)` followed by the first two factors of the retraction.
The naturality of `m` at the unit then moves `Tens` of the unit across it. -/
theorem comp_tensorComparisonOfIso_eq_unitRetraction {Tens : A ⥤ A} {Tens' TensM : A' ⥤ A'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (m : Lg ⋙ TensM ⟶ Tens ⋙ Lg) (X : A) :
    m.app X ≫ tensorComparisonOfIso pf pf' γ Θ X =
      TensM.map (Lg.map (adjf.unit.app X)) ≫
        (m.app (Rf.obj (Lf.obj X)) ≫
            tensorComparisonOfIso pf pf' γ Θ (Rf.obj (Lf.obj X))) ≫
          unitRetraction adjf' pf' γ Θ X := by
  have hm : TensM.map (Lg.map (adjf.unit.app X)) ≫ m.app (Rf.obj (Lf.obj X)) =
      m.app X ≫ Lg.map (Tens.map (adjf.unit.app X)) := m.naturality (adjf.unit.app X)
  have hC : tensorComparisonOfIso pf pf' γ Θ X =
      Lg.map (Tens.map (adjf.unit.app X)) ≫
        tensorComparisonOfIso pf pf' γ Θ (Rf.obj (Lf.obj X)) ≫
          unitRetraction adjf' pf' γ Θ X := by
    rw [unitRetraction, tensorComparisonOfIso, tensorComparisonOfIso,
      inv_app_eq_map_unit_comp_action adjf pf X, Lg.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (Lg.map (action adjf pf (Lf.obj X))),
      ← tensorComparisonOfIso_comp_action adjf adjf' pf pf' γ Θ hα (Lf.obj X),
      tensorComparisonOfIso]
    simp only [Category.assoc]
  rw [hC, ← Category.assoc, ← hm]
  simp only [Category.assoc]

/-- **The comparison identity descends from the monad to the object.**  If a lax structure map
`m` satisfies the comparison identity `m ≫ tensorComparisonOfIso = n` at `Rf (Lf X)`, it satisfies
it at `X`.

`Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_unitRetraction` factors the
left-hand side at `X` through its value at `Rf (Lf X)`; substituting the hypothesis there and
moving `n` across `TensM` applied to `Lg` of the unit by naturality leaves `n` at `Lg X` followed
by the split monomorphism and its retraction, which is
`Stacks.CategoryTheory.BaseChange.map_unit_comp_unitRetraction`.

So the comparison identity has to be checked only on the image of the monad `Rf ⋙ Lf`.  Nothing
is assumed invertible, and `n` is a bare transformation. -/
theorem comp_tensorComparisonOfIso_eq_of_monad {Tens : A ⥤ A} {Tens' TensM : A' ⥤ A'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (n : TensM ⟶ Tens') (m : Lg ⋙ TensM ⟶ Tens ⋙ Lg) (X : A)
    (h : m.app (Rf.obj (Lf.obj X)) ≫
        tensorComparisonOfIso pf pf' γ Θ (Rf.obj (Lf.obj X)) =
      n.app (Lg.obj (Rf.obj (Lf.obj X)))) :
    m.app X ≫ tensorComparisonOfIso pf pf' γ Θ X = n.app (Lg.obj X) := by
  have hn : TensM.map (Lg.map (adjf.unit.app X)) ≫ n.app (Lg.obj (Rf.obj (Lf.obj X))) =
      n.app (Lg.obj X) ≫ Tens'.map (Lg.map (adjf.unit.app X)) :=
    n.naturality (Lg.map (adjf.unit.app X))
  rw [comp_tensorComparisonOfIso_eq_unitRetraction adjf adjf' pf pf' γ Θ hα m X, h,
    ← Category.assoc, hn, Category.assoc,
    map_unit_comp_unitRetraction adjf adjf' pf' γ Θ hα X]
  exact Category.comp_id _

end Stacks.CategoryTheory.BaseChange

end
