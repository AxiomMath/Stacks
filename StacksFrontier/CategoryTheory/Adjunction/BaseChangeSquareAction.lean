module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# The base change mate of a square of adjunctions is a morphism of actions

Consider a square of adjunctions

```
     Lf
  A ---→ B
Lg |     | Lg'
   v     v
  A' --→ B'
     Lf'
```

with `Lf ⊣ Rf`, `Lf' ⊣ Rf'` and the two composites around the square identified with one functor
`Lc` by `eg : Lg ⋙ Lf' ≅ Lc` and `ef : Lf ⋙ Lg' ≅ Lc`, so that
`Stacks.CategoryTheory.BaseChange.map` is the base change morphism
`Lg (Rf K) ⟶ Rf' (Lg' K)`.

Suppose in addition that each of the two monads `Lf ⋙ Rf` and `Lf' ⋙ Rf'` is identified with an
endofunctor of the base, by isomorphisms `pf : Lf ⋙ Rf ≅ Tens` and `pf' : Lf' ⋙ Rf' ≅ Tens'`.
This is the shape of a *projection formula*: for `Lf` extension of scalars along a ring map
`R → A` and `Rf` restriction, `Lf ⋙ Rf` is tensoring with `A` over `R`.  Through `pf` every
object `Rf K` carries an action

`Tens (Rf K) ⟶ Rf (Lf (Rf K)) ⟶ Rf K`

— the inverse of the projection formula followed by `Rf` of the counit — which is
`Stacks.CategoryTheory.BaseChange.action`, and likewise over `A'`.

The content of this file is that **the base change mate is a morphism of actions**: there is a
canonical comparison `Stacks.CategoryTheory.BaseChange.tensorComparison`

`Lg (Tens X) ⟶ Tens' (Lg X)`,

built from the mate at `Lf X` and the two identifications of the composites around the square,
and the square it makes with the two actions and the mate commutes
(`Stacks.CategoryTheory.BaseChange.tensorComparison_comp_action`).  No invertibility of anything
is assumed; when the comparison is invertible, the statement is the expected one
(`Stacks.CategoryTheory.BaseChange.action_comp_map`), with the comparison's inverse in front of
the base-changed action.

Nothing here is about rings, modules or derived categories: the projection formulas, the two
actions and the mate are the only data.

## Main definitions

* `Stacks.CategoryTheory.BaseChange.action` — the action of `Tens` on `Rf K` carried by a
  projection formula.
* `Stacks.CategoryTheory.BaseChange.tensorComparison` — the canonical comparison
  `Lg (Tens X) ⟶ Tens' (Lg X)` of the two endofunctors across `Lg`, built from the mate.

## Main results

* `Stacks.CategoryTheory.BaseChange.tensorComparison_comp_action_of_mate` — **the mate is a
  morphism of actions**, in the form that needs neither `Lc` nor the pair `eg`, `ef` nor any
  invertibility: a 2-cell `α : Lg ⋙ Lf' ⟶ Lf ⋙ Lg'`, a 2-cell `β` identified with its mate, and
  one morphism retracting `Rf'.map (α.app (Rf W))`.
* `Stacks.CategoryTheory.BaseChange.tensorComparison_comp_action` — the same statement for
  `Stacks.CategoryTheory.BaseChange.tensorComparison`, obtained from it.
* `Stacks.CategoryTheory.BaseChange.action_comp_map` — the same equation solved for the
  base-changed action, when the comparison is invertible.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']

/-- **The action carried by a projection formula.**  An identification `pf : Lf ⋙ Rf ≅ Tens` of
the monad of an adjunction `Lf ⊣ Rf` with an endofunctor `Tens` of the base makes every object
`Rf K` into an object with a `Tens`-action: the inverse of `pf` followed by `Rf` applied to the
counit.

For `Lf` derived extension of scalars along a ring map `R → A`, `Rf` derived restriction and
`Tens` derived tensoring with `A` over `R`, this is the `A`-module structure of the restriction of
an object of `D(A)`. -/
def action {Lf : A ⥤ B} {Rf : B ⥤ A} {Tens : A ⥤ A} (adjf : Lf ⊣ Rf) (pf : Lf ⋙ Rf ≅ Tens)
    (K : B) : Tens.obj (Rf.obj K) ⟶ Rf.obj K :=
  pf.inv.app (Rf.obj K) ≫ Rf.map (adjf.counit.app K)

variable {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc : A ⥤ B'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  {Tens : A ⥤ A} {Tens' : A' ⥤ A'} (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')

/-- **The comparison of the two endofunctors across the square.**  At an object `X` of `A` the
morphism `Lg (Tens X) ⟶ Tens' (Lg X)` given by the inverse projection formula at `X`, the base
change mate at `Lf X`, the comparison of the two composites around the square, and the projection
formula over `A'` at `Lg X`.

For the square of derived categories of a square of rings, with `Lg` derived base change along
`R → R'` and `Tens`, `Tens'` derived tensoring with the two algebras, this is the comparison
`(X ⊗ᴸ_R A) ⊗ᴸ_R R' ⟶ (X ⊗ᴸ_R R') ⊗ᴸ_{R'} A'` of the two ways of tensoring with the algebra and
base changing. -/
def tensorComparison (X : A) : Lg.obj (Tens.obj X) ⟶ Tens'.obj (Lg.obj X) :=
  Lg.map (pf.inv.app X) ≫ map adjf adjf' eg ef (Lf.obj X) ≫
    Rf'.map (ef.hom.app X ≫ eg.inv.app X) ≫ pf'.hom.app (Lg.obj X)

/-- **The base change mate is a morphism of actions: the form with no identification of the two
composites around the square.**  For a 2-cell `α : Lg ⋙ Lf' ⟶ Lf ⋙ Lg'` with mate `β` and a
morphism `k` retracting `Rf'.map (α.app (Rf W))`, the square made by the comparison built from
`β` and `k`, `Tens'` applied to `β` at `W`, the two actions, and `β` at `W` commutes. Taking `k`
to be `Rf'` of a quasi-inverse of `α` recovers
`Stacks.CategoryTheory.BaseChange.tensorComparison_comp_action`.

For derived base change along a Tor-independent pair of ring maps, `β` is the comparison of
[stacks 0661]. -/
theorem tensorComparison_comp_action_of_mate (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    {Tens : A ⥤ A} {Tens' : A' ⥤ A'} (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (α : TwoSquare Lg Lf Lf' Lg') (β : TwoSquare Rf Lg' Lg Rf')
    (hα : mateEquiv adjf adjf' α = β) (W : B)
    (k : Rf'.obj (Lg'.obj (Lf.obj (Rf.obj W))) ⟶ Rf'.obj (Lf'.obj (Lg.obj (Rf.obj W))))
    (hk : k ≫ Rf'.map (α.app (Rf.obj W)) = 𝟙 _) :
    (Lg.map (pf.inv.app (Rf.obj W)) ≫ β.app (Lf.obj (Rf.obj W)) ≫ k ≫
          pf'.hom.app (Lg.obj (Rf.obj W))) ≫
        Tens'.map (β.app W) ≫ action adjf' pf' (Lg'.obj W) =
      Lg.map (action adjf pf W) ≫ β.app W := by
  have hcounit : Lf'.map (β.app W) ≫ adjf'.counit.app (Lg'.obj W) =
      α.app (Rf.obj W) ≫ Lg'.map (adjf.counit.app W) := by
    rw [← hα]; exact mateEquiv_counit adjf adjf' α W
  have hcounit' : Rf'.map (Lf'.map (β.app W)) ≫ Rf'.map (adjf'.counit.app (Lg'.obj W)) =
      Rf'.map (α.app (Rf.obj W)) ≫ Rf'.map (Lg'.map (adjf.counit.app W)) := by
    rw [← Rf'.map_comp, hcounit, Rf'.map_comp]
  have hpf : ∀ (b : Lg.obj (Rf.obj W) ⟶ Rf'.obj (Lg'.obj W)) {Z : A'}
      (z : Tens'.obj (Rf'.obj (Lg'.obj W)) ⟶ Z),
      pf'.hom.app (Lg.obj (Rf.obj W)) ≫ Tens'.map b ≫ z =
        Rf'.map (Lf'.map b) ≫ pf'.hom.app (Rf'.obj (Lg'.obj W)) ≫ z := by
    intro b Z z
    have h1 := (pf'.hom.naturality b).symm
    simp only [Functor.comp_map] at h1
    rw [← Category.assoc, h1, Category.assoc]
  have hid : ∀ {Z : A'} (z : Rf'.obj (Lf'.obj (Rf'.obj (Lg'.obj W))) ⟶ Z),
      pf'.hom.app (Rf'.obj (Lg'.obj W)) ≫ pf'.inv.app (Rf'.obj (Lg'.obj W)) ≫ z = z := by
    intro Z z
    rw [← Category.assoc, pf'.hom_inv_id_app, Category.id_comp]
  have hcancel : ∀ {Z : A'} (z : Rf'.obj (Lg'.obj (Lf.obj (Rf.obj W))) ⟶ Z),
      k ≫ Rf'.map (α.app (Rf.obj W)) ≫ z = z := by
    intro Z z
    rw [← Category.assoc, hk, Category.id_comp]
  have hnat : β.app (Lf.obj (Rf.obj W)) ≫ Rf'.map (Lg'.map (adjf.counit.app W)) =
      Lg.map (Rf.map (adjf.counit.app W)) ≫ β.app W :=
    (β.naturality (adjf.counit.app W)).symm
  simp only [action, Category.assoc, Functor.map_comp]
  rw [hpf (β.app W), hid, hcounit', hcancel, hnat]

/-- **The inverse projection formula is the unit followed by the action.**  For an adjunction
`adjf : Lf ⊣ Rf` and an identification `pf : Lf ⋙ Rf ≅ Tens`, the component of `pf.inv` at an
object `X` is `Tens` applied to the unit of `adjf`, followed by the action of `Tens` on
`Rf (Lf X)`.

For `Lf` extension of scalars along `R → A` this is the statement that the inverse projection
formula `X ⊗ᴸ_R A ⟶ (A ⊗ᴸ_R X)|_R` sends `x ⊗ a` to `a · (1 ⊗ x)`. -/
theorem inv_app_eq_map_unit_comp_action {Lf : A ⥤ B} {Rf : B ⥤ A} {Tens : A ⥤ A}
    (adjf : Lf ⊣ Rf) (pf : Lf ⋙ Rf ≅ Tens) (X : A) :
    pf.inv.app X = Tens.map (adjf.unit.app X) ≫ action adjf pf (Lf.obj X) := by
  have hnat : Tens.map (adjf.unit.app X) ≫ pf.inv.app (Rf.obj (Lf.obj X)) =
      pf.inv.app X ≫ Rf.map (Lf.map (adjf.unit.app X)) := pf.inv.naturality (adjf.unit.app X)
  rw [action, ← Category.assoc, hnat, Category.assoc, ← Rf.map_comp,
    adjf.left_triangle_components]
  simp

/-- **The comparison of the two endofunctors across the square, written with no auxiliary
functor.**  `Stacks.CategoryTheory.BaseChange.tensorComparison` is built from the identifications
`eg`, `ef` of the two composites around the square with a third functor `Lc`.  When the comparison
`γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf'` of those two composites is given directly as an isomorphism, and the
base change 2-cell is given as (the inverse of) an isomorphism `Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg`, the
same morphism `Lg (Tens X) ⟶ Tens' (Lg X)` is written without `Lc`.

Every factor is invertible, so this comparison is an isomorphism,
`Stacks.CategoryTheory.BaseChange.tensorComparisonIsoOfIso`. -/
def tensorComparisonOfIso {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg) (X : A) :
    Lg.obj (Tens.obj X) ⟶ Tens'.obj (Lg.obj X) :=
  Lg.map (pf.inv.app X) ≫ Θ.inv.app (Lf.obj X) ≫ Rf'.map (γ.hom.app X) ≫
    pf'.hom.app (Lg.obj X)

/-- **The comparison of the two endofunctors across the square, as an isomorphism.**  Each of the
four factors of `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` is a component of an
isomorphism of functors, or a functor applied to one, so the composite is invertible.  Its
underlying morphism is that comparison on the nose, by
`Stacks.CategoryTheory.BaseChange.tensorComparisonIsoOfIso_hom`. -/
def tensorComparisonIsoOfIso {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg) (X : A) :
    Lg.obj (Tens.obj X) ≅ Tens'.obj (Lg.obj X) :=
  Lg.mapIso ((pf.app X).symm) ≪≫ (Θ.app (Lf.obj X)).symm ≪≫ Rf'.mapIso (γ.app X) ≪≫
    pf'.app (Lg.obj X)

/-- The underlying morphism of `Stacks.CategoryTheory.BaseChange.tensorComparisonIsoOfIso` is
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso`. -/
@[simp]
theorem tensorComparisonIsoOfIso_hom {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg) (X : A) :
    (tensorComparisonIsoOfIso pf pf' γ Θ X).hom = tensorComparisonOfIso pf pf' γ Θ X :=
  rfl

/-- **The comparison of the two endofunctors across the square is invertible.** -/
theorem isIso_tensorComparisonOfIso {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg) (X : A) :
    IsIso (tensorComparisonOfIso pf pf' γ Θ X) :=
  (tensorComparisonIsoOfIso pf pf' γ Θ X).isIso_hom

/-- **The base change mate is a morphism of actions, in the form with two isomorphisms and no
auxiliary functor.**  `Stacks.CategoryTheory.BaseChange.tensorComparison_comp_action_of_mate` with
the 2-cell taken to be the inverse of an isomorphism `γ` of the two composites around the square
and the retraction taken to be `Rf'` applied to `γ`: the retraction identity is then that `γ`
cancels against itself. -/
theorem tensorComparisonOfIso_comp_action {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (W : B) :
    tensorComparisonOfIso pf pf' γ Θ (Rf.obj W) ≫ Tens'.map (Θ.inv.app W) ≫
        action adjf' pf' (Lg'.obj W) =
      Lg.map (action adjf pf W) ≫ Θ.inv.app W :=
  tensorComparison_comp_action_of_mate adjf adjf' pf pf' _ _ hα W
    (Rf'.map (γ.hom.app (Rf.obj W)))
    (by rw [← Rf'.map_comp, γ.hom_inv_id_app]; exact Rf'.map_id _)

/-- **The two algebra actions agree, granted one comparison identity.**  Let
`t : M₁ ⟶ M₂`, `n₁ : M₂ ⟶ Tens' (Lg (Rf W))`, `n₂ : M₁ ⟶ Tens' (Rf' (Lg' W))` and
`m : M₂ ⟶ Lg (Tens (Rf W))` satisfy `t ≫ n₁ = n₂ ≫ Tens' (Θ W)`. The two composites

* `n₂`, the action of `Tens'` on `Rf' (Lg' W)`, and `Θ` — and
* `t`, `m`, and `Lg` of the action of `Tens` on `Rf W`

agree, as soon as `m` followed by `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` at
`Rf W` is `n₁`. -/
theorem action_comp_eq_of_tensorComparisonOfIso {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (W : B) {M₁ M₂ : A'} (t : M₁ ⟶ M₂)
    (n₁ : M₂ ⟶ Tens'.obj (Lg.obj (Rf.obj W)))
    (n₂ : M₁ ⟶ Tens'.obj (Rf'.obj (Lg'.obj W)))
    (m : M₂ ⟶ Lg.obj (Tens.obj (Rf.obj W)))
    (hn : t ≫ n₁ = n₂ ≫ Tens'.map (Θ.hom.app W))
    (ha : m ≫ tensorComparisonOfIso pf pf' γ Θ (Rf.obj W) = n₁) :
    n₂ ≫ action adjf' pf' (Lg'.obj W) ≫ Θ.hom.app W =
      t ≫ m ≫ Lg.map (action adjf pf W) := by
  have hL : tensorComparisonOfIso pf pf' γ Θ (Rf.obj W) ≫ Tens'.map (Θ.inv.app W) ≫
      action adjf' pf' (Lg'.obj W) ≫ Θ.hom.app W = Lg.map (action adjf pf W) := by
    rw [← Category.assoc (Tens'.map (Θ.inv.app W)), ← Category.assoc,
      tensorComparisonOfIso_comp_action adjf adjf' pf pf' γ Θ hα W, Category.assoc,
      Θ.inv_hom_id_app]
    simp
  rw [← hL, ← Category.assoc m, ha, ← Category.assoc t, hn]
  simp only [Category.assoc]
  rw [← Category.assoc (Tens'.map (Θ.hom.app W)), ← Tens'.map_comp, Θ.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- `Stacks.CategoryTheory.BaseChange.action_comp_eq_of_tensorComparisonOfIso` with the two
actions written out as the inverse projection formula followed by the counit, and bracketed to the
right. -/
theorem comp_counit_eq_of_tensorComparisonOfIso {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (W : B) {M₁ M₂ : A'} (t : M₁ ⟶ M₂)
    (n₁ : M₂ ⟶ Tens'.obj (Lg.obj (Rf.obj W)))
    (n₂ : M₁ ⟶ Tens'.obj (Rf'.obj (Lg'.obj W)))
    (m : M₂ ⟶ Lg.obj (Tens.obj (Rf.obj W)))
    (hn : t ≫ n₁ = n₂ ≫ Tens'.map (Θ.hom.app W))
    (ha : m ≫ tensorComparisonOfIso pf pf' γ Θ (Rf.obj W) = n₁) :
    n₂ ≫ pf'.inv.app (Rf'.obj (Lg'.obj W)) ≫ Rf'.map (adjf'.counit.app (Lg'.obj W)) ≫
        Θ.hom.app W =
      t ≫ m ≫ Lg.map (pf.inv.app (Rf.obj W) ≫ Rf.map (adjf.counit.app W)) := by
  rw [← Category.assoc (pf'.inv.app (Rf'.obj (Lg'.obj W)))]
  exact action_comp_eq_of_tensorComparisonOfIso adjf adjf' pf pf' γ Θ hα W t n₁ n₂ m hn ha

/-- `Stacks.CategoryTheory.BaseChange.action_comp_eq_of_tensorComparisonOfIso` for a
transformation `n : TensM ⟶ Tens'` of endofunctors and a lax structure map
`m : Lg ⋙ TensM ⟶ Tens ⋙ Lg`, the naturality square of `n` at the component of `Θ` serving as
the hypothesis `hn`.

For `Lg` derived base change along `R → R'`, `TensM` derived tensoring with `A ⊗ᴸ_R R'`, `n`
tensoring with the identification `A ⊗ᴸ_R R' ≅ A ⊗_R R'` and `m` the lax monoidal structure map of
derived base change, the two composites are the two algebra actions of [stacks 0E2A] and the
hypothesis is the identification of `m` with the comparison of the two tensor functors. -/
theorem action_comp_eq_of_tensorComparisonOfIso_natTrans {Tens : A ⥤ A} {Tens' TensM : A' ⥤ A'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg)
    (hα : mateEquiv adjf adjf' (TwoSquare.mk Lg Lf Lf' Lg' γ.inv) =
      TwoSquare.mk Rf Lg' Lg Rf' Θ.inv)
    (n : TensM ⟶ Tens') (m : Lg ⋙ TensM ⟶ Tens ⋙ Lg) (W : B)
    (ha : m.app (Rf.obj W) ≫ tensorComparisonOfIso pf pf' γ Θ (Rf.obj W) =
      n.app (Lg.obj (Rf.obj W))) :
    n.app (Rf'.obj (Lg'.obj W)) ≫ action adjf' pf' (Lg'.obj W) ≫ Θ.hom.app W =
      TensM.map (Θ.hom.app W) ≫ m.app (Rf.obj W) ≫ Lg.map (action adjf pf W) :=
  action_comp_eq_of_tensorComparisonOfIso adjf adjf' pf pf' γ Θ hα W
    (TensM.map (Θ.hom.app W)) (n.app (Lg.obj (Rf.obj W))) (n.app (Rf'.obj (Lg'.obj W)))
    (m.app (Rf.obj W)) (n.naturality _) ha

/-- **The base change mate of a square of adjunctions is a morphism of actions.**  At an object
`W` of `B` the square made by

* the comparison `Stacks.CategoryTheory.BaseChange.tensorComparison` at `Rf W`,
* `Tens'` applied to the base change mate at `W`,
* the action of `Tens'` on `Rf' (Lg' W)`,
* `Lg` applied to the action of `Tens` on `Rf W`,
* the base change mate at `W`

commutes.  Nothing is assumed invertible. -/
theorem tensorComparison_comp_action (W : B) :
    tensorComparison adjf adjf' eg ef pf pf' (Rf.obj W) ≫
        Tens'.map (map adjf adjf' eg ef W) ≫ action adjf' pf' (Lg'.obj W) =
      Lg.map (action adjf pf W) ≫ map adjf adjf' eg ef W :=
  tensorComparison_comp_action_of_mate adjf adjf' pf pf' (pullbackComparison eg ef)
    (twoSquare adjf adjf' eg ef) rfl W
    (Rf'.map (ef.hom.app (Rf.obj W) ≫ eg.inv.app (Rf.obj W)))
    (by
      rw [← Rf'.map_comp]
      refine Eq.trans (congrArg Rf'.map ?_) (Rf'.map_id _)
      dsimp only [pullbackComparison, TwoSquare.mk, NatTrans.comp_app]
      rw [Category.assoc, eg.inv_hom_id_app_assoc, ef.hom_inv_id_app]
      rfl)

/-- **The base change mate is a morphism of actions, solved for the base-changed action.**  When
the comparison `Stacks.CategoryTheory.BaseChange.tensorComparison` is invertible at `Rf W` — for
derived base change along a flat or Tor-independent ring map, that is the strong monoidality of
base change — the equation of
`Stacks.CategoryTheory.BaseChange.tensorComparison_comp_action` reads: the base change of the
action, followed by the mate, is the inverse comparison, the mate in the tensor factor and the
action over `A'`. -/
theorem action_comp_map (W : B)
    [IsIso (tensorComparison adjf adjf' eg ef pf pf' (Rf.obj W))] :
    Tens'.map (map adjf adjf' eg ef W) ≫ action adjf' pf' (Lg'.obj W) =
      inv (tensorComparison adjf adjf' eg ef pf pf' (Rf.obj W)) ≫
        Lg.map (action adjf pf W) ≫ map adjf adjf' eg ef W := by
  rw [← tensorComparison_comp_action adjf adjf' eg ef pf pf' W, ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp]

end Stacks.CategoryTheory.BaseChange

end
