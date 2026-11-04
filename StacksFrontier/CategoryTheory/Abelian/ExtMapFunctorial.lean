module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# `Ext.mapExactFunctor` is functorial in the exact functor

Mathlib's `CategoryTheory.Abelian.Ext.mapExactFunctor` turns an exact additive functor
`F : C ⥤ D` into a map `Ext^n(X, Y) → Ext^n(F X, F Y)`, and records that it preserves
`Ext.comp`, `Ext.mk₀` and the class of a short exact sequence.  What it does not record is
functoriality in `F` itself: that the identity functor acts as the identity, and that the
composite of two exact functors acts as the composite of their actions.

Both are proved here by dimension shifting in the second variable: in degree zero every `Ext`
class is `Ext.mk₀` of a morphism, where the statements are the functor laws of `F`; in degree
`n + 1` an injective presentation `Y ↪ J` writes every class as `x.comp e` with `e` the class
of the resulting short exact sequence, and the two compatibilities just quoted reduce the claim
to degree `n`.

## Main results

* `Stacks.ExtFunctorial.mapExactFunctor_id` — the identity functor induces the identity.
* `Stacks.ExtFunctorial.mapExactFunctor_comp_functor` — `(e.mapExactFunctor L).mapExactFunctor M`
  is `e.mapExactFunctor (L ⋙ M)`.
* `Stacks.ExtFunctorial.comp_mk₀_app_eq_of_app_eq_comp` and
  `Stacks.ExtFunctorial.comp_mk₀_eq_self_of_app_eq_comp` — the scaling identity: if two natural
  transformations `p a : 𝟭 ⟶ T` into an exact endofunctor differ at the source object by a
  natural endomorphism `τ` of `T`, then they act alike on `Ext` after `τ`; with a retraction of
  `τ ∘ p` this fixes every class under the resulting endomorphism of the target.

## Implementation notes

The short exact sequences produced by the two functors from one presentation are *equal*, not
merely isomorphic: `ShortComplex.map` is computed object by object, so `(S.map L).map M` and
`S.map (L ⋙ M)` are the same short complex, and `ShortComplex.ShortExact` is a `Prop`.  The
final step of each induction is therefore `rfl`.

Enough injectives is needed in the source category only, and no hypothesis is placed on the
target categories beyond `HasExt`.
-/

@[expose] public noncomputable section

universe w w' w'' v v' v'' u u' u''

namespace Stacks.ExtFunctorial

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]

attribute [local instance] Ext.subsingleton_of_injective comp_preservesFiniteLimits
  comp_preservesFiniteColimits

/-- The identity functor induces the identity on every `Ext` group. -/
public lemma mapExactFunctor_id [HasExt.{w} C] [EnoughInjectives C] (X : C) :
    ∀ (n : ℕ) {Y : C} (e : Ext.{w} X Y n), e.mapExactFunctor (𝟭 C) = e := by
  intro n
  induction n with
  | zero =>
      intro Y e
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective e
      rw [Ext.mapExactFunctor_mk₀]
      rfl
  | succ n ih =>
      intro Y e
      let I : InjectivePresentation Y := Classical.arbitrary _
      have hS : (ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)).ShortExact :=
        { exact := ShortComplex.exact_cokernel I.f }
      obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ X hS e (by subsingleton) rfl
      simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ih]

/-- The action on `Ext` of a composite of exact functors is the composite of their actions. -/
public lemma mapExactFunctor_comp_functor
    [HasExt.{w} C] [HasExt.{w'} D] [HasExt.{w''} E] [EnoughInjectives C]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (M : D ⥤ E) [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M] (X : C) :
    ∀ (n : ℕ) {Y : C} (e : Ext.{w} X Y n),
      (e.mapExactFunctor L).mapExactFunctor M = e.mapExactFunctor (L ⋙ M) := by
  intro n
  induction n with
  | zero =>
      intro Y e
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective e
      rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]
      rfl
  | succ n ih =>
      intro Y e
      let I : InjectivePresentation Y := Classical.arbitrary _
      have hS : (ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)).ShortExact :=
        { exact := ShortComplex.exact_cokernel I.f }
      obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ X hS e (by subsingleton) rfl
      simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ih]

/-- A natural transformation `τ : L ⟶ L'` of exact functors intertwines the two actions on
`Ext`: the square with sides `Ext.mk₀ (τ.app _)` commutes in every degree. -/
public lemma mk₀_comp_mapExactFunctor
    [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
    {L L' : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    (τ : L ⟶ L') (X : C) :
    ∀ (n : ℕ) {Y : C} (e : Ext.{w} X Y n),
      (Ext.mk₀ (τ.app X)).comp (e.mapExactFunctor L') (zero_add n) =
        (e.mapExactFunctor L).comp (Ext.mk₀ (τ.app Y)) (add_zero n) := by
  intro n
  induction n with
  | zero =>
      intro Y e
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective e
      rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
        Ext.mk₀_comp_mk₀, τ.naturality f]
  | succ n ih =>
      intro Y e
      let I : InjectivePresentation Y := Classical.arbitrary _
      have hS : (ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)).ShortExact :=
        { exact := ShortComplex.exact_cokernel I.f }
      obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ X hS e (by subsingleton) rfl
      have key := ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact L)
        (hS.map_of_exact L') (ShortComplex.mapNatTrans _ τ)
      simp only [ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₃] at key
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
        Ext.mapExactFunctor_extClass,
        ← Ext.comp_assoc _ _ _ (zero_add n) rfl (by lia), ih x₃,
        Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by lia),
        Ext.comp_assoc _ _ _ rfl (add_zero 1) (by lia), ← key]

/-- The endomorphism of `Ext^n(Z, G)` induced by an exact endofunctor `L` together with a map
`z : Z ⟶ L Z` on the source and a map `c : L G ⟶ G` on the target. -/
public def extEndo [HasExt.{w} C] (L : C ⥤ C) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] {Z G : C} (z : Z ⟶ L.obj Z) (c : L.obj G ⟶ G) (n : ℕ)
    (x : Ext.{w} Z G n) : Ext.{w} Z G n :=
  ((Ext.mk₀ z).comp (x.mapExactFunctor L) (zero_add n)).comp (Ext.mk₀ c) (add_zero n)

/-- **Two such endomorphisms are mutually inverse as soon as their data are.** If `w` maps the
composite of the two exact functors to the identity functor, and the two maps on the source and
the two maps on the target are compatible with `w`, then the endomorphism attached to the first
undoes the one attached to the second, in every degree. -/
public lemma extEndo_extEndo [HasExt.{w} C] [EnoughInjectives C]
    (Lα Lβ : C ⥤ C) [Lα.Additive] [PreservesFiniteLimits Lα] [PreservesFiniteColimits Lα]
    [Lβ.Additive] [PreservesFiniteLimits Lβ] [PreservesFiniteColimits Lβ]
    (w : Lβ ⋙ Lα ⟶ 𝟭 C) {Z G : C} (zα : Z ⟶ Lα.obj Z) (zβ : Z ⟶ Lβ.obj Z)
    (cα : Lα.obj G ⟶ G) (cβ : Lβ.obj G ⟶ G)
    (hz : zα ≫ Lα.map zβ ≫ w.app Z = 𝟙 Z) (hc : Lα.map cβ ≫ cα = w.app G)
    (n : ℕ) (x : Ext.{w} Z G n) :
    extEndo Lα zα cα n (extEndo Lβ zβ cβ n x) = x := by
  have key := mk₀_comp_mapExactFunctor w Z n x
  rw [mapExactFunctor_id Z n x] at key
  simp only [extEndo, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    mapExactFunctor_comp_functor Lβ Lα Z n x, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc]
  rw [hc, ← key, Ext.mk₀_comp_mk₀_assoc, Category.assoc, hz, Ext.mk₀_id_comp]

/-- **A scaling identity on `Ext`.** Let `T` be an exact endofunctor, `p a : 𝟭 C ⟶ T` two natural
transformations and `τ : T ⟶ T` a natural endomorphism, such that at the source object `X` the
map `a` is `p` followed by `τ`. Then every class `ξ ∈ Ext^n(X, Y)` satisfies
`ξ ∘ a_Y = ξ ∘ (τ_Y ∘ p_Y)`, although `a` and `p ≫ τ` need not agree at `Y`.

Both sides are compared with the image of `ξ` under `T`: each of `p`, `a` and `τ` intertwines
the actions of its source and target functors on `Ext`, and the identity functor acts as the
identity. -/
public lemma comp_mk₀_app_eq_of_app_eq_comp [HasExt.{w} C] [EnoughInjectives C]
    (T : C ⥤ C) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (p a : 𝟭 C ⟶ T) (τ : T ⟶ T) {X : C} (hX : a.app X = p.app X ≫ τ.app X)
    (n : ℕ) {Y : C} (ξ : Ext.{w} X Y n) :
    ξ.comp (Ext.mk₀ (a.app Y)) (add_zero n) =
      ξ.comp (Ext.mk₀ (p.app Y ≫ τ.app Y)) (add_zero n) := by
  have ha := mk₀_comp_mapExactFunctor a X n ξ
  have hp := mk₀_comp_mapExactFunctor p X n ξ
  have hτ := mk₀_comp_mapExactFunctor τ X n ξ
  rw [mapExactFunctor_id X n ξ] at ha hp
  rw [← ha, hX, ← Ext.mk₀_comp_mk₀_assoc, hτ, ← Ext.comp_assoc_of_third_deg_zero, hp,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

/-- **Classes see only the part of the target singled out by a scaling.** In the situation of
`Stacks.ExtFunctorial.comp_mk₀_app_eq_of_app_eq_comp`, let `π : T Y ⟶ Y` be a retraction of
`p_Y` followed by `τ_Y`. Then every class `ξ ∈ Ext^n(X, Y)` is fixed by the endomorphism
`e = π ∘ a_Y` of `Y`: `ξ = e ∘ ξ`.

For a grading, with `T` the base change to a polynomial variable `t`, `p` the inclusion, `a` the
scaling of degree `d` parts by `t ^ d`, `τ` the multiplication by `t` and `π` the coefficient of
`t`, the endomorphism `e` is the projection onto the weight-one part of `Y`. -/
public lemma comp_mk₀_eq_self_of_app_eq_comp [HasExt.{w} C] [EnoughInjectives C]
    (T : C ⥤ C) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (p a : 𝟭 C ⟶ T) (τ : T ⟶ T) {X : C} (hX : a.app X = p.app X ≫ τ.app X)
    {Y : C} (π : T.obj Y ⟶ Y) (hπ : p.app Y ≫ τ.app Y ≫ π = 𝟙 Y)
    (n : ℕ) (ξ : Ext.{w} X Y n) :
    ξ.comp (Ext.mk₀ (a.app Y ≫ π)) (add_zero n) = ξ := by
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    comp_mk₀_app_eq_of_app_eq_comp T p a τ hX n ξ, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, Category.assoc, hπ, Ext.comp_mk₀_id]

end Stacks.ExtFunctorial

end
