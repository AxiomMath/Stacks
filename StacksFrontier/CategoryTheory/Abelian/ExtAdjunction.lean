module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# `Ext` groups along an adjunction whose inverse image is exact

Let `L ⊣ R` be an adjunction between abelian categories in which both functors are exact and
the unit is an isomorphism, so that `L` is a fully faithful embedding whose retraction `R` is
exact. This file shows that `L` then induces bijections on all `Ext` groups,
`Ext^n(A, B) ≃ Ext^n(L A, L B)`.

Mathlib's `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects` proves the same
conclusion for a fully faithful exact functor that *preserves injective objects*. That hypothesis
is unavailable here, and in the situations this file is written for it is false: for the inverse
image along the comparison morphism from a big site to a small site, the image of an injective
abelian sheaf restricts on each object of the big site to a pullback of that sheaf, and a
pullback of an injective sheaf is not injective. The argument below replaces it by exactness of
`R`, which holds whenever `R` is restriction along a functor that is both continuous and
cocontinuous.

## Main results

* `Stacks.ExtAdjunction.extMap_bijective`: the adjunction map
  `Ext^n(A, R M) → Ext^n(L A, M)` is bijective.
* `Stacks.ExtAdjunction.mapExtAddHom_bijective`: if moreover the unit of the adjunction is an
  isomorphism, then `CategoryTheory.Functor.mapExtAddHom` for `L` is bijective.

## Implementation notes

The adjunction map `extMap` is the composite of `Ext.mapExactFunctor L` with postcomposition by
the counit; it is the only map built from the available structure, and at `n = 0` it is the
`Adjunction.homEquiv` of the adjunction transported through `Ext.mk₀`.

Bijectivity is proved by induction on `n`, dimension-shifting on the *target* side: an injective
presentation `M ↪ I` is chosen in the target category, and `R` applied to the resulting short
exact sequence is again short exact (because `R` is exact) with injective middle term (because
`R` preserves injectives, `L` being exact). The two long exact sequences of `Ext` in the second
variable then sandwich the degree `n + 1` comparison between two comparisons in degree `n`, and
`AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact` concludes. This is the same
skeleton as Mathlib's `mapExt_bijective_of_preservesInjectiveObjects`, with the presentation
taken on the other side of the adjunction.

Deducing `mapExtAddHom_bijective` uses the triangle identity: precomposing `extMap` with
postcomposition by the unit — a bijection, the unit being invertible — gives exactly
`Ext.mapExactFunctor L`.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

universe w w' v v' u u'

namespace Stacks.ExtAdjunction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C}

section

variable (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [HasExt.{w} C] [HasExt.{w'} D]

/-- The map `Ext^n(A, R M) → Ext^n(L A, M)` attached to an adjunction `L ⊣ R` with `L` exact:
apply `L` and postcompose with the counit. -/
def extMap (A : C) (M : D) (n : ℕ) : Ext.{w} A (R.obj M) n →+ Ext.{w'} (L.obj A) M n :=
  ((Ext.mk₀ (adj.counit.app M)).postcomp (L.obj A) (add_zero n)).comp
    (L.mapExtAddHom A (R.obj M) n)

/-- `extMap` sends `e` to the image of `e` under `L`, composed with the counit at `M`. -/
lemma extMap_apply (A : C) (M : D) (n : ℕ) (e : Ext.{w} A (R.obj M) n) :
    extMap adj A M n e =
      (e.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app M)) (add_zero n) :=
  rfl

/-- Precomposition by a degree-zero class `α` is composition with `α` on the left. -/
lemma precomp_apply {X Y Z : C} {n : ℕ} (α : Ext.{w} X Y 0) (y : Ext.{w} Y Z n) :
    (α.precomp Z (zero_add n)) y = α.comp y (zero_add n) :=
  rfl

/-- Precomposition with an isomorphism is bijective on `Ext`. -/
lemma precomp_mk₀_bijective_of_isIso {X Y Z : C} (f : X ⟶ Y) [IsIso f] (n : ℕ) :
    Function.Bijective
      ((Ext.mk₀ f).precomp (a := n) (b := n) Z (zero_add n) : Ext.{w} Y Z n → _) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun z ↦ (Ext.mk₀ (inv f)).comp z (zero_add n), fun x ↦ ?_, fun z ↦ ?_⟩
  · show (Ext.mk₀ (inv f)).comp ((Ext.mk₀ f).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, IsIso.inv_hom_id, Ext.mk₀_id_comp]
  · show (Ext.mk₀ f).comp ((Ext.mk₀ (inv f)).comp z (zero_add n)) (zero_add n) = z
    rw [Ext.mk₀_comp_mk₀_assoc, IsIso.hom_inv_id, Ext.mk₀_id_comp]

/-- Postcomposition by a degree-zero class `β` is composition with `β` on the right. -/
lemma postcomp_apply {X Y Z : C} {n : ℕ} (β : Ext.{w} Y Z 0) (x : Ext.{w} X Y n) :
    (β.postcomp X (add_zero n)) x = x.comp β (add_zero n) :=
  rfl

/-- Postcomposition with an isomorphism is bijective on `Ext`. -/
lemma postcomp_mk₀_bijective_of_isIso {X Y Z : C} (f : Y ⟶ Z) [IsIso f] (n : ℕ) :
    Function.Bijective
      ((Ext.mk₀ f).postcomp (a := n) (b := n) X (add_zero n) : Ext.{w} X Y n → _) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun z ↦ z.comp (Ext.mk₀ (inv f)) (add_zero n), fun x ↦ ?_, fun z ↦ ?_⟩
  · show (x.comp (Ext.mk₀ f) (add_zero n)).comp (Ext.mk₀ (inv f)) (add_zero n) = x
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, IsIso.hom_inv_id, Ext.comp_mk₀_id]
  · show (z.comp (Ext.mk₀ (inv f)) (add_zero n)).comp (Ext.mk₀ f) (add_zero n) = z
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, IsIso.inv_hom_id, Ext.comp_mk₀_id]

/-- In degree zero, the adjunction map `Ext^0(A, R M) → Ext^0(L A, M)` is bijective. -/
lemma extMap_zero_bijective (A : C) (M : D) :
    Function.Bijective (extMap adj A M 0 : Ext.{w} A (R.obj M) 0 → Ext.{w'} (L.obj A) M 0) := by
  have key : ∀ f : A ⟶ R.obj M,
      extMap adj A M 0 (Ext.mk₀ f) = Ext.mk₀ ((adj.homEquiv A M).symm f) := by
    intro f
    rw [extMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    congr 1
  constructor
  · intro x y hxy
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective A (R.obj M)).2 x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective A (R.obj M)).2 y
    rw [key, key] at hxy
    exact congrArg Ext.mk₀ ((adj.homEquiv A M).symm.injective ((Ext.mk₀_bijective _ _).1 hxy))
  · intro z
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (L.obj A) M).2 z
    exact ⟨Ext.mk₀ (adj.homEquiv A M g), by rw [key]; simp⟩

/-- The adjunction map commutes with composition by a morphism `g : M ⟶ N` in the second
variable, applied as `R.map g` on the source side and as `g` on the target side. -/
lemma extMap_naturality_mk₀ (A : C) {M N : D} (g : M ⟶ N) (n : ℕ)
    (e : Ext.{w} A (R.obj M) n) :
    extMap adj A N n (e.comp (Ext.mk₀ (R.map g)) (add_zero n)) =
      (extMap adj A M n e).comp (Ext.mk₀ g) (add_zero n) := by
  rw [extMap_apply, extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀]
  congr 2
  exact adj.counit.naturality g

variable [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- The counit as a morphism of short complexes from the image of `S` under `R ⋙ L` to `S`. -/
@[simps]
def counitShortComplexHom (S : ShortComplex D) : (S.map R).map L ⟶ S where
  τ₁ := adj.counit.app S.X₁
  τ₂ := adj.counit.app S.X₂
  τ₃ := adj.counit.app S.X₃
  comm₁₂ := (adj.counit.naturality S.f).symm
  comm₂₃ := (adj.counit.naturality S.g).symm

/-- The adjunction map commutes with the connecting maps given by composition with the extension
class of a short exact sequence `S` and of its image under `R`. -/
lemma extMap_naturality_extClass (A : C) {S : ShortComplex D} (hS : S.ShortExact) (n : ℕ)
    (e : Ext.{w} A (R.obj S.X₃) n) :
    extMap adj A S.X₁ (n + 1) (e.comp (hS.map_of_exact R).extClass rfl) =
      (extMap adj A S.X₃ n e).comp hS.extClass rfl := by
  rw [extMap_apply, extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero]
  congr 1
  exact ((hS.map_of_exact R).map_of_exact L).extClass_naturality hS
    (counitShortComplexHom adj S)

/-- For a short exact sequence `S` with injective middle term, the connecting map
`Ext^n(X, S.X₃) → Ext^(n+1)(X, S.X₁)` is surjective and its kernel is the image of `S.g`. -/
private lemma ext_exact_and_surjective {E : Type*} [Category E] [Abelian E] [HasExt.{w} E]
    (X : E) {S : ShortComplex E} (hS : S.ShortExact) [Injective S.X₂] (n : ℕ) :
    Function.Exact ((Ext.mk₀ S.g).postcomp (a := n) (b := n) X (add_zero n))
        (hS.extClass.postcomp (a := n) (b := n + 1) X rfl) ∧
      Function.Surjective (hS.extClass.postcomp (a := n) (b := n + 1) X rfl) :=
  ⟨(ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl),
    fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (Ext.eq_zero_of_injective _) rfl⟩

attribute [local instance] Ext.subsingleton_of_injective in
/-- The adjunction map `Ext^n(A, R M) → Ext^n(L A, M)` is bijective when both `L` and `R` are
exact and the target category has enough injectives. -/
lemma extMap_bijective [EnoughInjectives D] (A : C) (M : D) (n : ℕ) :
    Function.Bijective (extMap adj A M n : Ext.{w} A (R.obj M) n → Ext.{w'} (L.obj A) M n) := by
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  induction n generalizing M with
  | zero => exact extMap_zero_bijective adj A M
  | succ n hn =>
    let I : InjectivePresentation M := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have : Injective S.X₂ := I.injective
    have : Injective (S.map R).X₂ := R.injective_obj_of_injective I.injective
    obtain ⟨hex, hsurj⟩ := ext_exact_and_surjective A (hS.map_of_exact R) n
    obtain ⟨hex', hsurj'⟩ := ext_exact_and_surjective (L.obj A) hS n
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extMap adj A S.X₂ n) (extMap adj A S.X₃ n) (extMap adj A S.X₁ (n + 1))
      (by ext e; exact (extMap_naturality_mk₀ adj A S.g n e).symm)
      (by ext e; exact (extMap_naturality_extClass adj A hS n e).symm)
      hex hex' (hn S.X₂).surjective (hn S.X₃) hsurj hsurj'

/-- When the unit of the adjunction is an isomorphism, `L` induces bijections on `Ext`. -/
lemma mapExtAddHom_bijective [EnoughInjectives D] [IsIso adj.unit] (A B : C) (n : ℕ) :
    Function.Bijective
      (L.mapExtAddHom A B n : Ext.{w} A B n → Ext.{w'} (L.obj A) (L.obj B) n) := by
  have : IsIso (adj.unit.app B) := inferInstance
  have key : ∀ e : Ext.{w} A B n, L.mapExtAddHom A B n e =
      extMap adj A (L.obj B) n (e.comp (Ext.mk₀ (adj.unit.app B)) (add_zero n)) := by
    intro e
    rw [extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, adj.left_triangle_components,
      Ext.comp_mk₀_id]
    rfl
  have : (L.mapExtAddHom A B n : Ext.{w} A B n → Ext.{w'} (L.obj A) (L.obj B) n) =
      (extMap adj A (L.obj B) n) ∘
        ((Ext.mk₀ (adj.unit.app B)).postcomp (a := n) (b := n) A (add_zero n)) := by
    exact funext key
  rw [this]
  exact (extMap_bijective adj A (L.obj B) n).comp
    (postcomp_mk₀_bijective_of_isIso (adj.unit.app B) n)

end

end Stacks.ExtAdjunction
