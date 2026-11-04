module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomEvaluationBijection

/-!
# A homothety at an internal hom isomorphic to the unit object is invertible

Let `C` be a monoidal category, let `K` be an object, and let `c : A ⊗ K ⟶ K` exhibit `A` as an
internal hom from `K` to itself, in the sense of
`StacksFrontier/CategoryTheory/Monoidal/InternalHomEvaluationBijection.lean`: for every object `Z`
the map `(Z ⟶ A) → (Z ⊗ K ⟶ K)`, `x ↦ x ▷ K ≫ c`, is a bijection. A *homothety* of `K` at `c`
is a morphism `a : 𝟙_ C ⟶ A` with `a ▷ K ≫ c = (λ_ K).hom`.

**The result of this file is that `a` is invertible as soon as `A` is isomorphic to `𝟙_ C`** — the
bare existence of an isomorphism of *objects*, with no compatibility with `c` whatsoever.

That is more than the uniqueness statements of
`CategoryTheory.MonoidalCategory.isIso_iff_of_whiskerRight_comp_eq_leftUnitor` give. Those
compare two homotheties *read at two internal homs*, so they need an isomorphism of the two
internal homs compatible with the two evaluation morphisms, and an unrelated isomorphism
`A ≅ 𝟙_ C` supplies no such compatibility: a morphism between isomorphic objects need not be
invertible, and `a` is exactly such a morphism.

What closes the gap is that `A` is not merely an object but an *algebra*. The universal property
of `c` produces a multiplication

`m : A ⊗ A ⟶ A`,

namely the morphism matched with `(α_ A A K).hom ≫ (A ◁ c) ≫ c` by the bijections of `c`, and the
homothety is a left unit for it. For a left unit the isomorphism `ψ : A ≅ 𝟙_ C` is enough: the
left unit axiom, conjugated by `ψ`, exhibits `a` as a split monomorphism with retraction
`A ⟶ 𝟙_ C`, so `a ≫ ψ.hom` has a right inverse in `End (𝟙_ C)`; and endomorphisms of the unit
object commute, so a right inverse there is a two-sided inverse.

## Main results

* `CategoryTheory.MonoidalCategory.comp_comm_tensorUnit` — **endomorphisms of the unit object
  commute.** Not in Mathlib, and what makes the splitting below suffice.
* `CategoryTheory.MonoidalCategory.isIso_unit_of_iso_tensorUnit` — **a left unit of a
  multiplication on an object isomorphic to `𝟙_ C` is invertible.** Only the left unit axiom is
  used; neither associativity nor the right unit axiom enters, so the hypothesis is a bare pair
  `(a, m)` rather than a `Mon_` object.
* `CategoryTheory.MonoidalCategory.internalHomMul` and
  `CategoryTheory.MonoidalCategory.whiskerRight_internalHomMul_comp` — the composition on an
  internal hom from `K` to `K`, and its defining equation.
* `CategoryTheory.MonoidalCategory.whiskerRight_comp_internalHomMul` — a homothety is a left
  unit for that composition.
* `CategoryTheory.MonoidalCategory.isIso_of_whiskerRight_comp_eq_leftUnitor_of_iso_tensorUnit` —
  **the result: a homothety at an internal hom isomorphic to the unit object is invertible.**

## Implementation notes

The multiplication is obtained from `Function.surjInv` of the bijection at `Z = A ⊗ A`, so it is
a definite morphism and the unit axiom is a lemma about it rather than a hypothesis. The axiom is
checked by applying the *injectivity* of the bijection at `Z = 𝟙_ C ⊗ A`, which turns it into an
identity between two morphisms `(𝟙_ C ⊗ A) ⊗ K ⟶ K`; that identity is the coherence of the left
unitor with the associator together with the defining equations of `m` and of the homothety.

The splitting is written with whiskerings and the two unitors only — the retraction is
`(ρ_ A).inv ≫ (A ◁ ψ.inv) ≫ m ≫ ψ.hom` — so no interchange law for `⊗ₘ` is needed: the one
exchange used is `CategoryTheory.MonoidalCategory.whisker_exchange` at `a` and `ψ.inv`, and the
one place the two unitors meet is `CategoryTheory.MonoidalCategory.unitors_inv_equal`.

No braiding and no closedness is used, and `C` is an arbitrary monoidal category: nothing here
needs the internal hom to be a value of a bifunctor, let alone an adjoint.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Endomorphisms of the unit object -/

/-- **Endomorphisms of the unit object of a monoidal category commute.** Both `f ≫ g` and
`g ≫ f` are the conjugate by `λ_ (𝟙_ C)` of the two whiskerings of `f` and `g` composed in the
two orders, and those two composites agree by the interchange law. -/
theorem comp_comm_tensorUnit (f g : 𝟙_ C ⟶ 𝟙_ C) : f ≫ g = g ≫ f := by
  have hl := leftUnitor_inv_naturality g
  have hr : f ≫ (λ_ (𝟙_ C)).inv = (λ_ (𝟙_ C)).inv ≫ f ▷ 𝟙_ C := by
    rw [unitors_inv_equal]
    exact rightUnitor_inv_naturality f
  rw [← cancel_mono (λ_ (𝟙_ C)).inv, Category.assoc, Category.assoc, hl, reassoc_of% hr,
    ← whisker_exchange, ← reassoc_of% hl, ← hr]

/-! ### A left unit on an object isomorphic to the unit object -/

/-- **A left unit of a multiplication on an object isomorphic to the unit object is
invertible.** Let `a : 𝟙_ C ⟶ A` and `m : A ⊗ A ⟶ A` satisfy the left unit axiom
`a ▷ A ≫ m = (λ_ A).hom`, and let `ψ : A ≅ 𝟙_ C` be an isomorphism — arbitrary, with no
compatibility with `a` or `m` assumed. Then `a` is an isomorphism.

The left unit axiom says that `(λ_ A).inv ≫ (a ▷ A) ≫ m` is the identity of `A`. Commuting
`ψ.inv` past `a` turns that into the statement that
`a ≫ ((ρ_ A).inv ≫ (A ◁ ψ.inv) ≫ m ≫ ψ.hom)` is the identity of `𝟙_ C`, so `a ≫ ψ.hom` has a
right inverse in `End (𝟙_ C)`; endomorphisms of the unit object commute
(`CategoryTheory.MonoidalCategory.comp_comm_tensorUnit`), so that right inverse is an inverse. -/
theorem isIso_unit_of_iso_tensorUnit {A : C} (a : 𝟙_ C ⟶ A) (m : A ⊗ A ⟶ A)
    (ha : a ▷ A ≫ m = (λ_ A).hom) (ψ : A ≅ 𝟙_ C) : IsIso a := by
  have h₁ := leftUnitor_inv_naturality ψ.inv
  have h₂ : a ≫ (ρ_ A).inv = (λ_ (𝟙_ C)).inv ≫ (a ▷ 𝟙_ C) := by
    rw [unitors_inv_equal]
    exact rightUnitor_inv_naturality a
  have hsplit : a ≫ ((ρ_ A).inv ≫ (A ◁ ψ.inv) ≫ m ≫ ψ.hom) = 𝟙 (𝟙_ C) := by
    rw [reassoc_of% h₂, ← reassoc_of% whisker_exchange a ψ.inv, ← reassoc_of% h₁,
      reassoc_of% ha, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  have hiso : IsIso (a ≫ ψ.hom) := by
    refine ⟨ψ.inv ≫ (ρ_ A).inv ≫ (A ◁ ψ.inv) ≫ m ≫ ψ.hom, ?_, ?_⟩
    · rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact hsplit
    · rw [← comp_comm_tensorUnit, Category.assoc, Iso.hom_inv_id_assoc]
      exact hsplit
  exact IsIso.of_isIso_comp_right a ψ.hom

/-! ### The composition on an internal hom from `K` to `K` -/

/-- The composition on an internal hom `A` from `K` to `K`: the morphism `A ⊗ A ⟶ A` matched by
the bijections of `c` with evaluating twice. -/
def internalHomMul {K A : C} (c : A ⊗ K ⟶ K)
    (hc : ∀ Z : C, Function.Bijective fun x : Z ⟶ A => x ▷ K ≫ c) : A ⊗ A ⟶ A :=
  Function.surjInv (hc (A ⊗ A)).surjective ((α_ A A K).hom ≫ (A ◁ c) ≫ c)

/-- The defining equation of `CategoryTheory.MonoidalCategory.internalHomMul`: evaluating a
composite is evaluating twice. -/
theorem whiskerRight_internalHomMul_comp {K A : C} (c : A ⊗ K ⟶ K)
    (hc : ∀ Z : C, Function.Bijective fun x : Z ⟶ A => x ▷ K ≫ c) :
    internalHomMul c hc ▷ K ≫ c = (α_ A A K).hom ≫ (A ◁ c) ≫ c :=
  Function.surjInv_eq (hc (A ⊗ A)).surjective _

/-- **A homothety is a left unit for the composition.** If `a : 𝟙_ C ⟶ A` satisfies the defining
equation `a ▷ K ≫ c = (λ_ K).hom` of a homothety of `K` at `c`, then `a` is a left unit for
`CategoryTheory.MonoidalCategory.internalHomMul`.

Both sides are morphisms into `A`, so they may be compared after evaluation, and there the
identity is the coherence of the left unitor with the associator together with the two defining
equations. -/
theorem whiskerRight_comp_internalHomMul {K A : C} (c : A ⊗ K ⟶ K)
    (hc : ∀ Z : C, Function.Bijective fun x : Z ⟶ A => x ▷ K ≫ c)
    {a : 𝟙_ C ⟶ A} (ha : a ▷ K ≫ c = (λ_ K).hom) :
    a ▷ A ≫ internalHomMul c hc = (λ_ A).hom := by
  refine (hc (𝟙_ C ⊗ A)).injective ?_
  show (a ▷ A ≫ internalHomMul c hc) ▷ K ≫ c = (λ_ A).hom ▷ K ≫ c
  rw [comp_whiskerRight, Category.assoc, whiskerRight_internalHomMul_comp,
    associator_naturality_left_assoc, ← reassoc_of% whisker_exchange a c, ha,
    leftUnitor_naturality, leftUnitor_tensor_hom_assoc, Iso.hom_inv_id_assoc]

/-! ### The result -/

/-- **A homothety at an internal hom isomorphic to the unit object is invertible.** Let
`c : A ⊗ K ⟶ K` exhibit `A` as an internal hom from `K` to `K`, let `a : 𝟙_ C ⟶ A` satisfy the
defining equation `a ▷ K ≫ c = (λ_ K).hom` of a homothety, and suppose merely that `A` is
isomorphic to `𝟙_ C` as an object. Then `a` is an isomorphism.

The isomorphism `A ≅ 𝟙_ C` is arbitrary: no compatibility with `c` or with `a` is assumed, and
none is needed. The universal property of `c` makes `a` a left unit for a multiplication on `A`
(`CategoryTheory.MonoidalCategory.whiskerRight_comp_internalHomMul`), and a left unit on an
object isomorphic to `𝟙_ C` is invertible
(`CategoryTheory.MonoidalCategory.isIso_unit_of_iso_tensorUnit`).

This is what turns an *object* computation of an internal hom from `K` to `K` into invertibility
of the homothety, and hence — through
`CategoryTheory.MonoidalCategory.isIso_iff_tensorHomBijective_tensorUnit` — into the statement
that `𝟙_ C` is itself an internal hom from `K` to `K` through the left unitor. -/
theorem isIso_of_whiskerRight_comp_eq_leftUnitor_of_iso_tensorUnit {K A : C} (c : A ⊗ K ⟶ K)
    (hc : ∀ Z : C, Function.Bijective fun x : Z ⟶ A => x ▷ K ≫ c)
    {a : 𝟙_ C ⟶ A} (ha : a ▷ K ≫ c = (λ_ K).hom) (ψ : A ≅ 𝟙_ C) : IsIso a :=
  isIso_unit_of_iso_tensorUnit a (internalHomMul c hc)
    (whiskerRight_comp_internalHomMul c hc ha) ψ

end CategoryTheory.MonoidalCategory

end
