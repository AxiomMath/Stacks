module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual

/-!
# Endomorphisms of the tensor unit are central, and what that gives for an invertible object

Let `C` be a monoidal category. An endomorphism `a : 𝟙_ C ⟶ 𝟙_ C` of the tensor unit acts on
every object `B` by

`unitEndScalar a |>.app B = (ρ_ B).inv ≫ (B ◁ a) ≫ (ρ_ B).hom`,

and that action is an endomorphism of the *identity functor*: it commutes with every morphism of
`C`. This is the categorical form of "multiplication by a global function is `𝒪`-linear", and it
is obtained here for free, by conjugating `(tensoringRight C).map a` by the right unitor read as
a natural isomorphism `- ⊗ 𝟙_ C ≅ 𝟭 C`, so that naturality is the naturality of a composite of
natural transformations.

Two further computations pin the action down: it is `a` itself at the unit
(`unitEndScalar_unit`), and it is compatible with the tensor product in the sense that
`unitEndScalar a |>.app (A ⊗ B) = A ◁ unitEndScalar a |>.app B` (`unitEndScalar_tensor`).

Together with the invertibility of an object — `CategoryTheory.MonoidalCategory.HasInverse`, a
two-sided tensor inverse — these give the statement this file exists for:

`eq_zero_of_mono_unit_comp_eq_zero`: **if `L` is invertible and `f : 𝟙_ C ⟶ L` is a
monomorphism, then an endomorphism `k` of `L` with `f ≫ k = 0` vanishes.**

## Main definitions

* `CategoryTheory.MonoidalCategory.unitEndScalar`: the action of an endomorphism of the tensor
  unit on every object, as an endomorphism of the identity functor.

## Main results

* `CategoryTheory.MonoidalCategory.unitEndScalar_unit`,
  `CategoryTheory.MonoidalCategory.unitEndScalar_tensor`: the two computations above.
* `CategoryTheory.MonoidalCategory.unitEndScalar_app_eq_of_hasInverse`: **every endomorphism of
  an invertible object is the action of an endomorphism of the tensor unit** — namely of the one
  it becomes under the trivialisation `L' ⊗ L ≅ 𝟙_ C`.
* `CategoryTheory.MonoidalCategory.eq_zero_of_mono_unit_comp_eq_zero`: the statement displayed
  above.

## Implementation notes

**No `MonoidalPreadditive` is needed.** The last step of the argument needs `L ◁ 0 = 0`, which is
one of the four fields of `CategoryTheory.MonoidalPreadditive`; but for an *invertible* `L` the
functor `MonoidalCategory.tensorLeft L` is an equivalence
(`CategoryTheory.MonoidalCategory.HasInverse.tensorLeftEquivalence`), hence a left adjoint, hence
preserves zero morphisms by Mathlib's
`CategoryTheory.Functor.preservesZeroMorphisms_of_isLeftAdjoint`. So
`whiskerLeft_eq_zero_of_hasInverse` and `eq_of_whiskerLeft_eq_of_hasInverse` — zero and
faithfulness, the only two things the argument asks of the tensor product — come from the
equivalence alone, and the results below hold in any monoidal category with zero morphisms, with no
bilinearity hypothesis on the tensor product.
-/

@[expose] public noncomputable section

namespace CategoryTheory.MonoidalCategory

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The action of an endomorphism `a` of the tensor unit on every object of `C`**, as an
endomorphism of the identity functor: on `B` it is `B ◁ a` conjugated by the right unitor.
Writing it as a composite of natural transformations is what makes its naturality — the
centrality of `a` — hold by construction. -/
def unitEndScalar (a : 𝟙_ C ⟶ 𝟙_ C) : 𝟭 C ⟶ 𝟭 C :=
  (rightUnitorNatIso C).inv ≫ (tensoringRight C).map a ≫ (rightUnitorNatIso C).hom

/-- The action of `a` on an object is `B ◁ a` conjugated by the right unitor. -/
theorem unitEndScalar_app (a : 𝟙_ C ⟶ 𝟙_ C) (B : C) :
    (unitEndScalar a).app B = (ρ_ B).inv ≫ (B ◁ a) ≫ (ρ_ B).hom := by
  simp [unitEndScalar]

/-- **An endomorphism of the tensor unit is central:** its action commutes with every morphism
of `C`. -/
theorem unitEndScalar_naturality (a : 𝟙_ C ⟶ 𝟙_ C) {B B' : C} (h : B ⟶ B') :
    (unitEndScalar a).app B ≫ h = h ≫ (unitEndScalar a).app B' :=
  ((unitEndScalar a).naturality h).symm

/-- The action of `a` on the tensor unit is `a`: the two unitors agree at the unit, and the left
unitor is natural. -/
theorem unitEndScalar_unit (a : 𝟙_ C ⟶ 𝟙_ C) : (unitEndScalar a).app (𝟙_ C) = a := by
  rw [unitEndScalar_app, ← unitors_equal, leftUnitor_naturality, unitors_equal,
    Iso.inv_hom_id_assoc]

/-- The action of `a` on a tensor product is its action on the right factor, whiskered: the
right unitor of a tensor product factors through the associator, which carries `(A ⊗ B) ◁ a` to
`A ◁ B ◁ a`. -/
theorem unitEndScalar_tensor (a : 𝟙_ C ⟶ 𝟙_ C) (A B : C) :
    (unitEndScalar a).app (A ⊗ B) = A ◁ (unitEndScalar a).app B := by
  have key : (α_ A B (𝟙_ C)).inv ≫ (A ⊗ B) ◁ a ≫ (α_ A B (𝟙_ C)).hom = A ◁ B ◁ a := by
    rw [associator_naturality_right, Iso.inv_hom_id_assoc]
  rw [unitEndScalar_app, unitEndScalar_app, whiskerLeft_comp, whiskerLeft_comp,
    rightUnitor_tensor_hom, rightUnitor_tensor_inv, Category.assoc, ← key]
  simp

/-- Tensoring on the left by an invertible object is an equivalence. -/
private theorem isEquivalence_tensorLeft_of_hasInverse {L : C} (h : HasInverse L) :
    (tensorLeft L).IsEquivalence :=
  h.tensorLeftEquivalence.isEquivalence_functor

/-- **Whiskering by an invertible object kills the zero morphism.** Tensoring by an invertible
object is an equivalence, hence a left adjoint, hence preserves zero morphisms; no bilinearity
of the tensor product is assumed. -/
theorem whiskerLeft_eq_zero_of_hasInverse [Limits.HasZeroMorphisms C] {L : C}
    (h : HasInverse L) {A B : C} : L ◁ (0 : A ⟶ B) = 0 := by
  have := isEquivalence_tensorLeft_of_hasInverse h
  exact (tensorLeft L).map_zero A B

/-- **Whiskering by an invertible object is injective on morphisms**: tensoring by an invertible
object is an equivalence, hence faithful. -/
theorem eq_of_whiskerLeft_eq_of_hasInverse {L : C}
    (h : HasInverse L) {A B : C} {f g : A ⟶ B} (hf : L ◁ f = L ◁ g) : f = g := by
  have := isEquivalence_tensorLeft_of_hasInverse h
  exact (tensorLeft L).map_injective (a₁ := f) (a₂ := g) hf

/-- **Every endomorphism of an invertible object is the action of an endomorphism of the tensor
unit**, namely of the endomorphism `a` it becomes under the trivialisation `L' ⊗ L ≅ 𝟙_ C`.

Whiskering by `L'` is injective, so it is enough to check the identity after whiskering; there
the left-hand side is the action of `a` on `L' ⊗ L` by `unitEndScalar_tensor`, which by
centrality and `unitEndScalar_unit` is `a` conjugated back by the trivialisation, i.e. `L' ◁ k`
again. -/
theorem unitEndScalar_app_eq_of_hasInverse {L : C} (h : HasInverse L) (k : L ⟶ L) :
    (unitEndScalar (h.isoRight.inv ≫ (h.inv ◁ k) ≫ h.isoRight.hom)).app L = k := by
  refine eq_of_whiskerLeft_eq_of_hasInverse h.hasInverseInv ?_
  rw [← unitEndScalar_tensor]
  have h2 := unitEndScalar_naturality
    (h.isoRight.inv ≫ (h.inv ◁ k) ≫ h.isoRight.hom) h.isoRight.hom
  rw [unitEndScalar_unit, ← Iso.eq_comp_inv] at h2
  rw [h2]
  simp

/-- **An endomorphism of an invertible object killed by a monomorphism out of the tensor unit is
zero.**

The endomorphism `k` is the action of an endomorphism `a` of the tensor unit
(`unitEndScalar_app_eq_of_hasInverse`); centrality turns `f ≫ k = 0` into `a ≫ f = 0`, the
monomorphism `f` cancels and leaves `a = 0`, and the action of `0` is `0`. -/
theorem eq_zero_of_mono_unit_comp_eq_zero [Limits.HasZeroMorphisms C] {L : C}
    (h : HasInverse L) {f : 𝟙_ C ⟶ L} (hf : Mono f) {k : L ⟶ L} (hk : f ≫ k = 0) : k = 0 := by
  have := hf
  have hkeq := unitEndScalar_app_eq_of_hasInverse h k
  have h3 := unitEndScalar_naturality (h.isoRight.inv ≫ (h.inv ◁ k) ≫ h.isoRight.hom) f
  rw [unitEndScalar_unit, hkeq, hk] at h3
  have ha : h.isoRight.inv ≫ (h.inv ◁ k) ≫ h.isoRight.hom = 0 :=
    (cancel_mono f).mp (h3.trans (Limits.zero_comp).symm)
  rw [← hkeq, unitEndScalar_app, ha, whiskerLeft_eq_zero_of_hasInverse h]
  simp

end CategoryTheory.MonoidalCategory

end
