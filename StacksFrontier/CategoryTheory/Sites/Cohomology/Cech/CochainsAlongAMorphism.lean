module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstCocycles

/-!
# Čech cochains along a morphism of coefficients, and degree-zero cochains

Let `C` be a category, let `X` be an object of `C` and let `E = {U_i → X}` be a family of
morphisms with target `X` whose finite nonempty iterated fibre products exist. A morphism of
abelian presheaves acts on the Čech cochains of `E` termwise, and the resulting map commutes
with the Čech differential. In degree zero a Čech cochain is the same thing as a family of
sections, one over each member `U_i`, because the one-member iterated fibre product projects
isomorphically onto its member.

## Main definitions

* `Stacks.CechSite.pushCochain`: the termwise action of a morphism of presheaves on Čech
  cochains.
* `Stacks.CechSite.famCochain` and `Stacks.CechSite.cochainFam`: the two directions of the
  identification of degree-zero Čech cochains with families of sections over the members.

## Main results

* `Stacks.CechSite.cechDifferential_pushCochain`: pushing a cochain along a morphism of
  presheaves commutes with the Čech differential.
* `Stacks.CechSite.famCochain_cochainFam` and `Stacks.CechSite.cochainFam_famCochain`: the two
  directions are mutually inverse.
* `Stacks.CechSite.cechDifferential_zero_famCochain`: the Čech differential of the cochain of a
  family of sections is the difference of the two restrictions to the twofold iterated fibre
  products, with no one-member products left in the formula.

## Implementation notes

A degree-`n` Čech cochain is indexed by `(n+1)`-tuples of members, so a degree-zero cochain is
indexed by `Fin 1 → E.I₀` and its value at `l` is a section over the *one-member* product
`∏ᶜ (fun _ : Fin 1 ↦ Over.mk (E.f (l 0)))` rather than over the member itself. The two are
identified by `Stacks.CechSite.singletonProjection`, which is an isomorphism, and the
degree-zero differential formula is obtained by composing the face projections with that
isomorphism, which `Limits.Pi.lift_comp_π` does in one step.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03AN](https://stacks.math.columbia.edu/tag/03AN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe a w v u

namespace Stacks.CechSite

attribute [local instance] singletonProjection_isIso

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasProducts.{w} AddCommGrpCat.{a}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- A morphism of abelian presheaves acts on Čech cochains termwise. -/
def pushCochain {F F' : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ F') (n : ℕ) :
    cechCochain E F n →+ cechCochain E F' n where
  toFun c := fun k ↦ φ.app _ (c k)
  map_zero' := by funext k; exact map_zero _
  map_add' c c' := by funext k; exact map_add _ _ _

omit [HasProducts.{w} AddCommGrpCat.{a}] in
/-- The value of a pushed cochain at a tuple of indices is the image of the original value. -/
lemma pushCochain_apply {F F' : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ F') (n : ℕ)
    (c : cechCochain E F n) (k : Fin (n + 1) → E.I₀) :
    pushCochain E φ n c k = φ.app _ (c k) := rfl

/-- Pushing a Čech cochain along a morphism of presheaves commutes with the Čech
differential. -/
lemma cechDifferential_pushCochain {F F' : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ F') (n : ℕ)
    (c : cechCochain E F n) :
    cechDifferential E F' n (pushCochain E φ n c) =
      pushCochain E φ (n + 1) (cechDifferential E F n c) := by
  funext k
  rw [cechDifferential_apply, pushCochain_apply, cechDifferential_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, pushCochain_apply]
  exact congrArg _ (NatTrans.naturality_apply φ (faceProjection E k j).left.op _).symm

omit [HasProducts.{w} AddCommGrpCat.{a}] in
/-- Pushing a Čech cochain along a composite of morphisms of presheaves. -/
lemma pushCochain_comp {F F' F'' : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ F') (ψ : F' ⟶ F'')
    (n : ℕ) (c : cechCochain E F n) :
    pushCochain E ψ n (pushCochain E φ n c) = pushCochain E (φ ≫ ψ) n c := by
  funext k
  exact (ConcreteCategory.comp_apply (φ.app _) (ψ.app _) (c k)).symm

/-! ### Degree-zero cochains and families of sections -/

variable (F : Cᵒᵖ ⥤ AddCommGrpCat.{a})

/-- The degree-zero Čech cochain of a family of sections over the members of the family,
restricted along the projection of the one-member iterated fibre product. -/
def famCochain (t : ∀ i, F.obj (op (E.X i))) : cechCochain E F 0 :=
  fun l ↦ F.map (Pi.π (fun j : Fin 1 ↦ Over.mk (E.f (l j))) 0).left.op (t (l 0))

/-- The family of sections underlying a degree-zero Čech cochain. -/
def cochainFam (b : cechCochain E F 0) (i : E.I₀) : F.obj (op (E.X i)) :=
  F.map (inv (singletonProjection E i)).left.op (b fun _ ↦ i)

omit [HasProducts.{w} AddCommGrpCat.{a}] in
/-- Taking the degree-zero cochain of a family of sections and then its underlying family
recovers the family. -/
lemma cochainFam_famCochain (t : ∀ i, F.obj (op (E.X i))) :
    cochainFam E F (famCochain E F t) = t := by
  funext i
  show F.map (inv (singletonProjection E i)).left.op
    (F.map (singletonProjection E i).left.op (t i)) = t i
  rw [← Functor.map_comp_apply, ← op_comp, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
    op_id, F.map_id]
  rfl

omit [HasProducts.{w} AddCommGrpCat.{a}] in
/-- Taking the family of sections underlying a degree-zero cochain and then its cochain
recovers the cochain. -/
lemma famCochain_cochainFam (b : cechCochain E F 0) :
    famCochain E F (cochainFam E F b) = b := by
  funext l
  obtain ⟨i, rfl⟩ : ∃ i, l = fun _ ↦ i := ⟨l 0, funext fun j ↦ congrArg l (Fin.eq_zero j)⟩
  show F.map (singletonProjection E i).left.op
    (F.map (inv (singletonProjection E i)).left.op (b fun _ ↦ i)) = _
  rw [← Functor.map_comp_apply, ← op_comp, ← Over.comp_left, IsIso.hom_inv_id, Over.id_left,
    op_id, F.map_id]
  rfl

/-- The Čech differential of the degree-zero cochain of a family of sections, at a pair of
indices: the difference of the two restrictions to the twofold iterated fibre product. -/
lemma cechDifferential_zero_famCochain (t : ∀ i, F.obj (op (E.X i))) (k : Fin 2 → E.I₀) :
    cechDifferential E F 0 (famCochain E F t) k =
      F.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) (1 : Fin 2)).left.op (t (k 1)) -
        F.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) (0 : Fin 2)).left.op (t (k 0)) := by
  have key : ∀ m : Fin 2,
      F.map (faceProjection E k m).left.op
        (F.map (Pi.π (fun j : Fin 1 ↦ Over.mk (E.f (k (m.succAbove j)))) 0).left.op
          (t (k (m.succAbove 0)))) =
      F.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) (m.succAbove 0)).left.op (t (k (m.succAbove 0))) :=
    fun m ↦ by
      rw [← Functor.map_comp_apply, ← op_comp, ← Over.comp_left]
      rw [show faceProjection E k m ≫
        Pi.π (fun j : Fin 1 ↦ Over.mk (E.f (k (m.succAbove j)))) 0 = _ from Pi.lift_comp_π _ _]
  rw [cechDifferential_zero_apply]
  exact congrArg₂ (· - ·) (key 0) (key 1)

end Stacks.CechSite

end
