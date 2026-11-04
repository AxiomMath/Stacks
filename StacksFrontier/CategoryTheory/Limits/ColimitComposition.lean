module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Composing coproducts and composing cokernels

Two facts about colimits needed to present a tensor product of two presented objects, both of
them pure category theory.

The first assembles a coproduct of copies of one object out of a binary coproduct of two such
coproducts: the index type of the result is the sum of the two index types.  The companion fact
for a *product* of index types, a coproduct of coproducts, is Mathlib's
`CategoryTheory.Limits.Cofan.IsColimit.prod`.

The second composes two cokernels.  If `p` is a cokernel of `y` and `q` is a cokernel of `w`,
then `p ≫ q` is a cokernel of the morphism out of the binary coproduct of the two sources whose
components are `y` and a morphism `v` related to `w` by an epimorphism over `p`.

## Main results

* `Stacks.CategoryTheory.ColimitComposition.isColimitCofanSum`
* `Stacks.CategoryTheory.ColimitComposition.isColimitCokernelComp`
* `Stacks.CategoryTheory.ColimitComposition.isColimitCokernelCompIso`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.CategoryTheory.ColimitComposition

variable {D : Type u} [Category.{v} D]

/-- A binary coproduct of two coproducts of copies of a single object `A` is a coproduct of
copies of `A` indexed by the sum of the two index types. -/
def isColimitCofanSum {I₁ I₂ : Type*} {A Y V Z : D}
    {g₁ : I₁ → (A ⟶ Y)} {g₂ : I₂ → (A ⟶ V)} {jY : Y ⟶ Z} {jV : V ⟶ Z}
    (h₁ : IsColimit (Cofan.mk Y g₁)) (h₂ : IsColimit (Cofan.mk V g₂))
    (hb : IsColimit (BinaryCofan.mk jY jV)) :
    IsColimit (Cofan.mk (f := fun _ : I₁ ⊕ I₂ ↦ A) Z
      (Sum.elim (fun i ↦ g₁ i ≫ jY) fun i ↦ g₂ i ≫ jV)) := by
  have hl : ∀ {T : D} (f₁ : Y ⟶ T) (f₂ : V ⟶ T),
      jY ≫ BinaryCofan.IsColimit.desc hb f₁ f₂ = f₁ :=
    fun f₁ f₂ ↦ BinaryCofan.IsColimit.inl_desc hb f₁ f₂
  have hr : ∀ {T : D} (f₁ : Y ⟶ T) (f₂ : V ⟶ T),
      jV ≫ BinaryCofan.IsColimit.desc hb f₁ f₂ = f₂ :=
    fun f₁ f₂ ↦ BinaryCofan.IsColimit.inr_desc hb f₁ f₂
  refine Cofan.IsColimit.mk _
    (fun t ↦ BinaryCofan.IsColimit.desc hb
      (Cofan.IsColimit.desc h₁ fun i ↦ t.inj (Sum.inl i))
      (Cofan.IsColimit.desc h₂ fun i ↦ t.inj (Sum.inr i))) ?_ ?_
  · rintro t (i | i)
    · exact (Category.assoc (g₁ i) jY _).trans
        ((congrArg (g₁ i ≫ ·) (hl _ _)).trans (Cofan.IsColimit.fac h₁ _ i))
    · exact (Category.assoc (g₂ i) jV _).trans
        ((congrArg (g₂ i ≫ ·) (hr _ _)).trans (Cofan.IsColimit.fac h₂ _ i))
  · intro t m hm
    refine BinaryCofan.IsColimit.hom_ext hb ?_ ?_
    · exact (Cofan.IsColimit.hom_ext h₁ (jY ≫ m) _ fun i ↦
        ((Category.assoc (g₁ i) jY m).symm.trans (hm (Sum.inl i))).trans
          (Cofan.IsColimit.fac h₁ (fun i ↦ t.inj (Sum.inl i)) i).symm).trans (hl _ _).symm
    · exact (Cofan.IsColimit.hom_ext h₂ (jV ≫ m) _ fun i ↦
        ((Category.assoc (g₂ i) jV m).symm.trans (hm (Sum.inr i))).trans
          (Cofan.IsColimit.fac h₂ (fun i ↦ t.inj (Sum.inr i)) i).symm).trans (hr _ _).symm

variable [HasZeroMorphisms D]

/-- **The composition of two cokernels is a cokernel.**  If `p : Z ⟶ X` is a cokernel of
`y : Y ⟶ Z` and `q : X ⟶ M` is a cokernel of `w : W ⟶ X`, and if an epimorphism `e : V ⟶ W`
together with `v : V ⟶ Z` makes the square `v ≫ p = e ≫ w` commute, then `p ≫ q` is a cokernel
of the morphism `d` out of a binary coproduct of `Y` and `V` whose two components are `y`
and `v`. -/
def isColimitCokernelComp {Y V W Z X M E : D} {y : Y ⟶ Z} {p : Z ⟶ X} {w : W ⟶ X} {q : X ⟶ M}
    {e : V ⟶ W} {v : V ⟶ Z} {jY : Y ⟶ E} {jV : V ⟶ E} {d : E ⟶ Z}
    {hyp : y ≫ p = 0} (hp : IsColimit (CokernelCofork.ofπ p hyp))
    {hwq : w ≫ q = 0} (hq : IsColimit (CokernelCofork.ofπ q hwq))
    [Epi e] (hsq : v ≫ p = e ≫ w) (hjY : jY ≫ d = y) (hjV : jV ≫ d = v)
    (hd : d ≫ p ≫ q = 0) :
    IsColimit (CokernelCofork.ofπ (p ≫ q) hd) := by
  have hpepi : Epi p := by simpa using epi_of_isColimit_cofork hp
  have hqepi : Epi q := by simpa using epi_of_isColimit_cofork hq
  refine Cofork.IsColimit.mk' _ (fun s ↦ ?_)
  have hs : d ≫ Cofork.π s = 0 := by simp
  have hy : y ≫ Cofork.π s = 0 := by rw [← hjY, Category.assoc, hs, comp_zero]
  have hv : v ≫ Cofork.π s = 0 := by rw [← hjV, Category.assoc, hs, comp_zero]
  obtain ⟨k₁, hk₁⟩ := Cofork.IsColimit.desc' hp (Cofork.π s) (by rw [zero_comp]; exact hy)
  rw [show Cofork.π (CokernelCofork.ofπ p hyp) = p from rfl] at hk₁
  have hw : w ≫ k₁ = 0 := by
    rw [← cancel_epi e, comp_zero, ← Category.assoc, ← hsq, Category.assoc, hk₁, hv]
  obtain ⟨k₂, hk₂⟩ := Cofork.IsColimit.desc' hq k₁ (by rw [zero_comp]; exact hw)
  rw [show Cofork.π (CokernelCofork.ofπ q hwq) = q from rfl] at hk₂
  refine ⟨k₂, ?_, ?_⟩
  · rw [show Cofork.π (CokernelCofork.ofπ (p ≫ q) hd) = p ≫ q from rfl, Category.assoc, hk₂, hk₁]
  · intro m hm
    rw [show Cofork.π (CokernelCofork.ofπ (p ≫ q) hd) = p ≫ q from rfl, Category.assoc] at hm
    rw [← cancel_epi q, hk₂]
    rw [← cancel_epi p, hk₁]
    exact hm

/-- A cokernel followed by an isomorphism is a cokernel. -/
def isColimitCokernelCompIso {Y Z X X' : D} {y : Y ⟶ Z} {p : Z ⟶ X} (φ : X ≅ X')
    {hyp : y ≫ p = 0} (hp : IsColimit (CokernelCofork.ofπ p hyp))
    (hyp' : y ≫ p ≫ φ.hom = 0) :
    IsColimit (CokernelCofork.ofπ (p ≫ φ.hom) hyp') := by
  have hpepi : Epi p := by simpa using epi_of_isColimit_cofork hp
  refine Cofork.IsColimit.mk' _ (fun s ↦ ?_)
  have hy : y ≫ Cofork.π s = 0 := by simp
  obtain ⟨k, hk⟩ := Cofork.IsColimit.desc' hp (Cofork.π s) (by rw [zero_comp]; exact hy)
  rw [show Cofork.π (CokernelCofork.ofπ p hyp) = p from rfl] at hk
  refine ⟨φ.inv ≫ k, ?_, ?_⟩
  · rw [show Cofork.π (CokernelCofork.ofπ (p ≫ φ.hom) hyp') = p ≫ φ.hom from rfl,
      Category.assoc, ← Category.assoc φ.hom, φ.hom_inv_id, Category.id_comp, hk]
  · intro m hm
    rw [show Cofork.π (CokernelCofork.ofπ (p ≫ φ.hom) hyp') = p ≫ φ.hom from rfl] at hm
    rw [← cancel_epi φ.hom, ← Category.assoc, φ.hom_inv_id, Category.id_comp,
      ← cancel_epi p, hk, ← Category.assoc]
    exact hm

end Stacks.CategoryTheory.ColimitComposition

end
