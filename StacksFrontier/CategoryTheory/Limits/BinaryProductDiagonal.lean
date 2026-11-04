module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Representable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Binary products against a diagonal

Two facts about binary products.

The first is that a product of two morphisms inherits from its factors a morphism property
stable under composition and base change, and likewise a relative morphism property stable under
composition.

The second identifies the base change of a diagonal `Δ : F ⟶ F ⨯ F` along `prod.map q q`:
when `t, s : R ⟶ X` is a kernel pair of `q : X ⟶ F`, that base change is `R` with the
projection `prod.lift t s`.

## Main results

* `CategoryTheory.MorphismProperty.prod_map`: a morphism property which is stable under
  composition and under base change is stable under binary products of morphisms.
* `CategoryTheory.MorphismProperty.relative_prod_map`: the same for a relative morphism
  property.
* `CategoryTheory.Limits.isPullback_diagonal_prod_of_kernelPair`: the kernel pair of `q`
  presents the base change of the diagonal of its target along `prod.map q q`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

/-- A morphism property which is stable under composition and under base change is stable
under binary products of morphisms: if `P f` and `P g`, then `P (prod.map f g)`. -/
@[ega "I 3.5.1" "more general",
  ega "I 5.5.12" "(iv) ⇒ (iii) under (ii)",
  sga "3 IV 3.4.1" "special case"]
theorem prod_map {C : Type*} [Category* C] [HasBinaryProducts C] (P : MorphismProperty C)
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (hf : P f) (hg : P g) :
    P (prod.map f g) := by
  have hri : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hfirst : P (prod.map f (𝟙 X')) :=
    P.of_isPullback (IsPullback.of_prod_fst_with_id f X') hf
  have hbase : P (prod.map g (𝟙 Y)) :=
    P.of_isPullback (IsPullback.of_prod_fst_with_id g Y) hg
  have hswap : ((prod.braiding Y X').hom ≫ prod.map g (𝟙 Y)) ≫ (prod.braiding Y' Y).hom =
      prod.map (𝟙 Y) g := by
    apply prod.hom_ext <;> simp
  have hsecond : P (prod.map (𝟙 Y) g) := by
    rw [← hswap]
    exact MorphismProperty.RespectsIso.postcomp _ (prod.braiding Y' Y).hom _
      (MorphismProperty.RespectsIso.precomp _ (prod.braiding Y X').hom _ hbase)
  have hmap : prod.map f (𝟙 X') ≫ prod.map (𝟙 Y) g = prod.map f g := by
    apply prod.hom_ext <;> simp
  simpa only [hmap] using MorphismProperty.comp_mem _ _ _ hfirst hsecond

/-- A relative morphism property of a fully faithful functor which is stable under
composition is stable under binary products of morphisms. -/
@[ega "I 3.5.1" "(ii), special case"]
theorem relative_prod_map {C D : Type*} [Category* C] [Category* D] [HasBinaryProducts D]
    (F : C ⥤ D) (P : MorphismProperty C) [F.Full] [F.Faithful]
    [P.IsStableUnderComposition] {X Y X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : P.relative F f) (hg : P.relative F g) : P.relative F (prod.map f g) := by
  have : (P.relative F).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  exact prod_map (P.relative F) f g hf hg

end CategoryTheory.MorphismProperty

namespace CategoryTheory.Limits

/-- If `t, s : R ⟶ X` is a kernel pair of `q : X ⟶ F`, then `R` with the morphisms
`t ≫ q` and `prod.lift t s` is the base change of the diagonal of `F` along
`prod.map q q`. -/
theorem isPullback_diagonal_prod_of_kernelPair {C : Type*} [Category* C]
    [HasBinaryProducts C] {R X F : C} (t s : R ⟶ X) (q : X ⟶ F)
    (hker : IsPullback t s q q) :
    IsPullback (t ≫ q) (prod.lift t s) (diag F) (prod.map q q) := by
  have hcomm : (t ≫ q) ≫ diag F = (prod.lift t s) ≫ prod.map q q := by
    apply prod.hom_ext
    · simp
    · simpa [Category.assoc] using hker.w
  let c : PullbackCone (diag F) (prod.map q q) :=
    PullbackCone.mk (t ≫ q) (prod.lift t s) hcomm
  refine IsPullback.of_isLimit (PullbackCone.isLimitAux' c ?_)
  intro d
  let b₁ := d.snd ≫ prod.fst
  let b₂ := d.snd ≫ prod.snd
  have h₁ : d.fst = b₁ ≫ q := by
    calc
      d.fst = (d.fst ≫ diag F) ≫ prod.fst := by simp
      _ = (d.snd ≫ prod.map q q) ≫ prod.fst :=
        congrArg (fun m => m ≫ prod.fst) d.condition
      _ = b₁ ≫ q := by simp [b₁, Category.assoc]
  have h₂ : d.fst = b₂ ≫ q := by
    calc
      d.fst = (d.fst ≫ diag F) ≫ prod.snd := by simp
      _ = (d.snd ≫ prod.map q q) ≫ prod.snd :=
        congrArg (fun m => m ≫ prod.snd) d.condition
      _ = b₂ ≫ q := by simp [b₂, Category.assoc]
  let l := hker.lift b₁ b₂ (h₁.symm.trans h₂)
  refine ⟨l, ?_, ?_, ?_⟩
  · calc
      l ≫ (t ≫ q) = (l ≫ t) ≫ q := by simp [Category.assoc]
      _ = b₁ ≫ q := by simp [l]
      _ = d.fst := h₁.symm
  · change l ≫ prod.lift t s = d.snd
    apply prod.hom_ext
    · simp [l, b₁]
    · simp [l, b₂]
  · intro m hm₁ hm₂
    dsimp [c] at hm₁ hm₂ ⊢
    change d.pt ⟶ R at m
    change m ≫ prod.lift t s = d.snd at hm₂
    apply hker.hom_ext
    · simpa [Category.assoc, b₁, l] using congrArg (fun f => f ≫ prod.fst) hm₂
    · simpa [Category.assoc, b₂, l] using congrArg (fun f => f ≫ prod.snd) hm₂

end CategoryTheory.Limits

end
