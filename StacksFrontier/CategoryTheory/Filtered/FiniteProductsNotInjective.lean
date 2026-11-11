module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import StacksFrontier.CategoryTheory.Filtered.FiniteProducts

/-!
# Colimits over a weakly filtered index do not commute with products (Stacks 09WQ)

Stacks 09WQ considers an index category `I` in which every pair of objects admits a
common upper bound, and states:

1. for diagrams of sets `M, N` over `I`, the comparison
   `colim (M ⨯ N) ⟶ colim M ⨯ colim N` is surjective
   (`CategoryTheory.Limits.surjective_prodComparison_colim`);
2. in general, colimits of diagrams of sets over such `I` do not commute with finite
   nonempty products.

This file proves part (2) by an explicit example and packages both parts as
`CategoryTheory.Limits.colim_prod_surjective_and_not_injective`.

The example: `I` is the walking parallel pair `0 ⇉ 1` (which satisfies the hypothesis,
every pair of objects mapping to `1`), and `M = N` is the pair of maps
`id, not : Bool ⟶ Bool` (lifted to `Type v`). The colimit of `M` is a point, while
`colim (M ⨯ N)` is `Bool × Bool` modulo `(a, b) ~ (¬a, ¬b)`, which has two elements,
separated by `a xor b`. So the comparison map is not injective, and in particular is not
an isomorphism. (Stacks uses the one-object category of a nontrivial group instead; any
example proves the negative statement.)
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v u

open WalkingParallelPair

/-- The two maps `id, not : Bool ⟶ Bool` (on `ULift Bool`), indexed by the morphisms of
the walking parallel pair. -/
def boolNotMap : {j k : WalkingParallelPair} → (j ⟶ k) → ULift.{v} Bool → ULift.{v} Bool
  | _, _, WalkingParallelPairHom.left, b => b
  | _, _, WalkingParallelPairHom.right, b => ⟨!b.down⟩
  | _, _, WalkingParallelPairHom.id _, b => b

/-- The diagram `id, not : Bool ⇉ Bool` of sets, lifted to `Type v`. -/
@[simps]
def boolNotParallelPair : WalkingParallelPair ⥤ Type v where
  obj _ := ULift.{v} Bool
  map f := TypeCat.ofHom (boolNotMap f)
  map_id _ := rfl
  map_comp f g := by cases f <;> cases g <;> rfl

/-- The cocone on `M ⨯ M` (for `M = boolNotParallelPair`) given by `(a, b) ↦ a xor b`,
which is invariant under negating both coordinates. -/
noncomputable def boolNotParallelPairProdXorCocone :
    Cocone (boolNotParallelPair.{v} ⨯ boolNotParallelPair.{v}) where
  pt := ULift.{v} Bool
  ι :=
    { app := fun j => TypeCat.ofHom fun w => ULift.up <|
        xor ((Limits.prod.fst (X := boolNotParallelPair.{v})).app j w).down
          ((Limits.prod.snd (X := boolNotParallelPair.{v})).app j w).down
      naturality := by
        intro j k f
        refine ConcreteCategory.hom_ext _ _ fun w => ?_
        have h1 := ConcreteCategory.congr_hom
          ((Limits.prod.fst (X := boolNotParallelPair.{v})).naturality f) w
        have h2 := ConcreteCategory.congr_hom
          ((Limits.prod.snd (X := boolNotParallelPair.{v})).naturality f) w
        simp only [ConcreteCategory.comp_apply] at h1 h2
        simp only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply, Functor.const_obj_map, h1, h2,
          boolNotParallelPair_map]
        cases f
        · rfl
        · exact congrArg ULift.up (Bool.not_xor_not _ _)
        · rfl }

/-- **Stacks 09WQ (2).** There are an index category in which every pair of objects
admits a common upper bound, and diagrams of sets `M, N` over it, for which the
comparison `colim (M ⨯ N) ⟶ colim M ⨯ colim N` is not injective: colimits over such
index categories do not commute with finite nonempty products. -/
theorem exists_not_injective_prodComparison_colim :
    ∃ (I : Type) (_ : SmallCategory I),
      (∀ x y : I, ∃ (z : I) (_ : x ⟶ z) (_ : y ⟶ z), True) ∧
      ∃ M N : I ⥤ Type v,
        ¬ Function.Injective (prodComparison (colim : (I ⥤ Type v) ⥤ Type v) M N) := by
  refine ⟨WalkingParallelPair, inferInstance, fun x y => ⟨one, ?_, ?_, trivial⟩,
    boolNotParallelPair, boolNotParallelPair, ?_⟩
  · cases x
    exacts [WalkingParallelPairHom.left, 𝟙 _]
  · cases y
    exacts [WalkingParallelPairHom.left, 𝟙 _]
  set M : WalkingParallelPair ⥤ Type v := boolNotParallelPair.{v}
  have key : ∀ {P : WalkingParallelPair ⥤ Type v} (f : M ⨯ M ⟶ P)
      (g : colim.obj M ⨯ colim.obj M ⟶ colim.obj P),
      prodComparison (colim : (WalkingParallelPair ⥤ Type v) ⥤ Type v) M M ≫ g = colim.map f →
      ∀ (k : WalkingParallelPair) (w : (M ⨯ M).obj k),
      g (prodComparison (colim : (WalkingParallelPair ⥤ Type v) ⥤ Type v) M M
          (colimit.ι (M ⨯ M) k w)) = colimit.ι P k (f.app k w) := by
    intro P f g hfg k w
    have e1 := ConcreteCategory.congr_hom hfg (colimit.ι (M ⨯ M) k w)
    have e2 := ConcreteCategory.congr_hom (ι_colimMap f k) w
    simp only [ConcreteCategory.comp_apply, colim_map] at e1 e2
    exact e1.trans e2
  -- the comparison only sees the classes of the two coordinates
  have hcomp : ∀ a b c d : M.obj one, colimit.ι M one a = colimit.ι M one c →
      colimit.ι M one b = colimit.ι M one d →
      prodComparison (colim : (WalkingParallelPair ⥤ Type v) ⥤ Type v) M M
          (colimit.ι (M ⨯ M) one (FunctorToTypes.prodMk a b)) =
        prodComparison (colim : (WalkingParallelPair ⥤ Type v) ⥤ Type v) M M
          (colimit.ι (M ⨯ M) one (FunctorToTypes.prodMk c d)) := by
    intro a b c d hac hbd
    apply (Types.binaryProductIso (colim.obj M) (colim.obj M)).toEquiv.injective
    simp only [Iso.toEquiv_fun]
    refine Prod.ext ?_ ?_
    · simp only [Types.binaryProductIso_hom_comp_fst_apply]
      rw [key _ _ (prodComparison_fst _ _ _), key _ _ (prodComparison_fst _ _ _),
        FunctorToTypes.prodMk_fst, FunctorToTypes.prodMk_fst, hac]
    · simp only [Types.binaryProductIso_hom_comp_snd_apply]
      rw [key _ _ (prodComparison_snd _ _ _), key _ _ (prodComparison_snd _ _ _),
        FunctorToTypes.prodMk_snd, FunctorToTypes.prodMk_snd, hbd]
  -- the cocone `xor` separates classes of `colim (M ⨯ M)`
  have hdesc : ∀ a b : M.obj one,
      colimit.desc (M ⨯ M) boolNotParallelPairProdXorCocone
          (colimit.ι (M ⨯ M) one (FunctorToTypes.prodMk a b)) =
        ULift.up (xor (ULift.down (α := Bool) a) (ULift.down (α := Bool) b)) := by
    intro a b
    rw [colimit.ι_desc_apply]
    change ULift.up (xor ((Limits.prod.fst (X := M)).app one (FunctorToTypes.prodMk a b)).down
      ((Limits.prod.snd (X := M)).app one (FunctorToTypes.prodMk a b)).down) = _
    rw [FunctorToTypes.prodMk_fst, FunctorToTypes.prodMk_snd]
  -- in `colim M`, the two points of `M.obj one` are identified
  have hM : colimit.ι M one (⟨true⟩ : M.obj one) = colimit.ι M one (⟨false⟩ : M.obj one) := by
    have e1 := colimit.w_apply M WalkingParallelPairHom.left (⟨false⟩ : M.obj zero)
    have e2 := colimit.w_apply M WalkingParallelPairHom.right (⟨false⟩ : M.obj zero)
    exact e2.trans e1.symm
  intro hinj
  have hne := congrArg (colimit.desc (M ⨯ M) boolNotParallelPairProdXorCocone)
    (hinj (hcomp ⟨true⟩ ⟨false⟩ ⟨false⟩ ⟨false⟩ hM rfl))
  have h := (hdesc ⟨true⟩ ⟨false⟩).symm.trans (hne.trans (hdesc ⟨false⟩ ⟨false⟩))
  exact absurd (congrArg ULift.down h) (by decide)

/-- **Stacks 09WQ.** Let `I` be a category in which every pair of objects `x, y` admits
an object `z` with morphisms `x ⟶ z` and `y ⟶ z`. Then

1. for all diagrams of sets `M, N` over `I`, the comparison
   `colim (M ⨯ N) ⟶ colim M ⨯ colim N` is surjective;
2. in general colimits of diagrams of sets over such index categories do not commute
   with finite nonempty products: there are such an `I` and diagrams `M, N` for which
   the comparison is not injective.

Part (1) is `surjective_prodComparison_colim`, part (2) is
`exists_not_injective_prodComparison_colim`. The instance `HasColimitsOfShape I (Type v)`
in part (1) only makes the colimit functor available; it holds for every small `I`. -/
@[stacks 09WQ]
theorem colim_prod_surjective_and_not_injective :
    (∀ (I : Type u) [Category.{v} I] [HasColimitsOfShape I (Type v)],
      (∀ x y : I, ∃ (z : I) (_ : x ⟶ z) (_ : y ⟶ z), True) →
      ∀ M N : I ⥤ Type v,
        Function.Surjective (prodComparison (colim : (I ⥤ Type v) ⥤ Type v) M N)) ∧
    ∃ (I : Type) (_ : SmallCategory I),
      (∀ x y : I, ∃ (z : I) (_ : x ⟶ z) (_ : y ⟶ z), True) ∧
      ∃ M N : I ⥤ Type v,
        ¬ Function.Injective (prodComparison (colim : (I ⥤ Type v) ⥤ Type v) M N) :=
  ⟨fun _ _ _ h M N => surjective_prodComparison_colim h M N,
    exists_not_injective_prodComparison_colim⟩

end CategoryTheory.Limits
