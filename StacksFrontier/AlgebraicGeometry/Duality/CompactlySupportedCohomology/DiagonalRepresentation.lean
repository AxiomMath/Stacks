module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Fubini
public import Mathlib.CategoryTheory.Limits.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProMorphisms
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.StrictMajorant

/-!
# Diagonal representation of a countable inverse system of pro-objects

A countable inverse system whose terms are pro-objects indexed by the natural numbers is
represented by a single inverse sequence. Its terms may be chosen diagonally from the given
representing sequences, and maps from the resulting sequence are the iterated colimit of maps
from the original system.

## Main definitions

* `CategoryTheory.Pro.liftedInverseSequence` is an inverse sequence with its indexing category
  lifted to the morphism universe of the ambient category.
* `CategoryTheory.Pro.iteratedIndex` composes the successive reindexing functions used in the
  diagonal.
* `CategoryTheory.Pro.DiagonalRepresentation` packages a diagonal inverse sequence and the
  natural comparison isomorphism.

## Main results

* `CategoryTheory.Pro.exists_diagonalRepresentation` constructs a diagonal representation of a
  countable inverse system of countably represented pro-objects.

## Implementation notes

A pro-object is used through its functor of points `N ↦ colim_n Hom(M_n, N)`, which is
`CategoryTheory.Pro.coyonedaColim`. Thus an inverse system of pro-objects is a direct system of
these functors. The comparison is stated as an isomorphism of functors, which includes its
naturality in `N`. The selected index in row `k` is required to be at least `k`; replacing the
representing increasing maps by their maxima with the identity gives precisely such a diagonal.

## References

* [Stacks Project, Tag 0G53](https://stacks.math.columbia.edu/tag/0G53)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory
attribute [-instance] CategoryTheory.Limits.instCategoryULiftHomULiftOfSmallCategory

universe v u

namespace CategoryTheory.Pro

/-- An inverse sequence with its indexing category lifted to the morphism
universe of the ambient category. -/
public abbrev liftedInverseSequence {C : Type u} [Category.{v} C]
    (M : Functor ℕᵒᵖ C) :
    Functor (ULiftHom.{v} (ULift.{v} ℕᵒᵖ)) C :=
  ULiftHom.down ⋙ ULift.downFunctor ⋙ M

/-- Successively apply the first `i` reindexing functions to `n`.  In the
one-based notation of the source, `iteratedIndex m k k` is
`m_k (m_{k-1} (… (m_2 k) …))`. -/
public def iteratedIndex (m : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | i + 1, n => m i (iteratedIndex m i n)

/-- Iterated increasing reindexings are increasing. -/
public lemma iteratedIndex_monotone (m : ℕ → ℕ → ℕ)
    (hm : ∀ i, Monotone (m i)) (i : ℕ) : Monotone (iteratedIndex m i) := by
  induction i with
  | zero => exact fun _ _ h ↦ h
  | succ i hi => exact fun _ _ h ↦ hm i (hi h)

private lemma iteratedIndex_le (m : ℕ → ℕ → ℕ)
    (hm : ∀ i n, n ≤ m i n) : ∀ i n, n ≤ iteratedIndex m i n
  | 0, _n => le_rfl
  | i + 1, n => (iteratedIndex_le m hm i n).trans (hm i _)

/-- The lift of `op n` into the index category of a lifted inverse sequence. -/
public abbrev liftedIndexObj (n : ℕ) : ULiftHom.{v} (ULift.{v} ℕᵒᵖ) :=
  ULiftHom.objUp (ULift.up (op n))

/-- The transition `liftedIndexObj m ⟶ liftedIndexObj n` attached to `n ≤ m`. -/
public abbrev liftedIndexHom {n m : ℕ} (h : n ≤ m) :
    liftedIndexObj m ⟶ liftedIndexObj n :=
  ⟨⟨⟨PLift.up h⟩⟩⟩

private abbrev liftedIndexCategory := (ULiftHom.{v} (ULift.{v} ℕᵒᵖ))ᵒᵖ

private def liftIndexFunctor : ℕ ⥤ liftedIndexCategory where
  obj n := op (liftedIndexObj n)
  map f := (liftedIndexHom (leOfHom f)).op
  map_id _ := rfl
  map_comp _ _ := rfl

private lemma liftIndexFunctor_final : liftIndexFunctor.Final :=
  Functor.final_of_exists_of_isFiltered _ (fun ⟨⟨⟨n⟩⟩⟩ => ⟨n, ⟨𝟙 _⟩⟩)
    fun {_ c} s s' => ⟨c, 𝟙 _, by cases s; cases s'; rfl⟩

private def natReindex (r : ℕ → ℕ) (hr : Monotone r) : ℕ ⥤ ℕ where
  obj n := r n
  map f := homOfLE (hr (leOfHom f))
  map_id _ := rfl
  map_comp _ _ := rfl

private lemma natReindex_final (r : ℕ → ℕ) (hr : Monotone r)
    (hle : ∀ n, n ≤ r n) : (natReindex r hr).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun n => ⟨n, ⟨homOfLE (hle n)⟩⟩)
    fun {_ c} _ _ => ⟨c, 𝟙 _, Subsingleton.elim _ _⟩

private def diagonalFunctor : ℕ ⥤ ℕ × ℕ where
  obj n := (n, n)
  map f := (f, f)
  map_id _ := rfl
  map_comp _ _ := rfl

private lemma diagonalFunctor_final : diagonalFunctor.Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro d
    exact ⟨max d.1 d.2,
      ⟨homOfLE (le_max_left _ _), homOfLE (le_max_right _ _)⟩⟩
  · intro d c s s'
    refine ⟨c, 𝟙 _, ?_⟩
    ext <;> apply Subsingleton.elim

private noncomputable def coyonedaColimLiftIso {C : Type u} [Category.{v} C]
    (M : ℕᵒᵖ ⥤ C) :
    colimit (liftIndexFunctor ⋙ (liftedInverseSequence M).op ⋙ coyoneda) ≅
      Pro.coyonedaColim (liftedInverseSequence M) := by
  letI : liftIndexFunctor.Final := liftIndexFunctor_final
  exact Functor.Final.colimitIso liftIndexFunctor
    ((liftedInverseSequence M).op ⋙ coyoneda)

private noncomputable abbrev stageClass {C : Type u} [Category.{v} C]
    (M : ℕᵒᵖ ⥤ C) {X : C} {n : ℕ} (f : M.obj (op n) ⟶ X) :
    (Pro.coyonedaColim (liftedInverseSequence M)).obj X :=
  (colimit.ι ((liftedInverseSequence M).op ⋙ coyoneda) (op (liftedIndexObj n))).app X f

private lemma stageClass_postcomp {C : Type u} [Category.{v} C]
    (M : ℕᵒᵖ ⥤ C) {X Y : C} {n : ℕ}
    (f : M.obj (op n) ⟶ X) (g : X ⟶ Y) :
    (Pro.coyonedaColim (liftedInverseSequence M)).map g (stageClass M f) =
      stageClass M (f ≫ g) :=
  (ConcreteCategory.congr_hom
    ((colimit.ι ((liftedInverseSequence M).op ⋙ coyoneda)
      (op (liftedIndexObj n))).naturality g) f).symm

private lemma stageClass_transition {C : Type u} [Category.{v} C]
    (M : ℕᵒᵖ ⥤ C) {X : C} {n m : ℕ} (h : n ≤ m)
    (f : M.obj (op n) ⟶ X) :
    stageClass M ((M.map (homOfLE h).op) ≫ f) = stageClass M f := by
  have he := congrArg (fun t => t.app X)
    (colimit.w ((liftedInverseSequence M).op ⋙ coyoneda) (liftedIndexHom h).op)
  exact ConcreteCategory.congr_hom he f

private lemma stageClass_surjective {C : Type u} [Category.{v} C]
    (M : ℕᵒᵖ ⥤ C) (X : C)
    (x : (Pro.coyonedaColim (liftedInverseSequence M)).obj X) :
    ∃ (n : ℕ) (f : M.obj (op n) ⟶ X), x = stageClass M f := by
  obtain ⟨j, f, h⟩ := FunctorToTypes.jointly_surjective'
    ((liftedInverseSequence M).op ⋙ coyoneda) X x
  rcases j with ⟨⟨⟨n⟩⟩⟩
  exact ⟨n, f, h⟩

private lemma stageClass_eq {C : Type u} [Category.{v} C]
    (M : ℕᵒᵖ ⥤ C) {X : C} {n m : ℕ}
    (f : M.obj (op n) ⟶ X) (g : M.obj (op m) ⟶ X)
    (h : stageClass M f = stageClass M g) :
    ∃ (k : ℕ) (hn : n ≤ k) (hm : m ≤ k),
      M.map (homOfLE hn).op ≫ f = M.map (homOfLE hm).op ≫ g := by
  let S := liftedInverseSequence M
  let F := (S.op ⋙ coyoneda) ⋙ (evaluation _ _).obj X
  let E := colimitObjIsoColimitCompEvaluation (S.op ⋙ coyoneda) X
  have he :
      colimit.ι F (op (liftedIndexObj n)) f =
      colimit.ι F (op (liftedIndexObj m)) g := by
    have hh :
        (((colimit.ι (S.op ⋙ coyoneda) (op (liftedIndexObj n))).app X) ≫ E.hom) f =
        (((colimit.ι (S.op ⋙ coyoneda) (op (liftedIndexObj m))).app X) ≫ E.hom) g :=
      congrArg E.hom h
    simpa only [E, colimitObjIsoColimitCompEvaluation_ι_app_hom] using hh
  obtain ⟨j, a, b, hab⟩ :=
    (Limits.Types.FilteredColimit.colimit_eq_iff F).mp he
  let hn := leOfHom a.unop.down.unop
  let hm := leOfHom b.unop.down.unop
  refine ⟨j.unop.objDown.down.unop, hn, hm, ?_⟩
  have hmap {x y : ℕᵒᵖ} (t : x ⟶ y) : M.map t = M.map (homOfLE (leOfHom t.unop)).op := by
    congr 1
  change S.map a.unop ≫ f = S.map b.unop ≫ g at hab
  rwa [show S.map a.unop = _ from hmap a.unop.down,
    show S.map b.unop = _ from hmap b.unop.down] at hab

private lemma transformation_stage {C : Type u} [Category.{v} C]
    {A B : ℕᵒᵖ ⥤ C} (φ : Pro.coyonedaColim (liftedInverseSequence A) ⟶
      Pro.coyonedaColim (liftedInverseSequence B)) {n m : ℕ}
    (f : B.obj (op m) ⟶ A.obj (op n))
    (h : φ.app (A.obj (op n)) (stageClass A (𝟙 _)) = stageClass B f)
    {X : C} (g : A.obj (op n) ⟶ X) :
    φ.app X (stageClass A g) = stageClass B (f ≫ g) := by
  have hn := ConcreteCategory.congr_hom (φ.naturality g) (stageClass A (𝟙 _))
  dsimp at hn
  rwa [stageClass_postcomp, Category.id_comp, h, stageClass_postcomp] at hn

private lemma map_comp_le {C : Type u} [Category.{v} C]
    (M : ℕᵒᵖ ⥤ C) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    M.map (homOfLE hjk).op ≫ M.map (homOfLE hij).op =
      M.map (homOfLE (hij.trans hjk)).op := by
  rw [← Functor.map_comp]
  congr 1

private lemma exists_levelwiseRepresentative {C : Type u} [Category.{v} C]
    (A B : ℕᵒᵖ ⥤ C)
    (φ : Pro.coyonedaColim (liftedInverseSequence A) ⟶
      Pro.coyonedaColim (liftedInverseSequence B)) :
    ∃ (m : ℕ → ℕ) (hm : StrictMono m) (_hm' : ∀ n, n ≤ m n)
      (f : ∀ n, B.obj (op (m n)) ⟶ A.obj (op n)),
      (∀ {n n'} (h : n ≤ n'),
        B.map (homOfLE (hm.monotone h)).op ≫ f n =
          f n' ≫ A.map (homOfLE h).op) ∧
      (∀ n, φ.app (A.obj (op n)) (stageClass A (𝟙 _)) = stageClass B (f n)) := by
  have hs (n : ℕ) := stageClass_surjective B (A.obj (op n))
    (φ.app (A.obj (op n)) (stageClass A (𝟙 _)))
  choose p f hf using hs
  have hc (n : ℕ) : stageClass B (f n) =
      stageClass B (f (n + 1) ≫ A.map (homOfLE (Nat.le_succ n)).op) := by
    rw [← hf n, ← transformation_stage φ (f (n + 1)) (hf (n + 1))
      (A.map (homOfLE (Nat.le_succ n)).op)]
    congr 1
    simpa only [Category.comp_id] using
      (stageClass_transition A (Nat.le_succ n) (𝟙 _)).symm
  choose k hk hk' heq using fun n => stageClass_eq B (f n)
    (f (n + 1) ≫ A.map (homOfLE (Nat.le_succ n)).op) (hc n)
  obtain ⟨m, hm, hb⟩ :=
    StacksDraft.InverseSystem.exists_strict_majorant fun n => max n (max (p n) (k n))
  have hle (n : ℕ) : n ≤ m n ∧ p n ≤ m n ∧ k n ≤ m n := by simpa only [max_le_iff] using hb n
  choose hn hp hkn using hle
  have hmMono : Monotone m := hm.monotone
  let g (n : ℕ) : B.obj (op (m n)) ⟶ A.obj (op n) :=
    B.map (homOfLE (hp n)).op ≫ f n
  have hnat (n : ℕ) :
      B.map (homOfLE (hmMono (Nat.le_succ n))).op ≫ g n =
        g (n + 1) ≫ A.map (homOfLE (Nat.le_succ n)).op := by
    have hmn : m n ≤ m (n + 1) := hmMono (Nat.le_succ n)
    have hkm : k n ≤ m (n + 1) := (hkn n).trans hmn
    have he := congrArg (fun z => B.map (homOfLE hkm).op ≫ z) (heq n)
    rw [← Category.assoc, map_comp_le B (hk n) hkm, ← Category.assoc,
      map_comp_le B (hk' n) hkm] at he
    dsimp [g]
    rw [← Category.assoc, map_comp_le B (hp n) hmn]
    simpa only [Category.assoc] using he
  refine ⟨m, hm, hn, g, ?_, ?_⟩
  · intro n n' h
    induction n', h using Nat.le_induction with
    | base => simp [g]
    | succ n' h ih =>
      rw [← map_comp_le B (hmMono h) (hmMono (Nat.le_succ n')),
        Category.assoc, ih, ← Category.assoc, hnat n', Category.assoc,
        map_comp_le A h (Nat.le_succ n')]
  · intro n
    exact (hf n).trans (stageClass_transition B (hp n) (f n)).symm

private structure LevelwiseRepresentative {C : Type u} [Category.{v} C]
    (A B : ℕᵒᵖ ⥤ C)
    (φ : Pro.coyonedaColim (liftedInverseSequence A) ⟶
      Pro.coyonedaColim (liftedInverseSequence B)) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  index_le : ∀ n, n ≤ index n
  component : ∀ n, B.obj (op (index n)) ⟶ A.obj (op n)
  naturality : ∀ {n n'} (h : n ≤ n'),
    B.map (homOfLE (index_strict.monotone h)).op ≫ component n =
      component n' ≫ A.map (homOfLE h).op
  represents : ∀ n, φ.app (A.obj (op n)) (stageClass A (𝟙 _)) =
    stageClass B (component n)

private noncomputable def chooseLevelwiseRepresentative {C : Type u} [Category.{v} C]
    (A B : ℕᵒᵖ ⥤ C)
    (φ : Pro.coyonedaColim (liftedInverseSequence A) ⟶
      Pro.coyonedaColim (liftedInverseSequence B)) :
    LevelwiseRepresentative A B φ := by
  classical
  let h0 := exists_levelwiseRepresentative A B φ
  let m := Classical.choose h0
  let h1 := Classical.choose_spec h0
  let hm := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let hm' := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let f := Classical.choose h3
  let h4 := Classical.choose_spec h3
  exact ⟨m, hm, hm', f, h4.1, h4.2⟩

private lemma LevelwiseRepresentative.ι_comp {C : Type u} [Category.{v} C] {A B : ℕᵒᵖ ⥤ C}
    {φ : Pro.coyonedaColim (liftedInverseSequence A) ⟶
      Pro.coyonedaColim (liftedInverseSequence B)}
    (R : LevelwiseRepresentative A B φ) (n : ℕ) :
    colimit.ι ((liftedInverseSequence A).op ⋙ coyoneda) (op (liftedIndexObj n)) ≫ φ =
      coyoneda.map (R.component n).op ≫
        colimit.ι ((liftedInverseSequence B).op ⋙ coyoneda) (op (liftedIndexObj (R.index n))) := by
  ext X g
  exact transformation_stage φ (R.component n) (R.represents n) g

private abbrev rowIndex {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (i n : ℕ) : ℕ :=
  iteratedIndex (fun j => (R j).index) i n

private lemma rowIndex_monotone {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (i : ℕ) : Monotone (rowIndex R i) :=
  iteratedIndex_monotone _ (fun j => (R j).index_strict.monotone) i

private def diagStep {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (k : ℕ) :
    (M (k + 1)).obj (op ((R k).index (rowIndex R k (k + 1)))) ⟶
      (M k).obj (op (rowIndex R k k)) :=
  (M (k + 1)).map (homOfLE ((R k).index_strict.monotone
    (rowIndex_monotone R k (Nat.le_succ k)))).op ≫ (R k).component (rowIndex R k k)

private def diagSystem {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i)) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun k => (M k).obj (op (rowIndex R k k))) (diagStep R)

private lemma diagSystem_map_succ {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (k : ℕ) :
    (diagSystem R).map (homOfLE (Nat.le_succ k)).op = diagStep R k :=
  Functor.ofOpSequence_map_homOfLE_succ _ k

private def rowReindex {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (i : ℕ) : ℕ ⥤ liftedIndexCategory.{v} :=
  natReindex (rowIndex R i) (rowIndex_monotone R i) ⋙ liftIndexFunctor

private def rowFunctor {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (i : ℕ) : ℕ ⥤ C ⥤ Type v :=
  rowReindex R i ⋙ (liftedInverseSequence (M i)).op ⋙ coyoneda

private lemma rowReindex_final {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (i : ℕ) : (rowReindex R i).Final := by
  have := natReindex_final (rowIndex R i) (rowIndex_monotone R i)
    (iteratedIndex_le _ (fun j x => (R j).index_le x) i)
  have : liftIndexFunctor.{v}.Final := liftIndexFunctor_final
  unfold rowReindex
  infer_instance

private def rowTransition {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (i : ℕ) : rowFunctor R i ⟶ rowFunctor R (i + 1) where
  app n := coyoneda.map ((R i).component (rowIndex R i n)).op
  naturality n n' g := by
    have h := (R i).naturality (rowIndex_monotone R i (leOfHom g))
    change coyoneda.map ((M i).map (homOfLE (rowIndex_monotone R i (leOfHom g))).op).op ≫
        coyoneda.map ((R i).component (rowIndex R i n')).op =
      coyoneda.map ((R i).component (rowIndex R i n)).op ≫
        coyoneda.map ((M (i + 1)).map (homOfLE
          ((R i).index_strict.monotone (rowIndex_monotone R i (leOfHom g)))).op).op
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, h]

private noncomputable def rowColimitIso {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (i : ℕ) :
    colimit (rowFunctor R i) ≅ Pro.coyonedaColim (liftedInverseSequence (M i)) :=
  haveI := rowReindex_final R i
  (colimit.isColimit (rowFunctor R i)).coconePointUniqueUpToIso
    ((Functor.Final.isColimitWhiskerEquiv (rowReindex R i)
      (colimit.cocone ((liftedInverseSequence (M i)).op ⋙ coyoneda))).symm
      (colimit.isColimit _))

@[reassoc]
private lemma ι_rowColimitIso_hom {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (i n : ℕ) :
    colimit.ι (rowFunctor R i) n ≫ (rowColimitIso R i).hom =
      colimit.ι ((liftedInverseSequence (M i)).op ⋙ coyoneda) ((rowReindex R i).obj n) := by
  have := rowReindex_final R i
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n

private lemma rowColimitIso_hom_comp {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (i : ℕ) :
    (rowColimitIso R i).hom ≫ φ i =
      colimMap (rowTransition R i) ≫ (rowColimitIso R (i + 1)).hom := by
  refine colimit.hom_ext fun n => ?_
  rw [ι_rowColimitIso_hom_assoc, ι_colimMap_assoc, ι_rowColimitIso_hom]
  exact (R i).ι_comp (rowIndex R i n)

private lemma diagonal_map_succ {C : Type u} [Category.{v} C] {M : ℕ → ℕᵒᵖ ⥤ C}
    {φ : ∀ i, Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1)))}
    (R : ∀ i, LevelwiseRepresentative (M i) (M (i + 1)) (φ i))
    (k : ℕ) :
    (diagonalFunctor ⋙ Functor.uncurry.obj (Functor.ofSequence (rowTransition R))).map
        (homOfLE (Nat.le_succ k)) =
      (liftIndexFunctor ⋙ (liftedInverseSequence (diagSystem R)).op ⋙ coyoneda).map
        (homOfLE (Nat.le_succ k)) := by
  show ((Functor.ofSequence (rowTransition R)).map (homOfLE (Nat.le_succ k))).app k ≫
      ((Functor.ofSequence (rowTransition R)).obj (k + 1)).map (homOfLE (Nat.le_succ k)) =
    coyoneda.map ((diagSystem R).map (homOfLE (Nat.le_succ k)).op).op
  rw [diagSystem_map_succ, Functor.ofSequence_map_homOfLE_succ]
  exact (coyoneda.map_comp ((R k).component (rowIndex R k k)).op
    ((M (k + 1)).map (homOfLE ((R k).index_strict.monotone
      (rowIndex_monotone R k (Nat.le_succ k)))).op).op).symm

/-- A diagonal inverse sequence representing the colimit of a sequence `P` of
countably represented pro-objects.  The fields `reindex` and `component` are
the increasing reindexings and compatible maps representing the successive
pro-morphisms.  The isomorphisms `objIso` record the stated diagonal formula;
`comparison` is the natural form of the two displayed colimit equalities in
Stacks 0G53. -/
public structure DiagonalRepresentation {C : Type u} [Category.{v} C]
    (P : Functor ℕ (Functor C (Type v))) (M : ℕ → Functor ℕᵒᵖ C)
    (e : ∀ i, P.obj i ≅ Pro.coyonedaColim (liftedInverseSequence (M i))) where
  /-- The reindexing which represents the transition from row `i + 1` to row
  `i`. -/
  reindex : ℕ → ℕ → ℕ
  /-- Every reindexing is increasing. -/
  reindex_monotone : ∀ i, Monotone (reindex i)
  /-- Reindexings may be chosen to increase every index. -/
  le_reindex : ∀ i n, n ≤ reindex i n
  /-- A levelwise representative of each transition pro-morphism. -/
  component : ∀ i n,
    (M (i + 1)).obj (op (reindex i n)) ⟶ (M i).obj (op n)
  /-- The levelwise representatives commute with the transition maps in the
  rows. -/
  component_naturality : ∀ i {n n' : ℕ} (h : n ≤ n'),
    (M (i + 1)).map (homOfLE (reindex_monotone i h)).op ≫ component i n =
      component i n' ≫ (M i).map (homOfLE h).op
  /-- The levelwise maps represent the given transition of `P`. -/
  represents_transition : ∀ i n,
    colimit.ι ((liftedInverseSequence (M i)).op ⋙ coyoneda)
        (op (ULiftHom.objUp (ULift.up (op n)))) ≫ (e i).inv ≫
        P.map (homOfLE (Nat.le_succ i)) ≫ (e (i + 1)).hom =
      coyoneda.map (component i n).op ≫
        colimit.ι ((liftedInverseSequence (M (i + 1))).op ⋙ coyoneda)
          (op (ULiftHom.objUp (ULift.up (op (reindex i n)))))
  /-- The resulting inverse sequence. -/
  system : Functor ℕᵒᵖ C
  /-- Its `k`-th term is the term prescribed by the iterated reindexings. -/
  objIso : ∀ k, system.obj (op k) ≅
    (M k).obj (op (iteratedIndex reindex k k))
  /-- The transition maps of `system` are the diagonal transitions induced by
  the chosen levelwise representatives. -/
  map_objIso : ∀ k,
    (objIso (k + 1)).hom ≫
        (M (k + 1)).map
          (homOfLE (reindex_monotone k
            (iteratedIndex_monotone reindex reindex_monotone k (Nat.le_succ k)))).op ≫
        component k (iteratedIndex reindex k k) =
      system.map (homOfLE (Nat.le_succ k)).op ≫ (objIso k).hom
  /-- Naturally in `N`, the iterated colimit of `Hom(M_{i,n}, N)` is the
  colimit of `Hom(system_k, N)`. -/
  comparison : colimit P ≅
    Pro.coyonedaColim (liftedInverseSequence system)

/-- **Stacks Project, Tag 0G53 (diagonal representation).** A countable inverse
system of pro-objects, each represented by an inverse sequence, has a diagonal
inverse-sequence representation.  Equivalently, naturally in `N`,
`colim_i colim_n Hom(M_{i,n}, N)` is `colim_k Hom(D_k, N)`. -/
@[stacks 0G53 "diagonal_representation"]
public theorem exists_diagonalRepresentation {C : Type u} [Category.{v} C]
    (P : Functor ℕ (Functor C (Type v))) (M : ℕ → Functor ℕᵒᵖ C)
    (e : ∀ i, P.obj i ≅ Pro.coyonedaColim (liftedInverseSequence (M i))) :
    Nonempty (DiagonalRepresentation P M e) := by
  let φ (i : ℕ) : Pro.coyonedaColim (liftedInverseSequence (M i)) ⟶
      Pro.coyonedaColim (liftedInverseSequence (M (i + 1))) :=
    (e i).inv ≫ P.map (homOfLE (Nat.le_succ i)) ≫ (e (i + 1)).hom
  let R (i : ℕ) := chooseLevelwiseRepresentative (M i) (M (i + 1)) (φ i)
  let T := Functor.ofSequence (rowTransition R)
  let Q := T ⋙ colim
  let u (i : ℕ) : Q.obj i ≅ Pro.coyonedaColim (liftedInverseSequence (M i)) :=
    rowColimitIso R i
  have hQsucc (i : ℕ) : Q.map (homOfLE (Nat.le_succ i)) = colimMap (rowTransition R i) :=
    congrArg colimMap (Functor.ofSequence_map_homOfLE_succ (rowTransition R) i)
  have hsquare (i : ℕ) :
      φ i ≫ (u (i + 1)).inv = (u i).inv ≫ Q.map (homOfLE (Nat.le_succ i)) := by
    apply (cancel_epi (u i).hom).1
    apply (cancel_mono (u (i + 1)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc]
    rw [hQsucc]
    exact rowColimitIso_hom_comp R i
  let b (i : ℕ) : P.obj i ≅ Q.obj i := e i ≪≫ (u i).symm
  have hsucc (i : ℕ) :
      P.map (homOfLE (Nat.le_succ i)) ≫ (b (i + 1)).hom =
        (b i).hom ≫ Q.map (homOfLE (Nat.le_succ i)) := by
    dsimp [b]
    rw [Category.assoc, ← hsquare]
    simp [φ]
  let bNatIso : P ≅ Q := NatIso.ofComponents b fun f =>
    (NatTrans.ofSequence (F := P) (G := Q) (fun i => (b i).hom) hsucc).naturality f
  let K := diagonalFunctor ⋙ Functor.uncurry.obj T
  let U := liftIndexFunctor ⋙ (liftedInverseSequence (diagSystem R)).op ⋙ coyoneda
  let diagNatIso : K ≅ U := NatIso.ofComponents (fun _ => Iso.refl _) fun f =>
    (NatTrans.ofSequence (F := K) (G := U) (fun _ => 𝟙 _) fun k =>
      (Category.comp_id _).trans
        ((diagonal_map_succ R k).trans (Category.id_comp _).symm)).naturality f
  refine ⟨{
    reindex i := (R i).index
    reindex_monotone i := (R i).index_strict.monotone
    le_reindex i := (R i).index_le
    component i := (R i).component
    component_naturality i := (R i).naturality
    represents_transition i := (R i).ι_comp
    system := diagSystem R
    objIso _ := Iso.refl _
    map_objIso k := by
      rw [diagSystem_map_succ]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    comparison := ?_ }⟩
  have : diagonalFunctor.Final := diagonalFunctor_final
  exact HasColimit.isoOfNatIso bNatIso ≪≫ (colimitUncurryIsoColimitCompColim T).symm ≪≫
    (Functor.Final.colimitIso diagonalFunctor (Functor.uncurry.obj T)).symm ≪≫
    HasColimit.isoOfNatIso diagNatIso ≪≫ coyonedaColimLiftIso (diagSystem R)

end CategoryTheory.Pro
