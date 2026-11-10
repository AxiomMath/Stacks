module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Cosimplicial
public import StacksCore.Tactic.StacksAttribute

/-!
# The Čech conerve of an arrow, and the split case

For an arrow `f` in a category admitting the iterated pushouts of `f` along itself, the Čech
conerve `f.cechConerve` is the cosimplicial object whose value in degree `n` is the `(n+1)`-fold
pushout of `f`. This file proves that when `f` admits a retraction its Čech conerve is homotopy
equivalent to the constant cosimplicial object on its source.

For a commutative ring map `R → A` with a section this is the statement that the Čech
cosimplicial `R`-algebra `(A/R)•` is homotopy equivalent to the constant cosimplicial algebra
`R`.

## Main definitions

* `CategoryTheory.Arrow.cechSectionMap` is the map to the constant cosimplicial object on the
  source determined by a retraction of `f`.

## Main results

* `CategoryTheory.Arrow.cechConerve_homotopyEquivalent_const_of_section` gives the homotopy
  equivalence for any arrow with the required iterated pushouts.

## Implementation notes

The homotopy equivalence is stated in an arbitrary category with the relevant Čech pushouts,
rather than only in commutative `R`-algebras. Cosimplicial homotopy equivalence is expressed
using the simplicial homotopy equivalence of the opposite objects.

## References

* [Stacks Project, Tag 039Y](https://stacks.math.columbia.edu/tag/039Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Arrow

section SplitCechMaps

variable {C : Type u} [Category.{v} C] {f : Arrow C}
  [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]

/-- The degree-`n` component of the map to the constant cosimplicial object determined by a
retraction of `f`. -/
noncomputable def cechSectionComponent (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left) (n : SimplexCategory) :
    f.cechConerve.obj n ⟶ f.left :=
  WidePushout.desc (arrows := cechLegs f n) (𝟙 f.left) (fun _ => s) (fun _ => hs)

/-- The component `cechSectionComponent s hs n` restricts to the retraction `s` on each
coprojection `cechι n i`. -/
lemma cechι_comp_sectionComponent (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    cechι n i ≫ cechSectionComponent s hs n = s :=
  WidePushout.ι_desc (cechLegs f n) _ _ _ i

/-- The map from the Čech conerve to the constant cosimplicial object on the source determined
by a retraction of `f`. -/
noncomputable def cechSectionMap (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left) :
    f.cechConerve ⟶ (CosimplicialObject.const C).obj f.left where
  app n := cechSectionComponent s hs n
  naturality := by
    intro n m g
    apply cech_hom_ext
    intro i
    rw [← Category.assoc, cechι_comp_map (f := f) g i,
      cechι_comp_sectionComponent (f := f) s hs m (g.toOrderHom i),
      ← Category.assoc, cechι_comp_sectionComponent (f := f) s hs n i]
    simp

/-- The endomorphism of `f` given by a retraction followed by `f` itself. -/
def cechRetractionEndomorphism (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left) : f ⟶ f :=
  Arrow.homMk (𝟙 f.left) (s ≫ f.hom) (by
    simp [← Category.assoc, hs])

/-- The augmentation of the Čech conerve followed by `cechSectionMap s hs` is the identity of
the constant cosimplicial object on the source. -/
lemma cechAugmentation_section_comp (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left) :
    f.augmentedCechConerve.hom ≫ cechSectionMap s hs = 𝟙 _ := by
  ext n
  change cechHead n ≫ cechSectionComponent s hs n = 𝟙 f.left
  exact WidePushout.head_desc (cechLegs f n) _ _ _

/-- `cechSectionMap s hs` followed by the augmentation of the Čech conerve is the map of Čech
conerves induced by `cechRetractionEndomorphism s hs`. -/
lemma cechSection_augmentation_comp (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left) :
    cechSectionMap s hs ≫ f.augmentedCechConerve.hom =
      Arrow.mapCechConerve (cechRetractionEndomorphism s hs) := by
  ext n
  apply cech_hom_ext
  intro i
  change cechι n i ≫ (cechSectionComponent s hs n ≫ cechHead n) =
    cechι n i ≫ (Arrow.mapCechConerve (cechRetractionEndomorphism s hs)).app n
  rw [← Category.assoc, cechι_comp_sectionComponent (f := f) s hs n i,
    cechι_comp_mapCechConerve, ← hom_comp_cechι (f := f) n i]
  change s ≫ (f.hom ≫ cechι n i) = (s ≫ f.hom) ≫ cechι n i
  exact (Category.assoc _ _ _).symm

end SplitCechMaps

/-- A split Čech conerve is homotopy equivalent to the constant cosimplicial object on the base.
For commutative `R`-algebras this is the split Čech algebra `(A/R)•` and the constant algebra
`R`. -/
@[stacks 039Y "split_cech_homotopy"]
theorem cechConerve_homotopyEquivalent_const_of_section
    {C : Type u} [Category.{v} C] (f : Arrow C)
    [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]
    (h : ∃ s : f.right ⟶ f.left, f.hom ≫ s = 𝟙 f.left) :
    ∃ a : f.cechConerve.op ⟶ ((CosimplicialObject.const C).obj f.left).op,
      SimplicialObject.homotopyEquivalences Cᵒᵖ a := by
  obtain ⟨s, hs⟩ := h
  let i := f.augmentedCechConerve.hom
  let r := cechSectionMap (f := f) s hs
  let F := cechRetractionEndomorphism (f := f) s hs
  refine ⟨NatTrans.op i, ?_⟩
  change ∃ b : ((CosimplicialObject.const C).obj f.left).op ⟶ f.cechConerve.op, _
  refine ⟨NatTrans.op r, ?_, ?_⟩
  · change Relation.EqvGen _ (NatTrans.op (r ≫ i)) (𝟙 _)
    rw [cechSection_augmentation_comp (f := f) s hs]
    apply Relation.EqvGen.rel
    exact (CosimplicialObject.exists_homotopy_iff_nonempty_homotopy_op
      (Arrow.mapCechConerve F) (𝟙 f.cechConerve)).mp
        (Arrow.exists_homotopy_mapCechConerve_id F
          (by simp [F, cechRetractionEndomorphism]))
  · change Relation.EqvGen _ (NatTrans.op (i ≫ r)) (𝟙 _)
    rw [cechAugmentation_section_comp (f := f) s hs]
    exact Relation.EqvGen.refl _

end CategoryTheory.Arrow
