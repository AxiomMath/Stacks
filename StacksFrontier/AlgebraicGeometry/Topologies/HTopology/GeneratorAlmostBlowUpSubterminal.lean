module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpInduction
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpReduction
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSheafCriterion
public import StacksFrontier.CategoryTheory.Sites.SubsingletonPresheaf

/-!
# The h sheaf criterion of Stacks 0EVI, and its form for a subterminal presheaf

The sufficiency direction of Stacks 0EVI is available in this development without hypotheses:
`AlgebraicGeometry.affineAlmostBlowUpHSheafCriterion` proves the sufficiency direction of Stacks
0EVF and `AlgebraicGeometry.generatorAlmostBlowUpSquaresSuffice` proves the reduction of its
condition (3) to the two shapes of Examples 0EVG and 0EVH.  Composing them,
`AlgebraicGeometry.BigHOver.isSheaf_of_generatorSquares` below is the criterion itself: a presheaf
of sets on the big h category over `S` satisfying conditions (1) to (4) of Stacks 0EVI is a sheaf
for the h topology.

The rest of the file specialises that criterion to a presheaf all of whose values are
subsingletons.  For such a presheaf a family of elements carries no data — compatibility is
automatic and an amalgamation is unique as soon as it exists — so each of the four conditions
collapses to an implication between *nonemptiness* statements:

1. a section over each member of a Zariski covering family gives a section over its target;
2. a section over the source of a flat proper surjection of finite presentation onto an affine
   object gives a section over the target;
3. and 4. a section over the centre and a section over the modification of an almost blowup square
   of the shape of Example 0EVG, resp. 0EVH, give a section over its base.

This is the form in which a criterion for *categories* fibred in groupoids consumes Stacks 0EVI:
the statements that have to be descended along an h covering — that two morphisms of a fibre
agree, that a compatible family of local isomorphisms is induced by a global one, that a descent
datum is effective — are propositions, and the presheaf of their truth values over the slice site
is subterminal.

## Main results

* `AlgebraicGeometry.BigHOver.isSheaf_of_generatorSquares`: **the sufficiency direction of Stacks
  0EVI**, with no hypothesis carried.
* `AlgebraicGeometry.BigHOver.isZariskiSheaf_of_nonempty`,
  `AlgebraicGeometry.BigHOver.isAffineFlatProperFinitePresentationSheaf_of_nonempty`,
  `AlgebraicGeometry.BigHOver.isOneGeneratorAlmostBlowUpSheaf_of_nonempty` and
  `AlgebraicGeometry.BigHOver.isTwoGeneratorAlmostBlowUpSheaf_of_nonempty`: the four conditions of
  Stacks 0EVI for a subterminal presheaf, read as nonemptiness implications.
* `AlgebraicGeometry.BigHOver.nonempty_of_isSheaf_of_covering`: the conclusion in the form it is
  used — a section exists over the target of a covering family as soon as one exists over each
  member.

## References

* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-- **Stacks 0EVI, sufficiency.** A presheaf of sets on the big h category over `S` which is a
Zariski sheaf, which satisfies the sheaf condition for a flat proper surjection of finite
presentation onto an affine object, and which sends the almost blowup squares of the shapes of
Examples 0EVG and 0EVH to cartesian squares of sets, is a sheaf for the h topology.

This composes the two halves of the source's proof, both of which are available here: the
sufficiency direction of Stacks 0EVF, `AlgebraicGeometry.affineAlmostBlowUpHSheafCriterion`, and
the reduction of its condition (3) to the two shapes,
`AlgebraicGeometry.generatorAlmostBlowUpSquaresSuffice`. -/
public theorem isSheaf_of_generatorSquares
    (hzar : IsZariskiSheaf B S hS F)
    (haff : IsAffineFlatProperFinitePresentationSheaf B S hS F)
    (h1 : IsOneGeneratorAlmostBlowUpSheaf B S hS F)
    (h2 : IsTwoGeneratorAlmostBlowUpSheaf B S hS F) :
    Presheaf.IsSheaf (BigHOver.topology B S hS) F :=
  affineAlmostBlowUpHSheafCriterion.{u, v} B S hS F hzar haff
    (generatorAlmostBlowUpSquaresSuffice.{u, v} B S hS F hzar haff h1 h2)

/-! ### The four conditions for a subterminal presheaf -/

variable [hsub : ∀ X : (BigHOver B S hS)ᵒᵖ, Subsingleton (F.obj X)]

/-- A commutative square of subsingletons is cartesian as soon as its corner is inhabited
whenever both of its sides are. -/
public theorem isPullback_of_subsingleton_of_nonempty {P X Y Z : Type v}
    [Subsingleton P] [Subsingleton X] [Subsingleton Y] [Subsingleton Z]
    (t : P ⟶ X) (l : P ⟶ Y) (r : X ⟶ Z) (b : Y ⟶ Z)
    (h : Nonempty X → Nonempty Y → Nonempty P) : IsPullback t l r b := by
  rw [Types.isPullback_iff]
  refine ⟨?_, fun _ _ _ ↦ Subsingleton.elim _ _, ?_⟩
  · ext x
    exact Subsingleton.elim _ _
  intro x₂ x₃ _
  obtain ⟨a⟩ := h ⟨x₂⟩ ⟨x₃⟩
  exact ⟨a, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Condition (1) of Stacks 0EVI for a subterminal presheaf. -/
public theorem isZariskiSheaf_of_nonempty
    (h : ∀ (X : BigHOver B S hS) (E : PreZeroHypercover.{u + 1} X),
      (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
        Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X) →
      (∀ i, Nonempty (F.obj (op (E.X i)))) → Nonempty (F.obj (op X))) :
    IsZariskiSheaf B S hS F := by
  intro X E hE
  rw [Presieve.isSheafFor_iff_nonempty_of_subsingleton]
  intro hne
  exact h X E hE fun i ↦ hne (E.f i) (Presieve.ofArrows.mk i)

/-- Condition (2) of Stacks 0EVI for a subterminal presheaf. -/
public theorem isAffineFlatProperFinitePresentationSheaf_of_nonempty
    (h : ∀ (X Y : BigHOver B S hS) (f : Y ⟶ X),
      IsAffine ((BigHOver.toScheme B S hS).obj X) →
      Flat ((BigHOver.toScheme B S hS).map f) →
      IsProper ((BigHOver.toScheme B S hS).map f) →
      Surjective ((BigHOver.toScheme B S hS).map f) →
      FinitePresentation ((BigHOver.toScheme B S hS).map f) →
      Nonempty (F.obj (op Y)) → Nonempty (F.obj (op X))) :
    IsAffineFlatProperFinitePresentationSheaf B S hS F := by
  intro X Y f hX hflat hproper hsurj hfp
  rw [Presieve.isSheafFor_iff_nonempty_of_subsingleton]
  intro hne
  exact h X Y f hX hflat hproper hsurj hfp (hne f (Presieve.singleton_self f))

/-- Condition (3) of Stacks 0EVI for a subterminal presheaf. -/
public theorem isOneGeneratorAlmostBlowUpSheaf_of_nonempty
    (h : ∀ (X X' Z E : BigHOver B S hS) (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
        (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData),
      IsAffine ((BigHOver.toScheme B S hS).obj X) →
      IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b) →
      Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι) →
      IsPullback
        ((BigHOver.toScheme B S hS).map e) ((BigHOver.toScheme B S hS).map q)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map b) →
      IsOneGeneratorAlmostBlowUpModel
        ((BigHOver.toScheme B S hS).map b) ((BigHOver.toScheme B S hS).map z) →
      Nonempty (F.obj (op Z)) → Nonempty (F.obj (op X')) → Nonempty (F.obj (op X))) :
    IsOneGeneratorAlmostBlowUpSheaf B S hS F := fun X X' Z E b z q e I hX hb hZ hsq hmod ↦
  isPullback_of_subsingleton_of_nonempty _ _ _ _ (h X X' Z E b z q e I hX hb hZ hsq hmod)

/-- Condition (4) of Stacks 0EVI for a subterminal presheaf. -/
public theorem isTwoGeneratorAlmostBlowUpSheaf_of_nonempty
    (h : ∀ (X X' Z E : BigHOver B S hS) (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
        (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData),
      IsAffine ((BigHOver.toScheme B S hS).obj X) →
      IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b) →
      Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι) →
      IsPullback
        ((BigHOver.toScheme B S hS).map e) ((BigHOver.toScheme B S hS).map q)
        ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map b) →
      IsTwoGeneratorAlmostBlowUpModel
        ((BigHOver.toScheme B S hS).map b) ((BigHOver.toScheme B S hS).map z) →
      Nonempty (F.obj (op Z)) → Nonempty (F.obj (op X')) → Nonempty (F.obj (op X))) :
    IsTwoGeneratorAlmostBlowUpSheaf B S hS F := fun X X' Z E b z q e I hX hb hZ hsq hmod ↦
  isPullback_of_subsingleton_of_nonempty _ _ _ _ (h X X' Z E b z q e I hX hb hZ hsq hmod)

/-- For a subterminal sheaf a section over the target of a covering family exists as soon as one
exists over each member of the family. -/
public theorem nonempty_of_isSheaf_of_covering
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F)
    {T : BigHOver B S hS} {I : Type*} {V : I → BigHOver B S hS} (f : ∀ i, V i ⟶ T)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS T)
    (hV : ∀ i, Nonempty (F.obj (op (V i)))) : Nonempty (F.obj (op T)) := by
  rw [Presheaf.isSheaf_iff_nonempty_of_subsingleton] at hF
  refine hF T _ hf ?_
  rintro Y g ⟨W, a, b, ⟨i⟩, rfl⟩
  exact ⟨F.map a.op (hV i).some⟩

end BigHOver

end AlgebraicGeometry

end
