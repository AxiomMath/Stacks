module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite
import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# The situation for comparing cohomology in two topologies

Let `C` be a category carrying two collections of covering families, a finer one `τ` and a
coarser one `τ'`, each satisfying the site axioms. Comparing cohomology computed for `τ` with
cohomology computed for `τ'` requires more than the inclusion `τ' ⊆ τ`: one needs a supply of
abelian sheaves on every localized coarse site which already satisfy descent for the finer
topology, which is stable under restriction and under all higher direct images along a
distinguished class `P` of morphisms, and one needs every fine covering to be refinable in
three stages — first by a coarse covering, then by a single fine `P`-morphism over each
member, and finally by a coarse covering of its source.

This file packages exactly that data as `Stacks.ComparingTopologies.CohomologyComparison`,
the standing situation of Stacks 0EZ3, together with the two change-of-topology functors
between abelian sheaves on the localized sites which the situation is about.

## Main definitions

* `Stacks.ComparingTopologies.abelianComparisonPullback`: the inverse image of the
  change-of-topology morphism on abelian sheaves, namely sheafification for the finer
  localized topology.
* `Stacks.ComparingTopologies.abelianComparisonPushforward`: its right adjoint, a sheaf for
  the finer localized topology regarded as a sheaf for the coarser one.
* `Stacks.ComparingTopologies.CohomologyComparison`: the comparison situation of the tag.

## Main results

The fields of `CohomologyComparison` are the two site structures and the five comparison
assumptions of the situation. The remaining declarations make those assumptions available to
instance synthesis.

## Implementation notes

A site's specified covering families are represented by a `Precoverage`, and the topology it
generates by `Precoverage.toGrothendieck`. The four fields attached to each precoverage are
the site axioms: isomorphisms cover, coverings compose, and the pullbacks needed to base
change a covering both exist and cover. This does not impose the existence of unrelated
pullbacks in `C`.

The assertion that an object of the coarse weak Serre class satisfies descent for the fine
coverings is recorded by saying that its underlying presheaf is a sheaf for the fine
localized topology, which is the form in which it is used.

The class `P` is a `MorphismProperty`, and its stability under base change is stated so as to
assert the existence of the base change as well, since `C` is not assumed to have fibre
products.

The three-stage refinement condition uses `Presieve.FactorsThruAlong`, which retains the
factorization through the originally given covering family rather than only the inclusion of
sieves.

## References

* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
-/

@[expose] public section

universe v u

open CategoryTheory

namespace Stacks.ComparingTopologies

variable {C : Type u} [Category.{v} C]

/-- Direct image along a morphism of a localized site is additive, being a right adjoint
between abelian categories. -/
noncomputable instance sheafPushforwardCocontinuous_additive
    (J : GrothendieckTopology C) {U V : C} (f : U ⟶ V) :
    ((Over.map f).sheafPushforwardCocontinuous Ab.{max u v} (J.over U) (J.over V)).Additive := by
  let _ :=
    ((Over.map f).sheafAdjunctionCocontinuous Ab.{max u v} (J.over U) (J.over V)).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-- Inverse image on abelian sheaves from the coarser precoverage `K'` to the finer
precoverage `K`, over an object `X`: forget to a presheaf and sheafify for the finer localized
topology. -/
noncomputable abbrev abelianComparisonPullback (K K' : Precoverage C) (X : C) :
    Sheaf (K'.toGrothendieck.over X) Ab.{max u v} ⥤ Sheaf (K.toGrothendieck.over X) Ab.{max u v} :=
  sheafToPresheaf (K'.toGrothendieck.over X) (Ab.{max u v}) ⋙
    presheafToSheaf (K.toGrothendieck.over X) (Ab.{max u v})

/-- Direct image on abelian sheaves for a comparison of a finer precoverage `K` with a coarser
precoverage `K'`, over an object `X`. It is the fully faithful inclusion determined by the
common underlying presheaf category. -/
def abelianComparisonPushforward (K K' : Precoverage C) (h : K' ≤ K) (X : C) :
    Sheaf (K.toGrothendieck.over X) Ab.{max u v} ⥤ Sheaf (K'.toGrothendieck.over X) Ab.{max u v} :=
  ObjectProperty.ιOfLE fun _ hF ↦ hF.of_le fun Y _S hS ↦
    (Precoverage.toGrothendieck_mono h) Y.left hS

/-- Change-of-topology direct image is additive, so its higher right-derived functors are
defined. -/
instance abelianComparisonPushforward_additive
    (K K' : Precoverage C) (h : K' ≤ K) (X : C) :
    (abelianComparisonPushforward K K' h X).Additive where
  map_add := rfl

/-- **Stacks 0EZ3.** The standing situation for comparing cohomology computed in a finer
coverage with cohomology computed in a coarser one. -/
@[stacks 0EZ3]
structure CohomologyComparison (C : Type u) [Category.{v} C] where
  /-- The covering families defining the finer site `τ`. -/
  fineCoverage : Precoverage C
  /-- Isomorphisms are fine coverings. -/
  fine_hasIsos : fineCoverage.HasIsos
  /-- Fine coverings are stable under refinement by fine coverings. -/
  fine_stableUnderComposition : fineCoverage.IsStableUnderComposition
  /-- The pullbacks required to base-change a fine covering exist. -/
  fine_hasPullbacks : fineCoverage.HasPullbacks
  /-- The projections from pullbacks of a fine covering form a fine covering. -/
  fine_stableUnderBaseChange : fineCoverage.IsStableUnderBaseChange
  /-- The covering families defining the coarser site `τ'`. -/
  coarseCoverage : Precoverage C
  /-- Isomorphisms are coarse coverings. -/
  coarse_hasIsos : coarseCoverage.HasIsos
  /-- Coarse coverings are stable under refinement by coarse coverings. -/
  coarse_stableUnderComposition : coarseCoverage.IsStableUnderComposition
  /-- The pullbacks required to base-change a coarse covering exist. -/
  coarse_hasPullbacks : coarseCoverage.HasPullbacks
  /-- The projections from pullbacks of a coarse covering form a coarse covering. -/
  coarse_stableUnderBaseChange : coarseCoverage.IsStableUnderBaseChange
  /-- Every `τ'`-covering is a `τ`-covering. -/
  coarse_le_fine : coarseCoverage ≤ fineCoverage
  /-- The distinguished class `P` of arrows. -/
  morphismProperty : MorphismProperty C
  /-- The weak Serre class `A'_X` on the coarser site localized at `X`. -/
  weakSerre : ∀ X : C,
    ObjectProperty (Sheaf (coarseCoverage.toGrothendieck.over X) Ab.{max u v})
  /-- Each `A'_X` is a weak Serre class. -/
  weakSerreClass : ∀ X : C, (weakSerre X).IsWeakSerreClass
  /-- The class `P` is stable under arbitrary base change, including existence of the base
  change. -/
  morphismProperty_baseChange : ∀ ⦃X Y Y' : C⦄ (f : X ⟶ Y), morphismProperty f →
    ∀ (g : Y' ⟶ Y), ∃ (Z : C) (q : Z ⟶ X) (p : Z ⟶ Y'),
      IsPullback q p f g ∧ morphismProperty p
  /-- Relocalization inverse image along any arrow preserves the weak Serre classes. -/
  weakSerre_relocalizationInverseImage : ∀ ⦃X Y : C⦄ (f : X ⟶ Y)
    (F : Sheaf (coarseCoverage.toGrothendieck.over Y) Ab.{max u v}), weakSerre Y F →
      weakSerre X ((coarseCoverage.toGrothendieck.overMapPullback Ab.{max u v} f).obj F)
  /-- Every object of `A'_X`, viewed as a presheaf on the localized category, satisfies the
  sheaf condition for the finer topology. -/
  weakSerre_isSheaf_fine : ∀ (X : C)
    (F : Sheaf (coarseCoverage.toGrothendieck.over X) Ab.{max u v}),
    weakSerre X F → Presheaf.IsSheaf (fineCoverage.toGrothendieck.over X) F.obj
  /-- All higher direct images along arrows in `P` remain in the designated weak Serre class. -/
  weakSerre_rightDerived_relocalizationPushforward : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    morphismProperty f →
      ∀ (F : Sheaf (coarseCoverage.toGrothendieck.over X) Ab.{max u v}), weakSerre X F →
        ∀ i : ℕ, weakSerre Y
          ((((Over.map f).sheafPushforwardCocontinuous Ab.{max u v}
            (coarseCoverage.toGrothendieck.over X)
            (coarseCoverage.toGrothendieck.over Y)).rightDerived i).obj F)
  /-- Every fine covering admits the three-stage refinement: first a coarse covering, then one
  fine `P`-arrow over each member, and finally a coarse covering of its source. -/
  covering_refinement : ∀ (U : C) (R : Presieve U), R ∈ fineCoverage U →
    ∃ S : Presieve U, S ∈ coarseCoverage U ∧
      ∀ ⦃V : C⦄ (v : V ⟶ U), S v →
        ∃ (W : C) (f : W ⟶ V), morphismProperty f ∧
          Presieve.singleton f ∈ fineCoverage V ∧
          ∃ T : Presieve W, T ∈ coarseCoverage W ∧ T.FactorsThruAlong R (f ≫ v)

/-- The fine covering families in a comparison situation contain all isomorphisms. -/
instance CohomologyComparison.fineCoverage_hasIsos (S : CohomologyComparison C) :
    S.fineCoverage.HasIsos := S.fine_hasIsos

/-- Fine covering families are stable under composition. -/
instance CohomologyComparison.fineCoverage_isStableUnderComposition
    (S : CohomologyComparison C) : S.fineCoverage.IsStableUnderComposition :=
  S.fine_stableUnderComposition

/-- Pullbacks needed to base-change fine covering families exist. -/
instance CohomologyComparison.fineCoverage_hasPullbacks (S : CohomologyComparison C) :
    S.fineCoverage.HasPullbacks := S.fine_hasPullbacks

/-- Fine covering families are stable under base change. -/
instance CohomologyComparison.fineCoverage_isStableUnderBaseChange
    (S : CohomologyComparison C) : S.fineCoverage.IsStableUnderBaseChange :=
  S.fine_stableUnderBaseChange

/-- The coarse covering families in a comparison situation contain all isomorphisms. -/
instance CohomologyComparison.coarseCoverage_hasIsos (S : CohomologyComparison C) :
    S.coarseCoverage.HasIsos := S.coarse_hasIsos

/-- Coarse covering families are stable under composition. -/
instance CohomologyComparison.coarseCoverage_isStableUnderComposition
    (S : CohomologyComparison C) : S.coarseCoverage.IsStableUnderComposition :=
  S.coarse_stableUnderComposition

/-- Pullbacks needed to base-change coarse covering families exist. -/
instance CohomologyComparison.coarseCoverage_hasPullbacks (S : CohomologyComparison C) :
    S.coarseCoverage.HasPullbacks := S.coarse_hasPullbacks

/-- Coarse covering families are stable under base change. -/
instance CohomologyComparison.coarseCoverage_isStableUnderBaseChange
    (S : CohomologyComparison C) : S.coarseCoverage.IsStableUnderBaseChange :=
  S.coarse_stableUnderBaseChange

/-- The designated property on every localized coarse site is a weak Serre class. -/
instance CohomologyComparison.weakSerre_isWeakSerreClass
    (S : CohomologyComparison C) (X : C) :
    (S.weakSerre X).IsWeakSerreClass := S.weakSerreClass X


/-- The abelian change-of-topology inverse image is the sheaf pullback along the identity
functor of the slice category, for the two localized topologies. -/
noncomputable def abelianComparisonPullbackIsoSheafPullback (S : CohomologyComparison C) (X : C)
    [Functor.IsContinuous (Functor.id (Over X))
      (S.coarseCoverage.toGrothendieck.over X) (S.fineCoverage.toGrothendieck.over X)] :
    abelianComparisonPullback S.fineCoverage S.coarseCoverage X ≅
      (Functor.id (Over X)).sheafPullback Ab.{max u v}
        (S.coarseCoverage.toGrothendieck.over X)
        (S.fineCoverage.toGrothendieck.over X) := by
  let lanIso : (Functor.id (Over X)).op.lan ≅ 𝟭 ((Over X)ᵒᵖ ⥤ Ab.{max u v}) :=
    Adjunction.leftAdjointUniq ((Functor.id (Over X)).op.lanAdjunction Ab.{max u v}) Adjunction.id
  change (sheafToPresheaf _ Ab.{max u v} ⋙ presheafToSheaf _ Ab.{max u v}) ≅ _
  exact (Functor.isoWhiskerLeft (sheafToPresheaf _ Ab.{max u v})
      (Functor.isoWhiskerRight lanIso (presheafToSheaf _ Ab.{max u v}))).symm ≪≫
    (Functor.sheafPullbackConstruction.sheafPullbackIso
      (Functor.id (Over X)) Ab.{max u v} _ _).symm

end Stacks.ComparingTopologies


/-!
# Comparing restriction functors for two topologies

Let `K ≤ J` be two Grothendieck topologies on a category `C`, so that `J` is the finer of the
two. Every `J`-sheaf is in particular a `K`-sheaf, which gives the direct image `ε_*` of the
comparison morphism of topoi `ε : Sh(C, J) ⟶ Sh(C, K)`; its left adjoint `ε⁻¹` is
`J`-sheafification of a `K`-sheaf. For a morphism `f : X ⟶ Y` of `C`, restriction to the
slices and the two comparison morphisms form the square of topoi of Stacks 0EZ2. This file
records both forms of its commutativity: an isomorphism of the composed inverse-image
functors, and the strict identity on direct images for `ε` and inverse images for `f`.

## Main definitions

* `Stacks.ComparingTopologies.comparisonPushforward`: a sheaf for the finer topology,
  regarded as a sheaf for the coarser one.
* `Stacks.ComparingTopologies.comparisonPullback`: its left adjoint, the inverse image of the
  comparison morphism.

## Main results

* `Stacks.ComparingTopologies.over_le_over`: passing to the slice topologies preserves an
  inequality of Grothendieck topologies.
* `Stacks.ComparingTopologies.comparisonPullbackOverMapPullbackIso`: the canonical natural
  isomorphism expressing commutativity of the square of topoi.
* `Stacks.ComparingTopologies.overMapPullback_comp_comparisonPushforward`: the corresponding
  strict identity `ε_{X,*} f_J^{-1} = f_K^{-1} ε_{Y,*}` on sheaves.

## Implementation notes

The topology called `J` here is `τ` in the source and `K` is `τ'`; thus `K ≤ J` says that
every `K`-cover is a `J`-cover. The comparison pushforward does not change the underlying
presheaf, which is why the second result is an equality of functors rather than merely an
isomorphism: it holds by `rfl`.

The isomorphism is obtained from uniqueness of left adjoints. Both composites in the square
are left adjoints of composites of the two pushforwards, and those two composites of
pushforwards are *equal* (again because the comparison pushforward does not touch the
underlying presheaf), so `Adjunction.leftAdjointUniq` applies after transporting one
adjunction along that equality.

## References

* [Stacks Project, Tag 0EZ2](https://stacks.math.columbia.edu/tag/0EZ2)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.ComparingTopologies

variable {C : Type u} [Category.{v} C]

/-- Passing to the slice topologies preserves an inequality of Grothendieck topologies. -/
lemma over_le_over {J K : GrothendieckTopology C} (h : K ≤ J) (X : C) :
    K.over X ≤ J.over X := by
  intro U S hS
  rw [GrothendieckTopology.mem_over_iff] at hS ⊢
  exact h _ hS

/-- The direct image of the comparison morphism from the finer topology `J` to the coarser
topology `K`. It leaves the underlying presheaf unchanged. -/
def comparisonPushforward {J K : GrothendieckTopology C} (h : K ≤ J) :
    Functor (Sheaf J (Type (max u v))) (Sheaf K (Type (max u v))) :=
  ObjectProperty.ιOfLE fun _ hF ↦ hF.of_le h

/-- The inverse image of the comparison morphism from the finer topology `J` to the coarser
topology `K`; equivalently, `J`-sheafification of a `K`-sheaf. -/
noncomputable def comparisonPullback {J K : GrothendieckTopology C} (h : K ≤ J) :
    Functor (Sheaf K (Type (max u v))) (Sheaf J (Type (max u v))) := by
  let : (Functor.id C).IsContinuous K J :=
    { op_comp_isSheaf_of_types := fun F ↦
        (isSheaf_iff_isSheaf_of_type _ _).1 (F.property.of_le h) }
  exact (Functor.id C).sheafPullback (Type (max u v)) K J

/-- **Stacks 0EZ2.** For two comparable topologies, change of topology commutes with
restriction along a morphism, up to the canonical natural isomorphism of inverse-image
functors. -/
@[stacks 0EZ2 "commutativity of the square of topoi"]
noncomputable def comparisonPullbackOverMapPullbackIso
    {J K : GrothendieckTopology C} (h : K ≤ J) {X Y : C} (f : X ⟶ Y) :
    comparisonPullback (over_le_over h Y) ⋙ J.overMapPullback (Type (max u v)) f ≅
      K.overMapPullback (Type (max u v)) f ⋙ comparisonPullback (over_le_over h X) := by
  let : (Functor.id (Over Y)).IsContinuous (K.over Y) (J.over Y) :=
    { op_comp_isSheaf_of_types := fun F ↦
        (isSheaf_iff_isSheaf_of_type _ _).1 (F.property.of_le (over_le_over h Y)) }
  let : (Functor.id (Over X)).IsContinuous (K.over X) (J.over X) :=
    { op_comp_isSheaf_of_types := fun F ↦
        (isSheaf_iff_isSheaf_of_type _ _).1 (F.property.of_le (over_le_over h X)) }
  let adjY : comparisonPullback (over_le_over h Y) ⊣
      comparisonPushforward (over_le_over h Y) :=
    (Functor.id (Over Y)).sheafAdjunctionContinuous (Type (max u v)) (K.over Y) (J.over Y)
  let adjX : comparisonPullback (over_le_over h X) ⊣
      comparisonPushforward (over_le_over h X) :=
    (Functor.id (Over X)).sheafAdjunctionContinuous (Type (max u v)) (K.over X) (J.over X)
  let rightEq :
      (Over.map f).sheafPushforwardCocontinuous (Type (max u v)) (J.over X) (J.over Y) ⋙
        comparisonPushforward (over_le_over h Y) =
      comparisonPushforward (over_le_over h X) ⋙
        (Over.map f).sheafPushforwardCocontinuous (Type (max u v)) (K.over X) (K.over Y) := rfl
  let adj₁ := adjY.comp
    ((Over.map f).sheafAdjunctionCocontinuous (Type (max u v)) (J.over X) (J.over Y))
  let adj₂ := ((Over.map f).sheafAdjunctionCocontinuous (Type (max u v)) (K.over X) (K.over Y)).comp
    adjX
  exact adj₁.leftAdjointUniq (adj₂.ofNatIsoRight (eqToIso rightEq).symm)

/-- **Stacks 0EZ2.** On direct images for the comparison morphisms and inverse images for
restriction, the square commutes strictly:
`ε_{X,*} ∘ f_J^{-1} = f_K^{-1} ∘ ε_{Y,*}`. -/
@[stacks 0EZ2 "the identity `ε_{X,*} f_J^{-1} = f_K^{-1} ε_{Y,*}`"]
theorem overMapPullback_comp_comparisonPushforward
    {J K : GrothendieckTopology C} (h : K ≤ J) {X Y : C} (f : X ⟶ Y) :
    J.overMapPullback (Type (max u v)) f ⋙ comparisonPushforward (over_le_over h X) =
      comparisonPushforward (over_le_over h Y) ⋙ K.overMapPullback (Type (max u v)) f := by
  rfl

end Stacks.ComparingTopologies
