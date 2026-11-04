module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsTriangulatedSubcategory
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksCore.Tactic.StacksAttribute

/-!
# Where the unit or the counit of an adjunction is invertible

Let `F ⊣ G` be an adjunction. Two properties of objects are attached to it:

* `CategoryTheory.Adjunction.unitIsIso`, the objects `K` of the source of `F` at which the unit
  `K ⟶ G (F K)` is invertible;
* `CategoryTheory.Adjunction.counitIsIso`, the objects `K` of the source of `G` at which the
  counit `F (G K) ⟶ K` is invertible.

Each of the two is a strictly full subcategory closed under direct summands, `F` is fully
faithful on the first and `G` is fully faithful on the second. When the two categories are
pre-triangulated and the adjunction is exact, both are triangulated subcategories; being
closed under direct summands they are then *saturated*, or *thick*.

For the derived adjunction `Lf^* ⊣ Rf_*` of a morphism of ringed topoi
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` these are the two subcategories of cohomological descent:
the objects `K` of `D(O_D)` with `K ⟶ Rf_* Lf^* K` invertible, and the objects `K` of `D(O_C)`
with `Lf^* Rf_* K ⟶ K` invertible. Nothing in the statements below uses the geometry, so they
are proved for an arbitrary adjunction, and specialise to the derived adjunction of a morphism of
ringed topoi.

## Main definitions

* `CategoryTheory.Adjunction.unitIsIso` and `CategoryTheory.Adjunction.counitIsIso`; the first is
  carried into the second by `F`
  (`CategoryTheory.Adjunction.unitIsIso_le_counitIsIso_inverseImage`).
* `CategoryTheory.Adjunction.fullyFaithfulιCompLeftAdjoint` and
  `CategoryTheory.Adjunction.fullyFaithfulιCompRightAdjoint`, the full faithfulness of the two
  restricted adjoints, with
  `CategoryTheory.Adjunction.fullyFaithfulιCompLeftAdjointOfLE` and
  `CategoryTheory.Adjunction.fullyFaithfulιCompRightAdjointOfLE` transporting them along a bound
  `P ≤ adj.unitIsIso`, respectively `Q ≤ adj.counitIsIso`.

## Main results

* `CategoryTheory.Adjunction.unitIsIso_isStableUnderRetracts`,
  `isClosedUnderIsomorphisms_unitIsIso`, `unitIsIso_isSaturated` and
  `unitIsIso_isTriangulated`: the unit subcategory is a saturated triangulated strictly full
  subcategory.
* `CategoryTheory.Adjunction.counitIsIso_isStableUnderRetracts`,
  `isClosedUnderIsomorphisms_counitIsIso`, `counitIsIso_isSaturated` and
  `counitIsIso_isTriangulated`: the same for the counit subcategory.

## Implementation notes

Closure under isomorphisms and triangulatedness are instances of the corresponding statements
for an arbitrary shift-compatible natural transformation between exact functors, namely
`Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms` and
`isIso_app_isTriangulated`, applied to the unit `𝟭 ⟶ F ⋙ G` and to the counit `G ⋙ F ⟶ 𝟭`.
Stability under retracts is `CategoryTheory.NatTrans.retractArrowApp` together with the
stability of the isomorphisms under retracts of arrows, and saturation follows from it.

Full faithfulness is *data*, not a proposition, because `CategoryTheory.Functor.FullyFaithful`
records a chosen inverse on each hom-set; the preimage of `g : F K ⟶ F L` is the morphism
adjoint to `g` followed by the inverse of the unit at `L`.

## References

* [Stacks Project, Tag 0D7Q](https://stacks.math.columbia.edu/tag/0D7Q)
* [Stacks Project, Tag 0D7R](https://stacks.math.columbia.edu/tag/0D7R)
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open Limits ObjectProperty Pretriangulated

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- The objects `K` of the source of the left adjoint of an adjunction `F ⊣ G` at which the
unit `K ⟶ G (F K)` is invertible. -/
@[stacks 0D7Q "variant: the subcategory of objects at which the unit is invertible, for an arbitrary adjunction F ⊣ G; the tag, for the
derived adjunction Lf^* ⊣ Rf_* of a morphism of ringed topoi, is
Stacks.Cohomology.CohomologicalDescent.unitIsIso_saturated_triangulated_fullyFaithful"]
def unitIsIso : ObjectProperty C := fun K ↦ IsIso (adj.unit.app K)

/-- The objects `K` of the source of the right adjoint of an adjunction `F ⊣ G` at which the
counit `F (G K) ⟶ K` is invertible. -/
@[stacks 0D7R "variant: the subcategory of objects at which the counit is invertible, for an arbitrary adjunction F ⊣ G; the tag, for the
derived adjunction Lf^* ⊣ Rf_* of a morphism of ringed topoi, is
Stacks.Cohomology.CohomologicalDescent.counitIsIso_saturated_triangulated_fullyFaithful"]
def counitIsIso : ObjectProperty D := fun K ↦ IsIso (adj.counit.app K)

/-- **If the unit at `K` is invertible then so is the counit at `F K`**, because `F` of the unit
at `K` followed by the counit at `F K` is the identity. -/
lemma isIso_counit_app_obj_of_isIso_unit_app (K : C) (hK : IsIso (adj.unit.app K)) :
    IsIso (adj.counit.app (F.obj K)) := by
  have := hK
  have heq : F.map (adj.unit.app K) ≫ adj.counit.app (F.obj K) = 𝟙 (F.obj K) :=
    adj.left_triangle_components K
  have h : IsIso (F.map (adj.unit.app K) ≫ adj.counit.app (F.obj K)) := by
    rw [heq]
    exact (Iso.refl _).isIso_hom
  exact IsIso.of_isIso_comp_left (F.map (adj.unit.app K)) (adj.counit.app (F.obj K))

/-- **The left adjoint carries the unit subcategory into the counit subcategory.** -/
lemma unitIsIso_le_counitIsIso_inverseImage :
    adj.unitIsIso ≤ adj.counitIsIso.inverseImage F :=
  fun _ hK ↦ adj.isIso_counit_app_obj_of_isIso_unit_app _ hK

/-- The unit subcategory is closed under direct summands: a retract of `K` gives a retract of
the arrow `adj.unit.app K`, and the isomorphisms are stable under retracts of arrows. -/
instance unitIsIso_isStableUnderRetracts : adj.unitIsIso.IsStableUnderRetracts where
  of_retract h hY :=
    MorphismProperty.of_retract (P := MorphismProperty.isomorphisms C)
      (NatTrans.retractArrowApp adj.unit h) hY

/-- The counit subcategory is closed under direct summands. -/
instance counitIsIso_isStableUnderRetracts : adj.counitIsIso.IsStableUnderRetracts where
  of_retract h hY :=
    MorphismProperty.of_retract (P := MorphismProperty.isomorphisms D)
      (NatTrans.retractArrowApp adj.counit h) hY

/-- **The unit subcategory is strictly full**: it is closed under isomorphisms, by naturality
of the unit. -/
@[stacks 0D7Q "variant: the unit subcategory is strictly full, for an arbitrary adjunction F ⊣ G; the tag, for the
derived adjunction Lf^* ⊣ Rf_* of a morphism of ringed topoi, is
Stacks.Cohomology.CohomologicalDescent.unitIsIso_saturated_triangulated_fullyFaithful"]
lemma isClosedUnderIsomorphisms_unitIsIso : adj.unitIsIso.IsClosedUnderIsomorphisms :=
  Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms adj.unit

/-- **The counit subcategory is strictly full**: it is closed under isomorphisms, by naturality
of the counit. -/
@[stacks 0D7R "variant: the counit subcategory is strictly full, for an arbitrary adjunction F ⊣ G; the tag, for the
derived adjunction Lf^* ⊣ Rf_* of a morphism of ringed topoi, is
Stacks.Cohomology.CohomologicalDescent.counitIsIso_saturated_triangulated_fullyFaithful"]
lemma isClosedUnderIsomorphisms_counitIsIso : adj.counitIsIso.IsClosedUnderIsomorphisms :=
  Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms adj.counit

/-- **The unit subcategory is saturated**: a direct summand of an object at which the unit is
invertible is again such an object. -/
@[stacks 0D7Q "variant: the unit subcategory is saturated, for an arbitrary adjunction F ⊣ G; the tag, for the
derived adjunction Lf^* ⊣ Rf_* of a morphism of ringed topoi, is
Stacks.Cohomology.CohomologicalDescent.unitIsIso_saturated_triangulated_fullyFaithful"]
instance unitIsIso_isSaturated [HasZeroMorphisms C] : adj.unitIsIso.IsSaturated :=
  IsSaturated.of_isStableUnderRetracts _

/-- **The counit subcategory is saturated**: a direct summand of an object at which the counit
is invertible is again such an object. -/
@[stacks 0D7R "variant: the counit subcategory is saturated, for an arbitrary adjunction F ⊣ G; the tag, for the
derived adjunction Lf^* ⊣ Rf_* of a morphism of ringed topoi, is
Stacks.Cohomology.CohomologicalDescent.counitIsIso_saturated_triangulated_fullyFaithful"]
instance counitIsIso_isSaturated [HasZeroMorphisms D] : adj.counitIsIso.IsSaturated :=
  IsSaturated.of_isStableUnderRetracts _

/-- **The left adjoint is fully faithful on the unit subcategory.** The preimage of
`g : F K ⟶ F L` is the morphism `K ⟶ G (F L)` adjoint to `g`, followed by the inverse of the
unit at `L`. -/
@[stacks 0D7Q "variant: the left adjoint is fully faithful on the unit subcategory, for an arbitrary adjunction F ⊣ G; the tag, for the
derived adjunction Lf^* ⊣ Rf_* of a morphism of ringed topoi, is
Stacks.Cohomology.CohomologicalDescent.unitIsIso_saturated_triangulated_fullyFaithful"]
noncomputable def fullyFaithfulιCompLeftAdjoint : (adj.unitIsIso.ι ⋙ F).FullyFaithful where
  preimage {K L} g :=
    letI : IsIso (adj.unit.app L.obj) := L.property
    homMk (adj.homEquiv K.obj (F.obj L.obj) g ≫ inv (adj.unit.app L.obj))
  map_preimage {K L} g := by
    let : IsIso (adj.unit.app L.obj) := L.property
    change F.map (adj.homEquiv K.obj (F.obj L.obj) g ≫ inv (adj.unit.app L.obj)) = g
    simp only [Functor.map_comp, Adjunction.homEquiv_apply]
    rw [Functor.map_inv, adj.inv_map_unit, ← Functor.comp_map, Category.assoc,
      adj.counit.naturality, ← Category.assoc, adj.left_triangle_components]
    simp
  preimage_map {K L} g := by
    let : IsIso (adj.unit.app L.obj) := L.property
    apply hom_ext
    change adj.homEquiv K.obj (F.obj L.obj) (F.map g.hom) ≫ inv (adj.unit.app L.obj) = g.hom
    rw [Adjunction.homEquiv_apply, ← Functor.comp_map, ← adj.unit.naturality g.hom]
    simp

/-- **The right adjoint is fully faithful on the counit subcategory.** The preimage of
`g : G A ⟶ G B` is the inverse of the counit at `A`, followed by the morphism `F (G A) ⟶ B`
adjoint to `g`. -/
@[stacks 0D7R "variant: the right adjoint is fully faithful on the counit subcategory, for an arbitrary adjunction F ⊣ G; the tag, for the
derived adjunction Lf^* ⊣ Rf_* of a morphism of ringed topoi, is
Stacks.Cohomology.CohomologicalDescent.counitIsIso_saturated_triangulated_fullyFaithful",
  sga "4 I 6.4" "more general"]
noncomputable def fullyFaithfulιCompRightAdjoint : (adj.counitIsIso.ι ⋙ G).FullyFaithful where
  preimage {A B} g :=
    letI : IsIso (adj.counit.app A.obj) := A.property
    homMk (inv (adj.counit.app A.obj) ≫ (adj.homEquiv (G.obj A.obj) B.obj).symm g)
  map_preimage {A B} g := by
    let : IsIso (adj.counit.app A.obj) := A.property
    change
      G.map (inv (adj.counit.app A.obj) ≫ (adj.homEquiv (G.obj A.obj) B.obj).symm g) = g
    rw [Functor.map_comp, Functor.map_inv, adj.inv_counit_map]
    change (adj.homEquiv (G.obj A.obj) B.obj) ((adj.homEquiv (G.obj A.obj) B.obj).symm g) = g
    exact (adj.homEquiv (G.obj A.obj) B.obj).apply_symm_apply g
  preimage_map {A B} g := by
    let : IsIso (adj.counit.app A.obj) := A.property
    apply hom_ext
    change
      inv (adj.counit.app A.obj) ≫ (adj.homEquiv (G.obj A.obj) B.obj).symm (G.map g.hom) = g.hom
    rw [adj.homEquiv_counit]
    change inv (adj.counit.app A.obj) ≫ ((G ⋙ F).map g.hom ≫ adj.counit.app B.obj) = g.hom
    rw [adj.counit.naturality g.hom]
    simp

/-- **The left adjoint is fully faithful on any subcategory of the unit subcategory.**
`CategoryTheory.Adjunction.fullyFaithfulιCompLeftAdjoint` transported along the bound
`P ≤ adj.unitIsIso`: the inclusion of `P` into the unit subcategory is fully faithful, and
composing it with `adj.unitIsIso.ι ⋙ F` is the functor `P.ι ⋙ F` up to the associator and the
comparison of the two inclusions. -/
@[sga "4 I 5.6" "iii⇒ii",
  sga "4 I 6.4" "more general",
  sga "4 IV 4.3.5" "partial",
  sga "4 Vbis 2.2.5" "partial",
  sga "4 Vbis 2.4.9" "partial"]
noncomputable def fullyFaithfulιCompLeftAdjointOfLE {P : ObjectProperty C}
    (h : P ≤ adj.unitIsIso) : (P.ι ⋙ F).FullyFaithful :=
  ((ObjectProperty.fullyFaithfulιOfLE h).comp adj.fullyFaithfulιCompLeftAdjoint).ofIso
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      (ObjectProperty.ιOfLECompιIso h) F)

/-- **The right adjoint is fully faithful on any subcategory of the counit subcategory.**
`CategoryTheory.Adjunction.fullyFaithfulιCompRightAdjoint` transported along the bound
`Q ≤ adj.counitIsIso`, exactly as for the left adjoint. -/
@[sga "4 I 6.4" "more general", sga "4 IV 9.1.1" "partial"]
noncomputable def fullyFaithfulιCompRightAdjointOfLE {Q : ObjectProperty D}
    (h : Q ≤ adj.counitIsIso) : (Q.ι ⋙ G).FullyFaithful :=
  ((ObjectProperty.fullyFaithfulιOfLE h).comp adj.fullyFaithfulιCompRightAdjoint).ofIso
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      (ObjectProperty.ιOfLECompιIso h) G)

end

section Triangulated

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.CommShift ℤ] [G.CommShift ℤ]
  [adj.IsTriangulated]

/-- **The unit subcategory is triangulated**: it contains the zero object, is stable under the
shift because the unit commutes with it, and passes from two vertices of a distinguished
triangle to the third by the five lemma for triangles. -/
@[stacks 0D7Q "variant: the unit subcategory is triangulated, for a triangulated adjunction, for an arbitrary adjunction F ⊣ G; the tag, for the
derived adjunction Lf^* ⊣ Rf_* of a morphism of ringed topoi, is
Stacks.Cohomology.CohomologicalDescent.unitIsIso_saturated_triangulated_fullyFaithful"]
instance unitIsIso_isTriangulated : adj.unitIsIso.IsTriangulated :=
  Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated (𝟭 C) (F ⋙ G) adj.unit

/-- **The counit subcategory is triangulated.** -/
@[stacks 0D7R "variant: the counit subcategory is triangulated, for a triangulated adjunction, for an arbitrary adjunction F ⊣ G; the tag, for the
derived adjunction Lf^* ⊣ Rf_* of a morphism of ringed topoi, is
Stacks.Cohomology.CohomologicalDescent.counitIsIso_saturated_triangulated_fullyFaithful"]
instance counitIsIso_isTriangulated : adj.counitIsIso.IsTriangulated :=
  Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated (G ⋙ F) (𝟭 D)
    adj.counit

end Triangulated

end CategoryTheory.Adjunction

end
