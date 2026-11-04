module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-!
# Transformations induced on complexes commute with the shift

An additive functor `F : 𝒜 ⥤ ℬ` of preadditive categories induces functors on cochain
complexes, on the homotopy category and on the bounded below homotopy category, and an additive
natural transformation `α : F ⟶ G` induces transformations between them. This file records that
each of those induced transformations commutes with the shift by `ℤ`, together with the same
statement for the two comparison isomorphisms `(𝟭 𝒜)_* ≅ 𝟭` and `F_* ⋙ G_* ≅ (F ⋙ G)_*`.

Degreewise this is immediate: the shift of cochain complexes does not change the terms of a
complex, so the commutation isomorphism of `F.mapHomologicalComplex` has identity components,
and so does the transformation induced by `α`. The content is the transport of that statement
along the quotient onto the homotopy category and along the inclusion of the bounded below
subcategory, which is carried out with the two reduction lemmas of
`StacksFrontier.CategoryTheory.Shift.DetectingCommShift`: the quotient is essentially surjective and
commutes with the shift, and the inclusion of the bounded below subcategory is faithful and
commutes with the shift.

## Main results

* `CategoryTheory.commShift_mapHomologicalComplex`,
  `CategoryTheory.commShift_mapHomologicalComplexIdIso`,
  `CategoryTheory.commShift_mapHomologicalComplexCompIso`: the degreewise statements.
* `CategoryTheory.commShift_mapHomotopyCategory`: the transformation induced by `α` on homotopy
  categories commutes with the shift.
* `CategoryTheory.commShift_mapHomotopyCategoryPlusNatTrans`: the same on bounded below homotopy
  categories.
* `CategoryTheory.commShift_mapHomotopyCategoryCompIso` and
  `CategoryTheory.commShift_mapHomotopyCategoryPlusCompIso`: the comparison
  `F_* ⋙ G_* ≅ (F ⋙ G)_*` commutes with the shift, on homotopy categories and on bounded below
  homotopy categories.
* `CategoryTheory.commShift_mapHomotopyCategoryPlusIdComparison`: the comparison of the identity
  functor of a bounded below homotopy category with the functor induced by the identity commutes
  with the shift.

## Implementation notes

The comparison isomorphisms used to transport — `CategoryTheory.Functor.mapHomotopyCategoryFactors`
and `CategoryTheory.ObjectProperty.liftCompιIso` — have identity components, which is why each
transport step ends with the same two unitor equations rather than with a computation. They are
discharged by `Category.id_comp` and `Category.comp_id` applied as a term rather than by `simp`:
the object arguments of the two identities are produced by the comparison isomorphisms in a
spelling which is only definitionally the source and target of the morphism between them, so the
rewrite has nothing to match on. The same holds of `Functor.map_id` whiskered into such a chain,
which is why it too is applied as a term, through `CategoryTheory.eq_whisker`.

For the two comparison isomorphisms the transport is not a conjugation but an equality: the
restriction of the comparison along the quotient, respectively its whiskering with the inclusion
of the bounded below subcategory, is written out as an explicit composite of associators, of
whiskerings of `mapHomotopyCategoryFactors` respectively `liftCompιIso`, and of the degreewise
comparison — each factor shift-compatible for a reason of its own — and the two are then
identified by `CategoryTheory.NatTrans.commShift_of_eq`.
-/

@[expose] public section

universe v u v' u' v'' u''

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Preadditive A] {B : Type u'} [Category.{v'} B]
  [Preadditive B] {E : Type u''} [Category.{v''} E] [Preadditive E]

/-- **An additive natural transformation commutes with the shift degreewise**: the shift of
cochain complexes leaves the terms of a complex unchanged, and both the transformation and the
commutation isomorphism of `mapHomologicalComplex` are the identity in each degree. -/
instance commShift_mapHomologicalComplex {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G) :
    NatTrans.CommShift (α.mapHomologicalComplex (ComplexShape.up ℤ)) ℤ := by
  constructor
  intro n
  ext K i
  simp [NatTrans.mapHomologicalComplex, CochainComplex.shiftFunctor_map_f']

/-- **The comparison of the identity functor on complexes with the identity functor commutes
with the shift**, both sides being the identity in each degree. -/
instance commShift_mapHomologicalComplexIdIso :
    NatTrans.CommShift (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom ℤ := by
  constructor
  intro n
  ext K i
  simp [CochainComplex.shiftFunctor_map_f']

/-- **The comparison of a composite of functors on complexes with the functor induced by the
composite commutes with the shift**, both sides being given in each degree by the component of
the comparison of the underlying functors. -/
instance commShift_mapHomologicalComplexCompIso {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ E}
    (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.CommShift (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom ℤ := by
  constructor
  intro n
  ext K i
  simp [CochainComplex.shiftFunctor_map_f', Functor.commShiftIso_comp_hom_app]

/-- **The transformation induced on homotopy categories by an additive natural transformation
commutes with the shift.** The quotient onto the homotopy category is essentially surjective and
commutes with the shift, so the equation may be tested on the image of a complex, where the
transformation is the quotient of the degreewise one. -/
instance commShift_mapHomotopyCategory {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)) ℤ := by
  refine NatTrans.commShift_of_whiskerLeft
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _ ?_
  refine NatTrans.commShift_of_eq_conj (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    (Functor.whiskerRight (α.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient B (ComplexShape.up ℤ))) ?_
  ext K
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **The transformation induced on bounded below homotopy categories by an additive natural
transformation commutes with the shift.** The inclusion of the bounded below subcategory is
faithful and commutes with the shift, and after whiskering with it the transformation is the one
induced on the whole homotopy category. -/
instance commShift_mapHomotopyCategoryPlusNatTrans {F G : A ⥤ B} [F.Additive] [G.Additive]
    (α : F ⟶ G) : NatTrans.CommShift (Functor.mapHomotopyCategoryPlusNatTrans α) ℤ := by
  refine NatTrans.commShift_of_whiskerRight _ (HomotopyCategory.Plus.ι B) ?_
  let eF : F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ≅
      HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  let eG : G.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ≅
      HomotopyCategory.Plus.ι A ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  have : NatTrans.CommShift eF.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eG.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  refine NatTrans.commShift_of_eq_conj eF eG
    (Functor.whiskerLeft (HomotopyCategory.Plus.ι A)
      (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ))) ?_
  ext K
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **The comparison of a composite of functors on homotopy categories with the functor induced
by the composite commutes with the shift.** The quotient onto the homotopy category is
essentially surjective and commutes with the shift, and after restriction along it the
comparison is the degreewise one, transported across the two factorizations of the induced
functors through the quotient. -/
instance commShift_mapHomotopyCategoryCompIso {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ E}
    (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.CommShift (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom ℤ := by
  refine NatTrans.commShift_of_whiskerLeft
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _ ?_
  refine NatTrans.commShift_of_eq (θ :=
    (Functor.associator (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (F.mapHomotopyCategory (ComplexShape.up ℤ))
        (G.mapHomotopyCategory (ComplexShape.up ℤ))).inv ≫
      Functor.whiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
        (G.mapHomotopyCategory (ComplexShape.up ℤ)) ≫
      (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (G.mapHomotopyCategory (ComplexShape.up ℤ))).hom ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ≫
      (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (G.mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.quotient E (ComplexShape.up ℤ))).inv ≫
      Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom
        (HomotopyCategory.quotient E (ComplexShape.up ℤ)) ≫
      (H.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv) ?_
  ext K
  exact ((Category.id_comp _).trans
    ((((G.mapHomotopyCategory (ComplexShape.up ℤ)).map_id _) =≫ _).trans
      ((Category.id_comp _).trans ((Category.id_comp _).trans ((Category.id_comp _).trans
        ((Category.id_comp _).trans (Category.comp_id _))))))).symm

/-- **The comparison of a composite of functors on bounded below homotopy categories with the
functor induced by the composite commutes with the shift.** The inclusion of the bounded below
subcategory is faithful and commutes with the shift, and after whiskering with it the comparison
is the one on the whole homotopy category, transported across the three presentations of the
induced functors as lifts. -/
instance commShift_mapHomotopyCategoryPlusCompIso {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ E}
    (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.CommShift (Functor.mapHomotopyCategoryPlusCompIso e).hom ℤ := by
  refine NatTrans.commShift_of_whiskerRight _ (HomotopyCategory.Plus.ι E) ?_
  let eF : F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ≅
      HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  let eG : G.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι E ≅
      HomotopyCategory.Plus.ι B ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  let eH : H.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι E ≅
      HomotopyCategory.Plus.ι A ⋙ H.mapHomotopyCategory (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  have : NatTrans.CommShift eF.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eG.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eH.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  refine NatTrans.commShift_of_eq (θ :=
    (Functor.associator F.mapHomotopyCategoryPlus G.mapHomotopyCategoryPlus
        (HomotopyCategory.Plus.ι E)).hom ≫
      Functor.whiskerLeft F.mapHomotopyCategoryPlus eG.hom ≫
      (Functor.associator F.mapHomotopyCategoryPlus (HomotopyCategory.Plus.ι B)
        (G.mapHomotopyCategory (ComplexShape.up ℤ))).inv ≫
      Functor.whiskerRight eF.hom (G.mapHomotopyCategory (ComplexShape.up ℤ)) ≫
      (Functor.associator (HomotopyCategory.Plus.ι A)
        (F.mapHomotopyCategory (ComplexShape.up ℤ))
        (G.mapHomotopyCategory (ComplexShape.up ℤ))).hom ≫
      Functor.whiskerLeft (HomotopyCategory.Plus.ι A)
        (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom ≫
      eH.inv) ?_
  ext K
  exact ((Category.id_comp _).trans
    ((Category.id_comp _).trans
      ((Category.id_comp _).trans
        ((((G.mapHomotopyCategory (ComplexShape.up ℤ)).map_id _) =≫ _).trans
          ((Category.id_comp _).trans
            ((Category.id_comp _).trans (Category.comp_id _))))))).symm

/-- **The comparison of the identity functor of a bounded below homotopy category with the
functor induced by the identity commutes with the shift.** The inclusion of the bounded below
subcategory is faithful and commutes with the shift, and after whiskering with it the comparison
is the comparison on the whole homotopy category, which is the lift of the degreewise one. -/
instance commShift_mapHomotopyCategoryPlusIdComparison :
    NatTrans.CommShift (Functor.mapHomotopyCategoryPlusIdComparison A) ℤ := by
  refine NatTrans.commShift_of_whiskerRight _ (HomotopyCategory.Plus.ι A) ?_
  let eI : (𝟭 A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory A (ComplexShape.up ℤ)) :=
    CategoryTheory.Quotient.natIsoLift _
      (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)))
  have : NatTrans.CommShift eI.hom ℤ := by
    refine NatTrans.commShift_of_whiskerLeft
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _ ?_
    refine NatTrans.commShift_of_eq_conj
      ((𝟭 A).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      (Functor.rightUnitor (HomotopyCategory.quotient A (ComplexShape.up ℤ)))
      (Functor.whiskerRight (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)) ≫
        (Functor.leftUnitor (HomotopyCategory.quotient A (ComplexShape.up ℤ))).hom) ?_
    ext K
    exact ((Category.id_comp _).trans ((Category.comp_id _).trans (Category.comp_id _))).symm
  let eP : (𝟭 A).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι A ≅
      HomotopyCategory.Plus.ι A ⋙ (𝟭 A).mapHomotopyCategory (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  have : NatTrans.CommShift eP.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  refine NatTrans.commShift_of_eq_conj
    (Functor.leftUnitor (HomotopyCategory.Plus.ι A)) eP
    ((Functor.rightUnitor (HomotopyCategory.Plus.ι A)).inv ≫
      Functor.whiskerLeft (HomotopyCategory.Plus.ι A) eI.inv) ?_
  ext K
  exact ((Category.id_comp _).trans ((Category.comp_id _).trans (Category.id_comp _))).symm

end CategoryTheory

end
