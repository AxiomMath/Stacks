module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.AugmentedAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Presheaf
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplex

/-!
# Degree-zero cohomology of a hypercovering of a presheaf

Let `C` be a category with equalizers and fibre products, carrying a pretopology `J`, let `G` be
a presheaf of sets on `C`, let `K` be a hypercovering of `G` in the sense of Tag 09VU, and let
`F` be a sheaf of abelian groups on `C`.  Evaluating `F` on `K` degreewise gives the Čech
cochain complex of `K` with coefficients in `F` (Tag 01GX), whose cohomology is the Čech
cohomology `cechCohomology`.  This file identifies its degree-zero part with
`presheafCohomologyZero`, the group of morphisms from the free abelian presheaf on `G` to the
underlying presheaf of `F`.  This is Stacks Project, Tag 09VV in degree zero.

The proof is the one of the source.  The hypercovering conditions say that the augmented
simplicial presheaf `F(K) ⟶ G` is locally covering in the sense of Tag 01GE, so its degree-zero
homology sheaf is the free abelian sheaf `**Z**_G^♯` (Tag 01GC).  Applying `Hom(-, F)` to the
complex of free abelian sheaves and comparing with the complex of sections (Tag 01GX) turns that
identification into the asserted one, the last step being the sheafification adjunction together
with the free–forgetful adjunction on presheaves of sets.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.cechCohomology`: the Čech cohomology of a hypercovering
  of a presheaf with coefficients in a sheaf of abelian groups, that is the cohomology of the
  alternating coface complex of Tag 01GX.
* `Stacks.CategoryTheory.Hypercovering.presheafCohomologyZero`: degree-zero cohomology of a
  presheaf of sets with coefficients in a sheaf of abelian groups.
* `Stacks.CategoryTheory.Hypercovering.HypercoveringOf.toAugmented` and
  `Stacks.CategoryTheory.Hypercovering.HypercoveringOf.toAugmentedULift`: the augmented
  simplicial presheaf underlying a hypercovering of a presheaf, with values in
  `Type (max q w v)` respectively lifted into the common universe `max (max u v) (max q w)` of
  the statement.
* `CategoryTheory.uliftFunctorCompIso`: two successive universe lifts of type-valued functors
  compose to a single one; this is what identifies the two ways of lifting the presheaves of
  Tag 09VU into the common universe
  (`Stacks.CategoryTheory.Hypercovering.associatedPresheafFunctorULiftIso` and
  `Stacks.CategoryTheory.Hypercovering.liftedPresheafULiftIso`).
* `Stacks.CategoryTheory.Hypercovering.presheafULiftFunctor`: the sectionwise universe lift of
  presheaves of sets effecting that comparison.
* `Stacks.CategoryTheory.Hypercovering.cechCohomologyZeroIso`: the explicit isomorphism asserted
  by Tag 09VV in degree zero.

## Main results

* `Stacks.CategoryTheory.Hypercovering.nonempty_cechCohomologyZeroIso`: **Tag 09VV**, the
  degree-zero Čech cohomology of a hypercovering of `G` with coefficients in `F` is the
  degree-zero cohomology of `G` with coefficients in `F`.
* `sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees`, in the namespace
  `CategoryTheory.SimplicialObject.Augmented`: the degree-zero half of Tag 01GE needs no
  hypothesis on the higher matching maps.
* `Stacks.CategoryTheory.Hypercovering.homFreeAbelianSheafComplexHomologyZeroIso`: the
  degree-zero cohomology of the Hom complex of Tag 01GX is `Hom` out of degree-zero homology.
* `Stacks.CategoryTheory.Hypercovering.hasSheafify_addCommGrpCat`: presheaves of abelian groups
  valued in any universe at least as large as that of the site admit sheafification.
* `Stacks.CategoryTheory.Hypercovering.isLocallySurjective_presheafULiftFunctor_map`,
  `Stacks.CategoryTheory.Hypercovering.isLocallySurjective_edgesToFiberProduct_toAugmented`,
  `Stacks.CategoryTheory.Hypercovering.isLocallySurjective_toAugmentedULift_hom_app_zero` and
  `Stacks.CategoryTheory.Hypercovering.isLocallySurjective_edgesToFiberProduct_toAugmentedULift`:
  the hypercovering conditions (1) and (2) in the form Tag 01GE asks for them, before and after
  the universe lift.

## Implementation notes

The source states the result as an equality of groups; it is given here as the existence of an
isomorphism in `AddCommGrpCat`.  The two sides are built from independently chosen
sheafifications and products, so no equality of objects is available, and the group on the right
is presented through the free–forgetful adjunction as morphisms out of the pointwise free abelian
presheaf.  The `Nonempty` wrapper of `nonempty_cechCohomologyZeroIso` is weaker than the source,
which asserts an identification: the isomorphism itself is therefore also exposed, as
`cechCohomologyZeroIso`, and `nonempty_cechCohomologyZeroIso` is literally `⟨·⟩` of it.

Four universes occur and none of them is specialised: `C : Type u` with `Category.{v} C`, the
index types of the semi-representable objects of Tag 09VU live in `Type w`, the presheaf `G` is
valued in `Type q`, and the sheaf of abelian groups is valued in
`AddCommGrpCat.{max (max u v) (max q w)}`.  Every `max` is load-bearing.  This is forced rather
than chosen: the presheaf represented by a semi-representable object has values in
`Type (max w v)` and is lifted to `Type (max q w v)` in Tag 09VU, while sheafification of
abelian groups is only available in a universe containing that of the site, so the comparison
can only take place in `max (max u v) (max q w)`; and `q` is what makes the coefficient universe
of the statement arbitrary.  The two ways of reaching that universe — lift `G` to
`Type (max q w v)` first and then to the top, or lift it directly — are identified by
`uliftFunctorCompIso`.

Four declarations are stated at universes more general than the ones they are used at, which is
both the natural form of the statement and what keeps the file free of `checkUnivs` exceptions:
a declaration whose type only mentions `max (max u v) (max q w)` has no subterm in which `q` or
`w` occurs on its own and is rejected by that linter.  So `hasSheafify_addCommGrpCat` is stated
for `AddCommGrpCat.{max (max u' v') t}` with `t` free, `presheafULiftFunctor`,
`isLocallySurjective_presheafULiftFunctor_map` and
`presheafULiftFunctor_preservesLimitsOfShape_walkingCospan` for an arbitrary lift
`Type s ⥤ Type (max s t)`, and
`CategoryTheory.SimplicialObject.Augmented.sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees`
for presheaves valued in an arbitrary `Type w'`.  The last of these is where the degree-zero case
of Tag 01GE is isolated: unlike
`CategoryTheory.SimplicialObject.Augmented.sheafHomologyZeroIso_of_isLocallySurjective_matchingMaps`
it needs no hypothesis on the higher matching maps, because degree-zero homology only depends on
the degrees `≤ 1`, on which the unit of the first coskeleton adjunction is already an
isomorphism.  It is also a `def` producing the isomorphism rather than a proof of its existence,
which is what makes `cechCohomologyZeroIso` available.

No transparency option is used.  `presheafULiftFunctor` is deliberately an `abbrev`, hence
reducible: the comparison of the lifted augmented simplicial presheaf with the unlifted one in
`isLocallySurjective_edgesToFiberProduct_toAugmentedULift` transports local surjectivity along
`eqToIso`s of its object parts, and the `change`, `rfl` and `cat_disch` steps doing so see the
syntactic form of the lift only because it unfolds at reducible transparency.  In that transport
the two morphisms whose fibre products are being compared are named as local `let`s and the
rewriting is done with equations between them, rather than by rewriting the spelled-out terms in
place; the same device is used in
`StacksFrontier/CategoryTheory/Sites/CechNerveHomology.lean`.

## References

* [Stacks Project, Tag 09VV](https://stacks.math.columbia.edu/tag/09VV)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 01GB](https://stacks.math.columbia.edu/tag/01GB)
* [Stacks Project, Tag 01GC](https://stacks.math.columbia.edu/tag/01GC)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Two successive universe lifts of type-valued functors compose to a single one. -/
def uliftFunctorCompIso.{s, t, r} :
    CategoryTheory.uliftFunctor.{s, r} ⋙ CategoryTheory.uliftFunctor.{t, max s r} ≅
      CategoryTheory.uliftFunctor.{max s t, r} := by
  refine NatIso.ofComponents (fun α => Equiv.toIso ?_) ?_
  · exact
      { toFun := fun x => ⟨x.down.down⟩
        invFun := fun x => ⟨⟨x.down⟩⟩
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; cases x; rfl }
  · intro α β f
    ext x
    rfl

end CategoryTheory

namespace CategoryTheory.SimplicialObject.Augmented

/-- The degree-zero half of Tag 01GE needs no hypothesis on the higher matching maps: if the
degree-zero augmentation and the relation map of an augmented simplicial presheaf are locally
surjective, its degree-zero homology sheaf is already the free abelian sheaf on the presheaf of
augmentation points.  Only the comparison with the first coskeleton is used, and the unit of the
coskeleton adjunction is an isomorphism in the degrees `≤ 1` on which degree-zero homology
depends. -/
noncomputable def sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees.{w', v', u'}
    {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w'}]
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w'))
    (h₀ : Presheaf.IsLocallySurjective J
      (K.hom.app (Opposite.op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct K)) :
    SimplicialObject.sheafHomology J K.left 0 ≅
      (presheafToSheaf J AddCommGrpCat.{w'}).obj (K.right ⋙ AddCommGrpCat.free) := by
  letI : SimplicialObject.HasCosk₁ (Cᵒᵖ ⥤ Type w') := ⟨fun _ => inferInstance⟩
  have hη : IsIso ((SimplicialObject.sheafHomologyFunctor J 0).map
      ((SimplicialObject.coskAdj 1).unit.app K.left)) := by
    apply SimplicialObject.isIso_sheafHomologyFunctor_map_of_isIso_lowDegrees
    intro j hj
    exact SimplicialObject.isIso_coskAdj_unit_app_app_of_le K.left 1 j hj
  have hc : IsIso ((SimplicialObject.sheafHomologyFunctor J 0).map
      (coskOneToCechNerve K)) :=
    isIso_sheafHomologyFunctor_map_coskOneToCechNerve J K h₁ 0
  have hf : IsIso (Presheaf.cechNerveSheafHomologyZeroAugmentation J
      (K.hom.app (Opposite.op (SimplexCategory.mk 0)))) :=
    Presheaf.isIso_cechNerveSheafHomologyZeroAugmentation J
      (K.hom.app (Opposite.op (SimplexCategory.mk 0))) h₀
  exact (@asIso _ _ _ _ _ hη).trans <| (@asIso _ _ _ _ _ hc).trans (@asIso _ _ _ _ _ hf)

end CategoryTheory.SimplicialObject.Augmented

namespace Stacks.CategoryTheory.Hypercovering

universe q w v u

open CategoryTheory CategoryTheory.Limits

/-- Presheaves of abelian groups valued in any universe at least as large as that of the site
admit sheafification, by transporting along a small model of the site. -/
theorem hasSheafify_addCommGrpCat.{t, v', u'} {C : Type u'} [Category.{v'} C]
    (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{max (max u' v') t} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max u' v' t, v', u'} J

/-- The universe lift on presheaves of sets, applied sectionwise.  It is used to carry the
presheaves of Tag 09VU, whose values live in `Type (max q w v)`, into the common universe
`max (max u v) (max q w)` of the statement. -/
noncomputable abbrev presheafULiftFunctor.{s, t, v', u'} {C : Type u'} [Category.{v'} C] :
    (Cᵒᵖ ⥤ Type s) ⥤ (Cᵒᵖ ⥤ Type (max s t)) :=
  (Functor.whiskeringRight Cᵒᵖ (Type s) (Type (max s t))).obj uliftFunctor.{t, s}

/-- A sectionwise universe lift of presheaves of sets preserves local surjectivity. -/
theorem isLocallySurjective_presheafULiftFunctor_map.{s, t, v', u'} {C : Type u'}
    [Category.{v'} C] (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ Type s} (f : F ⟶ G)
    [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J
      ((presheafULiftFunctor.{s, t} (C := C)).map f) where
  imageSieve_mem {X} s := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J f s.down)
    rintro Y g ⟨x, hx⟩
    exact ⟨ULift.up x, congrArg ULift.up hx⟩

/-- A sectionwise universe lift of presheaves of sets preserves fibre products. -/
theorem presheafULiftFunctor_preservesLimitsOfShape_walkingCospan.{s, t, v', u'}
    {C : Type u'} [Category.{v'} C] :
    PreservesLimitsOfShape WalkingCospan (presheafULiftFunctor.{s, t} (C := C)) :=
  inferInstance

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]

/-- Lifting the values of `associatedPresheafFunctor` at the universe `q` into
`Type (max (max u v) (max q w))` gives `associatedPresheafFunctor` at that universe. -/
noncomputable def associatedPresheafFunctorULiftIso :
    associatedPresheafFunctor.{q} (C := C) ⋙
        presheafULiftFunctor.{max q w v, max (max u v) (max q w)} (C := C) ≅
      associatedPresheafFunctor.{max (max u v) (max q w)} (C := C) := by
  let H := FormalCoproduct.uliftYoneda.{w} (C := C)
  let W₁ := (Functor.whiskeringRight Cᵒᵖ (Type (max w v))
      (Type (max q w v))).obj uliftFunctor.{q, max w v}
  let W₂ := presheafULiftFunctor.{max q w v, max (max u v) (max q w)} (C := C)
  let W₃ := (Functor.whiskeringRight Cᵒᵖ (Type (max w v))
      (Type (max (max u v) (max q w)))).obj
    uliftFunctor.{max (max u v) (max q w), max w v}
  have eW : W₁ ⋙ W₂ ≅ W₃ := by
    refine NatIso.ofComponents (fun P => ?_) ?_
    · exact (Functor.associator P _ _).trans
        (Functor.isoWhiskerLeft P
          (uliftFunctorCompIso.{q, max (max u v) (max q w), max w v}))
    · intro P Q f
      ext X x
      rfl
  change (H ⋙ W₁) ⋙ W₂ ≅ H ⋙ W₃
  exact (Functor.associator H W₁ W₂).trans (Functor.isoWhiskerLeft H eW)

/-- Lifting the values of `liftedPresheaf G` into `Type (max (max u v) (max q w))` gives the
sectionwise lift of `G` itself into that universe. -/
noncomputable def liftedPresheafULiftIso (G : Cᵒᵖ ⥤ Type q) :
    liftedPresheaf.{q, w} G ⋙ uliftFunctor.{max (max u v) (max q w), max q w v} ≅
      G ⋙ uliftFunctor.{max (max u v) (max q w), q} := by
  refine Functor.associator G _ _ ≪≫ Functor.isoWhiskerLeft G ?_
  exact uliftFunctorCompIso.{max w v, max (max u v) (max q w), q}

/-- The augmented simplicial presheaf underlying a hypercovering of a presheaf, with values in
`Type (max q w v)`. -/
noncomputable def HypercoveringOf.toAugmented (J : Pretopology C)
    (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G) :
    SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max q w v)) :=
  ⟨K.toSimplicialObject ⋙ associatedPresheafFunctor.{q}, liftedPresheaf.{q, w} G,
    K.augmentation⟩

/-- The augmented simplicial presheaf underlying a hypercovering of a presheaf, with its values
lifted into the common universe `max (max u v) (max q w)` of the statement. -/
noncomputable def HypercoveringOf.toAugmentedULift (J : Pretopology C)
    (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G) :
    SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max (max u v) (max q w))) :=
  (SimplicialObject.Augmented.whiskeringObj _ _
      (presheafULiftFunctor.{max q w v, max (max u v) (max q w)} (C := C))).obj
    (K.toAugmented.{q, w, v, u} J G)

/-- Condition (2) of a hypercovering of a presheaf, read as local surjectivity of the relation
map of the augmented simplicial presheaf `HypercoveringOf.toAugmented`. -/
theorem isLocallySurjective_edgesToFiberProduct_toAugmented (J : Pretopology C)
    (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G) :
    Presheaf.IsLocallySurjective J.toGrothendieck
      (SimplicialObject.Augmented.edgesToFiberProduct
        (K.toAugmented.{q, w, v, u} J G)) := by
  have : Presheaf.IsLocallySurjective J.toGrothendieck
      (oneMatchingMap (associatedSimplicialPresheaf.{q} K.toSimplicialObject)
        (liftedPresheaf.{q, w} G) K.augmentation) :=
    K.locallySurjective_one
  simpa [HypercoveringOf.toAugmented, SimplicialObject.Augmented.edgesToFiberProduct,
    oneMatchingMap]

/-- Condition (1) of a hypercovering of a presheaf, read as local surjectivity of the
degree-zero augmentation of `HypercoveringOf.toAugmentedULift`. -/
theorem isLocallySurjective_toAugmentedULift_hom_app_zero (J : Pretopology C)
    (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G) :
    Presheaf.IsLocallySurjective J.toGrothendieck
      ((K.toAugmentedULift.{q, w, v, u} J G).hom.app
        (Opposite.op (SimplexCategory.mk 0))) := by
  have : Presheaf.IsLocallySurjective J.toGrothendieck
      (K.augmentation.app (Opposite.op (SimplexCategory.mk 0))) :=
    K.locallySurjective_zero
  have h := isLocallySurjective_presheafULiftFunctor_map.{max q w v, max (max u v) (max q w)}
    (C := C) J.toGrothendieck (K.augmentation.app (Opposite.op (SimplexCategory.mk 0)))
  simpa [HypercoveringOf.toAugmentedULift, HypercoveringOf.toAugmented,
    SimplicialObject.Augmented.whiskeringObj] using h

/-- Condition (2) of a hypercovering of a presheaf, read as local surjectivity of the relation
map of the augmented simplicial presheaf `HypercoveringOf.toAugmentedULift`.

The relation map of the lift is the lift of the relation map followed by the comparison
`pullbackComparison` of the lifted fibre product with the fibre product of the lifts. -/
theorem isLocallySurjective_edgesToFiberProduct_toAugmentedULift (J : Pretopology C)
    (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G) :
    Presheaf.IsLocallySurjective J.toGrothendieck
      (SimplicialObject.Augmented.edgesToFiberProduct
        (K.toAugmentedULift.{q, w, v, u} J G)) := by
  let A := K.toAugmented.{q, w, v, u} J G
  let W := presheafULiftFunctor.{max q w v, max (max u v) (max q w)} (C := C)
  let f := A.hom.app (Opposite.op (SimplexCategory.mk 0))
  let edge := SimplicialObject.Augmented.edgesToFiberProduct A
  have key : ∀ {X} (d : _ ⟶ X) (p : pullback f f ⟶ X)
      (p' : pullback (W.map f) (W.map f) ⟶ W.obj X),
      edge ≫ p = d → pullbackComparison W f f ≫ p' = W.map p → W.map d = (W.map edge ≫
        pullbackComparison W f f) ≫ p' := by
    intro X d p p' hd hp
    rw [Category.assoc, hp, ← W.map_comp, hd]
  have h : @Eq (W.obj (A.left.obj (Opposite.op (SimplexCategory.mk 1))) ⟶
      pullback (W.map f) (W.map f))
      (SimplicialObject.Augmented.edgesToFiberProduct (K.toAugmentedULift.{q, w, v, u} J G))
      (W.map edge ≫ pullbackComparison W f f) := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans
        (key _ _ _ (pullback.lift_fst _ _ _) (pullbackComparison_comp_fst W f f))
    · exact (pullback.lift_snd _ _ _).trans
        (key _ _ _ (pullback.lift_snd _ _ _) (pullbackComparison_comp_snd W f f))
  have : Presheaf.IsLocallySurjective J.toGrothendieck edge :=
    isLocallySurjective_edgesToFiberProduct_toAugmented.{q, w, v, u} J G K
  have : Presheaf.IsLocallySurjective J.toGrothendieck (W.map edge) :=
    isLocallySurjective_presheafULiftFunctor_map.{max q w v, max (max u v) (max q w)}
    (C := C) J.toGrothendieck edge
  have := Presheaf.isLocallySurjective_of_iso J.toGrothendieck (pullbackComparison W f f)
  have hc := Presheaf.isLocallySurjective_comp J.toGrothendieck (W.map edge)
    (pullbackComparison W f f)
  rw [h]
  exact hc

/-- The degree-zero cohomology of the Hom complex of Tag 01GX is the group of morphisms out of
the degree-zero homology sheaf of the associated simplicial presheaf.  The additive Yoneda
functor preserves the relevant left homology data because the incoming differential of the
opposite complex vanishes in degree zero. -/
noncomputable def homFreeAbelianSheafComplexHomologyZeroIso
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) :
    (SemiRepresentable.homFreeAbelianSheafComplex.{q, w, v, u} J K F).homology 0 ≅
      AddCommGrpCat.of
        (SimplicialObject.sheafHomology J
          (associatedSimplicialPresheaf.{max (max u v) (max q w)} K) 0 ⟶ F) := by
  let S := (SimplicialObject.freeAbelianSheafComplexFunctor J).obj
    (associatedSimplicialPresheaf.{max (max u v) (max q w)} K)
  let Y := preadditiveYonedaObj F
  let M := ((Y.mapHomologicalComplex (ComplexShape.up ℕ)).obj S.op)
  let Forget := forget₂ (ModuleCat (End F)) AddCommGrpCat
  let U := ((Forget.mapHomologicalComplex (ComplexShape.up ℕ)).obj M)
  change U.homology 0 ≅ AddCommGrpCat.of (S.homology 0 ⟶ F)
  have : PreservesLimits Y := by infer_instance
  have : Functor.PreservesZeroMorphisms Y := by infer_instance
  have hf : (S.op.sc 0).f = 0 := by
    simp only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rfl
  have hpres (h : (S.op.sc 0).LeftHomologyData) : h.IsPreservedBy Y := by
    refine ⟨?_, ?_⟩
    · infer_instance
    · have hzero : h.f' = 0 := by
        apply (cancel_mono h.i).1
        rw [h.f'_i, hf]
        simp
      rw [hzero]
      infer_instance
  have : Y.PreservesLeftHomologyOf (S.op.sc 0) := ⟨hpres⟩
  let eU : U.homology 0 ≅ Forget.obj (M.homology 0) := by
    calc
      U.homology 0 ≅ U.cycles 0 := (CochainComplex.isoHomologyπ₀ U).symm
      _ ≅ Forget.obj (M.cycles 0) := by
        haveI : Forget.PreservesHomology := Functor.preservesHomologyOfExact Forget
        change ((M.sc 0).map Forget).cycles ≅ Forget.obj (M.sc 0).cycles
        exact (M.sc 0).mapCyclesIso Forget
      _ ≅ Forget.obj (M.homology 0) := Forget.mapIso (CochainComplex.isoHomologyπ₀ M)
  let eM : M.homology 0 ≅ Y.obj (Opposite.op (S.homology 0)) := by
    calc
      M.homology 0 ≅ M.cycles 0 := (CochainComplex.isoHomologyπ₀ M).symm
      _ ≅ Y.obj (S.op.cycles 0) := by
        change ((S.op.sc 0).map Y).cycles ≅ Y.obj ((S.op.sc 0).cycles)
        exact (S.op.sc 0).mapCyclesIso Y
      _ ≅ Y.obj (S.op.homology 0) := Y.mapIso (CochainComplex.isoHomologyπ₀ S.op)
      _ ≅ Y.obj (Opposite.op (S.homology 0)) := Y.mapIso (S.homologyOp 0)
  exact eU.trans (Forget.mapIso eM)

/-- The `p`-th Čech cohomology group of a hypercovering of a presheaf with coefficients in a
sheaf of abelian groups, that is the cohomology of the alternating coface complex obtained by
evaluating the sheaf on the underlying simplicial semi-representable object. -/
@[sga "4 V 2.4.4" "more general"]
noncomputable abbrev cechCohomology (J : Pretopology C)
    (G : Functor Cᵒᵖ (Type q)) (K : HypercoveringOf.{q, w} J G)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p : ℕ) :
    AddCommGrpCat.{max (max u v) (max q w)} :=
  ((FormalCoproduct.cochainComplexFunctor K.toSimplicialObject).obj F.obj).homology p

/-- Degree-zero cohomology of a presheaf of sets `G` with coefficients in a sheaf of abelian
groups `F`.

By the pointwise free–forgetful adjunction, its underlying group consists of the natural
transformations from `G` to the underlying presheaf of `F`. -/
noncomputable abbrev presheafCohomologyZero (J : Pretopology C) (G : Functor Cᵒᵖ (Type q))
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    AddCommGrpCat.{max (max u v) (max q w)} :=
  AddCommGrpCat.of
    ((G ⋙ uliftFunctor.{max (max u v) (max q w)} ⋙ AddCommGrpCat.free) ⟶ F.obj)

/-- **Stacks Project, Tag 09VV.** The isomorphism identifying the degree-zero Čech cohomology of
a hypercovering of a presheaf with the degree-zero cohomology of that presheaf.

It is the composite of the comparison of the complex of sections with the Hom complex (Tag 01GX),
the identification of the degree-zero cohomology of the latter with `Hom` out of degree-zero
homology, the degree-zero acyclicity of a locally covering augmented simplicial presheaf
(Tag 01GE), and the sheafification adjunction. -/
noncomputable def cechCohomologyZeroIso (J : Pretopology C)
    (G : Functor Cᵒᵖ (Type q)) (K : HypercoveringOf.{q, w} J G)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    cechCohomology J G K F 0 ≅ presheafCohomologyZero J G F := by
  let J' := J.toGrothendieck
  letI : HasSheafify J' AddCommGrpCat.{max (max u v) (max q w)} :=
    hasSheafify_addCommGrpCat.{max q w} J'
  let A := K.toAugmentedULift.{q, w, v, u} J G
  have hzero := isLocallySurjective_toAugmentedULift_hom_app_zero.{q, w, v, u} J G K
  have hone := isLocallySurjective_edgesToFiberProduct_toAugmentedULift.{q, w, v, u} J G K
  let hAug := SimplicialObject.Augmented.sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees
    J' A hzero hone
  have hAssociated : A.left ≅
      associatedSimplicialPresheaf.{max (max u v) (max q w)} K.toSimplicialObject := by
    change (K.toSimplicialObject ⋙ associatedPresheafFunctor.{q} ⋙
        presheafULiftFunctor.{max q w v, max (max u v) (max q w)}) ≅
      (K.toSimplicialObject ⋙ associatedPresheafFunctor.{max (max u v) (max q w)})
    exact Functor.isoWhiskerLeft K.toSimplicialObject
      (associatedPresheafFunctorULiftIso.{q, w, v, u} (C := C))
  have hLifted : A.right ≅ (G ⋙ uliftFunctor.{max (max u v) (max q w)}) :=
    liftedPresheafULiftIso.{q, w, v, u} (C := C) G
  let eHomology := (SimplicialObject.sheafHomologyFunctor J' 0).mapIso hAssociated
  let Y := preadditiveYonedaObj F
  let Forget := forget₂ (ModuleCat (End F)) AddCommGrpCat
  have eSections : cechCohomology J G K F 0 ≅
      (SemiRepresentable.homFreeAbelianSheafComplex.{q, w, v, u}
        J' K.toSimplicialObject F).homology 0 := by
    change (SemiRepresentable.sectionsComplex.{q, w, v, u}
        J' K.toSimplicialObject F).homology 0 ≅ _
    exact (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) 0).mapIso
      (SemiRepresentable.sectionsComplexIsoHomFreeAbelianSheafComplex.{q, w, v, u}
        J' K.toSimplicialObject F)
  let eHomFree := homFreeAbelianSheafComplexHomologyZeroIso.{q, w, v, u} J'
      K.toSimplicialObject F
  have eAssociatedHom :
      AddCommGrpCat.of
          (SimplicialObject.sheafHomology J'
            (associatedSimplicialPresheaf.{max (max u v) (max q w)}
              K.toSimplicialObject) 0 ⟶ F) ≅
        AddCommGrpCat.of (SimplicialObject.sheafHomology J' A.left 0 ⟶ F) := by
    change Forget.obj (Y.obj (Opposite.op
        (SimplicialObject.sheafHomology J'
          (associatedSimplicialPresheaf.{max (max u v) (max q w)}
            K.toSimplicialObject) 0))) ≅
      Forget.obj (Y.obj (Opposite.op
        (SimplicialObject.sheafHomology J' A.left 0)))
    exact Forget.mapIso (Y.mapIso eHomology.op)
  have eAugHom :
      AddCommGrpCat.of (SimplicialObject.sheafHomology J' A.left 0 ⟶ F) ≅
        AddCommGrpCat.of
          ((presheafToSheaf J' AddCommGrpCat.{max (max u v) (max q w)}).obj
            (A.right ⋙ AddCommGrpCat.free) ⟶ F) := by
    change Forget.obj (Y.obj (Opposite.op
        (SimplicialObject.sheafHomology J' A.left 0))) ≅
      Forget.obj (Y.obj (Opposite.op
        ((presheafToSheaf J' AddCommGrpCat.{max (max u v) (max q w)}).obj
          (A.right ⋙ AddCommGrpCat.free))))
    exact Forget.mapIso (Y.mapIso hAug.op.symm)
  let P := G ⋙ uliftFunctor.{max (max u v) (max q w)} ⋙ AddCommGrpCat.free
  let eSheafify :=
    (presheafToSheaf J' AddCommGrpCat.{max (max u v) (max q w)}).mapIso
      (Functor.isoWhiskerRight hLifted AddCommGrpCat.free)
  have eLiftHom :
      AddCommGrpCat.of
          ((presheafToSheaf J' AddCommGrpCat.{max (max u v) (max q w)}).obj
            (A.right ⋙ AddCommGrpCat.free) ⟶ F) ≅
        AddCommGrpCat.of
          ((presheafToSheaf J' AddCommGrpCat.{max (max u v) (max q w)}).obj P ⟶ F) := by
    change Forget.obj (Y.obj (Opposite.op
        ((presheafToSheaf J' AddCommGrpCat.{max (max u v) (max q w)}).obj
          (A.right ⋙ AddCommGrpCat.free)))) ≅
      Forget.obj (Y.obj (Opposite.op
        ((presheafToSheaf J' AddCommGrpCat.{max (max u v) (max q w)}).obj P)))
    exact Forget.mapIso (Y.mapIso eSheafify.op.symm)
  have eAdjunction :
      AddCommGrpCat.of
        ((presheafToSheaf J' AddCommGrpCat.{max (max u v) (max q w)}).obj P ⟶ F) ≅
        presheafCohomologyZero J G F := by
    change AddCommGrpCat.of
        ((presheafToSheaf J' AddCommGrpCat.{max (max u v) (max q w)}).obj P ⟶ F) ≅
      AddCommGrpCat.of (P ⟶ F.obj)
    exact ((sheafificationAdjunction J'
      AddCommGrpCat.{max (max u v) (max q w)}).homAddEquiv P F).toAddCommGrpIso
  exact eSections.trans (eHomFree.trans
    (eAssociatedHom.trans (eAugHom.trans (eLiftHom.trans eAdjunction))))

/-- **Stacks Project, Tag 09VV.** Degree-zero Čech cohomology of a hypercovering of a presheaf is
the degree-zero cohomology of that presheaf with coefficients in the given sheaf of abelian
groups.

The source asserts an identification; the isomorphism realising it is `cechCohomologyZeroIso`,
of which this is the existence statement. -/
@[stacks 09VV]
theorem nonempty_cechCohomologyZeroIso (J : Pretopology C)
    (G : Functor Cᵒᵖ (Type q)) (K : HypercoveringOf.{q, w} J G)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    Nonempty (cechCohomology J G K F 0 ≅ presheafCohomologyZero J G F) :=
  ⟨cechCohomologyZeroIso J G K F⟩

end Stacks.CategoryTheory.Hypercovering

end
