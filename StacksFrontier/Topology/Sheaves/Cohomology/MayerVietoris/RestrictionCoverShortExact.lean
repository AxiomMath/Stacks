module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.Topology.Sheaves.MayerVietoris
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# The restriction-cover short exact sequence of an injective sheaf of modules

Let `X` be a topological space, `O` a sheaf of rings on `X`, and `U`, `V` two opens with
`U ⊔ V = ⊤`.  Write `restrictPush O U` for restriction to `U` followed by pushforward back,
an endofunctor of `Mod(O)` whose sections over an open `W` are the sections of the argument
over `W ⊓ U`.  This file proves that for an *injective* sheaf of modules `I` the
Mayer--Vietoris short complex

`0 ⟶ I ⟶ (restrictPush O U) I ⊞ (restrictPush O V) I ⟶ (restrictPush O (U ⊓ V)) I ⟶ 0`

is short exact.  This is the statement the Stacks proof of Tag 01EC refers to as having been
"shown in the proof of Lemma 01EB", and it is the hypothesis that
`CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives` takes.

## Main definitions

* `Stacks.Cohomology.RestrictionCover.restrictPush`: restriction to an open followed by
  pushforward.
* `Stacks.Cohomology.RestrictionCover.restrictPushTransition`: the transition map
  `restrictPush O U ⟶ restrictPush O T` attached to `T ≤ U`, which on sections over `W` is the
  restriction map of the argument from `W ⊓ U` to `W ⊓ T`.
* `Stacks.Cohomology.RestrictionCover.restrictionCoverMiddle`: the middle term of the short
  complex, the pointwise biproduct of `restrictPush O U` and `restrictPush O V`.
* `Stacks.Cohomology.RestrictionCover.restrictionCoverFirst` and
  `Stacks.Cohomology.RestrictionCover.restrictionCoverSecond`: the two maps of the short
  complex, as natural transformations of endofunctors of `Mod(O)`.

## Main results

* `Stacks.Cohomology.RestrictionCover.restrictPushTransition_app_val_app`: the transition map
  is the restriction map on sections.
* `Stacks.Cohomology.RestrictionCover.restrictionCoverFirst_comp_second`: the two maps compose
  to zero.
* `Stacks.Cohomology.RestrictionCover.restrictionCoverShortExact`: short exactness of the
  complex obtained by applying the three functors degreewise to a cochain complex of
  injectives.
* `Stacks.Cohomology.RestrictionCover.restrictionCoverShortExact_object`: **short exactness at
  an injective sheaf of modules.**

## Implementation notes

`restrictPush O U` is `jStar U O ⋙ jPush U O`, a composite of two pushforwards, along the
functors `Opens U ⥤ Opens X` and `Opens X ⥤ Opens U`; `restrictPushOpenIntersectionIso`
rewrites it as a single pushforward along their composite `W ↦ W ⊓ U`, which is what makes the
transition map available as a `CategoryTheory.SheafOfModules.pushforwardNatTrans` and
computable on sections.

Short exactness is proved first on sections, where it is exactly the sheaf condition for the
cover of `W` by `W ⊓ U` and `W ⊓ V` (`sheafSections_ext_cover` and `sheafSections_glue_cover`,
both instances of `Opens.mayerVietorisSquare`) together with surjectivity of the restriction
maps of an injective sheaf, which is Stacks 01EA.  It is then transported to sheaves of
modules by joint faithfulness of the evaluation functors on presheaves of abelian groups,
which reflects short exactness.

The statement at an object is deduced from the statement for a cochain complex of injectives,
applied to the complex concentrated in degree zero.  Stating it for complexes first costs
nothing, and is the form the derived-category assertion of Tag 08BV needs.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules

universe u

namespace Stacks.Cohomology.RestrictionCover

attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Restriction to `U`, followed by pushforward along the inclusion `U → X`.  Its sections
over an open `W` are the sections of the argument over `W ⊓ U`. -/
public noncomputable abbrev restrictPush (U : Opens X) :
    SheafOfModules.{u} O ⥤ SheafOfModules.{u} O :=
  jStar U O ⋙ jPush U O

/-- Restriction followed by pushforward is additive: both factors are right adjoints. -/
public noncomputable instance restrictPush_additive (U : Opens X) :
    (restrictPush O U).Additive := by
  let _ : (jStar U O).IsRightAdjoint := (jShriekAdjunction U O).isRightAdjoint
  let _ : (jPush U O).IsRightAdjoint := (jStarAdjunction U O).isRightAdjoint
  let _ : (jStar U O).Additive := by
    apply Functor.additive_of_preserves_binary_products
  let _ : (jPush U O).Additive := by
    apply Functor.additive_of_preserves_binary_products
  infer_instance

/-! ### The overlap maps -/

/-- The functor `W ↦ W ⊓ U` on opens of `X`, written as the preimage along the inclusion of
`U` followed by the image.  This is the functor along which `restrictPush O U` is a single
pushforward. -/
public noncomputable abbrev openIntersection (U : Opens X) : Opens X ⥤ Opens X :=
  Opens.map U.inclusion' ⋙ TopCat.Presheaf.imF U

/-- The comparison of structure sheaves along `openIntersection U`: the restriction of `O` to
`U` pushed back, which is `O` again on `W ⊓ U`. -/
public noncomputable def openIntersectionRingMap (U : Opens X) :
  O ⟶ ((openIntersection U).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)).obj O :=
  toPushRing U O ≫
    ((Opens.map U.inclusion').sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (Usp U))).map (𝟙 (resRing U O))

/-- `restrictPush O U` is a single pushforward, along the functor `W ↦ W ⊓ U`.  This is the
spelling in which its transition maps are available and computable on sections. -/
public noncomputable def restrictPushOpenIntersectionIso (U : Opens X) :
    restrictPush O U ≅ SheafOfModules.pushforward (openIntersectionRingMap O U) := by
  dsimp [restrictPush, jStar, jPush, openIntersectionRingMap, openIntersection]
  exact SheafOfModules.pushforwardComp (toPushRing U O) (𝟙 (resRing U O))

/-- For `T ≤ U`, the inclusion `W ⊓ T ≤ W ⊓ U` as a morphism of the functors
`openIntersection T ⟶ openIntersection U`. -/
public noncomputable def openIntersectionToOpenIntersection
    (T U : Opens X) (hTU : T ≤ U) :
    openIntersection T ⟶ openIntersection U where
  app W := homOfLE (by
    change T.isOpenEmbedding.functor.obj ((Opens.map T.inclusion').obj W) ≤
      U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj W)
    rw [Opens.functor_map_eq_inf, Opens.functor_map_eq_inf]
    exact inf_le_inf_left _ hTU)
  naturality _ _ _ := Subsingleton.elim _ _

/-- The transition map `restrictPush O U ⟶ restrictPush O T` attached to an inclusion
`T ≤ U` of opens.  On sections over `W` it is the restriction map of the argument from
`W ⊓ U` to `W ⊓ T`. -/
public noncomputable def restrictPushTransition (T U : Opens X) (hTU : T ≤ U) :
    restrictPush O U ⟶ restrictPush O T := by
  let α := openIntersectionToOpenIntersection T U hTU
  let q := SheafOfModules.pushforwardNatTrans
    (openIntersectionRingMap O U) α
  let e := restrictPushOpenIntersectionIso O U
  let eT := restrictPushOpenIntersectionIso O T
  exact e.hom ≫ q ≫ (SheafOfModules.pushforwardCongr (by
    ext W : 3
    apply RingCat.hom_ext
    apply RingHom.ext
    intro x
    let cU := U.isOpenEmbedding.isOpenMap.adjunction.counit.app W.unop
    let cT := T.isOpenEmbedding.isOpenMap.adjunction.counit.app W.unop
    have hc : α.app W.unop ≫ cU = cT := Subsingleton.elim _ _
    change ((O.obj.map cU.op ≫ O.obj.map (α.app W.unop).op).hom) x =
      (O.obj.map cT.op).hom x
    rw [← Functor.map_comp, ← op_comp, hc])).hom ≫ eT.inv

/-- The transition map is the restriction map on sections. -/
public lemma restrictPushTransition_app_val_app
    (T U : Opens X) (hTU : T ≤ U) (M : SheafOfModules.{u} O)
    (W : (Opens X)ᵒᵖ) (x : ((restrictPush O U).obj M).val.obj W) :
    (((restrictPushTransition O T U hTU).app M).val.app W) x =
      (M.val.map ((openIntersectionToOpenIntersection T U hTU).app W.unop).op).hom x := by
  simp [restrictPushTransition, restrictPushOpenIntersectionIso]
  rfl

/-- The unit of restriction and pushforward is the restriction map on sections: over an open
`W` it sends a section of `M` over `W` to its restriction to `W ⊓ U`.  This holds by `rfl`. -/
public lemma jStarAdjunction_unit_app_val_app
    (U : Opens X) (M : SheafOfModules.{u} O) (W : (Opens X)ᵒᵖ)
    (x : M.val.obj W) :
    (((jStarAdjunction U O).unit.app M).val.app W) x =
      M.val.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W.unop).op x := by
  dsimp only [jStarAdjunction, jStar, jPush]
  rfl

/-- Restricting to `U` and then further to `T ≤ U` is restricting to `T`: the unit of `U`
followed by the transition map is the unit of `T`. -/
public lemma restrictPushTransition_unit (T U : Opens X) (hTU : T ≤ U) :
    (jStarAdjunction U O).unit ≫ restrictPushTransition O T U hTU =
  (jStarAdjunction T O).unit := by
  ext M W x
  change (((jStarAdjunction U O).unit.app M).val.app W ≫
      ((restrictPushTransition O T U hTU).app M).val.app W) x =
    (((jStarAdjunction T O).unit.app M).val.app W) x
  rw [ModuleCat.comp_apply, restrictPushTransition_app_val_app]
  let cU := U.isOpenEmbedding.isOpenMap.adjunction.counit.app W.unop
  let cT := T.isOpenEmbedding.isOpenMap.adjunction.counit.app W.unop
  let α := openIntersectionToOpenIntersection T U hTU
  have hc : α.app W.unop ≫ cU = cT := Subsingleton.elim _ _
  rw [jStarAdjunction_unit_app_val_app, jStarAdjunction_unit_app_val_app,
    ← M.val.map_comp_apply cU.op (α.app W.unop).op x, ← op_comp, hc]

/-- The middle term of the Mayer--Vietoris short complex: the pointwise biproduct of
`restrictPush O U` and `restrictPush O V`.  It is written out rather than taken as a
biproduct in the functor category so that its action on morphisms is literally
`CategoryTheory.Limits.biprod.map`. -/
public noncomputable def restrictionCoverMiddle (U V : Opens X) :
    SheafOfModules.{u} O ⥤ SheafOfModules.{u} O where
  obj M := (restrictPush O U).obj M ⊞ (restrictPush O V).obj M
  map f := biprod.map ((restrictPush O U).map f) ((restrictPush O V).map f)
  map_id M := by
    apply biprod.hom_ext <;> simp
  map_comp f g := by
    apply biprod.hom_ext <;> simp [Functor.map_comp]

/-- The middle term of the short complex is additive. -/
public noncomputable instance restrictionCoverMiddle_additive (U V : Opens X) :
    (restrictionCoverMiddle O U V).Additive := ⟨by
  intro A B f g
  change biprod.map ((restrictPush O U).map (f + g)) ((restrictPush O V).map (f + g)) =
    biprod.map ((restrictPush O U).map f) ((restrictPush O V).map f) +
      biprod.map ((restrictPush O U).map g) ((restrictPush O V).map g)
  rw [Functor.map_add, Functor.map_add]
  apply biprod.hom_ext <;> simp [Preadditive.comp_add]⟩

/-- The first map of the Mayer--Vietoris short complex: the pair of the two units, restricting
a sheaf of modules to `U` and to `V`. -/
public noncomputable def restrictionCoverFirst (U V : Opens X) :
    (CategoryTheory.Functor.id (SheafOfModules.{u} O)) ⟶
      restrictionCoverMiddle O U V where
  app M := biprod.lift ((jStarAdjunction U O).unit.app M)
    ((jStarAdjunction V O).unit.app M)
  naturality := by
    intro A B f
    apply biprod.hom_ext
    · simp [restrictionCoverMiddle, Category.assoc]
    · simp [restrictionCoverMiddle, Category.assoc]

/-- The second map of the Mayer--Vietoris short complex: the difference of the two transition
maps to the intersection. -/
public noncomputable def restrictionCoverSecond (U V : Opens X) :
    restrictionCoverMiddle O U V ⟶ restrictPush O (U ⊓ V) where
  app M := biprod.desc ((restrictPushTransition O (U ⊓ V) U inf_le_left).app M)
    (-((restrictPushTransition O (U ⊓ V) V inf_le_right).app M))
  naturality := by
    intro A B f
    apply biprod.hom_ext'
    · simpa [restrictionCoverMiddle, Category.assoc] using
        (restrictPushTransition O (U ⊓ V) U inf_le_left).naturality f
    · simpa [restrictionCoverMiddle, Category.assoc,
        Preadditive.neg_comp, Preadditive.comp_neg] using
        congrArg Neg.neg
          ((restrictPushTransition O (U ⊓ V) V inf_le_right).naturality f)

/-- The two maps of the short complex compose to zero: both transition maps take the unit of
`U`, respectively of `V`, to the unit of `U ⊓ V`, so their difference vanishes. -/
public lemma restrictionCoverFirst_comp_second (U V : Opens X) :
    restrictionCoverFirst O U V ≫ restrictionCoverSecond O U V = 0 := by
  apply NatTrans.ext
  funext M
  change biprod.lift ((jStarAdjunction U O).unit.app M)
      ((jStarAdjunction V O).unit.app M) ≫
      biprod.desc ((restrictPushTransition O (U ⊓ V) U inf_le_left).app M)
        (-((restrictPushTransition O (U ⊓ V) V inf_le_right).app M)) = 0
  rw [biprod.lift_desc]
  have hU : (jStarAdjunction U O).unit.app M ≫
      (restrictPushTransition O (U ⊓ V) U inf_le_left).app M =
      (jStarAdjunction (U ⊓ V) O).unit.app M :=
    NatTrans.congr_app (restrictPushTransition_unit O (U ⊓ V) U inf_le_left) M
  have hV : (jStarAdjunction V O).unit.app M ≫
      (restrictPushTransition O (U ⊓ V) V inf_le_right).app M =
      (jStarAdjunction (U ⊓ V) O).unit.app M :=
    NatTrans.congr_app (restrictPushTransition_unit O (U ⊓ V) V inf_le_right) M
  rw [Preadditive.comp_neg, hU, hV, add_neg_cancel]

/-- Evaluating a sheaf of modules on sections over a fixed open is additive. -/
public noncomputable instance restrictionCoverEvaluation_additive (W : Opens X) :
    (SheafOfModules.evaluation O (Opposite.op W)).Additive := by
  constructor
  intro A B f g
  ext s
  rfl

/-- Evaluating a sheaf of modules on sections over a fixed open preserves zero morphisms. -/
public noncomputable instance restrictionCoverEvaluation_preservesZeroMorphisms
    (W : Opens X) :
    (SheafOfModules.evaluation O (Opposite.op W)).PreservesZeroMorphisms :=
  inferInstance

/-- Two sections of a sheaf of types over `A` and over `B` which agree on `A ⊓ B` glue to a
section over `A ⊔ B`.  This is the sheaf condition for `Opens.mayerVietorisSquare`. -/
public lemma sheafSections_glue (F : TopCat.Presheaf (Type u) X)
    (hF : F.IsSheaf) (A B : Opens X) (xA : F.obj (Opposite.op A))
    (xB : F.obj (Opposite.op B))
    (hAB : F.map (homOfLE inf_le_left).op xA =
      F.map (homOfLE inf_le_right).op xB) :
    ∃ x : F.obj (Opposite.op (A ⊔ B)),
      F.map (homOfLE le_sup_left).op x = xA ∧
      F.map (homOfLE le_sup_right).op x = xB := by
  have hs := (Opens.mayerVietorisSquare A B).sheafCondition_of_sheaf ⟨F, hF⟩
  exact ⟨hs.glue xA xB hAB, hs.map_f₂₄_op_glue xA xB hAB, hs.map_f₃₄_op_glue xA xB hAB⟩

/-- `sheafSections_glue` for a pair of opens presented as a cover `A ⊔ B = W` of a third. -/
public lemma sheafSections_glue_cover (F : TopCat.Presheaf (Type u) X)
    (hF : F.IsSheaf) (A B W : Opens X) (hcover : A ⊔ B = W)
    (xA : F.obj (Opposite.op A)) (xB : F.obj (Opposite.op B))
    (hAB : F.map (homOfLE inf_le_left).op xA =
      F.map (homOfLE inf_le_right).op xB) :
    ∃ x : F.obj (Opposite.op W),
      F.map (homOfLE (le_sup_left.trans (le_of_eq hcover))).op x = xA ∧
      F.map (homOfLE (le_sup_right.trans (le_of_eq hcover))).op x = xB := by
  obtain ⟨x, hxA, hxB⟩ := sheafSections_glue F hF A B xA xB hAB
  subst W
  exact ⟨x, by simpa using hxA, by simpa using hxB⟩

/-- Two sections of a sheaf of types over `W` which agree on `A` and on `B` agree, when
`A ⊔ B = W`.  This is the locality half of the sheaf condition for
`Opens.mayerVietorisSquare`. -/
public lemma sheafSections_ext_cover (F : TopCat.Presheaf (Type u) X)
    (hF : F.IsSheaf) (A B W : Opens X) (hcover : A ⊔ B = W)
    (x y : F.obj (Opposite.op W))
    (hA : F.map (homOfLE (le_sup_left.trans (le_of_eq hcover))).op x =
      F.map (homOfLE (le_sup_left.trans (le_of_eq hcover))).op y)
    (hB : F.map (homOfLE (le_sup_right.trans (le_of_eq hcover))).op x =
      F.map (homOfLE (le_sup_right.trans (le_of_eq hcover))).op y) : x = y := by
  subst W
  exact ((Opens.mayerVietorisSquare A B).sheafCondition_of_sheaf ⟨F, hF⟩).ext hA hB

/-- If `U ⊔ V = ⊤` then `W ⊓ U` and `W ⊓ V` cover `W`. -/
public lemma openIntersection_cover (U V W : Opens X) (hUV : U ⊔ V = ⊤) :
    (openIntersection U).obj W ⊔ (openIntersection V).obj W = W := by
  have hA : (openIntersection U).obj W = W ⊓ U := by simp [openIntersection]
  have hB : (openIntersection V).obj W = W ⊓ V := by simp [openIntersection]
  rw [hA, hB]
  calc
    (W ⊓ U) ⊔ (W ⊓ V) = (U ⊓ W) ⊔ (V ⊓ W) := by simp [inf_comm]
    _ = (U ⊔ V) ⊓ W := (inf_sup_right U V W).symm
    _ = W := by rw [hUV, top_inf_eq]

/-- The Mayer--Vietoris short complex of a cochain complex of sheaves of modules, obtained by
applying the three functors degreewise. -/
public noncomputable def restrictionCoverShortComplex (U V : Opens X)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    ShortComplex (CochainComplex (SheafOfModules.{u} O) ℤ) := by
  let c := ComplexShape.up ℤ
  let F₂ := restrictionCoverMiddle O U V
  let F₃ := restrictPush O (U ⊓ V)
  let : F₃.Additive := by infer_instance
  refine {
    X₁ := K
    X₂ := (F₂.mapHomologicalComplex c).obj K
    X₃ := (F₃.mapHomologicalComplex c).obj K
    f := (NatTrans.mapHomologicalComplex (restrictionCoverFirst O U V) c).app K
    g := (NatTrans.mapHomologicalComplex (restrictionCoverSecond O U V) c).app K
    zero := ?_ }
  rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
    restrictionCoverFirst_comp_second]
  ext n
  simp [F₃]

/-- The first map followed by the first projection is the unit of `U`. -/
private theorem restrictionCoverFirst_app_comp_fst (U V : Opens X) (M : SheafOfModules.{u} O) :
    (restrictionCoverFirst O U V).app M ≫
      (biprod.fst : (restrictPush O U).obj M ⊞ (restrictPush O V).obj M ⟶
        (restrictPush O U).obj M) = (jStarAdjunction U O).unit.app M :=
  biprod.lift_fst _ _

/-- The first map followed by the second projection is the unit of `V`. -/
private theorem restrictionCoverFirst_app_comp_snd (U V : Opens X) (M : SheafOfModules.{u} O) :
    (restrictionCoverFirst O U V).app M ≫
      (biprod.snd : (restrictPush O U).obj M ⊞ (restrictPush O V).obj M ⟶
        (restrictPush O V).obj M) = (jStarAdjunction V O).unit.app M :=
  biprod.lift_snd _ _

/-- The presheaf of sets of sections of a sheaf of modules is a sheaf. -/
private theorem isSheaf_sections (M : SheafOfModules.{u} O) :
    TopCat.Presheaf.IsSheaf (((SheafOfModules.toSheaf O).obj M).obj ⋙ forget AddCommGrpCat) :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mp
    ((SheafOfModules.toSheaf O).obj M).property

/-- The unit of restriction and pushforward is, over `W`, the restriction map to `W ⊓ U`. -/
private theorem jStarAdjunction_unit_app_val_app_eq (U : Opens X) (M : SheafOfModules.{u} O)
    (W : Opens X) (h : (openIntersection U).obj W ≤ W) (x : M.val.obj (Opposite.op W)) :
    (((jStarAdjunction U O).unit.app M).val.app (Opposite.op W)) x =
      M.val.map (homOfLE h).op x := by
  rw [jStarAdjunction_unit_app_val_app]
  congr 1

/-- Short exactness of the Mayer--Vietoris short complex on sections over an open `W`, in each
degree of a cochain complex of injectives.  Injectivity of the first map and exactness in
the middle are the two halves of the sheaf condition for the cover of `W` by `W ⊓ U` and
`W ⊓ V`; surjectivity of the second map is Stacks 01EA. -/
public lemma restrictionCoverDegreeShortExact (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (K : CochainComplex (SheafOfModules.{u} O) ℤ)
    [∀ n, Injective (K.X n)] (n : ℤ) (W : Opens X) :
    ((((restrictionCoverShortComplex O U V K).map
      (HomologicalComplex.eval (SheafOfModules.{u} O) (ComplexShape.up ℤ) n)).map
      (SheafOfModules.evaluation O (Opposite.op W)))).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    intro x
    constructor
    · intro hx
      let F := SheafOfModules.evaluation O (Opposite.op W)
      let A := (restrictPush O U).obj (K.X n)
      let B := (restrictPush O V).obj (K.X n)
      change F.obj (A ⊞ B) at x
      let xU : A.val.obj (Opposite.op W) := (F.map (biprod.fst : A ⊞ B ⟶ A)).hom x
      let xV : B.val.obj (Opposite.op W) := (F.map (biprod.snd : A ⊞ B ⟶ B)).hom x
      have htot := congrArg F.map (biprod.total (X := A) (Y := B))
      simp only [Functor.map_add, Functor.map_comp] at htot
      have hxrep : x = (F.map (biprod.inl : A ⟶ A ⊞ B)).hom xU +
          (F.map (biprod.inr : B ⟶ A ⊞ B)).hom xV := by
        simpa [xU, xV, ModuleCat.comp_apply, LinearMap.id_apply] using
          (congrArg (fun f : F.obj (A ⊞ B) ⟶ F.obj (A ⊞ B) => f.hom x) htot).symm
      rw [hxrep] at hx
      let τU := (restrictPushTransition O (U ⊓ V) U inf_le_left).app (K.X n)
      let τV := (restrictPushTransition O (U ⊓ V) V inf_le_right).app (K.X n)
      have hUcomp : F.map (biprod.inl : A ⟶ A ⊞ B) ≫
          F.map (biprod.desc τU (-τV)) = F.map τU := by
        rw [← Functor.map_comp, biprod.inl_desc]
      have hVcomp : F.map (biprod.inr : B ⟶ A ⊞ B) ≫
          F.map (biprod.desc τU (-τV)) = F.map (-τV) := by
        rw [← Functor.map_comp, biprod.inr_desc]
      change (F.map (biprod.desc τU (-τV))).hom
          ((F.map (biprod.inl : A ⟶ A ⊞ B)).hom xU +
            (F.map (biprod.inr : B ⟶ A ⊞ B)).hom xV) = 0 at hx
      simp only [map_add] at hx
      change (F.map (biprod.inl : A ⟶ A ⊞ B) ≫
            F.map (biprod.desc τU (-τV))).hom xU +
          (F.map (biprod.inr : B ⟶ A ⊞ B) ≫
            F.map (biprod.desc τU (-τV))).hom xV = 0 at hx
      rw [hUcomp, hVcomp, Functor.map_neg] at hx
      have hmatch : (F.map τU).hom xU = (F.map τV).hom xV := by
        have hh := add_eq_zero_iff_eq_neg.mp hx
        change (F.map τU).hom xU = (-( -(F.map τV).hom)) xV at hh
        rwa [neg_neg] at hh
      change ((restrictPushTransition O (U ⊓ V) U inf_le_left).app (K.X n)).val.app
          (Opposite.op W) xU =
        ((restrictPushTransition O (U ⊓ V) V inf_le_right).app (K.X n)).val.app
          (Opposite.op W) xV at hmatch
      rw [restrictPushTransition_app_val_app,
        restrictPushTransition_app_val_app] at hmatch
      let M := K.X n
      let F : TopCat.Presheaf (Type u) X :=
        ((SheafOfModules.toSheaf O).obj M).obj ⋙ forget AddCommGrpCat
      have hF : F.IsSheaf := isSheaf_sections O M
      let A' := (openIntersection U).obj W
      let B' := (openIntersection V).obj W
      let D := (openIntersection (U ⊓ V)).obj W
      change F.obj (Opposite.op A') at xU
      change F.obj (Opposite.op B') at xV
      change F.map ((openIntersectionToOpenIntersection (U ⊓ V) U inf_le_left).app W).op xU =
        F.map ((openIntersectionToOpenIntersection (U ⊓ V) V inf_le_right).app W).op xV at hmatch
      have hD : D = A' ⊓ B' := by
        ext x
        simp [D, A', B', Opens.functor_map_eq_inf, inf_left_comm, inf_comm]
      have αU := openIntersectionToOpenIntersection (U ⊓ V) U inf_le_left
      have αV := openIntersectionToOpenIntersection (U ⊓ V) V inf_le_right
      change F.map (αU.app W).op xU = F.map (αV.app W).op xV at hmatch
      have hDrev : A' ⊓ B' ≤ D := le_of_eq hD.symm
      have hcompU : homOfLE inf_le_left = homOfLE hDrev ≫ αU.app W :=
        Subsingleton.elim _ _
      have hcompV : homOfLE inf_le_right = homOfLE hDrev ≫ αV.app W :=
        Subsingleton.elim _ _
      have hcompat' := congrArg (F.map (homOfLE hDrev).op) hmatch
      change (F.map (αU.app W).op ≫ F.map (homOfLE hDrev).op).hom xU =
        (F.map (αV.app W).op ≫ F.map (homOfLE hDrev).op).hom xV at hcompat'
      simp only [← Functor.map_comp, ← op_comp] at hcompat'
      rw [← hcompU, ← hcompV] at hcompat'
      have hcompat : F.map (homOfLE inf_le_left).op xU =
          F.map (homOfLE inf_le_right).op xV := hcompat'
      have hcover : A' ⊔ B' = W := openIntersection_cover U V W hUV
      obtain ⟨sW, hresU, hresV⟩ :=
        sheafSections_glue_cover F hF A' B' W hcover xU xV hcompat
      change ↑(M.val.obj (Opposite.op W)) at sW
      have hunitU : (((jStarAdjunction U O).unit.app M).val.app (Opposite.op W)) sW = xU :=
        (jStarAdjunction_unit_app_val_app_eq O U M W _ sW).trans hresU
      have hunitV : (((jStarAdjunction V O).unit.app M).val.app (Opposite.op W)) sW = xV :=
        (jStarAdjunction_unit_app_val_app_eq O V M W _ sW).trans hresV
      refine ⟨sW, ?_⟩
      change ((SheafOfModules.evaluation O (Opposite.op W)).map
        ((restrictionCoverFirst O U V).app M)).hom sW = x
      let E := SheafOfModules.evaluation O (Opposite.op W)
      change ↑(E.obj M) at sW
      change ↑(E.obj A) at xU
      change ↑(E.obj B) at xV
      have hfst : (E.map (biprod.fst : A ⊞ B ⟶ A)).hom
          ((E.map ((restrictionCoverFirst O U V).app M)).hom sW) = xU := by
        change (E.map ((restrictionCoverFirst O U V).app M ≫ biprod.fst)).hom sW = xU
        rw [restrictionCoverFirst_app_comp_fst]
        exact hunitU
      have hsnd : (E.map (biprod.snd : A ⊞ B ⟶ B)).hom
          ((E.map ((restrictionCoverFirst O U V).app M)).hom sW) = xV := by
        change (E.map ((restrictionCoverFirst O U V).app M ≫ biprod.snd)).hom sW = xV
        rw [restrictionCoverFirst_app_comp_snd]
        exact hunitV
      have hyrep : (E.map ((restrictionCoverFirst O U V).app M)).hom sW =
          (E.map biprod.inl).hom xU + (E.map biprod.inr).hom xV := by
        have hh := (congrArg
          (fun f => f.hom ((E.map ((restrictionCoverFirst O U V).app M)).hom sW)) htot).symm
        change _ = (E.map (biprod.inl : A ⟶ A ⊞ B)).hom ((E.map (biprod.fst : A ⊞ B ⟶ A)).hom _) +
          (E.map (biprod.inr : B ⟶ A ⊞ B)).hom ((E.map (biprod.snd : A ⊞ B ⟶ B)).hom _) at hh
        rwa [hfst, hsnd] at hh
      exact hyrep.trans hxrep.symm
    · rintro ⟨y, rfl⟩
      let F := SheafOfModules.evaluation O (Opposite.op W)
      let M := K.X n
      change ↑(M.val.obj (Opposite.op W)) at y
      have hcomp : F.map ((restrictionCoverFirst O U V).app M) ≫
          F.map ((restrictionCoverSecond O U V).app M) = 0 := by
        rw [← Functor.map_comp, ← NatTrans.comp_app, restrictionCoverFirst_comp_second]
        simp
      exact congrArg (fun f => f.hom y) hcomp
  · rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    let M := K.X n
    let E := SheafOfModules.evaluation O (Opposite.op W)
    change ↑(M.val.obj (Opposite.op W)) at x
    change ↑(M.val.obj (Opposite.op W)) at y
    let F : TopCat.Presheaf (Type u) X :=
      ((SheafOfModules.toSheaf O).obj M).obj ⋙ forget AddCommGrpCat
    have hF : F.IsSheaf := isSheaf_sections O M
    let A := (restrictPush O U).obj M
    let B := (restrictPush O V).obj M
    let A' := (openIntersection U).obj W
    let B' := (openIntersection V).obj W
    let xF : F.obj (Opposite.op W) := x
    let yF : F.obj (Opposite.op W) := y
    have hcover := openIntersection_cover U V W hUV
    have hU : (((jStarAdjunction U O).unit.app M).val.app (Opposite.op W)) x =
        (((jStarAdjunction U O).unit.app M).val.app (Opposite.op W)) y := by
      have h := congrArg (E.map (biprod.fst : A ⊞ B ⟶ A)).hom hxy
      change (E.map ((restrictionCoverFirst O U V).app M ≫
        (biprod.fst : A ⊞ B ⟶ A))).hom x =
        (E.map ((restrictionCoverFirst O U V).app M ≫
          (biprod.fst : A ⊞ B ⟶ A))).hom y at h
      rwa [restrictionCoverFirst_app_comp_fst] at h
    have hV : (((jStarAdjunction V O).unit.app M).val.app (Opposite.op W)) x =
        (((jStarAdjunction V O).unit.app M).val.app (Opposite.op W)) y := by
      have h := congrArg (E.map (biprod.snd : A ⊞ B ⟶ B)).hom hxy
      change (E.map ((restrictionCoverFirst O U V).app M ≫
        (biprod.snd : A ⊞ B ⟶ B))).hom x =
        (E.map ((restrictionCoverFirst O U V).app M ≫
          (biprod.snd : A ⊞ B ⟶ B))).hom y at h
      rwa [restrictionCoverFirst_app_comp_snd] at h
    have hU' : F.map (homOfLE (le_sup_left.trans (le_of_eq hcover))).op x =
        F.map (homOfLE (le_sup_left.trans (le_of_eq hcover))).op y :=
      (jStarAdjunction_unit_app_val_app_eq O U M W _ x).symm.trans
        (hU.trans (jStarAdjunction_unit_app_val_app_eq O U M W _ y))
    have hV' : F.map (homOfLE (le_sup_right.trans (le_of_eq hcover))).op x =
        F.map (homOfLE (le_sup_right.trans (le_of_eq hcover))).op y :=
      (jStarAdjunction_unit_app_val_app_eq O V M W _ x).symm.trans
        (hV.trans (jStarAdjunction_unit_app_val_app_eq O V M W _ y))
    exact sheafSections_ext_cover F hF A' B' W hcover xF yF hU' hV'
  · apply (ModuleCat.epi_iff_surjective _).2
    intro z
    let M := K.X n
    let E := SheafOfModules.evaluation O (Opposite.op W)
    let A := (restrictPush O U).obj M
    let B := (restrictPush O V).obj M
    let T := U ⊓ V
    let A' := (openIntersection U).obj W
    let D := (openIntersection T).obj W
    change M.val.obj (Opposite.op D) at z
    have hDA : D ≤ A' := by
      simpa [D, A', openIntersection, Opens.functor_map_eq_inf,
        inf_assoc, inf_left_comm, inf_comm] using (inf_le_inf_left W inf_le_left)
    obtain ⟨y, hy⟩ :=
      Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective O M hDA z
    change ↑(A.val.obj (Opposite.op W)) at y
    let τU := (restrictPushTransition O T U inf_le_left).app M
    have htrans : (τU.val.app (Opposite.op W)) y = z := by
      change ((((restrictPushTransition O T U inf_le_left).app M).val.app
        (Opposite.op W))) y = z
      rwa [restrictPushTransition_app_val_app]
    refine ⟨(E.map (biprod.inl : A ⟶ A ⊞ B)).hom y, ?_⟩
    change (E.map (biprod.inl ≫ biprod.desc τU
      (-((restrictPushTransition O T V inf_le_right).app M)))).hom y = z
    rwa [biprod.inl_desc]

/-- **Short exactness for a cochain complex of injectives.**  Degreewise this is short
exactness at an injective sheaf of modules, read off sections through the evaluation
functors. -/
public lemma restrictionCoverShortExact (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ)
    [∀ n, Injective (K.X n)] :
    (restrictionCoverShortComplex O U V K).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  let E : Opens X → ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
    fun W => (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op W)
  have hfaith : JointlyFaithful E := ⟨fun h => by
    ext W x
    exact congrArg (fun f => f x) (h W.unop)⟩
  have hreflect : JointlyReflectIsomorphisms E := hfaith.jointlyReflectsIsomorphisms
  let F : SheafOfModules.{u} O ⥤ ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    SheafOfModules.toSheaf O ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X
  have : (TopCat.Sheaf.forget AddCommGrpCat.{u} X).Faithful :=
    TopCat.Sheaf.forgetFaithful AddCommGrpCat.{u} X
  have : F.Faithful := ⟨fun h => (SheafOfModules.toSheaf O).map_injective
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map_injective h)⟩
  have : F.PreservesZeroMorphisms := ⟨by
    intro A B
    ext W x
    rfl⟩
  have : ∀ W, PreservesFiniteLimits (E W) := fun W =>
    preservesFiniteLimits_of_preservesFiniteLimitsOfSize (E W) fun J hJ => by
      dsimp [E]
      infer_instance
  have : ∀ W, PreservesFiniteColimits (E W) := fun W =>
    preservesFiniteColimits_of_preservesFiniteColimitsOfSize (E W) fun J hJ => by
      dsimp [E]
      infer_instance
  have hpresheaf :
      (((restrictionCoverShortComplex O U V K).map
        (HomologicalComplex.eval (SheafOfModules.{u} O) (ComplexShape.up ℤ) n)).map
          F).ShortExact := by
    rw [JointlyReflectIsomorphisms.shortExact_iff hreflect]
    intro W
    exact (restrictionCoverDegreeShortExact O U V hUV K n W).map_of_exact
      (forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op W))) AddCommGrpCat.{u})
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful F hpresheaf

/-- **The Mayer--Vietoris short complex of an injective sheaf of modules is short exact.**
This is the fact the Stacks proof of Tag 01EC cites from the proof of Lemma 01EB. -/
public lemma restrictionCoverShortExact_object (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (M : SheafOfModules.{u} O) [Injective M] :
    (ShortComplex.mk ((restrictionCoverFirst O U V).app M)
      ((restrictionCoverSecond O U V).app M)
      (NatTrans.congr_app (restrictionCoverFirst_comp_second O U V) M)).ShortExact := by
  let K := (HomologicalComplex.single (SheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj M
  have hK : ∀ n, Injective (K.X n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simpa [K] using (inferInstance : Injective M)
    · have hz : IsZero (K.X n) := by
        simpa [K] using
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn)
      let := hz
      infer_instance
  have h' := (restrictionCoverShortExact O U V hUV K).map_of_exact
    (HomologicalComplex.eval (SheafOfModules.{u} O) (ComplexShape.up ℤ) 0)
  let S := restrictionCoverShortComplex O U V K
  let S' := S.map (HomologicalComplex.eval (SheafOfModules.{u} O) (ComplexShape.up ℤ) 0)
  let S₀ := ShortComplex.mk ((restrictionCoverFirst O U V).app M)
    ((restrictionCoverSecond O U V).app M)
    (NatTrans.congr_app (restrictionCoverFirst_comp_second O U V) M)
  change S'.ShortExact at h'
  let e₁ := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
  let e₂ := (restrictionCoverMiddle O U V).mapIso e₁
  let e₃ := (restrictPush O (U ⊓ V)).mapIso e₁
  have h₁₂ : e₁.hom ≫ S₀.f = S'.f ≫ e₂.hom := by
    dsimp [S', S, S₀, ShortComplex.map, restrictionCoverShortComplex, e₂]
    exact (restrictionCoverFirst O U V).naturality e₁.hom
  have h₂₃ : e₂.hom ≫ S₀.g = S'.g ≫ e₃.hom := by
    dsimp [S', S, S₀, ShortComplex.map, restrictionCoverShortComplex, e₂, e₃]
    exact (restrictionCoverSecond O U V).naturality e₁.hom
  exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁₂ h₂₃) h'

/-! ### Universal-property bridges -/

end Stacks.Cohomology.RestrictionCover

end
