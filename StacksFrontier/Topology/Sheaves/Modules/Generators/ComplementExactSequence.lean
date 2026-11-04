module

public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.Sheaves.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial
public import StacksFrontier.Topology.Sheaves.Sheaf.Abelian
public import StacksFrontier.Topology.Sheaves.Stalk.Restrict

/-!
# The canonical exact sequence of an open subset and its closed complement

Let `U` be an open subset of a topological space `X`, let `j : U → X` be its open inclusion and
`i : X \ U → X` the inclusion of the closed complement. Every sheaf `F` of abelian groups on `X`
sits in a canonical short exact sequence

`0 ⟶ j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F ⟶ 0`,

whose two maps are the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*`. The sequence is
functorial in `F`: it is a functor from abelian sheaves on `X` to short complexes.

## Main definitions

* `Stacks.Sheaf.closedComplementInclusion`: the inclusion of the complement of an open subset.
* `Stacks.Sheaf.closedComplementPullback`, `Stacks.Sheaf.closedComplementPushforward`,
  `Stacks.Sheaf.closedComplementAdjunction`: inverse image and direct image along it, and the
  adjunction between them.
* `Stacks.Sheaf.canonicalComplementSequence`: the canonical sequence, functorial in the sheaf.

## Main results

* `Stacks.Sheaf.canonicalComplementMaps_comp_zero`: the two canonical maps compose to zero.
* `Stacks.Sheaf.canonicalComplementSequence_shortExact`: every canonical complement sequence is
  short exact.

## References

* [Stacks Project, Tag 02UT](https://stacks.math.columbia.edu/tag/02UT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Sheaf

variable {X : TopCat.{u}} (U : Opens X)

/-- The inclusion `i : X ∖ U ⟶ X` of the closed complement of an open subset. -/
def closedComplementInclusion : TopCat.of (Set.compl (U : Set X)) ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Inverse image of abelian sheaves along the inclusion of the closed complement. -/
noncomputable abbrev closedComplementPullback :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤
      TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Set.compl (U : Set X))) :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} (closedComplementInclusion U)

/-- Direct image of abelian sheaves along the inclusion of the closed complement. -/
noncomputable abbrev closedComplementPushforward :
    TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Set.compl (U : Set X))) ⥤
      TopCat.Sheaf AddCommGrpCat.{u} X :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedComplementInclusion U)

/-- The adjunction `i^{-1} ⊣ i_*` for the inclusion of the closed complement. -/
noncomputable abbrev closedComplementAdjunction :
    closedComplementPullback U ⊣ closedComplementPushforward U :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (closedComplementInclusion U)

private lemma isZero_stalk_closedComplementPushforward
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Set.compl (U : Set X))))
    (x : X) (hx : x ∈ U) :
    IsZero (((closedComplementPushforward U).obj F).presheaf.stalk x) := by
  have hi := U.2.isClosed_compl.isClosedEmbedding_subtypeVal
  have hnot : x ∉ Set.range (ConcreteCategory.hom (closedComplementInclusion U)) := by
    rintro ⟨z, rfl⟩
    exact z.property hx
  exact (ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange
    (i := closedComplementInclusion U) (F := F.presheaf) F.property hi x hnot).isZero

private lemma closedComplementPushforward_restrict_isZero
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Set.compl (U : Set X)))) :
    IsZero ((Opens.sheafRestrict U).obj ((closedComplementPushforward U).obj F)) := by
  show IsZero (show TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) from _)
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  intro x
  show IsZero (TopCat.Presheaf.stalk
    ((TopCat.Presheaf.imF U).op ⋙ ((closedComplementPushforward U).obj F).presheaf) x)
  exact (isZero_stalk_closedComplementPushforward U F (U.inclusion' x) x.property).of_iso
    (TopCat.Presheaf.stalkRestrictIso U ((closedComplementPushforward U).obj F).presheaf x)

private lemma isIso_stalk_extendByInitial_counit_app
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) (hx : x ∈ U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((TopCat.Presheaf.extendByInitialSheafAdjunction U).counit.app F).hom) := by
  have hunit := TopCat.Presheaf.ExtensionByInitial.isIso_unit_extendByInitialSheafAdjunction
    (C := AddCommGrpCat.{u}) U
  let instUnitApp : IsIso ((TopCat.Presheaf.extendByInitialSheafAdjunction U).unit.app
      ((Opens.sheafRestrict U).obj F)) :=
    ((asIso (TopCat.Presheaf.extendByInitialSheafAdjunction U).unit).app _).isIso_hom
  have hR : IsIso ((Opens.sheafRestrict U).map
      ((TopCat.Presheaf.extendByInitialSheafAdjunction U).counit.app F)) :=
    @isIso_of_hom_comp_eq_id _ _ _ _ _ instUnitApp _
      ((TopCat.Presheaf.extendByInitialSheafAdjunction U).right_triangle_components F)
  have hwhisk : IsIso (Functor.whiskerLeft (TopCat.Presheaf.imF U).op
      ((TopCat.Presheaf.extendByInitialSheafAdjunction U).counit.app F).hom) :=
    @Functor.map_isIso _ _ _ _ _ _
      (TopCat.Sheaf.forget AddCommGrpCat.{u} ((Opens.toTopCat X).obj U))
      ((Opens.sheafRestrict U).map
        ((TopCat.Presheaf.extendByInitialSheafAdjunction U).counit.app F)) hR
  have h := (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff U _ _
    ((TopCat.Presheaf.extendByInitialSheafAdjunction U).counit.app F).hom ⟨x, hx⟩).mp
      inferInstance
  simpa using h

section PullbackStalks

variable {Y : TopCat.{u}}

private lemma pullbackPushforwardAdjunction_unit_comp_pullbackIso
    (f : X ⟶ Y) (F : TopCat.Sheaf AddCommGrpCat.{u} Y) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F).hom ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
        ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).hom.app F).hom =
    (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F.presheaf ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj F.presheaf)) :=
  congrArg ((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
        AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) F)

attribute [local implicit_reducible] TopCat.Presheaf.stalk TopCat.Presheaf.stalkFunctor in
private lemma stalkPushforward_naturality (f : X ⟶ Y)
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X} (α : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map α) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f G x =
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f F x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hx => ?_
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.stalkPushforward_germ_assoc]
  exact (TopCat.Presheaf.stalkFunctor_map_germ ((Opens.map f).obj V) x hx α).symm

attribute [local implicit_reducible] TopCat.Presheaf.stalk TopCat.Presheaf.stalkFunctor in
private lemma isIso_stalk_unit_of_isInducing (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (F : TopCat.Sheaf AddCommGrpCat.{u} Y) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F).hom) := by
  let P := (TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj F.presheaf
  let Q := ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P).obj
  let B := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F).presheaf
  let u : F.presheaf ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj B :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F).hom
  let e : B ⟶ Q := ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).hom.app F).hom
  let pu : F.presheaf ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj P :=
    (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F.presheaf
  let ts : P ⟶ Q := toSheafify (Opens.grothendieckTopology X) P
  show IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map u)
  have heSheaf : IsIso ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).hom.app F) :=
    ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).app F).isIso_hom
  have he : IsIso e := (ObjectProperty.isIso_hom_iff _).mpr heSheaf
  have hp : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f B x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat.{u} hf B x
  have hq : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ts) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  have hb : IsIso (TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f F.presheaf x) :=
    (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f F.presheaf x).isIso_hom
  have nat : ∀ {A C : TopCat.Presheaf AddCommGrpCat.{u} X}
      (a : F.presheaf ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj A) (b : A ⟶ C),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
          (a ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map b) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f C x =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map a ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f A x) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map b := fun a b => by
    rw [Functor.map_comp, Category.assoc, stalkPushforward_naturality f b x, Category.assoc]
  have key :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map u ≫
          TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f B x) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map e =
      TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f F.presheaf x ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ts := by
    have h : u ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map e =
        pu ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map ts :=
      pullbackPushforwardAdjunction_unit_comp_pullbackIso f F
    rw [← nat, h, nat]
    rfl
  have ht : IsIso (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map u ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f B x) ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map e) := by
    rw [key]; infer_instance
  have hcomp : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map u ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f B x) :=
    IsIso.of_isIso_comp_right _ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map e)
  exact IsIso.of_isIso_comp_right _
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f B x)

end PullbackStalks

private lemma isIso_stalk_closedComplement_unit_app
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) (hx : x ∉ U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((closedComplementAdjunction U).unit.app F).hom) :=
  isIso_stalk_unit_of_isInducing (closedComplementInclusion U)
    U.2.isClosed_compl.isClosedEmbedding_subtypeVal.isInducing F ⟨x, hx⟩

/-- The composite of the two canonical adjunction maps is zero. -/
lemma canonicalComplementMaps_comp_zero :
    (TopCat.Presheaf.extendByInitialSheafAdjunction U).counit ≫
      (closedComplementAdjunction U).unit = 0 := by
  ext F
  apply ((TopCat.Presheaf.extendByInitialSheafAdjunction U).homEquiv _ _).injective
  exact (closedComplementPushforward_restrict_isZero U
    ((closedComplementPullback U).obj F)).eq_of_tgt _ _

/-- The canonical sequence `j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F`, functorially in the abelian
sheaf `F`. -/
noncomputable def canonicalComplementSequence :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  (ShortComplex.functorEquivalence
      (TopCat.Sheaf AddCommGrpCat.{u} X) (TopCat.Sheaf AddCommGrpCat.{u} X)).functor.obj
    (ShortComplex.mk (TopCat.Presheaf.extendByInitialSheafAdjunction U).counit
      (closedComplementAdjunction U).unit (canonicalComplementMaps_comp_zero U))

/-- **Stacks Project, Tag 02UT.** The canonical sequence associated to an open subset and its
closed complement is short exact for every sheaf of abelian groups. -/
@[stacks 02UT, sga "4 IV 14.6" "(14.6.1)"]
theorem canonicalComplementSequence_shortExact
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((canonicalComplementSequence U).obj F).ShortExact := by
  apply TopCat.Sheaf.shortExact_of_stalk
  intro x
  let S := ((canonicalComplementSequence U).obj F).map
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  show S.ShortExact
  by_cases hx : x ∈ U
  · have hiso : IsIso S.f := isIso_stalk_extendByInitial_counit_app U F x hx
    have hz : IsZero S.X₃ :=
      isZero_stalk_closedComplementPushforward U ((closedComplementPullback U).obj F) x hx
    exact { exact := (S.exact_iff_epi (hz.eq_of_tgt _ _)).2 inferInstance
            mono_f := inferInstance
            epi_g := epi_of_target_iso_zero _ hz.isoZero }
  · have hiso : IsIso S.g := isIso_stalk_closedComplement_unit_app U F x hx
    have hz : IsZero S.X₁ :=
      TopCat.Presheaf.isZero_stalk_extendByInitialSheafify U
        ((Opens.sheafRestrict U).obj F).obj hx
    exact { exact := (S.exact_iff_mono (hz.eq_of_src _ _)).2 inferInstance
            mono_f := mono_of_source_iso_zero _ hz.isoZero
            epi_g := inferInstance }

end Stacks.Sheaf

end
