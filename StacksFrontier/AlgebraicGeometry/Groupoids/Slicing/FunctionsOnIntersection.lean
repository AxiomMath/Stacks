module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SectionsOnIntersection
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffine

/-!
# Functions on an intersection of quasi-compact opens

An intersection of a nonempty family of quasi-compact opens of a quasi-separated scheme may
always be presented by a family which is directed under reverse inclusion. The functions on the
intersection are then the filtered colimit of the rings of functions on the members of the family,
and the spectrum of that colimit is the inverse limit of the corresponding affine schemes. On an
ind-quasi-affine scheme the members of such a family moreover map to the spectra of their rings of
functions by quasi-compact open immersions.

## Main definitions

* `AlgebraicGeometry.Scheme.sectionsRingOnSubset` is the ring of sections of the restriction of
  the structure sheaf to a subset.
* `AlgebraicGeometry.Scheme.sectionsRingDiagram` is the filtered diagram of rings of functions on
  a family of opens ordered by reverse inclusion.
* `AlgebraicGeometry.Scheme.stageToSubset` is the canonical restriction from a stage of the family
  to the subset.
* `AlgebraicGeometry.Scheme.spectrumDiagram` is the associated inverse diagram of affine schemes.

## Main results

* `AlgebraicGeometry.exists_directed_quasiCompact_open_presentation` produces a presentation of
  an intersection of quasi-compact opens by a family that is directed under reverse inclusion.
* `AlgebraicGeometry.isOpenImmersion_toSpecΓ_of_isIndQuasiAffine` and
  `AlgebraicGeometry.quasiCompact_toSpecΓ_of_isIndQuasiAffine` describe the canonical map from a
  quasi-compact open to the spectrum of its functions.
* `AlgebraicGeometry.colimit_sectionsRing_iso_sectionsRingOnSubset` and
  `AlgebraicGeometry.spec_sectionsRingOnSubset_iso_limit` are the filtered colimit and the inverse
  limit comparisons, each characterized on every structure map.

## Implementation notes

The rings `Γ(U i, 𝒪_{U i})` are represented by the canonically identified presheaf values
`Γ(X, U i)`, and the index category is `AlgebraicGeometry.intersectionIndex`, that is the family
ordered by reverse inclusion. Agreement with a colimit or a limit is expressed by an isomorphism
characterized on every structure map rather than by an equality of objects.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- Sections of the restriction of a scheme's structure sheaf to a subset. -/
def Scheme.sectionsRingOnSubset (X : Scheme.{u}) (E : Set X) : CommRingCat.{u} :=
  ((TopCat.Sheaf.pullback CommRingCat.{u} (Stacks.subsetInclusion (TopCat.of X) E)).obj
      X.toSheafedSpace.sheaf).obj.obj (op ⊤)

/-- The diagram of rings of functions on a family of opens ordered by reverse inclusion. -/
def Scheme.sectionsRingDiagram (X : Scheme.{u}) {I : Type u} (U : I → X.Opens) :
    intersectionIndex U ⥤ CommRingCat.{u} where
  obj i := Γ(X, U i.val)
  map {i j} f := X.presheaf.map (homOfLE f.le).op
  map_id i := by
    rw [← X.presheaf.map_id]
    rfl
  map_comp f g := by
    rw [← X.presheaf.map_comp]
    rfl

/-- The canonical restriction map from a stage to the sections on a contained subset. -/
def Scheme.stageToSubset (X : Scheme.{u}) {I : Type u} (U : I → X.Opens) (E : Set X)
    (hE : ∀ i, E ⊆ U i) (i : intersectionIndex U) :
    (Scheme.sectionsRingDiagram X U).obj i ⟶ Scheme.sectionsRingOnSubset X E :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (Stacks.subsetInclusion (TopCat.of X) E)).unit.app
        X.toSheafedSpace.sheaf).hom.app (op (U i.val))) ≫
    ((TopCat.Sheaf.pullback CommRingCat.{u} (Stacks.subsetInclusion (TopCat.of X) E)).obj
      X.toSheafedSpace.sheaf).obj.map
        (homOfLE (by
          intro x hx
          exact hE i.val x.2)).op


/-- The inverse diagram of affine spectra associated to a decreasing family of opens. -/
def Scheme.spectrumDiagram (X : Scheme.{u}) {I : Type u} (U : I → X.Opens) :
    (intersectionIndex U)ᵒᵖ ⥤ AffineScheme.{u} :=
  (Scheme.sectionsRingDiagram X U).op ⋙ AffineScheme.Spec

/-- The structure sheaf of a scheme, regarded as a sheaf of sets. -/
private def structureSheafToTypes (X : Scheme.{u}) : X.toTopCat.Sheaf (Type u) :=
  (CategoryTheory.sheafForget (Opens.grothendieckTopology X.toTopCat)).obj
    X.toSheafedSpace.sheaf

/-- A stage of the diagram of rings of functions is, as a set, the corresponding stage of the
diagram of sections of the structure sheaf viewed as a sheaf of sets. -/
private lemma sectionsRingDiagram_obj_forget (X : Scheme.{u}) {I : Type u}
    (U : I → X.Opens) (i : intersectionIndex U) :
    (forget CommRingCat).obj ((Scheme.sectionsRingDiagram X U).obj i) =
      (sectionsDiagram (structureSheafToTypes X) U).obj i := by
  rfl

/-- The comma categories computing the inverse image of a presheaf along the inclusion of a
subset are filtered. -/
private lemma pullbackCostructuredArrow_isFiltered {X : Type u} [TopologicalSpace X]
    (E : Set X) (U : Opens E) :
    IsFiltered
      (CostructuredArrow (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op (op U)) := by
  let L := (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op
  let c := op U
  have : Nonempty (CostructuredArrow L c) :=
    ⟨CostructuredArrow.mk (homOfLE (show
      U ≤ (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj ⊤ from le_top)).op⟩
  let : IsFilteredOrEmpty (CostructuredArrow L c) := by
    constructor
    · intro a b
      let W : Opens X := a.left.unop ⊓ b.left.unop
      have ha : U ≤ (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj a.left.unop :=
        a.hom.unop.le
      have hb : U ≤ (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj b.left.unop :=
        b.hom.unop.le
      have hW : U ≤ (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj W :=
        fun _ hx ↦ ⟨ha hx, hb hx⟩
      let z : CostructuredArrow L c := CostructuredArrow.mk (homOfLE hW).op
      exact ⟨z,
        CostructuredArrow.homMk (homOfLE (show W ≤ a.left.unop from inf_le_left)).op,
        CostructuredArrow.homMk (homOfLE (show W ≤ b.left.unop from inf_le_right)).op,
        trivial⟩
    · intro a b f g
      exact ⟨b, 𝟙 _, CostructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)⟩
  exact IsFiltered.mk

/-- Presheaves of commutative rings have pointwise left Kan extensions along the inclusion of a
subset (instance search no longer finds the colimits of shape `CostructuredArrow` unaided). -/
private instance hasPointwiseLeftKanExtension_opensMap {X : Type u} [TopologicalSpace X]
    (E : Set X) (F : (Opens (TopCat.of X))ᵒᵖ ⥤ CommRingCat.{u}) :
    (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op.HasPointwiseLeftKanExtension F :=
  fun c ↦
    have : HasColimitsOfShape (CostructuredArrow
        (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op c) CommRingCat.{u} :=
      HasColimitsOfSize.has_colimits_of_shape.{u, u} _
    HasColimitsOfShape.has_colimit _

/-- The forgetful functor from commutative rings preserves the left Kan extensions computing the
inverse image of a presheaf along the inclusion of a subset. -/
private lemma forget_preservesLeftKanExtensions_opensMap {X : Type u} [TopologicalSpace X]
    (E : Set X) :
    (forget CommRingCat.{u}).PreservesLeftKanExtensions
      (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op := by
  intro F
  let : ∀ c : (Opens (TopCat.of E))ᵒᵖ, IsFiltered (CostructuredArrow
      (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op c) :=
    fun c ↦ pullbackCostructuredArrow_isFiltered E c.unop
  have : ∀ c : (Opens (TopCat.of E))ᵒᵖ, HasColimitsOfShape (CostructuredArrow
      (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op c) CommRingCat.{u} :=
    fun c ↦ HasColimitsOfSize.has_colimits_of_shape.{u, u} _
  have : ∀ c : (Opens (TopCat.of E))ᵒᵖ, PreservesColimitsOfShape (CostructuredArrow
      (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op c) (forget CommRingCat.{u}) :=
    fun c ↦ inferInstance
  have : (forget CommRingCat.{u}).PreservesPointwiseLeftKanExtension F
      (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op :=
    fun c ↦ Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit _ _ _ c
  exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise _ _ _

/-- The inverse image of a presheaf of commutative rings along the inclusion of a subset has the
inverse image of the underlying presheaf of sets as its underlying presheaf of sets. -/
private noncomputable def presheafPullbackForgetIso {X : Type u} [TopologicalSpace X]
    (E : Set X) :
    (TopCat.Presheaf.pullback CommRingCat (Stacks.subsetInclusion (TopCat.of X) E)).comp
        ((Functor.whiskeringRight (Opens (TopCat.of E))ᵒᵖ CommRingCat (Type u)).obj
          (forget CommRingCat)) ≅
      ((Functor.whiskeringRight (Opens (TopCat.of X))ᵒᵖ CommRingCat (Type u)).obj
        (forget CommRingCat)).comp
        (TopCat.Presheaf.pullback (Type u) (Stacks.subsetInclusion (TopCat.of X) E)) := by
  dsimp [TopCat.Presheaf.pullback]
  let L := (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op
  haveI := forget_preservesLeftKanExtensions_opensMap E
  exact Functor.lanCompIsoOfPreserves (forget CommRingCat) L

/-- The inverse image of the structure sheaf of a scheme along the inclusion of a subset has the
inverse image of the associated sheaf of sets as its underlying sheaf of sets. -/
private noncomputable def pullbackSheafForgetIso (X : Scheme.{u}) (E : Set X) :
    ((CategoryTheory.sheafForget (Opens.grothendieckTopology (TopCat.of E))).obj
      ((TopCat.Sheaf.pullback CommRingCat (Stacks.subsetInclusion (TopCat.of X) E)).obj
        X.toSheafedSpace.sheaf)) ≅
      ((TopCat.Sheaf.pullback (Type u) (Stacks.subsetInclusion (TopCat.of X) E)).obj
        (structureSheafToTypes X)) := by
  let JX := Opens.grothendieckTopology X.toTopCat
  let JE := Opens.grothendieckTopology (TopCat.of E)
  let P := (TopCat.Presheaf.pullback CommRingCat (Stacks.subsetInclusion (TopCat.of X) E)).obj
    (X.toSheafedSpace.sheaf.obj)
  let Q := (TopCat.Presheaf.pullback (Type u) (Stacks.subsetInclusion (TopCat.of X) E)).obj
    (X.toSheafedSpace.sheaf.obj ⋙ (forget CommRingCat))
  let hR := (TopCat.Sheaf.pullbackIso CommRingCat (Stacks.subsetInclusion (TopCat.of X) E)).app
    X.toSheafedSpace.sheaf
  let hT := (TopCat.Sheaf.pullbackIso (Type u) (Stacks.subsetInclusion (TopCat.of X) E)).app
    (structureSheafToTypes X)
  let hS :
      (CategoryTheory.presheafToSheaf JE (Type u)).obj (P ⋙ forget CommRingCat) ≅
        (CategoryTheory.sheafCompose JE (forget CommRingCat)).obj
          ((CategoryTheory.presheafToSheaf JE CommRingCat).obj P) :=
    (fullyFaithfulSheafToPresheaf JE (Type u)).preimageIso
      (CategoryTheory.sheafifyComposeIso JE (forget CommRingCat) P)
  let hP := (presheafPullbackForgetIso E).app X.toSheafedSpace.sheaf.obj
  exact ((CategoryTheory.sheafForget JE).mapIso hR) ≪≫ hS.symm ≪≫
    (CategoryTheory.presheafToSheaf JE (Type u)).mapIso hP ≪≫ hT.symm

/-- An ind-quasi-affine scheme is quasi-separated. -/
instance quasiSeparatedSpace_of_isIndQuasiAffine (X : Scheme.{u})
    [AlgebraicGeometry.IsIndQuasiAffine X] : QuasiSeparatedSpace X := by
  constructor
  intro U V hUopen hUc hVopen hVc
  let W : X.Opens := ⟨U ∪ V, hUopen.union hVopen⟩
  have : W.toScheme.IsQuasiAffine :=
    AlgebraicGeometry.IsIndQuasiAffine.isQuasiAffine W (hUc.union hVc)
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ W.isOpen).mpr
    (inferInstanceAs (QuasiSeparatedSpace W.toScheme)) U V
    Set.subset_union_left hUopen hUc Set.subset_union_right hVopen hVc

/-- A nonempty intersection of quasi-compact opens of a quasi-separated scheme is also the
intersection of a family of quasi-compact opens that is directed under reverse inclusion. -/
theorem exists_directed_quasiCompact_open_presentation {X : Scheme.{u}} {I : Type v}
    [QuasiSeparatedSpace X] [Nonempty I]
    (V : I → X.Opens) (hV : ∀ i, IsCompact (V i : Set X))
    (E : Set X) (hE : E = ⋂ i, (V i : Set X)) :
    ∃ (J : Type u) (_ : Nonempty J) (U : J → X.Opens),
      (∀ j, IsCompact (U j : Set X)) ∧
        (∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j) ∧
          E = ⋂ j, (U j : Set X) := by
  let J : Type u := { U : X.Opens // IsCompact (U : Set X) ∧
    (∃ i, U ≤ V i) ∧ E ⊆ U }
  refine ⟨J, ?_, Subtype.val, ?_, ?_, ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty I›
    exact ⟨⟨V i, hV i, ⟨i, le_rfl⟩, hE ▸ Set.iInter_subset _ i⟩⟩
  · exact fun j ↦ j.2.1
  · intro i j
    refine ⟨⟨i.1 ⊓ j.1, ?_, ?_, ?_⟩, ?_⟩
    · exact i.2.1.inter_of_isOpen j.2.1 i.1.isOpen j.1.isOpen
    · obtain ⟨k, hk⟩ := i.2.2.1
      exact ⟨k, le_trans inf_le_left hk⟩
    · exact Set.subset_inter i.2.2.2 j.2.2.2
    · exact fun _ hx ↦ hx
  · refine Set.Subset.antisymm (fun x hx ↦ Set.mem_iInter.mpr fun j ↦ j.2.2.2 hx) fun x hx ↦ ?_
    rw [hE]
    exact Set.mem_iInter.mpr fun i ↦
      Set.mem_iInter.mp hx ⟨V i, hV i, ⟨i, le_rfl⟩, hE ▸ Set.iInter_subset _ i⟩

/-- The canonical map from a quasi-compact open of an ind-quasi-affine scheme to the spectrum
of its functions is an open immersion. -/
theorem isOpenImmersion_toSpecΓ_of_isIndQuasiAffine (X : Scheme.{u})
    [AlgebraicGeometry.IsIndQuasiAffine X] (U : X.Opens) (hU : IsCompact (U : Set X)) :
    IsOpenImmersion U.toSpecΓ := by
  have : U.toScheme.IsQuasiAffine :=
    AlgebraicGeometry.IsIndQuasiAffine.isQuasiAffine U hU
  unfold Scheme.Opens.toSpecΓ
  infer_instance

/-- The canonical map from a quasi-compact open of an ind-quasi-affine scheme to the spectrum
of its functions is quasi-compact. -/
theorem quasiCompact_toSpecΓ_of_isIndQuasiAffine (X : Scheme.{u})
    [AlgebraicGeometry.IsIndQuasiAffine X] (U : X.Opens) (hU : IsCompact (U : Set X)) :
    QuasiCompact U.toSpecΓ := by
  have : U.toScheme.IsQuasiAffine :=
    AlgebraicGeometry.IsIndQuasiAffine.isQuasiAffine U hU
  unfold Scheme.Opens.toSpecΓ
  infer_instance

/-- The sections of the inverse image of the structure sheaf on a subset, computed in sets, are
the sections of the inverse image of the associated sheaf of sets. -/
private lemma sectionsOnSubset_eq (X : Scheme.{u}) (E : Set X) :
    sectionsOnSubset E (structureSheafToTypes X) =
      ((TopCat.Sheaf.pullback (Type u) (Stacks.subsetInclusion (TopCat.of X) E)).obj
        (structureSheafToTypes X)).obj.obj (op ⊤) := rfl

/-- The comparison between the inverse image of a presheaf of commutative rings and the inverse
image of the underlying presheaf of sets carries the unit of the left Kan extension to the unit
of the left Kan extension of the underlying presheaf. -/
private lemma presheafPullbackForgetIso_hom_app_leftKanExtensionUnit
    (X : Scheme.{u}) (E : Set X) (W : X.Opens) (s : Γ(X, W)) :
    ConcreteCategory.hom
        (((presheafPullbackForgetIso E).hom.app X.toSheafedSpace.sheaf.obj).app
          (op ((Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj W)))
        (ConcreteCategory.hom
          (((Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op.leftKanExtensionUnit
            X.toSheafedSpace.sheaf.obj).app (op W)) s) =
      ConcreteCategory.hom
        (((Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).op.lanUnit.app
          (X.toSheafedSpace.sheaf.obj ⋙ forget CommRingCat)).app (op W)) s := by
  let G := Opens.map (Stacks.subsetInclusion (TopCat.of X) E)
  have := forget_preservesLeftKanExtensions_opensMap E
  let V : Opens E := G.obj W
  let κ := (presheafPullbackForgetIso E).hom.app X.toSheafedSpace.sheaf.obj
  let xR := ConcreteCategory.hom
    ((G.op.leftKanExtensionUnit X.toSheafedSpace.sheaf.obj).app (op W)) s
  change (ConcreteCategory.hom (κ.app (op V))) xR = _
  let : G.op.HasLeftKanExtension
      (X.toSheafedSpace.sheaf.obj ⋙ forget CommRingCat) :=
    Functor.HasLeftKanExtension.mk _
      (G.op.pointwiseLeftKanExtensionUnit
        (X.toSheafedSpace.sheaf.obj ⋙ forget CommRingCat))
  have hfac := Functor.descOfIsLeftKanExtension_fac_app
    (F := X.toSheafedSpace.sheaf.obj ⋙ forget CommRingCat)
    (L := G.op)
    (F' := G.op.leftKanExtension X.toSheafedSpace.sheaf.obj ⋙ forget CommRingCat)
    (α := Functor.whiskerRight
      (G.op.leftKanExtensionUnit X.toSheafedSpace.sheaf.obj) (forget CommRingCat) ≫
        (G.op.associator (G.op.leftKanExtension X.toSheafedSpace.sheaf.obj)
          (forget CommRingCat)).hom)
    (G := G.op.leftKanExtension
      (X.toSheafedSpace.sheaf.obj ⋙ forget CommRingCat))
    (β := G.op.leftKanExtensionUnit
      (X.toSheafedSpace.sheaf.obj ⋙ forget CommRingCat)) (op W)
  have hfac' := congrArg (fun f ↦ f s) hfac
  simp only [Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Category.assoc] at hfac'
  convert hfac' using 1
  all_goals rfl

/-- The comparison between the inverse image of the structure sheaf and the inverse image of
the associated sheaf of sets matches the units of the two inverse-image adjunctions. -/
private lemma pullbackSheafForgetIso_hom_unit (X : Scheme.{u}) (E : Set X) (W : X.Opens)
    (s : Γ(X, W)) :
    (pullbackSheafForgetIso X E).hom.hom.app
        (op ((Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj W))
        (ConcreteCategory.hom
          (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
            (Stacks.subsetInclusion (TopCat.of X) E)).unit.app
              X.toSheafedSpace.sheaf).hom.app (op W)) s) =
      ConcreteCategory.hom
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
          (Stacks.subsetInclusion (TopCat.of X) E)).unit.app
            (structureSheafToTypes X)).hom.app (op W)) s := by
  let hS := pullbackSheafForgetIso X E
  let V : Opens E := (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj W
  let G := Opens.map (Stacks.subsetInclusion (TopCat.of X) E)
  let JX := Opens.grothendieckTopology (TopCat.of X)
  let JE := Opens.grothendieckTopology (TopCat.of E)
  have := forget_preservesLeftKanExtensions_opensMap E
  have : (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).IsContinuous JX JE :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreserving_opens_map (Stacks.subsetInclusion (TopCat.of X) E))
      (coverPreserving_opens_map (Stacks.subsetInclusion (TopCat.of X) E))
  let adj₂ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    G CommRingCat JX JE
  have : (G.sheafPushforwardContinuous CommRingCat JX JE).IsRightAdjoint :=
    adj₂.isRightAdjoint
  let adj₁ := G.sheafAdjunctionContinuous CommRingCat JX JE
  have hRunit := Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₂
    X.toSheafedSpace.sheaf
  have hRunitVal :
      (ConcreteCategory.hom
        (((adj₁.leftAdjointUniq adj₂).hom.app X.toSheafedSpace.sheaf).hom.app (op V)))
          ((ConcreteCategory.hom ((adj₁.unit.app X.toSheafedSpace.sheaf).hom.app
            (op W))) s) =
        (ConcreteCategory.hom ((adj₂.unit.app X.toSheafedSpace.sheaf).hom.app
          (op W))) s := by
    have hh := congrArg
      (fun f ↦ (ConcreteCategory.hom (f.hom.app (op W))) s) hRunit
    have hObj := Functor.sheafPushforwardContinuous_obj_obj_obj
      G CommRingCat JX JE
      ((Functor.sheafPullbackConstruction.sheafPullback G CommRingCat JX JE).obj
        X.toSheafedSpace.sheaf) (op W)
    cases hObj
    exact hh
  let f1 := (sheafForget JE).mapIso
    ((TopCat.Sheaf.pullbackIso CommRingCat (Stacks.subsetInclusion (TopCat.of X) E)).app
      X.toSheafedSpace.sheaf)
  let P := (TopCat.Presheaf.pullback CommRingCat (Stacks.subsetInclusion (TopCat.of X) E)).obj
    X.toSheafedSpace.sheaf.obj
  let f2Base :
      (CategoryTheory.presheafToSheaf JE (Type u)).obj (P ⋙ forget CommRingCat) ≅
        (CategoryTheory.sheafCompose JE (forget CommRingCat)).obj
          ((CategoryTheory.presheafToSheaf JE CommRingCat).obj P) :=
    (fullyFaithfulSheafToPresheaf JE (Type u)).preimageIso
    (CategoryTheory.sheafifyComposeIso JE (forget CommRingCat)
      P)
  let f2 := f2Base.symm
  let f3 := (CategoryTheory.presheafToSheaf JE (Type u)).mapIso
    ((presheafPullbackForgetIso E).app X.toSheafedSpace.sheaf.obj)
  let f4 := ((TopCat.Sheaf.pullbackIso (Type u) (Stacks.subsetInclusion (TopCat.of X) E)).app
    (structureSheafToTypes X)).symm
  let f2Source := (CategoryTheory.sheafCompose JE (forget CommRingCat)).obj
    ((CategoryTheory.presheafToSheaf JE CommRingCat).obj P)
  let f2Target := (CategoryTheory.presheafToSheaf JE (Type u)).obj
    (P ⋙ forget CommRingCat)
  let hχIso : (sheafToPresheaf JE (Type u)).obj f2Target ≅
      (sheafToPresheaf JE (Type u)).obj f2Source :=
    CategoryTheory.sheafifyComposeIso JE (forget CommRingCat) P
  have hf2BaseMap :
      (sheafToPresheaf JE (Type u)).mapIso f2Base = hχIso := by
    dsimp [f2Base, hχIso]
    exact Iso.ext ((fullyFaithfulSheafToPresheaf JE (Type u)).map_preimage hχIso.hom)
  have hf2 : f2.hom.hom =
      (CategoryTheory.sheafifyComposeIso JE (forget CommRingCat) P).inv := by
    simpa [f2, hχIso] using congrArg (fun e ↦ e.inv) hf2BaseMap
  have hf3 : f3.hom =
      (CategoryTheory.presheafToSheaf JE (Type u)).map
        ((presheafPullbackForgetIso E).hom.app X.toSheafedSpace.sheaf.obj) := rfl
  let adjT₁ := G.sheafAdjunctionContinuous (Type u) JX JE
  let adjT₂ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    G (Type u) JX JE
  have hTunit :
      (ConcreteCategory.hom (f4.inv.hom.app (op V)))
          ((ConcreteCategory.hom ((adjT₁.unit.app (structureSheafToTypes X)).hom.app
            (op W))) s) =
        (ConcreteCategory.hom ((adjT₂.unit.app (structureSheafToTypes X)).hom.app
          (op W))) s := by
    have h := Adjunction.unit_leftAdjointUniq_hom_app adjT₁ adjT₂
      (structureSheafToTypes X)
    have hh := congrArg
      (fun f ↦ (ConcreteCategory.hom (f.hom.app (op W))) s) h
    have hObj := Functor.sheafPushforwardContinuous_obj_obj_obj
      G (Type u) JX JE
      ((Functor.sheafPullbackConstruction.sheafPullback G (Type u) JX JE).obj
        (structureSheafToTypes X)) (op W)
    dsimp [f4, adjT₁, adjT₂, TopCat.Sheaf.pullbackIso,
      Functor.sheafPullbackConstruction.sheafPullbackIso,
      TopCat.Sheaf.pullbackPushforwardAdjunction,
      Functor.sheafAdjunctionContinuous,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous] at hh ⊢
    cases hObj
    exact hh
  have hFunit :
      f1.hom.hom.app (op V)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
          (Stacks.subsetInclusion (TopCat.of X) E)).unit.app X.toSheafedSpace.sheaf).hom.app
            (op W) s) =
      (((adj₂.unit.app X.toSheafedSpace.sheaf).hom.app (op W)) s) := by
    dsimp [f1, TopCat.Sheaf.pullbackIso,
      Functor.sheafPullbackConstruction.sheafPullbackIso,
      TopCat.Sheaf.pullbackPushforwardAdjunction,
      Functor.sheafAdjunctionContinuous,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    change (ConcreteCategory.hom
        (((adj₁.leftAdjointUniq adj₂).hom.app X.toSheafedSpace.sheaf).hom.app (op V)))
        ((ConcreteCategory.hom ((adj₁.unit.app X.toSheafedSpace.sheaf).hom.app
          (op W))) s) = _
    exact hRunitVal
  dsimp [adj₁, adj₂] at hFunit
  change f4.hom.hom.app (op V)
      (f3.hom.hom.app (op V)
        (f2.hom.hom.app (op V)
          (f1.hom.hom.app (op V)
            ((ConcreteCategory.hom
              (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
                (Stacks.subsetInclusion (TopCat.of X) E)).unit.app
                  X.toSheafedSpace.sheaf).hom.app
                (op W))) s)))) =
    (ConcreteCategory.hom
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
        (Stacks.subsetInclusion (TopCat.of X) E)).unit.app (structureSheafToTypes X)).hom.app
        (op W))) s
  have hOuter := congrArg
    (fun z ↦ (ConcreteCategory.hom (f4.hom.hom.app (op V)))
      ((ConcreteCategory.hom (f3.hom.hom.app (op V)))
        ((ConcreteCategory.hom (f2.hom.hom.app (op V))) z))) hFunit
  let q := ConcreteCategory.hom
    (((adj₂.unit.app X.toSheafedSpace.sheaf).hom.app (op W))) s
  have hqVal : q =
      (ConcreteCategory.hom
        ((toSheafify JE (G.op.lan.obj X.toSheafedSpace.sheaf.obj)).app (op V)))
        ((ConcreteCategory.hom
          (((G.op.lanAdjunction CommRingCat).unit.app
            X.toSheafedSpace.sheaf.obj).app (op W))) s) := by
    dsimp [q, adj₂,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    simp [Functor.lanAdjunction_unit]; rfl
  have hqTVal :
      (ConcreteCategory.hom ((adjT₂.unit.app (structureSheafToTypes X)).hom.app
        (op W))) s =
        (ConcreteCategory.hom
          ((toSheafify JE
            (G.op.lan.obj (structureSheafToTypes X).obj)).app (op V)))
          ((ConcreteCategory.hom
            (((G.op.lanAdjunction (Type u)).unit.app
              (structureSheafToTypes X).obj).app (op W))) s) := by
    dsimp [adjT₂,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    simp [Functor.lanAdjunction_unit]; rfl
  let κ := (presheafPullbackForgetIso E).hom.app X.toSheafedSpace.sheaf.obj
  let xR := (ConcreteCategory.hom
    ((G.op.leftKanExtensionUnit X.toSheafedSpace.sheaf.obj).app
      (op W))) s
  have hχFac := congrArg
    (fun f ↦ (ConcreteCategory.hom (f.app (op V))) xR)
    (CategoryTheory.sheafComposeIso_inv_fac
      (J := JE) (F := forget CommRingCat) (P := P))
  simp only [NatTrans.comp_app] at hχFac
  have hToFac := congrArg
    (fun f ↦ (ConcreteCategory.hom (f.app (op V))) xR)
    (CategoryTheory.toSheafify_naturality JE κ)
  have hBridge :
      (ConcreteCategory.hom
        (((presheafToSheaf JE (Type u)).map κ).hom.app (op V)))
          ((ConcreteCategory.hom ((toSheafify JE (P ⋙ forget CommRingCat)).app
            (op V))) xR) =
        (ConcreteCategory.hom ((toSheafify JE
          (G.op.lan.obj (structureSheafToTypes X).obj)).app (op V)))
          ((ConcreteCategory.hom (κ.app (op V))) xR) :=
    hToFac.symm
  have hη' := presheafPullbackForgetIso_hom_app_leftKanExtensionUnit X E W s
  have hCmp :
      (ConcreteCategory.hom (f3.hom.hom.app (op V)))
          ((ConcreteCategory.hom (f2.hom.hom.app (op V))) q) =
        (ConcreteCategory.hom ((adjT₂.unit.app (structureSheafToTypes X)).hom.app
          (op W))) s := by
    have hχMapped := congrArg
      (fun z ↦ (ConcreteCategory.hom
        (((presheafToSheaf JE (Type u)).map
          ((presheafPullbackForgetIso E).hom.app X.toSheafedSpace.sheaf.obj)).hom.app
            (op V))) z) hχFac
    simp only [Functor.whiskerRight_app] at hχMapped
    have hCombined := hχMapped.trans hBridge
    have hInitial :
        (ConcreteCategory.hom (f3.hom.hom.app (op V)))
            ((ConcreteCategory.hom (f2.hom.hom.app (op V))) q) =
          (ConcreteCategory.hom
            (((presheafToSheaf JE (Type u)).map κ).hom.app (op V)))
            ((ConcreteCategory.hom
              (((Functor.whiskerRight (toSheafify JE P)
                (forget CommRingCat)).app (op V) ≫
                (sheafifyComposeIso JE (forget CommRingCat) P).inv.app
                  (op V)))) xR) := by
      rw [hf3, hf2, hqVal]
      rfl
    exact hInitial.trans (hCombined.trans (congrArg
      (fun z ↦ (ConcreteCategory.hom
        ((toSheafify JE
          (G.op.lan.obj (structureSheafToTypes X).obj)).app (op V))) z) hη'))
  calc
    _ = (ConcreteCategory.hom (f4.hom.hom.app (op V)))
        ((ConcreteCategory.hom (f3.hom.hom.app (op V)))
          ((ConcreteCategory.hom (f2.hom.hom.app (op V))) q)) := hOuter
    _ = _ := by
      rw [hCmp, ← hTunit]
      have hcomp := congrArg (fun f ↦ f.hom.app (op V)) f4.inv_hom_id
      have hCancel := congrArg
        (fun f ↦ (ConcreteCategory.hom f)
          ((ConcreteCategory.hom ((adjT₁.unit.app
            (structureSheafToTypes X)).hom.app (op W))) s)) hcomp
      exact hCancel

/-- The comparison between the inverse image of the structure sheaf and the inverse image of the
associated sheaf of sets carries the canonical map from a stage to the canonical map from that
stage for sheaves of sets. -/
private lemma pullbackSheafForgetIso_hom_stageToSubset (X : Scheme.{u}) {I : Type u}
    (U : I → X.Opens) (E : Set X) (hE' : ∀ i, E ⊆ U i) (i : intersectionIndex U)
    (s : (forget CommRingCat).obj ((Scheme.sectionsRingDiagram X U).obj i)) :
    (pullbackSheafForgetIso X E).hom.hom.app (op ⊤)
        ((forget CommRingCat).map (Scheme.stageToSubset X U E hE' i) s) =
      sectionsOnSubset_eq X E ▸ stageToSubset (structureSheafToTypes X) U E hE' i
          ((sectionsRingDiagram_obj_forget X U i) ▸ s) := by
  let hS := pullbackSheafForgetIso X E
  have hSub := sectionsOnSubset_eq X E
  change hS.hom.hom.app (op ⊤)
      ((forget CommRingCat).map (Scheme.stageToSubset X U E hE' i) s) =
    hSub ▸ stageToSubset (structureSheafToTypes X) U E hE' i
      ((sectionsRingDiagram_obj_forget X U i) ▸ s)
  cases sectionsRingDiagram_obj_forget X U i
  cases hSub
  dsimp [Scheme.stageToSubset, stageToSubset,
    sectionsOnSubset]
  let a : ⊤ ⟶ (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj (U i.val) :=
    homOfLE (fun x _ ↦ hE' i.val x.2)
  have hNatVal := congrArg
    (fun f ↦ f (ConcreteCategory.hom
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
        (Stacks.subsetInclusion (TopCat.of X) E)).unit.app X.toSheafedSpace.sheaf).hom.app
        (op (U i.val))) s)) (hS.hom.hom.naturality a.op)
  exact hNatVal.trans (congrArg
    (fun z ↦ ConcreteCategory.hom
      (((TopCat.Sheaf.pullback (Type u) (Stacks.subsetInclusion (TopCat.of X) E)).obj
        (structureSheafToTypes X)).obj.map a.op) z)
    (pullbackSheafForgetIso_hom_unit X E (U i.val) s))

/-- Functions on the intersection are canonically the filtered colimit of the rings of
functions on a directed decreasing family of quasi-compact opens. -/
theorem colimit_sectionsRing_iso_sectionsRingOnSubset (X : Scheme.{u})
    [QuasiSeparatedSpace X] {I : Type u} [Nonempty I] (U : I → X.Opens)
    (hU : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) :
    ∃ e : colimit (Scheme.sectionsRingDiagram X U) ≅ Scheme.sectionsRingOnSubset X E,
      ∀ i, colimit.ι (Scheme.sectionsRingDiagram X U) i ≫ e.hom =
        Scheme.stageToSubset X U E
          (fun j ↦ by rw [hE]; exact Set.iInter_subset _ j) i := by
  classical
  let : IsFiltered (intersectionIndex U) := filtered_intersectionIndex U hdir
  let hE' (i : I) : E ⊆ U i := by
    rw [hE]
    exact Set.iInter_subset _ i
  let c : Cocone (Scheme.sectionsRingDiagram X U) :=
    { pt := Scheme.sectionsRingOnSubset X E
      ι :=
        { app := fun i ↦ Scheme.stageToSubset X U E hE' i
          naturality := by
            intro i j f
            have hnat := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
              (Stacks.subsetInclusion (TopCat.of X) E)).unit.app
                X.toSheafedSpace.sheaf).hom.naturality (homOfLE f.le).op
            simp only [Functor.id_obj] at hnat
            dsimp [Scheme.sectionsRingDiagram, Scheme.stageToSubset]
            rw [Category.comp_id]
            erw [← Category.assoc, hnat, Category.assoc]
            congr 1
            exact (((TopCat.Sheaf.pullback CommRingCat
              (Stacks.subsetInclusion (TopCat.of X) E)).obj
                X.toSheafedSpace.sheaf).obj.map_comp _ _).symm } }
  let g := colimit.desc _ c
  let hS := pullbackSheafForgetIso X E
  have hSub := sectionsOnSubset_eq X E
  let hSt : (forget CommRingCat).obj (Scheme.sectionsRingOnSubset X E) ≃
      sectionsOnSubset E (structureSheafToTypes X) := {
    toFun := hS.hom.hom.app (op ⊤)
    invFun := hS.inv.hom.app (op ⊤)
    left_inv := by
      intro x
      have hh := congrArg (fun f ↦ f.hom.app (op ⊤)) hS.hom_inv_id
      change hS.inv.hom.app (op ⊤) (hS.hom.hom.app (op ⊤) x) = x
      exact congrArg (fun f ↦ f x) hh
    right_inv := by
      intro x
      have hh := congrArg (fun f ↦ f.hom.app (op ⊤)) hS.inv_hom_id
      change hS.hom.hom.app (op ⊤) (hS.inv.hom.app (op ⊤) x) = x
      exact congrArg (fun f ↦ f x) hh
  }
  have hStage := pullbackSheafForgetIso_hom_stageToSubset X U E hE'
  obtain ⟨eAPH, heAPH⟩ :=
    colimit_sections_equiv_sections_iInter
      (structureSheafToTypes X) U hU hdir E hE
  let dAPH := sectionsDiagram (structureSheafToTypes X) U
  let eAPHiso : colimit dAPH ≅ sectionsOnSubset E (structureSheafToTypes X) :=
    Equiv.toIso eAPH
  let cAPH : Cocone dAPH := (colimit.cocone dAPH).extend eAPHiso.hom
  have hcAPH : IsColimit cAPH :=
    (colimit.isColimit dAPH).extendIso eAPHiso.hom
  have hDiagram : dAPH = Scheme.sectionsRingDiagram X U ⋙ forget CommRingCat := rfl
  let cType : Cocone (Scheme.sectionsRingDiagram X U ⋙ forget CommRingCat) := cAPH
  have hcType : IsColimit cType := hcAPH
  let hCol : IsColimit (Functor.mapCocone (forget CommRingCat)
      (colimit.cocone (Scheme.sectionsRingDiagram X U))) :=
    isColimitOfPreserves (forget CommRingCat) (colimit.isColimit (Scheme.sectionsRingDiagram X U))
  let eCol := hCol.coconePointUniqueUpToIso hcType
  let hStIso := Equiv.toIso hSt
  have hcomp : (forget CommRingCat).map g ≫ hStIso.hom = eCol.hom := by
    apply hCol.hom_ext
    intro i
    have hfac := colimit.ι_desc c i
    have hci := hCol.comp_coconePointUniqueUpToIso_hom hcType i
    ext s
    dsimp [Functor.mapCocone]
    change hStIso.hom
      ((forget CommRingCat).map g
        ((forget CommRingCat).map (colimit.ι (Scheme.sectionsRingDiagram X U) i) s)) =
      eCol.hom ((forget CommRingCat).map (colimit.ι (Scheme.sectionsRingDiagram X U) i) s)
    calc
      _ = hStIso.hom ((forget CommRingCat).map
            (colimit.ι (Scheme.sectionsRingDiagram X U) i ≫ g) s) := by
              congr 1
      _ = hStIso.hom ((forget CommRingCat).map (c.ι.app i) s) := by rw [hfac]
      _ = cType.ι.app i s := by
        cases hSub
        dsimp [c]
        change (ConcreteCategory.hom (hS.hom.hom.app (op ⊤)))
          ((ConcreteCategory.hom ((forget CommRingCat).map (c.ι.app i))) s) = _
        rw [hStage]
        change stageToSubset (structureSheafToTypes X) U E hE' i s =
          eAPH ((colimit.ι dAPH i) s)
        exact (heAPH i s).symm
      _ = eCol.hom ((forget CommRingCat).map
            (colimit.ι (Scheme.sectionsRingDiagram X U) i) s) := by
              have hci' : (forget CommRingCat).map
                    (colimit.ι (Scheme.sectionsRingDiagram X U) i) ≫ eCol.hom = cType.ι.app i := by
                simpa only [Functor.mapCocone_ι_app, colimit.cocone_ι, eCol] using hci
              simpa only [ConcreteCategory.comp_apply] using
                (congrArg (fun f ↦ f s) hci').symm
  have hgf : IsIso ((forget CommRingCat).map g) := by
    have hEq : (forget CommRingCat).map g = eCol.hom ≫ hStIso.inv := by
      calc
        (forget CommRingCat).map g =
            ((forget CommRingCat).map g ≫ hStIso.hom) ≫ hStIso.inv := by simp
        _ = eCol.hom ≫ hStIso.inv := by rw [hcomp]
    rw [hEq]
    infer_instance
  have : IsIso g := isIso_of_reflects_iso g (forget CommRingCat)
  exact ⟨asIso g, fun i ↦ by simp [g, c, colimit.ι_desc]⟩

/-- The spectrum of the functions on the intersection is canonically the inverse limit of
the spectra of the rings of functions at the stages. -/
theorem spec_sectionsRingOnSubset_iso_limit (X : Scheme.{u})
    [QuasiSeparatedSpace X] {I : Type u} [Nonempty I] (U : I → X.Opens)
    (hU : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) :
    ∃ e : Scheme.Spec.obj (op (Scheme.sectionsRingOnSubset X E)) ≅
        AffineScheme.forgetToScheme.obj (limit (Scheme.spectrumDiagram X U)),
      ∀ i, e.hom ≫ AffineScheme.forgetToScheme.map
          (limit.π (Scheme.spectrumDiagram X U) (op i)) =
        Scheme.Spec.map
          (Scheme.stageToSubset X U E
            (fun j ↦ by rw [hE]; exact Set.iInter_subset _ j) i).op := by
  obtain ⟨e, he⟩ := colimit_sectionsRing_iso_sectionsRingOnSubset X U hU hdir E hE
  let d := Scheme.sectionsRingDiagram X U
  let f : Scheme.Spec.obj (op (Scheme.sectionsRingOnSubset X E)) ≅
      AffineScheme.forgetToScheme.obj (limit (Scheme.spectrumDiagram X U)) :=
    Scheme.Spec.mapIso e.op ≪≫
      Scheme.Spec.mapIso (limitOpIsoOpColimit d).symm ≪≫
      preservesLimitIso Scheme.Spec d.op ≪≫
      (preservesLimitIso AffineScheme.forgetToScheme (Scheme.spectrumDiagram X U)).symm
  refine ⟨f, fun i ↦ ?_⟩
  dsimp [f, Iso.trans]
  have hforget := preservesLimitIso_inv_π AffineScheme.forgetToScheme
    (Scheme.spectrumDiagram X U) (op i)
  have hstep1 := congrArg
    (fun t ↦ Spec.map e.op.hom.unop ≫
      Spec.map (limitOpIsoOpColimit d).inv.unop ≫
      (preservesLimitIso Scheme.Spec d.op).hom ≫ t) hforget
  have hgoal1 :
      (Spec.map e.op.hom.unop ≫
        Spec.map (limitOpIsoOpColimit d).inv.unop ≫
        (preservesLimitIso Scheme.Spec d.op).hom ≫
        (preservesLimitIso AffineScheme.forgetToScheme (Scheme.spectrumDiagram X U)).inv) ≫
          AffineScheme.forgetToScheme.map (limit.π (Scheme.spectrumDiagram X U) (op i)) =
        (Spec.map e.op.hom.unop ≫
          Spec.map (limitOpIsoOpColimit d).inv.unop ≫
          (preservesLimitIso Scheme.Spec d.op).hom) ≫
            limit.π (Scheme.spectrumDiagram X U ⋙ AffineScheme.forgetToScheme) (op i) := by
    convert hstep1 using 1 <;> exact Category.assoc _ _ _
  rw [hgoal1]
  have hspec := preservesLimitIso_hom_π Scheme.Spec d.op (op i)
  have hstep2 := congrArg
    (fun t ↦ Spec.map e.op.hom.unop ≫
      Spec.map (limitOpIsoOpColimit d).inv.unop ≫ t) hspec
  have hgoal2 :
      (Spec.map e.op.hom.unop ≫
        Spec.map (limitOpIsoOpColimit d).inv.unop ≫
          (preservesLimitIso Scheme.Spec d.op).hom) ≫
            limit.π (d.op ⋙ Scheme.Spec) (op i) =
        Spec.map e.op.hom.unop ≫
          Spec.map (limitOpIsoOpColimit d).inv.unop ≫
            Scheme.Spec.map (limit.π d.op (op i)) := by
    convert hstep2 using 1
    exact Category.assoc _ _ _
  change (Spec.map e.op.hom.unop ≫
    Spec.map (limitOpIsoOpColimit d).inv.unop ≫
      (preservesLimitIso Scheme.Spec d.op).hom) ≫
        limit.π (d.op ⋙ Scheme.Spec) (op i) = _
  rw [hgoal2]
  change Scheme.Spec.map e.op.hom ≫
    Scheme.Spec.map (limitOpIsoOpColimit d).inv ≫
      Scheme.Spec.map (limit.π d.op (op i)) = _
  rw [← Scheme.Spec.map_comp, limitOpIsoOpColimit_inv_comp_π, ← Scheme.Spec.map_comp]
  exact congrArg Spec.map (he i)

end AlgebraicGeometry
