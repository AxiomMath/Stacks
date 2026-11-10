module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Morphism

/-!
# The total functor of a morphism between simplicial sites, continuous case

A morphism between simplicial sites in the continuous case is a simplicial family of functors
between the component categories, each representing a morphism of sites. Applying them
degreewise gives a single functor between the total categories, in the direction opposite to
the morphism, and that functor is again continuous.

## Main definitions

* `CategoryTheory.SimplicialSite.Morphism.totalFunctor`: the functor between the total
  categories obtained by applying the given functors degreewise.

## Main results

* `CategoryTheory.SimplicialSite.Morphism.ι_comp_totalFunctor`: the inclusion of the component
  of a simplicial degree, followed by the functor between the total categories, is the given
  functor in that degree followed by the inclusion of the component of the target.
* `CategoryTheory.SimplicialSite.Morphism.totalFunctor_isContinuous`: the functor between the
  total categories is continuous.

## References

* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 09WC](https://stacks.math.columbia.edu/tag/09WC)
* [Stacks Project, Tag 00WW](https://stacks.math.columbia.edu/tag/00WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

universe u

namespace CategoryTheory

namespace SimplicialSite.Morphism

attribute [local implicit_reducible] CategoryTheory.SimplicialSite.totalPseudofunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc

attribute [local simp] PrelaxFunctor.map₂_eqToHom

variable {C C' : SimplicialSite.{u}}

/-- The strict commutation of the degreewise functors with the transition functors, read on
objects. -/
theorem app_obj_map (h : SimplicialSite.Morphism C C') {m n : SimplexCategory} (φ : m ⟶ n)
    (V : C'.underlying.obj m) :
    (h.hom.app n).toFunctor.obj ((C'.underlying.map φ).toFunctor.obj V) =
      (C.underlying.map φ).toFunctor.obj ((h.hom.app m).toFunctor.obj V) :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (h.hom.naturality φ)) V

/-- The strict commutation of the degreewise functors with the transition functors, read on
morphisms of a component. -/
theorem app_map_total (h : SimplicialSite.Morphism C C') {b b' : SimplexCategoryᵒᵖ} (δ : b ⟶ b')
    {V W : C'.totalPseudofunctor.obj ⟨Opposite.op b'⟩} (u : V ⟶ W) :
    (h.hom.app b.unop).toFunctor.map ((C'.totalPseudofunctor.map δ.op.toLoc).toFunctor.map u) =
      eqToHom (h.app_obj_map δ.unop V) ≫
        (C.totalPseudofunctor.map δ.op.toLoc).toFunctor.map
          ((h.hom.app b'.unop).toFunctor.map u) ≫ eqToHom (h.app_obj_map δ.unop W).symm := by
  have hu := Functor.congr_hom (congrArg Cat.Hom.toFunctor (h.hom.naturality δ.unop)) u
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hu
  exact hu

/-- The unit comparison of the total pseudofunctor of a simplicial site is, on sections, the
transport along the identity law of the cosimplicial diagram. -/
theorem totalPseudofunctor_mapId_inv_app (D : SimplicialSite.{u}) (b : SimplexCategoryᵒᵖ)
    (V : D.totalPseudofunctor.obj ⟨Opposite.op b⟩) :
    (D.totalPseudofunctor.mapId ⟨Opposite.op b⟩).inv.toNatTrans.app V =
      eqToHom (Functor.congr_obj
        (congrArg Cat.Hom.toFunctor (D.underlying.map_id b.unop)).symm V) := by
  simp [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapId]

/-- The functor between the total categories attached to a morphism between simplicial sites in
the continuous case: in each simplicial degree it is the given functor. -/
@[stacks 0D96 "case (A), the functor of total sites"]
def totalFunctor (h : SimplicialSite.Morphism C C') :
    CoGrothendieck C'.totalPseudofunctor ⥤ CoGrothendieck C.totalPseudofunctor where
  obj X := ⟨X.base, (h.hom.app X.base.unop).toFunctor.obj X.fiber⟩
  map {X Y} f :=
    ⟨f.base, (h.hom.app X.base.unop).toFunctor.map f.fiber ≫
      eqToHom (h.app_obj_map f.base.unop Y.fiber)⟩
  map_id X := by
    refine CoGrothendieck.Hom.ext _ _ rfl ?_
    simp [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapId, eqToHom_map]
  map_comp {X Y Z} f g := by
    refine CoGrothendieck.Hom.ext _ _ rfl ?_
    simp only [CoGrothendieck.categoryStruct_comp_fiber, Functor.map_comp, Category.assoc,
      h.app_map_total]
    simp [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapComp, eqToHom_map]

/-- The functor between the total categories sends the image of a morphism of the component of
simplicial degree `b` to the image of the morphism that degree's functor assigns to it. -/
theorem ι_map_totalFunctor (h : SimplicialSite.Morphism C C') (b : SimplexCategoryᵒᵖ)
    {P Q : C'.totalPseudofunctor.obj ⟨Opposite.op b⟩} (u : P ⟶ Q) :
    h.totalFunctor.map ((CoGrothendieck.ι C'.totalPseudofunctor b).map u) =
      (CoGrothendieck.ι C.totalPseudofunctor b).map ((h.hom.app b.unop).toFunctor.map u) := by
  refine CoGrothendieck.Hom.ext _ _ rfl ?_
  change (h.hom.app b.unop).toFunctor.map
        (u ≫ (C'.totalPseudofunctor.mapId ⟨Opposite.op b⟩).inv.toNatTrans.app Q) ≫
      eqToHom (h.app_obj_map (𝟙 b).unop Q) =
    ((h.hom.app b.unop).toFunctor.map u ≫
      (C.totalPseudofunctor.mapId ⟨Opposite.op b⟩).inv.toNatTrans.app
        ((h.hom.app b.unop).toFunctor.obj Q)) ≫ 𝟙 _
  simp only [Functor.map_comp, Category.assoc, Category.comp_id,
    totalPseudofunctor_mapId_inv_app, eqToHom_map, eqToHom_trans]

/-- The inclusion of the component in simplicial degree `b`, followed by the functor between
the total categories, is the given functor in that degree followed by the inclusion of the
component of the target. -/
theorem ι_comp_totalFunctor (h : SimplicialSite.Morphism C C') (b : SimplexCategoryᵒᵖ) :
    CoGrothendieck.ι C'.totalPseudofunctor b ⋙ h.totalFunctor =
      (h.hom.app b.unop).toFunctor ⋙ CoGrothendieck.ι C.totalPseudofunctor b :=
  Functor.ext (fun _ => rfl) fun X Y u => by
    change h.totalFunctor.map ((CoGrothendieck.ι C'.totalPseudofunctor b).map u) =
      𝟙 _ ≫ (CoGrothendieck.ι C.totalPseudofunctor b).map
        ((h.hom.app b.unop).toFunctor.map u) ≫ 𝟙 _
    simp only [h.ι_map_totalFunctor b u, Category.id_comp, Category.comp_id]
    rfl

/-- The image of a covering family of one component is the covering family that degree's
functor assigns to it, included in the component of the target. -/
theorem map_ι_totalFunctor (h : SimplicialSite.Morphism C C') (b : SimplexCategoryᵒᵖ)
    {P : C'.totalPseudofunctor.obj ⟨Opposite.op b⟩} (S : Presieve P) :
    (S.map (CoGrothendieck.ι C'.totalPseudofunctor b)).map h.totalFunctor =
      (S.map (h.hom.app b.unop).toFunctor).map (CoGrothendieck.ι C.totalPseudofunctor b) := by
  apply le_antisymm <;> rintro Z f ⟨⟨hu⟩⟩
  · rw [h.ι_map_totalFunctor]
    exact Presieve.map_map (Presieve.map_map hu)
  · rw [← h.ι_map_totalFunctor]
    exact Presieve.map_map (Presieve.map_map hu)

/-- The functor between the total categories takes covering families to covering families. -/
theorem totalFunctor_coverPreserving (h : SimplicialSite.Morphism C C') :
    C'.totalCoverage ≤ C.totalCoverage.comap h.totalFunctor := by
  rintro X R ⟨S, hS, rfl⟩
  exact ⟨S.map (h.hom.app X.base.unop).toFunctor, h.coverPreserving X.base.unop X.fiber hS,
    (h.map_ι_totalFunctor X.base S).symm⟩

/-- The functor between the total categories preserves the pullbacks of a covering family. -/
@[instance]
theorem totalFunctor_pullbacksPreservedBy (h : SimplicialSite.Morphism C C') :
    C'.totalCoverage.PullbacksPreservedBy h.totalFunctor := by
  constructor
  rintro X R ⟨S, hS, rfl⟩
  constructor
  rintro Y Z f g ⟨hu⟩ ⟨hw⟩
  rename_i u _ w
  have : (C'.coverage X.base.unop).HasPullbacks := C'.coverage_hasPullbacks _
  have hSpp : S.HasPairwisePullbacks := (C'.coverage X.base.unop).hasPairwisePullbacks_of_mem hS
  have : HasPullback u w := Presieve.HasPairwisePullbacks.has_pullbacks hu hw
  have hpb : IsPullback (pullback.fst u w) (pullback.snd u w) u w := IsPullback.of_hasPullback u w
  have : PreservesLimit (cospan u w) (CoGrothendieck.ι C'.totalPseudofunctor X.base) :=
    ((C'.coverage_pullbacksPreservedBy_ι X.base.unop).preservesPairwisePullbacks_of_mem
      hS).preservesLimit hu hw
  have : PreservesLimit (cospan u w) (h.hom.app X.base.unop).toFunctor :=
    h.preservesPullbacks X.base.unop hS hw u
  have : PreservesLimit
      (cospan ((h.hom.app X.base.unop).toFunctor.map u)
        ((h.hom.app X.base.unop).toFunctor.map w))
      (CoGrothendieck.ι C.totalPseudofunctor X.base) :=
    ((C.coverage_pullbacksPreservedBy_ι X.base.unop).preservesPairwisePullbacks_of_mem
      (h.coverPreserving X.base.unop X.fiber hS)).preservesLimit
      (Presieve.map_map hu) (Presieve.map_map hw)
  have : PreservesLimit (cospan u w ⋙ (h.hom.app X.base.unop).toFunctor)
      (CoGrothendieck.ι C.totalPseudofunctor X.base) :=
    preservesLimit_of_iso_diagram _ (cospanCompIso _ u w).symm
  have : PreservesLimit (cospan u w)
      ((h.hom.app X.base.unop).toFunctor ⋙ CoGrothendieck.ι C.totalPseudofunctor X.base) :=
    comp_preservesLimit _ _
  have : PreservesLimit (cospan u w)
      (CoGrothendieck.ι C'.totalPseudofunctor X.base ⋙ h.totalFunctor) :=
    preservesLimit_of_natIso _ (eqToIso (h.ι_comp_totalFunctor X.base)).symm
  have : PreservesLimit (cospan u w ⋙ CoGrothendieck.ι C'.totalPseudofunctor X.base)
      h.totalFunctor :=
    preservesLimit_of_preserves_limit_cone
      (isLimitOfPreserves (CoGrothendieck.ι C'.totalPseudofunctor X.base) hpb.isLimit)
      (isLimitOfPreserves (CoGrothendieck.ι C'.totalPseudofunctor X.base ⋙ h.totalFunctor)
        hpb.isLimit)
  exact preservesLimit_of_iso_diagram _ (cospanCompIso _ u w)

/-- The functor between the total categories is continuous. -/
@[sga "4 VI 7.4.9" "simplicial, continuous", instance,
  stacks 0D96 "case (A), continuity of the functor of total sites"]
theorem totalFunctor_isContinuous (h : SimplicialSite.Morphism C C') :
    h.totalFunctor.IsContinuous C'.totalTopology C.totalTopology := by
  have : C'.totalCoverage.HasPullbacks := C'.totalCoverage_hasPullbacks
  have : C'.totalCoverage.IsStableUnderBaseChange := C'.totalCoverage_isStableUnderBaseChange
  have : C.totalCoverage.HasPullbacks := C.totalCoverage_hasPullbacks
  have : C.totalCoverage.IsStableUnderBaseChange := C.totalCoverage_isStableUnderBaseChange
  exact h.totalFunctor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
    C'.totalCoverage C.totalCoverage h.totalFunctor_coverPreserving

end SimplicialSite.Morphism

end CategoryTheory

end
