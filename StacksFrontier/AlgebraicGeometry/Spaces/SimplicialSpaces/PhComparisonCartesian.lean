module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectOverDescent
public import StacksFrontier.Homology.DerivedCategory.PlusModelTransport

/-!
# The comparison `h⁻¹` sends cartesian sheaves to cartesian sheaves

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S` and let
`h : Sh((Spaces/U)_total) → Sh(U_étale)` be the comparison morphism of topoi of Tag 0DHJ. In the
proof of Tag 0DHK one uses that for a cartesian sheaf `G` on `U_étale` the sheaf `h⁻¹G` on
`(Spaces/U)_total` is cartesian. This file proves it, in the form needed for Stacks 0DA8 on
`(Spaces/U)_total`: restriction of `h⁻¹G` along every cross-fibre arrow `(b, V/U_b) ⟶ (c, V/U_c)`
is bijective, assuming that for every algebraic space `Y` the inverse image along
`Y_{spaces, étale} → Spaces/Y` is fully faithful (Stacks 0DGT (1)).

The transition of `h⁻¹G` along `f : b ⟶ c` is a map of sheaves on `Spaces/U_b`, and it is tested
on maps out of it. Through the adjunction `Over.map (U f) ⊣ Over.pullback (U f)` such maps become
maps out of the restriction of `h⁻¹G` to the degree `c` into a direct image along base change by
`U f`; by the full faithfulness of `h⁻¹` and of `v⁻¹` in each degree, maps out of the restriction
of `h⁻¹G` are maps out of the restriction of `G`; and the base change of the inclusion of
`U_{c, spaces, étale}` is the inclusion of `U_{b, spaces, étale}` after the transition of
`U_étale`. The transition of `h⁻¹G` is thereby carried to the transition of `G`, which is
bijective on maps because `G` is cartesian.

## Main definitions

* `AlgebraicGeometry.Space.phBaseChangeNatIso`: base change along `U_b → U_c` of the inclusion of
  `U_{c, spaces, étale}` is the inclusion of `U_{b, spaces, étale}` after the transition.
* `AlgebraicGeometry.Space.phRestrictTransition` and
  `AlgebraicGeometry.Space.phRestrictBaseChange`: the transitions of a sheaf on
  `(Spaces/U)_total`, in the inverse-image and in the direct-image form.
* `AlgebraicGeometry.Space.etaleRestrictTransition`: the direct-image transition of a sheaf on
  `U_étale`.
* `AlgebraicGeometry.Space.phDegreeUnit`: the restriction to a degree of the unit of `h⁻¹ ⊣ h_*`.

## Main results

* `AlgebraicGeometry.Space.phRestrictBaseChange_comp`: the direct-image transitions on the two
  total sites correspond under `h_*`.
* `AlgebraicGeometry.Space.bijective_phDegreeUnit`: maps out of the restriction of `h⁻¹G` are maps
  out of the restriction of `G`.
* `AlgebraicGeometry.Space.isCartesianOnSections_phComparison_inverseImage`: `h⁻¹` sends
  cartesian sheaves to sheaves which are cartesian on sections.

## References

* [Stacks Project, Tag 0DHK](https://stacks.math.columbia.edu/tag/0DHK)
* [Stacks Project, Tag 0DHJ](https://stacks.math.columbia.edu/tag/0DHJ)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Adjunction

/-- For an adjunction whose left adjoint is fully faithful, a morphism from an object `L X` to an
object of the essential image of `L` is invertible as soon as its image under the right adjoint
is: the counit is invertible on the essential image. -/
theorem isIso_of_isIso_rightAdjoint_map {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.unit] {X : C} {Y : D} (f : L.obj X ⟶ Y)
    (hY : L.essImage Y) (hf : IsIso (R.map f)) : IsIso f := by
  have := adj.fullyFaithfulLOfIsIsoUnit.full
  have := adj.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso (adj.counit.app Y) := (adj.isIso_counit_app_iff_mem_essImage).2 hY
  have : IsIso (adj.counit.app (L.obj X)) :=
    (adj.isIso_counit_app_iff_mem_essImage).2 (L.obj_mem_essImage X)
  have e := adj.counit.naturality f
  simp only [Functor.comp_map, Functor.id_map] at e
  have : IsIso (adj.counit.app (L.obj X) ≫ f) := by
    rw [← e]
    infer_instance
  exact IsIso.of_isIso_comp_left (adj.counit.app (L.obj X)) f

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

open EtaleComponent

variable (A) in
/-- The transition functor of `U_étale` along `f : b ⟶ c`, base change of formal base changes,
on the fibres of the total pseudofunctor. -/
abbrev etaleTransition {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c) :
    (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op c⟩ ⥤
      (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩ :=
  ((etaleSimplicialSite A).totalPseudofunctor.map f.op.toLoc).toFunctor

/-- The base change along `U_b ⟶ U_c` of the realization of `y` is the realization of the formal
base change `y.push f`: the isomorphism of the two pullbacks. -/
def phBaseChangeIso {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (y : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op c⟩) :
    (Over.pullback (A.left.map f)).obj ((phComparisonDegree A c).obj y) ≅
      (phComparisonDegree A b).obj ((etaleTransition A f).obj y) :=
  Over.isoMk ((IsPullback.of_hasPullback ((phComparisonDegree A c).obj y).hom
    (A.left.map f)).isoIsPullback _ _ (isPullback_comparison f.unop y))
    ((IsPullback.of_hasPullback ((phComparisonDegree A c).obj y).hom
      (A.left.map f)).isoIsPullback_hom_snd _ _ (isPullback_comparison f.unop y))

/-- The identification `phBaseChangeIso` followed by the cartesian comparison is the first
projection of the base change. -/
theorem phBaseChangeIso_hom_left_comp {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (y : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op c⟩) :
    (phBaseChangeIso f y).hom.left ≫ comparison f.unop y =
      pullback.fst ((phComparisonDegree A c).obj y).hom (A.left.map f) :=
  (IsPullback.of_hasPullback ((phComparisonDegree A c).obj y).hom
    (A.left.map f)).isoIsPullback_hom_fst _ _ (isPullback_comparison f.unop y)

/-- The identification of `phBaseChangeIso` is natural: base change along `U_b ⟶ U_c` of the
inclusion of `U_{c, spaces, étale}` is the inclusion of `U_{b, spaces, étale}` after the transition
of `U_étale`. -/
def phBaseChangeNatIso {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c) :
    phComparisonDegree A c ⋙ Over.pullback (A.left.map f) ≅
      etaleTransition A f ⋙ phComparisonDegree A b :=
  NatIso.ofComponents (phBaseChangeIso f) (fun {y y'} k => by
    apply Over.OverMorphism.ext
    refine (isPullback_comparison f.unop y').hom_ext ?_ ?_
    · have h₁ : ((Over.pullback (A.left.map f)).map ((phComparisonDegree A c).map k)).left ≫
          pullback.fst ((phComparisonDegree A c).obj y').hom (A.left.map f) =
          pullback.fst ((phComparisonDegree A c).obj y).hom (A.left.map f) ≫
            k.hom.hom.left :=
        pullback.lift_fst _ _ _
      have h₂ : ((etaleTransition A f).map k).hom.hom.left ≫ comparison f.unop y' =
          comparison f.unop y ≫ k.hom.hom.left :=
        transition_map_hom_comp f.unop k
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) (phBaseChangeIso_hom_left_comp f y')).trans ?_
      refine h₁.trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg ((phBaseChangeIso f y).hom.left ≫ ·) h₂).symm
      refine Eq.trans ?_ (Category.assoc _ _ _)
      exact congrArg (· ≫ k.hom.hom.left) (phBaseChangeIso_hom_left_comp f y).symm
    · exact (Over.w _).trans (Over.w _).symm)

section Transitions

variable (J : GrothendieckTopology (AlgebraicSpaces B S hS))
  [hJ : ∀ X : AlgebraicSpaces B S hS,
    (SpacesEtale.inclusion B S hS X).IsContinuous (SpacesEtale.topology B S hS X) (J.over X)]

/-- The transitions of `U_étale` are continuous. -/
instance etaleTransition_isContinuous {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c) :
    (etaleTransition A f).IsContinuous (etaleDegreeTopology A c) (etaleDegreeTopology A b) :=
  ((etaleSimplicialSite A).isMorphismOfSites f.unop).isContinuous

variable (A) in
/-- Restriction of a sheaf on `(Spaces/U)_total` to the simplicial degree `b`. -/
abbrev phRestrict (b : SimplexCategoryᵒᵖ) :
    Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1)) ⥤
      Sheaf (J.over (A.left.obj b)) (Type (u + 1)) :=
  (phDegreeInclusion A b).sheafPushforwardContinuous (Type (u + 1)) (J.over (A.left.obj b))
    (SimplicialOver.totalTopology J A.left)

variable (A) in
/-- Restriction of a sheaf on `U_étale` to the simplicial degree `b`. -/
abbrev etaleRestrict (b : SimplexCategoryᵒᵖ) :
    Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)) ⥤
      Sheaf (etaleDegreeTopology A b) (Type (u + 1)) :=
  (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b
    ).sheafPushforwardContinuous (Type (u + 1)) (etaleDegreeTopology A b)
      (etaleSimplicialSite A).totalTopology

variable (A) in
/-- The direct image along `U_{b, spaces, étale} → Spaces/U_b`. -/
abbrev degreePushforward (b : SimplexCategoryᵒᵖ) :
    Sheaf (J.over (A.left.obj b)) (Type (u + 1)) ⥤ Sheaf (etaleDegreeTopology A b) (Type (u + 1)) :=
  (phComparisonDegree A b).sheafPushforwardContinuous (Type (u + 1)) (etaleDegreeTopology A b)
    (J.over (A.left.obj b))

variable (A) in
/-- The direct image along the transition of `U_étale` of `f : b ⟶ c`. -/
abbrev etaleTransitionPushforward {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c) :
    Sheaf (etaleDegreeTopology A b) (Type (u + 1)) ⥤
      Sheaf (etaleDegreeTopology A c) (Type (u + 1)) :=
  (etaleTransition A f).sheafPushforwardContinuous (Type (u + 1)) (etaleDegreeTopology A c)
    (etaleDegreeTopology A b)

/-- The restriction of `h_* F` to the degree `b` is the direct image along
`U_{b, spaces, étale} → Spaces/U_b` of the restriction of `F`. -/
def phRestrictPushforwardIso (b : SimplexCategoryᵒᵖ)
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) :
    (etaleRestrict A b).obj ((phComparisonMorphism A J).pushforward.obj F) ≅
      (degreePushforward A J b).obj ((phRestrict A J b).obj F) :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerRight (NatIso.op
    (Pseudofunctor.CoGrothendieck.ιCompFunctorFrom phComparisonFib
      (fun f => phComparisonHom f) phComparisonHom_id (fun f g => phComparisonHom_comp f g)
        b).symm) F.obj)

/-- The direct-image transition of a sheaf on `U_étale` along `f : b ⟶ c`: restriction along
the cartesian arrows `(b, y.push f) ⟶ (c, y)`. -/
def etaleRestrictTransition {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (G : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) :
    (etaleRestrict A c).obj G ⟶ (etaleTransitionPushforward A f).obj ((etaleRestrict A b).obj G) :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op
    (Pseudofunctor.CoGrothendieck.ιNatTrans (etaleSimplicialSite A).totalPseudofunctor f)) G.obj)

/-- Base change along `U_b ⟶ U_c` commutes with the inclusions of the spaces-étale sites, on
direct images. -/
def degreePushforwardBaseChangeIso {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (M : Sheaf (J.over (A.left.obj b)) (Type (u + 1))) :
    (etaleTransitionPushforward A f).obj ((degreePushforward A J b).obj M) ≅
      (degreePushforward A J c).obj
        (((Over.pullback (A.left.map f)).sheafPushforwardContinuous (Type (u + 1))
          (J.over (A.left.obj c)) (J.over (A.left.obj b))).obj M) :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerRight (NatIso.op (phBaseChangeNatIso f)) M.obj)

/-- The transition of a sheaf on `(Spaces/U)_total` along `f : b ⟶ c`, on the restriction of
the sheaf along `Over.map (U f)`: restriction along the cross-fibre arrows
`(b, V/U_b) ⟶ (c, V/U_c)`. -/
def phRestrictTransition {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) :
    ((Over.map (A.left.map f)).sheafPushforwardContinuous (Type (u + 1)) (J.over (A.left.obj b))
        (J.over (A.left.obj c))).obj ((phRestrict A J c).obj F) ⟶ (phRestrict A J b).obj F :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op
    (Grothendieck.ιNatTrans (F := SimplicialOver.slices A.left) f)) F.obj)

/-- The arrows `(b, (V/U_c) ×_{U_c} U_b) ⟶ (c, V/U_c)` of `(Spaces/U)_total`: a cross-fibre arrow
followed by the projection of the base change. -/
def phBaseChangeArrow {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c) :
    Over.pullback (A.left.map f) ⋙ phDegreeInclusion A b ⟶ phDegreeInclusion A c :=
  Functor.whiskerLeft (Over.pullback (A.left.map f))
      (Grothendieck.ιNatTrans (F := SimplicialOver.slices A.left) f) ≫
    Functor.whiskerRight (Over.mapPullbackAdj (A.left.map f)).counit (phDegreeInclusion A c)

/-- The transition of a sheaf on `(Spaces/U)_total` along `f : b ⟶ c`, in direct-image form:
restriction along the arrows `(b, V ×_{U_c} U_b) ⟶ (c, V)`. -/
def phRestrictBaseChange {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) :
    (phRestrict A J c).obj F ⟶
      ((Over.pullback (A.left.map f)).sheafPushforwardContinuous (Type (u + 1))
        (J.over (A.left.obj c)) (J.over (A.left.obj b))).obj ((phRestrict A J b).obj F) :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op (phBaseChangeArrow f)) F.obj)

/-- The arrow `(b, W ×_{U_c} U_b) ⟶ (c, W)` of `(Spaces/U)_total`, for `W` étale over `U_c`, is
the image of the cartesian arrow of `U_étale` from the formal base change, through the
identification of the base change with the realization of the formal base change. -/
theorem phBaseChangeArrow_app_comp {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (y : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op c⟩) :
    (phBaseChangeArrow f).app ((phComparisonDegree A c).obj y) ≫
        (phInclusionSquare A c).app y =
      (phDegreeInclusion A b).map (phBaseChangeIso f y).hom ≫
        (phInclusionSquare A b).app ((etaleTransition A f).obj y) ≫
          (phComparisonFunctor A).map
            ((Pseudofunctor.CoGrothendieck.ιNatTrans (etaleSimplicialSite A).totalPseudofunctor
              f).app y) := by
  refine spacesTotal_hom_ext ?_ ?_
  · exact ((Category.comp_id _).trans (Category.comp_id _)).trans
      ((Category.id_comp _).trans ((Category.id_comp _).trans (Category.id_comp _))).symm
  · have l₀ : (Grothendieck.Hom.fiber ((Grothendieck.ιNatTrans (F := SimplicialOver.slices A.left)
        f).app ((Over.pullback (A.left.map f)).obj ((phComparisonDegree A c).obj y)))).left =
        𝟙 _ := rfl
    have l₁ : (Grothendieck.Hom.fiber
        ((phBaseChangeArrow f).app ((phComparisonDegree A c).obj y))).left =
        pullback.fst ((phComparisonDegree A c).obj y).hom (A.left.map f) := by
      refine (spacesTotal_comp_fiber_left _ _).trans ?_
      refine (congrArg (· ≫ _) l₀).trans ((Category.id_comp _).trans ?_)
      exact grothendieckι_map_fiber_left c _
    have l₂ := phInclusionSquare_app_fiber_left c y
    have l₃ := phSquare_comp_fiber_left b (phBaseChangeIso f y).hom
      ((Pseudofunctor.CoGrothendieck.ιNatTrans (etaleSimplicialSite A).totalPseudofunctor f).app y)
    have l₄ := phComparisonFunctor_map_ιNatTrans_fiber_left f y
    refine (spacesTotal_comp_fiber_left _ _).trans ?_
    refine (congrArg₂ (· ≫ ·) l₁ l₂).trans ((Category.comp_id _).trans ?_)
    refine Eq.trans ?_ l₃.symm
    exact (phBaseChangeIso_hom_left_comp f y).symm.trans (congrArg (_ ≫ ·) l₄.symm)

/-- The direct-image transition of sheaves on `U_étale` is natural in the sheaf. -/
@[reassoc]
theorem etaleRestrictTransition_naturality {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    {G G' : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))} (η : G ⟶ G') :
    etaleRestrictTransition f G ≫ (etaleTransitionPushforward A f).map ((etaleRestrict A b).map η) =
      (etaleRestrict A c).map η ≫ etaleRestrictTransition f G' := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext y
  exact η.hom.naturality _

/-- The identification `degreePushforwardBaseChangeIso` is natural in the sheaf. -/
@[reassoc]
theorem degreePushforwardBaseChangeIso_naturality {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    {M M' : Sheaf (J.over (A.left.obj b)) (Type (u + 1))} (ψ : M ⟶ M') :
    (etaleTransitionPushforward A f).map ((degreePushforward A J b).map ψ) ≫
        (degreePushforwardBaseChangeIso J f M').hom =
      (degreePushforwardBaseChangeIso J f M).hom ≫ (degreePushforward A J c).map
        (((Over.pullback (A.left.map f)).sheafPushforwardContinuous (Type (u + 1))
          (J.over (A.left.obj c)) (J.over (A.left.obj b))).map ψ) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext y
  exact (ψ.hom.naturality _).symm

/-- **The transitions of a cartesian sheaf on `U_étale`, read on maps**: for a cartesian sheaf
`G`, maps out of the restriction of `G` to degree `b` are maps out of its restriction to degree
`c` into the direct image along the transition. -/
theorem bijective_etaleRestrictTransition
    {G : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))}
    (hG : (etaleSituation A).IsCartesianSheaf G) {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (N : Sheaf (etaleDegreeTopology A b) (Type (u + 1))) :
    Function.Bijective (fun κ : (etaleRestrict A b).obj G ⟶ N =>
      etaleRestrictTransition f G ≫ (etaleTransitionPushforward A f).map κ) :=
  (StacksDraft.DerivedModel.PlusTransport.isIso_homEquiv_symm_iff
    ((etaleSituation A).transitionMorphism f.unop).adj
    (((etaleSituation A).restrictTransition f.unop).app G)).1 (hG f.unop) N

/-- The adjunction `(Over.map (U f))_* ⊣ (Over.pullback (U f))_*` of restrictions of sheaves. -/
abbrev phTransitionAdjunction {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c) :
    (Over.map (A.left.map f)).sheafPushforwardContinuous (Type (u + 1)) (J.over (A.left.obj b))
        (J.over (A.left.obj c)) ⊣
      (Over.pullback (A.left.map f)).sheafPushforwardContinuous (Type (u + 1))
        (J.over (A.left.obj c)) (J.over (A.left.obj b)) :=
  (Over.mapPullbackAdj (A.left.map f)).sheafPushforwardContinuous (E := Type (u + 1))
    (J.over (A.left.obj b)) (J.over (A.left.obj c))

omit hJ in
/-- The transpose of a map out of `phRestrictTransition` is the corresponding map out of
`phRestrictBaseChange`. -/
theorem phTransitionAdjunction_homEquiv {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1)))
    {M : Sheaf (J.over (A.left.obj b)) (Type (u + 1))} (ψ : (phRestrict A J b).obj F ⟶ M) :
    (phTransitionAdjunction J f).homEquiv _ _ (phRestrictTransition J f F ≫ ψ) =
      phRestrictBaseChange J f F ≫ ((Over.pullback (A.left.map f)).sheafPushforwardContinuous
        (Type (u + 1)) (J.over (A.left.obj c)) (J.over (A.left.obj b))).map ψ := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  congr 1
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext Z
  simp only [Functor.comp_obj, phRestrictTransition, SimplicialOver.slices_obj, Cat.of_α,
    SimplicialOver.slices_map, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.sheafPushforwardContinuous_unit_app_hom_app, Over.mapPullbackAdj_counit_app,
    Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op,
    Functor.sheafPushforwardContinuous_map_hom_app, phRestrictBaseChange, phBaseChangeArrow]
  exact (F.obj.map_comp _ _).symm

/-- **The cube of direct images.** The direct-image transitions of `F` on `(Spaces/U)_total` and
of `h_* F` on `U_étale` correspond under the identifications of the restrictions of `h_* F` with
the direct images of the restrictions of `F`. -/
theorem phRestrictBaseChange_comp {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) :
    (phRestrictPushforwardIso J c F).hom ≫ (degreePushforward A J c).map
        (phRestrictBaseChange J f F) =
      etaleRestrictTransition f ((phComparisonMorphism A J).pushforward.obj F) ≫
        (etaleTransitionPushforward A f).map (phRestrictPushforwardIso J b F).hom ≫
          (degreePushforwardBaseChangeIso J f ((phRestrict A J b).obj F)).hom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext y
  induction y with | op y => ?_
  have h := congrArg (fun t => F.obj.map t.op) (phBaseChangeArrow_app_comp f y)
  simp only [op_comp, F.obj.map_comp] at h
  exact h

/-- The restriction to degree `b` of the unit `G ⟶ h_* h⁻¹ G`, read as a map to the direct image
along `U_{b, spaces, étale} → Spaces/U_b` of the restriction of `h⁻¹ G`. -/
def phDegreeUnit (b : SimplexCategoryᵒᵖ)
    (G : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) :
    (etaleRestrict A b).obj G ⟶
      (degreePushforward A J b).obj ((phRestrict A J b).obj
        ((phComparisonMorphism A J).inverseImage.obj G)) :=
  (etaleRestrict A b).map ((phComparisonMorphism A J).adj.unit.app G) ≫
    (phRestrictPushforwardIso J b _).hom

/-- **Maps out of the restriction of `h⁻¹G` are maps out of the restriction of `G`**: composition
with `phDegreeUnit` is a bijection, as soon as for every algebraic space `X` the inverse image
along `X_{spaces, étale} → Spaces/X` is fully faithful. -/
theorem bijective_phDegreeUnit
    (hX : ∀ X : AlgebraicSpaces B S hS, IsIso (spacesEtaleComparisonMorphism J X).adj.unit)
    (b : SimplexCategoryᵒᵖ) (G : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)))
    (N : Sheaf (J.over (A.left.obj b)) (Type (u + 1))) :
    Function.Bijective (fun χ : (phRestrict A J b).obj
        ((phComparisonMorphism A J).inverseImage.obj G) ⟶ N =>
      phDegreeUnit J b G ≫ (degreePushforward A J b).map χ) := by
  let adjc := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (phComparisonDegree A b) (Type (u + 1)) (etaleDegreeTopology A b) (J.over (A.left.obj b))
  have : IsIso adjc.unit :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun G' => isIso_phComparisonDegree_unit J b (hX _) G')
  have hff := fullyFaithfulPhComparisonInverseImage (A := A) J hX
  have : IsIso (phComparisonMorphism A J).adj.unit :=
    @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _ _ hff.full hff.faithful
  have hg : IsIso (phDegreeUnit J b G) := by
    unfold phDegreeUnit
    infer_instance
  have hBC : IsIso ((adjc.homEquiv _ _).symm (phDegreeUnit J b G)) := by
    refine adjc.isIso_of_isIso_rightAdjoint_map _ ⟨(etaleRestrict A b).obj G,
      ⟨((Functor.sheafPullbackConstruction.sheafPullbackIso (phComparisonDegree A b)
        (Type (u + 1)) (etaleDegreeTopology A b) (J.over (A.left.obj b))).app _).symm ≪≫
          ((phRestrictInverseImageIso J b).app G).symm⟩⟩ ?_
    have e : adjc.unit.app _ ≫ (degreePushforward A J b).map
        ((adjc.homEquiv _ _).symm (phDegreeUnit J b G)) = phDegreeUnit J b G :=
      (adjc.homEquiv_unit _ _ _).symm.trans ((adjc.homEquiv _ _).apply_symm_apply _)
    have : IsIso (adjc.unit.app ((etaleRestrict A b).obj G) ≫ (degreePushforward A J b).map
        ((adjc.homEquiv _ _).symm (phDegreeUnit J b G))) := by
      rw [e]
      exact hg
    exact IsIso.of_isIso_comp_left (adjc.unit.app _) _
  exact (StacksDraft.DerivedModel.PlusTransport.isIso_homEquiv_symm_iff adjc _).1 hBC N

/-- **`h⁻¹` sends cartesian sheaves to sheaves which are cartesian on sections.** Let `G` be a
cartesian sheaf on `U_étale`, and assume that for every algebraic space `X` the inverse image
along `X_{spaces, étale} → Spaces/X` is fully faithful. Then restriction of `h⁻¹G` along every
cross-fibre arrow `(n, V/U_n) ⟶ (m, V/U_m)` of `(Spaces/U)_total` is bijective.

The transition of `h⁻¹G` is tested on maps out of it: maps out of the restriction of `h⁻¹G` to a
degree are maps out of the restriction of `G` (`bijective_phDegreeUnit`), and under this the
transition of `h⁻¹G` becomes the transition of `G` followed by the base change of
`phBaseChangeNatIso` (`phRestrictBaseChange_comp`), which is bijective on maps because `G` is
cartesian. -/
theorem isCartesianOnSections_phComparison_inverseImage
    (hX : ∀ X : AlgebraicSpaces B S hS, IsIso (spacesEtaleComparisonMorphism J X).adj.unit)
    {G : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))}
    (hG : (etaleSituation A).IsCartesianSheaf G) :
    SimplicialOver.IsCartesianOnSections A.left
      ((phComparisonMorphism A J).inverseImage.obj G) := by
  intro m n φ V
  let F' := (phComparisonMorphism A J).inverseImage.obj G
  let f : op n ⟶ op m := φ.op
  let pbS := (Over.pullback (A.left.map f)).sheafPushforwardContinuous (Type (u + 1))
    (J.over (A.left.obj (op m))) (J.over (A.left.obj (op n)))
  have hΦ : ∀ M, Function.Bijective (fun ψ : (phRestrict A J (op n)).obj F' ⟶ M =>
      phRestrictBaseChange J f F' ≫ pbS.map ψ) := by
    intro M
    have hc := bijective_phDegreeUnit J hX (op m) G (pbS.obj M)
    have hb := bijective_phDegreeUnit J hX (op n) G M
    have hψ := bijective_etaleRestrictTransition hG f ((degreePushforward A J (op n)).obj M)
    let σ := degreePushforwardBaseChangeIso J f M
    have hσ : Function.Bijective (fun κ : (etaleRestrict A (op m)).obj G ⟶
        (etaleTransitionPushforward A f).obj ((degreePushforward A J (op n)).obj M) =>
          κ ≫ σ.hom) :=
      Function.bijective_iff_has_inverse.2 ⟨fun κ => κ ≫ σ.inv, fun κ => by simp,
        fun κ => by simp⟩
    have heq : (fun χ : (phRestrict A J (op m)).obj F' ⟶ pbS.obj M =>
          phDegreeUnit J (op m) G ≫ (degreePushforward A J (op m)).map χ) ∘
        (fun ψ : (phRestrict A J (op n)).obj F' ⟶ M => phRestrictBaseChange J f F' ≫ pbS.map ψ) =
        ((fun κ => κ ≫ σ.hom) ∘ (fun κ : (etaleRestrict A (op n)).obj G ⟶
          (degreePushforward A J (op n)).obj M =>
            etaleRestrictTransition f G ≫ (etaleTransitionPushforward A f).map κ)) ∘
        (fun χ : (phRestrict A J (op n)).obj F' ⟶ M =>
          phDegreeUnit J (op n) G ≫ (degreePushforward A J (op n)).map χ) := by
      funext ψ
      simp only [Function.comp_apply, phDegreeUnit, Functor.map_comp, Category.assoc]
      rw [reassoc_of% (phRestrictBaseChange_comp J f F'),
        etaleRestrictTransition_naturality_assoc, degreePushforwardBaseChangeIso_naturality]
      rfl
    exact (Function.Bijective.of_comp_iff' hc _).1 (heq ▸ (hσ.comp hψ).comp hb)
  have key : IsIso (phRestrictTransition J f F') := by
    rw [isIso_iff_coyoneda_map_bijective]
    intro M
    have e : (fun ψ : (phRestrict A J (op n)).obj F' ⟶ M =>
        (phTransitionAdjunction J f).homEquiv _ M (phRestrictTransition J f F' ≫ ψ)) =
        fun ψ => phRestrictBaseChange J f F' ≫ pbS.map ψ :=
      funext (phTransitionAdjunction_homEquiv J f F')
    have h := hΦ M
    rw [← e] at h
    exact (Equiv.comp_bijective (fun ψ => phRestrictTransition J f F' ≫ ψ)
      ((phTransitionAdjunction J f).homEquiv _ M)).1 h
  exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _
    ((sheafToPresheaf _ _).map (phRestrictTransition J f F')) inferInstance (op V)

end Transitions

end AlgebraicGeometry.Space

end
