module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonSquare
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismCaseA

/-!
# The inverse image along the ph comparison of a simplicial algebraic space

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S` and let
`h : Sh((Spaces/U)_total) → Sh(U_étale)` be the comparison morphism of topoi of Tag 0DHJ, given by
the functor `w : U_{spaces, étale} ⥤ (Spaces/U)_total`, `V/U_n ↦ V/U_n`. In the proof of Tag 0DHK
the full faithfulness of `h⁻¹` is deduced from that of its components
`h_n⁻¹ : Sh(U_{n, étale}) ⥤ Sh(Spaces/U_n)` (Stacks 0DGT (1)) through the description of `h⁻¹`
in each simplicial degree (Tag 0D96). This file carries out that deduction for any topology on
algebraic spaces whose localizations receive the spaces-étale sites continuously.

The description of `h⁻¹` in degree `b` comes from the square formed by the inclusions of the
degree `b` into the two total categories, the comparison functor `v_b` of the degree and `w`: it
is Guitart exact, because an arrow `V/U_b ⟶ W/U_c` with `W` étale over `U_c` factors uniquely
through the cartesian arrow out of the formal base change `W ×_{U_c} U_b`. Hence restricting a
left Kan extension along `w` to the degree `b` is the left Kan extension along `v_b` of the
restriction, and sheafification commutes with restriction to a degree.

## Main definitions

* `AlgebraicGeometry.Space.phComparisonDegree`: the comparison functor `v_b` in simplicial degree
  `b`, from the degree-`b` component of `U_{spaces, étale}` to `Spaces/U_b`.
* `AlgebraicGeometry.Space.phDegreeInclusion`: the inclusion of the simplicial degree `b` into
  `(Spaces/U)_total`.
* `AlgebraicGeometry.Space.phInclusionSquare`: the commutative square of the inclusions of a
  simplicial degree and the comparison functors.
* `AlgebraicGeometry.Space.fullyFaithfulPhComparisonInverseImage`: full faithfulness of `h⁻¹`.
* `AlgebraicGeometry.Space.phRestrictInverseImageIso`: **Tag 0D96 for `h`**, the restriction of
  `h⁻¹G` to the degree `b` is `v_b⁻¹` of the restriction of `G`.

## Main results

* `AlgebraicGeometry.Space.guitartExact_phInclusionSquare`: the square is Guitart exact.
* `AlgebraicGeometry.Space.isIso_toSheafify_lan_app`: the sheafification of the left Kan
  extension along `w` is bijective on the sections over the objects étale over some `U_b`.
* `AlgebraicGeometry.Space.isIso_phComparison_unit`: the unit of `h⁻¹ ⊣ h_*` is invertible as
  soon as the units of the components are.
* `AlgebraicGeometry.Space.mem_essImage_phRestrict_inverseImage`: the restriction of `h⁻¹G` to a
  simplicial degree is in the essential image of the inverse image of that degree.

## Implementation notes

The degree-`b` component of `U_{spaces, étale}` is used in the spelling of the fibre of the total
pseudofunctor, which is the domain of the inclusion of the degree into the total category, so that
the square of the inclusions has a single source category; its topology there is
`AlgebraicGeometry.Space.etaleDegreeTopology`. The inverse images along `w` and along `v_b` are
compared through the constructed sheafified left Kan extensions
(`CategoryTheory.Functor.sheafPullbackConstruction`), whose units are explicit.

## References

* [Stacks Project, Tag 0DHK](https://stacks.math.columbia.edu/tag/0DHK)
* [Stacks Project, Tag 0DHJ](https://stacks.math.columbia.edu/tag/0DHJ)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0DGT](https://stacks.math.columbia.edu/tag/0DGT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

open EtaleComponent

variable (A) in
/-- The comparison functor in simplicial degree `b`: an object étale over `U_b`, presented as a
formal base change, goes to its realization in `Spaces/U_b`. -/
abbrev phComparisonDegree (b : SimplexCategoryᵒᵖ) :
    (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩ ⥤ Over (A.left.obj b) :=
  realizeFunctor (A := A) b.unop ⋙ SpacesEtale.inclusion B S hS (A.left.obj b)

variable (A) in
/-- The inclusion `V/U_b ↦ V/U_b` of the simplicial degree `b` into `(Spaces/U)_total`. -/
abbrev phDegreeInclusion (b : SimplexCategoryᵒᵖ) : Over (A.left.obj b) ⥤ SpacesTotal A :=
  Grothendieck.ι (SimplicialOver.slices A.left) b

variable (A) in
/-- The square formed by the inclusions of the simplicial degree `b` into the total categories of
`U_{spaces, étale}` and of `(Spaces/U)_total`, the comparison functor in degree `b` and the
comparison functor of the total categories. It commutes on the nose. -/
def phInclusionSquare (b : SimplexCategoryᵒᵖ) :
    TwoSquare (phComparisonDegree A b)
      (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b)
      (phDegreeInclusion A b) (phComparisonFunctor A) :=
  TwoSquare.mk _ _ _ _ (Pseudofunctor.CoGrothendieck.ιCompFunctorFrom phComparisonFib
    (fun f => phComparisonHom f) phComparisonHom_id (fun f g => phComparisonHom_comp f g) b).inv

/-- The comparison functor of a simplicial degree is full. -/
instance phComparisonDegree_full (b : SimplexCategoryᵒᵖ) : (phComparisonDegree A b).Full :=
  inferInstanceAs (realizeFunctor (A := A) b.unop ⋙
    SpacesEtale.inclusion B S hS (A.left.obj b)).Full

/-- The comparison functor of a simplicial degree is faithful. -/
instance phComparisonDegree_faithful (b : SimplexCategoryᵒᵖ) :
    (phComparisonDegree A b).Faithful :=
  inferInstanceAs (realizeFunctor (A := A) b.unop ⋙
    SpacesEtale.inclusion B S hS (A.left.obj b)).Faithful

/-- The 2-cell of `phInclusionSquare` is an identity. -/
@[simp]
theorem phInclusionSquare_app (b : SimplexCategoryᵒᵖ)
    (y : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩) :
    (phInclusionSquare A b).natTrans.app y = 𝟙 _ :=
  rfl

/-- The underlying morphism of algebraic spaces of the 2-cell of `phInclusionSquare` is an
identity. -/
theorem phInclusionSquare_app_fiber_left (b : SimplexCategoryᵒᵖ)
    (y : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩) :
    (Grothendieck.Hom.fiber ((phInclusionSquare A b).natTrans.app y)).left = 𝟙 _ := by
  rw [phInclusionSquare_app]
  exact spacesTotal_id_fiber_left _

/-- An arrow inside degree `b`, followed by the square and by the image of an arrow of
`U_étale`, has as underlying morphism of algebraic spaces the composite of the two. -/
theorem phSquare_comp_fiber_left (b : SimplexCategoryᵒᵖ) {V : Over (A.left.obj b)}
    {z : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩} {Y : EtaleTotal A}
    (a : V ⟶ (phComparisonDegree A b).obj z)
    (β : (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b).obj z ⟶ Y) :
    (Grothendieck.Hom.fiber ((phDegreeInclusion A b).map a ≫
      (phInclusionSquare A b).natTrans.app z ≫ (phComparisonFunctor A).map β)).left =
      a.left ≫ (Grothendieck.Hom.fiber ((phComparisonFunctor A).map β)).left := by
  refine (spacesTotal_comp_fiber_left _ _).trans ?_
  refine congrArg₂ (· ≫ ·) (grothendieckι_map_fiber_left b a) ?_
  refine (spacesTotal_comp_fiber_left _ _).trans ?_
  exact (congrArg (· ≫ _) (phInclusionSquare_app_fiber_left b z)).trans (Category.id_comp _)

/-- The comparison functor sends a cartesian arrow of `U_étale` to the cartesian comparison of
realizations. -/
theorem phComparisonFunctor_map_ιNatTrans_fiber_left {b c : SimplexCategoryᵒᵖ} (f : b ⟶ c)
    (y : EtaleComponent A c.unop) :
    (Grothendieck.Hom.fiber ((phComparisonFunctor A).map
      ((Pseudofunctor.CoGrothendieck.ιNatTrans (etaleSimplicialSite A).totalPseudofunctor f).app
        y))).left = comparison f.unop y := by
  have h : (Grothendieck.Hom.fiber ((phComparisonFunctor A).map
      ((Pseudofunctor.CoGrothendieck.ιNatTrans (etaleSimplicialSite A).totalPseudofunctor f).app
        y))).left = Over.Hom.left ((Pseudofunctor.CoGrothendieck.ιNatTrans
          (etaleSimplicialSite A).totalPseudofunctor f).app y).fiber.hom.hom ≫
      comparison f.unop y :=
    phComparisonFunctor_map_fiber_left _
  have e : Over.Hom.left ((Pseudofunctor.CoGrothendieck.ιNatTrans
      (etaleSimplicialSite A).totalPseudofunctor f).app y).fiber.hom.hom =
      𝟙 (realize (y.push f.unop)).obj.left := rfl
  exact h.trans ((congrArg (· ≫ comparison f.unop y) e).trans (Category.id_comp _))

/-- The factorization of an arrow `(f, k) : V/U_b ⟶ W/U_c` of `(Spaces/U)_total`, with `W`
étale over `U_c` the realization of `y`, through the base change `W ×_{U_c} U_b`: the induced
morphism `V ⟶ W ×_{U_c} U_b` over `U_b`. -/
def phFactorLift {b c : SimplexCategoryᵒᵖ} (V : Over (A.left.obj b))
    (y : EtaleComponent A c.unop) (f : b ⟶ c)
    (k : (Over.map (A.left.map f)).obj V ⟶ (realize y).obj) :
    V ⟶ (realize (y.push f.unop)).obj :=
  Over.homMk ((isPullback_comparison f.unop y).lift k.left V.hom (Over.w k))
    ((isPullback_comparison f.unop y).lift_snd _ _ _)

/-- The factorization `phFactorLift` followed by the cartesian comparison is the given arrow. -/
theorem phFactorLift_left_comp {b c : SimplexCategoryᵒᵖ} (V : Over (A.left.obj b))
    (y : EtaleComponent A c.unop) (f : b ⟶ c)
    (k : (Over.map (A.left.map f)).obj V ⟶ (realize y).obj) :
    (phFactorLift V y f k).left ≫ comparison f.unop y = k.left :=
  (isPullback_comparison f.unop y).lift_fst _ _ _

/-- An arrow `(f, k) : V/U_b ⟶ W/U_c` of `(Spaces/U)_total` is the factorization `phFactorLift`
followed by the image of the cartesian arrow of `U_étale`. -/
theorem phFactor_comm {b c : SimplexCategoryᵒᵖ} (V : Over (A.left.obj b))
    (y : EtaleComponent A c.unop) (f : b ⟶ c)
    (k : (Over.map (A.left.map f)).obj V ⟶ (realize y).obj) :
    (phDegreeInclusion A b).map (phFactorLift V y f k) ≫
      (phInclusionSquare A b).natTrans.app (y.push f.unop) ≫ (phComparisonFunctor A).map
        ((Pseudofunctor.CoGrothendieck.ιNatTrans (etaleSimplicialSite A).totalPseudofunctor
          f).app y) =
      (⟨f, k⟩ : (phDegreeInclusion A b).obj V ⟶
        (phComparisonFunctor A).obj
          ((Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor c).obj
            y)) := by
  refine spacesTotal_hom_ext ?_ ?_
  · exact (Category.id_comp _).trans ((Category.id_comp _).trans (Category.id_comp _))
  · exact (phSquare_comp_fiber_left b _ _).trans ((congrArg (_ ≫ ·)
      (phComparisonFunctor_map_ιNatTrans_fiber_left f y)).trans (phFactorLift_left_comp V y f k))

/-- An arrow `a : V ⟶ W'` of `Spaces/U_b`, followed by the image of an arrow `W' ⟶ y.push f` of
the degree-`b` component, agrees with `phFactorLift` as soon as the two composites to the
realization of `y` agree. -/
theorem phFactorLift_unique {b c : SimplexCategoryᵒᵖ} (V : Over (A.left.obj b))
    (y : EtaleComponent A c.unop) (f : b ⟶ c)
    (k : (Over.map (A.left.map f)).obj V ⟶ (realize y).obj)
    {z : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩}
    (a : V ⟶ (phComparisonDegree A b).obj z)
    (β : z ⟶ ((etaleSimplicialSite A).totalPseudofunctor.map f.op.toLoc).toFunctor.obj y)
    (h : a.left ≫ β.hom.hom.left ≫ comparison f.unop y = k.left) :
    a ≫ (phComparisonDegree A b).map β = phFactorLift V y f k := by
  apply Over.OverMorphism.ext
  refine (isPullback_comparison f.unop y).hom_ext ?_ ?_
  · exact ((Category.assoc _ _ _).trans h).trans (phFactorLift_left_comp V y f k).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (a.left ≫ ·) (Over.w β.hom.hom)).trans ?_
    exact (Over.w a).trans ((isPullback_comparison f.unop y).lift_snd _ _ _).symm

/-- **The square of the inclusions of a simplicial degree is Guitart exact.** Every arrow
`V/U_b ⟶ W/U_c` of `(Spaces/U)_total` with `W` étale over `U_c` factors through the cartesian
arrow from the base change `W ×_{U_c} U_b`, and that factorization is terminal among all
factorizations through objects étale over `U_b`. -/
instance guitartExact_phInclusionSquare (b : SimplexCategoryᵒᵖ) :
    (phInclusionSquare A b).GuitartExact := by
  constructor
  intro V Y g
  have comm : (phDegreeInclusion A b).map
      (phFactorLift V Y.fiber g.base g.fiber) ≫
      (phInclusionSquare A b).natTrans.app (Y.fiber.push g.base.unop) ≫
        (phComparisonFunctor A).map ((Pseudofunctor.CoGrothendieck.ιNatTrans
          (etaleSimplicialSite A).totalPseudofunctor g.base).app Y.fiber) = g :=
    phFactor_comm V Y.fiber g.base g.fiber
  have hterminal : ∀ Q : (phInclusionSquare A b).StructuredArrowRightwards g,
      Nonempty (Q ⟶ TwoSquare.StructuredArrowRightwards.mk (phInclusionSquare A b) g
        (Y.fiber.push g.base.unop) (phFactorLift V Y.fiber g.base g.fiber)
        ((Pseudofunctor.CoGrothendieck.ιNatTrans (etaleSimplicialSite A).totalPseudofunctor
          g.base).app Y.fiber) comm) := by
    intro Q
    obtain ⟨z, a, β, hcomm, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective Q
    have hb : β.base = g.base := by
      refine Eq.trans ?_ (congrArg Grothendieck.Hom.base hcomm)
      exact ((Category.id_comp _).trans ((Category.id_comp _).trans (Category.id_comp _))).symm
    obtain ⟨fb, β'⟩ := β
    dsimp only at hb
    subst hb
    have hl := (phSquare_comp_fiber_left b a _).symm.trans (congrArg SpacesTotal.homLeft hcomm)
    have hw := phComparisonFunctor_map_fiber_left
      (⟨g.base, β'⟩ : (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor
        b).obj z ⟶ Y)
    have h₁ : (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b).map β' ≫
        (Pseudofunctor.CoGrothendieck.ιNatTrans (etaleSimplicialSite A).totalPseudofunctor
          g.base).app Y.fiber = ⟨g.base, β'⟩ :=
      Pseudofunctor.CoGrothendieck.ι_map_comp_ιNatTrans_app _ g.base β'
    let φ := CostructuredArrow.homMk (S := Pseudofunctor.CoGrothendieck.ι
      (etaleSimplicialSite A).totalPseudofunctor b) (T := Y) (f := CostructuredArrow.mk
        (⟨g.base, β'⟩ : (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor
          b).obj z ⟶ Y)) (f' := CostructuredArrow.mk ((Pseudofunctor.CoGrothendieck.ιNatTrans
            (etaleSimplicialSite A).totalPseudofunctor g.base).app Y.fiber)) β' h₁
    refine ⟨StructuredArrow.homMk φ (CostructuredArrow.hom_ext _ _ ?_)⟩
    exact phFactorLift_unique V Y.fiber g.base g.fiber a β'
      ((congrArg (a.left ≫ ·) hw).symm.trans hl)
  have : Nonempty ((phInclusionSquare A b).StructuredArrowRightwards g) :=
    ⟨TwoSquare.StructuredArrowRightwards.mk (phInclusionSquare A b) g _ _ _ comm⟩
  exact zigzag_isConnected fun Q₁ Q₂ =>
    (Zigzag.of_hom (hterminal Q₁).some).trans (Zigzag.of_inv (hterminal Q₂).some)

/-! ### Full faithfulness of `h⁻¹` -/

section FullyFaithful

variable (J : GrothendieckTopology (AlgebraicSpaces B S hS))
  [hJ : ∀ X : AlgebraicSpaces B S hS,
    (SpacesEtale.inclusion B S hS X).IsContinuous (SpacesEtale.topology B S hS X) (J.over X)]

/-- The inclusion of a simplicial degree into `(Spaces/U)_total` is continuous. -/
instance phDegreeInclusion_isContinuous (b : SimplexCategoryᵒᵖ) :
    (phDegreeInclusion A b).IsContinuous (J.over (A.left.obj b))
      (SimplicialOver.totalTopology J A.left) := by
  have h := SimplicialSiteSituation.componentFunctor_isContinuous
    (SimplicialOver.situation J A.left) b.unop
  rwa [SimplicialOver.componentTopology_eq, SimplicialOver.totalTopology_eq] at h

/-- The inclusion of a simplicial degree into `(Spaces/U)_total` is cocontinuous. -/
instance phDegreeInclusion_isCocontinuous (b : SimplexCategoryᵒᵖ) :
    (phDegreeInclusion A b).IsCocontinuous (J.over (A.left.obj b))
      (SimplicialOver.totalTopology J A.left) := by
  have h := SimplicialSiteSituation.componentFunctor_isCocontinuous
    (SimplicialOver.situation J A.left) b.unop
  rwa [SimplicialOver.componentTopology_eq, SimplicialOver.totalTopology_eq] at h

variable (A) in
/-- The topology of the degree-`b` component of `U_{spaces, étale}`, on the fibre of the total
pseudofunctor. -/
def etaleDegreeTopology (b : SimplexCategoryᵒᵖ) :
    GrothendieckTopology ((etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩) :=
  (precoverage (A := A) b.unop).toGrothendieck

/-- The comparison functor of a simplicial degree is continuous. -/
instance phComparisonDegree_isContinuous (b : SimplexCategoryᵒᵖ) :
    (phComparisonDegree A b).IsContinuous (etaleDegreeTopology A b) (J.over (A.left.obj b)) :=
  phComparisonFib_realize_isContinuous J b

/-- The underlying presheaf map of the unit of the constructed adjunction `G⁻¹ ⊣ G_*` is the unit
of the left Kan extension followed by the map to the sheafification. -/
private theorem map_sheafAdjunctionContinuous_unit_app {C : Type*} [Category C] {D : Type*}
    [Category D] (G : C ⥤ D) (A : Type*) [Category A] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [G.IsContinuous J K]
    [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F] [HasWeakSheafify K A] (P : Sheaf J A) :
    (sheafToPresheaf _ _).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app P) =
      G.op.lanUnit.app P.obj ≫
        Functor.whiskerLeft G.op (toSheafify K (G.op.lan.obj P.obj)) := by
  have := Adjunction.map_restrictFullyFaithful_unit_app
    (adj := (G.op.lanAdjunction A).comp (sheafificationAdjunction K A))
    (hiC := fullyFaithfulSheafToPresheaf J A) (hiD := Functor.FullyFaithful.id (Sheaf K A))
    (L := Functor.sheafPullbackConstruction.sheafPullback G A J K)
    (R := G.sheafPushforwardContinuous A J K) (comm1 := Iso.refl _) (comm2 := Iso.refl _) P
  refine this.trans ?_
  simp only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    sheafificationAdjunction_unit_app, Iso.refl_hom, NatTrans.id_app, Category.assoc]
  simp only [Functor.id_obj, ObjectProperty.ι_obj, Functor.comp_obj,
    Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map]
  erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- If the unit of the constructed adjunction `v⁻¹ ⊣ v_*` of the degree-`b` comparison functor is
invertible at a sheaf `G`, the canonical map from the left Kan extension of `G` to its
sheafification is bijective on the sections over the objects of `U_{b, spaces, étale}`. -/
theorem isIso_toSheafify_lan_app_of_isIso_unit (b : SimplexCategoryᵒᵖ)
    (G : Sheaf (etaleDegreeTopology A b) (Type (u + 1)))
    (hG : IsIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (phComparisonDegree A b) (Type (u + 1)) (etaleDegreeTopology A b)
        (J.over (A.left.obj b))).unit.app G))
    (y : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩) :
    IsIso ((toSheafify (J.over (A.left.obj b))
      ((phComparisonDegree A b).op.lan.obj G.obj)).app (op ((phComparisonDegree A b).obj y))) := by
  have h₁ := (sheafToPresheaf _ _).map_isIso
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (phComparisonDegree A b)
      (Type (u + 1)) (etaleDegreeTopology A b) (J.over (A.left.obj b))).unit.app G)
  have e := map_sheafAdjunctionContinuous_unit_app (phComparisonDegree A b) (Type (u + 1))
    (etaleDegreeTopology A b) (J.over (A.left.obj b)) G
  rw [e] at h₁
  have h₂ := @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ h₁ (op y)
  rw [NatTrans.comp_app, Functor.whiskerLeft_app] at h₂
  have : (phComparisonDegree A b).op.HasPointwiseLeftKanExtension G.obj := inferInstance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    (((phComparisonDegree A b).op.lanUnit.app G.obj).app (op y)) _ inferInstance h₂

/-- The inclusion of a simplicial degree into `U_étale` is continuous. -/
instance etaleDegreeInclusion_isContinuous (b : SimplexCategoryᵒᵖ) :
    (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b).IsContinuous
      (etaleDegreeTopology A b) (etaleSimplicialSite A).totalTopology :=
  SimplicialSiteSituation.componentFunctor_isContinuous (etaleSituation A) b.unop

/-- The inclusion of a simplicial degree into `U_étale` is cocontinuous. -/
instance etaleDegreeInclusion_isCocontinuous (b : SimplexCategoryᵒᵖ) :
    (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b).IsCocontinuous
      (etaleDegreeTopology A b) (etaleSimplicialSite A).totalTopology :=
  SimplicialSiteSituation.componentFunctor_isCocontinuous (etaleSituation A) b.unop

/-- **The sections of the sheafified left Kan extension along the comparison functor**, over the
objects of the image: if in every degree the unit of `v⁻¹ ⊣ v_*` is invertible, then for every
sheaf `G` on `U_étale` the canonical map from the left Kan extension of `G` along
`V/U_n ↦ V/U_n` to its sheafification is bijective on sections over `V/U_b`, `V` étale over
`U_b`. The left Kan extension restricted to degree `b` is the left Kan extension of the restriction
of `G` (Guitart exactness of `phInclusionSquare`), and sheafification commutes with restriction to
degree `b`, the inclusion of the degree being continuous and cocontinuous. -/
theorem isIso_toSheafify_lan_app (b : SimplexCategoryᵒᵖ)
    (hv : ∀ G : Sheaf (etaleDegreeTopology A b) (Type (u + 1)),
      IsIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (phComparisonDegree A b) (Type (u + 1)) (etaleDegreeTopology A b)
          (J.over (A.left.obj b))).unit.app G))
    (G : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)))
    (y : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩) :
    IsIso ((toSheafify (SimplicialOver.totalTopology J A.left)
      ((phComparisonFunctor A).op.lan.obj G.obj)).app
        (op ((phDegreeInclusion A b).obj ((phComparisonDegree A b).obj y)))) := by
  let P := (phComparisonFunctor A).op.lan.obj G.obj
  let G' : Sheaf (etaleDegreeTopology A b) (Type (u + 1)) :=
    (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b
      ).sheafPushforwardContinuous (Type (u + 1)) (etaleDegreeTopology A b)
        (etaleSimplicialSite A).totalTopology |>.obj G
  -- the left Kan extension of the restriction, sheafified, at the objects of the image
  have h₁ := isIso_toSheafify_lan_app_of_isIso_unit J b G' (hv G') y
  -- base change of left Kan extensions
  let θ := (phInclusionSquare A b).op.lanBaseChange.app G.obj
  have hθ : IsIso θ := inferInstance
  let x := op ((phComparisonDegree A b).obj y)
  have hn' : θ.app x ≫ (toSheafify (J.over (A.left.obj b)) ((phDegreeInclusion A b).op ⋙ P)).app x =
      (toSheafify (J.over (A.left.obj b)) ((phComparisonDegree A b).op.lan.obj G'.obj)).app x ≫
        (sheafifyMap (J.over (A.left.obj b)) θ).app x :=
    NatTrans.congr_app (toSheafify_naturality (J := J.over (A.left.obj b)) θ) x
  have h₂ : IsIso ((sheafifyMap (J.over (A.left.obj b)) θ).app x) :=
    NatIso.isIso_app_of_isIso _ _
  have h₃ : IsIso ((toSheafify (J.over (A.left.obj b))
      ((phDegreeInclusion A b).op ⋙ P)).app x) := by
    have : IsIso (θ.app x ≫ (toSheafify (J.over (A.left.obj b))
        ((phDegreeInclusion A b).op ⋙ P)).app x) := by
      rw [hn']
      exact IsIso.comp_isIso' h₁ h₂
    exact IsIso.of_isIso_comp_left (θ.app x) _
  have hc' : (toSheafify (J.over (A.left.obj b)) ((phDegreeInclusion A b).op ⋙ P)).app x ≫
      (((phDegreeInclusion A b).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
        (J.over (A.left.obj b)) (SimplicialOver.totalTopology J A.left)).hom.app P).hom.app x =
      (toSheafify (SimplicialOver.totalTopology J A.left)
        ((phComparisonFunctor A).op.lan.obj G.obj)).app
          (op ((phDegreeInclusion A b).obj ((phComparisonDegree A b).obj y))) :=
    NatTrans.congr_app ((phDegreeInclusion A b).toSheafify_pullbackSheafificationCompatibility
      (Type (u + 1)) (J.over (A.left.obj b)) (SimplicialOver.totalTopology J A.left) P) x
  rw [← hc']
  exact IsIso.comp_isIso' h₃ (((sheafToPresheaf _ _).mapIso
    (((phDegreeInclusion A b).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (J.over (A.left.obj b)) (SimplicialOver.totalTopology J A.left)).app P)).app x).isIso_hom

/-- In simplicial degree `b` the unit of `v⁻¹ ⊣ v_*` is invertible as soon as the inverse image
along the inclusion `U_{b, spaces, étale} → Spaces/U_b` is fully faithful: the degree-`b` component
of `U_étale` is a strict model of `U_{b, spaces, étale}`, its realization functor inducing an
equivalence of topoi. -/
theorem isIso_phComparisonDegree_unit (b : SimplexCategoryᵒᵖ)
    (hX : IsIso (spacesEtaleComparisonMorphism J (A.left.obj b)).adj.unit)
    (G : Sheaf (etaleDegreeTopology A b) (Type (u + 1))) :
    IsIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (phComparisonDegree A b) (Type (u + 1)) (etaleDegreeTopology A b)
        (J.over (A.left.obj b))).unit.app G) := by
  let E := sheafEquiv (A := A) b.unop (Type (u + 1))
  let h := spacesEtaleComparisonMorphism J (A.left.obj b)
  let adj₂ : E.functor ⋙ h.inverseImage ⊣
      (phComparisonDegree A b).sheafPushforwardContinuous (Type (u + 1))
        (etaleDegreeTopology A b) (J.over (A.left.obj b)) :=
    E.toAdjunction.comp h.adj
  let adjc := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (phComparisonDegree A b) (Type (u + 1)) (etaleDegreeTopology A b) (J.over (A.left.obj b))
  have hffc := (E.fullyFaithfulFunctor.comp h.adj.fullyFaithfulLOfIsIsoUnit).ofIso
    (adjc.leftAdjointUniq adj₂).symm
  exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _
    (@Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _ adjc hffc.full hffc.faithful) G

/-- **The unit of `h⁻¹ ⊣ h_*` is invertible**, granted that in every simplicial degree the unit of
`v⁻¹ ⊣ v_*` is invertible, `v : U_{b, spaces, étale} → Spaces/U_b` the inclusion. The unit at a
sheaf `G` on `U_étale` is the unit of the left Kan extension along the fully faithful comparison
functor, which is invertible, followed by the canonical map to the sheafification, which is
bijective on the sections over every object of `U_étale` by `isIso_toSheafify_lan_app`. -/
theorem isIso_phComparison_unit
    (hv : ∀ (b : SimplexCategoryᵒᵖ) (G : Sheaf (etaleDegreeTopology A b) (Type (u + 1))),
      IsIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (phComparisonDegree A b) (Type (u + 1)) (etaleDegreeTopology A b)
          (J.over (A.left.obj b))).unit.app G)) :
    haveI := phComparisonFunctor_isContinuous (A := A) J
    IsIso (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (phComparisonFunctor A)
      (Type (u + 1)) (etaleSimplicialSite A).totalTopology
        (SimplicialOver.totalTopology J A.left)).unit := by
  have := phComparisonFunctor_isContinuous (A := A) J
  have key : ∀ G, IsIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (phComparisonFunctor A) (Type (u + 1)) (etaleSimplicialSite A).totalTopology
        (SimplicialOver.totalTopology J A.left)).unit.app G) := by
    intro G
    have e := map_sheafAdjunctionContinuous_unit_app (phComparisonFunctor A) (Type (u + 1))
      (etaleSimplicialSite A).totalTopology (SimplicialOver.totalTopology J A.left) G
    have hp : IsIso ((phComparisonFunctor A).op.lanUnit.app G.obj ≫
        Functor.whiskerLeft (phComparisonFunctor A).op
          (toSheafify (SimplicialOver.totalTopology J A.left)
            ((phComparisonFunctor A).op.lan.obj G.obj))) := by
      have : ∀ z, IsIso (((phComparisonFunctor A).op.lanUnit.app G.obj ≫
          Functor.whiskerLeft (phComparisonFunctor A).op
            (toSheafify (SimplicialOver.totalTopology J A.left)
              ((phComparisonFunctor A).op.lan.obj G.obj))).app z) := by
        intro z
        induction z with | op z => ?_
        obtain ⟨b, y⟩ := z
        rw [NatTrans.comp_app, Functor.whiskerLeft_app]
        have : (phComparisonFunctor A).op.HasPointwiseLeftKanExtension G.obj := inferInstance
        exact IsIso.comp_isIso' inferInstance (isIso_toSheafify_lan_app J b (hv b) G y)
      exact NatIso.isIso_of_isIso_app _
    rw [← e] at hp
    exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (sheafToPresheaf _ _) hp _
  exact NatIso.isIso_of_isIso_app _

/-- **The inverse image `h⁻¹ : Sh(U_étale) ⥤ Sh((Spaces/U)_total)` is fully faithful**, as soon as
for every algebraic space `X` the inverse image along `X_{spaces, étale} → Spaces/X` is fully
faithful. This is the deduction, in the proof of Tag 0DHK, of the full faithfulness of `h⁻¹` from
that of its components `h_n⁻¹` (Stacks 0DGT (1)) through the description of `h⁻¹` of Tag 0D96. -/
def fullyFaithfulPhComparisonInverseImage
    (hX : ∀ X : AlgebraicSpaces B S hS, IsIso (spacesEtaleComparisonMorphism J X).adj.unit) :
    (phComparisonMorphism A J).inverseImage.FullyFaithful := by
  haveI := phComparisonFunctor_isContinuous (A := A) J
  have hu := isIso_phComparison_unit (A := A) J
    (fun b G => isIso_phComparisonDegree_unit J b (hX _) G)
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (phComparisonFunctor A)
      (Type (u + 1)) (etaleSimplicialSite A).totalTopology
        (SimplicialOver.totalTopology J A.left)).fullyFaithfulLOfIsIsoUnit.ofIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso (phComparisonFunctor A) (Type (u + 1))
      (etaleSimplicialSite A).totalTopology (SimplicialOver.totalTopology J A.left)).symm

/-- The direct image along the comparison functor of a simplicial degree is a right adjoint, the
left adjoint being the constructed sheafified left Kan extension. -/
instance phComparisonDegree_sheafPushforwardContinuous_isRightAdjoint (b : SimplexCategoryᵒᵖ) :
    ((phComparisonDegree A b).sheafPushforwardContinuous (Type (u + 1)) (etaleDegreeTopology A b)
      (J.over (A.left.obj b))).IsRightAdjoint :=
  ⟨_, ⟨Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (phComparisonDegree A b)
    (Type (u + 1)) (etaleDegreeTopology A b) (J.over (A.left.obj b))⟩⟩

/-- **Stacks 0D96 for the comparison `h`, on inverse images**: the restriction of `h⁻¹G` to the
simplicial degree `b` is the inverse image along `U_{b, spaces, étale} → Spaces/U_b` of the
restriction of `G`. This is the base change of left Kan extensions along `phInclusionSquare`,
which is Guitart exact. -/
def phRestrictInverseImageIso (b : SimplexCategoryᵒᵖ) :
    (phComparisonMorphism A J).inverseImage ⋙
        (phDegreeInclusion A b).sheafPushforwardContinuous (Type (u + 1)) (J.over (A.left.obj b))
          (SimplicialOver.totalTopology J A.left) ≅
      (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b
          ).sheafPushforwardContinuous (Type (u + 1)) (etaleDegreeTopology A b)
          (etaleSimplicialSite A).totalTopology ⋙
        (phComparisonDegree A b).sheafPullback (Type (u + 1)) (etaleDegreeTopology A b)
          (J.over (A.left.obj b)) :=
  haveI := phComparisonFunctor_isContinuous (A := A) J
  sheafPullbackContinuousSquareIso (phComparisonDegree A b)
    (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b)
    (phDegreeInclusion A b) (phComparisonFunctor A) (etaleDegreeTopology A b)
    (J.over (A.left.obj b)) (etaleSimplicialSite A).totalTopology
    (SimplicialOver.totalTopology J A.left) (phInclusionSquare A b)

/-- The restriction of `h⁻¹G` to the simplicial degree `b` is in the essential image of the
inverse image along `U_{b, spaces, étale} → Spaces/U_b`: it is the inverse image of the
restriction of `G`, transported through the equivalence of topoi of the realization. -/
theorem mem_essImage_phRestrict_inverseImage (b : SimplexCategoryᵒᵖ)
    (G : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) :
    (spacesEtaleComparisonMorphism J (A.left.obj b)).inverseImage.essImage
      (((phDegreeInclusion A b).sheafPushforwardContinuous (Type (u + 1))
        (J.over (A.left.obj b)) (SimplicialOver.totalTopology J A.left)).obj
          ((phComparisonMorphism A J).inverseImage.obj G)) := by
  let E := sheafEquiv (A := A) b.unop (Type (u + 1))
  let h := spacesEtaleComparisonMorphism J (A.left.obj b)
  let adj₂ : E.functor ⋙ h.inverseImage ⊣
      (phComparisonDegree A b).sheafPushforwardContinuous (Type (u + 1))
        (etaleDegreeTopology A b) (J.over (A.left.obj b)) :=
    E.toAdjunction.comp h.adj
  let Gb := ((Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b
    ).sheafPushforwardContinuous (Type (u + 1)) (etaleDegreeTopology A b)
      (etaleSimplicialSite A).totalTopology).obj G
  exact ⟨E.functor.obj Gb, ⟨((((phComparisonDegree A b).sheafAdjunctionContinuous (Type (u + 1))
    (etaleDegreeTopology A b) (J.over (A.left.obj b))).leftAdjointUniq adj₂).app Gb).symm ≪≫
      ((phRestrictInverseImageIso J b).app G).symm⟩⟩

end FullyFaithful

end AlgebraicGeometry.Space

end
