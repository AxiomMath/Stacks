module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSiteTopoi
public import StacksFrontier.CategoryTheory.Bicategory.CoGrothendieckFunctorFrom
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhToSmallEtale
public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectTotalSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalPullbacks
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Descent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.FiberRestriction
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# The comparison of the total ph site with the small étale site of a simplicial space

Let `a : U → X` be an augmented simplicial algebraic space over `S`, and let `(Spaces/S)_ph`
be a big ph site of algebraic spaces. The total site `(Spaces/U)_{ph, total}` of Section 09X8
has as objects the algebraic spaces `V/U_n` over some `U_n`, and the small étale site
`U_{spaces, étale}` of Section 0DE7 has as objects the algebraic spaces étale over some `U_n`.
The functor `U_{spaces, étale} → (Spaces/U)_{ph, total}`, `V/U_n ↦ V/U_n`, is in every
simplicial degree the inclusion `U_{n, spaces, étale} → (Spaces/U_n)_ph` of More on Cohomology
of Spaces, Section 0DGS, and it defines the morphism of topoi
`h : Sh((Spaces/U)_{ph, total}) → Sh(U_étale)` of Tag 0DHJ.

## Main definitions

* `AlgebraicGeometry.Space.phComparisonFunctor`: the functor from the total site of
  `U_{spaces, étale}` to `(Spaces/U)_{ph, total}`.
* `AlgebraicGeometry.Space.phComparisonMorphism`: the morphism of topoi
  `h : Sh((Spaces/U)_{ph, total}) → Sh(U_étale)`.
* `AlgebraicGeometry.Space.spacesEtaleComparisonMorphism`: the morphism of topoi
  `h_{-1} : Sh((Spaces/X)_ph) → Sh(X_étale)` of the inclusion `W ↦ W/X`.

## Main results

* `AlgebraicGeometry.Space.phComparisonFunctor_isContinuous`: the comparison functor is
  continuous.
* `AlgebraicGeometry.Space.phComparisonFunctor_representablyFlat`: the comparison functor is
  representably flat, being an equivalence onto the objects `V/U_n` with `V` étale over `U_n`,
  which form a coreflective subcategory of `(Spaces/U)_{ph, total}` in each fibre.
* `AlgebraicGeometry.Space.phComparisonFunctor_isMorphismOfSites`: it is a morphism of sites.

## Implementation notes

The constructions are carried out for an arbitrary Grothendieck topology `J` on algebraic spaces
over `S` such that the inclusions `X_{spaces, étale} → Spaces/X` are continuous for the
localizations of `J`; the ph topology of a big ph site is one such topology. The degree-`n`
component of `U_{spaces, étale}` is a strict model whose objects are formal base changes, so the
comparison functor sends an object to its realization, and a morphism lying over `φ` to its
composite with the cartesian comparison of realizations lying over `U(φ)`.

## References

* [Stacks Project, Tag 0DHJ](https://stacks.math.columbia.edu/tag/0DHJ)
* [Stacks Project, Section 0DGS](https://stacks.math.columbia.edu/tag/0DGS)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Section 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

open EtaleComponent

/-- The total category of the small étale site `U_{spaces, étale}`. -/
abbrev EtaleTotal := Pseudofunctor.CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor

/-- The total category of `(Spaces/U)_total`, with objects the `V/U_n`. -/
abbrev SpacesTotal := Grothendieck (SimplicialOver.slices A.left)

variable {A}

/-- The underlying morphism of algebraic spaces of a morphism of `(Spaces/U)_total`. -/
abbrev SpacesTotal.homLeft {X Y : SpacesTotal A} (m : X ⟶ Y) :
    (X.fiber : Over (A.left.obj X.base)).left ⟶ (Y.fiber : Over (A.left.obj Y.base)).left :=
  (Grothendieck.Hom.fiber m).left

/-- A morphism of `(Spaces/U)_total` is determined by its simplex map and its underlying
morphism of algebraic spaces. -/
theorem spacesTotal_hom_ext {X Y : SpacesTotal A} {f g : X ⟶ Y}
    (hb : Grothendieck.Hom.base f = Grothendieck.Hom.base g)
    (hl : (Grothendieck.Hom.fiber f).left = (Grothendieck.Hom.fiber g).left) : f = g := by
  rcases f with ⟨fb, ff⟩
  rcases g with ⟨gb, gf⟩
  dsimp only at hb hl
  subst hb
  congr 1
  exact Over.OverMorphism.ext hl

/-- The underlying morphism of algebraic spaces of a composite in `(Spaces/U)_total`. -/
@[simp]
theorem spacesTotal_comp_fiber_left {X Y Z : SpacesTotal A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Grothendieck.Hom.fiber (f ≫ g)).left =
      (Grothendieck.Hom.fiber f).left ≫ (Grothendieck.Hom.fiber g).left :=
  (congrArg (fun t => t ≫ _) (Over.eqToHom_left _)).trans (Category.id_comp _)

/-- The underlying morphism of algebraic spaces of an identity of `(Spaces/U)_total`. -/
@[simp]
theorem spacesTotal_id_fiber_left (X : SpacesTotal A) :
    (Grothendieck.Hom.fiber (𝟙 X)).left = 𝟙 _ :=
  Over.eqToHom_left (by simp; rfl)

/-- The comparison along an identity is the identification of `x.push 𝟙` with `x`. -/
theorem comparison_id' {n : SimplexCategory} (x : Index A n) :
    comparison (𝟙 n) x = eqToHom (by rw [Index.push_id]) := by
  rcases x with V | ⟨m, φ, V⟩
  · exact comparison_id_inl V
  · exact comparison_id_inr φ V

/-- The comparison along a composite is the composite of the comparisons, up to the
identification of `x.push (ψ ≫ χ)` with `(x.push ψ).push χ`. -/
theorem comparison_comp' {n k l : SimplexCategory} (ψ : n ⟶ k) (χ : k ⟶ l) (x : Index A n) :
    comparison (ψ ≫ χ) x = eqToHom (by rw [Index.push_comp]) ≫
      comparison χ (x.push ψ) ≫ comparison ψ x := by
  rcases x with V | ⟨m, φ, V⟩
  · exact (comparison_comp_inl ψ χ V).trans (Category.id_comp _).symm
  · exact (comparison_comp_inr ψ χ φ V).trans (Category.id_comp _).symm

/-- The underlying morphism of algebraic spaces of an identification of formal base changes. -/
theorem etaleComponent_eqToHom_left {n : SimplexCategory} {x y : EtaleComponent A n}
    (h : x = y) :
    (eqToHom h).hom.hom.left = eqToHom (by rw [h]) := by
  subst h
  rfl

/-- In simplicial degree `b`, the comparison functor sends a formal base change to its
realization, an algebraic space over `U_b`. -/
def phComparisonFib (b : SimplexCategoryᵒᵖ) :
    (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩ ⥤ SpacesTotal A :=
  realizeFunctor (A := A) b.unop ⋙ SpacesEtale.inclusion B S hS (A.left.obj b) ⋙
    Grothendieck.ι (SimplicialOver.slices A.left) b

/-- The degree-`b` comparison functor sends a formal base change to its realization in degree
`b`. -/
theorem phComparisonFib_obj (b : SimplexCategoryᵒᵖ)
    (x : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩) :
    (phComparisonFib b).obj x = ⟨b, (realize (A := A) (n := b.unop) x).obj⟩ :=
  rfl

/-- The transition functors of the total pseudofunctor of `U_{spaces, étale}` are the base-change
transitions of the components. -/
theorem totalPseudofunctor_map_toFunctor {R S : SimplexCategoryᵒᵖ} (f : R ⟶ S) :
    ((etaleSimplicialSite A).totalPseudofunctor.map f.op.toLoc).toFunctor =
      transition (A := A) f.unop :=
  rfl

/-- The underlying morphism of algebraic spaces of the image of a morphism under the inclusion
of a simplicial degree. -/
private theorem fiber_left_ι_map (b : SimplexCategoryᵒᵖ)
    {V W : Over (A.left.obj b)} (g : V ⟶ W) :
    (Grothendieck.Hom.fiber ((Grothendieck.ι (SimplicialOver.slices A.left) b).map g)).left =
      g.left :=
  (congrArg (fun t => t ≫ g.left) (Over.eqToHom_left (by simp))).trans (Category.id_comp _)

/-- The underlying morphism of algebraic spaces of the image of a morphism of degree `b`. -/
theorem phComparisonFib_map_fiber_left (b : SimplexCategoryᵒᵖ)
    {x y : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩} (g : x ⟶ y) :
    (Grothendieck.Hom.fiber ((phComparisonFib b).map g)).left = g.hom.hom.left :=
  fiber_left_ι_map b _

/-- The comparison of realizations along `f : R ⟶ S`: the cartesian comparison morphism from the
realization of `x.push f` to the realization of `x`, lying over `U(f) : U_R → U_S`. -/
def phComparisonHomApp {R S : SimplexCategoryᵒᵖ} (f : R ⟶ S)
    (x : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op S⟩) :
    (phComparisonFib R).obj
        (((etaleSimplicialSite A).totalPseudofunctor.map f.op.toLoc).toFunctor.obj x) ⟶
      (phComparisonFib S).obj x :=
  ⟨f, Over.homMk (comparison f.unop x) (comparison_hom f.unop x)⟩

/-- The comparison of realizations along `f`, as a natural transformation. -/
def phComparisonHom {R S : SimplexCategoryᵒᵖ} (f : R ⟶ S) :
    ((etaleSimplicialSite A).totalPseudofunctor.map f.op.toLoc).toFunctor ⋙ phComparisonFib R ⟶
      phComparisonFib S where
  app x := phComparisonHomApp f x
  naturality {x x'} g := by
    refine spacesTotal_hom_ext ((Category.id_comp f).trans (Category.comp_id f).symm) ?_
    refine (spacesTotal_comp_fiber_left
      ((phComparisonFib R).map (((etaleSimplicialSite A).totalPseudofunctor.map
        f.op.toLoc).toFunctor.map g)) (phComparisonHomApp f x')).trans (Eq.trans ?_
      (spacesTotal_comp_fiber_left (phComparisonHomApp f x) ((phComparisonFib S).map g)).symm)
    exact (congrArg (fun t => t ≫ comparison f.unop x')
      (phComparisonFib_map_fiber_left R ((transition (A := A) f.unop).map g))).trans
        ((transition_map_hom_comp f.unop g).trans (congrArg (fun t => comparison f.unop x ≫ t)
          (phComparisonFib_map_fiber_left S g)).symm)

/-- The unit isomorphism of the total pseudofunctor of `U_{spaces, étale}` is the identification
of `x.push 𝟙` with `x`. -/
theorem totalPseudofunctor_mapId_hom_app (S : SimplexCategoryᵒᵖ)
    (x : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op S⟩) :
    ((etaleSimplicialSite A).totalPseudofunctor.mapId ⟨op S⟩).hom.toNatTrans.app x =
      eqToHom (show ((etaleSimplicialSite A).totalPseudofunctor.map
        (𝟙 (⟨op S⟩ : LocallyDiscrete SimplexCategoryᵒᵖᵒᵖ))).toFunctor.obj x = x from
          Index.push_id (A := A) (n := S.unop) x) := by
  simp only [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapId, eqToIso.hom]
  exact Cat.eqToHom_app _ _ _ x

/-- The comparison of realizations along an identity is the unit isomorphism of the total
pseudofunctor, whiskered by the degree-`S` comparison functor. -/
theorem phComparisonHom_id (S : SimplexCategoryᵒᵖ) :
    phComparisonHom (A := A) (𝟙 S) = Functor.whiskerRight
      ((etaleSimplicialSite A).totalPseudofunctor.mapId ⟨op S⟩).hom.toNatTrans
        (phComparisonFib S) := by
  ext x
  refine spacesTotal_hom_ext rfl ?_
  refine Eq.trans ?_ (phComparisonFib_map_fiber_left S _).symm
  change comparison (𝟙 S).unop x = _
  rw [totalPseudofunctor_mapId_hom_app]
  exact (comparison_id' x).trans (etaleComponent_eqToHom_left _).symm

/-- The composition isomorphism of the total pseudofunctor of `U_{spaces, étale}` is the
identification of `x.push (ψ ≫ χ)` with `(x.push ψ).push χ`. -/
theorem totalPseudofunctor_mapComp_hom_app {R S T : SimplexCategoryᵒᵖ} (f : R ⟶ S) (g : S ⟶ T)
    (x : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op T⟩) :
    ((etaleSimplicialSite A).totalPseudofunctor.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans.app
        x =
      eqToHom (show ((etaleSimplicialSite A).totalPseudofunctor.map
        (g.op.toLoc ≫ f.op.toLoc)).toFunctor.obj x =
          ((etaleSimplicialSite A).totalPseudofunctor.map f.op.toLoc).toFunctor.obj
            (((etaleSimplicialSite A).totalPseudofunctor.map g.op.toLoc).toFunctor.obj x) from
          Index.push_comp (A := A) g.unop f.unop x) := by
  simp only [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapComp, eqToIso.hom]
  exact Cat.eqToHom_app _ _ _ x

/-- The comparison of realizations along a composite `f ≫ g` is the composition isomorphism of
the total pseudofunctor followed by the comparisons along `f` and along `g`. -/
theorem phComparisonHom_comp {R S T : SimplexCategoryᵒᵖ} (f : R ⟶ S) (g : S ⟶ T) :
    phComparisonHom (A := A) (f ≫ g) = Functor.whiskerRight
      ((etaleSimplicialSite A).totalPseudofunctor.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans
        (phComparisonFib R) ≫
      Functor.whiskerLeft ((etaleSimplicialSite A).totalPseudofunctor.map g.op.toLoc).toFunctor
        (phComparisonHom f) ≫ phComparisonHom g := by
  ext x
  refine spacesTotal_hom_ext (Category.id_comp (f ≫ g)).symm ?_
  let a₁ := (phComparisonFib R).map (((etaleSimplicialSite A).totalPseudofunctor.mapComp
    g.op.toLoc f.op.toLoc).hom.toNatTrans.app x)
  let a₂ := phComparisonHomApp f
    (((etaleSimplicialSite A).totalPseudofunctor.map g.op.toLoc).toFunctor.obj x)
  let a₃ := phComparisonHomApp g x
  change comparison (f ≫ g).unop x = (Grothendieck.Hom.fiber (a₁ ≫ a₂ ≫ a₃)).left
  refine (comparison_comp' g.unop f.unop x).trans ?_
  refine Eq.trans ?_ (spacesTotal_comp_fiber_left a₁ (a₂ ≫ a₃)).symm
  refine Eq.trans ?_ (congrArg (fun t => (Grothendieck.Hom.fiber a₁).left ≫ t)
    (spacesTotal_comp_fiber_left a₂ a₃).symm)
  refine congrArg (fun t => t ≫ comparison f.unop (x.push g.unop) ≫ comparison g.unop x) ?_
  refine Eq.trans ?_ (phComparisonFib_map_fiber_left R _).symm
  rw [totalPseudofunctor_mapComp_hom_app]
  exact (etaleComponent_eqToHom_left _).symm

variable (A) in
/-- **The comparison functor of Tag 0DHJ.** The functor `U_{spaces, étale} ⥤ (Spaces/U)_total`,
`V/U_n ↦ V/U_n`: an object étale over some `U_n`, presented as a formal base change, goes to its
realization, and a morphism `(φ, f)` goes to `(φ, f)` read through the cartesian comparison of
realizations lying over `U(φ)`. -/
def phComparisonFunctor : EtaleTotal A ⥤ SpacesTotal A :=
  Pseudofunctor.CoGrothendieck.functorFrom phComparisonFib (fun f => phComparisonHom f)
    phComparisonHom_id (fun f g => phComparisonHom_comp f g)

/-- The comparison functor sends a formal base change over `U_n` to its realization over `U_n`. -/
theorem phComparisonFunctor_obj (X : EtaleTotal A) :
    (phComparisonFunctor A).obj X = ⟨X.base, (realize (A := A) (n := X.base.unop) X.fiber).obj⟩ :=
  rfl

/-- The simplex map of the image of a morphism under the comparison functor is its simplex map. -/
theorem phComparisonFunctor_map_base {X Y : EtaleTotal A} (f : X ⟶ Y) :
    Grothendieck.Hom.base ((phComparisonFunctor A).map f) = f.base :=
  Category.id_comp f.base

/-- The underlying morphism of algebraic spaces of the image of a morphism `(φ, f)` under the
comparison functor is `f` followed by the comparison of realizations along `φ`. -/
theorem phComparisonFunctor_map_fiber_left {X Y : EtaleTotal A} (f : X ⟶ Y) :
    (Grothendieck.Hom.fiber ((phComparisonFunctor A).map f)).left =
      f.fiber.hom.hom.left ≫ comparison f.base.unop Y.fiber :=
  (spacesTotal_comp_fiber_left ((phComparisonFib X.base).map f.fiber)
    (phComparisonHomApp f.base Y.fiber)).trans
      (congrArg (fun t => t ≫ comparison f.base.unop Y.fiber)
        (phComparisonFib_map_fiber_left X.base f.fiber))

/-! ### Continuity -/

section Continuity

variable (J : GrothendieckTopology (AlgebraicSpaces B S hS))
  [hJ : ∀ X : AlgebraicSpaces B S hS,
    (SpacesEtale.inclusion B S hS X).IsContinuous (SpacesEtale.topology B S hS X) (J.over X)]

omit hJ in
/-- The restriction of a sheaf on `(Spaces/U)_total` to simplicial degree `b` is a sheaf on
`Spaces/U_b`. -/
theorem spacesTotal_restrict_isSheaf (b : SimplexCategoryᵒᵖ)
    (G : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) :
    Presheaf.IsSheaf (J.over (A.left.obj b))
      ((Grothendieck.ι (SimplicialOver.slices A.left) b).op ⋙ G.obj) := by
  have h := (SimplicialOver.situation J A.left).restrict_isSheaf b.unop G
  rwa [SimplicialOver.componentTopology_eq] at h

/-- The degree-`b` part of the comparison functor is continuous. -/
instance phComparisonFib_realize_isContinuous (b : SimplexCategoryᵒᵖ) :
    (realizeFunctor (A := A) b.unop ⋙ SpacesEtale.inclusion B S hS (A.left.obj b)).IsContinuous
      (precoverage (A := A) b.unop).toGrothendieck (J.over (A.left.obj b)) :=
  haveI : (realizeFunctor (A := A) b.unop).IsContinuous
      (precoverage (A := A) b.unop).toGrothendieck (SpacesEtale.topology B S hS (A.left.obj b)) :=
    EtaleComponent.realizeFunctor_isContinuous b.unop
  Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS (A.left.obj b)) _

/-- **The comparison functor is continuous**: a sheaf on `(Spaces/U)_total`, restricted to
`U_{spaces, étale}`, is a sheaf. The covering families of the total site of
`U_{spaces, étale}` lie in one simplicial degree, where they are étale coverings, and the
comparison functor there is the inclusion of `U_{n, spaces, étale}` in `Spaces/U_n`. -/
theorem phComparisonFunctor_isContinuous :
    (phComparisonFunctor A).IsContinuous (etaleSimplicialSite A).totalTopology
      (SimplicialOver.totalTopology J A.left) where
  op_comp_isSheaf_of_types G := by
    have := (etaleSimplicialSite A).totalCoverage_hasPullbacks
    have := (etaleSimplicialSite A).totalCoverage_isStableUnderBaseChange
    refine (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange
      (J := (etaleSimplicialSite A).totalCoverage) _).mpr ?_
    rintro X _ ⟨T, hT, rfl⟩
    refine Presieve.isSheafFor_map _ _ _ ?_
    have hsheaf : Presheaf.IsSheaf (precoverage (A := A) X.base.unop).toGrothendieck
        ((phComparisonFib X.base).op ⋙ G.obj) :=
      Functor.op_comp_isSheaf_of_isSheaf
        (realizeFunctor (A := A) X.base.unop ⋙ SpacesEtale.inclusion B S hS (A.left.obj X.base))
        _ (J.over (A.left.obj X.base)) _ (spacesTotal_restrict_isSheaf J X.base G)
    refine Presieve.isSheafFor_iso (Functor.isoWhiskerRight (NatIso.op
      (Pseudofunctor.CoGrothendieck.ιCompFunctorFrom phComparisonFib
        (fun f => phComparisonHom f) phComparisonHom_id
          (fun f g => phComparisonHom_comp f g) X.base)) G.obj) ?_
    exact (Presieve.isSheafFor_iff_generate T).mpr ((isSheaf_iff_isSheaf_of_type _ _).mp hsheaf _
      (Precoverage.generate_mem_toGrothendieck hT))

end Continuity

/-! ### Flatness -/

section Flatness

variable (A) in
/-- The objects `V/U_n` of `(Spaces/U)_total` with `V` étale over `U_n`. -/
def etaleObjects : ObjectProperty (SpacesTotal A) :=
  fun t => IsEtaleOver B S hS (A.left.obj t.base) t.fiber

variable (A) in
/-- The full subcategory of `(Spaces/U)_total` on the objects étale over their `U_n`. -/
abbrev SpacesTotalEtale := (etaleObjects A).FullSubcategory

/-- The underlying morphism of algebraic spaces of the image of a morphism under the inclusion
of a simplicial degree. -/
theorem grothendieckι_map_fiber_left (b : SimplexCategoryᵒᵖ) {V W : Over (A.left.obj b)}
    (g : V ⟶ W) :
    (Grothendieck.Hom.fiber ((Grothendieck.ι (SimplicialOver.slices A.left) b).map g)).left =
      g.left :=
  fiber_left_ι_map b g

/-- The inclusion of the spaces-étale site of `U_b` in the étale objects of `(Spaces/U)_total`
in simplicial degree `b`. -/
def etaleDegreeInclusion (b : SimplexCategoryᵒᵖ) :
    SpacesEtale B S hS (A.left.obj b) ⥤ SpacesTotalEtale A :=
  (etaleObjects A).lift (SpacesEtale.inclusion B S hS (A.left.obj b) ⋙
    Grothendieck.ι (SimplicialOver.slices A.left) b) (fun V => V.property)

variable (t : SpacesTotal A)

/-- The algebraic space over `U_n` of an object `V/U_n` of `(Spaces/U)_total`. -/
abbrev SpacesTotal.over : Over (A.left.obj t.base) := t.fiber

/-- The structured arrows from `t` in the spaces-étale site of its degree, included in the
structured arrows from `t` to the étale objects of `(Spaces/U)_total`. -/
def etaleArrowInclusion :
    StructuredArrow (SpacesTotal.over t) (SpacesEtale.inclusion B S hS (A.left.obj t.base)) ⥤
      StructuredArrow t (etaleObjects A).ι :=
  StructuredArrow.post (SpacesTotal.over t) (SpacesEtale.inclusion B S hS (A.left.obj t.base))
      (Grothendieck.ι (SimplicialOver.slices A.left) t.base) ⋙
    StructuredArrow.pre t (etaleDegreeInclusion t.base) (etaleObjects A).ι

/-- The base change to the degree of `t` of the target of a structured arrow from `t`, with the
transposed structure arrow. -/
def etaleArrowRestrictObj (k : StructuredArrow t (etaleObjects A).ι) :
    StructuredArrow (SpacesTotal.over t) (SpacesEtale.inclusion B S hS (A.left.obj t.base)) :=
  StructuredArrow.mk (Y := (⟨(Over.pullback (A.left.map k.hom.base)).obj
      (SpacesTotal.over k.right.obj),
      isEtaleOver_overPullback B S hS _ _ k.right.property⟩ :
        SpacesEtale B S hS (A.left.obj t.base)))
    (Over.homMk (pullback.lift (SpacesTotal.homLeft k.hom) (SpacesTotal.over t).hom
      (Over.w (Grothendieck.Hom.fiber k.hom))) (pullback.lift_snd _ _ _))

variable {t}

/-- The simplex map of a morphism out of an included arrow is the simplex map of its target
arrow. -/
theorem etaleArrowInclusion_hom_base {z : StructuredArrow (SpacesTotal.over t)
    (SpacesEtale.inclusion B S hS (A.left.obj t.base))} {k : StructuredArrow t (etaleObjects A).ι}
    (φ : (etaleArrowInclusion t).obj z ⟶ k) :
    Grothendieck.Hom.base φ.right.hom = k.hom.base :=
  (Category.id_comp _).symm.trans (congrArg Grothendieck.Hom.base (StructuredArrow.w φ))

/-- The structure morphism of an included arrow followed by the underlying morphism of a
morphism out of it is the underlying morphism of the target arrow. -/
theorem etaleArrowInclusion_hom_left {z : StructuredArrow (SpacesTotal.over t)
    (SpacesEtale.inclusion B S hS (A.left.obj t.base))} {k : StructuredArrow t (etaleObjects A).ι}
    (φ : (etaleArrowInclusion t).obj z ⟶ k) :
    z.hom.left ≫ (Grothendieck.Hom.fiber φ.right.hom).left = (Grothendieck.Hom.fiber k.hom).left :=
  (congrArg (fun m => m ≫ (Grothendieck.Hom.fiber φ.right.hom).left)
      (grothendieckι_map_fiber_left t.base z.hom).symm).trans
    ((spacesTotal_comp_fiber_left ((Grothendieck.ι (SimplicialOver.slices A.left) t.base).map
      z.hom) φ.right.hom).symm.trans
        (congrArg SpacesTotal.homLeft (StructuredArrow.w φ)))

/-- The underlying morphism of a morphism out of an included arrow lies over the map `U(φ)`
of the simplex map `φ` of the target arrow. -/
theorem etaleArrowInclusion_hom_w {z : StructuredArrow (SpacesTotal.over t)
    (SpacesEtale.inclusion B S hS (A.left.obj t.base))} {k : StructuredArrow t (etaleObjects A).ι}
    (φ : (etaleArrowInclusion t).obj z ⟶ k) :
    SpacesTotal.homLeft φ.right.hom ≫ (SpacesTotal.over k.right.obj).hom =
      z.right.obj.hom ≫ A.left.map k.hom.base :=
  (Over.w (Grothendieck.Hom.fiber φ.right.hom)).trans
    (congrArg (fun f => z.right.obj.hom ≫ A.left.map f) (etaleArrowInclusion_hom_base φ))

/-- The degree-`t` morphism underlying a morphism out of an included arrow. -/
def etaleArrowHomEquivToFun {z : StructuredArrow (SpacesTotal.over t)
    (SpacesEtale.inclusion B S hS (A.left.obj t.base))} {k : StructuredArrow t (etaleObjects A).ι}
    (φ : (etaleArrowInclusion t).obj z ⟶ k) : z ⟶ etaleArrowRestrictObj t k :=
  StructuredArrow.homMk (ObjectProperty.homMk (Over.homMk
    (pullback.lift (SpacesTotal.homLeft φ.right.hom) z.right.obj.hom
      (etaleArrowInclusion_hom_w φ)) (pullback.lift_snd _ _ _))) (by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · exact ((Category.assoc _ _ _).trans (congrArg (fun m => z.hom.left ≫ m)
        (pullback.lift_fst _ _ _))).trans
          ((etaleArrowInclusion_hom_left φ).trans (pullback.lift_fst _ _ _).symm)
    · exact ((Category.assoc _ _ _).trans (congrArg (fun m => z.hom.left ≫ m)
        (pullback.lift_snd _ _ _))).trans ((Over.w z.hom).trans (pullback.lift_snd _ _ _).symm))

/-- The morphism out of an included arrow attached to a degree-`t` morphism. -/
def etaleArrowHomEquivInvFun {z : StructuredArrow (SpacesTotal.over t)
    (SpacesEtale.inclusion B S hS (A.left.obj t.base))} {k : StructuredArrow t (etaleObjects A).ι}
    (ψ : z ⟶ etaleArrowRestrictObj t k) : (etaleArrowInclusion t).obj z ⟶ k :=
  StructuredArrow.homMk (ObjectProperty.homMk
    (⟨k.hom.base, Over.homMk (ψ.right.hom.left ≫ pullback.fst _ _)
      ((Category.assoc _ _ _).trans ((congrArg (fun m => ψ.right.hom.left ≫ m)
        pullback.condition).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ A.left.map k.hom.base) (Over.w ψ.right.hom)))))⟩ :
      ((etaleDegreeInclusion t.base).obj z.right).obj ⟶ k.right.obj)) (by
    refine spacesTotal_hom_ext (Category.id_comp _) ?_
    refine (spacesTotal_comp_fiber_left ((Grothendieck.ι (SimplicialOver.slices A.left)
      t.base).map z.hom) _).trans ?_
    refine (congrArg (fun m => m ≫ ψ.right.hom.left ≫ pullback.fst _ _)
      (grothendieckι_map_fiber_left t.base z.hom)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ pullback.fst _ _)
      (congrArg Over.Hom.left (StructuredArrow.w ψ))).trans (pullback.lift_fst _ _ _)))

/-- Morphisms from the inclusion of a degree-`t` arrow to an arrow `k` are the morphisms to the
base change of `k` to the degree of `t`. -/
def etaleArrowHomEquiv (z : StructuredArrow (SpacesTotal.over t)
    (SpacesEtale.inclusion B S hS (A.left.obj t.base))) (k : StructuredArrow t (etaleObjects A).ι) :
    ((etaleArrowInclusion t).obj z ⟶ k) ≃ (z ⟶ etaleArrowRestrictObj t k) where
  toFun := etaleArrowHomEquivToFun
  invFun := etaleArrowHomEquivInvFun
  left_inv φ := StructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _
    (spacesTotal_hom_ext (etaleArrowInclusion_hom_base φ).symm (pullback.lift_fst _ _ _)))
  right_inv ψ := StructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _
    (Over.OverMorphism.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
      ((pullback.lift_snd _ _ _).trans (Over.w ψ.right.hom).symm))))

/-- The bijection `etaleArrowHomEquiv` is natural in the degree-`t` arrow. -/
theorem etaleArrowHomEquiv_naturality {z' z : StructuredArrow (SpacesTotal.over t)
    (SpacesEtale.inclusion B S hS (A.left.obj t.base))} {k : StructuredArrow t (etaleObjects A).ι}
    (f : z' ⟶ z) (φ : (etaleArrowInclusion t).obj z ⟶ k) :
    etaleArrowHomEquiv z' k ((etaleArrowInclusion t).map f ≫ φ) =
      f ≫ etaleArrowHomEquiv z k φ :=
  StructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    (pullback.hom_ext
      (((pullback.lift_fst _ _ _).trans ((spacesTotal_comp_fiber_left
        ((etaleArrowInclusion t).map f).right.hom φ.right.hom).trans
          (congrArg (fun m => m ≫ SpacesTotal.homLeft φ.right.hom)
            (grothendieckι_map_fiber_left t.base f.right.hom)))).trans
        ((congrArg (fun m => f.right.hom.left ≫ m) (pullback.lift_fst _ _ _)).symm.trans
          (Category.assoc _ _ _).symm))
      ((pullback.lift_snd _ _ _).trans ((Over.w f.right.hom).symm.trans
        ((congrArg (fun m => f.right.hom.left ≫ m) (pullback.lift_snd _ _ _)).symm.trans
          (Category.assoc _ _ _).symm))))))

variable (t) in
/-- The inclusion of the degree-`t` arrows is left adjoint to base change to the degree of
`t`. -/
def etaleArrowAdjunction :
    etaleArrowInclusion t ⊣ Adjunction.rightAdjointOfEquiv (G_obj := etaleArrowRestrictObj t)
      etaleArrowHomEquiv (fun _ _ _ f φ => etaleArrowHomEquiv_naturality f φ) :=
  Adjunction.adjunctionOfEquivRight _ _

/-- The spaces-étale site of an algebraic space has finite limits, preserved by its inclusion in
the slice. -/
instance spacesEtale_inclusion_representablyFlat (X : AlgebraicSpaces B S hS) :
    RepresentablyFlat (SpacesEtale.inclusion B S hS X) :=
  haveI : HasFiniteLimits (SpacesEtale B S hS X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  haveI : PreservesFiniteLimits (SpacesEtale.inclusion B S hS X) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  flat_of_preservesFiniteLimits _

/-- **The inclusion of the étale objects of `(Spaces/U)_total` is representably flat**: the
structured arrows from `t` are cofiltered, because the arrows from `t` within the degree of `t`
are cofiltered and every arrow from `t` has a universal arrow from that degree, its base change
to the degree of `t`. -/
instance etaleObjects_ι_representablyFlat : RepresentablyFlat (etaleObjects A).ι where
  cofiltered t := IsCofiltered.of_left_adjoint (etaleArrowAdjunction t)

/-- The comparison functor is faithful: a morphism of formal base changes is determined by the
morphism of realizations, because the comparison squares are cartesian. -/
instance phComparisonFunctor_faithful : (phComparisonFunctor A).Faithful where
  map_injective {X Y f g} h := by
    have hb : f.base = g.base := (phComparisonFunctor_map_base f).symm.trans
      ((congrArg Grothendieck.Hom.base h).trans (phComparisonFunctor_map_base g))
    have hl := (phComparisonFunctor_map_fiber_left f).symm.trans
      ((congrArg SpacesTotal.homLeft h).trans (phComparisonFunctor_map_fiber_left g))
    rcases f with ⟨fb, ff⟩
    rcases g with ⟨gb, gf⟩
    dsimp only at hb hl
    subst hb
    congr 1
    refine InducedCategory.hom_ext (ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_))
    exact (isPullback_comparison fb.unop Y.fiber).hom_ext hl
      ((Over.w ff.hom.hom).trans (Over.w gf.hom.hom).symm)

/-- The morphism of formal base changes lifting a morphism of realizations over `U(φ)` through
the cartesian comparison square. -/
def phComparisonPreimage {X Y : EtaleTotal A}
    (m : (phComparisonFunctor A).obj X ⟶ (phComparisonFunctor A).obj Y) : X ⟶ Y :=
  ⟨m.base, InducedCategory.homMk (ObjectProperty.homMk (Over.homMk
    ((isPullback_comparison m.base.unop Y.fiber).lift (SpacesTotal.homLeft m)
      (realize (A := A) (n := X.base.unop) X.fiber).obj.hom (Over.w (Grothendieck.Hom.fiber m)))
    ((isPullback_comparison m.base.unop Y.fiber).lift_snd _ _ _)))⟩

/-- The comparison functor sends `phComparisonPreimage m` to `m`. -/
theorem phComparisonFunctor_map_preimage {X Y : EtaleTotal A}
    (m : (phComparisonFunctor A).obj X ⟶ (phComparisonFunctor A).obj Y) :
    (phComparisonFunctor A).map (phComparisonPreimage m) = m :=
  spacesTotal_hom_ext (phComparisonFunctor_map_base (phComparisonPreimage m))
    ((phComparisonFunctor_map_fiber_left (phComparisonPreimage m)).trans
      ((isPullback_comparison m.base.unop Y.fiber).lift_fst _ _ _))

/-- The comparison functor is full: a morphism of realizations over `U(φ)` lifts through the
cartesian comparison square to a morphism of formal base changes. -/
instance phComparisonFunctor_full : (phComparisonFunctor A).Full where
  map_surjective m := ⟨phComparisonPreimage m, phComparisonFunctor_map_preimage m⟩

variable (A) in
/-- The comparison functor, as a functor to the étale objects of `(Spaces/U)_total`. -/
def phComparisonLift : EtaleTotal A ⥤ SpacesTotalEtale A :=
  (etaleObjects A).lift (phComparisonFunctor A)
    (fun X => (realize (A := A) (n := X.base.unop) X.fiber).property)

/-- Every étale object `V/U_n` of `(Spaces/U)_total` is the realization of a formal base change:
the trivial one. -/
instance phComparisonLift_essSurj : (phComparisonLift A).EssSurj where
  mem_essImage y := ⟨⟨y.obj.base, ofSpacesEtale (A := A) (n := y.obj.base.unop)
      ⟨SpacesTotal.over y.obj, y.property⟩⟩,
    ⟨(etaleObjects A).isoMk ((Grothendieck.ι (SimplicialOver.slices A.left) y.obj.base).mapIso
      ((SpacesEtale.inclusion B S hS (A.left.obj y.obj.base)).mapIso
        (realizeOfSpacesEtaleIso (A := A) (n := y.obj.base.unop)
          ⟨SpacesTotal.over y.obj, y.property⟩)))⟩⟩

/-- **The small étale site of `U` is equivalent to the étale objects of `(Spaces/U)_total`.** -/
instance phComparisonLift_isEquivalence : (phComparisonLift A).IsEquivalence where
  faithful := ⟨fun {_ _} _ _ h => (phComparisonFunctor A).map_injective
    (congrArg (etaleObjects A).ι.map h)⟩
  full := ⟨fun {_ _} m => ⟨phComparisonPreimage m.hom,
    ObjectProperty.hom_ext _ (phComparisonFunctor_map_preimage m.hom)⟩⟩
  essSurj := inferInstance

/-- **The comparison functor is representably flat**, being an equivalence onto the étale
objects of `(Spaces/U)_total` followed by their representably flat inclusion. -/
instance phComparisonFunctor_representablyFlat : RepresentablyFlat (phComparisonFunctor A) :=
  haveI : (phComparisonLift A).IsRightAdjoint :=
    (phComparisonLift A).asEquivalence.symm.toAdjunction.isRightAdjoint
  inferInstanceAs (RepresentablyFlat (phComparisonLift A ⋙ (etaleObjects A).ι))

end Flatness

/-! ### The comparison morphisms of topoi -/

section Morphisms

variable (J : GrothendieckTopology (AlgebraicSpaces B S hS))
  [hJ : ∀ X : AlgebraicSpaces B S hS,
    (SpacesEtale.inclusion B S hS X).IsContinuous (SpacesEtale.topology B S hS X) (J.over X)]

/-- **The comparison functor is a morphism of sites** `(Spaces/U)_total → U_{spaces, étale}`:
it is continuous and representably flat. -/
theorem phComparisonFunctor_isMorphismOfSites :
    (phComparisonFunctor A).IsMorphismOfSites (etaleSimplicialSite A).totalTopology
      (SimplicialOver.totalTopology J A.left) :=
  have := phComparisonFunctor_isContinuous (A := A) J
  Functor.isMorphismOfSites_of_representablyFlat _ _ _

variable (A) in
/-- **The upper horizontal arrow of Tag 0DHJ**, `h : Sh((Spaces/U)_total) → Sh(U_étale)`, the
morphism of topoi of the morphism of sites given by `V/U_n ↦ V/U_n`. -/
@[stacks 0DHJ "the upper horizontal arrow h : Sh((Spaces/U)_{ph, total}) → Sh(U_étale)"]
def phComparisonMorphism :
    MorphismOfTopoi (Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1)))
      (Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) :=
  (phComparisonFunctor_isMorphismOfSites J).morphismOfTopoi

/-- The direct image of `h` is restriction along `V/U_n ↦ V/U_n`. -/
theorem phComparisonMorphism_pushforward :
    haveI := phComparisonFunctor_isContinuous (A := A) J
    (phComparisonMorphism A J).pushforward =
      (phComparisonFunctor A).sheafPushforwardContinuous (Type (u + 1))
        (etaleSimplicialSite A).totalTopology (SimplicialOver.totalTopology J A.left) :=
  rfl

/-- The inclusion of `X_{spaces, étale}` in `Spaces/X` is a morphism of sites. -/
theorem spacesEtale_inclusion_isMorphismOfSites (X : AlgebraicSpaces B S hS) :
    (SpacesEtale.inclusion B S hS X).IsMorphismOfSites (SpacesEtale.topology B S hS X)
      (J.over X) :=
  Functor.isMorphismOfSites_of_isTerminal _ _ _ (SpacesEtale.final_isTerminal B S hS X)
    Over.mkIdTerminal

/-- **The lower horizontal arrow of Tag 0DHJ**, `h_{-1} : Sh(Spaces/X) → Sh(X_étale)`, the
morphism of topoi of the inclusion `X_{spaces, étale} → Spaces/X`, `W ↦ W/X`. -/
@[stacks 0DHJ "the lower horizontal arrow h_{-1} : Sh((Spaces/X)_ph) → Sh(X_étale)"]
def spacesEtaleComparisonMorphism (X : AlgebraicSpaces B S hS) :
    MorphismOfTopoi (Sheaf (J.over X) (Type (u + 1)))
      (Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) :=
  (spacesEtale_inclusion_isMorphismOfSites J X).morphismOfTopoi

end Morphisms

end AlgebraicGeometry.Space
