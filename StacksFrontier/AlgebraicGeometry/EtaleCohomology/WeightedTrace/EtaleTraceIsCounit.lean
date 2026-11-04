module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleCanonicalWeighting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleRestrictionStalkIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceStalkDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceProperties
public import StacksCore.Tactic.StacksAttribute

/-!
# The trace map of an étale morphism is the counit of `j_! ⊣ j^{-1}`

Let `j : U ⟶ X` be an étale morphism of schemes, presented as an object of the small étale site
of `X` inside a big étale site. Being flat, locally quasi-finite and locally of finite
presentation, `j` carries the canonical weighting of Stacks 0F3D, and Example 0GKI builds from
it the trace map `Tr : j_! j^{-1}ℱ ⟶ ℱ` of Stacks 0GKG, the unique morphism whose effect on the
stalk at a geometric point `s̄` of `X`,

`(j_! j^{-1}ℱ)_s̄ = ⨁_{j(x̄) = s̄} ℱ_s̄ ⟶ ℱ_s̄`,

is multiplication by `w(x̄)` on the summand indexed by `x̄`. This file proves Remark 0GL4: that
trace map is the counit of the adjunction between `j_!` and `j^{-1}`.

## Main definitions

* `AlgebraicGeometry.etaleFShriekAbPullbackAdjunction` — the adjunction `j_! ⊣ j^{-1}` with
  `j_!` the direct image with compact support of Stacks 0F6R and `j^{-1}` the sheaf pullback
  along base change.

## Main results

* `AlgebraicGeometry.hasWeightedTraceStalks_counit` — the counit has the behaviour on geometric
  stalks which characterises the trace map of Stacks 0GKG for the canonical weighting of `j`.
* `AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit` — a morphism `j_! j^{-1}ℱ ⟶ ℱ` is the
  trace map of Example 0GKI — that is, it has the behaviour on geometric stalks prescribed by
  Stacks 0GKG for the canonical weighting of Stacks 0F3D — if and only if it is the counit of
  `j_! ⊣ j^{-1}`.

## Implementation notes

The trace map of Example 0GKI is pinned down by Stacks 0GKG, which asserts that exactly one
morphism `j_! j^{-1}ℱ ⟶ ℱ` has the prescribed effect on every geometric stalk; that
characterisation is `AlgebraicGeometry.SmallEtale.HasWeightedTraceStalks` and its uniqueness
half is `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_unique`. So the statement below is
an equivalence rather than an equation between two separately constructed morphisms: its
backward direction produces the trace map — the existence half of Stacks 0GKG in the étale case
— and its forward direction is Remark 0GL4's equality.

The canonical weighting of an étale morphism is the constant function `1`
(`AlgebraicGeometry.flatQuasiFiniteWeight_eq_one_of_etale`), so the prescribed stalk map is the
sum over the geometric fibre; that this is the counit is the triangle identity of `j_! ⊣ j^{-1}`,
read on stalks. The three inputs are: the unit of the extension-by-zero adjunction of Stacks
03S3 is the inclusion of a summand of the stalk decomposition of Stacks 0F5F
(`AlgebraicGeometry.extensionUnitStalkMap_comp_fShriekStalkIso`); the triangle identity on
stalks (`AlgebraicGeometry.extensionUnitStalkMap_comp_counit`); and the comparison of the two
spellings of `j^{-1}` on stalks
(`AlgebraicGeometry.restrictionStalkMap_comp_etaleRestrictionIso`).

The adjunction is taken with `j^{-1}` spelled as the sheaf pullback
`AlgebraicGeometry.SmallEtale.abPullback`, which is the spelling the characterisation of Stacks
0GKG uses; it is transported from the extension-by-zero adjunction of Stacks 03S3 along the two
comparisons `AlgebraicGeometry.SmallEtale.abelianExtensionByZeroIsoFShriek` (Stacks 0F6Q) and
`AlgebraicGeometry.etaleRestrictionIso` (Stacks 03S3), so no new adjunction is built.

## References

* [Stacks Project, Tag 0GL4](https://stacks.math.columbia.edu/tag/0GL4)
* [Stacks Project, Tag 0GKI](https://stacks.math.columbia.edu/tag/0GKI)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F3D](https://stacks.math.columbia.edu/tag/0F3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- **The adjunction `j_! ⊣ j^{-1}` for an étale `j`,** with `j_!` the direct image with compact
support of Stacks 0F6R and `j^{-1}` the sheaf pullback along base change. It is the
extension-by-zero adjunction of Stacks 03S3 read through the comparison of Stacks 0F6Q on the
left and the comparison of the two spellings of the inverse image on the right. -/
public def etaleFShriekAbPullbackAdjunction :
    SmallEtale.fShriekFunctor.{u, u + 1} B U.obj.hom ⊣
      SmallEtale.abPullback.{u, u + 1} B U.obj.hom :=
  (SmallEtale.fShriekAdjunctionRestriction B X hX U).ofNatIsoRight
    (etaleRestrictionIso B X hX U).symm

/-- The counit of `j_! ⊣ j^{-1}` is the counit of the extension-by-zero adjunction of Stacks
03S3, read through the two comparisons. -/
public theorem etaleFShriekAbPullbackAdjunction_counit_app
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :
    (etaleFShriekAbPullbackAdjunction B X hX U).counit.app F =
      (SmallEtale.fShriekFunctor.{u, u + 1} B U.obj.hom).map
          ((etaleRestrictionIso B X hX U).hom.app F) ≫
        (SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).inv.app
            ((abelianRestriction B X hX U).obj F) ≫
          (abelianExtensionByZeroAdjunction B X hX U).counit.app F :=
  rfl

section Stalks

variable (s : GeometricPoint X) (x : SmallEtale.GeometricFiberPoint B U.obj.hom s)

/-- The stalk map at a geometric point is functorial for composition of sheaf morphisms. -/
private theorem stalkMap_comp
    {G H K : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}} (f : G ⟶ H) (g : H ⟶ K) :
    colim.map (Functor.whiskerLeft (CategoryOfElements.π
        (geometricPointFiber B X hX s)).op (f ≫ g).1) =
      colim.map (Functor.whiskerLeft (CategoryOfElements.π
        (geometricPointFiber B X hX s)).op f.1) ≫
      colim.map (Functor.whiskerLeft (CategoryOfElements.π
        (geometricPointFiber B X hX s)).op g.1) :=
  (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map_comp _ _

/-- The stalk map at a geometric point of an identity morphism is the identity. -/
private theorem stalkMap_id (G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :
    colim.map (Functor.whiskerLeft (CategoryOfElements.π
        (geometricPointFiber B X hX s)).op (𝟙 G : G ⟶ G).1) = 𝟙 _ :=
  (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map_id _

/-- The inclusion of the summand of the stalk decomposition of Stacks 0F5F indexed by a point of
the geometric fibre, read in the stalk of `j_!G`. -/
public abbrev fShriekStalkSummand
    (G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}) :
    etaleStalk B U.obj.left.1 U.obj.left.property (x.toGeometricPoint B U.obj.hom s) G.obj ⟶
      etaleStalk B X hX s ((SmallEtale.fShriekFunctor.{u, u + 1} B U.obj.hom).obj G).obj :=
  SmallEtale.fiberStalkOf.{u, u + 1} B U.obj.hom s G x ≫
    (SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s G).inv

/-- The summand inclusion is natural in the sheaf on `U`: a morphism of sheaves on `U` carries
the summand indexed by `x` to the summand indexed by `x`. -/
public theorem fShriekStalkSummand_natural
    {G H : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}}
    (φ : G ⟶ H) :
    fShriekStalkSummand B X hX U s x G ≫
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B X hX s)).op
          ((SmallEtale.fShriekFunctor.{u, u + 1} B U.obj.hom).map φ).1) =
      colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B U.obj.left.1 U.obj.left.property
            (x.toGeometricPoint B U.obj.hom s))).op φ.1) ≫
        fShriekStalkSummand B X hX U s x H := by
  have hiso : (SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s G).inv ≫
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B X hX s)).op
          ((SmallEtale.fShriekFunctor.{u, u + 1} B U.obj.hom).map φ).1) =
      AddCommGrpCat.ofHom (SmallEtale.fiberStalksMap.{u, u + 1} B U.obj.hom s φ) ≫
        (SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s H).inv :=
    (Iso.eq_comp_inv _).2
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => (SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s G).inv ≫ z)
            (SmallEtale.fShriekStalkIso_natural.{u, u + 1} B U.obj.hom s φ)).trans
          ((SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s G).inv_hom_id_assoc _)))
  have hsummand : SmallEtale.fiberStalkOf.{u, u + 1} B U.obj.hom s G x ≫
        AddCommGrpCat.ofHom (SmallEtale.fiberStalksMap.{u, u + 1} B U.obj.hom s φ) =
      colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B U.obj.left.1 U.obj.left.property
            (x.toGeometricPoint B U.obj.hom s))).op φ.1) ≫
        SmallEtale.fiberStalkOf.{u, u + 1} B U.obj.hom s H x := by
    refine ConcreteCategory.hom_ext _ _ fun z => ?_
    exact (ConcreteCategory.comp_apply _ _ z).trans
      ((SmallEtale.fiberStalksMap_fiberStalkOf.{u, u + 1} B U.obj.hom s φ x z).trans
        (ConcreteCategory.comp_apply _ _ z).symm)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => SmallEtale.fiberStalkOf.{u, u + 1} B U.obj.hom s G x ≫ z) hiso).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫
            (SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s H).inv) hsummand).trans
          (Category.assoc _ _ _))))

/-- The summand inclusion of the stalk decomposition of Stacks 0F5F is the unit of the
extension-by-zero adjunction of Stacks 03S3, read through the comparison of Stacks 0F6Q. -/
public theorem fShriekStalkSummand_eq_extensionUnitStalkMap
    (G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}) :
    fShriekStalkSummand B X hX U s x G =
      extensionUnitStalkMap B X hX U s x G ≫
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B X hX s)).op
          ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).hom.app G).1) :=
  ((Iso.eq_comp_inv _).2
    ((Category.assoc _ _ _).trans
      (extensionUnitStalkMap_comp_fShriekStalkIso B X hX U s G x))).symm

/-- The stalk map of the counit of `j_! ⊣ j^{-1}` splits along the two comparisons out of which
the adjunction is transported. -/
public theorem stalkMap_counit_app_eq
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :
    colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B X hX s)).op
          ((etaleFShriekAbPullbackAdjunction B X hX U).counit.app F).1) =
      colim.map (Functor.whiskerLeft (CategoryOfElements.π
            (geometricPointFiber B X hX s)).op
            ((SmallEtale.fShriekFunctor.{u, u + 1} B U.obj.hom).map
              ((etaleRestrictionIso B X hX U).hom.app F)).1) ≫
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
            (geometricPointFiber B X hX s)).op
            ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).inv.app
              ((abelianRestriction B X hX U).obj F)).1) ≫
          colim.map (Functor.whiskerLeft (CategoryOfElements.π
            (geometricPointFiber B X hX s)).op
            ((abelianExtensionByZeroAdjunction B X hX U).counit.app F).1) := by
  rw [etaleFShriekAbPullbackAdjunction_counit_app, stalkMap_comp, stalkMap_comp]

/-- The stalk maps of the comparison of Stacks 0F6Q and of its inverse cancel. -/
public theorem stalkMap_abelianExtensionByZeroIsoFShriek_hom_inv
    (G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}) :
    colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B X hX s)).op
          ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).hom.app G).1) ≫
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B X hX s)).op
          ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).inv.app G).1) =
      𝟙 _ := by
  rw [← stalkMap_comp, Iso.hom_inv_id_app]
  exact stalkMap_id B X hX s _

/-- **The counit of `j_! ⊣ j^{-1}` acts on the summand indexed by `x` as the identification of
Stacks 03Q1.** This is the triangle identity of the adjunction read on geometric stalks: the
summand inclusion is the unit of the extension-by-zero adjunction of Stacks 03S3 and the counit
cancels it. -/
public theorem fShriekStalkSummand_comp_counit
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :
    fShriekStalkSummand B X hX U s x
          ((SmallEtale.abPullback.{u, u + 1} B U.obj.hom).obj F) ≫
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
          (geometricPointFiber B X hX s)).op
          ((etaleFShriekAbPullbackAdjunction B X hX U).counit.app F).1) =
      (SmallEtale.fiberPointPullbackStalkIso.{u, u + 1} B U.obj.hom s F x).hom := by
  have hinner : fShriekStalkSummand B X hX U s x ((abelianRestriction B X hX U).obj F) ≫
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
            (geometricPointFiber B X hX s)).op
            ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).inv.app
              ((abelianRestriction B X hX U).obj F)).1) ≫
          colim.map (Functor.whiskerLeft (CategoryOfElements.π
            (geometricPointFiber B X hX s)).op
            ((abelianExtensionByZeroAdjunction B X hX U).counit.app F).1) =
      restrictionStalkMap B X hX U s x F := by
    rw [fShriekStalkSummand_eq_extensionUnitStalkMap]
    erw [Category.assoc, reassoc_of% stalkMap_abelianExtensionByZeroIsoFShriek_hom_inv B X hX U s,
      extensionUnitStalkMap_comp_counit]
  rw [stalkMap_counit_app_eq]
  erw [← Category.assoc, fShriekStalkSummand_natural, Category.assoc, hinner,
    restrictionStalkMap_comp_etaleRestrictionIso]

end Stalks

section Identification

variable (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})

/-- **The counit of `j_! ⊣ j^{-1}` is a trace map for the canonical weighting of `j`.** At every
geometric point of `X` the map it induces on stalks is, through the decomposition of Stacks 0F5F,
the sum over the geometric fibre — the behaviour Stacks 0GKG prescribes for the trace map of
Example 0GKI, the canonical weighting of an étale morphism being the constant function `1`. -/
public theorem hasWeightedTraceStalks_counit :
    SmallEtale.HasWeightedTraceStalks.{u, u + 1} B U.obj.hom
      (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) F
      ((etaleFShriekAbPullbackAdjunction B X hX U).counit.app F) := by
  intro s
  refine SmallEtale.fiberStalks_hom_ext.{u, u + 1} B U.obj.hom s fun x z => ?_
  have h := ConcreteCategory.congr_hom (fShriekStalkSummand_comp_counit B X hX U s x F) z
  refine Eq.trans ?_ (SmallEtale.weightedTraceStalkMap_fiberStalkOf.{u, u + 1} B U.obj.hom
    (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) F s x z).symm
  rw [flatQuasiFiniteWeight_eq_one_of_etale (B.inclusion.map U.obj.hom) (x.1 default), one_smul]
  simp only [fShriekStalkSummand] at h ⊢
  exact h

/-- For an étale morphism `j : U ⟶ X` the trace map `Tr : j_! j^{-1}ℱ ⟶ ℱ` of Example 0GKI is
the counit of the adjunction between `j_!` and `j^{-1}`.

The trace map of Example 0GKI is the morphism Stacks 0GKG attaches to the canonical weighting of
Stacks 0F3D, characterised by its behaviour on geometric stalks; so the identification is stated
as an equivalence: a morphism `j_! j^{-1}ℱ ⟶ ℱ` has that behaviour exactly when it is the
counit. The forward direction is the remark's equality and the backward direction produces the
trace map. -/
@[stacks 0GL4 "For an abelian étale sheaf `ℱ`: a morphism `j_! j^{-1}ℱ ⟶ ℱ` has the behaviour
on geometric stalks by which Lemma 0GKG characterises the trace map of Example 0GKI, for the
canonical weighting of Stacks 0F3D, exactly when it is the counit of the adjunction
`j_! ⊣ j^{-1}`. The forward implication is the remark's equality; the backward implication
produces the trace map, so nothing about it is assumed.",
  sga "4 XVII 6.2.11" "more general",
  sga "4 XVIII 3.1.8" "(iii), special case",
  sga "4½ Dualite 2.3" "special case"]
public theorem hasWeightedTraceStalks_iff_eq_counit
    (τ : (SmallEtale.fShriekFunctor.{u, u + 1} B U.obj.hom).obj
      ((SmallEtale.abPullback.{u, u + 1} B U.obj.hom).obj F) ⟶ F) :
    SmallEtale.HasWeightedTraceStalks.{u, u + 1} B U.obj.hom
        (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) F τ ↔
      τ = (etaleFShriekAbPullbackAdjunction B X hX U).counit.app F :=
  ⟨fun h => SmallEtale.hasWeightedTraceStalks_unique.{u, u + 1} B U.obj.hom
      (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) F h
      (hasWeightedTraceStalks_counit B X hX U F),
    fun h => h ▸ hasWeightedTraceStalks_counit B X hX U F⟩

end Identification

end AlgebraicGeometry

end
