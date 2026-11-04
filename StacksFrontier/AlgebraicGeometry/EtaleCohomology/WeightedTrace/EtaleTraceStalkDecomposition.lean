module

public import StacksFrontier.AlgebraicGeometry.Etale.EtaleUpperShriekRestriction
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleRestrictionStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceConstruction
public import StacksCore.Tactic.StacksAttribute

/-!
# The unit of `j_! ⊣ j^{-1}` is the summand inclusion of the stalk decomposition

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`, let
`G` be an abelian sheaf on `U`, let `s` be a geometric point of `X` and let `x` be a point of
the geometric fibre of `j` above `s`. There are two descriptions of the stalk `(j_!G)_s`:

* extension by zero of Stacks 03S3 is the direct image with compact support of Stacks 0F6R, by
  Stacks 0F6Q, and the stalk of the latter decomposes as `⨁_{j(x̄) = s̄} G_x̄` by Stacks 0F5F;
* a section of `G` over an étale neighbourhood `W ⟶ U` of `x` is a section of `j_!G` over `W`
  viewed as an étale neighbourhood of `s` in `X`, by the unit of `j_! ⊣ j^{-1}`, so its germ at
  `x` has a germ at `s`.

This file proves that the second map is the inclusion of the summand indexed by `x` in the
first decomposition. That is the geometric input of Stacks 0GL4: combined with the triangle
identity of `j_! ⊣ j^{-1}` it says that the counit acts on the summand indexed by `x` as the
identification `G_x = ℱ_s` of Stacks 03Q1, which is the prescribed behaviour of the trace map
of Stacks 0GKG for the weighting constant equal to one.

## Main results

* `AlgebraicGeometry.abelianExtensionByZeroAdjunction_unit_hom_app` — the unit of the
  extension-by-zero adjunction on sections is the unit of the left Kan extension followed by the
  sheafification unit.
* `AlgebraicGeometry.extensionUnitStalkMap_eq_liftedStalkToExtension` — the unit map on stalks
  of `AlgebraicGeometry.extensionUnitStalkMap` is the presheaf-level germ map
  `AlgebraicGeometry.SmallEtale.liftedStalkToExtension` of the proof of Stacks 0F6Q, followed by
  the invariance of the stalk under sheafification.
* `AlgebraicGeometry.extensionUnitStalkMap_comp_fShriekStalkIso` — **the unit is the summand
  inclusion.** Composing the unit map on stalks with the comparison of Stacks 0F6Q and the stalk
  decomposition of Stacks 0F5F gives the inclusion of the summand indexed by `x`.

## Implementation notes

The whole computation is the identity
`AlgebraicGeometry.SmallEtale.liftedStalkToExtension_comp` of the proof of Stacks 0F6Q, read
through the invariance of a geometric stalk under sheafification. Nothing new about geometric
fibres is proved here; what is new is that the map which the proof of Stacks 0F6Q builds by
hand out of germs of Kan-extension generators is the unit of the adjunction of Stacks 03S3,
which is what connects it to the trace map.

The two spellings of a point of the geometric fibre above `s` — a lift of `s` to `U` in the
sense of `AlgebraicGeometry.geometricPointLifts`, and a point of the geometric fibre in the
sense of `AlgebraicGeometry.SmallEtale.GeometricFiberPoint` — are the same subtype, and
`AlgebraicGeometry.pushLift` and `AlgebraicGeometry.SmallEtale.liftedPoint` are the same lift;
they differ only in the proof field, so no transport is needed.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 0F6Q](https://stacks.math.columbia.edu/tag/0F6Q)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0GL4](https://stacks.math.columbia.edu/tag/0GL4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u

namespace AlgebraicGeometry

/-- The inclusion of a summand of a direct sum does not depend on the decidability instance
chosen for the index type. -/
private theorem directSum_of_congr {ι : Type*} (β : ι → Type*) [∀ i, AddCommMonoid (β i)]
    (inst₁ inst₂ : DecidableEq ι) (i : ι) (b : β i) :
    (letI := inst₁; DirectSum.of β i b) = (letI := inst₂; DirectSum.of β i b) := by
  cases Subsingleton.elim inst₁ inst₂
  rfl

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  (s : GeometricPoint X)

/-- The unit of the extension-by-zero adjunction of Stacks 03S3, on sections over an étale
object `W ⟶ U`: a section of `G` over `W` is sent to its image in the left Kan extension
`j_{p!}G`, read in the sheafification `j_!G`, over `W` viewed as étale over `X`. -/
public theorem abelianExtensionByZeroAdjunction_unit_hom_app
    (G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    ((abelianExtensionByZeroAdjunction B X hX U).unit.app G).hom.app (op W) =
      ((smallEtalePostcompose B X hX U).op.lanUnit.app G.obj).app (op W) ≫
        (toSheafify (SmallEtale.topology B X hX)
            ((abelianPresheafExtensionByZero B X hX U).obj G)).app
          (op ((smallEtalePostcompose B X hX U).obj W)) :=
  rfl

section Sheafification

/-- The invariance of a geometric stalk under sheafification, on a germ: the germ of a section
of a presheaf goes to the germ of its image under the sheafification unit. -/
public theorem etaleStalkSheafificationMap_etaleGerm
    (P : (SmallEtale B X hX)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (V : SmallEtale B X hX) (q : (geometricPointFiber B X hX s).obj V)
    (a : ↑(P.obj (op V))) :
    etaleStalkSheafificationMap B X hX s P (SmallEtale.etaleGerm B X hX s P V q a) =
      SmallEtale.etaleGerm B X hX s
        ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj P).obj V q
        ((toSheafify (SmallEtale.topology B X hX) P).app (op V) a) :=
  (ConcreteCategory.comp_apply _ _ a).symm.trans
    ((ConcreteCategory.congr_hom (colimit_ι_comp_etaleStalkSheafificationMap B X hX s P
        (op (⟨V, q⟩ : (geometricPointFiber B X hX s).Elements))) a).trans
      (ConcreteCategory.comp_apply _ _ a))

end Sheafification

section Summand

variable (G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
  AddCommGrpCat.{u + 1}) (x : SmallEtale.GeometricFiberPoint B U.obj.hom s)

/-- The unit map on stalks is the germ map of the proof of Stacks 0F6Q followed by the
invariance of a geometric stalk under sheafification: the unit of Stacks 03S3 on sections is the
unit of the left Kan extension followed by the sheafification unit, and the germ of a section of
a presheaf is carried to the germ of its image in the sheafification. -/
public theorem extensionUnitStalkMap_eq_liftedStalkToExtension :
    extensionUnitStalkMap B X hX U s x G =
      SmallEtale.liftedStalkToExtension B X hX U s G x ≫
        etaleStalkSheafificationMap B X hX s
          ((abelianPresheafExtensionByZero B X hX U).obj G) := by
  refine ConcreteCategory.hom_ext _ _ fun g => ?_
  obtain ⟨W, w, a, rfl⟩ := SmallEtale.exists_etaleGerm_eq B U.obj.left.1 U.obj.left.property
    (x.toGeometricPoint B U.obj.hom s) G.obj g
  refine (pushStalkMap_etaleGerm B X hX U s x ((abelianExtensionByZero B X hX U).obj G) G
    ((abelianExtensionByZeroAdjunction B X hX U).unit.app G) W w a).trans ?_
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg (etaleStalkSheafificationMap B X hX s
      ((abelianPresheafExtensionByZero B X hX U).obj G))
    (SmallEtale.liftedStalkToExtension_etaleGerm B X hX U s G x W w a)).symm
  exact (etaleStalkSheafificationMap_etaleGerm B X hX s
    ((abelianPresheafExtensionByZero B X hX U).obj G)
    ((smallEtalePostcompose B X hX U).obj W) (pushLift B X hX U s W x w)
    (((smallEtalePostcompose B X hX U).op.lanUnit.app G.obj).app (op W) a)).symm

/-- Sheafifying the comparison of Stacks 0F6Q commutes with the sheafification unit on stalks:
the stalk map of the comparison between the two presheaves, followed by the invariance of the
stalk of the finite-support direct image presheaf, is the invariance of the stalk of the
presheaf extension by zero followed by the stalk map of the sheafified comparison. -/
public theorem etaleStalkSheafificationMap_comp_abelianExtensionByZeroIsoFShriek :
    etaleStalkSheafificationMap B X hX s
          ((abelianPresheafExtensionByZero B X hX U).obj G) ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B X hX s)).op
          ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).hom.app G).1) =
      SmallEtale.comparisonStalkMap B X hX U s G ≫
        etaleStalkSheafificationMap B X hX s
          ((SmallEtale.etaleFiniteSupportPresheaf B X hX U).obj G) :=
  ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map_comp
      (toSheafify (SmallEtale.topology B X hX)
        ((abelianPresheafExtensionByZero B X hX U).obj G))
      (sheafifyMap (SmallEtale.topology B X hX)
        ((SmallEtale.etaleExtensionToFiniteSupport B X hX U).app G))).symm.trans
    ((congrArg (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map
        (toSheafify_naturality (SmallEtale.topology B X hX)
          ((SmallEtale.etaleExtensionToFiniteSupport B X hX U).app G)).symm).trans
      ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map_comp
        ((SmallEtale.etaleExtensionToFiniteSupport B X hX U).app G)
        (toSheafify (SmallEtale.topology B X hX)
          ((SmallEtale.etaleFiniteSupportPresheaf B X hX U).obj G))))

/-- The invariance of the stalk of the presheaf extension by zero under sheafification, followed
by the comparison of Stacks 0F6Q and the stalk decomposition of Stacks 0F5F, is the stalk map of
the comparison followed by the germ decomposition of Stacks 0F6P. -/
public theorem etaleStalkSheafificationMap_comp_fShriekStalkIso :
    etaleStalkSheafificationMap B X hX s
          ((abelianPresheafExtensionByZero B X hX U).obj G) ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B X hX s)).op
          ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).hom.app G).1) ≫
        (SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s G).hom =
      SmallEtale.comparisonStalkMap B X hX U s G ≫
        SmallEtale.etaleFiniteSupportStalkMap B X hX U s G :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s G).hom)
        (etaleStalkSheafificationMap_comp_abelianExtensionByZeroIsoFShriek
          B X hX U s G)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => SmallEtale.comparisonStalkMap B X hX U s G ≫ z)
          (SmallEtale.fShriekStalkIso_comp_sheafification.{u, u + 1} B U.obj.hom s G))))

/-- The germ map of the proof of Stacks 0F6Q, followed by the stalk map of the comparison and
the germ decomposition of Stacks 0F6P, is the inclusion of the summand indexed by `x`. This is
`AlgebraicGeometry.SmallEtale.liftedStalkToExtension_comp` read as an equality of morphisms. -/
public theorem liftedStalkToExtension_comp_etaleFiniteSupportStalkMap :
    SmallEtale.liftedStalkToExtension B X hX U s G x ≫
        SmallEtale.comparisonStalkMap B X hX U s G ≫
        SmallEtale.etaleFiniteSupportStalkMap B X hX U s G =
      SmallEtale.fiberStalkOf.{u, u + 1} B U.obj.hom s G x := by
  refine ConcreteCategory.hom_ext _ _ fun z => ?_
  have hz := SmallEtale.liftedStalkToExtension_comp B X hX U s G x z
  rw [ConcreteCategory.comp_apply] at hz
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hz]
  exact directSum_of_congr (fun y : SmallEtale.GeometricFiberPoint B U.obj.hom s =>
    ↑(etaleStalk B U.obj.left.1 U.obj.left.property
      (y.toGeometricPoint B U.obj.hom s) G.obj)) _ (Classical.decEq _) x z

/-- **The unit of `j_! ⊣ j^{-1}` is the inclusion of a summand of the stalk decomposition.**
The germ map `G_x ⟶ (j_!G)_s` given by the unit of the extension-by-zero adjunction, read
through the identification of `j_!` with the direct image with compact support of Stacks 0F6Q
and the stalk decomposition `(j_!G)_s ≅ ⨁_{j(x̄) = s̄} G_x̄` of Stacks 0F5F, is the inclusion of
the summand indexed by `x`. -/
public theorem extensionUnitStalkMap_comp_fShriekStalkIso :
    extensionUnitStalkMap B X hX U s x G ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B X hX s)).op
          ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).hom.app G).1) ≫
        (SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s G).hom =
      SmallEtale.fiberStalkOf.{u, u + 1} B U.obj.hom s G x :=
  (congrArg (fun z => z ≫ colim.map (Functor.whiskerLeft
        (CategoryOfElements.π (geometricPointFiber B X hX s)).op
        ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).hom.app G).1) ≫
      (SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s G).hom)
    (extensionUnitStalkMap_eq_liftedStalkToExtension B X hX U s G x)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => SmallEtale.liftedStalkToExtension B X hX U s G x ≫ z)
          (etaleStalkSheafificationMap_comp_fShriekStalkIso B X hX U s G)).trans
        (liftedStalkToExtension_comp_etaleFiniteSupportStalkMap B X hX U s G x)))

end Summand

end AlgebraicGeometry

end
