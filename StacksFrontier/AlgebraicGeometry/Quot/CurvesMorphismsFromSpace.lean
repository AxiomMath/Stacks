module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesOverSpace
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStack
public import StacksFrontier.AlgebraicGeometry.Quot.FamiliesOverBaseSpace
public import StacksFrontier.AlgebraicGeometry.Quot.SpacesOverSpaceEquivalence
public import StacksFrontier.AlgebraicGeometry.Quot.SpacesOverSpaceEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.CategoryTheory.FiberedCategory.BasedFunctorPostcompFullyFaithful
public import StacksFrontier.CategoryTheory.FiberedCategory.BasedFunctorWhiskering
public import StacksFrontier.CategoryTheory.FiberedCategory.CostructuredArrowBasedFunctor

/-!
# Morphisms from an algebraic space to the stack of curves (Stacks 0DMK)

Let `T → B` be a morphism of algebraic spaces. Stacks 0DMK asserts that the category
`Mor_B(T, B-Curves)` of morphisms over `B` from `T` to the stack `B-Curves` of families of curves
over schemes over `B` is the category `Mor(T, Curves)` of morphisms from `T` to the stack of
curves, and that this is the category of families of curves over `T`, i.e. of morphisms of
algebraic spaces `X → T` which are flat, proper, of finite presentation and of relative dimension
at most one.

Here the algebraic space `T` is the category `(Sch/T)` of schemes with a morphism to `T`, over
the big fppf site of schemes, and the stack `B-Curves` is the category of families of curves
`X → S` together with a morphism `S → B`, over `(Sch/B)`. A morphism over `B` from `T` to
`B-Curves` is a functor `(Sch/T) → B-Curves` over `(Sch/B)`, and a morphism of such is a natural
transformation lying over identities of `(Sch/B)`.

## Main definitions

* `AlgebraicGeometry.curvesOverSpaceBased`: the stack `B-Curves` as a category over `(Sch/B)`;
  its objects are those of `AlgebraicGeometry.CurveFamilyOver` (Stacks 0D54).
* `AlgebraicGeometry.schemesOverSpaceBased` and `AlgebraicGeometry.schemesOverSpaceBasedOver`:
  an algebraic space `T` as the category `(Sch/T)` over the big fppf site of schemes, and over
  `(Sch/B)` along a morphism `T → B`.
* `AlgebraicGeometry.curveFamilyProperty`: the defining property of a family of curves over an
  algebraic space, and `AlgebraicGeometry.CurveFamilyOnSpace` the category of families of curves
  over an algebraic space `T`, whose morphisms are the isomorphisms over `T`.
* `AlgebraicGeometry.SpacesOverSpace.cartesianFamiliesInclusion`: for properties `P ≤ Q` of
  morphisms of algebraic spaces, the inclusion of the families with `P` among those with `Q`.
* `AlgebraicGeometry.pointsSchemesOverSpaceEquivalence`: the category `𝒮_T` of points of `T` and
  the category `(Sch/T)` are equivalent over the site.

## Main results

* `AlgebraicGeometry.relativeCurvesMorphismsEquivalence`: **Stacks 0DMK**, the identification
  `Mor_B(T, B-Curves) = Mor(T, Curves)`.
* `AlgebraicGeometry.curvesMorphismsEquivalence`: **Stacks 0DMK**, the identification of
  `Mor(T, Curves)` with the category of families of curves over `T`.
* `AlgebraicGeometry.relativeCurvesMorphismsCurveFamilyEquivalence`: **Stacks 0DMK**, the two
  together.
* `AlgebraicGeometry.Space.hasRelativeDimensionLE_iff_forall_pullback`: a morphism of algebraic
  spaces locally of finite type has relative dimension at most `d` exactly when each of its base
  changes to a scheme does.
* `AlgebraicGeometry.SpacesOverSpace.baseChangeFunctor_isEquivalence_of_le`: the base-change
  equivalence of Stacks 0E93 restricts to a smaller property detected on base changes to schemes.
* `AlgebraicGeometry.curveFamilyBaseChange_isEquivalence`: base change along the points of `T` is
  an equivalence from families of curves over `T` to functors from `𝒮_T` to families of curves.

## Implementation notes

The first identification of the source is the product description of `B-Curves` of Stacks 0D54:
a functor over `(Sch/B)` into the category of families of curves equipped with a morphism of the
base to `B` is a functor over the site into the category of families of curves, the morphism to
`B` of the image of a scheme `U → T` being forced to be `U → T → B`. This is
`CategoryTheory.CostructuredArrow.basedFunctorEquivalence`.

The second identification, of `Mor(T, Curves)` with `AlgebraicGeometry.CurveFamilyOnSpace`, is
the restriction to families of relative dimension at most one of the identification of Stacks
0E93 of the morphisms from `T` to the stack of finitely presented, flat and proper families of
algebraic spaces with the finitely presented, flat and proper algebraic spaces over `T`. The
source glues a family over `T` out of its pullback to an étale atlas (Stacks 0ADV); this is the
gluing behind Stacks 0E93, and what is left is that the glued `X ⟶ T` has relative dimension at
most one when its base changes to schemes do, which is
`AlgebraicGeometry.Space.hasRelativeDimensionLE_iff_forall_pullback`. Stacks 0E93 is stated for
the category `𝒮_T` of points of `T`, and the identification with `(Sch/T)` is the Yoneda lemma;
the stack of curves is compared with the category of algebraic spaces over varying schemes with
the four conditions of a family of curves by `AlgebraicGeometry.curveFamilyEquivalence`.

## References

* [Stacks Project, Tag 0DMK](https://stacks.math.columbia.edu/tag/0DMK)
* [Stacks Project, Tag 0D54](https://stacks.math.columbia.edu/tag/0D54)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 0E93](https://stacks.math.columbia.edu/tag/0E93)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

section RelativeDimension

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Relative dimension at most `d` at a point is invariant under base change of the morphism. -/
private theorem hasRelativeDimensionLEAt_iff_of_isPullback (d : ℕ)
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hf : Space.IsLocallyOfFiniteType B S hS f)
    (x' : Space.points B S hS W) :
    Space.HasRelativeDimensionLEAt d B S hS p x' ↔
      Space.HasRelativeDimensionLEAt d B S hS f (Space.pointsMap B S hS W q x') :=
  exists_congr fun e => and_congr_right fun _ =>
    Space.hasRelativeDimensionAt_iff_of_isPullback' B S hS (e : ℕ∞) sq hX hY hZ hf x'

/-- **Relative dimension is tested on base changes to schemes.** A morphism `f : X ⟶ Y` of
algebraic spaces which is locally of finite type has relative dimension at most `d` (Stacks
06LR) if and only if its base change `U ×_Y X ⟶ U` along every morphism from a scheme to `Y`
does.

The relative dimension at a point of a base change is that at the image point (Stacks 04NS), and
every point of `X` is the image of a point of the base change along an atlas of `Y`. -/
theorem Space.hasRelativeDimensionLE_iff_forall_pullback (d : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : Space.IsLocallyOfFiniteType B S hS f) :
    Space.HasRelativeDimensionLE d B S hS f ↔
      ∀ (U : BigFppfOver B S hS) (t : yoneda.obj U ⟶ Y),
        Space.HasRelativeDimensionLE d B S hS (pullback.fst t f) := by
  refine ⟨fun h U t x' => ?_, fun h x => ?_⟩
  · exact (hasRelativeDimensionLEAt_iff_of_isPullback B S hS d (IsPullback.of_hasPullback t f)
      hX hY (isAlgebraicSpace_yoneda B S hS U) hf x').2 (h _)
  · obtain ⟨V, a, hsurj, -⟩ := hY.exists_atlas
    obtain ⟨v, hv⟩ := (Space.surjective_iff_surjective_pointsMap B S hS Y hY V a).1 hsurj
      (Space.pointsMap B S hS X f x)
    obtain ⟨w, -, hw⟩ := Space.exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback a f) v x hv
    rw [← hw]
    exact (hasRelativeDimensionLEAt_iff_of_isPullback B S hS d (IsPullback.of_hasPullback a f)
      hX hY (isAlgebraicSpace_yoneda B S hS V) hf w).1 (h V a w)

end RelativeDimension

/-! ### Restricting the base-change equivalence to a smaller property -/

namespace SpacesOverSpace

section Restriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {P Q : MorphismProperty (AlgebraicSpaces B S hS)} {T : AlgebraicSpaces B S hS}

/-- For properties `P ≤ Q` of morphisms of algebraic spaces, the families with property `P` are
among the families with property `Q`: the inclusion, as a functor over the site, keeping the
cartesian squares. -/
def cartesianFamiliesInclusion (hPQ : P ≤ Q) :
    BasedCategory.ofFunctor (cartesianProjection B S hS P) ⥤ᵇ
      BasedCategory.ofFunctor (cartesianProjection B S hS Q) where
  obj Y := ⟨⟨Y.obj.obj, hPQ _ Y.obj.property⟩⟩
  map φ := ⟨ObjectProperty.homMk φ.hom.hom, φ.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl
  w := rfl

/-- The inclusion of the families with property `P` among those with property `Q` is fully
faithful: both have the cartesian squares as morphisms. -/
def cartesianFamiliesInclusionFullyFaithful (hPQ : P ≤ Q) :
    (cartesianFamiliesInclusion (B := B) (S := S) (hS := hS) hPQ).toFunctor.FullyFaithful where
  preimage φ := ⟨ObjectProperty.homMk φ.hom.hom, φ.property⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- A family isomorphic to a family with property `P` has property `P`, for `P` respecting
isomorphisms: the isomorphism of families is an isomorphism of the structure morphisms as
arrows. -/
theorem familyProperty_of_iso [P.RespectsIso]
    {X Y : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (e : X ≅ Y) (hX : familyProperty B S hS P X) : familyProperty B S hS P Y := by
  refine (P.arrow_mk_iso_iff (Arrow.isoMk ((Comma.fst _ _).mapIso e)
    ((schemeSpaceFunctor B S hS).mapIso ((Comma.snd _ _).mapIso e)) ?_)).1 hX
  exact ObjectProperty.hom_ext _ e.hom.w

variable [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
  [Q.IsLocalAtTarget (Space.Topology.precoverage.{u, 0} .fpqc B S hS)]

/-- **Essential surjectivity of base change for a smaller property.** Let `P ≤ Q` be properties
of morphisms of algebraic spaces, both stable under base change, `Q` local on the target for the
fpqc topology, and such that a morphism `X ⟶ T` with `Q` whose base changes along all
scheme-valued points of `T` have `P` itself has `P`. Then every functor over the site from `𝒮_T`
to the families with property `P` is the base-change functor of an algebraic space over `T` with
property `P`.

The functor composed with the inclusion of families with `P` among families with `Q` is the
base-change functor of some `X ⟶ T` with `Q` (Stacks 0E93); its values are the base changes of
`X`, so these have `P`, hence `X ⟶ T` has `P`; and postcomposition with the inclusion is fully
faithful, so the isomorphism of base-change functors comes from one over `P`. -/
theorem baseChangeFunctor_essSurj_of_le (hPQ : P ≤ Q)
    (hP : ∀ X : Over T, Q X.hom →
      (∀ a : (pointsCategory B S hS T).obj, familyProperty B S hS P (baseChangeComma X a)) →
        P X.hom) :
    (baseChangeFunctor (B := B) (S := S) (hS := hS) (P := P) (T := T)).EssSurj := by
  refine ⟨fun G => ?_⟩
  let J := cartesianFamiliesInclusion (B := B) (S := S) (hS := hS) hPQ
  let Φ := baseChangeFunctor (B := B) (S := S) (hS := hS) (P := Q) (T := T)
  let G' : pointsCategory B S hS T ⥤ᵇ BasedCategory.ofFunctor (cartesianProjection B S hS Q) :=
    G.comp J
  let X := Φ.objPreimage G'
  let e : Φ.obj X ≅ G' := Φ.objObjPreimageIso G'
  have hX : P X.1.of.hom := hP X.1.of X.2 fun a => by
    let ea := ((BasedNatTrans.forgetful _ _).mapIso e).app a
    let ec := (wideSubcategoryInclusion _ ⋙ (familyProperty B S hS Q).ι).mapIso ea
    exact familyProperty_of_iso ec.symm (G.obj a).obj.property
  exact ⟨(⟨X.1, hX⟩ : SpacesOver B S hS P T),
    ⟨(BasedFunctor.postcompFullyFaithful (pointsCategory B S hS T) J
      (cartesianFamiliesInclusionFullyFaithful hPQ)).preimageIso e⟩⟩

/-- **The base-change equivalence for a smaller property.** Under the hypotheses of
`AlgebraicGeometry.SpacesOverSpace.baseChangeFunctor_essSurj_of_le`, base change along the points
of `T` is an equivalence from the algebraic spaces over `T` with property `P` to the functors
over the site from `𝒮_T` to the families with property `P`. -/
theorem baseChangeFunctor_isEquivalence_of_le (hPQ : P ≤ Q)
    (hP : ∀ X : Over T, Q X.hom →
      (∀ a : (pointsCategory B S hS T).obj, familyProperty B S hS P (baseChangeComma X a)) →
        P X.hom) :
    (baseChangeFunctor (B := B) (S := S) (hS := hS) (P := P) (T := T)).IsEquivalence :=
  have := baseChangeFunctor_essSurj_of_le hPQ hP
  ⟨inferInstance, inferInstance, inferInstance⟩

end Restriction

end SpacesOverSpace

/-! ### Families of curves over an algebraic space -/

section CurveFamilyOnSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The defining property of a *family of curves* over an algebraic space: a morphism of
algebraic spaces which is of finite presentation, flat, proper and of relative dimension at most
one (Stacks 06LR). -/
abbrev curveFamilyProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  SpacesOverSpace.properFlatProperty B S hS ⊓
    fun _ _ f => Space.HasRelativeDimensionLE 1 B S hS f.hom

attribute [local instance] Space.isFlat_isStableUnderBaseChange in
/-- Being a family of curves is stable under base change: the first three conditions by Stacks
03XR, 03MO and 04WP, and the bound on the relative dimension by Stacks 04NS, the structure
morphism being locally of finite type. -/
instance curveFamilyProperty_isStableUnderBaseChange :
    (curveFamilyProperty B S hS).IsStableUnderBaseChange where
  of_isPullback {X Y Y' Z} {f g f' g'} sq hg := by
    refine ⟨MorphismProperty.of_isPullback sq hg.1, fun x' => ?_⟩
    obtain ⟨e, he, hx⟩ := hg.2 (Space.pointsMap B S hS _ f'.hom x')
    exact ⟨e, he, (Space.hasRelativeDimensionAt_iff_of_isPullback' B S hS (e : ℕ∞)
      (AlgebraicSpaces.isPullback_hom B S hS sq).flip Y.property Z.property X.property
      (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hg.1.1.1) x').2 hx⟩

/-- The category of *families of curves* over an algebraic space `T`: morphisms `X → T` of
algebraic spaces which are flat, proper, of finite presentation and of relative dimension at most
one, with the isomorphisms over `T` as morphisms. -/
abbrev CurveFamilyOnSpace (T : AlgebraicSpaces B S hS) :=
  SpacesOverSpace.SpacesOver B S hS (curveFamilyProperty B S hS) T

attribute [local instance] Space.isFlat_isStableUnderBaseChange in
/-- **Families of curves over `T` are the functors from `𝒮_T` to families of curves.** Base
change along the points of an algebraic space `T` is an equivalence from the families of curves
over `T` to the functors over the site from `𝒮_T` to the families of curves over schemes.

This is Stacks 0E93 for finitely presented, flat and proper morphisms restricted to relative
dimension at most one: a finitely presented, flat and proper morphism `X ⟶ T` all of whose base
changes to schemes have relative dimension at most one has relative dimension at most one
(`AlgebraicGeometry.Space.hasRelativeDimensionLE_iff_forall_pullback`). -/
theorem curveFamilyBaseChange_isEquivalence (T : AlgebraicSpaces B S hS) :
    (SpacesOverSpace.baseChangeFunctor (B := B) (S := S) (hS := hS)
      (P := curveFamilyProperty B S hS) (T := T)).IsEquivalence :=
  SpacesOverSpace.baseChangeFunctor_isEquivalence_of_le
    (Q := SpacesOverSpace.properFlatProperty B S hS) (fun _ _ _ h => h.1) fun X hX hbc =>
      ⟨hX, (Space.hasRelativeDimensionLE_iff_forall_pullback B S hS 1 X.hom.hom X.left.property
        T.property (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
          hX.1.1)).2 fun U t => by
        have h : Space.HasRelativeDimensionLE 1 B S hS (pullback.fst
            (SpacesOverSpace.pointMap (SpacesOverSpace.pt U (yonedaEquiv t))).hom X.hom.hom) :=
          (hbc (SpacesOverSpace.pt U (yonedaEquiv t))).2
        rwa [SpacesOverSpace.pointMap_pt_yonedaEquiv] at h⟩

end CurveFamilyOnSpace

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- An algebraic space `T` as the category `(Sch/T)` of schemes with a morphism to `T`, over the
big fppf site of schemes. -/
abbrev schemesOverSpaceBased (T : AlgebraicSpaces B integerBase hZ) :
    BasedCategory (BigFppfOver B integerBase hZ) :=
  BasedCategory.ofFunctor (bigFppfOverSpaceProjection B integerBase hZ T)

/-- An algebraic space `T` with a morphism to an algebraic space `A`, as the category `(Sch/T)`
over `(Sch/A)`. -/
abbrev schemesOverSpaceBasedOver {T A : AlgebraicSpaces B integerBase hZ} (f : T ⟶ A) :
    BasedCategory (BigFppfOverSpace B integerBase hZ A) :=
  BasedCategory.ofFunctor (CostructuredArrow.map f :
    BigFppfOverSpace B integerBase hZ T ⥤ BigFppfOverSpace B integerBase hZ A)

/-- The stack `A-Curves` of families of curves over schemes over an algebraic space `A`, as a
category over `(Sch/A)`: the base change of the stack of curves from the big fppf site to
`(Sch/A)`. -/
abbrev curvesOverSpaceBased (A : AlgebraicSpaces B integerBase hZ) :
    BasedCategory (BigFppfOverSpace B integerBase hZ A) :=
  CostructuredArrow.baseChangeBased (curvesFiberedCategory B hZ).val
    (schemeSpaceFunctor B integerBase hZ) A

/-- The objects of `A-Curves` are the families of curves over a scheme with a morphism from the
scheme to `A`, the category of Stacks 0D54. -/
theorem curvesOverSpaceBased_obj (A : AlgebraicSpaces B integerBase hZ) :
    (curvesOverSpaceBased B hZ A).obj = CurveFamilyOver B hZ A :=
  rfl

/-- **Stacks 0DMK, the identification `Mor_B(T, B-Curves) = Mor(T, Curves)`.** For a morphism
`f : T → A` of algebraic spaces, the category of morphisms over `(Sch/A)` from `T` to the stack
`A-Curves` is equivalent to the category of morphisms over the big fppf site from `T` to the stack
of curves, by forgetting the morphisms of the bases to `A`. -/
@[stacks 0DMK "the identification of Mor_B(T, B-Curves) with Mor(T, Curves)"]
def relativeCurvesMorphismsEquivalence {T A : AlgebraicSpaces B integerBase hZ} (f : T ⟶ A) :
    (schemesOverSpaceBasedOver B hZ f ⥤ᵇ curvesOverSpaceBased B hZ A) ≌
      (schemesOverSpaceBased B hZ T ⥤ᵇ (curvesFiberedCategory B hZ).val) :=
  CostructuredArrow.basedFunctorEquivalence (curvesFiberedCategory B hZ).val
    (schemeSpaceFunctor B integerBase hZ) A (schemesOverSpaceBasedOver B hZ f)

/-- The identification `Mor_B(T, B-Curves) = Mor(T, Curves)` forgets the morphisms of the bases
to `A`: it takes a functor `(Sch/T) → A-Curves` over `(Sch/A)` to its composite with the
forgetful functor to the category of families of curves. -/
theorem relativeCurvesMorphismsEquivalence_functor_obj {T A : AlgebraicSpaces B integerBase hZ}
    (f : T ⟶ A) (G : schemesOverSpaceBasedOver B hZ f ⥤ᵇ curvesOverSpaceBased B hZ A) :
    ((relativeCurvesMorphismsEquivalence B hZ f).functor.obj G).toFunctor =
      G.toFunctor ⋙ CostructuredArrow.proj (curveBaseSpace B hZ) A :=
  rfl

/-! ### The two models of `𝒮_T` -/

section Points

-- The local reducibility below lets the elaborator see that a scheme read as an algebraic space
-- is its functor of points, and through the spellings of the points category, as in
-- `StacksFrontier.AlgebraicGeometry.Quot.SpacesOverSpaceBaseChange`.
attribute [local implicit_reducible] schemeSpaceFunctor schemeSpace Stack.fibredCategory
  BasedCategory.ofFunctor Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd
  Grpd.forgetToCat

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A point `t ∈ T(U)` of an algebraic space `T` is the morphism `U ⟶ T` it names: the functor
over the site from the category `𝒮_T` of points of `T` to the category `(Sch/T)` of schemes with a
morphism to `T`. -/
def pointsToSchemesOverSpace (T : AlgebraicSpaces B integerBase hZ) :
    SpacesOverSpace.pointsCategory B integerBase hZ T ⥤ᵇ schemesOverSpaceBased B hZ T where
  obj a := CostructuredArrow.mk (SpacesOverSpace.pointMap a)
  map u := CostructuredArrow.homMk u.base
    (ObjectProperty.hom_ext _ (SpacesOverSpace.yoneda_map_comp_pointMap_hom u))
  map_id _ := CostructuredArrow.hom_ext _ _ rfl
  map_comp _ _ := CostructuredArrow.hom_ext _ _ rfl
  w := rfl

/-- A morphism `U ⟶ T` from a scheme is the point of `T` it names, by the Yoneda lemma: the
functor over the site from `(Sch/T)` to `𝒮_T`. -/
def schemesOverSpaceToPoints (T : AlgebraicSpaces B integerBase hZ) :
    schemesOverSpaceBased B hZ T ⥤ᵇ SpacesOverSpace.pointsCategory B integerBase hZ T where
  obj X := SpacesOverSpace.pt X.left (yonedaEquiv X.hom.hom)
  map {X Y} f := SpacesOverSpace.ptHom f.left (by
    calc yonedaEquiv X.hom.hom = yonedaEquiv (yoneda.map f.left ≫ Y.hom.hom) :=
          congrArg (fun k => yonedaEquiv k.hom) (CostructuredArrow.w f).symm
      _ = T.obj.map f.left.op (yonedaEquiv Y.hom.hom) := (yonedaEquiv_naturality _ _).symm)
  map_id _ := SpacesOverSpace.hom_ext_base _ _ rfl
  map_comp _ _ := SpacesOverSpace.hom_ext_base _ _ rfl
  w := rfl

/-- A morphism `U ⟶ T` from a scheme is the morphism named by the point of `T` it names. -/
def schemesOverSpaceRoundTripIso {T : AlgebraicSpaces B integerBase hZ}
    (X : CostructuredArrow (schemeSpaceFunctor B integerBase hZ) T) :
    CostructuredArrow.mk (SpacesOverSpace.pointMap
      (SpacesOverSpace.pt X.left (yonedaEquiv X.hom.hom))) ≅ X :=
  CostructuredArrow.isoMk (Iso.refl X.left) (ObjectProperty.hom_ext _ (by
    simp [schemeSpaceFunctor, schemeSpaceMap, SpacesOverSpace.pointMap]))

/-- **The two models of `𝒮_T` agree.** The category `𝒮_T` of points of an algebraic space `T`
(Stacks 0458) and the category `(Sch/T)` of schemes with a morphism to `T` are equivalent over
the site, by the Yoneda lemma. -/
def pointsSchemesOverSpaceEquivalence (T : AlgebraicSpaces B integerBase hZ) :
    BasedCategory.Equivalence (SpacesOverSpace.pointsCategory B integerBase hZ T)
      (schemesOverSpaceBased B hZ T) where
  functor := pointsToSchemesOverSpace T
  inverse := schemesOverSpaceToPoints T
  unitIso := BasedNatIso.mkNatIso (NatIso.ofComponents
    (fun (a : (SpacesOverSpace.pointsCategory B integerBase hZ T).obj) =>
      { hom := SpacesOverSpace.ptHom (𝟙 a.base) (by
          change yonedaEquiv (yonedaEquiv.symm a.fiber.as) = T.obj.map (𝟙 a.base).op a.fiber.as
          simp)
        inv := SpacesOverSpace.ptHom (𝟙 a.base) (by
          change a.fiber.as = T.obj.map (𝟙 a.base).op (yonedaEquiv (yonedaEquiv.symm a.fiber.as))
          simp)
        hom_inv_id := SpacesOverSpace.hom_ext_base _ _ (Category.comp_id _)
        inv_hom_id := SpacesOverSpace.hom_ext_base _ _ (Category.comp_id _) })
    (fun u => SpacesOverSpace.hom_ext_base _ _
      ((Category.comp_id _).trans (Category.id_comp _).symm)))
    (fun a => by
      refine IsHomLift.of_fac' _ (𝟙 a.base) _ rfl rfl ?_
      change 𝟙 a.base = eqToHom (rfl : a.base = a.base) ≫ 𝟙 a.base ≫ eqToHom rfl
      rw [eqToHom_refl, Category.id_comp, Category.id_comp])
  counitIso := BasedNatIso.mkNatIso (NatIso.ofComponents
    (fun X => schemesOverSpaceRoundTripIso X)
    (fun f => CostructuredArrow.hom_ext _ _
      ((Category.comp_id _).trans (Category.id_comp _).symm)))
    (fun X => IsHomLift.of_fac' _ (𝟙 _) _ rfl rfl
      ((Category.comp_id _).symm.trans (Category.id_comp _).symm))

end Points

/-! ### Stacks 0DMK -/

/-- **Stacks 0DMK, `Mor(T, Curves)` is the category of families of curves over `T`.** For an
algebraic space `T`, the category of morphisms over the big fppf site from `T` (read as the
category `(Sch/T)` of schemes with a morphism to `T`) to the stack of curves is equivalent to the
category of families of curves over `T`: morphisms of algebraic spaces `X ⟶ T` which are flat,
proper, of finite presentation and of relative dimension at most one, with the isomorphisms over
`T` as morphisms. A family `X ⟶ T` corresponds to the morphism sending `U ⟶ T` to the family of
curves `U ×_T X ⟶ U`. -/
@[stacks 0DMK "Mor(T, Curves) is the category of families of curves over the algebraic space T"]
noncomputable def curvesMorphismsEquivalence (T : AlgebraicSpaces B integerBase hZ) :
    (schemesOverSpaceBased B hZ T ⥤ᵇ (curvesFiberedCategory B hZ).val) ≌
      CurveFamilyOnSpace B integerBase hZ T :=
  haveI := curveFamilyBaseChange_isEquivalence B integerBase hZ T
  ((pointsSchemesOverSpaceEquivalence T).precompEquivalence _).trans
    (((curveFamilyEquivalence B hZ).symm.postcompEquivalence _).trans
      (SpacesOverSpace.baseChangeFunctor (P := curveFamilyProperty B integerBase hZ)
        (T := T)).asEquivalence.symm)

/-- **Stacks 0DMK.** For a morphism `f : T ⟶ A` of algebraic spaces, the category
`Mor_A(T, A-Curves)` of morphisms over `(Sch/A)` from `T` to the stack `A-Curves` is equivalent to
`Mor(T, Curves)` (`AlgebraicGeometry.relativeCurvesMorphismsEquivalence`), and both are the
category of families of curves over `T`. -/
@[stacks 0DMK "Mor_B(T, B-Curves) = Mor(T, Curves) is the category of families of curves over T"]
noncomputable def relativeCurvesMorphismsCurveFamilyEquivalence
    {T A : AlgebraicSpaces B integerBase hZ} (f : T ⟶ A) :
    (schemesOverSpaceBasedOver B hZ f ⥤ᵇ curvesOverSpaceBased B hZ A) ≌
      CurveFamilyOnSpace B integerBase hZ T :=
  (relativeCurvesMorphismsEquivalence B hZ f).trans (curvesMorphismsEquivalence B hZ T)

end AlgebraicGeometry

end
