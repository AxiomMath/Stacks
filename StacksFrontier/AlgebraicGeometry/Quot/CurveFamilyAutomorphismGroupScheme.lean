module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyInfinitesimalAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SliceFiniteProducts
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpacesOverFields.SeparatedFiniteTypeScheme

/-!
# The automorphism group scheme of a curve over a field

Let `X` be a proper scheme of dimension at most one over a field `k`. When the automorphism
group algebraic space `Aut(X)` of the point `Spec k → Curves` classifying `X` (Stacks 04YP) is a
scheme, as Stacks 0B8F makes it once it is separated and locally of finite type over `k`
(Stacks 0DSQ), its representing scheme is a group scheme over `k` with the group law of
`Aut(X)`, and it represents the automorphism functor of `X` with the identity automorphism as
unit. This is the group scheme `G = Aut(X)` of the proof of Stacks 0E6G, and it gives Stacks 0E6G:
the conditions of Stacks 0DSW (3) are equivalent to `Der_k(𝒪_X, 𝒪_X) = 0`.

## Main definitions

* `AlgebraicGeometry.Space.representingGrpObj`: the representing object of a representable group
  object of presheaves on the big fppf site of `S` is a group object of that site.
* `AlgebraicGeometry.Space.representingGrp`: the corresponding group scheme over `S`.

## References

* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
* [Stacks Project, Tag 0B8F](https://stacks.math.columbia.edu/tag/0B8F)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- **A representable group object of presheaves is represented by a group object of the site.**
The Yoneda embedding of the big fppf site of `S` is fully faithful and preserves finite products,
so the group structure of a representable group object `I` of presheaves pulls back to the
representing object. -/
@[instance_reducible]
def representingGrpObj (I : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [GrpObj I] [I.IsRepresentable] :
    GrpObj I.reprX :=
  letI : (yoneda : BigFppfOver B S hS ⥤ _).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts yoneda
  letI : GrpObj (yoneda.obj I.reprX) := GrpObj.ofIso I.reprW.symm
  Yoneda.fullyFaithful.grpObj I.reprX

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- The unit of `AlgebraicGeometry.Space.representingGrpObj` represents the unit of `I`. -/
theorem yoneda_map_representingGrpObj_one (I : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [GrpObj I]
    [I.IsRepresentable] :
    yoneda.map (letI := representingGrpObj B S hS I; η[I.reprX]) ≫ I.reprW.hom =
      toUnit _ ≫ η[I] := by
  let : (yoneda : BigFppfOver B S hS ⥤ _).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts yoneda
  let : GrpObj (yoneda.obj I.reprX) := GrpObj.ofIso I.reprW.symm
  change yoneda.map (Yoneda.fullyFaithful.preimage
    (Functor.OplaxMonoidal.η yoneda ≫ (η[I] ≫ I.reprW.symm.hom))) ≫ I.reprW.hom = _
  rw [Functor.FullyFaithful.map_preimage, Category.assoc, Category.assoc, Iso.symm_hom,
    Iso.inv_hom_id, Category.comp_id]
  congr 1

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- **The group scheme representing a representable group object of presheaves.** The representing
object of `I`, a group object of the big fppf site of `S` by
`AlgebraicGeometry.Space.representingGrpObj`, read as a scheme over `S`: the comparison functor to
schemes over `S` preserves finite products. -/
def representingGrp (I : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [GrpObj I] [I.IsRepresentable] :
    Grp (Over S) :=
  haveI := preservesFiniteProducts_overPost_bigFppfInclusion B S hS
  letI := representingGrpObj B S hS I
  (Over.post B.inclusion).mapGrp.obj (Grp.mk I.reprX)

/-- The scheme underlying `AlgebraicGeometry.Space.representingGrp` is the representing object
of `I`, read as a scheme over `S`. -/
theorem representingGrp_X (I : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [GrpObj I]
    [I.IsRepresentable] :
    (representingGrp B S hS I).X = (Over.post B.inclusion).obj I.reprX :=
  rfl

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- **A point of the representing scheme lying over the unit is the unit of `I`.** A morphism
`t : V ⟶ I.reprX` of the site whose underlying morphism of schemes over `S` factors through the
unit of the group scheme `AlgebraicGeometry.Space.representingGrp` corresponds, under the
representation of `I`, to the unit section of `I` over `V`. -/
theorem yoneda_map_comp_reprW_hom_eq_one (I : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [GrpObj I]
    [I.IsRepresentable] {V : BigFppfOver B S hS} (t : V ⟶ I.reprX)
    (ht : (Over.post B.inclusion).map t = toUnit _ ≫ η[(representingGrp B S hS I).X]) :
    yoneda.map t ≫ I.reprW.hom = toUnit _ ≫ η[I] := by
  have := preservesFiniteProducts_overPost_bigFppfInclusion B S hS
  let := representingGrpObj B S hS I
  have hε : (Over.post B.inclusion).map (toUnit V) =
      toUnit _ ≫ Functor.LaxMonoidal.ε (Over.post (X := B.obj hS) B.inclusion) := by
    exact (Iso.comp_inv_eq (Functor.Monoidal.εIso (Over.post (X := B.obj hS) B.inclusion))).1
      (toUnit_unique _ _)
  have h1 : t = toUnit V ≫ η[I.reprX] := by
    refine (fullyFaithful_overPost_bigFppfInclusion B S hS).map_injective (ht.trans ?_)
    change toUnit _ ≫ (Functor.LaxMonoidal.ε (Over.post (X := B.obj hS) B.inclusion) ≫
      (Over.post B.inclusion).map η[I.reprX]) = _
    rw [Functor.map_comp, hε, Category.assoc]
  rw [h1, Functor.map_comp, Category.assoc, yoneda_map_representingGrpObj_one, ← Category.assoc]
  congr 1

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.curvesSmall

open Deformation Deformation.Examples

attribute [local implicit_reducible] schemeSpace ShrinkHoms.fromShrinkHoms ShrinkHoms.inverse
  curvesSmall curvesSmallBased

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
variable {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
  (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)

/-- The object of the small model of the stack of curves over `Spec k` classifying a proper scheme
`X` of dimension at most one over `k`: the family of curves `X ⟶ Spec k`. -/
abbrev curveFiber : (curvesSmall B hZ).val.p.Fiber (integerSiteObject B hZ hk) :=
  ⟨ShrinkHoms.toShrinkHoms (curveFamilyOfScheme X B hZ hk hdim), rfl⟩

/-- The presheaf `Isom(X, X)` on the big fppf site of `Spec k`, underlying the automorphism group
algebraic space `Aut(X)` of the point of `Curves` classifying `X` (Stacks 04YP). -/
abbrev autIsomSpace : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u :=
  Stack.isomSpace B integerBase hZ (curvesSmall B hZ) (integerSiteObject B hZ hk)
    (curveFiber X hk hdim) (curveFiber X hk hdim)

/-- The group law of `Aut(X)`: composition of automorphisms (Stacks 04YP). -/
@[instance_reducible]
def autIsomSpaceGrpObj : GrpObj (autIsomSpace (hZ := hZ) X hk hdim) :=
  letI : (curvesSmall B hZ).val.p.IsPreFibered :=
    (curvesSmall B hZ).isFiberedInGroupoids.isFibered.toIsPreFibered
  Stack.isomSpaceGrpObj B integerBase hZ (curvesSmall B hZ) (integerSiteObject B hZ hk)
    (curveFiber X hk hdim)

/-- **The automorphism group scheme of `X`.** When `Aut(X)` is a scheme, its representing scheme
over `k`, with the group law of `Aut(X)`. -/
def autGroupScheme [(autIsomSpace (hZ := hZ) X hk hdim).IsRepresentable] :
    Grp (Over (Spec (.of k))) :=
  letI := autIsomSpaceGrpObj (hZ := hZ) X hk hdim
  Space.representingGrp B (Spec (.of k)) hk (autIsomSpace (hZ := hZ) X hk hdim)

section Representable

variable [(autIsomSpace (hZ := hZ) X hk hdim).IsRepresentable]

/-- The scheme underlying the automorphism group scheme is the representing object of `Aut(X)`,
read as a scheme over `k`. -/
theorem autGroupScheme_X :
    (autGroupScheme (hZ := hZ) X hk hdim).X =
      (Over.post B.inclusion).obj (autIsomSpace (hZ := hZ) X hk hdim).reprX :=
  rfl

/-- The automorphism group scheme belongs to the site. -/
theorem contains_autGroupScheme_left : B.Contains (autGroupScheme (hZ := hZ) X hk hdim).X.left :=
  (autIsomSpace (hZ := hZ) X hk hdim).reprX.left.2

/-- **`Aut(X)` is represented by its group scheme, with the identity automorphism as unit.** When
`Aut(X)` is a scheme, the automorphism functor of the family `X ⟶ Spec k` (Stacks 0DSW) on the big
fppf site of `Spec(ℤ)` is represented by the automorphism group scheme `G` of `X`, by an
isomorphism lying over `Spec k` which sends the unit of `G` to the identity automorphism of `X`. -/
theorem exists_yonedaIso_autFunctor :
    ∃ ε : yoneda.obj (integerSiteObject B hZ (contains_autGroupScheme_left (hZ := hZ) X hk hdim)) ≅
        (CurveFamily.autFunctor (curveFamilyOfScheme X B hZ hk hdim)).toFunctor,
      ε.hom ≫ CurveFamily.autFunctorProjection (curveFamilyOfScheme X B hZ hk hdim) =
          yoneda.map (integerSiteMap B hZ (contains_autGroupScheme_left (hZ := hZ) X hk hdim) hk
            (autGroupScheme (hZ := hZ) X hk hdim).X.hom) ∧
        Space.relativeHomSections B integerBase hZ _ _ _ _ _ _ _ _ (integerSiteObject B hZ hk)
            (ε.hom.app (op (integerSiteObject B hZ hk))
              (integerSiteMap B hZ hk (contains_autGroupScheme_left (hZ := hZ) X hk hdim)
                (η[(autGroupScheme (hZ := hZ) X hk hdim).X]).left)).1 =
          Space.RelativeMorphism.identity _ (𝟙 _) := by
  let := autIsomSpaceGrpObj (hZ := hZ) X hk hdim
  let I := autIsomSpace (hZ := hZ) X hk hdim
  let U := integerSiteObject B hZ hk
  let y := curveFiber (hZ := hZ) X hk hdim
  let G := (autGroupScheme (hZ := hZ) X hk hdim).X
  have hG : B.Contains G.left := I.reprX.left.2
  obtain ⟨e, he₁, he₂⟩ := exists_isomSpaceRelocalizeIso_autFunctor y
  let c : integerSiteObject B hZ hG ≅ (Over.map U.hom).obj I.reprX :=
    Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  let ε : yoneda.obj (integerSiteObject B hZ hG) ≅
      (CurveFamily.autFunctor (curveFamilyOfScheme X B hZ hk hdim)).toFunctor :=
    yoneda.mapIso c ≪≫ (relocalizedYonedaIso B U.left (B.obj hZ) U.hom I.reprX).symm ≪≫
      (OverShriek.relocalizePresheafFunctor U.hom).mapIso I.reprW ≪≫ e
  have h1 : (OverShriek.relocalizePresheafFunctor U.hom).map I.reprW.hom ≫
      OverShriek.relocalizeToYoneda U.hom I =
        OverShriek.relocalizeToYoneda U.hom (yoneda.obj I.reprX) := by
    ext W x
    exact Over.OverMorphism.ext rfl
  refine ⟨ε, ?_, ?_⟩
  · ext W α
    refine (congrArg (fun f => f.app W (((OverShriek.relocalizePresheafFunctor U.hom).map
      I.reprW.hom).app W ((relocalizedYonedaIso B U.left (B.obj hZ) U.hom I.reprX).inv.app W
        (α ≫ c.hom)))) he₁).trans ?_
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    let a : W.unop ⟶ integerSiteObject B hZ hG := α
    change (((a.left ≫ 𝟙 _) ≫ I.reprX.hom) ≫ 𝟙 _).hom =
      (a.left ≫ (integerSiteMap B hZ hG hk G.hom).left).hom
    rw [Category.comp_id, Category.comp_id]
    rfl
  · let α : integerSiteObject B hZ hk ⟶ integerSiteObject B hZ hG :=
      integerSiteMap B hZ hk hG (η[G]).left
    let a : integerSiteObject B hZ hk ⟶ (Over.map U.hom).obj I.reprX := α ≫ c.hom
    let z := ((OverShriek.relocalizePresheafFunctor U.hom).map I.reprW.hom).app
      (op (integerSiteObject B hZ hk))
      ((relocalizedYonedaIso B U.left (B.obj hZ) U.hom I.reprX).inv.app
        (op (integerSiteObject B hZ hk)) a)
    let V : BigFppfOver B (Spec (.of k)) hk := Over.mk (a.left ≫ I.reprX.hom)
    let t : V ⟶ I.reprX := Over.homMk a.left rfl
    have hV : (a.left ≫ I.reprX.hom).hom = 𝟙 _ := by
      change ((η[G]).left ≫ 𝟙 _) ≫ G.hom = 𝟙 _
      rw [Category.comp_id]
      exact Over.w (η[G])
    have ht : (Over.post B.inclusion).map t =
        toUnit _ ≫ η[(Space.representingGrp B (Spec (.of k)) hk I).X] := by
      apply Over.OverMorphism.ext
      have hu : (toUnit ((Over.post B.inclusion).obj V)).left = 𝟙 _ :=
        ((Category.comp_id _).symm.trans (Over.w (toUnit ((Over.post B.inclusion).obj V)))).trans hV
      change (η[G]).left ≫ 𝟙 _ = (toUnit ((Over.post B.inclusion).obj V)).left ≫ (η[G]).left
      rw [hu, Category.comp_id]
      exact (Category.id_comp _).symm
    have key := Space.yoneda_map_comp_reprW_hom_eq_one B (Spec (.of k)) hk I t ht
    have hz : z.1.2.1 = 𝟙 _ :=
      (congrArg (fun s => (I.reprW.hom.app (op V) s).1) (Category.id_comp t).symm).trans
        (congrArg (fun f => (f.app (op V) (𝟙 V)).1) key)
    refine (he₂ z hz).trans ?_
    have h2 : (Over.homMk z.1.1 (OverShriek.relocalizeFactors U.hom _ z) :
        integerSiteObject B hZ hk ⟶ U) ≫ eqToHom y.2.symm = 𝟙 _ := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change (a.left ≫ I.reprX.hom ≫ 𝟙 _).hom = 𝟙 _
      rw [Category.comp_id]
      exact hV
    exact congrArg (Space.RelativeMorphism.identity _)
      ((congrArg yoneda.map h2).trans (yoneda.map_id _))

/-- **Stacks 0E6G, at the automorphism group scheme.** Let `X` be a proper scheme of dimension at
most one over a field `k` whose automorphism group algebraic space `Aut(X)` is a scheme `G`,
locally of finite type over `k`. Then `G` is unramified over `k` if and only if
`Der_k(𝒪_X, 𝒪_X) = 0`: `G` with the group law of `Aut(X)` represents the automorphism functor of
`X` with unit the identity automorphism
(`AlgebraicGeometry.curvesSmall.exists_yonedaIso_autFunctor`), and
`AlgebraicGeometry.CurveFamily.unramified_iff_subsingleton_derivations_of_represents` applies. -/
theorem unramified_autGroupScheme_iff_subsingleton_derivations
    [LocallyOfFiniteType (autGroupScheme (hZ := hZ) X hk hdim).X.hom] :
    Unramified (autGroupScheme (hZ := hZ) X hk hdim).X.hom ↔
      Subsingleton (schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X.left) X.hom) := by
  obtain ⟨ε, hε, hη⟩ := exists_yonedaIso_autFunctor (hZ := hZ) X hk hdim
  exact CurveFamily.unramified_iff_subsingleton_derivations_of_represents B hZ hk X hdim _ _ ε hε hη

/-- **`Aut(X) ⟶ Spec k` is unramified exactly when its group scheme is.** The projection of the
automorphism functor of `X` to `Spec k` (Stacks 0DSW (2)) is unramified exactly when the
automorphism group scheme of `X` is unramified over `k`, the former being represented by the
latter (`AlgebraicGeometry.curvesSmall.exists_yonedaIso_autFunctor`). -/
theorem isUnramified_autFunctorProjection_iff_unramified_autGroupScheme :
    Space.IsUnramified B integerBase hZ
        (CurveFamily.autFunctorProjection (curveFamilyOfScheme X B hZ hk hdim)) ↔
      Unramified (autGroupScheme (hZ := hZ) X hk hdim).X.hom := by
  obtain ⟨ε, hε, -⟩ := exists_yonedaIso_autFunctor (hZ := hZ) X hk hdim
  have := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B integerBase hZ
    (@AlgebraicGeometry.Unramified : MorphismProperty Scheme.{u})
  exact (MorphismProperty.arrow_mk_iso_iff
    (fun ⦃F G : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) =>
      Space.IsUnramified B integerBase hZ f)
    (Arrow.isoMk ε (Iso.refl _) (hε.trans (Category.comp_id _).symm))).symm.trans
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      unramified_isEtaleLocalOnSourceAndTarget _)

/-- **The automorphism group scheme is locally of finite type when `Aut(X)` is.** -/
theorem locallyOfFiniteType_autGroupScheme
    (hlft : Space.IsLocallyOfFiniteType B (Spec (.of k)) hk
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from
        (autIsomSpace (hZ := hZ) X hk hdim))) :
    LocallyOfFiniteType (autGroupScheme (hZ := hZ) X hk hdim).X.hom := by
  let I := autIsomSpace (hZ := hZ) X hk hdim
  let g : I.reprX ⟶ Over.mk (𝟙 (B.obj hk)) := Over.homMk I.reprX.hom (Category.comp_id _)
  have := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B (Spec (.of k)) hk
    (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
  have h1 : Space.IsLocallyOfFiniteType B (Spec (.of k)) hk
      (I.reprW.hom ≫ (Space.isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from I) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (fun ⦃F G : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B (Spec (.of k)) hk f) _ _).2 hlft
  have h2 : yoneda.map g =
      I.reprW.hom ≫ (Space.isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from I :=
    (Space.isTerminal_yoneda_obj_base B (Spec (.of k)) hk).hom_ext _ _
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B (Spec (.of k)) hk
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget g).1 (h2 ▸ h1)

end Representable

section Stack

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The point `Spec k → Curves` classifying `X`**, as a field-valued point of the algebraic stack
of curves: the family `X ⟶ Spec k` over the object `Spec k` of the site. -/
def curveFieldPoint :
    Stack.FieldValuedPoint B integerBase hZ (curvesAlgebraicStack B hZ h).val.val :=
  { carrier := k
    base := integerSiteObject B hZ hk
    isSpec := Iso.refl _
    obj := ShrinkHoms.toShrinkHoms (curveFamilyOfScheme X B hZ hk hdim)
    «over» := rfl }

/-- **Stacks 0E6G, given the algebraicity of `Curves` and the finiteness of `Aut(X)`.** Let `X`
be a proper scheme of dimension at most one over a field `k`, and `x : Spec k → Curves` the point
classifying it. Suppose the stack of curves is algebraic (`h`, Stacks 0D5A) and that `Aut(X)` is
separated and locally of finite type over `k` (`hsep`, `hlft`, which Stacks 0DSQ gives). Then the
following are equivalent: `x` factors through `Curves^DM`; `Aut(X)` is geometrically reduced over
`k` of dimension `0`; `Aut(X) → Spec k` is unramified; `Der_k(𝒪_X, 𝒪_X) = 0`. By Stacks 0B8F
`Aut(X)` is then a group scheme over `k`
(`Space.GroupOverField.isRepresentable_of_isSeparatedOver_of_isLocallyOfFiniteType`), and the
last equivalence is `unramified_autGroupScheme_iff_subsingleton_derivations`.

Not registered: it takes `h` (Stacks 0D5A) and `hsep`, `hlft` (Stacks 0DSQ) as hypotheses. -/
theorem tfae_dmLocus_curveFieldPoint_subsingleton_derivations
    (hsep : Space.IsSeparatedOver B (Spec (.of k)) hk
      (Stack.automorphismGroupSpace B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (curvesAlgebraicStack B hZ h).property (curveFieldPoint X hk hdim h).base
        ⟨(curveFieldPoint X hk hdim h).obj, (curveFieldPoint X hk hdim h).over⟩).obj.X.left)
    (hlft : Space.IsLocallyOfFiniteType B (Spec (.of k)) hk
      (Stack.automorphismGroupSpace B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (curvesAlgebraicStack B hZ h).property (curveFieldPoint X hk hdim h).base
        ⟨(curveFieldPoint X hk hdim h).obj, (curveFieldPoint X hk hdim h).over⟩).obj.X.hom) :
    List.TFAE
      [Stack.dmLocus B integerBase hZ B.contains_terminal (curvesAlgebraicStack B hZ h)
          (curveFieldPoint X hk hdim h).obj,
        Space.IsGeometricallyReduced k B hk
            (Stack.automorphismGroupSpaceOverField B integerBase hZ _ (curveFieldPoint X hk hdim h))
            (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _
              (curveFieldPoint X hk hdim h)) ∧
          Space.dimension B (Spec (.of k)) hk
            (Stack.automorphismGroupSpaceOverField B integerBase hZ _ (curveFieldPoint X hk hdim h))
            (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _
              (curveFieldPoint X hk hdim h)) = 0,
        Stack.IsUnramifiedAutomorphismGroupSpace B integerBase hZ (curvesAlgebraicStack B hZ h)
          (curveFieldPoint X hk hdim h),
        Subsingleton (schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X.left) X.hom)] := by
  have hlft' : Space.IsLocallyOfFiniteType B (Spec (.of k)) hk
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from
        (autIsomSpace (hZ := hZ) X hk hdim)) :=
    Space.holdsOnEveryEtaleChart_of_isTerminal B (Spec (.of k)) hk
      (Stack.isTerminal_siteTerminalSpace B integerBase hZ (integerSiteObject B hZ hk))
      (Space.isTerminal_yoneda_obj_base B (Spec (.of k)) hk) _ _ hlft
  have : (autIsomSpace (hZ := hZ) X hk hdim).IsRepresentable :=
    Space.GroupOverField.isRepresentable_of_isSeparatedOver_of_isLocallyOfFiniteType (Iso.refl _) _
      hsep hlft'
  have := locallyOfFiniteType_autGroupScheme (hZ := hZ) X hk hdim hlft'
  have T := tfae_dmLocus_fieldValuedPoint h (curveFieldPoint X hk hdim h) hlft
  tfae_have 1 ↔ 2 := T.out 1 2
  tfae_have 1 ↔ 3 := T.out 1 3
  tfae_have 1 ↔ 4 :=
    (dmLocus_toShrinkHoms_iff h (curveFamilyOfScheme X B hZ hk hdim)).trans
      ((isUnramified_autFunctorProjection_iff_unramified_autGroupScheme (hZ := hZ) X hk hdim).trans
        (unramified_autGroupScheme_iff_subsingleton_derivations (hZ := hZ) X hk hdim))
  tfae_finish

end Stack

end AlgebraicGeometry.curvesSmall
