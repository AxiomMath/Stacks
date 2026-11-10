module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# The topology on the points of an algebraic stack

There is a unique way to topologize the point sets `|𝒳|` of all the algebraic stacks over a
scheme `S` so that

1. every 1-morphism of algebraic stacks is continuous on points;
2. a 1-morphism from an algebraic space all of whose represented base changes are flat and
   locally of finite presentation is continuous and open on points.

A chart of `𝒳` by an algebraic space `F` over `S` is a 1-morphism from the category of elements
of `F` to `𝒳`. It induces a map `|F| → |𝒳|` on points, sending the class of a field-valued point
of `F` to the class of its image. The topology on `|𝒳|` is the supremum, over all charts by
algebraic spaces, of the topologies coinduced from the point topologies of the algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Stack.spaceFieldValuedPoint` and
  `AlgebraicGeometry.Stack.spacePointMap`: the canonical map from the points of an algebraic
  space to the points of a stack along a 1-morphism.
* `AlgebraicGeometry.Stack.SpaceChart`: a chart of a stack by an algebraic space.
* `AlgebraicGeometry.Stack.pointTopology`: the topology on `|𝒳|`.
* `AlgebraicGeometry.Stack.PointTopologyFamily`: a family of topologies on the points of the
  algebraic stacks over `S` satisfying the two conditions above, and
  `AlgebraicGeometry.Stack.pointTopologyFamily` the family built from
  `AlgebraicGeometry.Stack.pointTopology`.
* `AlgebraicGeometry.Stack.chosenPointTopologyFamily`: the family obtained from the existence
  statement by `Classical.choose`.

## Main results

* `AlgebraicGeometry.Stack.spacePointMap_class`: the canonical map sends the class of a
  field-valued point of an algebraic space to the class of its image.
* `AlgebraicGeometry.Stack.spacePointMap_id_bijective`: the points of a presheaf are the points
  of its category of elements.
* `AlgebraicGeometry.Stack.isOpen_pointTopology_iff`: the open sets of the topology are those
  whose preimage along every chart by an algebraic space is open.
* `AlgebraicGeometry.Stack.continuous_pointsMap`,
  `AlgebraicGeometry.Stack.continuous_spacePointMap` and
  `AlgebraicGeometry.Stack.isOpenMap_spacePointMap`: the two conditions for the constructed
  topology.
* `AlgebraicGeometry.Stack.isOpen_pointTopology_of_family`: every set open for the topology a
  family satisfying the two conditions assigns is open for the constructed topology.
* `AlgebraicGeometry.Stack.PointTopologyFamily.topology_eq`: every family satisfying the two
  conditions assigns to each algebraic stack the constructed topology
  `AlgebraicGeometry.Stack.pointTopology`.
* `AlgebraicGeometry.Stack.existsUnique_pointTopologyFamily`: existence and uniqueness of such a
  family.
* `AlgebraicGeometry.Stack.chosenPointTopologyFamily_topology_eq`: the family produced by
  `Classical.choose` assigns the constructed topology.

## References

* [Stacks Project, Tag 04XE](https://stacks.math.columbia.edu/tag/04XE)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
-/

@[expose] public section

open CategoryTheory
open Pseudofunctor.CoGrothendieck

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The canonical map from the points of an algebraic space -/

/-- A field-valued point of a presheaf on the big fppf site of `S`, read as a field-valued
point of the category of elements of that presheaf. -/
noncomputable def spaceFieldValuedPoint (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : Space.FieldValuedPoint B S hS F) :
    FieldValuedPoint B S hS (fibredCategory B S hS F).val where
  carrier := p.carrier
  field := p.field
  base := p.siteObject
  isSpec := Iso.refl _
  obj := ⟨p.siteObject, Discrete.mk p.value⟩
  «over» := rfl

/-- Two field-valued points of a presheaf with a common refinement have images with a common
refinement in the category of elements. -/
theorem hasCommonExtension_spaceFieldValuedPoint
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {p q : Space.FieldValuedPoint B S hS F}
    (h : Space.FieldValuedPoint.HasCommonExtension B S hS F p q) :
    FieldValuedPoint.HasCommonExtension
      (spaceFieldValuedPoint B S hS F p) (spaceFieldValuedPoint B S hS F q) := by
  obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  let H := (F ⋙ typeToGrpd) ⋙ Grpd.forgetToCat
  have arrow₁ :
      (⟨r.siteObject, Discrete.mk r.value⟩ : ∫ᶜ H.toPseudofunctor') ⟶
        ⟨p.siteObject, Discrete.mk p.value⟩ :=
    (PresheafOfCategories.homEquiv H _ _).symm
      ⟨a, eqToHom (congrArg Discrete.mk ha.symm)⟩
  have arrow₂ :
      (⟨r.siteObject, Discrete.mk r.value⟩ : ∫ᶜ H.toPseudofunctor') ⟶
        ⟨q.siteObject, Discrete.mk q.value⟩ :=
    (PresheafOfCategories.homEquiv H _ _).symm
      ⟨b, eqToHom (congrArg Discrete.mk hb.symm)⟩
  exact ⟨spaceFieldValuedPoint B S hS F r, ⟨arrow₁⟩, ⟨arrow₂⟩⟩

/-- The point of a stack obtained by composing a point of an algebraic space with a
1-morphism from the space to the stack. -/
noncomputable def spacePointMap (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val) :
    Space.points B S hS F → points B S hS 𝒳.val 𝒳.property :=
  fun p => pointClass B S hS 𝒳.val 𝒳.property
    (fieldValuedPointMap B S hS (fibredCategory B S hS F).val f
      (spaceFieldValuedPoint B S hS F (Quot.out p)))

/-- The chosen quotient representative in `AlgebraicGeometry.Stack.spacePointMap` has the same
image as any field-valued representative of the point. -/
@[stacks 04XL "canonical map on points"]
theorem spacePointMap_class (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val)
    (p : Space.FieldValuedPoint B S hS F) :
    spacePointMap B S hS F 𝒳 f (p.class B S hS F) =
      pointClass B S hS 𝒳.val 𝒳.property
        (fieldValuedPointMap B S hS (fibredCategory B S hS F).val f
          (spaceFieldValuedPoint B S hS F p)) := by
  apply (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val 𝒳.property _ _).2
  apply hasCommonExtension_fieldValuedPointMap
  apply hasCommonExtension_spaceFieldValuedPoint
  exact (Space.FieldValuedPoint.class_eq_class_iff B S hS F _ _).mp
    (Quot.out_eq (p.class B S hS F))

/-- The comparison of points commutes with a based functor `a` between categories of elements:
transporting a point of `F` along the morphism of presheaves underlying `a` and then comparing it
with the points of the stack gives the same class as comparing first and transporting after. -/
public theorem spacePointMap_presheafMapOfBasedFunctor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : (fibredCategory B S hS F).val ⥤ᵇ (fibredCategory B S hS G).val)
    (p : Space.points B S hS F) :
    spacePointMap B S hS G (fibredCategory B S hS G)
      (BasedFunctor.id (fibredCategory B S hS G).val)
        (Space.pointsMap B S hS F (presheafMapOfBasedFunctor a) p) =
    pointsMap B S hS _ _ _ a
      (spacePointMap B S hS F (fibredCategory B S hS F)
        (BasedFunctor.id (fibredCategory B S hS F).val) p) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep p
  rw [Space.pointsMap_class, spacePointMap_class, spacePointMap_class, pointsMap_class]
  apply (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2
  let q := spaceFieldValuedPoint B S hS G
    (Space.FieldValuedPoint.map B S hS F (presheafMapOfBasedFunctor a) p)
  refine ⟨q, ⟨𝟙 q.obj⟩, ⟨?_⟩⟩
  exact ⟨eqToHom (a.w_obj (spaceFieldValuedPoint B S hS F p).obj).symm, Discrete.eqToHom rfl⟩

/-! ### Points of equivalent categories over the site -/

/-- The identity 1-morphism is the identity on points. -/
theorem pointsMap_basedFunctorId {𝒜 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (h𝒜 : 𝒜.p.IsFiberedInGroupoids) (x : points B S hS 𝒜 h𝒜) :
    pointsMap B S hS 𝒜 h𝒜 h𝒜 (BasedFunctor.id 𝒜) x = x := by
  induction x using Quotient.inductionOn with
  | h p => rfl

/-- The bijection on points induced by an equivalence of categories over the big fppf site of
`S`. -/
noncomputable def pointsEquivOfBasedEquivalence
    {𝒜 𝒞 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (h𝒜 : 𝒜.p.IsFiberedInGroupoids) (h𝒞 : 𝒞.p.IsFiberedInGroupoids)
    (e : BasedCategory.Equivalence 𝒜 𝒞) :
    points B S hS 𝒜 h𝒜 ≃ points B S hS 𝒞 h𝒞 where
  toFun := pointsMap B S hS 𝒜 h𝒜 h𝒞 e.functor
  invFun := pointsMap B S hS 𝒞 h𝒞 h𝒜 e.inverse
  left_inv x := by
    rw [pointsMap_comp, pointsMap_eq_of_basedNatTrans B S hS 𝒜 h𝒜 h𝒜 e.unitIso.hom]
    exact pointsMap_basedFunctorId B S hS h𝒜 x
  right_inv x := by
    rw [pointsMap_comp, pointsMap_eq_of_basedNatTrans B S hS 𝒞 h𝒞 h𝒞 e.counitIso.hom]
    exact pointsMap_basedFunctorId B S hS h𝒞 x

/-! ### The canonical map is compatible with composition -/

/-- The canonical map from the points of an algebraic space is compatible with postcomposition
by a 1-morphism of the target. -/
theorem spacePointMap_comp (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val) (g : 𝒳.val ⥤ᵇ 𝒴.val) :
    spacePointMap B S hS F 𝒴 (f.comp g) =
      pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property g ∘ spacePointMap B S hS F 𝒳 f := by
  funext q
  refine Quot.inductionOn q ?_
  intro p
  change spacePointMap B S hS F 𝒴 (f.comp g) (p.class B S hS F) =
    pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property g
      (spacePointMap B S hS F 𝒳 f (p.class B S hS F))
  rw [spacePointMap_class B S hS F 𝒴 (f.comp g) p, spacePointMap_class B S hS F 𝒳 f p,
    pointsMap_class]
  rfl

/-! ### The canonical map of the tautological chart is bijective -/

/-- A field-valued point of the category of elements of a presheaf, read as a field-valued
point of the presheaf: its base is replaced by the canonical field spectrum of the site and
its section is restricted along the resulting comparison morphism. -/
private noncomputable def spacePointRepresentative
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : FieldValuedPoint B S hS (fibredCategory B S hS F).val) :
    Space.FieldValuedPoint B S hS F := by
  have hK : B.Contains (Spec (.of p.carrier)) := by
    have h := p.base.left.2
    change ((BigFppfOver.toScheme B S hS).obj p.base).size < B.cutoff at h
    rwa [Scheme.size_congr p.isSpec] at h
  let toBase := p.isSpec.inv ≫ B.inclusion.map p.base.hom
  let V : BigFppfOver B S hS := Over.mk (⟨toBase⟩ : B.obj hK ⟶ B.obj hS)
  let a : V ⟶ p.base := Over.homMk (ObjectProperty.homMk p.isSpec.inv) rfl
  let b : V ⟶ p.obj.base := a ≫ eqToHom p.over.symm
  exact { carrier := p.carrier
          field := p.field
          contained := hK
          toBase := toBase
          value := F.map b.op p.obj.fiber.as }

/-- The field-valued point of the category of elements attached to
`AlgebraicGeometry.Stack.spacePointRepresentative` dominates the original one. -/
private theorem spacePointRepresentative_arrow (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : FieldValuedPoint B S hS (fibredCategory B S hS F).val) :
    Nonempty ((spaceFieldValuedPoint B S hS F
      (spacePointRepresentative B S hS F p)).obj ⟶ p.obj) := by
  unfold spacePointRepresentative
  dsimp only
  exact ⟨(PresheafOfCategories.homEquiv _ _ _).symm ⟨_, 𝟙 _⟩⟩

/-- An arrow between the images of two field-valued points of a presheaf in its category of
elements is a domination of the two points. -/
private theorem spacePoint_dominates_of_arrow (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p q : Space.FieldValuedPoint B S hS F)
    (a : (spaceFieldValuedPoint B S hS F p).obj ⟶ (spaceFieldValuedPoint B S hS F q).obj) :
    Space.FieldValuedPoint.Dominates B S hS F p q :=
  ⟨a.base, (Discrete.eq_of_hom a.fiber).symm⟩

/-- The canonical map from the points of a presheaf to the points of its category of elements,
along the tautological 1-morphism, is bijective. -/
theorem spacePointMap_id_bijective (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Function.Bijective (spacePointMap B S hS F (fibredCategory B S hS F)
      (BasedFunctor.id (fibredCategory B S hS F).val)) := by
  refine ⟨fun x y h => ?_, fun x => ?_⟩
  · obtain ⟨p, rfl⟩ := Quot.exists_rep x
    obtain ⟨q, rfl⟩ := Quot.exists_rep y
    rw [spacePointMap_class, spacePointMap_class] at h
    obtain ⟨r, ⟨a⟩, ⟨b⟩⟩ := (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).mp h
    obtain ⟨c⟩ := spacePointRepresentative_arrow B S hS F r
    exact Quot.sound ⟨spacePointRepresentative B S hS F r,
      spacePoint_dominates_of_arrow B S hS F _ p (c ≫ a),
      spacePoint_dominates_of_arrow B S hS F _ q (c ≫ b)⟩
  · obtain ⟨p, rfl⟩ := Quot.exists_rep x
    refine ⟨(spacePointRepresentative B S hS F p).class B S hS F, ?_⟩
    rw [spacePointMap_class]
    exact (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).mpr
      ⟨spaceFieldValuedPoint B S hS F (spacePointRepresentative B S hS F p), ⟨𝟙 _⟩,
        spacePointRepresentative_arrow B S hS F p⟩

/-! ### Charts from a representing presheaf -/

/-- The category of elements of a presheaf is, tautologically, equivalent over the site to the
category of elements of that presheaf. -/
def spaceEquivalenceOver (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    StacksRepresentableCFG.EquivalenceOver (fibredCategory B S hS F).val.p
      (presheafOfCategories (F ⋙ typeToCat)).p :=
  StacksRepresentableCFG.EquivalenceOver.refl _

/-- The 1-morphism from the category of elements of `F` to a category over the site
represented by `F`, given by the inverse of a chosen representing equivalence. -/
def representationMap (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val :=
  { toFunctor := e.inv.functor, w := e.inv.w }

/-- The canonical map of a representing chart is bijective. -/
private theorem representationMap_bijective (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Function.Bijective (spacePointMap B S hS F 𝒳 (representationMap B S hS F 𝒳 e)) := by
  rw [show representationMap B S hS F 𝒳 e =
    (BasedFunctor.id _).comp (representationMap B S hS F 𝒳 e) from rfl, spacePointMap_comp]
  exact (pointsEquivOfBasedEquivalence B S hS (fibredCategory B S hS F).property 𝒳.property
    ((spaceEquivalenceOver B S hS F).trans e.symm).toBasedEquivalence).bijective.comp
    (spacePointMap_id_bijective B S hS F)

/-- The canonical map is natural in the chart: the morphism of representing presheaves induced
by a 1-morphism of represented categories acts on points the way the 1-morphism does. -/
theorem representationMap_naturality
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (eX : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver 𝒴.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴) (x : Space.points B S hS F) :
    spacePointMap B S hS G 𝒴 (representationMap B S hS G 𝒴 eY)
        (Space.pointsMap B S hS F (representingMap B S hS 𝒳 𝒴 F G eX eY f) x) =
      pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property f.hom
        (spacePointMap B S hS F 𝒳 (representationMap B S hS F 𝒳 eX) x) := by
  induction x using Quot.inductionOn with
  | h p =>
    rw [Space.pointsMap_class, spacePointMap_class, spacePointMap_class, pointsMap_class]
    have h := morphismSpaceEquiv_map B S hS 𝒳 𝒴 F G eX eY
      ⟨CatFiberedInGroupoids.homFunctor f, CatFiberedInGroupoids.homFunctor_comp_p f⟩
      p.siteObject p.value
    obtain ⟨i⟩ := Functor.exists_iso_of_isoClassMk_eq h
    exact (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).mpr ⟨_, ⟨i.hom.1⟩, ⟨𝟙 _⟩⟩

/-! ### The topology -/

/-- A chart of a category fibred in groupoids over the big fppf site of `S` by an algebraic
space: an algebraic space over `S` together with a 1-morphism from its category of elements. -/
abbrev SpaceChart (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :=
  Σ F : {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u // IsAlgebraicSpace B S hS F},
    (fibredCategory B S hS F.1).val ⥤ᵇ 𝒳.val

/-- The topology on the points of a category fibred in groupoids over the big fppf site of `S`:
the supremum, over all charts by algebraic spaces, of the topologies coinduced from the point
topologies of the algebraic spaces along the canonical maps. -/
@[instance_reducible, stacks 04Y8 "the underlying topological space of an algebraic stack"]
noncomputable def pointTopology
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    TopologicalSpace (points B S hS 𝒳.val 𝒳.property) :=
  ⨆ c : SpaceChart B S hS 𝒳,
    TopologicalSpace.coinduced (spacePointMap B S hS c.1.1 𝒳 c.2)
      (Space.pointTopology B S hS c.1.1)

/-- The open sets of `AlgebraicGeometry.Stack.pointTopology` are exactly those whose preimage
along every chart by an algebraic space is open. -/
theorem isOpen_pointTopology_iff
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (W : Set (points B S hS 𝒳.val 𝒳.property)) :
    @IsOpen _ (pointTopology B S hS 𝒳) W ↔
      ∀ c : SpaceChart B S hS 𝒳,
        @IsOpen _ (Space.pointTopology B S hS c.1.1)
          (spacePointMap B S hS c.1.1 𝒳 c.2 ⁻¹' W) := by
  rw [pointTopology, isOpen_iSup_iff]
  simp only [isOpen_coinduced]

/-- Every 1-morphism of categories fibred in groupoids over the big fppf site of `S` is
continuous on points for `AlgebraicGeometry.Stack.pointTopology`. -/
theorem continuous_pointsMap
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳.val ⥤ᵇ 𝒴.val) :
    @Continuous _ _ (pointTopology B S hS 𝒳) (pointTopology B S hS 𝒴)
      (pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property f) := by
  refine continuous_def.2 fun W hW => (isOpen_pointTopology_iff B S hS 𝒳 _).2 fun c => ?_
  have hc := (isOpen_pointTopology_iff B S hS 𝒴 _).1 hW ⟨c.1, c.2.comp f⟩
  rw [spacePointMap_comp] at hc
  simpa [Function.comp_def, Set.preimage_preimage] using hc

/-- The canonical map from the points of an algebraic space along a 1-morphism into a category
fibred in groupoids is continuous for `AlgebraicGeometry.Stack.pointTopology`. -/
theorem continuous_spacePointMap (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val) :
    @Continuous _ _ (Space.pointTopology B S hS F) (pointTopology B S hS 𝒳)
      (spacePointMap B S hS F 𝒳 f) :=
  continuous_def.2 fun W hW => (isOpen_pointTopology_iff B S hS 𝒳 W).1 hW ⟨⟨F, hF⟩, f⟩

/-! ### Openness of a flat chart locally of finite presentation -/

/-- Let `𝒳` be an algebraic stack over `S` and let `f` be a 1-morphism to it from the category of
elements of an algebraic space `F`, all of whose represented base changes are flat and locally of
finite presentation. Then the canonical map on points is open for
`AlgebraicGeometry.Stack.pointTopology`. -/
theorem isOpenMap_spacePointMap (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val)
    (hbase : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.obj)
      (_hy : y ⋙ 𝒳.val.p = Over.map U.hom)
      (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom)
          (fibredCategory B S hS F).val.p 𝒳.val.p y f.toFunctor)
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      (let g := (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)).hom
       Space.IsFlat B S hS g ∧ Space.IsLocallyOfFinitePresentation B S hS g)) :
    @IsOpenMap _ _ (Space.pointTopology B S hS F) (pointTopology B S hS 𝒳)
      (spacePointMap B S hS F 𝒳 f) := by
  classical
  intro W hW
  refine (isOpen_pointTopology_iff B S hS 𝒳 _).2 ?_
  rintro ⟨⟨A, hA⟩, gb⟩
  let Acfg := fibredCategory B S hS A
  let Fcfg := fibredCategory B S hS F
  let g : Acfg ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom gb
  let fm : Fcfg ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom f
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g fm
  let hQ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g fm
  let eA := spaceEquivalenceOver B S hS A
  let eF := spaceEquivalenceOver B S hS F
  have hArep : IsRepresentableByAlgebraicSpace B S hS Acfg := ⟨A, hA, ⟨eA⟩⟩
  have hFrep : IsRepresentableByAlgebraicSpace B S hS Fcfg := ⟨F, hF, ⟨eF⟩⟩
  obtain ⟨H, hH, ⟨eH⟩⟩ :=
    hasAlgebraicSpaceProducts_of_hasRepresentableDiagonal.{u, u, u + 1, u, u, u, u} B S hS 𝒳
      (SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳 h𝒳)
      Acfg Fcfg hArep hFrep gb f
  let a : (⟨H, hH⟩ : AlgebraicSpaces B S hS) ⟶ ⟨A, hA⟩ :=
    ObjectProperty.homMk (representingMap B S hS Q.pt Acfg H A eH eA Q.fst)
  let b : (⟨H, hH⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩ :=
    ObjectProperty.homMk (representingMap B S hS Q.pt Fcfg H F eH eF Q.snd)
  let Pflat : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ k => Space.IsFlat B S hS k.hom
  let Plfp : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k.hom
  let : Pflat.IsStableUnderBaseChange := Space.isFlat_isStableUnderBaseChange B S hS
  let : Plfp.IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  let : Pflat.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  let : Plfp.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS h𝒳 hFrep fm
  have hboth : (Pflat ⊓ Plfp) a :=
    (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS (Pflat ⊓ Plfp) fm hrep).mp
      (fun U y hy G hG he => hbase U y hy G hG he) Acfg hArep g Q hQ H A hH hA eH eA
  let ap := Space.pointsMap B S hS H a.hom
  let bp := Space.pointsMap B S hS H b.hom
  let rH := spacePointMap B S hS H Q.pt (representationMap B S hS H Q.pt eH)
  let rA := spacePointMap B S hS A Acfg (BasedFunctor.id Acfg.val)
  let rF := spacePointMap B S hS F Fcfg (BasedFunctor.id Fcfg.val)
  let pA := pointsMap B S hS Q.pt.val Q.pt.property Acfg.property Q.fst.hom
  let pF := pointsMap B S hS Q.pt.val Q.pt.property Fcfg.property Q.snd.hom
  let gp := pointsMap B S hS Acfg.val Acfg.property 𝒳.property gb
  let fp := pointsMap B S hS Fcfg.val Fcfg.property 𝒳.property f
  have ha : ∀ z, rA (ap z) = pA (rH z) := fun z =>
    representationMap_naturality B S hS H A Q.pt Acfg eH eA Q.fst z
  have hb : ∀ z, rF (bp z) = pF (rH z) := fun z =>
    representationMap_naturality B S hS H F Q.pt Fcfg eH eF Q.snd z
  have hg : ∀ z, gp (rA z) = spacePointMap B S hS A 𝒳 gb z := fun z =>
    (congrFun (spacePointMap_comp B S hS A Acfg 𝒳 (BasedFunctor.id Acfg.val) gb) z).symm
  have hf : ∀ z, fp (rF z) = spacePointMap B S hS F 𝒳 f z := fun z =>
    (congrFun (spacePointMap_comp B S hS F Fcfg 𝒳 (BasedFunctor.id Fcfg.val) f) z).symm
  have hcomm : ∀ z, gp (pA z) = fp (pF z) := by
    intro z
    change pointsMap B S hS Acfg.val Acfg.property 𝒳.property gb
        (pointsMap B S hS Q.pt.val Q.pt.property Acfg.property Q.fst.hom z) =
      pointsMap B S hS Fcfg.val Fcfg.property 𝒳.property f
        (pointsMap B S hS Q.pt.val Q.pt.property Fcfg.property Q.snd.hom z)
    rw [pointsMap_comp, pointsMap_comp]
    exact congrFun (pointsMap_eq_of_basedNatTrans B S hS Q.pt.val Q.pt.property 𝒳.property
      Q.iso.hom.hom) z
  have heq : spacePointMap B S hS A 𝒳 gb ⁻¹' (spacePointMap B S hS F 𝒳 f '' W) =
      ap '' (bp ⁻¹' W) := by
    ext z
    constructor
    · rintro ⟨x, hx, hxz⟩
      have hz : gp (rA z) = fp (rF x) := by rw [hg, hf, hxz]
      obtain ⟨q, hqA, hqF⟩ := exists_point_of_isTwoFibreProduct B S hS Q hQ (rA z) (rF x) hz
      obtain ⟨q', hq'⟩ := (representationMap_bijective B S hS H Q.pt eH).surjective q
      have haq : ap q' = z := (spacePointMap_id_bijective B S hS A).injective
        ((ha q').trans ((congrArg pA hq').trans hqA))
      have hbq : bp q' = x := (spacePointMap_id_bijective B S hS F).injective
        ((hb q').trans ((congrArg pF hq').trans hqF))
      exact ⟨q', by change bp q' ∈ W; rwa [hbq], haq⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨bp q, hq, ?_⟩
      rw [← hf, ← hg, ha, hb]
      exact (hcomm (rH q)).symm
  have hpre : @IsOpen _ (Space.pointTopology B S hS H) (bp ⁻¹' W) := by
    let _tH : TopologicalSpace (Space.points B S hS H) := Space.pointTopology B S hS H
    let _tF : TopologicalSpace (Space.points B S hS F) := Space.pointTopology B S hS F
    exact hW.preimage (Space.continuous_pointsMap B S hS b.hom)
  rw [heq]
  exact Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS hH hA
    a.hom hboth.1 hboth.2 _ hpre

/-! ### Uniqueness of the topology -/

/-- A family of topologies on the points of the algebraic stacks over `S` with the two
properties characterizing the topology on points: every 1-morphism of algebraic stacks is
continuous on points, and a 1-morphism from an algebraic space all of whose represented base
changes are flat and locally of finite presentation is continuous and open on points. -/
structure PointTopologyFamily where
  /-- The topology assigned to each algebraic stack. -/
  topology : ∀ (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
      (_h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val),
    TopologicalSpace (points B S hS 𝒳.val 𝒳.property)
  /-- Every 1-morphism of algebraic stacks is continuous on points. -/
  continuous : ∀ (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
      (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
      (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val) (f : 𝒳 ⟶ 𝒴),
    @Continuous _ _ (topology 𝒳 h𝒳) (topology 𝒴 h𝒴)
      (pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property f.hom)
  /-- The canonical map from the points of an algebraic space is continuous. -/
  space_continuous : ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_hF : IsAlgebraicSpace B S hS F)
      (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
      (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
      (f : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val),
    @Continuous _ _ (Space.pointTopology B S hS F) (topology 𝒳 h𝒳)
      (spacePointMap B S hS F 𝒳 f)
  /-- The canonical map from the points of an algebraic space along a 1-morphism all of whose
  represented base changes are flat and locally of finite presentation is open. -/
  space_open : ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_hF : IsAlgebraicSpace B S hS F)
      (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
      (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
      (f : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val),
    (∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.obj)
      (_hy : y ⋙ 𝒳.val.p = Over.map U.hom)
      (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom)
          (fibredCategory B S hS F).val.p 𝒳.val.p y f.toFunctor)
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      (let g := (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)).hom
       Space.IsFlat B S hS g ∧ Space.IsLocallyOfFinitePresentation B S hS g)) →
    @IsOpenMap _ _ (Space.pointTopology B S hS F) (topology 𝒳 h𝒳)
      (spacePointMap B S hS F 𝒳 f)

/-- The family of topologies given by the constructed topology
`AlgebraicGeometry.Stack.pointTopology`. -/
noncomputable def pointTopologyFamily : PointTopologyFamily.{u, w} B S hS where
  topology 𝒳 _ := pointTopology B S hS 𝒳
  continuous 𝒳 𝒴 _ _ f := continuous_pointsMap B S hS 𝒳 𝒴 f.hom
  space_continuous F hF 𝒳 _ f := continuous_spacePointMap B S hS F hF 𝒳 f
  space_open F hF 𝒳 h𝒳 f hbase := isOpenMap_spacePointMap B S hS F hF 𝒳 h𝒳 f hbase

/-- Every set open for the topology that a family of topologies with the two characterizing
properties assigns to an algebraic stack is open for `AlgebraicGeometry.Stack.pointTopology`. -/
theorem isOpen_pointTopology_of_family (t : PointTopologyFamily.{u, w} B S hS)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (W : Set (points B S hS 𝒳.val 𝒳.property))
    (hW : @IsOpen _ (t.topology 𝒳 h𝒳) W) :
    @IsOpen _ (pointTopology B S hS 𝒳) W :=
  (isOpen_pointTopology_iff B S hS 𝒳 W).2 fun c ↦
    continuous_def.1 (t.space_continuous c.1.1 c.1.2 𝒳 h𝒳 c.2) W hW

/-- A surjective open map detects open sets. -/
private theorem isOpen_of_surjective_isOpenMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hsurj : Function.Surjective f) (hopen : IsOpenMap f)
    {s : Set β} (hs : IsOpen (f ⁻¹' s)) : IsOpen s :=
  Set.image_preimage_eq s hsurj ▸ hopen _ hs

/-- Every family of topologies with the two characterizing properties assigns to an algebraic
stack the constructed topology `AlgebraicGeometry.Stack.pointTopology`. -/
theorem PointTopologyFamily.topology_eq (t : PointTopologyFamily.{u, w} B S hS)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    t.topology 𝒳 h𝒳 = pointTopology B S hS 𝒳 := by
  classical
  ext W
  refine ⟨isOpen_pointTopology_of_family B S hS t 𝒳 h𝒳 W, fun hW => ?_⟩
  obtain ⟨_hFib, -, -, U, fU, hfU, hAtlas⟩ := id h𝒳
  let hU := isAlgebraicSpace_yoneda B S hS U
  let Ucfg := schemeFibredCategory B S hS U
  let e := PresheafOfCategories.sliceElementsEquivalenceOver U
  let aU := representationMap B S hS (yoneda.obj U) Ucfg e
  let fa : Ucfg ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom fU
  let Xalg : AlgebraicStacks.{u, w} B S hS := ⟨𝒳, h𝒳⟩
  let Ualg : AlgebraicStacks.{u, w} B S hS :=
    ⟨Ucfg, isAlgebraicStack_schemeFibredCategory B S hS U⟩
  let falg : Ualg ⟶ Xalg := Bicategory.InducedBicategory.mkHom fa
  have hsurj := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
    falg hfU).2 (fun V y hy G hG hE => (hAtlas V y hy G hG hE).1)
  have hasurj : Function.Surjective
      (spacePointMap B S hS (yoneda.obj U) 𝒳 (aU.comp fU)) := by
    rw [spacePointMap_comp B S hS (yoneda.obj U) Ucfg 𝒳 aU fU]
    exact hsurj.comp (representationMap_bijective B S hS (yoneda.obj U) Ucfg e).surjective
  have haeq : Functor.IsEquivalence aU.toFunctor := e.symm.toEquivalence.isEquivalence_functor
  have hbeq : Functor.IsEquivalence (BasedFunctor.id 𝒳.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.obj))
  have haopen : @IsOpenMap _ _ (Space.pointTopology B S hS (yoneda.obj U))
      (t.topology 𝒳 h𝒳) (spacePointMap B S hS (yoneda.obj U) 𝒳 (aU.comp fU)) := by
    refine t.space_open (yoneda.obj U) hU 𝒳 h𝒳 (aU.comp fU) ?_
    refine relativeProperty_of_equivalences B S hS
      (fun _ _ k => Space.IsFlat B S hS k.hom ∧
        Space.IsLocallyOfFinitePresentation B S hS k.hom)
      (aU.comp fU) fU aU (BasedFunctor.id 𝒳.val) (Iso.refl _) ?_
    intro V y hy G hG hE
    have hsm := (hAtlas V y hy G hG hE).2
    exact ⟨Space.isFlat_of_isSmooth B S hS _ hsm,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩
  have hpre := (isOpen_pointTopology_iff B S hS 𝒳 W).mp hW
    ⟨⟨yoneda.obj U, hU⟩, aU.comp fU⟩
  exact @isOpen_of_surjective_isOpenMap _ _
    (Space.pointTopology B S hS (yoneda.obj U)) (t.topology 𝒳 h𝒳) _ hasurj haopen W hpre

/-- There is a unique family of topologies on the points of the algebraic stacks over `S` which
makes every 1-morphism continuous on points and makes a 1-morphism from an algebraic space whose
represented base changes are all flat and locally of finite presentation continuous and open on
points. -/
@[stacks 04XL "existence and uniqueness of topology"]
theorem existsUnique_pointTopologyFamily :
    ∃! _t : PointTopologyFamily.{u, w} B S hS, True := by
  refine ⟨pointTopologyFamily B S hS, trivial, ?_⟩
  rintro ⟨topology, continuous, space_continuous, space_open⟩ -
  have htop : topology = (pointTopologyFamily B S hS).topology := by
    funext 𝒳 h𝒳
    exact PointTopologyFamily.topology_eq B S hS
      ⟨topology, continuous, space_continuous, space_open⟩ 𝒳 h𝒳
  subst htop
  rfl

/-- There is at most one family of topologies with the two characterizing properties. -/
theorem PointTopologyFamily.eq (t t' : PointTopologyFamily.{u, w} B S hS) : t = t' :=
  ((existsUnique_pointTopologyFamily B S hS).unique trivial trivial :)

/-- The family of topologies with the two characterizing properties obtained from
`AlgebraicGeometry.Stack.existsUnique_pointTopologyFamily` by `Classical.choose`. -/
noncomputable def chosenPointTopologyFamily : PointTopologyFamily.{u, w} B S hS :=
  Classical.choose (existsUnique_pointTopologyFamily.{u, w} B S hS)

/-- The topology that `AlgebraicGeometry.Stack.chosenPointTopologyFamily` assigns to an
algebraic stack is the constructed topology `AlgebraicGeometry.Stack.pointTopology`. -/
theorem chosenPointTopologyFamily_topology_eq
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    (chosenPointTopologyFamily.{u, w} B S hS).topology 𝒳 h𝒳 = pointTopology B S hS 𝒳 :=
  PointTopologyFamily.topology_eq B S hS _ 𝒳 h𝒳

/-! ### Points of algebraic stacks -/

add_to_stacks 04XE "the equivalence of morphisms from spectra of fields: a common refinement"
  AlgebraicGeometry.Stack.FieldValuedPoint.HasCommonExtension
add_to_stacks 04XE "the induced map |f| : |𝒳| → |𝒴| of a 1-morphism"
  AlgebraicGeometry.Stack.pointsMap
add_to_stacks 04XE "2-isomorphic 1-morphisms induce the same map on points, so a \
2-commutative square of stacks gives a commutative square of sets"
  AlgebraicGeometry.Stack.pointsMap_eq_of_basedNatTrans
add_to_stacks 04XE "the map on points of a composite is the composite of the maps"
  AlgebraicGeometry.Stack.pointsMap_comp
add_to_stacks 04XE "an equivalence 𝒳 → 𝒴 induces a bijection |𝒳| → |𝒴|"
  AlgebraicGeometry.Stack.pointsEquivOfBasedEquivalence
add_to_stacks 04XE "agreement with the points of an algebraic space (Definition 03BU)"
  AlgebraicGeometry.Stack.spacePointMap_id_bijective

end AlgebraicGeometry.Stack

end
