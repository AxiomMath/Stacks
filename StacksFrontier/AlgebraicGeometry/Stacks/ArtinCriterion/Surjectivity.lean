module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.SetTheory.Cardinal.Free
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatUniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphismRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.CoarserTopology
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCompositeSnd
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindexSnd
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import StacksFrontier.Deformation.Artin.LimitPreserving
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.SmoothNeighborhood
import all StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
import StacksFrontier.AlgebraicGeometry.Stacks.EtaleStackIsFppfStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.ChartCoproduct
import all StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.ChartCoproduct

/-!
# Artin's criterion: surjectivity of the atlas

The surjectivity half of the assembly of Artin's criterion (Stacks 07Y4): a 1-morphism from a
scheme to `𝒳` whose image is open and contains every finite type point is surjective, and so is
the 1-morphism out of a scheme through which every finite type field-valued object of `𝒳` factors.
The charts through those objects are what Stacks 07XY provides.

## Main definitions

* `AlgebraicGeometry.Stack.HasSmoothFiniteTypeNeighborhoods`: the conclusion of **Stacks 07XY**
  for `𝒳`, a smooth chart of finite type through every finite type field-valued object. Why it is
  carried as a hypothesis is explained in the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion.Algebraicity`.

## References

* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07XY](https://stacks.math.columbia.edu/tag/07XY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v v' v'' w z vX vI wI uX

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open CategoryTheory.Limits

/-- **The conclusion of Stacks 07XY for `𝒳`: every finite type field-valued object of `𝒳` has a
smooth neighbourhood of finite type.** For every finite type field `k` over `S` and every object
`x₀` of `𝒳` over `Spec(k)` there are a scheme `U` of finite type over `S`, an object `x` of `𝒳`
over `U`, a finite type point `u₀` of `U` with residue field `k`, a cartesian arrow `x₀ ⟶ x` whose
base is the residue field point of `u₀`, and a 1-morphism `(Sch/U) ⟶ 𝒳` sending the tautological
object to `x`, which is representable by algebraic spaces and smooth.

This is the statement Artin's criterion is assembled out of; see the implementation notes for why
it is carried as a hypothesis here. -/
public abbrev HasSmoothFiniteTypeNeighborhoods
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (AlgebraicGeometry.BigFppfOver B S hS)) : Prop :=
  ∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ S)
    (x₀ : 𝒳.val.obj)
    (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
    LocallyOfFiniteType i₀ → QuasiCompact i₀ →
    ∀ (s : S), i₀ (IsLocalRing.closedPoint k) = s →
      ∃ (U : AlgebraicGeometry.BigFppfOver B S hS)
        (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
        (u₀ : U.left.1)
        (e : U.left.1.residueField u₀ ≃+* k)
        (r : x₀ ⟶ x)
        (f : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳.val),
        LocallyOfFiniteType (B.inclusion.map U.hom) ∧
        QuasiCompact (B.inclusion.map U.hom) ∧
        AlgebraicGeometry.IsFiniteTypePoint u₀ ∧
        𝒳.val.p.IsCartesian (𝒳.val.p.map r) r ∧
        ((eqToHom hx₀.symm ≫
            (𝒳.val.p ⋙ Over.post B.inclusion).map r ≫
            eqToHom (congrArg (Over.post B.inclusion).obj hx)).left =
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫
            U.left.1.fromSpecResidueField u₀) ∧
        Nonempty ((Functor.twoYonedaEvaluation 𝒳.val.p U).obj f ≅
          (⟨x, hx⟩ : 𝒳.val.p.Fiber U)) ∧
        (∃ _hrep : IsRepresentableByAlgebraicSpaces B S hS f,
          ∀ (V : AlgebraicGeometry.BigFppfOver B S hS)
            (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
            (_hy : y ⋙ 𝒳.val.p = Over.map V.hom)
            (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
            (hF : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2 F),
            Nonempty (StacksRepresentableCFG.EquivalenceOver
              (TwoFibreProductOver.fst (Over.map V.hom)
                (schemeFibredCategory B S hS U).val.p 𝒳.val.p y
                f.toFunctor)
              (presheafOfCategories (F ⋙ typeToCat)).p) →
            AlgebraicGeometry.Space.IsSmooth B S hS
              (AlgebraicGeometry.algebraicSpaceMap B S hS V
                ((spacesOverSmallerBaseFunctor
                  B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom)

private theorem residueField_spec_mem {X : Scheme.{u}} (hX : B.Contains X) (x : X) :
    B.Contains (Spec (X.residueField x)) := by
  have : Mono (X.fromSpecResidueField x) := inferInstance
  have : QuasiCompact (X.fromSpecResidueField x) := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    intro V hV
    exact (Set.toFinite (X.fromSpecResidueField x ⁻¹' (V : Set X))).isCompact
  exact lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (X.fromSpecResidueField x)) hX

private noncomputable def fieldPointOverSchemePoint
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) :
    Space.FieldValuedPoint B S hS (yoneda.obj U) := by
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U
  let hK : B.Contains (Spec (X.residueField x)) :=
    residueField_spec_mem B U.left.property x
  let kobj : B.Schemes := B.obj hK
  let f : kobj ⟶ U.left := B.inclusion.preimage (X.fromSpecResidueField x)
  let V : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (f ≫ U.hom)
  refine ⟨X.residueField x, hK, ?_, ?_⟩
  · exact B.inclusion.map (f ≫ U.hom)
  · change V ⟶ U
    exact Over.homMk f

private theorem fieldPointOverSchemePoint_schemePoint
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) :
    Space.schemePoint B S hS U (fieldPointOverSchemePoint B S hS U x) = x := by
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U
  let kobj : B.Schemes := B.obj (residueField_spec_mem B U.left.property x)
  show B.inclusion.map (B.inclusion.preimage (X := kobj) (Y := U.left)
    (X.fromSpecResidueField x)) _ = x
  rw [B.inclusion.map_preimage]
  exact Scheme.fromSpecResidueField_apply x _

private theorem isSurjective_of_isOpen_of_finiteTypePoints_lift
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (f : F ⟶ yoneda.obj U)
    (hf : AlgebraicGeometry.Space.IsOpenMorphism B S hS f)
    (hpoints : ∀ x : U.left.1, AlgebraicGeometry.IsFiniteTypePoint x →
      (fieldPointOverSchemePoint B S hS U x).class ∈
        Set.range (Space.pointsMap B S hS F f)) :
    Space.IsSurjective B S hS f := by
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS F) :=
    Space.pointTopology B S hS F
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS (yoneda.obj U)) :=
    Space.pointTopology B S hS (yoneda.obj U)
  have hopen : IsOpen (Set.range (Space.pointsMap B S hS F f)) := hf.isOpen_range
  obtain ⟨V, hV, hcompat⟩ :=
    (Space.isOpen_yoneda_iff_isSchemeOpen B S hS U _).mp hopen
  have hVtop : V = Set.univ := by
    apply eq_univ_of_isOpen_of_finiteTypePoints_subset hV
    intro x hx
    have := (hcompat (fieldPointOverSchemePoint B S hS U x)).mp (hpoints x hx)
    simpa only [fieldPointOverSchemePoint_schemePoint] using this
  intro q
  induction q using Quot.inductionOn with
  | h q =>
    apply (hcompat q).mpr
    rw [hVtop]
    trivial

private theorem isSurjective_of_isSmooth_of_finiteTypePoints_lift
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (f : F ⟶ yoneda.obj U)
    (hf : AlgebraicGeometry.Space.IsSmooth B S hS f)
    (hpoints : ∀ x : U.left.1, AlgebraicGeometry.IsFiniteTypePoint x →
      (fieldPointOverSchemePoint B S hS U x).class ∈
        Set.range (Space.pointsMap B S hS F f)) :
    Space.IsSurjective B S hS f :=
  isSurjective_of_isOpen_of_finiteTypePoints_lift B S hS hF U f
    (Space.isOpenMorphism_of_isFlat_of_isLocallyOfFinitePresentation B S hS hF
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) f
      (Space.isFlat_of_isSmooth B S hS f hf)
      (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hf)) hpoints

private theorem nonempty_section_of_equivalenceOver
    {C : Type w} [Category.{v} C] {D : Type*} [Category D]
    (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) (x : D) :
    Nonempty (F.obj (Opposite.op (p.obj x))) := by
  let z := e.hom.functor.obj x
  have hz := congrArg (fun q : D ⥤ C => q.obj x) e.hom.w
  change z.base = p.obj x at hz
  rw [← hz]
  exact ⟨(PresheafOfCategories.objEquiv (F ⋙ typeToCat) z).2.as⟩

private theorem fieldPoint_mem_range_algebraicSpaceMap_of_nonempty_section
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2 F)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj V))
    (hp : Nonempty (F.obj (Opposite.op (Over.mk p.value.left)))) :
    p.class ∈ Set.range (Space.pointsMap B S hS _
      (AlgebraicGeometry.algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor
          B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom) := by
  obtain ⟨s⟩ := hp
  let G := (spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩
  let z : ((OverShriek.relocalizePresheafFunctor V.hom).obj F).obj
      (Opposite.op p.siteObject) := ⟨⟨p.value.left, s⟩, p.value.w⟩
  let q : Space.FieldValuedPoint B S hS G.1.left :=
    { carrier := p.carrier
      contained := p.contained
      toBase := p.toBase
      value := ((spacesOverSmallerBaseFunctorForgetIso
        B V.left.1 S V.left.2 hS V.hom).inv.app ⟨F, hF⟩).app _ z }
  refine ⟨q.class, ?_⟩
  show (Space.FieldValuedPoint.map B S hS G.1.left G.1.hom q).class = p.class
  have hz : G.1.hom.app _ q.value = p.value :=
    spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
      B V.left.1 S V.left.2 hS V.hom ⟨F, hF⟩ (Opposite.op p.siteObject) z
  have hq : Space.FieldValuedPoint.map B S hS G.1.left G.1.hom q = p := by
    cases p
    dsimp only [Space.FieldValuedPoint.map, q]
    congr 1
  exact congrArg (fun t => t.class) hq


private theorem fieldPoint_mem_range_algebraicSpaceMap_of_object
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2 F)
    {D : Type w} [Category.{v} D]
    (q : D ⥤ AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)
    (e : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj V))
    (x : D) (hx : q.obj x = Over.mk p.value.left) :
    p.class ∈ Set.range (Space.pointsMap B S hS _
      (AlgebraicGeometry.algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor
          B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom) := by
  apply fieldPoint_mem_range_algebraicSpaceMap_of_nonempty_section B S hS V F hF p
  simpa only [hx] using nonempty_section_of_equivalenceOver q F e x


/-- A morphism of the 1-morphism `g` out of `Over.forget W` over `δ : T ⟶ Over.mk (𝟙 W)` is
strongly cartesian over `δ.left`. -/
private theorem isStronglyCartesian_map_over
    {C : Type*} [Category C] {D : Type*} [Category D]
    (p : D ⥤ C) (hp : p.IsFiberedInGroupoids) {W : C}
    (g : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ BasedCategory.ofFunctor p)
    {T : Over W} (δ : T ⟶ Over.mk (𝟙 W)) :
    p.IsStronglyCartesian δ.left (g.map δ) := by
  have hw : g.toFunctor ⋙ p = Over.forget W := g.w
  have : (Over.forget W).IsHomLift δ.left δ := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
  have : p.IsHomLift δ.left (g.map δ) := Functor.isHomLift_map_of_comp_eq hw δ.left δ
  exact hp.isStronglyCartesian_homLift _ _

section IsoSchemePoint

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

private theorem exists_iso_schemePoint_obj_of_hom
    {C : Type*} [Category C] {D : Type*} [Category D]
    (p : D ⥤ C) (hp : p.IsFiberedInGroupoids) {W A : C}
    (g : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ BasedCategory.ofFunctor p)
    (x : D) (hx : p.obj x = W)
    (heval : Nonempty ((Functor.twoYonedaEvaluation p W).obj g ≅
      (⟨x, hx⟩ : p.Fiber W)))
    {z : D} (a : A ⟶ W) (r : z ⟶ x) (hr : p.IsHomLift a r) :
    ∃ e : z ≅ g.obj (Over.mk a), p.IsHomLift (𝟙 A) e.hom := by
  let δ : Over.mk a ⟶ Over.mk (𝟙 W) := Over.homMk a (by simp)
  have hmap : p.IsHomLift a (g.map δ) := (isStronglyCartesian_map_over p hp g δ).toIsHomLift
  let ehom : g.obj (Over.mk (𝟙 W)) ⟶ x :=
    Functor.Fiber.fiberInclusion.map heval.some.hom
  have he : p.IsHomLift (𝟙 W) ehom := heval.some.hom.2
  let s : g.obj (Over.mk a) ⟶ x := g.map δ ≫ ehom
  have hs : p.IsHomLift a s :=
    IsHomLift.comp_lift_id_right' p a (g.map δ) W ehom
  have hsCart : p.IsStronglyCartesian a s := hp.isStronglyCartesian_homLift a s
  have hrCart : p.IsStronglyCartesian a r := hp.isStronglyCartesian_homLift a r
  let iso := Functor.IsStronglyCartesian.domainIsoOfBaseIso p
    (f := a) (f' := a) (g := Iso.refl A) (by simp) s r
  refine ⟨iso, ?_⟩
  show p.IsHomLift (𝟙 A)
    (Functor.IsStronglyCartesian.domainIsoOfBaseIso p (g := Iso.refl A) _ s r).hom
  rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.map_isHomLift p a s _ r

end IsoSchemePoint

private theorem exists_twoFibreProductOver_of_hom
    {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E]
    (p : D ⥤ C) (hp : p.IsFiberedInGroupoids) (q : E ⥤ C)
    (y : E ⥤ D) {W : C}
    (g : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ BasedCategory.ofFunctor p)
    (x : D) (hx : p.obj x = W)
    (heval : Nonempty ((Functor.twoYonedaEvaluation p W).obj g ≅
      (⟨x, hx⟩ : p.Fiber W)))
    (t : E) (a : q.obj t ⟶ W) (r : y.obj t ⟶ x)
    (hr : p.IsHomLift a r) :
    ∃ z : TwoFibreProductOver q (Over.forget W) p y g.toFunctor, z.x = t := by
  obtain ⟨e, he⟩ := exists_iso_schemePoint_obj_of_hom p hp g x hx heval a r hr
  exact ⟨⟨q.obj t, t, Over.mk a, rfl, rfl, e, he⟩, rfl⟩

private theorem fieldPoint_mem_range_algebraicSpaceMap_of_hom
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (W V : AlgebraicGeometry.BigFppfOver B S hS)
    (g : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒳.val)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = W)
    (heval : Nonempty ((Functor.twoYonedaEvaluation 𝒳.val.p W).obj g ≅
      (⟨x, hx⟩ : 𝒳.val.p.Fiber W)))
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2 F)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom)
        (schemeFibredCategory B S hS W).val.p 𝒳.val.p y g.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj V))
    (a : (Over.map V.hom).obj (Over.mk p.value.left) ⟶ W)
    (r : y.obj (Over.mk p.value.left) ⟶ x)
    (hr : 𝒳.val.p.IsHomLift a r) :
    p.class ∈ Set.range (Space.pointsMap B S hS _
      (AlgebraicGeometry.algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor
          B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom) := by
  obtain ⟨z, hz⟩ := exists_twoFibreProductOver_of_hom 𝒳.val.p 𝒳.property
    (Over.map V.hom) y g x hx heval (Over.mk p.value.left) a r hr
  exact fieldPoint_mem_range_algebraicSpaceMap_of_object B S hS V F hF _ e p z hz

private theorem exists_fieldBaseOver_iso
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : Space.FieldValuedPoint B S hS F)
    [LocallyOfFiniteType p.toBase] [QuasiCompact p.toBase] :
    ∃ d : finiteTypeFieldBaseData S, Nonempty (p.siteObject ≅ fieldBaseOver B S hS d.1) := by
  obtain ⟨d, e, he⟩ := exists_finiteTypeFieldBaseMap S p.carrier p.toBase
  let eSpec : Spec (.of p.carrier) ≅ Spec (.of (FreeCommRing S.size.out ⧸ d.1.2.1.1)) :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op
  let eSite : p.siteObject.left ≅ (fieldBaseOver B S hS d.1).left :=
    B.inclusion.preimageIso eSpec
  refine ⟨d, ⟨Over.isoMk eSite ?_⟩⟩
  apply B.inclusion.map_injective
  show B.inclusion.map eSite.hom ≫ fieldBaseMap S d.1 = p.toBase
  dsimp only [eSite, Functor.preimageIso]
  rw [Functor.map_preimage]
  exact he

private theorem exists_hom_of_iso_base
    {C : Type*} [Category C] {D : Type*} [Category D]
    (p : D ⥤ C) (hp : p.IsFiberedInGroupoids)
    {A A' W : C} (e : A ≅ A') (x : p.Fiber A) (z : p.Fiber W)
    (h : ∀ x' : p.Fiber A', ∃ (a : A' ⟶ W) (r : x'.1 ⟶ z.1),
      p.IsHomLift a r) :
    ∃ (a : A ⟶ W) (r : x.1 ⟶ z.1), p.IsHomLift a r := by
  let : p.IsFibered := hp.isFibered
  let x' := Functor.pullbackFiber p x e.inv
  let s : x'.1 ⟶ x.1 := Functor.IsPreFibered.pullbackMap x.2 e.inv
  have hs : p.IsHomLift e.inv s := inferInstance
  have hsCart : p.IsStronglyCartesian e.inv s := hp.isStronglyCartesian_homLift e.inv s
  have hsIso : IsIso s := Functor.IsStronglyCartesian.isIso_of_base_isIso p e.inv s
  obtain ⟨a, r, hr⟩ := h x'
  refine ⟨e.hom ≫ a, inv s ≫ r, ?_⟩
  have hsi : p.IsHomLift e.hom (inv s) := by
    simpa using (inferInstance : p.IsHomLift (inv e.inv) (inv s))
  exact IsHomLift.comp p e.hom a (inv s) r

section SchemePoints

open CategoryTheory.Functor
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion Fiber.mk

private def precomposeSchemePoint
    {C : Type u} [Category C] {D : Type w} [Category.{v} D]
    (p : D ⥤ C) {U V : C} (a : U ⟶ V)
    (g : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ BasedCategory.ofFunctor p) :
    BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p where
  toFunctor := Over.map a ⋙ g.toFunctor
  w := by rw [Functor.assoc, g.w]; rfl

private def precomposeSchemePoint_evaluationIso
    {C : Type u} [Category C] {D : Type w} [Category.{v} D]
    (p : D ⥤ C) [p.IsFibered] (hp : p.IsFiberedInGroupoids)
    {U V : C} (a : U ⟶ V)
    (g : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ BasedCategory.ofFunctor p) :
    (twoYonedaEvaluation p U).obj (precomposeSchemePoint p a g) ≅
      pullbackFiber p ((twoYonedaEvaluation p V).obj g) a := by
  let x := (twoYonedaEvaluation p V).obj g
  let y := (twoYonedaEvaluation p U).obj (precomposeSchemePoint p a g)
  let δ : (Over.map a).obj (Over.mk (𝟙 U)) ⟶ Over.mk (𝟙 V) :=
    Over.homMk a (by simp)
  have hcart : p.IsStronglyCartesian a (g.map δ) := isStronglyCartesian_map_over p hp g δ
  exact (Restriction.ofCartesian y.2 x.2 (g.map δ) hcart).fiberIso.symm

private theorem schemePoint_iso_of_evaluation_iso
    {C : Type u} [Category C] {D : Type w} [Category.{v} D]
    (p : D ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C)
    (f g : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p)
    (h : Nonempty ((twoYonedaEvaluation p U).obj f ≅ (twoYonedaEvaluation p U).obj g)) :
    Nonempty (f ≅ g) := by
  let : (twoYonedaEvaluation p U).IsEquivalence := twoYonedaEvaluation_isEquivalence p hp U
  exact ⟨(twoYonedaEvaluation p U).preimageIso h.some⟩

end SchemePoints


private theorem exists_hom_to_glued_object
    {C : Type*} [Category C] {D : Type*} [Category D]
    (p : D ⥤ C) [p.IsFibered] {A U W : C}
    (j : U ⟶ W) (z : p.Fiber W) (x : p.Fiber U)
    (e : Functor.pullbackFiber p z j ≅ x)
    (y : p.Fiber A) (a : A ⟶ U) (r : y.1 ⟶ x.1)
    (hr : p.IsHomLift a r) :
    ∃ s : y.1 ⟶ z.1, p.IsHomLift (a ≫ j) s := by
  let t : x.1 ⟶ (Functor.pullbackFiber p z j).1 :=
    Functor.Fiber.fiberInclusion.map e.inv
  have ht : p.IsHomLift (𝟙 U) t := e.inv.2
  let q := Functor.IsPreFibered.pullbackMap z.2 j
  have hq : p.IsHomLift j q := inferInstance
  have htq : p.IsHomLift j (t ≫ q) :=
    IsHomLift.comp_lift_id_left' p U t j q
  exact ⟨r ≫ (t ≫ q), IsHomLift.comp p a j r (t ≫ q)⟩

private theorem exists_hom_of_field_models
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (W : AlgebraicGeometry.BigFppfOver B S hS) (z : 𝒳.val.p.Fiber W)
    (hmodels : ∀ d : finiteTypeFieldBaseData S,
      ∀ x : 𝒳.val.p.Fiber (fieldBaseOver B S hS d.1),
      ∃ (a : fieldBaseOver B S hS d.1 ⟶ W) (r : x.1 ⟶ z.1),
        𝒳.val.p.IsHomLift a r)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : Space.FieldValuedPoint B S hS F)
    [LocallyOfFiniteType p.toBase] [QuasiCompact p.toBase]
    (x : 𝒳.val.p.Fiber p.siteObject) :
    ∃ (a : p.siteObject ⟶ W) (r : x.1 ⟶ z.1), 𝒳.val.p.IsHomLift a r := by
  obtain ⟨d, ⟨e⟩⟩ := exists_fieldBaseOver_iso B S hS p
  exact exists_hom_of_iso_base 𝒳.val.p 𝒳.property e x z (hmodels d)


private theorem isSurjective_of_field_models [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (W : AlgebraicGeometry.BigFppfOver B S hS) (z : 𝒳.val.p.Fiber W)
    (g : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒳.val)
    (heval : Nonempty ((Functor.twoYonedaEvaluation 𝒳.val.p W).obj g ≅ z))
    (hmodels : ∀ d : finiteTypeFieldBaseData S,
      ∀ x : 𝒳.val.p.Fiber (fieldBaseOver B S hS d.1),
      ∃ (a : fieldBaseOver B S hS d.1 ⟶ W) (r : x.1 ⟶ z.1),
        𝒳.val.p.IsHomLift a r)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (hy : y ⋙ 𝒳.val.p = Over.map V.hom)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2 F)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom)
        (schemeFibredCategory B S hS W).val.p 𝒳.val.p y g.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (hsmooth : AlgebraicGeometry.Space.IsSmooth B S hS
      (AlgebraicGeometry.algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor
          B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom) :
    Space.IsSurjective B S hS
      (AlgebraicGeometry.algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor
          B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom := by
  let G := (spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩
  apply isSurjective_of_isSmooth_of_finiteTypePoints_lift B S hS G.property V
    G.1.hom hsmooth
  intro v hv
  let p := fieldPointOverSchemePoint B S hS V v
  have hbase : p.toBase = V.left.1.fromSpecResidueField v ≫ B.inclusion.map V.hom := by
    have hstep : B.inclusion.map
        ((B.inclusion.preimage (V.left.1.fromSpecResidueField v) :
          p.siteObject.left ⟶ V.left) ≫ V.hom) =
        V.left.1.fromSpecResidueField v ≫ B.inclusion.map V.hom :=
      (B.inclusion.map_comp _ _).trans
        (congrArg (· ≫ B.inclusion.map V.hom) (B.inclusion.map_preimage _))
    exact hstep
  have : LocallyOfFiniteType (V.left.1.fromSpecResidueField v) := hv.1
  have : LocallyOfFiniteType p.toBase := by
    rw [hbase]
    exact MorphismProperty.comp_mem _ _ _ hv.1 inferInstance
  have : QuasiCompact p.toBase := inferInstance
  let t := Over.mk p.value.left
  have ht : (Over.map V.hom).obj t = p.siteObject := by
    show Over.mk (p.value.left ≫ V.hom) = p.siteObject
    rw [p.value.w]
    rfl
  let x : 𝒳.val.p.Fiber p.siteObject :=
    ⟨y.obj t, (Functor.congr_obj hy t).trans ht⟩
  obtain ⟨a, r, hr⟩ := exists_hom_of_field_models B S hS 𝒳 W z hmodels p x
  let a' : (Over.map V.hom).obj t ⟶ W := eqToHom ht ≫ a
  have hr' : 𝒳.val.p.IsHomLift a' r := by
    dsimp [a']
    infer_instance
  exact fieldPoint_mem_range_algebraicSpaceMap_of_hom B S hS 𝒳 W V g z.1 z.2
    heval y F hF e p a' r hr'

end AlgebraicGeometry.Stack

end
