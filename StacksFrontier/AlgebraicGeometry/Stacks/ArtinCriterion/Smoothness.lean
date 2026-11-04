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
# Artin's criterion: smoothness of the atlas

The smoothness half of the assembly of Artin's criterion (Stacks 07Y4): the maps between the
presheaves of isomorphism classes represented by 1-morphisms of categories fibred in setoids, their
pullback squares, and the smoothness of a 1-morphism out of a coproduct of schemes, checked on the
open pieces of the coproduct.

## Main definitions

* `AlgebraicGeometry.Stack.HasFiniteDimensionalTangentSpaces`: the tangent-space half of
  **axiom [3]**, the hypothesis from which Stacks 07XY builds the smooth charts.

## Implementation notes

*Universes.* The last universe identity of the assembly of Artin's criterion to go was in the
`representedMap` section of this file, and it was an *object* universe identity, not a morphism
one. `CategoryTheory.Functor.isoClassPresheaf` is valued in the object universe of its total
category, so `CategoryTheory.Functor.isoClassMapUniv`, a morphism
`p.isoClassPresheaf ⟶ q.isoClassPresheaf`, exists only when the two categories it compares have
one object universe: a natural transformation between presheaves valued in different universes
does not typecheck. `AlgebraicGeometry.Stack.isPullback_representedMap` compares a 2-fibre product
with one of its factors, and the object universe of the product absorbs the morphism universes of
the factors and the objects of the site — equal to the factor's only when the factor absorbs them
too, which cannot be written as a universe identity: writing the factor's object universe as a
`max` containing them makes the constraint `max a ?v = c` at each call site, which Lean's universe
unifier cannot solve.

What lifted it is `CategoryTheory.Functor.isoClassFun`, the map on isomorphism classes at a single
object of the site, which exists at wholly independent object universes, together with
`CategoryTheory.Functor.isoClassFun_naturality` in place of the naturality of `isoClassMapUniv` and
`CategoryTheory.Functor.isoClassMapULift`, the `CategoryTheory.uliftFunctor`-composed
`isoClassMapUniv` — the idiom the library already uses for `CategoryTheory.Functor.isomPresheaf`,
as in `AlgebraicGeometry.ProperFlatFibre.isomPresheafIso`. Stacks 04SD
(`CategoryTheory.Functor.twoFibreProductIsoClassEquivUniv`) is stated through `isoClassFun` and so
now holds at independent object universes; `AlgebraicGeometry.Stack.representedMap` is built from
`isoClassMapULift`, and `isPullback_representedMap` and the rest of the section take their three
categories at independent object universes. Stacks 07XY does not go through this layer and was
already at the free shape.

## References

* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v v' v'' w z vX vI wI uX

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open CategoryTheory.Limits

/-- **Axiom [3], the tangent-space half.** For every finite type field `k` over `S`, every
object `x₀` of `𝒳` over `Spec(k)` and every presentation of the local ring of `S` at the image
point, the tangent space of the predeformation category of `x₀` is a finite dimensional
`k`-vector space for its canonical structure.

The finite-dimensionality of infinitesimal automorphisms, the other half of the source's axiom
[3], is not asked for: Stacks 07XY uses only the tangent spaces, so omitting it gives the
stronger criterion the published proof establishes. -/
public abbrev HasFiniteDimensionalTangentSpaces
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (AlgebraicGeometry.BigFppfOver B S hS)) : Prop :=
  ∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ S)
    (x₀ : 𝒳.val.obj)
    (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
    LocallyOfFiniteType i₀ → QuasiCompact i₀ →
    ∀ (s : S), i₀ (IsLocalRing.closedPoint k) = s →
    ∀ (Λ : Type u) [CommRing Λ] [Algebra Λ k]
      (_hΛstalk : Λ = S.presheaf.stalk s)
      (iΛ : Spec (.of Λ) ⟶ S)
      (_hiΛ : HEq iΛ (S.fromSpecStalk s))
      (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ = i₀),
      let hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
        hx₀.trans (congrArg Over.mk hbase.symm)
      let D := Deformation.Artin.predeformationCategory iΛ
        (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx
      letI : Category D.carrier := D.category
      ∀ hD : Deformation.IsDeformationCategory D.projection,
        let 𝓕 := BasedCategory.ofFunctor D.projection
        let hS2 :=
          Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
            𝓕 hD
        letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
        letI : Fact (Deformation.SchlessingerConditionS2
          (CategoryOfElements.π
            (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
        let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
        let T := Deformation.artinianTangentSpace Λ k F
        letI : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
        letI : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
        FiniteDimensional k T

section RepresentedMaps

open CategoryTheory.PresheafOfCategories Opposite

/-- A functor over `C` into a category fibred in groupoids is a 1-morphism of fibred categories. -/
private theorem isFibredOneMorphism_of_comp_eq
    {C : Type w} [Category.{u} C]
    {X : Type v} {Y : Type z} [Category.{u} X] [Category.{u} Y]
    {p : X ⥤ C} {q : Y ⥤ C} (hq : q.IsFiberedInGroupoids) {H : X ⥤ Y} (hH : H ⋙ q = p) :
    Functor.IsFibredOneMorphism p q H := ⟨hH, by
  intro _ _ f _ _ φ hφ
  have := hφ
  have := Functor.isHomLift_map_of_comp_eq hH f φ
  exact hq.isStronglyCartesian_homLift f (H.map φ)⟩

section ReprMap
variable {C : Type w} [Category.{u} C]
    {X : Type v} {Y : Type z} [Category.{u} X] [Category.{u} Y]
    (p : X ⥤ C) (q : Y ⥤ C) (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F G : Cᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver p (discreteProjection F))
    (eG : StacksRepresentableCFG.EquivalenceOver q (discreteProjection G))
    (H : X ⥤ Y) (hH : H ⋙ q = p)
private def representedMap : F ⟶ G := by
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  exact natTransEquivOfPointwiseEquiv
    (p.isoClassPresheaf ⋙ uliftFunctor.{z, v}) (q.isoClassPresheaf ⋙ uliftFunctor.{v, z}) F G
    (fun U => Equiv.ulift.trans (isoClassEquiv F eF U.unop))
    (fun U => Equiv.ulift.trans (isoClassEquiv G eG U.unop))
    (fun f a => isoClassEquiv_naturality hp F eF f.unop a.down)
    (fun f a => isoClassEquiv_naturality hq G eG f.unop a.down)
    (Functor.isoClassMapULift (isFibredOneMorphism_of_comp_eq hq hH))

private theorem representedMap_app_isoClass
    (U : C) (x : p.Fiber U) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    (representedMap p q hp hq F G eF eG H hH).app (op U)
      (isoClassEquiv F eF U (Functor.isoClassMk p x)) =
      isoClassEquiv G eG U (Functor.isoClassMk q
        ((Functor.fiberFunctorOfCompEq hH U).obj x)) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  show (isoClassEquiv G eG U)
    (Functor.isoClassFun (isFibredOneMorphism_of_comp_eq hq hH) U
      ((isoClassEquiv F eF U).symm ((isoClassEquiv F eF U) (Functor.isoClassMk p x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl
end ReprMap

private theorem representedMap_app
    {C : Type w} [Category.{u} C]
    {X : Type v} {Y : Type z} [Category.{u} X] [Category.{u} Y]
    (p : X ⥤ C) (q : Y ⥤ C) (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F G : Cᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver p (discreteProjection F))
    (eG : StacksRepresentableCFG.EquivalenceOver q (discreteProjection G))
    (H : X ⥤ Y) (hH : H ⋙ q = p) (U : C)
    (c : Quotient (isIsomorphicSetoid (p.Fiber U))) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    (representedMap p q hp hq F G eF eG H hH).app (op U)
      (isoClassEquiv F eF U c) =
      isoClassEquiv G eG U
        (Functor.isoClassFun (isFibredOneMorphism_of_comp_eq hq hH) U c) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  obtain ⟨x, rfl⟩ := Functor.isoClassMk_surjective c
  exact representedMap_app_isoClass p q hp hq F G eF eG H hH U x

private theorem isPullback_of_pointwise_fiber_equiv
    {C : Type w} [Category.{u} C]
    {X : Type v} {Y : Type v'} {Z : Type v''}
    [Category.{u} X] [Category.{u} Y] [Category.{u} Z]
    (p : X ⥤ C) (q : Y ⥤ C) (r : Z ⥤ C)
    [p.IsFibered] [q.IsFibered] [r.IsFiberedInSetoids]
    (A : X ⥤ Z) (B : Y ⥤ Z)
    (hA : Functor.IsFibredOneMorphism p r A) (hB : Functor.IsFibredOneMorphism q r B)
    {F G H K : Cᵒᵖ ⥤ Type u} (a : K ⟶ F) (b : K ⟶ G)
    (f : F ⟶ H) (g : G ⟶ H)
    (eK : ∀ U, Quotient (isIsomorphicSetoid
      ((TwoFibreProductOver.structureFunctor p q r A B).Fiber U)) ≃ K.obj (op U))
    (eF : ∀ U, Quotient (isIsomorphicSetoid (p.Fiber U)) ≃ F.obj (op U))
    (eG : ∀ U, Quotient (isIsomorphicSetoid (q.Fiber U)) ≃ G.obj (op U))
    (eH : ∀ U, Quotient (isIsomorphicSetoid (r.Fiber U)) ≃ H.obj (op U))
    (ha : ∀ U c, a.app (op U) (eK U c) =
      eF U (Functor.twoFibreProductIsoClassEquivUniv hA hB U c).1.1)
    (hb : ∀ U c, b.app (op U) (eK U c) =
      eG U (Functor.twoFibreProductIsoClassEquivUniv hA hB U c).1.2)
    (hf : ∀ U c, f.app (op U) (eF U c) =
      eH U (Functor.isoClassFun hA U c))
    (hg : ∀ U c, g.app (op U) (eG U c) =
      eH U (Functor.isoClassFun hB U c)) : IsPullback a b f g := by
  apply IsPullback.iff_app.mpr
  intro U
  induction U using Opposite.rec with | _ U =>
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext t
    obtain ⟨c, rfl⟩ := (eK U).surjective t
    show f.app (op U) (a.app (op U) (eK U c)) =
      g.app (op U) (b.app (op U) (eK U c))
    rw [ha, hb, hf, hg]
    exact congrArg (eH U) (Functor.twoFibreProductIsoClassEquivUniv hA hB U c).2
  · intro t t' ht
    obtain ⟨c, rfl⟩ := (eK U).surjective t
    obtain ⟨c', rfl⟩ := (eK U).surjective t'
    apply congrArg (eK U)
    apply (Functor.twoFibreProductIsoClassEquivUniv hA hB U).injective
    apply Subtype.ext
    apply Prod.ext
    · apply (eF U).injective
      simpa only [← ha] using ht.1
    · apply (eG U).injective
      simpa only [← hb] using ht.2
  · intro x y hxy
    obtain ⟨c, rfl⟩ := (eF U).surjective x
    obtain ⟨d, rfl⟩ := (eG U).surjective y
    have hcd : Functor.isoClassFun hA U c = Functor.isoClassFun hB U d := by
      apply (eH U).injective
      simpa only [← hf, ← hg] using hxy
    obtain ⟨t, ht⟩ := (Functor.twoFibreProductIsoClassEquivUniv hA hB U).surjective ⟨(c, d), hcd⟩
    refine ⟨eK U t, ?_, ?_⟩
    · rw [ha, ht]
    · rw [hb, ht]

private theorem isPullback_representedMap
    {C : Type w} [Category.{u} C]
    {X : Type v} {Y : Type v'} {Z : Type v''}
    [Category.{u} X] [Category.{u} Y] [Category.{u} Z]
    (p : X ⥤ C) (q : Y ⥤ C) (r : Z ⥤ C)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids) [r.IsFiberedInSetoids]
    (A : X ⥤ Z) (B : Y ⥤ Z) (hA : A ⋙ r = p) (hB : B ⋙ r = q)
    (F G H K : Cᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver p (discreteProjection F))
    (eG : StacksRepresentableCFG.EquivalenceOver q (discreteProjection G))
    (eH : StacksRepresentableCFG.EquivalenceOver r (discreteProjection H))
    (eK : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.structureFunctor p q r A B) (discreteProjection K)) :
    let hK := TwoFibreProductOver.isFiberedInGroupoids p q r A B hp hq hr hA hB
    IsPullback
      (representedMap _ p hK hp K F eK eF (TwoFibreProductOver.fst p q r A B)
        TwoFibreProductOver.fst_comp_eq)
      (representedMap _ q hK hq K G eK eG (TwoFibreProductOver.snd p q r A B)
        TwoFibreProductOver.snd_comp_eq)
      (representedMap p r hp hr F H eF eH A hA)
      (representedMap q r hq hr G H eG eH B hB) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let hK := TwoFibreProductOver.isFiberedInGroupoids p q r A B hp hq hr hA hB
  let : (TwoFibreProductOver.structureFunctor p q r A B).IsFibered := hK.isFibered
  apply isPullback_of_pointwise_fiber_equiv p q r A B
    (isFibredOneMorphism_of_comp_eq hr hA)
    (isFibredOneMorphism_of_comp_eq hr hB)
    _ _ _ _ (isoClassEquiv K eK) (isoClassEquiv F eF)
    (isoClassEquiv G eG) (isoClassEquiv H eH)
  · intro U c
    obtain ⟨x, rfl⟩ := Functor.isoClassMk_surjective c
    exact representedMap_app_isoClass _ _ hK hp K F eK eF _ _ U x
  · intro U c
    obtain ⟨x, rfl⟩ := Functor.isoClassMk_surjective c
    exact representedMap_app_isoClass _ _ hK hq K G eK eG _ _ U x
  · exact representedMap_app p r hp hr F H eF eH A hA
  · exact representedMap_app q r hq hr G H eG eH B hB

private theorem representedMap_comp
    {C : Type w} [Category.{u} C]
    {X : Type v} {Y : Type v'} {Z : Type v''}
    [Category.{u} X] [Category.{u} Y] [Category.{u} Z]
    (p : X ⥤ C) (q : Y ⥤ C) (r : Z ⥤ C)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (F G H : Cᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver p (discreteProjection F))
    (eG : StacksRepresentableCFG.EquivalenceOver q (discreteProjection G))
    (eH : StacksRepresentableCFG.EquivalenceOver r (discreteProjection H))
    (A : X ⥤ Y) (B : Y ⥤ Z) (hA : A ⋙ q = p) (hB : B ⋙ r = q) :
    representedMap p q hp hq F G eF eG A hA ≫ representedMap q r hq hr G H eG eH B hB =
      representedMap p r hp hr F H eF eH (A ⋙ B) (by rw [Functor.assoc, hB, hA]) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let : r.IsFibered := hr.isFibered
  ext U c
  obtain ⟨c, rfl⟩ := (isoClassEquiv F eF U.unop).surjective c
  obtain ⟨x, rfl⟩ := Functor.isoClassMk_surjective c
  show (representedMap q r hq hr G H eG eH B hB).app U
    ((representedMap p q hp hq F G eF eG A hA).app U
      (isoClassEquiv F eF U.unop (Functor.isoClassMk p x))) =
    (representedMap p r hp hr F H eF eH (A ⋙ B) _).app U
      (isoClassEquiv F eF U.unop (Functor.isoClassMk p x))
  rw [representedMap_app_isoClass, representedMap_app_isoClass, representedMap_app_isoClass]
  rfl

private theorem representedMap_overMap
    {C : Type w} [Category.{u} C] {U V : C} (j : U ⟶ V) :
    representedMap (Over.forget U) (Over.forget V)
      (Functor.IsFiberedInGroupoids.over_forget U) (Functor.IsFiberedInGroupoids.over_forget V)
      (yoneda.obj U) (yoneda.obj V) (sliceElementsEquivalenceOver U)
      (sliceElementsEquivalenceOver V) (Over.map j) rfl = yoneda.map j := by
  let : (Over.forget U).IsFibered := (Functor.IsFiberedInGroupoids.over_forget U).isFibered
  ext T c
  obtain ⟨c, rfl⟩ :=
    (isoClassEquiv (yoneda.obj U) (sliceElementsEquivalenceOver U) T.unop).surjective c
  obtain ⟨x, rfl⟩ := Functor.isoClassMk_surjective c
  refine (representedMap_app_isoClass _ _ _ _ _ _ _ _ _ _ T.unop x).trans ?_
  induction T using Opposite.rec with | _ T =>
  obtain ⟨x, hx⟩ := x
  dsimp at hx
  subst T
  rfl

private theorem relocalizeToYoneda_elementOf
    {C : Type w} [Category.{u} C] {X V : C} (a : V ⟶ X)
    (F : (Over V)ᵒᵖ ⥤ Type u)
    (z : (presheafOfCategories (F ⋙ typeToCat)).obj)
    (t : Over V) (ht : z.base = t) (T : Over X)
    (hT : (Over.map a).obj t = T)
    (hz : ((relocalizeToElements a F).obj z).base = T) :
    discreteFiberEquiv (yoneda.obj (Over.mk a)) T
        ⟨(overMapToElements a).obj t, hT⟩ =
      (OverShriek.relocalizeToYoneda a F).app (op T)
        (discreteFiberEquiv ((OverShriek.relocalizePresheafFunctor a).obj F) T
          ⟨(relocalizeToElements a F).obj z, hz⟩) := by
  subst t
  subst T
  rfl

private theorem representedMap_relocalized_fst
    {C : Type w} [Category.{u} C] {X V : C} (a : V ⟶ X)
    {D : Type v} [Category.{u} D]
    (q : D ⥤ Over V) (_hq : q.IsFiberedInGroupoids)
    (hcomp : (q ⋙ Over.map a).IsFiberedInGroupoids)
    (F : (Over V)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver q (discreteProjection F)) :
    representedMap (q ⋙ Over.map a) (Over.map a) hcomp
      (Functor.IsFiberedInGroupoids.over_map a)
      ((OverShriek.relocalizePresheafFunctor a).obj F) (yoneda.obj (Over.mk a))
      ((e.compRight (Over.map a)).trans (relocalizeElementsEquivalenceOver a F))
      (overMapElementsEquivalenceOver a) q rfl = OverShriek.relocalizeToYoneda a F := by
  let : (q ⋙ Over.map a).IsFibered := hcomp.isFibered
  ext T c
  obtain ⟨c, rfl⟩ := (isoClassEquiv _
    ((e.compRight (Over.map a)).trans (relocalizeElementsEquivalenceOver a F)) T.unop).surjective c
  obtain ⟨x, rfl⟩ := Functor.isoClassMk_surjective c
  refine (representedMap_app_isoClass _ _ _ _ _ _ _ _ _ _ T.unop x).trans ?_
  apply relocalizeToYoneda_elementOf a F (e.hom.functor.obj x.1) (q.obj x.1)
    (Functor.congr_obj e.hom.w x.1) T.unop


private theorem representedMap_relocalized_fst_ofEq
    {C : Type w} [Category.{u} C] {X V : C} (a : V ⟶ X)
    {D : Type v} [Category.{u} D]
    (q : D ⥤ Over V) (p : D ⥤ Over X) (h : q ⋙ Over.map a = p)
    (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (F : (Over V)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver q (discreteProjection F)) :
    representedMap p (Over.map a) hp (Functor.IsFiberedInGroupoids.over_map a)
      ((OverShriek.relocalizePresheafFunctor a).obj F) (yoneda.obj (Over.mk a))
      (((e.compRight (Over.map a)).trans (relocalizeElementsEquivalenceOver a F)).ofEq h)
      (overMapElementsEquivalenceOver a) q h = OverShriek.relocalizeToYoneda a F := by
  subst p
  exact representedMap_relocalized_fst a q hq hp F e

private theorem overForget_isFiberedInSetoids
    {C : Type w} [Category.{u} C] (W : C) : (Over.forget W).IsFiberedInSetoids := by
  refine ⟨Functor.IsFiberedInGroupoids.over_forget W, ?_⟩
  intro T x y
  refine ⟨fun f g => ?_⟩
  apply Functor.Fiber.hom_ext
  apply Over.OverMorphism.ext
  have hf := f.2
  have hg := g.2
  exact (IsHomLift.fac' (Over.forget W) (𝟙 T) f.1).trans
    (IsHomLift.fac' (Over.forget W) (𝟙 T) g.1).symm

private def relocalizedSndMap
    {C : Type (u + 1)} [Category.{u} C] {S V : C} (a : V ⟶ S)
    {X : Type v} [Category.{vX} X]
    (p : X ⥤ Over S) (hp : p.IsFiberedInGroupoids)
    (W : Over S) (g : Over W ⥤ X) (hg : g ⋙ p = Over.forget W)
    (y : Over V ⥤ X) (hy : y ⋙ p = Over.map a)
    (F : (Over V)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map a) (Over.forget W) p y g) (discreteProjection F)) :
    (OverShriek.relocalizePresheafFunctor a).obj F ⟶ yoneda.obj W :=
  let hF := TwoFibreProductOver.isFiberedInGroupoids (Over.map a) (Over.forget W) p y g
    (Functor.IsFiberedInGroupoids.over_map a) (Functor.IsFiberedInGroupoids.over_forget W) hp hy hg
  let eF' := ((eF.compRight (Over.map a)).trans
    (relocalizeElementsEquivalenceOver a F)).ofEq TwoFibreProductOver.fst_comp_eq
  representedMap _ (Over.forget W) hF (Functor.IsFiberedInGroupoids.over_forget W)
    _ _ eF' (sliceElementsEquivalenceOver W)
    (TwoFibreProductOver.snd (Over.map a) (Over.forget W) p y g) TwoFibreProductOver.snd_comp_eq

private theorem exists_pullback_relocalized_composite
    {C : Type (u + 1)} [Category.{u} C] {S V : C} (a : V ⟶ S)
    {X : Type v} [Category.{vX} X]
    (p : X ⥤ Over S) (hp : p.IsFiberedInGroupoids)
    {U W : Over S} (j : U ⟶ W)
    (g : Over W ⥤ X) (hg : g ⋙ p = Over.forget W)
    (y : Over V ⥤ X) (hy : y ⋙ p = Over.map a)
    (F G : (Over V)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map a) (Over.forget W) p y g) (discreteProjection F))
    (eG : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map a) (Over.forget U) p y (Over.map j ⋙ g))
      (discreteProjection G)) :
    ∃ (l : (OverShriek.relocalizePresheafFunctor a).obj G ⟶
        (OverShriek.relocalizePresheafFunctor a).obj F)
      (r : (OverShriek.relocalizePresheafFunctor a).obj G ⟶ yoneda.obj U),
      IsPullback l r (relocalizedSndMap a p hp W g hg y hy F eF) (yoneda.map j) ∧
      l ≫ OverShriek.relocalizeToYoneda a F = OverShriek.relocalizeToYoneda a G := by
  let pV := Over.map a
  let pU := Over.forget U
  let pW := Over.forget W
  let pF := TwoFibreProductOver.structureFunctor pV pW p y g
  let qF := TwoFibreProductOver.fst pV pW p y g
  let sF := TwoFibreProductOver.snd pV pW p y g
  let hpV := Functor.IsFiberedInGroupoids.over_map a
  let hpU := Functor.IsFiberedInGroupoids.over_forget U
  let hpW := Functor.IsFiberedInGroupoids.over_forget W
  let hpF := TwoFibreProductOver.isFiberedInGroupoids pV pW p y g hpV hpW hp hy hg
  have hqF : qF.IsFiberedInGroupoids := by
    apply (Functor.isFiberedInGroupoids_comp_overMap_iff a qF).mp
    show (qF ⋙ pV).IsFiberedInGroupoids
    rw [TwoFibreProductOver.fst_comp_eq]
    exact hpF
  let pK := TwoFibreProductOver.structureFunctor pF pU pW sF (Over.map j)
  let kF := TwoFibreProductOver.fst pF pU pW sF (Over.map j)
  let kU := TwoFibreProductOver.snd pF pU pW sF (Over.map j)
  let qK := kF ⋙ qF
  have hKq : qK ⋙ pV = pK := by
    dsimp only [qK]
    rw [Functor.assoc, TwoFibreProductOver.fst_comp_eq, TwoFibreProductOver.fst_comp_eq]
  let hpK := TwoFibreProductOver.isFiberedInGroupoids pF pU pW sF (Over.map j)
    hpF hpU hpW TwoFibreProductOver.snd_comp_eq rfl
  have hqK : qK.IsFiberedInGroupoids := by
    apply (Functor.isFiberedInGroupoids_comp_overMap_iff a qK).mp
    show (qK ⋙ pV).IsFiberedInGroupoids
    rw [hKq]
    exact hpK
  have hqG : (TwoFibreProductOver.fst pV pU p y (Over.map j ⋙ g)).IsFiberedInGroupoids := by
    apply (Functor.isFiberedInGroupoids_comp_overMap_iff a _).mp
    rw [TwoFibreProductOver.fst_comp_eq]
    exact TwoFibreProductOver.isFiberedInGroupoids pV pU p y (Over.map j ⋙ g)
      hpV hpU hp hy (by rw [Functor.assoc, hg]; rfl)
  obtain ⟨e⟩ := TwoFibreProductOver.nonempty_equivalenceOver_splitSnd pV pU pW p
    y (Over.map j) g rfl hg hqG hqK
  let eKF := e.symm.trans eG
  let eF' := ((eF.compRight pV).trans (relocalizeElementsEquivalenceOver a F)).ofEq
    TwoFibreProductOver.fst_comp_eq
  let eK := ((eKF.compRight pV).trans (relocalizeElementsEquivalenceOver a G)).ofEq hKq
  let l := representedMap pK pF hpK hpF _ _ eK eF' kF TwoFibreProductOver.fst_comp_eq
  let r := representedMap pK pU hpK hpU _ _ eK (sliceElementsEquivalenceOver U)
    kU TwoFibreProductOver.snd_comp_eq
  refine ⟨l, r, ?_, ?_⟩
  · let : pW.IsFiberedInSetoids := overForget_isFiberedInSetoids W
    have hpb := isPullback_representedMap pF pU pW hpF hpU hpW
      sF (Over.map j) TwoFibreProductOver.snd_comp_eq rfl
      _ _ _ _ eF' (sliceElementsEquivalenceOver U) (sliceElementsEquivalenceOver W) eK
    simpa only [pU, pW, representedMap_overMap, l, r, relocalizedSndMap,
      pF, pV, sF, eF', hpF, hpV, hpW, pK, kF, kU] using hpb
  · have hbF := representedMap_relocalized_fst_ofEq a qF pF
      TwoFibreProductOver.fst_comp_eq hqF hpF F eF
    rw [← hbF]
    show l ≫ representedMap pF pV hpF hpV _ _ eF' (overMapElementsEquivalenceOver a)
      qF TwoFibreProductOver.fst_comp_eq = _
    rw [representedMap_comp]
    exact representedMap_relocalized_fst_ofEq a qK pK hKq hqK hpK G eKF


end RepresentedMaps

private theorem mono_of_openImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : Space.IsOpenImmersion B S hS f) : Mono f := by
  apply MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
  apply MorphismProperty.relative_monotone (P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
    (P' := MorphismProperty.monomorphisms _) _ _ hf
  intro U V g hg
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : AlgebraicGeometry.IsOpenImmersion (T.map g) := hg
  exact T.mono_of_mono_map inferInstance

private theorem isSmoothAt_of_openImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (q : F ⟶ X) (hq : Space.IsOpenImmersion B S hS q)
    (f : X ⟶ Y) (hf : AlgebraicGeometry.Space.IsSmooth B S hS (q ≫ f))
    (x : AlgebraicGeometry.Space.points B S hS F) :
    AlgebraicGeometry.Space.IsSmoothAt B S hS f (Space.pointsMap B S hS F q x) := by
  let : Mono q := mono_of_openImmersion B S hS q hq
  let e := asIso (Subfunctor.toRange q)
  have he : e.inv ≫ q = (Subfunctor.range q).ι := by
    calc
      e.inv ≫ q = e.inv ≫ (e.hom ≫ (Subfunctor.range q).ι) :=
        congrArg (fun t => e.inv ≫ t) (Subfunctor.toRange_ι q).symm
      _ = (Subfunctor.range q).ι := by simp
  refine ⟨Subfunctor.range q, ⟨AlgebraicGeometry.Space.isAlgebraicSpace_of_iso B S hS e hF, ?_⟩,
    Space.pointsMap B S hS F e.hom x, ?_, ?_⟩
  · rw [← he]
    exact MorphismProperty.RespectsIso.precomp _ e.inv q hq
  · rw [← Space.pointsMap_comp_apply]
    rfl
  · rw [← he, Category.assoc]
    exact Space.isSmooth_precomp_iso B S hS e.symm (q ≫ f) hf


private theorem isSmooth_of_openImmersion_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type v} (F : I → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (F i))
    (q : ∀ i, F i ⟶ X)
    (hq : ∀ i, Space.IsOpenImmersion B S hS (q i))
    (hcover : ∀ x : AlgebraicGeometry.Space.points B S hS X, ∃ i y,
      Space.pointsMap B S hS (F i) (q i) y = x)
    (hsmooth : ∀ i, AlgebraicGeometry.Space.IsSmooth B S hS (q i ≫ f)) :
    AlgebraicGeometry.Space.IsSmooth B S hS f := by
  apply ((AlgebraicGeometry.Space.isSmooth_tfae B S hS hX hY f).out 1 2).mpr
  intro x
  obtain ⟨i, y, rfl⟩ := hcover x
  exact isSmoothAt_of_openImmersion B S hS (hF i) (q i) (hq i) f (hsmooth i) y

private theorem points_cover_of_pullback_of_scheme_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} (U : I → AlgebraicGeometry.BigFppfOver B S hS)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (j : ∀ i, U i ⟶ W)
    (hj : ∀ i, AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (j i)))
    (hcover : ∀ w : W.left.1, ∃ i u,
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (j i)) u = w)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (G : I → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : F ⟶ yoneda.obj W) (a : ∀ i, G i ⟶ F)
    (b : ∀ i, G i ⟶ yoneda.obj (U i))
    (hpb : ∀ i, IsPullback (a i) (b i) p (yoneda.map (j i))) :
    ∀ x : AlgebraicGeometry.Space.points B S hS F, ∃ i y,
      Space.pointsMap B S hS (G i) (a i) y = x := by
  intro x
  induction x using Quot.inductionOn with | h x =>
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let f : x.siteObject ⟶ W := p.app (Opposite.op x.siteObject) x.value
  obtain ⟨i, u, hu⟩ := hcover ((T.map f) (IsLocalRing.closedPoint x.carrier))
  let : AlgebraicGeometry.IsOpenImmersion (T.map (j i)) := hj i
  let : Field x.carrier := x.field
  have hr : Set.range (T.map f) ⊆ Set.range (T.map (j i)) := by
    rintro _ ⟨t, rfl⟩
    have ht : t = IsLocalRing.closedPoint x.carrier :=
      @Subsingleton.elim (PrimeSpectrum x.carrier) inferInstance t _
    rw [ht]
    exact ⟨u, hu⟩
  let l := IsOpenImmersion.lift (T.map (j i)) (T.map f) hr
  have hl : l ≫ T.map (j i) = T.map f := IsOpenImmersion.lift_fac _ _ hr
  let k : x.siteObject ⟶ U i := Over.homMk (ObjectProperty.homMk l) (by
    apply B.inclusion.map_injective
    show l ≫ B.inclusion.map (U i).hom = B.inclusion.map x.siteObject.hom
    have hjw := congrArg B.inclusion.map (j i).w
    have hfw := congrArg B.inclusion.map f.w
    change T.map (j i) ≫ B.inclusion.map W.hom = B.inclusion.map (U i).hom at hjw
    change T.map f ≫ B.inclusion.map W.hom = B.inclusion.map x.siteObject.hom at hfw
    rw [← hjw, ← Category.assoc, hl, hfw])
  have hk : k ≫ j i = f := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hl)
  obtain ⟨z, hz, _⟩ := (Types.isPullback_iff _ _ _ _).mp
    ((IsPullback.iff_app.mp (hpb i)) (Opposite.op x.siteObject)) |>.2.2 x.value k hk.symm
  let y : Space.FieldValuedPoint B S hS (G i) :=
    { carrier := x.carrier, contained := x.contained, toBase := x.toBase, value := z }
  refine ⟨i, y.class, ?_⟩
  show Quot.mk _ (Space.FieldValuedPoint.map B S hS _ (a i) y) = Quot.mk _ x
  congr 1
  cases x
  dsimp [y, Space.FieldValuedPoint.map] at hz ⊢
  congr


section RelativeSmooth

open CategoryTheory.PresheafOfCategories Opposite

private theorem isSmooth_relocalized_of_open_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{vX} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (W : AlgebraicGeometry.BigFppfOver B S hS)
    (g : Over W ⥤ X) (hg : g ⋙ p = Over.forget W)
    {I : Type u} (U : I → AlgebraicGeometry.BigFppfOver B S hS) (j : ∀ i, U i ⟶ W)
    (hj : ∀ i, AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (j i)))
    (hcover : ∀ w : W.left.1, ∃ i u,
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (j i)) u = w)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ X)
    (hy : y ⋙ p = Over.map V.hom)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2 F)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) (Over.forget W) p y g) (discreteProjection F))
    (hcharts : ∀ i, ∃ (G : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (_hG : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) (Over.forget (U i)) p y (Over.map (j i) ⋙ g))
        (discreteProjection G)) ∧
        AlgebraicGeometry.Space.IsSmooth B S hS (OverShriek.relocalizeToYoneda V.hom G)) :
    AlgebraicGeometry.Space.IsSmooth B S hS (OverShriek.relocalizeToYoneda V.hom F) := by
  classical
  choose G hG eG hsm using hcharts
  choose l r hpb hl using fun i => exists_pullback_relocalized_composite V.hom p hp
    (j i) g hg y hy F (G i) eF (eG i).some
  let LF := (OverShriek.relocalizePresheafFunctor V.hom).obj F
  let LG i := (OverShriek.relocalizePresheafFunctor V.hom).obj (G i)
  have hLF : AlgebraicGeometry.IsAlgebraicSpace B S hS LF :=
    AlgebraicGeometry.Space.isAlgebraicSpace_of_iso B S hS
      ((spacesOverSmallerBaseFunctorForgetIso
        B V.left.1 S V.left.2 hS V.hom).app ⟨F, hF⟩)
    ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩).property
  have hLG i : AlgebraicGeometry.IsAlgebraicSpace B S hS (LG i) :=
    AlgebraicGeometry.Space.isAlgebraicSpace_of_iso B S hS
      ((spacesOverSmallerBaseFunctorForgetIso
        B V.left.1 S V.left.2 hS V.hom).app ⟨G i, hG i⟩)
    ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G i, hG i⟩).property
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let := schemeBelow_closed_under_isomorphisms B
  let := schemeBelow_closed_under_pullbacks B
  let P : MorphismProperty (AlgebraicGeometry.BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u}) T
  let : P.IsStableUnderBaseChange := ⟨fun sq h =>
    MorphismProperty.of_isPullback
      (P := (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u}))
      (sq.map T) h⟩
  let : P.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  have hopen i : Space.IsOpenImmersion B S hS (l i) :=
    MorphismProperty.of_isPullback (P := P.presheaf) (hpb i).flip
      (MorphismProperty.relative_map (hj i))
  apply isSmooth_of_openImmersion_cover B S hS hLF
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) _ LG hLG l hopen
  · exact points_cover_of_pullback_of_scheme_cover B S hS U W j hj hcover LG
      (relocalizedSndMap V.hom p hp W g hg y hy F eF) l r hpb
  · intro i
    rw [hl]
    exact hsm i

private theorem isSmooth_algebraicSpaceMap_iff_relocalized
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2 F) :
    AlgebraicGeometry.Space.IsSmooth B S hS
      (AlgebraicGeometry.algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor
          B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom ↔
    AlgebraicGeometry.Space.IsSmooth B S hS (OverShriek.relocalizeToYoneda V.hom F) := by
  let G := (spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩
  let e : G.1.left ≅ (OverShriek.relocalizePresheafFunctor V.hom).obj F :=
    (spacesOverSmallerBaseFunctorForgetIso B V.left.1 S V.left.2 hS V.hom).app ⟨F, hF⟩
  have he : e.inv ≫ G.1.hom = OverShriek.relocalizeToYoneda V.hom F := by
    ext T s
    exact spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
      B V.left.1 S V.left.2 hS V.hom ⟨F, hF⟩ T s
  show AlgebraicGeometry.Space.IsSmooth B S hS G.1.hom ↔ _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← he]
    exact Space.isSmooth_precomp_iso B S hS e.symm G.1.hom h
  · have he' : G.1.hom = e.hom ≫ OverShriek.relocalizeToYoneda V.hom F := by
      rw [← he]
      simp
    rw [he']
    exact Space.isSmooth_precomp_iso B S hS e _ h

end RelativeSmooth

end AlgebraicGeometry.Stack

end
