module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.InducedProperty
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.SpecResidueFieldClosedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonalEquiv
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSliceProduct
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Predeformation.FibreProduct
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FiniteResidueFieldExtension
public import StacksFrontier.Deformation.Artin.Versality.SmoothPredeformation
public import StacksFrontier.Deformation.ArtinCriteria.Versality
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange.LocallyFiniteType
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange.ResidueFieldPoints
import all StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange.DeformationLifting
import all StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange.LocallyFiniteType

/-!
# Smoothness of a base change of a versal object

Let an object over a locally finite type scheme be versal at a point. If the
diagonal of its fibred category is representable and locally of finite type,
and the category satisfies (RS), then its fibre product with any other object
is smooth over the latter's base at each finite type point lying over the
versal point.

## Main results

* `Deformation.Artin.BaseChange.isSmoothAt_baseChange_of_isVersalAt` gives the smoothness claim.

## Implementation notes

The local finite type condition on the diagonal is tested on the algebraic
spaces representing its isomorphism sheaves.
The two-fibre product is represented over the base of the second object, so
its structural map is the map to the terminal presheaf. The
point lying over `u₀` is tested through the first projection of the fibre
product, transported by the chosen equivalence with its representing space.
Objects are expressed by their 2-Yoneda morphisms; this includes the
canonical 2-Yoneda morphism attached to an object over a scheme.

## References

* [Stacks Project, Tag 0CXM](https://stacks.math.columbia.edu/tag/0CXM)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin.BaseChange

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

-- The slice functor `Over.post`, fibres of a functor, their inclusion and formation, the
-- pullback functors of a choice of pullbacks and the slice functor of a 2-Yoneda lift are plain
-- `def`s, so goals mentioning an object of a fibre, or an object of the site read in `Over S`,
-- are not type-correct at `implicit` transparency.  Naming them here is what lets `rw`,
-- `simp only` and instance search see through exactly these and nothing else.
attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor
  CategoryTheory.Functor.TwoYoneda.liftBased
  CategoryTheory.Functor.TwoYoneda.liftFunctor
  CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.id
  CategoryTheory.TwoFibreProductOver.fst
  CategoryTheory.TwoFibreProductOver.snd
  CategoryTheory.TwoFibreProductOver.structureFunctor
  CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc
  CategoryTheory.Pseudofunctor.CoGrothendieck.forget
  AlgebraicGeometry.Space.FieldValuedPoint.map
  AlgebraicGeometry.Space.schemePoint
  CategoryTheory.Bicategory.InducedBicategory

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
    (AlgebraicGeometry.BigFppfOver B S hS))

attribute [local instance] schemeCutoff_isClosedUnderIsomorphisms

attribute [local instance] AlgebraicGeometry.Space.schemeCutoff_hasPullbacks
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

attribute [local instance] predeformationCarrierCategory

attribute [local instance] baseChangeProductCategory

/-- The 2-Yoneda lift of an object `x` of the fibre of `𝒳` over `U`: the scheme-valued point
of `𝒳` with values in `U` that `x` names.

The ascription to `Over U ⥤ 𝒳.val.obj` is load-bearing and must not be inlined away: the source
of `CategoryTheory.Functor.TwoYoneda.liftBased` carries the `CategoryTheory.Category` instance
`(CategoryTheory.BasedCategory.ofFunctor (Over.forget U)).category`, which is the standard
instance on `Over U` only after `CategoryTheory.BasedCategory.ofFunctor` is unfolded.  Without
the ascription the two spellings reach
`CategoryTheory.TwoFibreProductOver.instIsEquivalenceProdDiagComparison` as different terms and
instance search fails, since it does not unfold a plain `def`. -/
private noncomputable abbrev twoYonedaLift (U : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U) : Over U ⥤ 𝒳.val.obj :=
  (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩).toFunctor

open TwoFibreProductOver TwoFibreProductOver.DiagonalFibre in
/-- Given a representation `e` of the 2-fibre
product `(Sch/V) ×_𝒳 (Sch/U)` by the presheaf `F` over the big fppf site of `V`, there is a
scheme-valued point `Y` of `𝒳 ×_S 𝒳` with values in `T₀ = V ×_S U` whose 2-fibre product with
the diagonal of `𝒳`, read over the big fppf site of `V` through the first projection
`T₀ ⟶ V`, is the category of elements of `F`.

The point is the pair `(y|_{T₀}, x|_{T₀})`, obtained by composing the comparison
`𝒞_{T₀} ≃ 𝒞_V ×_{𝒞_S} (𝒞_S/U)` of `sliceProdCmp` with the product 1-morphism
`y × x`.  That the 2-fibre product of that point with the diagonal is `(Sch/V) ×_𝒳 (Sch/U)`
is Stacks 02XE over the site, in the form
`CategoryTheory.TwoFibreProductOver.prodDiagComparison` precomposed with
`CategoryTheory.TwoFibreProductOver.precomposeFst`; both commute with the first projection to
`𝒞_V` on the nose, so the comparison is an equivalence *over* `𝒞_V` and composes with `e`. -/
private lemma exists_point
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (hy : y ⋙ 𝒳.val.p = Over.map V.hom)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F) :
    ∃ (Y : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
          (prodObj B S hS U V).left.2 ⥤ Prod' 𝒳.val.p)
        (_hY : Y ⋙ ProdP 𝒳.val.p = Over.map (prodObj B S hS U V).hom),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map (prodObj B S hS U V).hom) 𝒳.val.p
              (ProdP 𝒳.val.p) Y (Diag 𝒳.val.p) ⋙
            Over.map (prodFst B S hS U V))
          (presheafOfCategories (F ⋙ typeToCat)).p) := by
  have hw : twoYonedaLift B S hS 𝒳 U x hx ⋙ 𝒳.val.p = Over.forget U :=
    (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩).w
  have ht : sliceProdCmp B S hS U V ⋙ structureFunctor (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U) =
      Over.map (prodObj B S hS U V).hom := sliceProdCmp_comp_structureFunctor B S hS U V
  refine ⟨sliceProdCmp B S hS U V ⋙
    prodMap y (twoYonedaLift B S hS 𝒳 U x hx) hy hw, ht, ?_⟩
  have hpZ : (structureFunctor (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom)
      (Over.forget U)).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
      (Functor.IsFiberedInGroupoids.over_map V.hom)
      (Functor.IsFiberedInGroupoids.over_forget U)
      Functor.isFiberedInGroupoids_id rfl rfl
  have hcmp := TwoFibreProductOver.isEquivalence_precomposeFst
    (Over.map (prodObj B S hS U V).hom)
    (structureFunctor (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U))
    𝒳.val.p (ProdP 𝒳.val.p) (prodMap y (twoYonedaLift B S hS 𝒳 U x hx) hy hw)
    (Diag 𝒳.val.p) (sliceProdCmp B S hS U V) ht
    𝒳.isFiberedInGroupoids
    (Functor.IsFiberedInGroupoids.over_map (prodObj B S hS U V).hom) hpZ
    (isEquivalence_sliceProdCmp B S hS U V) rfl
  have hPhi := ((@Functor.asEquivalence _ _ _ _ _ hcmp).trans (@Functor.asEquivalence _ _ _ _ _
    (TwoFibreProductOver.instIsEquivalenceProdDiagComparison y
      (twoYonedaLift B S hS 𝒳 U x hx) hy hw))).isEquivalence_functor
  have hProdP : (ProdP 𝒳.val.p).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids 𝒳.val.p 𝒳.val.p (𝟭 _) 𝒳.val.p 𝒳.val.p
      𝒳.isFiberedInGroupoids 𝒳.isFiberedInGroupoids Functor.isFiberedInGroupoids_id rfl rfl
  have hfstT : (TwoFibreProductOver.fst (Over.map (prodObj B S hS U V).hom) 𝒳.val.p
      (ProdP 𝒳.val.p) (sliceProdCmp B S hS U V ⋙
        prodMap y (twoYonedaLift B S hS 𝒳 U x hx) hy hw)
      (Diag 𝒳.val.p)).IsFiberedInGroupoids := by
    refine (Functor.isFiberedInGroupoids_comp_overMap_iff (prodObj B S hS U V).hom _).1 ?_
    rw [TwoFibreProductOver.fst_comp_eq]
    exact TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
      (Functor.IsFiberedInGroupoids.over_map (prodObj B S hS U V).hom)
      𝒳.isFiberedInGroupoids hProdP ht rfl
  have h1 := Functor.IsFiberedInGroupoids.comp _ (Over.map (prodFst B S hS U V)) hfstT
    (Functor.IsFiberedInGroupoids.over_map (prodFst B S hS U V))
  have h2 : (TwoFibreProductOver.fst (Over.map V.hom) (Over.forget U) 𝒳.val.p y
      (twoYonedaLift B S hS 𝒳 U x hx)).IsFiberedInGroupoids := by
    refine (Functor.isFiberedInGroupoids_comp_overMap_iff V.hom _).1 ?_
    rw [TwoFibreProductOver.fst_comp_eq]
    exact TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
      (Functor.IsFiberedInGroupoids.over_map V.hom)
      (Functor.IsFiberedInGroupoids.over_forget U) 𝒳.isFiberedInGroupoids hy hw
  refine (StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h1 h2 _ ?_
    hPhi).map (fun k => k.trans e)
  rw [← sliceProdCmp_comp_fst B S hS U V]
  rfl

open TwoFibreProductOver TwoFibreProductOver.DiagonalFibre in
-- This lemma and the `sliceProdCmp` chain above are the over-the-site form of Stacks 045G.
/-- If the diagonal of `𝒳` is representable by
algebraic spaces, if every algebraic space representing an isomorphism presheaf of `𝒳` is
locally of finite type over its base, if the structure morphism of `U` is locally of finite
type, and if the presheaf `F` on the big fppf site of `V` represents the 2-fibre product
`(Sch/V) ×_{y, 𝒳, x} (Sch/U)`, then `F` is locally of finite type over `V`. -/
private lemma isLocallyOfFiniteType_twoFibreProduct_of_baseChangeEquiv
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hΔlft :
      letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
        (a b : 𝒳.val.p.Fiber T)
        (G : (AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
        AlgebraicGeometry.IsAlgebraicSpace B T.left.1 T.left.2 G →
        Nonempty (G ⋙ uliftFunctor.{v, u} ≅
          ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
            uliftFunctor.{u, v}) →
        AlgebraicGeometry.Space.IsLocallyOfFiniteType B T.left.1 T.left.2
          (terminal.from G : G ⟶
            ⊤_ ((AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)))
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map U.hom)]
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (hy : y ⋙ 𝒳.val.p = Over.map V.hom)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F) :
    AlgebraicGeometry.Space.IsLocallyOfFiniteType B V.left.1 V.left.2
      (terminal.from F : F ⟶ ⊤_ ((AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) :=
  isLocallyOfFiniteType_of_exists_point B S hS 𝒳 hΔ hΔlft U V F
    (exists_point B S hS 𝒳 U V x hx y hy F e)

/-- **Stacks 0CXM.** Let `𝒳` be a category fibred in groupoids over the big fppf site of a
locally Noetherian scheme `S`, let `x` be an object of `𝒳` over a scheme `U` locally of finite
type over `S`, and let `u₀` be a finite type point of `U`.  Assume the diagonal of `𝒳` is
representable by algebraic spaces and locally of finite type, and that `𝒳` satisfies (RS).
Let `V` be a scheme locally of finite type over `S`, let `y` be an object of `𝒳` over `V`, let
`F` be the algebraic space representing the 2-fibre product
`𝒵 = (Sch/V)_{fppf} ×_𝒳 (Sch/U)_{fppf}` over `V`, and let `z₀` be a finite type point of `F`
lying over `u₀`.  If `x` is versal at `u₀`, then `F ⟶ V` is smooth at `z₀`. -/
@[stacks 0CXM]
public theorem isSmoothAt_baseChange_of_isVersalAt
    [IsLocallyNoetherian S]
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hΔlft :
      letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
        (a b : 𝒳.val.p.Fiber T)
        (G : (AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
        AlgebraicGeometry.IsAlgebraicSpace B T.left.1 T.left.2 G →
        Nonempty (G ⋙ uliftFunctor.{v, u} ≅
          ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
            uliftFunctor.{u, v}) →
        AlgebraicGeometry.Space.IsLocallyOfFiniteType B T.left.1 T.left.2
          (terminal.from G : G ⟶
            ⊤_ ((AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)))
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p
      𝒳.isFiberedInGroupoids)
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map U.hom)]
    [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (u₀ : U.left.1)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (hy : y ⋙ 𝒳.val.p = Over.map V.hom)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2 F)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (z₀ : AlgebraicGeometry.Space.FieldValuedPoint B V.left.1 V.left.2 F)
    (hz₀ : AlgebraicGeometry.Space.IsFiniteTypePoint B V.left.1 V.left.2 F
      (z₀.class B V.left.1 V.left.2 F))
    (hzu :
      letI : Category (TwoFibreProductOver (Over.map V.hom)
        (Over.forget U) 𝒳.val.p y
        (Functor.TwoYoneda.liftBased 𝒳.val.p
          𝒳.isFiberedInGroupoids U ⟨x, hx⟩).toFunctor) :=
            TwoFibreProductOver.instCategory
      let P := e.inv.functor.obj ⟨z₀.siteObject, Discrete.mk z₀.value⟩
      ∃ hP : P.x = z₀.siteObject,
        (B.inclusion.map
          ((eqToHom (P.hx.trans P.hy.symm) ≫ P.y.hom).left))
          ((B.inclusion.map (eqToHom (congrArg Over.left hP).symm))
            (IsLocalRing.closedPoint z₀.carrier)) = u₀)
    (hversal : Deformation.Artin.IsVersalAt (Over.mk (B.inclusion.map U.hom))
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x
      (by simpa using congrArg (Over.post B.inclusion).obj hx)) :
    AlgebraicGeometry.Space.IsSmoothAt B V.left.1 V.left.2
      (terminal.from F : F ⟶
        ⊤_ ((AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u))
      (z₀.class B V.left.1 V.left.2 F) := by
  subst U
  let U := 𝒳.val.p.obj x
  have hx : 𝒳.val.p.obj x = 𝒳.val.p.obj x := rfl
  let : Category (TwoFibreProductOver (Over.map V.hom)
      (Over.forget U) 𝒳.val.p y
      (Functor.TwoYoneda.liftBased 𝒳.val.p
        𝒳.isFiberedInGroupoids U ⟨x, hx⟩).toFunctor) :=
    TwoFibreProductOver.instCategory
  obtain ⟨p, hpclass, hplft⟩ := hz₀
  obtain ⟨W, aW, q, haW, hcclosed, hmaps⟩ :=
    (AlgebraicGeometry.Space.isFiniteTypePoint_iff_exists_isClosed_etaleChart
      B V.left.1 V.left.2 F hF (p.class B V.left.1 V.left.2 F)).mp ⟨p, rfl, hplft⟩
  let c' : AlgebraicGeometry.Space.EtaleChartAtPoint B V.left.1 V.left.2
      (terminal.from F) (z₀.class B V.left.1 V.left.2 F) :=
    { U := W
      V := Over.mk (𝟙 (B.obj V.left.2))
      a := aW
      b := (terminalYonedaIso B V.left.1 V.left.2).hom
      h := Over.homMk W.hom (by simp)
      a_etale := etale_presheaf_of_isEtale B V.left.1 V.left.2 aW haW
      b_etale := terminalYonedaIso_etale B V.left.1 V.left.2
      comm := terminal.hom_ext _ _
      representative := q
      point := IsLocalRing.closedPoint q.carrier
      maps_to := hmaps.trans hpclass }
  have hcfinite : AlgebraicGeometry.IsFiniteTypePoint
      (c'.sourcePoint B V.left.1 V.left.2) := finiteTypePoint_of_isClosed hcclosed
  have hcscheme : AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U
      c'.representative = c'.sourcePoint B V.left.1 V.left.2 :=
    congrArg ((AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).map
      c'.representative.value)
      (show IsLocalRing.closedPoint c'.representative.carrier = c'.point from
        Subsingleton.elim _ _)
  have hcfield : B.Contains (Spec (c'.U.left.1.residueField
      (AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U c'.representative))) :=
    contains_specResidueField B c'.U.left.1 c'.U.left.2 _
      (hcscheme.symm ▸ hcfinite)
  let d := residueFieldChart B V.left.1 V.left.2 c' hcfield
  have hdpoint : d.sourcePoint B V.left.1 V.left.2 =
      c'.sourcePoint B V.left.1 V.left.2 :=
    residueFieldChart_sourcePoint B V.left.1 V.left.2 c' hcfield
  have hdfinite : AlgebraicGeometry.IsFiniteTypePoint
      (d.sourcePoint B V.left.1 V.left.2) := hdpoint.symm ▸ hcfinite
  let η := baseChangeProjection B S hS 𝒳 U V x hx y F e
  have hzπ : B.inclusion.map
      (η.app ⟨z₀.siteObject, Discrete.mk z₀.value⟩).left
      (IsLocalRing.closedPoint z₀.carrier) = u₀ := by
    obtain ⟨hP, hpoint⟩ := hzu
    exact (baseChangeProjection_point B S hS 𝒳 U V x hx y F e z₀ hP).trans hpoint
  have hcπ : B.inclusion.map
      (η.app ⟨c'.U, Discrete.mk (c'.a.app (Opposite.op c'.U) (𝟙 c'.U))⟩).left
      (c'.sourcePoint B V.left.1 V.left.2) = u₀ := by
    have hcommon := chartRepresentative_hasCommonExtension
      B V.left.1 V.left.2 (terminal.from F)
        (z₀.class B V.left.1 V.left.2 F) c' z₀ rfl
    have heq := projection_point_eq_of_commonExtension B S hS U V F η
      (AlgebraicGeometry.Space.FieldValuedPoint.map B V.left.1 V.left.2
        (yoneda.obj c'.U) c'.a c'.representative) z₀ hcommon
    have hpoint : c'.point = IsLocalRing.closedPoint c'.representative.carrier :=
      Subsingleton.elim _ _
    change B.inclusion.map
      (η.app ⟨c'.U, Discrete.mk (c'.a.app (Opposite.op c'.U) (𝟙 c'.U))⟩).left
      (B.inclusion.map c'.representative.value.left c'.point) = u₀
    rw [hpoint]
    exact (projection_point_eq_chartPoint B S hS U V F η c'.U c'.a
      c'.representative).symm.trans (heq.trans hzπ)
  have hdπ : B.inclusion.map
      (η.app ⟨d.U, Discrete.mk (d.a.app (Opposite.op d.U) (𝟙 d.U))⟩).left
      (d.sourcePoint B V.left.1 V.left.2) = u₀ := by
    rwa [hdpoint]
  let p₀ := AlgebraicGeometry.Space.FieldValuedPoint.map B V.left.1 V.left.2
    (yoneda.obj d.U) d.a d.representative
  let P₀ := e.inv.functor.obj ⟨p₀.siteObject, Discrete.mk p₀.value⟩
  have hP₀ : P₀.x = p₀.siteObject :=
    congrArg (fun G => G.obj ⟨p₀.siteObject, Discrete.mk p₀.value⟩) e.inv.w
  have hp₀π : B.inclusion.map
      (η.app ⟨p₀.siteObject, Discrete.mk p₀.value⟩).left
      (IsLocalRing.closedPoint p₀.carrier) = u₀ :=
    (projection_point_eq_chartPoint B S hS U V F η d.U d.a d.representative).trans hdπ
  obtain ⟨R, iR, aR, hiR, hfactor⟩ := exists_affineOpen_fieldPointFactorization
    (p₀.toBase ≫ B.inclusion.map V.hom)
  let : Algebra R p₀.carrier := aR
  have hP₀base : (Over.map V.hom ⋙ Over.post B.inclusion).obj P₀.x =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R p₀.carrier)) ≫ iR) := by
    rw [hP₀]
    exact congrArg Over.mk hfactor.symm
  have huₗ₀ : (Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion).obj P₀.y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R p₀.carrier)) ≫ iR) :=
    (congrArg (Over.post B.inclusion).obj (P₀.hy.trans P₀.hx.symm)).trans hP₀base
  have hfieldπ : Deformation.Artin.fieldPointMap B S hS 𝒳.val.p x iR P₀.y huₗ₀ =
      B.inclusion.map (η.app ⟨p₀.siteObject, Discrete.mk p₀.value⟩).left := by
    dsimp only [η]
    rw [baseChangeProjection_app B S hS 𝒳 U V x hx y F e _ hP₀]
    simp only [Deformation.Artin.fieldPointMap, Over.comp_left, Over.eqToHom_left,
      Functor.map_comp, eqToHom_map, eqToHom_trans_assoc]
    rfl
  have hfieldpoint : Deformation.Artin.fieldPointMap B S hS 𝒳.val.p x iR P₀.y huₗ₀
      (IsLocalRing.closedPoint p₀.carrier) = u₀ := by
    rw [hfieldπ]
    exact hp₀π
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let α := twoYonedaLiftIsoSliceFunctor 𝒳.val.p 𝒳.isFiberedInGroupoids
    𝒳.val.p.chosenPullbacks U ⟨x, hx⟩
  have hsmooth_of_finite :
      LocallyOfFiniteType (Deformation.Artin.fieldPointMap B S hS 𝒳.val.p x iR P₀.y huₗ₀) →
      Deformation.IsSmooth (Deformation.Artin.mapPredeformationCategory iR
        (Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion)
        (𝒳.val.p ⋙ Over.post B.inclusion)
        (𝒳.val.p.chosenPullbacks.sliceFunctor ⟨x, rfl⟩)
        (Deformation.Artin.sliceFunctor_comp_post B S hS 𝒳.val.p 𝒳.val.p.chosenPullbacks x)
        P₀.y huₗ₀).toBasedFunctor := by
    intro hlft
    obtain ⟨a, ha, hfac⟩ := exists_finite_residueFieldAlgebra
      (Deformation.Artin.fieldPointMap B S hS 𝒳.val.p x iR P₀.y huₗ₀) u₀ hfieldpoint hlft
    let := a
    let := ha
    exact Deformation.Artin.isSmooth_mapPredeformationCategory_of_isVersalAt B S hS
      𝒳.val.p x iR P₀.y huₗ₀ 𝒳.isFiberedInGroupoids
      (show LocallyOfFiniteType (B.inclusion.map (𝒳.val.p.obj x).hom) from inferInstance) u₀ hu₀
      hfac hversal hRS
  have hZV : AlgebraicGeometry.Space.IsLocallyOfFiniteType B V.left.1 V.left.2
      (terminal.from F : F ⟶
        ⊤_ ((AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) :=
    isLocallyOfFiniteType_twoFibreProduct_of_baseChangeEquiv
      B S hS 𝒳 hΔ hΔlft U V x hx y hy F e
  have hWV : LocallyOfFiniteType
      ((AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).map d.h) :=
    hZV d.U d.V d.a d.b d.h d.a_etale d.b_etale d.comm
  have ht₀ : AlgebraicGeometry.IsFiniteTypePoint
      (AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U c'.representative) :=
    hcscheme.symm ▸ hcfinite
  let : LocallyOfFiniteType
      (c'.U.left.1.fromSpecResidueField
        (AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U c'.representative)) := ht₀.1
  let : LocallyOfFiniteType (B.inclusion.map d.U.hom) :=
    show LocallyOfFiniteType
      ((AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).map d.h) from hWV
  have hp₀base : LocallyOfFiniteType (p₀.toBase ≫ B.inclusion.map V.hom) := by
    have h1 : LocallyOfFiniteType p₀.toBase := by
      change LocallyOfFiniteType
        (c'.U.left.1.fromSpecResidueField
          (AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U c'.representative) ≫
          B.inclusion.map d.U.hom)
      infer_instance
    let := h1
    infer_instance
  have hfieldbase : Deformation.Artin.fieldPointMap B S hS 𝒳.val.p x iR P₀.y huₗ₀ ≫
      ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R p₀.carrier)) ≫ iR := by
    have hcomm : ((Over.post B.inclusion).map P₀.y.hom).left ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom =
        ((Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion).obj P₀.y).hom := by
      simpa using ((Over.post B.inclusion).map P₀.y.hom).w
    calc
      Deformation.Artin.fieldPointMap B S hS 𝒳.val.p x iR P₀.y huₗ₀ ≫
            ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom =
          eqToHom (congrArg Over.left huₗ₀).symm ≫
            (((Over.post B.inclusion).map P₀.y.hom).left ≫
              ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom) := rfl
      _ = eqToHom (congrArg Over.left huₗ₀).symm ≫
            ((Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion).obj P₀.y).hom := by
        rw [hcomm]
      _ = Spec.map (CommRingCat.ofHom (algebraMap R p₀.carrier)) ≫ iR := by
        let w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R p₀.carrier)) ≫ iR) ⟶
            (Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion).obj P₀.y :=
          eqToHom huₗ₀.symm
        have hw : w.left = eqToHom (congrArg Over.left huₗ₀).symm := by
          simp [w, Over.eqToHom_left]
        rw [← hw]
        exact w.w
  have hlftField : LocallyOfFiniteType
      (Deformation.Artin.fieldPointMap B S hS 𝒳.val.p x iR P₀.y huₗ₀) := by
    let : LocallyOfFiniteType
        (Deformation.Artin.fieldPointMap B S hS 𝒳.val.p x iR P₀.y huₗ₀ ≫
          ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom) := by
      rw [hfieldbase, hfactor]
      exact hp₀base
    exact locallyOfFiniteType_of_comp
      (Deformation.Artin.fieldPointMap B S hS 𝒳.val.p x iR P₀.y huₗ₀)
      ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom
  have hsmooth := hsmooth_of_finite hlftField
  have hTop : AlgebraicGeometry.IsAlgebraicSpace B V.left.1 V.left.2
      (⊤_ ((AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) :=
    AlgebraicGeometry.Space.isAlgebraicSpace_of_iso B V.left.1 V.left.2
      (terminalYonedaIso B V.left.1 V.left.2)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B V.left.1 V.left.2
        (Over.mk (𝟙 (B.obj V.left.2))))
  let : LocallyOfFiniteType
      ((AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).map d.h) := hWV
  let : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) :=
    (inferInstance : IsLocallyNoetherian S)
  let : IsLocallyNoetherian
      ((AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).obj d.V) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map V.hom)
  refine smoothAt_of_schemeChartSmoothAt B V.left.1 V.left.2 hF hTop
    (terminal.from F) (z₀.class B V.left.1 V.left.2 F) d ?_
  refine ((InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness
    ((AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).map d.h)
    (d.sourcePoint B V.left.1 V.left.2)).out 4 1).mp ?_
  -- The residually trivial small extension lifting property of the chart map `W ⟶ V`
  -- at `w₀`.  Both of its inputs are in hand: `hsmooth` is the smoothness of
  -- `𝓕_{(Sch/U),l,u_{l,0}} ⟶ 𝓕_{𝒳,l,x_{l,0}}` of Tag 07XG, which
  -- `exists_baseChange_section_of_deformation_lift` turns into a lift of `F`-sections along
  -- `Spec A ↪ Spec A'`, and `d.a_etale`, which by
  -- `AlgebraicGeometry.Space.formallyEtale_of_etale` lifts that
  -- `F`-section back to the chart `W` -- uniquely, and in one step, because a small
  -- extension has square-zero kernel and a residually trivial one has residue field `l`.
  have hdw : d.sourcePoint B V.left.1 V.left.2 =
      AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U c'.representative :=
    hdpoint.trans hcscheme.symm
  intro A' A φ hφ _ σ β hsq hclosed hresIso
  rw [hdw] at hclosed
  obtain ⟨hA'loc, hAloc, hA'art, hAart, hsurj, hlen⟩ := hφ
  let : IsLocalRing A' := hA'loc
  let : IsLocalRing A := hAloc
  let : IsArtinianRing A' := hA'art
  let : IsArtinianRing A := hAart
  have hsmall : InfinitesimalLifting.IsSmallExtension φ :=
    ⟨hA'loc, hAloc, hA'art, hAart, hsurj, hlen⟩
  have hker : RingHom.ker φ.hom ^ 2 = ⊥ :=
    (InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hsmall).2.2.2
  let : Ring.KrullDimLE 0 A := (isArtinianRing_iff_krullDimLE_zero (R := A)).mp hAart
  let : Ring.KrullDimLE 0 A' := (isArtinianRing_iff_krullDimLE_zero (R := A')).mp hA'art
  let : Subsingleton (Spec A) := Ring.KrullDimLE.subsingleton_primeSpectrum A
  let : Subsingleton (Spec A') := Ring.KrullDimLE.subsingleton_primeSpectrum A'
  -- Step 1: both spectra belong to the bounded site.
  let ires : CommRingCat.of p₀.carrier ⟶
      (Spec A).residueField (IsLocalRing.closedPoint A : Spec A) :=
    (c'.U.left.1.residueFieldCongr hclosed.symm).hom ≫
      σ.residueFieldMap (IsLocalRing.closedPoint A : Spec A)
  have hiresIso : IsIso ires := by
    let : IsIso ((c'.U.left.1.residueFieldCongr hclosed.symm).hom) :=
      (c'.U.left.1.residueFieldCongr hclosed.symm).isIso_hom
    let : IsIso (σ.residueFieldMap (IsLocalRing.closedPoint A : Spec A)) := hresIso
    change IsIso ((c'.U.left.1.residueFieldCongr hclosed.symm).hom ≫
      σ.residueFieldMap (IsLocalRing.closedPoint A : Spec A))
    infer_instance
  let eσ : p₀.carrier ≃+* (Spec A).residueField (IsLocalRing.closedPoint A : Spec A) :=
    (asIso ires).commRingCatIsoToRingEquiv
  let eA : IsLocalRing.ResidueField A ≃+* p₀.carrier :=
    (AlgebraicGeometry.residueFieldAtClosedPointEquiv (R := A)).symm.trans eσ.symm
  have hAsite : B.Contains (Spec A) :=
    spec_contains_of_artinianLocal_residueEquiv B hcfield eA
  let eA' : IsLocalRing.ResidueField A' ≃+* p₀.carrier :=
    (residueFieldEquiv_of_surjective φ hsurj).trans eA
  have hA'site : B.Contains (Spec A') :=
    spec_contains_of_artinianLocal_residueEquiv B hcfield eA'
  -- Step 2: the two site objects and the square-zero closed immersion between them.
  let T₀ : B.Schemes := B.obj hAsite
  let T'₀ : B.Schemes := B.obj hA'site
  let tW : T₀ ⟶ c'.U.left := B.inclusion.preimage σ
  let tV : T'₀ ⟶ B.obj V.left.2 := B.inclusion.preimage β
  let T : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 := Over.mk (tW ≫ c'.U.hom)
  let T' : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 := Over.mk tV
  let i₀ : T₀ ⟶ T'₀ := B.inclusion.preimage (Spec.map φ)
  have htW : B.inclusion.map tW = σ := B.inclusion.map_preimage _
  have htV : B.inclusion.map tV = β := B.inclusion.map_preimage _
  have hi₀ : B.inclusion.map i₀ = Spec.map φ := B.inclusion.map_preimage _
  have hsq' : σ ≫ B.inclusion.map c'.U.hom = Spec.map φ ≫ β := hsq
  have hiBase : i₀ ≫ tV = tW ≫ c'.U.hom := by
    apply B.inclusion.map_injective
    simp only [Functor.map_comp, htW, htV, hi₀]
    exact hsq'.symm
  let iAB : T ⟶ T' := Over.homMk i₀ hiBase
  let aT : T ⟶ c'.U := Over.homMk tW rfl
  have hiAB : (AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).map iAB =
      Spec.map φ := hi₀
  have haT : (AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).map aT = σ := htW
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).obj T) :=
    show IsAffine (Spec A) from inferInstance
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).obj T') :=
    show IsAffine (Spec A') from inferInstance
  have hrefl : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      f = (Iso.refl X).hom ≫ f ≫ (Iso.refl Y).inv := by
    intro X Y f
    simp
  have hzero : AlgebraicGeometry.Space.IsSquareZeroClosedImmersion B V.left.1 V.left.2 iAB :=
    AlgebraicGeometry.Space.isSquareZeroClosedImmersion_of_specMap B V.left.1 V.left.2 φ hsurj
      hker T T' iAB
      (Iso.refl _) (Iso.refl _) (by rw [hiAB]; exact hrefl _)
  -- Step 3: the structure maps of `Spec A` and `Spec A'` factor through the affine open
  -- `Spec R`, since both are one-point spaces lying over the image of `w₀`.
  have hp₀base' : p₀.toBase = c'.U.left.1.fromSpecResidueField
      (AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U c'.representative) ≫
      B.inclusion.map c'.U.hom := rfl
  have hrangeA : Set.range (σ ≫ B.inclusion.map c'.U.hom ≫ B.inclusion.map V.hom) ⊆
      Set.range iR := by
    rintro _ ⟨s, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap R p₀.carrier)))
      (IsLocalRing.closedPoint p₀.carrier), ?_⟩
    have h1 : (Spec.map (CommRingCat.ofHom (algebraMap R p₀.carrier)) ≫ iR)
          (IsLocalRing.closedPoint p₀.carrier) =
        (p₀.toBase ≫ B.inclusion.map V.hom) (IsLocalRing.closedPoint p₀.carrier) :=
      congrArg (fun k : Spec (.of p₀.carrier) ⟶ S =>
        k (IsLocalRing.closedPoint p₀.carrier)) hfactor
    have h4 : (c'.U.left.1.fromSpecResidueField
          (AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U c'.representative))
          (IsLocalRing.closedPoint p₀.carrier) =
        AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U c'.representative :=
      Scheme.fromSpecResidueField_apply _ _
    have h3 : σ s =
        AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U c'.representative :=
      (congrArg (fun z => σ z) (Subsingleton.elim s
        (IsLocalRing.closedPoint A : Spec A))).trans hclosed
    rw [hp₀base'] at h1
    simp only [Scheme.Hom.comp_apply] at h1 ⊢
    rw [h3]
    exact h1.trans (congrArg
      (fun z => B.inclusion.map V.hom (B.inclusion.map c'.U.hom z)) h4)
  have hrangeA' : Set.range (β ≫ B.inclusion.map V.hom) ⊆ Set.range iR := by
    rintro _ ⟨s, rfl⟩
    have hs : s = (Spec.map φ) (IsLocalRing.closedPoint A : Spec A) :=
      Subsingleton.elim _ _
    have h3 : ((Spec.map φ ≫ β) ≫ B.inclusion.map V.hom)
        (IsLocalRing.closedPoint A : Spec A) ∈ Set.range iR := by
      rw [← hsq', Category.assoc]
      exact hrangeA ⟨_, rfl⟩
    rw [hs]
    change ((Spec.map φ ≫ β) ≫ B.inclusion.map V.hom)
      (IsLocalRing.closedPoint A : Spec A) ∈ Set.range iR
    exact h3
  obtain ⟨algA, halgA⟩ := exists_algebra_factorization iR hiR
    (σ ≫ B.inclusion.map c'.U.hom ≫ B.inclusion.map V.hom) hrangeA
  let := algA
  have halgA2 : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iR =
      σ ≫ B.inclusion.map c'.U.hom ≫ B.inclusion.map V.hom := halgA
  obtain ⟨algA', halgA'⟩ := exists_algebra_factorization iR hiR
    (β ≫ B.inclusion.map V.hom) hrangeA'
  let := algA'
  have halgA'2 : Spec.map (CommRingCat.ofHom (algebraMap R A')) ≫ iR =
      β ≫ B.inclusion.map V.hom := halgA'
  have hφΛ : CommRingCat.ofHom (algebraMap R A') ≫ φ =
      CommRingCat.ofHom (algebraMap R A) := by
    apply ringHom_eq_of_specMap_comp_openImmersion iR hiR
    calc Spec.map (CommRingCat.ofHom (algebraMap R A') ≫ φ) ≫ iR
        = Spec.map φ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A')) ≫ iR := by
          rw [Spec.map_comp, Category.assoc]
      _ = (Spec.map φ ≫ β) ≫ B.inclusion.map V.hom := by
          rw [halgA'2]; simp only [Category.assoc]
      _ = (σ ≫ B.inclusion.map c'.U.hom) ≫ B.inclusion.map V.hom := by rw [hsq']
      _ = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iR := by
          rw [halgA2]; simp only [Category.assoc]
  have hφalg : ∀ r : R, φ.hom ((algebraMap R A') r) = (algebraMap R A) r := by
    intro r
    exact congrArg (fun k : R ⟶ A => k.hom r) hφΛ
  -- The residue-field identification realizes the canonical point of `Spec A`.
  let := hresIso
  have hiso : asIso ires = c'.U.left.1.residueFieldCongr hclosed.symm ≪≫
      asIso (σ.residueFieldMap (IsLocalRing.closedPoint A : Spec A)) := Iso.ext rfl
  have hνcomp : CommRingCat.ofHom (eA.toRingHom.comp (IsLocalRing.residue A)) =
      CommRingCat.ofHom
          ((AlgebraicGeometry.residueFieldAtClosedPointEquiv (R := A)).symm.toRingHom.comp
            (IsLocalRing.residue A)) ≫ (asIso ires).inv := rfl
  have hν : Spec.map (CommRingCat.ofHom (eA.toRingHom.comp (IsLocalRing.residue A))) ≫ σ =
      c'.U.left.1.fromSpecResidueField
        (AlgebraicGeometry.Space.schemePoint B V.left.1 V.left.2 c'.U c'.representative) := by
    rw [hνcomp, Spec.map_comp, specMap_residue_eq_fromSpecResidueField, hiso]
    exact specMap_residueIso_inv_comp σ (IsLocalRing.closedPoint A : Spec A) hclosed
  have hbaseA : ∀ r : R, eA (IsLocalRing.residue A (algebraMap R A r)) =
      algebraMap R p₀.carrier r := by
    have hringeq : CommRingCat.ofHom
          ((eA.toRingHom.comp (IsLocalRing.residue A)).comp (algebraMap R A)) =
        CommRingCat.ofHom (algebraMap R p₀.carrier) := by
      apply ringHom_eq_of_specMap_comp_openImmersion iR hiR
      calc Spec.map (CommRingCat.ofHom
              ((eA.toRingHom.comp (IsLocalRing.residue A)).comp (algebraMap R A))) ≫ iR
          = Spec.map (CommRingCat.ofHom (eA.toRingHom.comp (IsLocalRing.residue A))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iR := by
            rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
        _ = (Spec.map (CommRingCat.ofHom (eA.toRingHom.comp (IsLocalRing.residue A))) ≫ σ) ≫
              B.inclusion.map c'.U.hom ≫ B.inclusion.map V.hom := by
            rw [halgA2]; simp only [Category.assoc]
        _ = p₀.toBase ≫ B.inclusion.map V.hom := by
            rw [hν, hp₀base', Category.assoc]
        _ = Spec.map (CommRingCat.ofHom (algebraMap R p₀.carrier)) ≫ iR := hfactor.symm
    intro r
    exact congrArg (fun k : R ⟶ CommRingCat.of p₀.carrier => k.hom r) hringeq
  have heA' : ∀ a : A', eA' (IsLocalRing.residue A' a) =
      eA (IsLocalRing.residue A (φ.hom a)) := by
    intro a
    change eA (residueFieldEquiv_of_surjective φ hsurj (IsLocalRing.residue A' a)) = _
    rw [residueFieldEquiv_of_surjective_residue]
  have hbaseA' : ∀ r : R, eA' (IsLocalRing.residue A' (algebraMap R A' r)) =
      algebraMap R p₀.carrier r := by
    intro r
    rw [heA', hφalg]
    exact hbaseA r
  -- Step 4: the two objects of `𝒞_Λ` and the morphism between them.
  let AObj : Deformation.ArtinianLocalAlgCat.{u, u, u} R p₀.carrier :=
    artinianObject A eA hbaseA
  let A'Obj : Deformation.ArtinianLocalAlgCat.{u, u, u} R p₀.carrier :=
    artinianObject A' eA' hbaseA'
  let : IsLocalHom φ.hom := IsLocalHom.of_surjective φ.hom hsurj
  let ϕ : A'Obj ⟶ AObj :=
    { hom := { φ.hom with commutes' := hφalg }
      isLocal := by exact IsLocalHom.of_surjective φ.hom hsurj
      residue_comm := fun a => (heA' a).symm }
  have hϕ : CommRingCat.ofHom ϕ.hom.toRingHom = φ := rfl
  -- Step 4: the deformation objects and the morphism between them.
  let ν : Spec (.of p₀.carrier) ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (eA.toRingHom.comp (IsLocalRing.residue A)))
  let ρ₀ : p₀.siteObject.left ⟶ T.left := B.inclusion.preimage ν
  have hρ₀ : B.inclusion.map ρ₀ = ν := B.inclusion.map_preimage _
  have hρbase : ρ₀ ≫ T.hom = p₀.siteObject.hom := by
    apply B.inclusion.map_injective
    change B.inclusion.map (ρ₀ ≫ tW ≫ c'.U.hom) = B.inclusion.map p₀.siteObject.hom
    rw [Functor.map_comp, Functor.map_comp, hρ₀, htW]
    change ν ≫ σ ≫ B.inclusion.map c'.U.hom = p₀.toBase
    rw [← Category.assoc, hν, hp₀base']
  let ρ : p₀.siteObject ⟶ T := Over.homMk ρ₀ hρbase
  let aSec : F.obj (Opposite.op T) := d.a.app (Opposite.op T) aT
  have hρaT : ρ ≫ aT = d.representative.value := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (ρ₀ ≫ tW) = B.inclusion.map d.representative.value.left
    rwa [Functor.map_comp, hρ₀, htW]
  have hFρ : p₀.value = F.map ρ.op aSec := by
    have hn : d.a.app (Opposite.op p₀.siteObject) ((yoneda.obj d.U).map ρ.op aT) =
        F.map ρ.op (d.a.app (Opposite.op T) aT) := by
      simpa only [types_comp_apply] using congrArg (fun k => k aT) (d.a.naturality ρ.op)
    have hv : (yoneda.obj d.U).map ρ.op aT = d.representative.value := hρaT
    rw [← hn, hv]
    rfl
  let m : (⟨p₀.siteObject, Discrete.mk p₀.value⟩ :
      (presheafOfCategories (F ⋙ typeToCat)).obj) ⟶ ⟨T, Discrete.mk aSec⟩ :=
    ⟨ρ, Discrete.eqToHom' hFρ⟩
  let P := e.inv.functor.obj ⟨T, Discrete.mk aSec⟩
  have hP : P.x = T :=
    congrArg (fun G => G.obj ⟨T, Discrete.mk aSec⟩) e.inv.w
  let qU := Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion
  let qX := 𝒳.val.p ⋙ Over.post B.inclusion
  let G := 𝒳.val.p.chosenPullbacks.sliceFunctor (⟨x, rfl⟩ : 𝒳.val.p.Fiber (𝒳.val.p.obj x))
  let hG := Deformation.Artin.sliceFunctor_comp_post B S hS 𝒳.val.p 𝒳.val.p.chosenPullbacks x
  have hTstruct : B.inclusion.map (T.hom ≫ V.hom) =
      σ ≫ B.inclusion.map c'.U.hom ≫ B.inclusion.map V.hom := by
    change B.inclusion.map ((tW ≫ c'.U.hom) ≫ V.hom) = _
    rw [Functor.map_comp, Functor.map_comp, htW]
    simp only [Category.assoc]
  have hT'struct : B.inclusion.map (T'.hom ≫ V.hom) = β ≫ B.inclusion.map V.hom := by
    change B.inclusion.map (tV ≫ V.hom) = _
    rw [Functor.map_comp, htV]
  have hPbase : (Over.map V.hom ⋙ Over.post B.inclusion).obj P.x =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iR) := by
    rw [hP]
    exact congrArg Over.mk (hTstruct.trans halgA2.symm)
  have hbaseObjA : qU.obj P.y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iR) :=
    (congrArg (Over.post B.inclusion).obj (P.hy.trans P.hx.symm)).trans hPbase
  have hbaseObjA' : qX.obj (y.obj T') =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A')) ≫ iR) := by
    change (Over.post B.inclusion).obj (𝒳.val.p.obj (y.obj T')) = _
    rw [show 𝒳.val.p.obj (y.obj T') = (Over.map V.hom).obj T' from Functor.congr_obj hy T']
    exact congrArg Over.mk (hT'struct.trans halgA'2.symm)
  have harrowBaseA :
      eqToHom (congrArg Over.left huₗ₀).symm ≫
        (qU.map ((e.inv.functor.map m).b)).left ≫
        eqToHom (congrArg Over.left hbaseObjA) = ν := by
    have k₀ : P₀.y.left.left = p₀.siteObject.left :=
      (congrArg Over.left (P₀.hy.trans P₀.hx.symm)).trans (congrArg Over.left hP₀)
    have k₁ : T.left = P.y.left.left :=
      (congrArg Over.left hP).symm.trans
        (congrArg Over.left (P.hy.trans P.hx.symm)).symm
    have hb := baseChangeHom_b_left B S hS 𝒳 U V x hx y F e m hP₀ hP k₀ k₁
    change eqToHom (congrArg Over.left huₗ₀).symm ≫
        B.inclusion.map (((Over.forget U).map ((e.inv.functor.map m).b)).left) ≫
        eqToHom (congrArg Over.left hbaseObjA) = ν
    rw [hb, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
      show ((presheafOfCategories (F ⋙ typeToCat)).p.map m).left = ρ₀ from rfl, hρ₀]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    exact eqToHom_sandwich _ _ ν
  let aUobj : Deformation.Artin.DeformationObject iR qU P₀.y huₗ₀ :=
    { algebra := AObj
      point := P.y
      arrow := (e.inv.functor.map m).b
      base := hbaseObjA
      arrow_base := harrowBaseA }
  let ξ : G.obj P.y ⟶ y.obj T' :=
    (P.iso ≪≫ α.app P.y).inv ≫ y.map (eqToHom hP ≫ iAB)
  have hξbase :
      eqToHom (congrArg Over.left
          (mapDeformationObject iR qU qX G hG P₀.y huₗ₀ aUobj).base).symm ≫
        (qX.map ξ).left ≫ eqToHom (congrArg Over.left hbaseObjA') =
      Spec.map (CommRingCat.ofHom ϕ.hom.toRingHom) := by
    have hvert : 𝒳.val.p.IsHomLift (𝟙 P.base) (P.iso ≪≫ α.app P.y).hom := by
      have hα : 𝒳.val.p.IsHomLift (𝟙 P.base) (α.app P.y).hom := by
        rw [← P.hy]
        exact twoYonedaLiftIsoSliceFunctor_vertical 𝒳.val.p 𝒳.isFiberedInGroupoids
          𝒳.val.p.chosenPullbacks U ⟨x, hx⟩ P.y
      let := hα
      let := P.vertical
      exact IsHomLift.comp_lift_id_left 𝒳.val.p (𝟙 P.base) (α.app P.y).hom P.iso.hom
    let := hvert
    have hvertinv : 𝒳.val.p.IsHomLift (𝟙 P.base) (P.iso ≪≫ α.app P.y).inv := by
      rw [show (P.iso ≪≫ α.app P.y).inv = inv (P.iso ≪≫ α.app P.y).hom by simp]
      exact IsHomLift.lift_id_inv_isIso 𝒳.val.p P.base (P.iso ≪≫ α.app P.y).hom
    let k : P.base ⟶ (Over.map V.hom).obj T' :=
      eqToHom P.hx.symm ≫ (Over.map V.hom).map (eqToHom hP ≫ iAB)
    have hya : 𝒳.val.p.IsHomLift k (y.map (eqToHom hP ≫ iAB)) := by
      apply IsHomLift.of_fac' 𝒳.val.p k _
        ((Functor.congr_obj hy P.x).trans P.hx) (Functor.congr_obj hy T')
      have hm := Functor.congr_hom hy (eqToHom hP ≫ iAB)
      change 𝒳.val.p.map (y.map (eqToHom hP ≫ iAB)) = _ at hm
      rw [hm]
      simp only [k, Category.assoc, eqToHom_trans_assoc]
    let := hvertinv
    let := hya
    have hξlift : 𝒳.val.p.IsHomLift k ξ := by
      dsimp only [ξ]
      infer_instance
    let := hξlift
    have hfac := IsHomLift.fac' 𝒳.val.p k ξ
    change eqToHom _ ≫ B.inclusion.map ((𝒳.val.p.map ξ).left) ≫ eqToHom _ = _
    rw [hfac]
    simp only [k, Over.comp_left, Over.eqToHom_left, Over.map_map_left, Functor.map_comp,
      eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    rw [show B.inclusion.map iAB.left = Spec.map φ from hi₀, ← hϕ]
    exact eqToHom_sandwich _ _ _
  let bXobj : Deformation.Artin.DeformationObject iR qX (G.obj P₀.y)
      (Deformation.Artin.imageBasePoint (qY := qX) iR qU G hG P₀.y huₗ₀) :=
    { algebra := A'Obj
      point := y.obj T'
      arrow := G.map aUobj.arrow ≫ ξ
      base := hbaseObjA'
      arrow_base := deformationObject_arrow_base_comp
        (mapDeformationObject iR qU qX G hG P₀.y huₗ₀ aUobj) ϕ ξ hbaseObjA' hξbase }
  let i₁ : Deformation.Artin.DeformationMorphism iR qX (G.obj P₀.y)
      (Deformation.Artin.imageBasePoint (qY := qX) iR qU G hG P₀.y huₗ₀) bXobj
      (mapDeformationObject iR qU qX G hG P₀.y huₗ₀ aUobj) :=
    { ringHom := ϕ
      arrow := ξ
      triangle := rfl
      arrow_base := hξbase }
  obtain ⟨bSec, hbSec⟩ := exists_baseChange_section_of_deformation_objects B S hS 𝒳 V x y hy F e
    𝒳.val.p.chosenPullbacks iR P₀.y huₗ₀ hsmooth iAB aSec aUobj bXobj i₁ hsurj rfl rfl
    (by
      change ξ = G.map (𝟙 P.y) ≫ (P.iso ≪≫ α.app P.y).inv ≫
        y.map (eqToHom hP ≫ iAB) ≫ 𝟙 (y.obj T')
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])
  -- Step 5: the étale chart map is formally étale, so the lifted section of `F` comes
  -- from a morphism of the chart.
  obtain ⟨γsite, ⟨hγ₁, -⟩, -⟩ :=
    AlgebraicGeometry.Space.formallyEtale_of_etale B V.left.1 V.left.2
      d.a d.a_etale T T' inferInstance inferInstance iAB hzero aT bSec hbSec.symm
  refine ⟨(AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).map γsite, ?_, ?_⟩
  · have h := congrArg ((AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).map)
      (show iAB ≫ γsite = aT from hγ₁)
    rw [Functor.map_comp, hiAB, haT] at h
    exact h
  · change (AlgebraicGeometry.BigFppfOver.toScheme B V.left.1 V.left.2).map γsite ≫
      B.inclusion.map c'.U.hom = β
    rw [← htV]
    change B.inclusion.map γsite.left ≫ B.inclusion.map c'.U.hom = B.inclusion.map tV
    rw [← Functor.map_comp]
    exact congrArg B.inclusion.map γsite.w

end Deformation.Artin.BaseChange

end
