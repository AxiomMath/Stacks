module

public import Mathlib.Topology.Sets.Opens
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenLocusFullSubcategory
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackCoverScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeExistenceUniversallyClosed
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.RestrictMorPresheaf
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# Open substacks and open subsets of points (Stacks 06FJ)

Let `𝒳` be an algebraic stack over `S`. **Stacks 06FJ** says that the rule `𝒰 ↦ |𝒰|` is an
inclusion-preserving bijection from the open substacks of `𝒳` (**Stacks 04YM**, part (1)) onto
the open subsets of the topological space `|𝒳|` of **Stacks 04XG** and **Stacks 04XL**. This
file proves it.

Here `|𝒰| ⊆ |𝒳|` is `AlgebraicGeometry.Stack.OpenSubstack.pointSet`, the image on points of the
canonical inclusion of the open substack, which is the reading of `|𝒰|` as a subset of `|𝒳|`
that the library already uses. Open substacks are ordered by inclusion of their objects.

## Main definitions

* `AlgebraicGeometry.Stack.OpenSubstack.opens`: the rule `𝒰 ↦ |𝒰|`, valued in the open subsets
  of `|𝒳|`.
* `AlgebraicGeometry.Stack.OpenSubstack.pointsInProperty` and
  `AlgebraicGeometry.Stack.OpenSubstack.ofIsOpen`: the open substack attached to an open subset
  `W` of `|𝒳|`, made of the objects all of whose points lie in `W`.
* `AlgebraicGeometry.Stack.OpenSubstack.opensOrderIso`: the rule as an order isomorphism.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.isOpen_pointSet`: the point set of an open substack is
  open, so the rule is defined.
* `AlgebraicGeometry.Stack.OpenSubstack.pointSet_mono` and
  `AlgebraicGeometry.Stack.OpenSubstack.opens_mono`: the rule preserves inclusions.
* `AlgebraicGeometry.Stack.OpenSubstack.property_le_of_pointSet_subset`: the rule reflects
  inclusions, hence is injective.
* `AlgebraicGeometry.Stack.OpenSubstack.pointSet_ofIsOpen`: the rule is surjective.
* `AlgebraicGeometry.Stack.OpenSubstack.bijective_opens_and_opens_le_iff`: **Stacks 06FJ**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_of_range_pointsMap_subset`: a
  scheme-valued point whose points are covered by an open immersion lifts along it; and
  `AlgebraicGeometry.Stack.AlgebraicStacks.essSurj_of_isOpenImmersion_of_isSurjective`: an open
  immersion surjective on points is essentially surjective.

## Implementation notes

Openness is `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenMap_pointsMap_of_isOpenImmersion`
(**Stacks 0H20**) at the inclusion of the open substack, whose range is therefore open.
Inclusion-preservation is proved through `mem_pointSet_iff`.

The source argues through a presentation `[U/R] ⟶ 𝒳` and Stacks 0507. The proof here avoids the
presentation and works with scheme-valued points directly.

*Injectivity.* An object `x` of `𝒰` is named by a 1-morphism from the algebraic stack of a scheme
`T` (the 2-Yoneda lemma). If `|𝒰| ⊆ |𝒱|`, its image on points lies in that of the inclusion of
`𝒱`, and the base change `T ×_𝒳 𝒱 ⟶ T` is an open immersion of algebraic spaces surjective on
points (**Stacks 04XH**), hence an isomorphism; a section of it puts `x` in `𝒱` up to
isomorphism.

*Surjectivity.* For an open `W ⊆ |𝒳|` the objects all of whose points lie in `W` are cut out, on
every scheme-valued point `y` over `U`, by the open subscheme of `U` of points mapping into `W` —
open because `|U| ⟶ |𝒳|` is continuous (**Stacks 04XL**). So the inclusion of their full
subcategory is representable by algebraic spaces and an open immersion
(`AlgebraicGeometry.Stack.isOpenImmersion_of_openLocus`), and the full subcategory is an algebraic
stack by **Stacks 05UM**. Its points are exactly `W`.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

namespace OpenSubstack

/-- A point of `|𝒳|` lies in the point set of an open substack exactly when some field-valued
point representing it has its object in the substack. -/
theorem mem_pointSet_iff (W : OpenSubstack 𝒳) (x : AlgebraicStacks.points B S hS 𝒳) :
    x ∈ W.pointSet B S hS ↔
      ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
        W.property p.obj ∧ pointClass B S hS 𝒳.val.val 𝒳.val.property p = x := by
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | h q => exact ⟨fieldValuedPointMap B S hS _ (fullSubcategoryBasedInclusion 𝒳 W.property) q,
        q.obj.property, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨pointClass B S hS _ _
      { carrier := p.carrier
        field := p.field
        base := p.base
        isSpec := p.isSpec
        obj := ⟨p.obj, hp⟩
        «over» := p.over }, rfl⟩

/-- The rule of Stacks 06FJ is defined. The set of points of an algebraic stack lying in an
open substack is open: it is the range of the map on points of the inclusion, which is an open
map because the inclusion is an open immersion. -/
@[stacks 06FJ "the point set of an open substack is open, so the rule is defined"]
theorem isOpen_pointSet (W : OpenSubstack 𝒳) :
    @IsOpen _ (pointTopology B S hS 𝒳.val) (W.pointSet B S hS) := by
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS
    (fullSubcategoryAlgebraicStack 𝒳 W.property W.isAlgebraic).val
  exact (AlgebraicStacks.isOpenMap_pointsMap_of_isOpenImmersion B S hS
    W.inclusion W.isOpenImmersion).isOpen_range

/-- **The rule `𝒰 ↦ |𝒰|` of Stacks 06FJ**: the point set of an open substack of `𝒳`, as an open
subset of the topological space of points of `𝒳`. -/
@[stacks 06FJ "the rule"]
noncomputable def opens (W : OpenSubstack 𝒳) :
    letI := pointTopology B S hS 𝒳.val
    TopologicalSpace.Opens (AlgebraicStacks.points B S hS 𝒳) :=
  letI := pointTopology B S hS 𝒳.val
  ⟨W.pointSet B S hS, isOpen_pointSet B S hS W⟩

/-- The rule of Stacks 06FJ preserves inclusions. An open substack contained in another has a
smaller point set. -/
@[stacks 06FJ "inclusion-preservation for the point set of an open substack"]
theorem pointSet_mono {U V : OpenSubstack 𝒳} (h : U.property ≤ V.property) :
    U.pointSet B S hS ⊆ V.pointSet B S hS := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := (mem_pointSet_iff B S hS U x).1 hx
  exact (mem_pointSet_iff B S hS V x).2 ⟨p, h _ hp, hpx⟩

/-- The rule of Stacks 06FJ preserves inclusions, for the rule `𝒰 ↦ |𝒰|` of
`AlgebraicGeometry.Stack.OpenSubstack.opens`. -/
@[stacks 06FJ "inclusion-preservation for the rule U goes to |U| as an open subset of the \
point space"]
theorem opens_mono {U V : OpenSubstack 𝒳} (h : U.property ≤ V.property) :
    letI := pointTopology B S hS 𝒳.val
    opens B S hS U ≤ opens B S hS V :=
  pointSet_mono B S hS h

end OpenSubstack

/-! ### Lifting along an open immersion -/

namespace AlgebraicStacks

/-- **A scheme-valued point whose points are covered by an open immersion lifts along it.** Let
`f : 𝒵 ⟶ 𝒳` be an open immersion of algebraic stacks and let `b : T ⟶ 𝒳` be a 1-morphism from
the algebraic stack of a scheme `T` whose image on points lies in that of `f`. Then the object of
`𝒳` over `T` named by `b` is isomorphic to the image of an object of `𝒵`.

The base change `T ×_𝒳 𝒵 ⟶ T` is an open immersion (**Stacks 0302** and **Stacks 045C**) between
categories represented by algebraic spaces (**Stacks 0300**), so the induced morphism `G ⟶ h_T` of
representing presheaves is an open immersion
(`AlgebraicGeometry.Stack.isOpenImmersion_representingMap`). It is surjective on points by
**Stacks 04XH**, because the image of `b` on points lies in that of `f`, so it is an isomorphism.
Its inverse is induced by a section `T ⟶ T ×_𝒳 𝒵` (**Stacks 04SW**), and the second projection of
that section at the terminal object of the slice is the object sought. -/
theorem exists_iso_of_range_pointsMap_subset {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒵 ⟶ 𝒳) (hf : IsOpenImmersion B S hS f) {T : BigFppfOver B S hS}
    (b : schemeStack.{u, w} B S hS T ⟶ 𝒳)
    (hb : Set.range (pointsMap B S hS b) ⊆ Set.range (pointsMap B S hS f)) :
    ∃ z : 𝒵.val.val.obj, Nonempty ((CatFiberedInGroupoids.homFunctor f.hom).obj z ≅
      (CatFiberedInGroupoids.homFunctor b.hom).obj (Over.mk (𝟙 T))) := by
  set P := twoFibreProductSquareAlgebraicStacks B S hS b f
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS b f
  have hu : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      b.hom f.hom
  have hrep : IsRepresentableByAlgebraicSpaces B S hS P.fst.hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ f.hom b.hom _ hu hf.1
  have hoi : Stack.IsOpenImmersion B S hS P.fst.hom :=
    isOpenImmersion_baseChange.{u, u, u + 1} B S hS _ _ _ f.hom b.hom _ hu hf.2
  have hT : IsRepresentableByAlgebraicSpace B S hS (schemeFibredCategory B S hS T) :=
    ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T, ⟨representedChart B S hS T⟩⟩
  obtain ⟨G, hG, ⟨eG⟩⟩ := isRepresentableByAlgebraicSpace_of_representable B S hS _ _
    P.fst.hom hrep hT
  set m := representingMap B S hS P.pt.val (schemeFibredCategory B S hS T) G (yoneda.obj T) eG
    (representedChart B S hS T) P.fst.hom
  have hm : Space.IsOpenImmersion B S hS m :=
    isOpenImmersion_representingMap B S hS P.fst.hom hrep hoi G (yoneda.obj T) hG
      (isAlgebraicSpace_yoneda B S hS T) eG (representedChart B S hS T)
  have hsurj : Function.Surjective (Space.pointsMap B S hS G m) := by
    intro τ
    obtain ⟨x, hx⟩ := hb ⟨representedChartPointMap B S hS T τ, rfl⟩
    obtain ⟨π, hπ, -⟩ := exists_point_of_isTwoFibreProduct B S hS P hP
      (representedChartPointMap B S hS T τ) x hx.symm
    obtain ⟨γ, rfl⟩ := (bijective_spacePointMap_representing B S hS G P.pt.val eG).2 π
    refine ⟨γ, (bijective_representedChartPointMap B S hS T).1 ?_⟩
    rw [← hπ]
    exact spacePointMap_representing_naturality B S hS G (yoneda.obj T) P.pt.val
      (schemeFibredCategory B S hS T) eG (representedChart B S hS T) P.fst.hom γ
  have hiso : IsIso m := Space.isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS m hm hsurj
  obtain ⟨s, hs⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := schemeStack.{u, w} B S hS T) (𝒴 := P.pt) (yoneda.obj T) G
    (representedChart B S hS T) eG (inv m)
  have hcomp : representingMap B S hS _ _ (yoneda.obj T) (yoneda.obj T)
      (representedChart B S hS T) (representedChart B S hS T) (s.hom ≫ P.fst.hom) =
      representingMap B S hS _ _ (yoneda.obj T) (yoneda.obj T)
      (representedChart B S hS T) (representedChart B S hS T) (𝟙 _) := by
    rw [representingMap_comp B S hS (yoneda.obj T) G (yoneda.obj T) (representedChart B S hS T)
      eG (representedChart B S hS T), hs, representingMap_id, IsIso.inv_hom_id]
  obtain ⟨⟨⟨η⟩, -⟩⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS _ _ (yoneda.obj T)
    (yoneda.obj T) (representedChart B S hS T) (representedChart B S hS T) hcomp
  let t : (schemeFibredCategory B S hS T).val.obj := Over.mk (𝟙 T)
  let w := (CatFiberedInGroupoids.homFunctor s.hom).obj t
  exact ⟨(CatFiberedInGroupoids.homFunctor P.snd.hom).obj w,
    ⟨((CatFiberedInGroupoids.underlyingIso (toCatFiberedInGroupoids B S hS P).iso).app w).symm ≪≫
      (CatFiberedInGroupoids.homFunctor b.hom).mapIso
        ((CatFiberedInGroupoids.underlyingIso η).app t)⟩⟩

/-- **Every object of an algebraic stack is named by a scheme-valued point** (the 2-Yoneda lemma,
**Stacks 004B**): an object `x` lying over `T` is isomorphic to the value at the terminal object
of the slice of a 1-morphism from the algebraic stack of `T`. -/
theorem exists_schemeStack_hom_iso (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : 𝒳.val.val.obj) :
    ∃ b : schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳,
      Nonempty ((CatFiberedInGroupoids.homFunctor b.hom).obj (Over.mk (𝟙 _)) ≅ x) := by
  let c := Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (𝒳.val.val.p.obj x) ⟨x, rfl⟩ (Over.mk (𝟙 _))
  have : 𝒳.val.val.p.IsStronglyCartesian (𝟙 (𝒳.val.val.p.obj x)) c.φ := c.isStronglyCartesian
  have : IsIso c.φ :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.val.p (𝟙 (𝒳.val.val.p.obj x)) c.φ
  exact ⟨Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (Functor.TwoYoneda.liftBased 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (𝒳.val.val.p.obj x) ⟨x, rfl⟩)), ⟨@asIso _ _ _ _ c.φ this⟩⟩

/-- **An open immersion of algebraic stacks which is surjective on points is essentially
surjective on objects.** Every object of the target is named by a scheme-valued point, whose image
on points lies in that of the open immersion, which therefore lifts it. -/
theorem essSurj_of_isOpenImmersion_of_isSurjective {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒵 ⟶ 𝒳) (hf : IsOpenImmersion B S hS f) (hs : IsSurjective B S hS f) :
    (CatFiberedInGroupoids.homFunctor f.hom).EssSurj := by
  refine ⟨fun x => ?_⟩
  obtain ⟨b, ⟨e⟩⟩ := exists_schemeStack_hom_iso B S hS 𝒳 x
  obtain ⟨z, ⟨e'⟩⟩ := exists_iso_of_range_pointsMap_subset B S hS f hf b
    (fun _ _ => hs _)
  exact ⟨z, ⟨e' ≪≫ e⟩⟩

end AlgebraicStacks

namespace OpenSubstack

/-! ### The rule reflects inclusions -/

/-- **The rule `𝒰 ↦ |𝒰|` of Stacks 06FJ reflects inclusions**, which is its injectivity: an open
substack whose points lie among those of another is contained in it.

An object `x` of `𝒰` is named by a scheme-valued point of `𝒰`, and its image in `𝒳` has image on
points inside `|𝒰| ⊆ |𝒱|`; the inclusion of `𝒱` is an open immersion, so it lifts `x` up to
isomorphism, and `𝒱` is strictly full. -/
theorem property_le_of_pointSet_subset {U V : OpenSubstack 𝒳}
    (h : U.pointSet B S hS ⊆ V.pointSet B S hS) : U.property ≤ V.property := by
  intro x hx
  obtain ⟨b, ⟨e⟩⟩ := AlgebraicStacks.exists_schemeStack_hom_iso B S hS
    (fullSubcategoryAlgebraicStack 𝒳 U.property U.isAlgebraic) ⟨x, hx⟩
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS (b ≫ U.inclusion)) ⊆
      V.pointSet B S hS := by
    rintro _ ⟨q, rfl⟩
    refine h ⟨AlgebraicStacks.pointsMap B S hS b q, ?_⟩
    rw [AlgebraicStacks.pointsMap_comp]
    rfl
  obtain ⟨z, ⟨e'⟩⟩ := AlgebraicStacks.exists_iso_of_range_pointsMap_subset B S hS
    V.inclusion V.isOpenImmersion (b ≫ U.inclusion) hrange
  have := V.strictlyFull
  exact V.property.prop_of_iso (e' ≪≫ U.property.ι.mapIso e) z.property

/-! ### The open substack attached to an open set of points -/

variable {B S hS}

/-- The objects of an algebraic stack all of whose points lie in a given set of points: an object
`x` has the property when every field-valued point mapping to it represents a point of the set.
For an open set this cuts out the open substack whose points are that set. -/
def pointsInProperty (W : Set (AlgebraicStacks.points B S hS 𝒳)) :
    ObjectProperty 𝒳.val.val.obj :=
  fun x => ∀ p : FieldValuedPoint B S hS 𝒳.val.val, Nonempty (p.obj ⟶ x) →
    pointClass B S hS 𝒳.val.val 𝒳.val.property p ∈ W

/-- The objects all of whose points lie in a set form a strictly full subcategory. -/
instance (W : Set (AlgebraicStacks.points B S hS 𝒳)) :
    (pointsInProperty W).IsClosedUnderIsomorphisms :=
  ⟨fun e hx p ⟨a⟩ => hx p ⟨a ≫ e.inv⟩⟩

/-- The property is inherited along any morphism into an object having it. -/
theorem pointsInProperty_of_hom {W : Set (AlgebraicStacks.points B S hS 𝒳)}
    {x x' : 𝒳.val.val.obj} (hx : pointsInProperty W x) (a : x' ⟶ x) :
    pointsInProperty W x' :=
  fun p ⟨b⟩ => hx p ⟨b ≫ a⟩

/-- The full subcategory of objects all of whose points lie in a given set is fibred in groupoids:
it is closed under every morphism into it, so in particular under strongly cartesian pullbacks,
and its fibres embed fully faithfully into those of `𝒳`, which are groupoids. -/
theorem isFiberedInGroupoids_pointsInProperty (W : Set (AlgebraicStacks.points B S hS 𝒳)) :
    ((pointsInProperty W).ι ⋙ 𝒳.val.val.p).IsFiberedInGroupoids := by
  set p := 𝒳.val.val.p
  set P := pointsInProperty W
  have : p.IsFibered := 𝒳.val.property.isFibered
  have hFib : (P.ι ⋙ p).IsFibered :=
    Functor.isFibered_restrict_of_closed p P
      (fun _ φ _ hx => Functor.isoOverId_of_prop (pointsInProperty_of_hom hx φ))
  have hGroups : ∀ U : BigFppfOver B S hS, IsGroupoid ((P.ι ⋙ p).Fiber U) := by
    intro U
    have hrfl : P.ι ⋙ p = P.ι ⋙ p := rfl
    set L := Functor.Fiber.mapOfComp (P.ι ⋙ p) p P.ι hrfl U
    have : P.ι.Full := ObjectProperty.full_ι P
    have : P.ι.Faithful := ObjectProperty.faithful_ι P
    have : L.Full := Functor.Fiber.full_mapOfComp hrfl U
    have : L.Faithful := Functor.Fiber.faithful_mapOfComp hrfl U
    refine ⟨fun f => ?_⟩
    have : IsIso (L.map f) := (𝒳.val.property.fiber_isGroupoid U).all_isIso (L.map f)
    exact isIso_of_fully_faithful L f
  exact Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid.mpr ⟨hFib, hGroups⟩

variable (B S hS) in
/-- The 1-morphism from the slice over a scheme `U` into `𝒳` attached to a scheme-valued point
`y` of `𝒳` over `U`, read on the model `𝒳 / U` of the algebraic stack of `U` whose points are
computed by `AlgebraicGeometry.Stack.schemePoint`. On objects it sends `T ⟶ U` to `y(T)`. -/
def slicePointBased (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳.val.val where
  toFunctor := PresheafOfCategories.sliceToElements U ⋙
    PresheafOfCategories.elementsToOverMap U.hom ⋙ y
  w := by
    change (PresheafOfCategories.sliceToElements U ⋙
      PresheafOfCategories.elementsToOverMap U.hom ⋙ y) ⋙ 𝒳.val.val.p = Over.forget U
    rw [Functor.assoc, Functor.assoc, hy, PresheafOfCategories.elementsToOverMap_map_eq]
    rfl

/-- **An open set of points cuts out an open subscheme of every scheme-valued point.** Let `W` be
an open subset of `|𝒳|` and `y` a scheme-valued point of `𝒳` over `U`. The points of `U` whose
image in `|𝒳|` lies in `W` form an open subscheme `V ⊆ U` (by continuity, **Stacks 04XL**), and
an object `T` of the big fppf site of `U` maps to `V` exactly when every point of `|𝒳|` through
`y(T)` lies in `W`. -/
theorem exists_isOpenImmersion_forall_nonempty_hom_iff
    {W : Set (AlgebraicStacks.points B S hS 𝒳)} (hW : @IsOpen _ (pointTopology B S hS 𝒳.val) W)
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, _root_.AlgebraicGeometry.IsOpenImmersion V.hom.hom ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ pointsInProperty W (y.obj T) := by
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  set Y := slicePointBased B S hS U y hy
  let φ : (BigFppfOver.toScheme B S hS).obj U → AlgebraicStacks.points B S hS 𝒳 :=
    fun z => pointsMap B S hS _ _ 𝒳.val.property Y ((pointsHomeomorphScheme B S hS U).symm z)
  have hφ : Continuous φ :=
    (continuous_pointsMap B S hS (schemeFibredCategory B S hS U) 𝒳.val Y).comp
      (pointsHomeomorphScheme B S hS U).symm.continuous
  have hφp : ∀ q : FieldValuedPoint B S hS (schemeFibredCategory B S hS U).val,
      φ (schemePoint B S hS U (pointClass B S hS _ (schemeFibredCategory B S hS U).property q)) =
        pointClass B S hS 𝒳.val.val 𝒳.val.property
          (fieldValuedPointMap B S hS _ Y q) := by
    intro q
    change pointsMap B S hS _ _ 𝒳.val.property Y ((pointsHomeomorphScheme B S hS U).symm
      (schemePoint B S hS U _)) = _
    rw [← pointsHomeomorphScheme_eq_schemePoint, Homeomorph.symm_apply_apply]
    rfl
  let O : ((BigFppfOver.toScheme B S hS).obj U).Opens := ⟨φ ⁻¹' W, hW.preimage hφ⟩
  refine ⟨BigFppfOver.opensObj B U.left.1 U.left.2 O, ?_, fun T => ?_⟩
  · rw [BigFppfOver.opensObj_hom_hom]
    infer_instance
  let g : (Over.map U.hom).obj T ⟶ U := Over.homMk T.hom
  have hyT : 𝒳.val.val.p.obj (y.obj T) = (Over.map U.hom).obj T := Functor.congr_obj hy T
  constructor
  · rintro ⟨k⟩ q ⟨a⟩
    have hk := BigFppfOver.range_le_of_hom B U.left.1 U.left.2 k
    let m : q.base ⟶ (Over.map U.hom).obj T :=
      eqToHom q.over.symm ≫ 𝒳.val.val.p.map a ≫ eqToHom hyT
    let qU : FieldValuedPoint B S hS (schemeFibredCategory B S hS U).val :=
      { carrier := q.carrier
        base := q.base
        isSpec := q.isSpec
        obj := Over.mk (m ≫ g)
        «over» := rfl }
    have hmem : φ (schemePoint B S hS U
        (pointClass B S hS _ (schemeFibredCategory B S hS U).property qU)) ∈ W := by
      refine hk ⟨(BigFppfOver.toScheme B S hS).map m (q.isSpec.inv
        (IsLocalRing.closedPoint q.carrier)), ?_⟩
      change _ = (BigFppfOver.toScheme B S hS).map (𝟙 _ ≫ (m ≫ g)) _
      rw [Category.id_comp, Functor.map_comp]
      rfl
    rw [hφp] at hmem
    convert hmem using 1
    let β : (Over.mk (m ≫ g) : Over U) ⟶ Over.mk g := Over.homMk m
    have : (schemeFibredCategory B S hS U).val.p.IsHomLift m β :=
      (Functor.IsHomLift.map (p := Over.forget U) β : _)
    have : 𝒳.val.val.p.IsHomLift m (Y.map β) :=
      Y.preserves_isHomLift m β
    have : 𝒳.val.val.p.IsStronglyCartesian m (Y.map β) :=
      𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift m (Y.map β)
    let a' : q.obj ⟶ Y.obj (Over.mk g) := a
    have : 𝒳.val.val.p.IsHomLift m a' := IsHomLift.of_fac 𝒳.val.val.p m a q.over hyT rfl
    exact (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2
      ⟨q, ⟨𝟙 _⟩, ⟨Functor.IsStronglyCartesian.map 𝒳.val.val.p m (Y.map β)
        (Category.id_comp m).symm a'⟩⟩
  · intro hT
    refine ⟨BigFppfOver.homOfRangeLe B U.left.1 U.left.2 O ?_⟩
    rintro _ ⟨t, rfl⟩
    have hc := B.residueField_spec_contains ((Over.map U.hom).obj T).left.property t
    let r := Space.residueFieldMap B S hS ((Over.map U.hom).obj T) t hc
    let qU : FieldValuedPoint B S hS (schemeFibredCategory B S hS U).val :=
      { carrier := T.left.1.residueField t
        base := Space.residueFieldObject B S hS ((Over.map U.hom).obj T) t hc
        isSpec := Iso.refl _
        obj := Over.mk (r ≫ g)
        «over» := rfl }
    have hpt : schemePoint B S hS U
        (pointClass B S hS _ (schemeFibredCategory B S hS U).property qU) = T.hom.hom t := by
      change (BigFppfOver.toScheme B S hS).map (𝟙 _ ≫ (r ≫ g)) _ = _
      rw [Category.id_comp, Functor.map_comp]
      exact congrArg T.hom.hom (T.left.1.fromSpecResidueField_apply t _)
    change φ (T.hom.hom t) ∈ W
    rw [← hpt, hφp]
    let β : (Over.mk (r ≫ g) : Over U) ⟶ Over.mk g := Over.homMk r
    exact hT _ ⟨Y.map β⟩

variable (B S hS) in
/-- The objects of `𝒳` all of whose points lie in an open set `W` of `|𝒳|` form an algebraic
stack: the inclusion of their full subcategory is representable by algebraic spaces, the 2-fibre
product with a scheme-valued point being the open subscheme
`AlgebraicGeometry.Stack.OpenSubstack.exists_isOpenImmersion_forall_nonempty_hom_iff`, and the
source of a 1-morphism representable by algebraic spaces into an algebraic stack is one
(**Stacks 05UM**). -/
theorem isAlgebraicStack_pointsInProperty {W : Set (AlgebraicStacks.points B S hS 𝒳)}
    (hW : @IsOpen _ (pointTopology B S hS 𝒳.val) W) :
    IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (pointsInProperty W)) :=
  isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS
    (𝒳 := CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 (pointsInProperty W))
      (isFiberedInGroupoids_pointsInProperty W)) (𝒴 := 𝒳.val)
    (Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedInclusion 𝒳 (pointsInProperty W)))
    (isRepresentableByAlgebraicSpaces_of_openLocus B S hS (pointsInProperty W)
      (fullSubcategoryBasedInclusion 𝒳 (pointsInProperty W)) rfl
      (exists_isOpenImmersion_forall_nonempty_hom_iff hW))
    𝒳.property

variable (B S hS) in
/-- **The open substack attached to an open set of points**: the full subcategory of the objects
all of whose points lie in an open subset `W` of `|𝒳|`. Its inclusion is an open immersion because
its 2-fibre product with every scheme-valued point is the open subscheme of points mapping into
`W`. -/
def ofIsOpen (W : Set (AlgebraicStacks.points B S hS 𝒳))
    (hW : @IsOpen _ (pointTopology B S hS 𝒳.val) W) : OpenSubstack 𝒳 where
  property := pointsInProperty W
  strictlyFull := inferInstance
  isAlgebraic := isAlgebraicStack_pointsInProperty B S hS hW
  isOpenImmersion :=
    ⟨isRepresentableByAlgebraicSpaces_of_openLocus B S hS (pointsInProperty W)
      (fullSubcategoryBasedInclusion 𝒳 (pointsInProperty W)) rfl
      (exists_isOpenImmersion_forall_nonempty_hom_iff hW),
    isOpenImmersion_of_openLocus B S hS (pointsInProperty W)
      (fullSubcategoryBasedInclusion 𝒳 (pointsInProperty W)) rfl
      (exists_isOpenImmersion_forall_nonempty_hom_iff hW)⟩

/-- The points of the open substack attached to an open set of points are that set. -/
theorem pointSet_ofIsOpen (W : Set (AlgebraicStacks.points B S hS 𝒳))
    (hW : @IsOpen _ (pointTopology B S hS 𝒳.val) W) :
    (ofIsOpen B S hS W hW).pointSet B S hS = W := by
  ext x
  rw [mem_pointSet_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp p ⟨𝟙 _⟩
  · intro hx
    induction x using Quotient.inductionOn with
    | h p =>
      refine ⟨p, fun q ⟨a⟩ => ?_, rfl⟩
      have hqp : pointClass B S hS 𝒳.val.val 𝒳.val.property q =
          pointClass B S hS 𝒳.val.val 𝒳.val.property p :=
        (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2 ⟨q, ⟨𝟙 _⟩, ⟨a⟩⟩
      rwa [hqp]

variable (B S hS)

/-! ### Stacks 06FJ -/

/-- Open substacks are ordered by inclusion, that is by their object properties. An open substack
is determined by its objects (`AlgebraicGeometry.Stack.OpenSubstack.ext`), so this is a partial
order. -/
instance : PartialOrder (OpenSubstack 𝒳) :=
  PartialOrder.lift OpenSubstack.property fun _ _ h => OpenSubstack.ext h

/-- Inclusion of open substacks is inclusion of their objects. -/
theorem le_iff_property_le {U V : OpenSubstack 𝒳} : U ≤ V ↔ U.property ≤ V.property :=
  Iff.rfl

/-- The open substack attached to the point set of an open substack is that open substack. -/
theorem ofIsOpen_pointSet (U : OpenSubstack 𝒳) :
    ofIsOpen B S hS (U.pointSet B S hS) (isOpen_pointSet B S hS U) = U :=
  OpenSubstack.ext (le_antisymm
    (property_le_of_pointSet_subset B S hS (pointSet_ofIsOpen _ _).le)
    (property_le_of_pointSet_subset B S hS (pointSet_ofIsOpen _ _).ge))

/-- **Stacks 06FJ.** Let `𝒳` be an algebraic stack. The rule `𝒰 ↦ |𝒰|` defines an inclusion
preserving bijection between open substacks of `𝒳` and open subsets of `|𝒳|`: the rule
`AlgebraicGeometry.Stack.OpenSubstack.opens` is bijective, and `|𝒰| ⊆ |𝒱|` holds exactly when
`𝒰 ⊆ 𝒱`.

Injectivity, and the reflection of inclusions, is
`AlgebraicGeometry.Stack.OpenSubstack.property_le_of_pointSet_subset`; surjectivity is
`AlgebraicGeometry.Stack.OpenSubstack.ofIsOpen` with
`AlgebraicGeometry.Stack.OpenSubstack.pointSet_ofIsOpen`; preservation of inclusions is
`AlgebraicGeometry.Stack.OpenSubstack.pointSet_mono`. -/
@[stacks 06FJ]
theorem bijective_opens_and_opens_le_iff :
    letI := pointTopology B S hS 𝒳.val
    Function.Bijective (opens B S hS (𝒳 := 𝒳)) ∧
      ∀ U V : OpenSubstack 𝒳, opens B S hS U ≤ opens B S hS V ↔ U ≤ V := by
  let := pointTopology B S hS 𝒳.val
  refine ⟨⟨fun U V h => ?_, fun W => ⟨ofIsOpen B S hS W W.isOpen, ?_⟩⟩, fun U V => ⟨fun h => ?_,
    fun h => opens_mono B S hS h⟩⟩
  · rw [← ofIsOpen_pointSet B S hS U, ← ofIsOpen_pointSet B S hS V]
    simp_rw [show U.pointSet B S hS = V.pointSet B S hS from congrArg SetLike.coe h]
  · exact TopologicalSpace.Opens.ext (pointSet_ofIsOpen _ W.isOpen)
  · exact property_le_of_pointSet_subset B S hS h

/-- **Stacks 06FJ**, as an order isomorphism: the rule `𝒰 ↦ |𝒰|` from the open substacks of `𝒳`,
ordered by inclusion, to the open subsets of `|𝒳|`. -/
noncomputable def opensOrderIso :
    letI := pointTopology B S hS 𝒳.val
    OpenSubstack 𝒳 ≃o TopologicalSpace.Opens (AlgebraicStacks.points B S hS 𝒳) :=
  letI := pointTopology B S hS 𝒳.val
  { Equiv.ofBijective _ (bijective_opens_and_opens_le_iff B S hS).1 with
    map_rel_iff' := (bijective_opens_and_opens_le_iff B S hS).2 _ _ }

/-- The order isomorphism of Stacks 06FJ is the rule `𝒰 ↦ |𝒰|`. -/
theorem opensOrderIso_apply (U : OpenSubstack 𝒳) :
    letI := pointTopology B S hS 𝒳.val
    opensOrderIso B S hS U = opens B S hS U :=
  rfl

end OpenSubstack

end AlgebraicGeometry.Stack

end
