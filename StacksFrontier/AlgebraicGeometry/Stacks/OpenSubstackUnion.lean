module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Unions of open substacks (Stacks 05UQ)

Let `𝒳` be an algebraic stack over `S` and let `𝒳ᵢ ⊆ 𝒳`, `i ∈ I`, be open substacks
(**Stacks 04YM**, part (1)). **Stacks 05UQ** asserts that there is an open substack
`⋃_{i ∈ I} 𝒳ᵢ ⊆ 𝒳` of which the `𝒳ᵢ` are open substacks covering it. This file proves it,
together with the uniqueness that makes the notation legitimate.

## Main definitions

* `AlgebraicGeometry.Stack.OpenSubstack.IsUnion`: a property of the objects of `𝒳` is the union
  of a family of open substacks when it contains every member and every object with the property
  lies, locally on the big fppf site, in a member. This is the conclusion of **Stacks 05UQ**
  written as a predicate, with "covering" read as in
  `AlgebraicGeometry.Stack.IsOpenSubstackCover`.
* `AlgebraicGeometry.Stack.OpenSubstack.iUnion`: the union `⋃_{i ∈ I} 𝒳ᵢ`, the open substack
  attached by **Stacks 06FJ** to the open set of points `⋃_{i ∈ I} |𝒳ᵢ|`.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.isUnion_iUnion`: `⋃_{i ∈ I} 𝒳ᵢ` is the union of the
  family.
* `AlgebraicGeometry.Stack.OpenSubstack.pointSet_iUnion`: its points are `⋃_{i ∈ I} |𝒳ᵢ|`.
* `AlgebraicGeometry.Stack.OpenSubstack.eq_of_isUnion`: the union of a family of open substacks
  is unique.
* `AlgebraicGeometry.Stack.OpenSubstack.exists_openSubstack_of_isUnion`: the members of the
  family are open substacks of the union, with exactly their own objects.
* `AlgebraicGeometry.Stack.OpenSubstack.exists_isUnion`: **Stacks 05UQ**.
* `AlgebraicGeometry.Stack.OpenSubstack.exists_openSubstack_restrict`: for any two open
  substacks `𝒰`, `𝒱` of `𝒳`, the objects of `𝒱` lying in `𝒰` cut out an open substack of `𝒱`.

## Implementation notes

*Existence.* The source cuts out `⋃_{i ∈ I} 𝒳ᵢ` by the objects `x` over `T` for which
`∐_{i ∈ I} 𝒳ᵢ ×_𝒳 T ⟶ T` is surjective and invokes **Stacks 05UN**. Here the union is read
through **Stacks 06FJ** instead: it is `AlgebraicGeometry.Stack.OpenSubstack.ofIsOpen` at the
open set `⋃_{i ∈ I} |𝒳ᵢ|`, whose objects are those all of whose points lie in some `|𝒳ᵢ|`. It
contains each `𝒳ᵢ` because `|𝒳ᵢ|` lies in its point set and 06FJ reflects inclusions. It is
covered by the family because, for an object `x` over `T`, each `𝒳ᵢ` cuts out an open subscheme
`Tᵢ ⊆ T` of the scheme-valued point named by `x` (the open subscheme of points of `T` mapping into
`|𝒳ᵢ|`), the `Tᵢ` cover `T` since the point of `|𝒳|` through `x` at each residue field of `T` lies
in some `|𝒳ᵢ|`, and the Zariski covering `{Tᵢ ⟶ T}` is an fppf covering on whose members `x`
restricts into the `𝒳ᵢ`.

*Uniqueness* is fppf-locality of membership of a substack,
`AlgebraicGeometry.Stack.prop_of_locally_isoOverId`: an object of one candidate union lies,
over a covering sieve, in members of the family, hence in the other candidate, which being
strictly full and algebraic absorbs the local information. Open substacks are determined by
their objects, `AlgebraicGeometry.Stack.OpenSubstack.ext`, so the two candidates coincide.

That a member is an open substack of the union is the restriction result, applied to a member and
the union. The restriction of `𝒰` to `𝒱` is the base change `𝒰 ×_𝒳 𝒱 ⟶ 𝒱`, an open immersion by
`AlgebraicGeometry.Stack.isOpenImmersion_baseChange` and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange` (**Stacks 045C** and
**Stacks 0302**), whose essential image is an open substack of `𝒱` by
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_openSubstack_essImage` (**Stacks 0506**); that
essential image consists of the objects of `𝒱` lying in `𝒰` because an object of the 2-fibre
product is an object of `𝒱` together with an object of `𝒰` and a vertical isomorphism between
their images in `𝒳`.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
* [Stacks Project, Tag 05UQ](https://stacks.math.columbia.edu/tag/05UQ)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace OpenSubstack

/-- A property of the objects of an algebraic stack `𝒳` over `S` is *the union* of a family
`𝒰 : I → OpenSubstack 𝒳` when it contains every member of the family and every object with the
property lies, over the members of some covering sieve of the fppf topology, in a member of the
family.

The second clause is "the `𝒰 i` cover it" in the form that
`AlgebraicGeometry.Stack.IsOpenSubstackCover` uses, read for objects of `𝒳` with the property
rather than for objects of the subcategory they cut out. -/
def IsUnion (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type*} (𝒰 : I → OpenSubstack 𝒳)
    (P : ObjectProperty 𝒳.val.val.obj) : Prop :=
  haveI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  (∀ i, (𝒰 i).property ≤ P) ∧
    ∀ (T : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber T), P x.1 →
      ∃ R ∈ BigFppfOver.topology B S hS T,
        ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ T), R.arrows f →
          ∃ i, (𝒰 i).property (Functor.pullbackFiber 𝒳.val.val.p x f).1

/-- An open substack whose objects are the union of a family of open substacks contains every
open substack with the same two properties: the objects of the latter lie locally in members of
the family, hence in the former, membership of a substack being local on the big fppf site. -/
theorem le_of_isUnion {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*} {𝒰 : I → OpenSubstack 𝒳}
    {W W' : OpenSubstack 𝒳} (h : IsUnion 𝒳 𝒰 W.property) (h' : IsUnion 𝒳 𝒰 W'.property) :
    W.property ≤ W'.property := by
  intro x hx
  have hfib : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have := W'.strictlyFull
  obtain ⟨R, hR, hmem⟩ := h.2 (𝒳.val.val.p.obj x) ⟨x, rfl⟩ hx
  refine prop_of_locally_isoOverId W'.isAlgebraic ⟨x, rfl⟩ hR fun _ k hk => ?_
  obtain ⟨i, hi⟩ := hmem k hk
  exact Functor.isoOverId_of_prop (h'.1 i _ hi)

/-- The union of a family of open substacks is unique: an open substack of `𝒳` which contains
every member of the family and is covered by the family is determined by the family. This is what
makes the notation `⋃_{i ∈ I} 𝒳ᵢ` of the source legitimate. -/
@[stacks 05UQ "uniqueness of the union"]
theorem eq_of_isUnion {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*} {𝒰 : I → OpenSubstack 𝒳}
    {W W' : OpenSubstack 𝒳} (h : IsUnion 𝒳 𝒰 W.property) (h' : IsUnion 𝒳 𝒰 W'.property) :
    W = W' :=
  OpenSubstack.ext (le_antisymm (le_of_isUnion h h') (le_of_isUnion h' h))

/-- The objects of an open substack `𝒱` of `𝒳` which lie in an open substack `𝒰` of `𝒳` cut out
an open substack of `𝒱`.

It is the base change `𝒰 ×_𝒳 𝒱 ⟶ 𝒱`, which is an open immersion, read through its essential
image. -/
theorem exists_openSubstack_restrict {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (𝒰 𝒱 : OpenSubstack 𝒳) :
    ∃ W : OpenSubstack (fullSubcategoryAlgebraicStack 𝒳 𝒱.property 𝒱.isAlgebraic),
      ∀ y : 𝒱.property.FullSubcategory, W.property y ↔ 𝒰.property y.obj := by
  have := 𝒰.strictlyFull
  let i := fullSubcategoryInclusion 𝒳 𝒱.property 𝒱.isAlgebraic
  let j := fullSubcategoryInclusion 𝒳 𝒰.property 𝒰.isAlgebraic
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} i.hom j.hom
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      i.hom j.hom
  have hrepr : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ j.hom i.hom Q hQ
      𝒰.isOpenImmersion.1
  have hoi : Stack.IsOpenImmersion B S hS Q.fst :=
    isOpenImmersion_baseChange.{u, u, u + 1} B S hS _ _ _ j.hom i.hom Q hQ 𝒰.isOpenImmersion.2
  obtain ⟨W, hW⟩ := AlgebraicStacks.exists_openSubstack_essImage
    (twoFibreProductSquareAlgebraicStacks B S hS i j).fst ⟨hrepr, hoi⟩
  refine ⟨W, fun y => ?_⟩
  rw [hW]
  constructor
  · rintro ⟨z, ⟨e⟩⟩
    exact 𝒰.property.prop_of_iso (z.iso.symm ≪≫ i.hom.hom.toFunctor.mapIso e) z.y.property
  · intro hyU
    exact ⟨{ base := (fullSubcategoryAlgebraicStack 𝒳 𝒱.property 𝒱.isAlgebraic).val.val.p.obj y
             x := y
             y := ⟨i.hom.hom.toFunctor.obj y, hyU⟩
             hx := rfl
             hy := i.hom.hom.w_obj y
             iso := Iso.refl _
             vertical := IsHomLift.id (i.hom.hom.w_obj y) }, ⟨Iso.refl _⟩⟩

/-- The members of a family of open substacks are open substacks of its union. If an open
substack `W` of `𝒳` is the union of a family `𝒰 : I → OpenSubstack 𝒳`, then each `𝒰 i` is an
open substack of `W`: there are open substacks `V i` of `W` whose objects are, under the
inclusion of `W` into `𝒳`, exactly the objects of `𝒰 i`. -/
@[stacks 05UQ "the members of the family are open substacks of the union"]
theorem exists_openSubstack_of_isUnion {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*}
    {𝒰 : I → OpenSubstack 𝒳} {W : OpenSubstack 𝒳} (h : IsUnion 𝒳 𝒰 W.property) :
    ∃ V : I → OpenSubstack (fullSubcategoryAlgebraicStack 𝒳 W.property W.isAlgebraic),
      ∀ (i : I) (x : 𝒳.val.val.obj),
        (𝒰 i).property x ↔ ∃ hx : W.property x, (V i).property ⟨x, hx⟩ := by
  refine ⟨fun i => (exists_openSubstack_restrict (𝒰 i) W).choose, fun i x => ?_⟩
  have hspec := (exists_openSubstack_restrict (𝒰 i) W).choose_spec
  exact ⟨fun hx => ⟨h.1 i x hx, (hspec ⟨x, h.1 i x hx⟩).2 hx⟩,
    fun ⟨hx, hV⟩ => (hspec ⟨x, hx⟩).1 hV⟩

/-! ### Existence of the union -/

/-- An open substack is the open substack attached to its own point set, so its objects are those
all of whose points lie in its point set. -/
theorem property_eq_pointsInProperty {𝒳 : AlgebraicStacks.{u, w} B S hS} (U : OpenSubstack 𝒳) :
    U.property = pointsInProperty (U.pointSet B S hS) :=
  congrArg OpenSubstack.property (ofIsOpen_pointSet B S hS U).symm

/-- **The union of a family of open substacks**, `⋃_{i ∈ I} 𝒳ᵢ`: the open substack of `𝒳`
attached by Stacks 06FJ to the open subset `⋃_{i ∈ I} |𝒳ᵢ|` of `|𝒳|`. Its objects are those of
`𝒳` all of whose points lie in some `|𝒳ᵢ|`. -/
def iUnion {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*} (𝒰 : I → OpenSubstack 𝒳) :
    OpenSubstack 𝒳 :=
  letI := pointTopology B S hS 𝒳.val
  ofIsOpen B S hS (⋃ i, (𝒰 i).pointSet B S hS)
    (isOpen_iUnion fun i => isOpen_pointSet B S hS (𝒰 i))

/-- The points of the union of a family of open substacks are the union of their points. -/
theorem pointSet_iUnion {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) :
    (iUnion 𝒰).pointSet B S hS = ⋃ i, (𝒰 i).pointSet B S hS :=
  pointSet_ofIsOpen _ _

/-- Every member of a family of open substacks is contained in their union. -/
theorem property_le_iUnion {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) (i : I) : (𝒰 i).property ≤ (iUnion 𝒰).property :=
  property_le_of_pointSet_subset B S hS
    ((Set.subset_iUnion (fun j => (𝒰 j).pointSet B S hS) i).trans (pointSet_iUnion 𝒰).ge)

/-- **The union of a family of open substacks is covered by the family.** Let `x` be an object of
`⋃_{i ∈ I} 𝒳ᵢ` over `T`. For each `i` the objects of `𝒳ᵢ` cut out an open subscheme `Tᵢ ⊆ T` of
the scheme-valued point named by `x`
(`AlgebraicGeometry.Stack.OpenSubstack.exists_isOpenImmersion_forall_nonempty_hom_iff`); the
`Tᵢ` cover `T`, because the point of `|𝒳|` through `x` at a residue field of `T` lies in some
`|𝒳ᵢ|`; and the restriction of `x` to any scheme over some `Tᵢ` lies in `𝒳ᵢ`. -/
theorem isUnion_iUnion {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) : IsUnion 𝒳 𝒰 (iUnion 𝒰).property := by
  refine ⟨property_le_iUnion 𝒰, ?_⟩
  intro T x hx
  have hfib : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  set y := fibrePoint B S hS 𝒳.val T x
  have hy : y ⋙ 𝒳.val.val.p = Over.map T.hom := fibrePoint_comp B S hS 𝒳.val T x
  choose V hV hVy using fun i =>
    exists_isOpenImmersion_forall_nonempty_hom_iff (isOpen_pointSet B S hS (𝒰 i)) T y hy
  refine ⟨_, BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS
    (X := fun i => (Over.map T.hom).obj (V i))
    (fun i => (Over.homMk (V i).hom : (Over.map T.hom).obj (V i) ⟶ T)) (fun i => hV i) ?_, ?_⟩
  · intro t
    have hc := B.residueField_spec_contains T.left.property t
    let r := Space.residueFieldMap B S hS T t hc
    let T' : BigFppfOver B T.left.1 T.left.2 := Over.mk r.left
    let p₀ : FieldValuedPoint B S hS 𝒳.val.val :=
      { carrier := T.left.1.residueField t
        base := (Over.map T.hom).obj T'
        isSpec := Iso.refl _
        obj := y.obj T'
        «over» := Functor.congr_obj hy T' }
    have hφ : Nonempty (p₀.obj ⟶ x.1) :=
      ⟨(Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids T x
        ((Over.iteratedSliceBackward T).obj T')).φ⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hx p₀ hφ)
    have hT' : pointsInProperty ((𝒰 i).pointSet B S hS) (y.obj T') := by
      intro q ⟨a⟩
      have hqp : pointClass B S hS 𝒳.val.val 𝒳.val.property q =
          pointClass B S hS 𝒳.val.val 𝒳.val.property p₀ :=
        (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2 ⟨q, ⟨𝟙 _⟩, ⟨a⟩⟩
      rwa [hqp]
    obtain ⟨k⟩ := (hVy i T').2 hT'
    have hk : k.left ≫ (V i).hom = r.left := Over.w k
    have ht : t ∈ Set.range (T.left.1.fromSpecResidueField t) :=
      ⟨IsLocalRing.closedPoint _, T.left.1.fromSpecResidueField_apply t _⟩
    change t ∈ Set.range r.left.hom at ht
    rw [← hk] at ht
    obtain ⟨z, hz⟩ := ht
    exact ⟨i, k.left.hom z, hz⟩
  · rintro W f ⟨_, g, _, ⟨i⟩, rfl⟩
    refine ⟨i, ?_⟩
    rw [property_eq_pointsInProperty (𝒰 i)]
    let f' := g ≫ (Over.homMk (V i).hom : (Over.map T.hom).obj (V i) ⟶ T)
    let T'' : BigFppfOver B T.left.1 T.left.2 := Over.mk f'.left
    have hT'' := (hVy i T'').1 ⟨Over.homMk g.left⟩
    let c := Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids T x
      ((Over.iteratedSliceBackward T).obj T'')
    let m : W ⟶ (Over.map T.hom).obj T'' := Over.homMk (𝟙 W.left) (by
      simp [T'', Over.w f'])
    have hm : f' = m ≫ ((Over.iteratedSliceBackward T).obj T'').hom :=
      Over.OverMorphism.ext (Category.id_comp f'.left).symm
    have hc : 𝒳.val.val.p.IsStronglyCartesian ((Over.iteratedSliceBackward T).obj T'').hom c.φ :=
      c.isStronglyCartesian
    let a : (Functor.pullbackFiber 𝒳.val.val.p x f').1 ⟶ c.y :=
      @Functor.IsStronglyCartesian.map _ _ _ _ 𝒳.val.val.p _ _ _ _
        ((Over.iteratedSliceBackward T).obj T'').hom c.φ hc _ _ _ _ hm
        (Functor.IsPreFibered.pullbackMap x.2 f') _
    exact pointsInProperty_of_hom hT'' a

/-- **Stacks 05UQ.** Let `𝒳` be an algebraic stack and `𝒳ᵢ ⊆ 𝒳`, `i ∈ I`, a collection of open
substacks. Then there is an open substack `⋃_{i ∈ I} 𝒳ᵢ ⊆ 𝒳` such that the `𝒳ᵢ` are open
substacks covering it.

The open substack is `AlgebraicGeometry.Stack.OpenSubstack.iUnion 𝒰`. It is the union of the
family in the sense of `AlgebraicGeometry.Stack.OpenSubstack.IsUnion`: it contains every `𝒳ᵢ`,
and every object of it lies, over the members of a covering sieve of the fppf topology, in some
`𝒳ᵢ`. Its points are `⋃_{i ∈ I} |𝒳ᵢ|`, so `∐_{i ∈ I} 𝒳ᵢ ⟶ ⋃_{i ∈ I} 𝒳ᵢ` is surjective. Each `𝒳ᵢ`
is an open substack `V i` of it. And it is the only open substack of `𝒳` that is the union of the
family, which is what makes the notation `⋃_{i ∈ I} 𝒳ᵢ` legitimate. -/
@[stacks 05UQ]
theorem exists_isUnion {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) :
    ∃ W : OpenSubstack 𝒳,
      (IsUnion 𝒳 𝒰 W.property ∧ W.pointSet B S hS = ⋃ i, (𝒰 i).pointSet B S hS ∧
        ∃ V : I → OpenSubstack (fullSubcategoryAlgebraicStack 𝒳 W.property W.isAlgebraic),
          ∀ (i : I) (x : 𝒳.val.val.obj),
            (𝒰 i).property x ↔ ∃ hx : W.property x, (V i).property ⟨x, hx⟩) ∧
      ∀ W' : OpenSubstack 𝒳, IsUnion 𝒳 𝒰 W'.property → W' = W :=
  ⟨iUnion 𝒰, ⟨isUnion_iUnion 𝒰, pointSet_iUnion 𝒰,
    exists_openSubstack_of_isUnion (isUnion_iUnion 𝒰)⟩,
    fun _ hW' => eq_of_isUnion hW' (isUnion_iUnion 𝒰)⟩

end OpenSubstack

end AlgebraicGeometry.Stack

end
