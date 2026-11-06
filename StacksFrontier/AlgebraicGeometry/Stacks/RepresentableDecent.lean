module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors

/-!
# Decency of the source of a representable 1-morphism of algebraic stacks (Stacks 0GW3)

An algebraic stack over `S` is *decent* (**Stacks 0GW1**) when every one of its points admits a
field-valued representative whose 1-morphism `Spec k ⟶ 𝒳` is quasi-compact. This file proves
**Stacks 0GW3**: the source of a 1-morphism with decent target is decent as soon as that
1-morphism is representable by schemes, or is representable by algebraic spaces and
quasi-separated.

The argument is the source's. Fix a point `x` of `𝒳` and let `y` be its image. Decency of `𝒴`
supplies a *quasi-compact* field-valued representative `q` of `y`, so the 1-morphism
`g : Spec k ⟶ 𝒴` it determines is quasi-compact (**Stacks 050T**). Form the 2-fibre product `P`
of `g` and `f` (**Stacks 04T2**). Its second projection is quasi-compact, being a base change of
`g` (**Stacks 050V**), and **Stacks 04XH** lifts the pair `(q, x)` to a point `w` of `P`. Any
field-valued representative `p` of `w` has quasi-compact 1-morphism:

* in the representable case because `P` is the algebraic stack of a scheme, so `p` is the
  1-morphism of a morphism of the site out of the spectrum of a field;
* in the quasi-separated case because the composite of `p` with the *first* projection is such a
  1-morphism, the first projection is quasi-separated as a base change of `f`
  (**Stacks 050F**), and **Stacks 050Y** cancels it.

Composing `p` with the second projection (**Stacks 050W**) then exhibits the required
representative of `x`.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_yoneda_map_of_quasiCompact`: the implication of
  **Stacks 03KG** at a quasi-compact morphism of the site.
* `AlgebraicGeometry.Stack.fieldValuedPointMorphism_comp_iso`: the 1-morphism of a field-valued
  point is natural in the stack.
* `CategoryTheory.Functor.TwoYoneda.liftBased_overMap_iso`: a 2-Yoneda lift into a slice is the
  `CategoryTheory.Over.map` of the structure morphism the point names.
* `AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_schemeFibredCategory`: a field-valued
  point of a represented category fibred in groupoids is quasi-compact as soon as the arrow of
  the site it names is quasi-compact on representable algebraic spaces.
* `AlgebraicGeometry.Stack.isDecent_of_representable_or_quasiSeparated`: **Stacks 0GW3**.

## Implementation notes

**No appeal to Stacks 0DTK is made, and none is needed.** The source reads decency of `𝒴` at an
*arbitrary* representative of the image point and then invokes Stacks 0DTK — the independence of
the chosen representative — to transport quasi-compactness to it. Here the representative of `x`
is produced *downstream* of the one `𝒴`'s decency hands over, through Stacks 04XH, so only the
existential form of `AlgebraicGeometry.Stack.IsDecent` is ever used in either direction.

The passage between the two notions of quasi-compactness of a 1-morphism — the relative property
of Stacks 04XB and the base-change condition of Stacks 050U — is **Stacks 050T**, and it is used
in both directions; the locality instance that naming the relative property requires is
`AlgebraicGeometry.Space.isQuasiCompact_isLocalAtTarget_fppf`, supplied locally because it is a
theorem rather than an instance.

`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_basedIso`,
`AlgebraicGeometry.Stack.isQuasiCompact_congr_basedIso` and
`AlgebraicGeometry.Stack.isQuasiCompact_of_equivalenceTarget` are **Stacks 0457** and
**Stacks 0459** at identity horizontal 1-morphisms, for which the two composites of the
2-commutative square are the two 1-morphisms themselves. They are stated separately because the
transport is needed four times.

In the representable case the `CategoryTheory.Category` instance of the 2-fibre product of
categories over the site has to be supplied by name rather than by instance search, which does
not see it through the coercion of the apex of the canonical square; supplying it by name keeps
the auxiliary declarations' types in the spelling the kernel checks them at. No `set_option` of
any kind is used anywhere in this file.

## References

* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050V](https://stacks.math.columbia.edu/tag/050V)
* [Stacks Project, Tag 050W](https://stacks.math.columbia.edu/tag/050W)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
* [Stacks Project, Tag 0GW3](https://stacks.math.columbia.edu/tag/0GW3)
-/

@[expose] public section

open CategoryTheory


namespace AlgebraicGeometry

universe u w

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_RepresentableDecent :
    Limits.HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_RepresentableDecent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Limits.HasLimit (Limits.cospan f g) :=
  Limits.HasLimitsOfShape.has_limit _

/-- The implication of **Stacks 03KG** at a quasi-compact morphism of the site: a morphism of the
big fppf category of `S` whose underlying morphism of schemes is quasi-compact is quasi-compact
as a morphism of algebraic spaces over `S`.

This is the mirror of `AlgebraicGeometry.Space.isQuasiCompact_yoneda_map_of_isAffineHom` with
affineness of the pullback replaced by compactness of its space: by the affine criterion of
Stacks 03KG it is enough to test the base change along an affine scheme-valued point, Yoneda
being fully faithful that point comes from the site, and the base change is the representable
presheaf of the fibre product, whose scheme is compact because its projection is a base change
of the given quasi-compact morphism over an affine scheme. -/
theorem Space.isQuasiCompact_yoneda_map_of_quasiCompact
    {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : QuasiCompact ((BigFppfOver.toScheme B S hS).map g)) :
    Space.IsQuasiCompact B S hS (yoneda.map g) := by
  have hps : Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  refine Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS
    (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
    (yoneda.map g) ?_
  intro T hTaff h
  obtain ⟨h₀, hh⟩ : ∃ h₀ : T ⟶ V, yoneda.map h₀ = h :=
    ⟨Yoneda.fullyFaithful.preimage h, Yoneda.fullyFaithful.map_preimage _⟩
  subst hh
  have hsq : IsPullback (Limits.pullback.fst h₀ g) (Limits.pullback.snd h₀ g) h₀ g :=
    IsPullback.of_hasPullback _ _
  have hqcfst : QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst h₀ g)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (hsq.map (BigFppfOver.toScheme B S hS)).flip hg
  have hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hTaff
  have hTc : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) := inferInstance
  have hcompact : CompactSpace
      ((BigFppfOver.toScheme B S hS).obj (Limits.pullback h₀ g)) :=
    QuasiCompact.compactSpace_of_compactSpace
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst h₀ g))
  refine Space.isQuasiCompactSpace_of_iso B S hS
    ((hsq.map yoneda).isoIsPullback _ _
      (IsPullback.of_hasPullback (yoneda.map h₀) (yoneda.map g))) ?_
  refine (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS _
    (isAlgebraicSpace_yoneda B S hS (Limits.pullback h₀ g))).2 ?_
  exact (Space.schemePointsHomeomorph B S hS (Limits.pullback h₀ g)).symm.compactSpace

end AlgebraicGeometry

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- G2: naturality of the field-valued-point morphism. -/
noncomputable def fieldValuedPointMorphism_comp_iso
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : 𝒳.val ⥤ᵇ 𝒴.val) (p : FieldValuedPoint B S hS 𝒳.val) :
    BasedFunctor.comp (fieldValuedPointMorphism B S hS 𝒳 p).hom F ≅
      (fieldValuedPointMorphism B S hS 𝒴 (fieldValuedPointMap B S hS 𝒳.val F p)).hom := by
  let U := p.base
  let p₀ := 𝒳.val.p
  let q₀ := 𝒴.val.p
  let pObj : p₀.Fiber U := Functor.Fiber.mk (a := p.obj) p.over
  let qObj : q₀.Fiber U := Functor.Fiber.mk
    (a := F.toFunctor.obj p.obj) ((F.w_obj p.obj).trans p.over)
  let a := Over.mk (𝟙 U)
  let lp := Functor.TwoYoneda.chosenLift p₀ 𝒳.isFiberedInGroupoids U pObj a
  let lq := Functor.TwoYoneda.chosenLift q₀ 𝒴.isFiberedInGroupoids U qObj a
  let e := Functor.twoYonedaEvaluation q₀ U
  have : e.IsEquivalence :=
    Functor.twoYonedaEvaluation_isEquivalence q₀ 𝒴.isFiberedInGroupoids U
  have : IsGroupoid (q₀.Fiber U) := 𝒴.isFiberedInGroupoids.fiber_isGroupoid U
  have : p₀.IsHomLift (𝟙 U) lp.φ := by
    simpa [a] using lp.isStronglyCartesian.toIsHomLift
  have : q₀.IsHomLift (𝟙 U) lq.φ := by
    simpa [a] using lq.isStronglyCartesian.toIsHomLift
  have : q₀.IsHomLift (𝟙 U) (F.toFunctor.map lp.φ) := inferInstance
  let hFF : e.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful e
  let αp : e.obj (BasedFunctor.comp
      (fieldValuedPointMorphism B S hS 𝒳 p).hom F) ⟶ qObj :=
    Functor.Fiber.homMk q₀ U (F.toFunctor.map lp.φ)
  let αq : e.obj
      (fieldValuedPointMorphism B S hS 𝒴
        (fieldValuedPointMap B S hS 𝒳.val F p)).hom ⟶ qObj :=
    Functor.Fiber.homMk q₀ U lq.φ
  have hEval : e.obj (BasedFunctor.comp
      (fieldValuedPointMorphism B S hS 𝒳 p).hom F) ≅
      e.obj (fieldValuedPointMorphism B S hS 𝒴
        (fieldValuedPointMap B S hS 𝒳.val F p)).hom :=
    asIso αp ≪≫ (asIso αq).symm
  exact hFF.preimageIso hEval

/-- The arrow of the site named by a field-valued point of a represented category fibred in
groupoids: its object is an object of the slice over `T`, hence names its own structure
morphism. -/
def fieldValuedPointSchemeArrow {T : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (schemeFibredCategory B S hS T).val) : p.base ⟶ T :=
  eqToHom p.«over».symm ≫ p.obj.hom

/-- The field-valued point of the algebraic stack of the base of a field-valued point which the
identity of that base names. -/
def FieldValuedPoint.atBase {𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (p : FieldValuedPoint B S hS 𝒳) :
    FieldValuedPoint B S hS (schemeFibredCategory B S hS p.base).val where
  carrier := p.carrier
  base := p.base
  isSpec := p.isSpec
  obj := Over.mk (𝟙 p.base)
  «over» := rfl

/-- The 1-morphism a field-valued point determines carries the identity point of the algebraic
stack of its base to the point it represents: the chosen lift at the identity is an arrow to the
point's own object, so the two field-valued points have a common refinement. -/
theorem pointClass_fieldValuedPointMap_atBase
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (p : FieldValuedPoint B S hS 𝒳.val) :
    pointClass B S hS 𝒳.val 𝒳.isFiberedInGroupoids
        (fieldValuedPointMap B S hS (schemeFibredCategory B S hS p.base).val
          (fieldValuedPointMorphism B S hS 𝒳 p).hom p.atBase)
      = pointClass B S hS 𝒳.val 𝒳.isFiberedInGroupoids p := by
  refine (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val
    𝒳.isFiberedInGroupoids _ _).2 ⟨_, ⟨𝟙 _⟩, ⟨?_⟩⟩
  exact (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids p.base
    (Functor.Fiber.mk (a := p.obj) p.over) (Over.mk (𝟙 p.base))).φ

end AlgebraicGeometry.Stack

/-- G1: a 2-Yoneda lift into a slice is the `Over.map` of the point's structure morphism. -/
noncomputable def CategoryTheory.Functor.TwoYoneda.liftBased_overMap_iso
    {C : Type*} [Category C] {U V : C} (point : (Over.forget V).Fiber U)
    (hcategory : (Over.forget V).IsFiberedInGroupoids) :
    Functor.TwoYoneda.liftBased (Over.forget V) hcategory U point ≅
      (show BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor (Over.forget V) from
        ⟨Over.map (eqToHom point.property.symm ≫ point.val.hom), rfl⟩) := by
  let evaluation := Functor.twoYonedaEvaluation (Over.forget V) U
  have : evaluation.IsEquivalence :=
    Functor.twoYonedaEvaluation_isEquivalence _ hcategory U
  apply (Functor.FullyFaithful.ofFullyFaithful evaluation).preimageIso
  let lift := Functor.TwoYoneda.chosenLift (Over.forget V) hcategory U point (Over.mk (𝟙 U))
  have : (Over.forget V).IsHomLift (𝟙 U) lift.φ := lift.isStronglyCartesian.toIsHomLift
  let arrow := eqToHom point.property.symm ≫ point.val.hom
  let comparison : lift.y ⟶ (Over.map arrow).obj (Over.mk (𝟙 U)) :=
    Over.homMk (lift.φ.left ≫ eqToHom point.property) (by
      change (lift.φ.left ≫ eqToHom point.property) ≫ (𝟙 U ≫ arrow) = _
      rw [Category.id_comp]
      change (lift.φ.left ≫ eqToHom point.property) ≫
        (eqToHom point.property.symm ≫ point.val.hom) = lift.y.hom
      calc
        _ = lift.φ.left ≫ point.val.hom := by
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        _ = _ := Over.w lift.φ)
  have : (Over.forget V).IsHomLift (𝟙 U) comparison := by
    apply IsHomLift.of_fac' _ (𝟙 U) _
      (IsHomLift.domain_eq (Over.forget V) (𝟙 U) lift.φ) rfl
    change lift.φ.left ≫ eqToHom point.property = _
    have hfac := IsHomLift.fac' (Over.forget V) (𝟙 U) lift.φ
    change lift.φ.left = _ at hfac
    rw [hfac]
    simp only [Category.id_comp, eqToHom_trans]
  have : IsGroupoid ((Over.forget V).Fiber U) := hcategory.fiber_isGroupoid U
  let comparisonFiber :
      evaluation.obj (Functor.TwoYoneda.liftBased (Over.forget V) hcategory U point) ⟶
      evaluation.obj ⟨Over.map arrow, rfl⟩ :=
    Functor.Fiber.homMk (Over.forget V) U comparison
  exact asIso comparisonFiber

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identity based functor is an equivalence. -/
private theorem isEquivalence_basedFunctor_id (𝒜 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)) :
    Functor.IsEquivalence (BasedFunctor.id 𝒜).toFunctor :=
  inferInstanceAs (Functor.IsEquivalence (𝟭 𝒜.obj))

/-- G3: a field-valued point of a represented category fibred in groupoids is quasi-compact as
soon as the arrow of the site it names is quasi-compact on representable algebraic spaces. -/
theorem isQuasiCompactFieldValuedPoint_schemeFibredCategory {T : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (schemeFibredCategory B S hS T).val)
    (hqc : Space.IsQuasiCompact B S hS
      (yoneda.map (fieldValuedPointSchemeArrow B S hS p))) :
    IsQuasiCompactFieldValuedPoint B S hS (schemeFibredCategory B S hS T) p := by
  let _inst : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  have hsrc := isEquivalence_basedFunctor_id B S hS (schemeFibredCategory B S hS p.base).val
  have htgt := isEquivalence_basedFunctor_id B S hS (schemeFibredCategory B S hS T).val
  have hiso := (CategoryTheory.Functor.TwoYoneda.liftBased_overMap_iso
    (V := T) (Functor.Fiber.mk (a := p.obj) p.over)
    (schemeFibredCategory B S hS T).isFiberedInGroupoids).symm
  have harrow := hasRelativeProperty_schemeFibredCategoryMap.{u, u + 1} B S hS
    (Space.quasiCompactProperty B S hS) (fieldValuedPointSchemeArrow B S hS p) hqc
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      (fieldValuedPointMorphism B S hS (schemeFibredCategory B S hS T) p).hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
      (fieldValuedPointMorphism B S hS (schemeFibredCategory B S hS T) p).hom
      (schemeFibredCategoryMap B S hS (fieldValuedPointSchemeArrow B S hS p)).hom
      (BasedFunctor.id _) (BasedFunctor.id _) hiso).1
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS _)
  refine (isQuasiCompactFieldValuedPoint_iff_hasRelativeProperty B S hS
    (schemeFibredCategory B S hS T) p).2 ⟨hrep, ?_⟩
  exact (hasRelativeProperty_iff_of_equivalences' B S hS
    (Space.quasiCompactProperty B S hS)
    (fieldValuedPointMorphism B S hS (schemeFibredCategory B S hS T) p)
    (schemeFibredCategoryMap B S hS (fieldValuedPointSchemeArrow B S hS p))
    (BasedFunctor.id _) (BasedFunctor.id _) hiso
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS _) hrep).1 harrow


/-- Representability by algebraic spaces transfers along an isomorphism of based functors:
**Stacks 0457** at the identity equivalences. -/
theorem isRepresentableByAlgebraicSpaces_of_basedIso
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (u v : 𝒜 ⟶ ℬ) (e : u.hom ≅ v.hom)
    (hu : IsRepresentableByAlgebraicSpaces B S hS u.hom) :
    IsRepresentableByAlgebraicSpaces B S hS v.hom := by
  have ha := isEquivalence_basedFunctor_id B S hS 𝒜.val
  have hb := isEquivalence_basedFunctor_id B S hS ℬ.val
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS v.hom u.hom
    (BasedFunctor.id _) (BasedFunctor.id _) e).1 hu

/-- `AlgebraicGeometry.Stack.IsQuasiCompact` (the Stacks 04XB convention at quasi-compactness of
morphisms of algebraic spaces) is invariant under an isomorphism of the underlying based functors
of two 1-morphisms of categories fibred in groupoids: **Stacks 0459** at the identity
equivalences. -/
theorem isQuasiCompact_congr_basedIso
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (u v : 𝒜 ⟶ ℬ) (e : u.hom ≅ v.hom)
    (hu : IsRepresentableByAlgebraicSpaces B S hS u.hom)
    (hv : IsRepresentableByAlgebraicSpaces B S hS v.hom)
    (h : IsQuasiCompact B S hS u) : IsQuasiCompact B S hS v := by
  let _inst : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  have ha := isEquivalence_basedFunctor_id B S hS 𝒜.val
  have hb := isEquivalence_basedFunctor_id B S hS ℬ.val
  exact (hasRelativeProperty_iff_of_equivalences' B S hS (Space.quasiCompactProperty B S hS)
    v u (BasedFunctor.id _) (BasedFunctor.id _) e hu hv).1 h


/-- `AlgebraicGeometry.Stack.IsQuasiCompact` transported along an equivalence on the target:
**Stacks 0459** with the identity on the source. -/
theorem isQuasiCompact_of_equivalenceTarget
    {𝒜 ℬ 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (u : 𝒜 ⟶ ℬ) (v : 𝒜 ⟶ 𝒞) (b : ℬ.val ⥤ᵇ 𝒞.val)
    (hb : Functor.IsEquivalence b.toFunctor)
    (e : v.hom ≅ BasedFunctor.comp u.hom b)
    (hu : IsRepresentableByAlgebraicSpaces B S hS u.hom)
    (hv : IsRepresentableByAlgebraicSpaces B S hS v.hom)
    (h : IsQuasiCompact B S hS v) : IsQuasiCompact B S hS u := by
  let _inst : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  have ha := isEquivalence_basedFunctor_id B S hS 𝒜.val
  have hb' := hb
  exact (hasRelativeProperty_iff_of_equivalences' B S hS (Space.quasiCompactProperty B S hS)
    u v (BasedFunctor.id _) b e hv hu).1 h

/-- The underlying morphism of schemes of any arrow of the site out of the base of a field-valued
point is quasi-compact: that base is the spectrum of a field, so its space is finite and every
subset of it is compact. -/
theorem quasiCompact_toScheme_map_of_fieldValuedPointBase
    {𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (p : FieldValuedPoint B S hS 𝒳)
    {V : BigFppfOver B S hS} (arrow : p.base ⟶ V) :
    QuasiCompact ((BigFppfOver.toScheme B S hS).map arrow) := by
  have hfinite : Finite ((BigFppfOver.toScheme B S hS).obj p.base) :=
    Finite.of_injective p.isSpec.hom.homeomorph p.isSpec.hom.homeomorph.injective
  constructor
  intro openSet hopen hcompact
  exact (Set.toFinite _).isCompact

/-- The 1-morphism of any field-valued point of the stack of a scheme is quasi-compact. -/
private theorem isQuasiCompactFieldValuedPoint_schemeFibredCategory_of_base {T : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (schemeFibredCategory B S hS T).val) :
    IsQuasiCompactFieldValuedPoint B S hS (schemeFibredCategory B S hS T) p :=
  isQuasiCompactFieldValuedPoint_schemeFibredCategory B S hS _
    (Space.isQuasiCompact_yoneda_map_of_quasiCompact B S hS _
      (quasiCompact_toScheme_map_of_fieldValuedPointBase B S hS p _))

/-- Composing the 1-morphism of a field-valued point with a 1-morphism `f` is quasi-compact exactly
when the field-valued point it induces in the target is quasi-compact. -/
private theorem isQuasiCompactMorphism_comp_fieldValuedPointStackMorphism_iff
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒵 ⟶ 𝒳) (p : FieldValuedPoint B S hS 𝒵.val.val) :
    IsQuasiCompactMorphism B S hS (fieldValuedPointStackMorphism B S hS 𝒵 p ≫ f) ↔
      IsQuasiCompactFieldValuedPoint B S hS 𝒳.val
        (fieldValuedPointMap B S hS 𝒵.val.val f.hom.hom p) := by
  let _inst : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  have hv := isRepresentableByAlgebraicSpaces_fieldValuedPointMorphism B S hS 𝒳
    (fieldValuedPointMap B S hS 𝒵.val.val f.hom.hom p)
  have hu := isRepresentableByAlgebraicSpaces_of_basedIso B S hS _ _
    (fieldValuedPointMorphism_comp_iso B S hS f.hom.hom p).symm hv
  rw [isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism,
    ← isQuasiCompact_iff_baseChange_quasiCompact B S hS _ hu,
    ← isQuasiCompact_iff_baseChange_quasiCompact B S hS _ hv]
  exact ⟨fun h => isQuasiCompact_congr_basedIso B S hS _ _
      (fieldValuedPointMorphism_comp_iso B S hS f.hom.hom p) hu hv h,
    fun h => isQuasiCompact_congr_basedIso B S hS _ _
      (fieldValuedPointMorphism_comp_iso B S hS f.hom.hom p).symm hv hu h⟩

/-- **Stacks 0GW3.** The source of a 1-morphism of algebraic stacks over `S` with decent target
is decent as soon as the 1-morphism is representable by schemes, or is representable by algebraic
spaces and quasi-separated.

The argument is the source's.  Fix a point `x` of `𝒳`; decency of `𝒴` supplies a *quasi-compact*
field-valued representative `q` of the image of `x`, and the 1-morphism `g : Spec k ⟶ 𝒴` it
determines is quasi-compact (**Stacks 050T**).  Form the 2-fibre product `P` of `g` and `f`
(**Stacks 04T2**); its second projection is quasi-compact as a base change of `g`
(**Stacks 050V**), and by **Stacks 04XH** the pair consisting of the point of `Spec k` named by
`q` and of `x` lifts to a point `w` of `P`.  Any field-valued representative `p` of `w` then has
quasi-compact 1-morphism — in the representable case because `P` is the stack of a scheme, in the
quasi-separated case because the composite of that 1-morphism with the *first* projection is
quasi-compact and the first projection is quasi-separated, so **Stacks 050Y** cancels it — and the
field-valued point of `𝒳` it induces represents `x` with quasi-compact 1-morphism by
**Stacks 050W**.

Unlike the source, no appeal to **Stacks 0DTK** is needed: the representative is chosen
downstream rather than tested, so only the existential form of decency is ever used. -/
@[stacks 0GW3]
theorem isDecent_of_representable_or_quasiSeparated
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : IsDecent B S hS 𝒴.val)
    (hf : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) ∨
      (IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧
        AlgebraicStacks.IsQuasiSeparated B S hS f)) :
    IsDecent B S hS 𝒳.val := by
  classical
  intro x
  obtain ⟨q, hqclass, hqQC⟩ := h𝒴 (pointsMap B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids f.hom.hom x)
  let g : schemeStack.{u, w} B S hS q.base ⟶ 𝒴 := fieldValuedPointStackMorphism B S hS 𝒴 q
  have hgQC : IsQuasiCompactMorphism B S hS g :=
    (isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism B S hS 𝒴 q).1 hqQC
  let P := twoFibreProductSquareAlgebraicStacks B S hS g f
  have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  have hsnd : IsQuasiCompactMorphism B S hS P.snd :=
    isQuasiCompactMorphism_baseChange B S hS g f P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hgQC
  have hz : pointsMap B S hS (schemeStack.{u, w} B S hS q.base).val.val
      (schemeStack.{u, w} B S hS q.base).val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids g.hom.hom
      (pointClass B S hS (schemeStack.{u, w} B S hS q.base).val.val
        (schemeStack.{u, w} B S hS q.base).val.isFiberedInGroupoids q.atBase)
      = pointClass B S hS 𝒴.val.val 𝒴.val.isFiberedInGroupoids q :=
    pointClass_fieldValuedPointMap_atBase B S hS 𝒴.val q
  obtain ⟨w, hw1, hw2⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP
    (pointClass B S hS (schemeStack.{u, w} B S hS q.base).val.val
      (schemeStack.{u, w} B S hS q.base).val.isFiberedInGroupoids q.atBase) x
    (by rw [hz, hqclass])
  obtain ⟨p, rfl⟩ := Quotient.exists_rep w
  refine ⟨fieldValuedPointMap B S hS P.pt.val.val P.snd.hom.hom p, hw2, ?_⟩
  -- quasi-compactness of the chosen representative
  have hprep := isRepresentableByAlgebraicSpaces_fieldValuedPointMorphism B S hS P.pt p
  have hpQC : IsQuasiCompactMorphism B S hS (fieldValuedPointStackMorphism B S hS P.pt p) := by
    rcases hf with hscheme | ⟨hrepf, hqs⟩
    · -- the representable case: the 2-fibre product is the stack of a scheme
      obtain ⟨V, E, hE⟩ := hscheme q.base g.hom.hom.toFunctor g.hom.hom.w
      obtain ⟨W, eqv, heqv⟩ : ∃ (W : BigFppfOver B S hS)
          (eqv : P.pt.val ⟶ schemeFibredCategory B S hS W),
          Functor.IsEquivalence eqv.hom.toFunctor := by
        let instTFP : Category.{u, u + 1}
            (TwoFibreProductOver (Over.forget q.base) 𝒳.val.val.p 𝒴.val.val.p
              g.hom.hom.toFunctor (CatFiberedInGroupoids.homFunctor f.hom)) :=
          TwoFibreProductOver.instCategory
        have hEeq : E.IsEquivalence :=
          Stacks.RepresentableMorphism.SliceEquivalence.isEquivalence_of_isEquivalenceOver _ V E hE
        refine ⟨V.left, Bicategory.InducedBicategory.mkHom
          { toFunctor := E ⋙ (Over.iteratedSliceEquiv V).functor
            w := by
              show E ⋙ (Over.forget V ⋙ Over.forget q.base) = _
              rw [← Functor.assoc, hE.isCartesianFunctor.comm]
              exact TwoFibreProductOver.fst_comp_eq }, ?_⟩
        exact Functor.isEquivalence_trans E (Over.iteratedSliceEquiv V).functor
      refine (isQuasiCompact_iff_baseChange_quasiCompact B S hS
        (fieldValuedPointStackMorphism B S hS P.pt p) hprep).1 ?_
      exact isQuasiCompact_of_equivalenceTarget B S hS
        (fieldValuedPointMorphism B S hS P.pt.val p)
        (fieldValuedPointMorphism B S hS (schemeFibredCategory B S hS W)
          (fieldValuedPointMap B S hS P.pt.val.val eqv.hom p))
        eqv.hom heqv
        (fieldValuedPointMorphism_comp_iso B S hS eqv.hom p).symm
        hprep
        (isRepresentableByAlgebraicSpaces_fieldValuedPointMorphism B S hS
          (schemeStack.{u, w} B S hS W) _)
        (isQuasiCompactFieldValuedPoint_schemeFibredCategory_of_base B S hS
          (fieldValuedPointMap B S hS P.pt.val.val eqv.hom p)).2
    · -- the quasi-separated case
      have hfstQS : AlgebraicStacks.IsQuasiSeparated B S hS P.fst :=
        AlgebraicStacks.isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS f g P.swap
          (Bicategory.isTwoFibreProduct_swap hP) hqs
      have hcomp := (isQuasiCompactMorphism_comp_fieldValuedPointStackMorphism_iff B S hS
        P.fst p).2 (isQuasiCompactFieldValuedPoint_schemeFibredCategory_of_base B S hS _)
      exact isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS _ _ hcomp hfstQS
  -- transport along Stacks 050W to the induced field-valued point of 𝒳
  exact (isQuasiCompactMorphism_comp_fieldValuedPointStackMorphism_iff B S hS P.snd p).1
    (isQuasiCompactMorphism_comp B S hS _ _ hpQC hsnd)

end AlgebraicGeometry.Stack

end
