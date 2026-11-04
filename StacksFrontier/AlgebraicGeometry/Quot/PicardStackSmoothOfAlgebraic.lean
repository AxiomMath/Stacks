module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentToBaseLimitPreservingOnObjects
public import StacksFrontier.AlgebraicGeometry.Quot.BaseBasedCategoryElements
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOverBase
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBaseFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.FibredComparisonTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingObjectsFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothFormallySmooth

/-!
# The structure morphism `Pic_{X/B} ⟶ B` as a 1-morphism of algebraic stacks (towards 0DPJ)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` which is flat, of finite
presentation and proper (the standing assumptions of Section 0DM9), and suppose
`Picardstack_{X/B}` is an algebraic stack, which is Stacks 0D04. Stacks 0DPJ says that if
moreover `f` has relative dimension `≤ 1`, the structure morphism `Picardstack_{X/B} ⟶ B` is
smooth.

The 2-category of algebraic stacks of Stacks 03YP is formed at the universes of the site, while
the hom types of `Picardstack_{X/B}` lie one universe up, so the Picard stack enters it through
its small model (`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`). The base `B` enters as
the algebraic stack of its category of elements (Stacks 0458,
`AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`). The structure morphism between them
is the structure morphism `Picardstack_{X/B} ⟶ 𝒮_B` of Section 0DM9 composed with the two
comparisons: the small model with the Picard stack, and the test schemes over `B` with the
elements of `B`.

This file builds that 1-morphism and proves two steps of the source's proof of Stacks 0DPJ:

* local finite presentation (Stacks 0DMB): `Picardstack_{X/B} ⟶ Cohstack_{X/B}` is an open
  immersion (Stacks 0D03), `Cohstack_{X/B} ⟶ 𝒮_B` is limit preserving on objects (the relative
  form of Stacks 08KD), so the structure morphism is limit preserving on objects (Stacks 06CY,
  06CW), which for a 1-morphism of algebraic stacks is local finite presentation (Stacks 06CX);
* the reduction of formal smoothness to lifting invertible modules along first-order
  thickenings (`hasThickeningLifts_picardToBase_of_exists_lift`).

The lifting, the vanishing of the obstruction groups and Stacks 0DP0 are in
`StacksFrontier.AlgebraicGeometry.Quot.PicardStackObstructionVanishing` and
`StacksFrontier.AlgebraicGeometry.Quot.PicardStackSmooth`.

## Main definitions

* `AlgebraicGeometry.Space.testSchemesToElementsComparison`: the Yoneda comparison `𝒮_B ⥤ S_B`
  of the test schemes over `B` with the category of elements of `B`.
* `AlgebraicGeometry.Space.picardAlgebraicStack`: the small model of `Picardstack_{X/B}`, given
  the algebraicity of Stacks 0D04.
* `AlgebraicGeometry.Space.baseAlgebraicStack`: the algebraic stack of the algebraic space `B`.
* `AlgebraicGeometry.Space.picardStructureMorphism`: the structure morphism
  `Picardstack_{X/B} ⟶ B` as a 1-morphism of algebraic stacks.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_picardStructureMorphism`: the structure
  morphism is locally of finite presentation, given Stacks 0D04.
* `AlgebraicGeometry.Space.hasThickeningLifts_picardToBase_of_exists_lift`: lifts of the structure
  morphism along first-order thickenings, from lifts of invertible modules.

## References

* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0DMB](https://stacks.math.columbia.edu/tag/0DMB)
* [Stacks Project, Tag 0DP0](https://stacks.math.columbia.edu/tag/0DP0)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The test schemes over an algebraic space and its category of elements -/

/-- **The comparison of the test schemes over `Y` with the elements of `Y`**: the Yoneda
equivalence `AlgebraicGeometry.Space.baseBasedElementsEquivalenceOver`, whose functor is
`AlgebraicGeometry.Space.baseToElements`. -/
def testSchemesToElementsComparison (Y : AlgebraicSpaces B S hS) :
    Stack.FibredComparison (baseCFG Y) (Stack.fibredCategory B S hS Y.1) where
  F := (baseToElements Y).toFunctor
  w := (baseToElements Y).w
  full := (baseBasedElementsEquivalenceOver Y).toEquivalence.fullyFaithfulFunctor.full
  faithful := (baseBasedElementsEquivalenceOver Y).toEquivalence.fullyFaithfulFunctor.faithful
  essSurj x := ⟨(baseBasedElementsEquivalenceOver Y).inv.functor.obj x,
    (baseBasedElementsEquivalenceOver Y).counitIso.hom.app x,
    Iso.isIso_hom ((baseBasedElementsEquivalenceOver Y).counitIso.app x),
    (baseBasedElementsEquivalenceOver Y).isHomLift_counitIso_hom_app x⟩

/-! ### The small model of the Picard stack -/

/-- **The comparison of a small model with the category it models.** -/
def shrinkHomsComparison (𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}
      (BigFppfOver B S hS))
    (h : Stack.IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    Stack.FibredComparison (Stack.AlgebraicStacks.smallModel B S hS 𝒳.val h).val 𝒳 :=
  letI := Stack.locallySmall_of_isAlgebraicStack B S hS h
  { F := ShrinkHoms.inverse.{u} 𝒳.val.obj
    w := rfl
    full := (ShrinkHoms.equivalence.{u} 𝒳.val.obj).fullyFaithfulInverse.full
    faithful := (ShrinkHoms.equivalence.{u} 𝒳.val.obj).fullyFaithfulInverse.faithful
    essSurj := fun x => ⟨ShrinkHoms.toShrinkHoms x, 𝟙 x,
      ⟨⟨𝟙 x, Category.id_comp _, Category.id_comp _⟩⟩, IsHomLift.id rfl⟩ }

/-! ### The structure morphism as a 1-morphism of algebraic stacks -/

/-- **The Picard stack as an object of the 2-category of algebraic stacks**, given that it is an
algebraic stack (Stacks 0D04): its small model. -/
abbrev picardAlgebraicStack (D : CoherentSituation B S hS)
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val) :
    Stack.AlgebraicStacks.{u, w} B S hS :=
  Stack.AlgebraicStacks.smallModel B S hS _ h0D04

/-- **The algebraic space `Y` as an object of the 2-category of algebraic stacks**: its category
of elements (Stacks 0458). -/
abbrev baseAlgebraicStack (Y : AlgebraicSpaces B S hS) : Stack.AlgebraicStacks.{u, w} B S hS :=
  ⟨Stack.fibredCategory B S hS Y.1, Stack.isAlgebraicStack_fibredCategory B S hS Y.1 Y.2⟩

/-- **The structure morphism `Picardstack_{X/Y} ⟶ Y` as a 1-morphism of algebraic stacks**: the
structure morphism `Picardstack_{X/Y} ⟶ 𝒮_Y` of Section 0DM9, read on the small model of the
Picard stack and on the category of elements of `Y`. -/
def picardStructureMorphism (D : CoherentSituation B S hS)
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val) :
    picardAlgebraicStack D h0D04 ⟶ baseAlgebraicStack.{u, w} D.Y :=
  Bicategory.InducedBicategory.mkHom
    ((shrinkHomsComparison _ h0D04).conj
      (picardToBase (modulePushforwardCoherence B S hS) D.toPicardSituation)
      (testSchemesToElementsComparison D.Y))

/-! ### Local finite presentation (Stacks 0DMB) -/

/-- **The structure morphism `Picardstack_{X/Y} ⟶ 𝒮_Y` is limit preserving on objects**
(Stacks 06CU): it is the open immersion `Picardstack_{X/Y} ⟶ Cohstack_{X/Y}` of Stacks 0D03
followed by the projection `Cohstack_{X/Y} ⟶ 𝒮_Y`, which is limit preserving on objects. -/
theorem isLimitPreservingOnObjects_picardToBase (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS _ _
      (picardToBase (modulePushforwardCoherence B S hS) D.toPicardSituation) := by
  rw [← picardToCoherent_comp_coherentToBaseCFG D hflat hproper]
  exact isLimitPreservingOnObjects_picardToCoherent_comp D hflat hproper _
    (isLimitPreservingOnObjects_coherentToBaseCFG D)

/-- **The structure morphism `Picardstack_{X/Y} ⟶ Y` is locally of finite presentation**
(Stacks 0DMB, the half used by Stacks 0DPJ), given that the Picard stack is algebraic. -/
theorem isLocallyOfFinitePresentation_picardStructureMorphism (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val) :
    Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (picardStructureMorphism D h0D04) :=
  Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isLimitPreservingOnObjects B S hS _
    ((shrinkHomsComparison _ h0D04).isLimitPreservingOnObjects_conj _ _
      (isLimitPreservingOnObjects_picardToBase D hflat hproper))

/-! ### Formal smoothness -/

/-- **Lifts of the structure morphism `Picardstack_{X/B} ⟶ 𝒮_B` along first-order thickenings,
from lifts of invertible modules.** -/
theorem hasThickeningLifts_picardToBase_of_exists_lift (s : PicardSituation B S hS)
    (h : ∀ ⦃T T' : s.SchemesOver⦄ (g : T ⟶ T'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left) →
      Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map g.left) →
      ∀ L : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2,
        IsInvertibleModule (s.baseChange T) L →
        ∃ (L' : Modules.{u, u} B S hS (s.baseChange T').1 (s.baseChange T').2)
          (_ : IsInvertibleModule (s.baseChange T') L'),
          Nonempty ((modulePullback B S hS (baseChangeMap s.f g)).obj L' ≅ L)) :
    Stack.HasThickeningLifts (picardToBase (modulePushforwardCoherence B S hS) s) := by
  intro U U' i hU hU' hi x hx y' hy' ψ hψ
  let : Category.{u + 1} (PicardObject s) :=
    (picardCategoryData (modulePushforwardCoherence B S hS) s).category
  let T' : s.SchemesOver := ULiftHom.objDown y'
  let gm : x.T ⟶ T' := ψ.down
  have hTx : x.T.left = U := hx
  have hT' : T'.left = U' := hy'
  subst hTx hT'
  have hgl : gm.left = i :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (baseCFG s.base).val.p _ _ i ψ hψ).symm
  have hA : IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left) := hU
  have hA' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left) := hU'
  obtain ⟨L', hL', ⟨e⟩⟩ := h gm hA hA' (by rw [hgl]; exact hi) x.lineBundle x.invertible
  let x' : PicardObject s := ⟨T', L', hL'⟩
  let m : x ⟶ x' := (⟨gm, e.hom, inferInstance⟩ : PicardHom x x')
  have hm : (picardCFG (modulePushforwardCoherence B S hS) s).val.p.IsHomLift i m := by
    have h0 := IsHomLift.map (p := (picardCFG (modulePushforwardCoherence B S hS) s).val.p) m
    have h1 : (picardCFG (modulePushforwardCoherence B S hS) s).val.p.map m = i := hgl
    rw [h1] at h0
    exact h0
  exact ⟨x', rfl, m, hm, 𝟙 y', IsHomLift.id rfl⟩

end AlgebraicGeometry.Space

end
