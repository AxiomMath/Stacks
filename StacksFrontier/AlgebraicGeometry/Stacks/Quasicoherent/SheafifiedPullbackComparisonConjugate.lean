module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleSheafifiedBaseChangeComposition
public import StacksFrontier.CategoryTheory.Adjunction.CompTranspose

/-!
# The composition law for the sheafified Stacks 06WC pullbacks, pinned by its conjugate

`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` identifies the composite of two
sheafified Stacks 06WC pullbacks with the sheafified pullback along the composite.  Both sides
are left adjoints, so the identification has no formula; what pins it is its conjugate under
`CategoryTheory.conjugateEquiv`, which is a bijection.  This file computes that conjugate.

The answer is the composition law for the *pushforwards* along the morphisms of ringed sites
`ε` of **Stacks 070R (2)**, which is restriction of sections and therefore carries the
composition law of **Stacks 075D (1)** directly.  So this is the transpose of Stacks 075D (1)
to the sheafified pullback — the sheaf-level counterpart of
`AlgebraicGeometry.Stack.conjugateEquiv_smallEtalePullbackComparisonCompIso_inv`, which does the
same for the pullbacks of *presheaves* of modules along the maps `a_{small}^♯` of Stacks 06WC.

## How the four layers are peeled off

`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` is a composite of four
identifications, and `CategoryTheory.conjugateEquiv_comp` turns its conjugate into the composite
of their conjugates, in the opposite order.  Three of the four contribute nothing:

* the two whiskered copies of
  `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`, whose own conjugate is the identity
  by `AlgebraicGeometry.Stack.conjugateEquiv_sheafifiedPullbackComparisonIso_hom` — the two
  functors it compares being left adjoints of one and the same pushforward — and whiskering a
  2-cell of left adjoints whiskers its conjugate, by
  `CategoryTheory.conjugateEquiv_whiskerLeft` and
  `CategoryTheory.conjugateEquiv_whiskerRight`;
* the unwhiskered copy at the composite arrow, for the same reason.

What is left is the conjugate of
`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso`, which
`AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv` already pins.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallEtalePushforwardFactoredCompIso`: the composition law for
  the pushforwards along the morphisms of ringed sites of Stacks 070R (2), at a morphism of
  schemes which is only *provably* the composite of the two given ones.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_factoredComparisonComp` and
  `AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackFactoredCompIso_inv`: the two
  statements of
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleBaseChangeConjugate.lean` which
  the composition law consumes, at a morphism only provably the composite.
* `AlgebraicGeometry.Stack.conjugateEquiv_sheafifiedPullbackComparisonIso_inv`: the inverse of
  the comparison of the sheafified Stacks 06WC pullback with the pullback of sheaves of modules
  along `ε_a` also has the identity for its conjugate.
* `AlgebraicGeometry.Stack.conjugateEquiv_sheafifiedPullbackComparisonCompIso_inv`: **the
  conjugate of the composition law for the sheafified Stacks 06WC pullbacks is the composition
  law for the pushforwards along `ε`.**

## Implementation notes

The morphism of schemes below `ψ ∘ φ` is only *provably* the composite of the ones below `ψ` and
below `φ`, so each of the two statements of the conjugate file used here is restated at a
morphism `ab` together with a proof `a ≫ b = ab` and proved by substituting that proof, exactly
as
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleSheafifiedBaseChangeComposition.lean`
does for the pullbacks themselves.

No new Stacks tag is registered.  Stacks 075D (1) is tagged where it is proved — on
`AlgebraicGeometry.Stack.smallEtaleStructureComparison_app_comp`,
`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_comp` and
`AlgebraicGeometry.Stack.restrictModulePullbackComparison_comp`; what is proved here is the
transpose of those statements to a construction of this library.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v v₁

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z)
  (hab : a ≫ b = ab)

/-- `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_comparisonComp` at a morphism which
is only provably the composite of the two given ones. -/
public theorem smallEtaleStructureMapRing_factoredComparisonComp :
    smallEtaleStructureMapRing B ab ≫
        (Functor.sheafPushforwardContinuousNatTrans
            (smallEtaleBaseChange_factoredCompIso B X Y Z a b ab hab).hom RingCat.{u}
            (topology B Z.obj Z.property) (topology B X.obj X.property)).app
          (structureSheaf B X.obj X.property) =
      SheafOfModules.comparisonComp (smallEtaleStructureMapRing B b)
        (smallEtaleStructureMapRing B a) := by
  subst hab; exact smallEtaleStructureMapRing_comparisonComp B a b

/-- `AlgebraicGeometry.SmallEtale.smallEtalePushforwardCompIso` at a morphism which is only
provably the composite of the two given ones. -/
public noncomputable abbrev smallEtalePushforwardFactoredCompIso :
    SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B ab) ≅
      SheafOfModules.pushforward.{u} (smallEtaleStructureMapRingComp B a b) :=
  SheafOfModules.pushforwardCongr₂.{u} _
    (smallEtaleBaseChange_factoredCompIso B X Y Z a b ab hab)
    (smallEtaleStructureMapRing_factoredComparisonComp B a b ab hab)

/-- `AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv` at a morphism
which is only provably the composite of the two given ones. -/
public theorem conjugateEquiv_smallEtalePullbackFactoredCompIso_inv :
    conjugateEquiv
        ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B b)).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B a)))
        (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B ab))
        (smallEtalePullbackFactoredCompIso B a b ab hab).inv =
      (SheafOfModules.pushforwardComp.{u} (smallEtaleStructureMapRing B b)
          (smallEtaleStructureMapRing B a)).hom ≫
        (smallEtalePushforwardFactoredCompIso B a b ab hab).inv := by
  subst hab; exact conjugateEquiv_smallEtalePullbackCompIso_inv B a b

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z)

/-- The conjugate of a fourfold composite of 2-cells is the composite of the conjugates. -/
private theorem conjugateEquiv_comp_comp_comp {C D : Type*} [Category C] [Category D]
    {L₁ L₂ L₃ L₄ L₅ : C ⥤ D} {R₁ R₂ R₃ R₄ R₅ : D ⥤ C} {adj₁ : L₁ ⊣ R₁} {adj₂ : L₂ ⊣ R₂}
    {adj₃ : L₃ ⊣ R₃} {adj₄ : L₄ ⊣ R₄} {adj₅ : L₅ ⊣ R₅} (α : L₂ ⟶ L₁) (β : L₃ ⟶ L₂)
    (γ : L₄ ⟶ L₃) (δ : L₅ ⟶ L₄) :
    conjugateEquiv adj₁ adj₅ (δ ≫ γ ≫ β ≫ α) =
      conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β ≫ conjugateEquiv adj₃ adj₄ γ ≫
        conjugateEquiv adj₄ adj₅ δ := by
  simp

/-- **The unit characterisation of the inverse of
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`.**  Its conjugate, taken the other way
round, is again the identity of the pushforward along `ε_a`: the comparison is invertible, and
the conjugates of an isomorphism and of its inverse are mutually inverse. -/
public theorem conjugateEquiv_sheafifiedPullbackComparisonIso_inv :
    conjugateEquiv
        (sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ)
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)))
        (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).inv = 𝟙 _ := by
  have hc := conjugateEquiv_comm
    (adj₁ := SheafOfModules.pullbackPushforwardAdjunction.{u}
      (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)))
    (adj₂ := sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ)
    (Iso.inv_hom_id (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ))
  rw [conjugateEquiv_sheafifiedPullbackComparisonIso_hom, Category.id_comp] at hc
  exact hc

/-- **The conjugate of the composition law for the sheafified Stacks 06WC pullbacks is the
composition law for the pushforwards along `ε`.**  For arrows `φ : x ⟶ y` and `ψ : y ⟶ z` of
`𝒳`, the conjugate of `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` with respect
to the composite of the two transported adjunctions and the transported adjunction at `ψ ∘ φ` is
Mathlib's comparison of the two composite pushforwards followed by the reindexing
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardFactoredCompIso`.

This pins the composition law, `CategoryTheory.conjugateEquiv` being a bijection, and it is the
transpose of **Stacks 075D (1)** to the sheafified pullback: on the pushforward side the law is
restriction of sections, which is where this library proves it.

Three of the four layers of the composition law contribute the identity — the two whiskered
copies of `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso` and the unwhiskered one at
`ψ ∘ φ` — leaving the conjugate of the composition law for the pullbacks of sheaves of modules
along `ε` of **Stacks 070R (2)**.  No hypothesis on the arrows is used. -/
public theorem conjugateEquiv_sheafifiedPullbackComparisonCompIso_inv :
    conjugateEquiv
        ((sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ ψ).comp
          (sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ))
        (sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ (φ ≫ ψ))
        (sheafifiedPullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv =
      (SheafOfModules.pushforwardComp.{u}
          (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p ψ))
          (SmallEtale.smallEtaleStructureMapRing E
            (smallEtaleBaseMorphism B E h S hS p φ))).hom ≫
        (SmallEtale.smallEtalePushforwardFactoredCompIso E
          (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
          (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
          (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm).inv := by
  have hsplit : (sheafifiedPullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv =
      (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ (φ ≫ ψ)).hom ≫
        (SmallEtale.smallEtalePullbackFactoredCompIso E
            (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
            (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
            (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm).inv ≫
          Functor.whiskerLeft (SheafOfModules.pullback.{u}
              (SmallEtale.smallEtaleStructureMapRing E
                (smallEtaleBaseMorphism B E h S hS p ψ)))
            (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).inv ≫
          Functor.whiskerRight (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ ψ).inv
            (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ) := by
    simp only [sheafifiedPullbackComparisonCompIso, Iso.trans_inv, Iso.symm_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc]
  rw [hsplit, conjugateEquiv_comp_comp_comp, conjugateEquiv_whiskerRight,
    conjugateEquiv_sheafifiedPullbackComparisonIso_inv, conjugateEquiv_whiskerLeft,
    conjugateEquiv_sheafifiedPullbackComparisonIso_inv,
    conjugateEquiv_sheafifiedPullbackComparisonIso_hom,
    SmallEtale.conjugateEquiv_smallEtalePullbackFactoredCompIso_inv]
  simp

/-- **A composition law for the sheafified Stacks 06WC pullbacks follows from the corresponding
law on the pushforward side.**  Let `sψ : ε_b^*𝒩 ⟶ 𝒩'` and `sφ : ε_a^*𝒩' ⟶ 𝓜` be morphisms of
sheaves of modules out of sheafified Stacks 06WC pullbacks, and `s : ε_{b∘a}^*𝒩 ⟶ 𝓜` a third
one.  If the adjuncts of `sψ` and `sφ` compose — through the direct image along `ε_b` and the
composition law for the pushforwards — to the adjunct of `s`, then `ε_a^*(sψ)` followed by `sφ`
is `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` followed by `s`.

This is how a law about these pullbacks is proved: a morphism out of a value of a left adjoint
has no formula, whereas its adjunct is a morphism into a direct image, which is restriction of
sections.  The hypothesis is the law on that side, and
`AlgebraicGeometry.Stack.conjugateEquiv_sheafifiedPullbackComparisonCompIso_inv` is what makes
the interchange term of the conclusion transpose to the composition law of the pushforwards
appearing in it.  No hypothesis on the arrows or on the sheaves is used. -/
public theorem sheafifiedPullbackComparison_map_comp_of_homEquiv
    {𝒩 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z))}
    {𝒩' : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj y).left.1
      (contains_base B E h S hS p y))}
    {𝓜 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x))}
    (sψ : (sheafifiedPullbackComparison B E h S hS p hp τ hτ ψ).obj 𝒩 ⟶ 𝒩')
    (sφ : (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).obj 𝒩' ⟶ 𝓜)
    (s : (sheafifiedPullbackComparison B E h S hS p hp τ hτ (φ ≫ ψ)).obj 𝒩 ⟶ 𝓜)
    (hadj : ((sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ ψ).homEquiv 𝒩 𝒩' sψ ≫
          (SheafOfModules.pushforward.{u} (SmallEtale.smallEtaleStructureMapRing E
              (smallEtaleBaseMorphism B E h S hS p ψ))).map
            ((sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ).homEquiv
              𝒩' 𝓜 sφ)) ≫
        ((SheafOfModules.pushforwardComp.{u}
              (SmallEtale.smallEtaleStructureMapRing E
                (smallEtaleBaseMorphism B E h S hS p ψ))
              (SmallEtale.smallEtaleStructureMapRing E
                (smallEtaleBaseMorphism B E h S hS p φ))).hom ≫
            (SmallEtale.smallEtalePushforwardFactoredCompIso E
              (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
              (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
              (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm).inv).app 𝓜 =
      (sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ (φ ≫ ψ)).homEquiv 𝒩 𝓜 s) :
    (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map sψ ≫ sφ =
      (sheafifiedPullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).hom.app 𝒩 ≫ s := by
  have hkey : (sheafifiedPullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv.app 𝒩 ≫
      ((sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map sψ ≫ sφ) = s := by
    refine ((sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ
      (φ ≫ ψ)).homEquiv 𝒩 𝓜).injective ?_
    rw [Stacks.CategoryTheory.homEquiv_conjugate'
        ((sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ ψ).comp
          (sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ)),
      conjugateEquiv_sheafifiedPullbackComparisonCompIso_inv,
      Stacks.CategoryTheory.homEquiv_comp_map_comp]
    exact hadj
  exact (Iso.inv_comp_eq (Iso.app
    (sheafifiedPullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ) 𝒩)).mp hkey

end AlgebraicGeometry.Stack

end
