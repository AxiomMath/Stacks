module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePushforwardInverseSquare

/-!
# The comparison of the two routes round the square of small étale sites, on sections

`AlgebraicGeometry.Space.representedModulePushforwardInverseSquareIso` identifies the two
iterated direct images of modules round the square of small étale sites of a morphism
`k : U' ⟶ U` of schemes of the big fppf site over `S`.  This file computes the middle factor of
that identification on sections, which is what the derivation square of Stacks 05ZC and
Stacks 05ZD needs.

## Implementation notes

The target of `PresheafOfModules.map f` is a `ModuleCat.restrictScalars` along `f`, so checking
that the two sides of the reading on sections have the same type forces the elaborator to
weak-head-normalise the comparison of index functors
`(AlgebraicGeometry.Space.representedSmallEtaleBaseChangeInverseIso …).inv`, the conjugate of
Stacks 03G2 (4) by two equivalences of sites; with the concrete comparison this exceeds the
heartbeat budget, while with the comparison left as a variable the reading is
`SheafOfModules.pushforwardNatTrans_app_val_app`.

So the comparison is wrapped in a definition which is made `irreducible` **after** the one
statement that needs its value — that the two composite structure maps round the square agree,
`AlgebraicGeometry.Space.representedSquareSharpInverse_natTrans` — has been proved.  With the
comparison opaque the elaborator cannot walk into it, the type check happens on the underlying
carriers, and the reading goes through.

## Main definitions

* `AlgebraicGeometry.Space.representedSquareInverseNat`: the comparison of the two routes round
  the square, as a natural transformation, made opaque.
* `AlgebraicGeometry.Space.representedSquareSharpInverse` and
  `AlgebraicGeometry.Space.representedSquareSharpScheme`: the two composite structure maps round
  the square.  These are *not* opaque — the contractions
  `AlgebraicGeometry.Space.representedSquarePushforwardInverseIso` and
  `AlgebraicGeometry.Space.representedSquarePushforwardSchemeIso` are stated at them and need
  their values — and only
  `AlgebraicGeometry.Space.representedSquareInverseNat` carries `attribute [irreducible]` here.
* `AlgebraicGeometry.Space.representedSquareMiddle`: **the middle factor of the comparison of
  the two iterated direct images**, built as `SheafOfModules.pushforwardNatTrans` of the
  comparison followed by the transport along the agreement of the two structure maps.

## Main results

* `Stacks.SectionsComponents.comparison_inv_square`: two composite structure maps that agree
  after the forward comparison agree after the inverse one — the cancellation of
  `CategoryTheory.Functor.sheafPushforwardContinuousIso`.
* `AlgebraicGeometry.Space.representedSquareSharpInverse_natTrans`: **the two routes round the
  square carry the structure sheaf of the scheme `U` to the structure sheaf of the small étale
  site of `yoneda.obj U'` by the same map**, in the direction the middle factor consumes.
* `AlgebraicGeometry.Space.representedSquareMiddle_app_val_app_apply`: **the middle factor on
  sections is restriction along the component of the comparison.**  This is the reading that the
  derivation square of Stacks 05ZC and Stacks 05ZD needs.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05ZC](https://stacks.math.columbia.edu/tag/05ZC)
* [Stacks Project, Tag 05ZD](https://stacks.math.columbia.edu/tag/05ZD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.SectionsComponents

universe v₁ v₂ u₁ u₂ w m

section InverseSquare

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F G : C ⥤ D}
  {R : Sheaf J RingCat.{w}} {R' : Sheaf K RingCat.{w}}
  [F.IsContinuous J K] [G.IsContinuous J K]

/-- The two composite structure maps of a square agree in the inverse direction as soon as they
agree in the forward one. -/
theorem comparison_inv_square (e : F ≅ G)
    {chiG : R ⟶ (G.sheafPushforwardContinuous RingCat.{w} J K).obj R'}
    {chiF : R ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R'}
    (h : chiG ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{w} J K).app R' =
      chiF) :
    chiF ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat.{w} J K).app R' = chiG := by
  have h1 : (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{w} J K).app R' ≫
      (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat.{w} J K).app R' = 𝟙 _ :=
    (NatTrans.comp_app _ _ R').symm.trans
      (congrArg (fun t ↦ NatTrans.app t R')
        (Functor.sheafPushforwardContinuousIso e RingCat.{w} J K).inv_hom_id)
  rw [← h, Category.assoc, h1, Category.comp_id]

end InverseSquare

section Comp

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Applying a composite of morphisms of sheaves of modules on sections. -/
theorem comp_val_app_apply {M N P : SheafOfModules.{m} R} (f : M ⟶ N) (g : N ⟶ P) (A : Cᵒᵖ)
    (x : M.val.obj A) : (f ≫ g).val.app A x = g.val.app A (f.val.app A x) := rfl

end Comp

end Stacks.SectionsComponents

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U' U : BigFppfOver B S hS} (k : U' ⟶ U)
  (hk : yoneda.relativelyRepresentable (yoneda.map k))

/-- The comparison of the two routes round the square of small étale sites, in the inverse
direction, as a natural transformation. -/
def representedSquareInverseNat :
    representedSchemeBaseChange B S hS k ⋙
        (representedSmallEtaleEquivalence B S hS U').inverse ⟶
      (representedSmallEtaleEquivalence B S hS U).inverse ⋙
        smallBaseChange B S hS (representedSpaceMap B S hS k) hk :=
  (representedSmallEtaleBaseChangeInverseIso B S hS k hk).inv

/-- The structure map of the route that reads an object on the space's small étale site first. -/
def representedSquareSharpInverse :
    representedSchemeStructureSheaf B S hS U ⟶
      (((representedSmallEtaleEquivalence B S hS U).inverse ⋙
          smallBaseChange B S hS (representedSpaceMap B S hS k) hk).sheafPushforwardContinuous
        RingCat.{u} (representedSchemeSmallEtaleTopology B S hS U)
        (SmallEtale.topology B S hS (yoneda.obj U'))).obj
        (representedStructureRingSheaf B S hS U') :=
  SheafOfModules.comparisonComp (representedStructureMapInverse B S hS U)
    (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk)

/-- The structure map of the route that base changes the scheme first. -/
def representedSquareSharpScheme :
    representedSchemeStructureSheaf B S hS U ⟶
      ((representedSchemeBaseChange B S hS k ⋙
          (representedSmallEtaleEquivalence B S hS U').inverse).sheafPushforwardContinuous
        RingCat.{u} (representedSchemeSmallEtaleTopology B S hS U)
        (SmallEtale.topology B S hS (yoneda.obj U'))).obj
        (representedStructureRingSheaf B S hS U') :=
  SheafOfModules.comparisonComp (representedSchemeStructureMapRing B S hS k)
    (representedStructureMapInverse B S hS U')

/-- `AlgebraicGeometry.Space.representedSquareInverseNat` is the inverse of the comparison. -/
theorem representedSquareInverseNat_eq : representedSquareInverseNat B S hS k hk =
    (representedSmallEtaleBaseChangeInverseIso B S hS k hk).inv := rfl

/-- **The two routes round the square carry the structure sheaf by the same map**, read in the
inverse direction. -/
theorem representedSquareSharpInverse_natTrans : representedSquareSharpInverse B S hS k hk ≫
      (Functor.sheafPushforwardContinuousNatTrans (representedSquareInverseNat B S hS k hk)
        RingCat.{u} (representedSchemeSmallEtaleTopology B S hS U)
        (SmallEtale.topology B S hS (yoneda.obj U'))).app
        (representedStructureRingSheaf B S hS U') =
    representedSquareSharpScheme B S hS k :=
  Stacks.SectionsComponents.comparison_inv_square
    (representedSmallEtaleBaseChangeInverseIso B S hS k hk)
    (representedStructureMapRing_inverse_square B S hS k hk)

/-- Contracting the direct image along the inverse route. -/
def representedSquarePushforwardInverseIso :
    SheafOfModules.pushforward.{u}
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk) ⋙
        SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U) ≅
      SheafOfModules.pushforward.{u} (representedSquareSharpInverse B S hS k hk) :=
  SheafOfModules.pushforwardComp.{u} (representedStructureMapInverse B S hS U)
    (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk)

/-- Contracting the direct image along the forward route. -/
def representedSquarePushforwardSchemeIso :
    SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U') ⋙
        SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS k) ≅
      SheafOfModules.pushforward.{u} (representedSquareSharpScheme B S hS k) :=
  SheafOfModules.pushforwardComp.{u} (representedSchemeStructureMapRing B S hS k)
    (representedStructureMapInverse B S hS U')

/-- Contracting the inverse route does nothing on sections. -/
theorem representedSquarePushforwardInverseIso_hom_app_val_app_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (A : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ)
    (y : ((SheafOfModules.pushforward.{u}
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk) ⋙
      SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).obj
        C).val.obj A) :
    ((representedSquarePushforwardInverseIso B S hS k hk).hom.app C).val.app A y = y :=
  Stacks.SectionsComponents.pushforwardComp_hom_app_val_app _ _ C A y

/-- Expanding the forward route does nothing on sections. -/
theorem representedSquarePushforwardSchemeIso_inv_app_val_app_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (A : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ)
    (y : ((SheafOfModules.pushforward.{u} (representedSquareSharpScheme B S hS k)).obj
      C).val.obj A) :
    ((representedSquarePushforwardSchemeIso B S hS k).inv.app C).val.app A y = y :=
  Stacks.SectionsComponents.pushforwardComp_inv_app_val_app _ _ C A y

attribute [irreducible] representedSquareInverseNat

/-- The middle factor of the comparison, as a natural transformation of the two direct images
along the two composite structure maps round the square. -/
def representedSquareMiddle :
    SheafOfModules.pushforward.{u} (representedSquareSharpInverse B S hS k hk) ⟶
      SheafOfModules.pushforward.{u} (representedSquareSharpScheme B S hS k) :=
  SheafOfModules.pushforwardNatTrans.{u} (representedSquareSharpInverse B S hS k hk)
      (representedSquareInverseNat B S hS k hk) ≫
    (SheafOfModules.pushforwardCongr.{u} (representedSquareSharpInverse_natTrans B S hS k hk)).hom

/-- **The middle factor of the comparison on sections**: restriction along the component of the
comparison of the two routes round the square. -/
theorem representedSquareMiddle_app_val_app_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (y : ((SheafOfModules.pushforward.{u} (representedSquareSharpInverse B S hS k hk)).obj
      C).val.obj (op T)) :
    ((representedSquareMiddle B S hS k hk).app C).val.app (op T) y =
      C.val.map ((representedSquareInverseNat B S hS k hk).app T).op y := by
  refine Eq.trans (Stacks.SectionsComponents.comp_val_app_apply _ _ (op T) y) ?_
  refine Eq.trans (SheafOfModules.pushforwardCongr_hom_app_val_app _ C (op T) _) ?_
  exact SheafOfModules.pushforwardNatTrans_app_val_app _ _ C (op T) y

end AlgebraicGeometry.Space

end
