module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleGerbeAffineObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineThickening
public import StacksFrontier.AlgebraicGeometry.Stacks.FirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCartesianLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective

/-!
# Lifting smooth affines along a first-order thickening of algebraic stacks (Stacks 0CKI)

Let `𝒳 ⊂ 𝒳'` be a first-order thickening of algebraic stacks, `W` an affine scheme and
`x : W → 𝒳` smooth. Emerton's proposition (Stacks 0CKI) produces a cartesian square
```
  W ──→ W'
  │      │ x'
  ↓      ↓
  𝒳 ──→ 𝒳'
```
with `x'` smooth and `W'` affine. In the language of Stacks 0CJP the claim is that the category
`𝒞` of smooth lifts of the étale opens of `W` has an object over `W` itself; this file reduces
that to the gerbe and band properties of `𝒞`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isThickening_of_isFirstOrderThickening`: a first-order
  thickening of algebraic stacks is a thickening.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_lift_of_fiber_final`: an object of `𝒞` over the
  final object of `W_{spaces,étale}` gives the cartesian square of Stacks 0CKI, with `W'` affine
  (Stacks 05ZR and 06AD, in the form of the closed-immersion case of Stacks 07VS:
  `AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace`).
* `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_lift_of_isGerbe_of_cechVanishing`: the proof
  of Stacks 0CKI from the gerbe property of `𝒞` (Stacks 0CJX) and the Čech vanishing of its
  band, via Stacks 0CK0.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_lift_of_isGerbe_of_isQuasicoherent`: the same
  with the band given as a quasi-coherent `𝒪_W`-module (Stacks 0CKG (2)).

## References

* [Stacks Project, Tag 0CKI](https://stacks.math.columbia.edu/tag/0CKI)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CK0](https://stacks.math.columbia.edu/tag/0CK0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Opposite

namespace CategoryTheory.Bicategory

/-- **A 2-fibre product is unchanged by replacing its first leg by an equal 1-morphism**, the
filler being transported along the equality. -/
theorem nonempty_isTwoFibreProduct_of_fst_eq {ℬ : Type*} [Bicategory ℬ] {X Y Z P : ℬ}
    {f : X ⟶ Z} {g : Y ⟶ Z} {a a' : P ⟶ X} {b : P ⟶ Y} (h : a = a') (γ : a ≫ f ≅ b ≫ g)
    (hP : IsTwoFibreProduct (⟨P, a, b, γ⟩ : TwoCommSq f g)) :
    Nonempty (IsTwoFibreProduct
      (⟨P, a', b, eqToIso (congrArg (· ≫ f) h.symm) ≪≫ γ⟩ : TwoCommSq f g)) := by
  subst h
  have : (eqToIso (congrArg (· ≫ f) (rfl : a = a)) ≪≫ γ) = γ := by simp
  rw [this]
  exact ⟨hP⟩

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace AlgebraicStacks

/-- **A first-order thickening of algebraic stacks is a thickening.** It is a closed immersion by
definition, and it is surjective on points because surjectivity is tested after base change to
schemes, where the base change is a first-order, hence an ordinary, thickening of algebraic
spaces (Stacks 05ZK). -/
theorem isThickening_of_isFirstOrderThickening {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    {ι : 𝒳 ⟶ 𝒳'} (hι₁ : IsFirstOrderThickening B S hS ι) : IsThickening ι := by
  refine ⟨hι₁.1, ?_⟩
  apply (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS ι hι₁.1.1).mpr
  intro U y hy F hF hrep
  have hthick := Space.IsNthOrderThickening.isThickening B S hS (hι₁.2 U y hy F hF hrep)
  set f := algebraicSpaceMap B S hS U
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)
  change Function.Surjective (Space.pointsMap B S hS _ f.hom)
  rw [← Subfunctor.toRange_ι f.hom, Space.pointsMap_comp]
  refine hthick.2.comp (Space.surjective_pointsMap_of_surjective_app B S hS _ fun T => ?_)
  rw [← CategoryTheory.epi_iff_surjective]
  exact (NatTrans.epi_iff_epi_app (Subfunctor.toRange f.hom)).mp inferInstance T

end AlgebraicStacks

namespace EtaleSmoothLift

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

/-- **An object of the category of smooth lifts over the final object of `W_{spaces,étale}`
gives the square of Stacks 0CKI.** Such an object is `(W, W', 𝟙, i, x', α)` with
`W = 𝒳 ×_{𝒳'} W'`; the inclusion `i : W ⟶ W'` is a thickening (Stacks 0CJP), so `W'` is affine
when `W` is (the closed-immersion case of Stacks 07VS, which gives Stacks 05ZR and 06AD in the
form used by the source). -/
theorem exists_lift_of_fiber_final (hW : Space.IsAffineSpace B S hS W.obj)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber
      (Space.SpacesEtale.final B S hS W)) :
    ∃ (W' : AlgebraicSpaces B S hS) (i : W ⟶ W')
      (x' : (algebraicSpaceStackFunctor B S hS).obj W' ⟶ 𝒳')
      (α : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x'),
      AlgebraicStacks.IsSmooth B S hS x' ∧
        Nonempty (IsTwoFibreProduct
          (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
            (algebraicSpaceStackFunctor B S hS).map i, α⟩ : TwoCommSq ι x')) ∧
        Space.IsAffineSpace B S hS W'.obj := by
  obtain ⟨ζ, hζ⟩ := ξ
  have hthick := isThickeningHom_inclusion ζ
  obtain ⟨base, ambient, inclusion, ambientMap, hsm, comm, htw⟩ := ζ
  change base = _ at hζ
  subst hζ
  have hid : (algebraicSpaceStackFunctor B S hS).map (Space.SpacesEtale.final B S hS W).obj.hom ≫
      x = x := by
    change (algebraicSpaceStackFunctor B S hS).map (𝟙 W) ≫ x = x
    exact (congrArg (· ≫ x) ((algebraicSpaceStackFunctor B S hS).map_id W)).trans
      (Category.id_comp x)
  refine ⟨ambient, inclusion, ambientMap, eqToIso (congrArg (· ≫ ι) hid.symm) ≪≫ comm, hsm,
    nonempty_isTwoFibreProduct_of_fst_eq hid comm htw, ?_⟩
  exact Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace B S hS
    inclusion.hom W.property ambient.property hthick.isClosedImmersion
    hthick.surjective_pointsMap hW

/-- **Stacks 0CKI from the gerbe property and the Čech vanishing of the band.** If the category
of smooth lifts `p : 𝒞 ⟶ W_{spaces,étale}` is a stack (Stacks 0CJU) which is locally nonempty
and locally connected (Stacks 0CJX), and it has a band `𝒢` in the sense of Stacks 0CJY whose
positive-degree Čech cohomology vanishes on finite affine covering families of affine étale
charts (which holds for the quasi-coherent band of Stacks 0CKG), then for `W` affine there is a
cartesian square as in Stacks 0CKI with `x'` smooth and `W'` affine. -/
theorem exists_lift_of_isGerbe_of_cechVanishing (hW : Space.IsAffineSpace B S hS W.obj)
    (hst : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsStack
      (Space.SpacesEtale.topology B S hS W))
    (hne : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyNonempty
      (Space.SpacesEtale.topology B S hS W))
    (hlc : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyConnected
      (Space.SpacesEtale.topology B S hS W))
    (hband : haveI : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsFibered :=
        isFiberedInGroupoids_proj.isFibered
      haveI : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
        isFiberedInGroupoids_proj.fiber_isGroupoid
      ∃ (𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1})
        (θ : ∀ (U : Space.SpacesEtale B S hS W)
          (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
          (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
            (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf y y ⋙
              uliftFunctor.{u + 1, u + 1}),
        ((∀ (U : Space.SpacesEtale B S hS W)
            (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
            (a b : 𝒢.obj.obj (op g.left)),
            ((θ U y).hom.app (op g) (a * b)).down =
              ((θ U y).hom.app (op g) a).down ≫ ((θ U y).hom.app (op g) b).down) ∧
          (∀ (U : Space.SpacesEtale B S hS W)
              (y z : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (φ : y ⟶ z)
              (g : Over U) (a : 𝒢.obj.obj (op g.left)),
            ((θ U z).hom.app (op g) a).down =
              Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
                ((θ U y).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom) ∧
          ∀ (U : Space.SpacesEtale B S hS W)
            (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
            (a : 𝒢.obj.obj (op g.left)),
            ((θ U y).hom.app (op g) a).down =
              (Functor.pullbackFiberIdIso
                  ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y g.hom)).inv ≫
                ((θ g.left ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y
                    g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
                  (Functor.pullbackFiberIdIso
                    ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y
                      g.hom)).hom) ∧
        Space.SpacesEtale.CechVanishing
          ((sheafCompose (Space.SpacesEtale.topology B S hS W)
            commGroupAddCommGroupEquivalence.{u + 1}.functor).obj 𝒢)) :
    ∃ (W' : AlgebraicSpaces B S hS) (i : W ⟶ W')
      (x' : (algebraicSpaceStackFunctor B S hS).obj W' ⟶ 𝒳')
      (α : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x'),
      AlgebraicStacks.IsSmooth B S hS x' ∧
        Nonempty (IsTwoFibreProduct
          (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
            (algebraicSpaceStackFunctor B S hS).map i, α⟩ : TwoCommSq ι x')) ∧
        Space.IsAffineSpace B S hS W'.obj := by
  obtain ⟨𝒢, θ, hθ, hCech⟩ := hband
  obtain ⟨ξ⟩ := Space.SpacesEtale.nonempty_fiber_final_of_cechVanishing
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) isFiberedInGroupoids_proj hst hne hlc 𝒢
    ⟨θ, hθ⟩ hCech hW
  exact exists_lift_of_fiber_final hW ξ

/-- **Stacks 0CKI from the gerbe property and the quasi-coherence of the band.** As
`exists_lift_of_isGerbe_of_cechVanishing`, with the band given in the form of Stacks 0CKG (2): a
band `𝒢` of the gerbe in the sense of Stacks 0CJY which is a quasi-coherent `𝒪_W`-module, i.e.
whose restriction to the small étale site of `W` (Stacks 03G1) is the underlying abelian sheaf of
a quasi-coherent `𝒪_W`-module. -/
theorem exists_lift_of_isGerbe_of_isQuasicoherent (hW : Space.IsAffineSpace B S hS W.obj)
    (hst : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsStack
      (Space.SpacesEtale.topology B S hS W))
    (hne : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyNonempty
      (Space.SpacesEtale.topology B S hS W))
    (hlc : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyConnected
      (Space.SpacesEtale.topology B S hS W))
    (hband : haveI : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsFibered :=
        isFiberedInGroupoids_proj.isFibered
      haveI : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
        isFiberedInGroupoids_proj.fiber_isGroupoid
      ∃ (𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1})
        (θ : ∀ (U : Space.SpacesEtale B S hS W)
          (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
          (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
            (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf y y ⋙
              uliftFunctor.{u + 1, u + 1}),
        (∀ (U : Space.SpacesEtale B S hS W)
            (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
            (a b : 𝒢.obj.obj (op g.left)),
            ((θ U y).hom.app (op g) (a * b)).down =
              ((θ U y).hom.app (op g) a).down ≫ ((θ U y).hom.app (op g) b).down) ∧
          (∀ (U : Space.SpacesEtale B S hS W)
              (y z : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (φ : y ⟶ z)
              (g : Over U) (a : 𝒢.obj.obj (op g.left)),
            ((θ U z).hom.app (op g) a).down =
              Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
                ((θ U y).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom) ∧
          (∀ (U : Space.SpacesEtale B S hS W)
            (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
            (a : 𝒢.obj.obj (op g.left)),
            ((θ U y).hom.app (op g) a).down =
              (Functor.pullbackFiberIdIso
                  ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y g.hom)).inv ≫
                ((θ g.left ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y
                    g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
                  (Functor.pullbackFiberIdIso
                    ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y
                      g.hom)).hom) ∧
          ∃ M : SheafOfModules.{u + 1} (Space.structureRingSheaf B S hS W),
            M.IsQuasicoherentOnSite ∧
              Nonempty ((Space.spacesEtaleAbelianRestriction B S hS W).obj
                ((sheafCompose _ commGroupAddCommGroupEquivalence.{u + 1}.functor).obj 𝒢) ≅
                (SheafOfModules.toSheaf _).obj M)) :
    ∃ (W' : AlgebraicSpaces B S hS) (i : W ⟶ W')
      (x' : (algebraicSpaceStackFunctor B S hS).obj W' ⟶ 𝒳')
      (α : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x'),
      AlgebraicStacks.IsSmooth B S hS x' ∧
        Nonempty (IsTwoFibreProduct
          (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
            (algebraicSpaceStackFunctor B S hS).map i, α⟩ : TwoCommSq ι x')) ∧
        Space.IsAffineSpace B S hS W'.obj := by
  obtain ⟨𝒢, θ, h₁, h₂, h₃, M, hM, ⟨e⟩⟩ := hband
  exact exists_lift_of_isGerbe_of_cechVanishing hW hst hne hlc
    ⟨𝒢, θ, ⟨h₁, h₂, h₃⟩,
      Space.SpacesEtale.cechVanishing_of_restriction_iso_toSheaf M hM _ e⟩

end EtaleSmoothLift

end AlgebraicGeometry.Stack

end
