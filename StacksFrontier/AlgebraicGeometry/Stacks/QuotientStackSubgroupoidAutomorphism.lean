module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealizationAutomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupBaseChange

/-!
# Automorphism groups along the quotient stack of an open subgroupoid

Let `φ : H ⟶ K` be the inclusion of an open subgroupoid scheme on the same objects, and let `u`
be a point of the object scheme such that `H` contains the arrow of every stabilizer point of
`K` over `u`. Then a 1-morphism `f : 𝒰 ⟶ 𝒳` built as `𝒰 ≃ [U/H] ⟶ [U/K] ⟶ 𝒳`, the last arrow
fully faithful, induces an isomorphism between automorphism groups (Stacks 0DTW) at the point of
`|𝒰|` represented by `u`.

## Main results

* `CategoryTheory.Functor.bijective_verticalAutMap_iff_of_iso`: isomorphic functors over the base
  are bijective on the same vertical automorphism groups.
* `AlgebraicGeometry.Stack.inducesIsomorphismAt_of_quotientStackMap_realization`: the statement
  above, for any fully faithful `𝒰 ⟶ [U/H]` and `[U/K] ⟶ 𝒳` over the site and any field-valued
  point of `𝒰` whose image in `[U/H]` is presented by a point lying over `u`.

## References

* [Stacks Project, Tag 0DTW](https://stacks.math.columbia.edu/tag/0DTW)
* [Stacks Project, Tag 0DU4](https://stacks.math.columbia.edu/tag/0DU4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

universe uC vC uX vX uY vY

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y] {pX : X ⥤ C} {pY : Y ⥤ C}

/-- Isomorphic functors over the base are bijective on the same vertical automorphism groups:
the map of one is the map of the other followed by conjugation by the component of the
isomorphism. -/
theorem bijective_verticalAutMap_iff_of_iso (F F' : X ⥤ Y) (hF : F ⋙ pY = pX)
    (hF' : F' ⋙ pY = pX) (ι : F ≅ F') (a : X) :
    Function.Bijective (verticalAutMap F hF a) ↔ Function.Bijective (verticalAutMap F' hF' a) := by
  have key : (verticalAutMap F' hF' a : pX.verticalAut a → _) =
      (verticalAutConj pY (ι.app a)) ∘ (verticalAutMap F hF a) := by
    funext α
    apply Subtype.ext
    apply Aut.ext
    apply Iso.ext
    show F'.map (α : Aut a).asIso.hom = (ι.app a).inv ≫ F.map (α : Aut a).asIso.hom ≫ (ι.app a).hom
    rw [Iso.app_inv, Iso.app_hom, ι.hom.naturality, ← Category.assoc, ← NatTrans.comp_app,
      ι.inv_hom_id, NatTrans.id_app, Category.id_comp]
  rw [key]
  exact ((verticalAutConj pY (ι.app a)).bijective.of_comp_iff' _).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

open Stacks.Groupoids.GroupoidScheme

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 1-morphism `𝒰 ≃ [U/H] ⟶ [U/K] ⟶ 𝒳` preserves automorphism groups at a point over
which `H` contains the stabilizer.** Let `φ : H ⟶ K` be a morphism of groupoid schemes which is
an open immersion on arrows and an equality on objects, and let `u` be a point of the object
scheme of `K` such that the image of `φ` contains the arrow of every stabilizer point of `K` over
`u`. Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic stacks isomorphic to a composite
`E ⋙ [φ] ⋙ F` with `E : 𝒰 ⥤ [U/H]` and `F : [U/K] ⥤ 𝒳` fully faithful over the site, and let
`p` be a field-valued point of `𝒰` whose image under `E` is isomorphic, over the identity of its
field spectrum, to the object presented by a point of the object scheme lying over `u`. Then `f`
induces an isomorphism between automorphism groups at the point of `|𝒰|` represented by `p`. -/
theorem inducesIsomorphismAt_of_quotientStackMap_realization
    {H K : Stacks.Groupoids.GroupoidScheme S} (φ : Hom H K)
    [AlgebraicGeometry.IsOpenImmersion φ.mapArrows.left]
    (hHU : B.Contains H.objects.left) (hHR : B.Contains H.arrows.left)
    (hHP : B.Contains (pullback H.source H.target).left)
    (hKU : B.Contains K.objects.left) (hKR : B.Contains K.arrows.left)
    (hKP : B.Contains (pullback K.source K.target).left)
    (e : H.objects = K.objects) (hφ : φ.mapObjects = eqToHom e) (u : K.objects.left)
    (hstab : ∀ y : (AlgebraicGeometry.stabilizer K).left,
      (AlgebraicGeometry.stabilizer K).hom.base y = u →
        ∃ p : H.arrows.left,
          φ.mapArrows.left.base p = (AlgebraicGeometry.stabilizerArrow K).base y)
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
    (E : 𝒰.val.val ⥤ᵇ quotientStack (H.realization B hS hHU hHR hHP))
    (hE : E.toFunctor.FullyFaithful)
    (F : quotientStack (K.realization B hS hKU hKR hKP) ⥤ᵇ 𝒳.val.val)
    (hF : F.toFunctor.FullyFaithful)
    (ι : CatFiberedInGroupoids.homFunctor f.hom ≅ E.toFunctor ⋙
      (quotientStackMap (φ.realization B hS hHU hHR hHP hKU hKR hKP)).toFunctor ⋙ F.toFunctor)
    (p : FieldValuedPoint B S hS 𝒰.val.val)
    (x : (H.realization B hS hHU hHR hHP).objects.obj.obj (op p.base))
    (hx : Hom.IsOverPoint B hS hHU hHR hHP ((eqToHom e.symm).left.base u) p.base x)
    (j : E.obj p.obj ≅
      ((pointwiseToQuotientStackFiber (H.realization B hS hHU hHR hHP) p.base).obj x).1)
    (hj : (quotientStack (H.realization B hS hHU hHR hHP)).p.IsHomLift (𝟙 p.base) j.hom) :
    InducesIsomorphismAt B S hS f (pointClass B S hS 𝒰.val.val 𝒰.val.isFiberedInGroupoids p) := by
  let : 𝒰.val.val.p.IsFibered := 𝒰.val.isFiberedInGroupoids.isFibered
  let H' := H.realization B hS hHU hHR hHP
  let Φ := φ.realization B hS hHU hHR hHP hKU hKR hKP
  let Q := quotientStack H'
  have hQ : Q.p.IsFiberedInGroupoids := isFiberedInGroupoids_quotientStack H'
  let : Q.p.IsFibered := hQ.isFibered
  refine inducesIsomorphismAt_of_isIso_pointAutomorphismSpaceMap B S hS f p ?_
  refine (isIso_pointAutomorphismSpaceMap_iff_forall B S hS f p).2 fun W => ?_
  let g := sliceObj B S hS p.base W
  let b := Functor.pullbackFiber 𝒰.val.val.p (Functor.Fiber.mk p.over) g.hom
  let m := Functor.IsPreFibered.pullbackMap (Functor.Fiber.mk p.over).2 g.hom
  have hΦF : ((quotientStackMap Φ).toFunctor ⋙ F.toFunctor) ⋙ 𝒳.val.val.p = Q.p := by
    rw [Functor.assoc, F.w, (quotientStackMap Φ).w]
  have hcomp : (E.toFunctor ⋙ (quotientStackMap Φ).toFunctor ⋙ F.toFunctor) ⋙ 𝒳.val.val.p =
      𝒰.val.val.p := by
    rw [Functor.assoc, hΦF, E.w]
  show Function.Bijective (Functor.verticalAutMap (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) b.1)
  rw [Functor.bijective_verticalAutMap_iff_of_iso _ _ _ hcomp ι b.1]
  refine Functor.bijective_verticalAutMap_comp E.toFunctor
    ((quotientStackMap Φ).toFunctor ⋙ F.toFunctor) E.w hΦF hcomp b.1
    (Functor.bijective_verticalAutMap_of_fullyFaithful E.toFunctor E.w hE b.1) ?_
  refine Functor.bijective_verticalAutMap_comp (quotientStackMap Φ).toFunctor F.toFunctor
    (quotientStackMap Φ).w F.w hΦF (E.obj b.1) ?_
    (Functor.bijective_verticalAutMap_of_fullyFaithful F.toFunctor F.w hF _)
  let xF := (pointwiseToQuotientStackFiber H' p.base).obj x
  have hEm : Q.p.IsHomLift g.hom (E.toFunctor.map m) :=
    Functor.isHomLift_map_of_comp_eq E.w g.hom m
  have hc1 : Q.p.IsHomLift g.hom (E.toFunctor.map m ≫ j.hom) :=
    @IsHomLift.comp_lift_id_right _ _ _ _ Q.p _ _ _ _ _ g.hom (E.toFunctor.map m) hEm j.hom hj
  have hc1' : Q.p.IsStronglyCartesian g.hom (E.toFunctor.map m ≫ j.hom) :=
    hQ.isStronglyCartesian_homLift g.hom _
  let c2 := Functor.IsPreFibered.pullbackMap xF.2 g.hom
  have hc2 : Q.p.IsStronglyCartesian g.hom c2 := hQ.isStronglyCartesian_homLift g.hom c2
  let k₁ : E.obj b.1 ≅ (Functor.pullbackFiber Q.p xF g.hom).1 :=
    Functor.IsCartesian.domainUniqueUpToIso Q.p g.hom c2 (E.toFunctor.map m ≫ j.hom)
  let k₂ := Functor.Fiber.fiberInclusion.mapIso
    (presentedPullbackIso H' p.base x xF rfl g)
  refine Functor.bijective_verticalAutMap_of_iso' _ _ (k₁ ≪≫ k₂) ?_
  exact Hom.bijective_verticalAutMap_quotientStackMap_realization B hS φ hHU hHR hHP hKU hKR hKP
    e hφ u hstab g.left _ (Hom.isOverPoint_map B hS hHU hHR hHP _ g.hom x hx)

end AlgebraicGeometry.Stack

end
