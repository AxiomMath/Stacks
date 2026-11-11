module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentFlatFamilyDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDenseAffineFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints

/-!
# A module of `LQCoh^fbc(𝒪_𝒳)` killed by `c` along a flat surjection is parasitic

Let `𝒳` be an algebraic stack and `f : 𝒰 ⟶ 𝒳` a 1-morphism with `𝒰` the algebraic stack of an
algebraic space `U`, and let `c : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)`, `ℱ ↦ f^*ℱ|_{U_étale}`, be
the functor of Stacks 0GQS
(`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcSpaceRestriction`). Item (10) of Stacks 0GQS
says: if `f` is flat and surjective and `c(ℱ) = 0`, then `ℱ` is parasitic.

## The proof

The source's proof: `d(Q(ℱ)) = 0` by item (7); one may assume `U` is a scheme by the
compatibility of the restriction with étale localization (Stacks 0GQA); then Stacks 0GQF applied
to `0 → Q(ℱ)` and the morphism `U → 𝒳` gives `Q(ℱ) = 0`; and `ℱ` is parasitic by Stacks 0779.

This file follows that route, with item (7) replaced by its content at the objects that are used:

* the sections of `c(ℱ)` over an étale chart `V` of `U` are the sections of `ℱ` over the object
  `f(V)` of `𝒳` attached to `V`, so `c(ℱ) = 0` makes `ℱ` vanish there; and since every morphism
  of a category fibred in groupoids is cartesian, an object of `𝒳` with a morphism to `f(V₀)`
  lying over an étale morphism of schemes `W ⟶ V₀` is isomorphic to `f(W)`, the object attached
  to the étale chart `W ⟶ V₀ ⟶ U` — this is the compatibility with étale localization
  (`AlgebraicGeometry.Stack.AlgebraicStacks.subsingleton_obj_of_hom_map_chartObject`);
* `U` has a surjective étale chart `V₀` from a scheme (Stacks 025Y), and the 1-morphism named by
  `f(V₀)` is 2-isomorphic to `V₀ ⟶ 𝒰 ⟶ 𝒳`, hence surjective on points since `f` is
  (`AlgebraicGeometry.Stack.AlgebraicStacks.exists_surjective_pointsMap_map_chartObject`); the
  object `f(V₀)` is flat because `f` is
  (`AlgebraicGeometry.Stack.FlatFppf.flatObject_map_chartObject`) — this one object is the
  morphism `U → 𝒳` to which the source applies Stacks 0GQF;
* the counit `Q(ℱ) ⟶ ℱ` of the canonical coherator is bijective on sections over flat objects,
  its kernel and cokernel being parasitic (Stacks 0779 (2),
  `isParasitic_kernel_and_cokernel_coheratorAdjunction_counit` in the namespace
  `AlgebraicGeometry.Stack.AlgebraicStacks`, with
  `AlgebraicGeometry.Stack.isIso_app_of_isParasitic_kernel_cokernel`), and the objects of the
  small étale site of `f(V₀)` are flat and étale over `f(V₀)`; so `Q(ℱ)` vanishes on the small
  étale site of `f(V₀)`, which is what Stacks 0GQF needs of `0 ⟶ Q(ℱ)`
  (`AlgebraicGeometry.Stack.surjective_app_flatObject_of_surjective_smallEtaleOpen` and
  `AlgebraicGeometry.Stack.epi_of_surjective_app_flatObject`, applied to the zero endomorphism of
  `Q(ℱ)`);
* Stacks 0779 (1), `AlgebraicGeometry.Stack.AlgebraicStacks.isZero_coherator_obj_iff_isParasitic`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isParasitic_of_isZero_lqcohFbcSpaceRestriction_obj`:
  item (10) of Stacks 0GQS.

## Implementation notes

`ℱ` is read on the fppf site through `AlgebraicGeometry.Stack.fppfModuleOfLqcohSheafFbc`
(Stacks 0771 (1)), which keeps its underlying presheaf of modules, and the coherator is the
canonical one, `AlgebraicGeometry.Stack.AlgebraicStacks.coherator`. Parasitic is a condition on
sections only, so the conclusion is stated on the étale module `ℱ` itself.

## References

* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
* [Stacks Project, Tag 0GQF](https://stacks.math.columbia.edu/tag/0GQF)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

/-- **`c(ℱ) = 0` makes `ℱ` vanish at the objects attached to the étale charts.** The sections of
`c(ℱ)` over an étale chart `V` of `U` are the sections of `ℱ` over the object `f(V)` of `𝒳`. -/
theorem subsingleton_obj_map_chartObject_of_isZero (F : lqcohFbcModules B S hS 𝒳)
    (hF : IsZero ((lqcohFbcSpaceRestriction B S hS 𝒳 U hU f).obj F))
    (V : Space.SmallEtale B S hS U) :
    Subsingleton (F.obj.val.obj (op ((CatFiberedInGroupoids.homFunctor f.hom).obj
      (FlatFppf.chartObject.{u, w} B S hS U hU V)))) := by
  have h₁ := Functor.map_isZero (ObjectProperty.ι _) hF
  have h₂ := Functor.map_isZero (SheafOfModules.evaluation _ (op V)) h₁
  have h₃ := ModuleCat.subsingleton_of_isZero h₂
  exact h₃

/-- A presheaf of modules with no sections over an object has none over an isomorphic one. -/
theorem _root_.PresheafOfModules.subsingleton_obj_of_iso {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R) {X Y : C} (e : X ≅ Y)
    [h : Subsingleton (M.obj (op Y))] : Subsingleton (M.obj (op X)) :=
  @Equiv.subsingleton _ _
    ((M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).mapIso e.op).toEquiv.symm h

/-- **Vanishing at the objects attached to the étale charts propagates to the objects étale over
them** (the compatibility of Stacks 0GQA with étale localization). Let `M` be a presheaf of
modules on `𝒳` with no sections over `f(V)` for every étale chart `V` of `U`. If `g : y ⟶ f(V₀)`
lies over an étale morphism of schemes, then `M` has no sections over `y`: the composite
`p(y) ⟶ V₀ ⟶ U` is an étale chart `V'`, the object `f(V')` maps to `f(V₀)` over the same
morphism, and in the category fibred in groupoids `𝒳` the induced comparison `y ⟶ f(V')` lies
over an identity, hence is an isomorphism. -/
theorem subsingleton_obj_of_hom_map_chartObject {R : (𝒳.val.val.obj)ᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R)
    (hM : ∀ V : Space.SmallEtale B S hS U, Subsingleton (M.obj (op
      ((CatFiberedInGroupoids.homFunctor f.hom).obj (FlatFppf.chartObject.{u, w} B S hS U hU V)))))
    (V₀ : Space.SmallEtale B S hS U) {y : 𝒳.val.val.obj}
    (g : y ⟶ (CatFiberedInGroupoids.homFunctor f.hom).obj
      (FlatFppf.chartObject.{u, w} B S hS U hU V₀))
    (hg : Etale ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map g))) :
    Subsingleton (M.obj (op y)) := by
  have hx : 𝒳.val.val.p.obj ((CatFiberedInGroupoids.homFunctor f.hom).obj
      (FlatFppf.chartObject.{u, w} B S hS U hU V₀)) = V₀.obj.left :=
    Functor.congr_obj f.hom.hom.w _
  let w' : 𝒳.val.val.p.obj y ⟶ V₀.obj.left := 𝒳.val.val.p.map g ≫ eqToHom hx
  have hw' : Etale ((BigFppfOver.toScheme B S hS).map w') := by
    rw [Functor.map_comp, eqToHom_map]
    have := hg
    infer_instance
  let m := Space.SmallEtale.ofEtaleMapHom V₀ w' hw'
  let ψ := (Space.restrictionFunctor B S hS U (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p
    (StacksRepresentableCFG.EquivalenceOver.refl _)).map m
  have hψ : (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p.IsHomLift w' ψ :=
    (inferInstance : (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p.IsHomLift
      ((algebraicSpaceStack.{u, w} B S hS U hU).val.val.p.map ψ) ψ)
  have hfψ : 𝒳.val.val.p.IsHomLift w' ((CatFiberedInGroupoids.homFunctor f.hom).map ψ) :=
    PresheafOfCategories.isHomLift_map_of_comp f.hom.hom.w w' ψ hψ
  have hgl : 𝒳.val.val.p.IsHomLift w' g := IsHomLift.of_fac' _ w' g rfl hx (by simp [w'])
  have := Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift 𝒳.val.isFiberedInGroupoids w'
    ((CatFiberedInGroupoids.homFunctor f.hom).map ψ)
  let χ := Functor.IsStronglyCartesian.map 𝒳.val.val.p w'
    ((CatFiberedInGroupoids.homFunctor f.hom).map ψ) (g := 𝟙 _) (Category.id_comp w').symm g
  have := Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift 𝒳.val.isFiberedInGroupoids
    (𝟙 (𝒳.val.val.p.obj y)) χ
  have : IsIso χ :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.val.p (𝟙 (𝒳.val.val.p.obj y)) χ
  exact @PresheafOfModules.subsingleton_obj_of_iso _ _ _ M _ _ (asIso χ)
    (hM (Space.SmallEtale.ofEtaleMap V₀ w' hw'))

/-- **The étale chart of a surjective atlas names, through `f`, an object of `𝒳` whose
1-morphism is surjective on points**, when `f` is. For an atlas `V₀ ⟶ U` (Stacks 025Y), the
1-morphism `(Sch/V₀) ⟶ 𝒰` named by the object attached to `V₀` is surjective, its morphism of
representing presheaves being the atlas; and by the 2-Yoneda lemma the 1-morphism named by
`f(V₀)` is 2-isomorphic to its composite with `f`, read across the equality of the schemes below
the two objects. -/
theorem exists_surjective_pointsMap_map_chartObject (hsurj : Stack.IsSurjective B S hS f) :
    ∃ V₀ : Space.SmallEtale B S hS U, Function.Surjective (AlgebraicStacks.pointsMap B S hS
      (fibreObjectStackMap B S hS 𝒳 (𝒳.val.val.p.obj ((CatFiberedInGroupoids.homFunctor f.hom).obj
        (FlatFppf.chartObject.{u, w} B S hS U hU V₀))) (Functor.Fiber.mk rfl))) := by
  obtain ⟨T, a, hsa, hea⟩ := hU.exists_atlas
  let V₀ : Space.SmallEtale B S hS U := ⟨CostructuredArrow.mk a, hea⟩
  refine ⟨V₀, ?_⟩
  let c : schemeStack.{u, w} B S hS V₀.obj.left ⟶ algebraicSpaceStack.{u, w} B S hS U hU :=
    fibreObjectStackMap B S hS (algebraicSpaceStack.{u, w} B S hS U hU) V₀.obj.left
      (Functor.Fiber.mk (a := FlatFppf.chartObject.{u, w} B S hS U hU V₀) rfl)
  have hrep : representingMap B S hS (schemeFibredCategory B S hS V₀.obj.left)
      (algebraicSpaceStack.{u, w} B S hS U hU).val
      (yoneda.obj V₀.obj.left) U (PresheafOfCategories.sliceElementsEquivalenceOver V₀.obj.left)
      (StacksRepresentableCFG.EquivalenceOver.refl _) c.hom = a :=
    FlatFppf.representingMap_objectMorphism_chartObject.{u, w} B S hS U hU V₀
  have hc : IsSurjective B S hS c := by
    refine isSurjective_of_isSurjective_representingMap B S hS (yoneda.obj V₀.obj.left) U
      (isAlgebraicSpace_yoneda B S hS V₀.obj.left) hU
      (PresheafOfCategories.sliceElementsEquivalenceOver V₀.obj.left)
      (StacksRepresentableCFG.EquivalenceOver.refl _) c ?_
    have ha : Space.IsSurjective B S hS a :=
      Space.surjective_pointsMap_of_presheaf_surjective B S hS a hsa
    rw [hrep]
    exact ha
  let x := (CatFiberedInGroupoids.homFunctor f.hom).obj
    (FlatFppf.chartObject.{u, w} B S hS U hU V₀)
  have hx : 𝒳.val.val.p.obj x = V₀.obj.left := Functor.congr_obj f.hom.hom.w _
  have hψ : 𝒳.val.val.p.IsHomLift (eqToHom hx.symm) (𝟙 x) :=
    IsHomLift.of_fac' _ _ _ hx rfl (by simp)
  have h₂ : AlgebraicStacks.pointsMap B S hS (c ≫ f) =
      AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS (eqToHom hx.symm) ≫
        fibreObjectStackMap B S hS 𝒳 (𝒳.val.val.p.obj x) (Functor.Fiber.mk rfl)) :=
    AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
      ((fibreObjectStackMapFactorIso B S hS f (eqToHom hx.symm)
        (Functor.Fiber.mk (a := FlatFppf.chartObject.{u, w} B S hS U hU V₀) rfl)
        (Functor.Fiber.mk (a := x) rfl) (𝟙 x) hψ).hom)
  rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp] at h₂
  have hcomp : Function.Surjective (AlgebraicStacks.pointsMap B S hS f ∘
      AlgebraicStacks.pointsMap B S hS c) := hsurj.comp hc
  rw [h₂] at hcomp
  exact Function.Surjective.of_comp hcomp

/-- **Stacks 0GQS, item (10).** Let `f : 𝒰 ⟶ 𝒳` be a flat and surjective 1-morphism from the
algebraic stack of an algebraic space `U` to an algebraic stack `𝒳`, and let `ℱ` be an object of
`LQCoh^fbc(𝒪_𝒳)` with `c(ℱ) = f^*ℱ|_{U_étale} = 0`. Then `ℱ` is parasitic.

The route is the source's: the coherator `Q(ℱ)` agrees with `ℱ` at flat objects (Stacks 0779
(2)), so it vanishes on the small étale site of the flat object `f(V₀)` attached to a surjective
étale chart `V₀` of `U` (the compatibility of Stacks 0GQA with étale localization); Stacks 0GQF
for the zero endomorphism of `Q(ℱ)` and the flat object `f(V₀)`, whose 1-morphism is surjective,
gives `Q(ℱ) = 0`; and `ℱ` is parasitic by Stacks 0779 (1). -/
theorem isParasitic_of_isZero_lqcohFbcSpaceRestriction_obj
    (hf : AlgebraicStacks.IsFlat B S hS f) (hsurj : Stack.IsSurjective B S hS f)
    (F : lqcohFbcModules B S hS 𝒳)
    (hF : IsZero ((lqcohFbcSpaceRestriction B S hS 𝒳 U hU f).obj F)) :
    IsParasitic B S hS 𝒳 .etale F.obj.val := by
  let G := fppfModuleOfLqcohSheafFbc B (associatedBigEtaleSite B) rfl S hS 𝒳 F.obj F.property
  obtain ⟨V₀, hV₀⟩ := exists_surjective_pointsMap_map_chartObject B S hS 𝒳 U hU f hsurj
  let x := (CatFiberedInGroupoids.homFunctor f.hom).obj
    (FlatFppf.chartObject.{u, w} B S hS U hU V₀)
  have hxflat : flatObject B S hS 𝒳.val x :=
    FlatFppf.flatObject_map_chartObject B S hS 𝒳 U hU f hf V₀
  let Q := (coherator B S hS 𝒳).obj G.obj
  have hpar := isParasitic_kernel_and_cokernel_coheratorAdjunction_counit B S hS 𝒳
    (associatedBigEtaleSite B) rfl G.obj G.property
  have hQ : ∀ V, Subsingleton (Q.obj.val.obj (op ((smallEtaleToStack B (associatedBigEtaleSite B)
      rfl S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x).obj V))) := by
    intro V
    have hw := flatObject_smallEtaleToStack_obj B (associatedBigEtaleSite B) rfl S hS x hxflat V
    have hG : Subsingleton (G.obj.val.obj (op ((smallEtaleToStack B (associatedBigEtaleSite B)
        rfl S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x).obj V))) :=
      subsingleton_obj_of_hom_map_chartObject B S hS 𝒳 U hU f F.obj.val
        (subsingleton_obj_map_chartObject_of_isZero B S hS 𝒳 U hU f F hF) V₀
        (smallEtaleToStackArrow B (associatedBigEtaleSite B) rfl S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids x V)
        (etale_toScheme_map_smallEtaleToStackArrow B (associatedBigEtaleSite B) rfl S hS
          𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x V)
    have hinj := (isIso_app_of_isParasitic_kernel_cokernel B S hS
      ((coheratorAdjunction B S hS 𝒳).counit.app G.obj) hpar.1 hpar.2 _ hw).1
    exact ⟨fun a b => hinj (@Subsingleton.elim _ hG _ _)⟩
  have hepi : Epi (0 : Q ⟶ Q) := epi_of_surjective_app_flatObject (0 : Q ⟶ Q) fun _ hw hwa =>
    surjective_app_flatObject_of_surjective_smallEtaleOpen (associatedBigEtaleSite B) rfl
      (0 : Q ⟶ Q) (fun _ : Unit => x) (fun _ => hxflat) (fun q => ⟨(), hV₀ q⟩)
      (fun _ _ s => ⟨0, (hQ _).elim _ _⟩) hw hwa
  have hpG := (isZero_coherator_obj_iff_isParasitic B S hS 𝒳 (associatedBigEtaleSite B) rfl G.obj
    G.property).1 (IsZero.of_epi_zero Q Q)
  exact fun y hy => hpG y hy

end AlgebraicGeometry.Stack.AlgebraicStacks

end
