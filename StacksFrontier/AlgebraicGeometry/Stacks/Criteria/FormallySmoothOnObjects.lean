module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.On
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberHom
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# Formally smooth on objects

A morphism of categories fibred in groupoids over the big fppf category of a scheme is formally
smooth on objects when every object over the smaller member of an affine first-order thickening,
equipped with a comparison to the restriction of an object upstairs, lifts to an object over the
larger member, compatibly with the comparison.

This file proves the two stability properties of that condition,
`AlgebraicGeometry.Stack.IsFormallySmoothOnObjects`: it is preserved by base change along the
2-fibre product, and it is stable under composition. It then identifies it, for a 1-morphism
representable by algebraic spaces, with formal smoothness in the sense of the relative
properties of Stacks 03YK: every algebraic space representing a base change of the 1-morphism
along a scheme-valued point of the target has formally smooth structural morphism.

## Main definitions

* `AlgebraicGeometry.Space.formallySmoothProperty`: formal smoothness read as a property of
  morphisms in the category of algebraic spaces over `S`.
* `AlgebraicGeometry.BigFppfOver.IsRelativelyFormallySmooth`: formal smoothness of a 1-morphism
  representable by algebraic spaces, in the sense of Stacks 03YK.

## Main results

* `AlgebraicGeometry.BigFppfOver.isCartesian_homFunctor_map`: a 1-morphism of categories fibred in
  groupoids takes a morphism lying over `f` to a cartesian morphism over `f`.
* `AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjects_baseChange`: formal smoothness on
  objects is stable under base change.
* `AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjects_comp`: formal smoothness on objects is
  stable under composition.
* `AlgebraicGeometry.BigFppfOver.isRelativelyFormallySmooth_of_isFormallySmoothOnObjects`,
  `AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjects_of_isRelativelyFormallySmooth` and
  `AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjects_iff_isRelativelyFormallySmooth`:
  **Stacks 06D3**, the two implications and the equivalence they make up.
* `AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjectsOn_of_formallySmoothOn`: the
  implication from (2) to (1) of Stacks 06D3 against a class of larger test objects.
* `AlgebraicGeometry.BigFppfOver.isRelativelyFormallySmooth_iff_hasRelativeProperty`: that
  predicate is the relative property of Stacks 03YK at the formally smooth property.
* `AlgebraicGeometry.Space.FormallySmooth.isoComp`: formal smoothness is unchanged by
  precomposition with an isomorphism.
* `AlgebraicGeometry.Space.instIsStableUnderBaseChangeFormallySmoothProperty`: **Stacks 049U**
  at the packaged spelling, as an instance.

## Implementation notes

The restriction of an object of a fibre is the chosen pullback supplied by the prefibered
structure. The image of a restriction and the restriction of an image are two cartesian lifts of
the same morphism at the same object, hence canonically isomorphic in the fibre; the displayed
equation of the source is written in the fibre over the smaller scheme using that canonical
comparison.

The base change and its projection are the 2-fibre product
`AlgebraicGeometry.BigFppfOver.twoFibreProduct` and its second projection
`AlgebraicGeometry.BigFppfOver.twoFibreProductSnd`, which also serve limit preservation on
objects.

`AlgebraicGeometry.BigFppfOver.IsRelativelyFormallySmooth` writes out the quantifier of
`AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**) instead of invoking it, exactly
as the predicates of `StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMorphism` and
`StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism` do, and for the same reason: that
definition is stated for a `CategoryTheory.MorphismProperty` on the category of algebraic spaces
over `S` carrying two instance hypotheses — stability under base change and locality at the
target for the fppf precoverage — and while the first is available for formal smoothness, as
`AlgebraicGeometry.Space.instIsStableUnderBaseChangeFormallySmoothProperty` below, the second is
fppf descent for formal smoothness, which this library does not have. Writing the quantifier out
gives the same proposition with no hypothesis on the property, which is what a consumer of
Stacks 06D3 needs in order to state its result;
`AlgebraicGeometry.BigFppfOver.isRelativelyFormallySmooth_iff_hasRelativeProperty` recovers the
`AlgebraicGeometry.Stack.HasRelativeProperty` form the moment the missing instance is supplied,
and takes it as a hypothesis rather than looking it up, so it is available now. Compare
`StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth`, where both instances *are* available and
the predicate is defined through `AlgebraicGeometry.Stack.HasRelativeProperty` directly.

`AlgebraicGeometry.Space.formallySmoothProperty` and its base-change instance are stated here
rather than next to `AlgebraicGeometry.Space.FormallySmooth` because the packaging exists only to
serve that bridge; the content is `AlgebraicGeometry.Space.FormallySmooth.baseChange` (Stacks
049U) for the canonical pullback square of presheaves, transported to an arbitrary cartesian
square of algebraic spaces along
`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`.

Only `AlgebraicGeometry.spacesOverSmallerBaseFunctor`, the forward functor of Stacks 04SG, is
needed to read the structural morphism of a space over `U` as a morphism of spaces over `S`; the
equivalence of Stacks 04SG is not.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 06D1](https://stacks.math.columbia.edu/tag/06D1)
* [Stacks Project, Tag 06D2](https://stacks.math.columbia.edu/tag/06D2)
* [Stacks Project, Tag 06D3](https://stacks.math.columbia.edu/tag/06D3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

/-- Formal smoothness (Stacks 049S, part (1)) as a property of morphisms in the category of
algebraic spaces over `S`. This is the packaging
`AlgebraicGeometry.Stack.HasRelativeProperty` asks for, the counterpart for formal smoothness
of `AlgebraicGeometry.Space.smoothMorphismProperty`. -/
abbrev formallySmoothProperty (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => FormallySmooth f.hom

universe v

/-- Formal smoothness of a transformation of set-valued functors on the big fppf site of `S` is
unchanged by precomposition with an isomorphism of its source: a lift of a square against the
isomorphic source transports to a lift of the original square, and back. -/
theorem FormallySmooth.isoComp {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F' F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (e : F' ≅ F) {a : F ⟶ G}
    (ha : FormallySmooth a) : FormallySmooth (e.hom ≫ a) := by
  intro T T' hT hT' i hi x t hxt
  obtain ⟨z, hz₁, hz₂⟩ :=
    ha T T' hT hT' i hi (e.hom.app (Opposite.op T) x) t (by simpa using hxt)
  refine ⟨e.inv.app (Opposite.op T') z, ?_, ?_⟩
  · have hn := NatTrans.naturality_apply e.inv i.op z
    rw [hz₁] at hn
    simpa using hn.symm
  · simpa using hz₂

/-- **Stacks 049U** at the packaged spelling: formal smoothness, as a morphism property of
algebraic spaces over `S`, is stable under base change. A cartesian square of algebraic spaces
is cartesian as a square of presheaves
(`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`), hence identified with the canonical
pullback square of `AlgebraicGeometry.Space.FppfFunctorPullbackSituation`, where
`AlgebraicGeometry.Space.FormallySmooth.baseChange` applies. -/
@[sga "3 XI 1.6" "partial"]
instance instIsStableUnderBaseChangeFormallySmoothProperty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (formallySmoothProperty B S hS).IsStableUnderBaseChange where
  of_isPullback {X Y Y' Z f g f' g'} sq hg := by
    let D : FppfFunctorPullbackSituation.{u, u} :=
      { B := B, S := S, hS := hS, F := Y.1, G := Z.1, H := X.1, a := g.hom, b := f.hom }
    let e : D.fibreProduct ≅ Y'.1 :=
      D.isPullback.isoIsPullback _ _
        (AlgebraicGeometry.AlgebraicSpaces.isPullback_hom B S hS sq).flip
    have he : e.inv ≫ D.toH = g'.hom :=
      D.isPullback.isoIsPullback_inv_fst _ _
        (AlgebraicGeometry.AlgebraicSpaces.isPullback_hom B S hS sq).flip
    have hiso : FormallySmooth (e.inv ≫ D.toH) :=
      FormallySmooth.isoComp e.symm (FormallySmooth.baseChange D hg)
    rwa [he] at hiso

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigFppfOver

/- The two stability proofs below reason about morphisms of the fibre categories of the structure
functors `𝒳.val.p`. Those spellings are built from definitions the `implicit` transparency level
does not unfold -- `InducedBicategory`, so that `𝒳.val` is a subtype at all; `Functor.Fiber` and
its inclusion and induced functors; the 2-fibre product's structure functor and projections -- so
the goals are not type-correct at that level and `rw`, `simp` and `Trans` synthesis decline to act
on them. Naming the unfolding chain here is what lets the ordinary tactics see through it. -/
attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.BasedCategory.ofFunctor CategoryTheory.TwoFibreProductOver.structureFunctor
  CategoryTheory.TwoFibreProductOver.fst CategoryTheory.TwoFibreProductOver.snd
  twoFibreProduct twoFibreProductSnd
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.Fiber.mapOfComp CategoryTheory.Functor.Fiber.inducedFunctor
  CategoryTheory.instCategoryObj

universe u v w u₁ v₁ u₂ v₂

/-- A 1-morphism of categories fibred in groupoids carries a morphism lying over `f` to a
cartesian morphism over `f`; it is even strongly cartesian, by
`CategoryTheory.CatFiberedInGroupoids.isStronglyCartesian_map`. -/
lemma isCartesian_homFunctor_map {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    {𝒳 𝒴 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞} (G : 𝒳 ⟶ 𝒴) {R T : 𝒞}
    {a b : 𝒳.val.obj} (f : R ⟶ T) (φ : a ⟶ b) [𝒳.val.p.IsHomLift f φ] :
    𝒴.val.p.IsCartesian f ((CatFiberedInGroupoids.homFunctor G).map φ) :=
  @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ _ _ _ _ _ _ _
    (CatFiberedInGroupoids.isStronglyCartesian_map G f φ)

/-- **Stacks 06D1.** Formal smoothness on objects is stable under base change. -/
@[stacks 06D1,
  stacks 0H1I "base change of a formally smooth morphism of algebraic stacks is formally smooth"]
theorem isFormallySmoothOnObjects_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
      (BigFppfOver B S hS))
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    (hp : Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p) :
    Stack.IsFormallySmoothOnObjects B S hS
      (twoFibreProduct B S hS 𝒳 𝒴 𝒵 p q) 𝒵
      (twoFibreProductSnd B S hS 𝒳 𝒴 𝒵 p q) := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
  unfold Stack.IsFormallySmoothOnObjects at hp ⊢
  intro F hF pU compare U U' i hU hU' hth W y' γ
  let Xp := 𝒳.val.p
  let Yp := 𝒴.val.p
  let Zp := 𝒵.val.p
  let Fp := CatFiberedInGroupoids.homFunctor p
  let Gp := CatFiberedInGroupoids.homFunctor q
  let hFp := CatFiberedInGroupoids.homFunctor_comp_p p
  let hGp := CatFiberedInGroupoids.homFunctor_comp_p q
  let qU := fun V => Functor.Fiber.mapOfComp Zp Yp Gp hGp V
  rcases W with ⟨P, hP⟩
  change P.base = U at hP
  cases hP
  let x : Xp.Fiber P.base := ⟨P.x, P.hx⟩
  let z : Zp.Fiber P.base := ⟨P.y, P.hy⟩
  change z ≅ Zp.pullbackFiber y' i at γ
  have : Yp.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have : Zp.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
  let qCompare : Yp.pullbackFiber ((qU U').obj y') i ≅
      (qU P.base).obj (Zp.pullbackFiber y' i) :=
    Functor.fiberIsoOfCartesian i
      (Functor.IsPreFibered.pullbackMap ((qU U').obj y').2 i)
      (Gp.map (Functor.IsPreFibered.pullbackMap y'.2 i))
      (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
      (isCartesian_homFunctor_map q i (Functor.IsPreFibered.pullbackMap y'.2 i))
  -- The comparison isomorphism of `P`, read in the fibre over `P.base`. Its endpoints are the
  -- images of `x` and `z` under the induced fibre functors: those are the same objects of the
  -- fibre, so the type ascription is all that is needed to retype `η₀`.
  let η₀ := TwoFibreProductOver.fibreIso Xp Zp Yp Fp Gp hFp hGp P
  let η : (Functor.Fiber.mapOfComp Xp Yp Fp hFp P.base).obj x ≅ (qU P.base).obj z := η₀
  let α : (Functor.Fiber.mapOfComp Xp Yp Fp hFp P.base).obj x ≅
      Yp.pullbackFiber ((qU U').obj y') i :=
    η.trans ((qU P.base).mapIso γ) ≪≫ qCompare.symm
  obtain ⟨x', β, γ', hsq⟩ := hp P.base U' i hU hU' hth x ((qU U').obj y') α
  let P' : TwoFibreProductOver Xp Zp Yp Fp Gp :=
    { base := U'
      x := x'.1
      y := y'.1
      hx := x'.2
      hy := y'.2
      iso := Functor.Fiber.fiberInclusion.mapIso γ'
      vertical := γ'.hom.2 }
  let W' : (twoFibreProduct B S hS 𝒳 𝒴 𝒵 p q).val.p.Fiber U' := ⟨P', rfl⟩
  have hproj : (pU U').obj W' = y' := by
    apply Subtype.ext
    rfl
  let δ' : (pU U').obj W' ≅ y' := eqToIso hproj
  let pbXMap := Functor.IsPreFibered.pullbackMap x'.2 i
  let pbZMap := Functor.IsPreFibered.pullbackMap y'.2 i
  let pU0 := fun V => Functor.Fiber.mapOfComp Xp Yp Fp hFp V
  let pCompare := fun (V V' : BigFppfOver B S hS) (j : V ⟶ V')
      (a : Xp.Fiber V') =>
    Functor.fiberIsoOfCartesian (p := Yp)
      (z := Functor.pullbackFiber Yp ((pU0 V').obj a) j)
      (z' := (pU0 V).obj (Functor.pullbackFiber Xp a j))
      (a := Fp.obj a.1) j
      (Functor.IsPreFibered.pullbackMap ((pU0 V').obj a).2 j)
      (Fp.map (Functor.IsPreFibered.pullbackMap a.2 j))
      (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
      (isCartesian_homFunctor_map p j (Functor.IsPreFibered.pullbackMap a.2 j))
  let pbYqMap := Functor.IsPreFibered.pullbackMap ((qU U').obj y').2 i
  let aX := Functor.Fiber.fiberInclusion.map β.inv ≫ pbXMap
  let aZ := Functor.Fiber.fiberInclusion.map γ.hom ≫ pbZMap
  have hβinv : Xp.IsHomLift (𝟙 P.base) (Functor.Fiber.fiberInclusion.map β.inv) :=
    β.inv.2
  have hγ : Zp.IsHomLift (𝟙 P.base) (Functor.Fiber.fiberInclusion.map γ.hom) :=
    γ.hom.2
  have hpbX : Xp.IsHomLift i pbXMap :=
    (Functor.IsPreFibered.pullbackMap.IsCartesian x'.2 i).toIsHomLift
  have hpbZ : Zp.IsHomLift i pbZMap :=
    (Functor.IsPreFibered.pullbackMap.IsCartesian y'.2 i).toIsHomLift
  have haX : Xp.IsHomLift i aX := by
    simpa [aX] using @IsHomLift.comp _ _ _ _ Xp _ _ _ _ _ _ (𝟙 P.base) i
      (Functor.Fiber.fiberInclusion.map β.inv) pbXMap hβinv hpbX
  have haZ : Zp.IsHomLift i aZ := by
    simpa [aZ] using @IsHomLift.comp _ _ _ _ Zp _ _ _ _ _ _ (𝟙 P.base) i
      (Functor.Fiber.fiberInclusion.map γ.hom) pbZMap hγ hpbZ
  have hcmpFac : Functor.Fiber.fiberInclusion.map (pCompare P.base U' i x').hom ≫
      Fp.map pbXMap = Functor.IsPreFibered.pullbackMap ((pU0 U').obj x').2 i := by
    exact Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _
  have hqMapGamma : Functor.Fiber.fiberInclusion.map ((qU P.base).map γ.hom) =
      Gp.map (Functor.Fiber.fiberInclusion.map γ.hom) :=
    Functor.Fiber.fiberInclusion_map_mapOfComp_map Zp Yp Gp hGp P.base γ.hom
  have hηmap : Functor.Fiber.fiberInclusion.map η.hom = P.iso.hom := rfl
  have hqCompareInv : Functor.Fiber.fiberInclusion.map qCompare.inv ≫ pbYqMap =
      Gp.map pbZMap := by
    exact Functor.fiberIsoOfCartesian_inv_fac i _ _ _ _
  have hαfac : Functor.Fiber.fiberInclusion.map α.hom ≫ pbYqMap =
      P.iso.hom ≫ Gp.map (Functor.Fiber.fiberInclusion.map γ.hom) ≫ Gp.map pbZMap := by
    simp only [α, Iso.trans_hom, Functor.mapIso_hom,
      Functor.Fiber.fiberInclusion.map_comp]
    rw [hηmap, hqMapGamma]
    simpa [Category.assoc] using congrArg (fun f => P.iso.hom ≫ Gp.map
      (Functor.Fiber.fiberInclusion.map γ.hom) ≫ f) hqCompareInv
  have hsqPost :
      Functor.Fiber.fiberInclusion.map (pCompare P.base U' i x').hom ≫
        Fp.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
          Functor.Fiber.fiberInclusion.map α.hom ≫ pbYqMap =
        Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberHom γ'.hom i) ≫ pbYqMap := by
    have h := congrArg (fun f => f ≫ pbYqMap)
      (congrArg (fun f => Functor.Fiber.fiberInclusion.map f) hsq)
    simpa [pCompare, pU0, Functor.Fiber.fiberInclusion.map_comp,
      Functor.Fiber.fiberInclusion_map_mapOfComp_map] using h
  have hγ'fac : Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberHom γ'.hom i) ≫
      pbYqMap = Functor.IsPreFibered.pullbackMap ((pU0 U').obj x').2 i ≫
        Functor.Fiber.fiberInclusion.map γ'.hom :=
    Functor.pullbackFiberHom_fac γ'.hom i
  have htotal :
      Functor.Fiber.fiberInclusion.map (pCompare P.base U' i x').hom ≫
        Fp.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
          P.iso.hom ≫ Gp.map (Functor.Fiber.fiberInclusion.map γ.hom) ≫ Gp.map pbZMap =
        Functor.Fiber.fiberInclusion.map (pCompare P.base U' i x').hom ≫
          Fp.map pbXMap ≫ Functor.Fiber.fiberInclusion.map γ'.hom := by
    calc
      _ = Functor.Fiber.fiberInclusion.map (pCompare P.base U' i x').hom ≫
          Fp.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
            Functor.Fiber.fiberInclusion.map α.hom ≫ pbYqMap := by rw [hαfac]
      _ = Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberHom γ'.hom i) ≫
          pbYqMap := hsqPost
      _ = _ := by
        rw [hγ'fac, ← hcmpFac]
        simp [Category.assoc]
  have hcancel :
      Fp.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
          P.iso.hom ≫ Gp.map (Functor.Fiber.fiberInclusion.map γ.hom) ≫ Gp.map pbZMap =
        Fp.map pbXMap ≫ Functor.Fiber.fiberInclusion.map γ'.hom :=
    (cancel_epi (Functor.Fiber.fiberInclusion.map
      (pCompare P.base U' i x').hom)).mp htotal
  have hpre : P.iso.hom ≫ Gp.map (Functor.Fiber.fiberInclusion.map γ.hom) ≫
      Gp.map pbZMap =
      Fp.map (Functor.Fiber.fiberInclusion.map β.inv) ≫ Fp.map pbXMap ≫
        Functor.Fiber.fiberInclusion.map γ'.hom := by
    simpa [Category.assoc] using
      congrArg (fun f => Fp.map (Functor.Fiber.fiberInclusion.map β.inv) ≫ f) hcancel
  let θ : P ⟶ P' :=
    { hbase := i
      a := aX
      b := aZ
      ha := haX
      hb := haZ
      w := by
        dsimp [aX, aZ]
        simp only [Functor.map_comp, Category.assoc]
        exact hpre.symm }
  let BC := twoFibreProduct B S hS 𝒳 𝒴 𝒵 p q
  let BCp := BC.val.p
  have : BCp.IsFibered := BC.isFiberedInGroupoids.isFibered
  have hθLift : BCp.IsHomLift i θ := by
    change (TwoFibreProductOver.structureFunctor Xp Zp Yp Fp Gp).IsHomLift i θ
    exact IsHomLift.of_fac' (TwoFibreProductOver.structureFunctor Xp Zp Yp Fp Gp)
      i θ rfl rfl (by simp [θ, TwoFibreProductOver.structureFunctor])
  have hθSC : BCp.IsStronglyCartesian i θ :=
    BC.isFiberedInGroupoids.isStronglyCartesian_homLift i θ
  have hθCart : BCp.IsCartesian i θ := inferInstance
  let pbProdMap := Functor.IsPreFibered.pullbackMap W'.2 i
  let Wsource : BCp.Fiber P.base := ⟨P, rfl⟩
  let βprod : BCp.pullbackFiber W' i ≅ Wsource :=
    Functor.fiberIsoOfCartesian (p := BCp) i pbProdMap θ
      (Functor.IsPreFibered.pullbackMap.IsCartesian W'.2 i) hθCart
  have hβprodFac : Functor.Fiber.fiberInclusion.map βprod.hom ≫ θ = pbProdMap := by
    exact Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _
  let pbProjMap := Functor.IsPreFibered.pullbackMap ((pU U').obj W').2 i
  have hbcLift : BCp.IsHomLift i pbProdMap :=
    (Functor.IsPreFibered.pullbackMap.IsCartesian W'.2 i).toIsHomLift
  have hcompareFac : Functor.Fiber.fiberInclusion.map
      (compare P.base U' i W').hom ≫ F.map pbProdMap = pbProjMap := by
    exact Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _
  have hmapβ : Functor.Fiber.fiberInclusion.map ((pU P.base).map βprod.hom) =
      F.map (Functor.Fiber.fiberInclusion.map βprod.hom) :=
    Functor.Fiber.fiberInclusion_map_mapOfComp_map BCp Zp F hF P.base βprod.hom
  have hFθ : F.map θ = Functor.Fiber.fiberInclusion.map γ.hom ≫ pbZMap := by
    change (TwoFibreProductOver.snd Xp Zp Yp Fp Gp).map θ = _
    simp [θ, aZ]
  refine ⟨W', βprod, δ', ?_⟩
  apply Functor.fiber_hom_ext_of_cartesian (p := Zp) i pbProjMap
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
  have hleft : Functor.Fiber.fiberInclusion.map (compare P.base U' i W').hom ≫
      F.map (Functor.Fiber.fiberInclusion.map βprod.hom) ≫
        Functor.Fiber.fiberInclusion.map γ.hom ≫ pbProjMap = pbProjMap := by
    calc
      _ = Functor.Fiber.fiberInclusion.map (compare P.base U' i W').hom ≫
          F.map (Functor.Fiber.fiberInclusion.map βprod.hom) ≫ F.map θ := by
            rw [hFθ]
      _ = Functor.Fiber.fiberInclusion.map (compare P.base U' i W').hom ≫
          F.map (Functor.Fiber.fiberInclusion.map βprod.hom ≫ θ) := by
            rw [← Functor.map_comp]
      _ = Functor.Fiber.fiberInclusion.map (compare P.base U' i W').hom ≫
          F.map pbProdMap := by rw [hβprodFac]
      _ = pbProjMap := hcompareFac
  have hrhs : Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberHom δ'.hom i) ≫
      pbProjMap = pbProjMap := by
    rw [Functor.pullbackFiberHom_fac]
    have hδ : Functor.Fiber.fiberInclusion.map δ'.hom = 𝟙 _ := by
      simp [δ']
    rw [hδ]
    exact Category.comp_id pbProjMap
  simpa [Category.assoc, hmapβ] using hleft.trans hrhs.symm

/-- **Stacks 06D2.** A composite of morphisms formally smooth on objects is formally smooth on
objects. -/
@[stacks 06D2,
  stacks 0H1J "the case of algebraic stacks, formally smooth being formally smooth on objects"]
theorem isFormallySmoothOnObjects_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (p : 𝒳 ⟶ 𝒴) (q : 𝒴 ⟶ 𝒵)
    (hp : Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p)
    (hq : Stack.IsFormallySmoothOnObjects B S hS 𝒴 𝒵 q) :
    Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒵 (p ≫ q) := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
  unfold Stack.IsFormallySmoothOnObjects at hp hq ⊢
  intro Fcomp hFcomp pUcomp compareComp U U' i hU hU' hth x z' γ
  let pMap := Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor_comp_p p)
  let qMap := Functor.Fiber.mapOfComp 𝒴.val.p 𝒵.val.p
    (CatFiberedInGroupoids.homFunctor q) (CatFiberedInGroupoids.homFunctor_comp_p q)
  let pCompare := fun (V V' : BigFppfOver B S hS) (j : V ⟶ V')
    (a : 𝒳.val.p.Fiber V') =>
    Functor.fiberIsoOfCartesian (p := 𝒴.val.p)
      (z := Functor.pullbackFiber 𝒴.val.p ((pMap V').obj a) j)
      (z' := (pMap V).obj (Functor.pullbackFiber 𝒳.val.p a j))
      (a := (CatFiberedInGroupoids.homFunctor p).obj a.1) j
      (Functor.IsPreFibered.pullbackMap ((pMap V').obj a).2 j)
      ((CatFiberedInGroupoids.homFunctor p).map
        (Functor.IsPreFibered.pullbackMap a.2 j))
      (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
      (isCartesian_homFunctor_map p j (Functor.IsPreFibered.pullbackMap a.2 j))
  let qCompare := fun (V V' : BigFppfOver B S hS) (j : V ⟶ V')
    (a : 𝒴.val.p.Fiber V') =>
    Functor.fiberIsoOfCartesian (p := 𝒵.val.p)
      (z := Functor.pullbackFiber 𝒵.val.p ((qMap V').obj a) j)
      (z' := (qMap V).obj (Functor.pullbackFiber 𝒴.val.p a j))
      (a := (CatFiberedInGroupoids.homFunctor q).obj a.1) j
      (Functor.IsPreFibered.pullbackMap ((qMap V').obj a).2 j)
      ((CatFiberedInGroupoids.homFunctor q).map
        (Functor.IsPreFibered.pullbackMap a.2 j))
      (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
      (isCartesian_homFunctor_map q j (Functor.IsPreFibered.pullbackMap a.2 j))
  have htotal (a : 𝒳.val.obj) :
      (CatFiberedInGroupoids.homFunctor (p ≫ q)).obj a =
        (CatFiberedInGroupoids.homFunctor q).obj
          ((CatFiberedInGroupoids.homFunctor p).obj a) := by rfl
  let qx := (pMap U).obj x
  have hobj :
      (Functor.Fiber.mapOfComp 𝒳.val.p 𝒵.val.p
        (CatFiberedInGroupoids.homFunctor (p ≫ q)) hFcomp U).obj x =
      (Functor.Fiber.mapOfComp 𝒴.val.p 𝒵.val.p
        (CatFiberedInGroupoids.homFunctor q)
        (CatFiberedInGroupoids.homFunctor_comp_p q) U).obj qx :=
    Subtype.ext (htotal x.1)
  have hpFac (x' : 𝒳.val.p.Fiber U') :
      Functor.Fiber.fiberInclusion.map (pCompare U U' i x').hom ≫
          (CatFiberedInGroupoids.homFunctor p).map
            (Functor.IsPreFibered.pullbackMap x'.2 i) =
        Functor.IsPreFibered.pullbackMap ((pMap U').obj x').2 i := by
    simp [pCompare]
  have hqCompareFac (a : 𝒴.val.p.Fiber U') :
      Functor.Fiber.fiberInclusion.map (qCompare U U' i a).hom ≫
          (CatFiberedInGroupoids.homFunctor q).map
            (Functor.IsPreFibered.pullbackMap a.2 i) =
        Functor.IsPreFibered.pullbackMap ((qMap U').obj a).2 i := by
    simp [qCompare]
  have hqMapMap {a b : 𝒴.val.p.Fiber U} (φ : a ⟶ b) :
      Functor.Fiber.fiberInclusion.map ((qMap U).map φ) =
        (CatFiberedInGroupoids.homFunctor q).map
          (Functor.Fiber.fiberInclusion.map φ) := by
    simpa [qMap] using
      (Functor.Fiber.fiberInclusion_map_mapOfComp_map 𝒴.val.p 𝒵.val.p
        (CatFiberedInGroupoids.homFunctor q)
        (CatFiberedInGroupoids.homFunctor_comp_p q) U φ)
  have hqMapMap' {a b : 𝒴.val.p.Fiber U'} (φ : a ⟶ b) :
      Functor.Fiber.fiberInclusion.map ((qMap U').map φ) =
        (CatFiberedInGroupoids.homFunctor q).map
          (Functor.Fiber.fiberInclusion.map φ) := by
    simpa [qMap] using
      (Functor.Fiber.fiberInclusion_map_mapOfComp_map 𝒴.val.p 𝒵.val.p
        (CatFiberedInGroupoids.homFunctor q)
        (CatFiberedInGroupoids.homFunctor_comp_p q) U' φ)
  have hFcompMap {a b : 𝒳.val.obj} (f : a ⟶ b) :
      Fcomp.map f = (CatFiberedInGroupoids.homFunctor q).map
        ((CatFiberedInGroupoids.homFunctor p).map f) := by rfl
  have hcompMap {a b : 𝒳.val.p.Fiber U} (f : a ⟶ b) :
      (pUcomp U).map f = (qMap U).map ((pMap U).map f) :=
    Subtype.ext (hFcompMap (Functor.Fiber.fiberInclusion.map f))
  have hcompare (x' : 𝒳.val.p.Fiber U') :
      (compareComp U U' i x').hom =
        (qCompare U U' i ((pMap U').obj x')).hom ≫
          (qMap U).map (pCompare U U' i x').hom := by
    refine Functor.fiber_hom_ext_of_cartesian i
      (Fcomp.map (Functor.IsPreFibered.pullbackMap x'.2 i))
      (isCartesian_homFunctor_map (p ≫ q) i
        (Functor.IsPreFibered.pullbackMap x'.2 i))
      _ _ ?_
    have hL : Functor.Fiber.fiberInclusion.map (compareComp U U' i x').hom ≫
        Fcomp.map (Functor.IsPreFibered.pullbackMap x'.2 i) =
      Functor.IsPreFibered.pullbackMap ((pUcomp U').obj x').2 i :=
      Functor.fiberIsoOfCartesian_hom_fac i
        (p := 𝒵.val.p)
        (z := Functor.pullbackFiber 𝒵.val.p ((pUcomp U').obj x') i)
        (z' := (pUcomp U).obj (Functor.pullbackFiber 𝒳.val.p x' i))
        (a := Fcomp.obj x'.1)
        (Functor.IsPreFibered.pullbackMap ((pUcomp U').obj x').2 i)
        (Fcomp.map (Functor.IsPreFibered.pullbackMap x'.2 i))
        (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
        (isCartesian_homFunctor_map (p ≫ q) i
          (Functor.IsPreFibered.pullbackMap x'.2 i))
    have hR : Functor.Fiber.fiberInclusion.map
        ((qCompare U U' i ((pMap U').obj x')).hom ≫
          (qMap U).map (pCompare U U' i x').hom) ≫
        Fcomp.map (Functor.IsPreFibered.pullbackMap x'.2 i) =
      Functor.IsPreFibered.pullbackMap ((pUcomp U').obj x').2 i := by
      rw [Functor.map_comp, hqMapMap, hFcompMap]
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun t => Functor.Fiber.fiberInclusion.map
        (qCompare U U' i ((pMap U').obj x')).hom ≫ t)
        ((Functor.map_comp (CatFiberedInGroupoids.homFunctor q) _ _).symm.trans
          (congrArg (CatFiberedInGroupoids.homFunctor q).map (hpFac x')))).trans ?_
      exact hqCompareFac ((pMap U').obj x')
    exact hL.trans hR.symm
  have hqCompareNaturality {a b : 𝒴.val.p.Fiber U'} (δ : a ⟶ b) :
      (qCompare U U' i a).hom ≫
          (qMap U).map (Functor.pullbackFiberHom δ i) =
        Functor.pullbackFiberHom ((qMap U').map δ) i ≫ (qCompare U U' i b).hom := by
    refine Functor.fiber_hom_ext_of_cartesian i
      ((CatFiberedInGroupoids.homFunctor q).map
        (Functor.IsPreFibered.pullbackMap b.2 i))
      (isCartesian_homFunctor_map q i (Functor.IsPreFibered.pullbackMap b.2 i))
      _ _ ?_
    rw [Functor.Fiber.fiberInclusion.map_comp,
      Functor.Fiber.fiberInclusion.map_comp, hqMapMap]
    calc
      (Functor.Fiber.fiberInclusion.map (qCompare U U' i a).hom ≫
          (CatFiberedInGroupoids.homFunctor q).map
            (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberHom δ i))) ≫
          (CatFiberedInGroupoids.homFunctor q).map
            (Functor.IsPreFibered.pullbackMap b.2 i) =
        Functor.Fiber.fiberInclusion.map (qCompare U U' i a).hom ≫
          (CatFiberedInGroupoids.homFunctor q).map
            (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberHom δ i) ≫
              Functor.IsPreFibered.pullbackMap b.2 i) := by
          rw [Category.assoc, ← Functor.map_comp]
      _ = Functor.Fiber.fiberInclusion.map (qCompare U U' i a).hom ≫
          (CatFiberedInGroupoids.homFunctor q).map
            (Functor.IsPreFibered.pullbackMap a.2 i ≫
              Functor.Fiber.fiberInclusion.map δ) := by
          rw [Functor.pullbackFiberHom_fac]
      _ = Functor.IsPreFibered.pullbackMap ((qMap U').obj a).2 i ≫
          Functor.Fiber.fiberInclusion.map ((qMap U').map δ) := by
          rw [Functor.map_comp, ← Category.assoc, hqCompareFac a, hqMapMap']
      _ = Functor.Fiber.fiberInclusion.map
            (Functor.pullbackFiberHom ((qMap U').map δ) i) ≫
          Functor.IsPreFibered.pullbackMap ((qMap U').obj b).2 i := by
          rw [← Functor.pullbackFiberHom_fac]
      _ = Functor.Fiber.fiberInclusion.map
            (Functor.pullbackFiberHom ((qMap U').map δ) i) ≫
          (Functor.Fiber.fiberInclusion.map (qCompare U U' i b).hom ≫
            (CatFiberedInGroupoids.homFunctor q).map
              (Functor.IsPreFibered.pullbackMap b.2 i)) := by
          rw [← hqCompareFac b]
      _ = (Functor.Fiber.fiberInclusion.map
          (Functor.pullbackFiberHom ((qMap U').map δ) i) ≫
          Functor.Fiber.fiberInclusion.map (qCompare U U' i b).hom) ≫
          (CatFiberedInGroupoids.homFunctor q).map
            (Functor.IsPreFibered.pullbackMap b.2 i) := by
          rw [Category.assoc]
  let γq₀ : (qMap U).obj qx ≅ Functor.pullbackFiber 𝒵.val.p z' i :=
    (eqToIso hobj).symm ≪≫ γ
  obtain ⟨y', β, γq, hqEq⟩ := hq U U' i hU hU' hth qx z' γq₀
  obtain ⟨x', βp, γp, hpEq⟩ := hp U U' i hU hU' hth x y' β.symm
  have hpEq' : (pCompare U U' i x').hom ≫ (pMap U).map βp.hom ≫
      β.symm.hom = Functor.pullbackFiberHom γp.hom i := by
    simpa [pCompare, pMap] using hpEq
  have hpEqCancel : (pCompare U U' i x').hom ≫
      (pMap U).map βp.hom =
      Functor.pullbackFiberHom γp.hom i ≫ β.hom := by
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ β.hom) hpEq'
  have hobjx' : (qMap U').obj ((pMap U').obj x') =
      (pUcomp U').obj x' :=
    Subtype.ext (htotal x'.1).symm
  cases hobjx'
  refine ⟨x', βp, (qMap U').mapIso γp ≪≫ γq, ?_⟩
  cases hobj
  have hqEq' : (qCompare U U' i y').hom ≫ (qMap U).map β.hom ≫ γ.hom =
      Functor.pullbackFiberHom γq.hom i := by
    have hγq₀ : γq₀.hom = γ.hom := by
      change 𝟙 ((pUcomp U).obj x) ≫ γ.hom = γ.hom
      exact Category.id_comp _
    refine (Category.assoc _ _ _).symm.trans ?_
    simpa [qCompare, qMap, hγq₀] using hqEq
  -- The square, assembled in six steps. They are chained with `Eq.trans` rather than written as
  -- a `calc`: the endpoints carry two interchangeable spellings of the category instance on
  -- `𝒵.val.obj`, and `Trans` is resolved by instance search, which does not see through them,
  -- whereas `Eq.trans` unifies them.
  have s₁ : ((compareComp U U' i x').hom ≫ (pUcomp U).map βp.hom) ≫ γ.hom =
      ((qCompare U U' i ((pMap U').obj x')).hom ≫
        (qMap U).map (pCompare U U' i x').hom) ≫
        (qMap U).map ((pMap U).map βp.hom) ≫ γ.hom := by
    rw [hcompare x', hcompMap]
    exact Category.assoc _ _ _
  have s₂ : ((qCompare U U' i ((pMap U').obj x')).hom ≫
        (qMap U).map (pCompare U U' i x').hom) ≫
        (qMap U).map ((pMap U).map βp.hom) ≫ γ.hom =
      (qCompare U U' i ((pMap U').obj x')).hom ≫
        (qMap U).map ((pCompare U U' i x').hom ≫
          (pMap U).map βp.hom) ≫ γ.hom := by
    rw [Functor.map_comp]
    exact (Category.assoc _ _ _).trans
      (congrArg (fun t => (qCompare U U' i ((pMap U').obj x')).hom ≫ t) (Category.assoc _ _ _).symm)
  have s₃ : (qCompare U U' i ((pMap U').obj x')).hom ≫
        (qMap U).map ((pCompare U U' i x').hom ≫
          (pMap U).map βp.hom) ≫ γ.hom =
      (qCompare U U' i ((pMap U').obj x')).hom ≫
        (qMap U).map (Functor.pullbackFiberHom γp.hom i) ≫
        (qMap U).map β.hom ≫ γ.hom := by
    rw [hpEqCancel, Functor.map_comp]
    exact congrArg (fun t => (qCompare U U' i ((pMap U').obj x')).hom ≫ t) (Category.assoc _ _ _)
  have s₄ : (qCompare U U' i ((pMap U').obj x')).hom ≫
        (qMap U).map (Functor.pullbackFiberHom γp.hom i) ≫
        (qMap U).map β.hom ≫ γ.hom =
      Functor.pullbackFiberHom ((qMap U').map γp.hom) i ≫
        (qCompare U U' i y').hom ≫ (qMap U).map β.hom ≫ γ.hom := by
    simpa [Category.assoc] using congrArg
      (fun f => f ≫ (qMap U).map β.hom ≫ γ.hom)
      (hqCompareNaturality γp.hom)
  have s₅ : Functor.pullbackFiberHom ((qMap U').map γp.hom) i ≫
        (qCompare U U' i y').hom ≫ (qMap U).map β.hom ≫ γ.hom =
      Functor.pullbackFiberHom ((qMap U').map γp.hom) i ≫
        Functor.pullbackFiberHom γq.hom i := by
    simpa [Category.assoc] using congrArg
      (fun f => Functor.pullbackFiberHom ((qMap U').map γp.hom) i ≫ f)
      hqEq'
  have s₆ : Functor.pullbackFiberHom ((qMap U').map γp.hom) i ≫
        Functor.pullbackFiberHom γq.hom i =
      Functor.pullbackFiberHom ((qMap U').map γp.hom ≫ γq.hom) i := by
    rw [Functor.pullbackFiberHom_comp]
  exact s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans s₆))))

/-! ### Formal smoothness of a 1-morphism representable by algebraic spaces -/

/- The equivalence below also moves between an object of a fibre built by
`CategoryTheory.Functor.Fiber.mk` and the object of the total category it was built from, and
between an isomorphism of fibres built by `CategoryTheory.Functor.Fiber.isoMk` and the morphism
underlying it. Those are again the same data under two spellings that `implicit` transparency
does not identify, so the two definitions join the unfolding chain from here on. -/
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.isoMk

/-- Conjugating a morphism by two `eqToHom` and then conjugating the result again is
conjugating by the composite equalities. Stated with the objects as variables, because the
composites it is applied to below are only type-correct after the slice definitions are
unfolded, and at that point `rw [Category.assoc]` declines to act. -/
private lemma eqToHom_conj_trans {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    {A₁ A₂ A₃ A₄ A₅ A₆ : 𝒞} (h₁ : A₁ = A₂) (h₂ : A₂ = A₃) (m : A₃ ⟶ A₄)
    (h₃ : A₄ = A₅) (h₄ : A₅ = A₆) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ m ≫ eqToHom h₃) ≫ eqToHom h₄ =
      eqToHom (h₁.trans h₂) ≫ m ≫ eqToHom (h₃.trans h₄) := by
  subst h₁ h₂ h₃ h₄
  simp

/-- The pushforward along `U.hom` of the slice object `f` is `T` when `f ≫ U.hom = T.hom`. -/
private lemma map_obj_mk_eq {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U T : BigFppfOver B S hS} {f : T.left ⟶ U.left} (h : f ≫ U.hom = T.hom) :
    (Over.map U.hom).obj (Over.mk f) = T :=
  CostructuredArrow.obj_ext _ _ rfl h.symm

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is formally smooth* when every algebraic space representing
its base change along a scheme-valued point of the target has formally smooth structural
morphism, read as a morphism of algebraic spaces over `S`. This is the notion of Stacks 03YK at
`AlgebraicGeometry.Space.formallySmoothProperty`, written out; see
`AlgebraicGeometry.BigFppfOver.isRelativelyFormallySmooth_iff_hasRelativeProperty`. -/
abbrev IsRelativelyFormallySmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor p))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.FormallySmooth
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- `AlgebraicGeometry.BigFppfOver.IsRelativelyFormallySmooth` is the relative property of
Stacks 03YK at `AlgebraicGeometry.Space.formallySmoothProperty`. Of the two hypotheses that
definition carries as instances, stability under base change is discharged by
`AlgebraicGeometry.Space.instIsStableUnderBaseChangeFormallySmoothProperty`; locality at the
target for the fppf precoverage is a hypothesis rather than a looked-up instance, because fppf
descent for formal smoothness is not in the library. -/
theorem isRelativelyFormallySmooth_iff_hasRelativeProperty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [(Space.formallySmoothProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hp : Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom) :
    IsRelativelyFormallySmooth B S hS p ↔
      Stack.HasRelativeProperty B S hS (Space.formallySmoothProperty B S hS) p hp :=
  Iff.rfl

/-- **Stacks 06D3**, that (1) implies (2): a 1-morphism of categories fibred in groupoids over
the big fppf site of `S` which is formally smooth on objects is formally smooth, that is, every
algebraic space representing a base change of it along a scheme-valued point of the target has
formally smooth structural morphism.

Representability by algebraic spaces, which the source assumes throughout, is not needed for
this implication: the lifting problem of formal smoothness is transported to a lifting problem
for objects of the 2-fibre product through whatever equivalence with the category of elements of
the representing space is supplied. -/
@[stacks 06D3 "formally smooth on objects implies formally smooth"]
theorem isRelativelyFormallySmooth_of_isFormallySmoothOnObjects
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hobj : Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p) :
    IsRelativelyFormallySmooth B S hS p := by
  have h𝒳fib : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have h𝒴fib : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  unfold Stack.IsFormallySmoothOnObjects at hobj
  intro U y hy F hF hE T T' hT hT' i hi x y' hxy
  let spIso := spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom
  let spIsoF := spIso.hom.app ⟨F, hF⟩
  let Asp := (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩
  let sx := spIsoF.app (Opposite.op T) x
  let sxPoint := sx
  have hsx : spIsoF.app (Opposite.op T) x = sx := rfl
  change ((OverShriek.relocalizePresheafFunctor U.hom).obj F).obj (Opposite.op T) at sx
  rcases sx with ⟨⟨ψ, a⟩, hψ⟩
  have hψ₀ :
      (ConcreteCategory.hom
        (((Over.map (yoneda.map U.hom)).obj
          (OverShriek.presheafFunctorToOver.obj F)).hom.app
          (Opposite.op T.left)) ⟨ψ, a⟩) = ψ ≫ U.hom := rfl
  have hψcomm : ψ ≫ U.hom = T.hom := by
    rw [hψ₀] at hψ
    simpa using hψ
  have hsec : ((spIso.app ⟨F, hF⟩).inv.app (Opposite.op T)) ⟨⟨ψ, a⟩, hψ⟩ = x := by
    have hh := congrArg (fun f => f.app (Opposite.op T))
      (Iso.hom_inv_id_app spIso ⟨F, hF⟩)
    rw [← hsx]
    exact congrArg (fun f => f x) hh
  have hpoint :
      (algebraicSpaceMap B S hS U Asp).hom.app (Opposite.op T) x =
        Over.homMk ψ hψcomm := by
    rw [← hsec]
    simpa [algebraicSpaceMap, spIsoF] using
      (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS
        U.hom ⟨F, hF⟩ (Opposite.op T) ⟨⟨ψ, a⟩, hψ⟩)
  have hbase : Over.homMk ψ hψcomm = i ≫ y' := by
    rw [hpoint] at hxy
    simpa using hxy
  let E := Classical.choice hE
  let q : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨Over.mk ψ, Discrete.mk a⟩
  let P := E.inv.functor.obj q
  have hpx : P.x = Over.mk ψ := Functor.congr_obj E.inv.w q
  have hPbase : (Over.map U.hom).obj P.x = T := by
    rw [hpx]
    exact map_obj_mk_eq hψcomm
  have hbaseP : P.base = T := P.hx.symm.trans hPbase
  let xP : 𝒳.val.p.Fiber T := Functor.Fiber.mk (P.hy.trans hbaseP)
  have hψeq : ψ = i.left ≫ y'.left := by
    simpa using congrArg (fun f : T ⟶ U => f.left) hbase
  let target : BigFppfOver B U.left.1 U.left.2 := Over.mk y'.left
  have htarget : (Over.map U.hom).obj target = T' := by
    exact map_obj_mk_eq y'.w
  have hyTarget : 𝒴.val.p.obj (y.obj target) = T' :=
    (Functor.congr_obj hy target).trans htarget
  let yT' : 𝒴.val.p.Fiber T' := Functor.Fiber.mk hyTarget
  let k₀ : Over.mk ψ ⟶ target := Over.homMk i.left hψeq.symm
  let k : P.x ⟶ target := eqToHom hpx ≫ k₀
  let Fp := CatFiberedInGroupoids.homFunctor p
  have hFpc := CatFiberedInGroupoids.homFunctor_comp_p p
  let alpha : Fp.obj P.y ⟶ y.obj target := P.iso.inv ≫ y.map k
  have hSrc : 𝒴.val.p.obj (Fp.obj P.y) = T :=
    (Functor.congr_obj hFpc P.y).trans (P.hy.trans hbaseP)
  have hPinv : 𝒴.val.p.IsHomLift (𝟙 P.base) P.iso.inv := by
    have h₁ : 𝒴.val.p.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
    simpa using IsHomLift.lift_id_inv_isIso 𝒴.val.p P.base P.iso.hom
  have hSrcP : 𝒴.val.p.obj (Fp.obj P.y) = P.base :=
    (Functor.congr_obj hFpc P.y).trans P.hy
  have hYPxP : 𝒴.val.p.obj (y.obj P.x) = P.base :=
    (Functor.congr_obj hy P.x).trans P.hx
  have hYx : 𝒴.val.p.obj (y.obj P.x) = (Over.map U.hom).obj P.x :=
    Functor.congr_obj hy P.x
  have hYtarget : 𝒴.val.p.obj (y.obj target) = (Over.map U.hom).obj target :=
    Functor.congr_obj hy target
  have hPinvMap : 𝒴.val.p.map P.iso.inv =
      eqToHom hSrcP ≫ (𝟙 P.base) ≫ eqToHom hYPxP.symm := by
    simpa using
      @IsHomLift.fac' _ _ _ _ 𝒴.val.p _ _ _ _ (𝟙 P.base) P.iso.inv hPinv
  have hykMap : 𝒴.val.p.map (y.map k) =
      eqToHom hYx ≫ (Over.map U.hom).map k ≫ eqToHom hYtarget.symm :=
    Functor.congr_hom hy k
  have hik : (Over.map U.hom).map k =
      eqToHom hPbase ≫ i ≫ eqToHom htarget.symm := by
    apply Over.OverMorphism.ext
    simp [k, k₀]
  have hAlpha : 𝒴.val.p.IsHomLift i alpha := by
    apply IsHomLift.of_fac' 𝒴.val.p i alpha hSrc hyTarget
    apply Over.OverMorphism.ext
    rw [Functor.map_comp, Over.comp_left, congrArg Over.Hom.left hPinvMap,
      congrArg Over.Hom.left hykMap, hik]
    simp
  let pU := fun V => Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p Fp hFpc V
  let cmp := fun (V V' : BigFppfOver B S hS) (j : V ⟶ V')
      (x' : 𝒳.val.p.Fiber V') =>
    Functor.fiberIsoOfCartesian (p := 𝒴.val.p)
      (z := Functor.pullbackFiber 𝒴.val.p ((pU V').obj x') j)
      (z' := (pU V).obj (Functor.pullbackFiber 𝒳.val.p x' j))
      (a := Fp.obj x'.1) j
      (Functor.IsPreFibered.pullbackMap ((pU V').obj x').2 j)
      (Fp.map (Functor.IsPreFibered.pullbackMap x'.2 j))
      (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
      (isCartesian_homFunctor_map p j (Functor.IsPreFibered.pullbackMap x'.2 j))
  let pbY := Functor.IsPreFibered.pullbackMap yT'.2 i
  have hcartAlpha : 𝒴.val.p.IsCartesian i alpha := by
    have h₂ : 𝒴.val.p.IsStronglyCartesian i alpha :=
      𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift i alpha
    infer_instance
  let gamma : (pU T).obj xP ≅ Functor.pullbackFiber 𝒴.val.p yT' i :=
    Functor.fiberIsoOfCartesian (p := 𝒴.val.p)
      (z := Functor.Fiber.mk hSrc)
      (z' := Functor.pullbackFiber 𝒴.val.p yT' i)
      (a := y.obj target) i alpha pbY hcartAlpha
      (Functor.IsPreFibered.pullbackMap.IsCartesian yT'.2 i)
  have hgammaFac : Functor.Fiber.fiberInclusion.map gamma.hom ≫ pbY = alpha :=
    Functor.fiberIsoOfCartesian_hom_fac (p := 𝒴.val.p)
      (z := Functor.Fiber.mk hSrc)
      (z' := Functor.pullbackFiber 𝒴.val.p yT' i)
      (a := y.obj target) i alpha pbY hcartAlpha
      (Functor.IsPreFibered.pullbackMap.IsCartesian yT'.2 i)
  obtain ⟨xLift, beta, gamma', hsq⟩ := hobj T T' i hT hT' hi xP yT' gamma
  let liftIso : y.obj target ≅ Fp.obj xLift.1 :=
    (Functor.Fiber.fiberInclusion.mapIso gamma').symm
  let P' : TwoFibreProductOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p y Fp :=
    { base := T'
      x := target
      y := xLift.1
      hx := htarget
      hy := xLift.2
      iso := liftIso
      vertical := gamma'.inv.2 }
  let pullX := Functor.IsPreFibered.pullbackMap xLift.2 i
  have hpullX : 𝒳.val.p.IsHomLift i pullX :=
    (Functor.IsPreFibered.pullbackMap.IsCartesian xLift.2 i).toIsHomLift
  let xArrow := Functor.Fiber.fiberInclusion.map beta.inv ≫ pullX
  have hxArrow : 𝒳.val.p.IsHomLift i xArrow := by
    simpa [xArrow] using @IsHomLift.comp _ _ _ _ 𝒳.val.p _ _ _ _ _ _ (𝟙 T) i
      (Functor.Fiber.fiberInclusion.map beta.inv) pullX beta.inv.2 hpullX
  have hcmpCart : 𝒴.val.p.IsCartesian i (Fp.map pullX) :=
    @isCartesian_homFunctor_map _ _ _ _ p _ _ _ _ i pullX hpullX
  have hcmpFac : Functor.Fiber.fiberInclusion.map (cmp T T' i xLift).hom ≫
      Fp.map pullX = Functor.IsPreFibered.pullbackMap ((pU T').obj xLift).2 i :=
    Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _
  have hsqPost :
      Functor.Fiber.fiberInclusion.map (cmp T T' i xLift).hom ≫
        Fp.map (Functor.Fiber.fiberInclusion.map beta.hom) ≫
          Functor.Fiber.fiberInclusion.map gamma.hom ≫ pbY =
      Functor.IsPreFibered.pullbackMap ((pU T').obj xLift).2 i ≫
        Functor.Fiber.fiberInclusion.map gamma'.hom := by
    have h := congrArg
      (fun f => Functor.Fiber.fiberInclusion.map f ≫ pbY) hsq
    rw [Functor.pullbackFiberHom_fac gamma'.hom i] at h
    simpa [cmp, pU, Fp, Functor.Fiber.fiberInclusion.map_comp,
      Functor.Fiber.fiberInclusion_map_mapOfComp_map] using h
  have htotal :
      Functor.Fiber.fiberInclusion.map (cmp T T' i xLift).hom ≫
        Fp.map (Functor.Fiber.fiberInclusion.map beta.hom) ≫ alpha =
      Functor.Fiber.fiberInclusion.map (cmp T T' i xLift).hom ≫
        Fp.map pullX ≫ Functor.Fiber.fiberInclusion.map gamma'.hom := by
    calc
      _ = Functor.Fiber.fiberInclusion.map (cmp T T' i xLift).hom ≫
          Fp.map (Functor.Fiber.fiberInclusion.map beta.hom) ≫
            Functor.Fiber.fiberInclusion.map gamma.hom ≫ pbY := by
              rw [← hgammaFac]
      _ = Functor.IsPreFibered.pullbackMap ((pU T').obj xLift).2 i ≫
            Functor.Fiber.fiberInclusion.map gamma'.hom := hsqPost
      _ = _ := ((Category.assoc _ _ _).symm.trans
            (congrArg (fun f => f ≫ Functor.Fiber.fiberInclusion.map gamma'.hom)
              hcmpFac)).symm
  have hcancel : Fp.map (Functor.Fiber.fiberInclusion.map beta.hom) ≫ alpha =
      Fp.map pullX ≫ Functor.Fiber.fiberInclusion.map gamma'.hom :=
    (cancel_epi (Functor.Fiber.fiberInclusion.map (cmp T T' i xLift).hom)).mp htotal
  have hpre : alpha =
      Fp.map (Functor.Fiber.fiberInclusion.map beta.inv) ≫
        Fp.map pullX ≫ Functor.Fiber.fiberInclusion.map gamma'.hom := by
    have h := congrArg
      (fun f => Fp.map (Functor.Fiber.fiberInclusion.map beta.inv) ≫ f) hcancel
    simpa [xP, Functor.map_comp] using h
  have hfactor : alpha ≫ liftIso.hom = Fp.map xArrow := by
    have hGG : Functor.Fiber.fiberInclusion.map gamma'.hom ≫ liftIso.hom =
        𝟙 (Fp.obj xLift.1) :=
      (Functor.Fiber.fiberInclusion.mapIso gamma').hom_inv_id
    have e₁ : (Fp.map pullX ≫ Functor.Fiber.fiberInclusion.map gamma'.hom) ≫
        liftIso.hom = Fp.map pullX :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun t => Fp.map pullX ≫ t) hGG).trans (Category.comp_id _))
    refine (congrArg (fun t => t ≫ liftIso.hom) hpre).trans ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => Fp.map (Functor.Fiber.fiberInclusion.map beta.inv) ≫ t)
        e₁).trans (Fp.map_comp _ _).symm)
  let φ : TwoFibreProductOver.Hom P P' :=
    { hbase := eqToHom hbaseP ≫ i
      a := k
      b := xArrow
      ha := by
        apply IsHomLift.of_fac' (Over.map U.hom) (eqToHom hbaseP ≫ i) k P.hx P'.hx
        simpa [hPbase, hbaseP, eqToHom_trans] using hik
      hb := by simpa using hxArrow
      w := by
        calc
          y.map k ≫ liftIso.hom = P.iso.hom ≫ (alpha ≫ liftIso.hom) := by
            simp [alpha, Category.assoc]
          _ = P.iso.hom ≫ Fp.map xArrow := by rw [hfactor] }
  let qLift := E.hom.functor.obj P'
  have hqbase : qLift.base = target := Functor.congr_obj E.hom.w P'
  let aLift : F.obj (Opposite.op target) :=
    F.map (eqToHom hqbase.symm).op qLift.fiber.as
  have hcompLift : target.hom ≫ U.hom = T'.hom := by
    change y'.left ≫ U.hom = T'.hom
    exact y'.w
  let sLift : ((OverShriek.relocalizePresheafFunctor U.hom).obj F).obj
      (Opposite.op T') :=
    ⟨⟨target.hom, aLift⟩, hcompLift⟩
  let z := (spIso.app ⟨F, hF⟩).inv.app (Opposite.op T') sLift
  refine ⟨z, ?_, ?_⟩
  · let q0 := E.hom.functor.obj P
    let m := E.hom.functor.map φ
    have hq0base : q0.base = P.x := Functor.congr_obj E.hom.w P
    have hmBase : eqToHom hq0base.symm ≫ m.base ≫ eqToHom hqbase = k := by
      have h := Functor.congr_hom E.hom.w φ
      have h' : m.base = eqToHom hq0base ≫ k ≫ eqToHom hqbase.symm := by
        simpa [m, φ, CategoryTheory.presheafOfCategories, BasedCategory.ofFunctor,
          Pseudofunctor.CoGrothendieck.forget, TwoFibreProductOver.fst,
          hq0base, hqbase] using h
      calc
        _ = eqToHom hq0base.symm ≫
            (eqToHom hq0base ≫ k ≫ eqToHom hqbase.symm) ≫ eqToHom hqbase := by rw [h']
        _ = k := by simp
    have hmFiber : q0.fiber.as = (F.map m.base.op) qLift.fiber.as := by
      change q0.fiber.as =
        (ConcreteCategory.hom (F.map m.base.op)) qLift.fiber.as
      exact m.fiber.eq
    let c := E.counitIso.hom.app q
    have hq0q : q0.base = q.base := hq0base.trans hpx
    have hcLift :
        (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift (𝟙 q.base) c :=
      E.isHomLift_counitIso_hom_app q
    have hcBase : c.base = eqToHom hq0q := by
      have hfac := @IsHomLift.fac' _ _ _ _
        (presheafOfCategories (F ⋙ typeToCat)).p _ _ _ _ (𝟙 q.base) c hcLift
      change c.base = eqToHom hq0q at hfac
      exact hfac
    have hcFiber : q0.fiber.as = (F.map (eqToHom hq0q).op) q.fiber.as := by
      have hf := c.fiber.eq
      change q0.fiber.as = (F.map c.base.op) q.fiber.as at hf
      simpa [hcBase] using hf
    have hfirst :
        (((OverShriek.relocalizePresheafFunctor U.hom).obj F).map i.op sLift).val.1 =
          sxPoint.val.1 := by
      change i.left ≫ target.hom = ψ
      simpa [target] using hψeq.symm
    subst ψ
    have hrestrict :
        ((OverShriek.relocalizePresheafFunctor U.hom).obj F).map i.op sLift =
          sxPoint := by
      apply Subtype.ext
      apply Sigma.ext hfirst
      let j : Over.mk (i.left ≫ target.hom) ⟶ target :=
        Over.homMk i.left (by simp [target])
      have hrelMap :
          ((OverShriek.relocalizePresheafFunctor U.hom).obj F).map i.op sLift |>.val.2 =
            F.map j.op aLift := rfl
      have hkJ : k = eqToHom hpx ≫ j := by
        apply Over.OverMorphism.ext
        rfl
      have htri :
          eqToHom hq0base.symm ≫ m.base ≫ eqToHom hqbase = eqToHom hpx ≫ j :=
        hmBase.trans hkJ
      have hfiber :
          F.map (eqToHom hq0base.symm ≫ m.base).op qLift.fiber.as =
            F.map (eqToHom hpx).op a := by
        have hm := congrArg (F.map (eqToHom hq0base.symm).op) hmFiber
        have hc := congrArg (F.map (eqToHom hq0base.symm).op) hcFiber
        calc
          F.map (eqToHom hq0base.symm ≫ m.base).op qLift.fiber.as =
              F.map (eqToHom hq0base.symm).op
                (F.map m.base.op qLift.fiber.as) :=
                  (OverShriek.map_op_comp (G := F)
                    (eqToHom hq0base.symm) m.base qLift.fiber.as).symm
          _ = F.map (eqToHom hq0base.symm).op q0.fiber.as := hm.symm
          _ = F.map (eqToHom hq0base.symm).op
                (F.map (eqToHom hq0q).op q.fiber.as) := hc
          _ = F.map (eqToHom hpx).op a := by
                have harrow :
                    eqToHom hq0base.symm ≫ eqToHom hq0q = eqToHom hpx := by
                  apply Over.OverMorphism.ext
                  simp
                rw [OverShriek.map_op_comp (G := F)
                  (eqToHom hq0base.symm) (eqToHom hq0q) q.fiber.as, harrow]
      have hinj : Function.Injective (F.map (eqToHom hpx).op) := by
        intro a₁ a₂ hh
        have hh' := congrArg (F.map (eqToHom hpx.symm).op) hh
        simpa [OverShriek.map_op_comp] using hh'
      have hdata : F.map j.op aLift = a := by
        apply hinj
        calc
          F.map (eqToHom hpx).op (F.map j.op aLift) =
              F.map (eqToHom hpx ≫ j).op aLift :=
                OverShriek.map_op_comp (G := F) (eqToHom hpx) j aLift
          _ = F.map ((eqToHom hpx ≫ j) ≫ eqToHom hqbase.symm).op
                qLift.fiber.as := by
                  dsimp only [aLift]
                  exact OverShriek.map_op_comp (G := F)
                    (eqToHom hpx ≫ j) (eqToHom hqbase.symm) qLift.fiber.as
          _ = F.map (eqToHom hq0base.symm ≫ m.base).op qLift.fiber.as := by
                have harrow :
                    (eqToHom hpx ≫ j) ≫ eqToHom hqbase.symm =
                      eqToHom hq0base.symm ≫ m.base := by
                  rw [← htri]
                  simp [Category.assoc]
                rw [harrow]
          _ = F.map (eqToHom hpx).op a := hfiber
      exact heq_of_eq (hrelMap.trans hdata)
    have hnat := NatTrans.naturality_apply
      ((spIso.app ⟨F, hF⟩).inv) i.op sLift
    have hrestrict' := hrestrict
    change ((ObjectProperty.ι
        (fun F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B U.left.1 U.left.2 F) ⋙
        OverShriek.relocalizePresheafFunctor U.hom).obj ⟨F, hF⟩).map i.op sLift =
          sxPoint at hrestrict'
    rw [hrestrict'] at hnat
    simpa [z] using hnat.symm.trans hsec
  · change ((algebraicSpaceMap B S hS U Asp).hom.app (Opposite.op T')) z = y'
    have hz := spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S
      U.left.2 hS U.hom ⟨F, hF⟩ (Opposite.op T') sLift
    change (Asp.1.hom.app (Opposite.op T'))
      ((spIso.inv.app ⟨F, hF⟩).app (Opposite.op T') sLift) = y'
    rw [hz]
    apply Over.OverMorphism.ext
    rfl

/-- **Stacks 06D3, that (2) implies (1), against a class of test objects.** Let `p` be a
1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces, and let `P` be a class of objects of the site. If every
algebraic space representing a base change of `p` along a scheme-valued point of the target has
structural morphism satisfying the lifting condition of formal smoothness for the larger test
objects in `P`, then `p` satisfies the lifting condition of formal smoothness on objects for the
larger test objects in `P`.

The lifting problem on objects over a thickening `U₀ ⟶ U₁` is turned into a lifting problem for
the algebraic space representing the base change of `p` along the object over `U₁`, over the
same thickening, so the class of larger test objects is unchanged. With `P` the class of all
objects this is
`AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjects_of_isRelativelyFormallySmooth`. -/
theorem isFormallySmoothOnObjectsOn_of_formallySmoothOn
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (P : BigFppfOver B S hS → Prop)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hp : Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom)
    (hform : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor p))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.FormallySmoothOn P
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :
    Stack.IsFormallySmoothOnObjectsOn B S hS P 𝒳 𝒴 p := by
  unfold Stack.IsFormallySmoothOnObjectsOn
  intro Fp hFp pU compare U0 U1 i0 hU0 hU1 hPU1 hth x0 y0 γ0
  have h𝒴fib : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  obtain ⟨G, hGq, ξ, hξ⟩ :=
    Stacks.RepresentableMorphism.ClassifyingFunctor.exists_classifying_functor 𝒴.val.p
      𝒴.isFiberedInGroupoids U1 y0.1 y0.2
  let K := Over.iteratedSliceBackward U1
  let y := K ⋙ G
  have hy : y ⋙ 𝒴.val.p = Over.map U1.hom := by
    dsimp [y, K]
    rw [Functor.assoc, hGq]
    exact Over.iteratedSliceBackward_forget U1
  obtain ⟨F, hF, hE⟩ := hp U1 y hy
  have hspaceSmooth := hform U1 y hy F hF hE
  let T : BigFppfOver B U1.left.1 U1.left.2 := Over.mk i0.left
  let T' : BigFppfOver B U1.left.1 U1.left.2 := Over.mk (𝟙 U1.left)
  let k : T ⟶ T' := Over.homMk i0.left
  have hbaseT : (Over.map U1.hom).obj T = U0 := by
    exact map_obj_mk_eq i0.w
  have hbaseT' : (Over.map U1.hom).obj T' = U1 := by
    exact map_obj_mk_eq (Category.id_comp _)
  have hObjT : 𝒴.val.p.obj (y.obj T) = (Over.forget U1).obj (K.obj T) :=
    Functor.congr_obj hGq (K.obj T)
  have hObjT' : 𝒴.val.p.obj (y.obj T') = (Over.forget U1).obj (K.obj T') :=
    Functor.congr_obj hGq (K.obj T')
  have hforgetObj : (Over.forget U1).obj (K.obj T) = (Over.map U1.hom).obj T := rfl
  have hforgetObj' : (Over.forget U1).obj (K.obj T') = (Over.map U1.hom).obj T' := rfl
  have hSrc : 𝒴.val.p.obj (y.obj T) = U0 := hObjT.trans (hforgetObj.trans hbaseT)
  have hSrc' : 𝒴.val.p.obj (y.obj T') = U1 := hObjT'.trans (hforgetObj'.trans hbaseT')
  have hbaseMap :
      eqToHom hbaseT.symm ≫ (Over.map U1.hom).map k ≫ eqToHom hbaseT' = i0 := by
    apply Over.OverMorphism.ext
    simp [T, T', k]
  have hmapT : (Over.map U1.hom).map k = eqToHom hbaseT ≫ i0 ≫ eqToHom hbaseT'.symm := by
    have hh := congrArg
      (fun f => eqToHom hbaseT ≫ f ≫ eqToHom hbaseT'.symm) hbaseMap
    simpa [Category.assoc] using hh
  have hforgetMap : (Over.forget U1).map (K.map k) = (Over.map U1.hom).map k := rfl
  have hmap : 𝒴.val.p.IsHomLift i0 (G.map (K.map k)) := by
    apply IsHomLift.of_fac' 𝒴.val.p i0 (G.map (K.map k)) hSrc hSrc'
    have h0 : 𝒴.val.p.map (G.map (K.map k)) =
        eqToHom hObjT ≫ (Over.map U1.hom).map k ≫ eqToHom hObjT'.symm :=
      Functor.congr_hom hGq (K.map k)
    rw [h0, hmapT]
    exact eqToHom_conj_trans hObjT hbaseT i0 hbaseT'.symm hObjT'.symm
  let alpha : y.obj T ⟶ y0.1 := G.map (K.map k) ≫ ξ.hom
  have hAlpha : 𝒴.val.p.IsHomLift i0 alpha := by
    simpa [alpha] using
      @IsHomLift.comp _ _ _ _ 𝒴.val.p _ _ _ _ _ _ i0 (𝟙 U1)
        (G.map (K.map k)) ξ.hom hmap hξ
  have hcartAlpha : 𝒴.val.p.IsCartesian i0 alpha := by
    have h₂ : 𝒴.val.p.IsStronglyCartesian i0 alpha :=
      𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift i0 alpha
    infer_instance
  let pbY := Functor.IsPreFibered.pullbackMap y0.2 i0
  let gammaClass := Functor.fiberIsoOfCartesian (p := 𝒴.val.p)
    (z := Functor.Fiber.mk hSrc)
    (z' := Functor.pullbackFiber 𝒴.val.p y0 i0) (a := y0.1) i0 alpha pbY hcartAlpha
    (Functor.IsPreFibered.pullbackMap.IsCartesian y0.2 i0)
  let gamma := gammaClass ≪≫ γ0.symm
  let P0 : TwoFibreProductOver (Over.map U1.hom) 𝒳.val.p 𝒴.val.p y Fp :=
    { base := U0
      x := T
      y := x0.1
      hx := hbaseT
      hy := x0.2
      iso := by
        change y.obj T ≅ Fp.obj x0.1
        exact Functor.Fiber.fiberInclusion.mapIso gamma
      vertical := by
        change 𝒴.val.p.IsHomLift (𝟙 U0)
          (Functor.Fiber.fiberInclusion.map gamma.hom)
        exact gamma.hom.2 }
  let E := Classical.choice hE
  let q0 := E.hom.functor.obj P0
  have hq0base : q0.base = T := by
    have hh := Functor.congr_obj E.hom.w P0
    change q0.base = P0.x at hh
    exact hh
  let a0 : F.obj (Opposite.op T) := F.map (eqToHom hq0base.symm).op q0.fiber.as
  let s0 : ((OverShriek.relocalizePresheafFunctor U1.hom).obj F).obj
      (Opposite.op U0) := ⟨⟨i0.left, a0⟩, i0.w⟩
  let spIsoF := (spacesOverSmallerBaseFunctorForgetIso B U1.left.1 S U1.left.2 hS
    U1.hom).app ⟨F, hF⟩
  let Asp := (spacesOverSmallerBaseFunctor B U1.left.1 S U1.left.2 hS U1.hom).obj ⟨F, hF⟩
  let Fsp := Asp.1.left
  let xSpace := spIsoF.inv.app (Opposite.op U0) s0
  let targetPoint : (yoneda.obj (Over.mk U1.hom)).obj (Opposite.op U1) := 𝟙 U1
  have hxy : ((algebraicSpaceMap B S hS U1 Asp).hom.app (Opposite.op U0)) xSpace =
      (yoneda.obj (Over.mk U1.hom)).map i0.op targetPoint := by
    have h := spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U1.left.1 S U1.left.2 hS
      U1.hom ⟨F, hF⟩ (Opposite.op U0) s0
    have hi : Over.homMk i0.left i0.w = i0 := by
      apply Over.OverMorphism.ext
      rfl
    rw [hi] at h
    simpa [xSpace, spIsoF, targetPoint, algebraicSpaceMap] using h
  obtain ⟨z, hz⟩ := hspaceSmooth U0 U1 hU0 hU1 hPU1 i0 hth xSpace targetPoint hxy
  let s1 := spIsoF.hom.app (Opposite.op U1) z
  have hback : (spIsoF.inv.app (Opposite.op U1)) s1 = z := by
    simp [s1]
  have hs0 : (spIsoF.hom.app (Opposite.op U0)) xSpace = s0 := by
    simp [xSpace]
  have hstruct : Over.homMk s1.1.1 s1.2 = targetPoint := by
    calc
      _ = ((algebraicSpaceMap B S hS U1 Asp).hom.app (Opposite.op U1))
            ((spIsoF.inv.app (Opposite.op U1)) s1) := by
              symm
              exact spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U1.left.1 S
                U1.left.2 hS U1.hom ⟨F, hF⟩ (Opposite.op U1) s1
      _ = ((algebraicSpaceMap B S hS U1 Asp).hom.app (Opposite.op U1)) z :=
            congrArg _ hback
      _ = targetPoint := hz.2
  have hψ : s1.1.1 = targetPoint.left := Over.OverMorphism.ext_iff.mp hstruct
  have hT'seq : Over.mk s1.1.1 = T' := by
    simpa [T', targetPoint] using congrArg (fun f => Over.mk f) hψ
  let a1 : F.obj (Opposite.op T') := hT'seq ▸ s1.1.2
  let q' : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨T', Discrete.mk a1⟩
  let P' := E.inv.functor.obj q'
  have hnat := NatTrans.naturality_apply spIsoF.hom i0.op z
  change (spIsoF.hom.app (Opposite.op U0)) (Fsp.map i0.op z) =
    ((OverShriek.relocalizePresheafFunctor U1.hom).obj F).map i0.op s1 at hnat
  have hzrestr : Fsp.map i0.op z = xSpace := hz.1
  have hrel : ((OverShriek.relocalizePresheafFunctor U1.hom).obj F).map i0.op s1 = s0 := by
    rw [← hnat, hzrestr, hs0]
  have hnormalized : s1 =
      (⟨⟨𝟙 U1.left, a1⟩, by
        change (𝟙 U1.left) ≫ U1.hom = U1.hom
        simp⟩ :
        ((OverShriek.relocalizePresheafFunctor U1.hom).obj F).obj
          (Opposite.op U1)) := by
    apply Subtype.ext
    apply Sigma.ext hψ
    exact (eqRec_heq (φ := fun V => F.obj (Opposite.op V)) hT'seq s1.1.2).symm
  have hmapnormalized :
      ((OverShriek.relocalizePresheafFunctor U1.hom).obj F).map i0.op
        (⟨⟨𝟙 U1.left, a1⟩, by
          change (𝟙 U1.left) ≫ U1.hom = U1.hom
          simp⟩) =
      (⟨⟨i0.left, F.map k.op a1⟩, i0.w⟩ :
        ((OverShriek.relocalizePresheafFunctor U1.hom).obj F).obj
          (Opposite.op U0)) :=
    Subtype.ext (OverShriek.sigmaMk_eq F a1 _ k rfl)
  have hsection : F.map k.op a1 = a0 := by
    rw [hnormalized, hmapnormalized] at hrel
    exact eq_of_heq (Sigma.ext_iff.mp (congrArg Subtype.val hrel)).2
  let m : q0 ⟶ q' :=
    { base := eqToHom hq0base ≫ k
      fiber := eqToHom (by
        apply Discrete.ext
        change q0.fiber.as = F.map (eqToHom hq0base ≫ k).op a1
        rw [← OverShriek.map_op_comp, hsection]
        dsimp only [a0]
        rw [OverShriek.map_op_comp]
        simp) }
  let proj := TwoFibreProductOver.fst (Over.map U1.hom) 𝒳.val.p 𝒴.val.p y Fp
  have hm : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift k m := by
    apply IsHomLift.of_fac' _ k m hq0base rfl
    change eqToHom hq0base ≫ k = eqToHom hq0base ≫ k ≫ eqToHom rfl
    simp
  let φ : P0 ⟶ P' := E.unitIso.hom.app P0 ≫ E.inv.functor.map m
  have hφ : proj.IsHomLift k φ := by
    have h₂ : proj.IsHomLift k (E.inv.functor.map m) :=
      Functor.isHomLift_map_of_comp_eq E.inv.w k m
    have h₃ : proj.IsHomLift (𝟙 T) (E.unitIso.hom.app P0) :=
      E.isHomLift_unitIso_hom_app P0
    simpa [φ] using @IsHomLift.comp _ _ _ _ proj _ _ _ _ _ _ (𝟙 T) k
      (E.unitIso.hom.app P0) (E.inv.functor.map m) h₃ h₂
  have hpx : P'.x = T' := Functor.congr_obj E.inv.w q'
  have hbaseP' : P'.base = U1 :=
    P'.hx.symm.trans ((congrArg (Over.map U1.hom).obj hpx).trans hbaseT')
  have hφa : φ.a = k ≫ eqToHom hpx.symm := by
    simpa [proj] using @IsHomLift.fac' _ _ _ _ proj _ _ _ _ k φ hφ
  have hφbase : φ.hbase = i0 ≫ eqToHom hbaseP'.symm := by
    rw [TwoFibreProductOver.Hom.hbase_eq, hφa, Functor.map_comp, eqToHom_map, hmapT]
    simp [P0, Category.assoc]
  have hb : 𝒳.val.p.IsHomLift i0 φ.b := by
    apply IsHomLift.of_fac' _ i0 φ.b x0.2 (P'.hy.trans hbaseP')
    calc
      _ = eqToHom P0.hy ≫ φ.hbase ≫ eqToHom P'.hy.symm :=
        @IsHomLift.fac' _ _ _ _ 𝒳.val.p _ _ _ _ φ.hbase φ.b φ.hb
      _ = _ := by rw [hφbase]; simp
  let xLift : 𝒳.val.p.Fiber U1 := Functor.Fiber.mk (P'.hy.trans hbaseP')
  let liftIso : Fp.obj P'.y ≅ y0.1 :=
    P'.iso.symm ≪≫ y.mapIso (eqToIso hpx) ≪≫ ξ
  have hliftIsoHom : liftIso.hom = P'.iso.inv ≫ y.map (eqToHom hpx) ≫ ξ.hom := rfl
  have hLiftIso : 𝒴.val.p.IsHomLift (𝟙 U1) liftIso.hom := by
    have h₁ : 𝒴.val.p.IsHomLift (𝟙 U1) P'.iso.hom :=
      Eq.mp (congrArg (fun V => 𝒴.val.p.IsHomLift (𝟙 V) P'.iso.hom) hbaseP') P'.vertical
    have h₂ : 𝒴.val.p.IsHomLift (𝟙 U1) P'.iso.inv := by
      simpa using IsHomLift.lift_id_inv_isIso 𝒴.val.p U1 P'.iso.hom
    have h₃ : 𝒴.val.p.IsHomLift (𝟙 U1) (y.map (eqToHom hpx)) := by
      apply IsHomLift.of_fac' 𝒴.val.p (𝟙 U1) (y.map (eqToHom hpx))
        ((Functor.congr_obj hy P'.x).trans (P'.hx.trans hbaseP')) hSrc'
      simp only [eqToHom_map, Category.id_comp, eqToHom_trans]
    have h₄ : 𝒴.val.p.IsHomLift (𝟙 U1) ξ.hom := hξ
    have h₅ := @IsHomLift.comp _ _ _ _ 𝒴.val.p _ _ _ _ _ _ (𝟙 U1) (𝟙 U1)
      (y.map (eqToHom hpx)) ξ.hom h₃ h₄
    have h₆ := @IsHomLift.comp _ _ _ _ 𝒴.val.p _ _ _ _ _ _ (𝟙 U1) (𝟙 U1 ≫ 𝟙 U1)
      P'.iso.inv (y.map (eqToHom hpx) ≫ ξ.hom) h₂ h₅
    rw [hliftIsoHom]
    simpa using h₆
  let γ' : (pU U1).obj xLift ≅ y0 := Functor.Fiber.isoMk liftIso hLiftIso
  have h𝒳fib : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let pullX := Functor.IsPreFibered.pullbackMap xLift.2 i0
  have hcartB : 𝒳.val.p.IsCartesian i0 φ.b := by
    have h₂ : 𝒳.val.p.IsStronglyCartesian i0 φ.b :=
      𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift i0 φ.b
    infer_instance
  let β : Functor.pullbackFiber 𝒳.val.p xLift i0 ≅ x0 :=
    Functor.fiberIsoOfCartesian i0 pullX φ.b
      (Functor.IsPreFibered.pullbackMap.IsCartesian xLift.2 i0) hcartB
  refine ⟨xLift, β, γ', ?_⟩
  apply Functor.pullbackFiberHom_uniq γ'.hom i0
  have hβ : Functor.Fiber.fiberInclusion.map β.hom ≫ φ.b = pullX :=
    Functor.fiberIsoOfCartesian_hom_fac (p := 𝒳.val.p)
      (z := Functor.pullbackFiber 𝒳.val.p xLift i0) (z' := x0)
      i0 pullX φ.b _ _
  have hcmp : Functor.Fiber.fiberInclusion.map (compare U0 U1 i0 xLift).hom ≫
      Fp.map pullX = Functor.IsPreFibered.pullbackMap ((pU U1).obj xLift).2 i0 :=
    Functor.fiberIsoOfCartesian_hom_fac i0 _ _ _ _
  have hgammaClass : Functor.Fiber.fiberInclusion.map gammaClass.hom ≫ pbY = alpha :=
    Functor.fiberIsoOfCartesian_hom_fac (p := 𝒴.val.p)
      (z := Functor.Fiber.mk hSrc) (z' := Functor.pullbackFiber 𝒴.val.p y0 i0)
      i0 alpha pbY _ _
  have hcompat : Fp.map φ.b ≫ liftIso.hom =
      Functor.Fiber.fiberInclusion.map γ0.hom ≫ pbY := by
    have hwa : y.map φ.a ≫ y.map (eqToHom hpx) = y.map k := by
      rw [← y.map_comp, hφa]
      simp
    have e₁ : P0.iso.hom ≫ Fp.map φ.b ≫ liftIso.hom =
        y.map φ.a ≫ P'.iso.hom ≫ liftIso.hom := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ liftIso.hom) φ.w.symm
    have e₂ : P'.iso.hom ≫ liftIso.hom = y.map (eqToHom hpx) ≫ ξ.hom := by
      rw [hliftIsoHom]
      simp
    have e₃ : y.map φ.a ≫ y.map (eqToHom hpx) ≫ ξ.hom = alpha :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ ξ.hom) hwa)
    have hw' : P0.iso.hom ≫ Fp.map φ.b ≫ liftIso.hom = alpha :=
      e₁.trans ((congrArg (fun t => y.map φ.a ≫ t) e₂).trans e₃)
    have hP0fac : P0.iso.hom ≫ Functor.Fiber.fiberInclusion.map γ0.hom ≫ pbY = alpha := by
      have h : P0.iso.hom ≫ Functor.Fiber.fiberInclusion.map γ0.hom =
          Functor.Fiber.fiberInclusion.map gammaClass.hom := by
        simp [P0, gamma]
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ pbY) h)).trans hgammaClass
    exact (cancel_epi P0.iso.hom).mp (hw'.trans hP0fac.symm)
  have e₄ : Fp.map (Functor.Fiber.fiberInclusion.map β.hom) ≫ Fp.map φ.b = Fp.map pullX :=
    (Fp.map_comp _ _).symm.trans (congrArg Fp.map hβ)
  have e₅ : Fp.map (Functor.Fiber.fiberInclusion.map β.hom) ≫ Fp.map φ.b ≫ liftIso.hom =
      Fp.map pullX ≫ liftIso.hom :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ liftIso.hom) e₄)
  calc
    _ = Functor.Fiber.fiberInclusion.map (compare U0 U1 i0 xLift).hom ≫
        Fp.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
        Functor.Fiber.fiberInclusion.map γ0.hom ≫ pbY := by
          simp [Functor.map_comp, Functor.Fiber.fiberInclusion_map_mapOfComp_map,
            pU, pbY, Category.assoc]
    _ = Functor.Fiber.fiberInclusion.map (compare U0 U1 i0 xLift).hom ≫
        Fp.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
        Fp.map φ.b ≫ liftIso.hom := by rw [hcompat]
    _ = Functor.Fiber.fiberInclusion.map (compare U0 U1 i0 xLift).hom ≫
        Fp.map pullX ≫ liftIso.hom :=
      congrArg (fun t => Functor.Fiber.fiberInclusion.map
        (compare U0 U1 i0 xLift).hom ≫ t) e₅
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ liftIso.hom) hcmp)

/-- **Stacks 06D3**, that (2) implies (1): a 1-morphism of categories fibred in groupoids over
the big fppf site of `S` which is representable by algebraic spaces and formally smooth is
formally smooth on objects.

Representability is used here, and twice: to produce an algebraic space representing the base
change of `p` along the scheme-valued point of `𝒴` classifying the given object, which is where
the hypothesis is applied, and through the 2-Yoneda classifying functor of Stacks 02Y4 that
turns that object into such a point. -/
@[stacks 06D3 "formally smooth implies formally smooth on objects"]
theorem isFormallySmoothOnObjects_of_isRelativelyFormallySmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hp : Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom)
    (hform : IsRelativelyFormallySmooth B S hS p) :
    Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p :=
  (Stack.isFormallySmoothOnObjectsOn_true_iff p).mp
    (isFormallySmoothOnObjectsOn_of_formallySmoothOn B S hS (fun _ => True) p hp
      (fun U y hy F hF hE => (hform U y hy F hF hE).formallySmoothOn _))

/-- **Stacks 06D3.** For a 1-morphism of categories fibred in groupoids over the big fppf site
of `S` which is representable by algebraic spaces, being formally smooth on objects and being
formally smooth — the relative property of Stacks 03YK at formal smoothness, by
`AlgebraicGeometry.BigFppfOver.isRelativelyFormallySmooth_iff_hasRelativeProperty` — are
equivalent. -/
@[stacks 06D3 "the equivalence"]
theorem isFormallySmoothOnObjects_iff_isRelativelyFormallySmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hp : Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom) :
    Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p ↔ IsRelativelyFormallySmooth B S hS p :=
  ⟨isRelativelyFormallySmooth_of_isFormallySmoothOnObjects B S hS p,
    isFormallySmoothOnObjects_of_isRelativelyFormallySmooth B S hS p hp⟩

end AlgebraicGeometry.BigFppfOver
