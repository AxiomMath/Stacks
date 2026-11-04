module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorIsAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackGerbeModel
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSmoothRegistered
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSmoothTarget

/-!
# The Picard functor is smooth in relative dimension one (Stacks 0DPK)

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, proper and of finite
presentation, with `𝒪_T ≅ f_{T,*}𝒪_{X_T}` for every scheme `T` over `B` (the standing
assumptions of Section 0DMD), and of relative dimension `≤ 1`. Then `Pic_{X/B} ⟶ B` is smooth
([Stacks, Tag 0DPK]).

`Pic_{X/B}` is a functor on the test schemes over `B`; by Stacks 0D2C
(`AlgebraicGeometry.Space.isAlgebraicSpaceOver_picardFunctor`) it is an algebraic space over `B`,
i.e. there is an algebraic space `H` with a morphism `p : H ⟶ B` whose functor of points over `B`
is identified with `Pic_{X/B}` (`AlgebraicGeometry.Space.IsAlgebraicSpaceOver`). The statement is
that `p` is smooth, and it is proved for every such `H`.

The morphism `Picardstack_{X/B} ⟶ B` is smooth (Stacks 0DPJ); the Picard stack is a gerbe over
the Picard functor (Stacks 0DME), so `Picardstack_{X/B} ⟶ Pic_{X/B}` is smooth and surjective
(Stacks 0DN8), and smoothness descends to `Pic_{X/B} ⟶ B` (Stacks 0AHD).

## The universe of the Picard stack

`Picardstack_{X/B}` (`AlgebraicGeometry.Space.picardCFG`) has its morphisms one universe above the
schemes, so it is not itself an object of `AlgebraicGeometry.Stack.AlgebraicStacks`, where
smoothness of 1-morphisms (Stacks 075U) is defined. It is algebraic (Stacks 0D04,
`AlgebraicGeometry.Space.isAlgebraicStack_picardCFG`), so its small model
(`AlgebraicGeometry.Space.picardAlgebraicStack`) is such an object, and Stacks 0DPJ is the
smoothness of the structure 1-morphism `AlgebraicGeometry.Space.picardStructureMorphism` of that
small model.

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.picardEquivPoints`: an identification of the functor
  of points of `H` with `Pic_{X/B}`, read as the model data of
  `AlgebraicGeometry.Space.PicardSituation.picardFunctorToModelFunctor`.
* `AlgebraicGeometry.Space.PicardSituation.picardToModelAlgebraicCompIso`: the gerbe
  `Picardstack_{X/B} ⟶ Pic_{X/B}` of Stacks 0DME followed by `Pic_{X/B} ⟶ B` is the structure
  1-morphism `Picardstack_{X/B} ⟶ B`, up to 2-isomorphism.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.isSmooth_of_picardFunctorModel`: a model `q : F ⟶ B`
  of `Pic_{X/B}` is smooth.
* `AlgebraicGeometry.Space.isAlgebraicSpaceOver_and_isSmooth_picardFunctor`: `Pic_{X/B}` is an
  algebraic space over `B`, and every algebraic space representing it is smooth over `B`.

## References

* [Stacks Project, Tag 0DPK](https://stacks.math.columbia.edu/tag/0DPK)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0DME](https://stacks.math.columbia.edu/tag/0DME)
* [Stacks Project, Tag 0DN8](https://stacks.math.columbia.edu/tag/0DN8)
* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0D2C](https://stacks.math.columbia.edu/tag/0D2C)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace PicardSituation

/-! ### A space representing `Pic_{X/B}` as a model of it -/

section Points

variable {s : PicardSituation B S hS} {H : AlgebraicSpaces B S hS} {p : H ⟶ s.base}
  (e : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ s.picardFunctor)

/-- The bijection between `Pic_{X/B}(T)` and the points of `H` over `T` that an identification
`e` of the functor of points of `H` over `B` with `Pic_{X/B}` gives, in the form of the model
data of `AlgebraicGeometry.Space.PicardSituation.picardFunctorToModelFunctor`. -/
def picardEquivPoints (T : s.SchemesOver) :
    s.picardFunctor.obj (op T) ≃ {x : H.1.obj (op T.left) //
      p.hom.app (op T.left) x =
        yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom)} where
  toFun ξ := (e.inv.app (op T) ξ).down
  invFun x := e.hom.app (op T) (ULift.up x)
  left_inv ξ := (e.app (op T)).inv_hom_id_apply ξ
  right_inv x := by
    have h := (e.app (op T)).hom_inv_id_apply
      (show (spacePointsOver p ⋙ uliftFunctor.{u + 1, u}).obj (op T) from ULift.up x)
    exact congrArg ULift.down h

/-- The bijection `AlgebraicGeometry.Space.PicardSituation.picardEquivPoints` is natural in the
test scheme. -/
theorem picardEquivPoints_map (T U : s.SchemesOver) (g : T ⟶ U)
    (ξ : s.picardFunctor.obj (op U)) :
    (picardEquivPoints e T (s.picardFunctor.map g.op ξ)).val =
      H.1.map g.left.op (picardEquivPoints e U ξ).val := by
  show (e.inv.app (op T) (s.picardFunctor.map g.op ξ)).down.1 = _
  rw [NatTrans.naturality_apply]
  rfl

end Points

/-! ### The gerbe followed by the model is the structure 1-morphism -/

section Model

attribute [local instance] picardObjectCategory

variable (D : CoherentSituation B S hS) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : F ⟶ D.Y.1)
  (e : ∀ T : D.toPicardSituation.SchemesOver, D.toPicardSituation.picardFunctor.obj (op T) ≃
    {x : F.obj (op T.left) //
      q.app (op T.left) x = yonedaEquiv (show yoneda.obj T.left ⟶ D.Y.1 from T.hom.hom)})
  (he : ∀ (T U : D.toPicardSituation.SchemesOver) (g : T ⟶ U)
    (x : D.toPicardSituation.picardFunctor.obj (op U)),
    (e T (D.toPicardSituation.picardFunctor.map g.op x)).val = F.map g.left.op (e U x).val)
  (hF : IsAlgebraicSpace B S hS F)

/-- **The gerbe `Picardstack_{X/B} ⟶ F` followed by `q : F ⟶ B` is the structure 1-morphism
`Picardstack_{X/B} ⟶ B`**, up to 2-isomorphism: both send an object `(T, L)` of the Picard stack
to the section of `B` over the scheme underlying `T` that `T` is, since the point of the model
named by the class of `L` lies over that section. -/
def picardToModelAlgebraicCompIso
    (h : Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val) :
    D.toPicardSituation.picardToModelAlgebraic F q e he h hF ≫
        Stack.algebraicSpaceStackMap.{u, w} B S hS hF D.Y.2 q ≅
      picardStructureMorphism D h :=
  letI : LocallySmall.{u}
      (picardBasedCategory (modulePushforwardCoherence B S hS) D.toPicardSituation).obj :=
    Stack.locallySmall_of_isAlgebraicStack B S hS h
  Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso
      (NatIso.ofComponents (fun z =>
        ⟨⟨𝟙 _, Discrete.eqToHom (by
            let A := D.toPicardSituation.toPicardFunctorBased.obj
              ((ShrinkHoms.inverse.{u} (picardBasedCategory
                (modulePushforwardCoherence B S hS) D.toPicardSituation).obj).obj z)
            change q.app (op A.base.left) (e A.base A.fiber.as).val =
              D.Y.1.map (𝟙 A.base.left).op (testPoint A.base)
            rw [(e A.base A.fiber.as).property]
            simp
            rfl)⟩,
          ⟨𝟙 _, Discrete.eqToHom (by
            let A := D.toPicardSituation.toPicardFunctorBased.obj
              ((ShrinkHoms.inverse.{u} (picardBasedCategory
                (modulePushforwardCoherence B S hS) D.toPicardSituation).obj).obj z)
            change testPoint A.base =
              D.Y.1.map (𝟙 A.base.left).op (q.app (op A.base.left) (e A.base A.fiber.as).val)
            rw [(e A.base A.fiber.as).property]
            simp
            rfl)⟩,
          Pseudofunctor.CoGrothendieck.Hom.ext _ _ (Category.id_comp _)
            (by apply Discrete.hom_eq),
          Pseudofunctor.CoGrothendieck.Hom.ext _ _ (Category.id_comp _)
            (by apply Discrete.hom_eq)⟩)
        (fun g => Pseudofunctor.CoGrothendieck.Hom.ext _ _
          ((Category.comp_id _).trans (Category.id_comp _).symm) (by apply Discrete.hom_eq)))
      (fun z => IsHomLift.of_fac' _ _ _
        (Functor.congr_obj (D.toPicardSituation.picardToModelAlgebraic F q e he h hF ≫
          Stack.algebraicSpaceStackMap.{u, w} B S hS hF D.Y.2 q).hom.hom.w z)
        (Functor.congr_obj (picardStructureMorphism D h).hom.hom.w z)
        (by
          simp only [Bicategory.InducedBicategory.categoryStruct_comp_hom,
            Bicategory.InducedBicategory.bicategory_Hom, Lean.Elab.WF.paramLet,
            BasedCategory.comp_def, NatIso.ofComponents_hom_app, BasedFunctor.w_obj,
            eqToHom_naturality, Category.comp_id, eqToHom_trans]
          exact (eqToHom_refl _ _).symm))))

include e he hF in
/-- **A model of `Pic_{X/B}` is smooth over `B` in relative dimension `≤ 1`.** Let `f : X ⟶ B`
be flat, proper, of finite presentation and of relative dimension `≤ 1`, and let `q : F ⟶ B` be a
morphism from an algebraic space whose fibres are identified with `Pic_{X/B}`, naturally in the
test scheme. Then `q` is smooth. -/
theorem isSmooth_of_picardFunctorModel (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) (hd : HasRelativeDimensionLE 1 B S hS D.f.hom) :
    IsSmooth B S hS q :=
  let h := isAlgebraicStack_picardCFG.{u, u} D hflat hproper
  Stack.AlgebraicStacks.isSmooth_of_isGerbeOver_of_twoIso.{u, u} B S hS hF D.Y.2
    (D.toPicardSituation.picardToModelAlgebraic F q e he h hF)
    (D.toPicardSituation.isGerbeOver_picardToModelAlgebraic F q e he h hF)
    (picardStructureMorphism D h) (isSmooth_picardStructureMorphism.{u, u} D hflat hproper hd) q
    (picardToModelAlgebraicCompIso D F q e he hF h)

end Model

end PicardSituation

/-! ### The Picard functor is smooth -/

/-- **The Picard functor is smooth in relative dimension `≤ 1`.** Let `f : X ⟶ Y` be a morphism
of algebraic spaces over `S` which is flat, of finite presentation and proper, with
`𝒪_T ⟶ f_{T,*}𝒪_{X_T}` an isomorphism for every scheme `T` over `Y` (the standing assumptions of
Section 0DMD), and of relative dimension `≤ 1`. Then `Pic_{X/Y}` is an algebraic space over `Y`
(Stacks 0D2C) and `Pic_{X/Y} ⟶ Y` is smooth: every algebraic space `H` with a morphism
`p : H ⟶ Y` whose functor of points over `Y` is identified with `Pic_{X/Y}` has `p` smooth. -/
@[stacks 0DPK "the full statement, in the setting of Section 0DMD: f flat (hflat), of finite \
presentation (hfp), proper (hproper), O_T -> f_{T,*}O_{X_T} an isomorphism for every T (hstr), \
of relative dimension ≤ 1 (hd); the conclusion contains that Pic_{X/B} is an algebraic space over \
B (Stacks 0D2C) and that its morphism to B is smooth, for every algebraic space representing it"]
theorem isAlgebraicSpaceOver_and_isSmooth_picardFunctor {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hproper : IsProper B S hS f.hom)
    (hstr : (PicardSituation.mk X Y f).StructureSheafMapIso)
    (hd : HasRelativeDimensionLE 1 B S hS f.hom) :
    IsAlgebraicSpaceOver (PicardSituation.mk X Y f).picardFunctor ∧
      ∀ (H : AlgebraicSpaces B S hS) (p : H ⟶ Y),
        Nonempty (spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅
          (PicardSituation.mk X Y f).picardFunctor) →
        IsSmooth B S hS p.hom := by
  refine ⟨isAlgebraicSpaceOver_picardFunctor f hflat hfp hproper hstr, fun H p ⟨e⟩ => ?_⟩
  let D : CoherentSituation B S hS := ⟨X, Y, f, hfp⟩
  exact PicardSituation.isSmooth_of_picardFunctorModel D H.1 p.hom
    (PicardSituation.picardEquivPoints (s := D.toPicardSituation) e)
    (PicardSituation.picardEquivPoints_map (s := D.toPicardSituation) e) H.2 hflat hproper hd

end AlgebraicGeometry.Space

end
