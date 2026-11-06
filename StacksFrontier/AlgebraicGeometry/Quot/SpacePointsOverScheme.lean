module

public import StacksFrontier.AlgebraicGeometry.Spaces.OverSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBaseInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize

/-!
# An algebraic space over a scheme, read on the big fppf site of the scheme

Let `U` be a scheme of the big fppf site of `S` and `p : H ⟶ U` a morphism of algebraic spaces
over `S`. The functor of points of `H` over `U` on the test schemes over `U`
(`AlgebraicGeometry.Space.spacePointsOver`), restricted to the schemes over `U`, is a presheaf on
the big fppf site `(Sch/U)_fppf` of `U`: its sections over `V ⟶ U` are the sections of `H` over
`V` lying over `V ⟶ U`. This is the algebraic space over `U` that Stacks 04SG attaches to
`(H, p)`, written on sections: its lower-shriek extension to `S` is `H` itself, with structure
morphism `p` (`AlgebraicGeometry.Space.overSchemePointsRelocalizeIso`).

Consequently it is an algebraic space over `U`, and a property of morphisms of algebraic spaces
over `S` respecting isomorphisms holds for its structure morphism, read over `S` (Stacks 04SG),
exactly when it holds for `p`. This is how a representability statement of the `Quot` chapter,
which describes a functor on the test schemes over `U` by an algebraic space over `S` with a
morphism to `U`, is read in the form of Properties of Stacks, Section 04XB, where the algebraic
space lives on `(Sch/U)_fppf`.

## Main definitions

* `AlgebraicGeometry.Space.overSchemePoints`: the presheaf on `(Sch/U)_fppf` of points of `H`
  over `U`.
* `AlgebraicGeometry.Space.overSchemePointsRelocalizeIso`: its lower-shriek extension to `S` is
  `H`.

## Main results

* `AlgebraicGeometry.Space.overSchemePointsRelocalizeIso_hom_comp`: that identification is one
  over `U`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_overSchemePoints`: the presheaf is an algebraic
  space over `U`.
* `AlgebraicGeometry.Space.prop_algebraicSpaceMap_overSchemePoints`: its structure morphism, read
  over `S`, has every property of `p` that respects isomorphisms.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {H : AlgebraicSpaces B S hS}
  (p : H ⟶ (schemeSpaceFunctor B S hS).obj U)

/-- **The points of `H` over the scheme `U`, on the big fppf site of `U`.** For a morphism
`p : H ⟶ U` of algebraic spaces over `S`, the sections over `V ⟶ U` are the sections of `H` over
`V` (viewed over `S`) lying over `V ⟶ U`: the functor of points of `H` over `U` on the test
schemes over `U`, restricted to the schemes over `U`. -/
abbrev overSchemePoints : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u :=
  (Over.iteratedSliceBackward U).op ⋙ (overSchemeTest U).op ⋙ spacePointsOver p

/-- A section of `H` over `T` lies over the morphism `T ⟶ U` that `p` attaches to it, read as a
section of `H` over `T →ψ U` for `ψ` the underlying morphism of schemes. -/
theorem overSchemePoints_restrict_mem (T : (BigFppfOver B S hS)ᵒᵖ) (t : H.1.obj T) :
    p.hom.app _ (H.1.map (smallerBaseFactorHomInv B U.left.1 S U.left.2 hS U.hom
        (Over.w (p.hom.app T t))).op t) =
      testPoint ((overSchemeTest U).obj
        ((Over.iteratedSliceBackward U).obj (Over.mk (p.hom.app T t).left))) := by
  refine (NatTrans.naturality_apply p.hom _ t).trans ?_
  refine Eq.trans ?_ (yonedaEquiv_yoneda_map _).symm
  exact Over.OverMorphism.ext (Category.id_comp _)

/-- The sections over `T` of the lower-shriek extension to `S` of the points of `H` over `U` are
the sections of `H` over `T`. A section of the extension is a factorization `ψ : T ⟶ U` of the
structure morphism of `T` with a section of `H` over `T →ψ U` lying over `ψ`; it goes to that
section, restricted along the identity of `T`. -/
def overSchemePointsRelocalizeEquiv (T : (BigFppfOver B S hS)ᵒᵖ) :
    ((OverShriek.relocalizePresheafFunctor U.hom).obj (overSchemePoints p)).obj T ≃ H.1.obj T where
  toFun y := H.1.map (smallerBaseFactorHom B U.left.1 S U.left.2 hS U.hom
    (OverShriek.relocalizeFactors U.hom _ y)).op y.1.2.1
  invFun t := OverShriek.relocalizeMk U.hom (overSchemePoints p) (p.hom.app T t).left
    ⟨H.1.map (smallerBaseFactorHomInv B U.left.1 S U.left.2 hS U.hom
      (Over.w (p.hom.app T t))).op t, overSchemePoints_restrict_mem p T t⟩
    (Over.w (p.hom.app T t))
  left_inv := by
    rintro ⟨⟨ψ, s⟩, hψ⟩
    have hψ0 : ψ ≫ U.hom = T.unop.hom := hψ
    let fh := smallerBaseFactorHom B U.left.1 S U.left.2 hS U.hom hψ0
    have h1 : p.hom.app T (H.1.map fh.op s.1) = fh ≫ p.hom.app _ s.1 :=
      NatTrans.naturality_apply p.hom fh.op s.1
    have h2 : (p.hom.app _ s.1).left = ψ :=
      (congrArg Over.Hom.left s.2).trans (congrArg Over.Hom.left (yonedaEquiv_yoneda_map _))
    have hψ' : (p.hom.app T (H.1.map fh.op s.1)).left = ψ :=
      (congrArg Over.Hom.left h1).trans
        ((congrArg (fun k => 𝟙 _ ≫ k) h2).trans (Category.id_comp ψ))
    let e : (Over.mk (p.hom.app T (H.1.map fh.op s.1)).left : Over U.left) ⟶ Over.mk ψ :=
      Over.homMk (𝟙 _) ((Category.id_comp ψ).trans hψ'.symm)
    apply Subtype.ext
    refine Eq.trans ?_ (OverShriek.sigmaMk_eq_self _ s e rfl)
    refine congrArg (Sigma.mk _) (Subtype.ext ?_)
    refine (Functor.map_comp_apply H.1 fh.op _ s.1).symm.trans
      (congrArg (fun k => H.1.map k s.1) (Quiver.Hom.unop_inj (Over.OverMorphism.ext ?_)))
    rfl
  right_inv := by
    intro t
    refine (Functor.map_comp_apply H.1
      (smallerBaseFactorHomInv B U.left.1 S U.left.2 hS U.hom (Over.w (p.hom.app T t))).op _
        t).symm.trans ?_
    have : smallerBaseFactorHom B U.left.1 S U.left.2 hS U.hom (Over.w (p.hom.app T t)) ≫
        smallerBaseFactorHomInv B U.left.1 S U.left.2 hS U.hom (Over.w (p.hom.app T t)) = 𝟙 _ :=
      Over.OverMorphism.ext (by simp [smallerBaseFactorHom, smallerBaseFactorHomInv])
    have hop : (smallerBaseFactorHomInv B U.left.1 S U.left.2 hS U.hom
        (Over.w (p.hom.app T t))).op ≫
        (smallerBaseFactorHom B U.left.1 S U.left.2 hS U.hom (Over.w (p.hom.app T t))).op =
          𝟙 _ := by
      rw [← op_comp, this, op_id]
    exact (congrArg (fun k => H.1.map k t) hop).trans (Functor.map_id_apply _ _ _)

/-- **The lower-shriek extension to `S` of the points of `H` over `U` is `H`**, through the
bijections `AlgebraicGeometry.Space.overSchemePointsRelocalizeEquiv`. -/
def overSchemePointsRelocalizeIso :
    (OverShriek.relocalizePresheafFunctor U.hom).obj (overSchemePoints p) ≅ H.1 :=
  NatIso.ofComponents (fun T => (overSchemePointsRelocalizeEquiv p T).toIso)
    (by
      intro T T' f
      ext ⟨⟨ψ, s⟩, hψ⟩
      refine (Functor.map_comp_apply H.1 _ _ s.1).symm.trans
        (Eq.trans ?_ (Functor.map_comp_apply H.1 _ f s.1))
      refine congrArg (fun k => H.1.map k s.1) (Quiver.Hom.unop_inj ?_)
      refine Over.OverMorphism.ext ?_
      change 𝟙 _ ≫ f.unop.left = f.unop.left ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])

/-- **The identification of the lower-shriek extension with `H` is one over `U`**: followed by
`p`, it is the structure morphism of the extension, which reads off the factorization through
`U` that a section carries. -/
theorem overSchemePointsRelocalizeIso_hom_comp :
    (overSchemePointsRelocalizeIso p).hom ≫ p.hom =
      OverShriek.relocalizeToYoneda U.hom (overSchemePoints p) := by
  ext T ⟨⟨ψ, s⟩, hψ⟩
  have hψ0 : ψ ≫ U.hom = T.unop.hom := hψ
  let fh := smallerBaseFactorHom B U.left.1 S U.left.2 hS U.hom hψ0
  have h1 : p.hom.app T (H.1.map fh.op s.1) = fh ≫ p.hom.app _ s.1 :=
    NatTrans.naturality_apply p.hom fh.op s.1
  have h2 : (p.hom.app _ s.1).left = ψ :=
    (congrArg Over.Hom.left s.2).trans (congrArg Over.Hom.left (yonedaEquiv_yoneda_map _))
  exact h1.trans (Over.OverMorphism.ext
    ((congrArg (fun k => 𝟙 _ ≫ k) h2).trans (Category.id_comp ψ)))

/-- **The points of `H` over `U` form an algebraic space over `U`** (Stacks 04SG): their
lower-shriek extension to `S` is the algebraic space `H`. -/
theorem isAlgebraicSpace_overSchemePoints :
    IsAlgebraicSpace B U.left.1 U.left.2 (overSchemePoints p) :=
  (isAlgebraicSpace_viewOver_iff B U.left.1 S U.left.2 hS U.hom _).1
    (isAlgebraicSpace_of_iso B S hS (overSchemePointsRelocalizeIso p).symm H.2)

/-- **The structure morphism of the points of `H` over `U` is `p`.** For a property `P` of
morphisms of algebraic spaces over `S` respecting isomorphisms, the structure morphism of the
algebraic space `AlgebraicGeometry.Space.overSchemePoints p` over `U`, read over `S` (Stacks
04SG), has `P` as soon as `p` has: the two are isomorphic as arrows over `U`. -/
theorem prop_algebraicSpaceMap_overSchemePoints
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso] (hp : P p) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
        ⟨overSchemePoints p, isAlgebraicSpace_overSchemePoints p⟩)) := by
  refine (Stack.prop_algebraicSpaceMap_iff B S hS P U _ _).2 ?_
  let i : (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj (overSchemePoints p),
      isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom _
        (isAlgebraicSpace_overSchemePoints p)⟩ : AlgebraicSpaces B S hS) ≅ H :=
    ObjectProperty.isoMk _ (overSchemePointsRelocalizeIso p)
  have hw : i.hom ≫ p = ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom
      (overSchemePoints p)) :=
    ObjectProperty.hom_ext _ (overSchemePointsRelocalizeIso_hom_comp p)
  have key := (P.cancel_left_of_respectsIso i.hom p).2 hp
  rwa [hw] at key

end AlgebraicGeometry.Space

end
