module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictProduct

/-!
# Restricting to a smaller base versus multiplying by its representable presheaf

Let `f : S ⟶ S'` be a morphism of a big fppf site and let `F'` be a presheaf on the big fppf site
of `S'`. Restricting `F'` along `CategoryTheory.Over.map f` gives an algebraic space over `S`
exactly when the product of `F'` with the representable presheaf of the object `S →f S'` is an
algebraic space over `S'`.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_restrict_iff_product`: **Stacks 04SH**, the equivalence
  between the two algebraic-space conditions.

## Implementation notes

Both directions go through
`CategoryTheory.OverShriek.relocalizeRestrictIsoProduct`, which identifies the relocalization of
the restriction of `F'` with the product `h_{(S ⟶ S')} ⨯ F'`. Forwards, the relocalization of an
algebraic space is an algebraic space (Stacks 03I5 part (2)). Backwards, the restriction of `F'`
is exhibited as a presheaf fibre product: restricting is a base change of the product along the
tautological section of the representable presheaf of `S ⟶ S'`, so Stacks 03I5 part (1) and the
algebraicity of fibre products (Stacks 02X2) apply.

The source assumes that `F'` is an fppf sheaf. That hypothesis is not needed: the sheaf condition
on the two presheaves appearing in the statement is part of being an algebraic space on either
side, and the fibre-product argument uses nothing else.

## References

* [Stacks Project, Tag 04SH](https://stacks.math.columbia.edu/tag/04SH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **Stacks 04SH.** The restriction of a presheaf `F'` on the big fppf site of `S'` to the big
fppf site of `S` along `f : S ⟶ S'` is an algebraic space over `S` exactly when the product of
`F'` with the representable presheaf of the object `S →f S'` is an algebraic space over `S'`. -/
@[stacks 04SH]
theorem isAlgebraicSpace_restrict_iff_product
    (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
    (f : B.obj hS ⟶ B.obj hS') (F' : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) :
    IsAlgebraicSpace B S hS ((OverShriek.relocalizeRestrict f).obj F') ↔
      IsAlgebraicSpace B S' hS' (yoneda.obj (Over.mk f) ⨯ F') := by
  constructor
  · intro h
    exact isAlgebraicSpace_of_iso B S' hS'
      (OverShriek.relocalizeRestrictIsoProduct f F').symm
      (isAlgebraicSpace_viewOver B S S' hS hS' f _ h)
  · intro hP
    classical
    let R := (Over.map f).op
    let H := yoneda.obj (Over.mk f)
    let P := FunctorToTypes.prod H F'
    let RP := R ⋙ P
    let RH := R ⋙ H
    let RF := R ⋙ F'
    let K := yoneda.obj (Over.mk (𝟙 (B.obj hS)))
    let p : RP ⟶ RH :=
      { app W := ↾fun x => x.1
        naturality := by
          intro W W' g
          ext x
          rfl }
    let δ : K ⟶ RH :=
      { app W := ↾fun γ => Over.homMk γ.left (by
          show γ.left ≫ f = W.unop.hom ≫ f
          exact congrArg (· ≫ f) (Over.w γ))
        naturality := by
          intro W W' g
          ext γ
          exact Over.OverMorphism.ext rfl }
    let αW (W : (BigFppfOver B S hS)ᵒᵖ) : K.obj W := Over.homMk W.unop.hom rfl
    let αBase (W : (BigFppfOver B S hS)ᵒᵖ) : RH.obj W := δ.app W (αW W)
    let isoPullback : pullback p δ ≅ RF := by
      let compIso (W : (BigFppfOver B S hS)ᵒᵖ) :
          (pullback p δ).obj W ≅ Types.PullbackObj (p.app W) (δ.app W) :=
        pullbackObjIso p δ W ≪≫ Types.pullbackIsoPullback (p.app W) (δ.app W)
      let fiberEquiv (W : (BigFppfOver B S hS)ᵒᵖ) :
          Types.PullbackObj (p.app W) (δ.app W) ≃ RF.obj W :=
        Equiv.mk (fun z => z.1.1.2)
          (fun s =>
            let x : RP.obj W := by
              show H.obj (R.obj W) × F'.obj (R.obj W)
              exact (αBase W, s)
            ⟨(x, αW W), by
              show x.1 = δ.app W (αW W)
              rfl⟩)
          (by
            intro z
            apply Subtype.ext
            have hγ : z.1.2 = αW W :=
              Over.OverMorphism.ext (by simpa using Over.w z.1.2 : z.1.2.left = W.unop.hom)
            have hα : z.1.1.1 = αBase W := z.2.trans (congrArg (δ.app W) hγ)
            exact Prod.ext (Prod.ext hα.symm rfl) hγ.symm)
          fun _ => rfl
      refine NatIso.ofComponents (fun W => compIso W ≪≫ (fiberEquiv W).toIso) ?_
      intro W W' g
      ext s
      dsimp [compIso, fiberEquiv, RF, R]
      change
        ((Types.pullbackIsoPullback (p.app W') (δ.app W')).hom
          ((pullbackObjIso p δ W').hom ((pullback p δ).map g s))).1.1.2 =
        F'.map ((Over.map f).map g.unop).op
          ((Types.pullbackIsoPullback (p.app W) (δ.app W)).hom
            ((pullbackObjIso p δ W).hom s)).1.1.2
      have hproj (V : (BigFppfOver B S hS)ᵒᵖ) (t : (pullback p δ).obj V) :
          ((Types.pullbackIsoPullback (p.app V) (δ.app V)).hom
            ((pullbackObjIso p δ V).hom t)).1.1.2 = ((pullback.fst p δ).app V t).2 := by
        have h₁ := congrArg Prod.snd
          (Types.pullbackIsoPullback_hom_fst (p.app V) (δ.app V)
            ((pullbackObjIso p δ V).hom t))
        have h₂ := congrArg (fun z : RP.obj V => z.2)
          (congrArg (fun k => k t) (pullbackObjIso_hom_comp_fst p δ V))
        simpa using h₁.trans h₂
      rw [hproj W' ((pullback p δ).map g s), hproj W s]
      exact congrArg (fun x : RP.obj W' => x.2) (NatTrans.naturality_apply (pullback.fst p δ) g s)
    have hRP : IsAlgebraicSpace B S hS RP :=
      isAlgebraicSpace_relocalizeRestrict B S S' hS hS' f P
        (isAlgebraicSpace_of_iso B S' hS' (FunctorToTypes.binaryProductIso H F').symm hP)
    have hRH : IsAlgebraicSpace B S hS RH :=
      isAlgebraicSpace_relocalizeRestrict B S S' hS hS' f H
        (isAlgebraicSpace_yoneda B S' hS' (Over.mk f))
    have hK : IsAlgebraicSpace B S hS K :=
      isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))
    exact isAlgebraicSpace_of_iso B S hS isoPullback.symm
      (isAlgebraicSpace_pullback B S hS p δ hRP hK hRH)

end AlgebraicGeometry

end
