module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImage

/-!
# Evaluating `f_{cris, *}` at an object over a given object

For a morphism of global crystalline situations `f : X/S ⟶ X'/S'` (source `S`, target `S'`) and
an abelian sheaf `G` on `Cris(X/S)`, the sections of `f_{cris, *}G` over an object `A'` of
`Cris(X'/S')` are a limit over the objects of `Cris(X/S)` lying over `A'`
(`...SmallSite.crisDirectImageObjObjIsoLimit`).  This file names the projection of that limit at
one index: for an object `A` of `Cris(X/S)` and a morphism `τ : f(A) ⟶ A'` in `CRIS(X'/S')` from
the image of `A` under change of divided power base, the map

`crisDirectImageEval τ G : (f_{cris, *}G)(A') ⟶ G(A)`.

It is natural in `G` (`crisDirectImageEval_naturality`) and compatible with the restriction maps
of `f_{cris, *}G` and of `G` (`crisDirectImageEval_comp`).

## References

* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- **The value of `f_{cris, *}G` at `A'` projected to the value of `G` at an object `A` over
`A'`**: the index `(A, τ)` of the limit computing `(f_{cris, *}G)(A')`, where
`τ : f(A) ⟶ A'` is a morphism of `CRIS(X'/S')` out of the image of `A` under change of divided
power base.  It is the counit of the outer right Kan extension at `τ`, followed by the counit of
the inner one at `A`. -/
def crisDirectImageEval {A : CrystallineThickening S} {A' : CrystallineThickening S'}
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A) ⟶
      (CrystallineThickening.ι S').obj A')
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((crisDirectImage S S' fS fX hf).obj G).obj.obj (op A') ⟶ G.obj.obj (op A) :=
  ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map τ.op ≫
    ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj G).obj).app
      (op ((CrystallineThickening.ι S).obj A)) ≫
    ((CrystallineThickening.ι S).op.ranCounit.app G.obj).app (op A)

/-- **`crisDirectImageEval` is natural in the sheaf.** -/
@[reassoc]
theorem crisDirectImageEval_naturality {A : CrystallineThickening S}
    {A' : CrystallineThickening S'}
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A) ⟶
      (CrystallineThickening.ι S').obj A')
    {G H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (φ : G ⟶ H) :
    ((crisDirectImage S S' fS fX hf).map φ).hom.app (op A') ≫
        crisDirectImageEval S S' fS fX hf τ H =
      crisDirectImageEval S S' fS fX hf τ G ≫ φ.hom.app (op A) := by
  have h1 : ((changeBase S S' fS fX hf).op.ran.map ((bigDirectImage S).map φ).hom).app
        (op ((CrystallineThickening.ι S').obj A')) ≫
        ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj H).obj).map τ.op =
      ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map τ.op ≫
        ((changeBase S S' fS fX hf).op.ran.map ((bigDirectImage S).map φ).hom).app
          (op ((changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A))) :=
    (((changeBase S S' fS fX hf).op.ran.map ((bigDirectImage S).map φ).hom).naturality
      τ.op).symm
  have h2 : ((changeBase S S' fS fX hf).op.ran.map ((bigDirectImage S).map φ).hom).app
        (op ((changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A))) ≫
        ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj H).obj).app
          (op ((CrystallineThickening.ι S).obj A)) =
      ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj G).obj).app
          (op ((CrystallineThickening.ι S).obj A)) ≫
        ((bigDirectImage S).map φ).hom.app (op ((CrystallineThickening.ι S).obj A)) :=
    congrArg (fun k => NatTrans.app k (op ((CrystallineThickening.ι S).obj A)))
      ((changeBase S S' fS fX hf).op.ranCounit.naturality ((bigDirectImage S).map φ).hom)
  have h3 : ((bigDirectImage S).map φ).hom.app (op ((CrystallineThickening.ι S).obj A)) ≫
        ((CrystallineThickening.ι S).op.ranCounit.app H.obj).app (op A) =
      ((CrystallineThickening.ι S).op.ranCounit.app G.obj).app (op A) ≫ φ.hom.app (op A) :=
    congrArg (fun k => NatTrans.app k (op A))
      ((CrystallineThickening.ι S).op.ranCounit.naturality φ.hom)
  change ((changeBase S S' fS fX hf).op.ran.map ((bigDirectImage S).map φ).hom).app
      (op ((CrystallineThickening.ι S').obj A')) ≫
      ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj H).obj).map τ.op ≫
      ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj H).obj).app
        (op ((CrystallineThickening.ι S).obj A)) ≫
      ((CrystallineThickening.ι S).op.ranCounit.app H.obj).app (op A) =
    (((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map τ.op ≫
      ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj G).obj).app
        (op ((CrystallineThickening.ι S).obj A)) ≫
      ((CrystallineThickening.ι S).op.ranCounit.app G.obj).app (op A)) ≫ φ.hom.app (op A)
  refine ((reassoc_of% h1) _).trans ((congrArg (fun k => _ ≫ k) ((reassoc_of% h2) _)).trans ?_)
  exact (congrArg (fun k => _ ≫ _ ≫ k) h3).trans
    (congrArg (fun k => _ ≫ k) (Category.assoc _ _ _).symm)

/-- **`crisDirectImageEval` is compatible with restriction.**  For morphisms `g : A₁ ⟶ A₂` of
`Cris(X/S)` and `g' : A'₁ ⟶ A'₂` of `Cris(X'/S')` and indices `τ₁, τ₂` with
`f(g) ≫ τ₂ = τ₁ ≫ g'`, restricting along `g'` and then evaluating at `τ₁` is evaluating at `τ₂`
and then restricting along `g`. -/
theorem crisDirectImageEval_comp {A₁ A₂ : CrystallineThickening S}
    {A'₁ A'₂ : CrystallineThickening S'} (g : A₁ ⟶ A₂) (g' : A'₁ ⟶ A'₂)
    (τ₁ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A₁) ⟶
      (CrystallineThickening.ι S').obj A'₁)
    (τ₂ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A₂) ⟶
      (CrystallineThickening.ι S').obj A'₂)
    (hτ : (changeBase S S' fS fX hf).map ((CrystallineThickening.ι S).map g) ≫ τ₂ =
      τ₁ ≫ (CrystallineThickening.ι S').map g')
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((crisDirectImage S S' fS fX hf).obj G).obj.map g'.op ≫
        crisDirectImageEval S S' fS fX hf τ₁ G =
      crisDirectImageEval S S' fS fX hf τ₂ G ≫ G.obj.map g.op := by
  have h1 : ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map
        ((CrystallineThickening.ι S').map g').op ≫
        ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map τ₁.op =
      ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map τ₂.op ≫
        ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map
          ((changeBase S S' fS fX hf).map ((CrystallineThickening.ι S).map g)).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hτ]
  have h2 : ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map
        ((changeBase S S' fS fX hf).map ((CrystallineThickening.ι S).map g)).op ≫
        ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj G).obj).app
          (op ((CrystallineThickening.ι S).obj A₁)) =
      ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj G).obj).app
          (op ((CrystallineThickening.ι S).obj A₂)) ≫
        ((bigDirectImage S).obj G).obj.map ((CrystallineThickening.ι S).map g).op :=
    ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj G).obj).naturality
      ((CrystallineThickening.ι S).map g).op
  have h3 : ((bigDirectImage S).obj G).obj.map ((CrystallineThickening.ι S).map g).op ≫
        ((CrystallineThickening.ι S).op.ranCounit.app G.obj).app (op A₁) =
      ((CrystallineThickening.ι S).op.ranCounit.app G.obj).app (op A₂) ≫ G.obj.map g.op :=
    ((CrystallineThickening.ι S).op.ranCounit.app G.obj).naturality g.op
  change ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map
        ((CrystallineThickening.ι S').map g').op ≫
      ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map τ₁.op ≫
      ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj G).obj).app
        (op ((CrystallineThickening.ι S).obj A₁)) ≫
      ((CrystallineThickening.ι S).op.ranCounit.app G.obj).app (op A₁) =
    (((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj G).obj).map τ₂.op ≫
      ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj G).obj).app
        (op ((CrystallineThickening.ι S).obj A₂)) ≫
      ((CrystallineThickening.ι S).op.ranCounit.app G.obj).app (op A₂)) ≫ G.obj.map g.op
  refine ((reassoc_of% h1) _).trans ((congrArg (fun k => _ ≫ k) ((reassoc_of% h2) _)).trans ?_)
  exact (congrArg (fun k => _ ≫ _ ≫ k) h3).trans
    (congrArg (fun k => _ ≫ k) (Category.assoc _ _ _).symm)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
