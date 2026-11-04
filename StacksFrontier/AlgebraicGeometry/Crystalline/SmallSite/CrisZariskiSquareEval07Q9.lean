module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImageEval07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiFlatteningSections

/-!
# The square of topoi of [Stacks, Tag 07Q9], read on sections

Let `f : X'/S ⟶ X/S` be a morphism of global crystalline situations (in Lean the source is `S`
and the target `S'`).  The sections of `u_{X'/S, *}G` over an open `W` of `X'` are a limit over
the objects `A'` of `Cris(X'/S)` lying over `W`; this file names the projection of that limit at
one index,

`zariskiDirectImageEval h G : (u_{X'/S, *}G)(W) ⟶ G(A')`  for `h : U_{A'} ⊆ W`,

proves that it is natural in `G`, compatible with restriction to smaller opens and along
morphisms of `Cris(X'/S)`, and agrees with the projection of
`...SmallSite.zariskiDirectImageObjObjIsoLimit`.

It then reads the commutation `u_{X/S, *}f_{cris, *} ≅ f_{Zar, *}u_{X'/S, *}` of
[Stacks, Tag 07Q9] against these projections and against those of `f_{cris, *}`
(`...SmallSite.crisDirectImageEval`): for an open `V` of `X`, an object `A` of `Cris(X/S)` lying
over `V`, an object `A'` of `Cris(X'/S)` and a domination `k : f(A') ⟶ A`, the `2`-cell
`...SmallSite.crisZariskiCell` at `V`, followed by the projection at `A` and then at `k`, is the
projection of `u_{X'/S, *}G` over `f^{-1}V` at `A'`.  Both sides are the projection, at the
dominating pair `(A, A', k)`, of the limit computing `(u_{X/S, *}f_{cris, *}G)(V)`.

## Main definitions

* `zariskiDirectImageEval` — the projection `(u_{X/S, *}G)(V) ⟶ G(A)` for `U_A ⊆ V`.

## Main results

* `zariskiDirectImageEval_naturality`, `zariskiDirectImageEval_restrict`,
  `zariskiDirectImageEval_comp` — naturality in the sheaf, and compatibility with restriction.
* `zariskiDirectImageObjObjIsoLimit_hom_π` — it is the projection of the limit formula.
* `crisZariskiCell_app_hom_app_comp_eval` — **the `2`-cell of the square, on sections.**
* `eval_comp_crisDirectImageEval_eq_crisZariskiSquare` — the same for the commutation
  isomorphism `...SmallSite.crisZariskiSquare` itself.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section Eval

variable (S : GlobalCrystallineSituation.{u})

/-- **The value of `u_{X/S, *}G` over an open `V` projected to the value of `G` at an object `A`
of `Cris(X/S)` lying over `V`**: the index `(A, U_A ⊆ V)` of the limit computing
`(u_{X/S, *}G)(V)`.  It is the restriction to the open `U_A` followed by the counit of the right
Kan extension at `A`. -/
def zariskiDirectImageEval {V : S.X.Opens} {A : CrystallineThickening S}
    (h : (forgetToOpens S).obj A ≤ V) (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((zariskiDirectImage S).obj G).obj.obj (op V) ⟶ G.obj.obj (op A) :=
  ((forgetToOpens S).op.ran.obj G.obj).map (homOfLE h).op ≫
    ((forgetToOpens S).op.ranCounit.app G.obj).app (op A)

/-- **`zariskiDirectImageEval` is the projection of the limit formula** for the sections of
`u_{X/S, *}G`, `zariskiDirectImageObjObjIsoLimit`, at the index `(A, U_A ⊆ V)`. -/
theorem zariskiDirectImageObjObjIsoLimit_hom_π {V : S.X.Opens} {A : CrystallineThickening S}
    (h : (forgetToOpens S).obj A ≤ V) (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (zariskiDirectImageObjObjIsoLimit S G V).hom ≫
        limit.π (StructuredArrow.proj (op V) (forgetToOpens S).op ⋙ G.obj)
          (StructuredArrow.mk (Y := op A) (homOfLE h).op) =
      zariskiDirectImageEval S h G :=
  Functor.ranObjObjIsoLimit_hom_π (forgetToOpens S).op G.obj (op V)
    (StructuredArrow.mk (Y := op A) (homOfLE h).op)

/-- **`zariskiDirectImageEval` is natural in the sheaf.** -/
@[reassoc]
theorem zariskiDirectImageEval_naturality {V : S.X.Opens} {A : CrystallineThickening S}
    (h : (forgetToOpens S).obj A ≤ V)
    {G H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (φ : G ⟶ H) :
    ((zariskiDirectImage S).map φ).hom.app (op V) ≫ zariskiDirectImageEval S h H =
      zariskiDirectImageEval S h G ≫ φ.hom.app (op A) := by
  show ((forgetToOpens S).op.ran.map φ.hom).app (op V) ≫
      ((forgetToOpens S).op.ran.obj H.obj).map (homOfLE h).op ≫
        ((forgetToOpens S).op.ranCounit.app H.obj).app (op A) =
    (((forgetToOpens S).op.ran.obj G.obj).map (homOfLE h).op ≫
      ((forgetToOpens S).op.ranCounit.app G.obj).app (op A)) ≫ φ.hom.app (op A)
  rw [← ((forgetToOpens S).op.ran.map φ.hom).naturality_assoc, Category.assoc]
  congr 1
  exact congrArg (fun t ↦ NatTrans.app t (op A)) ((forgetToOpens S).op.ranCounit.naturality φ.hom)

/-- **`zariskiDirectImageEval` is compatible with restriction to a smaller open.** -/
@[reassoc]
theorem zariskiDirectImageEval_restrict {V W : S.X.Opens} (hWV : W ≤ V)
    {A : CrystallineThickening S} (h : (forgetToOpens S).obj A ≤ W)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((zariskiDirectImage S).obj G).obj.map (homOfLE hWV).op ≫ zariskiDirectImageEval S h G =
      zariskiDirectImageEval S (h.trans hWV) G := by
  show ((forgetToOpens S).op.ran.obj G.obj).map (homOfLE hWV).op ≫
      ((forgetToOpens S).op.ran.obj G.obj).map (homOfLE h).op ≫
        ((forgetToOpens S).op.ranCounit.app G.obj).app (op A) =
    ((forgetToOpens S).op.ran.obj G.obj).map (homOfLE (h.trans hWV)).op ≫
      ((forgetToOpens S).op.ranCounit.app G.obj).app (op A)
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

/-- **`zariskiDirectImageEval` is compatible with the restriction maps of `G`**: for a morphism
`g : A₁ ⟶ A₂` of `Cris(X/S)` with `U_{A₂} ⊆ V`, projecting to `A₂` and restricting along `g` is
projecting to `A₁`. -/
@[reassoc]
theorem zariskiDirectImageEval_comp {V : S.X.Opens} {A₁ A₂ : CrystallineThickening S}
    (g : A₁ ⟶ A₂) (h₁ : (forgetToOpens S).obj A₁ ≤ V) (h₂ : (forgetToOpens S).obj A₂ ≤ V)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    zariskiDirectImageEval S h₂ G ≫ G.obj.map g.op = zariskiDirectImageEval S h₁ G := by
  have hc : ((forgetToOpens S).op.ran.obj G.obj).map ((forgetToOpens S).map g).op ≫
        ((forgetToOpens S).op.ranCounit.app G.obj).app (op A₁) =
      ((forgetToOpens S).op.ranCounit.app G.obj).app (op A₂) ≫ G.obj.map g.op :=
    ((forgetToOpens S).op.ranCounit.app G.obj).naturality g.op
  have hm : ((forgetToOpens S).op.ran.obj G.obj).map (homOfLE h₂).op ≫
        ((forgetToOpens S).op.ran.obj G.obj).map ((forgetToOpens S).map g).op =
      ((forgetToOpens S).op.ran.obj G.obj).map (homOfLE h₁).op :=
    (((forgetToOpens S).op.ran.obj G.obj).map_comp _ _).symm.trans
      (congrArg (((forgetToOpens S).op.ran.obj G.obj).map ·) (Subsingleton.elim _ _))
  show (((forgetToOpens S).op.ran.obj G.obj).map (homOfLE h₂).op ≫
      ((forgetToOpens S).op.ranCounit.app G.obj).app (op A₂)) ≫ G.obj.map g.op =
    ((forgetToOpens S).op.ran.obj G.obj).map (homOfLE h₁).op ≫
      ((forgetToOpens S).op.ranCounit.app G.obj).app (op A₁)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t ↦ _ ≫ t) hc.symm).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hm)

end Eval

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- **A dominated object lies over the preimage.**  If `A` is an object of `Cris(X/S)` lying over
the open `V` of `X` and `k : f(A') ⟶ A` dominates an object `A'` of `Cris(X'/S)`, then `A'` lies
over `f^{-1}V`.  This is `dominationPairs_le_preimage` at the dominating pair `(A, A', k)`. -/
theorem forgetToOpens_le_preimage_of_domination {V : S'.X.Opens} {A : CrystallineThickening S'}
    (hA : (forgetToOpens S').obj A ≤ V) {A' : CrystallineThickening S}
    (k : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A) :
    (forgetToOpens S).obj A' ≤ fX ⁻¹ᵁ V :=
  dominationPairs_le_preimage S S' fS fX hf V
    (StructuredArrow.mk (Y := (⟨op A, op A', k.op⟩ : DominationPairs S S' fS fX hf))
      (homOfLE hA).op)

/-- **The `2`-cell of the square of topoi of [Stacks, Tag 07Q9], on sections.**  Let `V` be an
open of `X`, `A` an object of `Cris(X/S)` lying over `V`, `A'` an object of `Cris(X'/S)` and
`k : f(A') ⟶ A` a domination after change of divided power base.  Then the `2`-cell
`f_{Zar, *}u_{X'/S, *} ⟶ u_{X/S, *}f_{cris, *}` at `V`, followed by the projection to the
sections of `f_{cris, *}G` at `A` and the projection of those to `G(A')` along `k`, is the
projection of the sections of `u_{X'/S, *}G` over `f^{-1}V` to `G(A')`.

This is `crisZariskiCell_app_hom_app_comp_ranCounit` with its chains of counits named. -/
@[reassoc]
theorem crisZariskiCell_app_hom_app_comp_eval
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) {V : S'.X.Opens}
    {A : CrystallineThickening S'} (hA : (forgetToOpens S').obj A ≤ V)
    {A' : CrystallineThickening S}
    (k : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A)
    (hA' : (forgetToOpens S).obj A' ≤ fX ⁻¹ᵁ V) :
    ((crisZariskiCell S S' fS fX hf).app G).hom.app (op V) ≫
        zariskiDirectImageEval S' hA ((crisDirectImage S S' fS fX hf).obj G) ≫
          crisDirectImageEval S S' fS fX hf k G =
      zariskiDirectImageEval S hA' G :=
  crisZariskiCell_app_hom_app_comp_ranCounit S S' fS fX hf G V A A' k hA hA'

/-- **The commutation of the square of topoi of [Stacks, Tag 07Q9], on sections.**  In the
notation of `crisZariskiCell_app_hom_app_comp_eval`, projecting the sections of
`u_{X/S, *}f_{cris, *}G` over `V` to `A` and then to `G(A')` along `k` is the commutation
isomorphism `crisZariskiSquare` at `V` followed by the projection of the sections of
`u_{X'/S, *}G` over `f^{-1}V` to `G(A')`. -/
theorem eval_comp_crisDirectImageEval_eq_crisZariskiSquare
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) {V : S'.X.Opens}
    {A : CrystallineThickening S'} (hA : (forgetToOpens S').obj A ≤ V)
    {A' : CrystallineThickening S}
    (k : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A)
    (hA' : (forgetToOpens S).obj A' ≤ fX ⁻¹ᵁ V) :
    zariskiDirectImageEval S' hA ((crisDirectImage S S' fS fX hf).obj G) ≫
        crisDirectImageEval S S' fS fX hf k G =
      ((crisZariskiSquare S S' fS fX hf).hom.app G).hom.app (op V) ≫
        zariskiDirectImageEval S hA' G := by
  have hinv : ((crisZariskiSquare S S' fS fX hf).hom.app G).hom.app (op V) ≫
      ((crisZariskiCell S S' fS fX hf).app G).hom.app (op V) = 𝟙 _ := by
    have h := congrArg (fun t ↦ t.hom.app (op V))
      ((crisZariskiSquare S S' fS fX hf).hom_inv_id_app G)
    exact h
  rw [← crisZariskiCell_app_hom_app_comp_eval S S' fS fX hf G hA k hA', reassoc_of% hinv]

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
