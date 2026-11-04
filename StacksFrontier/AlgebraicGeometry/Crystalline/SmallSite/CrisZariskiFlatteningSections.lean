module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiCellSections
public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanBaseChange

/-!
# The flattening of `u_{X'/S', *}f_{cris, *}` into one limit, read against the counits

The three nested right Kan extensions computing `u_{X'/S', *}f_{cris, *}ℋ` are flattened into a
single one over the dominating pairs by
`Crystalline.GlobalCrystallineSituation.SmallSite.crisZariskiLeftRanIso` and, read at one open,
`Crystalline.GlobalCrystallineSituation.SmallSite.crisZariskiLeftObjIso`. This file computes these
isomorphisms on sections, against the counits of the right Kan extensions.

## Main results

* `crisZariskiLeftRanIso_hom_app_app_comp_ranCounit`: the flattening at the open a dominating pair
  lies over, followed by the counit of the single right Kan extension there, is the three counits
  of the nested extensions in turn, with the domination morphism of the pair in between.
* `crisZariskiLeftObjIso_hom_comp_π`: the same read at an arbitrary open `V` and against the
  projection of the limit over the dominating pairs over `V`.
* `crisZariskiCell_app_hom_app_comp_ranCounit`: the `2`-cell of the square of topoi of [Stacks, Tag
  07Q9] on sections. Followed by that composite of counits at a domination of an object of
  `Cris(X/S)`, it is the restriction of a section of `u_{X/S, *}ℋ` over `f^{-1}V` to the open of
  that object, followed by the counit of `u_{X/S, *}`.

## References

* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

variable (E : Type (u + 2)) [Category.{u + 1} E] [HasLimitsOfSize.{u, u + 1} E]

/-- **The flattening, read against the counits.** At the open of `X'` a dominating pair `(A, C, k)`
lies over, the comparison `crisZariskiLeftRanIso` followed by the counit of the single right Kan
extension over the dominating pairs is: the counit of `u_{X'/S', *}` at `A`, the restriction along
the domination `k`, the counit of `f_{CRIS, *}` at `C`, and the counit of `i_{X, *}` at `C`. This
is the statement at arbitrary coefficients `E`. -/
theorem crisZariskiLeftRanIso_hom_app_app_comp_ranCounitCoeff
    (P : (CrystallineThickening S)ᵒᵖ ⥤ E)
    (d : DominationPairs S S' fS fX hf) :
    ((crisZariskiLeftRanIso S S' fS fX hf E).hom.app P).app
          ((dominationToOpens S S' fS fX hf).obj d) ≫
        (((dominationToOpens S S' fS fX hf).ranCounit.app
          (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙
            P)).app d) =
      (((forgetToOpens S').op.ranCounit.app
            ((CrystallineThickening.ι S').op ⋙
              (changeBase S S' fS fX hf).op.ran.obj
                ((CrystallineThickening.ι S).op.ran.obj P))).app d.left) ≫
        ((changeBase S S' fS fX hf).op.ran.obj
            ((CrystallineThickening.ι S).op.ran.obj P)).map d.hom ≫
          (((changeBase S S' fS fX hf).op.ranCounit.app
            ((CrystallineThickening.ι S).op.ran.obj P)).app
              ((CrystallineThickening.ι S).op.obj d.right)) ≫
            (((CrystallineThickening.ι S).op.ranCounit.app P).app d.right) := by
  have hexp : ((crisZariskiLeftRanIso S S' fS fX hf E).hom.app P).app
        ((dominationToOpens S S' fS fX hf).obj d) =
      ((forgetToOpens S').op.ran.map (Functor.whiskerLeft (CrystallineThickening.ι S').op
          ((Functor.ranCompIsoOfAdjunctions E
            (CrystallineThickening.ι S).op
            (changeBase S S' fS fX hf).op).inv.app P))).app
          ((dominationToOpens S S' fS fX hf).obj d) ≫
        ((forgetToOpens S').op.ran.map
            ((TwoSquare.ranCommaIso (H := E)
              (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf)).hom.app P)).app
            ((dominationToOpens S S' fS fX hf).obj d) ≫
          ((Functor.ranCompIsoOfAdjunctions E
            (Comma.fst (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf))
            (forgetToOpens S').op).inv.app
              (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙
                P)).app ((dominationToOpens S S' fS fX hf).obj d) := by
    rw [crisZariskiLeftRanIso]
    dsimp only [dominationRan]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.whiskeringLeft_obj_obj, Functor.comp_map, Functor.whiskeringLeft_obj_map]
  have hA := Functor.ranCompIso_inv_app_app_comp_ranCounit E
    (Comma.fst (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf))
    (forgetToOpens S').op
    (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ P) d
  have hD := TwoSquare.ranBaseChange_app_app_ranCounit (D := E)
    (TwoSquare.commaSquare (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf)) P d
  have hF := Functor.ranCompIso_inv_app_app_comp_ranCounit E
    (CrystallineThickening.ι S).op (changeBase S S' fS fX hf).op P d.right
  have hB := congrArg (fun t ↦ NatTrans.app t d.left)
    ((forgetToOpens S').op.ranCounit.naturality
      ((TwoSquare.ranCommaIso (H := E) (CrystallineThickening.ι S').op
        (crisToBigOp S S' fS fX hf)).hom.app P))
  have hC := congrArg (fun t ↦ NatTrans.app t d.left)
    ((forgetToOpens S').op.ranCounit.naturality
      (Functor.whiskerLeft (CrystallineThickening.ι S').op
        ((Functor.ranCompIsoOfAdjunctions E (CrystallineThickening.ι S).op
          (changeBase S S' fS fX hf).op).inv.app P)))
  have hE := ((Functor.ranCompIsoOfAdjunctions E
    (CrystallineThickening.ι S).op (changeBase S S' fS fX hf).op).inv.app P).naturality d.hom
  rw [hexp]
  dsimp only [dominationRan, dominationToOpens]
  simp only [NatTrans.comp_app, Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
    Functor.id_map, Comma.fst_obj, Comma.snd_obj, TwoSquare.commaSquare_app,
    TwoSquare.ranCommaIso, asIso_hom, Category.assoc] at hA hB hC hD hE hF ⊢
  rw [hA, reassoc_of% hB, hD, reassoc_of% hC, reassoc_of% hE.symm, hF]

/-- **The flattening, read against the counits.** At the open of `X'` a dominating pair `(A, C, k)`
lies over, the comparison `crisZariskiLeftRanIso` followed by the counit of the single right Kan
extension over the dominating pairs is: the counit of `u_{X'/S', *}` at `A`, the restriction along
the domination `k`, the counit of `f_{CRIS, *}` at `C`, and the counit of `i_{X, *}` at `C`. -/
theorem crisZariskiLeftRanIso_hom_app_app_comp_ranCounit
    (P : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (d : DominationPairs S S' fS fX hf) :
    ((crisZariskiLeftRanIso S S' fS fX hf AddCommGrpCat.{u + 1}).hom.app P).app
          ((dominationToOpens S S' fS fX hf).obj d) ≫
        (((dominationToOpens S S' fS fX hf).ranCounit.app
          (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙
            P)).app d) =
      (((forgetToOpens S').op.ranCounit.app
            ((CrystallineThickening.ι S').op ⋙
              (changeBase S S' fS fX hf).op.ran.obj
                ((CrystallineThickening.ι S).op.ran.obj P))).app d.left) ≫
        ((changeBase S S' fS fX hf).op.ran.obj
            ((CrystallineThickening.ι S).op.ran.obj P)).map d.hom ≫
          (((changeBase S S' fS fX hf).op.ranCounit.app
            ((CrystallineThickening.ι S).op.ran.obj P)).app
              ((CrystallineThickening.ι S).op.obj d.right)) ≫
            (((CrystallineThickening.ι S).op.ranCounit.app P).app d.right) :=
  crisZariskiLeftRanIso_hom_app_app_comp_ranCounitCoeff S S' fS fX hf AddCommGrpCat.{u + 1} P d

/-- **The sections of `u_{X'/S', *}f_{cris, *}ℋ` over an open `V` of `X'`, read against one
projection of the limit over the dominating pairs over `V`.** The projection at a dominating pair
`(A, C, k)` is: restrict the section to the open of `A`, apply the counit of `u_{X'/S', *}` at `A`,
restrict along the domination `k`, and apply the counits of `f_{CRIS, *}` and of `i_{X, *}` at `C`.
This is the statement at arbitrary coefficients `E`. -/
theorem crisZariskiLeftObjIso_hom_comp_πCoeff
    (G : Sheaf (smallTopology S) E) (V : S'.X.Opens)
    (e : StructuredArrow (op V) (dominationToOpens S S' fS fX hf)) :
    (crisZariskiLeftObjIsoCoeff S S' fS fX hf E G V).hom ≫
        limit.π (StructuredArrow.proj (op V) (dominationToOpens S S' fS fX hf) ⋙
          Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj) e =
      ((forgetToOpens S').op.ran.obj ((CrystallineThickening.ι S').op ⋙
            (changeBase S S' fS fX hf).op.ran.obj
              ((CrystallineThickening.ι S).op.ran.obj G.obj))).map e.hom ≫
        (((forgetToOpens S').op.ranCounit.app
            ((CrystallineThickening.ι S').op ⋙
              (changeBase S S' fS fX hf).op.ran.obj
                ((CrystallineThickening.ι S).op.ran.obj G.obj))).app e.right.left) ≫
          ((changeBase S S' fS fX hf).op.ran.obj
              ((CrystallineThickening.ι S).op.ran.obj G.obj)).map e.right.hom ≫
            (((changeBase S S' fS fX hf).op.ranCounit.app
              ((CrystallineThickening.ι S).op.ran.obj G.obj)).app
                ((CrystallineThickening.ι S).op.obj e.right.right)) ≫
              (((CrystallineThickening.ι S).op.ranCounit.app G.obj).app e.right.right) := by
  have hmain := crisZariskiLeftRanIso_hom_app_app_comp_ranCounitCoeff S S' fS fX hf E G.obj e.right
  have hnat :=
    ((crisZariskiLeftRanIso S S' fS fX hf E).hom.app G.obj).naturality e.hom
  have hπ := Functor.ranObjObjIsoLimit_hom_π (dominationToOpens S S' fS fX hf)
    (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj) (op V) e
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z ↦ ((crisZariskiLeftRanIso S S' fS fX hf
      E).hom.app G.obj).app (op V) ≫ z)
    hπ).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z ↦ z ≫ (((dominationToOpens S S' fS fX hf).ranCounit.app
      (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj)).app
        e.right)) hnat.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z ↦ ((forgetToOpens S').op.ran.obj ((CrystallineThickening.ι S').op ⋙
    (changeBase S S' fS fX hf).op.ran.obj
      ((CrystallineThickening.ι S).op.ran.obj G.obj))).map e.hom ≫ z) hmain

/-- **The sections of `u_{X'/S', *}f_{cris, *}ℋ` over an open `V` of `X'`, read against one
projection of the limit over the dominating pairs over `V`.** The projection at a dominating pair
`(A, C, k)` is: restrict the section to the open of `A`, apply the counit of `u_{X'/S', *}` at `A`,
restrict along the domination `k`, and apply the counits of `f_{CRIS, *}` and of `i_{X, *}` at `C`.
-/
theorem crisZariskiLeftObjIso_hom_comp_π
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (V : S'.X.Opens)
    (e : StructuredArrow (op V) (dominationToOpens S S' fS fX hf)) :
    (crisZariskiLeftObjIso S S' fS fX hf G V).hom ≫
        limit.π (StructuredArrow.proj (op V) (dominationToOpens S S' fS fX hf) ⋙
          Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj) e =
      ((forgetToOpens S').op.ran.obj ((CrystallineThickening.ι S').op ⋙
            (changeBase S S' fS fX hf).op.ran.obj
              ((CrystallineThickening.ι S).op.ran.obj G.obj))).map e.hom ≫
        (((forgetToOpens S').op.ranCounit.app
            ((CrystallineThickening.ι S').op ⋙
              (changeBase S S' fS fX hf).op.ran.obj
                ((CrystallineThickening.ι S).op.ran.obj G.obj))).app e.right.left) ≫
          ((changeBase S S' fS fX hf).op.ran.obj
              ((CrystallineThickening.ι S).op.ran.obj G.obj)).map e.right.hom ≫
            (((changeBase S S' fS fX hf).op.ranCounit.app
              ((CrystallineThickening.ι S).op.ran.obj G.obj)).app
                ((CrystallineThickening.ι S).op.obj e.right.right)) ≫
              (((CrystallineThickening.ι S).op.ranCounit.app G.obj).app e.right.right) :=
  crisZariskiLeftObjIso_hom_comp_πCoeff S S' fS fX hf AddCommGrpCat.{u + 1} G V e

/-- **The `2`-cell of the square of topoi of [Stacks, Tag 07Q9] on sections, read against a
domination.** Let `A` be an object of `Cris(X/S)`, let `A'` be an object of `Cris(X'/S')` lying
over the open `V` of `X'`, and let `k : K A ⟶ i_{X'} A'` be a domination. Then the `2`-cell at `V`,
followed by the restriction to the open of `A'`, the counit of `u_{X'/S', *}`, the restriction
along `k` and the counits of `f_{CRIS, *}` and of `i_{X, *}` at `A`, is the restriction of a
section of `u_{X/S, *}ℋ` over `f^{-1}V` to the open of `A`, followed by the counit of `u_{X/S, *}`
there. This is the statement at arbitrary coefficients `E`. -/
theorem crisZariskiCell_app_hom_app_comp_ranCounitCoeff
    (G : Sheaf (smallTopology S) E) (V : S'.X.Opens)
    (A' : CrystallineThickening S') (A : CrystallineThickening S)
    (k : (crisToBig S S' fS fX hf).obj A ⟶ (CrystallineThickening.ι S').obj A')
    (hV : (forgetToOpens S').obj A' ≤ V)
    (hVA : (forgetToOpens S).obj A ≤ fX ⁻¹ᵁ V) :
    ((crisZariskiCellCoeff S S' fS fX hf E).app G).hom.app (op V) ≫
        ((forgetToOpens S').op.ran.obj ((CrystallineThickening.ι S').op ⋙
            (changeBase S S' fS fX hf).op.ran.obj
              ((CrystallineThickening.ι S).op.ran.obj G.obj))).map (homOfLE hV).op ≫
          (((forgetToOpens S').op.ranCounit.app
            ((CrystallineThickening.ι S').op ⋙
              (changeBase S S' fS fX hf).op.ran.obj
                ((CrystallineThickening.ι S).op.ran.obj G.obj))).app (op A')) ≫
            ((changeBase S S' fS fX hf).op.ran.obj
                ((CrystallineThickening.ι S).op.ran.obj G.obj)).map k.op ≫
              (((changeBase S S' fS fX hf).op.ranCounit.app
                ((CrystallineThickening.ι S).op.ran.obj G.obj)).app
                  ((CrystallineThickening.ι S).op.obj (op A))) ≫
                (((CrystallineThickening.ι S).op.ranCounit.app G.obj).app (op A)) =
      ((forgetToOpens S).op.ran.obj G.obj).map (homOfLE hVA).op ≫
        (((forgetToOpens S).op.ranCounit.app G.obj).app (op A)) := by
  have hCL := crisZariskiLeftObjIso_hom_comp_πCoeff S S' fS fX hf E G V
    (StructuredArrow.mk (Y := (⟨op A', op A, k.op⟩ : DominationPairs S S' fS fX hf))
      (homOfLE hV).op)
  have hcell := crisZariskiCell_app_hom_app_comp_homCoeff S S' fS fX hf E G V
  have hpre := limit.pre_π (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
    (dominationProj S S' fS fX hf V)
    (StructuredArrow.mk (Y := (⟨op A', op A, k.op⟩ : DominationPairs S S' fS fX hf))
      (homOfLE hV).op)
  have hzπ := Functor.ranObjObjIsoLimit_hom_π (forgetToOpens S).op G.obj (op (fX ⁻¹ᵁ V))
    ((dominationProj S S' fS fX hf V).obj
      (StructuredArrow.mk (Y := (⟨op A', op A, k.op⟩ : DominationPairs S S' fS fX hf))
        (homOfLE hV).op))
  refine (congrArg (fun z ↦ ((crisZariskiCellCoeff S S' fS fX hf E).app G).hom.app (op V) ≫ z)
    hCL.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z ↦ z ≫ limit.π (StructuredArrow.proj (op V)
      (dominationToOpens S S' fS fX hf) ⋙
        Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj)
      (StructuredArrow.mk (Y := (⟨op A', op A, k.op⟩ : DominationPairs S S' fS fX hf))
        (homOfLE hV).op)) hcell).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z ↦ ((forgetToOpens S).op.ranObjObjIsoLimit G.obj (op (fX ⁻¹ᵁ V))).hom ≫ z)
    hpre).trans ?_
  refine hzπ.trans ?_
  exact congrArg (fun z ↦ ((forgetToOpens S).op.ran.obj G.obj).map z ≫
    (((forgetToOpens S).op.ranCounit.app G.obj).app (op A))) (Subsingleton.elim _ _)

/-- **The `2`-cell of the square of topoi of [Stacks, Tag 07Q9] on sections, read against a
domination.** Let `A` be an object of `Cris(X/S)`, let `A'` be an object of `Cris(X'/S')` lying
over the open `V` of `X'`, and let `k : K A ⟶ i_{X'} A'` be a domination. Then the `2`-cell at `V`,
followed by the restriction to the open of `A'`, the counit of `u_{X'/S', *}`, the restriction
along `k` and the counits of `f_{CRIS, *}` and of `i_{X, *}` at `A`, is the restriction of a
section of `u_{X/S, *}ℋ` over `f^{-1}V` to the open of `A`, followed by the counit of `u_{X/S, *}`
there. -/
theorem crisZariskiCell_app_hom_app_comp_ranCounit
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (V : S'.X.Opens)
    (A' : CrystallineThickening S') (A : CrystallineThickening S)
    (k : (crisToBig S S' fS fX hf).obj A ⟶ (CrystallineThickening.ι S').obj A')
    (hV : (forgetToOpens S').obj A' ≤ V)
    (hVA : (forgetToOpens S).obj A ≤ fX ⁻¹ᵁ V) :
    ((crisZariskiCell S S' fS fX hf).app G).hom.app (op V) ≫
        ((forgetToOpens S').op.ran.obj ((CrystallineThickening.ι S').op ⋙
            (changeBase S S' fS fX hf).op.ran.obj
              ((CrystallineThickening.ι S).op.ran.obj G.obj))).map (homOfLE hV).op ≫
          (((forgetToOpens S').op.ranCounit.app
            ((CrystallineThickening.ι S').op ⋙
              (changeBase S S' fS fX hf).op.ran.obj
                ((CrystallineThickening.ι S).op.ran.obj G.obj))).app (op A')) ≫
            ((changeBase S S' fS fX hf).op.ran.obj
                ((CrystallineThickening.ι S).op.ran.obj G.obj)).map k.op ≫
              (((changeBase S S' fS fX hf).op.ranCounit.app
                ((CrystallineThickening.ι S).op.ran.obj G.obj)).app
                  ((CrystallineThickening.ι S).op.obj (op A))) ≫
                (((CrystallineThickening.ι S).op.ranCounit.app G.obj).app (op A)) =
      ((forgetToOpens S).op.ran.obj G.obj).map (homOfLE hVA).op ≫
        (((forgetToOpens S).op.ranCounit.app G.obj).app (op A)) :=
  crisZariskiCell_app_hom_app_comp_ranCounitCoeff S S' fS fX hf AddCommGrpCat.{u + 1} G V A' A k hV
    hVA

/-- **Maps into the sections of `u_{X'/S', *}f_{cris, *}ℋ` over `V` are detected by the dominating
pairs over `V`**: two maps agree as soon as they agree after the composite of restrictions and
counits of `crisZariskiLeftObjIso_hom_comp_πCoeff`, at every dominating pair over `V`. -/
theorem crisZariskiLeft_hom_extCoeff (G : Sheaf (smallTopology S) E) (V : S'.X.Opens) {T : E}
    {x y : T ⟶ ((zariskiDirectImageCoeff S' E).obj
      ((crisDirectImageCoeff S S' fS fX hf E).obj G)).obj.obj (op V)}
    (h : ∀ e : StructuredArrow (op V) (dominationToOpens S S' fS fX hf),
      x ≫ ((forgetToOpens S').op.ran.obj ((CrystallineThickening.ι S').op ⋙
            (changeBase S S' fS fX hf).op.ran.obj
              ((CrystallineThickening.ι S).op.ran.obj G.obj))).map e.hom ≫
        (((forgetToOpens S').op.ranCounit.app
            ((CrystallineThickening.ι S').op ⋙
              (changeBase S S' fS fX hf).op.ran.obj
                ((CrystallineThickening.ι S).op.ran.obj G.obj))).app e.right.left) ≫
          ((changeBase S S' fS fX hf).op.ran.obj
              ((CrystallineThickening.ι S).op.ran.obj G.obj)).map e.right.hom ≫
            (((changeBase S S' fS fX hf).op.ranCounit.app
              ((CrystallineThickening.ι S).op.ran.obj G.obj)).app
                ((CrystallineThickening.ι S).op.obj e.right.right)) ≫
              (((CrystallineThickening.ι S).op.ranCounit.app G.obj).app e.right.right) =
      y ≫ ((forgetToOpens S').op.ran.obj ((CrystallineThickening.ι S').op ⋙
            (changeBase S S' fS fX hf).op.ran.obj
              ((CrystallineThickening.ι S).op.ran.obj G.obj))).map e.hom ≫
        (((forgetToOpens S').op.ranCounit.app
            ((CrystallineThickening.ι S').op ⋙
              (changeBase S S' fS fX hf).op.ran.obj
                ((CrystallineThickening.ι S).op.ran.obj G.obj))).app e.right.left) ≫
          ((changeBase S S' fS fX hf).op.ran.obj
              ((CrystallineThickening.ι S).op.ran.obj G.obj)).map e.right.hom ≫
            (((changeBase S S' fS fX hf).op.ranCounit.app
              ((CrystallineThickening.ι S).op.ran.obj G.obj)).app
                ((CrystallineThickening.ι S).op.obj e.right.right)) ≫
              (((CrystallineThickening.ι S).op.ranCounit.app G.obj).app e.right.right)) :
    x = y := by
  rw [← cancel_mono (crisZariskiLeftObjIsoCoeff S S' fS fX hf E G V).hom]
  refine limit.hom_ext fun e ↦ ?_
  simp only [Category.assoc, crisZariskiLeftObjIso_hom_comp_πCoeff]
  exact h e

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
