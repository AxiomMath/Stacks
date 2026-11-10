module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiFlatteningSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.GlobalSectionsIsoRestriction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LerayCoherence

/-!
# The underived Leray coherence across the square of [Stacks, Tag 07Q9]

`SmallSite/LerayCoherence.lean` reduces the coherence of the four Leray comparisons of
[Stacks, Tag 07QA] — `...SmallSite.CrisZariskiLerayCoherence` — to its *underived* shadow: the
two routes

`Γ(X'_Zar, u_{X'/S', *}f_{cris, *}ℋ) ⟶ Γ(Cris(X/S), ℋ)`

agree, one through `...SmallSite.zariskiGlobalSectionsDirectImageIso` and
`...SmallSite.crisGlobalSectionsIso`, the other through the `2`-cell of the square of topoi, the
comparison for `f_{Zar}` and the comparison for `u_{X/S}`.  **This file proves that.**

## The proof

Both routes are maps into `Γ(Cris(X/S), ℋ)`, but the first factor of `crisGlobalSectionsIso` is
the comparison `Γ(Cris(X'/S'), i_{X'}^{-1}ℒ) ≅ Γ(CRIS(X'/S'), ℒ)`, which at an object of
`CRIS(X'/S')` outside the image of `i_{X'}` is a glued section and not a projection — and change
of divided power base carries an object of `Cris(X/S)` to just such an object.  So the equality
is not checked at `Γ(Cris(X/S), ℋ)` directly.  Instead the two comparisons along cocontinuous
functors that follow are moved to the other side, and the equality is checked at
`Γ(CRIS(X'/S'), ℒ)`, where `CategoryTheory.GrothendieckTopology.CoversTop.ext` and
`...CrystallineThickening.coversTop_ι` reduce it to the objects coming from `Cris(X'/S')`.  There
the restriction comparison *is* a projection,
`...SmallSite.smallRestrictionGlobalSectionsIso_hom_app_comp_ΓRes_ι`.

What is left is an equality of two maps into the sections of `ℒ` at an object of `Cris(X'/S')`.
Those sections are a right Kan extension twice over, so
`CategoryTheory.Functor.ran_obj_obj_hom_ext` twice reduces to the sections of `ℋ` at an object
`A` of `Cris(X/S)` dominating it — and there
both routes are the component at `A`, which is
`...SmallSite.crisZariskiCell_app_hom_app_comp_ranCounit` for the first route and the two
`ΓRes` evaluations for the second.

## Main results

* `...SmallSite.crisZariskiUnderivedCoherence` — the underived coherence, unconditionally.
* `...SmallSite.crisZariskiLerayCoherence` — **`...SmallSite.CrisZariskiLerayCoherence` holds**:
  the square of the four Leray comparisons of [Stacks, Tag 07QA] commutes.  This discharges the
  hypothesis of `...SmallSite.derivedZariskiGlobalSections_map_derivedZariskiComparison`, which
  is what carries a bound on the map induced on `H^i(X_Zar, -)` by
  `...SmallSite.derivedZariskiComparison` over to `...SmallSite.crisCohomologyMap`.

## What this does and does not give

No tag is placed here: the coherence square is one of the three inputs of [Stacks, Tag 07QA],
which is `...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover` of
`SmallSite/CrisCohomologyBound07QAMain.lean`.  The other two are the corepresentation
`H^i(RΓ(X_Zar, K)) ≅ Hom(ℤ_X[0]⟦-i⟧, K)` of Zariski hypercohomology,
`...SmallSite.derivedZariskiGlobalSectionsHomologyShiftAddEquiv` of
`SmallSite/ZariskiHypercohomology.lean`, with its naturality in `K`, which is the form the bounds
consume; and the annihilation of [Stacks, Tag 07Q9], which rests on [Stacks, Proposition 07LG] and
is `...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover`.
`SmallSite/HypercohomologyBound07QA.lean` assembles the first two with this square, its two bounds
taking `...SmallSite.Annihilation07Q9` as an input and nothing else beyond the monomorphism the
cokernel half needs.

## References

* [Stacks Project, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

/-- **The last two factors of `crisGlobalSectionsIso`**: the comparison of global sections along
change of divided power base followed by the one along the inclusion of the small crystalline
site of `X`.  Both are comparisons along a cocontinuous functor of sites, so both are evaluated
against the restriction maps, and it is this composite that the underived coherence is checked
against. -/
def crisBigGlobalSectionsIso (H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (bigGlobalSections S').obj
        ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H)) ≅
      (globalSections S).obj H :=
  (changeBaseDirectImageGlobalSectionsIso S S' fS fX hf).app ((bigDirectImage S).obj H) ≪≫
    (bigDirectImageGlobalSectionsIso S).app H

/-- `crisGlobalSectionsIso` is the restriction comparison followed by `crisBigGlobalSectionsIso`:
its four factors are those three and an associator. -/
theorem crisGlobalSectionsIso_hom_app_eq (H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (crisGlobalSectionsIso S S' fS fX hf).hom.app H =
      (smallRestrictionGlobalSectionsIso (S := S')).hom.app
          ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H)) ≫
        (crisBigGlobalSectionsIso S S' fS fX hf H).hom := by
  have hh : (crisBigGlobalSectionsIso S S' fS fX hf H).hom =
      (changeBaseDirectImageGlobalSectionsIso S S' fS fX hf).hom.app ((bigDirectImage S).obj H) ≫
        (bigDirectImageGlobalSectionsIso S).hom.app H := rfl
  rw [hh, crisGlobalSectionsIso]
  dsimp only [crisDirectImage]
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.comp_obj, Category.id_comp]

/-- **The composite of the two cocontinuous comparisons, inverted and read at an object of
`CRIS(X/S)`.**  Restricting a global section of `f_{CRIS, *}i_{X, *}ℋ` to the image of an object
`B` of `CRIS(X/S)` under change of base and applying the counit there is restricting the
corresponding global section of `ℋ` — which is what both `_hom_app_comp_ΓRes` evaluations say,
read backwards. -/
theorem crisBigGlobalSectionsIso_inv_comp_ΓRes
    (H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (B : Thickening S) :
    (crisBigGlobalSectionsIso S S' fS fX hf H).inv ≫
        Sheaf.ΓRes ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))
            (op ((changeBase S S' fS fX hf).obj B)) ≫
          (((changeBase S S' fS fX hf).op.ranCounit.app
            ((bigDirectImage S).obj H).obj).app (op B)) =
      (bigDirectImageGlobalSectionsIso S).inv.app H ≫
        Sheaf.ΓRes ((bigDirectImage S).obj H) (op B) := by
  have h := changeBaseDirectImageGlobalSectionsIso_hom_app_comp_ΓRes S S' fX fS hf
    ((bigDirectImage S).obj H) B
  have hinv : (crisBigGlobalSectionsIso S S' fS fX hf H).inv =
      (bigDirectImageGlobalSectionsIso S).inv.app H ≫
        (changeBaseDirectImageGlobalSectionsIso S S' fS fX hf).inv.app
          ((bigDirectImage S).obj H) := rfl
  rw [hinv, Category.assoc, ← h, Iso.inv_hom_id_app_assoc]

omit hf in
/-- **The Zariski route, read at an object of `Cris(X/S)`.**  Going `Γ(X'_Zar, f_{Zar, *}M) ⟶
Γ(X_Zar, M) ⟶ Γ(Cris(X/S), ℋ)` for `M = u_{X/S, *}ℋ` and restricting to `A` is restricting a
section of `f_{Zar, *}M` over the top open — which is a section of `M` over the top open of `X` —
to the open of `A` and applying the counit of `u_{X/S, *}` there. -/
theorem zariskiRoute_comp_ΓRes (H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (A : CrystallineThickening S) :
    ((zariskiPushforwardGlobalSectionsIso S S' fX).hom.app ((zariskiDirectImage S).obj H) ≫
        (zariskiGlobalSectionsDirectImageIso S).hom.app H) ≫ Sheaf.ΓRes H (op A) =
      Sheaf.ΓRes ((zariskiPushforward S S' fX).obj ((zariskiDirectImage S).obj H)) (op ⊤) ≫
        ((forgetToOpens S).op.ran.obj H.obj).map
            (homOfLE (le_top : (forgetToOpens S).obj A ≤ ⊤)).op ≫
          (((forgetToOpens S).op.ranCounit.app H.obj).app (op A)) := by
  rw [Category.assoc, zariskiGlobalSectionsDirectImageIso_hom_app_comp_ΓRes,
    ← Sheaf.ΓRes_map ((zariskiDirectImage S).obj H)
      (homOfLE (le_top : (forgetToOpens S).obj A ≤ ⊤)).op]
  erw [Category.assoc (Sheaf.ΓRes _ _), ← Category.assoc _ (Sheaf.ΓRes _ _),
    zariskiPushforwardGlobalSectionsIso_hom_app_comp_ΓRes S S' fX, Category.assoc]

/-- **The crystalline route, read at a domination.**  Going
`Γ(X'_Zar, f_{Zar, *}u_{X/S, *}ℋ) ⟶ Γ(X'_Zar, u_{X'/S', *}f_{cris, *}ℋ) ⟶ Γ(Cris(X'/S'),
f_{cris, *}ℋ) ⟶ Γ(CRIS(X'/S'), f_{CRIS, *}i_{X, *}ℋ)`, restricting to an object `A'` of
`Cris(X'/S')`, restricting further along a domination `A' ← K A` and applying the two counits is
the same thing: it is `crisZariskiCell_app_hom_app_comp_ranCounit` at the top open. -/
theorem crisRoute_comp_ΓRes (H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (A' : CrystallineThickening S') (A : CrystallineThickening S)
    (m : (crisToBig S S' fS fX hf).obj A ⟶ (CrystallineThickening.ι S').obj A') :
    (zariskiGlobalSections S').map ((crisZariskiCell S S' fS fX hf).app H) ≫
        (zariskiGlobalSectionsDirectImageIso S').hom.app
            ((crisDirectImage S S' fS fX hf).obj H) ≫
          ((smallRestrictionGlobalSectionsIso (S := S')).hom.app
              ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H)) ≫
            Sheaf.ΓRes ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))
                (op ((CrystallineThickening.ι S').obj A')) ≫
              ((changeBaseDirectImage S S' fS fX hf).obj
                  ((bigDirectImage S).obj H)).obj.map m.op ≫
                (((changeBase S S' fS fX hf).op.ranCounit.app
                  ((bigDirectImage S).obj H).obj).app
                    (op ((CrystallineThickening.ι S).obj A))) ≫
                  (((CrystallineThickening.ι S).op.ranCounit.app H.obj).app (op A))) =
      Sheaf.ΓRes ((zariskiPushforward S S' fX).obj ((zariskiDirectImage S).obj H)) (op ⊤) ≫
        ((forgetToOpens S).op.ran.obj H.obj).map
            (homOfLE (le_top : (forgetToOpens S).obj A ≤ ⊤)).op ≫
          (((forgetToOpens S).op.ranCounit.app H.obj).app (op A)) := by
  have hβ := smallRestrictionGlobalSectionsIso_hom_app_comp_ΓRes_ι S'
    ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H)) A'
  have hα := zariskiGlobalSectionsDirectImageIso_hom_app_comp_ΓRes S'
    ((crisDirectImage S S' fS fX hf).obj H) A'
  have hkey : ∀ {Z : AddCommGrpCat.{u + 1}}
      (g : ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H)).obj.obj
        (op ((CrystallineThickening.ι S').obj A')) ⟶ Z),
      (zariskiGlobalSectionsDirectImageIso S').hom.app
            ((crisDirectImage S S' fS fX hf).obj H) ≫
          (smallRestrictionGlobalSectionsIso (S := S')).hom.app
              ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H)) ≫
            Sheaf.ΓRes ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))
              (op ((CrystallineThickening.ι S').obj A')) ≫ g =
        Sheaf.ΓRes ((zariskiDirectImage S').obj ((crisDirectImage S S' fS fX hf).obj H))
            (op ((forgetToOpens S').obj A')) ≫
          (((forgetToOpens S').op.ranCounit.app
            ((crisDirectImage S S' fS fX hf).obj H).obj).app (op A')) ≫ g := by
    intro Z g
    exact ((congrArg (fun z ↦ (zariskiGlobalSectionsDirectImageIso S').hom.app
          ((crisDirectImage S S' fS fX hf).obj H) ≫ z)
        ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ g) hβ))).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ g) hα))).trans
        (Category.assoc _ _ _)
  have hcone : Sheaf.ΓRes ((zariskiDirectImage S').obj ((crisDirectImage S S' fS fX hf).obj H))
        (op ⊤) ≫
      ((zariskiDirectImage S').obj ((crisDirectImage S S' fS fX hf).obj H)).obj.map
        (homOfLE (le_top : (forgetToOpens S').obj A' ≤ ⊤)).op =
      Sheaf.ΓRes ((zariskiDirectImage S').obj ((crisDirectImage S S' fS fX hf).obj H))
        (op ((forgetToOpens S').obj A')) :=
    ((zariskiDirectImage S').obj ((crisDirectImage S S' fS fX hf).obj H)).coneΓ.w _
  have hnat := Sheaf.ΓRes_naturality ((crisZariskiCell S S' fS fX hf).app H) (op ⊤)
  have hcell := crisZariskiCell_app_hom_app_comp_ranCounit S S' fS fX hf H ⊤ A' A m
    le_top le_top
  rw [hkey, ← hcone]
  simp only [Category.assoc]
  rw [reassoc_of% hnat]
  exact congrArg (fun z ↦ Sheaf.ΓRes
    ((zariskiPushforward S S' fX).obj ((zariskiDirectImage S).obj H)) (op ⊤) ≫ z) hcell

/-- **The two routes agree before the last two comparisons are applied.**  Both sides are maps
into `Γ(CRIS(X'/S'), f_{CRIS, *}i_{X, *}ℋ)`; the objects of `Cris(X'/S')` cover the final object
of that topos, so it is enough to compare their restrictions there, and those sections are a
right Kan extension twice over, so it is enough to compare after a domination by an object of
`Cris(X/S)` — which is `crisRoute_comp_ΓRes` against `zariskiRoute_comp_ΓRes`. -/
theorem crisZariskiUnderivedCoherence_aux
    (H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (zariskiGlobalSections S').map ((crisZariskiCell S S' fS fX hf).app H) ≫
        (zariskiGlobalSectionsDirectImageIso S').hom.app
            ((crisDirectImage S S' fS fX hf).obj H) ≫
          (smallRestrictionGlobalSectionsIso (S := S')).hom.app
            ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H)) =
      ((zariskiPushforwardGlobalSectionsIso S S' fX).hom.app ((zariskiDirectImage S).obj H) ≫
          (zariskiGlobalSectionsDirectImageIso S).hom.app H) ≫
        (crisBigGlobalSectionsIso S S' fS fX hf H).inv := by
  refine (CrystallineThickening.coversTop_ι S').ext
    ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))
    (Sheaf.isLimitConeΓ _) fun A' ↦ ?_
  change ((zariskiGlobalSections S').map ((crisZariskiCell S S' fS fX hf).app H) ≫
        (zariskiGlobalSectionsDirectImageIso S').hom.app
            ((crisDirectImage S S' fS fX hf).obj H) ≫
          (smallRestrictionGlobalSectionsIso (S := S')).hom.app
            ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))) ≫
      Sheaf.ΓRes ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))
        (op ((CrystallineThickening.ι S').obj A')) =
    (((zariskiPushforwardGlobalSectionsIso S S' fX).hom.app ((zariskiDirectImage S).obj H) ≫
          (zariskiGlobalSectionsDirectImageIso S).hom.app H) ≫
        (crisBigGlobalSectionsIso S S' fS fX hf H).inv) ≫
      Sheaf.ΓRes ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))
        (op ((CrystallineThickening.ι S').obj A'))
  refine Functor.ran_obj_obj_hom_ext (changeBase S S' fS fX hf).op
    ((bigDirectImage S).obj H).obj (op ((CrystallineThickening.ι S').obj A')) fun e ↦ ?_
  refine Functor.ran_obj_obj_hom_ext (CrystallineThickening.ι S).op H.obj e.right fun e₂ ↦ ?_
  have hnatc : ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj H).obj).map
        ((changeBase S S' fS fX hf).op.map e₂.hom) ≫
      (((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj H).obj).app
        ((CrystallineThickening.ι S).op.obj e₂.right)) =
      (((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj H).obj).app
          e.right) ≫
        ((CrystallineThickening.ι S).op.ran.obj H.obj).map e₂.hom :=
    ((changeBase S S' fS fX hf).op.ranCounit.app
      ((bigDirectImage S).obj H).obj).naturality e₂.hom
  dsimp only [Functor.id_obj] at hnatc
  have hmerge : ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj H).obj).map
        e.hom ≫
      (((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj H).obj).app
        e.right) ≫
        ((CrystallineThickening.ι S).op.ran.obj H.obj).map e₂.hom ≫
          (((CrystallineThickening.ι S).op.ranCounit.app H.obj).app e₂.right) =
      ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj H).obj).map
          (e.hom ≫ (changeBase S S' fS fX hf).op.map e₂.hom) ≫
        (((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj H).obj).app
          ((CrystallineThickening.ι S).op.obj e₂.right)) ≫
          (((CrystallineThickening.ι S).op.ranCounit.app H.obj).app e₂.right) :=
    (congrArg (fun z ↦ ((changeBase S S' fS fX hf).op.ran.obj
          ((bigDirectImage S).obj H).obj).map e.hom ≫ z)
        (((Category.assoc _ _ _).symm.trans
            (congrArg (fun z ↦ z ≫ (((CrystallineThickening.ι S).op.ranCounit.app H.obj).app
              e₂.right)) hnatc.symm)).trans (Category.assoc _ _ _))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z ↦ z ≫ ((((changeBase S S' fS fX hf).op.ranCounit.app
              ((bigDirectImage S).obj H).obj).app
                ((CrystallineThickening.ι S).op.obj e₂.right)) ≫
            (((CrystallineThickening.ι S).op.ranCounit.app H.obj).app e₂.right)))
          (CategoryTheory.Functor.map_comp _ _ _).symm))
  have hΓ : Sheaf.ΓRes ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))
        (op ((CrystallineThickening.ι S').obj A')) ≫
      ((changeBase S S' fS fX hf).op.ran.obj ((bigDirectImage S).obj H).obj).map
        (e.hom ≫ (changeBase S S' fS fX hf).op.map e₂.hom) =
      Sheaf.ΓRes ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))
        (op ((changeBase S S' fS fX hf).obj
          ((CrystallineThickening.ι S).obj e₂.right.unop))) :=
    ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H)).coneΓ.w _
  have hδ : (bigDirectImageGlobalSectionsIso S).inv.app H ≫
        Sheaf.ΓRes ((bigDirectImage S).obj H)
            (op ((CrystallineThickening.ι S).obj e₂.right.unop)) ≫
          (((CrystallineThickening.ι S).op.ranCounit.app H.obj).app e₂.right) =
      Sheaf.ΓRes H (op e₂.right.unop) := by
    rw [← bigDirectImageGlobalSectionsIso_hom_app_comp_ΓRes S H e₂.right.unop,
      Iso.inv_hom_id_app_assoc]
  trans (Sheaf.ΓRes ((zariskiPushforward S S' fX).obj ((zariskiDirectImage S).obj H)) (op ⊤) ≫
    ((forgetToOpens S).op.ran.obj H.obj).map
        (homOfLE (le_top : (forgetToOpens S).obj e₂.right.unop ≤ ⊤)).op ≫
      (((forgetToOpens S).op.ranCounit.app H.obj).app (op e₂.right.unop)))
  · refine Eq.trans ?_ (crisRoute_comp_ΓRes S S' fS fX hf H A' e₂.right.unop
      (e.hom ≫ (changeBase S S' fS fX hf).op.map e₂.hom).unop)
    refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)
    refine Eq.trans (congrArg (fun z ↦ ((zariskiGlobalSections S').map
        ((crisZariskiCell S S' fS fX hf).app H) ≫
      (zariskiGlobalSectionsDirectImageIso S').hom.app
          ((crisDirectImage S S' fS fX hf).obj H) ≫
        (smallRestrictionGlobalSectionsIso (S := S')).hom.app
          ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))) ≫
      Sheaf.ΓRes ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))
          (op ((CrystallineThickening.ι S').obj A')) ≫ z)
      ((Category.assoc _ _ _).trans hmerge)) ?_
    exact (Category.assoc _ _ _).trans (congrArg (fun z ↦ (zariskiGlobalSections S').map
      ((crisZariskiCell S S' fS fX hf).app H) ≫ z) (Category.assoc _ _ _))
  · have hcbδ : (crisBigGlobalSectionsIso S S' fS fX hf H).inv ≫
          Sheaf.ΓRes ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H))
              (op ((changeBase S S' fS fX hf).obj
                ((CrystallineThickening.ι S).obj e₂.right.unop))) ≫
            (((changeBase S S' fS fX hf).op.ranCounit.app
              ((bigDirectImage S).obj H).obj).app
                (op ((CrystallineThickening.ι S).obj e₂.right.unop))) ≫
              (((CrystallineThickening.ι S).op.ranCounit.app H.obj).app e₂.right) =
        Sheaf.ΓRes H (op e₂.right.unop) :=
      ((congrArg (fun z ↦ (crisBigGlobalSectionsIso S S' fS fX hf H).inv ≫ z)
          (Category.assoc _ _ _).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫ (((CrystallineThickening.ι S).op.ranCounit.app H.obj).app
              e₂.right))
            (crisBigGlobalSectionsIso_inv_comp_ΓRes S S' fS fX hf H
              ((CrystallineThickening.ι S).obj e₂.right.unop))))).trans
        ((Category.assoc _ _ _).trans hδ)
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z ↦ _ ≫ z) ((Category.assoc _ _ _).trans hmerge)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z ↦ _ ≫ z)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ _) hΓ))) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z ↦ _ ≫ z) hcbδ) ?_
    exact zariskiRoute_comp_ΓRes S S' fX H e₂.right.unop

/-- **The underived Leray coherence across the square of topoi of [Stacks, Tag 07Q9].**  The two
routes `Γ(X'_Zar, u_{X'/S', *}f_{cris, *}ℋ) ⟶ Γ(Cris(X/S), ℋ)` agree: one is the comparison for
`u_{X'/S'}` followed by the comparison along `f_cris`, the other is the `2`-cell of the square
followed by the comparison for `f_{Zar}` and then the one for `u_{X/S}`.

This is `crisZariskiUnderivedCoherence_aux` with the two cocontinuous comparisons put back and
with the `2`-cell, whose inverse is the square, cancelled against it. -/
theorem crisZariskiUnderivedCoherence (H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (zariskiGlobalSectionsDirectImageIso S').hom.app
          ((crisDirectImage S S' fS fX hf).obj H) ≫
        (crisGlobalSectionsIso S S' fS fX hf).hom.app H =
      (zariskiGlobalSections S').map ((crisZariskiSquare S S' fS fX hf).hom.app H) ≫
        (zariskiPushforwardGlobalSectionsIso S S' fX).hom.app ((zariskiDirectImage S).obj H) ≫
          (zariskiGlobalSectionsDirectImageIso S).hom.app H := by
  have hsq : (crisZariskiSquare S S' fS fX hf).hom.app H ≫
      (crisZariskiCell S S' fS fX hf).app H = 𝟙 _ := by
    have h := NatTrans.congr_app (IsIso.inv_hom_id (crisZariskiCell S S' fS fX hf)) H
    rw [NatTrans.comp_app, NatTrans.id_app] at h
    exact h
  have hid : (zariskiGlobalSections S').map ((crisZariskiSquare S S' fS fX hf).hom.app H) ≫
      (zariskiGlobalSections S').map ((crisZariskiCell S S' fS fX hf).app H) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hsq, CategoryTheory.Functor.map_id]
  have h2 : (zariskiGlobalSections S').map ((crisZariskiCell S S' fS fX hf).app H) ≫
        (zariskiGlobalSectionsDirectImageIso S').hom.app
            ((crisDirectImage S S' fS fX hf).obj H) ≫
          (crisGlobalSectionsIso S S' fS fX hf).hom.app H =
      (zariskiPushforwardGlobalSectionsIso S S' fX).hom.app ((zariskiDirectImage S).obj H) ≫
        (zariskiGlobalSectionsDirectImageIso S).hom.app H := by
    rw [crisGlobalSectionsIso_hom_app_eq]
    refine Eq.trans ?_ (Eq.trans (congrArg (fun z ↦ z ≫
      (crisBigGlobalSectionsIso S S' fS fX hf H).hom)
        (crisZariskiUnderivedCoherence_aux S S' fS fX hf H)) ?_)
    · exact ((Category.assoc _ _ _).trans
        (congrArg (fun z ↦ (zariskiGlobalSections S').map
          ((crisZariskiCell S S' fS fX hf).app H) ≫ z) (Category.assoc _ _ _))).symm
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ ((zariskiPushforwardGlobalSectionsIso S S' fX).hom.app
              ((zariskiDirectImage S).obj H) ≫
            (zariskiGlobalSectionsDirectImageIso S).hom.app H) ≫ z)
          (crisBigGlobalSectionsIso S S' fS fX hf H).inv_hom_id).trans (Category.comp_id _))
  refine Eq.trans ?_ (congrArg (fun z ↦ (zariskiGlobalSections S').map
    ((crisZariskiSquare S S' fS fX hf).hom.app H) ≫ z) h2)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact ((congrArg (fun z ↦ z ≫ ((zariskiGlobalSectionsDirectImageIso S').hom.app
      ((crisDirectImage S S' fS fX hf).obj H) ≫
    (crisGlobalSectionsIso S S' fS fX hf).hom.app H)) hid).trans (Category.id_comp _)).symm

/-- **The coherence square of the four Leray comparisons of [Stacks, Tag 07QA] commutes.**  By
`...SmallSite.crisZariskiLerayCoherence_of_underived` the derived square reduces to the
underived one, which is `crisZariskiUnderivedCoherence`.

Nothing is carried: all five edges of the square are unconditional declarations of this
library. -/
theorem crisZariskiLerayCoherence
    [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}] :
    CrisZariskiLerayCoherence.{w, w'} S S' fS fX hf :=
  crisZariskiLerayCoherence_of_underived S S' fS fX hf
    (crisZariskiUnderivedCoherence S S' fS fX hf)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
