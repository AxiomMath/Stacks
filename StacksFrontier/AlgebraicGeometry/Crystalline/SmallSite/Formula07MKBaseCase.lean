module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKComma
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKPullback
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureDirectImage
public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanEvaluation

/-!
# The diagram of the base case of (07MK)

The base case of the displayed equation (07MK) of [Stacks, Tag 07MJ] is the *underived* formula

`(f_{cris, *}F)_{T'} = (T ⟶ T')_*(τ_{U/T, *}F_U)`

for an object `(U', T', δ')` of `Cris(X'/S')`.  Its left-hand side is a limit:
`Crystalline.GlobalCrystallineSituation.SmallSite.crisDirectImageObjObjIsoLimit` reads the
sections of `f_{cris, *}F` over an object as a limit over a comma category of the *big*
crystalline site, and `...pullbackCrystallineCommaEquivalence` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKComma.lean` identifies the
*small*-site comma category with `Cris(U/T)`.  This file cuts the big-site comma category down to
the small-site one and matches the **diagram**, not only the shape, so that the sections of
`f_{cris, *}F` over `(U', T', δ')` are `Γ(Cris(U/T), F_U)`, and these are the sections of
`(T ⟶ T')_*(τ_{U/T, *}F_U)` over the whole of `T'`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crisToBigRanIso`: **the two right Kan extensions of `f_{cris, *}` collapse into one** along
  `crisToBig`.
* `pullbackStructuredArrowEquivalence`: `Cris(U/T)` opposed is the structured-arrow category
  indexing the limit, the opposite of `...pullbackCrystallineCommaEquivalence`.
* `rightSide07MKUnderived`: **the right-hand side of the base case of (07MK)**,
  `F ↦ (T ⟶ T')_*(τ_{U/T, *}F_U)`, as a functor into abelian sheaves on `T'_Zar`.
* `FormulaBase07MK`: **the base case of (07MK) as a type of data**: an isomorphism of the two
  sides, natural in `F`.

## Main results

Each isomorphism below is an isomorphism of *functors* of the abelian sheaf `F`, with the
single-sheaf form its `CategoryTheory.Iso.app`.

* `crisDirectImageSectionsNatIsoLimitCrisToBig` and `crisDirectImageObjObjIsoLimitCrisToBig`:
  **the big-site comma category is cut down to the small-site one**: the sections of
  `f_{cris, *}F` over an object of `Cris(X'/S')` are a limit of `F` over
  `StructuredArrow (op (U', T', δ')) crisToBig.op`.
* `pullbackStructuredArrowEquivalence_functor_comp_proj`: **the diagram matches**, by `rfl`.
* `crisDirectImageSectionsNatIsoLimitPullbackCris`,
  `crisDirectImageObjObjIsoLimitPullbackCris` and `crisDirectImageSectionsRestrictionNatIso`:
  the sections of `f_{cris, *}F` over `(U', T', δ')` are the limit of
  `F ∘ pullbackSmallChangeBase` over `Cris(U/T)`, i.e. the global sections of the restriction of
  `F` to `Cris(U/T)`.
* `crisDirectImageSectionsNatIso` and `crisDirectImageGlobalSectionsPullbackIso`: the same with
  the formula's own pullback `F ↦ F_U`.
* `tauDirectImageSectionsTopNatIso` and `tauDirectImageObjTopIso`:
  `(τ_{X/S, *}F)(S) ≅ Γ(Cris(X/S), F)`: the sections of the direct image along the structure
  morphism over the whole base are crystalline global sections.
* `crisDirectImageSectionsNatIsoRightSideTop` and `crisDirectImageObjObjIsoRightSideTop`:
  **the base case of (07MK) on global sections of `T'`**: the sections of `f_{cris, *}F` over
  `(U', T', δ')` are the sections of `(T ⟶ T')_*(τ_{U/T, *}F_U)` over `T'`.

## References

* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07MK](https://stacks.math.columbia.edu/tag/07MK)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open DividedPowerScheme

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-! ### `(τ_{X/S, *}F)(S)` is `Γ(Cris(X/S), F)` -/

/-- **The sections of `τ_{X/S, *}F` over the whole of `S` are the crystalline global sections of
`F`.** -/
def tauDirectImageSectionsTopNatIso (T : GlobalCrystallineSituation.{u}) :
    tauDirectImage T ⋙
        (sheafSections (baseOpensTopology T) AddCommGrpCat.{u + 1}).obj (op ⊤) ≅
      globalSections T :=
  Functor.isoWhiskerLeft (zariskiDirectImage T)
      (Sheaf.ΓNatIsoSheafSections (opensTopology T) AddCommGrpCat.{u + 1}
        (isTerminalTop (α := T.X.Opens))).symm ≪≫
    zariskiGlobalSectionsDirectImageIso T

/-- `tauDirectImageSectionsTopNatIso` on a single abelian sheaf. -/
def tauDirectImageObjTopIso (T : GlobalCrystallineSituation.{u})
    (G : Sheaf (smallTopology T) AddCommGrpCat.{u + 1}) :
    ((tauDirectImage T).obj G).obj.obj (op ⊤) ≅ (globalSections T).obj G :=
  (tauDirectImageSectionsTopNatIso T).app G

include hf

/-! ### Cutting the big-site comma category down to the small one -/

/-- **The two right Kan extensions inside `f_{cris, *}` collapse into one along `crisToBig`.**
Right Kan extension along the composite
`Crystalline.GlobalCrystallineSituation.SmallSite.crisToBig` of the inclusion
`i_X : Cris(X/S) ⥤ CRIS(X/S)` and change of divided power base is the composite of the two right
Kan extensions of [Stacks, Tag 00XK]. -/
def crisToBigRanIso :
    (crisToBigOp S S' fS fX hf).ran (H := AddCommGrpCat.{u + 1}) ≅
      (CrystallineThickening.ι S).op.ran ⋙ (changeBase S S' fS fX hf).op.ran :=
  Functor.ranCompIsoOfAdjunctions AddCommGrpCat.{u + 1} (CrystallineThickening.ι S).op
    (changeBase S S' fS fX hf).op

/-- **The sections of `f_{cris, *}F` over an object `(U', T', δ')` of `Cris(X'/S')` are a limit of
`F` over the objects of `Cris(X/S)` lying over it**, namely over
`StructuredArrow (op (U', T', δ')) crisToBig.op`, the opposite of the comma category of
`crisToBig` over `(U', T', δ')`, naturally in `F`. -/
def crisDirectImageSectionsNatIsoLimitCrisToBig (A' : CrystallineThickening S') :
    crisDirectImage S S' fS fX hf ⋙
        (sheafSections (smallTopology S') AddCommGrpCat.{u + 1}).obj (op A') ≅
      sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (StructuredArrow.proj (op A'.obj) (crisToBig S S' fS fX hf).op) ⋙ lim :=
  Functor.isoWhiskerLeft (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (Functor.isoWhiskerRight (crisToBigRanIso S S' fS fX hf).symm
        ((evaluation ((Thickening S')ᵒᵖ) AddCommGrpCat.{u + 1}).obj (op A'.obj)) ≪≫
      Functor.ranObjNatIsoLimit AddCommGrpCat.{u + 1} (crisToBigOp S S' fS fX hf) (op A'.obj))

/-- `crisDirectImageSectionsNatIsoLimitCrisToBig` on a single abelian sheaf. -/
def crisDirectImageObjObjIsoLimitCrisToBig
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (A' : CrystallineThickening S') :
    ((crisDirectImage S S' fS fX hf).obj F).obj.obj (op A') ≅
      limit (StructuredArrow.proj (op A'.obj) (crisToBig S S' fS fX hf).op ⋙ F.obj) :=
  (crisDirectImageSectionsNatIsoLimitCrisToBig S S' fS fX hf A').app F

/-! ### The diagram over `Cris(U/T)` -/

/-- **The index category of the limit is `Cris(U/T)` opposed**: the opposite of
`Crystalline.GlobalCrystallineSituation.pullbackCrystallineCommaEquivalence`, read through
`CategoryTheory.costructuredArrowOpEquivalence`. -/
def pullbackStructuredArrowEquivalence (A' : CrystallineThickening S') :
    (CrystallineThickening (pullbackSituation S S' fS fX hf A'))ᵒᵖ ≌
      StructuredArrow (op A'.obj) (crisToBig S S' fS fX hf).op :=
  (pullbackCrystallineCommaEquivalence S S' fS fX hf A').op.trans
    (costructuredArrowOpEquivalence (crisToBig S S' fS fX hf) A'.obj)

/-- **The diagram matches the shape, on the nose.**  Transporting the projection of the
structured-arrow category along `pullbackStructuredArrowEquivalence` gives restriction along the
change-of-base functor `Cris(U/T) ⥤ Cris(X/S)` of [Stacks, Tag 07KL]. -/
theorem pullbackStructuredArrowEquivalence_functor_comp_proj (A' : CrystallineThickening S') :
    (pullbackStructuredArrowEquivalence S S' fS fX hf A').functor ⋙
        StructuredArrow.proj (op A'.obj) (crisToBig S S' fS fX hf).op =
      (pullbackSmallChangeBase S S' fS fX hf A').op :=
  rfl

/-- **The sections of `f_{cris, *}F` over `(U', T', δ')` are the limit over `Cris(U/T)` of the
restriction of `F` along `Cris(U/T) ⥤ Cris(X/S)`**, naturally in `F`. -/
def crisDirectImageSectionsNatIsoLimitPullbackCris (A' : CrystallineThickening S') :
    crisDirectImage S S' fS fX hf ⋙
        (sheafSections (smallTopology S') AddCommGrpCat.{u + 1}).obj (op A') ≅
      sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (pullbackSmallChangeBase S S' fS fX hf A').op ⋙ lim :=
  crisDirectImageSectionsNatIsoLimitCrisToBig S S' fS fX hf A' ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
      (Functor.isoWhiskerLeft
        ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (StructuredArrow.proj (op A'.obj) (crisToBig S S' fS fX hf).op))
        (Functor.Initial.limIso
          (pullbackStructuredArrowEquivalence S S' fS fX hf A').functor).symm)

/-- `crisDirectImageSectionsNatIsoLimitPullbackCris` on a single abelian sheaf. -/
def crisDirectImageObjObjIsoLimitPullbackCris
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (A' : CrystallineThickening S') :
    ((crisDirectImage S S' fS fX hf).obj F).obj.obj (op A') ≅
      limit ((pullbackSmallChangeBase S S' fS fX hf A').op ⋙ F.obj) :=
  (crisDirectImageSectionsNatIsoLimitPullbackCris S S' fS fX hf A').app F

/-- **The sections of `f_{cris, *}F` over `(U', T', δ')` are the global sections on `Cris(U/T)` of
the restriction of `F` along `Cris(U/T) ⥤ Cris(X/S)`**, naturally in `F`. -/
def crisDirectImageSectionsRestrictionNatIso (A' : CrystallineThickening S') :
    crisDirectImage S S' fS fX hf ⋙
        (sheafSections (smallTopology S') AddCommGrpCat.{u + 1}).obj (op A') ≅
      pullbackAbelianRestriction S S' fS fX hf A' ⋙
        globalSections (pullbackSituation S S' fS fX hf A') :=
  crisDirectImageSectionsNatIsoLimitPullbackCris S S' fS fX hf A' ≪≫
    Functor.isoWhiskerLeft (pullbackAbelianRestriction S S' fS fX hf A')
      (Sheaf.ΓNatIsoLim (smallTopology (pullbackSituation S S' fS fX hf A'))
        AddCommGrpCat.{u + 1}).symm

/-- **The sections of `f_{cris, *}F` over `(U', T', δ')` are `Γ(Cris(U/T), F_U)`**, naturally in
`F`, for the pullback `F ↦ F_U` the displayed equation (07MK) of [Stacks, Tag 07MJ] is written
with. -/
def crisDirectImageSectionsNatIso (A' : CrystallineThickening S') :
    crisDirectImage S S' fS fX hf ⋙
        (sheafSections (smallTopology S') AddCommGrpCat.{u + 1}).obj (op A') ≅
      pullbackAbelianSheaf S S' fS fX hf A' ⋙
        globalSections (pullbackSituation S S' fS fX hf A') :=
  crisDirectImageSectionsRestrictionNatIso S S' fS fX hf A' ≪≫
    Functor.isoWhiskerRight
      (pullbackAbelianSheafIsoPullbackAbelianRestriction S S' fS fX hf A').symm
      (globalSections (pullbackSituation S S' fS fX hf A'))

/-- `crisDirectImageSectionsNatIso` on a single abelian sheaf. -/
def crisDirectImageGlobalSectionsPullbackIso
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (A' : CrystallineThickening S') :
    ((crisDirectImage S S' fS fX hf).obj F).obj.obj (op A') ≅
      (globalSections (pullbackSituation S S' fS fX hf A')).obj
        ((pullbackAbelianSheaf S S' fS fX hf A').obj F) :=
  (crisDirectImageSectionsNatIso S S' fS fX hf A').app F

/-! ### The base case of (07MK) -/

/-- **The right-hand side of the base case of the displayed equation (07MK) of
[Stacks, Tag 07MJ]**, `F ↦ (T ⟶ T')_*(τ_{U/T, *}F_U)`: pull `F` back to `Cris(U/T)`, push it down
to `T_Zar` along the structure morphism `τ_{U/T}`, and push that along the second projection
`T = S ×_{S'} T' ⟶ T'`.  This is `...rightSide07MK` with the three derived functors replaced by
the functors they derive. -/
def rightSide07MKUnderived (A' : CrystallineThickening S') :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Opens.grothendieckTopology A'.obj.thickening.target.scheme)
        AddCommGrpCat.{u + 1} :=
  pullbackAbelianSheaf S S' fS fX hf A' ⋙ pullbackTauDirectImage S S' fS fX hf A' ⋙
    spaceZariskiPushforward (pullback.snd fS A'.obj.toBase).hom.base

/-- **The base case of the displayed equation (07MK) of [Stacks, Tag 07MJ] at one object
`(U', T', δ')`, as a type of data**: an isomorphism

`(f_{cris, *}F)_{T'} ≅ (T ⟶ T')_*(τ_{U/T, *}F_U)`

of abelian sheaves on the small Zariski site of `T'`, natural in the abelian sheaf `F` on
`Cris(X/S)`. -/
abbrev FormulaBase07MK (A' : CrystallineThickening S') : Type _ :=
  crisDirectImage S S' fS fX hf ⋙ CrystallineThickening.abelianAmbientRestriction A' ≅
    rightSide07MKUnderived S S' fS fX hf A'

/-- **The base case of the displayed equation (07MK) of [Stacks, Tag 07MJ], read on the sections
over the whole of `T'`**: the sections of `f_{cris, *}F` over an object `(U', T', δ')` of
`Cris(X'/S')` are the sections of `(T ⟶ T')_*(τ_{U/T, *}F_U)` over `T'`, naturally in `F`. -/
def crisDirectImageSectionsNatIsoRightSideTop (A' : CrystallineThickening S') :
    crisDirectImage S S' fS fX hf ⋙
        (sheafSections (smallTopology S') AddCommGrpCat.{u + 1}).obj (op A') ≅
      rightSide07MKUnderived S S' fS fX hf A' ⋙
        (sheafSections (Opens.grothendieckTopology A'.obj.thickening.target.scheme)
          AddCommGrpCat.{u + 1}).obj (op ⊤) :=
  crisDirectImageSectionsNatIso S S' fS fX hf A' ≪≫
    Functor.isoWhiskerLeft (pullbackAbelianSheaf S S' fS fX hf A')
      (tauDirectImageSectionsTopNatIso (pullbackSituation S S' fS fX hf A')).symm

/-- `crisDirectImageSectionsNatIsoRightSideTop` on a single abelian sheaf. -/
def crisDirectImageObjObjIsoRightSideTop
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (A' : CrystallineThickening S') :
    ((crisDirectImage S S' fS fX hf).obj F).obj.obj (op A') ≅
      ((rightSide07MKUnderived S S' fS fX hf A').obj F).obj.obj (op ⊤) :=
  (crisDirectImageSectionsNatIsoRightSideTop S S' fS fX hf A').app F

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
