module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareLimit
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKInjectives

/-!
# The comma category of change of base over `(U', T', δ')` is the situation `U/T`

The remark [Stacks, Tag 07MJ] states the displayed equation (07MK) with the hint that `Cris(U/T)`
is the localization of `Cris(X/S)` at `f_cris^{-1}h_{(U', T', δ')}`.  For the base case of the
equation — the underived formula `(f_{cris, *}F)_{T'} = (T ⟶ T')_*(τ_{U/T, *}F_U)` — what that
hint is used for is the identification of a **comma category**, not of a slice topos: the sections
of `f_{cris, *}F` over an object `(U', T', δ')` are a limit over the category of objects of
`CRIS(X/S)` equipped with a morphism to `(U', T', δ')` over `S ⟶ S'`
(`...SmallSite.crisDirectImageObjObjIsoLimit`), and that category is `CRIS(U/T)`.

This file proves exactly that, and its small-site form.  Nothing here is about a slice topos, so
[Stacks, Tag 0791] is not involved; the content is the universal property of the two fibre
products `T = S ×_{S'} T'` (taken in divided power schemes, [Stacks, Tag 07ME]) and
`U = X ×_{X'} U'` (taken in schemes).

## How the two directions go

Change of divided power base leaves the underlying divided power thickening alone and composes
the two structure morphisms.  So an object of the comma category is a thickening `V ↪ Z` together
with `Z ⟶ S`, `V ⟶ X`, and a morphism `(Z ⟶ T', V ⟶ U')` of thickenings over `S ⟶ S'`; the two
universal properties turn the pairs `(Z ⟶ S, Z ⟶ T')` and `(V ⟶ X, V ⟶ U')` into single maps
`Z ⟶ T` and `V ⟶ U`, which is an object of `CRIS(U/T)`.  In the other direction one composes with
the two first projections, which is change of divided power base along `T ⟶ S`.

The one point needing care is the compatibility `V ↪ Z ⟶ T = V ⟶ U ⟶ T₀ ↪ T` of an object of
`CRIS(U/T)`.  It cannot be checked by composing with the projections of `T`, the underlying
scheme of a divided power fibre product being only a closed subscheme of the fibre product of the
underlying schemes.  Instead it is read on *closed fibres*, where `T₀ = S₀ ×_{S'₀} T'₀` is an
honest fibre product of schemes ([Stacks, Tag 07ME],
`...DividedPowerScheme.closedFiberPullbackComparison_isIso`): the two projection identities
`...pullbackToClosedFiber_comp_fst` and `..._comp_snd` then do the work, and the compatibility
follows because `T₀ ↪ T` is a monomorphism.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `pullbackChangeBase` — change of divided power base along `T = S ×_{S'} T' ⟶ S`, the functor
  `CRIS(U/T) ⥤ CRIS(X/S)`; `SmallSite.pullbackSmallChangeBase` is its small-site form.
* `pullbackCommaProj` — the structure morphism to `(U', T', δ')` an object of `CRIS(U/T)` carries,
  through the second projections of the two fibre products.
* `pullbackToComma` — the functor `CRIS(U/T) ⥤ (CRIS(X/S) ↓ (U', T', δ'))` built from the two.
* `pullbackCommaObj` — the object of `CRIS(U/T)` attached to an object of the comma category, by
  the two universal properties.
* `pullbackThickeningCommaEquivalence` — **the comma category of change of divided power base
  over `(U', T', δ')` is `CRIS(U/T)`.**
* `pullbackCrisToComma` and `pullbackCrystallineCommaEquivalence` — **the same for the small
  crystalline sites**: the comma category of `...crisToBig` over `(U', T', δ')` is `Cris(U/T)`.
  `crisToBig` is `ι ⋙ changeBase`, which is `smallChangeBase ⋙ ι` whenever `X ⟶ X'` is an open
  immersion so that the small-site change of base of [Stacks, Tag 07KL] exists; in the situation
  of (07MK) it need not be, and `U ⟶ X` is the open immersion instead.

## Main results

* `SchemeThickening.toClosedFiber_naturality` — the identification of the thickened scheme with
  the closed fibre of the ambient scheme is natural in a square of thickenings.
* `toClosedFiber_comp_closedFiberMap_of_over_base` — the compatibility `U ↪ T ⟶ S` of an object of
  `CRIS(X/S)` read on closed fibres.

## Implementation notes

The structure fields of an object of `CRIS(U/T)` are morphisms into
`(pullbackSituation S S' fS fX hf A').S` and `....X`, which are the two fibre products but only
after unfolding `pullbackSituation`, a plain definition.  Tactics work at reducible transparency
and so see the unreduced projections; `rw` then fails on goals that are perfectly well typed.  So
every nontrivial field condition below is factored out as a lemma whose statement mentions the
fibre products directly and quantifies over the structure morphisms, and the definitions apply
those lemmas — the defeq is then discharged by elaboration, which is not transparency-bound.

## What is and is not proved

No `@[stacks]` attribute is placed here; (07MK) itself is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKProof.lean`,
which uses this equivalence.  It is one of the two inputs the proof needs, the other being
`...SmallSite.pullbackAbelianSheafIsoPullbackAbelianRestriction`.  Nothing here asserts that
`Cris(U/T)` is a localization of a topos, and nothing here identifies the limit of
`...SmallSite.crisDirectImageObjObjIsoLimit` with the right-hand side of (07MK) — that step
additionally has to match the *diagram*, not only the shape it is indexed on, and it is carried
out in `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKBaseCase.lean` on the
strength of `pullbackCrystallineCommaEquivalence` below.

## References

* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07MK](https://stacks.math.columbia.edu/tag/07MK)
* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline

open DividedPowerScheme

/-! ### Thickenings read on closed fibres -/

namespace SchemeThickening

/-- **The identification of the thickened scheme with the closed fibre of the ambient scheme is
natural.**  Given a map `s` of thickened schemes over a divided power map `t` of ambient schemes,
the two routes `U ⟶ U' ≅ T'₀` and `U ≅ T₀ ⟶ T'₀` agree: both become the diagonal `U ⟶ T'` of the
square after the monomorphism `T'₀ ↪ T'`. -/
theorem toClosedFiber_naturality {D E : SchemeThickening.{u}} (s : D.source ⟶ E.source)
    (t : D.target ⟶ E.target) (hst : D.immersion ≫ t.hom = s ≫ E.immersion) :
    D.toClosedFiber ≫ closedFiberMap t = s ≫ E.toClosedFiber := by
  rw [← cancel_mono (closedFiberι E.target), Category.assoc, Category.assoc,
    closedFiberMap_comp_closedFiberι, toClosedFiber_comp_closedFiberι_assoc,
    toClosedFiber_comp_closedFiberι, hst]

end SchemeThickening

namespace GlobalCrystallineSituation

/-- **The compatibility `U ↪ T ⟶ S` of an object of `CRIS(X/S)`, read on closed fibres**: the
identification of `U` with `T₀` followed by `T₀ ⟶ S₀` is the structure morphism `U ⟶ X ⟶ S₀`.
This is `Thickening.over_base` with the monomorphism `S₀ ↪ S` cancelled, stated for the two
structure morphisms separately so that it applies to an object of `CRIS(X/S)` however its
structure morphisms are presented. -/
theorem toClosedFiber_comp_closedFiberMap_of_over_base {S : GlobalCrystallineSituation.{u}}
    {D : SchemeThickening.{u}} (b : D.target ⟶ S.S) (x : D.source ⟶ S.X)
    (hob : D.immersion ≫ b.hom = x ≫ sourceToBase S) :
    D.toClosedFiber ≫ closedFiberMap b = x ≫ S.toClosedFiber := by
  rw [← cancel_mono (closedFiberι S.S), Category.assoc, Category.assoc,
    closedFiberMap_comp_closedFiberι, SchemeThickening.toClosedFiber_comp_closedFiberι_assoc]
  exact hob

/-! ### The comma category of change of base over an object -/

section Auxiliary

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (A' : CrystallineThickening S')

/-- The second projection of `T = S ×_{S'} T'` carries an object of `CRIS(U/T)` over `S ⟶ S'`:
one leg of the compatibility of `pullbackCommaProj`. -/
theorem snd_comp_toBase_of_pullback {Z : DividedPowerScheme.{u}}
    (tb : Z ⟶ pullbackBase S S' fS A') :
    (tb ≫ pullback.snd fS A'.obj.toBase) ≫ A'.obj.toBase =
      (tb ≫ pullback.fst fS A'.obj.toBase) ≫ fS := by
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- The second projection of `U = X ×_{X'} U'` carries an object of `CRIS(U/T)` over `X ⟶ X'`:
the other leg of the compatibility of `pullbackCommaProj`. -/
theorem snd_comp_toX_of_pullback {V : Scheme.{u}} (tx : V ⟶ pullbackSource S S' fX A') :
    (tx ≫ pullback.snd fX A'.obj.toX) ≫ A'.obj.toX =
      (tx ≫ pullback.fst fX A'.obj.toX) ≫ fX := by
  rw [Category.assoc, Category.assoc, pullback.condition]

variable (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

/-- **The two second projections of an object of `CRIS(U/T)` form a morphism of thickenings into
`(U', T', δ')`.**  The compatibility is `Thickening.over_base` for the object, composed with the
second projection of `T = S ×_{S'} T'` and read on closed fibres, where
`...pullbackToClosedFiber_comp_snd` identifies `T₀ ⟶ T'₀` with `U ⟶ U' ≅ T'₀`. -/
theorem immersion_comp_snd_of_pullback {D : SchemeThickening.{u}}
    (tb : D.target ⟶ pullbackBase S S' fS A') (tx : D.source ⟶ pullbackSource S S' fX A')
    (hob : D.immersion ≫ tb.hom =
      tx ≫ pullbackToClosedFiber S S' fS fX hf A' ≫ closedFiberι (pullbackBase S S' fS A')) :
    D.immersion ≫ (tb ≫ pullback.snd fS A'.obj.toBase).hom =
      (tx ≫ pullback.snd fX A'.obj.toX) ≫ A'.obj.thickening.immersion := by
  rw [DividedPowerScheme.Hom.comp_hom, ← Category.assoc, hob, Category.assoc, Category.assoc,
    ← closedFiberMap_comp_closedFiberι, pullbackToClosedFiber_comp_snd_assoc,
    SchemeThickening.toClosedFiber_comp_closedFiberι, Category.assoc]

/-- **The two universal maps attached to an object of the comma category agree on closed
fibres.**  The closed fibre of `T = S ×_{S'} T'` is the fibre product `S₀ ×_{S'₀} T'₀` of the
closed fibres, [Stacks, Tag 07ME], so the two maps may be compared projection by projection: on
the first, by `toClosedFiber_comp_closedFiberMap_of_over_base` for the object of `CRIS(X/S)`; on
the second, by `SchemeThickening.toClosedFiber_naturality` for the morphism of thickenings. -/
theorem lift_comp_pullbackToClosedFiber {D : SchemeThickening.{u}}
    (tb : D.target ⟶ A'.obj.thickening.target) (s : D.source ⟶ A'.obj.thickening.source)
    (b : D.target ⟶ S.S) (x : D.source ⟶ S.X) (hb : b ≫ fS = tb ≫ A'.obj.toBase)
    (hx : x ≫ fX = s ≫ A'.obj.toX)
    (himm : D.immersion ≫ tb.hom = s ≫ A'.obj.thickening.immersion)
    (hob : D.immersion ≫ b.hom = x ≫ sourceToBase S) :
    pullback.lift x s hx ≫ pullbackToClosedFiber S S' fS fX hf A' =
      D.toClosedFiber ≫ closedFiberMap (pullback.lift b tb hb) := by
  have := closedFiberPullbackComparison_isIso fS A'.obj.toBase
  rw [← cancel_mono (closedFiberPullbackComparison fS A'.obj.toBase)]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, closedFiberPullbackComparison_fst]
    rw [pullbackToClosedFiber_comp_fst, ← closedFiberMap_comp, pullback.lift_fst,
      pullbackSourceToClosedFiber, pullback.lift_fst_assoc]
    exact (toClosedFiber_comp_closedFiberMap_of_over_base b x hob).symm
  · simp only [Category.assoc, closedFiberPullbackComparison_snd]
    rw [pullbackToClosedFiber_comp_snd, ← closedFiberMap_comp, pullback.lift_snd,
      pullback.lift_snd_assoc]
    exact (SchemeThickening.toClosedFiber_naturality s tb himm).symm

/-- **The compatibility `V ↪ Z ⟶ T = V ⟶ U ⟶ T₀ ↪ T` for the object of `CRIS(U/T)` attached to an
object of the comma category.**  By `lift_comp_pullbackToClosedFiber` the two routes agree after
the closed fibre `T₀` is reached, and `T₀ ↪ T` is a closed immersion. -/
theorem over_base_of_lift {D : SchemeThickening.{u}}
    (tb : D.target ⟶ A'.obj.thickening.target) (s : D.source ⟶ A'.obj.thickening.source)
    (b : D.target ⟶ S.S) (x : D.source ⟶ S.X) (hb : b ≫ fS = tb ≫ A'.obj.toBase)
    (hx : x ≫ fX = s ≫ A'.obj.toX)
    (himm : D.immersion ≫ tb.hom = s ≫ A'.obj.thickening.immersion)
    (hob : D.immersion ≫ b.hom = x ≫ sourceToBase S) :
    D.immersion ≫ (pullback.lift b tb hb).hom =
      pullback.lift x s hx ≫ pullbackToClosedFiber S S' fS fX hf A' ≫
        closedFiberι (pullbackBase S S' fS A') := by
  rw [← Category.assoc, lift_comp_pullbackToClosedFiber S S' fS fX A' hf tb s b x hb hx himm hob,
    Category.assoc, closedFiberMap_comp_closedFiberι,
    SchemeThickening.toClosedFiber_comp_closedFiberι_assoc]

end Auxiliary

section Comma

open DividedPowerScheme

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)
  (A' : CrystallineThickening S')

include hf

/-- **Change of divided power base along `T = S ×_{S'} T' ⟶ S`**, the functor
`CRIS(U/T) ⥤ CRIS(X/S)` of [Stacks, Tag 07IC] for the situation `U/T` of [Stacks, Tag 07MJ].  Its
small-site form is `Crystalline.GlobalCrystallineSituation.SmallSite.pullbackSmallChangeBase`. -/
abbrev pullbackChangeBase :
    Thickening (pullbackSituation S S' fS fX hf A') ⥤ Thickening S :=
  changeBase (pullbackSituation S S' fS fX hf A') S (pullback.fst fS A'.obj.toBase)
    (pullback.fst fX A'.obj.toX) (pullbackSituation_comm S S' fS fX hf A')

/-- **The structure morphism to `(U', T', δ')` carried by an object of `CRIS(U/T)`**: an object
`(V, Z, δ)` of `CRIS(U/T)` maps to `(U', T', δ')` over `S ⟶ S'` through the *second* projections
of `T = S ×_{S'} T'` and `U = X ×_{X'} U'`. -/
def pullbackCommaProj (B : Thickening (pullbackSituation S S' fS fX hf A')) :
    (changeBase S S' fS fX hf).obj ((pullbackChangeBase S S' fS fX hf A').obj B) ⟶ A'.obj where
  sourceHom := B.toX ≫ pullback.snd fX A'.obj.toX
  targetHom := B.toBase ≫ pullback.snd fS A'.obj.toBase
  immersion_naturality :=
    immersion_comp_snd_of_pullback S S' fS fX A' hf B.toBase B.toX B.over_base
  base_naturality := snd_comp_toBase_of_pullback S S' fS A' B.toBase
  toX_naturality := snd_comp_toX_of_pullback S S' fX A' B.toX

/-- **The functor `CRIS(U/T) ⥤ (CRIS(X/S) ↓ (U', T', δ'))`**: change of divided power base along
`T ⟶ S`, together with the structure morphism to `(U', T', δ')` of `pullbackCommaProj`. -/
def pullbackToComma :
    Thickening (pullbackSituation S S' fS fX hf A') ⥤
      CostructuredArrow (changeBase S S' fS fX hf) A'.obj where
  obj B := CostructuredArrow.mk (pullbackCommaProj S S' fS fX hf A' B)
  map {B C} k :=
    CostructuredArrow.homMk ((pullbackChangeBase S S' fS fX hf A').map k)
      (Thickening.Hom.ext
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ pullback.snd fX A'.obj.toX) k.toX_naturality))
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ pullback.snd fS A'.obj.toBase) k.base_naturality)))
  map_id B := by apply CostructuredArrow.hom_ext; simp
  map_comp k l := by apply CostructuredArrow.hom_ext; simp

/-- The comma category sees only the components of a morphism of `CRIS(U/T)`, which change of
divided power base leaves untouched. -/
instance faithful_pullbackToComma : (pullbackToComma S S' fS fX hf A').Faithful where
  map_injective {_ _} {f g} e := by
    have hs : f.sourceHom = g.sourceHom := congrArg (fun m ↦ m.left.sourceHom) e
    have ht : f.targetHom = g.targetHom := congrArg (fun m ↦ m.left.targetHom) e
    exact Thickening.Hom.ext hs ht

/-- **A morphism of the comma category comes from a morphism of `CRIS(U/T)`.**  Its two components
already are maps of the underlying thickening; what has to be produced is their compatibility with
the structure morphisms to `T` and to `U`, and by the universal properties that is the pair
consisting of the compatibility over `S` resp. `X` — which is the morphism of `CRIS(X/S)` — and
the compatibility over `T'` resp. `U'` — which is the commuting triangle of the comma category. -/
instance full_pullbackToComma : (pullbackToComma S S' fS fX hf A').Full where
  map_surjective {B C} m :=
    ⟨{ sourceHom := m.left.sourceHom
       targetHom := m.left.targetHom
       immersion_naturality := m.left.immersion_naturality
       base_naturality := pullback.hom_ext
          ((Category.assoc _ _ _).trans m.left.base_naturality)
          ((Category.assoc _ _ _).trans
            (congrArg (fun p ↦ p.targetHom) (CostructuredArrow.w m)))
       toX_naturality := pullback.hom_ext
          ((Category.assoc _ _ _).trans m.left.toX_naturality)
          ((Category.assoc _ _ _).trans
            (congrArg (fun p ↦ p.sourceHom) (CostructuredArrow.w m))) },
      by apply CostructuredArrow.hom_ext; exact Thickening.Hom.ext rfl rfl⟩

/-- **The object of `CRIS(U/T)` attached to an object of the comma category**: the two universal
properties turn the pair of maps to `S` and to `T'` into a divided power map `Z ⟶ T` and the pair
of maps to `X` and to `U'` into a map `V ⟶ U`.  The compatibility
`V ↪ Z ⟶ T = V ⟶ U ⟶ T₀ ↪ T` is `over_base_of_lift`. -/
def pullbackCommaObj (Z : CostructuredArrow (changeBase S S' fS fX hf) A'.obj) :
    Thickening (pullbackSituation S S' fS fX hf A') where
  thickening := Z.left.thickening
  toBase := pullback.lift Z.left.toBase Z.hom.targetHom Z.hom.base_naturality.symm
  toX := pullback.lift Z.left.toX Z.hom.sourceHom Z.hom.toX_naturality.symm
  over_base :=
    over_base_of_lift S S' fS fX A' hf Z.hom.targetHom Z.hom.sourceHom Z.left.toBase Z.left.toX
      Z.hom.base_naturality.symm Z.hom.toX_naturality.symm Z.hom.immersion_naturality
      Z.left.over_base

/-- Every object of the comma category is in the image of `pullbackToComma`: composing the two
universal maps of `pullbackCommaObj` with the first projections returns the object one started
from, by `CategoryTheory.Limits.pullback.lift_fst`, and with the second projections returns its
structure morphism to `(U', T', δ')`, by `pullback.lift_snd`.  So the comparison isomorphism is
the identity on the underlying thickening. -/
instance essSurj_pullbackToComma : (pullbackToComma S S' fS fX hf A').EssSurj where
  mem_essImage Z :=
    ⟨pullbackCommaObj S S' fS fX hf A' Z,
      ⟨CostructuredArrow.isoMk
        { hom :=
            { sourceHom := 𝟙 _
              targetHom := 𝟙 _
              immersion_naturality :=
                (Category.comp_id _).trans (Category.id_comp _).symm
              base_naturality := (Category.id_comp _).trans (pullback.lift_fst _ _ _).symm
              toX_naturality := (Category.id_comp _).trans (pullback.lift_fst _ _ _).symm }
          inv :=
            { sourceHom := 𝟙 _
              targetHom := 𝟙 _
              immersion_naturality :=
                (Category.comp_id _).trans (Category.id_comp _).symm
              base_naturality := (Category.id_comp _).trans (pullback.lift_fst _ _ _)
              toX_naturality := (Category.id_comp _).trans (pullback.lift_fst _ _ _) }
          hom_inv_id := Thickening.Hom.ext (Category.id_comp _) (Category.id_comp _)
          inv_hom_id := Thickening.Hom.ext (Category.id_comp _) (Category.id_comp _) }
        (Thickening.Hom.ext ((Category.id_comp _).trans (pullback.lift_snd _ _ _).symm)
          ((Category.id_comp _).trans (pullback.lift_snd _ _ _).symm))⟩⟩

/-- **The comma category of change of divided power base over `(U', T', δ')` is `CRIS(U/T)`.**

This is the identification the base case of the displayed equation (07MK) of [Stacks, Tag 07MJ]
needs, read at the level of *categories*: by `...SmallSite.crisDirectImageObjObjIsoLimit` the
sections of `f_{cris, *}F` over `(U', T', δ')` are a limit over this comma category, and the
right-hand side of (07MK) is written over `Cris(U/T)`.  It is a statement about a comma category
and not about a slice topos, so it does not depend on [Stacks, Tag 0791]; it is the universal
property of `T = S ×_{S'} T'` and `U = X ×_{X'} U'`. -/
def pullbackThickeningCommaEquivalence :
    Thickening (pullbackSituation S S' fS fX hf A') ≌
      CostructuredArrow (changeBase S S' fS fX hf) A'.obj :=
  haveI : (pullbackToComma S S' fS fX hf A').IsEquivalence := {}
  (pullbackToComma S S' fS fX hf A').asEquivalence

/-! ### The small crystalline sites -/

/-- **The functor `Cris(U/T) ⥤ (Cris(X/S) ↓ (U', T', δ'))`**, the small-site form of
`pullbackToComma`: change of divided power base along `T ⟶ S`, which is
`...SmallSite.pullbackSmallChangeBase`, together with the structure morphism to `(U', T', δ')` of
`pullbackCommaProj`.

The comma category is taken over `...crisToBig = ι ⋙ changeBase`, which is the functor
`Cris(X/S) ⥤ CRIS(X'/S')` reading an object of the small crystalline site of `X/S` as an object of
the big crystalline site of `X'/S'`.  It is `smallChangeBase ⋙ ι` whenever `X ⟶ X'` is an open
immersion, so that the small-site change of base of [Stacks, Tag 07KL] exists; in the situation of
[Stacks, Tag 07MJ] it need not be, and `U = X ×_{X'} U' ⟶ X` is the open immersion instead. -/
def pullbackCrisToComma :
    CrystallineThickening (pullbackSituation S S' fS fX hf A') ⥤
      CostructuredArrow (SmallSite.crisToBig S S' fS fX hf) A'.obj where
  obj B :=
    CostructuredArrow.mk (S := SmallSite.crisToBig S S' fS fX hf)
      (Y := (SmallSite.pullbackSmallChangeBase S S' fS fX hf A').obj B)
      (pullbackCommaProj S S' fS fX hf A' B.obj)
  map k :=
    CostructuredArrow.homMk ((SmallSite.pullbackSmallChangeBase S S' fS fX hf A').map k)
      (Thickening.Hom.ext
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ pullback.snd fX A'.obj.toX) k.hom.toX_naturality))
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ pullback.snd fS A'.obj.toBase) k.hom.base_naturality)))
  map_id B := CostructuredArrow.hom_ext _ _
    ((SmallSite.pullbackSmallChangeBase S S' fS fX hf A').map_id B)
  map_comp k l := CostructuredArrow.hom_ext _ _
    ((SmallSite.pullbackSmallChangeBase S S' fS fX hf A').map_comp k l)

/-- As on the big sites, the comma category sees only the two components of a morphism. -/
instance faithful_pullbackCrisToComma : (pullbackCrisToComma S S' fS fX hf A').Faithful where
  map_injective {_ _} {f g} e := by
    have hs : f.hom.sourceHom = g.hom.sourceHom := congrArg (fun m ↦ m.left.hom.sourceHom) e
    have ht : f.hom.targetHom = g.hom.targetHom := congrArg (fun m ↦ m.left.hom.targetHom) e
    exact ObjectProperty.hom_ext _ (Thickening.Hom.ext hs ht)

/-- Fullness is the big-site argument again: the small crystalline sites are full subcategories of
the big crystalline categories, so a morphism of the comma category has the same two components,
and the universal properties turn their two compatibilities into one. -/
instance full_pullbackCrisToComma : (pullbackCrisToComma S S' fS fX hf A').Full where
  map_surjective m :=
    ⟨ObjectProperty.homMk
      { sourceHom := m.left.hom.sourceHom
        targetHom := m.left.hom.targetHom
        immersion_naturality := m.left.hom.immersion_naturality
        base_naturality := pullback.hom_ext
            ((Category.assoc _ _ _).trans m.left.hom.base_naturality)
            ((Category.assoc _ _ _).trans
              (congrArg (fun p ↦ p.targetHom) (CostructuredArrow.w m)))
        toX_naturality := pullback.hom_ext
            ((Category.assoc _ _ _).trans m.left.hom.toX_naturality)
            ((Category.assoc _ _ _).trans
              (congrArg (fun p ↦ p.sourceHom) (CostructuredArrow.w m))) },
      CostructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _ (Thickening.Hom.ext rfl rfl))⟩

/-- **The object of `CRIS(U/T)` attached to an object of the small comma category is again an
object of the small crystalline site.**  Its structure morphism to `U` composed with the open
immersion `U = X ×_{X'} U' ⟶ X` is the structure morphism to `X` of the object of `Cris(X/S)` one
started from, which is an open immersion; and an open immersion that becomes one after
composition with an open immersion is one. -/
theorem isCrystalline_pullbackCommaObj
    (Z : CostructuredArrow (SmallSite.crisToBig S S' fS fX hf) A'.obj) :
    Thickening.IsCrystalline (pullbackCommaObj S S' fS fX hf A'
      (CostructuredArrow.mk (S := changeBase S S' fS fX hf) Z.hom)) := by
  have : IsOpenImmersion (pullback.fst fX A'.obj.toX) :=
    isOpenImmersion_pullbackSituationToX S S' fX A'
  have hz : IsOpenImmersion Z.left.obj.toX := Z.left.property
  change IsOpenImmersion
    (pullback.lift Z.left.obj.toX Z.hom.sourceHom Z.hom.toX_naturality.symm)
  have e : pullback.lift Z.left.obj.toX Z.hom.sourceHom Z.hom.toX_naturality.symm ≫
      pullback.fst fX A'.obj.toX = Z.left.obj.toX := pullback.lift_fst _ _ _
  have : IsOpenImmersion
      (pullback.lift Z.left.obj.toX Z.hom.sourceHom Z.hom.toX_naturality.symm ≫
        pullback.fst fX A'.obj.toX) := by rw [e]; exact hz
  exact IsOpenImmersion.of_comp _ (pullback.fst fX A'.obj.toX)

/-- Every object of the small comma category is in the image of `pullbackCrisToComma`: the
comparison isomorphism is the big-site one, which is the identity on the underlying thickening. -/
instance essSurj_pullbackCrisToComma : (pullbackCrisToComma S S' fS fX hf A').EssSurj where
  mem_essImage Z :=
    ⟨⟨pullbackCommaObj S S' fS fX hf A'
        (CostructuredArrow.mk (S := changeBase S S' fS fX hf) Z.hom),
      isCrystalline_pullbackCommaObj S S' fS fX hf A' Z⟩,
      ⟨CostructuredArrow.isoMk
        { hom := ObjectProperty.homMk
            { sourceHom := 𝟙 _
              targetHom := 𝟙 _
              immersion_naturality :=
                (Category.comp_id _).trans (Category.id_comp _).symm
              base_naturality := (Category.id_comp _).trans (pullback.lift_fst _ _ _).symm
              toX_naturality := (Category.id_comp _).trans (pullback.lift_fst _ _ _).symm }
          inv := ObjectProperty.homMk
            { sourceHom := 𝟙 _
              targetHom := 𝟙 _
              immersion_naturality :=
                (Category.comp_id _).trans (Category.id_comp _).symm
              base_naturality := (Category.id_comp _).trans (pullback.lift_fst _ _ _)
              toX_naturality := (Category.id_comp _).trans (pullback.lift_fst _ _ _) }
          hom_inv_id := ObjectProperty.hom_ext _
            (Thickening.Hom.ext (Category.id_comp _) (Category.id_comp _))
          inv_hom_id := ObjectProperty.hom_ext _
            (Thickening.Hom.ext (Category.id_comp _) (Category.id_comp _)) }
        (Thickening.Hom.ext ((Category.id_comp _).trans (pullback.lift_snd _ _ _).symm)
          ((Category.id_comp _).trans (pullback.lift_snd _ _ _).symm))⟩⟩

/-- **The comma category of `Cris(X/S) ⥤ CRIS(X'/S')` over `(U', T', δ')` is `Cris(U/T)`** — the
hint of [Stacks, Tag 07MJ] read at the level of *sites*, for the small crystalline sites.

This is the shape over which the base case of the displayed equation (07MK) is to be computed: the
sections of `f_{cris, *}F` over `(U', T', δ')` are a limit over the big-site comma category
(`...SmallSite.crisDirectImageObjObjIsoLimit`), and `f_{cris, *}` factors through restriction to
the small crystalline site.  As for the big sites, nothing about a slice topos is involved, so
this is independent of [Stacks, Tag 0791]. -/
def pullbackCrystallineCommaEquivalence :
    CrystallineThickening (pullbackSituation S S' fS fX hf A') ≌
      CostructuredArrow (SmallSite.crisToBig S S' fS fX hf) A'.obj :=
  haveI : (pullbackCrisToComma S S' fS fX hf A').IsEquivalence := {}
  (pullbackCrisToComma S S' fS fX hf A').asEquivalence

end Comma

end GlobalCrystallineSituation

end Crystalline

end

end
