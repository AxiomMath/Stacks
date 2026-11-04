module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
import all StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation

/-!
# Stacks 0CJB with the restricted 1-morphism supplied by the universal property

**Stacks 0CJB** is stated for a *commutative diagram* of thickenings of algebraic stacks: a
thickening `iB : ℬ ⟶ ℬ'` of bases, structure 1-morphisms `pX' : 𝒳' ⟶ ℬ'` and `pY' : 𝒴' ⟶ ℬ'`, an
ambient 1-morphism `f' : 𝒳' ⟶ 𝒴'` over `ℬ'`, and the restricted 1-morphism `f : 𝒳 ⟶ 𝒴` of the
base changes along `iB`. In
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation` that restricted 1-morphism, the
two 2-cells comparing it with `f'`, and the cube-coherence equation relating them — which is what
the word "commutative" means for a diagram of 2-categories, and which nothing in the shape of the
diagram forces — are hypotheses of
`AlgebraicGeometry.Stack.isFlat_ambient_of_flatDeformation` and
`AlgebraicGeometry.Stack.isFlatAt_target_of_flatDeformation`.

They need not be. The restricted target is a 2-fibre product of `(pY', iB)`, and the restricted
source, its first projection composed with `f'`, and its second projection form a 2-commutative
square over the *same* cospan `(pY', iB)`, by the filler of the square of the restricted source
and the 2-cell `houter : f' ≫ pY' ≅ pX'` making `f'` a 1-morphism over `ℬ'`. So the universal
property of the restricted target supplies a 1-morphism between the two apexes together with its
two comparison 2-cells *and* their compatibility square — the data of **Stacks 003O** — and that
compatibility square is the cube-coherence equation. This file builds that square
(`AlgebraicGeometry.Stack.restrictedSq`), reads off the restricted 1-morphism
(`AlgebraicGeometry.Stack.restrictedHom`) and its two comparison 2-cells, discharges the
coherence equation from the `compat` field of the resulting pre-morphism, and states Stacks 0CJB
with no hypothesis on the restricted 1-morphism other than its flatness.

## Main definitions

* `AlgebraicGeometry.Stack.restrictedSq`: the square of the restricted source, read over the
  cospan `(pY', iB)` by composing its first projection with `f'`.
* `AlgebraicGeometry.Stack.restrictedPreHom`: the pre-morphism of **Stacks 003O** from that
  square to the square of the restricted target, supplied by the universal property.
* `AlgebraicGeometry.Stack.restrictedHom`: the restricted 1-morphism `𝒳 ⟶ 𝒴` it carries.
* `AlgebraicGeometry.Stack.restrictedIsoFst`, `AlgebraicGeometry.Stack.restrictedIsoSnd`: its two
  comparison 2-cells, against the thickening of the target and against the structure 1-morphism
  of the restricted target.

## Main results

* `AlgebraicGeometry.Stack.restrictedHom_coherence`: the cube-coherence equation holds for those
  data, with no hypothesis.
* `AlgebraicGeometry.Stack.isFlat_of_flatDeformation`: **Stacks 0CJB**, both conclusions, with the
  restricted 1-morphism the canonical one.

## Implementation notes

Nothing about flatness is re-proved: the two conclusions are
`AlgebraicGeometry.Stack.isFlat_ambient_of_flatDeformation` and
`AlgebraicGeometry.Stack.isFlatAt_target_of_flatDeformation` applied to the canonical data.

The filler of `AlgebraicGeometry.Stack.restrictedSq` carries one associator, which the 2-category
of algebraic stacks makes the identity 2-cell; and the compatibility square of Stacks 003O carries
two more. All three are written out as the identities they are, by `change`, rather than rewritten
away: the 2-category of algebraic stacks is an induced bicategory (**Stacks 03YP**) over another
one, so rewriting an associator out of a goal changes the type of an intermediate object of a
composite and the motive is not type-correct at the transparency at which Lean checks implicit
arguments. This is the device of
`StacksFrontier.CategoryTheory.TwoFibreProduct.StrictTwoCommSq`, whose
`CategoryTheory.CatFiberedInGroupoids.preHomOfStrict` writes such a square down in the other
direction.

`comp_inv_eq_inv_comp`, the general fact about categories this file reads a commuting square
with, is the `private` lemma of that name in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation`, reached by `import all`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 0CID](https://stacks.math.columbia.edu/tag/0CID)
* [Stacks Project, Tag 0CJB](https://stacks.math.columbia.edu/tag/0CJB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {ℬ ℬ' 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS}

section Restriction

variable {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'} {f' : 𝒳' ⟶ 𝒴'}

/-- **The square of the restricted source, read over the cospan of the restricted target.** Let
`PX` be a 2-commutative square over `(pX', iB)` — its apex is the restricted source `𝒳`, its
first projection the thickening `𝒳 ⟶ 𝒳'` and its second projection the structure 1-morphism
`𝒳 ⟶ ℬ` — and let `houter : f' ≫ pY' ≅ pX'` exhibit the ambient 1-morphism as a 1-morphism over
`ℬ'`. Composing the thickening with `f'` makes the same apex a 2-commutative square over the
cospan `(pY', iB)`, with filler the composite of `houter` whiskered by the thickening with the
filler of `PX`. -/
def restrictedSq (PX : Bicategory.TwoCommSq pX' iB) (houter : f' ≫ pY' ≅ pX') :
    Bicategory.TwoCommSq pY' iB where
  pt := PX.pt
  fst := PX.fst ≫ f'
  snd := PX.snd
  iso := Bicategory.associator PX.fst f' pY' ≪≫
    Bicategory.whiskerLeftIso PX.fst houter ≪≫ PX.iso

/-- **The restricted 1-morphism of a commutative diagram of thickenings, as a pre-morphism of
2-commutative squares (Stacks 003O).** If the square `PY` of the restricted target is a 2-fibre
product of `(pY', iB)` (**Stacks 003Q**) — the fourth hypothesis of **Stacks 0CJB** at the target
— then its universal property applied to `AlgebraicGeometry.Stack.restrictedSq` supplies a
1-morphism `𝒳 ⟶ 𝒴` of the two apexes, two comparison 2-cells, and the compatibility square of
Stacks 003O relating them. Those are exactly the restricted 1-morphism and the commutativity of
the cube of Stacks 0CJB. -/
noncomputable def restrictedPreHom (PX : Bicategory.TwoCommSq pX' iB)
    (PY : Bicategory.TwoCommSq pY' iB) (houter : f' ≫ pY' ≅ pX')
    (hcartY : Bicategory.IsTwoFibreProduct PY) :
    Bicategory.TwoCommSq.PreHom (restrictedSq B S hS PX houter) PY :=
  Bicategory.twoFibreProductPreHom hcartY (restrictedSq B S hS PX houter)

/-- **The restricted 1-morphism `𝒳 ⟶ 𝒴` of a commutative diagram of thickenings.** The
1-morphism of apexes carried by `AlgebraicGeometry.Stack.restrictedPreHom`, i.e. the one the
universal property of the restricted target induces on the restricted source. -/
noncomputable def restrictedHom (PX : Bicategory.TwoCommSq pX' iB)
    (PY : Bicategory.TwoCommSq pY' iB) (houter : f' ≫ pY' ≅ pX')
    (hcartY : Bicategory.IsTwoFibreProduct PY) :
    PX.pt ⟶ PY.pt :=
  (restrictedPreHom B S hS PX PY houter hcartY).hom

/-- **The restricted 1-morphism followed by the thickening of the target is the thickening of the
source followed by the ambient 1-morphism.** The first comparison 2-cell of
`AlgebraicGeometry.Stack.restrictedPreHom`: one of the two 2-cells of the commutative diagram of
**Stacks 0CJB**. -/
noncomputable def restrictedIsoFst (PX : Bicategory.TwoCommSq pX' iB)
    (PY : Bicategory.TwoCommSq pY' iB) (houter : f' ≫ pY' ≅ pX')
    (hcartY : Bicategory.IsTwoFibreProduct PY) :
    restrictedHom B S hS PX PY houter hcartY ≫ PY.fst ≅ PX.fst ≫ f' :=
  (restrictedPreHom B S hS PX PY houter hcartY).isoFst.symm

/-- **The restricted 1-morphism followed by the structure 1-morphism of the restricted target is
that of the restricted source.** The second comparison 2-cell of
`AlgebraicGeometry.Stack.restrictedPreHom`: the other 2-cell of the commutative diagram of
**Stacks 0CJB**. -/
noncomputable def restrictedIsoSnd (PX : Bicategory.TwoCommSq pX' iB)
    (PY : Bicategory.TwoCommSq pY' iB) (houter : f' ≫ pY' ≅ pX')
    (hcartY : Bicategory.IsTwoFibreProduct PY) :
    restrictedHom B S hS PX PY houter hcartY ≫ PY.snd ≅ PX.snd :=
  (restrictedPreHom B S hS PX PY houter hcartY).isoSnd.symm

/-- **The cube of Stacks 0CJB commutes, for the canonically induced restricted 1-morphism.** The
two routes from `𝒳 ⟶ 𝒴' ⟶ ℬ'` to `𝒳 ⟶ ℬ ⟶ ℬ'` — through the filler of the square of the
restricted target and through the filler of the square of the restricted source — are 2-cells
with the same source and target, and in a 2-category nothing in the shape of the diagram forces
them to agree. For the restricted 1-morphism supplied by the universal property of the restricted
target they do agree: that is the compatibility square of **Stacks 003O** carried by
`AlgebraicGeometry.Stack.restrictedPreHom`, with its two associators and the associator in the
filler of `AlgebraicGeometry.Stack.restrictedSq` written out as the identity 2-cells they are in
this strict 2-category.

So the hypothesis `hcoh` of `AlgebraicGeometry.Stack.isFlat_ambient_of_flatDeformation` and of
`AlgebraicGeometry.Stack.isFlatAt_target_of_flatDeformation` is not a hypothesis at all once the
restricted 1-morphism is taken to be the induced one. -/
theorem restrictedHom_coherence (PX : Bicategory.TwoCommSq pX' iB)
    (PY : Bicategory.TwoCommSq pY' iB) (houter : f' ≫ pY' ≅ pX')
    (hcartY : Bicategory.IsTwoFibreProduct PY) :
    Bicategory.whiskerLeft (restrictedHom B S hS PX PY houter hcartY) PY.iso.hom ≫
        Bicategory.whiskerRight (restrictedIsoSnd B S hS PX PY houter hcartY).hom iB =
      Bicategory.whiskerRight (restrictedIsoFst B S hS PX PY houter hcartY).hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom := by
  set P := restrictedPreHom B S hS PX PY houter hcartY
  have hc : (Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom) ≫
        Bicategory.whiskerRight P.isoSnd.hom iB =
      Bicategory.whiskerRight P.isoFst.hom pY' ≫
        Bicategory.whiskerLeft P.hom PY.iso.hom := by
    have h := P.compat
    change (𝟙 ((PX.fst ≫ f') ≫ pY') ≫
          Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom) ≫
        Bicategory.whiskerRight P.isoSnd.hom iB ≫ 𝟙 ((P.hom ≫ PY.snd) ≫ iB)
      = Bicategory.whiskerRight P.isoFst.hom pY' ≫
        𝟙 ((P.hom ≫ PY.fst) ≫ pY') ≫ Bicategory.whiskerLeft P.hom PY.iso.hom at h
    -- the three identity 2-cells are cancelled as terms: the source and target of a whiskering
    -- in an induced bicategory are structure literals, not syntactically composites, so a
    -- `simp only` with the two unit lemmas does not fire on them
    exact (congrArg₂ (fun a b => a ≫ b)
          (Category.id_comp (Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom))
          (Category.comp_id (Bicategory.whiskerRight P.isoSnd.hom iB))).symm.trans
      (h.trans (congrArg (fun t => Bicategory.whiskerRight P.isoFst.hom pY' ≫ t)
        (Category.id_comp (Bicategory.whiskerLeft P.hom PY.iso.hom))))
  exact comp_inv_eq_inv_comp (Bicategory.whiskerRightIso P.isoFst pY')
    (Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (Bicategory.whiskerRightIso P.isoSnd iB)
    (Bicategory.whiskerLeft P.hom PY.iso.hom) hc

end Restriction

/-- **Stacks 0CJB.** Let `iB : ℬ ⟶ ℬ'` be a thickening of algebraic stacks over `S`, let
`pX' : 𝒳' ⟶ ℬ'` and `pY' : 𝒴' ⟶ ℬ'` be structure 1-morphisms, and let `f' : 𝒳' ⟶ 𝒴'` be a
1-morphism over `ℬ'`, by `houter`. Let `PX` and `PY` present the restricted source and target as
the base changes of `𝒳'` and `𝒴'` along `iB`, and let `f : 𝒳 ⟶ 𝒴` be the restricted 1-morphism
the universal property of the restricted target induces,
`AlgebraicGeometry.Stack.restrictedHom`. Assume

1. `pY'` is locally of finite type,
2. `pX'` is flat and locally of finite presentation,
3. `f` is flat,
4. `𝒳 = ℬ ×_{ℬ'} 𝒳'` and `𝒴 = ℬ ×_{ℬ'} 𝒴'`, i.e. `PX` and `PY` are 2-fibre products.

Then `f'` is flat, and `pY'` is flat — in the sense of **Stacks 0CID** — at every point of `|𝒴'|`
in the image of `|f'|`.

This is `AlgebraicGeometry.Stack.isFlat_ambient_of_flatDeformation` and
`AlgebraicGeometry.Stack.isFlatAt_target_of_flatDeformation` with the two 2-cells of the
commutative diagram and its cube-coherence equation supplied by
`AlgebraicGeometry.Stack.restrictedIsoFst`, `AlgebraicGeometry.Stack.restrictedIsoSnd` and
`AlgebraicGeometry.Stack.restrictedHom_coherence` rather than assumed.

The two thickenings `𝒳 ⟶ 𝒳'` and `𝒴 ⟶ 𝒴'` of the source's diagram are not hypotheses: they are
base changes of `iB` and so are thickenings by **Stacks 0BPR**. -/
@[stacks 0CJB]
theorem isFlat_of_flatDeformation
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hYft : AlgebraicStacks.IsLocallyOfFiniteType B S hS pY')
    (hXflat : AlgebraicStacks.IsFlat B S hS pX')
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX')
    (hfflat : AlgebraicStacks.IsFlat B S hS (restrictedHom B S hS PX PY houter hcartY)) :
    AlgebraicStacks.IsFlat B S hS f' ∧
      ∀ x' : AlgebraicStacks.points B S hS 𝒳',
        AlgebraicStacks.IsFlatAt B S hS pY' (AlgebraicStacks.pointsMap B S hS f' x') :=
  ⟨isFlat_ambient_of_flatDeformation B S hS hiB hcartX hcartY houter
      (restrictedIsoFst B S hS PX PY houter hcartY)
      (restrictedIsoSnd B S hS PX PY houter hcartY)
      (restrictedHom_coherence B S hS PX PY houter hcartY) hYft hXflat hXfp hfflat,
    fun x' => isFlatAt_target_of_flatDeformation B S hS hiB hcartX hcartY houter
      (restrictedIsoFst B S hS PX PY houter hcartY)
      (restrictedIsoSnd B S hS PX PY houter hcartY)
      (restrictedHom_coherence B S hS PX PY houter hcartY) hYft hXflat hXfp hfflat x'⟩

end AlgebraicGeometry.Stack

end
