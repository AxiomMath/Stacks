module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalEssSurj

/-!
# Objects of the big crystalline category with affine thickened scheme

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine.  The
affine-to-global bridge of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalBridge.lean` sends an object
`(U, T, δ)` of `CRIS(X/S)` whose thickened scheme `U` is affine to the divided power thickening
`Γ(T, ⊤)` of [Stacks, Tag 07HM], by taking global sections
(`Crystalline.GlobalCrystallineSituation.wholeThickeningToAffine`).  This file proves that the
bridge is **fully faithful on the objects with affine thickened scheme**, not only on the chaotic
subsite of thickenings of the whole of `X`.

Faithfulness is already
`Crystalline.GlobalCrystallineSituation.wholeHomToAffine_injective`.  Fullness is not: the
library's `Crystalline.GlobalCrystallineSituation.wholeHomOfAffine` builds the map on thickened
schemes as `B.toX ≫ inv B'.toX`, which exists only when both structure morphisms to `X` are
isomorphisms.  Here the map on thickened schemes is instead forced by the map on ambient schemes,
through the identification of a thickened scheme with the closed fibre of its ambient divided
power scheme (`Crystalline.SchemeThickening.closedFiberSourceIso`): see
`Crystalline.SchemeThickening.sourceMapOfTargetMap`.  That identification needs no affineness at
all, and it is what makes the argument work for an arbitrary affine object.

## Main definitions

* `Crystalline.SchemeThickening.sourceMapOfTargetMap` — the map on thickened schemes induced by a
  map of ambient divided power schemes, through the closed fibre.
* `Crystalline.GlobalCrystallineSituation.homOfAffineSections` — **the morphism of `CRIS(X/S)`
  realising a morphism of divided power thickenings of global sections**, for objects with affine
  thickened scheme.

## Main results

* `Crystalline.SchemeThickening.sourceMapOfTargetMap_immersion` — the induced map on thickened
  schemes makes the square of immersions commute.
* `Crystalline.GlobalCrystallineSituation.wholeHomToAffine_homOfAffineSections` — the realised
  morphism induces the given morphism on global sections.
* **`Crystalline.GlobalCrystallineSituation.wholeHomToAffine_bijective`** — taking global sections
  is a bijection on morphisms between objects with affine thickened scheme, i.e. the bridge is
  fully faithful there.

## What is and is not proved

No tag attribute is placed in this file.  **This is not [Stacks, Tag 07I9]**, and in particular it
does not give binary products in `CRIS(X/S)`; what is here is one of the two ingredients the
affine case of the binary product needs, namely that an object of `CRIS(X/S)` with affine
thickened scheme is determined, together with its morphisms, by its divided power ring of global
sections.

The other ingredient is already in the library: `Crystalline.GlobalCrystallineSituation.
specThickeningOfAffine` realises an object of the affine site as an object of `CRIS(X/S)`, and
[Stacks, Tag 07HN] supplies the binary coproduct there
(`Crystalline.binaryCoproductWithTensorProductQuotient`).

What is still missing even for the affine binary product is the universal property against an
**arbitrary** object `T` of `CRIS(X/S)`: a cone over the pair with vertex `T` has to be lifted,
and `T` need not have affine thickened scheme, so `wholeThickeningToAffine` does not apply to it.
Lifting it needs a divided power thickening of global sections attached to `T` *relative to* a
given morphism `T ⟶ A` into an affine object — the structural map
`Γ(X, ⊤) → Γ(T, ⊤)/I_T(⊤)` cannot be built from `T` alone, because
`Γ(T, ⊤)/I_T(⊤) → Γ(U_T, ⊤)` is injective but not surjective without affineness of `U_T`.

Beyond the affine case, the global statement of [Stacks, Tag 07I9] needs the descent of a divided
power thickening along an open cover, which is absent from the library for
`Crystalline.SchemeThickening` and for `Crystalline.GlobalCrystallineSituation.Thickening`.  The
divided power *scheme* level version is now public, in
`StacksFrontier/AlgebraicGeometry/Crystalline/DividedPowerGluing.lean`
(`Crystalline.DividedPowerScheme.DividedPowerOpenPresentation` with its `glued`, `gluedι`,
`gluedMap` and `isColimit`), extracted from `FibreProduct.lean` together with the substrate it
rests on.  Promoting those declarations one at a time in place does not work — an exposed public
body may not reference a private declaration — but moving the closed set does, and needed no change
to any proof: the one obstruction was an undetermined implicit in `kernelSubmoduleIsLimit`, not the
transparency attributes.

For the restriction of the situation to a pair of opens, which is how the global statement reduces
to the affine one, see
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/SituationRestrict.lean`.

A remark on [Stacks, Tag 07I9].  The binary product half of the argument for that tag runs
through an affine realization of divided power thickenings, along the chain
`hasBinaryProducts_crystalline` to `hasBinaryProduct_glued` to `productPatch_hasBinaryProduct` to
`hasBinaryProduct_of_affine_localization` to `hasAffineCrystallineBinaryProduct` to
`affineThickeningRealization` to `dividedPowerSpecRealization`.  Only the instance of the affine
realization at the empty scheme is used, and only five of its fields, all of which are proved, as
`Crystalline.DividedPowerScheme.specDividedPowerScheme`, `specSectionsRingEquiv`,
`specDividedPowerIdeal_top` and `specSectionsRingIso` — which is why
`Crystalline.GlobalCrystallineSituation.specThickeningOfAffine`, built on them, suffices.

## References

* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

namespace SchemeThickening

/-- **The map on thickened schemes induced by a map of ambient divided power schemes.**  A
thickened scheme is the closed fibre of its ambient divided power scheme,
`Crystalline.SchemeThickening.closedFiberSourceIso`, and the closed fibre is functorial, so a map
of ambient schemes induces a map of thickened schemes with no choice involved. -/
def sourceMapOfTargetMap {D E : SchemeThickening.{u}} (t : D.target ⟶ E.target) :
    D.source ⟶ E.source :=
  D.closedFiberSourceIso.inv ≫ DividedPowerScheme.closedFiberMap t ≫ E.closedFiberSourceIso.hom

/-- **The induced map on thickened schemes makes the square of immersions commute.**  Composing
with the immersion of the target turns the identification of the thickened scheme with the closed
fibre into the closed fibre inclusion, and the closed fibre inclusions are natural. -/
theorem sourceMapOfTargetMap_immersion {D E : SchemeThickening.{u}} (t : D.target ⟶ E.target) :
    D.immersion ≫ t.hom = sourceMapOfTargetMap t ≫ E.immersion := by
  rw [sourceMapOfTargetMap, Category.assoc, Category.assoc,
    closedFiberSourceIso_hom_immersion, DividedPowerScheme.closedFiberMap_comp_closedFiberι,
    ← Category.assoc, closedFiberSourceIso_inv_closedFiberι]

end SchemeThickening

namespace GlobalCrystallineSituation

/-- **The ambient divided power scheme of an object with affine thickened scheme is affine.**  The
immersion is a surjective closed immersion, so this is `Crystalline.SchemeThickening.
isAffine_target`, [Stacks, Tag 06AD].  Recorded as an instance so that the constructions below
need no explicit affineness arguments. -/
instance isAffine_target_of_isAffine_source {S : GlobalCrystallineSituation.{u}}
    (B : Thickening S) [IsAffine B.thickening.source] :
    IsAffine B.thickening.target.scheme :=
  B.thickening.isAffine_target

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  {P A : Thickening S} [IsAffine P.thickening.source] [IsAffine A.thickening.source]

omit [IsAffine S.X] in
/-- **The morphism of ambient divided power schemes realising a morphism of divided power
thickenings of global sections is a morphism over the base.**  The base being affine, this is
checked on global sections, where it is the compatibility `fromBase_comp` of
[Stacks, Tag 07HM]. -/
theorem base_naturality_of_appTop_of_isAffine_source
    (g : wholeThickeningToAffine hp A ⟶ wholeThickeningToAffine hp P)
    {t : P.thickening.target ⟶ A.thickening.target}
    (ht : t.hom.appTop = CommRingCat.ofHom g.hom.toRingHom) :
    t ≫ A.toBase = P.toBase := by
  refine DividedPowerScheme.Hom.ext
    (ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)))
  rw [DividedPowerScheme.Hom.comp_hom, Scheme.Hom.comp_appTop, ht]
  exact DFunLike.congr_fun g.fromBase_comp c

omit [IsAffine S.S.scheme] in
/-- **The induced map on thickened schemes is a morphism over `X`.**  Both maps land in the affine
scheme `X`, so the identity is checked on global sections.  A section of `X` is carried by the
structure morphism of `A` into the thickened scheme of `A`, and lifts along the surjection
`Γ(T_A, ⊤) → Γ(U_A, ⊤)` of `Crystalline.SchemeThickening.surjective_immersion_appTop`; the
compatibility `toQuotient_comp` of [Stacks, Tag 07HM] identifies the image of that lift under `g`
with the corresponding section of the thickened scheme of `P`, and
`Crystalline.SchemeThickening.sourceMapOfTargetMap_immersion` transports the identity across the
square of immersions. -/
theorem toX_naturality_of_appTop_of_isAffine_source
    (g : wholeThickeningToAffine hp A ⟶ wholeThickeningToAffine hp P)
    {t : P.thickening.target ⟶ A.thickening.target}
    (ht : t.hom.appTop = CommRingCat.ofHom g.hom.toRingHom) :
    SchemeThickening.sourceMapOfTargetMap t ≫ A.toX = P.toX := by
  refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_))
  -- lift the section `A.toX.appTop y` of the thickened scheme of `A` to the ambient scheme
  obtain ⟨a, ha⟩ := A.thickening.surjective_immersion_appTop (A.toX.appTop.hom y)
  -- the class of `a` is the class attached to `y`
  have hA : wholeSectionsToQuotient A y =
      Ideal.Quotient.mk (SchemeThickening.sectionsIdeal A.thickening) a := by
    refine A.thickening.sectionsQuotientEquiv.injective ?_
    rw [sectionsQuotientEquiv_wholeSectionsToQuotient,
      SchemeThickening.sectionsQuotientEquiv_mk]
    exact ha.symm
  -- `g` carries it to the class attached to `y` for `P`
  have hP : wholeSectionsToQuotient P y =
      Ideal.Quotient.mk (SchemeThickening.sectionsIdeal P.thickening) (g.hom a) :=
    (DFunLike.congr_fun g.toQuotient_comp y).symm.trans
      ((congrArg (fun q ↦ DividedPowerRing.quotientRingHom g.hom q) hA).trans
        (DividedPowerRing.quotientRingHom_mk
          (A := (wholeThickeningToAffine hp A).ring)
          (B := (wholeThickeningToAffine hp P).ring) g.hom a))
  -- read the structure morphism of `P` through the restriction isomorphism
  have hPX : P.toX.appTop.hom y = P.thickening.immersion.appTop.hom (g.hom a) :=
    (sectionsQuotientEquiv_wholeSectionsToQuotient P y).symm.trans
      ((congrArg (fun q ↦ P.thickening.sectionsQuotientEquiv q) hP).trans
        (SchemeThickening.sectionsQuotientEquiv_mk P.thickening (g.hom a)))
  -- the square of immersions, read on the lift `a`
  have hsq : P.thickening.immersion.appTop.hom (t.hom.appTop.hom a) =
      (SchemeThickening.sourceMapOfTargetMap t).appTop.hom
        (A.thickening.immersion.appTop.hom a) := by
    have h2 := congrArg (fun k : P.thickening.source ⟶ A.thickening.target.scheme ↦
      k.appTop.hom a) (SchemeThickening.sourceMapOfTargetMap_immersion
        (D := P.thickening) (E := A.thickening) t)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply] using h2
  have hg : t.hom.appTop.hom a = g.hom a := by rw [ht]; rfl
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]
  rw [← ha, ← hsq, hg, hPX]

/-- **A morphism of divided power thickenings of global sections between two objects of `CRIS(X/S)`
with affine thickened scheme comes from a morphism of `CRIS(X/S)`.**  The ambient divided power
schemes being affine, the morphism of divided power rings of global sections is realised by a
morphism of ambient divided power schemes
(`Crystalline.DividedPowerScheme.homOfSectionsDPMorphism`); the map on thickened schemes is then
forced through the closed fibre, by
`Crystalline.SchemeThickening.sourceMapOfTargetMap`; and the two squares of [Stacks, Tag 07I6] are
the two compatibilities carried by the morphism of [Stacks, Tag 07HM]. -/
def homOfAffineSections
    (g : wholeThickeningToAffine hp A ⟶ wholeThickeningToAffine hp P) : P ⟶ A where
  sourceHom := SchemeThickening.sourceMapOfTargetMap
    (DividedPowerScheme.homOfSectionsDPMorphism g.hom)
  targetHom := DividedPowerScheme.homOfSectionsDPMorphism g.hom
  immersion_naturality := SchemeThickening.sourceMapOfTargetMap_immersion _
  base_naturality := base_naturality_of_appTop_of_isAffine_source hp g
    (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop g.hom)
  toX_naturality := toX_naturality_of_appTop_of_isAffine_source hp g
    (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop g.hom)

/-- The morphism of `CRIS(X/S)` produced by
`Crystalline.GlobalCrystallineSituation.homOfAffineSections` induces the given morphism of divided
power rings of global sections. -/
theorem wholeHomToAffine_homOfAffineSections
    (g : wholeThickeningToAffine hp A ⟶ wholeThickeningToAffine hp P) :
    wholeHomToAffine hp (homOfAffineSections hp g) = g := by
  refine DividedPowerThickening.Hom.ext ?_
  rw [wholeHomToAffine_hom]
  exact DividedPowerScheme.globalSectionsDPMorphism_homOfSectionsDPMorphism g.hom

/-- **Taking divided power rings of global sections is a bijection on morphisms between objects of
`CRIS(X/S)` with affine thickened scheme.**  Injectivity is
`Crystalline.GlobalCrystallineSituation.wholeHomToAffine_injective`; surjectivity is
`Crystalline.GlobalCrystallineSituation.homOfAffineSections`.  So the affine-to-global bridge is
fully faithful on the objects with affine thickened scheme, and such an object is determined,
together with its morphisms, by its divided power ring of global sections. -/
theorem wholeHomToAffine_bijective :
    Function.Bijective
      (fun f : P ⟶ A ↦ wholeHomToAffine hp f) :=
  ⟨fun _ _ h ↦ wholeHomToAffine_injective hp h,
    fun g ↦ ⟨homOfAffineSections hp g, wholeHomToAffine_homOfAffineSections hp g⟩⟩

end GlobalCrystallineSituation

end Crystalline

end
