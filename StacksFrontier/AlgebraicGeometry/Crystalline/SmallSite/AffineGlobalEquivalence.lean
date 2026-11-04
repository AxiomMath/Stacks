module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalBridge
public import StacksFrontier.AlgebraicGeometry.Crystalline.SpecDividedPowerScheme
public import StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor

/-!
# Morphisms of affine divided power schemes from their global sections

Let `(X, I_X, δ)` and `(Y, I_Y, ε)` be divided power schemes with `Y` affine.  A morphism of
divided power rings `Γ(Y, ⊤) ⟶ Γ(X, ⊤)` then comes from a unique morphism of divided power
schemes `X ⟶ Y`.

This is the **fullness** input for the affine-to-global bridge
`Crystalline.GlobalCrystallineSituation.wholeSiteToAffine` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalBridge.lean`, and it is where
the publicly re-derived `Crystalline.DividedPowerScheme.isDPMorphism_app_of_affine` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SpecDividedPowerScheme.lean` is used: the
compatibility of the morphism with the divided powers is checked on affine opens, where
`Crystalline.DividedPowerScheme.map_ideal_top` reduces it to `⊤`, and is then propagated to
every open.

## Main definitions

* `Crystalline.DividedPowerScheme.homOfSectionsDPMorphism` — the morphism of divided power
  schemes `X ⟶ Y`, `Y` affine, attached to a morphism of divided power rings of global sections.

## Main results

* `Crystalline.DividedPowerScheme.isDPMorphism_app_of_appTop` — for `Y` affine, a morphism of
  schemes `X.scheme ⟶ Y.scheme` compatible with the divided powers on global sections is
  compatible on every open.
* `Crystalline.DividedPowerScheme.globalSectionsDPMorphism_homOfSectionsDPMorphism` — the
  construction is a section of `Crystalline.globalSectionsDPMorphism`.
* **`Crystalline.GlobalCrystallineSituation.full_wholeSiteToAffine`** — the bridge
  `𝒞ᵒᵖ ⥤ CRIS(Γ(X, ⊤)/Γ(S, ⊤))` is full, when `X` and `S` are affine.

## What is and is not proved

No tag attribute is placed in this file; [Stacks, Tag 07JK] needs more than fullness of the
bridge.

The bridge is **full and faithful** after this file, hence an equivalence onto its image.  It is
*not* an equivalence onto `CRIS(Γ(X, ⊤)/Γ(S, ⊤))`, and it cannot be: the objects of `CRIS(C/A)`
whose structural map `C → B/J` is not bijective are not in the image, since
`Crystalline.GlobalCrystallineSituation.isCrystalline_wholeThickeningToAffine` shows every object
of the image is crystalline.  The correct target for an equivalence is the *little* category
`Cris(Γ(X, ⊤)/Γ(S, ⊤))`, and essential surjectivity onto it — hence the equivalence
`𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))` — is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalEssSurj.lean`, on top of the
`Spec` of a divided power ring of
`StacksFrontier/AlgebraicGeometry/Crystalline/SpecDividedPowerScheme.lean` and the thickening of
schemes it carries, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SpecSchemeThickening.lean`.

Affineness of the base `S` is a genuine hypothesis of fullness, not an artefact: a morphism
`T ⟶ T'` of `𝒞` must be a morphism *over* `S`, and the only handle on that compatibility supplied
by a morphism of `CRIS(C/A)` is its effect on global sections, which pins down a morphism into `S`
exactly when `S` is affine.  [Stacks, Tag 07JK] assumes `X` and `S` affine.

## References

* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07GR](https://stacks.math.columbia.edu/tag/07GR)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.DividedPowerScheme

/-- **For an affine target, compatibility with the divided powers on global sections implies
compatibility on every open.**  On an affine open `V` of `Y` the divided power ideal is generated
by the ideal of global sections (`map_ideal_top`), so `DividedPowers.IsDPMorphism.of_comp`
reduces compatibility over `V` to compatibility over `⊤`; the passage from affine opens to all
opens is `isDPMorphism_app_of_affine`. -/
theorem isDPMorphism_app_of_appTop {X Y : DividedPowerScheme.{u}} [IsAffine Y.scheme]
    (f : X.scheme ⟶ Y.scheme)
    (hf : DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op ⊤))
      (X.dividedPowers.dividedPowers (op ⊤)) f.appTop.hom)
    (U : Y.scheme.Opens) :
    DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op U))
      (X.dividedPowers.dividedPowers (op (f ⁻¹ᵁ U))) (f.app U).hom := by
  have key (V : Y.scheme.affineOpens) :
      DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op V.1))
        (X.dividedPowers.dividedPowers (op (f ⁻¹ᵁ V.1))) (f.app V.1).hom := by
    have hV : V.1 ≤ ⊤ := le_top
    apply DividedPowers.IsDPMorphism.of_comp (f := (Y.scheme.presheaf.map (homOfLE hV).op).hom)
    · exact (DividedPowerScheme.map_ideal_top Y V).symm
    · exact Y.dividedPowers.naturality (homOfLE hV).op
    · refine isDPMorphism_of_eq
        (congrArg CommRingCat.Hom.hom (f.naturality (homOfLE hV).op)).symm ?_
      exact DividedPowers.IsDPMorphism.comp _
        (X.dividedPowers.naturality ((TopologicalSpace.Opens.map f.base).map
          (homOfLE hV).op.unop).op) hf
  exact isDPMorphism_app_of_affine X Y f (fun V W h ↦ DividedPowers.IsDPMorphism.comp _
    (X.dividedPowers.naturality (homOfLE h).op) (key V)) U

/-- **A morphism of divided power rings of global sections into an affine divided power scheme
comes from a morphism of divided power schemes.**  The underlying morphism of schemes is the one
of `Stacks.Smooth.homEquivOfIsAffine`; compatibility with the divided powers is
`isDPMorphism_app_of_appTop`. -/
def homOfSectionsDPMorphism {X Y : DividedPowerScheme.{u}} [IsAffine Y.scheme]
    (φ : Y.dividedPowers.toDividedPowerRing (op ⊤) ⟶
      X.dividedPowers.toDividedPowerRing (op ⊤)) :
    X ⟶ Y where
  hom := Stacks.Smooth.homEquivOfIsAffine.symm (CommRingCat.ofHom φ.toRingHom)
  compatible := by
    refine isDPMorphism_app_of_appTop _ ?_
    have he : (Stacks.Smooth.homEquivOfIsAffine.symm
        (CommRingCat.ofHom φ.toRingHom) : X.scheme ⟶ Y.scheme).appTop =
        CommRingCat.ofHom φ.toRingHom :=
      Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply _
    rw [he]
    exact φ.isDPMorphism

/-- The morphism of schemes underlying `homOfSectionsDPMorphism φ` induces the ring map underlying
`φ` on global sections. -/
@[simp]
theorem homOfSectionsDPMorphism_hom_appTop {X Y : DividedPowerScheme.{u}} [IsAffine Y.scheme]
    (φ : Y.dividedPowers.toDividedPowerRing (op ⊤) ⟶
      X.dividedPowers.toDividedPowerRing (op ⊤)) :
    (homOfSectionsDPMorphism φ).hom.appTop = CommRingCat.ofHom φ.toRingHom :=
  Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply _

/-- The construction is a section of `Crystalline.globalSectionsDPMorphism`: the morphism of
divided power rings of global sections induced by `homOfSectionsDPMorphism φ` is `φ`. -/
theorem globalSectionsDPMorphism_homOfSectionsDPMorphism {X Y : DividedPowerScheme.{u}}
    [IsAffine Y.scheme]
    (φ : Y.dividedPowers.toDividedPowerRing (op ⊤) ⟶
      X.dividedPowers.toDividedPowerRing (op ⊤)) :
    globalSectionsDPMorphism (homOfSectionsDPMorphism φ) = φ :=
  DividedPowers.DPMorphism.ext <|
    congrArg (fun ψ : CommRingCat.of ↥(Y.dividedPowers.toDividedPowerRing (op ⊤)) ⟶
      CommRingCat.of ↥(X.dividedPowers.toDividedPowerRing (op ⊤)) => (ψ.hom : _ → _))
      (homOfSectionsDPMorphism_hom_appTop φ)

end Crystalline.DividedPowerScheme

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **The ambient divided power scheme of an object of `𝒞` over an affine `X` is affine.**  The
thickened scheme is isomorphic to `X`, hence affine, and `Crystalline.SchemeThickening`'s
`isAffine_target` ([Stacks, Tag 06AD]) applies.  Recorded as an instance so that the
constructions below need no explicit affineness arguments. -/
instance instIsAffineThickeningTarget [IsAffine S.X] (B : Thickening S) [IsIso B.toX] :
    IsAffine B.thickening.target.scheme :=
  B.thickening.isAffine_target

/-- Restriction along the inverse of the isomorphism `U' ≅ X` undoes restriction along it. -/
theorem toX_appTop_inv_appTop {B' : Thickening S} [IsIso B'.toX]
    (a : Γ(B'.thickening.source, ⊤)) :
    B'.toX.appTop.hom ((inv B'.toX).appTop.hom a) = a := by
  rw [Stacks.Thickenings.appTop_comp_apply, IsIso.hom_inv_id, Scheme.Hom.id_appTop]
  rfl

section Full

variable [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  {B B' : Thickening S} [IsIso B.toX] [IsIso B'.toX]

omit [IsAffine S.S.scheme] in
/-- **The square of thickenings commutes** for the morphism of ambient divided power schemes
realising a morphism of the affine crystalline category.  Both ambient schemes being affine, the
square is checked on global sections, where it is the compatibility `toQuotient_comp` of
[Stacks, Tag 07HM] read through the restriction isomorphisms `Γ(T, ⊤)/I_T(⊤) ≅ Γ(U, ⊤)`. -/
theorem immersion_naturality_of_appTop
    (g : wholeThickeningToAffine hp B' ⟶ wholeThickeningToAffine hp B)
    {t : B.thickening.target ⟶ B'.thickening.target}
    (ht : t.hom.appTop = CommRingCat.ofHom g.hom.toRingHom) :
    B.thickening.immersion ≫ t.hom = (B.toX ≫ inv B'.toX) ≫ B'.thickening.immersion := by
  refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_))
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, ht]
  set y : Γ(S.X, ⊤) :=
    (inv B'.toX).appTop.hom (B'.thickening.immersion.appTop.hom a) with hy
  have hq : wholeSectionsToQuotient B' y =
      Ideal.Quotient.mk (SchemeThickening.sectionsIdeal B'.thickening) a := by
    refine B'.thickening.sectionsQuotientEquiv.injective ?_
    rw [sectionsQuotientEquiv_wholeSectionsToQuotient,
      SchemeThickening.sectionsQuotientEquiv_mk, hy]
    exact toX_appTop_inv_appTop _
  have htq : DividedPowerRing.quotientRingHom g.hom
      (Ideal.Quotient.mk (SchemeThickening.sectionsIdeal B'.thickening) a) =
      wholeSectionsToQuotient B y := by
    rw [← hq]
    exact DFunLike.congr_fun g.toQuotient_comp y
  have hmk : DividedPowerRing.quotientRingHom g.hom
      (Ideal.Quotient.mk (SchemeThickening.sectionsIdeal B'.thickening) a) =
      Ideal.Quotient.mk (SchemeThickening.sectionsIdeal B.thickening) (g.hom a) :=
    DividedPowerRing.quotientRingHom_mk g.hom a
  have htq2 := hmk.symm.trans htq
  have hL : B.thickening.sectionsQuotientEquiv
      (Ideal.Quotient.mk (SchemeThickening.sectionsIdeal B.thickening) (g.hom a)) =
      B.thickening.immersion.appTop.hom (g.hom a) :=
    SchemeThickening.sectionsQuotientEquiv_mk _ _
  have hR : B.thickening.sectionsQuotientEquiv (wholeSectionsToQuotient B y) =
      B.toX.appTop.hom y :=
    sectionsQuotientEquiv_wholeSectionsToQuotient B y
  exact hL.symm.trans
    ((congrArg (fun q ↦ B.thickening.sectionsQuotientEquiv q) htq2).trans hR)

/-- **The morphism of ambient divided power schemes realising a morphism of the affine
crystalline category is a morphism over the base.**  The base being affine, this is checked on
global sections, where it is the compatibility `fromBase_comp` of [Stacks, Tag 07HM]. -/
theorem base_naturality_of_appTop
    (g : wholeThickeningToAffine hp B' ⟶ wholeThickeningToAffine hp B)
    {t : B.thickening.target ⟶ B'.thickening.target}
    (ht : t.hom.appTop = CommRingCat.ofHom g.hom.toRingHom) :
    t ≫ B'.toBase = B.toBase := by
  refine DividedPowerScheme.Hom.ext
    (ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)))
  rw [DividedPowerScheme.Hom.comp_hom, Scheme.Hom.comp_appTop, ht]
  exact DFunLike.congr_fun g.fromBase_comp c

/-- **A morphism of the affine crystalline category between the images of two objects of `𝒞`
comes from a morphism of `𝒞`.**  The ambient divided power schemes being affine, the morphism of
divided power rings of global sections is realised by a morphism of divided power schemes
(`Crystalline.DividedPowerScheme.homOfSectionsDPMorphism`); the map on thickened schemes is
forced, both being isomorphic to `X`; and the two squares of [Stacks, Tag 07I6] are exactly the
two compatibilities carried by the morphism of [Stacks, Tag 07HM]. -/
def wholeHomOfAffine
    (g : wholeThickeningToAffine hp B' ⟶ wholeThickeningToAffine hp B) : B ⟶ B' where
  sourceHom := B.toX ≫ inv B'.toX
  targetHom := DividedPowerScheme.homOfSectionsDPMorphism g.hom
  immersion_naturality := immersion_naturality_of_appTop hp g
    (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop g.hom)
  base_naturality := base_naturality_of_appTop hp g
    (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop g.hom)
  toX_naturality := by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The morphism of `𝒞` produced by `wholeHomOfAffine` induces the given morphism of divided
power rings of global sections. -/
theorem wholeHomToAffine_wholeHomOfAffine
    (g : wholeThickeningToAffine hp B' ⟶ wholeThickeningToAffine hp B) :
    wholeHomToAffine hp (wholeHomOfAffine hp g) = g := by
  refine DividedPowerThickening.Hom.ext ?_
  rw [wholeHomToAffine_hom]
  exact DividedPowerScheme.globalSectionsDPMorphism_homOfSectionsDPMorphism g.hom

/-- **The affine-to-global bridge is full.**  Every morphism of the affine crystalline category
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))` between the images of two objects of the chaotic subsite `𝒞` comes from a
morphism of `𝒞`.  Together with
`Crystalline.GlobalCrystallineSituation.faithful_wholeSiteToAffine` this makes the bridge fully
faithful, hence an equivalence onto its image. -/
instance full_wholeSiteToAffine : (wholeSiteToAffine hp).Full where
  map_surjective {A B} g := by
    have hA : IsIso ((wholeToBig S).obj A.unop).toX := A.unop.property
    have hB : IsIso ((wholeToBig S).obj B.unop).toX := B.unop.property
    refine ⟨((wholeToBig S).preimage (wholeHomOfAffine hp g)).op, ?_⟩
    have h : (wholeToBig S).map ((wholeToBig S).preimage (wholeHomOfAffine hp g)) =
        wholeHomOfAffine hp g := (wholeToBig S).map_preimage _
    exact (congrArg (fun k : (wholeToBig S).obj B.unop ⟶ (wholeToBig S).obj A.unop ↦
      wholeHomToAffine hp k) h).trans (wholeHomToAffine_wholeHomOfAffine hp g)

/-- **The affine-to-global bridge is fully faithful.** -/
def fullyFaithfulWholeSiteToAffine : (wholeSiteToAffine hp).FullyFaithful :=
  .ofFullyFaithful _

end Full

end Crystalline.GlobalCrystallineSituation

end

end
