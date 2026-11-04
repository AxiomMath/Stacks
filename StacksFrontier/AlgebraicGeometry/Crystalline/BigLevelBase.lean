module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelTower
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalEquivalence

/-!
# The finite levels `S_e = V(p^e) ⊂ S` of an affine divided power base

Let `(p, (S, I, γ), X)` be a global crystalline situation whose base `S` is affine, and write
`A = Γ(S, 𝒪_S)` with its ideal `I = Γ(S, ℐ)` and divided powers `γ`.  For an exponent `e` such
that `(p^e) ⊆ I` is preserved by `γ` (a *finite divided power level*), the closed subscheme
`S_e = Spec(A/p^eA)` is a divided power scheme with the same closed fibre as `S`, so `X` is a
scheme over the closed fibre of `S_e` as well.  This file builds the global crystalline
situations `X/S_e`, the divided power morphisms `S_e ⟶ S` and the transitions `S_m ⟶ S_e` for
`m ≤ e`, together with the compatibilities that change of divided power base consumes.

The construction goes through the canonical identification `Spec(A, I, γ) ≅ S` of divided power
schemes (`Crystalline.DividedPowerScheme.specIsoOfIsAffine`), which lets the levels of the divided
power ring `(A, I, γ)` of `StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelSite.lean` serve
for `S` itself.

## Main definitions

* `Crystalline.DividedPowerScheme.specIsoOfIsAffine` — an affine divided power scheme is the
  spectrum of its divided power ring of global sections.
* `Crystalline.GlobalCrystallineSituation.levelSituation` — the situation `X/S_e`.
* `Crystalline.GlobalCrystallineSituation.levelProj` — the divided power morphism `S_e ⟶ S`.
* `Crystalline.GlobalCrystallineSituation.levelTransition` — the transition `S_m ⟶ S_e`.
* `Crystalline.GlobalCrystallineSituation.levelLift` — a divided power morphism `T ⟶ S` on whose
  global sections `p^e` vanishes factors through `S_e`.

## Main results

* `Crystalline.GlobalCrystallineSituation.levelProj_condition` and
  `Crystalline.GlobalCrystallineSituation.levelTransition_condition` — the compatibilities with the
  structure morphisms, for the pairs `(S_e ⟶ S, 𝟙 X)` and `(S_m ⟶ S_e, 𝟙 X)`.
* `Crystalline.GlobalCrystallineSituation.levelTransition_comp_levelProj` — the levels form a
  tower under `S`.
* `Crystalline.GlobalCrystallineSituation.levelLift_comp_levelProj` — the factorization through
  `S_e`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

namespace DividedPowerScheme

attribute [local implicit_reducible] specDividedPowerScheme

/-- On global sections, the inverse of the canonical isomorphism `Y ≅ Spec Γ(Y, ⊤)` of an affine
scheme is the inverse of the `Γ`-`Spec` identification. -/
theorem isoSpec_inv_appTop_eq_ΓSpecIso_inv (Y : Scheme.{u}) [IsAffine Y] :
    Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := by
  have h : Y.isoSpec.hom.appTop ≫ Y.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop] at h
  exact (Iso.hom_comp_eq_id _).1 h

/-- `toSpecDividedPowerScheme` is natural in the divided power ring: composing with `Spec` of a
divided power morphism `g` is precomposing the divided power morphism with `g`. -/
theorem toSpecDividedPowerScheme_comp_specDividedPowerMap (X : DividedPowerScheme.{u})
    {A B : DividedPowerRing.{u}} (g : A ⟶ B) (φ : B ⟶ X.dividedPowers.toDividedPowerRing (op ⊤)) :
    toSpecDividedPowerScheme X B φ ≫ specDividedPowerMap g =
      toSpecDividedPowerScheme X A (g ≫ φ) := by
  apply toSpecDividedPowerScheme_hom_ext
  rw [toSpecDividedPowerScheme_appTop, DividedPowerScheme.Hom.comp_hom, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_assoc, specDividedPowerMap_hom]
  have h3 := congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g.toRingHom))
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h3
  rw [← h3, ← RingHom.comp_assoc, toSpecDividedPowerScheme_appTop]
  rfl

/-- `toSpecDividedPowerScheme` is natural in the divided power scheme. -/
theorem comp_toSpecDividedPowerScheme {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y)
    (A : DividedPowerRing.{u}) (φ : A ⟶ Y.dividedPowers.toDividedPowerRing (op ⊤)) :
    f ≫ toSpecDividedPowerScheme Y A φ =
      toSpecDividedPowerScheme X A (φ ≫ globalSectionsDPMorphism f) := by
  apply toSpecDividedPowerScheme_hom_ext
  rw [toSpecDividedPowerScheme_appTop, DividedPowerScheme.Hom.comp_hom, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_assoc, toSpecDividedPowerScheme_appTop]
  rfl

variable (Y : DividedPowerScheme.{u}) [IsAffine Y.scheme]

omit [IsAffine Y.scheme] in
/-- The underlying morphism of `specIsoOfIsAffine Y` is a morphism of divided power schemes: on
global sections it is the canonical map `Γ(Y, ⊤) ⟶ Γ(Spec Γ(Y, ⊤), ⊤)`, which is the divided
power morphism `specDividedPowerSchemeUnit`. -/
theorem specCarrier_eq :
    (specDividedPowerScheme (Y.dividedPowers.toDividedPowerRing (op ⊤))).scheme =
      Spec Γ(Y.scheme, ⊤) := rfl

/-- The underlying morphism of `specIsoOfIsAffine Y` is a morphism of divided power schemes: on
global sections it is the canonical map `Γ(Y, ⊤) ⟶ Γ(Spec Γ(Y, ⊤), ⊤)`, which is the divided
power morphism `specDividedPowerSchemeUnit`. -/
def specIsoOfIsAffineHom :
    specDividedPowerScheme (Y.dividedPowers.toDividedPowerRing (op ⊤)) ⟶ Y where
  hom := Y.scheme.isoSpec.inv
  compatible := isDPMorphism_app_of_appTop
    (X := specDividedPowerScheme (Y.dividedPowers.toDividedPowerRing (op ⊤))) Y.scheme.isoSpec.inv
    (isDPMorphism_of_eq
      (congrArg CommRingCat.Hom.hom (isoSpec_inv_appTop_eq_ΓSpecIso_inv Y.scheme)).symm
      (specDividedPowerSchemeUnit (Y.dividedPowers.toDividedPowerRing (op ⊤))).isDPMorphism)

/-- **An affine divided power scheme is the spectrum of its divided power ring of global
sections.**  The inverse is the morphism `Y ⟶ Spec(Γ(Y, ⊤), Γ(Y, ℐ), γ)` corresponding to the
identity under the universal property `specDividedPowerHomEquiv`, and the forward map is the
inverse of `Y ≅ Spec Γ(Y, ⊤)`, a morphism of divided power schemes by
`Crystalline.DividedPowerScheme.isDPMorphism_app_of_appTop`. -/
def specIsoOfIsAffine :
    specDividedPowerScheme (Y.dividedPowers.toDividedPowerRing (op ⊤)) ≅ Y where
  hom := specIsoOfIsAffineHom Y
  inv := toSpecDividedPowerScheme Y _ (𝟙 _)
  hom_inv_id := by
    apply toSpecDividedPowerScheme_hom_ext
    ext x
    have hx := RingHom.congr_fun
      (toSpecDividedPowerScheme_appTop Y (Y.dividedPowers.toDividedPowerRing (op ⊤)) (𝟙 _)) x
    change Y.scheme.isoSpec.inv.appTop.hom
      ((toSpecDividedPowerScheme Y _ (𝟙 _)).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.dividedPowers.toDividedPowerRing (op ⊤)))).inv.hom
          x)) =
        (Scheme.ΓSpecIso (CommRingCat.of (Y.dividedPowers.toDividedPowerRing (op ⊤)))).inv.hom x
    rw [show (toSpecDividedPowerScheme Y _ (𝟙 _)).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.dividedPowers.toDividedPowerRing (op ⊤)))).inv.hom
          x) = x from hx]
    exact RingHom.congr_fun
      (congrArg CommRingCat.Hom.hom (isoSpec_inv_appTop_eq_ΓSpecIso_inv Y.scheme)) x
  inv_hom_id := by
    refine DividedPowerScheme.Hom.ext (ext_of_isAffine (CommRingCat.hom_ext ?_))
    change (toSpecDividedPowerScheme Y _ (𝟙 _)).hom.appTop.hom.comp
      Y.scheme.isoSpec.inv.appTop.hom = RingHom.id _
    rw [isoSpec_inv_appTop_eq_ΓSpecIso_inv Y.scheme]
    exact toSpecDividedPowerScheme_appTop Y (Y.dividedPowers.toDividedPowerRing (op ⊤)) (𝟙 _)

end DividedPowerScheme

namespace GlobalCrystallineSituation

open DividedPowerScheme

variable (S : GlobalCrystallineSituation.{u})

/-- The divided power ideal `I = Γ(S, ℐ)` of global sections of the base. -/
abbrev baseIdeal : Ideal Γ(S.S.scheme, ⊤) := (S.S.dividedPowers.toDividedPowerRing (op ⊤)).ideal

/-- The divided powers `γ` on the ideal of global sections of the base. -/
abbrev baseDividedPowers : DividedPowers S.baseIdeal :=
  (S.S.dividedPowers.toDividedPowerRing (op ⊤)).dividedPowers

/-- **A finite divided power level of the base**: `(p^e) ⊆ Γ(S, ℐ)` is preserved by `γ`. -/
abbrev IsLevel (e : ℕ) : Prop := IsPAdicLevel S.baseIdeal S.baseDividedPowers S.p e

variable [IsAffine S.S.scheme]

/-- **The affine base is `Spec(A, I, γ)`**, `A = Γ(S, 𝒪_S)`: the instance of
`Crystalline.DividedPowerScheme.specIsoOfIsAffine` at the base, read on the divided power ring
`(A, I, γ)` of the finite level constructions. -/
def baseSpecIso : specBase S.baseIdeal S.baseDividedPowers ≅ S.S :=
  specIsoOfIsAffine S.S

/-- The structure morphism `X ⟶ Spec(A/I)` of `X` read in the closed fibre of `Spec(A, I, γ)`. -/
abbrev baseToClosedFiber : S.X ⟶ closedFiber (specBase S.baseIdeal S.baseDividedPowers) :=
  S.toClosedFiber ≫ closedFiberMap S.baseSpecIso.inv

/-- **The global crystalline situation `X/S_e`** at a finite divided power level `e` of an affine
base: `S_e = Spec(A/p^eA)` with the quotient divided powers, on the same scheme `X`. -/
abbrev levelSituation {e : ℕ} (he : S.IsLevel e) : GlobalCrystallineSituation.{u} where
  p := S.p
  S := pAdicLevelScheme S.baseIdeal S.baseDividedPowers S.p he
  algebraAtPrime := (pAdicLevelSituation S.baseIdeal S.baseDividedPowers S.p he S.X
    S.baseToClosedFiber S.prime_locallyNilpotent).algebraAtPrime
  X := S.X
  toClosedFiber := S.baseToClosedFiber ≫
    (pAdicLevelClosedFiberIso S.baseIdeal S.baseDividedPowers S.p he).inv
  prime_locallyNilpotent := S.prime_locallyNilpotent

/-- The level situation lives on the same scheme `X`. -/
@[simp]
theorem levelSituation_X {e : ℕ} (he : S.IsLevel e) : (S.levelSituation he).X = S.X := rfl

/-- The level situation has the same prime `p`. -/
@[simp]
theorem levelSituation_p {e : ℕ} (he : S.IsLevel e) : (S.levelSituation he).p = S.p := rfl

/-- The base of the level situation is `S_e = Spec(A/p^eA)`. -/
theorem levelSituation_S {e : ℕ} (he : S.IsLevel e) :
    (S.levelSituation he).S = pAdicLevelScheme S.baseIdeal S.baseDividedPowers S.p he := rfl

/-- **The divided power morphism `S_e ⟶ S`**: `Spec` of the quotient map `A ⟶ A/p^eA`, followed by
`Spec(A, I, γ) ≅ S`. -/
def levelProj {e : ℕ} (he : S.IsLevel e) : (S.levelSituation he).S ⟶ S.S :=
  pAdicLevelSchemeProj S.baseIdeal S.baseDividedPowers S.p he ≫ S.baseSpecIso.hom

/-- **The compatibility of `S_e ⟶ S` with the structure morphisms**, the hypothesis of change of
divided power base for the pair `(S_e ⟶ S, 𝟙 X)`. -/
theorem levelProj_condition {e : ℕ} (he : S.IsLevel e) :
    (S.levelSituation he).toClosedFiber ≫ closedFiberMap (S.levelProj he) =
      (𝟙 S.X : (S.levelSituation he).X ⟶ S.X) ≫ S.toClosedFiber := by
  have h : (S.levelSituation he).toClosedFiber ≫
      closedFiberMap (pAdicLevelSchemeProj S.baseIdeal S.baseDividedPowers S.p he) =
        𝟙 S.X ≫ S.baseToClosedFiber :=
    pAdicLevelSituation_changeBase_condition S.baseIdeal S.baseDividedPowers S.p he S.X
      S.baseToClosedFiber S.prime_locallyNilpotent
  rw [levelProj, closedFiberMap_comp, ← Category.assoc, h,
    Category.id_comp, Category.id_comp, Category.assoc, ← closedFiberMap_comp, Iso.inv_hom_id,
    closedFiberMap_id, Category.comp_id]

/-- **The transition `S_m ⟶ S_e`** of the levels of an affine base, for `m ≤ e`. -/
def levelTransition {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e) (hme : m ≤ e) :
    (S.levelSituation hm).S ⟶ (S.levelSituation he).S :=
  pAdicLevelTransitionScheme S.baseIdeal S.baseDividedPowers S.p hm he hme

/-- The compatibility of the transition `S_m ⟶ S_e` with the structure morphisms, for the pair
`(S_m ⟶ S_e, 𝟙 X)`. -/
theorem levelTransition_condition {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e) (hme : m ≤ e) :
    (S.levelSituation hm).toClosedFiber ≫ closedFiberMap (S.levelTransition hm he hme) =
      (𝟙 S.X : (S.levelSituation hm).X ⟶ (S.levelSituation he).X) ≫
        (S.levelSituation he).toClosedFiber :=
  pAdicLevelStep_changeBase_condition S.baseIdeal S.baseDividedPowers S.p hm he hme S.X
    S.baseToClosedFiber S.prime_locallyNilpotent

/-- **The levels form a tower under `S`**: `S_m ⟶ S_e ⟶ S` is `S_m ⟶ S`. -/
@[reassoc]
theorem levelTransition_comp_levelProj {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e)
    (hme : m ≤ e) : S.levelTransition hm he hme ≫ S.levelProj he = S.levelProj hm := by
  rw [levelTransition, levelProj, levelProj, pAdicLevelTransitionScheme_comp_proj_assoc]

/-- The transition of a level to itself is the identity. -/
theorem levelTransition_self {e : ℕ} (he : S.IsLevel e) :
    S.levelTransition he he le_rfl = 𝟙 _ := by
  show specDividedPowerMap (pAdicLevelTransition S.baseIdeal S.baseDividedPowers S.p he he
    le_rfl) = _
  rw [pAdicLevelTransition_self]
  exact DividedPowerScheme.Hom.ext (Spec.map_id _)

/-- The transitions of the levels compose. -/
@[reassoc]
theorem levelTransition_comp {k m e : ℕ} (hk : S.IsLevel k) (hm : S.IsLevel m) (he : S.IsLevel e)
    (hkm : k ≤ m) (hme : m ≤ e) :
    S.levelTransition hk hm hkm ≫ S.levelTransition hm he hme =
      S.levelTransition hk he (hkm.trans hme) := by
  show specDividedPowerMap _ ≫ specDividedPowerMap _ = specDividedPowerMap _
  rw [← specDividedPowerMap_comp, pAdicLevelTransition_comp]

/-- The ring map `A/p^eA ⟶ Γ(T, ⊤)` induced by a divided power morphism `b : T ⟶ S` on whose
global sections `p^e` vanishes. -/
def levelLiftRingHom {e : ℕ} (he : S.IsLevel e) {T : DividedPowerScheme.{u}} (b : T ⟶ S.S)
    (hT : ((S.p : ℕ) : Γ(T.scheme, ⊤)) ^ e = 0) :
    pAdicLevelRing S.baseIdeal S.baseDividedPowers S.p he →+* Γ(T.scheme, ⊤) :=
  Ideal.Quotient.lift _ b.hom.appTop.hom (by
    intro a ha
    rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_pow, map_natCast, hT, zero_mul])

omit [IsAffine S.S.scheme] in
/-- The ring map `A/p^eA ⟶ Γ(T, ⊤)` composed with the quotient map is the map `b` induces on
global sections. -/
theorem levelLiftRingHom_comp_mk {e : ℕ} (he : S.IsLevel e) {T : DividedPowerScheme.{u}}
    (b : T ⟶ S.S) (hT : ((S.p : ℕ) : Γ(T.scheme, ⊤)) ^ e = 0) :
    (S.levelLiftRingHom he b hT).comp
        (pAdicLevelProj S.baseIdeal S.baseDividedPowers S.p he).toRingHom =
      b.hom.appTop.hom :=
  Ideal.Quotient.lift_comp_mk _ _ _

/-- The ring map `A/p^eA ⟶ Γ(T, ⊤)` is a morphism of divided power rings: it is induced by the
divided power morphism `b` on global sections, through the quotient divided powers. -/
def levelLiftDPMorphism {e : ℕ} (he : S.IsLevel e) {T : DividedPowerScheme.{u}} (b : T ⟶ S.S)
    (hT : ((S.p : ℕ) : Γ(T.scheme, ⊤)) ^ e = 0) :
    pAdicLevelRing S.baseIdeal S.baseDividedPowers S.p he ⟶
      T.dividedPowers.toDividedPowerRing (op ⊤) :=
  DividedPowers.DPMorphism.mk' (f := S.levelLiftRingHom he b hT)
    (DividedPowers.IsDPMorphism.of_comp _ _ _
      (pAdicLevelProj S.baseIdeal S.baseDividedPowers S.p he).toRingHom _ rfl
      (pAdicLevelProj S.baseIdeal S.baseDividedPowers S.p he).isDPMorphism
      (isDPMorphism_of_eq (S.levelLiftRingHom_comp_mk he b hT).symm (b.compatible ⊤)))

/-- **A divided power morphism `T ⟶ S` on whose global sections `p^e` vanishes factors through
`S_e`**: the factorization is the morphism into `S_e = Spec(A/p^eA)` corresponding to the induced
divided power morphism `A/p^eA ⟶ Γ(T, ⊤)`. -/
def levelLift {e : ℕ} (he : S.IsLevel e) {T : DividedPowerScheme.{u}} (b : T ⟶ S.S)
    (hT : ((S.p : ℕ) : Γ(T.scheme, ⊤)) ^ e = 0) : T ⟶ (S.levelSituation he).S :=
  toSpecDividedPowerScheme T _ (S.levelLiftDPMorphism he b hT)

/-- **The factorization through `S_e` is a factorization of `b`.** -/
@[reassoc (attr := simp)]
theorem levelLift_comp_levelProj {e : ℕ} (he : S.IsLevel e) {T : DividedPowerScheme.{u}}
    (b : T ⟶ S.S) (hT : ((S.p : ℕ) : Γ(T.scheme, ⊤)) ^ e = 0) :
    S.levelLift he b hT ≫ S.levelProj he = b := by
  rw [levelProj, ← Category.assoc, ← Iso.eq_comp_inv]
  show toSpecDividedPowerScheme T _ (S.levelLiftDPMorphism he b hT) ≫
      specDividedPowerMap (pAdicLevelProj S.baseIdeal S.baseDividedPowers S.p he) =
    b ≫ toSpecDividedPowerScheme S.S _ (𝟙 _)
  rw [toSpecDividedPowerScheme_comp_specDividedPowerMap, comp_toSpecDividedPowerScheme]
  congr 1

end GlobalCrystallineSituation

end Crystalline
