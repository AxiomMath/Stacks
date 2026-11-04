module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalEquivalence
public import StacksFrontier.AlgebraicGeometry.Crystalline.SpecSchemeThickening

/-!
# The chaotic subsite of thickenings of an affine space is the little affine crystalline category

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine.  The chaotic
subsite `𝒞 ⊆ Cris(X/S)` of [Stacks, Tag 07JK] is the full subcategory of the divided power
thickenings of the *whole* of `X`; the little affine crystalline category
`Cris(Γ(X, ⊤)/Γ(S, ⊤))` of [Stacks, Tag 07HM] is the full subcategory of the divided power
thickenings `(B, J, δ)` of `Γ(X, ⊤)` over `(Γ(S, ⊤), I(⊤), γ)` whose structural map
`Γ(X, ⊤) → B/J` is bijective.

This file proves that the affine-to-global bridge of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalBridge.lean` is **an equivalence**

```
𝒞ᵒᵖ  ≌  Cris(Γ(X, ⊤)/Γ(S, ⊤)).
```

Faithfulness is the bridge's own `faithful_wholeSiteToAffine`; fullness is
`Crystalline.GlobalCrystallineSituation.full_wholeSiteToAffine` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalEquivalence.lean`; what is proved
here is essential surjectivity.  Given `(B, J, δ)` in `Cris(Γ(X, ⊤)/Γ(S, ⊤))`, the object of `𝒞`
mapping to it is `Spec (B/J) ↪ Spec (B, J, δ)`: the ambient divided power scheme is
`Crystalline.DividedPowerScheme.specDividedPowerScheme (B, J, δ)`, the thickening of schemes is
`Crystalline.DividedPowerScheme.specSchemeThickening`, the thickened scheme is `Spec (B/J) ≅ X`
because `Γ(X, ⊤) → B/J` is bijective and `X` is affine, and the map to the base is `Spec` of
`fromBase`.

## Main definitions

* `Crystalline.DividedPowerThickening.isoOfRingIso` — an isomorphism of the ambient divided power
  rings compatible with the structural maps is an isomorphism of divided power thickenings.
* `Crystalline.GlobalCrystallineSituation.specThickeningOfAffine` — **the object of `CRIS(X/S)`
  attached to an object of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))`**, and
  `Crystalline.GlobalCrystallineSituation.specWholeSpaceThickening`, the same object read in the
  chaotic subsite `𝒞`.
* `Crystalline.GlobalCrystallineSituation.wholeThickeningToAffineSpecIso` — the comparison
  isomorphism identifying the image of that object under the bridge with `(B, J, δ)`.
* `Crystalline.GlobalCrystallineSituation.wholeSiteToLittleAffine` — **the bridge as a functor
  `𝒞ᵒᵖ ⥤ Cris(Γ(X, ⊤)/Γ(S, ⊤))`**, and
  `Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`, **the equivalence**.

## Main results

* `Crystalline.DividedPowerScheme.schemeIsoSpec_inv_appTop` — the inverse of `Scheme.isoSpec` acts
  on global sections as the inverse of `Scheme.ΓSpecIso`.
* `Crystalline.GlobalCrystallineSituation.locallyNilpotent_ideal` — the divided power ideal of an
  object of `CRIS(C/A)` is locally nilpotent, by [Stacks, Tag 07GR].
* `Crystalline.GlobalCrystallineSituation.specOverBase` — the square of [Stacks, Tag 07I6] for the
  data attached to `(B, J, δ)`, from the compatibility `commutes` of [Stacks, Tag 07HM].
* `Crystalline.GlobalCrystallineSituation.isIso_specToX` — the thickened scheme of that object is
  the whole of `X`, so the object lies in the chaotic subsite `𝒞`.
* `Crystalline.GlobalCrystallineSituation.exists_iso_wholeSiteToAffine` — **the bridge is
  essentially surjective onto `Cris(Γ(X, ⊤)/Γ(S, ⊤))`.**
* `Crystalline.GlobalCrystallineSituation.isEquivalence_wholeSiteToLittleAffine` — **the bridge
  into the little affine crystalline category is an equivalence.**

## What is and is not proved

No tag attribute is placed in this file.  [Stacks, Tag 07JK] is a statement about *cohomology*,
and the equivalence proved here is one of its inputs, not the tag.

The target of the equivalence is the **little** category `Cris(Γ(X, ⊤)/Γ(S, ⊤))`, not the big one
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))`, and that is forced: every object in the image of the bridge is
crystalline, by `isCrystalline_wholeThickeningToAffine`, so the bridge into the big category is
full and faithful but not essentially surjective.

Both affineness hypotheses are used.  `IsAffine S.X` makes the ambient scheme of an object of `𝒞`
affine (by [Stacks, Tag 06AD]) and identifies `Spec (B/J)` with `X`; `IsAffine S.S.scheme` is what
lets a morphism into the base be recovered from its effect on global sections, and it is used both
for fullness and for the map `Spec (B, J, δ) ⟶ S` of the object constructed here.  [Stacks,
Tag 07JK] assumes both.

## References

* [Stacks Project, Tag 07GR](https://stacks.math.columbia.edu/tag/07GR)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.DividedPowerScheme

/-- **The inverse of `Scheme.isoSpec` acts on global sections as the inverse of
`Scheme.ΓSpecIso`.** -/
theorem schemeIsoSpec_inv_appTop (X : Scheme.{u}) [IsAffine X] :
    (Scheme.isoSpec X).inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  have h := congrArg Scheme.Hom.appTop (Scheme.isoSpec X).inv_hom_id
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, Scheme.isoSpec_hom,
    Scheme.toSpecΓ_appTop] at h
  exact (cancel_epi (Scheme.ΓSpecIso Γ(X, ⊤)).hom).mp
    (h.trans (Scheme.ΓSpecIso Γ(X, ⊤)).hom_inv_id.symm)

/-- `Scheme.ΓSpecIso` followed by its inverse is the identity, read on elements. -/
theorem ΓSpecIso_hom_inv_apply (R : CommRingCat.{u}) (b : R) :
    (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom b) = b :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).inv_hom_id b

end Crystalline.DividedPowerScheme

namespace Crystalline.DividedPowerThickening

variable {Sit : AffineCrystallineSituation.{u, u}}

/-- **An isomorphism of the ambient divided power rings compatible with the structural maps is an
isomorphism of divided power thickenings.**  The two compatibilities of [Stacks, Tag 07HM] for the
inverse follow from those for the isomorphism. -/
def isoOfRingIso {X Y : DividedPowerThickening.{u, u, u} Sit} (e : X.ring ≅ Y.ring)
    (hbase : e.hom.comp X.fromBase = Y.fromBase)
    (hquot : (DividedPowerRing.quotientRingHom e.hom).comp X.toQuotient = Y.toQuotient) :
    X ≅ Y where
  hom := ⟨e.hom, hbase, hquot⟩
  inv :=
    { hom := e.inv
      fromBase_comp := by
        apply DividedPowers.DPMorphism.ext
        funext a
        have h2 := congrFun (congrArg (fun φ : DividedPowers.DPMorphism Sit.A.dividedPowers
          Y.ring.dividedPowers ↦ (φ : ↥Sit.A → ↥Y.ring)) hbase) a
        change e.inv (Y.fromBase a) = X.fromBase a
        rw [← h2]
        exact ConcreteCategory.congr_hom e.hom_inv_id _
      toQuotient_comp := by
        refine RingHom.ext fun c ↦ ?_
        have hid : ∀ q, DividedPowerRing.quotientRingHom e.inv
            (DividedPowerRing.quotientRingHom e.hom q) = q := by
          intro q
          have hc := DividedPowerRing.quotientRingHom_comp e.hom e.inv
          rw [e.hom_inv_id, DividedPowerRing.quotientRingHom_id] at hc
          exact (RingHom.congr_fun hc q).symm
        change DividedPowerRing.quotientRingHom e.inv (Y.toQuotient c) = X.toQuotient c
        rw [← RingHom.congr_fun hquot c]
        exact hid _ }
  hom_inv_id := DividedPowerThickening.Hom.ext e.hom_inv_id
  inv_hom_id := DividedPowerThickening.Hom.ext e.inv_hom_id

end Crystalline.DividedPowerThickening

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  (T : DividedPowerThickening.{u, u, u} (affineSituation S hp))

omit [IsAffine S.X] in
/-- **The divided power ideal of an object of `CRIS(C/A)` is locally nilpotent.**  The prime `p`
is nilpotent in the ambient ring `B`, so by [Stacks, Tag 07GR] every element of the divided power
ideal `J` is nilpotent. -/
theorem locallyNilpotent_ideal : T.ring.ideal.LocallyNilpotent := by
  refine (DividedPowers.locallyNilpotent_iff_isNilpotent_natCast S.prime.out
    T.ring.dividedPowers ?_).mpr T.prime_nilpotent
  have h := T.prime_nilpotent.map (Ideal.Quotient.mk T.ring.ideal)
  rwa [map_natCast] at h

/-- The structure map `Spec (B/J) ⟶ X` of the object attached to `(B, J, δ)`: `Spec` of the
structural map `Γ(X, ⊤) → B/J`, followed by the inverse of `X ≅ Spec Γ(X, ⊤)`. -/
def specToX : Spec (CommRingCat.of (↥T.ring ⧸ T.ring.ideal)) ⟶ S.X :=
  Spec.map (CommRingCat.ofHom T.toQuotient :
      Γ(S.X, ⊤) ⟶ CommRingCat.of (↥T.ring ⧸ T.ring.ideal)) ≫
    (Scheme.isoSpec S.X).inv

/-- On global sections, `specToX` is the structural map `Γ(X, ⊤) → B/J`. -/
theorem appTop_specToX :
    (specToX hp T).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (↥T.ring ⧸ T.ring.ideal))).hom =
      CommRingCat.ofHom T.toQuotient := by
  rw [specToX, Scheme.Hom.comp_appTop, DividedPowerScheme.schemeIsoSpec_inv_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

/-- `specToX` read on an element of `Γ(X, ⊤)`. -/
theorem appTop_specToX_apply (y : Γ(S.X, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (↥T.ring ⧸ T.ring.ideal))).hom.hom
        ((specToX hp T).appTop.hom y) =
      T.toQuotient y :=
  ConcreteCategory.congr_hom (appTop_specToX hp T) y

omit [IsAffine S.X] in
/-- The immersion `Spec (B/J) ↪ Spec B` read on an element of `Γ(Spec B, ⊤)`. -/
theorem appTop_specQuotientImmersion_apply
    (x : Γ(Spec (CommRingCat.of ↥T.ring), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (↥T.ring ⧸ T.ring.ideal))).hom.hom
        ((DividedPowerScheme.specQuotientImmersion T.ring).appTop.hom x) =
      Ideal.Quotient.mk T.ring.ideal
        ((Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).hom.hom x) :=
  ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk T.ring.ideal))) x

/-- **The compatibility on global sections that makes the object attached to `(B, J, δ)` an
object over `X`.**  A lift `β ∈ B` of `T.toQuotient y` is sent by the immersion
`Spec (B/J) ↪ Spec B` to the image of `y` under `specToX`.  Both sides are computed by the
naturality of `Scheme.ΓSpecIso`, and `Γ(Spec (B/J), ⊤) ≅ B/J` is injective. -/
theorem appTop_specQuotientImmersion_eq {β : T.ring} {y : Γ(S.X, ⊤)}
    (h : Ideal.Quotient.mk T.ring.ideal β = T.toQuotient y) :
    (DividedPowerScheme.specQuotientImmersion T.ring).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).inv.hom β) =
      (specToX hp T).appTop.hom y := by
  have hinj : Function.Injective
      (Scheme.ΓSpecIso (CommRingCat.of (↥T.ring ⧸ T.ring.ideal))).hom.hom :=
    (ConcreteCategory.bijective_of_isIso _).injective
  refine hinj ?_
  rw [appTop_specQuotientImmersion_apply, appTop_specToX_apply,
    DividedPowerScheme.ΓSpecIso_hom_inv_apply, h]

/-- **The thickened scheme of the object attached to `(B, J, δ)` is the whole of `X`** as soon as
the structural map `Γ(X, ⊤) → B/J` is bijective, i.e. as soon as `(B, J, δ)` is an object of the
little category `Cris(Γ(X, ⊤)/Γ(S, ⊤))`. -/
theorem isIso_specToX (hT : Function.Bijective T.toQuotient) : IsIso (specToX hp T) := by
  have h1 : IsIso (CommRingCat.ofHom T.toQuotient :
      Γ(S.X, ⊤) ⟶ CommRingCat.of (↥T.ring ⧸ T.ring.ideal)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hT
  exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom T.toQuotient :
    Γ(S.X, ⊤) ⟶ CommRingCat.of (↥T.ring ⧸ T.ring.ideal)) ≫ (Scheme.isoSpec S.X).inv))

section Object

variable [IsAffine S.S.scheme]

/-- The morphism of divided power rings `Γ(S, ⊤) ⟶ Γ(Spec B, ⊤)` attached to the structural
map `fromBase` of an object of `CRIS(C/A)`. -/
def specFromBase : baseSectionsRing S ⟶
    (DividedPowerScheme.specDividedPowerScheme T.ring).dividedPowers.toDividedPowerRing
      (op ⊤) :=
  T.fromBase ≫ (DividedPowerScheme.specSectionsRingIso T.ring).hom

/-- The divided power morphism `Spec (B, J, δ) ⟶ (S, I, γ)` attached to the structural map
`fromBase` of an object of `CRIS(C/A)`.  The base being affine, it exists by
`Crystalline.DividedPowerScheme.homOfSectionsDPMorphism`. -/
def specThickeningToBase : DividedPowerScheme.specDividedPowerScheme T.ring ⟶ S.S :=
  DividedPowerScheme.homOfSectionsDPMorphism (specFromBase hp T)

/-- **The square of [Stacks, Tag 07I6] commutes for the data attached to `(B, J, δ)`.**  Both
ways around the square are morphisms into the affine base `S`, so they agree as soon as they do
on global sections, where the identity is the compatibility `commutes` of [Stacks, Tag 07HM]. -/
theorem specOverBase :
    DividedPowerScheme.specQuotientImmersion T.ring ≫ (specThickeningToBase hp T).hom =
      specToX hp T ≫ sourceToBase S := by
  refine ext_of_isAffine ?_
  have hB : (specThickeningToBase hp T).hom.appTop =
      CommRingCat.ofHom (specFromBase hp T).toRingHom :=
    DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop _
  have hL : (DividedPowerScheme.specQuotientImmersion T.ring ≫
        (specThickeningToBase hp T).hom).appTop =
      (specThickeningToBase hp T).hom.appTop ≫
        (DividedPowerScheme.specQuotientImmersion T.ring).appTop :=
    Scheme.Hom.comp_appTop _ _
  rw [hL, Scheme.Hom.comp_appTop, hB]
  refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
  exact appTop_specQuotientImmersion_eq hp T (DFunLike.congr_fun T.commutes c)

/-- **The object of `CRIS(X/S)` attached to an object `(B, J, δ)` of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))`.**
The ambient divided power scheme is `Spec (B, J, δ)`, the thickened scheme is `Spec (B/J)`, the
map to the divided power base is `Spec` of `fromBase`, and the map to `X` is `Spec` of the
structural map `Γ(X, ⊤) → B/J` followed by `Spec Γ(X, ⊤) ≅ X`. -/
def specThickeningOfAffine : Thickening S where
  thickening := DividedPowerScheme.specSchemeThickening T.ring (locallyNilpotent_ideal hp T)
  toBase := specThickeningToBase hp T
  toX := specToX hp T
  over_base := specOverBase hp T

/-- The map to `X` of `specThickeningOfAffine` is `specToX`. -/
@[simp]
theorem specThickeningOfAffine_toX :
    (specThickeningOfAffine hp T).toX = specToX hp T := rfl

/-- The map to the divided power base of `specThickeningOfAffine` is `specThickeningToBase`. -/
@[simp]
theorem specThickeningOfAffine_toBase :
    (specThickeningOfAffine hp T).toBase = specThickeningToBase hp T := rfl

/-- **The object of the chaotic subsite `𝒞` of [Stacks, Tag 07JK] attached to an object of
`Cris(Γ(X, ⊤)/Γ(S, ⊤))`.** -/
def specWholeSpaceThickening (hT : Function.Bijective T.toQuotient) :
    SmallSite.WholeSpaceThickening S :=
  haveI hiso : IsIso (specThickeningOfAffine hp T).toX := isIso_specToX hp T hT
  ⟨⟨specThickeningOfAffine hp T, inferInstance⟩, hiso⟩

/-- The object of `CRIS(X/S)` underlying `specWholeSpaceThickening` is
`specThickeningOfAffine`. -/
@[simp]
theorem specWholeSpaceThickening_obj_obj (hT : Function.Bijective T.toQuotient) :
    (specWholeSpaceThickening hp T hT).obj.obj = specThickeningOfAffine hp T := rfl

/-- **The thickened scheme of the object of `CRIS(X/S)` attached to an object of
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))` is affine**, being `Spec (B/J)`. -/
instance isAffine_specThickeningOfAffine_source :
    IsAffine (specThickeningOfAffine hp T).thickening.source :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (↥T.ring ⧸ T.ring.ideal))))

/-- **A class of `Γ(Spec B, ⊤)/I(⊤)` in the image of the structural map is represented by a lift
in `Γ(Spec B, ⊤)` of the corresponding element of `B`.**  The restriction isomorphism of
`Crystalline.SchemeThickening.sectionsQuotientEquiv` sends that class to the image of `y` under
`specToX`, which is `appTop_specQuotientImmersion_eq`. -/
theorem wholeSectionsToQuotient_eq_mk {β : T.ring} {y : Γ(S.X, ⊤)}
    (hβ : Ideal.Quotient.mk T.ring.ideal β = T.toQuotient y) :
    wholeSectionsToQuotient (specThickeningOfAffine hp T) y =
      Ideal.Quotient.mk
        (SchemeThickening.sectionsIdeal (specThickeningOfAffine hp T).thickening)
        ((Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).inv.hom β) := by
  refine (specThickeningOfAffine hp T).thickening.sectionsQuotientEquiv.injective ?_
  rw [sectionsQuotientEquiv_wholeSectionsToQuotient]
  exact (appTop_specQuotientImmersion_eq hp T hβ).symm.trans
    (SchemeThickening.sectionsQuotientEquiv_mk (specThickeningOfAffine hp T).thickening
      ((Scheme.ΓSpecIso (CommRingCat.of ↥T.ring)).inv.hom β)).symm

section WithIso

variable [IsIso (specThickeningOfAffine hp T).toX]

/-- The image under the bridge of the object of `𝒞` attached to `(B, J, δ)`. -/
abbrev specImage : DividedPowerThickening.{u, u, u} (affineSituation S hp) :=
  wholeThickeningToAffine hp (specThickeningOfAffine hp T)

/-- **The structural maps of `(B, J, δ)` and of its image under the bridge correspond under
`Crystalline.DividedPowerScheme.specSectionsRingIso`.**  This is the second of the two
compatibilities of [Stacks, Tag 07HM] for the comparison isomorphism. -/
theorem quotientMap_specSectionsRingIso_hom_comp :
    (DividedPowerRing.quotientRingHom (A := T.ring) (B := (specImage hp T).ring)
        (DividedPowerScheme.specSectionsRingIso T.ring).hom).comp T.toQuotient =
      (specImage hp T).toQuotient := by
  refine RingHom.ext fun y ↦ ?_
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (T.toQuotient y)
  show DividedPowerRing.quotientRingHom (A := T.ring) (B := (specImage hp T).ring)
    (DividedPowerScheme.specSectionsRingIso T.ring).hom (T.toQuotient y) = _
  rw [← hβ]
  refine (DividedPowerRing.quotientRingHom_mk (A := T.ring) (B := (specImage hp T).ring)
    (DividedPowerScheme.specSectionsRingIso T.ring).hom β).trans ?_
  exact (wholeSectionsToQuotient_eq_mk hp T hβ).symm

/-- **The image under the bridge of the object attached to `(B, J, δ)` is `(B, J, δ)`.**  The
underlying isomorphism of divided power rings is
`Crystalline.DividedPowerScheme.specSectionsRingIso`; its compatibility with `fromBase` is the
definition of the object's map to the base, and its compatibility with the structural maps is
`quotientMap_wholeSectionsToQuotient`. -/
def wholeThickeningToAffineSpecIso : specImage hp T ≅ T :=
  (DividedPowerThickening.isoOfRingIso (X := T) (Y := specImage hp T)
    (DividedPowerScheme.specSectionsRingIso T.ring)
    (DividedPowerScheme.globalSectionsDPMorphism_homOfSectionsDPMorphism
      (specFromBase hp T)).symm
    (quotientMap_specSectionsRingIso_hom_comp hp T)).symm

end WithIso

/-- **The affine-to-global bridge is essentially surjective onto the little affine crystalline
category `Cris(Γ(X, ⊤)/Γ(S, ⊤))`.**  Every object `(B, J, δ)` of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` whose
structural map `Γ(X, ⊤) → B/J` is bijective is isomorphic to the image under the bridge of the
object `Spec (B/J) ↪ Spec (B, J, δ)` of the chaotic subsite `𝒞`. -/
theorem exists_iso_wholeSiteToAffine (hT : Function.Bijective T.toQuotient) :
    ∃ A : (SmallSite.WholeSpaceThickening S)ᵒᵖ,
      Nonempty ((wholeSiteToAffine hp).obj A ≅ T) :=
  have : IsIso (specThickeningOfAffine hp T).toX := isIso_specToX hp T hT
  ⟨op (specWholeSpaceThickening hp T hT), ⟨wholeThickeningToAffineSpecIso hp T⟩⟩

end Object

section Equivalence

variable [IsAffine S.S.scheme]

/-- The property cutting out the little affine crystalline category `Cris(Γ(X, ⊤)/Γ(S, ⊤))`
inside `CRIS(Γ(X, ⊤)/Γ(S, ⊤))`: the structural map `C → B/J` is bijective. -/
abbrev affineIsCrystalline :
    ObjectProperty (DividedPowerThickening.{u, u, u} (affineSituation S hp)) :=
  DividedPowerThickening.IsCrystalline

/-- **The affine-to-global bridge, as a functor into the little affine crystalline category
`Cris(Γ(X, ⊤)/Γ(S, ⊤))`.**  It lands there by
`Crystalline.GlobalCrystallineSituation.isCrystalline_wholeThickeningToAffine`. -/
def wholeSiteToLittleAffine :
    (SmallSite.WholeSpaceThickening S)ᵒᵖ ⥤ (affineIsCrystalline hp).FullSubcategory :=
  (affineIsCrystalline hp).lift (wholeSiteToAffine hp) fun A ↦ by
    have : IsIso ((wholeToBig S).obj A.unop).toX := A.unop.property
    exact isCrystalline_wholeThickeningToAffine hp _

/-- Composing the bridge into `Cris(Γ(X, ⊤)/Γ(S, ⊤))` with the inclusion into
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))` gives the bridge back. -/
def wholeSiteToLittleAffineCompι :
    wholeSiteToLittleAffine hp ⋙ (affineIsCrystalline hp).ι ≅ wholeSiteToAffine hp :=
  (affineIsCrystalline hp).liftCompιIso _ _

/-- The bridge into `Cris(Γ(X, ⊤)/Γ(S, ⊤))` is faithful, the inclusion of the full subcategory
being faithful. -/
instance faithful_wholeSiteToLittleAffine : (wholeSiteToLittleAffine hp).Faithful :=
  Functor.Faithful.of_comp_iso (wholeSiteToLittleAffineCompι hp)

/-- The bridge into `Cris(Γ(X, ⊤)/Γ(S, ⊤))` is full, the inclusion of the full subcategory being
fully faithful. -/
instance full_wholeSiteToLittleAffine : (wholeSiteToLittleAffine hp).Full :=
  Functor.Full.of_comp_faithful_iso (wholeSiteToLittleAffineCompι hp)

/-- **The affine-to-global bridge is essentially surjective onto `Cris(Γ(X, ⊤)/Γ(S, ⊤))`.** -/
instance essSurj_wholeSiteToLittleAffine : (wholeSiteToLittleAffine hp).EssSurj where
  mem_essImage Y := by
    obtain ⟨A, ⟨e⟩⟩ := exists_iso_wholeSiteToAffine hp Y.obj Y.property
    exact ⟨A, ⟨(affineIsCrystalline hp).fullyFaithfulι.preimageIso e⟩⟩

/-- **The affine-to-global bridge is an equivalence onto the little affine crystalline category.**
The chaotic subsite `𝒞` of [Stacks, Tag 07JK], for `X` and `S` affine, is anti-equivalent to the
little crystalline category `Cris(Γ(X, ⊤)/Γ(S, ⊤))` of [Stacks, Tag 07HM]. -/
instance isEquivalence_wholeSiteToLittleAffine :
    (wholeSiteToLittleAffine hp).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- **The equivalence `𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))`.** -/
def wholeSiteEquivLittleAffine :
    (SmallSite.WholeSpaceThickening S)ᵒᵖ ≌ (affineIsCrystalline hp).FullSubcategory :=
  (wholeSiteToLittleAffine hp).asEquivalence

end Equivalence

end Crystalline.GlobalCrystallineSituation

end

end
