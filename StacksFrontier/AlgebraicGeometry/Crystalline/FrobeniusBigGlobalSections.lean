module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ChangeBaseBigGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DerivedTensorBaseChange

/-!
# The canonical `σ`-semilinear Frobenius action on `Γ(CRIS(X/S), E)`

In Situation [Stacks, Tag 07N2] — `Crystalline.FCrystalSituation` — the Frobenius endofunctor
`u = (F_X)_cris` of the big crystalline category is change of divided power base along `Spec(σ)`
and the absolute Frobenius of `X`, and `(F_X)_cris^*` on sheaves of modules is restriction along
it, `Crystalline.FCrystalSituation.frobeniusModulePullback`.  An `F`-crystal
[Stacks, Tag 07N3] carries a map `F_E : (F_X)_cris^* E ⟶ E`.

Specialising `StacksFrontier/AlgebraicGeometry/Crystalline/ChangeBaseBigGlobalSections.lean` to that
endofunctor and composing with `F_E` gives, for every `F`-crystal `E`, a map

`Γ(CRIS(X/S), E) ⟶ Γ(CRIS(X/S), E)`

which is **`σ`-semilinear over `A = Γ(S, 𝒪_S)`**: `Crystalline.FCrystal.sectionsFrobenius` sends
`a • x` to `σ(a) • -` of its value, `Crystalline.FCrystal.sectionsFrobenius_smul_base`.  Bundled as
a morphism into a restriction of scalars along `σ` — which by Mathlib's
`ModuleCat.semilinearMapAddEquiv` is what `σ`-semilinearity *is* — that is
`Crystalline.FCrystal.globalSectionsFrobenius`.

## What this is, and what it is not

It is the **underived** form of the first arrow of [Stacks, Tag 07N5], the composite
`F_E ∘ (F_X)^*_cris` read on global sections rather than on `RΓ`, and it is canonical: no
parameter is carried and nothing is quantified over.  The module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusSemilinearAction.lean` records that
the library has no such bookkeeping for the Frobenius, because the small-site constructions of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMap.lean` all assume `g` is an open
immersion and the absolute Frobenius is not one; the construction here assumes nothing about `g`,
being carried out on the big site where change of base is an endofunctor.

It is **not** a term of `...SmallSite.SigmaSemilinearAction07N5`, and this file constructs no such
term.  That type is about `RΓ(Cris(X/S), -)`, the derived global sections on the **small** site,
and two steps separate the two:

1. *the derived step.*  `Γ(CRIS(X/S), -)` has to be replaced by its right derived functor, and the
   natural transformation above by one of derived functors.  The Frobenius pullback intervenes:
   deriving `Γ(CRIS(X/S), -) ⟶ Γ(CRIS(X/S), (F_X)_cris^*(-))` gives a map to
   `R(Γ(CRIS(X/S), -) ∘ (F_X)_cris^*)`, and comparing that with
   `RΓ(CRIS(X/S), -) ∘ (F_X)_cris^*` is a Grothendieck-spectral-sequence question about whether
   `(F_X)_cris^*` carries injectives to `Γ(CRIS(X/S), -)`-acyclics.
2. *the site step.*  `RΓ(CRIS(X/S), N)` has to be identified with `RΓ(Cris(X/S), i^{-1} N)` along
   the inclusion `i : Cris(X/S) ⥤ CRIS(X/S)`.  The library has the underived identification
   `...SmallSite.restrictModuleGlobalSectionsIso` and the opposite derived one
   `...SmallSite.derivedModuleGlobalSectionsObjIsoDirectImage`
   (`RΓ(Cris(X/S), M) ≅ RΓ(CRIS(X/S), R i_* M)`); the one needed here is open, and would follow
   from `Γ(Cris(X/S), -)`-acyclicity of `i^{-1} I` for `I` injective on `CRIS(X/S)`.  The stronger
   statement that `i^{-1}` preserves injectives is **false**, being equivalent to exactness of the
   module-level `i_!` (`Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits`).

## Main definitions

* `Crystalline.FCrystalSituation.frobeniusSectionRingHom` — the ring endomorphism of
  `Γ(CRIS(X/S), 𝒪_{X/S})` induced by the Frobenius endofunctor.
* `Crystalline.FCrystalSituation.frobeniusSections` — the comparison
  `Γ(CRIS(X/S), N) ⟶ Γ(CRIS(X/S), (F_X)_cris^* N)` on global sections.
* `Crystalline.FCrystal.sectionsFrobenius` — **the Frobenius action `F_E ∘ (F_X)^*_cris` on
  `Γ(CRIS(X/S), E)`**, the comparison followed by `F_E`.
* `Crystalline.FCrystal.globalSectionsFrobenius` — that action bundled as a morphism of
  `A`-modules into the restriction of scalars along `...SmallSite.baseChangeRingHom Spec(σ)`,
  which is `σ` by `...SmallSite.baseChangeRingHom_specSigma`; a morphism into such a restriction
  of scalars is what a `σ`-semilinear endomorphism of `Γ(CRIS(X/S), E)` is.

## Main results

* `Crystalline.FCrystalSituation.frobeniusSectionRingHom_comp_bigBaseRingHom` — **the ring
  endomorphism of `Γ(CRIS(X/S), 𝒪_{X/S})` restricts to `σ` on the base scalars.**  This is what
  makes the semilinearity below semilinearity over `σ` and not over some other endomorphism of
  `A`; the identification of `...SmallSite.baseChangeRingHom Spec(σ)` with `σ` is
  `...SmallSite.baseChangeRingHom_specSigma`.
* `Crystalline.FCrystal.sectionsFrobenius_smul_base` — **the action is `σ`-semilinear over `A`.**
* `Crystalline.FCrystal.sectionsFrobenius_val` — its value at an object of `CRIS(X/S)` is `F_E`
  applied to the value of the original section at the image of that object, which pins the action
  down completely.

## What is and is not proved

No `@[stacks]` attribute is placed here.  [Stacks, Tag 07N5] is `...SmallSite.statement07N5` of
`SmallSite/Frobenius07N5Theorem.lean`: the proposition `...SmallSite.Statement07N5`, whose one
parameter is a map of type `...SmallSite.FrobeniusMap07N5`, proved at the canonical map.  A term of
that type is now constructed in the library, as `...SmallSite.frobeniusMap07N5Canonical` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusDerivedGlobalSections.lean`, by
deriving the comparison this file specialises and composing with `F_E`; **this** file does not
construct one, and the two steps listed above are what separates it from that one.  Of the second
of them — identifying `R(Γ(CRIS(X/S), -) ∘ (F_X)_cris^*)` with `RΓ(CRIS(X/S), -) ∘ (F_X)_cris^*` —
that file records that it is not needed: the canonical comparison of [Stacks, Tag 05T2] runs in the
direction the construction uses.  What is proved here is that the *underived* arrow exists, is
canonical, and is `σ`-semilinear, and `...SmallSite.sectionsMap_frobeniusBigSections_val` is where
the derived arrow is pinned to `Crystalline.FCrystal.sectionsFrobenius_val` below.

## References

* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 07N3](https://stacks.math.columbia.edu/tag/07N3)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline

open GlobalCrystallineSituation

namespace FCrystalSituation

variable (T : FCrystalSituation.{u})

/-- **The ring endomorphism of `Γ(CRIS(X/S), 𝒪_{X/S})` induced by the Frobenius endofunctor** of
the big crystalline category: a compatible family of sections of the structure sheaf read at the
images of the objects under change of divided power base along `Spec(σ)` and the absolute
Frobenius of `X`. -/
def frobeniusSectionRingHom :
    ↥(SmallSite.bigCrystallineSectionRing T.global) →+*
      ↥(SmallSite.bigCrystallineSectionRing T.global) :=
  changeBaseSectionRingHom T.global T.global T.specSigma T.frobenius
    T.toClosedFiber_comp_closedFiberMap_specSigma

/-- **The comparison `Γ(CRIS(X/S), N) ⟶ Γ(CRIS(X/S), (F_X)_cris^* N)` on global sections.**  The
Frobenius pullback of sheaves of modules is restriction along the Frobenius endofunctor, so a
compatible family of sections of `N` read at the images of the objects is a global section of
`(F_X)_cris^* N`. -/
def frobeniusSections (N : SheafOfModules.{u} (crystallineStructureSheaf T.global))
    (x : N.sections) : (T.frobeniusModulePullback.obj N).sections :=
  changeBaseSections T.global T.global T.specSigma T.frobenius
    T.toClosedFiber_comp_closedFiberMap_specSigma N x

/-- The value of `frobeniusSections N x` at an object of `CRIS(X/S)` is the value of `x` at the
image of that object under the Frobenius endofunctor. -/
@[simp]
theorem frobeniusSections_val (N : SheafOfModules.{u} (crystallineStructureSheaf T.global))
    (x : N.sections) (A : (Thickening T.global)ᵒᵖ) :
    (T.frobeniusSections N x).val A =
      x.val (op ((frobeniusChangeBase T).obj A.unop)) := rfl

/-- The comparison on global sections is semilinear over `frobeniusSectionRingHom`. -/
theorem frobeniusSections_smul (N : SheafOfModules.{u} (crystallineStructureSheaf T.global))
    (a : ↥(SmallSite.bigCrystallineSectionRing T.global)) (x : N.sections) :
    T.frobeniusSections N (a • x) = T.frobeniusSectionRingHom a • T.frobeniusSections N x := rfl

/-- **The ring endomorphism of `Γ(CRIS(X/S), 𝒪_{X/S})` restricts to `σ` on the base scalars.**

The structure morphism to `S` of the image of an object under the Frobenius endofunctor is its own
structure morphism followed by `Spec(σ)`, and `Spec(σ)` on global sections of the base is `σ`
(`...SmallSite.baseChangeRingHom_specSigma`).  So pulling back the base scalar attached to `a ∈ A`
gives the base scalar attached to `σ(a)`.

This is what makes the Frobenius action on global sections `σ`-semilinear, rather than semilinear
over some unidentified endomorphism of `A`. -/
theorem frobeniusSectionRingHom_comp_bigBaseRingHom :
    (T.frobeniusSectionRingHom).comp (SmallSite.bigBaseRingHom T.global) =
      (SmallSite.bigBaseRingHom T.global).comp T.sigma.toRingHom := by
  rw [← SmallSite.baseChangeRingHom_specSigma]
  exact changeBaseSectionRingHom_comp_bigBaseRingHom

/-- The Frobenius ring endomorphism sends the base scalar of `a` to the base scalar of `σ(a)`. -/
private theorem frobeniusSectionRingHom_bigBaseRingHom (a : Γ(T.global.S.scheme, ⊤)) :
    T.frobeniusSectionRingHom (SmallSite.bigBaseRingHom T.global a) =
      SmallSite.bigBaseRingHom T.global (T.sigma a) :=
  DFunLike.congr_fun T.frobeniusSectionRingHom_comp_bigBaseRingHom a

/-- The comparison on global sections is `σ`-semilinear over the base ring `A = Γ(S, 𝒪_S)`. -/
theorem frobeniusSections_smul_base
    (N : SheafOfModules.{u} (crystallineStructureSheaf T.global))
    (a : Γ(T.global.S.scheme, ⊤)) (x : N.sections) :
    T.frobeniusSections N (SmallSite.bigBaseRingHom T.global a • x) =
      SmallSite.bigBaseRingHom T.global (T.sigma a) • T.frobeniusSections N x := by
  rw [frobeniusSections_smul, frobeniusSectionRingHom_bigBaseRingHom]

end FCrystalSituation

/-! ### The Frobenius action on the global sections of an `F`-crystal -/

namespace FCrystal

variable {T : FCrystalSituation.{u}} (E : FCrystal T)

/-- **The Frobenius action `F_E ∘ (F_X)^*_cris` on `Γ(CRIS(X/S), E)`.**  A global section of the
crystal is read at the images of the objects under the Frobenius endofunctor, which makes it a
global section of `(F_X)_cris^* E`, and then pushed along the `F`-crystal's structure map
`F_E : (F_X)_cris^* E ⟶ E`.

It is `σ`-semilinear over `A = Γ(S, 𝒪_S)` (`sectionsFrobenius_smul_base`), and it is the underived
form of the first arrow of [Stacks, Tag 07N5]. -/
def sectionsFrobenius (x : E.crystal.sections) : E.crystal.sections :=
  SheafOfModules.sectionsMap E.frobenius (T.frobeniusSections E.crystal x)

/-- **The value of the Frobenius action at an object of `CRIS(X/S)`** is `F_E` applied to the value
of the original section at the image of that object.  This pins the action down completely. -/
@[simp]
theorem sectionsFrobenius_val (x : E.crystal.sections) (A : (Thickening T.global)ᵒᵖ) :
    (E.sectionsFrobenius x).val A =
      E.frobenius.val.app A (x.val (op ((FCrystalSituation.frobeniusChangeBase T).obj A.unop))) :=
  rfl

/-- The Frobenius action on global sections is additive. -/
theorem sectionsFrobenius_add (x y : E.crystal.sections) :
    E.sectionsFrobenius (x + y) = E.sectionsFrobenius x + E.sectionsFrobenius y :=
  Subtype.ext (funext fun A => (E.frobenius.val.app A).hom.map_add _ _)

/-- The Frobenius action on global sections is semilinear over `frobeniusSectionRingHom`: the
comparison is semilinear over it and `F_E` is a morphism of sheaves of modules. -/
theorem sectionsFrobenius_smul (a : ↥(SmallSite.bigCrystallineSectionRing T.global))
    (x : E.crystal.sections) :
    E.sectionsFrobenius (a • x) = T.frobeniusSectionRingHom a • E.sectionsFrobenius x :=
  Subtype.ext (funext fun A => (E.frobenius.val.app A).hom.map_smul _ _)

/-- **The Frobenius action on global sections is `σ`-semilinear over `A = Γ(S, 𝒪_S)`**: it carries
`a • x` to `σ(a) • F(x)`.  This is the semilinearity [Stacks, Tag 07N5] asks of its first arrow,
read on global sections. -/
theorem sectionsFrobenius_smul_base (a : Γ(T.global.S.scheme, ⊤)) (x : E.crystal.sections) :
    E.sectionsFrobenius (SmallSite.bigBaseRingHom T.global a • x) =
      SmallSite.bigBaseRingHom T.global (T.sigma a) • E.sectionsFrobenius x := by
  rw [sectionsFrobenius_smul, T.frobeniusSectionRingHom_bigBaseRingHom]

/-- **The Frobenius action on `Γ(CRIS(X/S), E)` as a `σ`-semilinear endomorphism of `A`-modules.**

A morphism into a restriction of scalars along a ring endomorphism of `A` is exactly a map
semilinear over that endomorphism, by Mathlib's `ModuleCat.semilinearMapAddEquiv`, so this is the
underived first arrow of [Stacks, Tag 07N5] in the shape that arrow has to have.  It is canonical:
nothing is carried as a parameter.

The endomorphism is spelled `...SmallSite.baseChangeRingHom Spec(σ)`, which **is** `σ` by
`...SmallSite.baseChangeRingHom_specSigma`; `sectionsFrobenius_smul_base` is the semilinearity
stated with `σ` itself. -/
def globalSectionsFrobenius :
    (crystalBaseModuleGlobalSections T.global).obj E.crystal ⟶
      (ModuleCat.restrictScalars (SmallSite.baseChangeRingHom T.specSigma)).obj
        ((crystalBaseModuleGlobalSections T.global).obj E.crystal) :=
  changeBaseBaseGlobalSectionsMap (f := T.specSigma) (g := T.frobenius)
      (h := T.toClosedFiber_comp_closedFiberMap_specSigma) E.crystal ≫
    (ModuleCat.restrictScalars (SmallSite.baseChangeRingHom T.specSigma)).map
      ((crystalBaseModuleGlobalSections T.global).map E.frobenius)

/-- The bundled Frobenius action is `Crystalline.FCrystal.sectionsFrobenius`. -/
@[simp]
theorem globalSectionsFrobenius_apply (x : E.crystal.sections) :
    E.globalSectionsFrobenius x = E.sectionsFrobenius x := rfl

end FCrystal

end Crystalline

end

end
