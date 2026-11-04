module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceBundledDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# The difference of two lifts, as a section of the acting sheaf

Let `G ⊂ X'` be a first-order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : X ⟶ X'`, let `q : Y' ⟶ Bb` be a morphism of algebraic spaces and let `a', b' : X' ⟶ Y'` be
two morphisms with `i ≫ a' = i ≫ b'`.
`StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDerivation` and
`StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceBundledDerivation` produce the derivation
`D` of [Stacks Project, Tag 0618] out of the difference of the two structure maps, as a
`PresheafOfModules.Derivation'` of `(b')^{-1}𝒪_{Y'}` with values in the defining ideal of the
thickening, on the small étale site of `X'`.

This file carries that derivation to the shape the acting sheaf of [Stacks Project, Tag 061D]
has: an `𝒪_X`-linear map

`a^*Ω_{Y'/Bb} ⟶ 𝒞_{X/X'}`,  `a = i ≫ b'`,

which by `AlgebraicGeometry.Space.smallEtaleInternalHomSectionsEquiv` is a global section of
`AlgebraicGeometry.Space.liftActionSheaf`.  That passage is what the "What is not done here"
section of `StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceBundledDerivation` lists as owed,
and it is what makes the difference of two lifts a *uniqueness criterion* for the chartwise
action of `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`: the difference
is defined with no reference to a chart presentation at all.

## Main definitions

* `AlgebraicGeometry.Space.definingIdealHomOfDerivation`: the morphism
  `(b')^*Ω_{Y'/Bb} ⟶ 𝓘` attached to such a derivation, on the small étale site of `X'`.
* `AlgebraicGeometry.Space.liftPairActionSectionOfDerivation`: the same read along the inclusion,
  as a morphism `a^*Ω_{Y'/Bb} ⟶ 𝒞_{X/X'}` on the small étale site of `X`.
* `AlgebraicGeometry.Space.liftPairGlobalSectionOfDerivation`: the same as a global section of
  `AlgebraicGeometry.Space.liftActionSheaf`.
* `AlgebraicGeometry.Space.liftPairDerivationSecond`: the derivation `D` of [Stacks Project,
  Tag 0618] for the pair of structure maps of `a'` and `b'`, with the coefficients taken over the
  structure map of `b'`.
* `AlgebraicGeometry.Space.liftPairActionSection` and
  `AlgebraicGeometry.Space.liftPairGlobalSection`: the composite, i.e. the difference of two
  lifts read as a section of the acting sheaf.

## Main results

* `AlgebraicGeometry.Space.liftDifferenceCoefficients_eq_liftPairCoefficients`: the coefficients
  of the bundled derivation, taken at the structure map of `b'`, **are** the restriction of
  scalars at which the transposition of derivations of [Stacks Project, Tag 08TQ] is stated, by
  `rfl`.

## Implementation notes

**The three bijections, and why none of them needs the thickening.**  The passage from the
inverse-image derivation to the morphism out of `(b')^*Ω_{Y'/Bb}` is the composite of the first
three of the four bijections of
`StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceLocalization`, run
backwards: the transposition of derivations along the morphism of small étale topoi of `b'`
(`Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv`, the module-level half of
[Stacks Project, Tag 08TQ]), the universal property of `Ω_{Y'/Bb}` ([Stacks Project, Tag 04CT],
in the form `AlgebraicGeometry.Space.differentialsHomEquiv`), and the adjunction
`(b')^* ⊣ (b')_*` of [Stacks Project, Tag 03LU].  The *fourth* bijection of that file is the only
one which asks `b'` to be étale, and it is not used here; `b'` is an arbitrary morphism.

**No transport of the module along the thickening is needed either.**  Routing the coefficients
through `AlgebraicGeometry.Space.firstOrderConormalModuleIso` (`𝓘 ≅ i_*𝒞_{X/X'}`) and then
through a composition law for the direct image of modules, in order to land in
`(modulePushforward a).obj 𝒞_{X/X'}` and apply Equation (0619),
`AlgebraicGeometry.Space.derivationDirectImageEquiv`, at `a`, is unnecessary and is not
done: running the three bijections at `b'` with coefficients `𝓘` itself lands in
`(b')^*Ω_{Y'/Bb} ⟶ 𝓘`, and the passage to `a^*Ω_{Y'/Bb} ⟶ 𝒞_{X/X'}` is then **two steps of
bookkeeping** — apply `modulePullback i`, whose value at `𝓘` is `𝒞_{X/X'}` by
`AlgebraicGeometry.Space.conormalModule_eq` (which is `rfl`), and precompose with the inverse of
the composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of [Stacks Project,
Tag 03LU].  In particular the identification of
`Stacks.Sheaves.RingedToposModules.directImageModules` composed with a restriction of scalars
against `AlgebraicGeometry.Space.modulePushforward`, which the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionDirectImageDerivation` record as owed by a
consumer, is **not** owed on this route.

**Why the coefficients are taken over the structure map of `b'` and not of `a'`.**
`AlgebraicGeometry.Space.liftPairDerivation` takes the structure map of `a'`, read through the
mate `AlgebraicGeometry.Space.commRingInverseImageIsoOfRestrictEq`, as its *first* map, so its
coefficients are `𝓘` with scalars restricted along that one.  The transposition of derivations is
stated at the restriction of scalars along the structure map of the morphism whose topoi it
transposes, which here is `b'`; so the two maps are supplied to
`AlgebraicGeometry.Space.liftDifferenceDerivation` in the opposite order, and the resulting
derivation is `(b')^♯ - (a')^♯` rather than `(a')^♯ - (b')^♯`.  Nothing else changes: the generic
lemma is applied with different arguments, and no second generic statement is introduced.  (The
two restrictions of scalars do in fact give the same module structure on `𝓘`, the two maps
differing by a section of a square-zero ideal, but that comparison is not needed and is not
proved here.)

**The two spellings of the coefficients.**  `PresheafOfModules.Derivation'` determines its sheaf
of commutative rings by unifying the module's base with `R.obj ⋙ forget₂ CommRingCat RingCat`, so
the coefficients must be presented as `AlgebraicGeometry.Space.liftDifferenceCoefficients` does
present them; presented instead as
`Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf`, which is what
`AlgebraicGeometry.Space.etaleSourceRestrictScalars` produces, the elaborator reports an
application type mismatch rather than a timeout — the two are the same term, and
`AlgebraicGeometry.Space.liftDifferenceCoefficients_eq_liftPairCoefficients` is `rfl`, but only
one of them is a higher-order pattern.  Everything in this file is stated at the first spelling
and the conversion happens by `rfl` where the bijections consume it.

## What is carried, and what is not

`AlgebraicGeometry.Space.liftPairDerivationSecond` carries the hypothesis `hφ`, that the two
structure maps agree on the base ring sheaf `(b')^{-1}q^{-1}𝒪_{Bb}`.  **That is hypothesis (1) of
[Stacks Project, Tag 0618] itself** — in the source both morphisms of thickenings are morphisms
over the base, so both comorphisms are maps of `𝒪_{Bb}`-algebras — and the derivation of the
source does not exist without it: a `Bb`-derivation is by definition one which kills
`q^{-1}𝒪_{Bb}`.  So it is not a weakening of 0618, and no `@[stacks]` attribute is claimed in
this file for any of these declarations.

Deriving `hφ` from the geometric hypothesis `a' ≫ q = b' ≫ q` is a separate step, and it is
**done** — in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftPairBaseDerivation`, as
`AlgebraicGeometry.Space.liftPairBaseMap_comp_liftPairSecondSharp`, with
`AlgebraicGeometry.Space.liftPairDerivationSecondOfCompEq`,
`AlgebraicGeometry.Space.liftPairActionSectionOfCompEq` and
`AlgebraicGeometry.Space.liftPairGlobalSectionOfCompEq` the three constructions of this file
with `hφ` discharged, carrying only `a' ≫ q = b' ≫ q` in its place.

That step takes two inputs.  Naturality of the mate
`AlgebraicGeometry.Space.commRingInverseImageIsoOfRestrictEq` at `q^♯` is one of them, and it is
free (`CategoryTheory.NatTrans.naturality`).  The other is **not** a compatibility of that mate
with the inverse-image composition comparison of [Stacks Project, Tag 03G8],
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso`; what it actually
needs is the compatibility of the comparison of [Stacks Project, Tag 05ZM] with
*postcomposition* by `q`, which is
`AlgebraicGeometry.Space.structureSharpPush_comp_map_smallEtalePushforwardIsoOfRestrictEq` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqPostcompose`, together
with the transposes
`AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp` of [Stacks Project,
Tag 03G8] and `AlgebraicGeometry.RingedToposHom.homEquiv_fSharpInverseImage`.  The mate itself is
never computed, and the generic transpose lemma
`Stacks.CategoryTheory.comp_natIso_inv_app_eq_of_transpose` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqInverseImage` is used
**at `m = 𝟙`** — the case its other application never takes, since there `m := i^♯`, and an
equation after `i^♯` says nothing about a difference which already lands in the defining ideal.

The unconditional content of this file is therefore
`AlgebraicGeometry.Space.definingIdealHomOfDerivation`,
`AlgebraicGeometry.Space.liftPairActionSectionOfDerivation` and
`AlgebraicGeometry.Space.liftPairGlobalSectionOfDerivation`, which take the derivation as a
datum and carry no hypothesis at all beyond the thickening and the morphisms; and the three
declarations which carry `hφ` have unconditional counterparts in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftPairBaseDerivation`.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' Y' Bb : AlgebraicSpaces B S hS} {G : Subfunctor X'.1}
  (hG : IsThickening B S hS X' G) (a' b' : X' ⟶ Y')

/-! ### The two spellings of the coefficients -/

/-- The structure map of `b'` in inverse-image form, read on sheaves of rings.  This is the map
along which the defining ideal of the thickening is read as a `(b')^{-1}𝒪_{Y'}`-module. -/
abbrev liftPairSecondSharp :=
  (sheafCompose (SmallEtale.topology B S hS X'.1)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (structureSharpInverseImage B S hS b')

/-- The base ring sheaf map of the derivation: the inverse image along `b'` of the structure map
`q♯ : q^{-1}𝒪_{Bb} ⟶ 𝒪_{Y'}`.  A `Bb`-derivation of `(b')^{-1}𝒪_{Y'}` is a derivation over this
map, and it is the map which the transposition of derivations carries to `q♯` itself. -/
abbrev liftPairBaseMap (q : Y' ⟶ Bb) :=
  (smallEtaleRingedToposHom B S hS b').toToposHom.inverseImageRing.map
    (structureSharpInverseImage B S hS q)

/-- The defining ideal of the thickening, read as a `(b')^{-1}𝒪_{Y'}`-module in the spelling at
which the transposition of derivations of [Stacks Project, Tag 08TQ] is stated. -/
abbrev liftPairCoefficients :=
  (etaleSourceRestrictScalars B S hS b').obj
    (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules

/-- The coefficients of the bundled derivation of [Stacks Project, Tag 0618], taken at the
structure map of `b'`, **are** the restriction of scalars at which the transposition of
derivations of [Stacks Project, Tag 08TQ] is stated.  The two are the same term; only the shape
in which the base sheaf of commutative rings is presented differs, and
`PresheafOfModules.Derivation'` needs the first of the two, since it determines that sheaf by
unification. -/
theorem liftDifferenceCoefficients_eq_liftPairCoefficients :
    liftDifferenceCoefficients B S hS ⟨G, hG.1⟩ (liftPairSecondSharp B S hS b') =
      (liftPairCoefficients B S hS hG b').val :=
  rfl

/-! ### From a derivation to a section of the acting sheaf -/

/-- **The morphism `(b')^*Ω_{Y'/Bb} ⟶ 𝓘` attached to a `Bb`-derivation of `(b')^{-1}𝒪_{Y'}` with
values in the defining ideal of the thickening.**  The composite of three of the four bijections
of `StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceLocalization`, run
backwards: the transposition of derivations of [Stacks Project, Tag 08TQ], the universal property
of `Ω_{Y'/Bb}` of [Stacks Project, Tag 04CT] and the adjunction `(b')^* ⊣ (b')_*` of
[Stacks Project, Tag 03LU].  The fourth bijection there, the only one needing an étale morphism,
plays no part, so `b'` is arbitrary. -/
def definingIdealHomOfDerivation (q : Y' ⟶ Bb)
    (D : (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
      (liftPairSecondSharp B S hS b')).Derivation' (liftPairBaseMap B S hS b' q).hom) :
    (modulePullback B S hS b').obj (sheafOfDifferentials B S hS q) ⟶
      (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules :=
  (etaleSourceAdjEquiv B S hS b' q
      (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules).symm
    ((differentialsHomEquiv B S hS q
        ((etaleSourcePushforward B S hS b').obj
          (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules)).symm
      ((etaleSourceTransposeEquiv B S hS b' q
        (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules).symm D))

/-- **The morphism `a^*Ω_{Y'/Bb} ⟶ 𝒞_{X/X'}` attached to such a derivation**, for `a = i ≫ b'`
the restriction of `b'` to the closed subspace.  This is the shape of a global section of the
acting sheaf of [Stacks Project, Tag 061D].

It is the previous morphism with `modulePullback i` applied to it — whose value at the defining
ideal is the conormal module by `AlgebraicGeometry.Space.conormalModule_eq` — precomposed with
the inverse of the composition comparison of [Stacks Project, Tag 03LU]. -/
def liftPairActionSectionOfDerivation (q : Y' ⟶ Bb)
    (D : (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
      (liftPairSecondSharp B S hS b')).Derivation' (liftPairBaseMap B S hS b' q).hom) :
    (modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ b')).obj
        (sheafOfDifferentials B S hS q) ⟶
      conormalModule B S hS X' ⟨G, hG.1⟩ :=
  (modulePullbackCompIso B S hS (IsThickening.inclusion B S hS hG) b').inv.app
      (sheafOfDifferentials B S hS q) ≫
    (modulePullback B S hS (IsThickening.inclusion B S hS hG)).map
      (definingIdealHomOfDerivation B S hS hG b' q D)

/-- **The same, as a global section of the acting sheaf `SheafHom(a^*Ω_{Y'/Bb}, 𝒞_{X/X'})` of
[Stacks Project, Tag 061D].**  The global sections of the internal hom are the morphisms, by
`AlgebraicGeometry.Space.smallEtaleInternalHomSectionsEquiv`. -/
def liftPairGlobalSectionOfDerivation (q : Y' ⟶ Bb)
    (D : (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
      (liftPairSecondSharp B S hS b')).Derivation' (liftPairBaseMap B S hS b' q).hom) :
    (liftActionSheaf B S hS ⟨G, hG.1⟩ q
      (IsThickening.inclusion B S hS hG ≫ b')).sections :=
  (smallEtaleInternalHomSectionsEquiv B S hS G.toFunctor hG.1.1
      ((modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ b')).obj
        (sheafOfDifferentials B S hS q))
      (conormalModule B S hS X' ⟨G, hG.1⟩)).symm
    (liftPairActionSectionOfDerivation B S hS hG b' q D)

/-! ### The derivation of two morphisms of a thickening -/

variable (h : IsThickening.inclusion B S hS hG ≫ a' = IsThickening.inclusion B S hS hG ≫ b')

/-- **The derivation `D` of [Stacks Project, Tag 0618] for two morphisms of a thickening agreeing
on its closed subspace**, with the two structure maps supplied in the order which puts the
coefficients over the structure map of `b'` — so the derivation is `(b')^♯ - (a')^♯`, the first
read through `AlgebraicGeometry.Space.commRingInverseImageIsoOfRestrictEq`.

The hypothesis `hφ` is hypothesis (1) of the source: both morphisms are morphisms over `Bb`, so
both structure maps agree on `(b')^{-1}q^{-1}𝒪_{Bb}`.  See the module documentation for what
deriving it from `a' ≫ q = b' ≫ q` would need. -/
def liftPairDerivationSecond (q : Y' ⟶ Bb) (hZ : IsFirstOrderThickening B S hS X' G)
    (hφ : (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map (liftPairBaseMap B S hS b' q) ≫
          liftPairSecondSharp B S hS b' =
        (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map (liftPairBaseMap B S hS b' q) ≫
          (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h)) :
    (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
      (liftPairSecondSharp B S hS b')).Derivation' (liftPairBaseMap B S hS b' q).hom :=
  liftDifferenceDerivation B S hS ⟨G, hG.1⟩ (liftPairBaseMap B S hS b' q)
    (liftPairSecondSharp B S hS b')
    ((sheafCompose (SmallEtale.topology B S hS X'.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map
      (inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h)) hZ
    (inverseImageStructureSharpOfRestrictEq_comp_structureSharp B S hS hG a' b' h).symm hφ

/-- **The difference of two lifts, as a morphism `a^*Ω_{Y'/Bb} ⟶ 𝒞_{X/X'}`.** -/
def liftPairActionSection (q : Y' ⟶ Bb) (hZ : IsFirstOrderThickening B S hS X' G)
    (hφ : (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map (liftPairBaseMap B S hS b' q) ≫
          liftPairSecondSharp B S hS b' =
        (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map (liftPairBaseMap B S hS b' q) ≫
          (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h)) :
    (modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ b')).obj
        (sheafOfDifferentials B S hS q) ⟶
      conormalModule B S hS X' ⟨G, hG.1⟩ :=
  liftPairActionSectionOfDerivation B S hS hG b' q
    (liftPairDerivationSecond B S hS hG a' b' h q hZ hφ)

/-- **The difference of two lifts, as a global section of the acting sheaf of [Stacks Project,
Tag 061D].**  This is the chart-free difference which a glueing of the chartwise action of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` would use as its uniqueness
criterion: it is defined without reference to any chart presentation. -/
def liftPairGlobalSection (q : Y' ⟶ Bb) (hZ : IsFirstOrderThickening B S hS X' G)
    (hφ : (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map (liftPairBaseMap B S hS b' q) ≫
          liftPairSecondSharp B S hS b' =
        (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map (liftPairBaseMap B S hS b' q) ≫
          (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h)) :
    (liftActionSheaf B S hS ⟨G, hG.1⟩ q
      (IsThickening.inclusion B S hS hG ≫ b')).sections :=
  liftPairGlobalSectionOfDerivation B S hS hG b' q
    (liftPairDerivationSecond B S hS hG a' b' h q hZ hφ)

end AlgebraicGeometry.Space

end
