module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkClosedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionsTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleTrivial
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Regular meromorphic sections of an invertible module on an algebraic space

Let `X` be an algebraic space over a scheme `S` for which the local rings `𝒪_{X, η}` at the
points `η ∈ X⁰` of codimension `0` and the canonical morphisms `j_η : Spec(𝒪_{X, η}) ⟶ X` are
defined, and let `ℒ` be an invertible `𝒪_X`-module.  Stacks 0EPQ asserts that `ℒ` has a regular
meromorphic section.  The source's argument is: `ℒ_η` is free of rank `1` over `𝒪_{X, η}`, so a
generator `s_η` may be chosen at every `η ∈ X⁰`, and the description of `𝒦_X` and of `𝒦_X(ℒ)`
as the product over `X⁰` of the direct images `j_{η, *}` of the stalks — the first two
conclusions of Stacks 0ENA — identifies `𝒦_X(ℒ)` with `𝒦_X` once such generators are chosen,
the identification sending the unit meromorphic function to the family `(s_η)`.  A meromorphic
section corresponding to an isomorphism `𝒦_X ≅ 𝒦_X(ℒ)` is regular, because multiplication by it
is then an isomorphism.

The route taken here uses only the **first** of those two conclusions, that `𝒦_X` is the product
over `X⁰` of the `j_{η, *}𝒪_{X, η}`: the generators `s_η` assign to every section of `ℒ` over an
étale chart a family of regular functions on the base-changed charts `U ×_X Spec(𝒪_{X, η})`,
hence — the comparison of the first conclusion being bijective on the sections over every chart —
a single meromorphic function, its *meromorphic value*.  Multiplication by the meromorphic value
of a free generator of `ℒ` is bijective on a covering sieve, which makes the comparison
`𝒦_X(ℒ) ⟶ 𝒦_X` adjoint to the meromorphic value a locally bijective morphism out of the presheaf
whose sheafification `𝒦_X(ℒ)` is, so an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicUnitModule` is `𝒦_X` read as a `𝒦_X`-module in the module
  universe of the sheaves of meromorphic sections, and
  `AlgebraicGeometry.Space.meromorphicUnitSection` is its unit global section.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.specStalkSpace` is `Spec(𝒪_{X, η})` as an
  algebraic space and `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericMorphism` is
  `j_η` as a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.IsTrivialAtCodimensionZeroPoints` says that the inverse image of an
  `𝒪_X`-module along `j_η` is free of rank `1` for every `η ∈ X⁰`, which is the choice of the
  generators `s_η`.

## Main results

* `AlgebraicGeometry.Space.injective_smul_meromorphicUnitSection`: multiplication by the unit
  meromorphic function is injective on every object of the small étale site.
* `AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_nonempty_iso`: an isomorphism
  `𝒦_X ≅ 𝒦_X(ℒ)` of `𝒦_X`-modules produces a regular meromorphic section of `ℒ`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.nonempty_iso_unit_of_isInvertibleModule`:
  an invertible module on the small étale site of `Spec(𝒪_{X, η})` is isomorphic to the
  structure sheaf, at every codimension-zero point `η`.
* `AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_isTrivialAtCodimensionZeroPoints`
  is **Stacks 0EPQ**: an invertible `𝒪_X`-module on an algebraic space satisfying conditions
  (a), (b) and (c) of Stacks 0ENA has a regular meromorphic section.

## Implementation notes

The hypotheses on `X` are exactly the three the source states: condition (a), that every weakly
associated point of `X` has codimension `0`; condition (b), the equivalent conditions of
Stacks 0BB1; and condition (c), representability of the codimension-zero points by monomorphisms
from spectra of fields.  Conditions (b) and (c) produce the presentation of the schematic locus
at the codimension-zero points, `AlgebraicGeometry.Space.exists_codimensionZeroPresentation`,
and condition (a) is what makes the comparison of the first conclusion of Stacks 0ENA bijective
on the sections over a chart — the same three hypotheses the first and third conclusions
of Stacks 0ENA take.

The isomorphism `𝒦_X ≅ 𝒦_X(ℒ)` is
`Space.CodimensionZeroPresentation.nonempty_uliftUnit_iso_meromorphicSectionSheaf`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionsTrivialization.lean`), which deduces
it from the first conclusion of Stacks 0ENA rather than from the second: the family of the values
of a section of `ℒ` at the codimension-zero points is, by that first conclusion, the comparison
image of a unique meromorphic function, and multiplication by the meromorphic function attached
to a free generator is bijective over a covering sieve.

The other input the source uses is that an invertible `𝒪_X`-module is trivial at every
codimension-zero point, the source's choice of a generator `s_η ∈ ℒ_η`.  **This is not a
hypothesis.**  It splits into the invertibility half of Stacks 0B8P for the inverse image along
`j_η`, which `AlgebraicGeometry.Space.modulePullbackInvertible`
(`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctor.lean`) proves
unconditionally, followed by the triviality of an invertible module on the small étale site of
`Spec(𝒪_{X, η})` itself, which is
`AlgebraicGeometry.Space.CodimensionZeroPresentation.nonempty_iso_unit_of_isInvertibleModule`
below.  The composite is `AlgebraicGeometry.Space.IsTrivialAtCodimensionZeroPoints` for `ℒ`, and
it is what the isomorphism `𝒦_X ≅ 𝒦_X(ℒ)` consumes.

The second half is the sheaf-level form of "the Picard group of a local ring is trivial", and
it is proved as
`AlgebraicGeometry.Space.nonempty_iso_unit_of_isInvertibleModule_of_forall_eq_top`
(`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedInvertibleTrivial.lean`) at the spectrum of
`𝒪_{X, η}`, whose closed point lies in no proper open.  That proof composes three existing
inputs.  The sections of the restriction of an invertible module to an étale scheme chart
carrying a point with no proper open neighbourhood are free of rank one,
`AlgebraicGeometry.Space.nonempty_linearEquiv_chartRestrictionTop_of_isInvertibleModule`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartZariskiStalkClosedPointInvertible.lean`), which
descends freeness of rank one from the geometric stalk across Stacks 05VP.  A quasi-coherent
module on the spectrum of a ring whose global sections are free of rank one is the structure
sheaf, `AlgebraicGeometry.nonempty_iso_unit_of_isQuasicoherent_of_gammaTop`
(`StacksFrontier/AlgebraicGeometry/Modules/SpecGlobalSectionsTrivial.lean`).  And restriction to
the small Zariski site reflects isomorphisms of quasi-coherent modules on the small étale site,
`AlgebraicGeometry.SmallEtale.nonempty_iso_of_iso_restrictModule`, which is the counit of
Descent, Proposition 03DX (2) at `τ = étale`.

Why faithfully flat descent of freeness of rank one appears in that composite: the source's
`𝒪_{X, η}` is the Zariski local ring of the chart, while the only tensor comparison of stalks
available is at a geometric point, and the passage between the two is
`Module.nonempty_linearEquiv_of_tensorProduct_of_faithfullyFlat`
(`StacksFrontier/RingTheory/Flat/FaithfullyFlat/RankOneDescent.lean`), which does not follow from
Mathlib's `Module.FaithfullyFlat` API as it stands and is proved here with no finiteness
hypothesis on the module, no locality of the source ring and no local-homomorphism hypothesis.
With it, the stalk route goes through and no tensor comparison across the Zariski–étale
comparison is needed: invertibility is used only at a geometric point, where
`AlgebraicGeometry.Space.geometricModuleStalkTensorIso` supplies it, and what crosses the
comparison afterwards is an isomorphism of modules, not a tensor inverse.  In particular no
passage of *invertibility* across the Zariski–étale comparison, and so no tensor comparison of
Stacks 03EL for a morphism of ringed topoi, enters.  That comparison itself — Stacks 03DX (2),
between modules on the small étale site of `Spec(𝒪_{X, η})` and quasi-coherent modules on that
scheme — is proved, as
`AlgebraicGeometry.Space.representedQuasicoherentSheavesEquivalence`.

`AlgebraicGeometry.Space.IsTrivialAtCodimensionZeroPoints` is the sheaf-level reading,
`j_η^* ℒ ≅ 𝒪` on the whole small étale site of `Spec(𝒪_{X, η})`, whereas the triviality the
source's proof uses is stalk-level — `ℒ_η` free of rank one over the Zariski local ring
`𝒪_{X, η}`, which is what `AlgebraicGeometry.Space.CodimensionZeroPresentation.stalk` is.  The
sheaf-level reading implies the stalk-level one, so this development splits 0EPQ at a stronger
intermediate than the source does, and the trivialisations it produces are the data the
isomorphism `𝒦_X ≅ 𝒦_X(ℒ)` is built from.

**The second conclusion of Stacks 0ENA — the description of `𝒦_X(M)` as the product over `X⁰`
of the direct images `j_{η, *}(M_η)` — is not used.**  The route taken instead goes through the
*first* conclusion only: the comparison `𝒦_X(M) ⟶ 𝒦_X` adjoint to the meromorphic value of a
section is a morphism of `𝒦_X`-modules by construction, so no passage between `𝒪_X`-modules and
`𝒦_X`-modules is needed either.  Both of the passages that would be needed by a route through
the second conclusion are nevertheless available: restriction of scalars along `𝒪_X ⟶ 𝒦_X` is
fully faithful, `AlgebraicGeometry.Space.fullyFaithfulMeromorphicRestrictScalars`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicRestrictScalarsFullyFaithful.lean`), with the
object-level consequence
`AlgebraicGeometry.Space.nonempty_iso_meromorphicSectionSheaf_of_nonempty_iso_meromorphicModule`
in the same file; and restriction of scalars reflects isomorphisms,
`Stacks.SheafOfModules.ChangeOfRings.isIso_of_isIso_restrictScalars`, which on its own promotes
an isomorphism of a given morphism and cannot identify two objects.

What is proved here is the passage from an isomorphism `𝒦_X ≅ 𝒦_X(ℒ)` to a regular meromorphic
section.  Regularity of a meromorphic section is injectivity of multiplication by it on each
object of the small étale site, so the isomorphism is used through the bijectivity of its
sections; the module universe of `𝒦_X(ℒ)` is larger than that of `𝒦_X`, which is why `𝒦_X` is
read as a `𝒦_X`-module through a universe lift rather than as `SheafOfModules.unit`.

## References

* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The sheaf of meromorphic functions as a module over itself -/

/-- The sheaf of meromorphic functions `𝒦_F`, read as a `𝒦_F`-module in the module universe of
the sheaves of meromorphic sections. -/
def meromorphicUnitModule :
    SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O) :=
  SheafOfModules.uliftObj.{_, _, _, _, u + 1}
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O))

/-- The unit meromorphic function, as a global section of `𝒦_F` read as a `𝒦_F`-module. -/
def meromorphicUnitSection : (meromorphicUnitModule B S hS F hF).sections :=
  PresheafOfModules.sectionsMk
    (fun V => ULift.up (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS F hF).O).obj.obj V))
    (fun {_ _} f => congrArg ULift.up (PresheafOfModules.unit_map_one _ f))

/-- The unit meromorphic function has value `1` on every object of the small étale site. -/
theorem meromorphicUnitSection_eval (V : SmallEtale B S hS F) :
    (meromorphicUnitSection B S hS F hF).eval (op V) =
      ULift.up (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.obj (op V)) :=
  rfl

/-- **Multiplication by the unit meromorphic function is injective** on the sections over every
object of the small étale site. -/
theorem injective_smul_meromorphicUnitSection (V : SmallEtale B S hS F) :
    Function.Injective
      fun r : (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.obj (op V) =>
        r • (meromorphicUnitSection B S hS F hF).eval (op V) := by
  intro r₁ r₂ hr
  rw [meromorphicUnitSection_eval] at hr
  have h : r₁ * 1 = r₂ * 1 := congrArg ULift.down hr
  simpa using h

/-! ### A regular meromorphic section from a trivialisation of the meromorphic sections -/

/-- **An isomorphism `𝒦_F ≅ 𝒦_F(ℒ)` of `𝒦_F`-modules produces a regular meromorphic section of
`ℒ`**: it carries the unit meromorphic function to a meromorphic section of `ℒ`, and
multiplication by that section is multiplication by the unit followed by a bijection. -/
theorem exists_isRegularMeromorphicSection_of_nonempty_iso (L : Modules.{u, u} B S hS F hF)
    (h : Nonempty (meromorphicUnitModule B S hS F hF ≅
      meromorphicSectionSheaf.{u, u} B S hS F hF L)) :
    ∃ s : MeromorphicSection.{u, u} B S hS F hF L,
      IsRegularMeromorphicSection.{u, u} B S hS F hF L s := by
  obtain ⟨e⟩ := h
  refine ⟨SheafOfModules.sectionsMap e.hom (meromorphicUnitSection B S hS F hF), fun V => ?_⟩
  intro r₁ r₂ hr
  refine injective_smul_meromorphicUnitSection B S hS F hF V ?_
  refine (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O)
        (op V)).map e.hom)).injective ?_
  have hlin := fun r => (PresheafOfModules.Hom.app e.hom.val (op V)).hom.map_smul r
    ((meromorphicUnitSection B S hS F hF).eval (op V))
  exact (hlin r₁).trans (hr.trans (hlin r₂).symm)

/-! ### Triviality at the codimension-zero points -/

variable {B S hS}

/-- An `𝒪_X`-module is *trivial at the codimension-zero points* when its inverse image along
`j_η : Spec(𝒪_{X, η}) ⟶ X` is free of rank `1` for every point `η` of codimension `0`; a
trivialisation is a choice of generator of the stalk `M_η` over `𝒪_{X, η}`. -/
def IsTrivialAtCodimensionZeroPoints {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (P : CodimensionZeroPresentation B S hS X)
    (M : Modules.{u, u} B S hS X hX) : Prop :=
  ∀ (x : points B S hS X) (hx : localRingDimension B S hS x = 0),
    Nonempty ((modulePullback B S hS (P.genericMorphism hx hX)).obj M ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).O))

/-! ### Triviality of an invertible module at a codimension-zero point -/

/-- The ring `𝒪_{X, η}` at a point of codimension `0` is a local ring: it is the Zariski stalk
of the scheme presenting the schematic locus. -/
instance CodimensionZeroPresentation.isLocalRing_stalk
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (P : CodimensionZeroPresentation B S hS X)
    {x : points B S hS X} (hx : localRingDimension B S hS x = 0) :
    IsLocalRing (P.stalk hx) :=
  inferInstanceAs (IsLocalRing (P.schemeObj.presheaf.stalk (P.schemePointAt hx)))

/-- **An invertible module on the small étale site of `Spec(𝒪_{X, η})` is isomorphic to the
structure sheaf**, at every point `η` of codimension `0`.

This is the sheaf-level triviality of the Picard group of the local ring `𝒪_{X, η}`, which
combined with `AlgebraicGeometry.Space.modulePullbackInvertible` is the choice of a generator
`s_η ∈ ℒ_η` that the proof of Stacks 0EPQ makes.  It is
`AlgebraicGeometry.Space.nonempty_iso_unit_of_isInvertibleModule_of_forall_eq_top` at the
spectrum of `𝒪_{X, η}`, whose closed point lies in no proper open. -/
theorem CodimensionZeroPresentation.nonempty_iso_unit_of_isInvertibleModule
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (P : CodimensionZeroPresentation B S hS X)
    (x : points B S hS X) (hx : localRingDimension B S hS x = 0)
    (N : Modules.{u, u} B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2)
    (hN : IsInvertibleModule (P.specStalkSpace hx) N) :
    Nonempty (N ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).O)) :=
  nonempty_iso_unit_of_isInvertibleModule_of_forall_eq_top B S hS (P.specStalk hx) rfl
    (IsLocalRing.closedPoint (P.stalk hx))
    (AlgebraicGeometry.forall_eq_top_of_mem_of_isLocalRing (P.stalk hx))
    (P.specStalkSpace hx).2 N hN

/-! ### Stacks 0EPQ -/

/-- **Stacks 0EPQ.** Let `X` be an algebraic space over a scheme `S` satisfying conditions (a),
(b) and (c) of Stacks 0ENA — every weakly associated point of `X` has codimension `0`, the
irreducible components of `X` are locally finite, and every codimension-zero point of `X` is
representable by a monomorphism from the spectrum of a field.  Then **every invertible
`𝒪_X`-module `ℒ` has a regular meromorphic section.**

The choice of the generators `s_η ∈ ℒ_η` that the source makes is
`AlgebraicGeometry.Space.CodimensionZeroPresentation.nonempty_iso_unit_of_isInvertibleModule`
above, the triviality of an invertible module on the small étale site of `Spec(𝒪_{X, η})`,
composed with `AlgebraicGeometry.Space.modulePullbackInvertible`.  Those trivialisations give
`𝒦_X ≅ 𝒦_X(ℒ)` by `CodimensionZeroPresentation.nonempty_uliftUnit_iso_meromorphicSectionSheaf`,
and an isomorphism `𝒦_X ≅ 𝒦_X(ℒ)` produces a regular meromorphic section by
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_nonempty_iso`.  See the
implementation notes. -/
@[stacks 0EPQ "every invertible module on an algebraic space satisfying conditions (a), (b) and
(c) of Tag 0ENA has a regular meromorphic section"]
theorem exists_isRegularMeromorphicSection_of_isTrivialAtCodimensionZeroPoints
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS X)
    (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L) :
    ∃ s : MeromorphicSection.{u, u} B S hS X hX L,
      IsRegularMeromorphicSection.{u, u} B S hS X hX L s := by
  obtain ⟨P⟩ := exists_codimensionZeroPresentation B S hS hX hfin hmono
  have hgenL : IsTrivialAtCodimensionZeroPoints hX P L := fun x hx =>
    P.nonempty_iso_unit_of_isInvertibleModule x hx _
      (modulePullbackInvertible (P.genericMorphism hx hX) L hL)
  have hτ : (η : CodimensionZeroPresentation.CodimensionZeroPoints B S hS X) →
      P.genericPointPullback (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) η.2 L ≅
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (P.specStalkSpace η.2).1 (P.specStalkSpace η.2).2).O) :=
    fun η => (hgenL η.1 η.2).some
  have hMinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  have hiso : Nonempty (SheafOfModules.uliftObj.{_, _, _, _, u + 1}
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O)) ≅
      meromorphicSectionSheaf.{u, u} B S hS X hX L) :=
    P.nonempty_uliftUnit_iso_meromorphicSectionSheaf
      (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) L hτ hwa hfin hMinv
  exact exists_isRegularMeromorphicSection_of_nonempty_iso B S hS X hX L hiso

end AlgebraicGeometry.Space

end
