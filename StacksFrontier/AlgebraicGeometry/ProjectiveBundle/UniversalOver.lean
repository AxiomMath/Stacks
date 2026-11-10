module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Universal

/-!
# Mapping into a projective bundle over its base

Let `X` be a scheme, `F` a quasi-coherent `𝒪_X`-module and `π : 𝐏(F) ⟶ X` the projection of its
projective bundle. Tag 01O4 says that `𝐏(F)` represents the functor sending a scheme `f : T ⟶ X`
over `X` to the invertible quotients of `f^*F` on `T`, taken up to isomorphism; in particular it
*produces a morphism `T ⟶ 𝐏(F)` over `X`* out of such a quotient. Nothing in this repository
produced one before this file: `Stacks.RelativeProj.TautologicalDatum.IsUniversal` of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Sections` is the mapping-in property at the base
alone — its left-hand side is the *sections* of `π`, i.e. the `X`-points of `𝐏(F)` — and
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation` is a structure of which no term
exists.

This file closes the gap between the two left-hand sides and reads the universal property off at
every test scheme.

## What is proved, and what it rests on

The whole file rests on one observation, and it is a theorem of this repository rather than a
hypothesis: the projective bundle of `f^*F` **is** the base change of `𝐏(F)` along `f`
(`Stacks.RelativeProj.isPullback_projectiveBundleBaseChange`, the cartesian square of
`StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChange`). So the
`X`-morphisms `T ⟶ 𝐏(F)` over `f` are *exactly* the sections of `π' : 𝐏(F') ⟶ T` for
`F' ≅ f^*F`, the bijection in both directions being the universal property of the fibre product
(`Stacks.RelativeProj.overMorphismEquivSection`). This is unconditional.

Composing that bijection with Tag 0B3V's bijection for the base-changed tautological datum
(`Stacks.RelativeProj.TautologicalDatum.sectionsEquivInvertibleQuotients`, whose input is
`IsUniversal` for that datum) gives Tag 01O4's mapping-in bijection at the test scheme `f`, and
with it the classifying morphism and the section of `π^{-1}(T) ⟶ T` that
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula` needs for
the `s = r - 1` case of Tag 02TW.

**The hypothesis carried is exactly one, and it is named rather than hidden.**
`Stacks.RelativeProj.TautologicalDatum.IsUniversalOver` is the statement that for every test
scheme the *base-changed* tautological datum is universal — Tag 0B3V at every base change of the
bundle. The implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalBaseChange` record that `IsUniversal`
at the base alone cannot supply this ("`IsUniversal` is *not* stable under base change"), which is
why the quantified form is the hypothesis here. Nothing below assumes anything about the morphism
it produces.

## Main definitions

* `Stacks.RelativeProj.overMorphismEquivSection`: **the morphisms `T ⟶ 𝐏(F)` over `X` with a
  given composite `f` are the sections of `𝐏(F') ⟶ T`**, for any `F' ≅ f^*F`. Unconditional, and
  the bridge the rest of the file is built on.
* `Stacks.RelativeProj.TautologicalDatum.overQuotientMap` and
  `Stacks.RelativeProj.TautologicalDatum.overQuotient`: the invertible quotient of `F'` that a
  morphism over the base pulls back from the tautological datum — `h^*𝒪(1)` with the map
  `F' ≅ f^*F ⟶ h^*𝒪(1)`. Unconditional, and the generalisation of
  `TautologicalDatum.pullbackQuotient` from a section to an arbitrary morphism over `X`.
* `Stacks.RelativeProj.TautologicalDatum.IsUniversalOver`: Tag 0B3V's bijection at every base
  change of the bundle. This is the one hypothesis.
* `Stacks.RelativeProj.TautologicalDatum.overMorphismEquivInvertibleQuotients`: **Tag 01O4's
  mapping-in bijection at a test scheme** — the `X`-morphisms `T ⟶ 𝐏(F)` over `f` are the
  invertible quotients of `f^*F` up to isomorphism.
* `Stacks.RelativeProj.TautologicalDatum.classifyingMorphismOver`: **the morphism `T ⟶ 𝐏(F)` over
  `X` attached to an invertible quotient of `f^*F`.** This is the term Tag 01O4 is wanted for.
* `Stacks.RelativeProj.TautologicalDatum.fibreSection`: **the section `T ⟶ π^{-1}(T)`** of the
  base change of `π` along `f`, cut out by such a quotient.

## Main results

* `Stacks.RelativeProj.TautologicalDatum.epi_overQuotientMap`: the quotient map a morphism over
  the base pulls back is surjective. No hypothesis.
* `Stacks.RelativeProj.TautologicalDatum.classifies_classifyingMorphismOver`: **the classifying
  morphism classifies the quotient it was built from**, so the bijection is normalised by the
  tautological quotient and not merely a bijection.
* `Stacks.RelativeProj.TautologicalDatum.fibreSection_comp_fst` and
  `Stacks.RelativeProj.TautologicalDatum.isClosedImmersion_fibreSection`: the section of
  `π^{-1}(T) ⟶ T` is a section, and it is a closed immersion — the latter by Tag 0B3V's second
  assertion, `π^{-1}(T) ⟶ T` being separated as a base change of the separated `π`.
* `Stacks.RelativeProj.TautologicalDatum.exists_section_fibre_of_invertibleQuotient`: the same
  existentially, in the shape the `s = r - 1` case of Tag 02TW consumes.
* `Stacks.RelativeProj.TautologicalDatum.isUniversalOver_of_isEmpty` and
  `Stacks.RelativeProj.isUniversalOver_tautologicalDatumUnit_empty`: **an unconditional
  inhabitant of `IsUniversalOver`**, so nothing above is vacuous. It is as degenerate as the
  inhabitant of `IsUniversal` in `ProjectiveBundle/Universal.lean` and for the same reason: a
  scheme with a morphism to a scheme with no points has no points either.

## Implementation notes

**Why `F'` with `hF : F' ≅ f^*F` rather than `f^*F` itself.** This is the shape
`StacksFrontier/AlgebraicGeometry/RelativeProjSituation/ProjectiveBundleBaseChange.lean` and
`TautologicalBaseChange.lean` are stated in — `𝐏(F')`
needs `F'.IsQuasicoherent`, which for a literal `f^*F` would need the stability of
quasi-coherence under pullback — and it is also the shape a consumer holds: the restriction of a
module to a subscheme is given as a module in its own right, identified with the pullback. Taking
`F' = f^*F` and `hF = Iso.refl` recovers the literal statement whenever that instance is at hand.

**The bijection is `Equiv.trans` of a cartesian-square bijection and Tag 0B3V's**, so the two
halves of Tag 01O4's mapping-in property — existence of a classifying morphism and its
uniqueness — are the two halves of `IsUniversal` for the base-changed datum, transported. No
third ingredient enters, and in particular no twist and no graded-algebra computation: those are
inside `IsUniversal`, where `Sections.lean` already records what inhabiting them costs.

**`π^{-1}(T)` is spelled `CategoryTheory.Limits.pullback f π`,** the fibre product of `f` with
the projection, and the section is `Limits.pullback.lift (𝟙 T) h`. The alternative spelling
`𝐏(F')` is isomorphic to it over `T` by
`Stacks.RelativeProj.projectiveBundleBaseChangeIsoFlip`, but the Chow material takes the fibre
over a subscheme as a fibre product, so that is the spelling produced here.

## What is not done

**No `@[stacks 01O4]` attribute is attached, and none is claimed.** Tag 01O4 asserts the
representability outright; every statement here carries `IsUniversalOver`, which is Tag 0B3V at
every base change of the bundle, and whose only inhabitant is over a base with no points. What is
proved is the *reduction* of Tag 01O4's mapping-in property to that, and the reduction is
unconditional: `overMorphismEquivSection` and the quotient of a morphism over the base assume
nothing.

**What `IsUniversalOver` still costs, unchanged by this file.** Inhabiting it non-degenerately
means inhabiting `TautologicalDatum.IsUniversal` for the bundle of a module of rank at least two.
The ingredients on the side of the twist are available. The twist exists
unconditionally (`Stacks.SymGraded.projectiveBundleTwist`, invertible by
`Stacks.SymGraded.isInvertible_projectiveBundleTwist`), degree-one generation is a theorem
(`Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra`), and Tag 01CG's
sheafification assertion is proved and tagged
(`SheafOfModules.symmetricPower_isSheafification`); see the implementation notes of
`Sections.lean`.

What stands between here and a non-degenerate inhabitant was two separate things, and the first
of them is now settled. The *datum* exists at arbitrary rank with no hypothesis:
`Stacks.SymGraded.nonempty_tautologicalDatum` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundleTwists/LocalGeneration.lean`, whose fourth field
comes from `Stacks.SymGraded.exists_local_bundleSection` there — the local generation of
`𝒪_{𝐏(E)}(1)` by Tag 01OB's sections from the base that
`Stacks.SymGraded.exists_tautologicalDatum_of_exists_bundleSection` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundleTwists/Epi.lean` had reduced the clause to.

What remains is the second and much the larger: `IsUniversal` itself, the mapping-in half of Tag
01O4, i.e. producing a morphism *into* the bundle from an invertible quotient. Nothing in the twist
material bears on that; `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation`, which states
it at the graded-algebra level, has no term in this repository either. The *absolute* mapping-in
property is proved and tagged — `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents`
`.existsUnique_classifies`, Tag 01NA, for an arbitrary scheme and an arbitrary invertible module —
so the relative statement is not blocked on the absolute one. Three separate things block the
descent of 01NA to the relative setting, each recorded where it lives: the graded map
`Sym(E) ⟶ ⨁ₙ L^{⊗n}` cannot be built from invertibility of `L` alone at this pin, because the
tensor algebra of a sheaf of modules is a hypothesis rather than a construction (the implementation
notes of `StacksFrontier/AlgebraicGeometry/ProjF1Dehomogenization/Basic.lean`); the local morphisms
are not glued over a cover of the test scheme (`ProjF1DegreeOneChart/Relative.lean`); and
`Stacks.AlgebraicGeometry.ProjChartCocycle.ratioOf` is not known to commute with restriction along
an open immersion, which is what glueing over a cover of the *base* needs
(`Constructions/RelativeProjMorphismFromSections.lean`).

**The direct and the base-changed description of the classified quotient are not identified
here.** `TautologicalDatum.overQuotient` is `h^*𝒪(1)` with the map pulled back along `h`
directly, whereas `classifies_classifyingMorphismOver` states the normalisation through the
base-changed datum on `𝐏(F')`. The two agree — the comparison is
`Scheme.Modules.pullbackComp σ b` together with
`TautologicalDatum.tautologicalBaseChangeIso_hom_comp_baseChange_univ` — but the equation is a
pseudofunctor coherence chase that is not performed here, so `overQuotient` is used by no
statement below; it is the honest name of the quotient a morphism over the base carries, and the
normalisation is stated at the spelling where it is proved.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01O2](https://stacks.math.columbia.edu/tag/01O2)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

open Stacks.Divisors

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent] {T : Scheme.{u}} {f : T ⟶ X}
  (F' : T.Modules) [F'.IsQuasicoherent] (hF : F' ≅ (Scheme.Modules.pullback f).obj F)

/-! ### Morphisms over the base are sections of the base change -/

/-- **The morphisms `T ⟶ 𝐏(F)` whose composite with `π` is `f` are the sections of
`π' : 𝐏(F') ⟶ T`**, for any quasi-coherent `F'` on `T` identified with `f^*F`.

Both directions are the universal property of the fibre product, the square of
`Stacks.RelativeProj.isPullback_projectiveBundleBaseChange` being cartesian: a morphism over `f`
is paired with the identity of `T` to give a section, and a section is composed with the
base-change comparison `b : 𝐏(F') ⟶ 𝐏(F)` to give a morphism over `f`. No tautological datum and
no hypothesis enter. -/
def overMorphismEquivSection :
    { h : T ⟶ projectiveBundle X F // h ≫ projectiveBundleToBase X F = f } ≃
      { σ : T ⟶ projectiveBundle T F' // σ ≫ projectiveBundleToBase T F' = 𝟙 T } where
  toFun h :=
    ⟨(isPullback_projectiveBundleBaseChange f F F' hF).lift h.1 (𝟙 T)
        (by rw [h.2, Category.id_comp]),
      (isPullback_projectiveBundleBaseChange f F F' hF).lift_snd _ _ _⟩
  invFun σ :=
    ⟨σ.1 ≫ projectiveBundleBaseChange f F F' hF, by
      rw [Category.assoc, projectiveBundleBaseChange_comp_projectiveBundleToBase,
        ← Category.assoc, σ.2, Category.id_comp]⟩
  left_inv h := Subtype.ext ((isPullback_projectiveBundleBaseChange f F F' hF).lift_fst _ _ _)
  right_inv σ := Subtype.ext ((isPullback_projectiveBundleBaseChange f F F' hF).hom_ext
    ((isPullback_projectiveBundleBaseChange f F F' hF).lift_fst _ _ _)
    (((isPullback_projectiveBundleBaseChange f F F' hF).lift_snd _ _ _).trans σ.2.symm))

/-- The morphism over `f` corresponding to a section `σ` of `𝐏(F') ⟶ T` is the composite of `σ`
with the base-change comparison `𝐏(F') ⟶ 𝐏(F)`. -/
@[simp] theorem overMorphismEquivSection_symm_apply_coe
    (σ : { σ : T ⟶ projectiveBundle T F' // σ ≫ projectiveBundleToBase T F' = 𝟙 T }) :
    ((overMorphismEquivSection F' hF).symm σ).1 =
      σ.1 ≫ projectiveBundleBaseChange f F F' hF :=
  rfl

namespace TautologicalDatum

/-! ### The invertible quotient a morphism over the base carries -/

/-- **The tautological quotient map pulled back along a morphism over the base**, read as a map
out of `f^*F`. This is `TautologicalDatum.pullbackQuotientMap` with the section replaced by an
arbitrary morphism `h` with `h ≫ π = f`: the comparison isomorphisms identify `f^*F` with
`h^*π^*F`, which maps onto `h^*𝒪(1)`. -/
def overQuotientMap (D : TautologicalDatum X F) (h : T ⟶ projectiveBundle X F)
    (hh : h ≫ projectiveBundleToBase X F = f) :
    (Scheme.Modules.pullback f).obj F ⟶ (Scheme.Modules.pullback h).obj D.twist :=
  (Scheme.Modules.pullbackCongr hh).inv.app F ≫
    (Scheme.Modules.pullbackComp h (projectiveBundleToBase X F)).inv.app F ≫
    (Scheme.Modules.pullback h).map D.univ

/-- **The pulled-back tautological quotient map is surjective.** The two comparisons are
isomorphisms and `Scheme.Modules.pullback h`, being a left adjoint, preserves epimorphisms. -/
instance epi_overQuotientMap (D : TautologicalDatum X F) (h : T ⟶ projectiveBundle X F)
    (hh : h ≫ projectiveBundleToBase X F = f) : Epi (D.overQuotientMap h hh) := by
  have := D.epi_univ
  unfold overQuotientMap
  infer_instance

/-- **The invertible quotient of `F'` carried by a morphism `T ⟶ 𝐏(F)` over the base**: the
pullback `h^*𝒪(1)` of the tautological module, with the pulled-back tautological surjection read
out of `F'` through its identification with `f^*F`. This is the datum Tag 01O4 attaches to a
morphism over the base, and it needs no hypothesis. -/
def overQuotient (D : TautologicalDatum X F) (h : T ⟶ projectiveBundle X F)
    (hh : h ≫ projectiveBundleToBase X F = f) : InvertibleQuotient T F' where
  L := (Scheme.Modules.pullback h).obj D.twist
  invertible :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (@Stacks.Modules.isInvertible_pullback _ _ h D.twist
        ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr D.invertible))
  q := hF.hom ≫ D.overQuotientMap h hh
  epi := inferInstance

omit [SheafOfModules.IsQuasicoherent F'] in
/-- The quotient map of `TautologicalDatum.overQuotient` is the identification `F' ≅ f^*F`
followed by `TautologicalDatum.overQuotientMap`. -/
@[simp] theorem overQuotient_q (D : TautologicalDatum X F) (h : T ⟶ projectiveBundle X F)
    (hh : h ≫ projectiveBundleToBase X F = f) :
    (D.overQuotient F' hF h hh).q = hF.hom ≫ D.overQuotientMap h hh :=
  rfl

/-! ### The mapping-in property at every test scheme -/

/-- **Tag 0B3V's bijection at every base change of the bundle**: for every scheme over `X` and
every quasi-coherent module on it identified with the pullback of `F`, the base-changed
tautological datum is universal.

This is the hypothesis under which Tag 01O4's mapping-in property is available below. It is
strictly more than `TautologicalDatum.IsUniversal`, which is the property at the base alone, and
the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalBaseChange` record why the latter
cannot be made to give it: sections of `π'` are `T`-points of `𝐏(F')`, not `X`-points of
`𝐏(F)`. -/
class IsUniversalOver (D : TautologicalDatum X F) : Prop where
  /-- The base-changed datum is universal over every test scheme. -/
  isUniversal_baseChange : ∀ {T : Scheme.{u}} (f : T ⟶ X) (F' : T.Modules) [F'.IsQuasicoherent]
    (hF : F' ≅ (Scheme.Modules.pullback f).obj F), (D.baseChange f F F' hF).IsUniversal

/-- If `D` is universal over every test scheme, then its base change along `f` is universal. -/
instance isUniversal_baseChange_of_isUniversalOver (D : TautologicalDatum X F)
    [D.IsUniversalOver] : (D.baseChange f F F' hF).IsUniversal :=
  IsUniversalOver.isUniversal_baseChange f F' hF

/-- **Tag 01O4's mapping-in bijection at a test scheme `f : T ⟶ X`**: the morphisms
`T ⟶ 𝐏(F)` over `X` with composite `f` are the invertible quotients of `f^*F`, up to isomorphism
of the quotient module.

It is the cartesian-square bijection `Stacks.RelativeProj.overMorphismEquivSection` followed by
Tag 0B3V's bijection for the base-changed tautological datum. -/
def overMorphismEquivInvertibleQuotients (D : TautologicalDatum X F) [D.IsUniversalOver] :
    { h : T ⟶ projectiveBundle X F // h ≫ projectiveBundleToBase X F = f } ≃
      InvertibleQuotientClass T F' :=
  (overMorphismEquivSection F' hF).trans
    (D.baseChange f F F' hF).sectionsEquivInvertibleQuotients

/-- **The morphism `T ⟶ 𝐏(F)` over `X` classified by an invertible quotient of `f^*F`.** This is
the term Tag 01O4 is wanted for: a morphism *into* the projective bundle, produced from the data
the tag describes. -/
def classifyingMorphismOver (D : TautologicalDatum X F) [D.IsUniversalOver]
    (Q : InvertibleQuotient T F') :
    { h : T ⟶ projectiveBundle X F // h ≫ projectiveBundleToBase X F = f } :=
  (D.overMorphismEquivInvertibleQuotients F' hF).symm
    (Quotient.mk (invertibleQuotientSetoid T F') Q)

/-- The classifying morphism of an invertible quotient composed with the projection of the
bundle is `f`. -/
@[simp] theorem classifyingMorphismOver_comp (D : TautologicalDatum X F) [D.IsUniversalOver]
    (Q : InvertibleQuotient T F') :
    (D.classifyingMorphismOver F' hF Q).1 ≫ projectiveBundleToBase X F = f :=
  (D.classifyingMorphismOver F' hF Q).2

/-- **The classifying morphism induces the class it was built from.** -/
theorem overMorphismEquivInvertibleQuotients_classifyingMorphismOver
    (D : TautologicalDatum X F) [D.IsUniversalOver] (Q : InvertibleQuotient T F') :
    D.overMorphismEquivInvertibleQuotients F' hF (D.classifyingMorphismOver F' hF Q) =
      Quotient.mk (invertibleQuotientSetoid T F') Q :=
  (D.overMorphismEquivInvertibleQuotients F' hF).apply_symm_apply _

/-- **The classifying morphism classifies the quotient it was built from**, in the spelling of
Tag 0B3V on `𝐏(F')`: the section of `π'` corresponding to it under the cartesian-square bijection
classifies `Q` for the base-changed tautological datum. So the bijection above is normalised by
the tautological quotient and is not merely some bijection. -/
theorem classifies_classifyingMorphismOver (D : TautologicalDatum X F) [D.IsUniversalOver]
    (Q : InvertibleQuotient T F') :
    (D.baseChange f F F' hF).Classifies
      (overMorphismEquivSection F' hF (D.classifyingMorphismOver F' hF Q)).1
      (overMorphismEquivSection F' hF (D.classifyingMorphismOver F' hF Q)).2 Q :=
  ((D.baseChange f F F' hF).sectionsEquivInvertibleQuotients_eq_iff _ _ Q).1
    (D.overMorphismEquivInvertibleQuotients_classifyingMorphismOver F' hF Q)

/-- **A morphism over the base is determined by the quotient it induces.** -/
theorem eq_of_overMorphismEquivInvertibleQuotients_eq (D : TautologicalDatum X F)
    [D.IsUniversalOver]
    (h h' : { h : T ⟶ projectiveBundle X F // h ≫ projectiveBundleToBase X F = f })
    (hq : D.overMorphismEquivInvertibleQuotients F' hF h =
      D.overMorphismEquivInvertibleQuotients F' hF h') : h = h' :=
  (D.overMorphismEquivInvertibleQuotients F' hF).injective hq

/-! ### The section of the fibre of `π` over a test scheme -/

/-- **The section `T ⟶ π^{-1}(T)` cut out by an invertible quotient of `f^*F`**, for
`π^{-1}(T)` the fibre product of `f` with the projection of the bundle. It pairs the identity of
`T` with the classifying morphism of the quotient. -/
def fibreSection (D : TautologicalDatum X F) [D.IsUniversalOver]
    (Q : InvertibleQuotient T F') : T ⟶ Limits.pullback f (projectiveBundleToBase X F) :=
  Limits.pullback.lift (𝟙 T) (D.classifyingMorphismOver F' hF Q).1
    ((Category.id_comp f).trans (D.classifyingMorphismOver F' hF Q).2.symm)

/-- The section `TautologicalDatum.fibreSection` composed with the first projection of the fibre
product is the identity of `T`. -/
@[reassoc (attr := simp)] theorem fibreSection_comp_fst (D : TautologicalDatum X F)
    [D.IsUniversalOver] (Q : InvertibleQuotient T F') :
    D.fibreSection F' hF Q ≫ Limits.pullback.fst f (projectiveBundleToBase X F) = 𝟙 T :=
  Limits.pullback.lift_fst _ _ _

/-- The section `TautologicalDatum.fibreSection` composed with the second projection of the fibre
product is the classifying morphism of the quotient. -/
@[reassoc (attr := simp)] theorem fibreSection_comp_snd (D : TautologicalDatum X F)
    [D.IsUniversalOver] (Q : InvertibleQuotient T F') :
    D.fibreSection F' hF Q ≫ Limits.pullback.snd f (projectiveBundleToBase X F) =
      (D.classifyingMorphismOver F' hF Q).1 :=
  Limits.pullback.lift_snd _ _ _

/-- **The section of `π^{-1}(T) ⟶ T` is a closed immersion**, which is Tag 0B3V's second
assertion for the base change of `π`: that projection is separated because `π` is, and a section
of a separated morphism is a closed immersion. -/
instance isClosedImmersion_fibreSection (D : TautologicalDatum X F) [D.IsUniversalOver]
    (Q : InvertibleQuotient T F') : IsClosedImmersion (D.fibreSection F' hF Q) :=
  have : IsClosedImmersion
      (D.fibreSection F' hF Q ≫ Limits.pullback.fst f (projectiveBundleToBase X F)) :=
    (D.fibreSection_comp_fst F' hF Q) ▸ inferInstance
  IsClosedImmersion.of_comp _ (Limits.pullback.fst f (projectiveBundleToBase X F))

include hF in
/-- **The section an invertible quotient of `f^*F` cuts out, existentially**, in the shape the
`s = r - 1` case of Tag 02TW consumes: a closed immersion `T ⟶ π^{-1}(T)` splitting the
projection of the fibre. -/
theorem exists_section_fibre_of_invertibleQuotient (D : TautologicalDatum X F)
    [D.IsUniversalOver] (Q : InvertibleQuotient T F') :
    ∃ s : T ⟶ Limits.pullback f (projectiveBundleToBase X F),
      s ≫ Limits.pullback.fst f (projectiveBundleToBase X F) = 𝟙 T ∧ IsClosedImmersion s :=
  ⟨D.fibreSection F' hF Q, D.fibreSection_comp_fst F' hF Q, inferInstance⟩

/-! ### An inhabitant -/

/-- **Every tautological datum over a scheme with no points is universal over every test
scheme.** A scheme with a morphism to a scheme with no points has no points either, so the
base-changed datum falls under `TautologicalDatum.isUniversal_of_isEmpty`. This is as degenerate
as the inhabitant of `TautologicalDatum.IsUniversal` in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Universal` and for the same reason, but it shows
that nothing above is vacuous. -/
instance isUniversalOver_of_isEmpty [IsEmpty X] (D : TautologicalDatum X F) :
    D.IsUniversalOver where
  isUniversal_baseChange f _ _ _ :=
    have : IsEmpty _ := ⟨fun t => isEmptyElim (α := X) (f.base t)⟩
    TautologicalDatum.isUniversal_of_isEmpty _

end TautologicalDatum

/-- **An unconditional inhabitant of `TautologicalDatum.IsUniversalOver`**: the tautological
datum of the structure sheaf of the empty scheme. -/
theorem isUniversalOver_tautologicalDatumUnit_empty :
    (tautologicalDatumUnit (∅ : Scheme.{u})).IsUniversalOver :=
  TautologicalDatum.isUniversalOver_of_isEmpty _

end Stacks.RelativeProj

end
