module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Section
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic

/-!
# Sections of a projective bundle and invertible quotients

Let `X` be a scheme, `F` a quasi-coherent `𝒪_X`-module and `π : 𝐏(F) ⟶ X` the projection of
the projective bundle of `F`. Tag 0B3V asserts that the sections of `π` are in bijection with
the invertible quotients of `F`, taken up to isomorphism of the quotient module.

The bijection is governed by a *tautological datum* on `𝐏(F)`: an invertible module `𝒪(1)` on
`𝐏(F)` together with a surjection `τ : π^*F ⟶ 𝒪(1)`. Given such a datum, a section `σ` of `π`
yields an invertible quotient of `F` with no further input, by pulling `τ` back along `σ` and
using `σ ≫ π = 𝟙` to identify `σ^*π^*F` with `F`. That construction is
`Stacks.RelativeProj.TautologicalDatum.pullbackQuotient`, and the induced map on isomorphism
classes is `Stacks.RelativeProj.TautologicalDatum.sectionsMap`; both are unconditional.

What the bijection needs beyond this is exactly that `sectionsMap` be bijective, which is the
mapping-in half of the universal property of relative `Proj` (Constructions, Section 01NS) in
its two parts: every invertible quotient is classified by some section, and a section is
determined by the quotient it classifies. These two are packaged as
`Stacks.RelativeProj.TautologicalDatum.IsUniversal`, and
`Stacks.RelativeProj.TautologicalDatum.sectionsEquivInvertibleQuotients` is the bijection.

## Main definitions

* `Stacks.RelativeProj.TautologicalDatum`: an invertible module on `𝐏(F)` together with a
  surjection onto it from `π^*F`.
* `Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap`: the pullback of the tautological
  surjection along a section of `π`, read as a map out of `F` itself.
* `Stacks.RelativeProj.TautologicalDatum.pullbackQuotient`: that map as an invertible quotient
  of `F`, which is the forward direction of Tag 0B3V's bijection.
* `Stacks.RelativeProj.TautologicalDatum.Classifies`: the relation "the section `σ` classifies
  the invertible quotient `Q`", namely that `Q` is isomorphic over `F` to the quotient `σ`
  pulls back.
* `Stacks.RelativeProj.TautologicalDatum.sectionsMap`: the induced map from the sections of `π`
  to the isomorphism classes of invertible quotients of `F`.
* `Stacks.RelativeProj.TautologicalDatum.IsUniversal`: the assertion that every invertible
  quotient is classified by a section and that a section is determined by the quotient it
  classifies.
* `Stacks.RelativeProj.TautologicalDatum.sectionsEquivInvertibleQuotients`: Tag 0B3V's
  bijection, for a universal tautological datum.

## Main results

* `Stacks.RelativeProj.TautologicalDatum.epi_pullbackQuotientMap`: the pulled-back
  tautological map is surjective, so it really is an invertible quotient. No hypothesis.
* `Stacks.RelativeProj.TautologicalDatum.classifies_iff`: the relation spelled out as the
  existence of an isomorphism of quotient modules compatible with the two quotient maps.
* `Stacks.RelativeProj.TautologicalDatum.sectionsMap_eq_iff`: `sectionsMap` sends a section to
  the class of `Q` exactly when the section classifies `Q`.
* `Stacks.RelativeProj.TautologicalDatum.sectionsEquivInvertibleQuotients_eq_iff`: the same
  for the bijection, which is the normalization Tag 0B3V asks of it.
* `Stacks.RelativeProj.TautologicalDatum.classifies_symm_apply`: the section attached to an
  invertible quotient by the inverse bijection classifies that quotient.
* `Stacks.RelativeProj.TautologicalDatum.isUniversal_of_equiv`: conversely, a bijection
  normalized by the tautological quotient forces `IsUniversal`, so neither half of that
  hypothesis is a strengthening introduced here.
* `Stacks.RelativeProj.TautologicalDatum.eq_of_normalized`: a normalized bijection is unique,
  so Tag 0B3V's bijection is canonical rather than merely existent.

## Implementation notes

**`TautologicalDatum` is inhabited at every rank.** `Stacks.SymGraded.nonempty_tautologicalDatum`
of `StacksFrontier/AlgebraicGeometry/ProjectiveBundleTwists/LocalGeneration.lean` produces one for
every quasi-coherent module on every scheme, with no hypothesis; the next note says how. At rank
one there is also the explicit `Stacks.RelativeProj.TautologicalDatum.ofInvertible`, which takes
`π^*F` for `𝒪(1)` and the identity for the universal surjection — the tautological datum when `F`
is invertible, since then `𝐏(F)` is the base; `Stacks.RelativeProj.tautologicalDatumUnit` is that
datum at the structure sheaf. Those two use only the unconditional
`Stacks.Modules.isInvertible_pullback`.

**At rank at least two.** `Stacks.SymGraded.projectiveBundleTwist` is `𝒪_{𝐏(E)}(n)` for every
quasi-coherent `E` at every rank, built from Tag 01NR's twist datum
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, which exists for *every*
quasi-coherent graded algebra on *every* scheme with no further hypothesis.

* It is invertible: `Stacks.SymGraded.isInvertible_projectiveBundleTwist`.
* `Sym(E)` is generated in degree one over every affine open,
  `Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra`, which rests on the
  sheafification assertion of Tag 01CG, `SheafOfModules.symmetricPower_isSheafification`.

These supply three of the four fields of `TautologicalDatum` at arbitrary rank. The fourth,
`epi_univ` — that the universal degree-one map `Stacks.SymGraded.bundleTwistUniv` be an
epimorphism — follows by `Stacks.SymGraded.exists_tautologicalDatum_of_exists_bundleSection` from
local generation: every section of `𝒪_{𝐏(E)}(1)` is locally an `𝒪_{𝐏(E)}`-multiple of one of Tag
01OB's sections coming from the base, which is `Stacks.SymGraded.exists_local_bundleSection`. On
an affine chart this is
`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection` together with
`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.exists_mem_basicOpen_degreeOne`, and it is carried
off the chart by the compatibility of
`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.mapSection` with restriction of the open
and with the scalar action, `Stacks.AlgebraicGeometry.TwistDataFromChart.mapSection_res` and
`Stacks.AlgebraicGeometry.TwistDataFromChart.mapSection_smul`.

**`IsUniversal` below is inhabited, and only degenerately.** Its only producer in this file,
`isUniversal_of_equiv`, takes Tag 0B3V's bijection as its input and so inhabits nothing. An
inhabitant is in
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/Universal.lean`:
`Stacks.RelativeProj.TautologicalDatum.isUniversal_of_isEmpty` holds for *every* tautological
datum over a scheme with no points, and
`Stacks.RelativeProj.isUniversal_tautologicalDatumUnit_empty` is the unconditional term at the
structure sheaf of the empty scheme, so the six declarations below quantified over `IsUniversal`
are not vacuous. They are not exercised either: over such a scheme both sides of the bijection
are one-element types. That file also measures what a non-degenerate inhabitant costs, in
`Stacks.RelativeProj.TautologicalDatum.isUniversal_ofInvertible_iff_sections`: for the canonical
datum of an invertible module, `IsUniversal` is *equivalent* to `π` having exactly one section —
the identification of `𝐏(F)` with the base on `X`-points, which is nowhere in this repository —
and to nothing else, the module-theoretic half being the theorem
`Stacks.Divisors.isIso_q_of_isInvertible`.

**Why the datum carries only the degree-one surjection.** Tag 01O4's datum is a graded algebra
map `f^*𝒜 ⟶ ⨁ₙ L^{⊗ n}` whose degree-one part is surjective. The forward direction of the
bijection consumes only the degree-one part, so that is all this structure carries; the higher
degrees are determined by it on `𝐏(F)` and are not needed to define `pullbackQuotient`. A
datum carrying the whole graded map would be harder to inhabit and no more useful here.

**The two invertibility predicates.** `Stacks.Divisors.InvertibleQuotient` records
invertibility as `AlgebraicGeometry.SheafOfModules.IsInvertible`, which is therefore what
`TautologicalDatum` records as well, while the unconditional stability of invertibility under
pullback along a morphism of schemes, `Stacks.Modules.isInvertible_pullback`, concludes in
`Stacks.SheafOfModules.IsInvertible`. The two are crossed once, in each direction, by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. Both names are written out in
full: inside a namespace beginning `Stacks`, the bare name `SheafOfModules.IsInvertible`
resolves to `Stacks.SheafOfModules.IsInvertible` with no ambiguity error.

**Surjectivity of the pulled-back quotient** is formal: `Scheme.Modules.pullback σ` is a left
adjoint, hence preserves epimorphisms, and the three comparison maps that identify `σ^*π^*F`
with `F` are isomorphisms.

That a section of `π` is a closed immersion — the second assertion of Tag 0B3V — is
`Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase` and needs none of
this.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace Stacks.RelativeProj

open Stacks.Divisors

/-- **A tautological datum on the projective bundle `𝐏(F)`**: an invertible module on `𝐏(F)`
together with a surjection onto it from the pullback of `F` along the projection. On `𝐏(F)`
this is `𝒪(1)` with the universal surjection of Tag 01O4. -/
structure TautologicalDatum (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] where
  /-- The tautological invertible module, `𝒪_{𝐏(F)}(1)`. -/
  twist : (projectiveBundle X F).Modules
  /-- It is invertible. -/
  invertible : AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveBundle X F).presheaf
    (projectiveBundle X F).ringCatSheaf.2 twist
  /-- The tautological quotient map `π^*F ⟶ 𝒪(1)`. -/
  univ : (Scheme.Modules.pullback (projectiveBundleToBase X F)).obj F ⟶ twist
  /-- It is surjective. -/
  epi_univ : Epi univ

namespace TautologicalDatum

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]

/-- **The tautological quotient map pulled back along a section**, read as a map out of `F`.
The three comparison isomorphisms identify `F` with `σ^*π^*F`, using `σ ≫ π = 𝟙 X`. -/
def pullbackQuotientMap (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) :
    F ⟶ (Scheme.Modules.pullback σ).obj D.twist :=
  (Scheme.Modules.pullbackId X).inv.app F ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app F ≫
    (Scheme.Modules.pullbackComp σ (projectiveBundleToBase X F)).inv.app F ≫
    (Scheme.Modules.pullback σ).map D.univ

/-- **The pulled-back tautological quotient map is surjective.** The three comparisons are
isomorphisms and `Scheme.Modules.pullback σ`, being a left adjoint, preserves epimorphisms. -/
instance epi_pullbackQuotientMap (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) : Epi (D.pullbackQuotientMap σ hσ) := by
  have := D.epi_univ
  unfold pullbackQuotientMap
  infer_instance

/-- **The invertible quotient of `F` classified by a section of `π`.** This is the forward
direction of Tag 0B3V's bijection, and it needs no hypothesis beyond the datum. -/
def pullbackQuotient (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) : InvertibleQuotient X F where
  L := (Scheme.Modules.pullback σ).obj D.twist
  invertible :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (@Stacks.Modules.isInvertible_pullback _ _ σ D.twist
        ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr D.invertible))
  q := D.pullbackQuotientMap σ hσ
  epi := inferInstance

/-- The quotient map of `D.pullbackQuotient σ hσ` is `D.pullbackQuotientMap σ hσ`. -/
@[simp]
theorem pullbackQuotient_q (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) :
    (D.pullbackQuotient σ hσ).q = D.pullbackQuotientMap σ hσ :=
  rfl

/-- **The section `σ` classifies the invertible quotient `Q`**: `Q` is isomorphic over `F` to
the quotient that `σ` pulls back from the tautological one. -/
def Classifies (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) (Q : InvertibleQuotient X F) : Prop :=
  (D.pullbackQuotient σ hσ).IsEquivalent Q

/-- The classifying relation spelled out: an isomorphism from the pullback of the tautological
module to the quotient module, carrying the pulled-back tautological map to `Q.q`. -/
theorem classifies_iff (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) (Q : InvertibleQuotient X F) :
    D.Classifies σ hσ Q ↔
      ∃ α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L,
        D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q :=
  Iff.rfl

/-- A section classifies the quotient it pulls back. -/
theorem classifies_pullbackQuotient (D : TautologicalDatum X F)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) :
    D.Classifies σ hσ (D.pullbackQuotient σ hσ) :=
  (invertibleQuotientSetoid X F).refl _

/-- The classifying relation only depends on the isomorphism class of the quotient. -/
theorem Classifies.trans {D : TautologicalDatum X F} {σ : X ⟶ projectiveBundle X F}
    {hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X} {Q R : InvertibleQuotient X F}
    (h : D.Classifies σ hσ Q) (hQR : Q.IsEquivalent R) : D.Classifies σ hσ R :=
  (invertibleQuotientSetoid X F).trans h hQR

/-- **The map from sections of `π` to isomorphism classes of invertible quotients of `F`**,
sending a section to the class of the quotient it pulls back. Unconditional. -/
def sectionsMap (D : TautologicalDatum X F) :
    { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X } →
      InvertibleQuotientClass X F :=
  fun σ => Quotient.mk (invertibleQuotientSetoid X F) (D.pullbackQuotient σ.1 σ.2)

/-- `sectionsMap` sends a section `σ` to the class of `Q` if and only if `σ` classifies `Q`. -/
theorem sectionsMap_eq_iff (D : TautologicalDatum X F)
    (σ : { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X })
    (Q : InvertibleQuotient X F) :
    D.sectionsMap σ = Quotient.mk (invertibleQuotientSetoid X F) Q ↔ D.Classifies σ.1 σ.2 Q :=
  Quotient.eq (r := invertibleQuotientSetoid X F)

/-- **The mapping-in half of the universal property of `𝐏(F)`**, for a tautological datum: every
invertible quotient of `F` is classified by a section of `π`, and a section is determined by the
quotient it classifies. This is Constructions, Section 01NS for the symmetric algebra of `F`,
and it is what Tag 0B3V's bijection needs beyond the datum itself. -/
class IsUniversal (D : TautologicalDatum X F) : Prop where
  /-- Every invertible quotient is classified by a section. -/
  exists_classifies : ∀ Q : InvertibleQuotient X F, ∃ σ : X ⟶ projectiveBundle X F,
    ∃ hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X, D.Classifies σ hσ Q
  /-- A section is determined by the quotient it classifies. -/
  eq_of_classifies : ∀ (σ σ' : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (hσ' : σ' ≫ projectiveBundleToBase X F = 𝟙 X) (Q : InvertibleQuotient X F),
    D.Classifies σ hσ Q → D.Classifies σ' hσ' Q → σ = σ'

/-- For a universal tautological datum, `sectionsMap` is a bijection from the sections of `π`
to the isomorphism classes of invertible quotients of `F`. -/
theorem bijective_sectionsMap (D : TautologicalDatum X F) [hD : D.IsUniversal] :
    Function.Bijective D.sectionsMap := by
  refine ⟨fun σ σ' h => Subtype.ext ?_, Quotient.ind fun Q => ?_⟩
  · exact hD.eq_of_classifies σ.1 σ'.1 σ.2 σ'.2 (D.pullbackQuotient σ'.1 σ'.2)
      ((D.sectionsMap_eq_iff σ _).1 h) (D.classifies_pullbackQuotient σ'.1 σ'.2)
  · obtain ⟨σ, hσ, h⟩ := hD.exists_classifies Q
    exact ⟨⟨σ, hσ⟩, (D.sectionsMap_eq_iff ⟨σ, hσ⟩ Q).2 h⟩

/-- **Tag 0B3V's bijection between the sections of `π : 𝐏(F) ⟶ X` and the invertible quotients
of `F` up to isomorphism**, for a universal tautological datum. The underlying map is
`sectionsMap`, so it is normalized by the tautological quotient. -/
def sectionsEquivInvertibleQuotients (D : TautologicalDatum X F) [D.IsUniversal] :
    { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X } ≃
      InvertibleQuotientClass X F :=
  Equiv.ofBijective D.sectionsMap D.bijective_sectionsMap

/-- The bijection sends a section `σ` to the class of the invertible quotient it pulls back. -/
@[simp]
theorem sectionsEquivInvertibleQuotients_apply (D : TautologicalDatum X F) [D.IsUniversal]
    (σ : { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X }) :
    D.sectionsEquivInvertibleQuotients σ =
      Quotient.mk (invertibleQuotientSetoid X F) (D.pullbackQuotient σ.1 σ.2) :=
  rfl

/-- **The bijection sends a section to the class of `Q` exactly when the section classifies
`Q`.** This is the normalization of the bijection by the tautological quotient. -/
theorem sectionsEquivInvertibleQuotients_eq_iff (D : TautologicalDatum X F) [D.IsUniversal]
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (Q : InvertibleQuotient X F) :
    D.sectionsEquivInvertibleQuotients ⟨σ, hσ⟩ =
        Quotient.mk (invertibleQuotientSetoid X F) Q ↔ D.Classifies σ hσ Q :=
  D.sectionsMap_eq_iff ⟨σ, hσ⟩ Q

/-- The section attached to an invertible quotient by the inverse bijection classifies it. -/
theorem classifies_symm_apply (D : TautologicalDatum X F) [D.IsUniversal]
    (Q : InvertibleQuotient X F) :
    D.Classifies (D.sectionsEquivInvertibleQuotients.symm
        (Quotient.mk (invertibleQuotientSetoid X F) Q)).1
      (D.sectionsEquivInvertibleQuotients.symm
        (Quotient.mk (invertibleQuotientSetoid X F) Q)).2 Q :=
  (D.sectionsEquivInvertibleQuotients_eq_iff _ _ Q).1
    (D.sectionsEquivInvertibleQuotients.apply_symm_apply _)

/-- **The two hypotheses are not merely sufficient: any normalized bijection forces them.** So
for a fixed tautological datum, `IsUniversal` is exactly the assertion of Tag 0B3V's bijection,
and neither half of it is a strengthening introduced here. -/
theorem isUniversal_of_equiv (D : TautologicalDatum X F)
    (e : { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X } ≃
      InvertibleQuotientClass X F)
    (he : ∀ (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
      (Q : InvertibleQuotient X F), e ⟨σ, hσ⟩ = Quotient.mk (invertibleQuotientSetoid X F) Q ↔
        D.Classifies σ hσ Q) :
    D.IsUniversal where
  exists_classifies Q :=
    ⟨(e.symm (Quotient.mk (invertibleQuotientSetoid X F) Q)).1,
      (e.symm (Quotient.mk (invertibleQuotientSetoid X F) Q)).2,
      (he _ _ Q).1 (by simp)⟩
  eq_of_classifies σ σ' hσ hσ' Q h h' :=
    congrArg Subtype.val (e.injective (((he σ hσ Q).2 h).trans ((he σ' hσ' Q).2 h').symm))

/-- **A bijection normalized by the tautological quotient is unique.** Tag 0B3V's bijection is
therefore canonical and not merely some bijection: `sectionsEquivInvertibleQuotients` is the
only map satisfying `sectionsEquivInvertibleQuotients_eq_iff`. -/
theorem eq_of_normalized (D : TautologicalDatum X F)
    (e e' : { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X } ≃
      InvertibleQuotientClass X F)
    (he : ∀ (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
      (Q : InvertibleQuotient X F), e ⟨σ, hσ⟩ = Quotient.mk (invertibleQuotientSetoid X F) Q ↔
        D.Classifies σ hσ Q)
    (he' : ∀ (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
      (Q : InvertibleQuotient X F), e' ⟨σ, hσ⟩ = Quotient.mk (invertibleQuotientSetoid X F) Q ↔
        D.Classifies σ hσ Q) :
    e = e' := by
  refine Equiv.coe_inj.1 (funext fun σ => ?_)
  have h := D.classifies_pullbackQuotient σ.1 σ.2
  exact ((he _ _ _).2 h).trans ((he' _ _ _).2 h).symm

/-- The section attached to an invertible quotient by the inverse bijection is a closed
immersion, by Tag 0B3V's second assertion. -/
instance isClosedImmersion_symm_apply (D : TautologicalDatum X F) [D.IsUniversal]
    (c : InvertibleQuotientClass X F) :
    IsClosedImmersion (D.sectionsEquivInvertibleQuotients.symm c).1 :=
  isClosedImmersion_of_section_projectiveBundleToBase X F _
    (D.sectionsEquivInvertibleQuotients.symm c).2

end TautologicalDatum

end Stacks.RelativeProj

end
