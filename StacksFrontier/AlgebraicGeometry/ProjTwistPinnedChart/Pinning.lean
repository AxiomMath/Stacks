module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartCocycleMatch
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistPinnedChart.Basic

/-!
# The pinning match: a pulled-back twisting section is the ring map's value times the frame

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `Y` a scheme, `f : A →+* Γ(Y, ⊤)` a ring map whose
image of the irrelevant ideal generates, and `g = Proj.fromOfGlobalSections 𝒜 f` the morphism
`Y ⟶ Proj A` it classifies. Let `r` be homogeneous of degree `d > 0` with `f r = 1`, so that `g`
lands wholly inside the standard open `D₊(r)` and
`StacksFrontier/AlgebraicGeometry/ProjTwistPinnedChart/Basic.lean` trivialises `g⁎𝒪(d)` on the
pulled-back degree-`d` section of `r`.

**This file computes every other pulled-back degree-`d` section in that frame**: for `a`
homogeneous of degree `d`,

`g⁎(degreeSection 𝒜 d a) |_V = (f a)|_V · g⁎(degreeSection 𝒜 d r) |_V`

over every open `V` of `Y`. So the trivialisation is not merely an isomorphism `g⁎𝒪(d) ≅ 𝒪_Y`: it
carries the degree-`d` tautological section of `a` to the scalar `f a`, on the nose.

## Why this file exists

On the route from the universal property of absolute `Proj` to [Stacks, Tag 0B3V]'s bijection
between the sections of `π : 𝐏(ℰ) ⟶ X` and the invertible quotients of `ℰ`, what is left between
step 2 (the twist through the chart, proved) and step 4 (descent along an open cover, proved) is
**one statement with no gluing and no global section in it**: over a trivialising affine open `V`
of the base, the comparison isomorphism between `σ⁎𝒪_{𝐏(ℰ)}(1)` and `ℒ|_V` must *carry the
pulled-back tautological map to `q`* rather than merely exist. Freeness of rank one pinned on the
frame gives the isomorphism; what it does not give is the compatibility with the two quotient
maps.

That compatibility is this file's conclusion, in its absolute form. The local section of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/LocalSectionMap.lean` is built from
`Stacks.RelativeProj.localChartMap`, which *is*
`AlgebraicGeometry.Proj.fromOfGlobalSections` of the dehomogenisation
`Stacks.RelativeProj.localDehomogenize` of `Sym ℰ` at the trivialised quotient; the degree-one
elements of the graded section ring `Γ(V, Sym ℰ)` are the sections of `ℰ` over `V`; and the
dehomogenisation sends such a section to the value of
`Stacks.RelativeProj.trivializedQuotientHom` on it. So at `d = 1` the identity below says exactly
that, in the frame pinned by the inverted section, the pulled-back tautological section of a
section `m` of `ℰ` is the trivialised quotient of `m` — the pinning match.

## Main results

* `ProjTwistPinnedChart.appLE_awayToSection_fromOfGlobalSections_basicOpen`
  and `…ProjTwistPinnedChart.appLE_awayToSection_fromOfGlobalSections`: **the effect of
  `AlgebraicGeometry.Proj.fromOfGlobalSections` on the sections `a/tᵏ` of a standard open**, for
  an arbitrary graded ring. This is `Stacks.ProjGlobalSectionsAppTop.projAwayHom`, the
  computation of the chart morphism on sections, read along the factorisation of the glued
  morphism through its chart.
* `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.projAwayHom_mk_of_app_eq_one`: the value of
  that ring map on `p/tᵏ` when `f t = 1`, where no inverse has to be taken.
* `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.resT_pullbackDegreeSection_eq_app_smul`:
  **the pinning match.** Over every open of `Y`, the pulled-back degree-`d` section of `a` is
  `f a` times the pulled-back degree-`d` section of `r`.

## Implementation notes

**The scalar is `f a` and not a fraction**, because `f r = 1`. Without that hypothesis the scalar
is `Stacks.ProjGlobalSectionsAppTop.projAwayHom` of the degree-zero fraction `a/r`, which is the
shape `projAwayHom_mk_of_app_eq_one` specialises; the hypothesis is not a loss of generality for
the consumer, since `Stacks.RelativeProj.exists_app_trivializedQuotientHom_eq_one` together with
`Stacks.SymmetricDehomogenize.dehomogenize_of_one` produces exactly an `r` with `f r = 1`.

**The morphism is a free variable with a defining equation.** Both
`appLE_awayToSection_fromOfGlobalSections` and the pinning lemma take `g` together with
`hgeq : g = Proj.fromOfGlobalSections 𝒜 f hf` rather than the glued morphism itself. That is what
lets them be applied at `Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj` of
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.chartFactor`, whose identification with `g` is
`toProj_chartFactor` — a proved equation and not a definitional one. Rewriting with it inside the
goal is not available: the proof argument of `AlgebraicGeometry.Scheme.Hom.appLE` mentions the
morphism, so `rw` reports the motive as not type-correct. Supplying the equation as a hypothesis
moves the transport into the application and needs no cast.

**`hg` is not an extra assumption.** The hypothesis that `g` lands wholly inside `D₊(r)` follows
from `h1` and Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen`, which
computes that preimage as `Y_{f r} = Y_1 = ⊤`; equivalently it is
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit_preimage_basicOpen`, since
`…ProjF1DegreeOneChart.fromOfIsUnit` is `AlgebraicGeometry.Proj.fromOfGlobalSections` with a
`Prop` for its last argument and the two are therefore the same morphism. It is taken as a
hypothesis only because `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.chartFactor` is indexed by
it, so a consumer holding a proof of its own should not be forced to transport along proof
irrelevance in the index of the conclusion.

**Only the degree-`d` part of the ratio identity is used.**
`Stacks.AlgebraicGeometry.ProjChartCocycleMatch.resTop_pullbackDegreeSection_eq_smul` is the
identity `g⁎(degreeSection a) = φ^♯(a/r) · g⁎(degreeSection r)` for two homogeneous elements of
one common degree, over any open mapping into `D₊(r)`; here that open is all of `Y`, so no
covering and no shrinking appears, and the whole of the new content is the identification of
`φ^♯(a/r)` with `f a`.

**No `@[stacks 0B3V]` attribute is attached**, and none of any other tag. [Stacks, Tag 0B3V] is
the bijection between the sections of `π : 𝐏(ℰ) ⟶ X` and the invertible quotients of `ℰ` up to
isomorphism; what is proved here is one identity of sections of a pulled-back twisting sheaf over
a single scheme, with no bundle, no quotient, no invertible module and no bijection in it. It is a
step in the route to that tag — the pinning of a trivialisation, which the tag's bijection needs
and which freeness alone does not give — and a registration of the tag on it would be the tag's
name on a strictly weaker statement. The tags of the inputs are already carried where they are
proved: [Stacks, Tag 01MV] at
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.nonvanishingLocus_degreeSection_inter` and
[Stacks, Tag 0H78] at `Stacks.NonvanishingPullback.preimage_nonvanishingLocus`.

## Not done here

**The transport to the projective bundle is not performed.** Composing the identity below with
`Stacks.ProjectiveBundle.chartTwistIso` and
`Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap` — so as to read it as the local
hypothesis of
`Stacks.RelativeProj.TautologicalDatum.exists_classifies_of_pullback_cover` — needs, beyond this
file, the identification of the degree-one component of the graded map
`Stacks.RelativeProj.localDehomogenize` with `Stacks.RelativeProj.trivializedQuotientHom`
(`Stacks.SymmetricDehomogenize.gradedHom`'s degree-one clause) and the comparison of
`Stacks.RelativeProj.localSection` with
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProjOfIsUnit`, which the local section
deliberately does not go through. Neither is in this file.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjChartCocycleMatch
open Stacks.ProjGlobalSectionsAppTop
open Stacks.ProjectiveFromSections (resT)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistPinnedChart

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d : ℕ} {t : A}

/-! ### `Proj.fromOfGlobalSections` on the sections of a standard open -/

/-- **The glued morphism of `AlgebraicGeometry.Proj.fromOfGlobalSections`, on the sections
`a/tᵏ` of the standard open `D₊(t)`**, over the chart `Y_{f t}` where the morphism lands in that
standard open. It is `Stacks.ProjGlobalSectionsAppTop.projAwayHom`.

Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections_resLE` says that the glued morphism
restricted to `Y_{f t}` *is* the chart morphism
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`, and
`Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop` computes the latter on
sections; `Stacks.ProjGlobalSectionsAppTop.topIso_inv_resLE_appTop` is what reads
`AlgebraicGeometry.Scheme.Hom.resLE` on global sections as
`AlgebraicGeometry.Scheme.Hom.appLE`. -/
theorem appLE_awayToSection_fromOfGlobalSections_basicOpen (f : A →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (z : Away 𝒜 t) :
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf).appLE
          (AlgebraicGeometry.Proj.basicOpen 𝒜 t) (Y.basicOpen (f t))
          (AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf h0d hd).ge
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 t).hom z) = projAwayHom 𝒜 f z := by
  have h1 := topIso_inv_resLE_appTop (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf)
    (U := AlgebraicGeometry.Proj.basicOpen 𝒜 t) (V := Y.basicOpen (f t))
    (AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf h0d hd).ge
  rw [AlgebraicGeometry.Proj.fromOfGlobalSections_resLE 𝒜 f hf h0d hd] at h1
  have h2 := toBasicOpenOfGlobalSections_appTop 𝒜 f h0d hd
  have h3 := (congrArg (fun k => (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 t hd h0d).hom ≫ k)
    h1).symm.trans h2
  have h5 := (cancel_mono ((Y.basicOpen (f t)).topIso.inv)).mp ((Category.assoc _ _ _).trans h3)
  exact CategoryTheory.ConcreteCategory.congr_hom h5 z

/-- **The same, over any open inside the chart, and for a morphism given by an equation.** The
equation `hgeq` is how the statement is applied to
`Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj` of
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.chartFactor`; see the implementation notes for why
the morphism cannot be rewritten inside the goal. -/
theorem appLE_awayToSection_fromOfGlobalSections (f : A →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    {g : Y ⟶ AlgebraicGeometry.Proj 𝒜}
    (hgeq : g = AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf) {V : Y.Opens}
    (hle : V ≤ g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 t) (hV : V ≤ Y.basicOpen (f t))
    (z : Away 𝒜 t) :
    g.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 t) V hle
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 t).hom z)
      = (Y.presheaf.map (homOfLE hV).op).hom (projAwayHom 𝒜 f z) := by
  subst hgeq
  have h := CategoryTheory.ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_map (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf)
      (AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf h0d hd).ge
      (homOfLE hV).op) ((AlgebraicGeometry.Proj.awayToSection 𝒜 t).hom z)
  rw [CategoryTheory.comp_apply,
    appLE_awayToSection_fromOfGlobalSections_basicOpen 𝒜 f hf h0d hd z] at h
  exact h.symm

/-- **The chart's ring map on `p/tᵏ` when `f t = 1`**, where the inverse of `(f t)|·` is `1` and
no unit is transported. -/
theorem projAwayHom_mk_of_app_eq_one (f : A →+* Γ(Y, ⊤)) (hd : t ∈ 𝒜 d) (h1 : f t = 1) (k : ℕ)
    (p : A) (hp : p ∈ 𝒜 (k • d)) :
    projAwayHom 𝒜 f (Away.mk 𝒜 hd k p hp) = resTop (Y.basicOpen (f t)) (f p) := by
  have hv : resTop (Y.basicOpen (f t)) (f t) * 1 = 1 := by
    rw [h1, map_one, mul_one]
  rw [projAwayHom_apply_mk_of_mul_eq_one 𝒜 f hd k p hp hv, one_pow, mul_one]

/-! ### The pinning match -/

/-- **The pinning match.** Let `f : A →+* Γ(Y, ⊤)` classify a morphism `g : Y ⟶ Proj A` and let
`r` be homogeneous of degree `d > 0` with `f r = 1`, so that `g` lands wholly inside `D₊(r)` and
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.bijective_smul_pullbackDegreeSection` makes the
pulled-back degree-`d` section of `r` a frame of `g⁎𝒪(d)` over every open of `Y`. **Then the
pulled-back degree-`d` section of any homogeneous `a` of degree `d` is `f a` times that frame**,
over every open of `Y`.

This is the compatibility that freeness alone does not give. A bare trivialisation
`g⁎𝒪(d) ≅ 𝒪_Y` says nothing about which section of the twist corresponds to which function on
`Y`; the identity here says that the correspondence is `a ↦ f a` on the degree-`d` tautological
sections, which is what [Stacks, Tag 0B3V]'s bijection is normalised by. See this file's
introduction for the reduction of the tag's local clause to it, and `Not done here` for what the
transport to the projective bundle still owes. -/
theorem resT_pullbackDegreeSection_eq_app_smul (f : A →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) (h0d : 0 < d) (r a : 𝒜 d)
    (h1 : f (r : A) = 1) {g : Y ⟶ AlgebraicGeometry.Proj 𝒜}
    (hgeq : g = AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf)
    (hg : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (r : A) = ⊤) (V : Y.Opens) :
    resT V (pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) a)
      = resTop V (f (a : A)) •
        resT V (pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r) := by
  have hbo : Y.basicOpen (f (r : A)) = ⊤ := by
    rw [h1]; exact Y.basicOpen_of_isUnit isUnit_one
  have hVb : V ≤ Y.basicOpen (f (r : A)) := le_top.trans hbo.ge
  have hV : V ≤ toProj 𝒜 (chartFactor 𝒜 r.2 g hg) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen 𝒜 (r : A) := by
    rw [toProj_chartFactor]; exact le_top.trans hg.ge
  refine (resTop_pullbackDegreeSection_eq_smul 𝒜 (chartFactor 𝒜 r.2 g hg) a r hV).trans ?_
  refine congrArg
    (fun z => z • resT V (pullbackDegreeSection 𝒜 (chartFactor 𝒜 r.2 g hg) r)) ?_
  refine (appLE_awayToSection_fromOfGlobalSections 𝒜 f hf h0d r.2
    ((toProj_chartFactor 𝒜 r.2 g hg).trans hgeq) hV hVb _).trans ?_
  rw [projAwayHom_mk_of_app_eq_one 𝒜 f r.2 h1 1 (a : A) (by simp),
    resTop_resTop hVb]

end Stacks.AlgebraicGeometry.ProjTwistPinnedChart

end
