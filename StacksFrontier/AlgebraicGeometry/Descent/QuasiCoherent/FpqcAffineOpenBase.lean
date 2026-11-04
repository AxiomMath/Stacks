module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcBaseGlobalization

/-!
# Quasi-coherent descent over an affine base, and over each affine open of an arbitrary base

`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcBaseGlobalization.lean` leaves the
effectivity half of Stacks 023T resting on one statement,
`AlgebraicGeometry.QuasicoherentDescentData.EffectiveSigmaFamilyOverAnyBase`: descent along a
single faithfully flat morphism over a base which is not assumed affine.  That statement carries
no hypothesis whatsoever, so proving it means carrying out the whole of the first paragraph of the
source's proof — localize the base, descend over each affine open, glue.

This file carries out the localization and the descent, unconditionally, and leaves only the
gluing.  Its two unconditional results are the *first* and *second* steps:

* over an affine base — not merely over a spectrum — every quasi-coherent descent datum for every
  fpqc covering family is effective;
* consequently, for an **arbitrary** base `S`, an arbitrary fpqc covering family of `S` and an
  arbitrary quasi-coherent descent datum for it, the datum restricted along the base change to
  any affine open of `S` is effective.

What is left is the third step and nothing else, and it mentions no fpqc descent: a datum whose
restrictions to the members of an affine open covering of the base are effective is effective.
That is `AlgebraicGeometry.QuasicoherentDescentData.EffectiveGluesOverAffineOpens`, and
`AlgebraicGeometry.QuasicoherentDescentData.effectiveGluesOverAffineOpens_iff` shows it is
equivalent to the effectivity half of Stacks 023T, so nothing has been strengthened along the
way.

## Main definitions

* `AlgebraicGeometry.QuasicoherentDescentData.homOverPullback₁`: the base change of a family of
  morphisms, as a morphism of families over the morphism of bases.
* `AlgebraicGeometry.QuasicoherentDescentData.EffectiveGluesOverAffineOpens`: effectivity of a
  quasi-coherent descent datum is Zariski-local on the base.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentData.mem_fpqcPrecoverage_pushforward`: composing a
  family with a flat surjective quasi-compact morphism out of its target preserves the fpqc
  covering condition.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage_isAffine`: **the
  effectivity half of Stacks 023T over an affine base, unconditionally**, at an arbitrary index
  universe.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_pullFunctor_homOverPullback₁`: **the
  restriction of an arbitrary quasi-coherent descent datum to an affine open of an arbitrary base
  is effective**, unconditionally.
* `AlgebraicGeometry.QuasicoherentDescentData.effectiveSigmaFamilyOverAnyBase_of_glues`: the one
  statement `FpqcBaseGlobalization` rests on, from the Zariski locality alone.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage_of_glues`: **the
  effectivity half of Stacks 023T over the Zariski locality alone**, for an arbitrary fpqc
  covering family of an arbitrary scheme at an arbitrary index universe.

## Implementation notes

Over an affine base the source's statement is reached from the one over a spectrum by transport
along `AlgebraicGeometry.Scheme.isoSpec`.  The transport of effectivity is
`…isEffective_of_forall_isEffective_pushforward_of_iso`; what it needs supplied is that the
pushed-forward family is still an fpqc covering, and that is
`mem_fpqcPrecoverage_pushforward` applied to the isomorphism, which is flat, surjective and
quasi-compact.  The generalization matters: the members of
`AlgebraicGeometry.Scheme.affineCover` are affine, and an affine scheme is a spectrum only up to
isomorphism.

No `stacks` attribute is placed: the unconditional results here are about an affine base or about
one member of a covering of the base, which is less than Stacks 023T asserts, and the general
statements carry a hypothesis.

## References

* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

namespace QuasicoherentDescentData

/-- **The base change of a family of morphisms, as a morphism of families over the morphism of
bases.**  The member above `i` is `CategoryTheory.Limits.pullback g (𝒰.f i)`, its structure
morphism is the first projection, and the square over `g` commutes by `pullback.condition`. -/
public noncomputable def homOverPullback₁ {S T : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} T)
    (g : S ⟶ T) : (𝒰.pullback₁ g).HomOver 𝒰 g where
  s₀ i := i
  h₀ i := pullback.snd g (𝒰.f i)
  w₀ _ := pullback.condition.symm

/-- **The base change of an fpqc covering family is an fpqc covering family.**  This is the fpqc
precoverage being stable under base change, read off its `0`-hypercovers. -/
public theorem mem_fpqcPrecoverage_pullback₁ {S T : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} T)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T) (g : S ⟶ T) :
    (𝒰.pullback₁ g).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S :=
  ((⟨𝒰, h𝒰⟩ : Scheme.fpqcPrecoverage.ZeroHypercover T).pullback₁ g).mem₀

/-- **Composing an fpqc covering family with a flat surjective quasi-compact morphism out of its
target is again an fpqc covering family.**

The composite family is the bind of the one-element covering `{g}` with the given family, whose
covering condition is `CategoryTheory.Precoverage.ZeroHypercover.bind`; the identification of
that bind with the pushforward is Mathlib's `PreZeroHypercover.pushforwardIsoBind`, and the fpqc
precoverage respects such isomorphisms. -/
public theorem mem_fpqcPrecoverage_pushforward {S T : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) (g : S ⟶ T) [Flat g] [Surjective g]
    [QuasiCompact g] : (𝒰.pushforward g).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T := by
  have hg : (PreZeroHypercover.singleton.{v} g).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T := by
    rw [PreZeroHypercover.presieve₀_singleton]
    exact Scheme.Hom.singleton_mem_fpqcPrecoverage g
  have hb := ((⟨PreZeroHypercover.singleton.{v} g, hg⟩ :
    Scheme.fpqcPrecoverage.ZeroHypercover T).bind (fun _ ↦ ⟨𝒰, h𝒰⟩)).mem₀
  exact PreZeroHypercover.presieve₀_mem_of_iso
    (PreZeroHypercover.pushforwardIsoBind g 𝒰).symm hb

/-- **The effectivity half of [Stacks, Tag 023T] over an affine base, unconditionally**: for
every affine scheme `S`, every fpqc covering family of `S` at any index universe, and every
quasi-coherent descent datum for it, the datum is effective.

Over a spectrum this is `…isEffective_fpqcPrecoverage_spec`.  An affine scheme is the spectrum of
its ring of functions only up to the isomorphism `AlgebraicGeometry.Scheme.isoSpec`, along which
`…isEffective_of_forall_isEffective_pushforward_of_iso` transports effectivity; the family pushed
forward along that isomorphism is still an fpqc covering by `mem_fpqcPrecoverage_pushforward`. -/
public theorem isEffective_fpqcPrecoverage_isAffine {S : Scheme.{u}} [IsAffine S]
    (𝒰 : PreZeroHypercover.{v} S) (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective := by
  refine isEffective_of_forall_isEffective_pushforward_of_iso S.isoSpec 𝒰 (fun D' ↦ ?_) D
  exact isEffective_fpqcPrecoverage_spec _
    (mem_fpqcPrecoverage_pushforward 𝒰 h𝒰 S.isoSpec.hom) D'

/-- **The restriction of a quasi-coherent descent datum to an affine open of the base is
effective**, with no hypothesis on the base, on the covering family or on the datum.

More generally the morphism `g` need not be an open immersion: for any morphism `g : U ⟶ S` with
`U` affine, the base change along `g` of an fpqc covering family of `S` is an fpqc covering family
of `U` by `mem_fpqcPrecoverage_pullback₁`, and `isEffective_fpqcPrecoverage_isAffine` applies to
it over the affine base `U`. -/
public theorem isEffective_pullFunctor_homOverPullback₁ {S T : Scheme.{u}} [IsAffine S]
    (𝒰 : PreZeroHypercover.{v} T) (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T) (g : S ⟶ T)
    (D : QuasicoherentDescentData 𝒰.f) :
    ((pullFunctor (homOverPullback₁ 𝒰 g)).obj D).IsEffective :=
  isEffective_fpqcPrecoverage_isAffine _ (mem_fpqcPrecoverage_pullback₁ 𝒰 h𝒰 g) _

/-! ### What is left: the Zariski locality of effectivity -/

/-- **Effectivity of a quasi-coherent descent datum is Zariski-local on the base**: a datum for an
fpqc covering family of a scheme `S` is effective as soon as its restriction along the base change
to each member of the affine open covering `AlgebraicGeometry.Scheme.affineCover` of `S` is
effective.

This is the third and last step of the first paragraph of the proof of Stacks 023T — glue the
quasi-coherent sheaves obtained over the affine opens, the gluing isomorphisms being produced by
the full faithfulness half of 023T over the intersections, which is already a theorem
(`…nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage`), and their cocycle
condition by its faithfulness over the triple intersections.  The hypothesis is *not* an
assumption about fpqc descent: `isEffective_pullFunctor_homOverPullback₁` discharges it for every
base, every family and every datum, so the content of this statement is exactly the gluing. -/
public abbrev EffectiveGluesOverAffineOpens : Prop :=
  ∀ {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S),
    𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S → ∀ D : QuasicoherentDescentData 𝒰.f,
      (∀ a : S.affineCover.I₀,
          ((pullFunctor (homOverPullback₁ 𝒰 (S.affineCover.f a))).obj D).IsEffective) →
        D.IsEffective

/-- **The effectivity half of [Stacks, Tag 023T] over the Zariski locality alone**, at the index
universe `v`: the hypothesis of `EffectiveGluesOverAffineOpens` is supplied by
`isEffective_pullFunctor_homOverPullback₁`, the members of
`AlgebraicGeometry.Scheme.affineCover` being affine. -/
public theorem isEffective_of_glues (h : EffectiveGluesOverAffineOpens.{v, u}) {S : Scheme.{u}}
    (𝒰 : PreZeroHypercover.{v} S) (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective :=
  h 𝒰 h𝒰 D fun a ↦ isEffective_pullFunctor_homOverPullback₁ 𝒰 h𝒰 (S.affineCover.f a) D

/-- **`EffectiveSigmaFamilyOverAnyBase` over the Zariski locality alone.**  Descent along a single
faithfully flat morphism over an arbitrary base follows from the locality, the affine case being
discharged. -/
public theorem effectiveSigmaFamilyOverAnyBase_of_glues
    (h : EffectiveGluesOverAffineOpens.{u, u}) : EffectiveSigmaFamilyOverAnyBase.{u} :=
  effectiveSigmaFamilyOverAnyBase_of_forall fun 𝒰 h𝒰 D ↦ isEffective_of_glues h 𝒰 h𝒰 D

/-- **The effectivity half of [Stacks, Tag 023T] over the Zariski locality alone**, for an
arbitrary fpqc covering family of an arbitrary scheme at an arbitrary index universe. -/
public theorem isEffective_fpqcPrecoverage_of_glues (h : EffectiveGluesOverAffineOpens.{u, u})
    {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective :=
  isEffective_fpqcPrecoverage_of_sigmaFamily (effectiveSigmaFamilyOverAnyBase_of_glues h) 𝒰 h𝒰 D

/-- The locality is *implied* by the conclusion it is used for, so assuming it is not a
strengthening of the effectivity half of Stacks 023T. -/
public theorem effectiveGluesOverAffineOpens_of_forall
    (h : ∀ {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S),
      𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S →
        ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective) :
    EffectiveGluesOverAffineOpens.{v, u} :=
  fun 𝒰 h𝒰 D _ ↦ h 𝒰 h𝒰 D

/-- **The Zariski locality is exactly the effectivity half of [Stacks, Tag 023T]**, so it is a
reformulation of what is missing and neither a weakening nor a strengthening of it. -/
public theorem effectiveGluesOverAffineOpens_iff :
    EffectiveGluesOverAffineOpens.{v, u} ↔
      ∀ {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S),
        𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S →
          ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective :=
  ⟨fun h _ 𝒰 h𝒰 D ↦ isEffective_of_glues h 𝒰 h𝒰 D, effectiveGluesOverAffineOpens_of_forall⟩

end QuasicoherentDescentData

end AlgebraicGeometry

end
