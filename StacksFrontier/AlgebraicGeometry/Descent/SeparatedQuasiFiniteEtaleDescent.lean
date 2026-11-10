module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical

/-!
# Effective descent for separated locally quasi-finite morphisms along an étale chart

Stacks 02W8 says that a descent datum for an fppf covering whose members are separated and
locally quasi-finite is effective. In the shape in which this library consumes effective
descent — `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` — that is the
assertion
```
AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS
  (@AlgebraicGeometry.IsSeparated ⊓ @AlgebraicGeometry.LocallyQuasiFinite)
```
and it is the one geometric input left in Stacks 0265, by
`AlgebraicGeometry.Space.presheaf_surjective_and_etale_of_surjectiveEtaleChart`.

This file does four things towards it. It supplies the *fppf descent* of the property of
Stacks 02W8, which is what lets `AlgebraicGeometry.Space` transport effective descent between
properties at all. It assembles the middle two steps of the proof of Stacks 02W8 — that a
separated quasi-finite morphism is quasi-affine (Stacks 02LR) and that quasi-affine morphisms
descend effectively (Stacks 0247) — into effective descent for separated *quasi-finite*
morphisms, with those two steps as named hypotheses. It proves that effective descent may be
verified after refining the covering, which is the role of Descent, Lemma 35.36.2 in the
source. And it proves the glueing step, Descent, Lemma 35.35.13: effective descent follows
from a Zariski covering of the descended sheaf by representable open subfunctors, with no
further hypothesis.

## Main results

* `AlgebraicGeometry.descendsAlong_fppf_of_descendsAlong_fpqc` is Mathlib's upgrade of fpqc
  descent to fppf descent, as a named theorem: the instance does not fire on a concrete
  property.
* `AlgebraicGeometry.isSeparated_inf_locallyQuasiFinite_descendsAlong_fppf` and
  `AlgebraicGeometry.isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_descendsAlong_fppf`
  state that separatedness together with local quasi-finiteness, and together with local
  quasi-finiteness and being locally of finite type, satisfy fppf descent.
* `AlgebraicGeometry.Space.presheaf_surjective_and_etale_of_locallyOfFiniteType_chart`
  is the atlas clause of Stacks 0265 obtained from effective descent at the property of Stacks
  02W8 proper, namely separated, locally quasi-finite *and locally of finite type* morphisms.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_refinement`: to verify
  effective descent along surjective étale morphisms of the site it suffices to verify it along
  a refinement of every covering.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover` is the
  glueing step: effective descent follows from a Zariski covering of the descended sheaf by
  representable open subfunctors.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite`
  is Stacks 02W8 for separated *quasi-finite* morphisms, reduced to Stacks 02LR and to
  effective descent for quasi-affine morphisms.

## Implementation notes

**The property of the target statement is larger than the property of Stacks 02W8.** Mathlib's
`AlgebraicGeometry.LocallyQuasiFinite` is `AlgebraicGeometry.HasRingHomProperty` for
`RingHom.QuasiFinite`, and `Algebra.QuasiFinite` deliberately omits the finite-type condition
which Stacks 00PL imposes: it asks only that every fibre `κ(p) ⊗_R S` be a finite-dimensional
`κ(p)`-vector space. So `@AlgebraicGeometry.IsSeparated ⊓ @AlgebraicGeometry.LocallyQuasiFinite`
is a strictly larger class of morphisms than the separated locally quasi-finite morphisms of
Stacks 02W8, which are
`@AlgebraicGeometry.IsSeparated ⊓ @AlgebraicGeometry.LocallyQuasiFinite ⊓
@AlgebraicGeometry.LocallyOfFiniteType`, and effective descent at the larger class does **not**
follow from Stacks 02W8. The proof of Stacks 02W8 passes through Stacks 02LR, that a
quasi-compact separated locally quasi-finite morphism is quasi-affine, which is a form of
Zariski's main theorem and is false without the finite-type hypothesis. The inclusion is strict
already for affine morphisms: `Spec ℚ ⟶ Spec ℤ` is a monomorphism, hence separated, and it is
locally quasi-finite in Mathlib's sense, since `ℚ ⊗[ℤ] ℚ = ℚ` and `ℤ/p ⊗[ℤ] ℚ = 0`, while `ℚ` is
not a finitely generated `ℤ`-algebra. Everything here is therefore stated at the smaller,
correct property, and
`AlgebraicGeometry.Space.presheaf_surjective_and_etale_of_locallyOfFiniteType_chart`
shows that the smaller property still supplies the atlas clause which Stacks 0265 needs: the
relation of an étale equivalence relation is étale, hence locally of finite type.

**What is still missing.** The source proves Stacks 02W8 in five steps: reduce to a single
faithfully flat covering of affines (Descent, Lemma 35.36.2); enlarge an affine open of the
source to a quasi-compact open stable under the descent datum, using universal openness of flat
morphisms of finite presentation (Stacks 01UA); observe that such an open is quasi-affine over
the base (Stacks 02LR); descend it (Stacks 0247); and glue the descended pieces (Descent, Lemma
35.35.13). The third and fourth steps are exactly the two hypotheses of
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite`,
so that theorem is the quasi-compact case of Stacks 02W8. The fifth step is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover`. The first
step is half-done: its refinement half is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_refinement`, while its
reduction to an affine *base* needs the Zariski glueing `AlgebraicGeometry.HasZariskiGluing`
— which is no longer an obstacle, since that is proved outright as
`AlgebraicGeometry.hasZariskiGluing` in
`StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover`
(`StacksFrontier/AlgebraicGeometry/Spaces/ZariskiGluingCover.lean:437`).

What is left is therefore the **second** step, and it is the only one left: produce, for each
quasi-compact open of the chart which is stable under the descent datum, an open subfunctor of
`X ×[Y] yoneda.obj a` cutting it out, and check that those subfunctors cover. The tool for the
first half is `AlgebraicGeometry.Space.openSubspaceOfPoints` together with
`AlgebraicGeometry.Space.presheaf_isOpenImmersion_ι_openSubspaceOfPoints`, which asks only that
the set of points be open and in particular does **not** require the ambient presheaf to be an
algebraic space — so it applies to `X ×[Y] yoneda.obj a` before anything is known about it. The
openness of the set of points is where the universal openness of Stacks 01UA enters, and the
quasi-compactness of the enlarged open is where the reduction to an affine covering of an
affine base is needed.

`AlgebraicGeometry.descendsAlong_fppf_of_descendsAlong_fpqc` duplicates the private
`descendsAlong_fppf` of `StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent`; on a
dedup pass the two should become one public theorem in this file.

The refinement theorem carries no hypothesis on `P` at all: a morphism satisfying
`CategoryTheory.MorphismProperty.relative` is stable under base change for free, by
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`, so the datum over the
refinement is obtained from the datum over the original covering with no stability assumption.
The refining morphism `p` itself is not required to be surjective or étale — only the composite
`p ≫ q` is, since that is the covering the hypothesis is applied to.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 00PL](https://stacks.math.columbia.edu/tag/00PL)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### fppf descent of the property of Stacks 02W8 -/

/-- Mathlib's upgrade of fpqc descent to fppf descent, as a named theorem: a property of
morphisms of schemes which is Zariski local on the target and descends along the surjective flat
quasi-compact morphisms descends along the surjective flat morphisms of finite presentation.

The corresponding instance does not fire by synthesis when the property is concrete, so every
use has to go through a statement whose property is a variable. -/
theorem descendsAlong_fppf_of_descendsAlong_fpqc (P : MorphismProperty Scheme.{u})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] [IsZariskiLocalAtTarget P] :
    P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  inferInstance

/-- Separatedness together with local quasi-finiteness is Zariski local on the target. -/
theorem isSeparated_inf_locallyQuasiFinite_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u}) :=
  have : IsZariskiLocalAtTarget (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.QuasiFinite)
  MorphismProperty.IsLocalAtTarget.inf _ _

/-- Separatedness together with local quasi-finiteness and with being locally of finite type —
the property of Stacks 02W8 — is Zariski local on the target. -/
theorem isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
      MorphismProperty Scheme.{u}) :=
  have := isSeparated_inf_locallyQuasiFinite_isZariskiLocalAtTarget.{u}
  have : IsZariskiLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FiniteType)
  MorphismProperty.IsLocalAtTarget.inf _ _

/-- Separatedness together with local quasi-finiteness is stable under base change. -/
theorem isSeparated_inf_locallyQuasiFinite_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u}) :=
  .inf

/-- The property of Stacks 02W8 is stable under base change. -/
theorem isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) :=
  have := isSeparated_inf_locallyQuasiFinite_isStableUnderBaseChange.{u}
  .inf

/-- Separated locally quasi-finite morphisms satisfy fppf descent: if the base change of `g`
along a surjective flat morphism of finite presentation is separated and locally quasi-finite,
then so is `g`.

This is the conjunction of the separated case of Stacks 02KU and the locally quasi-finite case
of Stacks 02VI, both of which this library proves for the fpqc coverings, upgraded to the fppf
coverings. -/
theorem isSeparated_inf_locallyQuasiFinite_descendsAlong_fppf :
    MorphismProperty.DescendsAlong
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have := isSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have := isSeparated_inf_locallyQuasiFinite_isZariskiLocalAtTarget.{u}
  have : MorphismProperty.DescendsAlong
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := MorphismProperty.DescendsAlong.inf
  descendsAlong_fppf_of_descendsAlong_fpqc _

/-- The property of Stacks 02W8 — separated, locally quasi-finite and locally of finite type —
satisfies fppf descent. -/
theorem isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_descendsAlong_fppf :
    MorphismProperty.DescendsAlong
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have := isSeparated_inf_locallyQuasiFinite_descendsAlong_fppf.{u}
  have : IsZariskiLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FiniteType)
  have : MorphismProperty.DescendsAlong (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    descendsAlong_fppf_of_descendsAlong_fpqc _
  MorphismProperty.DescendsAlong.inf

/-- The property of Stacks 02W8 together with quasi-compactness — separated and quasi-finite —
satisfies fppf descent. -/
theorem isSeparated_inf_quasiFinite_descendsAlong_fppf :
    MorphismProperty.DescendsAlong
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact :
        MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have := isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  have : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  have : MorphismProperty.DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    descendsAlong_fppf_of_descendsAlong_fpqc _
  MorphismProperty.DescendsAlong.inf

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The atlas clause at the property of Stacks 02W8 -/

/-- **Stacks 03I2 for the atlas clause of the algebraic-space property**, from effective descent
at the property of Stacks 02W8. Assume effective descent along surjective étale morphisms of the
big fppf site of `S` for the separated, locally quasi-finite morphisms which are locally of
finite type. Let `f : X ⟶ Y` be a morphism of presheaves with `X` and `Y` sheaves, and let `g`
be a surjective étale chart of `Y` along which the base change of `f` is a separated, locally
quasi-finite, locally of finite type, surjective and étale morphism of schemes. Then `f` is
representable, surjective and étale.

This is `AlgebraicGeometry.Space.presheaf_surjective_and_etale_of_surjectiveEtaleChart` with the
descent hypothesis taken at the property which Stacks 02W8 actually descends; the extra
locally-of-finite-type clause costs nothing where the hypothesis is used, since the base change
of the chart of Stacks 0265 along a chart of its target is the relation of an étale equivalence
relation, which is étale and hence locally of finite type. -/
theorem presheaf_surjective_and_etale_of_locallyOfFiniteType_chart
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {f : X ⟶ Y}
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hV : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g))
    (hVs : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g))
    (hVe : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  have _hsurj := surjective_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  have _hetale := etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  have _hbc :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange.{u}
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _hrie : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  ⟨presheaf_of_surjectiveEtaleChart_of_descent hdesc hX hYs hs he hV hVs,
    presheaf_of_surjectiveEtaleChart_of_descent hdesc hX hYs hs he hV hVe⟩

/-! ### Refining the covering -/

/-- **Descent, Lemma 35.36.2 in the shape of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`**, which is Tag 02W3.
Effective descent along the surjective étale morphisms of the big fppf site of `S` may be
verified after refining the covering: if every surjective étale `q : c ⟶ a` of the site carries a
morphism `p : c' ⟶ c` such that `p ≫ q` is again surjective étale and lies in a class `T` for
which the defining condition
of `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` is known, then that
condition holds for every surjective étale morphism of the site.

The point is that the conclusion of the defining condition does not mention the covering: it is
a statement about the base change of `f` along `h : yoneda.obj a ⟶ Y` alone. The datum over the
refinement is the base change of the datum over the original covering, and
`CategoryTheory.MorphismProperty.relative` is stable under base change unconditionally, so no
hypothesis on `P` is needed.

In the source this is used to replace an arbitrary fppf covering by a single faithfully flat
morphism of affine schemes. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_refinement
    {P : MorphismProperty Scheme.{u}}
    (T : ∀ {a c : BigFppfOver B S hS}, (c ⟶ a) → Prop)
    (hT : ∀ ⦃a c : BigFppfOver B S hS⦄ (q : c ⟶ a),
      Surjective ((BigFppfOver.toScheme B S hS).map q) →
      Etale ((BigFppfOver.toScheme B S hS).map q) →
      ∃ (c' : BigFppfOver B S hS) (p : c' ⟶ c),
        Surjective ((BigFppfOver.toScheme B S hS).map (p ≫ q)) ∧
          Etale ((BigFppfOver.toScheme B S hS).map (p ≫ q)) ∧ T (p ≫ q))
    (hdesc : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a), T q →
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h)) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  have hstable := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P.inverseImage (BigFppfOver.toScheme B S hS))
  intro X Y f hX hY a c h q _ _ A m r sq hr
  obtain ⟨c', p, hps, hpe, hpT⟩ := hT q ‹_› ‹_›
  have hbc : IsPullback (pullback.fst r (yoneda.map p)) (pullback.snd r (yoneda.map p)) r
      (yoneda.map p) := IsPullback.of_hasPullback _ _
  have hsq : IsPullback (pullback.fst r (yoneda.map p) ≫ m) (pullback.snd r (yoneda.map p)) f
      (yoneda.map (p ≫ q) ≫ h) := by
    have := hbc.paste_horiz sq
    simpa [Functor.map_comp] using this
  exact hdesc f hX hY h (p ≫ q) hpT hps hpe _ _ hsq
    (MorphismProperty.of_isPullback hbc hr)

/-! ### Glueing the descended pieces -/

/-- **Descent, Lemma 35.35.13 in the shape of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`**, which is Tag 0AP4: the
glueing step of Stacks 02W8. Effective descent along the surjective étale morphisms of the big
fppf site of `S` follows from producing, for each descent datum, a Zariski covering of the
descended sheaf by
representable open subfunctors, indexed by a type smaller than the cofinality of the site's
cutoff.

Nothing beyond that covering is needed: the fibre product `X ×[Y] yoneda.obj a` whose
representability is at stake is a sheaf, by
`AlgebraicGeometry.BigFppfOver.isSheaf_pullback_yoneda_obj`, so the covering makes it
representable by `AlgebraicGeometry.isRepresentable_of_zariskiCover_of_lt_cof`; and the
property `P` of
the descended morphism is then recovered from the datum by fppf descent, through
`AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart_of_descendsAlong`. In particular the
pieces of the covering are *not* required to carry `P`, which matters because the covering of
Stacks 02W8 is a covering of the *source*, and separatedness is not Zariski local there.

This reduces Stacks 02W8 to its second step: attaching to a quasi-compact open of the chart an
open subfunctor of the descended sheaf. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          ∃ (ι : Type u) (_ : Nonempty ι), Cardinal.mk ι < B.cutoff.ord.cof ∧
            ∃ (W : ι → BigFppfOver B S hS) (k : ∀ i, yoneda.obj (W i) ⟶ pullback f h),
              (∀ i, IsOpenImmersion B S hS (k i)) ∧
                Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k)) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  obtain ⟨ι, hne, hι, W, k, hk, hksurj⟩ := H f hX hY h q hqs hqe m r sq hr
  have hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback f h) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY
  have hrep : (pullback f h).IsRepresentable :=
    isRepresentable_of_zariskiCover_of_lt_cof B S hS hF hι W k hk hksurj
  set e := (pullback f h).reprW with he
  set p := yoneda.preimage (e.hom ≫ pullback.snd f h) with hp
  have hmap : yoneda.map p = e.hom ≫ pullback.snd f h := by rw [hp, Functor.map_preimage]
  have hfac : pullback.snd f h = e.inv ≫ yoneda.map p := by
    rw [hmap, Iso.inv_hom_id_assoc]
  have hrep' : yoneda.relativelyRepresentable (pullback.snd f h) := by
    rw [hfac]
    exact MorphismProperty.comp_mem _ _ _ (Functor.relativelyRepresentable.of_isIso _ _)
      (Functor.relativelyRepresentable.map yoneda p)
  have hqs' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs
  have hqe' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqe
  exact presheaf_of_surjectiveEtaleChart_of_descendsAlong hrep' hqs' hqe'
    (sq.of_right' (IsPullback.of_hasPullback f h)) hr

/-! ### The quasi-compact case of Stacks 02W8 -/

/-- **Stacks 02W8 for separated quasi-finite morphisms**, reduced to the two geometric inputs of
its proof which this library does not have.

Assume that every separated, quasi-compact, locally quasi-finite morphism of schemes which is
locally of finite type is quasi-affine — this is Stacks 02LR, a form of Zariski's main theorem —
and that quasi-affine morphisms descend effectively along the surjective étale morphisms of the
big fppf site of `S` — this is Stacks 0247 in the shape of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`. Then separated quasi-finite
morphisms descend effectively along the surjective étale morphisms of the site.

Stacks 02W8 itself drops the quasi-compactness: the source obtains it by covering the source of
the descent datum by quasi-compact opens stable under the datum, which needs the universal
openness of Stacks 01UA, and glues the pieces descended here. The glueing is available, as
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover`; the covering
by stable quasi-compact opens is not. See the implementation notes. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite
    (h02LR : (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓
        @LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ≤
      @_root_.AlgebraicGeometry.IsQuasiAffineHom)
    (h0247 : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓
        @LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
  have := isSeparated_inf_quasiFinite_descendsAlong_fppf.{u}
  have _hbc : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓
        @LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    have := isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange.{u}
    .inf
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓
        @LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  isEffectiveDescentAlongSurjectiveEtale_of_le h0247 h02LR

end Space

end AlgebraicGeometry

end
