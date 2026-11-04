module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedRelationSystem

/-!
# The relation `R₀ = U₀ ×_{X₀} U₀` of an étale chart, with its two projections as étale
morphisms of the site

The second step of the proof of Stacks 07SI chooses an affine étale chart `U₀ ⟶ X₀` of the
chosen stage of a limit situation and forms its relation `R₀ = U₀ ×_{X₀} U₀`.  Three things are
wanted of `R₀` at once: it must be *represented* by an object of the site, so that the chart
system machinery of Stacks 03WF applies to it; the representing object must be *affine*, so that
the resulting system `Rᵢ = R₀ ×_{X₀} Xᵢ` is a system of affine schemes; and its two projections
`t, s : R₀ ⟶ U₀` must be *étale*, being base changes of the étale chart along itself.

The library had the first and third of these for a chart with no affineness
(`AlgebraicGeometry.Space.exists_kernelPair_of_etale_atlas`, together with the base-change
clause of the étale morphism property), and the first and second for an affine chart with no
étaleness (`AlgebraicGeometry.Space.exists_affine_selfPullback_of_isAbsolutelySeparated`), but
not all three together.  This file puts them together, which costs only the observation that the
projection returned as a morphism of presheaves by the second is `yoneda` of a morphism of the
site, both of its source and its target being representable.

## Main results

* `AlgebraicGeometry.Space.exists_etale_kernelPair`: **an étale chart of a presheaf has a
  represented kernel pair whose two projections are étale morphisms of schemes.**
* `AlgebraicGeometry.Space.exists_affine_etale_selfPullback_of_isAbsolutelySeparated`: **the same
  with the representing object affine**, for an étale chart from an affine object of the site
  into a presheaf whose absolute diagonal is a closed immersion.
* `exists_affine_etale_relationChart_of_isAbsolutelySeparated`, in the namespace
  `AlgebraicGeometry.Space.LimitSituation`: that statement at the chosen stage of a limit
  situation, which is the relation `R₀` of the proof of Stacks 07SI together with its two étale
  projections.

## Implementation notes

*Which hypothesis makes which conclusion.*  Representability and étaleness of the two
projections come from the étaleness of the chart alone; affineness of the representing object
comes from separatedness of the target alone.  The two are therefore separated into
`AlgebraicGeometry.Space.exists_etale_kernelPair` and
`.exists_affine_etale_selfPullback_of_isAbsolutelySeparated`, and neither asks that the target be
an algebraic space: the étale morphism property of Stacks 03WG carries its own representability,
so `AlgebraicGeometry.IsAlgebraicSpace.diagonal_representable` is not needed.

*Both projections as morphisms of the site.*  `AlgebraicGeometry.Space.IsAffineHom` produces the
base change of an affine morphism with one leg a morphism of the site and the other a morphism of
presheaves, so `AlgebraicGeometry.Space.exists_affine_selfPullback_of_isAbsolutelySeparated`
returns the first projection as a morphism of presheaves.  Here it is carried back into the site
by `CategoryTheory.Yoneda.fullyFaithful`, giving a square `IsPullback (yoneda.map t)
(yoneda.map s) f f` symmetric in the two projections.  That is also the form the étale morphism
property wants, its base-change clause being stated for a leg of the shape `yoneda.map`.

*How the relation system and its limit are obtained from this.*  Nothing further is needed:
`AlgebraicGeometry.Space.LimitSituation.chartStagesDiagram` applied to `R₀` and the composite
`yoneda.map t ≫ f₀` is the system `Rᵢ`, its members are affine by
`.isAffine_chartStagesDiagram_obj`, and `.chartStagesCone` with `.isLimit_chartStagesCone` is a
limiting cone of schemes over it — all three for an arbitrary affine scheme-valued point of the
chosen stage, hence for `R₀`.  The square below is exactly the hypothesis `hpb` of
`isSectionsColimit_of_equalizerPresentation_of_relationChart` in that same namespace, read at
`τ := yoneda.map t`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **An étale chart has a represented kernel pair with étale projections.**  Let
`p : yoneda.obj W ⟶ X` be a morphism from a representable presheaf on the big fppf site of `S`
which is étale, that is, representable with étale represented base changes.  Then `W ×_X W` is
represented by an object `T` of the site, and the two projections `t, s : T ⟶ W` are étale
morphisms of schemes.

Representability is `AlgebraicGeometry.Space.exists_kernelPair_of_etale_atlas`; each projection
is then a represented base change of `p` along the other, so étale by the defining clause of the
étale morphism property. -/
theorem exists_etale_kernelPair {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : BigFppfOver B S hS} (p : yoneda.obj W ⟶ X)
    (hp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p) :
    ∃ (T : BigFppfOver B S hS) (t s : T ⟶ W),
      IsPullback (yoneda.map t) (yoneda.map s) p p ∧
      Etale ((BigFppfOver.toScheme B S hS).map t) ∧
      Etale ((BigFppfOver.toScheme B S hS).map s) := by
  obtain ⟨T, t, s, hpb⟩ := exists_kernelPair_of_etale_atlas B S hS p hp
  exact ⟨T, t, s, hpb, hp.property p (yoneda.map s) t hpb.flip,
    hp.property p (yoneda.map t) s hpb⟩

/-- **The self fibre product of an affine étale chart of a separated algebraic space is affine,
and its two projections are étale.**  Let `Y` be a presheaf on the big fppf site of `S` whose
absolute diagonal is a closed immersion — a separated algebraic space in the sense of Stacks
03BS, part (1) — and let `f : V ⟶ Y` be an étale morphism from an affine object of the site.
Then `V ×_Y V` is represented by an affine object `R` of the site, and both projections
`t, s : R ⟶ V` are étale morphisms of schemes.

This is `AlgebraicGeometry.Space.exists_affine_selfPullback_of_isAbsolutelySeparated`, whose
affineness of `R` comes from Stacks 08GB, part (4), with its first projection carried back into
the site through the full faithfulness of Yoneda and both projections recognised as represented
base changes of `f` along one another.  In the proof of Stacks 07SI it is the relation
`R₀ = U₀ ×_{X₀} U₀` of an affine étale chart of a separated stage. -/
theorem exists_affine_etale_selfPullback_of_isAbsolutelySeparated
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hsep : IsAbsolutelySeparated B S hS hZ Y)
    (V : BigAffineFppf B S hS)
    (f : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    ∃ (R : BigAffineFppf B S hS)
      (t s : (BigAffineFppf.inclusion B S hS).obj R ⟶
        (BigAffineFppf.inclusion B S hS).obj V),
      IsPullback (yoneda.map t) (yoneda.map s) f f ∧
      Etale ((BigFppfOver.toScheme B S hS).map t) ∧
      Etale ((BigFppfOver.toScheme B S hS).map s) := by
  obtain ⟨R, t, s, hpb⟩ :=
    exists_affine_selfPullback_of_isAbsolutelySeparated B S hS hZ hsep V f
  have hpb' : IsPullback (yoneda.map (yoneda.preimage t)) (yoneda.map s) f f := by
    rw [yoneda.map_preimage]
    exact hpb
  exact ⟨R, yoneda.preimage t, s, hpb',
    hf.property f (yoneda.map s) (yoneda.preimage t) hpb'.flip,
    hf.property f (yoneda.map (yoneda.preimage t)) s hpb'⟩

namespace LimitSituation

variable {B S hS hZ} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : LimitSituation B S hS hZ X)

/-- **The relation `R₀ = U₀ ×_{X₀} U₀` of an affine étale chart of a separated stage is affine,
and its two projections are étale.**  This is
`AlgebraicGeometry.Space.exists_affine_etale_selfPullback_of_isAbsolutelySeparated` at the chosen
stage of a limit situation: an affine object `R₀` of the site representing `U₀ ×_{X₀} U₀`,
together with its two projections `t` and `s` to `U₀` as étale morphisms of the site. -/
theorem exists_affine_etale_relationChart_of_isAbsolutelySeparated
    (hsep : IsAbsolutelySeparated B S hS hZ (A.system.obj (op A.base)))
    (U₀ : BigAffineFppf B S hS)
    (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base))
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀)) :
    ∃ (R₀ : BigAffineFppf B S hS)
      (t s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶
        (BigAffineFppf.inclusion B S hS).obj U₀),
      IsPullback (yoneda.map t) (yoneda.map s) f₀ f₀ ∧
      Etale ((BigFppfOver.toScheme B S hS).map t) ∧
      Etale ((BigFppfOver.toScheme B S hS).map s) :=
  exists_affine_etale_selfPullback_of_isAbsolutelySeparated B S hS hZ hsep U₀ f₀ hf₀

end LimitSituation

end AlgebraicGeometry.Space

end
