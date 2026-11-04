module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Components
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleRestrict
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleProperFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.AffineBase

/-!
# A projective morphism carries an invertible module ample on every fibre

Let `f : V ⟶ Y` be a projective morphism. Then there is an invertible `𝒪_V`-module `𝓗` whose
pullback to every fibre `V_y = V ×_Y Spec K` over a field-valued point `y : Spec K ⟶ Y`, and to
every closed subscheme of such a fibre, is ample.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `Scheme.Modules.isAmple_pullback_of_isRelativelyAmple_of_isPullback`: for a cartesian square
  over an *affine* scheme `S'`, the pullback of an `f`-ample invertible module is ample.
* `IsProjective.exists_isAmple_pullback_of_isPullback`: **a projective morphism has an
  invertible module whose pullback to every field-valued fibre is ample**, together with its
  pullback to every closed subscheme of that fibre.

## The argument

A projective morphism is quasi-projective ([Stacks, Tag 07RL],
`AlgebraicGeometry.IsProjective.isQuasiProjective`), so it carries an `f`-ample invertible module
`𝓗` ([Stacks, Tag 01VW]). Relative ampleness is stable under base change ([Stacks, Tag 0893],
`Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback`), and over an affine base it is
ampleness ([Stacks, Tag 01VT], `AlgebraicGeometry.Scheme.Modules.isAmple_of_isRelativelyAmple`);
`Spec K` is affine. Restriction to a closed subscheme preserves ampleness
(`AlgebraicGeometry.Scheme.Modules.isAmple_modulePullback_of_isClosedImmersion`, a closed immersion
being affine). No hypothesis on `Y` is used.

## Implementation notes

`Stacks.AmpleLocallyClosed.pullbackModule p`, `RingedSpaceModuleAdjunction.modulePullback
p.toLRSHom.toShHom` and `AlgebraicGeometry.Scheme.Modules.pullback p` are the same functor by
`rfl`, and `Stacks.Ample.IsInvertibleModule` is an `abbrev` for the invertibility class
`AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2`, so the lemmas above
apply with no transport. The invertibility of the pullbacks is the instance
`Stacks.AmpleRestrict.isInvertible_pullback` ([Stacks, Tag 0B8L]).

## References

* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The pullback of a relatively ample module to a cartesian square over an affine scheme is
ample.** For a cartesian square with sides `q : Z ⟶ V`, `g : Z ⟶ S'`, `f : V ⟶ Y` and
`y : S' ⟶ Y`, with `S'` affine, if `𝓗` is ample relative to `f` then `q^* 𝓗` is ample. -/
theorem Scheme.Modules.isAmple_pullback_of_isRelativelyAmple_of_isPullback
    {V Y Z S' : Scheme.{u}} {f : V ⟶ Y} {y : S' ⟶ Y} {q : Z ⟶ V} {g : Z ⟶ S'} [IsAffine S']
    (hsq : IsPullback q g f y) (H : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H]
    (hH : Stacks.RelativeAmple.IsRelativelyAmple f H) :
    Scheme.Modules.IsAmple Z ((Scheme.Modules.pullback q).obj H) :=
  Scheme.Modules.isAmple_of_isRelativelyAmple g _
    (Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hsq H hH)

/-- **A projective morphism carries an invertible module that is ample on every fibre and on
every closed subscheme of a fibre.** For `f : V ⟶ Y` projective there is an invertible
`𝓗` on `V` such that for every field `K`, every point `y : Spec K ⟶ Y` and every cartesian square
`Z = V ×_Y Spec K` with projection `q : Z ⟶ V`, the pullback `q^* 𝓗` is invertible and ample on
`Z`, and so is its pullback along every closed immersion `j : W ⟶ Z`. -/
theorem IsProjective.exists_isAmple_pullback_of_isPullback {V Y : Scheme.{u}} {f : V ⟶ Y}
    (hf : IsProjective f) :
    ∃ (H : V.Modules) (hH : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H),
      letI := hH
      ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ Y) {Z : Scheme.{u}} (q : Z ⟶ V)
        (g : Z ⟶ Spec (.of K)), IsPullback q g f y →
        SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
            ((Scheme.Modules.pullback q).obj H) ∧
          Scheme.Modules.IsAmple Z ((Scheme.Modules.pullback q).obj H) ∧
          ∀ {W : Scheme.{u}} (j : W ⟶ Z) [IsClosedImmersion j],
            Scheme.Modules.IsAmple W
              ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback q).obj H)) := by
  obtain ⟨H, hH, hamp⟩ := hf.isQuasiProjective.exists_isRelativelyAmple
  refine ⟨H, hH, fun K _ y Z q g hsq => ?_⟩
  have hZ : Scheme.Modules.IsAmple Z ((Scheme.Modules.pullback q).obj H) :=
    Scheme.Modules.isAmple_pullback_of_isRelativelyAmple_of_isPullback hsq H hamp
  exact ⟨inferInstance, hZ, fun j _ =>
    Scheme.Modules.isAmple_modulePullback_of_isClosedImmersion j _ hZ⟩

end AlgebraicGeometry

end
