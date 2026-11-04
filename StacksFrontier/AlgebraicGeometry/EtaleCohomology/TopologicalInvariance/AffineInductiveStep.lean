module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineSurjectiveCase

/-!
# The inductive step of the second proof of Stacks 04DZ, reduced to one descent

The second proof of Stacks Project, Tag 04DZ proves the affine case of the correspondence of
Stacks Project, Tag 04E0 by induction on a bound for the degrees of the fibres. This file
assembles everything in that induction except the descent itself, and so reduces
`Stacks.Etale.EssSurjAffineEtalePullback` to the single statement
`Stacks.Etale.EtaleDescentAlongAffineEtaleSurjection`: that the scheme over `W` produced by the
split *descends* along the étale surjection `W ⟶ Y`.

The chain is this. The affine case for a bound follows from its surjective case for the same
bound, by restricting the target to the open image of `U`
(`Stacks.Etale.essSurjAffineEtalePullbackBounded_of_surjectiveBounded`). In the surjective case
the dominating scheme `W` of `Stacks.Etale.exists_isAffine_etale_over_of_boundsFiberDegrees_succ`
is surjective over `Y`, so `W ⟶ Y` is an étale — in particular flat, surjective and locally of
finite presentation — covering of `Y` by an affine scheme, and the split produces an affine
scheme `V''` étale over `W` whose base change to `X ×_Y W` is `U ×_X (X ×_Y W)`. Descending
`V''` along that covering gives the scheme over `Y` whose base change is `U`, which closes the
induction: the base case `n = 1` is `Stacks.Etale.essSurjAffineEtalePullbackBounded_one` and the
passage from the bounded statements to the unbounded one is
`Stacks.Etale.essSurjAffineEtalePullback_of_forall_bounded`.

## Main definitions

* `Stacks.Etale.EtaleDescentAlongAffineEtaleSurjection` — the descent step: granted the data the
  split produces, `U` is the base change along `f` of a scheme étale over `Y`.

## Main results

* `Stacks.Etale.essSurjEtalePullbackSurjectiveBounded_succ_of_bounded` — the inductive step in
  its surjective form: the affine case for the bound `n` and the descent step give the surjective
  case for the bound `n + 1`.
* `Stacks.Etale.essSurjAffineEtalePullbackBounded_succ_of_etaleDescent` — the inductive step of
  the source's induction.
* `Stacks.Etale.essSurjAffineEtalePullback_of_etaleDescent` — consequently
  `Stacks.Etale.EssSurjAffineEtalePullback` follows from the descent step alone.

The descent step itself is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineEtaleDescentStep`, so
`Stacks.Etale.essSurjAffineEtalePullback_of_etaleDescent` applied to it is unconditional.

## Implementation notes

Surjectivity of `W ⟶ Y` is read off the surjection `X ×_Y W ⟶ U`: a point of `Y` comes from a
point of `X` because `f` is surjective, from a point of `U` because `p` is surjective in the
surjective case, and from a point of `X ×_Y W` because the dominating morphism is surjective;
the projection of that point to `W` then lies over the given point of `Y`.

The descent step is stated with the schemes and morphisms of the split as explicit arguments,
rather than as effectivity of an abstract descent datum, because that is the form the split
delivers: the gluing isomorphism over `W ×_Y W` and its cocycle condition are not among the
data, and have themselves to be produced from the full faithfulness of base change along `f`,
which is what the source's proof does. The gluing *morphism* is produced by
`Stacks.Etale.exists_gluing_hom_of_isoBaseChange`; what the descent step still asks for beyond
it is that this morphism be invertible, that it satisfy the cocycle condition, that the
resulting descent datum be effective — which is Stacks Project, Tag 0245, available here as
`AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom_of_locallyOfFinitePresentation`,
since `V ⟶ W` is an affine morphism and `W ⟶ Y` is étale and surjective — and that the scheme
so obtained over `Y` have base change `U` rather than merely base change `V` over `W`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-- **The descent step of the second proof of Stacks Project, Tag 04DZ.** Let `f : X ⟶ Y` be a
universal homeomorphism, let `w : W ⟶ Y` be étale and surjective with `W` affine, let `p : U ⟶ X`
be étale with `U` affine, and let `V` be an affine scheme étale over `W` whose base change along
`X ×_Y W ⟶ W` is identified with `U ×_X (X ×_Y W)` over `X ×_Y W`. Then `U` is, over `X`, the
base change along `f` of a scheme étale over `Y`.

This is the second half of the inductive step of the source's proof: the full faithfulness of
base change along the universal homeomorphism `X ×_Y (W ×_Y W) ⟶ W ×_Y W` turns the canonical
descent datum of `U ×_X (X ×_Y W)` relative to `X ×_Y W ⟶ X` into a descent datum for `V`
relative to `W ⟶ Y`, which is effective by effectivity of affine descent along an fpqc covering,
Stacks Project, Tag 0245. -/
def EtaleDescentAlongAffineEtaleSurjection : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), UniversalHomeomorphism f →
    ∀ (W : Scheme.{u}) (w : W ⟶ Y), Etale w → IsAffine W → Surjective w →
      ∀ (U : Scheme.{u}) (p : U ⟶ X), Etale p → IsAffine U →
        ∀ (V : Scheme.{u}) (q : V ⟶ W), Etale q → IsAffine V →
          ∀ e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w),
            e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w) →
              ∃ (V₀ : Scheme.{u}) (q₀ : V₀ ⟶ Y) (_ : Etale q₀) (e₀ : pullback q₀ f ≅ U),
                e₀.hom ≫ p = pullback.snd q₀ f

/-- **The inductive step, in its surjective form.** Granted the descent step and the affine case
of Stacks Project, Tag 04E0 for the bound `n`, the surjective case holds for the bound `n + 1`.

The split of `Stacks.Etale.exists_isAffine_etale_over_of_boundsFiberDegrees_succ` provides the
dominating affine scheme `W` étale over `Y` and the scheme over `W` to be descended; what the
surjectivity of `p` adds is that `W ⟶ Y` is surjective, hence a covering, which is the
hypothesis the descent step needs. -/
theorem essSurjEtalePullbackSurjectiveBounded_succ_of_bounded
    (hdesc : EtaleDescentAlongAffineEtaleSurjection.{u}) (n : ℕ)
    (hn : EssSurjAffineEtalePullbackBounded.{u} n) :
    EssSurjEtalePullbackSurjectiveBounded.{u} (n + 1) := by
  intro X Y f hf U p hp hU hpaff hpsurj hdeg
  have : Surjective f :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp hf).2.2
  obtain ⟨W, w, hw, hWaff, h, hhsurj, hh, V, q, hq, hVaff, e, he⟩ :=
    exists_isAffine_etale_over_of_boundsFiberDegrees_succ n hn f p hp hU hpaff hdeg
  have : Surjective (pullback.snd f w ≫ w) := by
    rw [← pullback.condition, ← hh, Category.assoc]
    infer_instance
  have hwsurj := Surjective.of_comp (pullback.snd f w) w
  exact hdesc f hf W w hw hWaff hwsurj U p hp hU V q hq hVaff e he

/-- **The inductive step of the induction of the second proof of Stacks Project, Tag 04DZ.**
Granted the descent step, the affine case of Stacks Project, Tag 04E0 for the bound `n` implies
it for the bound `n + 1`. -/
theorem essSurjAffineEtalePullbackBounded_succ_of_etaleDescent
    (hdesc : EtaleDescentAlongAffineEtaleSurjection.{u}) (n : ℕ)
    (hn : EssSurjAffineEtalePullbackBounded.{u} n) :
    EssSurjAffineEtalePullbackBounded.{u} (n + 1) :=
  essSurjAffineEtalePullbackBounded_of_surjectiveBounded (n + 1)
    (essSurjEtalePullbackSurjectiveBounded_succ_of_bounded hdesc n hn)

/-- **The affine case of Stacks Project, Tag 04E0 follows from the descent step alone.** Every
other part of the induction of the second proof of Stacks Project, Tag 04DZ is proved in this
library: the base case is `Stacks.Etale.essSurjAffineEtalePullbackBounded_one`, the domination by
an affine scheme étale over `Y` is `Stacks.Etale.exists_isAffine_etale_domination`, the splitting
off of the section and the drop in fibre degree are
`Stacks.Etale.exists_isAffine_etale_over_of_boundsFiberDegrees_succ`, the reduction to the
surjective case is `Stacks.Etale.essSurjAffineEtalePullbackBounded_of_surjectiveBounded`, and the
passage to the unbounded statement is
`Stacks.Etale.essSurjAffineEtalePullback_of_forall_bounded`. -/
theorem essSurjAffineEtalePullback_of_etaleDescent
    (hdesc : EtaleDescentAlongAffineEtaleSurjection.{u}) :
    EssSurjAffineEtalePullback.{u} :=
  essSurjAffineEtalePullback_of_inductiveStep fun n _ hn ↦
    essSurjAffineEtalePullbackBounded_succ_of_etaleDescent hdesc n hn

end Stacks.Etale

end

end
