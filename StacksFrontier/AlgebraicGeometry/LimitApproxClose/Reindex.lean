module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.SpecCone
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.Comp

/-!
# Restricting a limiting cone along a cofinal reindexing, and finite type on an open

Two utilities for the wiring of the one-affine-open step of Tag 07RN, and the composition rule
that chains the cofinalities the step needs.

The step reindexes the stages **twice** — once in step (i), onto the stages above the one at
which the overlap descends, and once again onto the stages at which the model of the overlap maps
by an open immersion into the spectrum of the fibre product — and then a third time onto the
pairs of a stage and a distinguished subalgebra.  Every one of those reindexings has to carry the
limiting cone along with it, and each is cofinal.  This file states that transport once.

## Main results

* `AlgebraicGeometry.isLimitWhiskerOfCofinal` is the transport: a limiting cone over a directed
  inverse system stays limiting after restriction along a monotone reindexing with cofinal
  image.  It is `AlgebraicGeometry.initial_dual_functor_of_cofinal` fed to
  `CategoryTheory.Functor.Initial.isLimitWhiskerEquiv`.
  Note that this is a *general* reindexing and not an equivalence, so finality is genuinely
  needed here — unlike the index bridge of `Stacks.StageSubalgebra.isLimitSpecDiagramCone`,
  where the reindexing is an equivalence and `CategoryTheory.Limits.IsLimit.whiskerEquivalence`
  asks for nothing.

* `AlgebraicGeometry.exists_le_comp` chains two cofinalities, which is what lets the composite of
  the reindexings be fed to the transport in one step rather than two.

* `AlgebraicGeometry.locallyOfFiniteType_terminal_from_opens`: an open subscheme of a scheme of
  finite type over the terminal scheme is again of finite type over it.  This is what makes the
  *models of the overlap* finite-type schemes, which is what
  `AlgebraicGeometry.finiteType_localization_away_of_basicOpen_le` needs in order to produce the
  chart data of `AlgebraicGeometry.exists_isChartedSubalgebra_ge` at each stage, the overlap
  models being opens of the stages rather than stages themselves.

## Implementation notes

One scheme universe; the two index preorders are in it as well, as the structure recording the
conclusion of Tag 07RN requires of its index type.

The initiality instance is introduced by `have` immediately before the equivalence is applied:
it is not an instance globally, and `CategoryTheory.Functor.Initial.isLimitWhiskerEquiv` will not
fire without it.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Two cofinal monotone maps compose to a cofinal one. -/
lemma exists_le_comp {L M N : Type u} [Preorder L] [Preorder M] [Preorder N] (f : L →o M)
    (g : M →o N) (hf : ∀ m, ∃ l, m ≤ f l) (hg : ∀ n, ∃ m, n ≤ g m) :
    ∀ n, ∃ l, n ≤ (g.comp f) l := by
  intro n
  obtain ⟨m, hm⟩ := hg n
  obtain ⟨l, hl⟩ := hf m
  exact ⟨l, hm.trans (g.monotone hl)⟩

/-- **A limiting cone stays limiting after restriction along a cofinal reindexing.**  The
reindexing is a general monotone map with cofinal image, so finality is genuinely needed; it is
supplied by `AlgebraicGeometry.initial_dual_functor_of_cofinal`. -/
noncomputable def isLimitWhiskerOfCofinal {L M : Type u} [Preorder L] [Preorder M] [Nonempty L]
    [IsDirected L (· ≤ ·)] (γ : L →o M) (hγ : ∀ m, ∃ l, m ≤ γ l) {D : Mᵒᵈ ⥤ Scheme.{u}}
    {c : Cone D} (hc : IsLimit c) : IsLimit (c.whisker γ.monotone.dual.functor) :=
  have : (γ.monotone.dual.functor).Initial := initial_dual_functor_of_cofinal γ hγ
  (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc

/-- **An open subscheme of a scheme of finite type over the terminal scheme is of finite type
over it.**  The models of the overlap in the one-affine-open step of Tag 07RN are opens of the
stages, so this is what makes them finite-type schemes and hence what lets
`AlgebraicGeometry.finiteType_localization_away_of_basicOpen_le` apply at each stage. -/
lemma locallyOfFiniteType_terminal_from_opens {X : Scheme.{u}} (U : X.Opens)
    [LocallyOfFiniteType (terminal.from X)] :
    LocallyOfFiniteType (terminal.from (U : Scheme.{u})) := by
  rw [← terminal.comp_from U.ι]
  infer_instance

end AlgebraicGeometry
