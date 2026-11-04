module

public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpenFinitelyManyComponents
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.NormalStrictHenselization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendUnramifiedCodimensionOne
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two facts about the boundary of a dense open with regular complement

* `AlgebraicGeometry.exists_primeDivisor_genericPoint_eq`: a point whose local ring is
  one-dimensional is the generic point of a prime divisor.
* `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_of_isRegularLocalRing`: restriction of
  finite étale covers from a locally Noetherian scheme to a dense open whose complement has
  regular local rings is fully faithful, the punctured spectrum of a strict henselization of a
  regular local ring of positive dimension being connected ([Stacks, Tag 0BQG]).

Both are used in the proof of [Stacks, Tag 0EYJ].

## References

* [Stacks Project, Tag 0BQG](https://stacks.math.columbia.edu/tag/0BQG)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A point whose local ring is one-dimensional is the generic point of a prime divisor. -/
lemma exists_primeDivisor_genericPoint_eq {X : Scheme.{u}} (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) = 1) :
    ∃ Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor X,
      Z.genericPoint = x := by
  have hco : Order.coheight x = 1 := by
    rw [ringKrullDim_stalk_eq_coheight] at hx
    exact_mod_cast hx
  let Z' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  exact ⟨⟨Z'.idealSheaf, Z'.integral, Z'.codimension_one⟩,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco⟩

/-- **Restriction to a dense open with regular complement is fully faithful.** If `U` is dense in
a locally Noetherian scheme `X` and the local rings outside `U` are regular, then restriction of
finite étale covers from `X` to `U` is fully faithful. -/
@[sga "7 II 2.3.1" "partial"]
lemma fullyFaithful_finiteEtaleBaseChange_of_isRegularLocalRing {X : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens) (hdense : Dense (U : Set X))
    (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x)) :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := by
  have hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite := by
    intro V hV
    have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
    have : IsNoetherian V.toScheme := ⟨⟩
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := V.toScheme)
  refine fullyFaithful_finiteEtaleBaseChange_of_finite_irreducibleComponents _ _ hfinite hdense ?_
  intro p hp
  have := hreg p hp
  have : IsDomain (X.presheaf.stalk p) := IsRegularLocalRing.isDomain _
  have : IsIntegrallyClosed (X.presheaf.stalk p) := isIntegrallyClosed_of_isRegularLocalRing _
  refine isConnectedPuncturedStrictHenselization_of_isIntegrallyClosed _ fun hfield ↦ hp ?_
  exact scheme_genericPoints_mem_dense_open X U.2 hdense
    ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints X p).mp
      (ringKrullDim_eq_zero_of_isField hfield))

end AlgebraicGeometry

end
