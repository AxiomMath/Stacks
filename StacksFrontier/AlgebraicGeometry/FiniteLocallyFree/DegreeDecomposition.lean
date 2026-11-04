module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat

/-!
# The decomposition of the base of a finite locally free morphism by degree

The rank function of a finite flat morphism of finite presentation is locally constant, so its
fibres are open and closed. They decompose the target into pieces over which the morphism is
finite locally free of one constant degree.

## Main definitions

* `Stacks.Morphisms.rankStratum`: the open subscheme of the target on which the rank function of
  a finite flat morphism of finite presentation takes a given value.

## Main results

* `Stacks.Morphisms.isClosed_rankStratum`: each stratum is closed as well as open.
* `Stacks.Morphisms.rankStratum_disjoint`: distinct strata are disjoint.
* `Stacks.Morphisms.iSup_rankStratum`: the strata cover the target.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_rankStratum`: over the stratum of value `d` the
  morphism is finite locally free of rank `d`.
* `Stacks.Morphisms.exists_isClosed_isFiniteLocallyFreeOfRank_decomposition`: the decomposition
  of the base of a finite locally free morphism by degree.

## Implementation notes

The strata are indexed by all natural numbers, with the empty open subscheme allowed as a
stratum, so the decomposition is a function of the degree rather than a finite indexed family.

Local finite presentation is a hypothesis of `Stacks.Morphisms.rankStratum` because it makes the
rank function locally constant, hence the stratum open; a finite locally free morphism has it.

## References

* [Stacks Project, Tag 04MH](https://stacks.math.columbia.edu/tag/04MH)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Morphisms

/-- The rank function of a finite flat morphism is compatible with restriction over an open of
the target. -/
theorem finrank_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Flat f]
    (U : S.Opens) (y : U) :
    (f ∣_ U).finrank y = f.finrank (U.ι.base y) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict f U).flip y

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

/-- The locus in the target where the rank function of a finite flat morphism of finite
presentation takes the value `d`. It is open because the rank function is locally constant. -/
def rankStratum (d : ℕ) : S.Opens :=
  ⟨{s : S | f.finrank s = d}, (Scheme.Hom.isLocallyConstant_finrank f).isOpen_fiber d⟩

/-- A point of the target lies in `rankStratum f d` exactly when the rank of `f` there is `d`. -/
@[simp]
theorem mem_rankStratum {d : ℕ} {s : S} : s ∈ rankStratum f d ↔ f.finrank s = d := Iff.rfl

/-- Each stratum of the rank function is closed as well as open. -/
theorem isClosed_rankStratum (d : ℕ) : IsClosed (rankStratum f d : Set S) :=
  (Scheme.Hom.isLocallyConstant_finrank f).isClosed_fiber d

/-- Strata of the rank function for distinct values are disjoint. -/
theorem rankStratum_disjoint {d e : ℕ} (h : d ≠ e) :
    Disjoint (rankStratum f d) (rankStratum f e) :=
  Opens.coe_disjoint.mp <| Set.disjoint_left.mpr fun _ hd he =>
    h <| ((mem_rankStratum f).mp hd).symm.trans ((mem_rankStratum f).mp he)

/-- The strata of the rank function cover the target. -/
theorem iSup_rankStratum : (⨆ d : ℕ, rankStratum f d) = ⊤ :=
  eq_top_iff.mpr fun s _ => Opens.mem_iSup.mpr ⟨f.finrank s, rfl⟩

/-- Over the stratum where the rank function takes the value `d`, a finite flat morphism of
finite presentation is finite locally free of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_rankStratum (d : ℕ) :
    IsFiniteLocallyFreeOfRank (f ∣_ rankStratum f d) d :=
  (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ d).mpr fun y =>
    (finrank_morphismRestrict f _ y).trans ((mem_rankStratum f).mp y.2)

/-- The base of a finite locally free morphism decomposes as a disjoint union of open and closed
subschemes indexed by the degree, over the `d`-th of which the morphism is finite locally free of
degree `d`. -/
@[stacks 04MH]
theorem exists_isClosed_isFiniteLocallyFreeOfRank_decomposition {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFiniteLocallyFree f] :
    ∃ Z : ℕ → S.Opens, (∀ d, IsClosed (Z d : Set S)) ∧
      (∀ d e, d ≠ e → Disjoint (Z d) (Z e)) ∧ (⨆ d : ℕ, Z d) = ⊤ ∧
      ∀ d, IsFiniteLocallyFreeOfRank (f ∣_ Z d) d := by
  obtain ⟨_, _, _⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp inferInstance
  exact ⟨rankStratum f, isClosed_rankStratum f, fun _ _ h => rankStratum_disjoint f h,
    iSup_rankStratum f, isFiniteLocallyFreeOfRank_rankStratum f⟩

end Stacks.Morphisms

end
