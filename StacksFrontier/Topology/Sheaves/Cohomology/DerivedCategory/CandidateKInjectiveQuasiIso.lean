module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.KInjectiveTowerQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CandidateKInjectiveResolution
import StacksCore.Tactic.StacksAttribute

/-!
# When the candidate K-injective resolution of a complex of sheaves is a resolution

Let `(X, 𝒪_X)` be a ringed space, let `F` be a complex of `𝒪_X`-modules and let
`F ⟶ I = lim_n I_n` be the candidate K-injective resolution of Tag 071A. Write `ℋ^q = H^q(F)`
for the cohomology sheaves of `F`. If a set `ℬ` of opens of `X` covers every open of `X` and
there is a `d ∈ ℕ` with `H^p(U, ℋ^q) = 0` for every `U ∈ ℬ`, every `p > d` and every `q < 0`,
then that canonical map is a quasi-isomorphism.

## Main definitions

* `Stacks.KInjective.coverZeroHypercover`: the covering of an open of `X` by all the members of
  `ℬ` contained in it.

## Main results

* `Stacks.KInjective.quasiIso_canonicalMap`: the canonical map of Tag 071A into the candidate
  K-injective resolution is a quasi-isomorphism.

## Implementation notes

The ringed space enters only through its site of opens, so this is the specialisation of the
ringed-site form (Tag 070Q) to `C = Opens X` with the topology of Tag 00ZB. Three translations
are needed. The covering hypothesis, which Tag 070Q asks for as a
`CategoryTheory.PreZeroHypercover` whose generated sieve is a covering sieve, is supplied by
`coverZeroHypercover`, whose index type is the subtype of members of `ℬ` contained in the given
open; taking all of them rather than choosing some avoids every choice principle. The cohomology
sheaf, which Tag 070Q spells as the homology of the image of `F` in the derived category, is here
the homology `F.homology q` of the complex itself, the two being identified by
`CategoryTheory.DerivedCategory.homologyFunctorFactors`; so no derived category occurs in the
statement below, at any model. Finally `H^p(U, -)` is the `p`-th right derived functor of taking
sections over `U`, which asks only for additivity of that functor, rather than
`Stacks.Cohomology.moduleCohomology`, whose type carries sheafification hypotheses; the two are
the same term, and for the site of opens — a small site — those hypotheses hold outright, so they
are discharged inside the proof instead of being imposed on the statement.

## References

* [Stacks Project, Tag 071A](https://stacks.math.columbia.edu/tag/071A)
* [Stacks Project, Tag 071B](https://stacks.math.columbia.edu/tag/071B)
* [Stacks Project, Tag 070Q](https://stacks.math.columbia.edu/tag/070Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.KInjective

attribute [local instance] HasDerivedCategory.standard

/-- Taking sections of sheaves of modules over an open subset is an additive functor. -/
local instance evaluation_additive (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    (SheafOfModules.evaluation.{u} O (Opposite.op U)).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

variable {X : TopCat.{u}}

/-- The covering of an open `V` of a topological space by all the members of a set `B` of opens
which are contained in `V`. -/
def coverZeroHypercover (B : Set (Opens X)) (V : Opens X) : PreZeroHypercover.{u} V where
  I₀ := { U : Opens X // U ∈ B ∧ U ≤ V }
  X U := U.1
  f U := homOfLE U.2.2

/-- If every open of `X` is a union of members of `B`, then the members of `B` contained in an
open `V` cover `V`. -/
theorem coverZeroHypercover_sieve₀_mem (B : Set (Opens X))
    (hB : ∀ V : Opens X, ∃ 𝒰 : Set (Opens X), 𝒰 ⊆ B ∧ (V : Set X) = ⋃ U ∈ 𝒰, (U : Set X))
    (V : Opens X) :
    (coverZeroHypercover B V).sieve₀ ∈ Opens.grothendieckTopology (X : Type u) V := by
  intro x hx
  obtain ⟨𝒰, h𝒰, hunion⟩ := hB V
  have hmem : x ∈ ⋃ U ∈ 𝒰, (U : Set X) := by rw [← hunion]; exact hx
  obtain ⟨U, hU𝒰, hxU⟩ := Set.mem_iUnion₂.mp hmem
  have hsub : (U : Set X) ⊆ (V : Set X) := by
    rw [hunion]; exact Set.subset_biUnion_of_mem hU𝒰
  have hUV : U ≤ V := SetLike.coe_subset_coe.mp hsub
  exact ⟨U, homOfLE hUV, (coverZeroHypercover B V).sieve₀_f ⟨U, h𝒰 hU𝒰, hUV⟩, hxU⟩

/-- **Stacks 071B.** Let `F` be a complex of `𝒪_X`-modules on a ringed space, with candidate
K-injective resolution `F ⟶ lim_n I_n` as in Tag 071A, and write `ℋ^q = H^q(F)` for its
cohomology sheaves. If a set `B` of opens of `X` covers every open of `X` and `H^p(U, ℋ^q) = 0`
for every `U ∈ B`, every `p > d` and every `q < 0`, then that canonical map is a
quasi-isomorphism. -/
@[stacks 071B]
theorem quasiIso_canonicalMap (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : CochainComplex (SheafOfModules.{u} O) ℤ)
    (R : CandidateKInjectiveResolution O F) (B : Set (Opens X)) (d : ℕ)
    (hB : ∀ V : Opens X, ∃ 𝒰 : Set (Opens X), 𝒰 ⊆ B ∧ (V : Set X) = ⋃ U ∈ 𝒰, (U : Set X))
    (hvan : ∀ U ∈ B, ∀ p : ℕ, d < p → ∀ q : ℤ, q < 0 →
      IsZero (((SheafOfModules.evaluation.{u} O (Opposite.op U)).rightDerived p).obj
        (F.homology q))) :
    QuasiIso R.canonicalMap := by
  let _ : (Opens.grothendieckTopology (X : Type u)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  let _ : HasSheafify (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  have hmapg : ∀ n : ℕ, (Functor.ofOpSequence R.g).map (homOfLE (Nat.le_succ n)).op = R.g n :=
    Functor.ofOpSequence_map_homOfLE_succ R.g
  have hKinj : ∀ n : ℕ, ((Functor.ofOpSequence R.g).obj ⟨n⟩).IsKInjective := fun n => by
    have := R.strictlyGE_I n
    have : ∀ i : ℤ, Injective ((R.I n).X i) := R.injective_I n
    exact CochainComplex.isKInjective_of_injective (R.I n) (-(n : ℤ))
  exact Stacks.Cohomology.quasiIso_to_limit_of_truncGE_resolutions O F
    (Functor.ofOpSequence R.g) R.f R.quasiIso_f
    (fun n => by rw [hmapg n]; exact R.ladder n) hKinj
    (fun n i => by rw [hmapg n]; exact R.splitEpi_g n i)
    R.canonicalMap R.canonicalMap_comp_π B d
    (fun V => ⟨coverZeroHypercover B V, coverZeroHypercover_sieve₀_mem B hB V, fun i => i.2.1⟩)
    fun V hV p hp q hq => (hvan V hV p hp q hq).of_iso
      ((Functor.rightDerived (SheafOfModules.evaluation.{u} O (Opposite.op V)) p).mapIso
        ((DerivedCategory.homologyFunctorFactors _ q).app F))

end Stacks.KInjective

end
