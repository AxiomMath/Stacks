module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RankDecomposition
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank

/-!
# The rank decomposition of a finite locally free module on a scheme

Let `X` be a scheme and let `E` be a finite locally free `O_X`-module. The rank of `E` is a
locally constant `ℕ`-valued function on `X`, so for each `r` the locus `X_r ⊆ X` where it equals
`r` is open and closed; the `X_r` are pairwise disjoint, they cover `X`, and the restriction of
`E` to `X_r` is finite locally free of constant rank `r`. This is the decomposition

  `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …`

that Stacks 0ESW uses to define the Chern classes of a module whose rank is not constant.

## Main definitions

* `Stacks.Chow.moduleRank` — the locally constant rank of `E`.
* `Stacks.Chow.rankLocus` — the open and closed locus `X_r` where the rank of `E` is `r`.
* `Stacks.Chow.rankLociFamily` — the family of rank loci, reindexed in the universe of the
  scheme.

## Main results

* `Stacks.Chow.isClopen_rankLocus` — each rank locus is open and closed, being a fibre of a
  locally constant function.
* `Stacks.Chow.isClopenDecomposition_rankLociFamily` — the rank loci decompose `X` into open and
  closed subschemes, in the sense of `Stacks.Chow.IsClopenDecomposition`.
* `Stacks.Chow.fiberRank_eq_moduleRank` — the locally constant rank agrees with the pointwise
  fibre rank.
* `Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_rankLocus` — `E|_{X_r}` is finite locally free
  of constant rank `r`, so the constant-rank theory applies to it.
* `Stacks.Chow.pieceMap_id` — the restriction of the identity of `X` to a piece of a
  decomposition into open and closed subschemes is the identity of that piece.

## Implementation notes

### Reading the rank of a ringed space on a scheme

`Stacks.SheafOfModules.finiteLocallyFreeRank` and `Stacks.SheafOfModules.rankStratum` are stated
for a sheaf of modules on a ringed space whose structure stalks are all nonzero, which for a
scheme is `LocallyFreeRank.scheme_stalksNontrivial`. The ring sheaf they are stated over,
`LocallyFreeRank.toRingSheaf X.toTopCat X.sheaf`, is definitionally but not syntactically
`X.ringCatSheaf`, so instance search does not find the finite-local-freeness hypothesis for it;
both the sheaf and that hypothesis are therefore supplied by explicit application.

### The two rank functions

This repository carries two notions of rank for a finite locally free module: the locally
constant `Stacks.Chow.moduleRank` used to cut out the loci, and the pointwise
`AlgebraicGeometry.Scheme.Modules.fiberRank`, the dimension of the fibre at a point. They agree,
`Stacks.Chow.fiberRank_eq_moduleRank`, both being the cardinality of the index set of a local
basis through the point. The constant-rank statement is proved through the second, because that
is the shape in which
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq` is
available.

### The index universe

`Stacks.Chow.rankLociFamily` reindexes the rank loci by `ULift ℕ`. The decomposition theorem
Stacks 0FDZ, `Stacks.Chow.bivariantPieceEquiv`, requires its index type to lie in the universe of
the schemes, whereas `ℕ` lies in `Type 0`. The lift carries no information: `ULift.up r` indexes
the rank-`r` locus.

## References

* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The rank of a finite locally free module on a scheme, as a locally constant `ℕ`-valued
function. It is the rank of Stacks 01C9 read as a natural number, the structure stalks of a
scheme being nonzero. -/
def moduleRank : LocallyConstant X ℕ :=
  @Stacks.SheafOfModules.finiteLocallyFreeRank X.toTopCat X.sheaf E
    (LocallyFreeRank.scheme_stalksNontrivial X) hE

/-- The locus `X_r` where a finite locally free module has rank `r`, as an open subscheme. It is
open and closed, being a fibre of a locally constant function. -/
def rankLocus (r : ℕ) : X.Opens :=
  @Stacks.SheafOfModules.rankStratum X.toTopCat X.sheaf E
    (LocallyFreeRank.scheme_stalksNontrivial X) hE r

/-- A point lies in the rank-`r` locus exactly when the rank there is `r`. -/
@[simp]
theorem mem_rankLocus {r : ℕ} {x : X} : x ∈ rankLocus E r ↔ moduleRank E x = r := Iff.rfl

/-- Each rank locus is open and closed. -/
theorem isClopen_rankLocus (r : ℕ) : IsClopen (rankLocus E r : Set X) :=
  (moduleRank E).isLocallyConstant.isClopen_fiber r

/-- The family of rank loci, reindexed by `ULift ℕ` so that it lies in the universe of the
scheme: `ULift.up r` indexes the rank-`r` locus. -/
def rankLociFamily : ULift.{u} ℕ → X.Opens := fun r ↦ rankLocus E r.down

/-- **The rank decomposition `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …`.** The rank loci of a finite locally free
module decompose the scheme into open and closed subschemes: they are pairwise disjoint, every
point lying in the locus of its own rank, and they cover the scheme. -/
theorem isClopenDecomposition_rankLociFamily : IsClopenDecomposition (rankLociFamily E) where
  disjoint _ _ hij := Opens.coe_disjoint.mp <| Set.disjoint_left.mpr fun _ hx hy ↦
    hij (congrArg ULift.up (((mem_rankLocus E).mp hx).symm.trans ((mem_rankLocus E).mp hy)))
  iSup_eq_top := top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨ULift.up (moduleRank E x), rfl⟩

/-- The pointwise fibre rank agrees with the locally constant rank: both compute the cardinality
of the index set of a local basis through the point. -/
theorem fiberRank_eq_moduleRank (x : X) :
    AlgebraicGeometry.Scheme.Modules.fiberRank E x = moduleRank E x := by
  obtain ⟨q, hq, hfin⟩ := hE.exists_isFiniteLocallyFreeData
  have hxcover : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff X.toTopCat q.X).mp q.coversTop]
    exact Opens.mem_top x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxcover
  have : Finite (q.generators i).I := (hfin.isFiniteType i).finite
  rw [Stacks.FiniteLocallyFree.ModuleTFAE.fiberRank_eq_card_of_trivialization E q hq i x hi]
  exact (@Stacks.SheafOfModules.finiteLocallyFreeRank_eq_card X.toTopCat X.sheaf E
    (LocallyFreeRank.scheme_stalksNontrivial X) hE q hq i x hi).symm

/-- On its rank-`r` locus the module is finite locally free of constant rank `r`. -/
theorem isFiniteLocallyFreeOfRank_pullback_rankLocus (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r :=
  AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq E
    (rankLocus E r) r fun x hx ↦ (fiberRank_eq_moduleRank E x).trans hx

/-- The restriction of the identity to a piece is the identity. -/
theorem pieceMap_id {I : Type u} (U : I → X.Opens) (ha : ∀ i, U i ≤ (𝟙 X) ⁻¹ᵁ U i) (i : I) :
    pieceMap (𝟙 X) U U id ha i = 𝟙 (U i : Scheme.{u}) := by
  refine (cancel_mono (U i).ι).mp ?_
  rw [Category.id_comp]
  simpa using pieceMap_comp_ι (𝟙 X) U U id ha i

end Stacks.Chow

end
