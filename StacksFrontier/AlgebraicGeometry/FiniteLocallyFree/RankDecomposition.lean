module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RankDecomposition
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank

/-!
# The rank decomposition of a scheme carrying a finite locally free module

Let `X` be a scheme and `E` a finite locally free `𝒪_X`-module. The rank of `E` is a locally
constant function on `X`, and its fibres

  `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …`,   `X_r = {x ∈ X | rank_x E = r}`,

are open and closed, pairwise disjoint and cover `X`, and `E` is free of rank `r` on a
neighbourhood of each point of `X_r`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.finiteLocallyFreeRank` — the rank of `E`, as a locally
  constant function with values in `ℕ`.
* `AlgebraicGeometry.Scheme.Modules.rankStratum` — the locus `X_r` where `E` has rank `r`, as an
  open subscheme of `X`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isClopen_rankStratum`,
  `AlgebraicGeometry.Scheme.Modules.disjoint_rankStratum` and
  `AlgebraicGeometry.Scheme.Modules.iSup_rankStratum` — the loci are open and closed, pairwise
  disjoint, and cover `X`.
* `AlgebraicGeometry.Scheme.Modules.exists_free_nbhd_of_mem_rankStratum` — `E` is free of rank
  `r` near every point of `X_r`.
* `AlgebraicGeometry.Scheme.Modules.rankDecomposition` — the decomposition of a scheme by the
  rank of a finite locally free module.

## References

* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- A module over the structure sheaf of a scheme, read as a module over the sheaf of rings
underlying it. -/
def toRingSheafModule : SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X.toTopCat X.sheaf) := E

/-- Finite local freeness of a module over the structure sheaf of a scheme is finite local
freeness over the underlying sheaf of rings. -/
instance isFiniteLocallyFree_toRingSheafModule :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (toRingSheafModule E) :=
  inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)

/-- The rank of a finite locally free module on a scheme, as a locally constant function with
values in `ℕ`. -/
def finiteLocallyFreeRank : LocallyConstant X ℕ :=
  @Stacks.SheafOfModules.finiteLocallyFreeRank X.toTopCat X.sheaf (toRingSheafModule E)
    (LocallyFreeRank.scheme_stalksNontrivial X) (isFiniteLocallyFree_toRingSheafModule E)

/-- The locus `X_r` where a finite locally free module on a scheme has rank `r`, as an open
subscheme. -/
def rankStratum (r : ℕ) : X.Opens :=
  @Stacks.SheafOfModules.rankStratum X.toTopCat X.sheaf (toRingSheafModule E)
    (LocallyFreeRank.scheme_stalksNontrivial X) (isFiniteLocallyFree_toRingSheafModule E) r

/-- A point lies in the rank locus `X_r` if and only if the rank of the module at it is `r`. -/
@[simp]
theorem mem_rankStratum {r : ℕ} {x : X} : x ∈ rankStratum E r ↔ finiteLocallyFreeRank E x = r :=
  Iff.rfl

/-- Each rank locus is open and closed. -/
theorem isClopen_rankStratum (r : ℕ) : IsClopen (rankStratum E r : Set X) :=
  @Stacks.SheafOfModules.isClopen_rankStratum X.toTopCat X.sheaf (toRingSheafModule E)
    (LocallyFreeRank.scheme_stalksNontrivial X) (isFiniteLocallyFree_toRingSheafModule E) r

/-- Distinct rank loci are disjoint. -/
theorem disjoint_rankStratum {r s : ℕ} (h : r ≠ s) :
    Disjoint (rankStratum E r) (rankStratum E s) :=
  disjoint_iff.2 <| Opens.ext <| Set.eq_empty_iff_forall_notMem.2 fun _ hx ↦
    h (hx.1.symm.trans hx.2)

/-- The rank loci cover the scheme. -/
theorem iSup_rankStratum : ⨆ r : ℕ, rankStratum E r = ⊤ :=
  eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨finiteLocallyFreeRank E x, rfl⟩

/-- A finite locally free module is free of rank `r` on a neighbourhood of every point of the
locus where its rank is `r`. -/
theorem exists_free_nbhd_of_mem_rankStratum (r : ℕ) (x : X) (hx : x ∈ rankStratum E r) :
    ∃ (V : X.Opens) (_ : x ∈ V) (_ : V ≤ rankStratum E r) (I : Type u),
      Nonempty (I ≃ Fin r) ∧ Nonempty (SheafOfModules.free.{u} I ≅ (toRingSheafModule E).over V) :=
  @Stacks.SheafOfModules.exists_free_nbhd_of_rank_eq X.toTopCat X.sheaf (toRingSheafModule E)
    (LocallyFreeRank.scheme_stalksNontrivial X) (isFiniteLocallyFree_toRingSheafModule E) r
    (rankStratum E r) (fun _ hy ↦ hy) x hx

/-- The rank of a finite locally free module `E` on a scheme `X` is locally constant, the loci
`X_r` where the rank is `r` are open and closed, pairwise disjoint and cover `X`, and `E` is free
of rank `r` on a neighbourhood of every point of `X_r`. -/
@[stacks 0ESW "the decomposition X = ∐ X_r of a scheme by the rank of a finite locally free \
module: the rank is locally constant, the loci are open and closed, pairwise disjoint and \
covering, and the module is free of rank r near each point of X_r. The Chern classes \
c_p(E) ∈ A^p(X) of a module of non-constant rank, the total Chern class in the completed \
bivariant group, the rank class r(E) ∈ A^0(X) and the centrality of c_p(E) and r(E) in A^*(X) \
are not covered"]
theorem rankDecomposition :
    IsLocallyConstant ⇑(finiteLocallyFreeRank E) ∧
      (∀ r : ℕ, IsClopen (rankStratum E r : Set X)) ∧
      (∀ r s : ℕ, r ≠ s → Disjoint (rankStratum E r) (rankStratum E s)) ∧
      (⨆ r : ℕ, rankStratum E r) = ⊤ ∧
      ∀ (r : ℕ) (x : X), x ∈ rankStratum E r →
        ∃ (V : X.Opens) (_ : x ∈ V) (_ : V ≤ rankStratum E r) (I : Type u),
          Nonempty (I ≃ Fin r) ∧
            Nonempty (SheafOfModules.free.{u} I ≅ (toRingSheafModule E).over V) :=
  ⟨(finiteLocallyFreeRank E).isLocallyConstant, isClopen_rankStratum E,
    fun _ _ h ↦ disjoint_rankStratum E h,
    iSup_rankStratum E, exists_free_nbhd_of_mem_rankStratum E⟩

end AlgebraicGeometry.Scheme.Modules

end
