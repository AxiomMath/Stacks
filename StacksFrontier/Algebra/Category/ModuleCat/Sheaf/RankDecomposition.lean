module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
import StacksCore.Tactic.StacksAttribute

/-!
# The rank decomposition of a finite locally free sheaf of modules

Let `(X, O_X)` be a ringed space all of whose structure stalks `O_{X, x}` are nonzero and let
`E` be a finite locally free sheaf of `O_X`-modules. The rank of `E` is then a locally constant
`ℕ`-valued function on `X`, so the loci `X_i = {x | rank_E x = i}` are open and closed and
partition `X`, and `E` is finite locally free of rank `i` on `X_i`. This is the disjoint union
decomposition `X = X_0 ⨿ X_1 ⨿ X_2 ⨿ …` of [Stacks, Tag 0B37].

## Main definitions

* `Stacks.SheafOfModules.finiteLocallyFreeRank`: the rank of a finite locally free sheaf of
  modules as a locally constant `ℕ`-valued function. It is the `Cardinal`-valued rank of
  [Stacks, Tag 01C9] read as a natural number, which loses nothing because a finite locally
  free sheaf has finite local bases.
* `Stacks.SheafOfModules.rankStratum`: the open locus `X_i` where the rank equals `i`.

## Main results

* `Stacks.SheafOfModules.rankDecomposition`: **Tag 0B37**, the decomposition itself. The rank
  is locally constant, each `X_i` is open and closed, the `X_i` are pairwise disjoint and cover
  `X`, and `E` is finite locally free of rank `i` on `X_i`.
* `Stacks.SheafOfModules.exists_free_nbhd_of_rank_eq`: on an open on which the rank is
  constant equal to `r`, every point has a neighbourhood inside that open over which `E` is
  free on an index type of cardinality `r`. This is the content of the last clause, stated for
  an arbitrary open so that it also applies to an open refining a stratum.
* `Stacks.SheafOfModules.freeIsoOverMap`: a presentation of a restricted sheaf of modules as a
  free one, transported along an arrow of the site. The index type is unchanged.

## Implementation notes

The rank is `LocallyFreeRank.locallyFreeRank` composed with `Cardinal.toNat`. Its
specification is `finiteLocallyFreeRank_eq_card`, which pins the value at a point of a
trivialising open against the cardinality of that trivialisation's index type; that is the only
property of the rank used below, and it determines it.

The last clause is proved for an arbitrary open `Y` on which the rank is constant rather than
for `rankStratum` itself. Keeping `Y` an opaque variable is what makes the proof elaborate:
unfolding `rankStratum` exposes the choice of a rank function inside
`LocallyFreeRank.locallyFreeRank`, and a definitional unfolding of a membership in `Y` then
unfolds that choice.

Freeness on `Y` is stated as the existence of a free presentation on a neighbourhood of each
point of `Y` rather than as `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` of the
restriction `E.over Y`. The two say the same thing, because the opens of the open subspace `Y`
are exactly the opens of the ambient space contained in `Y`; the form used here needs only the
restriction of a free presentation along an inclusion of opens, `freeIsoOverMap`, and not the
transport of local generators data across the comparison of the slice site over `Y` with the
iterated slice sites above it.

The members of a trivialising family for `E` which miss `Y` are irrelevant here, because the
statement is pointwise on `Y`; the member through a given point of `Y` cuts `Y` in an open on
which `E` is free, and the index type of that presentation computes the rank at the point.

The remaining content of the section is not formalised here: the exact structure on `Vect(X)`
and its `K`-group, the rank homomorphism `K_0(Vect(X)) → Map_cont(X, Z)`, the invertible sheaf
`det(E)` which is `⋀^i(E|_{X_i})` on `X_i`, and `det : K_0(Vect(X)) → Pic(X)`.

## References

* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u v w

namespace Stacks.SheafOfModules

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A presentation of the restriction of `M` to `U` as a free sheaf of modules on `I`
restricts, along an arrow `f : V ⟶ U`, to such a presentation of the restriction of `M` to `V`.
The index type is unchanged. -/
noncomputable def freeIsoOverMap (M : _root_.SheafOfModules.{w} R) {V U : C} (f : V ⟶ U)
    (I : Type w) (e : _root_.SheafOfModules.free.{w} I ≅ M.over U) :
    _root_.SheafOfModules.free.{w} I ≅ M.over V := by
  have : HasSheafify (J.over V) AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : PreservesColimitsOfSize.{w, w} (_root_.SheafOfModules.overMap.{w} R f) :=
    overMap_preservesColimits R f
  exact _root_.SheafOfModules.mapFreeIso (_root_.SheafOfModules.overMap R f) I
      (_root_.SheafOfModules.overMapUnitIso f).symm ≪≫
    (_root_.SheafOfModules.overMap R f).mapIso e ≪≫
    (_root_.SheafOfModules.overFunctorMap R f).app M

end Transport

section RingedSpace

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (F : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O))
  (hO : LocallyFreeRank.StalksNontrivial X O)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- The rank of a finite locally free sheaf of modules on a ringed space whose structure stalks
are all nonzero, as a locally constant function with values in `ℕ`. It is the `Cardinal`-valued
rank of [Stacks, Tag 01C9] read as a natural number. -/
@[sga "6 I 6.0"]
noncomputable def finiteLocallyFreeRank : LocallyConstant X ℕ :=
  (LocallyFreeRank.locallyFreeRank F hO).map Cardinal.toNat

/-- The rank at a point of a member of a local-generator presentation is the cardinality of that
member's index type. This is the full specification of `finiteLocallyFreeRank`. -/
theorem finiteLocallyFreeRank_eq_card
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} F) (hq : q.IsLocallyFreeData)
    (i : q.I) (x : X) (hx : x ∈ q.X i) :
    finiteLocallyFreeRank F hO x = Nat.card (q.generators i).I := by
  have h := LocallyFreeRank.locallyFreeRank_eq_mk_generators F hO q hq i x hx
  show Cardinal.toNat (LocallyFreeRank.locallyFreeRank F hO x) = _
  rw [h, Nat.card]

/-- The locus `X_i` where a finite locally free sheaf of modules has rank `i`, as an open subset
of the ringed space. It is open because the rank is locally constant. -/
def rankStratum (i : ℕ) : Opens X :=
  ⟨{x | finiteLocallyFreeRank F hO x = i},
    (finiteLocallyFreeRank F hO).isLocallyConstant.isOpen_fiber i⟩

/-- A point lies in the rank locus `X_i` exactly when the rank there is `i`. -/
@[simp]
theorem mem_rankStratum {i : ℕ} {x : X} :
    x ∈ rankStratum F hO i ↔ finiteLocallyFreeRank F hO x = i := Iff.rfl

/-- Each rank locus is open and closed, being a fibre of a locally constant function. -/
theorem isClopen_rankStratum (i : ℕ) : IsClopen (rankStratum F hO i : Set X) :=
  (finiteLocallyFreeRank F hO).isLocallyConstant.isClopen_fiber i

/-- The rank loci are pairwise disjoint. -/
theorem rankStratum_disjoint :
    Pairwise (Function.onFun Disjoint fun i : ℕ => (rankStratum F hO i : Set X)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hxi hxj => hij ?_
  exact (mem_rankStratum F hO |>.mp hxi).symm.trans (mem_rankStratum F hO |>.mp hxj)

/-- The rank loci cover the space. -/
theorem iSup_rankStratum : (⨆ i : ℕ, rankStratum F hO i) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  rw [Opens.mem_iSup]
  exact ⟨finiteLocallyFreeRank F hO x, rfl⟩

/-- **A finite locally free sheaf of modules is free of rank `r` near every point of an open on
which its rank is constant equal to `r`.** A member of a trivialising family for `E` through the
point cuts the open in an open on which `E` is free, and the index type of that presentation
computes the rank at the point, hence has cardinality `r`. -/
theorem exists_free_nbhd_of_rank_eq (r : ℕ) (Y : Opens X)
    (hY : ∀ x : X, x ∈ Y → finiteLocallyFreeRank F hO x = r) (x : X) (hx : x ∈ Y) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ Y) (I : Type u), Nonempty (I ≃ Fin r) ∧
      Nonempty (_root_.SheafOfModules.free.{u} I ≅ F.over V) := by
  classical
  obtain ⟨q, hq, hfin⟩ := (inferInstance :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F).exists_isFiniteLocallyFreeData
  have hxcover : x ∈ ⨆ k, q.X k := by
    rw [(Opens.coversTop_iff X q.X).mp q.coversTop]; trivial
  rw [Opens.mem_iSup] at hxcover
  obtain ⟨k, hk⟩ := hxcover
  have : Finite (q.generators k).I := (hfin.isFiniteType k).finite
  have : IsIso (q.generators k).π := hq.isIso k
  refine ⟨q.X k ⊓ Y, ⟨hk, hx⟩, inf_le_right, (q.generators k).I, ⟨Finite.equivFinOfCardEq ?_⟩,
    ⟨freeIsoOverMap F (homOfLE (inf_le_left : q.X k ⊓ Y ≤ q.X k)) (q.generators k).I
      (asIso (q.generators k).π)⟩⟩
  rw [← finiteLocallyFreeRank_eq_card F hO q hq k x hk]
  exact hY x hx

/-- **Stacks Project, Tag 0B37: the rank decomposition.** A finite locally free sheaf of modules
`E` on a ringed space whose structure stalks are all nonzero has locally constant rank, so the
loci `X_i` where the rank is `i` are open and closed, pairwise disjoint and cover `X`, and `E` is
finite locally free of rank `i` on `X_i`. -/
@[stacks 0B37 "the locally constant rank and the clopen rank decomposition \
X = X_0 ⊔ X_1 ⊔ … with E finite locally free of rank i on X_i; the exact category Vect(X) and \
its K-group, the rank homomorphism K_0(Vect(X)) → Map_cont(X, Z), the invertible sheaf det(E) \
and the homomorphism det : K_0(Vect(X)) → Pic(X) are not covered", ega "0 5.4.1" "partial"]
theorem rankDecomposition :
    IsLocallyConstant (⇑(finiteLocallyFreeRank F hO)) ∧
      (∀ i : ℕ, IsClopen (rankStratum F hO i : Set X)) ∧
      Pairwise (Function.onFun Disjoint fun i : ℕ => (rankStratum F hO i : Set X)) ∧
      (⨆ i : ℕ, rankStratum F hO i) = ⊤ ∧
      ∀ (i : ℕ) (x : X), x ∈ rankStratum F hO i →
        ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ rankStratum F hO i) (I : Type u),
          Nonempty (I ≃ Fin i) ∧ Nonempty (_root_.SheafOfModules.free.{u} I ≅ F.over V) :=
  ⟨(finiteLocallyFreeRank F hO).isLocallyConstant, isClopen_rankStratum F hO,
    rankStratum_disjoint F hO, iSup_rankStratum F hO,
    fun i => exists_free_nbhd_of_rank_eq F hO i _ (fun _ hx => hx)⟩

end RingedSpace

end Stacks.SheafOfModules

end
