module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeBiproduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLocallyFree
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineColimitPresentations
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Finite local freeness is closed under finite direct sums and tensor powers

Let `R` be a sheaf of rings on a site `(C, J)`.  This file proves that the conditions
`SheafOfModules.IsFiniteFree` of Stacks 03DE(2) and `SheafOfModules.IsFiniteLocallyFreeOnSite`
of Stacks 03DL(2) are stable under the direct sum of a finite family of sheaves of modules —
hence under the binary product and the binary coproduct, which a preadditive category identifies
with the binary direct sum — and that finite local freeness is stable under every tensor power.

The two ingredients are already in place and this file only joins them.  Finite freeness is
additive in the index: a binary coproduct of a coproduct of `n` copies of the structure sheaf
and a coproduct of `m` copies of it is a coproduct of `n + m` copies, which is
`SheafOfModules.isColimitCofanSumOfBinaryCofan` followed by the reindexing
`finSumFinEquiv`.  Passing from the global statement to the local one needs the restriction to a
slice site to commute with the direct sum, and it does because `SheafOfModules.overFunctor` is
additive — `SheafOfModules.instAdditiveOverFunctor` — and an additive functor preserves finite
biproducts.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.SheafOfModules.isFiniteFree_biprod`: the direct sum of two finite free sheaves of
  modules is finite free.
* `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_biprod`: the direct sum of two finite
  locally free sheaves of modules on a site is finite locally free.
* `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_coprod` and
  `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_prod`: the same statement for the binary
  coproduct and the binary product.
* `Stacks.SheafOfModules.isFiniteFree_biproduct` and
  `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_biproduct`: the direct sum of a family
  indexed by a finite type is finite free, resp. finite locally free.
* `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_tensorPower`: every tensor power of a finite
  locally free sheaf of modules is finite locally free.

The tensor product of *two* modules and the structure sheaf itself are not restated here: they
are already `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite`,
Stacks 03L6(2), and `SheafOfModules.isFiniteLocallyFreeOnSite_unit`.  The tensor power statement
is the induction that joins them.

## Implementation notes

The existence of the biproduct is a hypothesis `[HasBinaryBiproduct F G]` rather than an
instance, exactly as in `Stacks.SheafOfModules.isCoherentOnSite_biprod`.  It is never a real
restriction: `SheafOfModules.{w} R` is preadditive and has all limits, so
`CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts` produces it with no hypothesis
on the site.  Leaving it as an argument keeps the statement usable with whichever biproduct the
caller already has in hand.

The index type of the family form is in `Type`, not an arbitrary universe.  This is forced by
`CategoryTheory.Limits.PreservesFiniteBiproducts`, whose field quantifies over `J : Type` with
`[Finite J]`; it is the hypothesis under which an additive functor is known to preserve the
biproduct, and so the hypothesis under which the restriction to a slice site commutes with the
direct sum.  Every concrete finite index — `Fin n` above all — lives there.

The module universe is kept equal to the universe of the sheaf of rings.  This is the universe
in which `SheafOfModules.isFiniteFree_iff_exists_isColimit` and
`SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit` phrase the two conditions
as colimiting cofans, and a cofan of copies of `SheafOfModules.unit R` is the only description of
finite freeness that a direct sum can be computed against.

Restriction to a slice site only reaches *finite* direct sums, and that is exactly the range of
these statements.  An infinite coproduct of sheaves of modules is the sheafification of the
objectwise one, and `SheafOfModules.overFunctor` is not known to preserve it without pullbacks
in `C`; the discussion in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/OverFiniteFree.lean`
applies verbatim.

`SheafOfModules.tensorPower` recurses directly on `Stacks.SheafOfModules.Tensor.sheafTensor`
rather than through a `CategoryTheory.MonoidalCategory` instance, so the induction has three
cases and not two: the zeroth power is the structure sheaf, the first is the module, and the
`n + 2`-nd is one tensor product away from the `n + 1`-st.  The ringed site that
`tensorSheaf_isFiniteLocallyFreeOnSite` is stated for is assembled from the site and the sheaf
of commutative rings on the spot; `CategoryTheory.Sheaf.toRingCat` is the spelling of the
underlying sheaf of rings for which that matches `Stacks.SheafOfModules.Tensor.ringSheaf`
without unfolding `sheafCompose`.

The two covering families trivializing `F` and `G` are intersected as in
`Stacks.SheafOfModules.TensorLocalProperties.isLocallyFreeOnSiteWith_tensor`: the index type is
the set of arrows into the object that lie in both sieves, and each such arrow factors through a
member of either family, along which the trivialization is restricted by
`Stacks.SheafOfModules.exists_isColimitCofan_over_of_le`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL) — the definition of a
  finite locally free sheaf of modules on a ringed site.  This file proves a closure property of
  that condition and carries no tag of its own.
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE) — the definition of a
  finite free sheaf of modules.
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6) — the tensor product of
  two finite locally free sheaves of modules, which the tensor power statement iterates.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The binary coproduct of two finite locally free sheaves of modules on a site is finite
locally free: a preadditive category identifies it with the direct sum. -/
theorem isFiniteLocallyFreeOnSite_coprod {F G : _root_.SheafOfModules.{w} R}
    [HasBinaryBiproduct F G] [HasBinaryCoproduct F G]
    (hF : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite F)
    (hG : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite G) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite (F ⨿ G) :=
  Intrinsic.isFiniteLocallyFreeOnSite_of_iso (biprod.isoCoprod F G)
    (isFiniteLocallyFreeOnSite_biprod _ _ hF hG)

/-- The binary product of two finite locally free sheaves of modules on a site is finite locally
free: a preadditive category identifies it with the direct sum. -/
theorem isFiniteLocallyFreeOnSite_prod {F G : _root_.SheafOfModules.{w} R}
    [HasBinaryBiproduct F G] [HasBinaryProduct F G]
    (hF : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite F)
    (hG : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite G) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite (F ⨯ G) :=
  Intrinsic.isFiniteLocallyFreeOnSite_of_iso (biprod.isoProd F G)
    (isFiniteLocallyFreeOnSite_biprod _ _ hF hG)

/-- **The direct sum of a finite family of finite free sheaves of modules is finite free.**  If
each `M i` is a coproduct of `n i` copies of the structure sheaf, then `⨁ M` is a coproduct of
copies indexed by `Σ i, Fin (n i)`, which is finite; `CategoryTheory.Limits.isColimitCofanSigma`
splices the cofans and `Finite.equivFin` reindexes the total space by a `Fin`. -/
theorem isFiniteFree_biproduct {ι : Type} [Finite ι] (M : ι → _root_.SheafOfModules.{w} R)
    [HasBiproduct M] (hM : ∀ i, _root_.SheafOfModules.IsFiniteFree R (M i)) :
    _root_.SheafOfModules.IsFiniteFree R (⨁ M) := by
  choose n p hp using fun i =>
    (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R (M i)).1 (hM i)
  have hZ : IsColimit (Cofan.mk (⨁ M) (biproduct.ι M)) := biproduct.isColimit M
  have hs := Cofan.isColimitEquivOfEquiv
    (ε := (Finite.equivFin (Σ i, Fin (n i))).symm) _
    (isColimitCofanSigma (fun i => (hp i).some) hZ)
  exact (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R (⨁ M)).2
    ⟨Nat.card (Σ i, Fin (n i)), _, ⟨hs⟩⟩

/-- **The direct sum of a finite family of finite locally free sheaves of modules on a site is
finite locally free.**  This is the form in which the closure property is used: a surjection out
of a finite direct sum of finite locally free modules.

The covering families trivializing the summands are intersected by
`Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem`, a finite infimum of covering sieves being
covering; on each member of the intersection every summand is finite free, so
`isFiniteFree_biproduct` makes their direct sum finite free, and
`CategoryTheory.Functor.mapBiproduct` identifies it with the restriction of `⨁ M` because the
restriction is additive and hence preserves finite biproducts. -/
theorem isFiniteLocallyFreeOnSite_biproduct {ι : Type} [Finite ι]
    (M : ι → _root_.SheafOfModules.{w} R) [HasBiproduct M]
    (hM : ∀ i, _root_.SheafOfModules.IsFiniteLocallyFreeOnSite (M i)) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite (⨁ M) := by
  intro U
  choose Idx V a hcov hfree using fun i =>
    (_root_.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit (M i)).1
      (hM i) U
  refine ⟨{q : Σ Z : C, Z ⟶ U // ∀ i, Sieve.ofArrows (V i) (a i) q.2}, fun q => q.1.1,
    fun q => q.1.2, ?_, ?_⟩
  · refine J.superset_covering ?_ (FiniteTypeKernel.iInf_mem J _ hcov)
    intro Z g hg
    exact Sieve.ofArrows_mk _ _ (⟨⟨Z, g⟩, (FiniteTypeKernel.iInf_apply _ g).1 hg⟩ :
      {q : Σ Z : C, Z ⟶ U // ∀ i, Sieve.ofArrows (V i) (a i) q.2})
  · intro q
    choose j g _hjg using fun i => (Sieve.mem_ofArrows_iff (V i) (a i) q.1.2).1 (q.2 i)
    have hres : ∀ i, _root_.SheafOfModules.IsFiniteFree (R.over q.1.1) ((M i).over q.1.1) :=
      fun i => (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2
        (exists_isColimitCofan_over_of_le (M i) (g i) (hfree i (j i)))
    exact Intrinsic.isFiniteFree_of_iso
      (Functor.mapBiproduct (_root_.SheafOfModules.overFunctor.{w} R q.1.1) M).symm
      (isFiniteFree_biproduct _ hres)

section TensorPower

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Finite local freeness is inherited by every tensor power.**  The zeroth power is the
structure sheaf, which is finite locally free of rank one by
`SheafOfModules.isFiniteLocallyFreeOnSite_unit`, the first power is the sheaf itself, and each
higher power is one tensor product with `F` away from its predecessor, which is Stacks 03L6(2),
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite`. -/
theorem isFiniteLocallyFreeOnSite_tensorPower
    (F : _root_.SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp))
    (hF : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite F) (n : ℕ) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite
      (_root_.SheafOfModules.tensorPower J F n) := by
  induction n with
  | zero => exact _root_.SheafOfModules.isFiniteLocallyFreeOnSite_unit
  | succ n ih =>
    match n, ih with
    | 0, _ => exact hF
    | k + 1, ih =>
      exact TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite
        { C := C, J := J, O := Osharp } F _ hF ih

end TensorPower

end Stacks.SheafOfModules

end
