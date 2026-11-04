module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.QuasicoherenceSliceRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# Quasi-coherence on a slice of a site is local on coverings

Let `C` be a site, `R` a sheaf of rings on it and `V` an object of `C`.  A sheaf of
`R.over V`-modules `F` on the slice `C/V` restricts along every arrow `f : U ⟶ V` to the slice
`C/U` (`SheafOfModules.overMap`).  This file proves that quasi-coherence of `F` can be tested on
any covering family `{U_i ⟶ V}`: `F` is quasi-coherent exactly when every restriction of `F` to
`C/U_i` is.

The forward implication is `Stacks.SheafOfModules.isQuasicoherentOnSite_overMap`.  For the
converse, a covering family of `V`, read in `C/V`, covers its terminal object, so Stacks 03DN
(`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite`) reduces the
claim to the quasi-coherence of the restrictions `F.over T` to the iterated slices `(C/V)/T`.
The iterated slice `(C/V)/T` is the slice `C/T.left` (`CategoryTheory.Over.iteratedSliceEquiv`),
and under that identification `F.over T` is, on the nose, the restriction of `F` along
`T.hom`; quasi-coherence is invariant under an equivalence of ringed sites
(`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`).

## Main results

* `Stacks.SheafOfModules.isQuasicoherentOnSite_over_of_overMap`: if the restriction of `F` along
  `T.hom` is quasi-coherent, so is the restriction of `F` to the iterated slice at `T`.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_forall_overMap`: **quasi-coherence on a slice
  is local on coverings.**

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 0DC3](https://stacks.math.columbia.edu/tag/0DC3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- If the restriction of a sheaf of modules `F` on `C/V` along `T.hom : T.left ⟶ V` is
quasi-coherent, then so is the restriction of `F` to the iterated slice `(C/V)/T`: the two are
identified on the nose by the equivalence `(C/V)/T ≌ C/T.left`. -/
theorem isQuasicoherentOnSite_over_of_overMap (R : Sheaf J RingCat.{w}) {V : C}
    (F : SheafOfModules.{w} (R.over V)) (T : Over V)
    (h : ((SheafOfModules.overMap R T.hom).obj F).IsQuasicoherentOnSite) :
    (F.over T).IsQuasicoherentOnSite := by
  let e := T.iteratedSliceEquiv.symm
  have : e.inverse.IsDenseSubsite ((J.over V).over T) (J.over T.left) := by
    show T.iteratedSliceEquiv.functor.IsDenseSubsite ((J.over V).over T) (J.over T.left)
    infer_instance
  have : e.functor.IsContinuous (J.over T.left) ((J.over V).over T) := by
    show T.iteratedSliceEquiv.inverse.IsContinuous (J.over T.left) ((J.over V).over T)
    infer_instance
  exact (isQuasicoherentOnSite_reindex_iff e ((R.over V).over T) (F.over T)).1 h

/-- **Quasi-coherence on a slice is local on coverings.**  For a covering family `{U_i ⟶ V}` of an
object of a site, a sheaf of modules on `C/V` is quasi-coherent if and only if each of its
restrictions to the slices `C/U_i` is quasi-coherent. -/
theorem isQuasicoherentOnSite_iff_forall_overMap (R : Sheaf J RingCat.{w}) {V : C}
    (𝒰 : PreZeroHypercover.{max u v} V) (h𝒰 : 𝒰.sieve₀ ∈ J V)
    (F : SheafOfModules.{w} (R.over V)) :
    F.IsQuasicoherentOnSite ↔
      ∀ i, ((SheafOfModules.overMap R (𝒰.f i)).obj F).IsQuasicoherentOnSite := by
  refine ⟨fun hF i => isQuasicoherentOnSite_overMap R (𝒰.f i) F hF, fun hF => ?_⟩
  refine (isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite F).2
    ⟨𝒰.I₀, fun i => Over.mk (𝒰.f i), ?_, fun i =>
      isQuasicoherentOnSite_over_of_overMap R F (Over.mk (𝒰.f i)) (hF i)⟩
  intro W
  rw [GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ?_ (J.pullback_stable W.hom h𝒰)
  intro Z g hg
  obtain ⟨_, a, _, ⟨i⟩, ha⟩ := hg
  exact ⟨Over.mk (g ≫ W.hom), Over.homMk g, 𝟙 Z, ⟨i, ⟨Over.homMk a ha⟩⟩, by simp⟩

end Stacks.SheafOfModules
