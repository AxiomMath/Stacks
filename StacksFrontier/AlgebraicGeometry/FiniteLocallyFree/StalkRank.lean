module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs

/-!
# The rank of a finite locally free module is the rank of its stalks

Let `E` be a finite locally free module on a scheme `X`. The rank of `E` at a point `x` is the
rank of the stalk `E_x` as a module over the local ring `𝒪_{X, x}`. In particular the rank
vanishes away from the support of `E`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.finiteLocallyFreeRank_eq_finrank_stalk`: the rank of `E` at
  `x` is `Module.finrank 𝒪_{X, x} E_x`.
* `AlgebraicGeometry.Scheme.Modules.finiteLocallyFreeRank_eq_zero_of_notMem_supp`: the rank of
  `E` vanishes outside the support of `E`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The free module on an arbitrary index type over a nonzero commutative ring has rank the
cardinality of the index type, read in `ℕ`. -/
private theorem finrank_finsupp_self_eq_natCard (R : Type u) (ι : Type u) [CommRing R]
    [Nontrivial R] : Module.finrank R (ι →₀ R) = Nat.card ι := by
  rw [Module.finrank, rank_finsupp_self, Cardinal.lift_id, Nat.card]

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The rank of a finite locally free module on a scheme at a point is the rank of its stalk
over the local ring at that point. -/
theorem finiteLocallyFreeRank_eq_finrank_stalk (x : X) :
    finiteLocallyFreeRank E x =
      @Module.finrank (ToType (TopCat.Presheaf.stalk X.sheaf.obj x))
        (ToType (TopCat.Presheaf.stalk (toRingSheafModule E).val.presheaf x)) _ _
        (LocallyFreeRank.instModuleStalkF X.toTopCat X.sheaf (toRingSheafModule E) x) := by
  let := LocallyFreeRank.instModuleStalkF X.toTopCat X.sheaf (toRingSheafModule E) x
  have : Nontrivial (ToType (TopCat.Presheaf.stalk X.sheaf.obj x)) :=
    LocallyFreeRank.scheme_stalksNontrivial X x
  obtain ⟨q, hq, -⟩ :=
    (isFiniteLocallyFree_toRingSheafModule E).exists_isFiniteLocallyFreeData
  have hxcover : x ∈ ⨆ k, q.X k := by
    rw [(Opens.coversTop_iff _ q.X).mp q.coversTop]; trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hxcover
  obtain ⟨e⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp X.toTopCat X.sheaf
    (toRingSheafModule E) x hk (LocallyFreeRank.trivializationOfLocalGenerators _ q hq k)
  exact (Stacks.SheafOfModules.finiteLocallyFreeRank_eq_card _
    (LocallyFreeRank.scheme_stalksNontrivial X) q hq k x hk).trans
      ((finrank_finsupp_self_eq_natCard _ _).symm.trans e.finrank_eq.symm)

/-- The rank of a finite locally free module on a scheme vanishes at every point outside its
support. -/
theorem finiteLocallyFreeRank_eq_zero_of_notMem_supp {x : X}
    (hx : x ∉ _root_.SheafOfModules.supp E) : finiteLocallyFreeRank E x = 0 := by
  have : Nontrivial (ToType (TopCat.Presheaf.stalk X.sheaf.obj x)) :=
    LocallyFreeRank.scheme_stalksNontrivial X x
  have : Subsingleton (ToType (TopCat.Presheaf.stalk (toRingSheafModule E).val.presheaf x)) :=
    not_nontrivial_iff_subsingleton.mp fun h ↦ hx
      ((_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk E x).mpr h)
  exact (finiteLocallyFreeRank_eq_finrank_stalk E x).trans
    (@Module.finrank_zero_of_subsingleton _ _ _ _
      (LocallyFreeRank.instModuleStalkF X.toTopCat X.sheaf (toRingSheafModule E) x) _ _)

end AlgebraicGeometry.Scheme.Modules

end
