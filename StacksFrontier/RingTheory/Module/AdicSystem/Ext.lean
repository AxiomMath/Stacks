module

public import StacksFrontier.RingTheory.Module.AdicSystem.Ext.DelayedIso
public import StacksFrontier.RingTheory.Module.AdicSystem.Ext.Comparison
public import StacksFrontier.RingTheory.Module.AdicSystem.Ext.Counterexample
public import StacksFrontier.RingTheory.Module.AdicSystem.Ext.AdicComparison
public import StacksFrontier.RingTheory.Module.AdicSystem.Ext.FlatBaseChange

/-!
# Comparing Ext over a Noetherian ring with Ext over its adic quotients

Let `I` be an ideal of a Noetherian ring `A`, write `Aₙ = A ⧸ I ^ n`, and let `M`, `N` be
finite `A`-modules with reductions `Mₙ`, `Nₙ`.  This file compares the two inverse systems
`n ↦ Ext^i_A(M, N) ⧸ I ^ n Ext^i_A(M, N)` and `n ↦ Ext^i_{Aₙ}(Mₙ, Nₙ)`.  They are *not*
isomorphic as inverse systems, but they are isomorphic in the category of systems with
delayed morphisms of tag 0EGW, i.e. after allowing a uniform shift; an explicit example
shows the shift cannot be removed.  Over a flat base change the comparison becomes an
honest isomorphism on inverse limits.

## Main results

* `Stacks.AdicSystem.ExtDelayedIso.extAdicQuotientSystem_iso_extOfAdicQuotientsSystem`: the system
  of adic
  quotients of `Ext^i_A(M, N)` and the system of `Ext^i_{Aₙ}(Mₙ, Nₙ)` are isomorphic in the
  delayed-morphism category of tag 0EGW.
* `Stacks.AdicSystem.ExtComparison.exists_eventually_extOfAdicQuotients_comparison`: the explicit
  content of that
  isomorphism — powers `I ^ c` and `I ^ d` such that for `m ≫ n ≫ 0` the canonical maps
  between the two levels have kernel and cokernel annihilated by `I ^ d`.  The source states
  this with a single exponent; two are needed, and the caveat is recorded in the statement.
* `Stacks.AdicSystem.ExtCounterexample.extTwo_not_preserved_by_adicQuotients`: for `A = k[[x, y]] ⧸
  (xy)` and
  `M = A ⧸ (y)`, the group `Ext^2_A(M, M)` is `k` while every finite-level `Ext^2_{Aₙ}` group
  vanishes.  So no delay-free comparison exists.
* `Stacks.AdicSystem.ExtFlatBaseChange.limit_ext_quotient_iso_limit_ext_baseChange`: for a flat map
  `A → B` of
  Noetherian rings and finite `B`-modules `M`, `N` with `M` flat over `A`, the reduction maps
  from the adic quotients of `Ext_B(M, N)` to the Ext groups over `B ⧸ I ^ n B` are
  compatible with all transition maps and an isomorphism on inverse limits.

## Implementation notes

The systems of tag 0EGW are indexed by positive integers, so the Ext systems are formed on
`ℕ+`; the comparison morphisms are the `HomRepresentative`s of that file.  Ext groups are
`DerivedCategory.Ext` in `ModuleCat`, and the change-of-rings identification is the one
supplied by 09BB for `Hom` and by dimension shifting in higher degrees.  Tag 0EH2 works with
`MvPowerSeries (Fin 2) k` and the periodic resolution of `A ⧸ (y)`.

## References

* [Stacks Project, Tag 0EGY](https://stacks.math.columbia.edu/tag/0EGY)
* [Stacks Project, Tag 0EGZ](https://stacks.math.columbia.edu/tag/0EGZ)
* [Stacks Project, Tag 0EH2](https://stacks.math.columbia.edu/tag/0EH2)
* [Stacks Project, Tag 0EH0](https://stacks.math.columbia.edu/tag/0EH0)
-/
