module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
import StacksCore.Tactic.StacksAttribute

/-!
# Existence and boundedness of the derived upper shriek

Let `f : X ⟶ Y` be a separated morphism of finite type between quasi-compact and
quasi-separated schemes, let `j : X ⟶ Xbar` be a compactification of `f` with proper structure
morphism `fbar : Xbar ⟶ Y`, and let `Λ` be a torsion ring. The higher direct images along `fbar`
vanish in high degrees: the fibres of `fbar` have dimension bounded by some `m`
([Stacks, Tag 0A3V]), so `R^q fbar_* F = 0` for `q > 2m` and every torsion abelian sheaf `F`
([Stacks, Tag 095U]). Hence `Rf_!` has a right adjoint `Rf^!`, and `Rf^!` sends bounded below
complexes to bounded below complexes.

## Main results

* `exists_isZero_rightDerived_etaleAbelianDirectImage_toBase`: the higher direct images along
  `fbar` of torsion abelian sheaves vanish in high degrees.
* `isLeftAdjoint_derivedLowerShriekUnbounded`: [Stacks, Tag 0G2C], `Rf_!` has a right adjoint
  `Rf^!`.
* `exists_isZero_homology_derivedUpperShriek_obj`: [Stacks, Tag 0GLA], `Rf^!` sends
  `D^+(Y_étale, Λ)` into `D^+(X_étale, Λ)`, with a uniform bound `N`.

## Implementation notes

`Rf^!` is `CategoryTheory.Functor.rightAdjoint` of
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded f j Λ`, for the compactification `j` used
to define `Rf_!`; the statements hold for every compactification. A ring is torsion exactly when
`n = 0` in it for some `n ≥ 1`, since then `1` is torsion; this is how the hypothesis is stated.
The integer `N` is twice a bound for the dimensions of the fibres of `fbar`.

## References

* [Stacks Project, Tag 0GLA](https://stacks.math.columbia.edu/tag/0GLA)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.EtaleCohomology.DerivedUpperShriek

open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)

/-- **The higher direct images along the proper structure morphism of a compactification vanish
in high degrees**: for `Y` quasi-compact there is `d` with `R^q fbar_* G = 0` for `q > d` and
every torsion abelian sheaf `G` on `Xbar_étale` ([Stacks, Tags 0A3V and 095U]). -/
theorem exists_isZero_rightDerived_etaleAbelianDirectImage_toBase {X Y : Scheme.{u}}
    {f : X ⟶ Y} [CompactSpace Y] (j : CompactificationOf (Over.mk f)) :
    ∃ d : ℕ, ∀ G : Sheaf j.space.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty j.space.smallEtaleTopology G → ∀ q : ℕ, d < q →
        IsZero (((etaleAbelianDirectImage.{u, u + 1} j.toBase).rightDerived q).obj G) := by
  have : IsProper j.toBase := j.property.2
  obtain ⟨m, hm⟩ := exists_topologicalKrullDim_fiber_le j.toBase
  exact ⟨2 * m, fun G hG q hq ↦
    isZero_rightDerived_etaleAbelianDirectImage_of_isProper j.toBase m hm G hG q hq⟩

include hn hΛ in
/-- **[Stacks, Tag 0G2C].** Let `f : X ⟶ Y` be a morphism of schemes with `Y` quasi-compact
(for instance a separated morphism of finite type between quasi-compact and quasi-separated
schemes), let `j` be a compactification of `f` and let `Λ` be a torsion ring, that is, `n = 0`
in `Λ` for some `n ≥ 1`. Then the derived lower shriek
`Rf_! = R(fbar)_* ∘ j_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` has a right adjoint `Rf^!`. -/
theorem isLeftAdjoint_derivedLowerShriekUnbounded {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] (j : CompactificationOf (Over.mk f)) :
    (derivedLowerShriekUnbounded.{u, 0} f j Λ).IsLeftAdjoint := by
  obtain ⟨d, hd⟩ := exists_isZero_rightDerived_etaleAbelianDirectImage_toBase j
  exact isLeftAdjoint_derivedLowerShriekUnbounded_of_isZero_rightDerived Λ f j (d + 1)
    fun q hq F ↦ isZero_rightDerived_etaleModuleDirectImage_of_natCast_eq_zero Λ n hn hΛ j.toBase
      d hd q (by lia) F

include hn hΛ in
/-- Let `f : X ⟶ Y` be a separated morphism of finite type between quasi-compact and
quasi-separated schemes, let `j` be a compactification of `f`, and let `Λ` be a torsion ring
(`n = 0` in `Λ` for some `n ≥ 1`). The functor `Rf^!`, the right adjoint of
`Rf_! = R(fbar)_* ∘ j_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` of [Stacks, Tag 0G2C], sends
`D^+(Y_étale, Λ)` into `D^+(X_étale, Λ)`. More precisely, there is an integer `N ≥ 0` such that
if `K ∈ D(Y_étale, Λ)` has `H^i(K) = 0` for `i < a`, then `H^i(Rf^!K) = 0` for `i < a - N`. -/
@[stacks 0GLA]
theorem exists_isZero_homology_derivedUpperShriek_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (j : CompactificationOf (Over.mk f)) :
    letI := isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f j
    (∀ K : DerivedCategory (EtaleModules.{u, 0} Λ Y),
      (∃ a : ℤ, ∀ i < a, IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) →
      ∃ b : ℤ, ∀ i < b, IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((derivedLowerShriekUnbounded.{u, 0} f j Λ).rightAdjoint.obj K))) ∧
    ∃ N : ℕ, ∀ (K : DerivedCategory (EtaleModules.{u, 0} Λ Y)) (a : ℤ),
      (∀ i < a, IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) →
      ∀ i < a - N, IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((derivedLowerShriekUnbounded.{u, 0} f j Λ).rightAdjoint.obj K)) := by
  let := isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f j
  obtain ⟨d, hd⟩ := exists_isZero_rightDerived_etaleAbelianDirectImage_toBase j
  have key : ∀ (K : DerivedCategory (EtaleModules.{u, 0} Λ Y)) (a : ℤ),
      (∀ i < a, IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) →
      ∀ i < a - d, IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((derivedLowerShriekUnbounded.{u, 0} f j Λ).rightAdjoint.obj K)) := by
    intro K a hK i hi
    exact (DerivedCategory.isGE_iff _ _).1 (isGE_obj_of_derivedLowerShriekUnbounded_adjunction Λ f
      j (d + 1) (isZero_rightDerived_etaleModuleDirectImage_of_natCast_eq_zero Λ n hn hΛ j.toBase
        d hd (d + 1) (by lia)) (Adjunction.ofIsLeftAdjoint _) K a
      ((DerivedCategory.isGE_iff K a).2 hK)) i (by push_cast at hi ⊢; lia)
  exact ⟨fun K ⟨a, ha⟩ ↦ ⟨a - d, key K a ha⟩, d, key⟩

end Stacks.EtaleCohomology.DerivedUpperShriek
