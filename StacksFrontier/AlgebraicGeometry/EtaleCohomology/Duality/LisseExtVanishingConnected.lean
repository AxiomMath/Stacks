module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseCohomologicalDimension

/-!
# `Ext^q(F, G) = 0` for `F` lisse, from `H^q = 0` on finite étale covers

Let `X` be a connected scheme, `p` a prime and `F` a finite type locally constant sheaf of
`ℤ/p`-modules on `X_étale`. If `Ext^q(ℤ/p_T, K) = H^q(T, K)` vanishes for every finite étale
`T → X` and every sheaf `K` of `ℤ/p`-modules on `T`, then `Ext^q(F, G) = 0` for every sheaf `G` of
`ℤ/p`-modules on `X`.

This is how the vanishing of `Ext^q(F, G)` for lisse `F` (an input of the fibration step of
Poincaré duality, `Stacks.EtaleCohomology.CohomologicalDimensionInput`) reduces to the
cohomological dimension of the covers, with no internal `𝓗om`: by Tag 0A3R there is a connected
finite étale `π : T → X` of degree `δ` prime to `p` with `π⁻¹F` a successive extension of copies of
`ℤ/p_T`; `F` is a direct summand of `π_* π⁻¹F` (Tag 03SH,
`Stacks.EtaleCohomology.exists_comp_eq_id_directImage_inverseImage`); `π_*` is left adjoint to
`π⁻¹`, so `Ext^q_X(π_* π⁻¹F, G) = Ext^q_T(π⁻¹F, π⁻¹G)`
(`Stacks.EtaleCohomology.extDirectImageLeftAddEquiv`); and the long exact sequences of the
filtration bound this by `Ext^q_T(ℤ/p_T, π⁻¹G) = 0`.

## Main results

* `Stacks.EtaleCohomology.subsingleton_ext_of_relSeries_constantRankOneStep`: `Ext^q(G, K) = 0`
  for a successive extension `G` of copies of `ℤ/p` once `Ext^q(ℤ/p, K) = 0`.
* `Stacks.EtaleCohomology.subsingleton_ext_of_isFiniteTypeLocallyConstant_of_connectedSpace`:
  the reduction above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {p : ℕ} [Fact p.Prime]

/-- **`Ext^q` out of a successive extension of copies of `ℤ/p`.** If `Ext^q(ℤ/p_T, K) = 0`, then
`Ext^q(G, K) = 0` for every sheaf `G` with a finite filtration from `0` whose successive quotients
are `ℤ/p_T`: the long exact sequence of `Ext^q(-, K)` along each step. -/
theorem subsingleton_ext_of_relSeries_constantRankOneStep {T : Scheme.{u}} (q : ℕ)
    (K : EtaleModules.{u, 0} (ZMod p) T)
    (hΛ : Subsingleton (Ext (unitSheaf (X := T) p) K q))
    (G : EtaleModules.{u, 0} (ZMod p) T) (Xs : RelSeries (ConstantRankOneStep.{0} p G))
    (hhead : IsZero (Subobject.underlying.obj Xs.head)) (hlast : IsIso Xs.last.arrow) :
    Subsingleton (Ext G K q) := by
  have key : ∀ j : Fin (Xs.length + 1),
      Subsingleton (Ext (Subobject.underlying.obj (Xs j)) K q) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      exact subsingleton_ext_of_comp_eq_id (0 : _ ⟶ unitSheaf (X := T) p) 0
        (hhead.eq_of_src _ _) _ hΛ
    | succ j ih =>
      obtain ⟨hle, ⟨e⟩⟩ := Xs.step j
      let S := ShortComplex.mk (Subobject.ofLE _ _ hle) (cokernel.π (Subobject.ofLE _ _ hle))
        (cokernel.condition _)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
      exact Ext.subsingleton_ext_left_X₂_of_shortExact hS _ ih
        (AdequateFunctor.subsingleton_ext_of_iso_left e.symm q hΛ)
  exact AdequateFunctor.subsingleton_ext_of_iso_left (asIso Xs.last.arrow) q (key (Fin.last _))

/-- **`Ext^q(F, G) = 0` for `F` lisse, from the vanishing of `H^q` on finite étale covers.** Let
`X` be connected and `F` a finite type locally constant sheaf of `ℤ/p`-modules on `X_étale`. If
`Ext^q(ℤ/p_T, K) = 0` for every finite étale `T → X` and every sheaf `K` of `ℤ/p`-modules on `T`,
then `Ext^q(F, G) = 0` for every sheaf `G` of `ℤ/p`-modules on `X`. -/
theorem subsingleton_ext_of_isFiniteTypeLocallyConstant_of_connectedSpace {X : Scheme.{u}}
    [ConnectedSpace X] (q : ℕ)
    (hvan : ∀ (T : Scheme.{u}) (π : T ⟶ X) [IsFinite π] [Etale π]
      (K : EtaleModules.{u, 0} (ZMod p) T), Subsingleton (Ext (unitSheaf (X := T) p) K q))
    (F : EtaleModules.{u, 0} (ZMod p) X)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod p) X.smallEtaleTopology F)
    (G : EtaleModules.{u, 0} (ZMod p) X) : Subsingleton (Ext F G q) := by
  obtain ⟨T, π, δ, hfin, het, -, hrank, hδ, Xs, hhead, hlast⟩ :=
    exists_connected_primeToEll_finiteEtale_relSeries_constantRankOneStep Fact.out F hF
  have := hfin
  have := het
  have := hrank
  obtain ⟨i, r, hir⟩ := exists_comp_eq_id_directImage_inverseImage π δ hδ F
  refine subsingleton_ext_of_comp_eq_id i r hir _ ?_
  -- `Ext^q_X(π_* M, G) = Ext^q_T(M, π⁻¹ G)`
  suffices hT : Subsingleton (Ext ((etaleModuleInverseImage.{u, 0} (ZMod p) π).obj F)
      ((etaleModuleInverseImage.{u, 0} (ZMod p) π).obj G) q) from
    (extDirectImageLeftAddEquiv (ZMod p) π _ _ q).symm.toEquiv.subsingleton
  exact subsingleton_ext_of_relSeries_constantRankOneStep q _ (hvan T π _) _ Xs hhead hlast

end Stacks.EtaleCohomology

end
