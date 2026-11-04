module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalOfStratification
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StratifiedCrystalSections

/-!
# The crystal of a stratified module has that stratification

Let `(M, E)` be a `p`-adically complete stratified module over the system of [Stacks, Tag 07JN]
(`...SmallSite.wholeSpaceDescentSystem`), let `ℱ = ...SmallSite.stratCrystal E` be its crystal
and let `ι : lim_e Γ(T(0)_e, ℱ) ≃ M` be the identification `...SmallSite.stratLimitEquiv`.
This file proves that the stratification of `ℱ` in the sense of [Stacks, Lemma 60.17.3, Tag 07JG]
is `E`: written in the trivialisation of the first vertex `v₀ : T(1)_e ⟶ T(0)_e`, the restriction
of the section of `m` along the second vertex `v₁` is `E m`,

`crystalPointMap v₀ ((1 ⊗ ι⁻¹) (E m)) = v₁^* (ι⁻¹ m)_e`.

This is the half of [Stacks, Proposition 60.17.4, Tag 07JH] saying that the quasi-inverse
followed by the functor of [Stacks, Tag 07JG] gives back the stratified module.

## Main results

All names are in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `evalEquiv_stratSectionsEquiv_crysRestrict`: the restriction of the section of `m` along a
  pointing `h` evaluates at `h` to `1 ⊗ m`.
* `evalEquiv_stratSectionsEquiv_crystalPointMap`: the evaluation at `h` inverts
  `crystalPointMap h`, read through `ι`.
* `crystalPointMap_stratCrystal`: the crystal of `(M, E)` has the stratification `E`.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline.StratifiedDescent

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}
  [WholeSpacePresentation S hp] {M : Type u} [AddCommGroup M] [Module (envD S hp) M]
  (E : Stratification (wholeSpaceDescentSystem S hp) M)
  (hM : IsPAdicallyComplete S.p (envD S hp) M)

/-- **The restriction of the section of `m` along a pointing `h` evaluates at `h` to `1 ⊗ m`**:
for `h : A ⟶ T(0)_e`, the restriction along `h` of the component at the level `e` of the element
of the limit module corresponding to `m` is the descended section whose value at `h` is `1 ⊗ m`.
-/
theorem evalEquiv_stratSectionsEquiv_crysRestrict {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e) (m : M) :
    E.evalEquiv h (stratSectionsEquiv E A (crysRestrict (stratCrystal E).obj h.hom
      (wholeSpaceSectionsVal hp (stratCrystal E) ((stratLimitEquiv E hM).symm m) e))) =
      (1 : TwistedScalars _) ⊗ₜ[envD S hp] m := by
  refine (congrArg (E.evalEquiv h) (stratSectionsEquiv_restrict E h _)).trans ?_
  refine (E.evalEquiv_restrict' h (𝟙 _) h (Category.comp_id h) _).trans ?_
  refine (congrArg (twistMap _ _) (evalEquiv_stratLimitEquiv_symm E hM m e)).trans ?_
  exact twistMap_one_tmul _ _ m

/-- **The evaluation at a pointing inverts `crystalPointMap`**: for `h : A ⟶ T(0)_e` and
`z ∈ Γ(A, 𝒪) ⊗_D M`, the section `crystalPointMap h ((1 ⊗ ι⁻¹) z)` of the crystal of `(M, E)`
evaluates at `h` to `z`, `ι` being `...SmallSite.stratLimitEquiv`. -/
theorem evalEquiv_stratSectionsEquiv_crystalPointMap {A : AffineCrystallineThickening S} {e : ℕ}
    (h : A ⟶ (wholeSpaceDescentSystem S hp).T0 e)
    (z : TwistedScalars ((wholeSpaceDescentSystem S hp).ptRing h) ⊗[envD S hp] M) :
    E.evalEquiv h (stratSectionsEquiv E A (crystalPointMap hp (stratCrystal E) h.hom
      (LinearMap.lTensor _ (stratLimitEquiv E hM).symm.toLinearMap z))) = z := by
  let Φ : TwistedScalars ((wholeSpaceDescentSystem S hp).ptRing h) ⊗[envD S hp] M →+
      TwistedScalars ((wholeSpaceDescentSystem S hp).ptRing h) ⊗[envD S hp] M :=
    (E.evalEquiv h).toAddMonoidHom.comp ((stratSectionsEquiv E A).toAddMonoidHom.comp
      ((crystalPointMap hp (stratCrystal E) h.hom).toAddMonoidHom.comp
        (LinearMap.lTensor _ (stratLimitEquiv E hM).symm.toLinearMap).toAddMonoidHom))
  change Φ z = z
  induction z using TensorProduct.induction_on with
  | zero => exact map_zero Φ
  | tmul b m =>
    have hs : Φ (b ⊗ₜ m) = b.val • E.evalEquiv h (stratSectionsEquiv E A
        (crysRestrict (stratCrystal E).obj h.hom
          (wholeSpaceSectionsVal hp (stratCrystal E) ((stratLimitEquiv E hM).symm m) e))) :=
      (congrArg (E.evalEquiv h) ((stratSectionsEquiv E A).map_smul b.val _)).trans
        ((E.evalEquiv h).map_smul b.val _)
    rw [hs, evalEquiv_stratSectionsEquiv_crysRestrict E hM h m, TensorProduct.smul_tmul']
    congr 1
    exact mul_one b.val
  | add x y hx hy => rw [map_add, hx, hy]

/-- **The crystal of a stratified module has that stratification**: for a `p`-adically complete
stratified module `(M, E)`, `ι = ...SmallSite.stratLimitEquiv E hM` and `ℱ = stratCrystal E`, the
restriction of the section of `m` along the second vertex `v₁ : T(1)_e ⟶ T(0)_e`, written in the
trivialisation of the first vertex `v₀` by `crystalPointMap v₀`, is `E m`. -/
theorem crystalPointMap_stratCrystal (e : ℕ) (m : M) :
    crystalPointMap hp (stratCrystal E) ((wholeSpaceDescentSystem S hp).v e 0).hom
        (LinearMap.lTensor _ (stratLimitEquiv E hM).symm.toLinearMap (E.str e m)) =
      crysRestrict (stratCrystal E).obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp (stratCrystal E) ((stratLimitEquiv E hM).symm m) e) := by
  refine (stratSectionsEquiv E ((wholeSpaceDescentSystem S hp).T1 e)).injective
    ((E.evalEquiv ((wholeSpaceDescentSystem S hp).v e 0)).injective ?_)
  refine (evalEquiv_stratSectionsEquiv_crystalPointMap E hM _ _).trans ?_
  have h1 := evalEquiv_stratSectionsEquiv_crysRestrict E hM
    ((wholeSpaceDescentSystem S hp).v e 1) m
  have h3 := congrArg ((wholeSpaceDescentSystem S hp).comparison E.str (𝟙 _) _ _
    ((wholeSpaceDescentSystem S hp).map_comp_ptRing
      (Category.id_comp ((wholeSpaceDescentSystem S hp).v e 0)))
    ((wholeSpaceDescentSystem S hp).map_comp_ptRing
      (Category.id_comp ((wholeSpaceDescentSystem S hp).v e 1)))) h1
  refine Eq.trans ?_ (h3.symm.trans (E.comparison_evalEquiv (𝟙 _) _ _
    (Category.id_comp ((wholeSpaceDescentSystem S hp).v e 0))
    (Category.id_comp ((wholeSpaceDescentSystem S hp).v e 1)) _))
  rw [System.comparison_one_tmul, System.pullStrat_apply]
  exact (twistMap_eq_self _ (by rw [op_id, CategoryTheory.Functor.map_id]; rfl) _ _).symm

end Crystalline.GlobalCrystallineSituation.SmallSite

end
