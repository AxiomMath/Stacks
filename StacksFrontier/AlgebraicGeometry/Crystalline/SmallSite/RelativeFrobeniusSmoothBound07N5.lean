module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusAlphaPCoverSmooth
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCover07Q9LocalDegree
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCoverRelativeFrobenius07QB
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisCohomologyBound07QAMain

/-!
# The bound of [Stacks, Tag 07QB] for `X ⟶ S₀` smooth of locally bounded relative dimension

For `X ⟶ S₀` smooth with `X` quasi-compact, there is `D` such that for every crystal in
quasi-coherent modules `𝒢` on `Cris(X^{(1)}/S)` and every `i`, the kernel and the cokernel of the
pullback `F_{X/S₀}^*` along the relative Frobenius on `H^i` are annihilated by `p^{D(i+1)}`. This
is the bound of [Stacks, Tag 07QB] without the assumption that `X ⟶ S₀` has a fixed relative
dimension.

## Main results

* `exists_bound_crisModuleCohomologyMap_relativeFrobeniusToTwist_of_smooth` — **for `X ⟶ S₀`
  smooth with `X` quasi-compact there is `D` such that for every crystal in quasi-coherent
  modules `𝒢` on `Cris(X^{(1)}/S)` and every `i`, the kernel and the cokernel of
  `F_{X/S₀}^* : H^i(Cris(X^{(1)}/S), 𝒢) ⟶ H^i(Cris(X/S), F_{X/S₀, cris}^*𝒢)` are annihilated by
  `p^{D(i+1)}`.**

## References

* [Stacks Project, Lemma 60.26.5, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (T : GlobalCrystallineSituation.{u})
  (hp : (T.p : Γ(T.S.scheme, ⊤)) ∈ T.S.ideal.obj (Opposite.op ⊤))
  [HasDerivedCategory.{w} (Sheaf (smallTopology T) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (smallTopology (T.frobeniusTwistSituation hp)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology T) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (opensTopology (T.frobeniusTwistSituation hp)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **The bound of [Stacks, Tag 07QB] for `X ⟶ S₀` smooth, `X` quasi-compact.**  There is `D`
such that for every crystal in quasi-coherent modules `𝒢` on `Cris(X^{(1)}/S)` and every `i`,
the map `F_{X/S₀}^* : H^i(Cris(X^{(1)}/S), 𝒢) ⟶ H^i(Cris(X/S), F_{X/S₀, cris}^*𝒢)` has kernel
and cokernel annihilated by `p^{D(i+1)}`. -/
theorem exists_bound_crisModuleCohomologyMap_relativeFrobeniusToTwist_of_smooth
    (hsmooth : Smooth T.toClosedFiber) (hcompact : CompactSpace T.X) :
    ∃ D : ℕ, ∀ (G : SheafOfModules.{u} (structureSheaf (T.frobeniusTwistSituation hp))),
      IsQuasiCoherentCrystal (T.frobeniusTwistSituation hp) G → ∀ i : ℕ,
        ((T.p : ℤ) ^ (D * (i + 1))) • 𝟙 (kernel (crisModuleCohomologyMap T
            (T.frobeniusTwistSituation hp) (𝟙 T.S) (T.relativeFrobeniusToTwist hp)
            (T.toClosedFiber_comp_closedFiberMap_id hp)
            ((moduleULift (T.frobeniusTwistSituation hp)).obj G) i)) = 0 ∧
          ((T.p : ℤ) ^ (D * (i + 1))) • 𝟙 (cokernel (crisModuleCohomologyMap T
            (T.frobeniusTwistSituation hp) (𝟙 T.S) (T.relativeFrobeniusToTwist hp)
            (T.toClosedFiber_comp_closedFiberMap_id hp)
            ((moduleULift (T.frobeniusTwistSituation hp)).obj G) i)) = 0 := by
  obtain ⟨hcov, D, hD⟩ := T.relativeFrobeniusToTwist_isIteratedAlphaPCover_localDegree hp
  refine ⟨D, fun G hG i ↦ ?_⟩
  obtain ⟨hk, hc⟩ := crisModuleCohomologyMap_bound_congr
    ((moduleULift (T.frobeniusTwistSituation hp)).obj G) (((T.p ^ D : ℕ) : ℤ) ^ (i + 1)) i
    (overSituation_relativeFrobeniusToTwist_eq T hp) (𝟙 T.S) (T.relativeFrobeniusToTwist hp)
    (T.toClosedFiber_comp_closedFiberMap_id hp) (overSituation_compat _ _)
    (annihilated_ker_coker_crisModuleCohomologyMap_of_annihilation07Q9
      (T.frobeniusTwistSituation hp) (T.relativeFrobeniusToTwist hp) hcov G hG (T.p ^ D)
      (annihilation07Q9_of_isIteratedAlphaPCover_localDegree (T.frobeniusTwistSituation hp)
        (T.relativeFrobeniusToTwist hp) hp hcov D hD G hG) i)
  rw [natCast_pow_pow_succ] at hk hc
  exact ⟨zsmul_id_kernel_eq_zero _ _ hk, zsmul_id_cokernel_eq_zero _ _ hc⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
