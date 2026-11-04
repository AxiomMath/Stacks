module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCoverFrobeniusTwistSituation
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisCohomologyBound07QAMain

/-!
# [Stacks, Lemma 60.26.5, Tag 07QB]: the relative Frobenius on crystalline cohomology

In the global crystalline situation `X/S` of [Stacks, Tag 07MF] with `p` in the divided power
ideal, let `X^{(1)} = X ×_{S₀, F_{S₀}} S₀` and `F_{X/S₀} : X ⟶ X^{(1)}` the relative Frobenius.
[Stacks, Tag 07QB] says that for `X ⟶ S₀` smooth of relative dimension `d`, `F_{X/S₀}` is an
iterated `α_p`-cover of degree `p ^ d`, so that [Stacks, Tag 07Q9] and [Stacks, Tag 07QA] apply,
and in particular for `𝒢` a crystal in quasi-coherent modules on `Cris(X^{(1)}/S)` the map

`F_{X/S₀}^* : H^i(Cris(X^{(1)}/S), 𝒢) ⟶ H^i(Cris(X/S), F_{X/S₀, cris}^*𝒢)`

has kernel and cokernel annihilated by `p^{d(i + 1)}`.

The first sentence is
`Crystalline.GlobalCrystallineSituation.isIteratedAlphaPCoverOfDegree_relativeFrobeniusToTwist`.
[Stacks, Tag 07QA] is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`, stated
for a morphism `f : X' ⟶ X` over the situation `X'/S` whose structure morphism is `X' ⟶ X ⟶ S₀`
(`...SmallSite.overSituation`).  For `f = F_{X/S₀}` that situation is `X/S` itself
(`overSituation_relativeFrobeniusToTwist_eq`), so the bound transports to `X/S` along that equality
(`crisModuleCohomologyMap_bound_congr`), and `(p ^ d)^{i + 1} = p^{d(i + 1)}`.

## Main results

* `relativeFrobeniusToTwist_isIteratedAlphaPCover_cohomologyBound` — **[Stacks, Tag 07QB]**.
* `zsmul_id_kernel_cokernel_crisModuleCohomologyMap_relativeFrobeniusToTwist_of` — the bound of
  [Stacks, Tag 07QA] for `F_{X/S₀}` at `q = p ^ d` gives the annihilation of the kernel and the
  cokernel of `F_{X/S₀}^*` over `X/S`.
* `overSituation_relativeFrobeniusToTwist_eq` — `X` over `S₀` through `X^{(1)}` is `X/S`.
* `crisModuleCohomologyMap_bound_congr` — the element-wise bounds on `f^*` transport along an
  equality of source situations.
* `zsmul_id_kernel_eq_zero`, `zsmul_id_cokernel_eq_zero` — for a map of abelian groups, the
  element-wise bounds are the annihilation of the kernel and of the cokernel.

## References

* [Stacks Project, Lemma 60.26.5, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Kernels and cokernels of maps of abelian groups -/

section Objects

variable {A B : AddCommGrpCat.{u + 1}} (φ : A ⟶ B) (n : ℤ)

/-- **A map of abelian groups whose vanishing forces `n • x = 0` has kernel annihilated by
`n`.**  `ker(φ) ⟶ A` is a monomorphism and `n` times it kills every element of the kernel. -/
theorem zsmul_id_kernel_eq_zero (h : ∀ x : A, φ x = 0 → n • x = 0) :
    n • 𝟙 (kernel φ) = 0 := by
  rw [← cancel_mono (kernel.ι φ)]
  simp only [Preadditive.zsmul_comp, Category.id_comp, zero_comp]
  ext k
  have hk : φ (kernel.ι φ k) = 0 := by simp
  simpa using h _ hk

/-- **A map of abelian groups `n` times whose target is in its image has cokernel annihilated by
`n`.**  `B ⟶ coker(φ)` is an epimorphism and `n` times it kills every element of `B`. -/
theorem zsmul_id_cokernel_eq_zero (h : ∀ y : B, ∃ x : A, n • y = φ x) :
    n • 𝟙 (cokernel φ) = 0 := by
  rw [← cancel_epi (cokernel.π φ)]
  simp only [Preadditive.comp_zsmul, Category.comp_id, comp_zero]
  ext y
  obtain ⟨x, hx⟩ := h y
  have hc : cokernel.π φ (φ x) = 0 := by simp
  simpa [← hx] using hc

end Objects

/-! ### Transport along an equality of source situations -/

/-- **The element-wise bounds on `f^*` transport along an equality of source situations.**  For
`e : S₁ = S₂` and a morphism `(fS, fX)` of situations out of `S₂`, the bounds for the morphism
out of `S₁` read through `e` give the bounds for `(fS, fX)`.  The proof is `subst e`. -/
theorem crisModuleCohomologyMap_bound_congr {S' : GlobalCrystallineSituation.{u}}
    [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
    (F : ModuleSheaf S') (n : ℤ) (i : ℕ) {S₁ S₂ : GlobalCrystallineSituation.{u}} (e : S₁ = S₂)
    (fS : S₂.S ⟶ S'.S) (fX : S₂.X ⟶ S'.X)
    (hf : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
    [HasDerivedCategory.{w} (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S₂) AddCommGrpCat.{u + 1})]
    (hf₁ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap
        (cast (congrArg (fun S : GlobalCrystallineSituation.{u} => S.S ⟶ S'.S) e.symm) fS) =
      cast (congrArg (fun S : GlobalCrystallineSituation.{u} => S.X ⟶ S'.X) e.symm) fX ≫
        S'.toClosedFiber)
    (h : ∀ [HasDerivedCategory.{w} (Sheaf (smallTopology S₁) AddCommGrpCat.{u + 1})]
      [HasDerivedCategory.{w'} (Sheaf (opensTopology S₁) AddCommGrpCat.{u + 1})],
      (∀ x, crisModuleCohomologyMap S₁ S'
          (cast (congrArg (fun S : GlobalCrystallineSituation.{u} => S.S ⟶ S'.S) e.symm) fS)
          (cast (congrArg (fun S : GlobalCrystallineSituation.{u} => S.X ⟶ S'.X) e.symm) fX)
          hf₁ F i x = 0 → n • x = 0) ∧
        ∀ y, ∃ x, n • y = crisModuleCohomologyMap S₁ S'
          (cast (congrArg (fun S : GlobalCrystallineSituation.{u} => S.S ⟶ S'.S) e.symm) fS)
          (cast (congrArg (fun S : GlobalCrystallineSituation.{u} => S.X ⟶ S'.X) e.symm) fX)
          hf₁ F i x) :
    (∀ x, crisModuleCohomologyMap S₂ S' fS fX hf F i x = 0 → n • x = 0) ∧
      ∀ y, ∃ x, n • y = crisModuleCohomologyMap S₂ S' fS fX hf F i x := by
  subst e
  exact h

/-! ### The relative Frobenius -/

variable (T : GlobalCrystallineSituation.{u})
  (hp : (T.p : Γ(T.S.scheme, ⊤)) ∈ T.S.ideal.obj (Opposite.op ⊤))

/-- **`X` over `S₀` through `X^{(1)}` is the situation `X/S`.**  The situation
`...SmallSite.overSituation` of `F_{X/S₀} : X ⟶ X^{(1)}` has the structure morphism
`X ⟶ X^{(1)} ⟶ S₀`, which is the structure morphism of `X` because the relative Frobenius is a
morphism over `S₀`; every other datum is that of `X/S` on the nose. -/
theorem overSituation_relativeFrobeniusToTwist_eq :
    overSituation (T.frobeniusTwistSituation hp) (T.relativeFrobeniusToTwist hp) = T := by
  have h := T.relativeFrobeniusToTwist_comp_toClosedFiber hp
  cases T
  unfold overSituation
  congr 1

/-- The exponent of [Stacks, Tag 07QB] is the exponent of [Stacks, Tag 07QA] at `q = p ^ d`. -/
theorem natCast_pow_pow_succ (d i : ℕ) :
    (((T.p ^ d : ℕ) : ℤ)) ^ (i + 1) = (T.p : ℤ) ^ (d * (i + 1)) := by
  push_cast
  rw [← pow_mul]

variable [HasDerivedCategory.{w} (Sheaf (smallTopology T) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (smallTopology (T.frobeniusTwistSituation hp)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology T) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (opensTopology (T.frobeniusTwistSituation hp)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **The bound of [Stacks, Tag 07QA] for `F_{X/S₀}` at `q = p ^ d`, read on `X/S`.**  The bound
on `F_{X/S₀}^* : H^i(Cris(X^{(1)}/S), 𝒢) ⟶ H^i(Cris(X/S), F_{X/S₀, cris}^*𝒢)` over the situation
of `X` through `X^{(1)}`, with exponent `(p ^ d)^{i + 1}`, gives the annihilation of the kernel and
of the cokernel of the same map over `X/S` by `p^{d(i + 1)}`. -/
theorem zsmul_id_kernel_cokernel_crisModuleCohomologyMap_relativeFrobeniusToTwist_of (d i : ℕ)
    (G : ModuleSheaf (T.frobeniusTwistSituation hp))
    (h : ∀ [HasDerivedCategory.{w} (Sheaf (smallTopology (overSituation
        (T.frobeniusTwistSituation hp) (T.relativeFrobeniusToTwist hp))) AddCommGrpCat.{u + 1})]
      [HasDerivedCategory.{w'} (Sheaf (opensTopology (overSituation
        (T.frobeniusTwistSituation hp) (T.relativeFrobeniusToTwist hp))) AddCommGrpCat.{u + 1})],
      (∀ x, crisModuleCohomologyMap (overSituation (T.frobeniusTwistSituation hp)
          (T.relativeFrobeniusToTwist hp)) (T.frobeniusTwistSituation hp) (𝟙 T.S)
          (T.relativeFrobeniusToTwist hp) (overSituation_compat _ _) G i x = 0 →
            (((T.p ^ d : ℕ) : ℤ) ^ (i + 1)) • x = 0) ∧
        ∀ y, ∃ x, (((T.p ^ d : ℕ) : ℤ) ^ (i + 1)) • y =
          crisModuleCohomologyMap (overSituation (T.frobeniusTwistSituation hp)
            (T.relativeFrobeniusToTwist hp)) (T.frobeniusTwistSituation hp) (𝟙 T.S)
            (T.relativeFrobeniusToTwist hp) (overSituation_compat _ _) G i x) :
    ((T.p : ℤ) ^ (d * (i + 1))) • 𝟙 (kernel (crisModuleCohomologyMap T
        (T.frobeniusTwistSituation hp) (𝟙 T.S) (T.relativeFrobeniusToTwist hp)
        (T.toClosedFiber_comp_closedFiberMap_id hp) G i)) = 0 ∧
      ((T.p : ℤ) ^ (d * (i + 1))) • 𝟙 (cokernel (crisModuleCohomologyMap T
        (T.frobeniusTwistSituation hp) (𝟙 T.S) (T.relativeFrobeniusToTwist hp)
        (T.toClosedFiber_comp_closedFiberMap_id hp) G i)) = 0 := by
  obtain ⟨hk, hc⟩ := crisModuleCohomologyMap_bound_congr G _ i
    (overSituation_relativeFrobeniusToTwist_eq T hp) (𝟙 T.S) (T.relativeFrobeniusToTwist hp)
    (T.toClosedFiber_comp_closedFiberMap_id hp) (overSituation_compat _ _) h
  rw [natCast_pow_pow_succ] at hk hc
  exact ⟨zsmul_id_kernel_eq_zero _ _ hk, zsmul_id_cokernel_eq_zero _ _ hc⟩

/-- **[Stacks, Lemma 60.26.5, Tag 07QB].**  In the global crystalline situation `X/S` of
[Stacks, Tag 07MF] with `p` in the divided power ideal `I`, let `S₀ = V(I)`,
`X^{(1)} = X ×_{S₀, F_{S₀}} S₀` and `F_{X/S₀} : X ⟶ X^{(1)}` the relative Frobenius, and assume
that `X ⟶ S₀` is smooth of relative dimension `d`.  Then

* `F_{X/S₀}` is an iterated `α_p`-cover of degree `p ^ d`, and
* for every crystal in quasi-coherent modules `𝒢` on `Cris(X^{(1)}/S)` and every `i`, the map
  `F_{X/S₀}^* : H^i(Cris(X^{(1)}/S), 𝒢) ⟶ H^i(Cris(X/S), F_{X/S₀, cris}^*𝒢)` has kernel and
  cokernel annihilated by `p^{d(i + 1)}`.

The first assertion is
`Crystalline.GlobalCrystallineSituation.isIteratedAlphaPCoverOfDegree_relativeFrobeniusToTwist`.
The second is [Stacks, Lemma 60.26.4, Tag 07QA]
(`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`) applied to
`f = F_{X/S₀}` and `q = p ^ d`, whose two hypotheses on `f` are the first assertion, read on `X/S`
by `zsmul_id_kernel_cokernel_crisModuleCohomologyMap_relativeFrobeniusToTwist_of`.  The map is
`...SmallSite.crisModuleCohomologyMap` for the morphism `F_{X/S₀}` of situations over the
identity of `S`, and `F_{X/S₀, cris}^*` is the pullback `...SmallSite.crisModuleInverseImage` of
`𝒪`-modules; `𝒢` enters through `...SmallSite.moduleULift`, at the module universe of the
cohomology of `Cris(X^{(1)}/S)`. -/
@[stacks 07QB "for the global crystalline situation with p in I and X -> S_0 smooth of relative \
dimension d: F_{X/S_0} : X -> X^{(1)} is an iterated alpha_p-cover of degree p ^ d, and for every \
crystal in quasi-coherent modules G on Cris(X^{(1)}/S) and every i the map \
F_{X/S_0}^* : H^i(Cris(X^{(1)}/S), G) -> H^i(Cris(X/S), F_{X/S_0,cris}^* G) has kernel and \
cokernel annihilated by p^{d(i+1)}"]
theorem relativeFrobeniusToTwist_isIteratedAlphaPCover_cohomologyBound (d : ℕ)
    [SmoothOfRelativeDimension d T.toClosedFiber] :
    (IsIteratedAlphaPCover T.p (T.relativeFrobeniusToTwist hp) ∧
        HasConstantDegree (T.relativeFrobeniusToTwist hp) (T.p ^ d)) ∧
      ∀ (G : SheafOfModules.{u} (structureSheaf (T.frobeniusTwistSituation hp))),
        IsQuasiCoherentCrystal (T.frobeniusTwistSituation hp) G → ∀ i : ℕ,
          ((T.p : ℤ) ^ (d * (i + 1))) • 𝟙 (kernel (crisModuleCohomologyMap T
              (T.frobeniusTwistSituation hp) (𝟙 T.S) (T.relativeFrobeniusToTwist hp)
              (T.toClosedFiber_comp_closedFiberMap_id hp)
              ((moduleULift (T.frobeniusTwistSituation hp)).obj G) i)) = 0 ∧
            ((T.p : ℤ) ^ (d * (i + 1))) • 𝟙 (cokernel (crisModuleCohomologyMap T
              (T.frobeniusTwistSituation hp) (𝟙 T.S) (T.relativeFrobeniusToTwist hp)
              (T.toClosedFiber_comp_closedFiberMap_id hp)
              ((moduleULift (T.frobeniusTwistSituation hp)).obj G) i)) = 0 := by
  have hcov := T.isIteratedAlphaPCoverOfDegree_relativeFrobeniusToTwist hp d
  refine ⟨hcov, fun G hG i => ?_⟩
  exact zsmul_id_kernel_cokernel_crisModuleCohomologyMap_relativeFrobeniusToTwist_of T hp d i _
    (annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover
      (T.frobeniusTwistSituation hp) (T.relativeFrobeniusToTwist hp) hp (T.p ^ d) hcov.1 hcov.2
      G hG i)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
