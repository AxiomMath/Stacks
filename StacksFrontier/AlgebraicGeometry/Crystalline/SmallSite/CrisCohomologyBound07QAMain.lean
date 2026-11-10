module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCover07Q9Main
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisCohomologyBound07QAModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUnitMonoRings07QA

/-!
# Kernel and cokernel of crystalline pullback along an iterated `α_p`-cover

Let `p` be a prime, `(S, I, γ)` a divided power scheme over `ℤ_(p)` with `p ∈ I`, `S₀ = V(I)`,
`f : X' ⟶ X` an iterated `α_p`-cover of schemes over `S₀`, `ℱ` a crystal in quasi-coherent
modules on `Cris(X/S)` and `ℱ' = f_cris^*ℱ`. [Stacks, Tag 07QA] says that, when `f` has constant
degree `q`,

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`

has kernel and cokernel annihilated by `q^{i + 1}`.

## Main results

* `annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`: under the
  assumptions of [Stacks, Tag 07Q9], the kernel and the cokernel of `f^*` on `H^i` are
  annihilated by `q^{i + 1}`.
* `annihilated_ker_coker_crisModuleCohomologyMap_of_annihilation07Q9`: for an iterated
  `α_p`-cover and any `q` annihilating the cohomology sheaves of the cone of the comparison map of
  [Stacks, Tag 07Q9], the kernel and the cokernel of `f^*` on `H^i` are annihilated by
  `q^{i + 1}`.

## References

* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (T : GlobalCrystallineSituation.{u}) {X' : Scheme.{u}} (f : X' ⟶ T.X)

/-- For `f : X' ⟶ X` an iterated `α_p`-cover, `ℱ` a crystal in quasi-coherent modules on
`Cris(X/S)` and `q` such that the cohomology sheaves of the cone of
`Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}f_cris^*ℱ` are annihilated by `q`, the kernel and the
cokernel of `f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), f_cris^*ℱ)` are annihilated by
`q^{i + 1}`. -/
theorem annihilated_ker_coker_crisModuleCohomologyMap_of_annihilation07Q9
    (hf : IsIteratedAlphaPCover T.p f) (F : SheafOfModules.{u} (structureSheaf T))
    (hF : IsQuasiCoherentCrystal T F) (q : ℕ)
    [HasDerivedCategory.{w} (Sheaf (smallTopology (overSituation T f)) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w} (Sheaf (smallTopology T) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology (overSituation T f)) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology T) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
    (hann : Annihilation07Q9 T q (moduleComparison07Q9 (overSituation T f) T (𝟙 T.S) f
      (overSituation_compat T f) ((moduleULift T).obj F))) (i : ℕ) :
    (∀ x, crisModuleCohomologyMap (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f)
        ((moduleULift T).obj F) i x = 0 → ((q : ℤ) ^ (i + 1)) • x = 0) ∧
      ∀ y, ∃ x, ((q : ℤ) ^ (i + 1)) • y =
        crisModuleCohomologyMap (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f)
          ((moduleULift T).obj F) i x :=
  ⟨fun x hx => pow_smul_eq_zero_of_crisModuleCohomologyMap_eq_zero _ _ _ _ _ q i _ hann x hx,
    fun y => exists_crisModuleCohomologyMap_eq_pow_smul _ _ _ _ _ q i _ hann
      ((mono_homologyMap_moduleComparison07Q9_iff _ _ _ _ _ _).2
        (mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover T f hf F hF)) y⟩

/-- Let `p` be a prime and `(S, I, γ)` a divided power scheme over `ℤ_(p)` (the prime, the
`ℤ_(p)`-structure of the base and the local nilpotence of `p` on `X` are part of the situation
`T`), `S₀ = V(I)`.  Let `f : X' ⟶ X` be an iterated `α_p`-cover of
schemes over `S₀` of constant degree `q`, `ℱ` a crystal in quasi-coherent modules on `Cris(X/S)`
and `ℱ' = f_cris^*ℱ`.  Then the kernel and the cokernel of

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`

are annihilated by `q^{i + 1}`: every class killed by `f^*` is killed by `q^{i + 1}`, and
`q^{i + 1}` times every class of `H^i(Cris(X'/S), ℱ')` lies in the image of `f^*`. -/
@[stacks 07QA "f^* : H^i(Cris(X/S), F) → H^i(Cris(X'/S), F') has kernel and cokernel \
annihilated by q^(i+1)"]
theorem annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover
    (q : ℕ) (hf : IsIteratedAlphaPCover T.p f) (hq : HasConstantDegree f q)
    (F : SheafOfModules.{u} (structureSheaf T)) (hF : IsQuasiCoherentCrystal T F)
    [HasDerivedCategory.{w} (Sheaf (smallTopology (overSituation T f)) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w} (Sheaf (smallTopology T) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology (overSituation T f)) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology T) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}] (i : ℕ) :
    (∀ x, crisModuleCohomologyMap (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f)
        ((moduleULift T).obj F) i x = 0 → ((q : ℤ) ^ (i + 1)) • x = 0) ∧
      ∀ y, ∃ x, ((q : ℤ) ^ (i + 1)) • y =
        crisModuleCohomologyMap (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f)
          ((moduleULift T).obj F) i x :=
  annihilated_ker_coker_crisModuleCohomologyMap_of_annihilation07Q9 T f hf F hF q
    (annihilation07Q9_of_isIteratedAlphaPCover T f hf hq F hF) i

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
