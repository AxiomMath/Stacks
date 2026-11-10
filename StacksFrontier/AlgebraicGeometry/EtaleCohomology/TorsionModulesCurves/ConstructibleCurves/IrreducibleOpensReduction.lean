module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.Annihilator
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.DisjointIrreducibleOpens
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.DisjointOpensSum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FiniteCohomology
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.RestrictToDenseOpenCurve

/-!
# Reduction to extensions by zero from irreducible opens

Let `Λ` be a Noetherian ring, `k` an algebraically closed field, `X` a separated scheme of
finite type over `k` of dimension at most one and `ℱ` a constructible sheaf of `Λ`-modules on
`X_étale`. If `H^q(X, j_!(ℱ|_W))` is a finite `Λ`-module for every irreducible open `j : W ⟶ X`
on which `ℱ` is finite type and locally constant, then `H^q(X, ℱ)` is a finite `Λ`-module.

This is the second and third paragraph of the proof of [Stacks, Tag 0GJI]: choose a dense open
`U = U₁ ⨿ … ⨿ Uₙ` with irreducible `Uₐ` on which `ℱ` is finite type and locally constant
(`Stacks.EtaleCohomology.exists_disjoint_isIrreducible_opens_isFiniteTypeLocallyConstant`), pass
from `ℱ` to `j_!j^{-1}ℱ` by Lemma 0GJE
(`Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_iff_extensionByZero_of_dense`)
and split `j_!j^{-1}ℱ = ⨁ₐ j_{a!}(ℱ|_{Uₐ})`
(`Stacks.EtaleCohomology.isIso_biproductDesc_counit_etaleModuleExtensionByZero`).

## Main results

* `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_of_forall_isIrreducible_opens`
  — the reduction above.

## References

* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
* [Stacks Project, Tag 0GJE](https://stacks.math.columbia.edu/tag/0GJE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u r

namespace Stacks.EtaleCohomology.TorsionModules

attribute [local instance] Abelian.hasFiniteBiproducts

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- A finite direct sum of sheaves of `Λ`-modules on `X_étale` has finite cohomology in degree
`q` when every summand does. -/
theorem module_finite_etaleCohomology_biproduct {X : Scheme.{u}} {ι : Type} [Finite ι]
    (D : ι → EtaleModules.{u, r} Λ X) (q : ℕ)
    (hD : ∀ a, Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      (D a))) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj (⨁ D)) := by
  have := Fintype.ofFinite ι
  let := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
  let := HasDerivedCategory.standard (ModuleCat.{max (u + 1) r} Λ)
  let F := (etaleModuleGlobalSections.{u, r} Λ X).rightDerived q
  have : F.Additive := (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (etaleModuleGlobalSections.{u, r} Λ X)).additive q
  have := Functor.preservesFiniteBiproductsOfAdditive F
  let e : F.obj (⨁ D) ≅ ModuleCat.of Λ (∀ a, F.obj (D a)) :=
    F.mapBiproduct D ≪≫ ModuleCat.biproductIsoPi fun a => F.obj (D a)
  have : ∀ a, Module.Finite Λ (F.obj (D a)) := hD
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- **Reduction to extensions by zero from irreducible opens** (Stacks 0GJI, second and third
paragraphs of the proof). Let `Λ` be a Noetherian ring, `k` an algebraically closed field, `X` a
separated scheme of finite type over `k` of dimension at most one and `ℱ` a constructible sheaf of
`Λ`-modules on `X_étale`. Suppose that for every irreducible open `W ⊆ X` such that `ℱ|_W` is a
finite type, locally constant sheaf of `Λ`-modules, the modules `H^q(X, j_{W!}(ℱ|_W))` are finite.
Then `H^q(X, ℱ)` is a finite `Λ`-module. -/
theorem module_finite_cohomology_of_forall_isIrreducible_opens
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (hX : topologicalKrullDim X ≤ 1)
    (F : EtaleModules.{u, r} Λ X) (hF : IsConstructibleEtaleModule Λ F) (q : ℕ)
    (hpieces : ∀ W : X.Opens, IsIrreducible (W : Set X) →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
        W.toScheme.smallEtaleTopology Λ ((etaleModuleRestriction.{u, r} Λ W.ι).obj F) →
      Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
        ((etaleModuleExtensionByZero.{u, r} Λ W.ι).obj
          ((etaleModuleRestriction.{u, r} Λ W.ι).obj F)))) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj F) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  obtain ⟨n, W, hdisj, hdense, hW⟩ :=
    exists_disjoint_isIrreducible_opens_isFiniteTypeLocallyConstant Λ F hF
  let V : X.Opens := ⨆ a, W a
  have hV : (V : Set X) = ⋃ a, (W a : Set X) := TopologicalSpace.Opens.coe_iSup W
  have hrange : ∀ U : X.Opens, Set.range U.ι.base = (U : Set X) := fun U => U.range_ι
  -- Lemma 0GJE for the dense open `V`
  let B := BigEtaleSite.containing X
  have hXB : B.Contains X := BigEtaleSite.contains_containing X
  rw [module_finite_cohomology_iff_extensionByZero_of_dense B Λ (B.obj X hXB) π hX F hF V.ι
    (by rw [hrange, hV]; exact hdense) q]
  -- the decomposition of `j_! j^{-1} ℱ`
  set H := (etaleModuleExtensionByZero.{u, r} Λ V.ι).obj
    ((etaleModuleRestriction.{u, r} Λ V.ι).obj F)
  have hiso := isIso_biproductDesc_counit_etaleModuleExtensionByZero.{u, r} Λ
    (fun a => (W a).ι) V.ι (fun a b hab => by dsimp only; rw [hrange, hrange]; exact hdisj hab)
    (by simp only [hrange, hV]) ((etaleModuleRestriction.{u, r} Λ V.ι).obj F)
  let D := fun a => (etaleModuleExtensionByZero.{u, r} Λ (W a).ι).obj
    ((etaleModuleRestriction.{u, r} Λ (W a).ι).obj H)
  let e : ⨁ D ≅ H := @asIso _ _ _ _ _ hiso
  suffices hsum : Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      (⨁ D)) from
    Module.Finite.equiv (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).mapIso
      e).toLinearEquiv
  refine module_finite_etaleCohomology_biproduct Λ D q fun a => ?_
  -- on `Wₐ`, the restriction of `j_! j^{-1} ℱ` is the restriction of `ℱ`
  have hle : W a ≤ V := le_iSup W a
  have hc := isIso_etaleModuleRestriction_map_counit_of_factors.{u, r} Λ (W a).ι V.ι
    (X.homOfLE hle) (X.homOfLE_ι hle) F
  let e' : D a ≅ (etaleModuleExtensionByZero.{u, r} Λ (W a).ι).obj
      ((etaleModuleRestriction.{u, r} Λ (W a).ι).obj F) :=
    (etaleModuleExtensionByZero.{u, r} Λ (W a).ι).mapIso (asIso
      ((etaleModuleRestriction.{u, r} Λ (W a).ι).map
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ V.ι).counit.app F)))
  have := hpieces (W a) (hW a).1 (hW a).2
  exact Module.Finite.equiv
    (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).mapIso e').symm.toLinearEquiv

/-- **Reduction to locally constant sheaves of prime power torsion on irreducible opens**
(Stacks 0GJI, the whole proof except its last citation of Lemma 0GJH). Let `Λ` be a Noetherian
ring, `k` an algebraically closed field, `X` a separated scheme of finite type over `k` of
dimension at most one, `p` an integer and `ℱ` a constructible sheaf of `Λ`-modules on `X_étale`
which is torsion prime to `p`. Suppose that `H^q(X, j_{W!}𝒢)` is a finite `Λ`-module whenever
`W ⊆ X` is an irreducible open and `𝒢` is a finite type, locally constant sheaf of `Λ`-modules on
`W_étale` annihilated by `ℓⁿ` for a prime `ℓ` prime to `p` and `n > 0`. Then `H^q(X, ℱ)` is a
finite `Λ`-module.

A single integer prime to `p` kills `ℱ`
(`Stacks.EtaleCohomology.exists_nsmul_id_eq_zero_of_isConstructibleEtaleModule`); Lemma 0GJG
reduces to constructible sheaves killed by a power of a prime `ℓ` prime to `p`
(`Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_of_nsmul_id_eq_zero`), and those
are handled by `module_finite_cohomology_of_forall_isIrreducible_opens`. -/
theorem module_finite_cohomology_of_isTorsionPrimeTo_of_forall_isIrreducible_opens
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (hX : topologicalKrullDim X ≤ 1)
    (p : ℕ)
    (hpieces : ∀ W : X.Opens, IsIrreducible (W : Set X) → ∀ ℓ n : ℕ, ℓ.Prime → ℓ.Coprime p →
      0 < n → ∀ G : EtaleModules.{u, r} Λ W,
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
        W.toScheme.smallEtaleTopology Λ G → ℓ ^ n • 𝟙 G = 0 → ∀ q : ℕ,
      Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
        ((etaleModuleExtensionByZero.{u, r} Λ W.ι).obj G)))
    (F : EtaleModules.{u, r} Λ X) (hF : IsConstructibleEtaleModule Λ F)
    (hFp : IsTorsionPrimeToEtaleModule Λ p X F) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj F) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  obtain ⟨N, hN, hNp, hNF⟩ := exists_nsmul_id_eq_zero_of_isConstructibleEtaleModule Λ p F hF hFp
  refine module_finite_cohomology_of_nsmul_id_eq_zero Λ (IsConstructibleEtaleModule Λ) p
    (fun G hG ℓ a hℓ hℓp hGa q' => ?_) N hN hNp F hF hNF q
  refine module_finite_cohomology_of_forall_isIrreducible_opens Λ π hX G hG q'
    (fun W hW hlc => hpieces W hW ℓ (a + 1) hℓ hℓp a.succ_pos _ hlc ?_ q')
  have h0 : ℓ ^ a • 𝟙 ((etaleModuleRestriction.{u, r} Λ W.ι).obj G) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hGa, Functor.map_zero]
  rw [pow_succ', mul_smul, h0, smul_zero]

end Stacks.EtaleCohomology.TorsionModules

end
