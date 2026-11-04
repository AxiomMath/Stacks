module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientScalarsLocallyConstant
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.AdicModuleSheaf
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicQuotientTowerIso
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.LocallyConstantValues
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ProetaleTestingFamily
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf

/-!
# Lisse constructible `Λ`-sheaves on a connected scheme are adic lisse

Let `X` be a connected scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. A lisse constructible
`Λ`-sheaf `F` on `X_proét` is adic lisse: there is one `I`-adically complete `Λ`-module `M` with
`M / IM` finite such that `F` is locally isomorphic to `M̲^∧ = lim (M / IⁿM)̲`. This is
Stacks 09BW.

Each `F / IⁿF` is a locally constant constructible sheaf of `Λ ⧸ Iⁿ`-modules, hence locally
constant of finite presentation, and on the connected `X` all its local values are isomorphic
to one module `Mₙ`
(`AlgebraicGeometry.ProEtale.exists_forall_nonempty_linearEquiv_of_connectedSpace`).
Over an affine object `W` with w-contractible ring of global sections, `F / IⁿF ≅ Mₙ̲`
(`AlgebraicGeometry.ProEtale.nonempty_overPullback_iso_constantSheaf_of_isWContractible`), so
`F|_W` satisfies the hypotheses of Stacks 09BV on the slice site over `W`. Choosing the module
`M` of Stacks 09BV once, over one nonempty such `W₀`, the termwise isomorphisms
`(M / IⁿM)̲ ≅ Mₙ̲ ≅ F / IⁿF` over every `W` can be chosen compatibly, which gives
`F|_W ≅ M̲^∧|_W`; these `W` cover every object.

## Main results

* `AlgebraicGeometry.ProEtale.isAdicLisse_of_isLisseAdicModuleSheaf`: **Stacks 09BW**.

## Implementation notes

The source fixes the modules `N_t` given by Stacks 09BV over the members `W_t` of a covering
and identifies them by Stacks 09BC. Here the module is chosen once and the compatible choice of
the termwise isomorphisms
(`Stacks.ModuleSheaf.nonempty_natIso_constantAdicQuotientTower_of_isConstant`) is applied over
every `W` directly, which makes Stacks 09BC unnecessary.

## References

* [Stacks Project, Tag 09BW](https://stacks.math.columbia.edu/tag/09BW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ModuleSheaf Stacks.ConstantSheaf

universe w v u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] hasWeakSheafify_proEt_moduleCat hasWeakSheafify_proEt_over_moduleCat
  hasSheafify_proEt_over_moduleCat' wEqualsLocallyBijective_proEt_over_moduleCat

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] {I : Ideal Λ}

/-- **Stacks 09BW.** Let `X` be a connected scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal.
A lisse constructible `Λ`-sheaf on the small pro-étale site of `X` is adic lisse. -/
@[stacks 09BW]
theorem isAdicLisse_of_isLisseAdicModuleSheaf [ConnectedSpace X] [IsNoetherianRing Λ]
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
    (hF : IsLisseAdicModuleSheaf.{w} X Λ I F) : IsAdicLisse X Λ I F := by
  classical
  let J := Scheme.ProEt.topology X
  let A := ModuleCat.{max (u + 1) v w} Λ
  obtain ⟨Q, q, ⟨hlim⟩, hQ⟩ := hF
  choose hq G he hGc hGl using hQ
  -- the reductions are locally constant of finite presentation, with one value each
  have hfp (n : ℕ) : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      J (Λ ⧸ I ^ n) (G n) := by
    have := hGl n
    rw [isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf]
    exact isFiniteTypeLocallyConstantModuleSheaf_of_isLocallyConstant (Λ ⧸ I ^ n) (G n) (hGc n)
  choose M hMfp hval using fun n =>
    exists_forall_nonempty_linearEquiv_of_connectedSpace (Λ ⧸ I ^ n) (G n) (hfp n)
  let N (n : ℕ) : A := (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj (M n)
  have hNfin (n : ℕ) : Module.Finite Λ (N n) := by
    have := hMfp n
    exact finite_restrictScalars_quotient (I ^ n) (M n)
  -- over a w-contractible affine `W`, the `n`-th reduction is the constant sheaf on `N n`
  have hW (W : X.ProEt) (hWa : Scheme.ProEt.IsAffineWContractible W) (n : ℕ) :
      Nonempty ((constantSheaf (J.over W) A).obj (N n) ≅
        (J.overPullback A W).obj (Q.obj (op n))) := by
    have := hWa.1
    have := hMfp n
    obtain ⟨c⟩ := nonempty_overPullback_iso_constantSheaf_of_isWContractible (Λ ⧸ I ^ n) (G n)
      (hfp n) (M n) (hval n) W hWa.2
    have := Sheaf.preservesSheafification_of_adjunction (J.over W)
      (ModuleCat.restrictCoextendScalarsAdj.{max (u + 1) w} (Ideal.Quotient.mk (I ^ n)))
    exact ⟨((restrictQuotientScalarsConstantSheafIso.{u + 1, u, max (u + 1) v w, v} (J.over W) Λ
        (I ^ n)).app (M n)).symm ≪≫
      (Stacks.ModuleSheaf.restrictQuotientScalars.{u + 1, u, max (u + 1) v w, v} (J.over W) Λ
        (I ^ n)).mapIso c ≪≫
      (overPullbackRestrictQuotientScalarsIso.{u + 1, u, max (u + 1) v w, v} J Λ (I ^ n) W).app
        (G n) ≪≫
      (J.overPullback A W).mapIso (he n).some.symm⟩
  -- the tower of reductions over `W`
  let adjW (W : X.ProEt) := (Over.forget W).sheafAdjunctionCocontinuous A (J.over W) J
  let qW (W : X.ProEt) : (Functor.const ℕᵒᵖ).obj ((J.overPullback A W).obj F) ⟶
      Q ⋙ J.overPullback A W := ((J.overPullback A W).mapCone (Cone.mk F q)).π
  have hqW (W : X.ProEt) (n : ℕ) : Stacks.ModuleSheaf.IsQuotientBy (J.over W) Λ (I ^ n)
      ((J.overPullback A W).obj F) ((Q ⋙ J.overPullback A W).obj (op n)) ((qW W).app (op n)) :=
    (hq n).map (J.overPullback A W) (adjW W)
  -- a nonempty w-contractible affine
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨W₀, hW₀, w₀⟩ :
      ∃ W₀ : X.ProEt, Scheme.ProEt.IsAffineWContractible W₀ ∧ Nonempty W₀.left := by
    obtain ⟨ι, Ui, f, hf, hP⟩ := Scheme.ProEt.hasEnoughObjects_isAffineWContractible
      (Scheme.ProEt.mk (𝟙 X))
    obtain ⟨V, g, hg, y, -⟩ := Scheme.ProEt.exists_mem_range_of_mem_topology hf x₀
    obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    exact ⟨Ui i, hP i, ⟨h.left y⟩⟩
  obtain ⟨w₀⟩ := w₀
  -- the module of Stacks 09BV, over `W₀`
  obtain ⟨M₀, hM₀c, hM₀f, hM₀compl, hM₀fin, hM₀iso⟩ :=
    Stacks.ModuleSheaf.exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant.{u + 1, u,
        max (u + 1) v w, v}
      (J.over W₀) Λ I
      (Scheme.ProEt.exists_bot_notMem_over w₀) _ _ (qW W₀) (hqW W₀) (fun n => ⟨N n, hW W₀ hW₀ n⟩)
      ⟨N 1, hNfin 1, hW W₀ hW₀ 1⟩
  -- its reductions are the `N n`
  have hred (n : ℕ) : Nonempty ((adicQuotientModuleSystem Λ I M₀).obj (op n) ≅ N n) := by
    have : Module.Finite Λ ((adicQuotientModuleSystem Λ I M₀).obj (op n)) := hM₀fin n
    have := hNfin n
    have : Module.FinitePresentation Λ ((adicQuotientModuleSystem Λ I M₀).obj (op n)) :=
      Module.finitePresentation_of_finite Λ _
    have : Module.FinitePresentation Λ (N n) := Module.finitePresentation_of_finite Λ _
    exact nonempty_iso_of_constantSheaf_iso.{u + 1, u, v, max (u + 1) v w} (J.over W₀)
      (Scheme.ProEt.exists_bot_notMem_over w₀) _ _
      ((hM₀iso n).some ≪≫ (hW W₀ hW₀ n).some.symm)
  -- over every w-contractible affine, `F` is the completed constant sheaf of `M₀`
  have key (W : X.ProEt) (hWa : Scheme.ProEt.IsAffineWContractible W) :
      Nonempty ((J.overPullback A W).obj F ≅
        (J.overPullback A W).obj (completedConstantSheaf X Λ I M₀)) := by
    obtain ⟨α⟩ :=
      Stacks.ModuleSheaf.nonempty_natIso_constantAdicQuotientTower_of_isConstant.{u + 1, u,
        max v w, v}
      (J.over W) Λ I M₀
      ((J.overPullback A W).obj F) _ (qW W) (hqW W) hM₀fin hM₀compl
      fun n => ⟨(constantSheaf (J.over W) A).mapIso (hred n).some ≪≫ (hW W hWa n).some⟩
    let hlimW := isLimitOfPreserves (J.overPullback A W) hlim
    have : HasLimitsOfShape ℕᵒᵖ (Sheaf (J.over W) A) := inferInstance
    have : HasLimitsOfShape ℕᵒᵖ (Sheaf J A) := inferInstance
    exact ⟨(IsLimit.conePointsIsoOfNatIso hlimW
        (limit.isLimit (Stacks.ModuleSheaf.constantAdicQuotientTower (J.over W) Λ I M₀)) α.symm) ≪≫
      HasLimit.isoOfNatIso (Functor.isoWhiskerLeft (adicQuotientModuleSystem Λ I M₀)
        (overPullbackConstantSheafIso J A W)) ≪≫
      (preservesLimitIso (J.overPullback A W)
        (adicQuotientModuleSystem Λ I M₀ ⋙ constantSheaf J A)).symm⟩
  refine ⟨M₀, hM₀c, hM₀f, fun U => ?_⟩
  obtain ⟨ι, Ui, f, hf, hP⟩ := Scheme.ProEt.hasEnoughObjects_isAffineWContractible U
  refine ⟨ULift.{u + 1} ι, fun i => Ui i.down, fun i => f i.down, ?_, fun i => key _ (hP i.down)⟩
  convert hf using 1
  apply le_antisymm
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact Sieve.ofArrows_mk _ _ i.down
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact Sieve.ofArrows_mk (fun i : ULift.{u + 1} ι => Ui i.down) (fun i => f i.down) ⟨i⟩

end AlgebraicGeometry.ProEtale

end
