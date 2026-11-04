module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.SeparablyClosedFieldProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.KunnethOverFieldMapComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteType

/-!
# Künneth over a separably closed field, from the tensor base change isomorphism

Let `k` be a separably closed field, `X` and `Y` schemes of finite type over `k` with structure
morphisms `f : X ⟶ Spec k` and `g : Y ⟶ Spec k`, and `n ≥ 1` invertible in `k`. For
`E ∈ D(X_étale, ℤ/nℤ)` and `K ∈ D(Y_étale, ℤ/nℤ)`, [Stacks, Tag 0F1P] asserts

`RΓ(X ×_k Y, pr₁⁻¹E ⊗^L_{ℤ/nℤ} pr₂⁻¹K) = RΓ(X, E) ⊗^L_{ℤ/nℤ} RΓ(Y, K)`.

The source's proof has two steps. [Stacks, Tag 0F1N], at the square with `S' = Spec k` and
`T = Y`, gives `Rpr₁_*(pr₁⁻¹E ⊗^L pr₂⁻¹K) = E ⊗^L f⁻¹Rg_*K`. Then [Stacks, Tag 0F12] pulls the
constant factor `f⁻¹Rg_*K = RΓ(Y, K)` out of `RΓ(X, -)`, which is allowed because `cd(X) < ∞` by
[Stacks, Tag 0F10].

This file does everything except the first step, which enters as the explicit argument
`tensorBaseChange`. The second step is now unconditional:
`Stacks.EtaleCohomology.EtaleCoefficients.isIso_projectionFormulaMap_of_isSepClosed`, with
`cd(f) < ∞` from [Stacks, Tag 0F10] (1). The resulting isomorphism is the Künneth map of
[Stacks, Tag 0F1E] (`Stacks.EtaleCohomology.EtaleCoefficients.kunnethOverFieldMap_eq_kunnethMap`).
Read in `D(ℤ/nℤ)` through `D((Spec k)_étale, ℤ/nℤ) ≌ D(ℤ/nℤ)` and its compatibility with
`⊗^L`, it is the isomorphism of the source.

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `isIso_kunnethMap_of_isSepClosed_of_tensorBaseChange` — the Künneth map
  `Rf_*E ⊗^L Rg_*K ⟶ R(pr₁ ≫ f)_*(pr₁⁻¹E ⊗^L pr₂⁻¹K)` on `D((Spec k)_étale, ℤ/nℤ)` is invertible,
  given the base change isomorphism `tensorBaseChange`.
* `kunnethOverSepClosedIsoOfTensorBaseChange` — the same, read in `D(ℤ/nℤ)`:
  `RΓ(X ×_k Y, pr₁⁻¹E ⊗^L pr₂⁻¹K) ≅ RΓ(X, E) ⊗^L RΓ(Y, K)`.

## Implementation notes

*What is not proved.* The argument `tensorBaseChange` is the conclusion of [Stacks, Tag 0F1N] at
the fibre square of `X ×_k Y` (with `S' = Spec k`, `T = Y` and `p = 𝟙 X`). Its proof in the source
goes through Tag 0F1J, whose proof goes through Tags 0F1I and 0F1D and so through Tag 0F08, which
is not available here. So no declaration of this file is registered for Tag 0F1P.

## References

* [Stacks Project, Tag 0F1P](https://stacks.math.columbia.edu/tag/0F1P)
* [Stacks Project, Tag 0F1N](https://stacks.math.columbia.edu/tag/0F1N)
* [Stacks Project, Tag 0F12](https://stacks.math.columbia.edu/tag/0F12)
* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
* [Stacks Project, Tag 0F1E](https://stacks.math.columbia.edu/tag/0F1E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `DerivedModules`, the derived category of the étale site, is read at the standard model, as in
-- `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleKunnethMap`.
attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] [IsSepClosed k] (n : ℕ) [NeZero n] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType g] [QuasiCompact g]

/-- **The projection formula of the proof of [Stacks, Tag 0F1P]**: for `X` of finite type over a
separably closed field `k` and `n ≥ 1`, `Rf_*E ⊗^L M ⟶ Rf_*(E ⊗^L f⁻¹M)` is invertible for every
`E ∈ D(X_étale, ℤ/nℤ)` and `M ∈ D((Spec k)_étale, ℤ/nℤ)`; `cd(f) < ∞` is [Stacks, Tag 0F10] (1). -/
theorem isIso_projectionFormulaMap_of_finiteType_of_isSepClosed
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
    (M : DerivedModules (ULift.{u + 1} (ZMod n)) (Spec (.of k))) :
    IsIso (projectionFormulaMap (ULift.{u + 1} (ZMod n)) f E M) := by
  have : QuasiSeparated f := quasiSeparated_of_finiteType k f f
  have hcd := Scheme.Hom.etaleCohomologicalDimension_lt_top_of_finiteType k f (𝟙 _) f
    (Category.comp_id f)
  exact isIso_projectionFormulaMap_of_isSepClosed _ k f hcd (isTorsion_ulift_zmod n) E M

omit [LocallyOfFiniteType g] [QuasiCompact g] in
/-- **Künneth over a separably closed field, given the tensor base change isomorphism.** Let `k` be
a separably closed field, `X` and `Y` schemes of finite type over `k`, and `n ≥ 1` invertible in
`k`. For `E ∈ D(X_étale, ℤ/nℤ)` and `K ∈ D(Y_étale, ℤ/nℤ)` the Künneth map of [Stacks, Tag 0F1E]

`RΓ(X, E) ⊗^L_{ℤ/nℤ} RΓ(Y, K) = Rf_*E ⊗^L Rg_*K ⟶ R(pr₁ ≫ f)_*(pr₁⁻¹E ⊗^L pr₂⁻¹K)
  = RΓ(X ×_k Y, pr₁⁻¹E ⊗^L pr₂⁻¹K)`

is an isomorphism in `D((Spec k)_étale, ℤ/nℤ) = D(ℤ/nℤ)`.

`tensorBaseChange` is the conclusion of [Stacks, Tag 0F1N] at the fibre square of `X ×_k Y`
(`S' = Spec k`, `T = Y`, `p = 𝟙 X`): the canonical map `A ⊗^L f⁻¹Rg_*F ⟶ Rpr₁_*(pr₁⁻¹A ⊗^L pr₂⁻¹F)`
is invertible for all `A ∈ D(X_étale, ℤ/nℤ)` and `F ∈ D(Y_étale, ℤ/nℤ)`. The projection formula
step ([Stacks, Tag 0F12], with [Stacks, Tag 0F10]) is proved. -/
theorem isIso_kunnethMap_of_isSepClosed_of_tensorBaseChange (_hn : IsUnit (n : k))
    (tensorBaseChange : ∀ (A : DerivedModules (ULift.{u + 1} (ZMod n)) X)
      (F : DerivedModules (ULift.{u + 1} (ZMod n)) Y),
      IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f g (Limits.pullback.fst f g)
        (Limits.pullback.snd f g) Limits.pullback.condition A F))
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
    (K : DerivedModules (ULift.{u + 1} (ZMod n)) Y) :
    IsIso (kunnethMap (ULift.{u + 1} (ZMod n)) (Limits.pullback.fst f g) f
      (Limits.pullback.snd f g) g Limits.pullback.condition E K) := by
  rw [← kunnethOverFieldMap_eq_kunnethMap]
  exact isIso_kunnethMapOfBaseChange _ _ _ _ _ _ E K
    (isIso_projectionFormulaMap_of_finiteType_of_isSepClosed k n f E _) (tensorBaseChange E K)

/-- **Künneth over a separably closed field in `D(ℤ/nℤ)`, given the tensor base change
isomorphism.** In the situation of `isIso_kunnethMap_of_isSepClosed_of_tensorBaseChange`, write
`Γ : D((Spec k)_étale, ℤ/nℤ) ≌ D(ℤ/nℤ)` for the global sections equivalence
(`derivedModulesEquivOfSepClosed`), so that `RΓ(Z, -) = Γ ∘ R(Z ⟶ Spec k)_*`. Then

`RΓ(X ×_k Y, pr₁⁻¹E ⊗^L_{ℤ/nℤ} pr₂⁻¹K) ≅ RΓ(X, E) ⊗^L_{ℤ/nℤ} RΓ(Y, K)`

in `D(ℤ/nℤ)`, through the inverse of the Künneth map and the compatibility of `Γ` with `⊗^L`
(`derivedModulesEquivOfSepClosedTensorIso`). -/
def kunnethOverSepClosedIsoOfTensorBaseChange
    [HasDerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))] (hn : IsUnit (n : k))
    (tensorBaseChange : ∀ (A : DerivedModules (ULift.{u + 1} (ZMod n)) X)
      (F : DerivedModules (ULift.{u + 1} (ZMod n)) Y),
      IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f g (Limits.pullback.fst f g)
        (Limits.pullback.snd f g) Limits.pullback.condition A F))
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
    (K : DerivedModules (ULift.{u + 1} (ZMod n)) Y) :
    (derivedModulesEquivOfSepClosed k (ULift.{u + 1} (ZMod n))).functor.obj
        ((pushforward (ULift.{u + 1} (ZMod n)) (Limits.pullback.fst f g ≫ f)).obj
          (((tensor (ULift.{u + 1} (ZMod n)) (Limits.pullback f g)).obj
            ((pullback (ULift.{u + 1} (ZMod n)) (Limits.pullback.fst f g)).obj E)).obj
              ((pullback (ULift.{u + 1} (ZMod n)) (Limits.pullback.snd f g)).obj K))) ≅
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (ULift.{u + 1} (ZMod n))).tensor.obj
        ((derivedModulesEquivOfSepClosed k (ULift.{u + 1} (ZMod n))).functor.obj
          ((pushforward (ULift.{u + 1} (ZMod n)) f).obj E))).obj
        ((derivedModulesEquivOfSepClosed k (ULift.{u + 1} (ZMod n))).functor.obj
          ((pushforward (ULift.{u + 1} (ZMod n)) g).obj K)) :=
  haveI := isIso_kunnethMap_of_isSepClosed_of_tensorBaseChange k n f g hn tensorBaseChange E K
  (derivedModulesEquivOfSepClosed k (ULift.{u + 1} (ZMod n))).functor.mapIso
      (asIso (kunnethMap (ULift.{u + 1} (ZMod n)) (Limits.pullback.fst f g) f
        (Limits.pullback.snd f g) g Limits.pullback.condition E K)).symm ≪≫
    ((derivedModulesEquivOfSepClosedTensorIso k (ULift.{u + 1} (ZMod n))).app _).app _

end Stacks.EtaleCohomology.EtaleCoefficients

end
