module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.KunnethOverSeparablyClosedFieldOfBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeOverFieldFiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsPullbackId
import StacksCore.Tactic.StacksAttribute

/-!
# Künneth over a separably closed field

Let `k` be a separably closed field, `X` and `Y` schemes of finite type over `k` with structure
morphisms `f : X ⟶ Spec k` and `g : Y ⟶ Spec k`, and `n ≥ 1` an integer invertible in `k`.
[Stacks, Tag 0F1P] asserts that for `E ∈ D(X_étale, ℤ/nℤ)` and `K ∈ D(Y_étale, ℤ/nℤ)`

`RΓ(X ×_k Y, pr₁⁻¹E ⊗^L_{ℤ/nℤ} pr₂⁻¹K) = RΓ(X, E) ⊗^L_{ℤ/nℤ} RΓ(Y, K)`.

The source's proof: [Stacks, Tag 0F1N], at the square with `S' = Spec k`, `T = Y` and
`p = 𝟙 X`, gives `Rpr₁_*(pr₁⁻¹E ⊗^L pr₂⁻¹K) = E ⊗^L f⁻¹Rg_*K`, and [Stacks, Tag 0F12] pulls the
constant factor out of `RΓ(X, -)`, `cd(X) < ∞` by [Stacks, Tag 0F10]. The second step and the
assembly are
`Stacks.EtaleCohomology.EtaleCoefficients.isIso_kunnethMap_of_isSepClosed_of_tensorBaseChange`
and `Stacks.EtaleCohomology.EtaleCoefficients.kunnethOverSepClosedIsoOfTensorBaseChange`; this
file supplies the first step from Tag 0F1N
(`Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_finiteType`), read at
`E` itself through `(𝟙 X)⁻¹ ≅ 𝟭` (`Stacks.EtaleCohomology.EtaleCoefficients.pullbackIdIso`).

The isomorphism is the Künneth map of [Stacks, Tag 0F1E]
(`Stacks.EtaleCohomology.EtaleCoefficients.kunnethMap`)
`Rf_*E ⊗^L Rg_*K ⟶ R(pr₁ ≫ f)_*(pr₁⁻¹E ⊗^L pr₂⁻¹K)` on `D((Spec k)_étale, ℤ/nℤ)`, read in
`D(ℤ/nℤ)` through the global sections equivalence `Γ : D((Spec k)_étale, ℤ/nℤ) ≌ D(ℤ/nℤ)`
(`derivedModulesEquivOfSepClosed`, with `RΓ(Z, -) = Γ ∘ R(Z ⟶ Spec k)_*`) and its compatibility
with `⊗^L` (`derivedModulesEquivOfSepClosedTensorIso`).

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `isIso_kunnethMap_of_isSepClosed` — [Stacks, Tag 0F1P]: the Künneth map of Tag 0F1E is an
  isomorphism.
* `kunnethOverSepClosedIso` — [Stacks, Tag 0F1P]: the isomorphism
  `RΓ(X ×_k Y, pr₁⁻¹E ⊗^L pr₂⁻¹K) ≅ RΓ(X, E) ⊗^L RΓ(Y, K)` in `D(ℤ/nℤ)`.
* `kunnethOverSepClosedIso_inv` — [Stacks, Tag 0F1P]: that isomorphism is the Künneth map of
  Tag 0F1E, read in `D(ℤ/nℤ)`.

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

-- [Stacks, Tag 0F10] imports `SheafOfModules.hasDerivedCategory`
-- (`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean:155`), the locally small model, which
-- would otherwise be found before `HasDerivedCategory.standard`.

variable (k : Type u) [Field k] [IsSepClosed k] (n : ℕ) [NeZero n] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType g] [QuasiCompact g]

omit [IsSepClosed k] in
/-- **The first step of the proof of [Stacks, Tag 0F1P]**: [Stacks, Tag 0F1N] at the square of
`X ×_k Y` over `X ⟵ Spec k ⟶ Y` (`S' = Spec k`, `T = Y`, `p = 𝟙 X`), read at `A` itself through
`(𝟙 X)⁻¹ ≅ 𝟭` (`pullbackIdIso`): the canonical map
`A ⊗^L f⁻¹Rg_*F ⟶ Rpr₁_*(pr₁⁻¹A ⊗^L pr₂⁻¹F)` is invertible for all `A ∈ D(X_étale, ℤ/nℤ)` and
`F ∈ D(Y_étale, ℤ/nℤ)`. -/
theorem isIso_tensorBaseChangeMap_pullbackFst_of_isSepClosed (hn : IsUnit (n : k))
    (A : DerivedModules (ULift.{u + 1} (ZMod n)) X)
    (F : DerivedModules (ULift.{u + 1} (ZMod n)) Y) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f g (Limits.pullback.fst f g)
      (Limits.pullback.snd f g) Limits.pullback.condition A F) :=
  ((tensorBaseChangeNatTransLeft (ULift.{u + 1} (ZMod n)) f g (Limits.pullback.fst f g)
      (Limits.pullback.snd f g) Limits.pullback.condition F).isIso_app_iff_of_iso
      ((pullbackIdIso n X).app A)).1
    (isIso_tensorBaseChangeMap_of_finiteType k n hn f (𝟙 _) (𝟙 X) f (Limits.pullback.fst f g)
      (Limits.pullback.snd f g) g (IsPullback.of_id_fst) (IsPullback.of_hasPullback f g) A F)

/-- **[Stacks, Tag 0F1P], as the Künneth map of [Stacks, Tag 0F1E].** Let `k` be a separably
closed field, `X` and `Y` schemes of finite type over `k` (through `f` and `g`), and `n ≥ 1` an
integer invertible in `k`. For `E ∈ D(X_étale, ℤ/nℤ)` and `K ∈ D(Y_étale, ℤ/nℤ)` the Künneth map

`RΓ(X, E) ⊗^L_{ℤ/nℤ} RΓ(Y, K) = Rf_*E ⊗^L Rg_*K ⟶ R(pr₁ ≫ f)_*(pr₁⁻¹E ⊗^L pr₂⁻¹K)
  = RΓ(X ×_k Y, pr₁⁻¹E ⊗^L pr₂⁻¹K)`

is an isomorphism in `D((Spec k)_étale, ℤ/nℤ) = D(ℤ/nℤ)`. -/
@[stacks 0F1P, sga "4½ Th_finitude 1.11" "special case"]
theorem isIso_kunnethMap_of_isSepClosed (hn : IsUnit (n : k))
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
    (K : DerivedModules (ULift.{u + 1} (ZMod n)) Y) :
    IsIso (kunnethMap (ULift.{u + 1} (ZMod n)) (Limits.pullback.fst f g) f
      (Limits.pullback.snd f g) g Limits.pullback.condition E K) :=
  isIso_kunnethMap_of_isSepClosed_of_tensorBaseChange k n f g hn
    (isIso_tensorBaseChangeMap_pullbackFst_of_isSepClosed k n f g hn) E K

/-- **[Stacks, Tag 0F1P].** Let `k` be a separably closed field, `X` and `Y` schemes of finite
type over `k` (through `f` and `g`), and `n ≥ 1` an integer invertible in `k`. For
`E ∈ D(X_étale, ℤ/nℤ)` and `K ∈ D(Y_étale, ℤ/nℤ)`

`RΓ(X ×_k Y, pr₁⁻¹E ⊗^L_{ℤ/nℤ} pr₂⁻¹K) ≅ RΓ(X, E) ⊗^L_{ℤ/nℤ} RΓ(Y, K)`

in `D(ℤ/nℤ)`, where `RΓ(Z, -) = Γ ∘ R(Z ⟶ Spec k)_*` for the global sections equivalence
`Γ : D((Spec k)_étale, ℤ/nℤ) ≌ D(ℤ/nℤ)` (`derivedModulesEquivOfSepClosed`). It is the inverse of
`Γ` of the Künneth map of [Stacks, Tag 0F1E] (`isIso_kunnethMap_of_isSepClosed`), followed by the
compatibility of `Γ` with `⊗^L` (`kunnethOverSepClosedIso_inv`). -/
@[stacks 0F1P]
def kunnethOverSepClosedIso [HasDerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))]
    (hn : IsUnit (n : k))
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
  kunnethOverSepClosedIsoOfTensorBaseChange k n f g hn
    (isIso_tensorBaseChangeMap_pullbackFst_of_isSepClosed k n f g hn) E K

/-- **[Stacks, Tag 0F1P]: the isomorphism is the Künneth map of [Stacks, Tag 0F1E].** The inverse
of `kunnethOverSepClosedIso` is the compatibility of `Γ` with `⊗^L`,
`RΓ(X, E) ⊗^L RΓ(Y, K) ≅ Γ(Rf_*E ⊗^L Rg_*K)`, followed by `Γ` of the Künneth map
`Rf_*E ⊗^L Rg_*K ⟶ R(pr₁ ≫ f)_*(pr₁⁻¹E ⊗^L pr₂⁻¹K)` of Tag 0F1E. -/
@[stacks 0F1P, sga "4½ Th_finitude 1.11" "special case"]
theorem kunnethOverSepClosedIso_inv
    [HasDerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))] (hn : IsUnit (n : k))
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
    (K : DerivedModules (ULift.{u + 1} (ZMod n)) Y) :
    (kunnethOverSepClosedIso k n f g hn E K).inv =
      (((derivedModulesEquivOfSepClosedTensorIso k (ULift.{u + 1} (ZMod n))).app
          ((pushforward (ULift.{u + 1} (ZMod n)) f).obj E)).app
          ((pushforward (ULift.{u + 1} (ZMod n)) g).obj K)).inv ≫
        (derivedModulesEquivOfSepClosed k (ULift.{u + 1} (ZMod n))).functor.map
          (kunnethMap (ULift.{u + 1} (ZMod n)) (Limits.pullback.fst f g) f
            (Limits.pullback.snd f g) g Limits.pullback.condition E K) := by
  simp [kunnethOverSepClosedIso, kunnethOverSepClosedIsoOfTensorBaseChange]

end Stacks.EtaleCohomology.EtaleCoefficients

end
