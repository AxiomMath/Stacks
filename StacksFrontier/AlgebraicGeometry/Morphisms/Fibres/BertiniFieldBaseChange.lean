module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniImmersionQuasiCompact
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Pullback
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Base change of the Bertini situation along a field extension

The standing situation of the Bertini theorems ([Stacks, Tag 0G47]) is
`Stacks.Bertini.FamilyDivisors`: a field `k`, a scheme `X` over `k`, an invertible module `L`, a
finite dimensional linear system `V` with a basis, and a `k`-linear `ψ : V → Γ(X, L)`. This file
constructs, from such a situation and a field extension `K/k`, the situation over `K` obtained by
base change, which is what the reduction of [Stacks, Tag 0FD6] to an algebraically closed base
([Stacks, Tag 02FY]) needs an object to apply the theorem to.

The scheme is `X_K = X ×_k Spec K`, which the standing situation already provides
(`Stacks.Bertini.FamilyDivisors.baseChange`), the module is the pullback `L_K = pr₁^* L`, and the
linear system is `K ⊗_k V` with the base change of the chosen basis.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.baseChangePullbackSections` is `Γ(X, L) → Γ(X_K, L_K)`, the
  pullback of global sections read as a `k`-linear map.
* `Stacks.Bertini.FamilyDivisors.baseChangeψ` is `ψ_K : K ⊗_k V →ₗ[K] Γ(X_K, L_K)`.
* `Stacks.Bertini.FamilyDivisors.baseChangeBasis` is the base change of the chosen basis.
* `Stacks.Bertini.FamilyDivisors.baseChangeFamily` is the standing situation over `K`, and
  `Stacks.Bertini.FamilyDivisors.baseChangeAlgebraicClosure` is the case `K = k̄`.

## Main results

* `Stacks.Bertini.FamilyDivisors.baseChangeψ_one_tmul`: `ψ_K` agrees with `ψ` on the image of `V`,
  that is `ψ_K(1 ⊗ v)` is the pullback of `ψ(v)`.
* `Stacks.Bertini.FamilyDivisors.sectionOf_baseChangeFamily_basis`: the section of the `j`-th
  basis vector of the base-changed situation is the pullback of the section of the `j`-th basis
  vector of the original one. This is the family the universal section is assembled from, so it
  is what identifies the base-changed family of divisors.
* `Stacks.Bertini.FamilyDivisors.finrank_baseChangeFamily`: the base-changed linear system has the
  same dimension, so the parameter space of the base-changed situation has the same number of
  coordinates.
* `Stacks.Bertini.FamilyDivisors.smooth_baseChangeFamily` and
  `Stacks.Bertini.FamilyDivisors.generates_baseChangeFamily`: hypotheses (1) and (2) of
  [Stacks, Tag 0FD6] hold of the base-changed situation when they hold of the original one.
  Hypothesis (3) is not transferred in this module: it needs the base-change compatibility of
  `AlgebraicGeometry.toProjectiveSpaceOfModule`, and is
  `Stacks.Bertini.FamilyDivisors.isImmersive_baseChangeFamily` in
  `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFieldBaseChangeImmersion`.
* `Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_baseChangeFamily`:
  [Stacks, Tag 0FD6] for the base-changed situation over an algebraically closed extension,
  with hypothesis (3) *for that situation* as the single remaining input. This is what the
  construction is for; that input is now supplied, and
  `Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_baseChangeAlgebraicClosure`
  is what feeding it in gives.

## Implementation notes

The one real step is `ψ_K`. The pullback of global sections
`AlgebraicGeometry.pullbackGlobalSections` is only semilinear — it carries a scalar `r` of
`Γ(X, 𝒪_X)` to `f^♯ r` (`AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul`) — so it
is not a `K`-linear map and not even a map of `K`-vector spaces. What it *is* is `k`-linear into
`Γ(X_K, L_K)` with its scalars restricted along `k → K`: a scalar `t` of `k` acts on `Γ(X, L)` as
the constant function `t` of `Γ(X, 𝒪_X)`, whose pullback is the constant function `t` of
`Γ(X_K, 𝒪_{X_K})` (`Stacks.Bertini.FamilyDivisors.appTop_baseChangeToX_constSection`), which is
how `t` acts through `k → K`. That makes `ψ` followed by the pullback a `k`-linear map into a
`K`-module, and `LinearMap.liftBaseChange` turns it into the `K`-linear `ψ_K` on `K ⊗_k V`.

The `k`-module structure on `Γ(X_K, L_K)` that this needs is the restriction of scalars along
`k → K`; it is declared `local`, so that no `Module k` instance on a space of sections over `K`
escapes this file. `Stacks.Bertini.FamilyDivisors.baseChangePullbackSections` can still be applied
downstream — its type is stored with the instance already resolved — but restating that type
elsewhere requires putting the instance back in scope.

Everything is at `Stacks.Bertini.FamilyDivisors.{u, u}`, where the linear system lives in the
universe of the scheme. That is the shape the statement of [Stacks, Tag 0FD6] is proved at
(`FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_basis'`), and it
is closed under this construction: `K` and `V` both lie in `Type u`, hence so does `K ⊗_k V`.

## References

* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TensorProduct

universe u

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, u}) (K : Type u) [Field K] [Algebra D.k K]

/-- **The module `L_K = L|_{X_K}`** on the base change of `X` along a field extension: the
pullback of `L` along the projection `X_K → X`. It is invertible, by [Stacks, Tag 0B8L]. -/
abbrev baseChangeModule : (D.baseChange K).Modules :=
  (Scheme.Modules.pullback (D.baseChangeToX K)).obj D.L

/-- **The global sections `Γ(X_K, L_K)` as a `K`-vector space**, the scalars being restricted
along the structure morphism `X_K → Spec K` of the base change. -/
abbrev baseChangeGlobalSections : ModuleCat.{u} K :=
  globalSections K (D.baseChangeToSpec K) (D.baseChangeModule K)

/-- A scalar of the extension field acts on `Γ(X_K, L_K)` as the global function it determines
on `X_K`. -/
theorem smul_baseChangeGlobalSections (a : K) (s : ↥(D.baseChangeGlobalSections K)) :
    (show Γ(D.baseChangeModule K, ⊤) from (a • s : ↥(D.baseChangeGlobalSections K))) =
      D.baseChangeScalar K a • (show Γ(D.baseChangeModule K, ⊤) from s) :=
  rfl

/-- `Γ(X_K, L_K)` as a `k`-vector space, by restriction of scalars along `k → K`. This is the
target in which the pullback of global sections is linear rather than semilinear; it is local to
this file, so that no `k`-module structure on sections over `K` leaks. -/
local instance moduleBaseGlobalSections : Module D.k ↥(D.baseChangeGlobalSections K) :=
  Module.compHom _ (algebraMap D.k K)

/-- The `k`-action on `Γ(X_K, L_K)` is the restriction of the `K`-action, by construction. -/
local instance isScalarTowerBaseGlobalSections :
    IsScalarTower D.k K ↥(D.baseChangeGlobalSections K) :=
  ⟨fun a b s => by
    change (a • b : K) • s = (algebraMap D.k K a) • b • s
    rw [Algebra.smul_def, mul_smul]⟩

/-- **The pullback of global sections `Γ(X, L) → Γ(X_K, L_K)`, as a `k`-linear map.**

`AlgebraicGeometry.pullbackGlobalSections` is semilinear for the ring map
`Γ(X, 𝒪_X) → Γ(X_K, 𝒪_{X_K})`; over the base field it becomes linear, because a constant function
pulls back to the corresponding constant function
(`Stacks.Bertini.FamilyDivisors.appTop_baseChangeToX_constSection`). -/
def baseChangePullbackSections :
    ↥(globalSections D.k D.toBase D.L) →ₗ[D.k] ↥(D.baseChangeGlobalSections K) :=
  LinearMap.mk
    { toFun := fun s => pullbackGlobalSections (D.baseChangeToX K) D.L s
      map_add' := fun s t =>
        (ConcreteCategory.hom (pullbackGlobalSections (D.baseChangeToX K) D.L)).map_add s t }
    fun t s =>
      (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul (D.baseChangeToX K) D.L
          (D.constSection t) (show Γ(D.L, ⊤) from s)).trans
        (congrArg (fun r => r • (show Γ(D.baseChangeModule K, ⊤) from
            pullbackGlobalSections (D.baseChangeToX K) D.L (show Γ(D.L, ⊤) from s)))
          (D.appTop_baseChangeToX_constSection K t))

/-- The `k`-linear map `Stacks.Bertini.FamilyDivisors.baseChangePullbackSections` is the pullback
of global sections on the nose, no transport being needed between the two readings of
`Γ(X_K, L_K)`. -/
theorem baseChangePullbackSections_apply (s : ↥(globalSections D.k D.toBase D.L)) :
    (show Γ(D.baseChangeModule K, ⊤) from D.baseChangePullbackSections K s) =
      pullbackGlobalSections (D.baseChangeToX K) D.L (show Γ(D.L, ⊤) from s) :=
  rfl

/-- **The `K`-linear map `ψ_K : K ⊗_k V → Γ(X_K, L_K)`** of the base-changed situation: the
`K`-linear extension of the pullback of `ψ`. -/
def baseChangeψ : (K ⊗[D.k] D.V) →ₗ[K] ↥(D.baseChangeGlobalSections K) :=
  LinearMap.liftBaseChange K ((D.baseChangePullbackSections K).comp D.ψ)

/-- `ψ_K(a ⊗ v) = a · ψ(v)|_{X_K}`. -/
theorem baseChangeψ_tmul (a : K) (v : D.V) :
    D.baseChangeψ K (a ⊗ₜ v) =
      a • (D.baseChangePullbackSections K (D.ψ v) : ↥(D.baseChangeGlobalSections K)) :=
  rfl

/-- **`ψ_K` agrees with `ψ` on the image of `V`**: on `1 ⊗ v` it is the pullback of `ψ(v)`. -/
theorem baseChangeψ_one_tmul (v : D.V) :
    (show Γ(D.baseChangeModule K, ⊤) from D.baseChangeψ K (1 ⊗ₜ v)) =
      pullbackGlobalSections (D.baseChangeToX K) D.L (D.sectionOf v) := by
  rw [baseChangeψ, LinearMap.liftBaseChange_one_tmul]
  rfl

/-- **The base change of the chosen basis**, reindexed by `Fin (dim_K (K ⊗_k V))`, which is the
index type the standing situation asks the basis to carry. -/
def baseChangeBasis :
    Module.Basis (Fin (Module.finrank K (K ⊗[D.k] D.V))) K (K ⊗[D.k] D.V) :=
  (D.basis.baseChange K).reindex (finCongr Module.finrank_baseChange.symm)

/-- The `j`-th vector of the base-changed basis is `1 ⊗ vⱼ`, the reindexing being the equality of
dimensions. -/
theorem baseChangeBasis_apply (j : Fin (Module.finrank K (K ⊗[D.k] D.V))) :
    D.baseChangeBasis K j = 1 ⊗ₜ D.basis ((finCongr Module.finrank_baseChange.symm).symm j) := by
  rw [baseChangeBasis, Module.Basis.reindex_apply, Module.Basis.baseChange_apply]

/-- **The standing situation of the Bertini theorems base changed along a field extension
`K/k`**: the scheme `X_K = X ×_k Spec K` over `K`, the invertible module `L_K = L|_{X_K}`, the
linear system `K ⊗_k V` with the base-changed basis, and the `K`-linear map `ψ_K`. -/
def baseChangeFamily : FamilyDivisors.{u, u} where
  k := K
  V := K ⊗[D.k] D.V
  X := D.baseChange K
  toBase := D.baseChangeToSpec K
  L := D.baseChangeModule K
  ψ := D.baseChangeψ K
  basis := D.baseChangeBasis K

/-- The base field of the base-changed situation is `K`. -/
@[simp] theorem baseChangeFamily_k : (D.baseChangeFamily K).k = K := rfl

/-- The linear system of the base-changed situation is `K ⊗_k V`. -/
@[simp] theorem baseChangeFamily_V : (D.baseChangeFamily K).V = (K ⊗[D.k] D.V) := rfl

/-- The scheme of the base-changed situation is `X_K = X ×_k Spec K`. -/
@[simp] theorem baseChangeFamily_X : (D.baseChangeFamily K).X = D.baseChange K := rfl

/-- The structure morphism of the base-changed situation is `X_K → Spec K`. -/
@[simp] theorem baseChangeFamily_toBase :
    (D.baseChangeFamily K).toBase = D.baseChangeToSpec K := rfl

/-- The invertible module of the base-changed situation is `L_K`. -/
@[simp] theorem baseChangeFamily_L : (D.baseChangeFamily K).L = D.baseChangeModule K := rfl

/-- The linear map of the base-changed situation is `ψ_K`. -/
@[simp] theorem baseChangeFamily_ψ : (D.baseChangeFamily K).ψ = D.baseChangeψ K := rfl

/-- The basis of the base-changed situation is the base change of the chosen basis. -/
@[simp] theorem baseChangeFamily_basis : (D.baseChangeFamily K).basis = D.baseChangeBasis K := rfl

/-- The invertibility of `L_K` carried by the base-changed situation is the instance supplied by
[Stacks, Tag 0B8L] for the projection `X_K → X`. -/
theorem baseChangeFamily_isInvertible :
    (D.baseChangeFamily K).isInvertible =
      inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsInvertible (D.baseChange K).sheaf.obj
        (D.baseChange K).ringCatSheaf.property (D.baseChangeModule K)) :=
  rfl

/-- **Base change does not change the dimension of the linear system**, so the base-changed
situation has the same number of parameters. -/
theorem finrank_baseChangeFamily :
    Module.finrank (D.baseChangeFamily K).k (D.baseChangeFamily K).V =
      Module.finrank D.k D.V :=
  Module.finrank_baseChange (R := K) (S := D.k) (M' := D.V)

/-- The basis index set of the base-changed situation is that of the original one. -/
def baseChangeFamilyBasisIndexEquiv : (D.baseChangeFamily K).basisIndex ≃ D.basisIndex :=
  Equiv.ulift.trans ((finCongr (D.finrank_baseChangeFamily K)).trans Equiv.ulift.symm)

/-- **The section of `1 ⊗ v` in the base-changed situation is the pullback of the section of
`v`.** -/
theorem sectionOf_baseChangeFamily_one_tmul (v : D.V) :
    (D.baseChangeFamily K).sectionOf (1 ⊗ₜ v) =
      pullbackGlobalSections (D.baseChangeToX K) D.L (D.sectionOf v) :=
  D.baseChangeψ_one_tmul K v

/-- **The sections of the base-changed basis are the pullbacks of the sections of the basis.**
The universal section of the base-changed situation is assembled from these, so this is the
identity that lets the base-changed family of divisors be compared with the original one. -/
theorem sectionOf_baseChangeFamily_basis (j : Fin (Module.finrank K (K ⊗[D.k] D.V))) :
    (D.baseChangeFamily K).sectionOf (D.baseChangeBasis K j) =
      pullbackGlobalSections (D.baseChangeToX K) D.L
        (D.sectionOf (D.basis ((finCongr Module.finrank_baseChange.symm).symm j))) := by
  rw [baseChangeBasis_apply]
  exact D.sectionOf_baseChangeFamily_one_tmul K _

/-- The base field of the base-changed situation is the extension field, so it is algebraically
closed exactly when the extension is. -/
instance isAlgClosed_baseChangeFamily [IsAlgClosed K] : IsAlgClosed (D.baseChangeFamily K).k :=
  inferInstanceAs (IsAlgClosed K)

/-- **Hypothesis (1) of [Stacks, Tag 0FD6] transfers to the base change**: `X_K` is smooth over
`K` when `X` is smooth over `k`, smoothness being stable under base change. -/
instance smooth_baseChangeFamily [Smooth D.toBase] : Smooth (D.baseChangeFamily K).toBase :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (D.isPullback_baseChange K) inferInstance

/-- **Hypothesis (2) of [Stacks, Tag 0FD6] transfers to the base change**: if the image of `ψ`
generates `L`, the image of `ψ_K` generates `L_K`.

The sections of the vectors `1 ⊗ v` are the pullbacks of the sections of `v`, and a generating
family of global sections of an invertible module pulls back to a generating family
(`AlgebraicGeometry.generatesStalks_pullbackGlobalSections`); so the germs of the image of `ψ_K`
span every stalk, already on that part of the image. -/
theorem generates_baseChangeFamily (hgen : D.Generates) : (D.baseChangeFamily K).Generates := by
  have hpb : Stacks.ProjectiveFromSections.GeneratesStalks
      (fun v : D.V => pullbackGlobalSections (D.baseChangeToX K) D.L (D.sectionOf v)) :=
    AlgebraicGeometry.generatesStalks_pullbackGlobalSections (D.baseChangeToX K) D.L
      D.sectionOf hgen
  show Stacks.ProjectiveFromSections.GeneratesStalks (D.baseChangeFamily K).sectionOf
  refine Stacks.StalkwiseGeneration.generatesStalks_of_span_eq_top _ fun x => ?_
  obtain ⟨v, hv⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks _ hpb x
  refine Stacks.FinGenFromCover.span_eq_top_of_mem_nonvanishingLocus _ _ (i := 1 ⊗ₜ v) ?_
  rw [D.sectionOf_baseChangeFamily_one_tmul K v]
  exact hv

/-- **The carrier of [Stacks, Tag 0FD6] applied to the base-changed situation.** The base change
is a situation of the same shape, hypothesis (1) is stable under base change and hypothesis (2)
transfers, so over an algebraically closed extension of `k` the conclusion of the tag holds for
`H_v` on `X_K` — with hypothesis (3) *for the base-changed situation* as the one input that is
not supplied from `D` itself.

That input is supplied by `Stacks.Bertini.FamilyDivisors.isImmersive_baseChangeFamily`, which
identifies `φ_{L_K, ψ_K}` with the base change of `φ_{L, ψ}` and uses the stability of
`AlgebraicGeometry.IsImmersion` under base change; the composite is
`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_baseChangeAlgebraicClosure`,
in `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFieldBaseChangeImmersion`. -/
theorem forGeneral_smooth_specializedDivisor_baseChangeFamily
    [IsAlgClosed K] [Smooth D.toBase] (hgen : D.Generates) {m : ℕ}
    (b : Module.Basis (Fin (m + 1)) (D.baseChangeFamily K).k (D.baseChangeFamily K).V)
    (himm : (D.baseChangeFamily K).IsImmersive b
      ((D.baseChangeFamily K).generatesBy_basis (D.generates_baseChangeFamily K hgen) b)) :
    (D.baseChangeFamily K).ForGeneral (fun K' _ _ w =>
      ∀ a : Fin (Module.finrank (D.baseChangeFamily K).k (D.baseChangeFamily K).V) → K',
        w = ∑ i, TensorProduct.tmul (D.baseChangeFamily K).k
            ((D.baseChangeFamily K).basis i) (a i) →
          Smooth (((D.baseChangeFamily K).specializedDivisor K' a).subschemeι ≫
            (D.baseChangeFamily K).baseChangeToSpec K')) :=
  (D.baseChangeFamily K).forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_basis'
    (D.generates_baseChangeFamily K hgen) b himm

/-! ### The situation over an algebraic closure of the base field -/

/-- **The standing situation base changed to an algebraic closure of `k`.** This is the object
that the reduction of [Stacks, Tag 0FD6] to an algebraically closed base ([Stacks, Tag 02FY])
applies the theorem to; `Stacks.Bertini.FamilyDivisors.{u, u}` is closed under the construction,
so the base change of the situation is again a situation of the same shape. -/
abbrev baseChangeAlgebraicClosure : FamilyDivisors.{u, u} :=
  D.baseChangeFamily (AlgebraicClosure D.k)

end Stacks.Bertini.FamilyDivisors

end
