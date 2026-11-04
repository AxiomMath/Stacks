module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExtSingleIsGE
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality

/-!
# The dualizing module of a proper scheme over a field

Let `X` be a proper scheme over a field `k`, `ω_X^• = a(𝒪_{Spec k})` its relative dualizing
complex and `ω_X = H^{-n}(ω_X^•)` its relative dualizing module, `n = dim X`. If `ω_X^•` has no
cohomology in degrees `< -n` (part (1) of [Stacks, Tag 0FVV]), then for every quasi-coherent
`𝒪_X`-module `F` there is a `k`-linear isomorphism `Hom_X(F, ω_X) ≅ Hom_k(H^n(X, F), k)`, natural
in `F`. This is the deduction of part (6) of [Stacks, Tag 0FVV] from parts (1) and (5): it is the
duality isomorphism of part (5) for `K = F[0]` and `i = -n`, combined with
`Ext^{-n}_X(F[0], ω_X^•) = Hom_X(F, H^{-n}(ω_X^•))` ([Stacks, Tag 06XS]) and the comparison of the
hypercohomology of `F[0]` with the sheaf cohomology of `F`.

## Main definitions

* `Stacks.Duality.dualizingModuleHomEquiv` — `Hom_X(F, ω_X) ≃ₗ[k] Hom_k(H^n(X, F), k)`, given the
  vanishing of the cohomology of `ω_X^•` below degree `-n`.

## Main results

* `Stacks.Duality.dualizingModuleHomEquiv_comp` — naturality in `F`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The relative dualizing complex `ω_X^• = a(𝒪_{Spec k})` of `f : X ⟶ Spec k`. -/
local notation "ωX" =>
  relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- A quasi-coherent module placed in degree zero, as an object of `D_QCoh(𝒪_X)`. -/
def singleQuasiCoherentDegreeZero (F : X.Modules) [F.IsQuasicoherent] :
    quasiCoherentDerivedCategory X :=
  ⟨(DerivedCategory.singleFunctor X.Modules 0).obj F,
    DerivedPushforward.derivedCategoryB_singleFunctor_obj F inferInstance⟩

/-- `H^{-(-n)}(X, F[0]) ≅ H^n(X, F)`, naturally in `F`. -/
def hypercohomologyNegNegIso (n : ℕ) :
    DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat k) (-(-(n : ℤ))) ≅
      cohomologyOverFieldFunctor k f n :=
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f)
      (eqToIso (by rw [neg_neg])) ≪≫
    hypercohomologySingleIsoCohomologyOverField f n

/-- **The dualizing module and the dual of top cohomology.** Let `X` be a proper scheme over a
field `k` of dimension `n`, and suppose the cohomology sheaves of the relative dualizing complex
`ω_X^• = a(𝒪_{Spec k})` vanish in degrees `< -n`. Then for every quasi-coherent `𝒪_X`-module `F`
there is a `k`-linear isomorphism `Hom_X(F, ω_X) ≅ Hom_k(H^n(X, F), k)`, where
`ω_X = H^{-n}(ω_X^•)` is the relative dualizing module. -/
def dualizingModuleHomEquiv
    (hω : ∀ j < -(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ),
      IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj (ωX).obj))
    (F : X.Modules) [F.IsQuasicoherent] :
    letI := Scheme.linearOver f
    (F ⟶ relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))) ≃ₗ[k]
      (cohomologyOverField k f F (ENat.toNat ((topologicalKrullDim X).getD 0)) →ₗ[k] k) :=
  letI := Scheme.linearOver f
  haveI : (ωX).obj.IsGE (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ)) :=
    (DerivedCategory.isGE_iff _ _).2 hω
  (DerivedCategory.extSingleLinearEquivOfIsGE k F (ωX).obj
      (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ))).symm ≪≫ₗ
    dualityEquiv f (singleQuasiCoherentDegreeZero F)
      (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ)) ≪≫ₗ
    LinearEquiv.arrowCongr
      ((hypercohomologyNegNegIso f
        (ENat.toNat ((topologicalKrullDim X).getD 0))).app F).toLinearEquiv
      (LinearEquiv.refl k k)

/-- **Naturality of `Hom_X(F, ω_X) ≅ Hom_k(H^n(X, F), k)` in `F`.** For `φ : F ⟶ G`, the linear
form attached to `φ ≫ u` is the one attached to `u` precomposed with `H^n(X, φ)`. -/
theorem dualizingModuleHomEquiv_comp
    (hω : ∀ j < -(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ),
      IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj (ωX).obj))
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G)
    (u : G ⟶ relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))))
    (x : cohomologyOverField k f F (ENat.toNat ((topologicalKrullDim X).getD 0))) :
    letI := Scheme.linearOver f
    dualizingModuleHomEquiv f hω F (φ ≫ u) x =
      dualizingModuleHomEquiv f hω G u
        ((cohomologyOverFieldFunctor k f (ENat.toNat ((topologicalKrullDim X).getD 0))).map φ
          x) := by
  let := Scheme.linearOver f
  have : (ωX).obj.IsGE (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ)) :=
    (DerivedCategory.isGE_iff _ _).2 hω
  have h₁ := DerivedCategory.extSingleLinearEquivOfIsGE_symm_comp k φ (ωX).obj
    (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ)) u
  have h₂ := congrArg (fun y ↦ y.hom x)
    ((hypercohomologyNegNegIso f (ENat.toNat ((topologicalKrullDim X).getD 0))).inv.naturality φ)
  show dualityEquiv f (singleQuasiCoherentDegreeZero F) _
      ((DerivedCategory.extSingleLinearEquivOfIsGE k F (ωX).obj _).symm (φ ≫ u))
      (((hypercohomologyNegNegIso f (ENat.toNat ((topologicalKrullDim X).getD 0))).app F).inv x) =
    dualityEquiv f (singleQuasiCoherentDegreeZero G) _
      ((DerivedCategory.extSingleLinearEquivOfIsGE k G (ωX).obj _).symm u)
      (((hypercohomologyNegNegIso f (ENat.toNat ((topologicalKrullDim X).getD 0))).app G).inv
        ((cohomologyOverFieldFunctor k f (ENat.toNat ((topologicalKrullDim X).getD 0))).map φ x))
  rw [h₁]
  exact (dualityEquiv_comp f (singleQuasiCoherentDegreeZero F) (singleQuasiCoherentDegreeZero G) _
    ((DerivedCategory.singleFunctor X.Modules 0).map φ) _ _).trans
      (congrArg _ h₂.symm)

end Stacks.Duality
