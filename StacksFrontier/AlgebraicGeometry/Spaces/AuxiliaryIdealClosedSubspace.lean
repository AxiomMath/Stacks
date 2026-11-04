module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AuxiliaryIdealClosedSubspace

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AuxiliaryIdealAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.IdealQuotientPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.FormalFunctionsProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionFullyFaithfulProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.CompletionFullyFaithfulProperSupport

/-!
# Reading hypothesis (1) of Stacks 08BC on the closed subspaces `X_e`

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over `Spec A`.  Direct image along `i`
commutes with reduction modulo the powers of `I 𝒪`
(`AlgebraicGeometry.Space.C1573.pushforwardBaseQuotientIso`), detects annihilation by them, and
preserves and reflects support proper over `Spec A`.  When `Z` is cut out by `𝓚^e`, these
facts turn the hypothesis that completion along `I 𝒪_Z` is an equivalence into
`AlgebraicGeometry.Space.C1573.KTorsionEssSurj`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Generic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

end Generic

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {Z X : AlgebraicSpaces B (Spec (.of A)) hA} (i : Z ⟶ X)
  (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom)

section Support

variable (f : X ⟶ schemeSpace (baseObject A B hA))
  (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)

end Support

section KernelIdeal

variable (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule) (e : ℕ)
  (hker : SheafOfModules.kerIdeal (structureSharp B (Spec (.of A)) hA i) =
    idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K e (SheafOfModules.unit _))

end KernelIdeal

section Quotient

variable [IsNoetherianRing A] (I : Ideal A)

end Quotient

section Descent

variable [IsNoetherianRing A] (I : Ideal A)
  (E : ℕᵒᵖ ⥤ Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
  (G : ℕ → CoherentModules.{u, u} B (Spec (.of A)) hA Z.1 Z.2)
  (θ : ∀ n, (modulePushforward B (Spec (.of A)) hA i).obj (G n).obj ≅ E.obj (op n))

end Descent

section Transport

variable (I : Ideal A) [IsNoetherianRing A] [IsAdicComplete I A]
  [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA Z.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))]

variable (f : X ⟶ schemeSpace (baseObject A B hA))
  (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
  (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule) (hK : K.toSheafOfModules.IsQuasicoherentOnSite) (e : ℕ)
  (hker : SheafOfModules.kerIdeal (structureSharp B (Spec (.of A)) hA i) =
    idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K e (SheafOfModules.unit _))

end Transport

section Registered

/-- **Stacks 08BC.**  In Situation 08B7 — `A` Noetherian and `I`-adically complete,
`f : X ⟶ Spec A` of finite type and separated, `𝓘 = I 𝒪_X` — let `𝓚 ⊆ 𝒪_X` be a
quasi-coherent sheaf of ideals and `(F_n)` an object of
`Coh_{support proper over A}(X, 𝓘)`.  Assume

1. for every `e ≥ 1`, the closed subspace `X_e` cut out by `𝓚^e` is such that completion along
   `𝓘_e = I 𝒪_{X_e}` is an equivalence
   `Coh_{support proper over A}(𝒪_{X_e}) ≌ Coh_{support proper over A}(X_e, 𝓘_e)`, and
2. there are an object `𝓗` of `Coh_{support proper over A}(𝒪_X)` and a map
   `α : (F_n) ⟶ 𝓗^∧` whose kernel and cokernel are annihilated by a power of `𝓚`.

Then `(F_n)` is in the essential image of the completion functor of Stacks 08B8.

The closed subspace `X_e` of (1) is given as a closed immersion `i : Z ⟶ X` whose ideal sheaf
`ker(𝒪_X ⟶ i_* 𝒪_Z)` is `𝓚^e`. The proof follows the source: the systems `(F_n / 𝓚^(e+1) F_n)_n`
are algebraized on `X_(e+1)` and pushed to `X`
(`AlgebraicGeometry.Space.C1573.kTorsionEssSurj_of_essSurj`); the algebraizations `G_e` form a
coherent `𝓚`-adic system mapping to `𝓗^∧` with kernels and cokernels killed by `𝓚^(2t)` — the bound
the source leaves as "details omitted"
(`C1573.TorsionAlgebraization.isSystemKernelCokernelAnnihilatedByPower_γSystem`, a sharper exponent
than the source's `𝓚^(4t)`); Stacks 08BB along `𝓚` algebraizes this map to `a : 𝓕 ⟶ 𝓗`; reducing
modulo `𝓘^(n+1)` identifies `𝓕 / 𝓘^(n+1) 𝓕` with `F_n`; and the kernel of `a` embeds into some
`G_e` by Artin–Rees, so `𝓕` has proper support by Stacks 0CZH
(`AlgebraicGeometry.Space.C1573.essImage_completionFunctorProperOver_of_kTorsionEssSurj`). -/
@[stacks 08BC]
theorem essImage_completionFunctorProperOver_of_auxiliaryIdeal [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsFiniteType B (Spec (.of A)) hA f.hom)
    (hsep : IsSeparated B (Spec (.of A)) hA f.hom)
    (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule) (hK : K.toSheafOfModules.IsQuasicoherentOnSite)
    (h1 : ∀ e : ℕ, 0 < e → ∃ (Z : AlgebraicSpaces B (Spec (.of A)) hA) (i : Z ⟶ X)
      (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom),
      SheafOfModules.kerIdeal (structureSharp B (Spec (.of A)) hA i) =
        idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K e (SheafOfModules.unit _) ∧
      letI := C1573.fact_isLocallyNoetherian_of_baseObject Z (i ≫ f)
        (C1573.isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1)
      (completionFunctorProperOver B (Spec (.of A)) hA Z.1 (schemeSpace (baseObject A B hA)).1
        Z.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
        (C1573.isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1)
        (C1573.baseIdealSubmodule Z.1 Z.2 I)
        (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := Z.1) (hX := Z.2) I)).IsEquivalence)
    (E : CoherentAdicSystemsProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf.1 (C1573.baseIdealSubmodule X.1 X.2 I))
    (H : CoherentModulesProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf.1)
    (α : E ⟶ letI := C1573.fact_isLocallyNoetherian_of_baseObject X f hf.1
      (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
        (schemeSpace (baseObject A B hA)).2 f.hom hf.1 (C1573.baseIdealSubmodule X.1 X.2 I)
        (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).obj H)
    (hα : IsSystemKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K α.hom.hom) :
    letI := C1573.fact_isLocallyNoetherian_of_baseObject X f hf.1
    (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
      (schemeSpace (baseObject A B hA)).2 f.hom hf.1 (C1573.baseIdealSubmodule X.1 X.2 I)
      (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).essImage E :=
  by apply C1573.essImage_completionFunctorProperOver_of_auxiliaryIdeal <;> assumption

end Registered

end AlgebraicGeometry.Space

end
