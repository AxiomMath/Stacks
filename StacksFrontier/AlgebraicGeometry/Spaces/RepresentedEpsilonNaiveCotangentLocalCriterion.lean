module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonNaiveCotangentQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Modules.PullbackLeftAdjointIsIso

/-!
# Stacks 0D0X: the cohomology sheaves of `ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` by a local computation

The canonical map `α : ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` of Stacks 0D0X is the adjunct, degreewise, of the
chain map `β : NL_{X₀/Y₀} ⟶ ε_*NL_{X/Y}`.  This file reduces the two isomorphisms that make `α` a
quasi-isomorphism (`AlgebraicGeometry.Space.quasiIso_representedEpsilonNaiveCotangentMap_of_isIso`)
to statements about sections:

* `ε^*` is exact, so the map induced by `α` on the kernels (cokernels) of the differentials is,
  up to the canonical comparison isomorphisms, the adjunct of the map `κ : 𝒦₀ ⟶ ε_*𝒦` induced by
  `β` on kernels (cokernels) — `CategoryTheory.Adjunction.isIso_kernel_map_of_isIso_homEquiv_symm`;
* the adjunct of a map `κ : M ⟶ ε_*N` is an isomorphism as soon as the map of presheaves
  `V ↦ (𝒪_X(V) ⊗_{𝒪_{X₀}(f(V))} M(f(V)) ⟶ N(V))`, `s ⊗ m ↦ s • N(V ⟶ f(V))(κ m)`, is locally
  injective and locally surjective, `f(V)` being the image of the étale chart `V` in `X₀`
  (`AlgebraicGeometry.Space.isIso_representedEpsilonModuleAdjunction_homEquiv_symm`).  The
  structure rings are raised to the universe `u + 1` of the modules first, so that the concrete
  description of `ε^*` applies.

## Main results

* `AlgebraicGeometry.Space.representedEpsilonNaiveCotangentMap_f`: `α` is degreewise the adjunct
  of `β`.
* `AlgebraicGeometry.Space.isIso_representedEpsilonModuleAdjunction_homEquiv_symm`: the local
  criterion for an adjunct to be an isomorphism.
* `AlgebraicGeometry.Space.isIso_kernel_map_representedEpsilonNaiveCotangentMap` and
  `AlgebraicGeometry.Space.isIso_cokernel_map_representedEpsilonNaiveCotangentMap`: the two
  hypotheses of the quasi-isomorphism criterion, from the adjuncts on kernels and cokernels.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

/-- **`α` is degreewise the adjunct of `β`** under `ε^* ⊣ ε_*`. -/
theorem representedEpsilonNaiveCotangentMap_f (i : ℤ) :
    (representedEpsilonNaiveCotangentMap B S hS φ).f i =
      ((representedEpsilonModuleAdjunction B S hS U).homEquiv _ _).symm
        ((representedEpsilonNaiveCotangentPushforwardMap B S hS φ).f i) := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- The site functor of `ε` is continuous. -/
local instance isContinuous_representedToZariskiRingedToposSiteHom_u (U : BigFppfOver B S hS) :
    (representedToZariskiRingedToposSiteHom B S hS U).u.IsContinuous
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J :=
  (representedToZariskiRingedToposSiteHom B S hS U).isContinuous

/-- **The local criterion for `ε^* ⊣ ε_*`.**  The adjunct `ε^*M ⟶ N` of `κ : M ⟶ ε_*N` is an
isomorphism as soon as, after the structure rings are raised to the universe of the modules, the
map of presheaves `V ↦ (𝒪_X(V) ⊗_{𝒪_{X₀}(f(V))} M(f(V)) ⟶ N(V))`,
`s ⊗ m ↦ s • N(V ⟶ f(V))(κ m)`, is locally injective and locally surjective. -/
theorem isIso_representedEpsilonModuleAdjunction_homEquiv_symm (U : BigFppfOver B S hS)
    {M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O)}
    {N : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O)}
    (κ : M ⟶ (representedEpsilonModulePushforward B S hS U).obj N)
    (hi : PresheafOfModules.IsLocallyInjective
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
      (((Stacks.PullbackLeftAdjoint.modelAdjunction (representedImageOpenEpsilonAdjunction B S hS U)
        (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
          (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))
        (Stacks.UniverseLift.liftedRingHom.{u + 1}
          (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing).hom
        (Stacks.PullbackLeftAdjoint.ringHom_commRingHom _)).homEquiv _ _).symm
          (Stacks.UniverseLift.liftedPushforwardHom.{u + 1, u + 1}
            (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing κ).val))
    (hs : PresheafOfModules.IsLocallySurjective
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
      (((Stacks.PullbackLeftAdjoint.modelAdjunction (representedImageOpenEpsilonAdjunction B S hS U)
        (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
          (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))
        (Stacks.UniverseLift.liftedRingHom.{u + 1}
          (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing).hom
        (Stacks.PullbackLeftAdjoint.ringHom_commRingHom _)).homEquiv _ _).symm
          (Stacks.UniverseLift.liftedPushforwardHom.{u + 1, u + 1}
            (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing κ).val)) :
    IsIso (((representedEpsilonModuleAdjunction B S hS U).homEquiv M N).symm κ) := by
  have := Stacks.UniverseLift.isRightAdjoint_pushforward_liftedRingHom.{u + 1, u + 1}
    (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing
  refine Stacks.UniverseLift.isIso_homEquiv_symm_of_liftedRingHom.{u + 1, u + 1}
    (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing κ ?_
  exact @Stacks.PullbackLeftAdjoint.isIso_homEquiv_symm_of_isLocallyBijective _ _ _ _ _ _ _ _ _
    (representedImageOpenEpsilonAdjunction B S hS U) _ _ (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing)
    _ (wEqualsLocallyBijective_representedSmallEtale_addCommGrpCat B S hS U) this _ _ _ hi hs

/-- The category of sheaves of `𝒪_X`-modules with sections in `Type (u + 1)` is abelian. -/
local instance abelianRepresentedSmallEtaleModules' (U : BigFppfOver B S hS) :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O)) :=
  SheafOfModules.instAbelian.{u + 1} _

/-- The category of sheaves of `𝒪_{X₀}`-modules with sections in `Type (u + 1)` is abelian. -/
local instance abelianRepresentedZariskiModules (U : BigFppfOver B S hS) :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O)) :=
  SheafOfModules.instAbelian.{u + 1} _

/-- **The kernel hypothesis of the quasi-isomorphism criterion from an adjunct.**  The map
induced by `α` on the kernels of the differentials is an isomorphism as soon as the adjunct of a
map `κ : 𝒦₀ ⟶ ε_*𝒦` lifting `𝒦₀ ⟶ NL_{X₀/Y₀}^{-1} ⟶ ε_*NL_{X/Y}^{-1}` is. -/
theorem isIso_kernel_map_representedEpsilonNaiveCotangentMap
    (κ : kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0) ⟶
      (representedEpsilonModulePushforward B S hS U).obj
        (kernel ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0)))
    (hκ : κ ≫ (representedEpsilonModulePushforward B S hS U).map (kernel.ι _) =
      kernel.ι _ ≫ (representedEpsilonNaiveCotangentPushforwardMap B S hS φ).f (-1))
    (h : IsIso (((representedEpsilonModuleAdjunction B S hS U).homEquiv _ _).symm κ)) :
    IsIso (kernel.map _ _ ((representedEpsilonNaiveCotangentMap B S hS φ).f (-1))
      ((representedEpsilonNaiveCotangentMap B S hS φ).f 0)
      ((representedEpsilonNaiveCotangentMap B S hS φ).comm (-1) 0).symm) := by
  have := preservesFiniteLimits_representedEpsilonModulePullback B S hS U
  refine (representedEpsilonModuleAdjunction B S hS U).isIso_kernel_map_of_isIso_homEquiv_symm
    ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)
    ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0) _ _ _ κ ?_ h
  rw [representedEpsilonNaiveCotangentMap_f, Equiv.apply_symm_apply]
  exact hκ

/-- **The cokernel hypothesis of the quasi-isomorphism criterion from an adjunct.**  The map
induced by `α` on the cokernels of the differentials is an isomorphism as soon as the adjunct of
a map `κ : coker d₀ ⟶ ε_*(coker d)` compatible with `β` in degree `0` is. -/
theorem isIso_cokernel_map_representedEpsilonNaiveCotangentMap
    (κ : cokernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0) ⟶
      (representedEpsilonModulePushforward B S hS U).obj
        (cokernel ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0)))
    (hκ : cokernel.π _ ≫ κ = (representedEpsilonNaiveCotangentPushforwardMap B S hS φ).f 0 ≫
      (representedEpsilonModulePushforward B S hS U).map (cokernel.π _))
    (h : IsIso (((representedEpsilonModuleAdjunction B S hS U).homEquiv _ _).symm κ)) :
    IsIso (cokernel.map _ _ ((representedEpsilonNaiveCotangentMap B S hS φ).f (-1))
      ((representedEpsilonNaiveCotangentMap B S hS φ).f 0)
      ((representedEpsilonNaiveCotangentMap B S hS φ).comm (-1) 0).symm) := by
  refine (representedEpsilonModuleAdjunction B S hS U).isIso_cokernel_map_of_isIso_homEquiv_symm
    ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)
    ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0) _ _ _ κ ?_ h
  rw [representedEpsilonNaiveCotangentMap_f, Equiv.apply_symm_apply]
  exact hκ

/-- **The map `κ_{-1} : 𝒦₀ ⟶ ε_*𝒦` induced by `β` on the kernels of the differentials**, through
the identification `ε_*(ker d) = ker (ε_* d)` (`ε_*` is a right adjoint). -/
def representedEpsilonKernelHom :
    kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0) ⟶
      (representedEpsilonModulePushforward B S hS U).obj
        (kernel ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0)) :=
  have := (representedEpsilonModuleAdjunction B S hS U).rightAdjoint_preservesLimits
  kernel.lift ((representedEpsilonModulePushforward B S hS U).map
      ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0))
    (kernel.ι _ ≫ (representedEpsilonNaiveCotangentPushforwardMap B S hS φ).f (-1))
    (by
      rw [Category.assoc]
      change _ ≫ _ ≫ (((representedEpsilonModulePushforward B S hS U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (representedSpaceNaiveCotangentComplex B S hS φ)).d (-1) 0 = 0
      rw [(representedEpsilonNaiveCotangentPushforwardMap B S hS φ).comm (-1) 0,
        kernel.condition_assoc, zero_comp]) ≫
    inv (kernelComparison _ (representedEpsilonModulePushforward B S hS U))

/-- `κ_{-1}` followed by the inclusion `ε_*𝒦 ⟶ ε_*NL_{X/Y}^{-1}` is `β` in degree `-1` on `𝒦₀`. -/
theorem representedEpsilonKernelHom_comp_ι :
    representedEpsilonKernelHom B S hS φ ≫
        (representedEpsilonModulePushforward B S hS U).map (kernel.ι _) =
      kernel.ι _ ≫ (representedEpsilonNaiveCotangentPushforwardMap B S hS φ).f (-1) := by
  have := (representedEpsilonModuleAdjunction B S hS U).rightAdjoint_preservesLimits
  have h : inv (kernelComparison ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0)
      (representedEpsilonModulePushforward B S hS U)) ≫
        (representedEpsilonModulePushforward B S hS U).map (kernel.ι _) = kernel.ι _ := by
    rw [IsIso.inv_comp_eq, kernelComparison_comp_ι]
  rw [representedEpsilonKernelHom, Category.assoc, h, kernel.lift_ι]

/-- **The map `κ_0 : coker d₀ ⟶ ε_*(coker d)` induced by `β` on the cokernels of the
differentials.** -/
def representedEpsilonCokernelHom :
    cokernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0) ⟶
      (representedEpsilonModulePushforward B S hS U).obj
        (cokernel ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0)) :=
  cokernel.desc _ ((representedEpsilonNaiveCotangentPushforwardMap B S hS φ).f 0 ≫
      (representedEpsilonModulePushforward B S hS U).map (cokernel.π _))
    (by
      rw [← Category.assoc, ← (representedEpsilonNaiveCotangentPushforwardMap B S hS φ).comm (-1) 0,
        Category.assoc]
      change _ ≫ (representedEpsilonModulePushforward B S hS U).map
          ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0) ≫
        (representedEpsilonModulePushforward B S hS U).map (cokernel.π _) = 0
      rw [← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero])

/-- `κ_0` on the image of `NL_{X₀/Y₀}^0` is `β` in degree `0` followed by the projection. -/
theorem π_comp_representedEpsilonCokernelHom :
    cokernel.π _ ≫ representedEpsilonCokernelHom B S hS φ =
      (representedEpsilonNaiveCotangentPushforwardMap B S hS φ).f 0 ≫
        (representedEpsilonModulePushforward B S hS U).map (cokernel.π _) :=
  cokernel.π_desc _ _ _

/-- **Stacks 0D0X reduced to two local computations.**  The canonical map
`ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` is a quasi-isomorphism as soon as the adjuncts of the maps induced by
`β` on the kernels and on the cokernels of the differentials are isomorphisms; by
`AlgebraicGeometry.Space.isIso_representedEpsilonModuleAdjunction_homEquiv_symm` this holds once
the corresponding maps `V ↦ 𝒪_X(V) ⊗_{𝒪_{X₀}(f(V))} M(f(V)) ⟶ N(V)` are locally bijective. -/
theorem quasiIso_representedEpsilonNaiveCotangentMap_of_isIso_homEquiv_symm
    (hker : IsIso (((representedEpsilonModuleAdjunction B S hS U).homEquiv _ _).symm
      (representedEpsilonKernelHom B S hS φ)))
    (hcoker : IsIso (((representedEpsilonModuleAdjunction B S hS U).homEquiv _ _).symm
      (representedEpsilonCokernelHom B S hS φ))) :
    QuasiIso (representedEpsilonNaiveCotangentMap B S hS φ) :=
  quasiIso_representedEpsilonNaiveCotangentMap_of_isIso B S hS φ
    (isIso_kernel_map_representedEpsilonNaiveCotangentMap B S hS φ _
      (representedEpsilonKernelHom_comp_ι B S hS φ) hker)
    (isIso_cokernel_map_representedEpsilonNaiveCotangentMap B S hS φ _
      (π_comp_representedEpsilonCokernelHom B S hS φ) hcoker)

end AlgebraicGeometry.Space

end
