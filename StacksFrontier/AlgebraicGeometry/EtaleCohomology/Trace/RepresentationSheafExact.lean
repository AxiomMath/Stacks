module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftFunctorSheafification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheaf

/-!
# The sheaf `ℱ_ρ` depends exactly on the representation

Let `X` be a connected scheme with a geometric point `x` and `Λ` a finite ring. The functor
`ρ ↦ ℱ_ρ` of `AlgebraicGeometry.representationSheaf`, from finite `Λ`-modules with a continuous
action of `π₁(X, x)` to sheaves of `Λ`-modules on `X_étale`, is **exact**: it preserves finite
limits and finite colimits, hence carries short exact sequences of representations to short
exact sequences of sheaves. The same holds for its restriction `ρ ↦ ℱ_ρ|_{X_K}` to a base change.

This is what makes `(M, ρ) ↦ H^i(X_{k̄}, ℱ_ρ)` a cohomological δ-functor on representations, the
left-hand side of the right-derived assertion of Stacks Tag 03VM.

## The argument

`ℱ_ρ` is the composite of four functors, each exact:

* the inverse of the equivalence of Tag 0DV5 (3), an equivalence;
* the inclusion of the finite type locally constant sheaves into all sheaves, exact because they
  are closed under kernels and cokernels (Stacks Tag 093U (3),
  `Stacks.ConstantSheaf.isClosedUnderKernels_isFiniteTypeLocallyConstantModuleSheaf` and its
  cokernel companion), via `CategoryTheory.ObjectProperty.preservesKernels_ι`;
* the universe lift of the coefficients, exact because it commutes with sheafification
  (`ModuleCat.preservesSheafification_uliftFunctor`);
* the equivalence between the sheaves on the bounded and on the canonical small étale site.

## Main results

* `AlgebraicGeometry.preservesFiniteLimits_finiteTypeLocallyConstantInverse`,
  `AlgebraicGeometry.preservesFiniteColimits_finiteTypeLocallyConstantInverse`: the first two
  factors together are exact.
* `AlgebraicGeometry.preservesFiniteLimits_sheafCompose_uliftFunctor_smallEtale`,
  `AlgebraicGeometry.preservesFiniteColimits_sheafCompose_uliftFunctor_smallEtale`: the universe
  lift of the coefficients is exact.
* `AlgebraicGeometry.preservesFiniteLimits_representationSheaf`,
  `AlgebraicGeometry.preservesFiniteColimits_representationSheaf`: `ρ ↦ ℱ_ρ` is exact.
* `AlgebraicGeometry.preservesFiniteLimits_geometricRepresentationSheaf`,
  `AlgebraicGeometry.preservesFiniteColimits_geometricRepresentationSheaf`: so is
  `ρ ↦ ℱ_ρ|_{X_K}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type r) [Ring Λ] [Finite Λ]

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

/-- The inverse of the equivalence of Tag 0DV5 (3), followed by the inclusion into all sheaves,
preserves finite limits. -/
theorem preservesFiniteLimits_finiteTypeLocallyConstantInverse :
    PreservesFiniteLimits ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙
      ObjectProperty.ι _) := by
  have : PreservesFiniteLimits (ObjectProperty.ι
      (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F)) := by
    change PreservesFiniteLimits (ObjectProperty.ι
      (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r}
        (SmallEtale.topology B X.1 X.2) Λ))
    have {A A' : ObjectProperty.FullSubcategory
        (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r}
          (SmallEtale.topology B X.1 X.2) Λ)} (f : A ⟶ A') :=
      ObjectProperty.preservesKernels_ι
        (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r}
          (SmallEtale.topology B X.1 X.2) Λ) f
    exact Functor.preservesFiniteLimits_of_preservesKernels _
  exact Limits.comp_preservesFiniteLimits _ _

/-- The inverse of the equivalence of Tag 0DV5 (3), followed by the inclusion into all sheaves,
preserves finite colimits. -/
theorem preservesFiniteColimits_finiteTypeLocallyConstantInverse :
    PreservesFiniteColimits ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙
      ObjectProperty.ι _) := by
  have : PreservesFiniteColimits (ObjectProperty.ι
      (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F)) := by
    change PreservesFiniteColimits (ObjectProperty.ι
      (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r}
        (SmallEtale.topology B X.1 X.2) Λ))
    have {A A' : ObjectProperty.FullSubcategory
        (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r}
          (SmallEtale.topology B X.1 X.2) Λ)} (f : A ⟶ A') :=
      ObjectProperty.preservesCokernels_ι
        (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r}
          (SmallEtale.topology B X.1 X.2) Λ) f
    exact Functor.preservesFiniteColimits_of_preservesCokernels _
  exact Limits.comp_preservesFiniteColimits _ _

omit [ConnectedSpace X.1] [Finite Λ] in
/-- Raising the universe of the coefficients of sheaves of `Λ`-modules on the bounded small étale
site preserves finite limits. -/
theorem preservesFiniteLimits_sheafCompose_uliftFunctor_smallEtale :
    PreservesFiniteLimits (sheafCompose (SmallEtale.topology B X.1 X.2)
      (ModuleCat.uliftFunctor.{r, u + 1} Λ)) := by
  let F := sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{r, u + 1} Λ)
  let G := sheafToPresheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{max (u + 1) r} Λ)
  have : PreservesFiniteLimits ((Functor.whiskeringRight (SmallEtale B X.1 X.2)ᵒᵖ
      (ModuleCat.{u + 1} Λ) (ModuleCat.{max (u + 1) r} Λ)).obj
        (ModuleCat.uliftFunctor.{r, u + 1} Λ)) := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits (F ⋙ G) := by
    change PreservesFiniteLimits (sheafToPresheaf (SmallEtale.topology B X.1 X.2)
        (ModuleCat.{u + 1} Λ) ⋙
      (Functor.whiskeringRight _ _ _).obj (ModuleCat.uliftFunctor.{r, u + 1} Λ))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves F G

omit [ConnectedSpace X.1] [Finite Λ] in
/-- Raising the universe of the coefficients of sheaves of `Λ`-modules on the bounded small étale
site preserves finite colimits. -/
theorem preservesFiniteColimits_sheafCompose_uliftFunctor_smallEtale :
    PreservesFiniteColimits (sheafCompose (SmallEtale.topology B X.1 X.2)
      (ModuleCat.uliftFunctor.{r, u + 1} Λ)) := by
  let J := SmallEtale.topology B X.1 X.2
  let F := sheafCompose J (ModuleCat.uliftFunctor.{r, u + 1} Λ)
  let L := presheafToSheaf J (ModuleCat.{u + 1} Λ)
  let G := sheafToPresheaf J (ModuleCat.{u + 1} Λ)
  let e := sheafComposeNatIso J (ModuleCat.uliftFunctor.{r, u + 1} Λ)
    (sheafificationAdjunction J (ModuleCat.{u + 1} Λ))
    (sheafificationAdjunction J (ModuleCat.{max (u + 1) r} Λ))
  have : PreservesFiniteColimits ((Functor.whiskeringRight (SmallEtale B X.1 X.2)ᵒᵖ
      (ModuleCat.{u + 1} Λ) (ModuleCat.{max (u + 1) r} Λ)).obj
        (ModuleCat.uliftFunctor.{r, u + 1} Λ)) := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits (L ⋙ F) := preservesFiniteColimits_of_natIso e
  refine ⟨fun D _ _ => ⟨fun {K} => ?_⟩⟩
  have : PreservesColimit ((K ⋙ G) ⋙ L) F :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit (K ⋙ G)))
      (isColimitOfPreserves (L ⋙ F) (colimit.isColimit (K ⋙ G)))
  have : PreservesColimit (K ⋙ G ⋙ L) F := this
  exact preservesColimit_of_iso_diagram F (Functor.isoWhiskerLeft K (asIso
    (sheafificationAdjunction J (ModuleCat.{u + 1} Λ)).counit))

/-- **`ρ ↦ ℱ_ρ` preserves finite limits.** -/
theorem preservesFiniteLimits_representationSheaf :
    PreservesFiniteLimits (representationSheaf B X x Λ) := by
  have := preservesFiniteLimits_finiteTypeLocallyConstantInverse B X x Λ
  have := preservesFiniteLimits_sheafCompose_uliftFunctor_smallEtale B X Λ
  change PreservesFiniteLimits
    (((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙ ObjectProperty.ι _) ⋙
      (sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{r, u + 1} Λ) ⋙
        (@SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{max (u + 1) r} Λ) _
          (Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, r, max (u + 1) r} Λ)).functor))
  exact Limits.comp_preservesFiniteLimits _ _

/-- **`ρ ↦ ℱ_ρ` preserves finite colimits.** -/
theorem preservesFiniteColimits_representationSheaf :
    PreservesFiniteColimits (representationSheaf B X x Λ) := by
  have := preservesFiniteColimits_finiteTypeLocallyConstantInverse B X x Λ
  have := preservesFiniteColimits_sheafCompose_uliftFunctor_smallEtale B X Λ
  change PreservesFiniteColimits
    (((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙ ObjectProperty.ι _) ⋙
      (sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{r, u + 1} Λ) ⋙
        (@SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{max (u + 1) r} Λ) _
          (Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, r, max (u + 1) r} Λ)).functor))
  exact Limits.comp_preservesFiniteColimits _ _

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]

/-- **`ρ ↦ ℱ_ρ|_{X_K}` preserves finite limits.** -/
theorem preservesFiniteLimits_geometricRepresentationSheaf :
    PreservesFiniteLimits (geometricRepresentationSheaf B X x Λ f K) := by
  have h₁ := preservesFiniteLimits_representationSheaf B X x Λ
  have h₂ := Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ
    (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))
  exact @Limits.comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂

/-- **`ρ ↦ ℱ_ρ|_{X_K}` preserves finite colimits.** -/
theorem preservesFiniteColimits_geometricRepresentationSheaf :
    PreservesFiniteColimits (geometricRepresentationSheaf B X x Λ f K) := by
  have h₁ := preservesFiniteColimits_representationSheaf B X x Λ
  have h₂ := Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ
    (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))
  exact @Limits.comp_preservesFiniteColimits _ _ _ _ _ _ _ _ h₁ h₂

end AlgebraicGeometry
