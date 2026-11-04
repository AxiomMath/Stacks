module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksCore.Tactic.StacksAttribute

/-!
# The extension by zero of a constant finite module sheaf is constructible

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site, `Λ` a Noetherian ring
and `M` a finite `Λ`-module. Stacks 03S8 part (3) asserts that for `j : U ⟶ X` an étale morphism
with `U` quasi-compact and quasi-separated the sheaf `j_{U!}\underline{M}` of `Λ`-modules is
constructible on `X_étale`. That is proved here for every finite `M`;
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant` is the case `M = Λ`.

## Main definitions

* `AlgebraicGeometry.moduleShriek` — the extension by zero from `U` of the constant sheaf at a
  module `M`, and `AlgebraicGeometry.moduleShriekFunctor` the same as a functor of `M`.

## Main results

* `ModuleCat.exists_cokernel_finFreeSigma_of_finite` — a finite module over a Noetherian ring is
  the cokernel of a map between finite direct sums of copies of the free rank-one module.
* `AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriek` — **Stacks 03S8, part (3)** at an
  arbitrary finite module.

## Implementation notes

The dévissage is the one of the source. A finite module over a Noetherian ring is finitely
presented: a surjection `Λ^n ⟶ M` has finitely generated kernel, so `M` is the cokernel of a map
`Λ^m ⟶ Λ^n`. Extension by zero of the constant sheaf is a composite of two left adjoints — the
constant sheaf functor is left adjoint to evaluation at the final object `U/U` of the small étale
site of `U`, by `AlgebraicGeometry.SmallEtale.finalIsTerminal`, and extension by zero to
restriction — hence preserves finite direct sums and cokernels. So `j_{U!}\underline{Λ^n}` is a
finite direct sum of copies of `j_{U!}\underline{Λ}`, which is constructible by the case `M = Λ`,
and `j_{U!}\underline{M}` is the cokernel of a map between two such. Constructible sheaves of
modules over a Noetherian ring form a weak Serre subcategory, Stacks 03RZ (3), so they are closed
under both operations.

No left exactness of `j_{U!}` is used, which is why the dévissage goes through cokernels of maps
between free modules rather than through extensions.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u r w

namespace ModuleCat

/-- The direct sum of `n` copies of the free rank-one `Λ`-module `ULift Λ`. -/
public abbrev finFreeSigma (Λ : Type v) [CommRing Λ] (n : ℕ) : ModuleCat.{v} Λ :=
  ∐ fun _ : Fin n => ModuleCat.of Λ (ULift.{v} Λ)

/-- The direct sum of `n` copies of the free rank-one `Λ`-module is the module of functions
`Fin n → Λ`. -/
public def finFreeSigmaIso (Λ : Type v) [CommRing Λ] (n : ℕ) :
    finFreeSigma Λ n ≅ ModuleCat.of Λ (Fin n → Λ) :=
  (biproduct.isoCoproduct fun _ : Fin n => ModuleCat.of Λ (ULift.{v} Λ)).symm ≪≫
    ModuleCat.biproductIsoPi _ ≪≫
      (LinearEquiv.piCongrRight fun _ : Fin n => ULift.moduleEquiv).toModuleIso

/-- The direct sum of `n` copies of the free rank-one `Λ`-module is a finite module. -/
public instance finite_finFreeSigma (Λ : Type v) [CommRing Λ] (n : ℕ) :
    Module.Finite Λ (finFreeSigma Λ n) :=
  Module.Finite.equiv (finFreeSigmaIso Λ n).toLinearEquiv.symm

/-- A finite module is a quotient of a finite direct sum of copies of the free rank-one module. -/
private theorem exists_epi_finFreeSigma (Λ : Type v) [CommRing Λ] (N : ModuleCat.{v} Λ)
    [Module.Finite Λ N] : ∃ (n : ℕ) (π : finFreeSigma Λ n ⟶ N), Epi π := by
  obtain ⟨n, π₀, hπ₀⟩ := Module.Finite.exists_fin' Λ N
  have : Epi (ModuleCat.ofHom π₀ : ModuleCat.of Λ (Fin n → Λ) ⟶ N) :=
    (ModuleCat.epi_iff_surjective _).2 hπ₀
  exact ⟨n, (finFreeSigmaIso Λ n).hom ≫ ModuleCat.ofHom π₀, inferInstance⟩

/-- **A finite module over a Noetherian ring is a finite cokernel of finite free modules.** A
finite `Λ`-module is the cokernel of a map between finite direct sums of copies of the free
rank-one module `ULift Λ`. -/
public theorem exists_cokernel_finFreeSigma_of_finite (Λ : Type v) [CommRing Λ]
    [IsNoetherianRing Λ] (M : ModuleCat.{v} Λ) [Module.Finite Λ M] :
    ∃ (n m : ℕ) (f : finFreeSigma Λ m ⟶ finFreeSigma Λ n), Nonempty (cokernel f ≅ M) := by
  obtain ⟨n, π, hπ⟩ := exists_epi_finFreeSigma Λ M
  have : Module.Finite Λ (kernel π : ModuleCat.{v} Λ) :=
    Module.Finite.of_injective (kernel.ι π).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  obtain ⟨m, σ, hσ⟩ := exists_epi_finFreeSigma Λ (kernel π : ModuleCat.{v} Λ)
  refine ⟨n, m, σ ≫ kernel.ι π, ⟨?_⟩⟩
  have hcolim : IsColimit (CokernelCofork.ofπ (f := σ ≫ kernel.ι π) π
      (by rw [Category.assoc, kernel.condition, comp_zero])) :=
    isCokernelEpiComp (c := CokernelCofork.ofπ π (kernel.condition π))
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)) σ rfl
  exact (colimit.isColimit _).coconePointUniqueUpToIso hcolim

end ModuleCat

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

/-- The extension by zero, from an étale object `U` of `X`, of the constant sheaf of `R`-modules
with value `M`. The case `M = ULift R` is `AlgebraicGeometry.moduleShriekConstant`. -/
public abbrev moduleShriek (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type r) [CommRing R]
    (U : SmallEtale B X.1 X.property) (M : ModuleCat.{max (u + 1) r w} R) :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r w} R) := by
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, w} B X R
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, w} B U.obj.left R
  exact (Functor.sheafPullbackConstruction.sheafPullback
    (smallEtalePostcompose B X.1 X.property U)
    (ModuleCat.{max (u + 1) r w} R)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X.1 X.property)).obj
      ((constantSheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (ModuleCat.{max (u + 1) r w} R)).obj M)

/-- Extension by zero from `U` of the constant sheaf, as a functor of its value: it sends an
`R`-module `M` to `j_{U!}\underline{M}`. -/
public abbrev moduleShriekFunctor (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type r) [CommRing R]
    (U : SmallEtale B X.1 X.property) :
    ModuleCat.{max (u + 1) r w} R ⥤
      Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r w} R) := by
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, w} B X R
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, w} B U.obj.left R
  exact constantSheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) r w} R) ⋙
    Functor.sheafPullbackConstruction.sheafPullback
      (smallEtalePostcompose B X.1 X.property U)
      (ModuleCat.{max (u + 1) r w} R)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X.1 X.property)

/-- `j_{U!}\underline{M}` is the value at `M` of `AlgebraicGeometry.moduleShriekFunctor`. -/
public theorem moduleShriekFunctor_obj (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type r)
    [CommRing R] (U : SmallEtale B X.1 X.property) (M : ModuleCat.{max (u + 1) r w} R) :
    (moduleShriekFunctor.{u, r, w} B X R U).obj M = moduleShriek.{u, r, w} B X R U M :=
  rfl

/-- At the free rank-one module, `AlgebraicGeometry.moduleShriek` is
`AlgebraicGeometry.moduleShriekConstant`. -/
public theorem moduleShriek_ulift (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type r) [CommRing R]
    (U : SmallEtale B X.1 X.property) :
    moduleShriek.{u, r, w} B X R U (ModuleCat.of R (ULift.{max (u + 1) w} R)) =
      moduleShriekConstant.{u, r, w} B X R U :=
  rfl

/-- **Extension by zero of a constant module sheaf is a left adjoint**, hence preserves colimits:
the constant sheaf functor is left adjoint to evaluation at the final object `U/U` of the small
étale site of `U`, and extension by zero is left adjoint to restriction. -/
public instance isLeftAdjoint_moduleShriekFunctor (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) [CommRing R] (U : SmallEtale B X.1 X.property) :
    (moduleShriekFunctor.{u, r, w} B X R U).IsLeftAdjoint := by
  let := SmallEtale.hasSheafify_moduleCat.{u, r, w} B X R
  let := SmallEtale.hasSheafify_moduleCat.{u, r, w} B U.obj.left R
  have : (constantSheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) r w} R)).IsLeftAdjoint :=
    (constantSheafAdj (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) r w} R)
      (SmallEtale.finalIsTerminal B U.obj.left.1 U.obj.left.property)).isLeftAdjoint
  have : (Functor.sheafPullbackConstruction.sheafPullback
      (smallEtalePostcompose B X.1 X.property U) (ModuleCat.{max (u + 1) r w} R)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X.1 X.property)).IsLeftAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtalePostcompose B X.1 X.property U) (ModuleCat.{max (u + 1) r w} R)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X.1 X.property)).isLeftAdjoint
  exact inferInstanceAs ((constantSheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) r w} R) ⋙
    Functor.sheafPullbackConstruction.sheafPullback
      (smallEtalePostcompose B X.1 X.property U) (ModuleCat.{max (u + 1) r w} R)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X.1 X.property)).IsLeftAdjoint)

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} R)]

/-- The constructible sheaves of `R`-modules on `X_étale`, as a property of objects of the category
of sheaves of `R`-modules, at the universes of this file. -/
private abbrev constructibleModuleSheavesFinite :
    ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} R)) :=
  fun F => IsConstructibleModuleSheaf B X R F

/-- The constructible sheaves of `R`-modules form a weak Serre subcategory; this is Stacks 03RZ (3)
with its coefficient universe pinned to the one of this file. -/
private instance isWeakSerreClass_constructibleModuleSheavesFinite :
    (constructibleModuleSheavesFinite B X R).IsWeakSerreClass :=
  SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B X R

/-- A weak Serre subcategory is closed under finite coproducts: a binary coproduct is a binary
biproduct, hence an extension of one summand by the other. -/
private instance isClosedUnderFiniteCoproducts_constructibleModuleSheavesFinite :
    (constructibleModuleSheavesFinite B X R).IsClosedUnderFiniteCoproducts := by
  have : (constructibleModuleSheavesFinite B X R).IsClosedUnderBinaryCoproducts :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (fun _ ⟨G, hG⟩ =>
      (constructibleModuleSheavesFinite B X R).prop_of_iso
        ((biprod.isoCoprod _ _).trans (HasColimit.isoOfNatIso (diagramIsoPair G)).symm)
        ((constructibleModuleSheavesFinite B X R).prop_biprod (hG ⟨.left⟩) (hG ⟨.right⟩)))
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- **A finite direct sum of copies of `j_{U!}\underline{Λ}` is constructible.** Extension by
zero of the constant sheaf preserves finite coproducts, being a left adjoint, and the
constructible sheaves of modules are closed under them. -/
public theorem isConstructibleModuleSheaf_moduleShriek_sigma
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] (k : ℕ) :
    IsConstructibleModuleSheaf B X R
      (moduleShriek.{u, u + 1, u + 1} B X R U (ModuleCat.finFreeSigma R k)) :=
  (constructibleModuleSheavesFinite B X R).prop_of_isColimit
    (isColimitOfPreserves (moduleShriekFunctor.{u, u + 1, u + 1} B X R U)
      (coproductIsCoproduct fun _ : Fin k => ModuleCat.of R (ULift.{u + 1} R)))
    (fun _ => isConstructibleModuleSheaf_moduleShriekConstant B X R U)

/-- **Stacks 03S8, part (3).** Let `X` be a quasi-compact and quasi-separated scheme, `Λ` a
Noetherian ring and `M` a finite `Λ`-module. For `U` a quasi-compact and quasi-separated object of
the small étale site of `X`, the extension by zero `j_{U!}\underline{M}` is a constructible sheaf
of `Λ`-modules on `X_étale`.

By `ModuleCat.exists_cokernel_finFreeSigma_of_finite` the module `M` is the cokernel of a map
between finite direct sums of copies of `Λ`. Extension by zero of the constant sheaf is a left
adjoint, so it carries that presentation to one of `j_{U!}\underline{M}` as the cokernel of a map
between finite direct sums of copies of `j_{U!}\underline{Λ}`, which are constructible. -/
@[stacks 03S8 "part (3)"]
public theorem isConstructibleModuleSheaf_moduleShriek
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj]
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] :
    IsConstructibleModuleSheaf B X R (moduleShriek.{u, u + 1, u + 1} B X R U M) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := ModuleCat.exists_cokernel_finFreeSigma_of_finite R M
  refine (constructibleModuleSheavesFinite B X R).prop_of_iso
    ((PreservesCokernel.iso (moduleShriekFunctor.{u, u + 1, u + 1} B X R U) f).symm ≪≫
      (moduleShriekFunctor.{u, u + 1, u + 1} B X R U).mapIso e)
    ((constructibleModuleSheavesFinite B X R).prop_cokernel
      ((moduleShriekFunctor.{u, u + 1, u + 1} B X R U).map f)
      (isConstructibleModuleSheaf_moduleShriek_sigma B X R U m)
      (isConstructibleModuleSheaf_moduleShriek_sigma B X R U n))

end AlgebraicGeometry

end
