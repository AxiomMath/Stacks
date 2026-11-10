module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.Flat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AcyclicSheavesFilteredColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleCohomologyForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsTensorConstantDerived
public import StacksFrontier.Homology.TotalComplexTransport
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections of a tensor product with a constant complex

Let `X` be a quasi-compact and quasi-separated scheme, `E ∈ D⁺(X_étale)` and `K ∈ D⁺(ℤ)`.
[Stacks, Tag 0F0E] asserts

> `RΓ(X, E ⊗_ℤ^L K̲) = RΓ(X, E) ⊗_ℤ^L K`.

This file proves it. Abelian sheaves on the small étale site are taken as sheaves of modules over
the integers lifted to the coefficient universe `u + 1`, `ULift.{u + 1} ℤ`, which is the setting
of the derived tensor product of sheaves of modules (`Stacks.ModuleSheaf.derivedMonoidal`) and of
the derived constant sheaf on complexes (`Stacks.ModuleSheaf.derivedConstantSheafComplexes`).

## Main definitions

* `tensorConstComparison`: the canonical comparison `Γ(X, F) ⊗ M ⟶ Γ(X, F ⊗ M̲)`, the
  Eilenberg–Watts comparison of the functor `M ↦ Γ(X, F ⊗ M̲)`, natural in `F` and in `M`.
* `totalTensorIso`: for a complex `I` of sheaves and a complex `P` of flat modules, the
  comparison of complexes `Γ(X, I) ⊗ P ≅ Γ(X, I ⊗ P̲)`.

## Main results

* `isIso_tensorConstComparison`: the comparison is invertible at every flat module.
* `rightAcyclic_tensor_const`: `F ⊗ M̲` is acyclic for `Γ(X, -)` when `F` is and `M` is flat.
* `rightAcyclic_tensorObj_X`: the terms of `I ⊗ P̲` are acyclic when those of `I` are and those
  of `P` are flat.
* `nonempty_derivedSections_tensor_derivedConstantSheaf_iso`: **[Stacks, Tag 0F0E]**, for any
  right derived functor `RΓ(X, -)` of the global sections on the unbounded derived category, and
  `nonempty_totalRightDerived_tensor_derivedConstantSheaf_iso`, the same for the total right
  derived functor.

## The proof

The source reduces, by two nested dévissages along stupid truncations, to a single sheaf and a
single flat module, and settles that case by writing the module as a filtered colimit of free
modules of finite rank. The argument here keeps the second half and replaces the dévissages by
one acyclic resolution, which computes both sides at once.

Represent `E` by a bounded below complex `I` of injective sheaves and `K` by a bounded below
complex `P` of flat modules, strictly `≥ b - 1` if `K` is `≥ b` (`ℤ` has global dimension one:
`CochainComplex.ULiftInt.exists_flat_isStrictlyGE_iso`). Then `P̲` is K-flat, so
`E ⊗_ℤ^L K̲ = I ⊗ P̲`, and `P` is K-flat, so `RΓ(X, E) ⊗_ℤ^L K = Γ(X, I) ⊗ P`, using that the
bounded below complex `I` of injectives computes `RΓ(X, E)`. Two facts remain.

* *`Γ(X, I) ⊗ P ≅ Γ(X, I ⊗ P̲)` as complexes.* Bidegreewise this is the comparison
  `Γ(X, Iᵃ) ⊗ Pᵇ ⟶ Γ(X, Iᵃ ⊗ P̲ᵇ)` at a flat module, and global sections commute with the direct
  sums of the totalisation.
* *`Γ(X, I ⊗ P̲) ≅ RΓ(X, I ⊗ P̲)`.* The complex `I ⊗ P̲` is bounded below, and each of its terms is
  a direct sum of sheaves `Iᵃ ⊗ P̲ᵇ` with `Iᵃ` acyclic and `Pᵇ` flat, hence acyclic; Leray's
  acyclicity lemma (`Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic`) applies.

Both facts rest on the case of one sheaf `F` and one flat module `M`:
`Hᵖ(X, F) ⊗ M ≅ Hᵖ(X, F ⊗ M̲)` for every `p`, steps 6 to 8 of the source. For each `p` the functor
`M ↦ Hᵖ(X, F ⊗ M̲)` is additive and, `X` being quasi-compact and quasi-separated, commutes with
filtered colimits (Stacks 03Q5, `preservesColimitsOfShape_rightDerived_Γm`, transported from
abelian sheaves through `Stacks.EtaleCohomology.etaleModuleCohomologyForgetIso`). Its
Eilenberg–Watts comparison is therefore invertible at every flat module
(`Stacks.EilenbergWatts.isIso_wattsMap_of_flat`): a flat module is the filtered colimit of its
finitely generated submodules, which are free of finite rank. The same filtered colimits give
the commutation of cohomology with direct sums.

## Implementation notes

*The right derived functor is a hypothesis of the statement, not a choice.* The theorem is
stated for any `RΓ : D(X_étale) ⥤ D(ℤ)` with a unit `α` making it a right derived functor of
`Γ(X, -)` along the localization of the homotopy category, which is what `RΓ(X, -)` means; such
a functor exists (`hasRightDerivedFunctor_Γm`), and the corollary
`nonempty_totalRightDerived_tensor_derivedConstantSheaf_iso` states the result for the total right
derived functor. The unbounded derived category is used: `RΓ` on `D⁺` is its restriction, and
`E ⊗_ℤ^L K̲` is again bounded below
(`Stacks.ModuleSheaf.isGE_derivedTensor_derivedConstantSheafComplexes`).

*Any model of the derived categories.* Both derived categories are taken with arbitrary
`HasDerivedCategory` instances; the derived tensor product of `D(ℤ)` is
`CochainComplex.KFlatMonoidal.derivedMonoidal` with the K-flat resolutions of
`CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso`.

## References

* [Stacks Project, Tag 0F0E](https://stacks.math.columbia.edu/tag/0F0E)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe t t' u

namespace Stacks.EtaleCohomology.DerivedTensorConstant

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
  Stacks.ModuleSheaf.monoidalClosed CochainComplex.braidedCategory

variable (X : Scheme.{u})

/-- Shorthand for `Stacks.EtaleCohomology.EtaleModules` at the integers lifted to the coefficient
universe `u + 1`: the abelian étale sheaves of the source, as sheaves of modules. -/
abbrev Sh := EtaleModules.{u, u + 1} (ULift.{u + 1} ℤ) X

/-- Shorthand for `Stacks.EtaleCohomology.etaleModuleGlobalSections` at the lifted integers. -/
abbrev Γm : Sh X ⥤ ModuleCat.{u + 1} (ULift.{u + 1} ℤ) :=
  etaleModuleGlobalSections.{u, u + 1} (ULift.{u + 1} ℤ) X

/-- The constant sheaf functor, for sheaves of lifted-integer modules on the small étale site. -/
abbrev const : ModuleCat.{u + 1} (ULift.{u + 1} ℤ) ⥤ Sh X :=
  constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))

/-- The constant sheaf functor preserves colimits, being left adjoint to global sections. -/
local instance : PreservesColimits (const X) :=
  (constantSheafΓAdj X.smallEtaleTopology _).leftAdjoint_preservesColimits

/-- The constant sheaf functor is additive, being left adjoint to global sections. -/
local instance : (const X).Additive :=
  (constantSheafΓAdj X.smallEtaleTopology _).left_adjoint_additive

/-- Tensoring with a sheaf `F` preserves colimits, being left adjoint to `ihom F`. -/
local instance (F : Sh X) : PreservesColimits (tensorLeft F) :=
  (ihom.adjunction F).leftAdjoint_preservesColimits

/-- Tensoring with a sheaf `F` is additive, being left adjoint to `ihom F`. -/
local instance (F : Sh X) : (tensorLeft F).Additive :=
  (ihom.adjunction F).left_adjoint_additive

section Colimits

variable [CompactSpace X] [QuasiSeparatedSpace X]

attribute [local instance] Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp

/-- Forgetting the module structure of a sheaf of lifted-integer modules gives an abelian sheaf. -/
local instance : X.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} _ X.smallEtaleTopology

/-- Forgetting the module structure commutes with sheafification. -/
local instance : X.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.preservesSheafification_forget₂.{u + 1} _ X.smallEtaleTopology

/-- **The cohomology of sheaves of lifted-integer modules on a quasi-compact quasi-separated
scheme commutes with filtered colimits**: forgetting the module structure commutes with
cohomology, preserves colimits and reflects them, and on abelian sheaves this is Stacks 03Q5. -/
theorem preservesColimitsOfShape_rightDerived_Γm (p : ℕ) (I : Type (u + 1)) [SmallCategory I]
    [IsFiltered I] : PreservesColimitsOfShape I ((Γm X).rightDerived p) := by
  have : PreservesColimits (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} _
  have : PreservesColimitsOfShape I (etaleModuleForgetAb.{u, u + 1} (ULift.{u + 1} ℤ) X) :=
    preservesColimitsOfShape_sheafCompose _ _ I
  have := preservesColimitsOfShape_rightDerived_Γ_smallEtale.{0} X p I
  have : PreservesColimitsOfShape I ((Γm X).rightDerived p ⋙
      forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}) :=
    preservesColimitsOfShape_of_natIso
      (etaleModuleCohomologyForgetIso.{u, u + 1} (ULift.{u + 1} ℤ) X p).symm
  have : ReflectsColimitsOfShape I
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})

/-- **Global sections on a quasi-compact quasi-separated scheme commute with filtered colimits**
of sheaves of lifted-integer modules. -/
theorem preservesColimitsOfShape_Γm (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (Γm X) :=
  have := preservesColimitsOfShape_rightDerived_Γm X 0 I
  preservesColimitsOfShape_of_natIso (Functor.rightDerivedZeroIsoSelf _)

/-- **The cohomology of a direct sum is the direct sum of the cohomologies**, on a quasi-compact
quasi-separated scheme. -/
theorem preservesColimitsOfShape_discrete_rightDerived_Γm (p : ℕ) (α : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete α) ((Γm X).rightDerived p) :=
  have : PreservesColimitsOfShape (Finset (Discrete α)) ((Γm X).rightDerived p) :=
    preservesColimitsOfShape_rightDerived_Γm X p _
  Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete.{u + 1} _

/-- The same for direct sums indexed by a type in the lowest universe, such as the antidiagonals
along which a total complex is formed. -/
theorem preservesColimitsOfShape_discrete_rightDerived_Γm₀ (p : ℕ) (α : Type) :
    PreservesColimitsOfShape (Discrete α) ((Γm X).rightDerived p) :=
  have := preservesColimitsOfShape_discrete_rightDerived_Γm X p (ULift.{u + 1} α)
  preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

/-- Global sections commute with direct sums indexed by a type in the lowest universe. -/
theorem preservesColimitsOfShape_discrete_Γm₀ (α : Type) :
    PreservesColimitsOfShape (Discrete α) (Γm X) :=
  have := preservesColimitsOfShape_discrete_rightDerived_Γm₀ X 0 α
  preservesColimitsOfShape_of_natIso (Functor.rightDerivedZeroIsoSelf _)

end Colimits

/-! ### Tensoring a sheaf with a constant sheaf, then taking global sections -/

open Stacks.EilenbergWatts

/-- `M ↦ Γ(X, F ⊗ M̲)`, as an endofunctor of modules over the lifted integers. -/
abbrev tensorConstΓ (F : Sh X) :
    ModuleCat.{u + 1} (ULift.{u + 1} ℤ) ⥤ ModuleCat.{u + 1} (ULift.{u + 1} ℤ) :=
  const X ⋙ tensorLeft F ⋙ Γm X

/-- `M ↦ Hᵖ(X, F ⊗ M̲)`, as an endofunctor of modules over the lifted integers. -/
abbrev tensorConstH (F : Sh X) (p : ℕ) :
    ModuleCat.{u + 1} (ULift.{u + 1} ℤ) ⥤ ModuleCat.{u + 1} (ULift.{u + 1} ℤ) :=
  const X ⋙ tensorLeft F ⋙ (Γm X).rightDerived p

/-- The functor `M ↦ Γ(X, F ⊗ M̲)` is linear over the lifted integers. -/
instance (F : Sh X) : (tensorConstΓ X F).Linear (ULift.{u + 1} ℤ) := linear_uliftInt _

/-- The functor `M ↦ Hᵖ(X, F ⊗ M̲)` is linear over the lifted integers. -/
instance (F : Sh X) (p : ℕ) : (tensorConstH X F p).Linear (ULift.{u + 1} ℤ) :=
  linear_uliftInt _

/-- The identification `F ⊗ ℤ̲ ≅ F` underlying the value of `tensorConstΓ X F` at the ring: the
constant sheaf on the ring is the unit of the tensor product of sheaves, so this is the right
unitor. -/
def tensorConstUnitIso (F : Sh X) :
    F ⊗ (const X).obj (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} ℤ)) ≅ F :=
  ρ_ F

/-- **The canonical comparison `Γ(X, F) ⊗ M ⟶ Γ(X, F ⊗ M̲)`.** It is the Eilenberg–Watts
comparison of the functor `M ↦ Γ(X, F ⊗ M̲)`, read through `F ⊗ ℤ̲ ≅ F`: on a pure tensor
`s ⊗ m` it is the image of `s` under the map induced by `F ≅ F ⊗ ℤ̲ ⟶ F ⊗ M̲`, the second arrow
being attached to the morphism `ℤ ⟶ M` with generator `m`. -/
def tensorConstComparison (F : Sh X) (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) :
    (Γm X).obj F ⊗ M ⟶ (Γm X).obj (F ⊗ (const X).obj M) :=
  ((Γm X).map (tensorConstUnitIso X F).inv ▷ M) ≫ wattsMap (tensorConstΓ X F) M

/-- The comparison is natural in the module. -/
@[reassoc]
theorem tensorConstComparison_naturality_right (F : Sh X)
    {M M' : ModuleCat.{u + 1} (ULift.{u + 1} ℤ)} (g : M ⟶ M') :
    ((Γm X).obj F ◁ g) ≫ tensorConstComparison X F M' =
      tensorConstComparison X F M ≫ (Γm X).map (F ◁ (const X).map g) := by
  have h' : ((Γm X).obj (F ⊗ (const X).obj (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} ℤ)))
      ◁ g) ≫ wattsMap (tensorConstΓ X F) M' =
      wattsMap (tensorConstΓ X F) M ≫ (Γm X).map (F ◁ (const X).map g) :=
    wattsMap_naturality (tensorConstΓ X F) g
  dsimp only [tensorConstComparison]
  rw [whisker_exchange_assoc, h', Category.assoc]

/-- The comparison is natural in the sheaf. -/
@[reassoc]
theorem tensorConstComparison_naturality_left {F F' : Sh X} (f : F ⟶ F')
    (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) :
    ((Γm X).map f ▷ M) ≫ tensorConstComparison X F' M =
      tensorConstComparison X F M ≫ (Γm X).map (f ▷ (const X).obj M) := by
  let θ : tensorConstΓ X F ⟶ tensorConstΓ X F' :=
    Functor.whiskerLeft (const X) (Functor.whiskerRight ((curriedTensor (Sh X)).map f) (Γm X))
  dsimp only [tensorConstComparison]
  rw [Category.assoc]
  change _ = _ ≫ wattsMap (tensorConstΓ X F) M ≫ θ.app M
  rw [wattsMap_natTrans θ M, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  congr 2
  change (Γm X).map f ≫ (Γm X).map (tensorConstUnitIso X F').inv =
    (Γm X).map (tensorConstUnitIso X F).inv ≫ (Γm X).map (f ▷ _)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (Γm X).map (rightUnitor_inv_naturality f)

section Flat

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- `ULift ℤ` is a domain. -/
local instance : IsDomain (ULift.{u + 1} ℤ) :=
  MulEquiv.isDomain ℤ (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toMulEquiv

/-- `ULift ℤ` is a principal ideal ring. -/
local instance : IsPrincipalIdealRing (ULift.{u + 1} ℤ) :=
  IsPrincipalIdealRing.of_surjective (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).symm.toRingHom
    (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).symm.surjective

/-- `M ↦ Γ(X, F ⊗ M̲)` commutes with filtered colimits on a quasi-compact quasi-separated
scheme. -/
theorem preservesColimitsOfShape_tensorConstΓ (F : Sh X) (I : Type (u + 1)) [SmallCategory I]
    [IsFiltered I] : PreservesColimitsOfShape I (tensorConstΓ X F) :=
  have := preservesColimitsOfShape_Γm X I
  inferInstance

/-- `M ↦ Hᵖ(X, F ⊗ M̲)` commutes with filtered colimits on a quasi-compact quasi-separated
scheme. -/
theorem preservesColimitsOfShape_tensorConstH (F : Sh X) (p : ℕ) (I : Type (u + 1))
    [SmallCategory I] [IsFiltered I] : PreservesColimitsOfShape I (tensorConstH X F p) :=
  have := preservesColimitsOfShape_rightDerived_Γm X p I
  inferInstance

/-- **Stacks 0F0E, steps 7 and 8, in degree zero.** On a quasi-compact quasi-separated scheme
the comparison `Γ(X, F) ⊗ M ⟶ Γ(X, F ⊗ M̲)` is an isomorphism for every sheaf `F` and every flat
module `M`. -/
instance isIso_tensorConstComparison (F : Sh X) (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    [Module.Flat (ULift.{u + 1} ℤ) M] : IsIso (tensorConstComparison X F M) := by
  have := isIso_wattsMap_of_flat (tensorConstΓ X F) M
    (preservesColimitsOfShape_tensorConstΓ X F _)
  dsimp only [tensorConstComparison]
  infer_instance

/-- The comparison `Γ(X, F) ⊗ M ≅ Γ(X, F ⊗ M̲)` at a flat module, as an isomorphism. -/
def tensorConstComparisonIso (F : Sh X) (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    [Module.Flat (ULift.{u + 1} ℤ) M] :
    (Γm X).obj F ⊗ M ≅ (Γm X).obj (F ⊗ (const X).obj M) :=
  asIso (tensorConstComparison X F M)

/-- The forward map of `tensorConstComparisonIso X F M` is `tensorConstComparison X F M`. -/
@[simp]
theorem tensorConstComparisonIso_hom (F : Sh X) (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    [Module.Flat (ULift.{u + 1} ℤ) M] :
    (tensorConstComparisonIso X F M).hom = tensorConstComparison X F M := rfl

variable [HasDerivedCategory.{t} (Sh X)]
  [HasDerivedCategory.{t'} (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))]

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- Injective sheaves are acyclic for global sections. -/
theorem rightAcyclic_of_injective (I : Sh X) [Injective I] : (Γm X).rightAcyclic I := by
  rw [CategoryTheory.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact Functor.isZero_rightDerived_obj_injective_succ _ q I

/-- **Stacks 0F0E, steps 7 and 8, in positive degrees, for an acyclic sheaf.** On a
quasi-compact quasi-separated scheme, if `F` is acyclic for global sections and `M` is a flat
module, then `F ⊗ M̲` is acyclic for global sections: `Hᵖ(X, F ⊗ M̲) ≅ Hᵖ(X, F) ⊗ M`. -/
theorem rightAcyclic_tensor_const (F : Sh X) (hF : (Γm X).rightAcyclic F)
    (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) [Module.Flat (ULift.{u + 1} ℤ) M] :
    (Γm X).rightAcyclic (F ⊗ (const X).obj M) := by
  rw [CategoryTheory.rightAcyclic_iff_isZero_rightDerived] at hF ⊢
  intro p hp
  have := isIso_wattsMap_of_flat (tensorConstH X F p) M
    (preservesColimitsOfShape_tensorConstH X F p _)
  have h0 : IsZero ((tensorConstH X F p).obj
      (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} ℤ))) :=
    (hF p hp).of_iso (((Γm X).rightDerived p).mapIso (tensorConstUnitIso X F))
  refine IsZero.of_iso ?_ (asIso (wattsMap (tensorConstH X F p) M)).symm
  refine (IsZero.iff_id_eq_zero _).2 ?_
  change 𝟙 (((tensorConstH X F p).obj (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} ℤ))) ⊗ M) = 0
  rw [← id_whiskerRight, h0.eq_of_src (𝟙 _) 0, MonoidalPreadditive.zero_whiskerRight]

end Flat

/-! ### Complexes -/

section Complexes

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- The constant sheaf functor applied degreewise to complexes of modules. -/
abbrev constC : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ℤ ⥤
    CochainComplex (Sh X) ℤ :=
  (const X).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Global sections applied degreewise to complexes of sheaves. -/
abbrev ΓC : CochainComplex (Sh X) ℤ ⥤ CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ℤ :=
  (Γm X).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Global sections preserve the direct sums indexed by the bidegrees of total degree `n`. -/
local instance (n : ℤ) : PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) (Γm X) :=
  preservesColimitsOfShape_discrete_Γm₀ X _

variable (I : CochainComplex (Sh X) ℤ) (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ℤ)

/-- The bicomplex `Γ(X, Iᵃ) ⊗ Pᵇ`, whose total complex is `Γ(X, I) ⊗ P`. -/
abbrev bicomplexΓTensor : HomologicalComplex₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((curriedTensor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj ((ΓC X).obj I)).obj P

/-- The bicomplex `Iᵃ ⊗ P̲ᵇ` of sheaves, whose total complex is `I ⊗ P̲`. -/
abbrev bicomplexTensor : HomologicalComplex₂ (Sh X) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((curriedTensor (Sh X)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj I).obj ((constC X).obj P)

/-- **The comparison of bicomplexes `Γ(X, Iᵃ) ⊗ Pᵇ ≅ Γ(X, Iᵃ ⊗ P̲ᵇ)`**, for a complex `P` of flat
modules: it is the comparison `tensorConstComparison` in each bidegree, invertible there by
steps 7 and 8, and its two naturality squares are the two commutations with the differentials. -/
def bicomplexIso (hP : ∀ q, Module.Flat (ULift.{u + 1} ℤ) (P.X q)) :
    bicomplexΓTensor X I P ≅ HomologicalComplex₂.mapBicomplex (Γm X) (bicomplexTensor X I P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun a => HomologicalComplex.Hom.isoOfComponents
      (fun b => have := hP b; tensorConstComparisonIso X (I.X a) (P.X b))
      (fun b b' _ => (tensorConstComparison_naturality_right X (I.X a) (P.d b b')).symm))
    (fun a a' _ => HomologicalComplex.Hom.ext (funext fun b =>
      (tensorConstComparison_naturality_left X (I.d a a') (P.X b)).symm))

/-- **The complex-level comparison `Γ(X, I) ⊗ P ≅ Γ(X, I ⊗ P̲)`**, for a complex `P` of flat
modules on a quasi-compact quasi-separated scheme. Bidegreewise it is `tensorConstComparison`;
that global sections commute with the totalisation is the commutation of `Γ(X, -)` with direct
sums on such a scheme. -/
def totalTensorIso (hP : ∀ q, Module.Flat (ULift.{u + 1} ℤ) (P.X q)) :
    (ΓC X).obj I ⊗ P ≅ (ΓC X).obj (I ⊗ (constC X).obj P) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso X I P hP) (ComplexShape.up ℤ) ≪≫
    HomologicalComplex₂.totalIso (Γm X) (bicomplexTensor X I P)

variable [HasDerivedCategory.{t} (Sh X)]
  [HasDerivedCategory.{t'} (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))]

/-- **The terms of `I ⊗ P̲` are acyclic** when those of `I` are and those of `P` are flat: each is
a direct sum of sheaves `Iᵃ ⊗ P̲ᵇ`, acyclic by steps 7 and 8, and cohomology commutes with direct
sums on a quasi-compact quasi-separated scheme. -/
theorem rightAcyclic_tensorObj_X (hI : ∀ n, (Γm X).rightAcyclic (I.X n))
    (hP : ∀ q, Module.Flat (ULift.{u + 1} ℤ) (P.X q)) (n : ℤ) :
    (Γm X).rightAcyclic ((I ⊗ (constC X).obj P).X n) := by
  have hc := (bicomplexTensor X I P).toGradedObject.isColimitCofanMapObj
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n
  refine Stacks.DerivedFunctor.rightAcyclic_of_isColimit (Γm X) hc (fun p _ => ?_) (fun j => ?_)
  · have := preservesColimitsOfShape_discrete_rightDerived_Γm₀ X p
      ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {n})
    infer_instance
  · obtain ⟨⟨⟨a, b⟩, _⟩⟩ := j
    have := hP b
    exact rightAcyclic_tensor_const X (I.X a) (hI a) (P.X b)

end Complexes

/-! ### The derived statement -/

section Derived

variable [CompactSpace X] [QuasiSeparatedSpace X]
  [HasDerivedCategory.{t} (Sh X)] [HasDerivedCategory.{t'} (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))]

attribute [local instance] Stacks.ModuleSheaf.derivedMonoidal

/-- The image in the derived category of the unit of a right derived functor, at the class of a
complex, read on complexes: `Γ(X, T) ⟶ RΓ(X, T)`. -/
def unitIso {RΓ : DerivedCategory (Sh X) ⥤ DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))}
    (α : (Γm X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΓ) (T : CochainComplex (Sh X) ℤ)
    (h : IsIso (α.app ((HomotopyCategory.quotient (Sh X) (ComplexShape.up ℤ)).obj T))) :
    DerivedCategory.Q.obj ((ΓC X).obj T) ≅ RΓ.obj (DerivedCategory.Q.obj T) :=
  ((DerivedCategory.quotientCompQhIso _).app ((ΓC X).obj T)).symm ≪≫
    @asIso _ _ _ _ (α.app ((HomotopyCategory.quotient (Sh X) (ComplexShape.up ℤ)).obj T)) h ≪≫
    RΓ.mapIso ((DerivedCategory.quotientCompQhIso _).app T)

/-- **[Stacks, Tag 0F0E].** Let `X` be a quasi-compact and quasi-separated scheme, let
`E ∈ D⁺(X_étale)` and `K ∈ D⁺(ℤ)`. Then

> `RΓ(X, E ⊗_ℤ^L K̲) ≅ RΓ(X, E) ⊗_ℤ^L K`.

Here abelian sheaves are sheaves of modules over the integers lifted to the coefficient
universe, `E ⊗_ℤ^L K̲` is the derived tensor product of `E` with the derived constant sheaf on
`K`, `RΓ(X, -)` is any right derived functor of the global sections on the unbounded derived
category, and the right-hand side is the derived tensor product of `D(ℤ)`.

The isomorphism is the composite of the canonical identifications: `E` is represented by a
bounded below complex `I` of injective sheaves and `K` by a bounded below complex `P` of flat
modules (`ℤ` has global dimension one), so that `E ⊗_ℤ^L K̲ = I ⊗ P̲` and
`RΓ(X, E) ⊗_ℤ^L K = Γ(X, I) ⊗ P`; the comparison `Γ(X, I) ⊗ P ⟶ Γ(X, I ⊗ P̲)` is an isomorphism
of complexes (`totalTensorIso`), and `Γ(X, I ⊗ P̲) ⟶ RΓ(X, I ⊗ P̲)` is an isomorphism because
`I ⊗ P̲` is a bounded below complex of acyclic sheaves (`rightAcyclic_tensorObj_X`). Both use that
`X` is quasi-compact and quasi-separated, through the commutation of étale cohomology with
filtered colimits (Stacks 03Q5): a flat module is the filtered colimit of free modules of finite
rank (Stacks 058G), for which `Hᵖ(X, F ⊗ M̲) = Hᵖ(X, F) ⊗ M` is additivity. -/
@[stacks 0F0E]
theorem nonempty_derivedSections_tensor_derivedConstantSheaf_iso
    (RΓ : DerivedCategory (Sh X) ⥤ DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (α : (Γm X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso (Sh X) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Sh X)) (a : ℤ) [E.IsGE a]
    (K : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (b : ℤ) [K.IsGE b] :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso (ULift.{u + 1} ℤ))
    Nonempty (RΓ.obj (E ⊗ (Stacks.ModuleSheaf.derivedConstantSheafComplexes.{t, t', u + 1, u, u + 1}
        X.smallEtaleTopology).obj K) ≅ RΓ.obj E ⊗ K) := by
  let := CochainComplex.KFlatMonoidal.derivedMonoidal (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso (ULift.{u + 1} ℤ))
  obtain ⟨N, hN, ⟨eN⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE E a
  obtain ⟨L, i, hi, hinj, hL⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective N a
  obtain ⟨P, hP, hflat, ⟨eP⟩⟩ := CochainComplex.ULiftInt.exists_flat_isStrictlyGE_iso K b
  have hcyc := CochainComplex.ULiftInt.flat_cycles P hflat
  have hkfP := Stacks.ModuleSheaf.kFlat_of_isStrictlyGE_of_flat P (b - 1) hflat hcyc
  have hkf := Stacks.ModuleSheaf.kFlat_constantSheaf_of_isStrictlyGE_of_flat
    X.smallEtaleTopology P (b - 1) hflat hcyc
  have : IsIso (DerivedCategory.Q.map i) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ i).2 hi
  let eE : E ≅ DerivedCategory.Q.obj L := eN ≪≫ asIso (DerivedCategory.Q.map i)
  have hacL : ∀ n, (Γm X).rightAcyclic (L.X n) := fun n =>
    have := hinj n
    rightAcyclic_of_injective X (L.X n)
  have := CochainComplex.KFlatMonoidal.isStrictlyGE_tensorObj (Sh X) L ((constC X).obj P) a (b - 1)
  have h1 : IsIso (α.app ((HomotopyCategory.quotient (Sh X) (ComplexShape.up ℤ)).obj L)) :=
    Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic (Γm X) RΓ α L ⟨a, hL⟩ hacL
  have h2 : IsIso (α.app ((HomotopyCategory.quotient (Sh X) (ComplexShape.up ℤ)).obj
      (L ⊗ (constC X).obj P))) :=
    Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic (Γm X) RΓ α _ ⟨a + (b - 1), this⟩
      (rightAcyclic_tensorObj_X X L P hacL hflat)
  let D : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ⥤ DerivedCategory (Sh X) :=
    Stacks.ModuleSheaf.derivedConstantSheafComplexes.{t, t', u + 1, u, u + 1} X.smallEtaleTopology
  let eD : DerivedCategory.Q ⋙ D ≅ (constC X) ⋙ DerivedCategory.Q :=
    Stacks.ModuleSheaf.derivedConstantSheafComplexesFactors.{t, t', u + 1, u, u + 1}
      X.smallEtaleTopology
  let e1 : E ⊗ D.obj K ≅ DerivedCategory.Q.obj (L ⊗ (constC X).obj P) :=
    (eE ⊗ᵢ (D.mapIso eP.symm ≪≫ eD.app P)) ≪≫ Stacks.ModuleSheaf.derivedTensorIsoOfKFlat L hkf
  let e2 : RΓ.obj E ⊗ K ≅ DerivedCategory.Q.obj ((ΓC X).obj L ⊗ P) :=
    ((RΓ.mapIso eE ≪≫ (unitIso X α L h1).symm) ⊗ᵢ eP.symm) ≪≫
      ((CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso _
        (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso (ULift.{u + 1} ℤ))).app
          _).app _ ≪≫
      CochainComplex.KFlatBifunctor.comparisonRight _ ((ΓC X).obj L) P hkfP
  exact ⟨RΓ.mapIso e1 ≪≫ (unitIso X α _ h2).symm ≪≫
    DerivedCategory.Q.mapIso (totalTensorIso X L P hflat).symm ≪≫ e2.symm⟩

/-- **Derived global sections exist on the unbounded derived category** of sheaves of
lifted-integer modules on the small étale site: these sheaves form a Grothendieck abelian
category, in which every complex has a K-injective resolution (Stacks 079P). -/
instance hasPointwiseRightDerivedFunctor_Γm :
    ((Γm X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso (Sh X) (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian (Sh X))

/-- Global sections have a right derived functor on the unbounded derived category of sheaves of
lifted-integer modules on the small étale site. -/
instance hasRightDerivedFunctor_Γm :
    ((Γm X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sh X) (ComplexShape.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **[Stacks, Tag 0F0E] for the total right derived functor of global sections.** The
statement `nonempty_derivedSections_tensor_derivedConstantSheaf_iso`, at the right derived functor
`RΓ(X, -) : D(X_étale) ⥤ D(ℤ)` given by the total right derived functor of `Γ(X, -)` on the
homotopy category. -/
theorem nonempty_totalRightDerived_tensor_derivedConstantSheaf_iso
    (E : DerivedCategory (Sh X)) (a : ℤ) [E.IsGE a]
    (K : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (b : ℤ) [K.IsGE b] :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso (ULift.{u + 1} ℤ))
    Nonempty ((((Γm X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived
          DerivedCategory.Qh (HomotopyCategory.quasiIso (Sh X) (ComplexShape.up ℤ))).obj
          (E ⊗ (Stacks.ModuleSheaf.derivedConstantSheafComplexes.{t, t', u + 1, u, u + 1}
            X.smallEtaleTopology).obj K) ≅
      (((Γm X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso (Sh X) (ComplexShape.up ℤ))).obj E ⊗ K) :=
  nonempty_derivedSections_tensor_derivedConstantSheaf_iso X _
    (((Γm X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso (Sh X) (ComplexShape.up ℤ))) E a K b

end Derived

end Stacks.EtaleCohomology.DerivedTensorConstant

end
