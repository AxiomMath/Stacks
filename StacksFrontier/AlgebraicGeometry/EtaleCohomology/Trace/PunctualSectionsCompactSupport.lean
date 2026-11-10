module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPartStalkCompactSupport
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineCurveDirectImageCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDimensionZeroHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PurityComplexBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# Punctual sections and compactly supported sections

Let `k` be a finite field, `X` separated of finite type over `k` with a compactification, `k̄` an
algebraic closure of `k`, `i : Z ⟶ X` a closed immersion with `Z` reduced and finite over `k`, and
`j : V ⟶ X` the open immersion of the complement. For a sheaf `T` of `Λ`-modules on `X_étale`,
the sections of `T` supported on `Z` form the kernel `H` of the unit `T → j_* j⁻¹ T`. Since
`j⁻¹ H = 0`, the open–closed sequence (Tag 095L) gives `H ≅ i_* i⁻¹ H`, and the stalk of `H` at
the geometric point over a point `y` of `Z` embeds into `H⁰_c(X_k̄, i_* i⁻¹ H)`
(`Stacks.EtaleCohomology.closedPartStalkCompactSupportInput`), which embeds into
`H⁰_c(X_k̄, T)`, `H⁰_c` being left exact
(`Stacks.EtaleCohomology.mono_compactSupportSheafCohomology_zero_map`). Hence if
`H⁰_c(X_k̄, T) = 0`, the stalk at `ȳ` of the unit `T → j_* j⁻¹ T` is injective: `T` has no
sections supported at `ȳ`
(`Stacks.EtaleCohomology.injective_sheafFiber_unit_of_isZero_compactSupportSheafCohomology`).

This is how the absence of compactly supported sections over `k̄` of `G = R¹pr₂! K` excludes
punctual sections of `G` in Laumon's degeneration argument
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.isZero_inverseImage_kernel_unit_of_isOpenImmersion`.
* `Stacks.EtaleCohomology.injective_sheafFiber_unit_of_isZero_compactSupportSheafCohomology`.

## Implementation notes

`compactSupportFrobeniusFunctor` lives in the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Support

variable (Λ : Type) [Ring Λ] {X V : Scheme.{u}} (jV : V ⟶ X) [IsOpenImmersion jV]

omit [IsOpenImmersion jV] in
/-- **The sections supported off an open `V` vanish on `V`**: the inverse image along the open
immersion `j : V ⟶ X` of the kernel of the unit `T → j_* j⁻¹ T` is zero. -/
theorem isZero_inverseImage_kernel_unit_of_isOpenImmersion (T : EtaleModules.{u, 0} Λ X) :
    IsZero ((etaleModuleInverseImage.{u, 0} Λ jV).obj
      (kernel ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app T))) := by
  let adj := etaleModuleInverseImageAdj.{u, 0} Λ jV
  let L := etaleModuleInverseImage.{u, 0} Λ jV
  have : PreservesFiniteLimits L := etaleModuleInverseImage_preservesFiniteLimits Λ jV
  have htri : L.map (adj.unit.app T) ≫ adj.counit.app (L.obj T) = 𝟙 _ :=
    adj.left_triangle_components T
  have : Mono (L.map (adj.unit.app T)) := mono_of_mono_fac htri
  have hz : L.map (kernel.ι (adj.unit.app T)) = 0 := by
    rw [← cancel_mono (L.map (adj.unit.app T)), ← L.map_comp, kernel.condition, L.map_zero,
      zero_comp]
  have : Mono (L.map (kernel.ι (adj.unit.app T))) := inferInstance
  exact IsZero.of_mono_eq_zero _ hz

variable {Z : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ]
  (hij : Set.range jV.base = (Set.range iZ.base)ᶜ)

include hij in
/-- **A sheaf vanishing on `V` is the direct image of its restriction to the complement `Z`**:
the unit `H → i_* i⁻¹ H` is an isomorphism when `j⁻¹ H = 0`. -/
theorem isIso_closedPart_unit_of_isZero_inverseImage (H : EtaleModules.{u, 0} Λ X)
    (hH : IsZero ((etaleModuleInverseImage.{u, 0} Λ jV).obj H)) :
    IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ iZ).unit.app H) := by
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ iZ jV hij H
  refine hS.isIso_g_iff.2 ?_
  have : (etaleModuleExtensionByZero.{u, 0} Λ jV).IsLeftAdjoint :=
    (etaleModuleExtensionByZeroAdj.{u, 0} Λ jV).isLeftAdjoint
  exact (etaleModuleExtensionByZero.{u, 0} Λ jV).map_isZero
    (hH.of_iso ((etaleModuleInverseImageRestrictionIso Λ jV).app H).symm)

end Support

section Punctual

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Finite k] {X Z V : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar] (iZ : Z ⟶ X) [IsClosedImmersion iZ] [IsReduced Z] [IsFinite (iZ ≫ f)]
  (jV : V ⟶ X) [IsOpenImmersion jV] (hij : Set.range jV.base = (Set.range iZ.base)ᶜ)
  (y : X) (hy : y ∈ Set.range iZ.base) [Finite (X.residueField y)]

include hij hy in
/-- **No punctual sections without compactly supported sections**: if `H⁰_c(X_k̄, T) = 0`, the
stalk at the geometric point over `y ∈ Z` of the unit `T → j_* j⁻¹ T` is injective. -/
theorem injective_sheafFiber_unit_of_isZero_compactSupportSheafCohomology
    (T : EtaleModules.{u, 0} Λ X)
    (hT : IsZero ((compactSupportSheafCohomology Λ f j kbar 0).obj T)) :
    Function.Injective
      ((Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt X y).hom).sheafFiber
        (A := ModuleCat.{u + 1} Λ) |>.map
          ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app T)).hom := by
  have := Fintype.ofFinite k
  obtain ⟨p, _⟩ := CharP.exists k
  obtain ⟨n, hpr, hn⟩ := FiniteField.card k p
  have : Fact p.Prime := ⟨hpr⟩
  let u := (etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app T
  let Φ := (Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt X y).hom).sheafFiber
    (A := ModuleCat.{u + 1} Λ)
  let H := kernel u
  have hH0 : IsZero ((compactSupportSheafCohomology Λ f j kbar 0).obj H) := by
    have := mono_compactSupportSheafCohomology_zero_map Λ f j kbar (kernel.ι u)
    exact IsZero.of_mono ((compactSupportSheafCohomology Λ f j kbar 0).map (kernel.ι u)) hT
  have := isIso_closedPart_unit_of_isZero_inverseImage Λ jV iZ hij H
    (isZero_inverseImage_kernel_unit_of_isOpenImmersion Λ jV T)
  have hHZ : IsZero ((compactSupportSheafCohomology Λ f j kbar 0).obj
      ((etaleModuleClosedPart Λ iZ).obj H)) :=
    hH0.of_iso ((compactSupportSheafCohomology Λ f j kbar 0).mapIso
      (asIso ((etaleModuleInverseImageAdj.{u, 0} Λ iZ).unit.app H))).symm
  obtain ⟨-, -, -, s, hs, -⟩ := closedPartStalkCompactSupportInput f j kbar p n hn iZ y hy Λ
  have hΦH : IsZero (Φ.obj H) := by
    have : Subsingleton ((etaleModuleClosedPart Λ iZ ⋙ compactSupportSheafCohomology Λ f j kbar
        0).obj H) := ModuleCat.isZero_iff_subsingleton.1 hHZ
    exact ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => hs H (Subsingleton.elim _ _)⟩
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} (ModuleCat.{u + 1} Λ)
  have : Mono (Φ.map u) := Preadditive.mono_of_isZero_kernel' _
    (isLimitForkMapOfIsLimit' Φ (kernel.condition u)
      (IsLimit.ofIsoLimit (kernelIsKernel u) (Fork.ext (Iso.refl _) (by simp)))) hΦH
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

end Punctual

end Stacks.EtaleCohomology

end
