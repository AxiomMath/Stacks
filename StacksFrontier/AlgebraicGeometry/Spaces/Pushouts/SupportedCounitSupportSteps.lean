module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedDerivedCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective

/-!
# Supports and the open complement in the proof of Stacks 0AEU

Let `Y` be an algebraic space and `V ⊆ Y` an open subspace, with inclusion `j : V ⟶ Y`. The proof
of Stacks 0AEU replaces a K-injective complex `I` representing `Q ∈ D(𝒪_Y)`, supported on the
closed complement `W` of `V`, by the complex `Γ_W I = ker(I ⟶ j_*j^*I)`. This file proves the
statements about supports that this uses.

## Main results

* `AlgebraicGeometry.Space.isZero_openSubspaceRestriction_iff_disjoint`: an `𝒪_Y`-module restricts
  to zero on `V` exactly when its support does not meet `|V|`.
* `AlgebraicGeometry.Space.disjoint_supportOfSheaf_sectionsOffOpen`: the module `Γ_W M` is
  supported off `|V|`, for every `𝒪_Y`-module `M`; it restricts to zero on `V` because
  `j^*j_* ≅ 𝟭` (`AlgebraicGeometry.Space.isIso_etaleModulePullbackAdjunction_counit`).
* `AlgebraicGeometry.Space.supportOfSheaf_homology_subset`: the cohomology sheaves of a complex
  of `𝒪_Y`-modules whose terms are supported on `T` are supported on `T`.
* Together with `AlgebraicGeometry.Space.acyclic_openSubspaceRestriction_of_isZero`, the first
  result shows that a complex whose cohomology sheaves are supported off `|V|` restricts to an
  acyclic complex on `V`.

## Implementation notes

The acyclicity statement itself is stated in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedDerivedCounit`, whose imports leave the
abelian structure of the modules to instance search; stated here, the homology of the restricted
complex meets the universe-polymorphic sheafification instances of the imports of
`StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkExactness` and leaves an unsolvable
universe constraint.

The abelian structure of the `𝒪_Y`-modules is the local instance
`AlgebraicGeometry.Space.smallEtaleModulesAbelian`, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkExactness`. Supports are read on the
geometric stalks `AlgebraicGeometry.Space.geometricModuleStalk`
(`AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk`), the stalk of a
restriction at a point of `V` being the stalk at its image
(`AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_etaleModulePullback_iff`).

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Supports of cohomology sheaves -/

section Morphisms

attribute [local instance 10000] smallEtaleModulesAbelian

variable (X : AlgebraicSpaces B S hS)

/-- **Termwise support bounds the support of cohomology.** If every term of a complex of
`𝒪_X`-modules is supported on `T`, so is every cohomology sheaf: `Hⁿ` is a quotient of the
cycles, which are a submodule of the degree `n` term. -/
theorem supportOfSheaf_homology_subset (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (T : Set (points B S hS X.1))
    (hK : ∀ n, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (K.X n)) ⊆ T) (n : ℤ) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf.{u} _).obj (K.homology n)) ⊆ T :=
  (supportOfSheaf_toSheaf_subset_of_epi B S hS X (K.homologyπ n)).trans
    ((supportOfSheaf_toSheaf_subset_of_mono B S hS X (K.iCycles n)).trans (hK n))

end Morphisms

/-! ### Restriction to an open subspace -/

section OpenSubspace

variable {Y : AlgebraicSpaces B S hS} (V : Subfunctor Y.1) (hV : IsOpenSubspace B S hS V)

/-- A module whose support does not meet an open subspace restricts to zero on it. -/
theorem isZero_openSubspaceRestriction_of_disjoint (M : Modules.{u, u} B S hS Y.1 Y.2)
    (h : Disjoint (supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj M))
      (Set.range (pointsMap B S hS V.toFunctor V.ι))) :
    IsZero ((openSubspaceRestriction B S hS V hV).obj M) := by
  refine (isZero_iff_subsingleton_geometricModuleStalk B S hS (openSubspaceSpace B S hS V hV)
    _).2 fun v ↦ ?_
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  have hnt' := (nontrivial_geometricModuleStalk_etaleModulePullback_iff B S hS
    (openSubspaceHom B S hS V hV) (isEtale_openSubspaceHom B S hS V hV) v M).1 hnt
  have hmem := (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS Y M _).2
    ⟨_, rfl, hnt'⟩
  exact Set.disjoint_left.1 h hmem ⟨v.image, (geometricPointMap_image _ _).symm⟩

/-- A module restricting to zero on an open subspace has support disjoint from it. -/
theorem disjoint_of_isZero_openSubspaceRestriction (M : Modules.{u, u} B S hS Y.1 Y.2)
    (h : IsZero ((openSubspaceRestriction B S hS V hV).obj M)) :
    Disjoint (supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj M))
      (Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨w, rfl⟩
  obtain ⟨xbar, hxbar, hnt⟩ :=
    (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS Y M _).1 hx
  obtain ⟨wbar, -, hval⟩ := exists_geometricPoint_lift_of_isEtale B S hS hV.1 Y.2 V.ι
    (isEtale_openSubspaceHom B S hS V hV) xbar w hxbar.symm
  have heq : geometricPointMap V.ι wbar = xbar := Subtype.ext hval
  have hnt' : Nontrivial (geometricModuleStalk B S hS (openSubspaceSpace B S hS V hV) wbar
      ((openSubspaceRestriction B S hS V hV).obj M)) :=
    (nontrivial_geometricModuleStalk_etaleModulePullback_iff B S hS
      (openSubspaceHom B S hS V hV) (isEtale_openSubspaceHom B S hS V hV) wbar M).2
      (heq ▸ hnt)
  exact not_nontrivial_iff_subsingleton.2
    ((isZero_iff_subsingleton_geometricModuleStalk B S hS _ _).1 h wbar) hnt'

/-- **A module restricts to zero on an open subspace exactly when its support does not meet
it.** -/
theorem isZero_openSubspaceRestriction_iff_disjoint (M : Modules.{u, u} B S hS Y.1 Y.2) :
    IsZero ((openSubspaceRestriction B S hS V hV).obj M) ↔
      Disjoint (supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj M))
        (Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
  ⟨disjoint_of_isZero_openSubspaceRestriction B S hS V hV M,
    isZero_openSubspaceRestriction_of_disjoint B S hS V hV M⟩

/-- **`Γ_W M` is supported off the open subspace.** The sections supported on the closed
complement `W` of `V` restrict to zero on `V`, the counit `j^*j_* ⟶ 𝟭` of an open immersion being
invertible. -/
theorem disjoint_supportOfSheaf_sectionsOffOpen (M : Modules.{u, u} B S hS Y.1 Y.2) :
    Disjoint
      (supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf _).obj ((sectionsOffOpen B S hS V hV).obj M)))
      (Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
  have h₀ := isZero_openSubspaceRestriction_sectionsOffOpen B S hS V hV M
  exact disjoint_of_isZero_openSubspaceRestriction B S hS V hV _ h₀

end OpenSubspace

end AlgebraicGeometry.Space

end
