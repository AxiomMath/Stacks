module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.EquivalenceOverBase
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.UnitComplexMaps

/-!
# Global sections on a scheme over a field, `k`-linearly

Let `k` be a field and `f : X ⟶ Spec(k)`. Two identifications of global sections are recorded
here, both over `k` rather than merely additively, because Serre duality on a curve computes a
dimension and an additive bijection does not determine one.

* Maps out of the structure sheaf are the global sections: `Hom_{𝒪_X}(𝒪_X, ℱ) = Γ(X, ℱ)`, and
  the right-hand side is `H^0(X, ℱ)`.
* For `f` quasi-compact and quasi-separated, the global sections over `Spec(k)` of the `n`-th
  higher direct image of the structure sheaf is the cohomology module
  `AlgebraicGeometry.structureSheafCohomology f n` from which the genus of [Stacks, Tag 0BY7] is
  defined. This is [Stacks, Tag 01XK] over the affine base, read in the `k`-linear spelling.

## Main definitions

* `AlgebraicGeometry.CurveDuality.unitHomLinearEquiv` — `Hom_{𝒪_X}(𝒪_X, ℱ) ≃ₗ[k] Γ(X, ℱ)`.
* `AlgebraicGeometry.CurveDuality.unitHomCohomologyZeroLinearEquiv` — the same with the
  right-hand side read as `H^0(X, ℱ)`.
* `AlgebraicGeometry.CurveDuality.gammaRightDerivedCohomologyOverFieldIso` —
  `Γ(Spec(k), R^n f_* ℱ) ≅ H^n(X, ℱ)` for `ℱ` quasi-coherent.
* `AlgebraicGeometry.CurveDuality.gammaRightDerivedIso` and
  `AlgebraicGeometry.CurveDuality.gammaRightDerivedLinearEquiv` — the same at the structure
  sheaf, in the `structureSheafCohomology` spelling.

## Implementation notes

The `k`-linear structure on `𝒪_X`-modules is `AlgebraicGeometry.modulesLinear`, installed with
`letI` because it depends on the structure morphism, which instance search cannot recover from
`X`. The scalar acts inside the source of a morphism by multiplication by
`AlgebraicGeometry.baseRingToSections`, which over the whole space is the ring map
`AlgebraicGeometry.restrictScalars` acts by; that is the only computation in
`AlgebraicGeometry.CurveDuality.unitHomLinearEquiv`, and it is the one
`AlgebraicGeometry.globalSectionsOver_linear` makes.

The bijection itself is `Stacks.Cohomology.LeftDualPerfect.unitHomOfTop` and its two round-trip
identities; the structure sheaf has to be given the type ascription `show X.Modules from` because
`AlgebraicGeometry.Scheme.Modules` is not a reducible definition and the Hom-group instance is
not found without it.

`AlgebraicGeometry.CurveDuality.gammaRightDerivedIso` is
`Stacks.Cohomology.AffineBase.affineBaseHigherDirectImageIso` with scalars restricted along
`AlgebraicGeometry.Scheme.ΓSpecIso`. On the higher-direct-image side that restriction is already
what `AlgebraicGeometry.moduleSpecΓFunctor` is, so no comparison is needed there; on the
cohomology side the two successive restrictions are collapsed by
`ModuleCat.restrictScalarsComp'App` and matched to
`AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField`.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.CurveDuality

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A base scalar acts on a morphism of modules by multiplication by its image in the functions
on each open, read inside the source. -/
private theorem smul_val_app_top {M N : X.Modules} (a : k) (φ : M ⟶ N)
    (x : M.val.obj (op (⊤ : X.Opens))) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    (a • φ).val.app (op ⊤) x =
      φ.val.app (op ⊤) (baseRingToSections k (Over.mk f) (op ⊤) a • x) :=
  rfl

/-- **Maps out of the structure sheaf are the global sections, `k`-linearly.** A map is
determined by the image of the unit section over the whole space, and the base scalar acts on
both sides by multiplication by its image in `Γ(X, 𝒪_X)`. -/
def unitHomLinearEquiv (M : X.Modules) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M) ≃ₗ[k]
      (globalSectionsOver f).obj M :=
  letI : Linear k X.Modules := modulesLinear k (Over.mk f)
  { toFun := fun φ => φ.val.app (op ⊤) (Stacks.Cohomology.LeftDualPerfect.oneS X.ringCatSheaf)
    map_add' := fun _ _ => rfl
    map_smul' := fun a φ => by
      rw [smul_val_app_top k f a φ, map_smul,
        AlgebraicGeometry.CoherentModuleFunctors.baseRingToSections_top]
      rfl
    invFun := fun s => Stacks.Cohomology.LeftDualPerfect.unitHomOfTop M s
    left_inv := fun φ => (Stacks.Cohomology.LeftDualPerfect.eq_unitHomOfTop φ).symm
    right_inv := fun s => Stacks.Cohomology.LeftDualPerfect.unitHomOfTop_app_oneS M s }

/-- `AlgebraicGeometry.CurveDuality.unitHomLinearEquiv` sends a map out of the structure sheaf to
the image of the unit section over the whole space. -/
theorem unitHomLinearEquiv_apply (M : X.Modules)
    (φ : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    unitHomLinearEquiv k f M φ =
      φ.val.app (op ⊤) (Stacks.Cohomology.LeftDualPerfect.oneS X.ringCatSheaf) :=
  rfl

/-- **Maps out of the structure sheaf are the degree-zero cohomology, `k`-linearly.** The global
sections of a module are its `H^0` over the ground field, by
`AlgebraicGeometry.cohomologyOverFieldZeroIsoSections`. -/
def unitHomCohomologyZeroLinearEquiv (M : X.Modules) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M) ≃ₗ[k]
      cohomologyOverField k f M 0 :=
  letI : Linear k X.Modules := modulesLinear k (Over.mk f)
  (unitHomLinearEquiv k f M).trans
    (cohomologyOverFieldZeroIsoSections k f M).toLinearEquiv.symm

/-- **Global sections over `Spec(k)` of the `n`-th higher direct image of a quasi-coherent module
is its `n`-th cohomology over the ground field.** This is [Stacks, Tag 01XK] over the affine base
`Spec(k)`, with scalars restricted to `k`. -/
def gammaRightDerivedCohomologyOverFieldIso [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    [hF : F.IsQuasicoherent] (n : ℕ) :
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj F) ≅
      cohomologyOverField k f F n := by
  have e0 := (Stacks.Cohomology.AffineBase.affineBaseHigherDirectImageIso f n).app ⟨F, hF⟩
  have e1 := (ModuleCat.restrictScalars.{u}
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).mapIso e0
  have e2 := ModuleCat.restrictScalarsComp'App
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom f.appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom rfl
    (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).obj F)
  have e3 := (ModuleCat.restrictScalarsCongr (comp_appTop_hom_eq_comp_appLE_hom' k f)).app
    (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).obj F)
  exact e1.symm ≪≫ e2.symm ≪≫ e3

/-- **Global sections over `Spec(k)` of the `n`-th higher direct image of the structure sheaf is
the cohomology module that defines the genus.** -/
def gammaRightDerivedIso [QuasiCompact f] [QuasiSeparated f] (n : ℕ) :
    moduleSpecΓFunctor.obj
        (((Scheme.Modules.pushforward f).rightDerived n).obj
          (SheafOfModules.unit X.ringCatSheaf)) ≅
      structureSheafCohomology f n :=
  gammaRightDerivedCohomologyOverFieldIso k f (SheafOfModules.unit X.ringCatSheaf) n ≪≫
    (structureSheafCohomologyIsoCohomologyOverField k f n).symm

/-- `AlgebraicGeometry.CurveDuality.gammaRightDerivedIso` as a `k`-linear equivalence. -/
def gammaRightDerivedLinearEquiv [QuasiCompact f] [QuasiSeparated f] (n : ℕ) :
    moduleSpecΓFunctor.obj
        (((Scheme.Modules.pushforward f).rightDerived n).obj
          (SheafOfModules.unit X.ringCatSheaf)) ≃ₗ[k]
      structureSheafCohomology f n :=
  (gammaRightDerivedIso k f n).toLinearEquiv

end AlgebraicGeometry.CurveDuality

end
