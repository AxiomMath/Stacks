module

public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.Basic
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.TildeExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Modules.TildeSymmetricPower

/-!
# The affine exterior-power comparison on a wedge of global sections

`Stacks.AffineExteriorPower.tildeExteriorPowerIso` compares `(⋀ⁿ_R M)~` with `⋀ⁿ(M̃)`, and
`Stacks.AffineExteriorPower.exteriorPowerΓIso` reads that comparison on global sections.
**This file evaluates it on the global sections that determine it**: the comparison carries the
global section of `(⋀ⁿ_R M)~` attached to `m₁ ∧ ⋯ ∧ mₙ` to the wedge, in `⋀(M̃)`, of the global
sections of `M̃` attached to the `mᵢ`.

The wedges `m₁ ∧ ⋯ ∧ mₙ` span `⋀ⁿ_R M`, and a morphism out of an associated sheaf is determined
by its values on the canonical global sections (the transpose
`AlgebraicGeometry.tilde.adjunction.homEquiv` is a bijection), so this equation determines the
comparison.

## Main results

* `Stacks.AffineExteriorPower.tildeExteriorPowerIso_hom_ιMulti`: **the comparison on a wedge of
  global sections.**
* `Stacks.AffineExteriorPower.exteriorPowerΓIso_inv_ιMulti`: the same equation read through the
  global-sections form: the inverse of `Γ(Spec R, ⋀ⁿ(M̃)) ≅ ⋀ⁿ_R M` carries `m₁ ∧ ⋯ ∧ mₙ` to the
  wedge of the corresponding global sections of `M̃`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AssociatedSheaf
open scoped TensorProduct

universe u

namespace Stacks.AffineExteriorPower

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (n : ℕ)

/-! ### The comparison of Tag 01I7 on canonical global sections -/

/-- The presheaf-level comparison on the global section `1 ⊗ x` is the base-change comparison of
exterior powers at the ring of global sections. -/
theorem specTildeExteriorPowerPresheafIso_unit (x : ↥(⋀[↥R]^n ↥M)) :
    letI : Algebra ↥R ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) :=
      ((globalSectionsMap (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom).app
        (specGlobalOpen R)).hom.toAlgebra
    PresheafOfModules.Hom.app (specTildeExteriorPowerPresheafIso R (Spec R).toRingedSpace
          (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
        (specTildePresheafUnit R (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) x) =
      ExteriorAlgebra.intPieceBaseChange ↥R
        ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ↥M n
        ((1 : ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))) ⊗ₜ[↥R] x) :=
  rfl

/-- **The presheaf-level comparison on a wedge.** It carries `1 ⊗ (m₁ ∧ ⋯ ∧ mₙ)` to the
sectionwise wedge of the sections `1 ⊗ mᵢ`. -/
theorem specTildeExteriorPowerPresheafIso_unit_ιMulti (s : Fin n → ↥M) :
    PresheafOfModules.Hom.app (specTildeExteriorPowerPresheafIso R (Spec R).toRingedSpace
          (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
        (specTildePresheafUnit R (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M))
          (exteriorPower.ιMulti ↥R n s)) =
      (exteriorPower.ιMulti
          ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) n
          (fun i => specTildePresheafUnit R M (s i)) :
        ⋀[↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))]^n
          ((specTildePresheaf R M).obj (specGlobalOpen R))) := by
  let : Algebra ↥R ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) :=
    ((globalSectionsMap (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom).app
      (specGlobalOpen R)).hom.toAlgebra
  refine Eq.trans (specTildeExteriorPowerPresheafIso_unit M n _) ?_
  refine Subtype.ext ?_
  refine Eq.trans (congrArg Subtype.val
    (ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti ↥R
      ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ↥M n 1 s)) ?_
  exact congrArg Subtype.val (one_smul
    ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) _)

/-! ### The comparison for the chosen bundle -/

/-- The comparison for the chosen bundle of algebras on a canonical global section, written out
as the three legs it is built from: the comparison of Tag 01I7, the sheafified presheaf-level
comparison, and the presheaf-model comparison. -/
theorem tildeExteriorPowerIso_hom_toOpen (x : ↥(⋀[↥R]^n ↥M)) :
    (AlgebraicGeometry.tildeExteriorPowerIso R M n).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) ⊤).hom x) =
      (SheafOfModules.presheafModelExteriorPowerIso (Opens.grothendieckTopology ↥(Spec R))
          (specTildePresheaf R M) (specTildeAlgebras R M) (specTildeModel R M)
          (n : ℤ)).hom.val.app (specGlobalOpen R)
        (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
            (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
            (PresheafOfModules.exteriorAlgebraPiece (n : ℤ) (specTildePresheaf R M)))
          (specGlobalOpen R)
          (PresheafOfModules.Hom.app (specTildeExteriorPowerPresheafIso R
              (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
            (specTildePresheafUnit R (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) x))) :=
  congrArg
    ((SheafOfModules.presheafModelExteriorPowerIso (Opens.grothendieckTopology ↥(Spec R))
      (specTildePresheaf R M) (specTildeAlgebras R M) (specTildeModel R M)
      (n : ℤ)).hom.val.app (specGlobalOpen R))
    (Eq.trans
      (congrArg (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafification
          (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)).map
            (specTildeExteriorPowerPresheafIso R (Spec R).toRingedSpace
              (Scheme.ΓSpecIso R).inv.hom M n).hom).val (specGlobalOpen R))
        (AlgebraicGeometry.tildeModel_toOpen R (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) x))
      (PresheafOfModules.unit_naturality_apply
        (α := 𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
        (specTildeExteriorPowerPresheafIso R (Spec R).toRingedSpace
          (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
        (specTildePresheafUnit R (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) x)))

/-- **The comparison for the chosen bundle on a wedge of global sections.** -/
theorem specTildeExteriorPowerIso_hom_ιMulti (s : Fin n → ↥M) :
    (AlgebraicGeometry.tildeExteriorPowerIso R M n).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) ⊤).hom
          (exteriorPower.ιMulti ↥R n s)) =
      (specTildeAlgebras R M).exterior.toPresheafGradedAlgebra.homogeneousProd
        (specGlobalOpen R) n
        (fun i => (specTildeAlgebras R M).exteriorGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen M ⊤).hom (s i))) := by
  rw [tildeExteriorPowerIso_hom_toOpen, specTildeExteriorPowerPresheafIso_unit_ιMulti]
  refine (SheafOfModules.presheafModelExteriorPowerIso_ιMulti
    (Opens.grothendieckTopology ↥(Spec R)) _ _ _ n _ _).trans ?_
  exact congrArg ((specTildeAlgebras R M).exterior.toPresheafGradedAlgebra.homogeneousProd
      (specGlobalOpen R) n)
    (funext fun i => congrArg
      ((specTildeAlgebras R M).exteriorGenerator.val.app (specGlobalOpen R))
      (AlgebraicGeometry.tildeModel_inv_unit R M (s i)))

/-! ### The comparison for an arbitrary bundle -/

open SheafOfModules.TensorExteriorSymmetricAlgebras in
/-- The canonical comparison between the exterior algebras of two bundles respects ordered
products of degree-one local sections. -/
theorem exteriorAlgebraIso_homogeneousProd
    {F : SheafOfModules.{u} (Spec R).ringCatSheaf}
    (A B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) F)
    (k : ℕ) (U : ((Spec R).Opens)ᵒᵖ) (z : Fin k → (A.exterior.piece 1).val.obj U) :
    (exteriorAlgebraIso A B (k : ℤ)).hom.val.app U
        (A.exterior.toPresheafGradedAlgebra.homogeneousProd U k z) =
      B.exterior.toPresheafGradedAlgebra.homogeneousProd U k
        (fun i => (exteriorAlgebraIso A B 1).hom.val.app U (z i)) :=
  SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd
    (A.exterior_isExteriorAlgebra.isUniversal.desc B.exterior B.exteriorGenerator
      B.exterior_isExteriorAlgebra.1) U k z

/-- **The affine exterior-power comparison on a wedge of global sections.** The global section of
`(⋀ⁿ_R M)~` attached to `m₁ ∧ ⋯ ∧ mₙ` is carried to the ordered product, in `⋀(M̃)`, of the
degree-one generators at the global sections of `M̃` attached to the `mᵢ`. -/
@[stacks 01I8 "exterior_power"]
theorem tildeExteriorPowerIso_hom_ιMulti
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M)) (s : Fin n → ↥M) :
    (((tilde.adjunction (R := R)).homEquiv (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M))
          (A.exteriorPower n)) (tildeExteriorPowerIso M A n).hom).hom
        (exteriorPower.ιMulti ↥R n s) =
      A.exterior.toPresheafGradedAlgebra.homogeneousProd (specGlobalOpen R) n
        (fun i => A.exteriorGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen M ⊤).hom (s i))) := by
  refine Eq.trans (congrArg
    ((SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso
      (specTildeAlgebras R M) A (n : ℤ)).hom.val.app (specGlobalOpen R))
    (specTildeExteriorPowerIso_hom_ιMulti M n s)) ?_
  refine Eq.trans (exteriorAlgebraIso_homogeneousProd (specTildeAlgebras R M) A n
    (specGlobalOpen R) _) ?_
  refine congrArg (A.exterior.toPresheafGradedAlgebra.homogeneousProd (specGlobalOpen R) n)
    (funext fun i => ?_)
  exact congrArg (fun k : (tilde M : SheafOfModules.{u} (Spec R).ringCatSheaf) ⟶
      A.exterior.piece 1 => k.val.app (specGlobalOpen R) ((tilde.toOpen M ⊤).hom (s i)))
    (SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso_generator
      (specTildeAlgebras R M) A)

/-- **The global-sections comparison on a wedge.** The inverse of
`Γ(Spec R, ⋀ⁿ(M̃)) ≅ ⋀ⁿ_R M` carries `m₁ ∧ ⋯ ∧ mₙ` to the wedge of the global sections of `M̃`
attached to the `mᵢ`. -/
theorem exteriorPowerΓIso_inv_ιMulti
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M)) (s : Fin n → ↥M) :
    (exteriorPowerΓIso M A n).inv.hom (exteriorPower.ιMulti ↥R n s) =
      A.exterior.toPresheafGradedAlgebra.homogeneousProd (specGlobalOpen R) n
        (fun i => A.exteriorGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen M ⊤).hom (s i))) :=
  tildeExteriorPowerIso_hom_ιMulti M n A s

end Stacks.AffineExteriorPower

end
