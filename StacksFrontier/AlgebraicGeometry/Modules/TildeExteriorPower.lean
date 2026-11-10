module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import StacksFrontier.AlgebraicGeometry.Modules.TildeSymmetricPower
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerPresheafModel

/-!
# Exterior powers of associated sheaves on an affine scheme

For a module `M` over a commutative ring `R` and `n : ℕ`, the sheaf associated to the `n`-th
exterior power `⋀ⁿ_R M` is canonically the `n`-th exterior power, in the sense of Stacks
Section 17.21, of the associated sheaf of `M` on `Spec R`.

## Main definitions

* `AlgebraicGeometry.specTildeExteriorPowerPointIso`: the base-change comparison
  `𝒪(U) ⊗_R ⋀ⁿ_R M ≅ ⋀ⁿ_{𝒪(U)}(𝒪(U) ⊗_R M)` over one open.
* `AlgebraicGeometry.specTildeExteriorPowerPresheafIso`: the same comparison as an isomorphism
  of presheaves of modules.
* `AlgebraicGeometry.tildeExteriorPowerIso`: the comparison `(⋀ⁿ_R M)~ ≅ ⋀ⁿ(M~)` on
  `Spec R`.

## Implementation notes

The route is the one used for the symmetric powers of this tag in
`StacksFrontier.AlgebraicGeometry.Modules.TildeSymmetricPower`, and it factors through the same
presheaf model: `M~` is the sheafification of `U ↦ 𝒪(U) ⊗_R M`
(`Stacks.AssociatedSheaf.associatedPresheaf`, Tag 01I7), the degree-`n` exterior power of a
sheaf of modules is the sheafification of the sectionwise exterior power of any presheaf model
of it (`SheafOfModules.presheafModelExteriorPowerIso`), and the sectionwise exterior power of
that particular model is the model of `(⋀ⁿ_R M)~` because exterior powers commute with base
change (`ExteriorAlgebra.exteriorPowerBaseChange`). The three identifications compose to the
comparison.

The exterior case is not a specialisation of the symmetric one: the two universal properties
differ in their degree-one constraint — the exterior generator is square-zero, the symmetric one
commutes — so the generation argument for the exterior algebra runs through
`PresheafOfModules.isExteriorAlgebra_sheafify_exteriorAlgebra` rather than its symmetric
namesake. The base-change comparison here is built from the alternating-map universal property,
so it needs neither flatness nor a hypothesis on the characteristic, and the degree-two relation
`x ∧ x = 0` is never weakened to antisymmetry.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AssociatedSheaf
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

/-- The `n`-th exterior power of `M`, in the `ℤ`-graded spelling `ExteriorAlgebra.intPiece` that
the presheaves of sectionwise exterior powers are built from.

It is `⋀ⁿ_R M` definitionally (`ExteriorAlgebra.intPiece_natCast`), and it is spelled this way
throughout because the unifier cannot afford the other direction: matching `⋀[A]^n` against a
sectionwise exterior power unfolds both to `LinearMap.range (ExteriorAlgebra.ι A) ^ n` and then
compares two presentations of the exterior algebra. -/
noncomputable abbrev exteriorPowerSource (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (n : ℕ) :
    ModuleCat.{u} ↥R :=
  ModuleCat.of ↥R ↥(ExteriorAlgebra.intPiece ↥R ↥M (n : ℤ))

/-! ### The presheaf-level comparison -/

section Presheaf

variable (R : CommRingCat.{u}) (X : RingedSpace.{u, u}) (α : ↥R →+* X.presheaf.obj (op ⊤))
  (M : ModuleCat.{u} R) (n : ℕ)

/-- The base-change comparison `𝒪(U) ⊗_R ⋀ⁿ_R M ≅ ⋀ⁿ_{𝒪(U)}(𝒪(U) ⊗_R M)` over one open.

The two sides are the sections over `U` of the two presheaves compared by
`specTildeExteriorPowerPresheafIso`; the identification is `exteriorPowerBaseChange` with no
retyping, because the sections of the sectionwise exterior power are the exterior power of the
sections (`ExteriorAlgebra.intPiece_natCast`). -/
noncomputable def specTildeExteriorPowerPointIso (U : (Opens X.carrier)ᵒᵖ) :
    (associatedPresheaf X α (exteriorPowerSource R M n)).obj U ≅
      (PresheafOfModules.exteriorAlgebraPiece (n : ℤ) (associatedPresheaf X α M)).obj U := by
  letI : Algebra ↥R ↥(X.presheaf.obj U) := ((globalSectionsMap X α).app U).hom.toAlgebra
  exact (ExteriorAlgebra.intPieceBaseChange ↥R ↥(X.presheaf.obj U) ↥M n).toModuleIso

/-- The presheaf-level comparison: the presheaf `U ↦ 𝒪(U) ⊗_R ⋀ⁿ_R M` whose sheafification is
`(⋀ⁿ_R M)~` is the sectionwise degree-`n` exterior power of the presheaf `U ↦ 𝒪(U) ⊗_R M` whose
sheafification is `M~`. -/
noncomputable def specTildeExteriorPowerPresheafIso :
    associatedPresheaf X α (exteriorPowerSource R M n) ≅
      PresheafOfModules.exteriorAlgebraPiece (n : ℤ) (associatedPresheaf X α M) := by
  refine PresheafOfModules.isoMk
    (fun U ↦ specTildeExteriorPowerPointIso R X α M n U) (fun {U V} f ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun t ↦ ?_)
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg (fun z ↦ z + _) hx).trans
        ((congrArg (fun z ↦ _ + z) hy).trans (map_add _ x y).symm))
  | tmul a x =>
      refine Subtype.ext ?_
      let : Algebra ↥R ↥(X.presheaf.obj U) := ((globalSectionsMap X α).app U).hom.toAlgebra
      let : Algebra ↥R ↥(X.presheaf.obj V) := ((globalSectionsMap X α).app V).hom.toAlgebra
      refine (ExteriorAlgebra.intPieceBaseChange_naturality
        (R := ↥R) (A := ↥(X.presheaf.obj U)) (B := ↥(X.presheaf.obj V)) (M := ↥M)
        (φ := ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf X.presheaf).map f).hom) ?_
        (u := (associatedPresheaf X α M).restrictₛₗ f) ?_ n a x).symm
      · exact fun r => (congrArg
          (fun g : (constantRingPresheaf X ↥R).obj U ⟶ X.presheaf.obj V =>
            (ConcreteCategory.hom g) r) ((globalSectionsMap X α).naturality f)).symm
      · exact fun m => congrArg (fun b : ↥(X.presheaf.obj V) => b ⊗ₜ[↥R] m)
          (map_one (X.presheaf.map f).hom)

end Presheaf

/-! ### The comparison -/

section Comparison

variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (n : ℕ)

/-- The `n`-th exterior power of the sheaf associated to `M` on `Spec R`. -/
noncomputable abbrev specTildeExteriorPower : (Spec R).Modules :=
  (specTildeAlgebras R M).exteriorPower n

/-- The associated sheaf of the `n`-th exterior power is canonically the `n`-th exterior power
of the associated sheaf, the exterior-power part of [Stacks, Tag 01I8]. -/
noncomputable def tildeExteriorPowerIso :
    tilde (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) ≅ specTildeExteriorPower R M n :=
  (tildeAssociatedSheafNatIso R).val.app (exteriorPowerSource R M n) ≪≫
    (PresheafOfModules.sheafification
        (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)).mapIso
      (specTildeExteriorPowerPresheafIso R (Spec R).toRingedSpace
        (Scheme.ΓSpecIso R).inv.hom M n) ≪≫
    SheafOfModules.presheafModelExteriorPowerIso (Opens.grothendieckTopology ↥(Spec R))
      (specTildePresheaf R M) (specTildeAlgebras R M) (specTildeModel R M) (n : ℤ)

end Comparison

end AlgebraicGeometry

end
