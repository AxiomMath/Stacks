module

public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.AffineOpen
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineFormsMapSections
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical map on differential forms, on the sections over an affine open

Let `f : X' ⟶ X` be a morphism of schemes over `S`, and let `V ⊆ S`, `U ⊆ X`, `U' ⊆ X'` be opens
with `U ≤ p⁻¹V`, `U' ≤ f⁻¹U` and `U'` affine.  Writing `R := Γ(S, V)`, `A := Γ(X, U)` and
`B := Γ(X', U')`, **this file identifies the sections over `U'` of the canonical map

`f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S}`

of [Stacks, Tag 0FL5] with `exteriorPower.map n (KaehlerDifferential.mapBaseChange R A B)`.**

Only the source chart `U'` is assumed affine; `X`, `X'` and `S` are arbitrary schemes.

## Main definitions

* `formsPullbackAffineOpenΓIso`: the comparison `Γ(f^*Ω^n_{X/S}, U') ≅ ⋀ⁿ_B Γ(f^*Ω_{X/S}, U')`,
  the comparison of Tag 01CI followed by the comparison of Tag 01I8 on the affine open `U'`.

## Main results

* `relativeDifferentialFormsMap_app_conj_apply`: conjugating the sections over `U'` of the
  canonical map on `n`-forms by the two comparisons gives `exteriorPower.map n` of the sections of
  the canonical map on relative differentials.
* `relativeDifferentialFormsMap_app_exteriorPower_map`: if the sections over `U'` of the canonical
  map on relative differentials are a linear map `L` up to comparisons, then the sections over
  `U'` of the canonical map on `n`-forms are `exteriorPower.map n L` up to the corresponding
  comparisons; with `L := KaehlerDifferential.mapBaseChange R A B` this is the identification
  above.

## References

* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AffineExteriorPower (affineOpenExteriorPowerΓIso)
open Stacks.AlgebraicGeometry.AffineDifferentialForms (pullbackFormsIso
  relativeDifferentialFormsMap_eq_pullbackFormsIso_comp)
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenDifferentialForms

variable {X' X S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S)

/-- The sections over an open of a composite of morphisms of modules, on an element. -/
theorem app_comp_apply {Y : Scheme.{u}} {M N P : Y.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (W : Y.Opens) (x : Γ(M, W)) :
    Scheme.Modules.Hom.app (a ≫ b) W x =
      Scheme.Modules.Hom.app b W (Scheme.Modules.Hom.app a W x) :=
  (congr($(Scheme.Modules.Hom.comp_app a b) x)).trans (ConcreteCategory.comp_apply _ _ x)

/-- An isomorphism of modules cancels its inverse on the sections over an open. -/
theorem app_inv_app_cancel {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N) (W : Y.Opens)
    (x : Γ(N, W)) :
    Scheme.Modules.Hom.app e.hom W (Scheme.Modules.Hom.app e.inv W x) = x := by
  rw [← app_comp_apply, e.inv_hom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]

/-- The degree-one generator of the algebra of relative differential forms, typed at the
spelling `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra` rather than at
`AlgebraicGeometry.Scheme.Modules.exteriorAlgebra` of the relative differentials. -/
abbrev relativeDifferentialFormsGenerator {Y : Scheme.{u}} (q : Y ⟶ S) :
    Scheme.Hom.relativeDifferentials q ⟶
      (Scheme.Hom.relativeDifferentialFormsAlgebra q).piece 1 :=
  Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials q)

/-- The algebra of relative differential forms is an exterior algebra of the relative
differentials. -/
@[ega "IV 16.6.1" "Ω•_{X/S} = ∧(Ω^1_{X/S})"]
theorem isExteriorAlgebra_relativeDifferentialFormsAlgebra {Y : Scheme.{u}} (q : Y ⟶ S) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra q).IsExteriorAlgebra
      (relativeDifferentialFormsGenerator q) :=
  Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _

variable {U' : X'.Opens} (hU' : IsAffineOpen U') (n : ℕ)

/-- **The comparison `Γ(f^*Ω^n_{X/S}, U') ≅ ⋀ⁿ_B Γ(f^*Ω_{X/S}, U')`** on an affine open `U'` of
the source: the comparison of Tag 01CI in degree `n`, read on sections, followed by the
comparison of Tag 01I8 on `U'`. -/
def formsPullbackAffineOpenΓIso :
    ModuleCat.of Γ(X', U')
        Γ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms p (n : ℤ)),
          U') ≅
      ModuleCat.of Γ(X', U') (⋀[Γ(X', U')]^n
        Γ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p), U')) :=
  (sectionsLinearEquivOfIso (pullbackFormsIso f p (n : ℤ)) U').toModuleIso ≪≫
    affineOpenExteriorPowerΓIso
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p)) hU'
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n

/-- The inverse of `formsPullbackAffineOpenΓIso` on an element: the inverse of the comparison of
Tag 01I8, followed by the sections over `U'` of the inverse of the comparison of Tag 01CI. -/
theorem formsPullbackAffineOpenΓIso_inv_apply
    (ω : ⋀[Γ(X', U')]^n
      Γ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p), U')) :
    (formsPullbackAffineOpenΓIso f p hU' n).inv ω =
      Scheme.Modules.Hom.app (pullbackFormsIso f p (n : ℤ)).inv U'
        ((affineOpenExteriorPowerΓIso
          ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p)) hU'
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n).inv ω) :=
  rfl

variable (hcomm : f ≫ p = p' ≫ 𝟙 S)

include hcomm in
/-- **Conjugating the sections over an affine open `U'` of the canonical map on `n`-forms by the
two comparisons gives `exteriorPower.map n` of the sections of the canonical map on relative
differentials.** -/
theorem relativeDifferentialFormsMap_app_conj_apply
    (ω : ⋀[Γ(X', U')]^n
      Γ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p), U')) :
    (affineOpenExteriorPowerΓIso (Scheme.Hom.relativeDifferentials p') hU'
          (isExteriorAlgebra_relativeDifferentialFormsAlgebra p') n).hom
        (Scheme.Modules.Hom.app
          (Scheme.Hom.relativeDifferentialFormsMap f p p' (𝟙 S) hcomm (n : ℤ)) U'
          ((formsPullbackAffineOpenΓIso f p hU' n).inv ω)) =
      exteriorPower.map n (Scheme.Modules.sectionsLinearMap
        (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 S) hcomm) U') ω := by
  set c := affineOpenExteriorPowerΓIso
    ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p)) hU'
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n with hc
  have hnat := Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso_natural hU'
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p)))
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra p')
    (Scheme.Hom.relativeDifferentialFormsComparison f p p' (𝟙 S) hcomm)
    (Scheme.Hom.relativeDifferentialFormsComparison_generator f p p' (𝟙 S) hcomm) n
  have hpt := congr($(hnat) (c.inv ω))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply] at hpt
  have hco : c.hom (c.inv ω) = ω := by simp [c]
  have key : Scheme.Modules.Hom.app
        (Scheme.Hom.relativeDifferentialFormsMap f p p' (𝟙 S) hcomm (n : ℤ)) U'
        ((formsPullbackAffineOpenΓIso f p hU' n).inv ω) =
      Scheme.Modules.Hom.app
        ((Scheme.Hom.relativeDifferentialFormsComparison f p p' (𝟙 S) hcomm).app (n : ℤ)) U'
        (c.inv ω) := by
    rw [formsPullbackAffineOpenΓIso_inv_apply, ← hc]
    exact (app_comp_apply _ _ U' _).trans
      (congrArg _ (app_inv_app_cancel (pullbackFormsIso f p (n : ℤ)) U' _))
  exact (congrArg _ key).trans (hpt.trans (congrArg
    (fun z => exteriorPower.map n (Scheme.Modules.sectionsLinearMap
      (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 S) hcomm) U') z) hco))

/-! ### The sections of the canonical map on `n`-forms -/

include hcomm in
/-- **The canonical map on differential `n`-forms of a morphism over `S`, read on the sections
over an affine open `U'` of the source, is the `n`-th exterior power of the map it is in degree
one.**  Precisely: let `T` and `E` be linear maps from two `Γ(X', U')`-modules to the sections
over `U'` of `f^*Ω_{X/S}` and of `Ω_{X'/S}`, and suppose (`hdeg`) that the sections over `U'` of
the canonical map of [Stacks, Tag 01UV] composed with `T` equal `E` composed with `L`. Then,
modulo the comparisons `formsPullbackAffineOpenΓIso` and
`Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso`, the sections over `U'` of the canonical
map on `n`-forms send `exteriorPower.map n T ω` to
`exteriorPower.map n E (exteriorPower.map n L ω)`. -/
theorem relativeDifferentialFormsMap_app_exteriorPower_map
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module Γ(X', U') M₁]
    [AddCommGroup M₂] [Module Γ(X', U') M₂]
    (T : M₁ →ₗ[Γ(X', U')]
      Γ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p), U'))
    (E : M₂ →ₗ[Γ(X', U')] Γ(Scheme.Hom.relativeDifferentials p', U'))
    (L : M₁ →ₗ[Γ(X', U')] M₂)
    (hdeg : (Scheme.Modules.sectionsLinearMap
        (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 S) hcomm) U').comp T = E.comp L)
    (ω : ⋀[Γ(X', U')]^n M₁) :
    (affineOpenExteriorPowerΓIso (Scheme.Hom.relativeDifferentials p') hU'
          (isExteriorAlgebra_relativeDifferentialFormsAlgebra p') n).hom
        (Scheme.Modules.Hom.app
          (Scheme.Hom.relativeDifferentialFormsMap f p p' (𝟙 S) hcomm (n : ℤ)) U'
          ((formsPullbackAffineOpenΓIso f p hU' n).inv (exteriorPower.map n T ω))) =
      exteriorPower.map n E (exteriorPower.map n L ω) := by
  refine (relativeDifferentialFormsMap_app_conj_apply f p p' hU' n hcomm
    (exteriorPower.map n T ω)).trans ?_
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hdeg, exteriorPower.map_comp,
    LinearMap.comp_apply]

end Stacks.AlgebraicGeometry.AffineOpenDifferentialForms

end
