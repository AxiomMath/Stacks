module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtendScalarsAdjunction

/-!
# Right derived functors corepresented through the underlying abelian sheaf

Let `R` be a sheaf of rings on a site and let `G : Mod(R) ⥤ Ab` be a left exact additive functor
which, through the forgetful functor to abelian sheaves, is corepresented by the sheafification
`P^#` of a sectionwise torsion-free abelian presheaf `P`:

`G ≅ Hom_{Ab}(P^#, (-)_ab)`.

Then the right derived functors of `G` are the `Ext`-groups out of `P^#` of the underlying abelian
sheaf:

`RᵠG(M) ≅ Ext^q_{Ab}(P^#, M_ab)`.

This is the comparison of **Stacks 03FD** with sections replaced by an arbitrary functor
corepresented by a torsion-free sheaf. `G` is corepresented on `Mod(R)` by the sheafified
extension of scalars `(R ⊗ P)^#` (`Stacks.SheafOfModules.tensorSheafHomIso`), so its right derived
functors are the `Ext`-groups out of `(R ⊗ P)^#`
(`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived`); and those are the `Ext`-groups
of the underlying abelian sheaves out of `P^#` by the universality of `Ext` as a δ-functor
(`ModuleSheafCohomology.extComparisonIso`), whose acyclicity input is that the underlying abelian
sheaf of an injective module has no higher `Ext` out of a torsion-free sheaf
(`Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree`).

The case used in **Stacks 0775** (2) is `G` the sections over an object `y` of the direct image
along a 1-morphism of algebraic stacks, and `P` the free abelian presheaf on the presheaf
represented by the 2-fibre product over `y`.

## Main results

* `Stacks.SheafOfModules.nonempty_rightDerived_iso_toSheaf_comp_extFunctorObj`: the comparison.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

universe t r v

namespace Stacks.SheafOfModules

variable {C : Type t} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max r t}] [J.WEqualsLocallyBijective AddCommGrpCat.{max r t}]
  [HasExt.{max r t} (Sheaf J AddCommGrpCat.{max r t})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max r t})]
  (R : Sheaf J RingCat.{r})
  [HasExt.{max r t} (SheafOfModules.{max r t} R)] [EnoughInjectives (SheafOfModules.{max r t} R)]

/-- **The right derived functors of a functor corepresented through the underlying abelian sheaf
by a torsion-free sheaf are the `Ext`-groups out of it.** If `G ≅ Hom_{Ab}(P^#, (-)_ab)` with `P`
sectionwise torsion-free, then `RᵠG ≅ Ext^q_{Ab}(P^#, (-)_ab)`. -/
theorem nonempty_rightDerived_iso_toSheaf_comp_extFunctorObj
    (G : SheafOfModules.{max r t} R ⥤ AddCommGrpCat.{max r t}) [G.Additive]
    [PreservesFiniteLimits G] (P : Cᵒᵖ ⥤ AddCommGrpCat.{max r t})
    (hP : ∀ U, Module.IsTorsionFree ℤ
      (((presheafToSheaf J AddCommGrpCat.{max r t}).obj P).obj.obj U))
    (α : G ≅ SheafOfModules.toSheaf R ⋙
      preadditiveCoyoneda.obj (op ((presheafToSheaf J AddCommGrpCat.{max r t}).obj P)))
    (q : ℕ) :
    Nonempty (G.rightDerived q ≅ SheafOfModules.toSheaf R ⋙
      extFunctorObj ((presheafToSheaf J AddCommGrpCat.{max r t}).obj P) q) := by
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{max r t} R) :=
    Stacks.SheafOfModules.toSheaf_preservesFiniteColimits R
  let Y := (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (Stacks.SheafOfModules.tensorPresheaf R.obj P)
  let e₁ := Stacks.SheafOfModules.tensorSheafHomIso J R P
  obtain ⟨e₂⟩ := ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived G Y
    (α ≪≫ e₁.symm) q
  exact ⟨e₂.symm ≪≫ ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R)
    ((presheafToSheaf J AddCommGrpCat.{max r t}).obj P) Y
    (fun I _ m e => Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree J R I _ hP m e) e₁ q⟩

end Stacks.SheafOfModules

end
