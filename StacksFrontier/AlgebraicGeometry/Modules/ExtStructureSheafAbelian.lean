module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsHomUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.MapAlongAcyclic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.GlobalSectionsCohomologyBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism

/-!
# `Ext` out of the structure sheaf is the cohomology of the underlying abelian sheaf

Let `X` be a scheme. For an `𝒪_X`-module `M`, forgetting the module structure and precomposing
with the section `1 : ℤ ⟶ 𝒪_X` of the constant sheaf gives a map

`Extⁿ_{𝒪_X}(𝒪_X, M) ⟶ Extⁿ_{Ab(X)}(ℤ, M) = Hⁿ(X, M)`.

This file proves it is bijective in every degree. It is compatible with Yoneda products: the
image of `y ∘ e` is the image of `y` composed with `e` read in abelian sheaves. This is the
comparison of [Stacks, Tag 03FD], in the form natural in both variables of `Ext`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.toAbelian`: the forgetful functor `Mod(𝒪_X) ⥤ Ab(X)`,
  spelled at `X.Modules`, with its exactness instances.
* `AlgebraicGeometry.Scheme.Modules.constantOneSection`: the section `1` of `𝒪_X`, as a
  morphism from the constant sheaf `ℤ`.
* `AlgebraicGeometry.Scheme.Modules.extToAbelian`: the comparison map.

## Main results

* `AlgebraicGeometry.Scheme.Modules.extToAbelian_bijective`.
* `AlgebraicGeometry.Scheme.Modules.extToAbelian_comp`: compatibility with Yoneda products.

## Implementation notes

`X.Modules` is a `def`, so instances stated for `SheafOfModules.toSheaf R` are not found for a
functor out of `X.Modules`. `toAbelian` restates them once, by `inferInstanceAs`. The `Ext`
groups of abelian sheaves are taken in the universe of the sections, through the instance
`hasExt_of_enoughInjectives`, as in `StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- `Ext` groups of abelian sheaves on a space, in the universe of the sections. It is not a
global instance, following Mathlib's policy on `CategoryTheory.HasExt`; files using it make it a
local instance. -/
abbrev hasExtAbelianSheaf (Y : TopCat.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives _

attribute [local instance] hasExtAbelianSheaf

variable (X : Scheme.{u})

/-- **The forgetful functor `Mod(𝒪_X) ⥤ Ab(X)`**, spelled at `X.Modules`. -/
abbrev toAbelian : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance toAbelian_additive : (toAbelian X).Additive :=
  inferInstanceAs ((SheafOfModules.toSheaf X.ringCatSheaf).Additive)

instance toAbelian_preservesFiniteLimits : PreservesFiniteLimits (toAbelian X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

instance toAbelian_preservesFiniteColimits : PreservesFiniteColimits (toAbelian X) :=
  Stacks.SheafOfModules.toSheaf_preservesFiniteColimits _

/-- The constant abelian sheaf `ℤ` on `X`. -/
abbrev constantZ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

/-- Morphisms out of the constant sheaf `ℤ` are global sections. -/
def constantZHomEquiv (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (constantZ X ⟶ F) ≃ F.obj.obj (op ⊤) :=
  (Ext.addEquiv₀ : Ext.{u} (constantZ X) F 0 ≃+ _).symm.toEquiv.trans
    (CategoryTheory.Sheaf.H.equiv₀.{u} F (isTerminalTop : IsTerminal (⊤ : Opens X))).toEquiv

variable {X}

/-- Naturality of `constantZHomEquiv`. -/
theorem constantZHomEquiv_comp {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : constantZ X ⟶ F) (g : F ⟶ G) :
    constantZHomEquiv X G (φ ≫ g) = g.hom.app (op ⊤) (constantZHomEquiv X F φ) := by
  have h := CategoryTheory.Sheaf.H.equiv₀_naturality.{u}
    (isTerminalTop : IsTerminal (⊤ : Opens X)) g (Ext.mk₀ φ)
  rw [CategoryTheory.Sheaf.H.map_apply, Ext.mk₀_comp_mk₀] at h
  simp only [constantZHomEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
    Ext.addEquiv₀_symm_apply]
  exact h.symm

variable (X)

/-- **The section `1` of `𝒪_X`**, as a morphism `ℤ ⟶ 𝒪_X` of abelian sheaves. -/
def constantOneSection : constantZ X ⟶ (toAbelian X).obj (unitModule X) :=
  (constantZHomEquiv X _).symm (1 : X.ringCatSheaf.obj.obj (op ⊤))

/-- Morphisms out of `𝒪_X` are morphisms out of `ℤ` into the underlying abelian sheaf. -/
theorem bijective_constantOneSection_comp (M : X.Modules) :
    Function.Bijective (fun s : unitModule X ⟶ M =>
      constantOneSection X ≫ (toAbelian X).map s) := by
  have heq : ∀ s : unitModule X ⟶ M, constantOneSection X ≫ (toAbelian X).map s =
      (constantZHomEquiv X _).symm ((s.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤))) :=
    fun s => (constantZHomEquiv X _).injective <|
      (constantZHomEquiv_comp _ _).trans <|
        (congrArg (((toAbelian X).map s).hom.app (op ⊤)).hom
          ((constantZHomEquiv X _).apply_symm_apply _)).trans
        ((constantZHomEquiv X _).apply_symm_apply _).symm
  have hfun : (fun s : unitModule X ⟶ M => constantOneSection X ≫ (toAbelian X).map s) =
      (constantZHomEquiv X _).symm ∘
        (fun s : unitModule X ⟶ M =>
          (s.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤))) :=
    funext heq
  rw [hfun]
  exact (constantZHomEquiv X _).symm.bijective.comp (bijective_unitHom_app_top_one M)

/-- **The comparison `Extⁿ_{𝒪_X}(𝒪_X, M) ⟶ Hⁿ(X, M)`**: forget the module structure and precompose
with `1 : ℤ ⟶ 𝒪_X`. -/
def extToAbelian (M : X.Modules) (n : ℕ) :
    Ext.{u} (unitModule X) M n →+ Ext.{u} (constantZ X) ((toAbelian X).obj M) n :=
  Stacks.Cohomology.ExtComparison.extMapAlong.{u, u} (toAbelian X) (constantOneSection X) M n

/-- **The comparison is bijective**, in every degree. -/
theorem extToAbelian_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (extToAbelian X M n) :=
  Stacks.Cohomology.ExtComparison.extMapAlong_bijective_of_subsingleton _ _
    (bijective_constantOneSection_comp X)
    (fun I hI m => by
      have hI' : @Injective (SheafOfModules.{u} X.ringCatSheaf) _ I := hI
      have htf := ModuleSheafCohomology.isTorsionFree_sheafify (Opens.grothendieckTopology X) _
        Stacks.Cohomology.ObjectSections.isTorsionFree_constantZPresheaf
      exact ⟨fun a b =>
        (ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree (Opens.grothendieckTopology X)
          X.ringCatSheaf I _ htf m a).trans
        (ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree (Opens.grothendieckTopology X)
          X.ringCatSheaf I _ htf m b).symm⟩)
    M n

/-- **Compatibility with Yoneda products**: the image of `y ∘ e` is the image of `y` composed
with `e` read in abelian sheaves. -/
theorem extToAbelian_comp {M N : X.Modules} {a b c : ℕ}
    (y : Ext.{u} (unitModule X) M a) (e : Ext.{u} M N b) (h : a + b = c) :
    extToAbelian X N c (y.comp e h) =
      (extToAbelian X M a y).comp (e.mapExactFunctor (toAbelian X)) h := by
  simp only [extToAbelian, Stacks.Cohomology.ExtComparison.extMapAlong_apply,
    Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add a) h (by omega)).symm

end AlgebraicGeometry.Scheme.Modules

end
