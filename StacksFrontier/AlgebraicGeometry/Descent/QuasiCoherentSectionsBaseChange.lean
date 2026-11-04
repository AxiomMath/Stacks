module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentSectionsModule
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfInternalHom

/-!
# The pullback-sections presheaf of modules is cartesian on affine objects

Let `U` be a scheme in a big fppf site and `𝓕` a quasi-coherent `𝒪_U`-module.  The presheaf of
Stacks 03DS, `T ↦ Γ(T, T.hom⁺ 𝓕)`, is a presheaf of modules over the structure sheaf of the big
fppf site of `U` (`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`).  This file proves
that its restriction map along a morphism `k : T ⟶ T'` between objects with affine underlying
schemes is a base change: the comparison

`Γ(T, 𝒪_T) ⊗_{Γ(T', 𝒪_{T'})} Γ(T', T'.hom⁺ 𝓕) ⟶ Γ(T, T.hom⁺ 𝓕)`, `c ⊗ m ↦ c · m|_T`

is bijective.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_iso`: the base-change comparison
  of a restriction map is bijective as soon as some isomorphism out of an extension of scalars
  along a ring map *equal* to the restriction map of the coefficients agrees with it on the
  elements `1 ⊗ x`.
* `AlgebraicGeometry.BigFppfOver.bijective_restrictionBaseChange_sectionsPresheafOfModules`: the
  restriction maps of the pullback-sections presheaf of modules between affine objects of the
  big fppf site are base changes.

## Implementation notes

The content is `Stacks.Sites.affineAssociatedBaseChangeIso`, Tag 02KH in degree zero between
two affine schemes.  That isomorphism is an extension of scalars along
`AlgebraicGeometry.Scheme.Hom.appLE`, which is equal but not definitionally equal to the
restriction map `AlgebraicGeometry.Scheme.Hom.appTop` of the coefficient presheaf; the general
lemma takes the ring map and the equation as arguments, so the equation is substituted once at
abstract rings.

The isomorphism is read as an isomorphism between the values of the presheaf of modules by a
type ascription, which is checked at the level of `ModuleCat` objects.  The normalisation on
`1 ⊗ x` is then transferred by first identifying the two spellings of the element `1 ⊗ x` by
`rfl` at a type ascribed on both sides; applying the normalisation lemma directly to the
presheaf-side spelling exhausts the default recursion depth, the two `Module` instances on the
sections (the one transported along `AlgebraicGeometry.PullbackSectionsPresheaf.objIso` and the
native one) being compared inside the tensor product.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped ChangeOfRings

universe u

namespace Stacks.PresheafOfModules

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- **The base-change comparison of a restriction map is bijective as soon as some isomorphism
agrees with it on the elements `1 ⊗ x`.**  The isomorphism may be an extension of scalars along
any ring map `φ` equal to the restriction map `R.map f` of the coefficients, which lets a
comparison built along a propositionally equal ring map be used without transport. -/
theorem bijective_restrictionBaseChange_of_iso
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ : R.obj X ⟶ R.obj Y) (hφ : φ = R.map f)
    (e : (ModuleCat.extendScalars φ.hom).obj (M.obj X) ≅ M.obj Y)
    (he : ∀ x : M.obj X, e.hom ((1 : R.obj Y) ⊗ₜ[R.obj X, φ.hom] x) = M.map f x) :
    Function.Bijective (restrictionBaseChange M f) := by
  subst hφ
  have h : restrictionBaseChange M f = e.hom :=
    ModuleCat.ExtendScalars.hom_ext_one_tmul _ fun x =>
      (restrictionBaseChange_one_tmul M f x).trans (he x).symm
  rw [h]
  exact ConcreteCategory.bijective_of_isIso _

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (U : Scheme.{u}) (hU : B.Contains U)

/-- **The pullback-sections presheaf of modules is cartesian on affine objects.**  For a
quasi-coherent `𝒪_U`-module `𝓕` and a morphism `k : T ⟶ T'` of the big fppf site of `U` between
objects whose underlying schemes are affine, the base-change comparison

`Γ(T, 𝒪_T) ⊗_{Γ(T', 𝒪_{T'})} Γ(T', T'.hom⁺ 𝓕) ⟶ Γ(T, T.hom⁺ 𝓕)`

of the restriction map of `AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules` along `k` is
bijective.  The coefficient presheaf is read as
`AlgebraicGeometry.BigFppfOver.commStructurePresheaf`, whose underlying presheaf of rings is the
structure sheaf on the nose. -/
theorem bijective_restrictionBaseChange_sectionsPresheafOfModules (𝓕 : U.Modules)
    [𝓕.IsQuasicoherent] {T T' : BigFppfOver B U hU} (k : T ⟶ T')
    (hT : IsAffine ((BigFppfOver.toScheme B U hU).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B U hU).obj T')) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
      (R := commStructurePresheaf B U hU) (sectionsPresheafOfModules B U hU 𝓕) k.op) := by
  let X : Over U := (Over.post (X := B.obj hU) B.inclusion).obj T
  let Y : Over U := (Over.post (X := B.obj hU) B.inclusion).obj T'
  let g : X ⟶ Y := (Over.post (X := B.obj hU) B.inclusion).map k
  have : IsAffine X.left := hT
  have : IsAffine Y.left := hT'
  have h : (⊤ : X.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Y.left.Opens) := le_of_eq (by simp)
  let M : PresheafOfModules.{u} (commStructurePresheaf B U hU ⋙ forget₂ CommRingCat RingCat) :=
    sectionsPresheafOfModules B U hU 𝓕
  let φ : (commStructurePresheaf B U hU).obj (op T') ⟶
      (commStructurePresheaf B U hU).obj (op T) :=
    g.left.appLE ⊤ ⊤ h
  have hφ : φ = (commStructurePresheaf B U hU).map k.op := Scheme.Hom.appLE_eq_app g.left
  let e : (ModuleCat.extendScalars φ.hom).obj (M.obj (op T')) ≅ M.obj (op T) :=
    Stacks.Sites.affineAssociatedBaseChangeIso 𝓕 g h
  refine Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_iso M k.op φ hφ e
    (fun x => ?_)
  let x' : Γ((Scheme.Modules.pullback Y.hom).obj 𝓕, ⊤) := x
  have hx : ((1 : (commStructurePresheaf B U hU).obj (op T)) ⊗ₜ[_, φ.hom] x :
      (ModuleCat.extendScalars φ.hom).obj (M.obj (op T'))) =
      ((1 : Γ(X.left, ⊤)) ⊗ₜ[Γ(Y.left, ⊤), (g.left.appLE ⊤ ⊤ h).hom] x' :
      (ModuleCat.extendScalars (g.left.appLE ⊤ ⊤ h).hom).obj
        (ModuleCat.of Γ(Y.left, ⊤) Γ((Scheme.Modules.pullback Y.hom).obj 𝓕, ⊤))) := rfl
  have hmap : M.map k.op x = pullbackSectionsMap 𝓕 g x' :=
    (PresheafOfModules.presheaf_map_apply_coe M k.op x).symm
  exact (congrArg (fun z => ConcreteCategory.hom e.hom z) hx).trans
    ((Stacks.Sites.affineAssociatedBaseChangeIso_hom_one_tmul 𝓕 g h x').trans hmap.symm)

end AlgebraicGeometry.BigFppfOver
