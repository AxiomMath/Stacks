module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleImageSubmoduleAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjDegreeIdealQuotientProj
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal

/-!
# The graded ideal generated in one degree is quasi-coherent, on an algebraic space

In Situation 0849 let `𝒜` be the quasi-coherent graded `𝒪_X`-algebra on the algebraic space `X`
and let `ℱ ⊆ 𝒜_d` be a quasi-coherent `𝒪_X`-submodule.  The source of Stacks 085M and 085N reads
the degree-`n` piece of the graded ideal `ℱ𝒜` as the image of the multiplication
`ℱ ⊗_{𝒪_X} 𝒜_{n-d} ⟶ 𝒜_n`.  This file proves that reading: the degree-`(d + e)` piece of
`AlgebraicGeometry.Space.RelativeProjSituation.degreeIdeal ℱ` is the image submodule of the
multiplication map out of the tensor product, and consequently every piece of `ℱ𝒜` is
quasi-coherent — the tensor product of two quasi-coherent modules is quasi-coherent
(Stacks 03M1 (5)) and so is the image of a morphism of quasi-coherent modules on the small étale
site.

So the quotient situation `s.quotient (s.degreeIdeal ℱ) _` of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjDegreeIdealQuotientProj`, the relative Proj
`Proj_X(𝒜/ℱ𝒜)` of the conclusion of Stacks 085M and 085N, is available for every quasi-coherent
`ℱ`, with no hypothesis on the ideal.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.degreeProductsPresheafHom`: the products
  `ℱ ⊗ 𝒜_e ⟶ 𝒜_{d+e}` on the objectwise tensor product of the presheaves of sections.
* `AlgebraicGeometry.Space.RelativeProjSituation.degreeProductsHom`: the multiplication map
  `ℱ ⊗_{𝒪_X} 𝒜_e ⟶ 𝒜_{d+e}` out of the sheaf tensor product
  `AlgebraicGeometry.Space.tensorModule`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.imageSubmodule_degreeProductsHom`: **the image of
  `ℱ ⊗ 𝒜_e ⟶ 𝒜_{d+e}` is the ideal `ℱ𝒜` in degree `d + e`** of Stacks 085M,
  `AlgebraicGeometry.Space.closedSubspaceDegreeProducts`.
* **Every homogeneous piece of `ℱ𝒜` is quasi-coherent** when `ℱ` is:
`AlgebraicGeometry.Space.RelativeProjSituation.isQuasicoherentOnSite_closedSubspaceDegreeProducts`
  and `AlgebraicGeometry.Space.RelativeProjSituation.isQuasicoherentOnSite_degreeIdeal_piece`.

## References

* [Stacks Project, Tag 085M](https://stacks.math.columbia.edu/tag/085M)
* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules.ImageSubsheaf
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space.RelativeProjSituation

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (s : RelativeProjSituation.{u, u}) {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) (e : ℤ)

/-- The products `f · a` of a local section `f` of `ℱ ⊆ 𝒜_d` with a local section `a` of `𝒜_e`,
as a morphism out of the objectwise tensor product `ℱ ⊗ 𝒜_e` of the presheaves of sections. -/
def degreeProductsPresheafHom :
    PresheafOfModules.tensorObj ℱ.toSheafOfModules.val (s.algebra.piece e).val ⟶
      (s.algebra.piece (d + e)).val :=
  PresheafOfModules.tensorMk
    (fun X x y => ((s.algebra.mul d e).compLeft ℱ.ι.val).app X x y)
    (fun X x x' y => ((s.algebra.mul d e).compLeft ℱ.ι.val).map_add_left X x x' y)
    (fun X r x y => ((s.algebra.mul d e).compLeft ℱ.ι.val).map_smul_left X r x y)
    (fun X x y y' => map_add (((s.algebra.mul d e).compLeft ℱ.ι.val).app X x) y y')
    (fun X r x y => ((s.algebra.mul d e).compLeft ℱ.ι.val).map_smul_right X r x y)
    (fun _ _ f x y => ((s.algebra.mul d e).compLeft ℱ.ι.val).naturality f x y)

/-- On a pure tensor `x ⊗ₜ y`, the objectwise products are the product of `x`, as a section of
`𝒜_d`, with `y`. -/
theorem degreeProductsPresheafHom_app_tmul
    (X : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (x : ℱ.toSheafOfModules.val.obj X) (y : (s.algebra.piece e).val.obj X) :
    (s.degreeProductsPresheafHom ℱ e).app X (x ⊗ₜ y) =
      (s.algebra.mul d e).app X (ℱ.ι.val.app X x) y :=
  rfl

/-- The objectwise products land in the objectwise span of the products. -/
theorem degreeProductsPresheafHom_app_mem
    (X : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (t : (PresheafOfModules.tensorObj ℱ.toSheafOfModules.val (s.algebra.piece e).val).obj X) :
    (s.degreeProductsPresheafHom ℱ e).app X t ∈ (presheafDegreeProducts s d e ℱ).obj X := by
  have key : ∀ t, t ∈ ((presheafDegreeProducts s d e ℱ).obj X).toAddSubmonoid.comap
      (ConcreteCategory.hom ((s.degreeProductsPresheafHom ℱ e).app X)).toAddMonoidHom := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact AddSubmonoid.zero_mem _
    | tmul x y => exact Submodule.subset_span ⟨_, s.ι_app_mem ℱ X x, y, rfl⟩
    | add t t' ht ht' => exact AddSubmonoid.add_mem _ ht ht'
  exact key t

/-- **The multiplication map `ℱ ⊗_{𝒪_X} 𝒜_e ⟶ 𝒜_{d+e}`** out of the tensor product of
`𝒪_X`-modules `AlgebraicGeometry.Space.tensorModule`, the sheafification of the objectwise tensor
product: the morphism induced by `degreeProductsPresheafHom` by the universal property of the
sheafification. -/
def degreeProductsHom :
    tensorModule s.site s.base s.containsBase s.space.1 s.space.2 ℱ.toSheafOfModules
        (s.algebra.piece e) ⟶ s.algebra.piece (d + e) :=
  letI := SheafOfModules.isLocallyInjective_id_structure
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite s.site s.base s.containsBase s.space.1 s.space.2).O))
  letI := SheafOfModules.isLocallySurjective_id_structure
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite s.site s.base s.containsBase s.space.1 s.space.2).O))
  (PresheafOfModules.sheafificationHomEquiv _).symm
    ((PresheafOfModules.uliftSectionsSelfIso _).hom ≫ s.degreeProductsPresheafHom ℱ e)

/-- On the sections of the objectwise tensor product, the multiplication map is the objectwise
product. -/
theorem degreeProductsHom_app_toSheafify
    (X : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (t : (PresheafOfModules.tensorObj ℱ.toSheafOfModules.val (s.algebra.piece e).val).obj X) :
    (s.degreeProductsHom ℱ e).val.app X
        ((CategoryTheory.toSheafify
          (SmallEtale.topology s.site s.base s.containsBase s.space.1)
          (PresheafOfModules.tensorObj ℱ.toSheafOfModules.val
            (s.algebra.piece e).val).uliftSections.{u}.presheaf).app X (ULift.up t)) =
      (s.degreeProductsPresheafHom ℱ e).app X t := by
  let := SheafOfModules.isLocallyInjective_id_structure
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite s.site s.base s.containsBase s.space.1 s.space.2).O))
  let := SheafOfModules.isLocallySurjective_id_structure
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite s.site s.base s.containsBase s.space.1 s.space.2).O))
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite s.site s.base s.containsBase s.space.1 s.space.2).O).obj)
    (s.degreeProductsHom ℱ e)
  rw [degreeProductsHom, Equiv.apply_symm_apply] at h
  exact (congrArg (fun φ => (ConcreteCategory.hom (φ.app X)) (ULift.up t)) h).symm

/-- Every section in the range of the multiplication map lies in the ideal `ℱ𝒜`: locally it is
the image of a section of the objectwise tensor product, whose image is a sum of products. -/
theorem degreeProductsHom_app_mem
    (X : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (t : (tensorModule s.site s.base s.containsBase s.space.1 s.space.2 ℱ.toSheafOfModules
      (s.algebra.piece e)).val.obj X) :
    (s.degreeProductsHom ℱ e).val.app X t ∈ (closedSubspaceDegreeProducts s d e ℱ).obj X := by
  refine Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem
    (Presheaf.imageSieve_mem (SmallEtale.topology s.site s.base s.containsBase s.space.1)
      (CategoryTheory.toSheafify (SmallEtale.topology s.site s.base s.containsBase s.space.1)
        (PresheafOfModules.tensorObj ℱ.toSheafOfModules.val
          (s.algebra.piece e).val).uliftSections.{u}.presheaf) t) ?_
  rintro Y g ⟨⟨τ⟩, hτ⟩
  have hnat := PresheafOfModules.naturality_apply (s.degreeProductsHom ℱ e).val g.op t
  erw [← hτ, s.degreeProductsHom_app_toSheafify ℱ e] at hnat
  exact hnat ▸ s.degreeProductsPresheafHom_app_mem ℱ e (op Y) τ

/-- **The image of `ℱ ⊗ 𝒜_e ⟶ 𝒜_{d+e}` is the ideal `ℱ𝒜` in degree `d + e`** — the reading of
`ℱ𝒜` in the source of Stacks 085M and 085N. -/
theorem imageSubmodule_degreeProductsHom :
    imageSubmodule (s.degreeProductsHom ℱ e) = closedSubspaceDegreeProducts s d e ℱ := by
  have h₁ : ∀ (X : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
      (x : (s.algebra.piece (d + e)).val.obj X),
      x ∈ (imageSubmodule (s.degreeProductsHom ℱ e)).obj X →
        x ∈ (closedSubspaceDegreeProducts s d e ℱ).obj X := by
    intro X x hx
    refine (closedSubspaceDegreeProducts s d e ℱ).isSheaf x
      (GrothendieckTopology.superset_covering _ (fun V g hg => ?_)
        ((mem_localImage_obj_iff (s.degreeProductsHom ℱ e) x).1 hx))
    obtain ⟨t, ht⟩ := hg
    exact (congrArg (fun z => z ∈ (closedSubspaceDegreeProducts s d e ℱ).obj (op V)) ht).mp
      (s.degreeProductsHom_app_mem ℱ e (op V) t)
  have h₂ := closedSubspaceDegreeProducts_le (K := imageSubmodule (s.degreeProductsHom ℱ e))
    fun U a ha b => by
      have h := apply_mem_imageSubmodule (s.degreeProductsHom ℱ e)
        ((CategoryTheory.toSheafify (SmallEtale.topology s.site s.base s.containsBase s.space.1)
          (PresheafOfModules.tensorObj ℱ.toSheafOfModules.val
            (s.algebra.piece e).val).uliftSections.{u}.presheaf).app U
          (ULift.up (show (PresheafOfModules.tensorObj ℱ.toSheafOfModules.val
            (s.algebra.piece e).val).obj U from ⟨a, ha⟩ ⊗ₜ b)))
      erw [s.degreeProductsHom_app_toSheafify ℱ e U] at h
      exact h
  exact SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun X =>
    _root_.le_antisymm (fun x hx => h₁ X x hx)
      (fun x hx => SheafOfModules.Submodule.le_iff.1 h₂ X hx))

/-- **The ideal `ℱ𝒜` in degree `d + e` is quasi-coherent** when `ℱ` is: it is the image of the
morphism `ℱ ⊗ 𝒜_e ⟶ 𝒜_{d+e}` of quasi-coherent modules. -/
theorem isQuasicoherentOnSite_closedSubspaceDegreeProducts
    (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite) :
    (closedSubspaceDegreeProducts s d e ℱ).toSheafOfModules.IsQuasicoherentOnSite := by
  rw [← s.imageSubmodule_degreeProductsHom ℱ e]
  exact isQuasicoherentOnSite_imageSubmodule _
    (isQuasicoherentOnSite_tensorModule s.site s.base s.containsBase s.space.1 s.space.2 _ _ hℱ
      (s.isQuasicoherent e))
    (s.isQuasicoherent (d + e))

/-- **Every homogeneous piece of the graded ideal `ℱ𝒜` generated by a quasi-coherent submodule
`ℱ ⊆ 𝒜_d` is quasi-coherent.**  So `s.quotient (s.degreeIdeal ℱ) (…)`, the relative Proj
`Proj_X(𝒜/ℱ𝒜)` of Stacks 085M and 085N, is formed with no hypothesis on the ideal. -/
theorem isQuasicoherentOnSite_degreeIdeal_piece (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite)
    (n : ℤ) : ((s.degreeIdeal ℱ).piece n).toSheafOfModules.IsQuasicoherentOnSite := by
  obtain ⟨e, rfl⟩ : ∃ e, n = d + e := ⟨n - d, by omega⟩
  show (s.generatedByDegree ℱ (d + e)).toSheafOfModules.IsQuasicoherentOnSite
  rw [s.generatedByDegree_add_eq_closedSubspaceDegreeProducts]
  exact s.isQuasicoherentOnSite_closedSubspaceDegreeProducts ℱ e hℱ

end AlgebraicGeometry.Space.RelativeProjSituation

end
