module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.AmbientTensorPresheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleBaseChangeNaturality

/-!
# The coefficient comparison `Γ(-, 𝒪) ⊗_{𝒪(x)} ℱ(x) ⟶ ℱ` on the slice of a fibred site

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `x` an object of `𝒳` lying over
the scheme `X`, and `ℱ` a sheaf of `𝒪_𝒳`-modules on one of the associated sites.  Write
`M = ℱ(x)`, a module over `Γ(X, 𝒪)`.  This file builds the comparison

`Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} M ⟶ ℱ(z)`,  `a ⊗ s ↦ a • s|_z`,

for `z ⟶ x` an object of the slice `𝒳/x` lying over `Z`, as a morphism of abelian presheaves on
`𝒳/x`, from the ambient coefficient presheaf `AlgebraicGeometry.overTensorPresheaf X M` read on the
slice through the functor `𝒳/x ⥤ Sch/X` induced by `p`.

This is the fibred-site counterpart of `AlgebraicGeometry.Space.SmallEtale.tensorToChartSections`.

## Main definitions

* `AlgebraicGeometry.FibredSite.sliceToSchemes`: the functor `𝒳/x ⥤ Sch/X` induced by `p`.
* `AlgebraicGeometry.FibredSite.abelianPresheaf`: the abelian presheaf underlying `ℱ`.
* `AlgebraicGeometry.FibredSite.tensorToSections`: **the comparison**.

## Main results

* `AlgebraicGeometry.FibredSite.tensorToSectionsApp_tmul`: the comparison sends `a ⊗ s` to
  `a • s|_z`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

universe v u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : SiteKind) (x : 𝒳)
  (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ))

/-- The scheme an object of `𝒳` lies over. -/
abbrev schemeOf (z : 𝒳) : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj (p.obj z)

/-- The functor `𝒳/x ⥤ Sch/X` induced by the structure functor `p`. -/
abbrev sliceToSchemes : Over x ⥤ Over (schemeOf B S hS p x) :=
  Over.post (p ⋙ BigFppfOver.toScheme B S hS)

/-- The abelian presheaf underlying a sheaf of `𝒪_𝒳`-modules. -/
abbrev abelianPresheaf : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (sheafToPresheaf (BigFppfOver.associatedTopology B S hS p τ) AddCommGrpCat.{u}).obj
    ((SheafOfModules.toSheaf (ringStructureSheafCore B S hS p hp τ)).obj F)

/-- The sections of `ℱ` over `z` are a module over the coordinate ring of the scheme below `z`. -/
instance instModuleAbelianPresheaf (z : 𝒳) :
    Module (Scheme.Γ.obj (op (schemeOf B S hS p z)) : Type u)
      ((abelianPresheaf B S hS p hp τ F).obj (op z) : Type u) :=
  inferInstanceAs (Module ((ringStructureSheafCore B S hS p hp τ).obj.obj (op z))
    (F.val.obj (op z)))

/-- The coordinate algebra of an object of the slice at `x`. -/
abbrev sliceGammaAlg :
    (Over x)ᵒᵖ ⥤ CommAlgCat.{u} (ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u)) :=
  (sliceToSchemes B S hS p x).op ⋙ overGammaAlg (schemeOf B S hS p x)

/-- The sections of `ℱ` over an object of the slice are a module over its coordinate algebra. -/
instance instModuleSliceGammaAlg (Z : (Over x)ᵒᵖ) :
    Module (((sliceGammaAlg B S hS p x).obj Z : CommAlgCat.{u} _) : Type u)
      ((abelianPresheaf B S hS p hp τ F).obj (op Z.unop.left) : Type u) :=
  instModuleAbelianPresheaf B S hS p hp τ F Z.unop.left

/-- Restriction of sections of `ℱ` is semilinear. -/
theorem abelianPresheaf_map_smul {z z' : 𝒳} (f : z' ⟶ z)
    (r : (Scheme.Γ.obj (op (schemeOf B S hS p z)) : Type u))
    (s : ((abelianPresheaf B S hS p hp τ F).obj (op z) : Type u)) :
    (abelianPresheaf B S hS p hp τ F).map f.op (r • s) =
      (show (Scheme.Γ.obj (op (schemeOf B S hS p z')) : Type u) from
        ((ringStructureSheafCore B S hS p hp τ).obj.map f.op).hom r) •
        (abelianPresheaf B S hS p hp τ F).map f.op s :=
  F.val.map_smul f.op r s

/-- Restriction of a section of `ℱ` over `x` to an object of the slice at `x`. -/
abbrev coeffRestrict (Z : (Over x)ᵒᵖ) :
    (abelianPresheaf B S hS p hp τ F).obj (op x) ⟶
      (abelianPresheaf B S hS p hp τ F).obj (op Z.unop.left) :=
  (abelianPresheaf B S hS p hp τ F).map Z.unop.hom.op

/-- Restriction to the slice is semilinear over the lifted base ring. -/
theorem coeffRestrict_smul (Z : (Over x)ᵒᵖ)
    (c : ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u))
    (s : ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u)) :
    coeffRestrict B S hS p hp τ x F Z (c • s) =
      algebraMap (ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u))
          (((sliceGammaAlg B S hS p x).obj Z : CommAlgCat.{u} _) : Type u) c •
        coeffRestrict B S hS p hp τ x F Z s :=
  abelianPresheaf_map_smul B S hS p hp τ F Z.unop.hom c.down s

/-- The restriction maps are semilinear for the coordinate-algebra actions along a morphism of
the slice. -/
theorem coeffMap_smul {Z Z' : (Over x)ᵒᵖ} (g : Z ⟶ Z')
    (a : (((sliceGammaAlg B S hS p x).obj Z : CommAlgCat.{u} _) : Type u))
    (s : ((abelianPresheaf B S hS p hp τ F).obj (op Z.unop.left) : Type u)) :
    (abelianPresheaf B S hS p hp τ F).map g.unop.left.op (a • s) =
      (sliceGammaAlg B S hS p x).map g a •
        (abelianPresheaf B S hS p hp τ F).map g.unop.left.op s :=
  abelianPresheaf_map_smul B S hS p hp τ F g.unop.left a s

/-- The bilinear data of the comparison: `(a, s) ↦ a • s|_z`. -/
def tensorBilin (Z : (Over x)ᵒᵖ) :
    (((sliceGammaAlg B S hS p x).obj Z : CommAlgCat.{u} _) : Type u) →+
      (((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u) →+
        ((abelianPresheaf B S hS p hp τ F).obj (op Z.unop.left) : Type u)) where
  toFun a :=
    { toFun := fun s => a • coeffRestrict B S hS p hp τ x F Z s
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' := fun s t => by simp only [map_add, smul_add] }
  map_zero' := AddMonoidHom.ext fun s => zero_smul _ _
  map_add' a b := AddMonoidHom.ext fun s => add_smul _ _ _

/-- `tensorBilin` sends `(a, s)` to `a • s|_z`. -/
theorem tensorBilin_apply (Z : (Over x)ᵒᵖ)
    (a : (((sliceGammaAlg B S hS p x).obj Z : CommAlgCat.{u} _) : Type u))
    (s : ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u)) :
    tensorBilin B S hS p hp τ x F Z a s = a • coeffRestrict B S hS p hp τ x F Z s := rfl

/-- `tensorBilin` is balanced over `Γ(X, 𝒪)`: `(c • a, s)` and `(a, c • s)` have the same image. -/
theorem tensorBilin_balanced (Z : (Over x)ᵒᵖ)
    (c : ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u))
    (a : (((sliceGammaAlg B S hS p x).obj Z : CommAlgCat.{u} _) : Type u))
    (s : ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u)) :
    tensorBilin B S hS p hp τ x F Z (c • a) s = tensorBilin B S hS p hp τ x F Z a (c • s) := by
  rw [tensorBilin_apply, tensorBilin_apply, coeffRestrict_smul, Algebra.smul_def, smul_smul,
    mul_comm]

/-- The comparison at one object of the slice at `x`. -/
def tensorToSectionsApp (Z : (Over x)ᵒᵖ) :
    ((sliceToSchemes B S hS p x).op ⋙
        overTensorPresheaf (schemeOf B S hS p x)
          ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u)).obj Z ⟶
      ((Over.forget x).op ⋙ abelianPresheaf B S hS p hp τ F).obj Z :=
  AddCommGrpCat.ofHom (TensorProduct.liftAddHom (tensorBilin B S hS p hp τ x F Z)
    (tensorBilin_balanced B S hS p hp τ x F Z))

/-- The comparison sends `a ⊗ s` to `a • s|_z`. -/
theorem tensorToSectionsApp_tmul (Z : (Over x)ᵒᵖ)
    (a : (((sliceGammaAlg B S hS p x).obj Z : CommAlgCat.{u} _) : Type u))
    (s : ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u)) :
    tensorToSectionsApp B S hS p hp τ x F Z
        (a ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u)] s) =
      a • coeffRestrict B S hS p hp τ x F Z s :=
  (TensorProduct.liftAddHom_tmul (tensorBilin B S hS p hp τ x F Z)
    (tensorBilin_balanced B S hS p hp τ x F Z) a s).trans
    (tensorBilin_apply B S hS p hp τ x F Z a s)

/-- Along a morphism `g` of the slice, the coefficient presheaf sends `a ⊗ s` to `g(a) ⊗ s`. -/
theorem overTensorPresheaf_slice_map_tmul {Z Z' : (Over x)ᵒᵖ} (g : Z ⟶ Z')
    (a : (((sliceGammaAlg B S hS p x).obj Z : CommAlgCat.{u} _) : Type u))
    (s : ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u)) :
    ((sliceToSchemes B S hS p x).op ⋙
          overTensorPresheaf (schemeOf B S hS p x)
            ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u)).map g
        (a ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u)] s) =
      (sliceGammaAlg B S hS p x).map g a
        ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u)] s :=
  rfl

/-- The comparison commutes with restriction along a morphism `g` of the slice on pure tensors:
it sends `g(a) ⊗ s` to the restriction along `g` of the image of `a ⊗ s`. -/
theorem tensorToSectionsApp_naturality {Z Z' : (Over x)ᵒᵖ} (g : Z ⟶ Z')
    (a : (((sliceGammaAlg B S hS p x).obj Z : CommAlgCat.{u} _) : Type u))
    (s : ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u)) :
    tensorToSectionsApp B S hS p hp τ x F Z'
        ((sliceGammaAlg B S hS p x).map g a
          ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u)] s) =
      (abelianPresheaf B S hS p hp τ F).map g.unop.left.op
        (tensorToSectionsApp B S hS p hp τ x F Z
          (a ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u)] s)) := by
  rw [tensorToSectionsApp_tmul, tensorToSectionsApp_tmul, coeffMap_smul]
  congr 1
  simp only [coeffRestrict, ← ConcreteCategory.comp_apply,
    ← (abelianPresheaf B S hS p hp τ F).map_comp, ← op_comp, Over.w g.unop]

/-- **The comparison** `Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} ℱ(x) ⟶ ℱ(z)`, `a ⊗ s ↦ a • s|_z`, as a morphism of
abelian presheaves on the slice at `x`. -/
def tensorToSections :
    (sliceToSchemes B S hS p x).op ⋙
        overTensorPresheaf (schemeOf B S hS p x)
          ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u) ⟶
      (Over.forget x).op ⋙ abelianPresheaf B S hS p hp τ F where
  app Z := tensorToSectionsApp B S hS p hp τ x F Z
  naturality Z Z' g := by
    apply AddCommGrpCat.hom_ext
    refine Stacks.Sites.addHom_ext_tmul
      (Rr := ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u))
      (Mm := (((sliceGammaAlg B S hS p x).obj Z : CommAlgCat.{u} _) : Type u))
      (Nn := ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u))
      (Pp := ((abelianPresheaf B S hS p hp τ F).obj (op Z'.unop.left) : Type u))
      (fun a s => ?_)
    exact tensorToSectionsApp_naturality B S hS p hp τ x F g a s

/-- The comparison `tensorToSectionsApp` at an object `z ⟶ x` of the slice is an isomorphism
whenever the base-change comparison `Stacks.PresheafOfModules.restrictionBaseChange` of `ℱ` along
`z ⟶ x` is one. -/
theorem isIso_tensorToSectionsApp_of_isIso_restrictionBaseChange (Z : Over x)
    (hZ : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{v, u, u, u}
      (R := (structureSheaf B S hS p hp τ).obj) F.val Z.hom.op)) :
    IsIso (tensorToSectionsApp B S hS p hp τ x F (op Z)) := by
  let Rr := (structureSheaf B S hS p hp τ).obj
  let Aa := (((sliceGammaAlg B S hS p x).obj (op Z) : CommAlgCat.{u} _) : Type u)
  let Mm := ((abelianPresheaf B S hS p hp τ F).obj (op x) : Type u)
  let Uu := ULift.{u} (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u)
  let N : PresheafOfModules.{u} (Rr ⋙ forget₂ CommRingCat RingCat) := F.val
  let d : ((ModuleCat.extendScalars (Rr.map Z.hom.op).hom).obj (N.obj (op x)) : Type u) →+
      (Aa ⊗[Uu] Mm) :=
    TensorProduct.liftAddHom
      { toFun := fun a =>
          { toFun := fun s => (show Aa from a) ⊗ₜ[Uu] (show Mm from s)
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' := fun s t => TensorProduct.tmul_add _ _ _ }
        map_zero' := AddMonoidHom.ext fun s => TensorProduct.zero_tmul _ _
        map_add' := fun a b => AddMonoidHom.ext fun s => TensorProduct.add_tmul _ _ _ }
      (fun r a s => TensorProduct.smul_tmul (R := Uu) (R' := Uu) (show Uu from ULift.up r)
        (show Aa from a) (show Mm from s))
  let T := tensorToSectionsApp B S hS p hp τ x F (op Z)
  let ρ := Stacks.PresheafOfModules.restrictionBaseChange.{v, u, u, u}
    (R := (structureSheaf B S hS p hp τ).obj) F.val Z.hom.op
  have hTd : ∀ z, T (d z) = ρ z := DFunLike.congr_fun
    (Stacks.Sites.addHom_ext_tmul (f := T.hom.comp d) (h := ρ.hom.toAddMonoidHom) fun a s =>
      (tensorToSectionsApp_tmul B S hS p hp τ x F (op Z) a s).trans
        (Stacks.PresheafOfModules.restrictionBaseChange_tmul
          (R := (structureSheaf B S hS p hp τ).obj) F.val Z.hom.op a s).symm)
  have hdsurj : Function.Surjective d := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, d.map_zero⟩
    | tmul a s => exact ⟨(show Rr.obj (op Z.left) from a) ⊗ₜ[Rr.obj (op x),
        (Rr.map Z.hom.op).hom] (show N.obj (op x) from s), rfl⟩
    | add z w hz hw =>
      obtain ⟨z', rfl⟩ := hz
      obtain ⟨w', rfl⟩ := hw
      exact ⟨z' + w', d.map_add _ _⟩
  have hρ := ConcreteCategory.bijective_of_isIso ρ
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun z w h => ?_, fun y => ?_⟩
  · obtain ⟨z', rfl⟩ := hdsurj z
    obtain ⟨w', rfl⟩ := hdsurj w
    rw [hρ.1 ((hTd z').symm.trans (h.trans (hTd w')))]
  · obtain ⟨u, rfl⟩ := hρ.2 y
    exact ⟨d u, hTd u⟩

end AlgebraicGeometry.FibredSite
