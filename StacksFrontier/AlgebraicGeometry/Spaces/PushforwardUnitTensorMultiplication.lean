module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardSubmoduleIdeal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.AbelianSheavesAbelian

/-!
# The multiplication `ℰ ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y` and images closed under multiplication

Let `f : Y ⟶ X` be a representable morphism of algebraic spaces and `φ : ℰ ⟶ f_*𝒪_Y` a map of
`𝒪_X`-modules.  The proof of Stacks 0GV1 considers the composite

`ℰ ⊗_{𝒪_X} f_*𝒪_Y ⟶ f_*𝒪_Y ⊗_{𝒪_X} f_*𝒪_Y ⟶ f_*𝒪_Y ⟶ 𝒬 = coker φ`,

`e ⊗ b ↦ b φ(e) mod im φ`, and uses that it vanishes exactly when the image of `φ` is an
`f_*𝒪_Y`-submodule of `f_*𝒪_Y`.  That closure under multiplication is the hypothesis `hmul` of
`AlgebraicGeometry.Space.exists_ideal_pushforwardSubmodule_eq`, which then writes the image as the
direct image `f_*ℐ` of a sheaf of ideals of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardUnitTensorMulHom`: the morphism
  `ℰ ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y`, `e ⊗ b ↦ b φ(e)`, out of the tensor product sheaf.

## Main results

* `AlgebraicGeometry.Space.mul_mem_imageSubmodule_of_pushforwardUnitTensorMulHom_comp_eq_zero`:
  if the composite with the cokernel map of `φ` vanishes, the image of `φ` is closed under
  multiplication by the sections of `f_*𝒪_Y`.
* `AlgebraicGeometry.Space.pushforwardUnitTensorMulHom_comp_eq_zero_of_mul_mem`: the converse.
* `AlgebraicGeometry.Space.pushforwardUnitTensorMulHom_comp_eq_zero_iff`: the equivalence.
* `AlgebraicGeometry.Space.exists_ideal_pushforwardSubmodule_eq_imageSubmodule`: for an affine
  `f`, the image of `φ` is then the direct image of a quasi-coherent sheaf of ideals of `Y`.

## Implementation notes

The morphism is built, as `AlgebraicGeometry.Space.chartPowTensorHom` is, from the bilinear map
`(e, b) ↦ b φ(e)` on sections through the universal property of the sheafified tensor product
(`Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom`).  It is the composite of `φ ⊗ 𝟙` with
the multiplication of the algebra `f_*𝒪_Y`, but it is not built that way: only its values on
sections are used.

Both directions are elementwise statements about the image subsheaf
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ`, whose sections are those that lie locally
in the range of `φ`.  The kernel of the cokernel map is that image, locally:
`Stacks.AbelianSheaves.imageSieve_mem_of_exact` for one inclusion and
`Stacks.AbelianSheaves.app_eq_zero_of_imageSieve_mem` for the other, read on the underlying
abelian sheaves.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)

/-- The abelian structure on modules, pinned at the universes in use. -/
noncomputable local instance (priority := high) abelianModulesPushforwardUnitTensor
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

variable {B S hS f hf} {E : Modules.{u, u} B S hS X.1 X.2}
    (φ : E ⟶ chartBaseChangeStructureModule B S hS f hf)

/-! ### The product `b φ(e)` on sections -/

/-- The section `b φ(e)` of `f_*𝒪_Y`. -/
def pushforwardUnitScale {V : SmallEtale B S hS X.1} (e : E.val.obj (op V))
    (b : (chartBaseChangeStructureModule B S hS f hf).val.obj (op V)) :
    (chartBaseChangeStructureModule B S hS f hf).val.obj (op V) :=
  (show chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj V) from b) *
    (show chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj V) from
      φ.val.app (op V) e)

/-- The product `b φ(e)` is additive in `e`. -/
theorem pushforwardUnitScale_add_left {V : SmallEtale B S hS X.1}
    (e₁ e₂ : E.val.obj (op V)) (b : (chartBaseChangeStructureModule B S hS f hf).val.obj (op V)) :
    pushforwardUnitScale φ (e₁ + e₂) b =
      pushforwardUnitScale φ e₁ b + pushforwardUnitScale φ e₂ b := by
  unfold pushforwardUnitScale
  rw [map_add]
  exact mul_add (R := chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj V)) _ _ _

/-- The product `b φ(e)` is additive in `b`. -/
theorem pushforwardUnitScale_add_right {V : SmallEtale B S hS X.1}
    (e : E.val.obj (op V)) (b₁ b₂ : (chartBaseChangeStructureModule B S hS f hf).val.obj (op V)) :
    pushforwardUnitScale φ e (b₁ + b₂) =
      pushforwardUnitScale φ e b₁ + pushforwardUnitScale φ e b₂ :=
  add_mul (R := chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj V)) _ _ _

/-- The product `b φ(e)` is linear in `e` over the sections of `𝒪_X`. -/
theorem pushforwardUnitScale_smul_left {V : SmallEtale B S hS X.1}
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
      (op V))
    (e : E.val.obj (op V)) (b : (chartBaseChangeStructureModule B S hS f hf).val.obj (op V)) :
    pushforwardUnitScale φ (r • e) b = r • pushforwardUnitScale φ e b := by
  unfold pushforwardUnitScale
  rw [map_smul]
  exact mul_left_comm (G := chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj V)) _ _ _

/-- The product `b φ(e)` is linear in `b` over the sections of `𝒪_X`. -/
theorem pushforwardUnitScale_smul_right {V : SmallEtale B S hS X.1}
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
      (op V))
    (e : E.val.obj (op V)) (b : (chartBaseChangeStructureModule B S hS f hf).val.obj (op V)) :
    pushforwardUnitScale φ e (r • b) = r • pushforwardUnitScale φ e b :=
  mul_assoc (G := chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj V)) _ _ _

/-- Restricting `b` along `g : W ⟶ V` and multiplying by a `φ(e)` that restricts `m` gives the
restriction of `b * m`. -/
private theorem pushforwardUnitScale_map_mul {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    (e : E.val.obj (op W)) (b m : chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj V))
    (he : φ.val.app (op W) e =
      ((chartBaseChangeStructureModule B S hS f hf).val.map g.op).hom m) :
    pushforwardUnitScale φ e (((chartBaseChangeStructureModule B S hS f hf).val.map g.op).hom b) =
      ((chartBaseChangeStructureModule B S hS f hf).val.map g.op).hom (b * m) := by
  unfold pushforwardUnitScale
  dsimp only
  rw [he]
  exact (map_mul ((smallEtaleRingSheaf B S hS Y.1 Y.2).obj.map
    ((smallBaseChange B S hS f hf).map g).op).hom _ _).symm

/-- The product `b φ(e)` commutes with restriction along a morphism `g : W ⟶ V`. -/
theorem pushforwardUnitScale_map {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    (e : E.val.obj (op V)) (b : (chartBaseChangeStructureModule B S hS f hf).val.obj (op V))
    (e' : E.val.obj (op W)) (b' : (chartBaseChangeStructureModule B S hS f hf).val.obj (op W))
    (he : e' = (E.val.map g.op).hom e)
    (hb : b' = ((chartBaseChangeStructureModule B S hS f hf).val.map g.op).hom b) :
    pushforwardUnitScale φ e' b' =
      ((chartBaseChangeStructureModule B S hS f hf).val.map g.op).hom
        (pushforwardUnitScale φ e b) := by
  subst he hb
  exact pushforwardUnitScale_map_mul φ g _ b _ (PresheafOfModules.naturality_apply φ.val g.op e)

/-! ### The morphism out of the tensor product -/

/-- The morphism `E ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y`, `e ⊗ b ↦ b φ(e)`, of presheaves of modules. -/
def pushforwardUnitTensorMulPresheafHom :
    E.val ⊗ (chartBaseChangeStructureModule B S hS f hf).val ⟶
      (chartBaseChangeStructureModule B S hS f hf).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun e b => pushforwardUnitScale φ (V := U.unop) e b)
    (fun e₁ e₂ b => pushforwardUnitScale_add_left φ e₁ e₂ b)
    (fun (r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U) e b =>
      pushforwardUnitScale_smul_left φ r e b)
    (fun e b₁ b₂ => pushforwardUnitScale_add_right φ e b₁ b₂)
    (fun (r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U) e b =>
      pushforwardUnitScale_smul_right φ r e b)
  naturality g := ModuleCat.MonoidalCategory.tensor_ext fun e b =>
    pushforwardUnitScale_map φ g.unop e b _ _ rfl rfl

/-- **The multiplication morphism** `E ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y`, `e ⊗ b ↦ b φ(e)`, out of the tensor
product sheaf: `φ ⊗ 𝟙` followed by the multiplication of `f_*𝒪_Y`. -/
def pushforwardUnitTensorMulHom :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
      E).obj (chartBaseChangeStructureModule B S hS f hf) ⟶
      (chartBaseChangeStructureModule B S hS f hf) :=
  Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom.symm
    (pushforwardUnitTensorMulPresheafHom φ)

/-- The multiplication morphism reads on presheaves as the morphism built from sections. -/
private theorem tensorHomEquivPresheafTensorHom_mulHom :
    Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom (pushforwardUnitTensorMulHom φ) =
      pushforwardUnitTensorMulPresheafHom φ :=
  Equiv.apply_symm_apply Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom _

/-- **Every product `b φ(e)` of sections is a value of the multiplication morphism.** -/
theorem exists_pushforwardUnitTensorMulHom_app_eq (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (e : E.val.obj U) (b : (chartBaseChangeStructureModule B S hS f hf).val.obj U) :
    ∃ z : (((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj E).obj
          (chartBaseChangeStructureModule B S hS f hf)).val.obj U,
      (pushforwardUnitTensorMulHom φ).val.app U z = pushforwardUnitScale φ (V := U.unop) e b := by
  have h := congrArg (fun ψ => ψ.app U (e ⊗ₜ[(smallEtaleRingedSite B S hS X.1 X.2).O.obj.obj U] b))
    (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj) (pushforwardUnitTensorMulHom φ))
  refine ⟨_, h.symm.trans ?_⟩
  erw [tensorHomEquivPresheafTensorHom_mulHom]
  rfl

/-! ### The image is the kernel of the cokernel map, locally -/

/-- A section of the image of `φ` is killed by the cokernel map. -/
private theorem cokernelπ_app_eq_zero_of_mem_imageSubmodule {Q : SmallEtale B S hS X.1}
    (z : (chartBaseChangeStructureModule B S hS f hf).val.obj (op Q))
    (hz : z ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ).obj (op Q)) :
    (cokernel.π φ).val.app (op Q) z = 0 :=
  Stacks.AbelianSheaves.app_eq_zero_of_imageSieve_mem
    ((SheafOfModules.toSheaf _).map φ) ((SheafOfModules.toSheaf _).map (cokernel.π φ))
    (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]) Q z
    ((SmallEtale.topology B S hS X.1).superset_covering (fun _ _ hg => hg) hz)

/-- A section killed by the cokernel map lies in the image of `φ`. -/
private theorem mem_imageSubmodule_of_cokernelπ_app_eq_zero {Q : SmallEtale B S hS X.1}
    (z : (chartBaseChangeStructureModule B S hS f hf).val.obj (op Q))
    (hz : (cokernel.π φ).val.app (op Q) z = 0) :
    z ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ).obj (op Q) := by
  let SC := (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).map
    (SheafOfModules.toSheaf _)
  exact (SmallEtale.topology B S hS X.1).superset_covering (fun _ _ hg => hg)
    (Stacks.AbelianSheaves.imageSieve_mem_of_exact SC
      ((Stacks.SheafOfModules.exact_iff_toSheaf_exact _ _).mpr (ShortComplex.exact_cokernel φ))
      Q z hz)

/-! ### Closure of the image under multiplication -/

/-- **If `ℰ ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y ⟶ coker φ` vanishes, the image of `φ` is closed under
multiplication by `f_*𝒪_Y`.** -/
theorem mul_mem_imageSubmodule_of_pushforwardUnitTensorMulHom_comp_eq_zero
    (h : pushforwardUnitTensorMulHom φ ≫ cokernel.π φ = 0) (Q : SmallEtale B S hS X.1)
    (b m : chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q))
    (hm : m ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ).obj (op Q)) :
    b * m ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ).obj (op Q) := by
  refine mem_imageSubmodule_of_cokernelπ_app_eq_zero φ (b * m) ?_
  refine Stacks.AbelianSheaves.app_eq_zero_of_imageSieve_mem
    ((SheafOfModules.toSheaf _).map (pushforwardUnitTensorMulHom φ))
    ((SheafOfModules.toSheaf _).map (cokernel.π φ))
    (by rw [← Functor.map_comp, h, Functor.map_zero]) Q (b * m) ?_
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ hm
  rintro W g ⟨e, he⟩
  obtain ⟨z, hz⟩ := exists_pushforwardUnitTensorMulHom_app_eq φ (op W) e
    (((chartBaseChangeStructureModule B S hS f hf).val.map g.op).hom b)
  exact ⟨z, hz.trans (pushforwardUnitScale_map_mul φ g e b m he)⟩

/-- Morphisms out of the tensor product sheaf read on presheaves commute with postcomposition. -/
private theorem tensorHomEquivPresheafTensorHom_comp {N : Modules.{u, u} B S hS X.1 X.2}
    (a : ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
      E).obj (chartBaseChangeStructureModule B S hS f hf) ⟶
        (chartBaseChangeStructureModule B S hS f hf))
    (c : (chartBaseChangeStructureModule B S hS f hf) ⟶ N) :
    Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom (a ≫ c) =
      Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom a ≫ c.val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O).obj)).homEquiv_naturality_right a c

/-- **If the image of `φ` is closed under multiplication by `f_*𝒪_Y`, then
`ℰ ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y ⟶ coker φ` vanishes.** -/
theorem pushforwardUnitTensorMulHom_comp_eq_zero_of_mul_mem
    (hmul : ∀ (Q : SmallEtale B S hS X.1)
      (b m : chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q)),
        m ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ).obj (op Q) →
          b * m ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ).obj (op Q)) :
    pushforwardUnitTensorMulHom φ ≫ cokernel.π φ = 0 := by
  apply Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom.injective
  rw [← comp_zero (f := pushforwardUnitTensorMulHom φ) (Z := cokernel φ),
    tensorHomEquivPresheafTensorHom_comp, tensorHomEquivPresheafTensorHom_comp]
  rw [tensorHomEquivPresheafTensorHom_mulHom]
  ext U : 1
  refine ModuleCat.MonoidalCategory.tensor_ext fun e b => ?_
  simp only [PresheafOfModules.comp_app]
  exact (cokernelπ_app_eq_zero_of_mem_imageSubmodule φ _ (hmul U.unop b (φ.val.app U e)
    (Stacks.SheafOfModules.ImageSubsheaf.apply_mem_imageSubmodule φ e))).trans rfl

/-- **`ℰ ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y ⟶ coker φ` vanishes exactly when the image of `φ` is closed under
multiplication by the sections of `f_*𝒪_Y`.** -/
theorem pushforwardUnitTensorMulHom_comp_eq_zero_iff :
    pushforwardUnitTensorMulHom φ ≫ cokernel.π φ = 0 ↔
      ∀ (Q : SmallEtale B S hS X.1)
        (b m : chartSectionsRing B S hS Y ((smallBaseChange B S hS f hf).obj Q)),
          m ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ).obj (op Q) →
            b * m ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ).obj (op Q) :=
  ⟨mul_mem_imageSubmodule_of_pushforwardUnitTensorMulHom_comp_eq_zero φ,
    pushforwardUnitTensorMulHom_comp_eq_zero_of_mul_mem φ⟩

/-- **The image of `φ` is the direct image of a sheaf of ideals once the multiplication composite
vanishes.**  For an affine `f`, if `ℰ ⊗ f_*𝒪_Y ⟶ f_*𝒪_Y ⟶ coker φ` is zero and the image of `φ` is
quasi-coherent, then the image of `φ` is `f_*ℐ` for a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y`,
of finite type when the image is. -/
theorem exists_ideal_pushforwardSubmodule_eq_imageSubmodule (haff : IsAffineHom B S hS f.hom)
    (h : pushforwardUnitTensorMulHom φ ≫ cokernel.π φ = 0)
    (hM : (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ).toSheafOfModules
      |>.IsQuasicoherentOnSite) :
    ∃ I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS Y.1 Y.2)).Submodule,
      I.toSheafOfModules.IsQuasicoherentOnSite ∧
      (SheafOfModules.IsFiniteTypeOnSite
          ((Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ).toSheafOfModules :
            Modules.{u, u} B S hS X.1 X.2) →
        SheafOfModules.IsFiniteTypeOnSite
          (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)) ∧
      pushforwardSubmodule B S hS f hf _ I =
        Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ :=
  exists_ideal_pushforwardSubmodule_eq B S hS f hf
    (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ) haff
    (mul_mem_imageSubmodule_of_pushforwardUnitTensorMulHom_comp_eq_zero φ h) hM

end AlgebraicGeometry.Space

end
