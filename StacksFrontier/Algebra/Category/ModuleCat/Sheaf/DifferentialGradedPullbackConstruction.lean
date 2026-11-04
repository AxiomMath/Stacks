module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleStructures

/-!
# The pullback of a right differential graded module, constructed as `f⁻¹M ⊗_{f⁻¹A'} A`

Let `F : C ⥤ D` be a continuous functor of sites, read as the functor underlying a morphism of
ringed sites `f` in the opposite direction, and let `α : O ⟶ f_*P` be the structure map of its
sheaves of commutative rings. Let `A'` be a sheaf of differential graded `O`-algebras, let `A` be
a sheaf of differential graded `P`-algebras and let `φ₀ : f⁻¹A' ⟶ A` be a unital homomorphism of
sheaves of differential graded `P`-algebras. For a right differential graded `A'`-module `M` the
module `f^*M = f⁻¹M ⊗_{f⁻¹A'} A` is a right differential graded `A`-module: the inverse image
`f⁻¹M` is a right differential graded `f⁻¹A'`-module, `A` is a differential graded
`(f⁻¹A', A)`-bimodule through `φ₀`, and the relative tensor product of the two is a right
differential graded `A`-module.

## Main definitions

* `Stacks.DifferentialGradedPullbackConstruction.pushforwardAlgebra` is `f_*A` as a sheaf of
  differential graded `O`-algebras, and `structureMapEquiv` is the adjunction
  `(f⁻¹A' ⟶ A) ≃ (A' ⟶ f_*A)` of sheaves of differential graded algebras, with `structureMap`
  the adjoint transpose of a homomorphism `A' ⟶ f_*A`.
* `Stacks.DifferentialGradedPullbackConstruction.pullbackBimodule` is **`A` as a differential
  graded `(f⁻¹A', A)`-bimodule** through `φ₀`.
* `Stacks.DifferentialGradedPullbackConstruction.pullbackObj` is **the pullback
  `f^*M = f⁻¹M ⊗_{f⁻¹A'} A`**, a right differential graded `A`-module.

## Main results

* `Stacks.DifferentialGradedPullbackConstruction.pullbackObj_complex`: the cochain complex of
  `f^*M` is the relative tensor product of the complex of `f⁻¹M` with that of `A`.
* `Stacks.DifferentialGradedPullbackConstruction.pullbackObj_mul_tmul` and
  `pullbackObj_d_tmul`: the action of `A` and the differential of `f^*M` on a local section
  `x ⊗ y`.

## Implementation notes

The two ingredients live at different spellings of the same data. The inverse image of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInverseImage` is built from the
monoidality of `CategoryTheory.SheafOfModules.pullback`, so it is stated for small categories in
a single universe with `[CategoryTheory.Functor.RepresentablyFlat F]` and `[F.Final]`; the
relative tensor product of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensor` produces a right
differential graded module over an algebra whose homogeneous pieces live in `max u v`. At a small
site those two settings agree, which is why the pullback can be formed at all.

The structure map `φ₀ : f⁻¹A' ⟶ A` is not extra data: it is the adjoint transpose of a
homomorphism `A' ⟶ f_*A` under the adjunction between pullback and pushforward of sheaves of
differential graded algebras, whose inverse map is
`SheafOfModules.DifferentialGradedAlgebra.transportHomBackward`. That adjunction needs the
pushforward to be lax monoidal and additive, which `pushforwardLaxMonoidal` and
`pushforward_additive` supply from the monoidality of the inverse image; both are local
instances.

Unitality of `φ₀` is a separate hypothesis because a homomorphism of sheaves of differential
graded algebras is not required to preserve the unit, while the bimodule structure on `A` needs
it: the unit axiom for the left action of `f⁻¹A'` on `A` is exactly `φ₀ 1 = 1`.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf Functor
open Stacks.SheafOfModules.TensorSheafification Stacks.PullbackMonoidalSite
open Stacks.DifferentialGradedInverseImage

universe u

namespace Stacks.DifferentialGradedPullbackConstruction

/-- The direct image of sheaves of modules along a continuous functor of sites is additive. -/
theorem pushforward_additive {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [Functor.IsContinuous F J K] {S : Sheaf J RingCat.{u}} {T : Sheaf K RingCat.{u}}
    (ρ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj T) :
    (SheafOfModules.pushforward.{u} ρ).Additive where
  map_add := rfl

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [Functor.IsContinuous F J K] [RepresentablyFlat F] [F.Final]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}} {Psharp : Sheaf K CommRingCat.{u}}
  (α : Osharp.obj ⟶ F.op ⋙ Psharp.obj)
  (hO : Presheaf.IsSheaf J (structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K (structureRingPresheaf Psharp.obj))
  [radj : (SheafOfModules.pushforward.{u} (sheafRingHom α hO hP)).IsRightAdjoint]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
attribute [local instance] inverseImageMonoidal
attribute [local instance] pushforward_additive

/-- The adjunction between the inverse image and the direct image of sheaves of modules along a
continuous functor of sites. -/
noncomputable abbrev inverseImageAdjunction :
    inverseImageModules α hO hP ⊣ SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP) :=
  SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingHom α hO hP)

/-- The direct image of sheaves of modules is lax monoidal, being right adjoint to the strong
monoidal inverse image. -/
noncomputable abbrev pushforwardLaxMonoidal :
    (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).LaxMonoidal :=
  (inverseImageAdjunction α hO hP).rightAdjointLaxMonoidal

attribute [local instance] pushforwardLaxMonoidal

variable {A' : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}
  {A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)}

/-- **`f_*A` as a sheaf of differential graded `O`-algebras**: its cochain complex is the direct
image of that of `A` degreewise. -/
noncomputable def pushforwardAlgebra
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)) :
    SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp) :=
  SheafOfModules.DifferentialGradedAlgebra.transport
    (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)) hP hO A

/-- The cochain complex of `f_*A` is the direct image of the cochain complex of `A`,
degreewise. -/
theorem pushforwardAlgebra_complex
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)) :
    (pushforwardAlgebra α hO hP A).complex =
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A.complex :=
  rfl

/-- **Homomorphisms `f⁻¹A' ⟶ A` of sheaves of differential graded algebras are homomorphisms
`A' ⟶ f_*A`**, the adjunction of part (3) of the functoriality of sheaves of differential graded
algebras at a continuous functor of sites. -/
noncomputable def structureMapEquiv
    (A' : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp))
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)) :
    (inverseImageAlgebra α hO hP A' ⟶ A) ≃ (A' ⟶ pushforwardAlgebra α hO hP A) :=
  SheafOfModules.DifferentialGradedAlgebra.transportHomEquiv
    (inverseImageAdjunction α hO hP) hP hO A A'

/-- **The structure map `f⁻¹A' ⟶ A` of a homomorphism `ψ : A' ⟶ f_*A`**, its adjoint
transpose. -/
noncomputable def structureMap (ψ : A' ⟶ pushforwardAlgebra α hO hP A) :
    inverseImageAlgebra α hO hP A' ⟶ A :=
  (structureMapEquiv α hO hP A' A).symm ψ

/-- In each degree the structure map is the adjoint transpose of `ψ` on sheaves of modules. -/
@[simp]
theorem structureMap_f (ψ : A' ⟶ pushforwardAlgebra α hO hP A) (n : ℤ) :
    (structureMap α hO hP ψ).toHomologicalComplex.f n =
      ((inverseImageAdjunction α hO hP).homEquiv (A'.complex.X n) (A.complex.X n)).symm
        (ψ.toHomologicalComplex.f n) :=
  rfl

/-- **`A` as a differential graded `(f⁻¹A', A)`-bimodule** through a unital homomorphism
`φ₀ : f⁻¹A' ⟶ A`: a homogeneous section `a` of `f⁻¹A'` acts on the left as `φ₀ a`. -/
noncomputable def pullbackBimodule (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A)
    (hφ₀ : φ₀.IsUnital) :
    SheafOfModules.DifferentialGradedBimodule.{u, u, u} (inverseImageAlgebra α hO hP A') A :=
  SheafOfModules.DifferentialGradedAlgebra.asBimodule φ₀ hφ₀

/-- **The pullback `f^*M = f⁻¹M ⊗_{f⁻¹A'} A` of a right differential graded `A'`-module**, a
right differential graded `A`-module: the relative tensor product of the inverse image of `M`
with `A`, read as a differential graded `(f⁻¹A', A)`-bimodule through `φ₀`. -/
noncomputable def pullbackObj (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)
    (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A') :
    SheafOfModules.DifferentialGradedModule.{u, u, u} A :=
  SheafOfModules.RelativeTensor.dgTensorRight (inverseImageModule α hO hP M)
    (pullbackBimodule α hO hP φ₀ hφ₀)

/-- The cochain complex of `f^*M` is the relative tensor product of the complex of `f⁻¹M` with
the complex of `A`, read as a left differential graded `f⁻¹A'`-module. -/
theorem pullbackObj_complex (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)
    (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A') :
    (pullbackObj α hO hP φ₀ hφ₀ M).complex =
      SheafOfModules.RelativeTensor.dgTensor (inverseImageModule α hO hP M)
        (pullbackBimodule α hO hP φ₀ hφ₀).toLeftDifferentialGradedModule :=
  rfl

/-- **The action of a homogeneous section `b` of `A` on a local section `x ⊗ y` of `f^*M`**: it is
`x ⊗ (y b)`. -/
theorem pullbackObj_mul_tmul (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)
    (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A') (n i : ℤ)
    (p : SheafOfModules.TensorIndex n) (X : Dᵒᵖ)
    (x : ((SheafOfModules.RelativeTensor.gP
      (inverseImageModule α hO hP M)).piece p.1.1).val.obj X)
    (y : (A.complex.X p.1.2).val.obj X) (b : (A.complex.X i).val.obj X) :
    ((pullbackObj α hO hP φ₀ hφ₀ M).mul n i).app X
        (SheafOfModules.RelativeTensor.tmul
          (SheafOfModules.RelativeTensor.gP (inverseImageModule α hO hP M))
          (pullbackBimodule α hO hP φ₀ hφ₀).toGradedBimodule.toLeftGradedModule n p X x y) b =
      SheafOfModules.RelativeTensor.tmul
        (SheafOfModules.RelativeTensor.gP (inverseImageModule α hO hP M))
        (pullbackBimodule α hO hP φ₀ hφ₀).toGradedBimodule.toLeftGradedModule (n + i)
        (SheafOfModules.RelativeTensor.actIndex p i (n + i) rfl) X x
        ((A.mul p.1.2 i).app X y b) :=
  SheafOfModules.RelativeTensor.dgTensorRight_mul_tmul (inverseImageModule α hO hP M)
    (pullbackBimodule α hO hP φ₀ hφ₀) n i p X x y b

/-- **The differential of `f^*M` on a local section `x ⊗ y`**: it is
`dx ⊗ y + (-1)^{deg x} x ⊗ dy`. -/
theorem pullbackObj_d_tmul (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)
    (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A') (n : ℤ)
    (p : SheafOfModules.TensorIndex n) (X : Dᵒᵖ)
    (x : ((SheafOfModules.RelativeTensor.gP
      (inverseImageModule α hO hP M)).piece p.1.1).val.obj X)
    (y : (A.complex.X p.1.2).val.obj X) :
    PresheafOfModules.Hom.app
        ((pullbackObj α hO hP φ₀ hφ₀ M).complex.d n (n + 1)).val X
        (SheafOfModules.RelativeTensor.tmul
          (SheafOfModules.RelativeTensor.gP (inverseImageModule α hO hP M))
          (pullbackBimodule α hO hP φ₀ hφ₀).toGradedBimodule.toLeftGradedModule n p X x y) =
      SheafOfModules.RelativeTensor.tmul
          (SheafOfModules.RelativeTensor.gP (inverseImageModule α hO hP M))
          (pullbackBimodule α hO hP φ₀ hφ₀).toGradedBimodule.toLeftGradedModule (n + 1)
          (SheafOfModules.RelativeTensor.tensorIndexShiftLeft p) X
          (((inverseImageModule α hO hP M).complex.d p.1.1 (p.1.1 + 1)).val.app X x) y +
        (Int.negOnePow p.1.1 : ℤ) •
          SheafOfModules.RelativeTensor.tmul
            (SheafOfModules.RelativeTensor.gP (inverseImageModule α hO hP M))
            (pullbackBimodule α hO hP φ₀ hφ₀).toGradedBimodule.toLeftGradedModule (n + 1)
            (SheafOfModules.RelativeTensor.tensorIndexShiftRight p) X x
            ((A.complex.d p.1.2 (p.1.2 + 1)).val.app X y) :=
  SheafOfModules.RelativeTensor.dgTensorRight_d_tmul (inverseImageModule α hO hP M)
    (pullbackBimodule α hO hP φ₀ hφ₀) n p X x y

/-- The pullback formed from a homomorphism `ψ : A' ⟶ f_*A` of sheaves of differential graded
algebras whose adjoint transpose is unital. -/
noncomputable def pullbackObjOfPushforwardHom (ψ : A' ⟶ pushforwardAlgebra α hO hP A)
    (hψ : (structureMap α hO hP ψ).IsUnital)
    (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A') :
    SheafOfModules.DifferentialGradedModule.{u, u, u} A :=
  pullbackObj α hO hP (structureMap α hO hP ψ) hψ M

end Stacks.DifferentialGradedPullbackConstruction

end
