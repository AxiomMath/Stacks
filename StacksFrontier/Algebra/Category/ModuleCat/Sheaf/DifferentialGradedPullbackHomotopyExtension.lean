module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissibleBimoduleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleTransportHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedAdmissible

/-!
# The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` on homotopy categories, for the constructed pullback

Let `F : C ⥤ D` be a continuous, representably flat and final functor of small sites in one
universe, read as the functor underlying a morphism of ringed sites `f` in the opposite
direction, with structure map `α : O ⟶ f_*P` of its sheaves of commutative rings. Let `ℬ` be a
sheaf of differential graded `O`-algebras on the target, let `𝒜` and `𝒜'` be sheaves of
differential graded `P`-algebras on the source, let `φ₀ : f⁻¹ℬ ⟶ 𝒜` be a unital homomorphism
and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule. This file produces the functor

`K(Mod(ℬ, d)) ⟶ K(Mod(𝒜', d))`, `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`

of [Stacks, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE) for such a functor of sites:
the pullback is the construction `f^*ℳ = f⁻¹ℳ ⊗_{f⁻¹ℬ} 𝒜` of
`DifferentialGradedPullbackConstruction.lean`, and the tensor product is the relative tensor
product of `DifferentialGradedBimoduleTensorUniversal.lean`.

The one thing the universal property of the pullback does not give is the pullback of a
*homotopy*: a homotopy is a degree `-1` map, while
`SheafOfModules.DifferentialGradedModule.IsPullback` speaks only of morphisms, that is of
degree-zero maps. Here it comes from the construction. The pullback of a morphism *is* the
extension of scalars of its inverse image along `φ₀`, which is `pullbackData_map` below; the
inverse image carries a homotopy by
`SheafOfModules.DifferentialGradedModule.transportHomotopy`, and extension of scalars carries
one by `SheafOfModules.TensorFunctorData.mapHomotopy`.

## Main definitions

* `Stacks.DifferentialGradedPullbackConstruction.pullbackHomotopyExtension` is the pullback of
  a homotopy, that is the `SheafOfModules.DifferentialGradedModule.PullbackData.HomotopyExtension`
  of the constructed pullback.
* `Stacks.DifferentialGradedPullbackConstruction.homotopyPullbackTensor` is **the functor
  `K(Mod(ℬ, d)) ⟶ K(Mod(𝒜', d))`, `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`**.

## Main results

* `Stacks.DifferentialGradedPullbackConstruction.pullbackData_map`: the pullback of a morphism
  is the extension of scalars of its inverse image.
* `Stacks.DifferentialGradedPullbackConstruction.preservesHomotopic_pullbackFunctor`: the
  pullback carries homotopic morphisms to homotopic morphisms.
* `Stacks.DifferentialGradedPullbackConstruction.isAdmissibleShortExact_pullbackTensor`: the
  functor carries an admissible short exact sequence to an admissible short exact sequence,
  which by Tag 0FS7 is the triangle half of its exactness.
* `Stacks.DifferentialGradedPullbackConstruction.exists_homotopyPullbackTensor`: the functor
  descends to the homotopy categories. The exact functor of Tag 0FTE along a morphism of ringed
  topoi is
  `SheafOfModules.DifferentialGradedModule.exists_isTriangulated_homotopyToposPullbackTensorTopos`.

## Implementation notes

The identification of the pullback of a morphism with the extension of scalars of its inverse
image is proved from the uniqueness half of the universal property: both morphisms compose with
the unit of the pullback of the source to the unit of the pullback of the target precomposed
with the morphism. That in turn is naturality in the *source* of the three bijections composing
`Stacks.DifferentialGradedPullbackConstruction.pullbackHomEquiv`, which is
`SheafOfModules.DifferentialGradedModule.extensionUnit_naturality` for the first,
`CategoryTheory.Adjunction.homEquiv_naturality_left` for the second and a computation on local
sections for the third.

## References

* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf Functor
open Stacks.SheafOfModules.TensorSheafification Stacks.PullbackMonoidalSite
open Stacks.DifferentialGradedInverseImage

universe u

namespace Stacks.DifferentialGradedPullbackConstruction

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
attribute [local instance] pushforwardLaxMonoidal

include radj

variable {A' : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}
  {A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)}

open SheafOfModules.DifferentialGradedModule

variable (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A) (hφ₀ : φ₀.IsUnital)

/-! ### The pullback functor is the inverse image followed by extension of scalars -/

section Factorisation

variable {M M₂ : SheafOfModules.DifferentialGradedModule.{u, u, u} A'}

/-- Composing the unit of the pullback with a morphism out of the pullback is the universal
property's bijection. -/
theorem pullbackUnit_postcomp (N : SheafOfModules.DifferentialGradedModule.{u, u, u} A)
    (g : pullbackObj α hO hP φ₀ hφ₀ M ⟶ N) :
    (pullbackUnit α hO hP φ₀ hφ₀ M).postcomp g =
      pullbackHomEquiv α hO hP φ₀ hφ₀ M N g :=
  (pullbackHomEquiv_comp α hO hP φ₀ hφ₀ M (pullbackObj α hO hP φ₀ hφ₀ M) N
        (𝟙 (pullbackObj α hO hP φ₀ hφ₀ M)) g).symm.trans
    (congrArg (pullbackHomEquiv α hO hP φ₀ hφ₀ M N) (Category.id_comp g))

/-- The unit of the extension of scalars is the hom-set bijection at the identity. -/
theorem extensionRestrictionHomEquiv_id
    (Q : SheafOfModules.DifferentialGradedModule.{u, u, u}
      (inverseImageAlgebra α hO hP A')) :
    extensionRestrictionHomEquiv φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀) Q
        ((pullbackTensorFunctorData α hO hP φ₀ hφ₀).functor.obj Q)
        (𝟙 ((pullbackTensorFunctorData α hO hP φ₀ hφ₀).functor.obj Q)) =
      extensionUnit φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀) Q := by
  show extensionUnit φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀) Q ≫
      (restriction φ₀ hφ₀).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The universal property of the pullback is natural in the source**: the extension of
scalars of the inverse image of a morphism, composed with the unit of the pullback of the
source, is the unit of the pullback of the target precomposed with the morphism. -/
theorem pullbackHomEquiv_extension (ψ : M ⟶ M₂) :
    pullbackHomEquiv α hO hP φ₀ hφ₀ M (pullbackObj α hO hP φ₀ hφ₀ M₂)
        ((pullbackTensorFunctorData α hO hP φ₀ hφ₀).functor.map
          ((inverseImageFunctor α hO hP).map ψ)) =
      (pullbackUnit α hO hP φ₀ hφ₀ M₂).precomp ψ := by
  have hE : extensionRestrictionHomEquiv φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀)
        (inverseImageModule α hO hP M) (pullbackObj α hO hP φ₀ hφ₀ M₂)
        ((pullbackTensorFunctorData α hO hP φ₀ hφ₀).functor.map
          ((inverseImageFunctor α hO hP).map ψ)) =
      (inverseImageFunctor α hO hP).map ψ ≫
        extensionUnit φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀)
          (inverseImageModule α hO hP M₂) :=
    (extensionUnit_naturality φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀)
      ((inverseImageFunctor α hO hP).map ψ)).symm
  have hT : transposeEquiv α hO hP φ₀ hφ₀ M (pullbackObj α hO hP φ₀ hφ₀ M₂)
        ((inverseImageFunctor α hO hP).map ψ ≫
          extensionUnit φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀)
            (inverseImageModule α hO hP M₂)) =
      ψ ≫ transposeEquiv α hO hP φ₀ hφ₀ M₂ (pullbackObj α hO hP φ₀ hφ₀ M₂)
        (extensionUnit φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀)
          (inverseImageModule α hO hP M₂)) :=
    SheafOfModules.DifferentialGradedModule.Hom.ext fun q =>
      Adjunction.homEquiv_naturality_left (inverseImageAdjunction α hO hP)
        (ψ.toHomologicalComplex.f q)
        ((extensionUnit φ₀ hφ₀ (pullbackTensorFunctorData α hO hP φ₀ hφ₀)
          (inverseImageModule α hO hP M₂)).toHomologicalComplex.f q)
  simp only [pullbackUnit, pullbackHomEquiv]
  erw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, hE, hT,
    extensionRestrictionHomEquiv_id]
  rfl

/-- **The pullback of a morphism is the extension of scalars of its inverse image.** -/
theorem pullbackData_map (ψ : M ⟶ M₂) :
    (pullbackData α hO hP φ₀ hφ₀).map ψ =
      (pullbackTensorFunctorData α hO hP φ₀ hφ₀).functor.map
        ((inverseImageFunctor α hO hP).map ψ) := by
  refine ((pullbackData α hO hP φ₀ hφ₀).isPullback M).hom_ext ?_
  refine Eq.trans ((pullbackData α hO hP φ₀ hφ₀).unit_postcomp_map ψ) ?_
  refine Eq.trans (pullbackHomEquiv_extension α hO hP φ₀ hφ₀ ψ).symm ?_
  exact (pullbackUnit_postcomp α hO hP φ₀ hφ₀ (pullbackObj α hO hP φ₀ hφ₀ M₂) _).symm

end Factorisation

/-! ### The pullback of a homotopy -/

/-- **The pullback of a homotopy along the morphism of ringed sites**: the inverse image of the
homotopy, tensored with the identity of `𝒜`. This is the extra datum that
`DifferentialGradedPullbackTensor.lean` carries as
`SheafOfModules.DifferentialGradedModule.PullbackData.HomotopyExtension`; here it is a
theorem. -/
noncomputable def pullbackHomotopyExtension :
    (pullbackData α hO hP φ₀ hφ₀).HomotopyExtension where
  mapHomotopy {_M _M₂ ψ χ} h :=
    ((pullbackTensorFunctorData α hO hP φ₀ hφ₀).mapHomotopy
      (transportHomotopy (inverseImageModules α hO hP) hO hP h)).ofDiffEq fun _ => by
        rw [pullbackData_map α hO hP φ₀ hφ₀ ψ, pullbackData_map α hO hP φ₀ hφ₀ χ]
        rfl

/-- **The pullback carries homotopic morphisms of right differential graded modules to
homotopic morphisms.** -/
theorem preservesHomotopic_pullbackFunctor :
    PreservesHomotopic (pullbackFunctor α hO hP φ₀ hφ₀) :=
  (pullbackHomotopyExtension α hO hP φ₀ hφ₀).preservesHomotopic

/-! ### The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE -/

variable {A₂ : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)}

/-- **The functor `K(Mod(ℬ, d)) ⟶ K(Mod(𝒜', d))`, `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`**, induced on the
homotopy categories by the pullback along `f` followed by the tensor product with the
differential graded `(𝒜, 𝒜')`-bimodule `𝒩`. -/
noncomputable def homotopyPullbackTensor
    (N : SheafOfModules.DifferentialGradedBimodule.{u, u, u} A A₂) :
    SheafOfModules.DifferentialGradedModule.HomotopyCategory.{u, u, u} A' ⥤
      SheafOfModules.DifferentialGradedModule.HomotopyCategory.{u, u, u} A₂ :=
  HomotopyCategory.pullbackTensor (pullbackHomotopyExtension α hO hP φ₀ hφ₀)
    (SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight N)

/-- **The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` carries an admissible short exact sequence to an
admissible short exact sequence.** Admissibility asks only that the sequence be split after the
differentials are forgotten, and both halves of the functor are additive functors of the
underlying graded modules: the pullback by
`SheafOfModules.DifferentialGradedModule.GradedSplitting.pullback` and the tensor product by
`SheafOfModules.DifferentialGradedModule.GradedSplitting.dgTensorRight`.

By [Stacks, Tag 0FS7] the distinguished triangles of `K(Mod(𝒜', d))` are the triangles of
admissible short exact sequences, so this is the triangle half of the exactness of the functor
of Tag 0FTE. -/
theorem isAdmissibleShortExact_pullbackTensor
    (N : SheafOfModules.DifferentialGradedBimodule.{u, u, u} A A₂)
    {M M₂ M₃ : SheafOfModules.DifferentialGradedModule.{u, u, u} A'}
    {ψ : M ⟶ M₂} {χ : M₂ ⟶ M₃} (h : IsAdmissibleShortExact ψ χ) :
    IsAdmissibleShortExact
      ((pullbackTensorFunctor (pullbackData α hO hP φ₀ hφ₀)
        (SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight N)).map ψ)
      ((pullbackTensorFunctor (pullbackData α hO hP φ₀ hφ₀)
        (SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight N)).map χ) :=
  (h.pullback (pullbackData α hO hP φ₀ hφ₀)).dgTensorRight N

/-- **The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` on homotopy categories, for the constructed pullback.**
For a morphism of ringed sites `f`, a sheaf of differential graded
algebras `ℬ` on its target, sheaves of differential graded algebras `𝒜` and `𝒜'` on its
source, a unital homomorphism `φ₀ : f⁻¹ℬ ⟶ 𝒜` and a differential graded `(𝒜, 𝒜')`-bimodule
`𝒩`, there is a functor

`K(Mod(ℬ, d)) ⟶ K(Mod(𝒜', d))`, `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`

on the homotopy categories of right differential graded modules. It is the functor
`G : Mod(ℬ, d) ⟶ Mod(𝒜', d)` whose value at `ℳ` is a tensor product of the pullback
`f^*ℳ = f⁻¹ℳ ⊗_{f⁻¹ℬ} 𝒜` with `𝒩`, and which sends a morphism `ψ` to `f^*ψ ⊗ 1` on local
sections, descended through the two quotient functors. -/
theorem exists_homotopyPullbackTensor
    (N : SheafOfModules.DifferentialGradedBimodule.{u, u, u} A A₂) :
    ∃ (G : SheafOfModules.DifferentialGradedModule.{u, u, u} A' ⥤
          SheafOfModules.DifferentialGradedModule.{u, u, u} A₂)
      (hG : ∀ M : SheafOfModules.DifferentialGradedModule.{u, u, u} A',
          SheafOfModules.IsTensorProduct (pullbackObj α hO hP φ₀ hφ₀ M) N (G.obj M))
      (Φ : SheafOfModules.DifferentialGradedModule.HomotopyCategory.{u, u, u} A' ⥤
          SheafOfModules.DifferentialGradedModule.HomotopyCategory.{u, u, u} A₂),
      (∀ (M M₂ : SheafOfModules.DifferentialGradedModule.{u, u, u} A') (ψ : M ⟶ M₂) (i j : ℤ)
          (U : Dᵒᵖ) (x : ((pullbackObj α hO hP φ₀ hφ₀ M).complex.X i).val.obj U)
          (y : (N.complex.X j).val.obj U),
        ((G.map ψ).toHomologicalComplex.f (i + j)).val.app U ((hG M).tmul i j U x y) =
          (hG M₂).tmul i j U
            ((((pullbackFunctor α hO hP φ₀ hφ₀).map ψ).toHomologicalComplex.f i).val.app U x)
            y) ∧
        SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient A' ⋙ Φ =
          G ⋙ SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient A₂ :=
  ⟨pullbackTensorFunctor (pullbackData α hO hP φ₀ hφ₀)
      (SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight N),
    fun M => isTensorProduct_pullbackTensorFunctor_obj (pullbackData α hO hP φ₀ hφ₀)
      (SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight N) M,
    homotopyPullbackTensor α hO hP φ₀ hφ₀ N,
    fun _ _ ψ i j U x y => pullbackTensorFunctor_map_tmul (pullbackData α hO hP φ₀ hφ₀)
      (SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight N) ψ i j U x y,
    HomotopyCategory.quotient_comp_pullbackTensor (pullbackHomotopyExtension α hO hP φ₀ hφ₀)
      (SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight N)⟩

end Stacks.DifferentialGradedPullbackConstruction

end
