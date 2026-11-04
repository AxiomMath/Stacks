module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom

/-!
# The derived multiplication of a sheaf of algebras

Let `A` be a sheaf of commutative `𝒪_X`-algebras on a scheme `X`. Multiplication of sections is
`𝒪_X`-bilinear and compatible with restriction, so it descends to a morphism `A ⊗_{𝒪_X} A ⟶ A` of
sheaves of `𝒪_X`-modules. Composing the canonical map from the derived tensor product with the
degree-zero identification of the total tensor complex of two complexes concentrated in degree
zero gives the derived multiplication `A ⊗^L_{𝒪_X} A ⟶ A` in `D(𝒪_X)`.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.bilinearMul`: multiplication of sections, as a bilinear map
  of the underlying presheaves of modules.
* `Stacks.RelativeSpec.AlgebraSheaf.mul`: the multiplication `A ⊗_{𝒪_X} A ⟶ A` of the underlying
  sheaves of modules.
* `Stacks.RelativeSpec.AlgebraSheaf.singleMul`: the multiplication as a map of complexes
  `Tot(A[0] ⊗_{𝒪_X} A[0]) ⟶ A[0]`.
* `Stacks.RelativeSpec.AlgebraSheaf.derivedMul`: the derived multiplication `A ⊗^L_{𝒪_X} A ⟶ A`
  in `D(𝒪_X)`.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.sheafificationHomEquiv_mul`: the multiplication of sheaves
  of modules restricts along the sheafification unit of the presheaf tensor product to
  multiplication of sections.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} (A : AlgebraSheaf X)

/-- The underlying `𝒪_X`-module of a sheaf of algebras, spelled as a sheaf of modules over the
underlying sheaf of rings of `X` rather than through the type synonym `Scheme.Modules`. -/
abbrev moduleOfAlgebra : SheafOfModules.{u} X.ringCatSheaf := underlyingModule A

/-- The sections of the underlying module of a sheaf of commutative algebras over an open form a
commutative ring: the ring of sections of the algebra. -/
local instance sectionsCommRing (U : (Opens X)ᵒᵖ) :
    CommRing ((moduleOfAlgebra A).val.obj U) :=
  inferInstanceAs (CommRing (A.right.obj.obj U))

/-- Multiplication of sections of a sheaf of commutative algebras, as a bilinear map of the
underlying presheaves of `𝒪_X`-modules: over each open it is the multiplication of the ring of
sections. -/
def bilinearMul : Stacks.BilinearMap (moduleOfAlgebra A).val (moduleOfAlgebra A).val
    (moduleOfAlgebra A).val where
  app _ := AddMonoidHom.mul
  map_smul_left _ _ x y := mul_assoc _ x y
  map_smul_right _ _ x y := mul_left_comm x _ y
  naturality f x y := map_mul ((ringSheaf A).obj.map f).hom x y

/-- Multiplication of a sheaf of commutative algebras, as a morphism out of the objectwise
tensor product of the underlying presheaves of modules. -/
def presheafMul :
    PresheafOfModules.tensorObj (moduleOfAlgebra A).val (moduleOfAlgebra A).val ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj (moduleOfAlgebra A).val :=
  PresheafOfModules.ofBilinear (bilinearMul A)

/-- **The multiplication `A ⊗_{𝒪_X} A ⟶ A` of a sheaf of commutative `𝒪_X`-algebras**, as a
morphism of sheaves of `𝒪_X`-modules. -/
def mul :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (moduleOfAlgebra A)).obj
        (moduleOfAlgebra A) ⟶
      moduleOfAlgebra A :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm (presheafMul A)

/-- The multiplication restricts along the sheafification unit of the presheaf tensor product
to multiplication of sections. -/
theorem sheafificationHomEquiv_mul :
    PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) (mul A) = presheafMul A :=
  (PresheafOfModules.sheafificationHomEquiv _).apply_symm_apply _

/-! ### The derived multiplication

The universes of the site `Opens X` and of the sections of `𝒪_X` coincide, so the additivity
of `⊗_{𝒪_X}` and the existence of the total tensor complexes are named rather than synthesized:
the search would have to solve `max ?u ?v =?= u` with both unknown. They are the shared
`Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive`, `sheafTensorObjAdditive` and
`hasMapBifunctorSheafTensor`. -/

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- The underlying module of a sheaf of algebras, placed in cohomological degree zero. -/
abbrev single : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj (moduleOfAlgebra A)

/-- **The multiplication as a map of complexes** `Tot(A[0] ⊗_{𝒪_X} A[0]) ⟶ A[0]`: the total
tensor complex of two complexes concentrated in degree zero is itself concentrated in degree
zero, where it is `A ⊗_{𝒪_X} A`. -/
def singleMul :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj (single A)).obj (single A) ⟶
      single A :=
  (HomologicalComplex.mapBifunctorSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (moduleOfAlgebra A)
      (moduleOfAlgebra A)).hom ≫
    (CochainComplex.singleFunctor _ 0).map (mul A)

/-- **The derived multiplication `A ⊗^L_{𝒪_X} A ⟶ A` of a sheaf of commutative
`𝒪_X`-algebras**: the canonical map from the derived tensor product to the ordinary total
tensor complex, followed by the multiplication of complexes. -/
def derivedMul :
    ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj
          (DerivedCategory.Q.obj (single A))).obj (DerivedCategory.Q.obj (single A)) ⟶
      DerivedCategory.Q.obj (single A) :=
  (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf)).toTensor (single A) (single A) ≫
    DerivedCategory.Q.map (singleMul A)

end Stacks.RelativeSpec.AlgebraSheaf

end
