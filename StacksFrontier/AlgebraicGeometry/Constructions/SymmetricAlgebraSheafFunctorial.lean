module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFunctorial
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of `Sym` and of the vector bundle `𝐕(ℱ)` in the module

A morphism `f : ℱ ⟶ 𝒢` of `𝒪_X`-modules induces a morphism of sheaves of commutative
`𝒪_X`-algebras

`Sym(f) : Sym(ℱ) ⟶ Sym(𝒢)`

and hence, contravariantly, a morphism of schemes over `X`

`𝐕(f) : 𝐕(𝒢) ⟶ 𝐕(ℱ)`,

both compatibly with identities and composition.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraUnitalHom`: the unital homomorphism of
  sheaves of graded algebras `Sym(ℱ) ⟶ Sym(𝒢)` induced by `f : ℱ ⟶ 𝒢`.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheafMap`: `Sym(f) : Sym(ℱ) ⟶ Sym(𝒢)` as a
  morphism of sheaves of commutative `𝒪_X`-algebras, and `symmetricAlgebraSheafFunctor` the
  functor from `𝒪_X`-modules to sheaves of commutative `𝒪_X`-algebras it assembles into.
* `AlgebraicGeometry.Scheme.Modules.vectorBundleMap`: `𝐕(f) : 𝐕(𝒢) ⟶ 𝐕(ℱ)` as a morphism of
  schemes over `X`.

## Main results

* `Stacks.RelativeSpec.gradedAlgebraSheafMap_id` and `gradedAlgebraSheafMap_comp`: functoriality
  of `Stacks.RelativeSpec.gradedAlgebraSheafMap`.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheafMap_id` and
  `symmetricAlgebraSheafMap_comp`: functoriality of `Sym` in the module, and
  `symmetricAlgebraSheafMap_ungradedIncl` the formula on a homogeneous local section.
* `AlgebraicGeometry.Scheme.Modules.pushforwardAlgebraMap_vectorBundleMap`: `𝐕(f)` is the
  morphism of schemes over `X` classified by `Sym(f)` under the universal property of the
  relative spectrum.
* `AlgebraicGeometry.Scheme.Modules.vectorBundleMap_id` and `vectorBundleMap_comp`:
  functoriality of `𝐕` in the module.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence

universe u

/-! ### The algebra sheaf of a sheaf of graded algebras is functorial -/

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A B D : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
    HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
  (hB : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (B.piece i).val.obj W) (b : (B.piece j).val.obj W),
    HEq ((B.mul i j).app W a b) ((B.mul j i).app W b a))

/-- The underlying morphism of sheaves of commutative rings of the algebra sheaf map induced by
`ψ` is the ungraded realization `SheafOfModules.GradedAlgebra.ungradedCommSheafMap ψ`. -/
@[simp]
theorem gradedAlgebraSheafMap_right (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    (gradedAlgebraSheafMap X ψ hA hB).right =
      SheafOfModules.GradedAlgebra.ungradedCommSheafMap ψ hA hB :=
  rfl

/-- The algebra sheaf map of the identity is the identity. -/
theorem gradedAlgebraSheafMap_id :
    gradedAlgebraSheafMap X (SheafOfModules.GradedAlgebra.UnitalHom.id A) hA hA =
      𝟙 (gradedAlgebraSheaf X A hA) :=
  Under.UnderMorphism.ext (SheafOfModules.GradedAlgebra.ungradedCommSheafMap_id hA)

/-- The algebra sheaf map of a composite is the composite of the algebra sheaf maps. -/
theorem gradedAlgebraSheafMap_comp
    (hD : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (D.piece i).val.obj W)
      (b : (D.piece j).val.obj W), HEq ((D.mul i j).app W a b) ((D.mul j i).app W b a))
    (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (χ : SheafOfModules.GradedAlgebra.UnitalHom B D) :
    gradedAlgebraSheafMap X (ψ.comp χ) hA hD =
      gradedAlgebraSheafMap X ψ hA hB ≫ gradedAlgebraSheafMap X χ hB hD :=
  Under.UnderMorphism.ext
    (SheafOfModules.GradedAlgebra.ungradedCommSheafMap_comp hA hB hD ψ χ)

end Stacks.RelativeSpec

/-! ### `Sym` is functorial in the module -/

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) {F G H : SheafOfModules.{u} X.ringCatSheaf}

/-- The unital homomorphism of sheaves of graded algebras `Sym(ℱ) ⟶ Sym(𝒢)` induced by a
morphism `f : ℱ ⟶ 𝒢` of `𝒪_X`-modules: the unique one extending `f` followed by the degree-one
generator of `Sym(𝒢)`. -/
def symmetricAlgebraUnitalHom (f : F ⟶ G) :
    SheafOfModules.GradedAlgebra.UnitalHom (symmetricAlgebra X F) (symmetricAlgebra X G) :=
  SheafOfModules.GradedAlgebra.IsUniversal.descComp
    (isSymmetricAlgebra_symmetricAlgebra X F) f (symmetricAlgebraGen X G)
    (SheafOfModules.GradedAlgebra.pairwiseCommutes_comp f
      (isSymmetricAlgebra_symmetricAlgebra X G).1)

/-- The induced homomorphism extends `f`: in degree one it carries the generator of `Sym(ℱ)` to
the image under `f` of the generator of `Sym(𝒢)`. -/
theorem symmetricAlgebraGen_comp_symmetricAlgebraUnitalHom (f : F ⟶ G) :
    symmetricAlgebraGen X F ≫ (symmetricAlgebraUnitalHom X f).app 1 =
      f ≫ symmetricAlgebraGen X G :=
  SheafOfModules.GradedAlgebra.IsUniversal.descComp_extends
    (isSymmetricAlgebra_symmetricAlgebra X F) f (symmetricAlgebraGen X G) _

/-- The homomorphism induced by the identity is the identity. -/
theorem symmetricAlgebraUnitalHom_id :
    symmetricAlgebraUnitalHom X (𝟙 F) =
      SheafOfModules.GradedAlgebra.UnitalHom.id (symmetricAlgebra X F) :=
  SheafOfModules.GradedAlgebra.IsUniversal.descComp_id
    (isSymmetricAlgebra_symmetricAlgebra X F) _

/-- The homomorphism induced by a composite is the composite of the induced homomorphisms. -/
theorem symmetricAlgebraUnitalHom_comp (f : F ⟶ G) (g : G ⟶ H) :
    symmetricAlgebraUnitalHom X (f ≫ g) =
      (symmetricAlgebraUnitalHom X f).comp (symmetricAlgebraUnitalHom X g) :=
  SheafOfModules.GradedAlgebra.IsUniversal.descComp_comp
    (isSymmetricAlgebra_symmetricAlgebra X F) (isSymmetricAlgebra_symmetricAlgebra X G)
    f g (symmetricAlgebraGen X H) _ _ _

/-- **`Sym(f) : Sym(ℱ) ⟶ Sym(𝒢)`, the morphism of sheaves of commutative `𝒪_X`-algebras induced
by a morphism `f : ℱ ⟶ 𝒢` of `𝒪_X`-modules.** -/
@[ega "II 1.7.4" "special case"]
def symmetricAlgebraSheafMap (f : F ⟶ G) :
    symmetricAlgebraSheaf X F ⟶ symmetricAlgebraSheaf X G :=
  Stacks.RelativeSpec.gradedAlgebraSheafMap X (symmetricAlgebraUnitalHom X f)
    (symmetricAlgebra_mul_comm X F) (symmetricAlgebra_mul_comm X G)

/-- `Sym(f)` carries a homogeneous local section of `Sym(ℱ)` of degree `n` to its image under the
degree-`n` component of the induced homomorphism. -/
theorem symmetricAlgebraSheafMap_ungradedIncl (f : F ⟶ G) (W : X.Opensᵒᵖ) (n : ℤ)
    (x : ((symmetricAlgebra X F).piece n).val.obj W) :
    ((symmetricAlgebraSheafMap X f).right.hom.app W).hom
        ((symmetricAlgebra X F).ungradedIncl n x) =
      (symmetricAlgebra X G).ungradedIncl n
        (((symmetricAlgebraUnitalHom X f).app n).val.app W x) :=
  SheafOfModules.GradedAlgebra.ungradedIncl_ungradedSheafMap
    (symmetricAlgebraUnitalHom X f) n x

/-- `Sym` is functorial: the identity induces the identity. -/
theorem symmetricAlgebraSheafMap_id :
    symmetricAlgebraSheafMap X (𝟙 F) = 𝟙 (symmetricAlgebraSheaf X F) := by
  rw [symmetricAlgebraSheafMap, symmetricAlgebraUnitalHom_id]
  exact Stacks.RelativeSpec.gradedAlgebraSheafMap_id X (symmetricAlgebra X F)
    (symmetricAlgebra_mul_comm X F)

/-- `Sym` is functorial: a composite induces the composite. -/
theorem symmetricAlgebraSheafMap_comp (f : F ⟶ G) (g : G ⟶ H) :
    symmetricAlgebraSheafMap X (f ≫ g) =
      symmetricAlgebraSheafMap X f ≫ symmetricAlgebraSheafMap X g := by
  rw [symmetricAlgebraSheafMap, symmetricAlgebraUnitalHom_comp]
  exact Stacks.RelativeSpec.gradedAlgebraSheafMap_comp X (symmetricAlgebra X F)
    (symmetricAlgebra X G) (symmetricAlgebra X H) (symmetricAlgebra_mul_comm X F)
    (symmetricAlgebra_mul_comm X G) (symmetricAlgebra_mul_comm X H)
    (symmetricAlgebraUnitalHom X f) (symmetricAlgebraUnitalHom X g)

/-- **The symmetric algebra as a functor from `𝒪_X`-modules to sheaves of commutative
`𝒪_X`-algebras.** -/
@[ega "II 1.7.4" "special case"]
def symmetricAlgebraSheafFunctor :
    SheafOfModules.{u} X.ringCatSheaf ⥤ Stacks.RelativeSpec.AlgebraSheaf X where
  obj F := symmetricAlgebraSheaf X F
  map f := symmetricAlgebraSheafMap X f
  map_id _ := symmetricAlgebraSheafMap_id X
  map_comp f g := symmetricAlgebraSheafMap_comp X f g

/-! ### The vector bundle `𝐕(ℱ)` is functorial in the module -/

section VectorBundle

variable [F.IsQuasicoherent] [G.IsQuasicoherent] [H.IsQuasicoherent]

/-- The vector bundle `𝐕(ℱ)` together with its projection, as an object of the category of
schemes over `X`. -/
abbrev vectorBundleOver : Over X := Over.mk (vectorBundleToBase X F)

/-- The structure morphism of the vector bundle `𝐕(ℱ)`, as an object over `X`, is affine. -/
theorem isAffineHom_vectorBundleOver : IsAffineHom (vectorBundleOver X (F := F)).hom :=
  isAffineHom_vectorBundleToBase X F

/-- The comparison isomorphism `(𝐕(ℱ) ⟶ X)_* 𝒪 ≅ Sym(ℱ)`. -/
def vectorBundlePushforwardIso :
    pushforwardAlgebra (vectorBundleOver X (F := F)).hom ≅ symmetricAlgebraSheaf X F :=
  pushforwardAlgebraIso (symmetricAlgebraSheaf X F)

/-- `𝐕(f) : 𝐕(𝒢) ⟶ 𝐕(ℱ)`, the morphism of schemes over `X` induced by a morphism
`f : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules: the morphism classified by `Sym(f)` under the
universal property of the relative spectrum. -/
def vectorBundleMap (f : F ⟶ G) :
    vectorBundleOver X (F := G) ⟶ vectorBundleOver X (F := F) :=
  haveI := isAffineHom_vectorBundleOver X (F := F)
  (overHomEquivAlgebraHom (vectorBundleOver X (F := G)) (vectorBundleOver X (F := F))).symm
    ((vectorBundlePushforwardIso X (F := F)).hom ≫ symmetricAlgebraSheafMap X f ≫
      (vectorBundlePushforwardIso X (F := G)).inv)

/-- `𝐕(f)` is the morphism over `X` classified by `Sym(f)`: its canonical map on pushed-forward
structure sheaves is `Sym(f)`, read through the two comparison isomorphisms. -/
theorem pushforwardAlgebraMap_vectorBundleMap (f : F ⟶ G) :
    haveI := isAffineHom_vectorBundleOver X (F := F)
    pushforwardAlgebraMap (vectorBundleMap X f) =
      (vectorBundlePushforwardIso X (F := F)).hom ≫ symmetricAlgebraSheafMap X f ≫
        (vectorBundlePushforwardIso X (F := G)).inv :=
  have := isAffineHom_vectorBundleOver X (F := F)
  (overHomEquivAlgebraHom_apply (vectorBundleMap X f)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- `𝐕(f)` commutes with the projections `vectorBundleToBase` of the two vector bundles to `X`. -/
@[reassoc]
theorem vectorBundleMap_left_comp (f : F ⟶ G) :
    (vectorBundleMap X f).left ≫ vectorBundleToBase X F = vectorBundleToBase X G :=
  Over.w (vectorBundleMap X f)

/-- `𝐕` is functorial: the identity induces the identity. -/
theorem vectorBundleMap_id : vectorBundleMap X (𝟙 F) = 𝟙 (vectorBundleOver X (F := F)) := by
  have := isAffineHom_vectorBundleOver X (F := F)
  refine eq_of_pushforwardAlgebraMap_eq ?_
  rw [pushforwardAlgebraMap_vectorBundleMap, symmetricAlgebraSheafMap_id, Category.id_comp,
    Iso.hom_inv_id, pushforwardAlgebraMap_id]

/-- `𝐕` is functorial: a composite induces the composite, contravariantly. -/
theorem vectorBundleMap_comp (f : F ⟶ G) (g : G ⟶ H) :
    vectorBundleMap X (f ≫ g) = vectorBundleMap X g ≫ vectorBundleMap X f := by
  have := isAffineHom_vectorBundleOver X (F := F)
  have := isAffineHom_vectorBundleOver X (F := G)
  refine eq_of_pushforwardAlgebraMap_eq ?_
  rw [pushforwardAlgebraMap_vectorBundleMap, pushforwardAlgebraMap_comp,
    pushforwardAlgebraMap_vectorBundleMap, pushforwardAlgebraMap_vectorBundleMap,
    symmetricAlgebraSheafMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end VectorBundle

end AlgebraicGeometry.Scheme.Modules

end
