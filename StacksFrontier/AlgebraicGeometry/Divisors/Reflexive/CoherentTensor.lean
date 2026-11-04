module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.InternalHom

/-!
# The tensor product of coherent reflexive modules

Let `X` be an integral locally Noetherian scheme and `𝒞` the category of coherent reflexive
`𝒪_X`-modules.  The tensor product of `Coh(𝒪_X)` does not preserve reflexivity, so `𝒞` inherits
instead the *hull* tensor product

`ℱ ⊗_𝒞 𝒢 = (ℱ ⊗_{𝒪_X} 𝒢)^∨∨`,

the reflexive hull of the ordinary tensor product, which is coherent by [Stacks, Tag 01CE].  It
is symmetric and associative, and the internal Hom of `𝒞` is adjoint to it: for objects
`ℱ, 𝒢, ℋ` of `𝒞`,

`Hom_𝒞(ℱ ⊗_𝒞 𝒢, ℋ) = Hom_𝒞(ℱ, ℋom_{𝒪_X}(𝒢, ℋ))`.

## Main definitions

* `ordinaryTensor F G`: the ordinary tensor product `ℱ ⊗_{𝒪_X} 𝒢`, as a coherent module.
* `tensorObj F G`: the hull tensor product, as a coherent reflexive module.
* `tensorObjComm F G`: the symmetry isomorphism `ℱ ⊗_𝒞 𝒢 ≅ 𝒢 ⊗_𝒞 ℱ`.

## Main results

* `tensorHomEquiv F G H`: **the internal-Hom adjunction of `𝒞`**, with
  `tensorHomEquiv_apply` identifying its forward direction with the currying map of
  [Stacks, Tag 01CN] applied after the canonical map from the ordinary tensor product.
* `tensorSheafHomEquiv_natural_left`: naturality of Tag 01CN's currying bijection in the first
  tensor factor.
* `tensorProductBraiding_hom_comp`: the braiding of the ordinary tensor product is an
  involution, so `tensorObjComm` is one too.

## Implementation notes

`tensorObj F G` is literally `hullReflection X` applied to `ordinaryTensor F G`, so the
adjunction `hullReflectionAdjunction` applies to it with no transport, and
`tensorHomEquiv` is a composite of four bijections each of which is either that adjunction, a
full-subcategory hom bijection, or Tag 01CN.

The symmetry and associativity constraints of the *ordinary* tensor product of sheaves of
modules are `Stacks.SheafOfModules.Invertible.tensorProductBraiding` and
`Stacks.SheafOfModules.tensorSheafAssociator`; they are not rebuilt here.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive reflexiveHull toDoubleDual)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentModules CoherentReflexiveModules inclusion)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)

universe u

namespace AlgebraicGeometry.CoherentReflexive

attribute [local implicit_reducible] Scheme.Modules

/-! ### Naturality of the currying bijection in the first tensor factor -/

/-- Two morphisms into a sheaf Hom agree as soon as their evaluations at the terminal object of
every slice site agree. -/
theorem sheafHom_hom_ext (X : RingedSpace.{u, u})
    {A B H : SheafOfModules.{u} (structureSheafRing X)}
    (c d : A ⟶ Stacks.SheafOfModules.sheafHomSpace X B H)
    (h : ∀ (U : Opens X.carrier) (a : A.val.obj (op U)) (b : B.val.obj (op U)),
      ((c.val.app (op U) a).app (op (Over.mk (𝟙 U)))).hom b =
        ((d.val.app (op U) a).app (op (Over.mk (𝟙 U)))).hom b) : c = d := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  have hc := PresheafOfModules.naturality_apply c.val V.unop.hom.op a
  have hd := PresheafOfModules.naturality_apply d.val V.unop.hom.op a
  have hh := h V.unop.left (A.val.map V.unop.hom.op a) b
  rw [hc, hd] at hh
  exact hh

/-- **Naturality of the currying bijection of [Stacks, Tag 01CN] in the first tensor
factor.**  Currying a morphism out of `𝒜' ⊗ ℬ` after tensoring `f : 𝒜 ⟶ 𝒜'` with the identity
is currying followed by `f`. -/
theorem tensorSheafHomEquiv_natural_left (X : RingedSpace.{u, u})
    {A A' B H : SheafOfModules.{u} (structureSheafRing X)} (f : A ⟶ A')
    (g : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (A')).obj (B)) ⟶ H) :
    Stacks.SheafOfModules.tensorHomEquiv X A B H
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (X := (A, B)) (Y := (A', B))
          ((f, 𝟙 B) : (A, B) ⟶ (A', B))) ≫ g) =
      f ≫ Stacks.SheafOfModules.tensorHomEquiv X A' B H g := by
  apply sheafHom_hom_ext X (A := A) (B := B) (H := H)
  intro U a b
  have tensorSection :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
      X A B A' B f (𝟙 B) U a b
  have curryComposite := Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry
    X (F := A) (G := B) (H := H)
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩)).map (X := (A, B)) (Y := (A', B)) (f, 𝟙 B) ≫ g) U a b
  have curryTarget := Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry
    X (F := A') (G := B) (H := H) g U (f.val.app (op U) a) b
  exact curryComposite.trans
    ((congrArg (fun tensorElement => g.val.app (op U) tensorElement) tensorSection).trans
      curryTarget.symm)

/-! ### The hull tensor product -/

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The ordinary tensor product of two coherent reflexive modules, as a coherent module.  It is
coherent by [Stacks, Tag 01CE]. -/
noncomputable abbrev ordinaryTensor (F G : CoherentReflexiveModules X) : CoherentModules X :=
  ⟨(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F.obj.obj)).obj
        (G.obj.obj)),
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace F.obj.obj G.obj.obj
      F.obj.property G.obj.property⟩

/-- **Stacks Project, Tag 0EBH.**  The tensor product of the category of coherent reflexive
modules: the reflexive hull of the ordinary tensor product. -/
@[stacks 0EBH "tensor"]
noncomputable def tensorObj (F G : CoherentReflexiveModules X) : CoherentReflexiveModules X :=
  (hullReflection X).obj (ordinaryTensor F G)

/-- The underlying `𝒪_X`-module of the tensor product of `𝒞` is the double dual of the ordinary
tensor product. -/
theorem tensorObj_obj_obj (F G : CoherentReflexiveModules X) :
    (tensorObj F G).obj.obj = reflexiveHull
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F.obj.obj)).obj
          (G.obj.obj))) :=
  rfl

/-- **Stacks Project, Tag 0EBH.**  The tensor product of the category of coherent reflexive
modules is symmetric: the hull of the braiding of the ordinary tensor product. -/
@[stacks 0EBH "symmetry"]
noncomputable def tensorObjComm (F G : CoherentReflexiveModules X) :
    tensorObj F G ≅ tensorObj G F :=
  (hullReflection X).mapIso (ObjectProperty.isoMk _
    (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2
      F.obj.obj G.obj.obj))

/-- The braiding of the ordinary tensor product of sheaves of modules is an involution. -/
theorem tensorProductBraiding_hom_comp (Y : Scheme.{u})
    (A B : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf Y.ringCatSheaf.2)) :
    (Stacks.SheafOfModules.Invertible.tensorProductBraiding Y.presheaf Y.ringCatSheaf.2 A B).hom ≫
        (Stacks.SheafOfModules.Invertible.tensorProductBraiding Y.presheaf Y.ringCatSheaf.2
          B A).hom = 𝟙 _ := by
  let : MonoidalCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
        Y.ringCatSheaf.2).obj) :=
    PresheafOfModules.monoidalCategory (R := Y.presheaf)
  let : SymmetricCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
        Y.ringCatSheaf.2).obj) :=
    PresheafOfModules.symmetricCategory (R := Y.presheaf)
  show (Stacks.SheafOfModules.TensorSheafification.sheafify Y.presheaf Y.ringCatSheaf.2).map
        (β_ A.val B.val).hom ≫
      (Stacks.SheafOfModules.TensorSheafification.sheafify Y.presheaf Y.ringCatSheaf.2).map
        (β_ B.val A.val).hom = _
  rw [← CategoryTheory.Functor.map_comp, SymmetricCategory.symmetry,
    CategoryTheory.Functor.map_id]
  rfl

/-- **Stacks Project, Tag 0EBH.**  The internal-Hom adjunction of the category of coherent
reflexive modules: morphisms out of the hull tensor product `ℱ ⊗_𝒞 𝒢` are morphisms of `ℱ` into
the internal Hom `ℋom_{𝒪_X}(𝒢, ℋ)`. -/
@[stacks 0EBH "internal_hom"]
noncomputable def tensorHomEquiv (F G H : CoherentReflexiveModules X) :
    (tensorObj F G ⟶ H) ≃ (F ⟶ internalHomObj G H) :=
  ((hullReflectionAdjunction X).homEquiv (ordinaryTensor F G) H).trans
    ((homEquivCoh (ordinaryTensor F G) H).trans
      ((Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace F.obj.obj G.obj.obj
        H.obj.obj).trans (homEquiv₂ F (internalHomObj G H)).symm))

/-- **Stacks Project, Tag 0EBH.**  The adjunction bijection is the currying map of
[Stacks, Tag 01CN], applied after restricting along the canonical map from the ordinary tensor
product to its double dual.  This pins the bijection down. -/
@[stacks 0EBH "internal_hom"]
theorem tensorHomEquiv_apply (F G H : CoherentReflexiveModules X)
    (f : tensorObj F G ⟶ H) :
    (tensorHomEquiv F G H f).hom.hom =
      Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace F.obj.obj G.obj.obj H.obj.obj
        (toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F.obj.obj)).obj
            (G.obj.obj))) ≫ f.hom.hom) :=
  congrArg (Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace F.obj.obj G.obj.obj H.obj.obj)
    (hullReflectionAdjunction_homEquiv_apply X (ordinaryTensor F G) H f)

end AlgebraicGeometry.CoherentReflexive

end
