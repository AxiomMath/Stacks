module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor

/-!
# Tensoring with the structure sheaf, and multiplication by a global section

Let `O` be a sheaf of commutative rings on a site and let `G` be a sheaf of `O`-modules. This
file proves the two facts about the endofunctor
`- ⊗_O G = (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G` that a base change of a
system of modules needs: that it carries the rank-one module `O` to `G`, and that it commutes
with multiplication by a compatible family of local sections of `O`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.sheafTensorRightUnitIso`: **`O ⊗_O G ≅ G`**.

## Main results

* `AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd`: **tensoring
  commutes with multiplication by a global section**, that is, `- ⊗_O G` carries the
  endomorphism `a ·` of a sheaf of modules to the endomorphism `a ·` of its tensor product
  with `G`.
* `AlgebraicGeometry.SheafOfModules.globalSectionToEnd_app_sheafTensorRight_eq_zero`: **a global
  section killing a sheaf of modules kills its tensor product with `G`.**

## Implementation notes

`(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G` is the composite of the forgetful
functor to presheaves of modules, the objectwise tensor product
`PresheafOfModules.tensorObj` with `G`, and sheafification over `O`, so both statements are
proved by descending to presheaves.

For the first that is all there is to it: the objectwise tensor product with the unit presheaf
is the left unitor of the monoidal structure
`AlgebraicGeometry.SheafOfModules.monoidalCategoryAssociatedRing` on presheaves of modules, and
the sheafification of the presheaf underlying a sheaf is that sheaf, which is the counit of
`PresheafOfModules.sheafificationAdjunction` at it.

For the second, both sides are morphisms out of a sheafification, so they agree as soon as their
adjoint transposes do, and the transpose of a morphism is its composite with the unit of that
adjunction. Against the unit the left-hand side is the objectwise statement
`(a · x) ⊗ y = a · (x ⊗ y)` — `TensorProduct.smul_tmul'` — and the right-hand side is the
`O`-linearity of the unit. Multiplication by a family of local sections is
`Stacks.SheafOfModules.globalSectionToEnd`, an endomorphism of the *identity* functor of
`Mod(O)`, so no naturality square has to be checked for it: the two statements here are exactly
the two places where that endomorphism meets a functor that is not the identity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u w

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w}) (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- **`O ⊗_O G ≅ G`**: tensoring with the rank-one module `O` changes nothing.

Objectwise this is the left unitor of the monoidal structure on presheaves of modules, and what
remains after sheafifying it is that the sheafification of the presheaf underlying `G` is `G`. -/
def sheafTensorRightUnitIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ≅ G :=
  ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).mapIso (λ_ G.val)).trans
    ((asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).counit)).app G)

section Smul

variable [∀ U, IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U)]

open scoped IsMulCommutative

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Tensoring commutes with multiplication by a global section.** -/
theorem sheafTensorRight_map_globalSectionToEnd
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⋙ forget RingCat.{w}).sections)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).map
          ((Stacks.SheafOfModules.globalSectionToEnd
            (Stacks.SheafOfModules.Tensor.ringSheaf O) a).asHom.app M) =
      (Stacks.SheafOfModules.globalSectionToEnd
        (Stacks.SheafOfModules.Tensor.ringSheaf O) a).asHom.app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).obj M) := by
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).homEquiv _ _).injective ?_
  refine (Adjunction.homEquiv_unit _ _ _ _).trans
    (Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm)
  refine (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.naturality
    (((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O.obj).flip.obj G.val).map
      ((Stacks.SheafOfModules.globalSectionToEnd
        (Stacks.SheafOfModules.Tensor.ringSheaf O) a).asHom.app M).val)).symm).trans ?_
  refine PresheafOfModules.hom_ext fun U => ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
  exact (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O.obj).flip.obj G.val).obj
          M.val)).app U).hom.map_smul
    (a.val U) (x ⊗ₜ[(ringPresheaf O.obj).obj U] y)

/-- **A global section killing a sheaf of modules kills its tensor product with anything.**
Multiplication by `a` is an endomorphism of the *identity* functor, so `- ⊗_O G` carries its
value at `M` to its value at `M ⊗_O G`; if the former is zero then so is the latter, because
tensoring preserves zero morphisms.

Mathematically this is the statement that the module structure of `M ⊗_O G` is the one of its
first factor, which is why an annihilator of `M` annihilates `M ⊗_O G`. It is the step by which
the annihilation of the cohomology sheaves of a derived pullback, [Stacks, Tag 0GA0], is carried
across a twist in the proof of [Stacks, Tag 0GA1]. -/
theorem globalSectionToEnd_app_sheafTensorRight_eq_zero
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⋙ forget RingCat.{w}).sections)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hM : (Stacks.SheafOfModules.globalSectionToEnd
      (Stacks.SheafOfModules.Tensor.ringSheaf O) a).asHom.app M = 0) :
    (Stacks.SheafOfModules.globalSectionToEnd
      (Stacks.SheafOfModules.Tensor.ringSheaf O) a).asHom.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).obj M) = 0 := by
  let :=
    Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesZeroMorphisms J O G
  rw [← sheafTensorRight_map_globalSectionToEnd O G a M, hM, Functor.map_zero]

end Smul

end AlgebraicGeometry.SheafOfModules

end
