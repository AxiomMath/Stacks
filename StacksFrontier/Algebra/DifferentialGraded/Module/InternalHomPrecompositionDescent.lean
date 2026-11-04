module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecompositionFunctor
public import StacksCore.Tactic.StacksAttribute

/-! # Precomposition on the internal hom, read on differential graded modules

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let
`f : M ⟶ N` be a homomorphism of differential graded `(A, B)`-bimodules. Precomposition with `f`
is a natural transformation of the internal hom functors on the *homotopy* categories
(`DifferentialGraded.Bimodule.precompHomotopyNatTrans`), but that transformation is defined
through the inverse of `DifferentialGradedModule.homotopyCategoryEquivalence`, which is built by
choice and is therefore opaque. This file produces the transformation of the internal hom
functors on the categories of differential graded modules themselves, and identifies the two
through the descent isomorphism `DifferentialGradedModule.homHomotopyDescent`.

That identification is what lets a naturality statement about the internal hom functor on
`K(B, d)` — Tag 09LC or Tag 0FQR, read as a statement about the bimodule variable — be checked on
differential graded modules, where precomposition is given by an explicit formula.

## Main definitions

* `DifferentialGraded.Bimodule.precompModuleNatTrans`: precomposition as a natural transformation
  of the internal hom functors on differential graded modules.

## Main results

* `DifferentialGraded.Bimodule.precompModuleNatTrans_homogeneousEquiv`: the homogeneous map
  attached to the image of a homogeneous element is the composite with `f` of the one attached to
  the element. This is the only computation the two naturality statements need.
* `DifferentialGraded.Bimodule.homHomotopyDescent_precompHomotopyNatTrans`: the descent
  isomorphism identifies precomposition on the homotopy categories with precomposition on
  differential graded modules.

## Implementation notes

*Why the transformation is produced by whiskering rather than by proving naturality.* The
internal hom functor on differential graded modules is the differential graded functor's action
on the category of complexes, conjugated by `DifferentialGradedModule.dgCategoryCompEquivalence`
(`DifferentialGradedModule.homModuleFunctor`), and `DifferentialGraded.Bimodule.precompDGNatTrans`
is already a transformation of differential graded functors. Whiskering the latter's action on
complexes therefore gives the transformation outright, with no naturality square to check, and its
component is `DifferentialGraded.Bimodule.precompModuleHom` on the nose — the equivalence is the
identity on objects and does not change the underlying linear map of a morphism.

*Why the component has to be spelled as a component.* The value of the internal hom functor at
`P` is equal to the chosen presentation of `Hom^•_B(N, P)` only by unfolding at default
transparency, so a goal in which `DifferentialGraded.Bimodule.precompModuleHom f P` appears in
place of `(precompModuleNatTrans f).app P` is not type-correct at `implicit` transparency and no
rewrite fires in it. Every statement below is therefore phrased with the component.

*How the descent identification is proved.* The functor of
`DifferentialGradedModule.homotopyCategoryEquivalence` is transparent — it is the identity on
objects and sends the homotopy class of a homomorphism to the class of the associated cocycle — so
applying it to the component of `precompHomotopyNatTrans` gives the component of
`precompDGNatTrans` on the nose. The descent isomorphism is a
`CategoryTheory.Functor.fullyFaithfulCancelRight` of the counit, so after applying
`CategoryTheory.Functor.map_injective` and `CategoryTheory.Functor.map_preimage` the square is
exactly the naturality of the counit.

## References

* [Stacks Project, Tag 0BYV](https://stacks.math.columbia.edu/tag/0BYV); the internal hom functor
  is [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ) and the homotopy category is
  [Tag 09JQ](https://stacks.math.columbia.edu/tag/09JQ).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R} {M N : Bimodule A B}

/-- Precomposition with a homomorphism of differential graded `(A, B)`-bimodules, as a natural
transformation of the internal hom functors of Tag 0FQQ on the categories of differential graded
modules. -/
def precompModuleNatTrans (f : M ⟶ N) :
    homModuleFunctor A B N.rightModule N.leftAction ⟶
      homModuleFunctor A B M.rightModule M.leftAction :=
  Functor.whiskerLeft (dgCategoryCompEquivalence B).1.inverse
    (Functor.whiskerRight (precompDGNatTrans f).onComp (dgCategoryCompEquivalence A).1.functor)

/-- The component of the transformation is precomposition itself: the equivalence with the
category of complexes does not change the underlying linear map of a morphism. -/
theorem precompModuleNatTrans_app (f : M ⟶ N) (P : DifferentialGradedModule B) :
    (precompModuleNatTrans f).app P = precompModuleHom f P :=
  rfl

/-- **The homogeneous map attached to the image of a homogeneous element under precomposition.**
It is the homogeneous map attached to the element, composed with `f`. -/
theorem precompModuleNatTrans_homogeneousEquiv (f : M ⟶ N) (P : DifferentialGradedModule B)
    (n : ℤ) (v : ((homModuleFunctor A B N.rightModule N.leftAction).obj P).grading n) :
    (homPresentation M P).homogeneousEquiv n
        (((precompModuleNatTrans f).app P).gradedMap n v) =
      homogeneousMapComp B (add_zero n) ((homPresentation N P).homogeneousEquiv n v)
        (cocycleOfHom B f.rightHom).1 := by
  rw [show ((precompModuleNatTrans f).app P).gradedMap n v =
      precompGraded f (homPresentation N P) (homPresentation M P) n v from
    Subtype.ext (precompModuleHom_apply_grading f P n v)]
  exact homogeneousEquiv_precompGraded f (homPresentation N P) (homPresentation M P) n v

/-- **The value of the homogeneous map attached to the image of a homogeneous element under
precomposition.** -/
theorem precompModuleNatTrans_homogeneousEquiv_apply (f : M ⟶ N) (P : DifferentialGradedModule B)
    (n : ℤ) (v : ((homModuleFunctor A B N.rightModule N.leftAction).obj P).grading n)
    (z : M.rightModule.M) :
    (((homPresentation M P).homogeneousEquiv n
        (((precompModuleNatTrans f).app P).gradedMap n v)).1 z : P.M) =
      ((homPresentation N P).homogeneousEquiv n v).1 (f.rightHom.toFun z) := by
  rw [precompModuleNatTrans_homogeneousEquiv]
  rfl

/-- The functor of the canonical equivalence `K(A, d) ≌ K(dgCategory A)` carries the homotopy
class of the component of `DifferentialGraded.Bimodule.precompModuleNatTrans` to the component of
the differential graded precomposition transformation: both are the class of the cocycle attached
to precomposition with `f`. -/
theorem homotopyCategoryEquivalence_functor_map_precompModuleNatTrans (f : M ⟶ N)
    (P : DifferentialGradedModule B) :
    (homotopyCategoryEquivalence A).functor.map
        ((toHomotopyCategory A).map ((precompModuleNatTrans f).app P)) =
      (precompDGNatTrans f).onK.app
        ((homotopyCategoryEquivalence B).functor.obj ((toHomotopyCategory B).obj P)) :=
  rfl

/-- **Precomposition on the homotopy categories is the descent of precomposition on differential
graded modules.** The descent isomorphism of Tag 0FQQ
(`DifferentialGradedModule.homHomotopyDescent`) carries
`DifferentialGraded.Bimodule.precompHomotopyNatTrans` to
`DifferentialGraded.Bimodule.precompModuleNatTrans`. -/
theorem homHomotopyDescent_precompHomotopyNatTrans (f : M ⟶ N) (P : DifferentialGradedModule B) :
    (precompHomotopyNatTrans f).app ((toHomotopyCategory B).obj P) ≫
        (homHomotopyDescent M.rightModule M.leftAction).hom.app P =
      (homHomotopyDescent N.rightModule N.leftAction).hom.app P ≫
        (toHomotopyCategory A).map ((precompModuleNatTrans f).app P) := by
  apply (homotopyCategoryEquivalence A).functor.map_injective
  rw [Functor.map_comp, Functor.map_comp, homHomotopyDescent, homHomotopyDescent,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, Functor.map_preimage,
    homotopyCategoryEquivalence_functor_map_precompModuleNatTrans]
  exact (homotopyCategoryEquivalence A).counitIso.hom.naturality _

/-- `DifferentialGraded.Bimodule.homHomotopyDescent_precompHomotopyNatTrans` read through the
inverse of the descent isomorphism. -/
theorem homHomotopyDescent_inv_precompHomotopyNatTrans (f : M ⟶ N)
    (P : DifferentialGradedModule B) :
    (toHomotopyCategory A).map ((precompModuleNatTrans f).app P) ≫
        (homHomotopyDescent M.rightModule M.leftAction).inv.app P =
      (homHomotopyDescent N.rightModule N.leftAction).inv.app P ≫
        (precompHomotopyNatTrans f).app ((toHomotopyCategory B).obj P) := by
  rw [← cancel_epi ((homHomotopyDescent N.rightModule N.leftAction).hom.app P),
    ← Category.assoc, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
    ← homHomotopyDescent_precompHomotopyNatTrans, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

end DifferentialGraded.Bimodule

end
