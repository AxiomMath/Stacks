module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction

/-! # A homomorphism of bimodules induces a transformation of derived tensor functors

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let
`f : N ⟶ N'` be a homomorphism of differential graded `(A, B)`-bimodules. Tensoring with `f` on
the right of a right differential graded `A`-module is a homomorphism `M ⊗_A N ⟶ M ⊗_A N'`,
natural in `M`, and it descends to the homotopy categories and then along the localization to a
morphism of functors `1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'` on `D(A, d)`. This is the first assertion
of Stacks Tag 09S3.

## Main definitions

* `DifferentialGraded.Bimodule.tensorHomOfBimoduleHom`: the homomorphism `M ⊗_A N ⟶ M ⊗_A N'`.
* `DifferentialGraded.Bimodule.tensorModuleNatTrans`: it as a transformation of the functors of
  Tag 09LM on differential graded modules.
* `DifferentialGraded.Bimodule.tensorHomotopyNatTrans` and
  `DifferentialGraded.Bimodule.ordinaryTensorNatTrans`: the same on the homotopy categories, and
  with the target localized.
* `DifferentialGraded.Bimodule.derivedTensorNatTrans`: `1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'`.

## Main results

* `DifferentialGraded.Bimodule.derivedTensorNatTrans_counit`: `1 ⊗ f` is compatible with the
  comparisons of Tag 09LS from the derived to the plain tensor product; this identity determines
  it.
* `DifferentialGraded.Bimodule.derivedTensorNatTrans_id` and
  `DifferentialGraded.Bimodule.derivedTensorNatTrans_comp`: functoriality in the bimodule.
* `DifferentialGraded.Bimodule.derivedTensorNatTrans_app_comp_counit`: the component of `1 ⊗ f`
  at the image of a differential graded module, modulo the two comparisons, is the ordinary map
  `M ⊗_A N ⟶ M ⊗_A N'`.
* `DifferentialGraded.Bimodule.isIso_derivedTensorNatTrans_of_propertyP`: `1 ⊗ f` is an
  isomorphism of functors as soon as the ordinary map is one at every module with property (P).

## Implementation notes

*What is proved here and what is not.* Tag 09S3 has two assertions: that `f` induces `1 ⊗ f`,
and that `1 ⊗ f` is an isomorphism of functors when `f` is a quasi-isomorphism. Only the first
is proved here, so the tag below is part-qualified. One route to the second asks for the
statement that for a differential graded `A`-module `P` with property (P) the ordinary map
`P ⊗_A N ⟶ P ⊗_A N'` is a quasi-isomorphism — the source proves it by filtering `P` and reducing
to `P = A[k]` — which is not available here;
`DifferentialGraded.Bimodule.isIso_derivedTensorNatTrans_of_propertyP` records the reduction of
the second assertion to exactly that statement. The second assertion itself is proved, by the
dévissage of Tag 0FQE in the derived category rather than by that reduction, as
`DifferentialGraded.Bimodule.quasiIsoInvertsDerivedTensor` in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensorQuasiIsoDevissage.lean`, which is
downstream of this file.

*The tensor product is characterized, not named, so every map out of it is a lift.* The value
`M ⊗_A N` is given by `DifferentialGraded.Bimodule.TensorDGFunctorData`, whose `universal` field
characterizes it by homomorphisms of differential graded modules out of it. The map `1 ⊗ f` on
`M ⊗_A N` is accordingly the lift of the balanced bilinear map `(x, y) ↦ x ⊗ f(y)`, and every
identity it satisfies — naturality in `M`, and functoriality in `f` — is proved by
`DifferentialGraded.Bimodule.tensorObj_hom_ext'`, the uniqueness half of that property: two
homomorphisms out of `M ⊗_A N` agreeing on pure tensors are equal.

*Why naturality is only checked in degree zero.* `DGCategory.DGNatTrans` would ask for strict
naturality against homogeneous morphisms of *every* degree, which the universal property cannot
supply: it characterizes `M ⊗_A N` by closed maps of degree zero only. The transformation is
therefore built on the category of differential graded modules, where the morphisms are exactly
those maps, and transported to the homotopy categories by
`CategoryTheory.Quotient.natTransLift` against the compatibility of Tag 09LM with the quotient.

*The descent to `D(A, d)` is the universal property of the derived functor.* `- ⊗_A^𝐋 N` is a
right Kan extension along the localization, so a transformation out of it into any functor is
determined by its composite with the comparison; `CategoryTheory.Functor.leftDerivedNatTrans`
is that construction, and `derivedTensorNatTrans_counit` is its defining identity.

*Universes.* As in `StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleTensor.lean`, the base
ring, the algebras and the modules all live in a single universe `u`; the narrowing comes down
the chain from `DifferentialGraded.Bimodule.TensorDGFunctorData` and is not decided here.

## References

* [Stacks Project, Tag 09S3](https://stacks.math.columbia.edu/tag/09S3); the functor being
  transformed is [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS), built on
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-! ### The map on the relative tensor products -/

/-- The universal pure tensor of `M ⊗_A N'`, read through `f` as a balanced bilinear map out of
`M` and `N`: it sends `(x, y)` to the pure tensor `x ⊗ f(y)`. -/
private def tensorBilinearOfHom {N N' : Bimodule A B} (f : N ⟶ N')
    (M : DifferentialGradedModule A) :
    BalancedBilinearMap M N ((tensorDGFunctor N').functor.obj M) where
  toLinearMap := ((tensorDGFunctor N').pure M).toLinearMap.compl₂ f.rightHom.toFun
  map_grading p q x y :=
    ((tensorDGFunctor N').pure M).map_grading p q x (f.rightHom.gradedMap q y)
  map_d p x y := by
    have hd : f.rightHom.toFun (N.rightModule.d y) = N'.rightModule.d (f.rightHom.toFun y) :=
      LinearMap.congr_fun f.rightHom.map_d y
    change ((tensorDGFunctor N').functor.obj M).d
        (((tensorDGFunctor N').pure M).toLinearMap x (f.rightHom.toFun y)) = _
    rw [((tensorDGFunctor N').pure M).map_d p x (f.rightHom.toFun y)]
    change _ = ((tensorDGFunctor N').pure M).toLinearMap (M.d x) (f.rightHom.toFun y) +
      (p.negOnePow : ℤ) • ((tensorDGFunctor N').pure M).toLinearMap x
        (f.rightHom.toFun (N.rightModule.d y))
    rw [hd]
  balance p q n x y a := by
    have h := ((tensorDGFunctor N').pure M).balance p q n x (f.rightHom.gradedMap q y) a
    change ((tensorDGFunctor N').pure M).toLinearMap
        (MulOpposite.op (a : A.A) • (x : M.M)) (f.rightHom.toFun (y : N.rightModule.M)) = _
    change _ = ((tensorDGFunctor N').pure M).toLinearMap x
      (f.rightHom.toFun ((show N.rightModule.grading (q + n) from
        (N.leftAction.1.action n a).v q (q + n) (by omega) y) : N.rightModule.M))
    rw [f.map_left n q a y]
    exact h
  map_right x y b := by
    change ((tensorDGFunctor N').pure M).toLinearMap x
      (f.rightHom.toFun (MulOpposite.op b • y)) = _
    rw [f.rightHom.map_smul y b]
    exact ((tensorDGFunctor N').pure M).map_right x (f.rightHom.toFun y) b

/-- **Tensoring with a homomorphism of bimodules.** The homomorphism
`1 ⊗ f : M ⊗_A N ⟶ M ⊗_A N'` of right differential graded `B`-modules attached to a homomorphism
`f : N ⟶ N'` of differential graded `(A, B)`-bimodules; on pure tensors it is `x ⊗ y ↦ x ⊗ f(y)`,
which determines it. -/
@[no_expose]
def tensorHomOfBimoduleHom {N N' : Bimodule A B} (f : N ⟶ N')
    (M : DifferentialGradedModule A) :
    DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M)
      ((tensorDGFunctor N').functor.obj M) :=
  ((tensorDGFunctor N).universal M ((tensorDGFunctor N').functor.obj M)
    (tensorBilinearOfHom f M)).choose

/-- `1 ⊗ f` sends the pure tensor `x ⊗ y` to the pure tensor `x ⊗ f(y)`. -/
theorem tensorHomOfBimoduleHom_pure {N N' : Bimodule A B} (f : N ⟶ N')
    (M : DifferentialGradedModule A) (x : M.M) (y : N.rightModule.M) :
    (tensorHomOfBimoduleHom f M).toFun (((tensorDGFunctor N).pure M).toLinearMap x y) =
      ((tensorDGFunctor N').pure M).toLinearMap x (f.rightHom.toFun y) :=
  ((tensorDGFunctor N).universal M ((tensorDGFunctor N').functor.obj M)
    (tensorBilinearOfHom f M)).choose_spec.1 x y

/-- Tensoring with the identity of a bimodule is the identity. -/
theorem tensorHomOfBimoduleHom_id (N : Bimodule A B) (M : DifferentialGradedModule A) :
    tensorHomOfBimoduleHom (𝟙 N) M =
      DifferentialGradedModule.Hom.id ((tensorDGFunctor N).functor.obj M) :=
  tensorObj_hom_ext' N M _ _ fun x y => by
    rw [tensorHomOfBimoduleHom_pure]; rfl

/-- Tensoring with a composite of homomorphisms of bimodules is the composite. -/
theorem tensorHomOfBimoduleHom_comp {N N' N'' : Bimodule A B} (f : N ⟶ N') (g : N' ⟶ N'')
    (M : DifferentialGradedModule A) :
    tensorHomOfBimoduleHom (f ≫ g) M =
      DifferentialGradedModule.Hom.comp (tensorHomOfBimoduleHom g M)
        (tensorHomOfBimoduleHom f M) :=
  tensorObj_hom_ext' N M _ _ fun x y => by
    show _ = (tensorHomOfBimoduleHom g M).toFun
      ((tensorHomOfBimoduleHom f M).toFun (((tensorDGFunctor N).pure M).toLinearMap x y))
    rw [tensorHomOfBimoduleHom_pure, tensorHomOfBimoduleHom_pure, tensorHomOfBimoduleHom_pure]
    rfl

/-! ### The transformation on differential graded modules -/

/-- **Stacks 09S3, on the categories of differential graded modules.** `1 ⊗ f` as a natural
transformation `- ⊗_A N ⟶ - ⊗_A N'` of the functors of Tag 09LM. Naturality is the equality of
two homomorphisms out of a tensor product, so it is checked on pure tensors, where both sides
send `x ⊗ y` to `g(x) ⊗ f(y)`. -/
def tensorModuleNatTrans {N N' : Bimodule A B} (f : N ⟶ N') :
    tensorCompFunctor N ⟶ tensorCompFunctor N' where
  app M := tensorHomOfBimoduleHom f M
  naturality L M g := by
    refine tensorObj_hom_ext' N L _ _ fun x y => ?_
    change (tensorHomOfBimoduleHom f M).toFun
        (((tensorCompFunctor N).map g).toFun (((tensorDGFunctor N).pure L).toLinearMap x y)) =
      ((tensorCompFunctor N').map g).toFun
        ((tensorHomOfBimoduleHom f L).toFun (((tensorDGFunctor N).pure L).toLinearMap x y))
    rw [tensorCompFunctor_map_pure', tensorHomOfBimoduleHom_pure, tensorHomOfBimoduleHom_pure,
      tensorCompFunctor_map_pure']

/-- The component of `tensorModuleNatTrans f` at `M` is `tensorHomOfBimoduleHom f M`, the map
`M ⊗_A N ⟶ M ⊗_A N'` sending `x ⊗ y` to `x ⊗ f(y)`. -/
@[simp] theorem tensorModuleNatTrans_app {N N' : Bimodule A B} (f : N ⟶ N')
    (M : DifferentialGradedModule A) :
    (tensorModuleNatTrans f).app M = tensorHomOfBimoduleHom f M := rfl

/-- The transformation of Tag 09LM attached to the identity is the identity. -/
@[simp] theorem tensorModuleNatTrans_id (N : Bimodule A B) :
    tensorModuleNatTrans (𝟙 N) = 𝟙 (tensorCompFunctor N) :=
  NatTrans.ext (funext fun M => tensorHomOfBimoduleHom_id N M)

/-- The transformation of Tag 09LM is functorial in the bimodule. -/
@[simp] theorem tensorModuleNatTrans_comp {N N' N'' : Bimodule A B} (f : N ⟶ N') (g : N' ⟶ N'') :
    tensorModuleNatTrans (f ≫ g) = tensorModuleNatTrans f ≫ tensorModuleNatTrans g :=
  NatTrans.ext (funext fun M => tensorHomOfBimoduleHom_comp f g M)

/-! ### The transformation on the homotopy categories -/

/-- `1 ⊗ f` on the homotopy categories, before descending along the quotient: the transformation
of Tag 09LM read through the compatibility of Tag 09LM with the passage to homotopy classes. -/
private def tensorHomotopyNatTransAux {N N' : Bimodule A B} (f : N ⟶ N') :
    toHomotopyCategory A ⋙ tensorHomotopyFunctor N ⟶
      toHomotopyCategory A ⋙ tensorHomotopyFunctor N' :=
  (tensorCompFunctor_quotient N).inv ≫
    Functor.whiskerRight (tensorModuleNatTrans f) (toHomotopyCategory B) ≫
      (tensorCompFunctor_quotient N').hom

private theorem tensorHomotopyNatTransAux_id (N : Bimodule A B) :
    tensorHomotopyNatTransAux (𝟙 N) = 𝟙 _ := by
  rw [tensorHomotopyNatTransAux, tensorModuleNatTrans_id, Functor.whiskerRight_id',
    Category.id_comp, Iso.inv_hom_id]

private theorem tensorHomotopyNatTransAux_comp {N N' N'' : Bimodule A B} (f : N ⟶ N')
    (g : N' ⟶ N'') :
    tensorHomotopyNatTransAux (f ≫ g) =
      tensorHomotopyNatTransAux f ≫ tensorHomotopyNatTransAux g := by
  rw [tensorHomotopyNatTransAux, tensorHomotopyNatTransAux, tensorHomotopyNatTransAux,
    tensorModuleNatTrans_comp, Functor.whiskerRight_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **Stacks 09S3, on the homotopy categories.** `1 ⊗ f` as a natural transformation
`- ⊗_A N ⟶ - ⊗_A N'` of the functors `K(A, d) ⥤ K(B, d)` of Tag 09LM. It is the descent of
`DifferentialGraded.Bimodule.tensorModuleNatTrans` along the quotient by homotopy, which is
available because `K(A, d)` is that quotient. -/
@[no_expose]
def tensorHomotopyNatTrans {N N' : Bimodule A B} (f : N ⟶ N') :
    tensorHomotopyFunctor N ⟶ tensorHomotopyFunctor N' :=
  CategoryTheory.Quotient.natTransLift (homotopyRel A) (tensorHomotopyNatTransAux f)

/-- The component of `1 ⊗ f` at the class of a differential graded module, through the
compatibility of Tag 09LM with the quotient. -/
theorem tensorHomotopyNatTrans_app {N N' : Bimodule A B} (f : N ⟶ N')
    (M : DifferentialGradedModule A) :
    (tensorHomotopyNatTrans f).app ((toHomotopyCategory A).obj M) =
      (tensorCompFunctor_quotient N).inv.app M ≫
        (toHomotopyCategory B).map ((tensorModuleNatTrans f).app M) ≫
          (tensorCompFunctor_quotient N').hom.app M := by
  show (tensorHomotopyNatTransAux f).app M = _
  rfl

/-- `1 ⊗ f` on the homotopy categories is the identity for the identity of a bimodule. -/
@[simp] theorem tensorHomotopyNatTrans_id (N : Bimodule A B) :
    tensorHomotopyNatTrans (𝟙 N) = 𝟙 (tensorHomotopyFunctor N) := by
  rw [tensorHomotopyNatTrans, tensorHomotopyNatTransAux_id,
    CategoryTheory.Quotient.natTransLift_id]

/-- `1 ⊗ f` on the homotopy categories is functorial in the bimodule. -/
@[simp] theorem tensorHomotopyNatTrans_comp {N N' N'' : Bimodule A B} (f : N ⟶ N')
    (g : N' ⟶ N'') :
    tensorHomotopyNatTrans (f ≫ g) = tensorHomotopyNatTrans f ≫ tensorHomotopyNatTrans g := by
  rw [tensorHomotopyNatTrans, tensorHomotopyNatTransAux_comp, tensorHomotopyNatTrans,
    tensorHomotopyNatTrans, CategoryTheory.Quotient.comp_natTransLift]

/-- `1 ⊗ f` between the functors `K(A, d) ⥤ D(B, d)` that Tag 09LS derives: the transformation on
the homotopy categories, with the target localized at the quasi-isomorphisms. -/
def ordinaryTensorNatTrans {N N' : Bimodule A B} (f : N ⟶ N') :
    tensorFunctorToDerivedCategory N ⟶ tensorFunctorToDerivedCategory N' :=
  Functor.whiskerRight (tensorHomotopyNatTrans f) (quasiIsomorphisms' B).Q

/-- The component of `1 ⊗ f` with localized target is the image under the localization of its
component on the homotopy categories. -/
theorem ordinaryTensorNatTrans_app {N N' : Bimodule A B} (f : N ⟶ N') (X : HomotopyCategory A) :
    (ordinaryTensorNatTrans f).app X =
      (quasiIsomorphisms' B).Q.map ((tensorHomotopyNatTrans f).app X) := rfl

/-- `1 ⊗ f` with localized target is the identity when `f` is the identity of a bimodule. -/
@[simp] theorem ordinaryTensorNatTrans_id (N : Bimodule A B) :
    ordinaryTensorNatTrans (𝟙 N) = 𝟙 (tensorFunctorToDerivedCategory N) := by
  rw [ordinaryTensorNatTrans, tensorHomotopyNatTrans_id, Functor.whiskerRight_id']

/-- `1 ⊗ f` with localized target sends a composite of homomorphisms of bimodules to the
composite of the transformations. -/
@[simp] theorem ordinaryTensorNatTrans_comp {N N' N'' : Bimodule A B} (f : N ⟶ N')
    (g : N' ⟶ N'') :
    ordinaryTensorNatTrans (f ≫ g) = ordinaryTensorNatTrans f ≫ ordinaryTensorNatTrans g := by
  rw [ordinaryTensorNatTrans, tensorHomotopyNatTrans_comp, Functor.whiskerRight_comp,
    ordinaryTensorNatTrans, ordinaryTensorNatTrans]

/-! ### The transformation of the derived tensor functors -/

/-- **Stacks 09S3**, the morphism of functors. A homomorphism `f : N ⟶ N'` of differential graded
`(A, B)`-bimodules induces `1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'`, a natural transformation of the
derived tensor functors of Tag 09LS on `D(A, d)`.

It is the descent of `DifferentialGraded.Bimodule.ordinaryTensorNatTrans` along the localization:
`- ⊗_A^𝐋 N'` is a right Kan extension of ordinary tensoring with `N'`, so the transformation is
the unique one compatible with the two comparisons of Tag 09LS
(`DifferentialGraded.Bimodule.derivedTensorNatTrans_counit`). -/
@[stacks 09S3 "the natural transformation 1 (x) f"]
def derivedTensorNatTrans {N N' : Bimodule A B} (f : N ⟶ N') :
    derivedTensorFunctor N ⟶ derivedTensorFunctor N' :=
  Functor.leftDerivedNatTrans (derivedTensorFunctor N) (derivedTensorFunctor N')
    (derivedTensorFunctorCounit N) (derivedTensorFunctorCounit N')
    (quasiIsomorphisms' A) (ordinaryTensorNatTrans f)

/-- **The defining identity of `1 ⊗ f`.** Composed with the comparison of Tag 09LS from the
derived to the plain tensor product with `N'`, the transformation `1 ⊗ f` is the comparison for
`N` followed by ordinary tensoring with `f`. -/
@[reassoc]
theorem derivedTensorNatTrans_counit {N N' : Bimodule A B} (f : N ⟶ N') :
    Functor.whiskerLeft (quasiIsomorphisms' A).Q (derivedTensorNatTrans f) ≫
        derivedTensorFunctorCounit N' =
      derivedTensorFunctorCounit N ≫ ordinaryTensorNatTrans f :=
  Functor.leftDerivedNatTrans_fac (derivedTensorFunctor N) (derivedTensorFunctor N')
    (derivedTensorFunctorCounit N) (derivedTensorFunctorCounit N')
    (quasiIsomorphisms' A) (ordinaryTensorNatTrans f)

/-- The component of `1 ⊗ f` at the image of an object of `K(A, d)`, modulo the two comparisons
of Tag 09LS: it is ordinary tensoring with `f`. -/
theorem derivedTensorNatTrans_app_comp_counit {N N' : Bimodule A B} (f : N ⟶ N')
    (X : HomotopyCategory A) :
    (derivedTensorNatTrans f).app ((quasiIsomorphisms' A).Q.obj X) ≫
        (derivedTensorFunctorCounit N').app X =
      (derivedTensorFunctorCounit N).app X ≫ (ordinaryTensorNatTrans f).app X :=
  Functor.leftDerivedNatTrans_app (derivedTensorFunctor N) (derivedTensorFunctor N')
    (derivedTensorFunctorCounit N) (derivedTensorFunctorCounit N')
    (quasiIsomorphisms' A) (ordinaryTensorNatTrans f) X

/-- `1 ⊗ f` is the identity for the identity of a bimodule. -/
@[simp] theorem derivedTensorNatTrans_id (N : Bimodule A B) :
    derivedTensorNatTrans (𝟙 N) = 𝟙 (derivedTensorFunctor N) := by
  refine Functor.leftDerived_ext (derivedTensorFunctor N) (derivedTensorFunctorCounit N)
    (quasiIsomorphisms' A) _ _ _ ?_
  rw [derivedTensorNatTrans_counit, ordinaryTensorNatTrans_id, Category.comp_id,
    Functor.whiskerLeft_id', Category.id_comp]

/-- `1 ⊗ f` is functorial in the bimodule. -/
@[simp] theorem derivedTensorNatTrans_comp {N N' N'' : Bimodule A B} (f : N ⟶ N')
    (g : N' ⟶ N'') :
    derivedTensorNatTrans (f ≫ g) = derivedTensorNatTrans f ≫ derivedTensorNatTrans g := by
  refine Functor.leftDerived_ext (derivedTensorFunctor N'') (derivedTensorFunctorCounit N'')
    (quasiIsomorphisms' A) _ _ _ ?_
  simp only [Functor.whiskerLeft_comp, Category.assoc, derivedTensorNatTrans_counit,
    derivedTensorNatTrans_counit_assoc, ordinaryTensorNatTrans_comp]

/-! ### The second assertion of Tag 09S3, reduced to the modules with property (P) -/

/-- **The second assertion of Stacks 09S3, reduced to its content.** `1 ⊗ f` is an isomorphism of
functors as soon as, for every right differential graded `A`-module `P` carrying a property-(P)
filtration, ordinary tensoring with `f` is an isomorphism `P ⊗_A N ⟶ P ⊗_A N'` in `D(B, d)` —
equivalently, a quasi-isomorphism.

Only this implication is proved here. The hypothesis is the whole content of the second
assertion: the source obtains it by filtering `P`, reducing along the admissible short exact
sequences of the filtration to its graded pieces, which are direct sums of shifts `A[k]`, and
there it is the hypothesis that `f` is a quasi-isomorphism. That reduction is not formalized, so
`f` being a quasi-isomorphism does not appear below and the tag is not claimed for this
statement; the second assertion is instead obtained downstream, by the dévissage of Tag 0FQE in
`D(A, d)`, as `DifferentialGraded.Bimodule.quasiIsoInvertsDerivedTensor`.

What *is* proved is the passage from the modules with property (P) to all of `D(A, d)`: the two
comparisons of Tag 09LS are invertible at the image of such a module, because Tag 09KM puts it in
the left orthogonal of the acyclic modules and `Q` is then bijective on the morphisms out of it,
and every object of `D(A, d)` is isomorphic to such an image by Tag 09KP. -/
theorem isIso_derivedTensorNatTrans_of_propertyP {N N' : Bimodule A B} (f : N ⟶ N')
    (h : ∀ P : DifferentialGradedModule A, Nonempty (PropertyPFiltration P) →
      IsIso ((ordinaryTensorNatTrans f).app ((toHomotopyCategory A).obj P))) :
    IsIso (derivedTensorNatTrans f) := by
  have : ∀ M : Bimodule A B, (tensorFunctorToDerivedCategory M).HasPointwiseLeftDerivedFunctor
      (quasiIsomorphisms' A) := fun M =>
    Functor.hasPointwiseLeftDerivedFunctor_of_resolutions (quasiIsomorphisms' A)
      (tensorFunctorToDerivedCategory M) (exists_resolution_map_bijective A)
  have := Localization.essSurj (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)
  have happ : ∀ Y : derivedCategory' A, IsIso ((derivedTensorNatTrans f).app Y) := by
    intro Y
    obtain ⟨P, g, hg, ⟨F⟩⟩ := exists_propertyP_resolution A
      ((quasiIsomorphisms' A).Q.objPreimage Y).as
    have hb := bijective_q_map_of_leftOrthogonal (leftOrthogonal_acyclic_of_propertyP F)
    have hc : ∀ M : Bimodule A B,
        IsIso ((derivedTensorFunctorCounit M).app ((toHomotopyCategory A).obj P)) := fun M =>
      (Functor.RightExtension.mk _ (derivedTensorFunctorCounit M)).isIso_hom_app_of_bijective
        (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
          (derivedTensorFunctor M) (derivedTensorFunctorCounit M) (quasiIsomorphisms' A) _) hb
    have h3 : IsIso ((ordinaryTensorNatTrans f).app ((toHomotopyCategory A).obj P)) := h P ⟨F⟩
    have hcomp : IsIso ((derivedTensorNatTrans f).app
        ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj P)) ≫
        (derivedTensorFunctorCounit N').app ((toHomotopyCategory A).obj P)) := by
      rw [derivedTensorNatTrans_app_comp_counit]
      infer_instance
    have h4 : IsIso ((derivedTensorNatTrans f).app
        ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj P))) :=
      IsIso.of_isIso_comp_right _
        ((derivedTensorFunctorCounit N').app ((toHomotopyCategory A).obj P))
    have : IsIso ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map g)) :=
      Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) _
        ((quasiIsomorphisms_map_iff' A g).2 hg)
    let e : (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj P) ≅ Y :=
      asIso ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map g)) ≪≫
        (quasiIsomorphisms' A).Q.objObjPreimageIso Y
    have h5 : IsIso ((derivedTensorFunctor N).map e.hom ≫ (derivedTensorNatTrans f).app Y) := by
      rw [(derivedTensorNatTrans f).naturality e.hom]
      infer_instance
    exact IsIso.of_isIso_comp_left ((derivedTensorFunctor N).map e.hom) _
  exact NatIso.isIso_of_isIso_app _

end DifferentialGraded.Bimodule

end
