module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DGNaturalTransformation
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecomposition
public import StacksCore.Tactic.StacksAttribute

/-! # Precomposition as a transformation of internal hom functors

Let `f : M ⟶ N` be a homomorphism of differential graded `(A, B)`-bimodules. Precomposition with
`f` is a homomorphism `Hom^•_B(N, P) ⟶ Hom^•_B(M, P)` of right differential graded `A`-modules
for every right differential graded `B`-module `P`
(`DifferentialGraded.Bimodule.precompHom`), and it commutes strictly with postcomposition by a
homogeneous map `P → Q`, since the two act on opposite sides of a homogeneous map `N → P`. It is
therefore a natural transformation of the internal hom functors of Tag 0FQQ, in the direction
opposite to `f`: of the differential graded functors, and hence of the induced functors on the
homotopy categories.

## Main definitions

* `DifferentialGraded.Bimodule.precompModuleHom`: precomposition between the values of the
  differential graded internal hom functors.
* `DifferentialGraded.Bimodule.precompDGNatTrans`: precomposition as a natural transformation of
  the differential graded internal hom functors.
* `DifferentialGraded.Bimodule.precompHomotopyNatTrans`: the induced natural transformation of
  the internal hom functors on the homotopy categories of Tag 09JQ.

## Main results

* `DifferentialGraded.Bimodule.precompModuleHom_id` and
  `DifferentialGraded.Bimodule.precompModuleHom_comp`: precomposition is contravariantly
  functorial in the bimodule, on the nose.
* `DifferentialGraded.Bimodule.precompHomotopyNatTrans_id` and
  `DifferentialGraded.Bimodule.precompHomotopyNatTrans_comp`: the same for the transformation of
  functors on the homotopy categories.

## Implementation notes

The internal hom functor is `DifferentialGradedModule.homDGFunctorData`, whose value at `P` is
`DifferentialGradedModule.homModulePresentation A B N L P`; the identification is the `obj_eq`
field of the data and holds by definitional unfolding, so no transport along it intervenes.
Strict naturality is checked on homogeneous elements, where both composites are the triple
composite of the homogeneous maps involved, and is transported to the homotopy categories by
`DGCategory.DGNatTrans.onK`.

Functoriality is proved at the level of the differential graded transformation, where the
components are homomorphisms of differential graded modules rather than homotopy classes, so the
two identities are equalities of homomorphisms and descend to the homotopy categories formally.

## References

* [Stacks Project, Tag 0BYV](https://stacks.math.columbia.edu/tag/0BYV); the internal hom
  functor is [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- The chosen presentation of the internal hom out of a differential graded bimodule, namely the
value of the differential graded internal hom functor of Tag 0FQQ. -/
abbrev homPresentation (X : Bimodule A B) (P : DifferentialGradedModule B) :
    HomModuleData A B X.rightModule P X.leftAction :=
  homModulePresentation A B X.rightModule X.leftAction P

variable {M N L : Bimodule A B}

/-- Precomposition with a bimodule homomorphism, as a homomorphism between the values of the
differential graded internal hom functors. -/
def precompModuleHom (f : M ⟶ N) (P : DifferentialGradedModule B) :
    (homPresentation N P).module ⟶ (homPresentation M P).module :=
  precompHom f (homPresentation N P) (homPresentation M P)

/-- On a homogeneous element, precomposition between the values of the internal hom functors is
the precomposition of that homogeneous map with `f`. -/
theorem precompModuleHom_apply_grading (f : M ⟶ N) (P : DifferentialGradedModule B) (n : ℤ)
    (g : (homPresentation N P).module.grading n) :
    (precompModuleHom f P).toFun (g : (homPresentation N P).module.M) =
      (precompGraded f (homPresentation N P) (homPresentation M P) n g :
        (homPresentation M P).module.M) :=
  precompHom_apply_grading f (homPresentation N P) (homPresentation M P) n g

/-- Precomposition with the identity is the identity. -/
@[simp] theorem precompModuleHom_id (M : Bimodule A B) (P : DifferentialGradedModule B) :
    precompModuleHom (𝟙 M) P = 𝟙 (homPresentation M P).module := by
  refine (precompHom_unique (𝟙 M) (homPresentation M P) (homPresentation M P) _ ?_).symm
  intro n g
  exact Subtype.ext (LinearMap.ext fun _ => rfl)

/-- Precomposition reverses composition. -/
theorem precompModuleHom_comp (f : M ⟶ N) (g : N ⟶ L) (P : DifferentialGradedModule B) :
    precompModuleHom (f ≫ g) P = precompModuleHom g P ≫ precompModuleHom f P := by
  refine (precompHom_unique (f ≫ g) (homPresentation L P) (homPresentation M P) _ ?_).symm
  intro n h
  apply homogeneousMap_ext
  intro p x
  have h₁ : (precompModuleHom g P ≫ precompModuleHom f P).toFun
      (h : (homPresentation L P).module.M) =
      (precompGraded f (homPresentation N P) (homPresentation M P) n
        (precompGraded g (homPresentation L P) (homPresentation N P) n h) :
          (homPresentation M P).module.M) := by
    show (precompModuleHom f P).toFun ((precompModuleHom g P).toFun
      (h : (homPresentation L P).module.M)) = _
    rw [precompModuleHom_apply_grading g P n h, precompModuleHom_apply_grading f P n]
  rw [show (⟨(precompModuleHom g P ≫ precompModuleHom f P).toFun
        (h : (homPresentation L P).module.M), _⟩ : (homPresentation M P).module.grading n) =
      precompGraded f (homPresentation N P) (homPresentation M P) n
        (precompGraded g (homPresentation L P) (homPresentation N P) n h) from
    Subtype.ext h₁]
  rw [precompGraded_apply, homogeneousEquiv_precompGraded]
  rfl

/-- Precomposition commutes with postcomposition: on a homogeneous map `N → P` the two act on
opposite sides. -/
private theorem precomp_postcomp_apply (f : M ⟶ N) {P Q : DifferentialGradedModule B} {n p : ℤ}
    (u : HomogeneousMap B P Q n) (g : (homPresentation N P).module.grading p) :
    (precompModuleHom f Q).toFun
        ((homPostcompHomogeneousMap A B N.rightModule N.leftAction (homPresentation N P)
          (homPresentation N Q) n u).1 (g : (homPresentation N P).module.M)) =
      (homPostcompHomogeneousMap A B M.rightModule M.leftAction (homPresentation M P)
        (homPresentation M Q) n u).1
          ((precompModuleHom f P).toFun (g : (homPresentation N P).module.M)) := by
  rw [homPostcompHomogeneousMap_apply A B N.rightModule N.leftAction (homPresentation N P)
      (homPresentation N Q) n p u g,
    precompModuleHom_apply_grading f P p g,
    homPostcompHomogeneousMap_apply A B M.rightModule M.leftAction (homPresentation M P)
      (homPresentation M Q) n p u (precompGraded f (homPresentation N P)
        (homPresentation M P) p g),
    precompModuleHom_apply_grading f Q (n + p)]
  refine congrArg Subtype.val
    (((homPresentation M Q).homogeneousEquiv (n + p)).injective (Subtype.ext ?_))
  simp only [homogeneousEquiv_precompGraded, LinearEquiv.apply_symm_apply,
    homogeneousMapComp_val]
  exact LinearMap.comp_assoc _ _ _

/-- The underived half of Tag 0BYV. Precomposition with a homomorphism of
differential graded bimodules, as a natural transformation of the differential graded internal
hom functors of Tag 0FQQ. -/
def precompDGNatTrans (f : M ⟶ N) :
    DGCategory.DGNatTrans (homDGFunctorData A B N.rightModule N.leftAction).functor
      (homDGFunctorData A B M.rightModule M.leftAction).functor where
  app P := cocycleOfHom A (precompModuleHom f P)
  naturality {P Q n} u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    change (precompModuleHom f Q).toFun
        ((homPostcompHomogeneousMap A B N.rightModule N.leftAction (homPresentation N P)
          (homPresentation N Q) n u).1 z) =
      (homPostcompHomogeneousMap A B M.rightModule M.leftAction (homPresentation M P)
        (homPresentation M Q) n u).1 ((precompModuleHom f P).toFun z)
    induction z using DirectSum.Decomposition.inductionOn (homPresentation N P).module.grading
      with
    | zero => simp only [map_zero]
    | @homogeneous p g => exact precomp_postcomp_apply f u g
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The component of the precomposition transformation at `P` is the cocycle of the
precomposition homomorphism `precompModuleHom f P`. -/
@[simp] theorem precompDGNatTrans_app (f : M ⟶ N) (P : DifferentialGradedModule B) :
    (precompDGNatTrans f).app P = cocycleOfHom A (precompModuleHom f P) := rfl

/-- On the homotopy category of the differential graded category, precomposition with the
identity is the identity. -/
@[simp] theorem precompDGNatTrans_onK_id (M : Bimodule A B) :
    (precompDGNatTrans (𝟙 M)).onK = 𝟙 _ := by
  ext P
  show Quotient.mk _ (cocycleOfHom A (precompModuleHom (𝟙 M) P)) =
    Quotient.mk _ ⟨(dgCategory A).id (homPresentation M P).module, (dgCategory A).d_id _⟩
  refine congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext ?_))
  exact congrArg DifferentialGradedModule.Hom.toFun (precompModuleHom_id M P)

/-- On the homotopy category of the differential graded category, precomposition reverses
composition. -/
theorem precompDGNatTrans_onK_comp (f : M ⟶ N) (g : N ⟶ L) :
    (precompDGNatTrans (f ≫ g)).onK =
      (precompDGNatTrans g).onK ≫ (precompDGNatTrans f).onK := by
  ext P
  show Quotient.mk _ (cocycleOfHom A (precompModuleHom (f ≫ g) P)) =
    (dgCategory A).compK (Quotient.mk _ (cocycleOfHom A (precompModuleHom f P)))
      (Quotient.mk _ (cocycleOfHom A (precompModuleHom g P)))
  refine congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext ?_))
  exact congrArg DifferentialGradedModule.Hom.toFun (precompModuleHom_comp f g P)

/-- The natural transformation of internal hom functors on the homotopy categories of
differential graded modules induced by precomposition with a homomorphism of differential graded
bimodules. -/
def precompHomotopyNatTrans (f : M ⟶ N) :
    homHomotopyCategoryFunctor A B N.rightModule N.leftAction ⟶
      homHomotopyCategoryFunctor A B M.rightModule M.leftAction :=
  Functor.whiskerLeft (homotopyCategoryEquivalence B).functor
    (Functor.whiskerRight (precompDGNatTrans f).onK (homotopyCategoryEquivalence A).inverse)

/-- Precomposition with the identity is the identity transformation of internal hom functors on
the homotopy categories. -/
@[simp] theorem precompHomotopyNatTrans_id (M : Bimodule A B) :
    precompHomotopyNatTrans (𝟙 M) =
      𝟙 (homHomotopyCategoryFunctor A B M.rightModule M.leftAction) := by
  ext P
  simp only [precompHomotopyNatTrans, precompDGNatTrans_onK_id, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.id_app]
  exact (homotopyCategoryEquivalence A).inverse.map_id _

/-- Precomposition reverses composition, as transformations of internal hom functors on the
homotopy categories. -/
theorem precompHomotopyNatTrans_comp (f : M ⟶ N) (g : N ⟶ L) :
    precompHomotopyNatTrans (f ≫ g) =
      precompHomotopyNatTrans g ≫ precompHomotopyNatTrans f := by
  ext P
  simp only [precompHomotopyNatTrans, precompDGNatTrans_onK_comp, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.map_comp]
  rfl

end DifferentialGraded.Bimodule

end
