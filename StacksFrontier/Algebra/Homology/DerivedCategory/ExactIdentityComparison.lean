module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionComparison

/-!
# The identity comparison of right derived functors

Let `𝒜` be an abelian category with a derived category and enough injectives, and let
`F : 𝒜 ⥤ 𝒜` be an additive functor isomorphic to the identity, `e : F ≅ 𝟭 𝒜`. This file
constructs the comparison
$$
RF \;\cong\; \mathbf{1}
$$
of functors `D⁺(𝒜) ⥤ D⁺(𝒜)` on the bounded below derived category, and characterizes it by its
behaviour on the derived-functor unit of `RF`.

It is the identity analogue of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`, and it is what turns a family
of comparisons satisfying only a cocycle condition into a genuine functor on an index category:
the law at an identity index is an identity *modulo* this comparison, and nothing else can say
so.

No exactness hypothesis is needed, and none is imposed: a functor isomorphic to the identity is
exact, but the construction never uses it. What makes the comparison exist is that *both* sides
are right derived functors of the same functor `K⁺(𝒜) ⥤ D⁺(𝒜)`. For `RF` that is its own
derived-functor unit; for the identity functor of `D⁺(𝒜)` it is
`CategoryTheory.Functor.isRightDerivedFunctor_of_inverts` applied to the right unitor of the
localization `Qh : K⁺(𝒜) ⥤ D⁺(𝒜)`, which says that a functor whose precomposition with a
localization is isomorphic to the functor being derived is a right derived functor of it. The
comparison is then the uniqueness of right derived functors,
`CategoryTheory.Functor.rightDerivedNatIso`, applied to the degreewise identity comparison
`F.mapHomotopyCategoryPlus ≅ 𝟭 K⁺(𝒜)`.

## Main definitions

* `CategoryTheory.Functor.mapHomotopyCategoryPlusIdIso`: the functor induced by the identity
  functor on the bounded below homotopy category is the identity.
* `CategoryTheory.Functor.mapHomotopyCategoryPlusIdIsoOf`: the degreewise identity comparison
  `F.mapHomotopyCategoryPlus ≅ 𝟭 K⁺(𝒜)` attached to `e : F ≅ 𝟭 𝒜`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusIdIsoOf`: **the comparison `RF ≅ 𝟭` for
  `e : F ≅ 𝟭 𝒜`.**

## Main results

* `CategoryTheory.Functor.mapHomotopyCategoryPlusIdIso_hom_comp` and the three companion
  cancellation lemmas: the components of the identity comparison on bounded below homotopy
  categories are identities.
* `CategoryTheory.Functor.mapHomotopyCategoryPlusIdIsoOf_hom_app` and `..._inv_app`: the
  components of the degreewise identity comparison are `Stacks.Cohomology.BaseChange.mapPlus`
  of the components of `e`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusIdIsoOf_fac`: **the characterizing
  factorization** of the comparison through the derived-functor unit of `RF`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusIdIsoOf_inv_app`: the same identity solved for
  the inverse of the comparison, which is the form a descent along the unit of a right derived
  functor consumes.

## Implementation notes

*Why the component statements are cancellations.* The functors `(𝟭 𝒜).mapHomotopyCategoryPlus`
and `𝟭 K⁺(𝒜)` agree on objects definitionally but are not equal, so a component of
`mapHomotopyCategoryPlusIdIso` cannot be rewritten to `𝟙`: replacing it by `𝟙 K` forces the two
ends of the surrounding composite to be the *same* object where they are merely definitionally
equal, and the ambient term stops being type-correct. This is the same phenomenon as for
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso` at the identity isomorphism, and it has
the same resolution: four cancellation lemmas which rewrite a whole composite.

*Both halves of the characterization are components of
`CategoryTheory.Functor.rightDerivedNatTrans`*, so neither needs the invertibility of the
derived-functor unit of `F`. In particular the inverse form is stated with the unit appearing
positively, rather than with `CategoryTheory.asIso` of it, which is what makes it usable before
exactness of `F` has been established.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)

Tags covered: none.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The identity functor, degreewise -/

section HomotopyCategoryId

variable (V : Type u) [Category.{v} V] [Preadditive V]

/-- **The functor induced on bounded below homotopy categories by the identity functor is the
identity.** It is `mapHomotopyCategoryIdIso` read through the fully faithful inclusion of the
bounded below part, as `CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso` is. -/
def mapHomotopyCategoryPlusIdIso :
    (𝟭 V).mapHomotopyCategoryPlus ≅ 𝟭 (HomotopyCategory.Plus V) :=
  ((HomotopyCategory.plus V).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (HomotopyCategory.Plus.ι V)
      (mapHomotopyCategoryIdIso V (ComplexShape.up ℤ)))

variable {V} {K : HomotopyCategory.Plus V}

/-- The identity comparison on bounded below homotopy categories cancels on the left. -/
theorem mapHomotopyCategoryPlusIdIso_hom_comp {Z : HomotopyCategory.Plus V} (f : K ⟶ Z) :
    (mapHomotopyCategoryPlusIdIso V).hom.app K ≫ f = f :=
  Category.id_comp f

/-- The identity comparison on bounded below homotopy categories cancels on the right. -/
theorem mapHomotopyCategoryPlusIdIso_comp_hom {Z : HomotopyCategory.Plus V}
    (f : Z ⟶ (𝟭 V).mapHomotopyCategoryPlus.obj K) :
    f ≫ (mapHomotopyCategoryPlusIdIso V).hom.app K = f :=
  Category.comp_id f

/-- The inverse identity comparison on bounded below homotopy categories cancels on the
left. -/
theorem mapHomotopyCategoryPlusIdIso_inv_comp {Z : HomotopyCategory.Plus V}
    (f : (𝟭 V).mapHomotopyCategoryPlus.obj K ⟶ Z) :
    (mapHomotopyCategoryPlusIdIso V).inv.app K ≫ f = f :=
  Category.id_comp f

/-- The inverse identity comparison on bounded below homotopy categories cancels on the
right. -/
theorem mapHomotopyCategoryPlusIdIso_comp_inv {Z : HomotopyCategory.Plus V} (f : Z ⟶ K) :
    f ≫ (mapHomotopyCategoryPlusIdIso V).inv.app K = f :=
  Category.comp_id f

end HomotopyCategoryId

/-! ### The degreewise identity comparison attached to `F ≅ 𝟭` -/

section DegreewiseId

variable {A : Type u} [Category.{v} A] [Preadditive A] (F : A ⥤ A) [F.Additive]
  (e : F ≅ 𝟭 A)

/-- **The degreewise identity comparison** `F.mapHomotopyCategoryPlus ≅ 𝟭 K⁺(𝒜)` attached to an
isomorphism `e : F ≅ 𝟭 𝒜`: the degreewise image of `e`, followed by the identity comparison for
the identity functor. -/
def mapHomotopyCategoryPlusIdIsoOf : F.mapHomotopyCategoryPlus ≅ 𝟭 (HomotopyCategory.Plus A) :=
  mapHomotopyCategoryPlusNatIso e ≪≫ mapHomotopyCategoryPlusIdIso A

end DegreewiseId

section DegreewiseIdApp

variable {A : Type u} [Category.{v} A] [Abelian A] (F : A ⥤ A) [F.Additive] (e : F ≅ 𝟭 A)

/-- **The components of the degreewise identity comparison** are the degreewise images of the
components of `e`. -/
theorem mapHomotopyCategoryPlusIdIsoOf_hom_app (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusIdIsoOf F e).hom.app K =
      (Stacks.Cohomology.BaseChange.mapPlus e.hom).app K := by
  change (mapHomotopyCategoryPlusNatIso e).hom.app K ≫
    (mapHomotopyCategoryPlusIdIso A).hom.app K = _
  rw [mapHomotopyCategoryPlusNatIso_hom]
  exact mapHomotopyCategoryPlusIdIso_comp_hom _

/-- The inverse half of `mapHomotopyCategoryPlusIdIsoOf_hom_app`. -/
theorem mapHomotopyCategoryPlusIdIsoOf_inv_app (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusIdIsoOf F e).inv.app K =
      (Stacks.Cohomology.BaseChange.mapPlus e.inv).app K := by
  change (mapHomotopyCategoryPlusIdIso A).inv.app K ≫
    (mapHomotopyCategoryPlusNatIso e).inv.app K = _
  rw [mapHomotopyCategoryPlusNatIso_inv]
  exact mapHomotopyCategoryPlusIdIso_inv_comp _

end DegreewiseIdApp

/-! ### The comparison `RF ≅ 𝟭` -/

section Identity

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A]

/-- **The identity functor of `D⁺(𝒜)` is a right derived functor of the localization
`Qh : K⁺(𝒜) ⥤ D⁺(𝒜)`**, with the right unitor of `Qh` as its unit. -/
instance isRightDerivedFunctor_id_derivedCategoryPlus :
    (𝟭 (DerivedCategory.Plus A)).IsRightDerivedFunctor
      (rightUnitor (DerivedCategory.Plus.Qh (C := A))).inv
      (HomotopyCategory.Plus.quasiIso A) :=
  isRightDerivedFunctor_of_inverts _ _ (rightUnitor _)

variable (F : A ⥤ A) [F.Additive] (e : F ≅ 𝟭 A)

/-- **The comparison `RF ≅ 𝟭` attached to an isomorphism `e : F ≅ 𝟭 𝒜`.** Both sides are right
derived functors along `Qh` of the same functor `K⁺(𝒜) ⥤ D⁺(𝒜)` — of
`F.mapHomotopyCategoryPlus ⋙ Qh` for the left hand side and of `Qh` itself for the right, the
two being identified by the degreewise identity comparison — so the uniqueness of right derived
functors produces the isomorphism. -/
def rightDerivedFunctorPlusIdIsoOf : F.rightDerivedFunctorPlus ≅ 𝟭 (DerivedCategory.Plus A) :=
  rightDerivedNatIso _ _ F.rightDerivedFunctorPlusUnith
    (rightUnitor (DerivedCategory.Plus.Qh (C := A))).inv (HomotopyCategory.Plus.quasiIso A)
    (isoWhiskerRight (mapHomotopyCategoryPlusIdIsoOf F e) DerivedCategory.Plus.Qh ≪≫
      leftUnitor DerivedCategory.Plus.Qh)

/-- `rightDerivedFunctorPlusIdIsoOf` unfolded in the forward direction, so that the uniqueness
transformation it is built from can be handled directly. -/
theorem rightDerivedFunctorPlusIdIsoOf_hom :
    (rightDerivedFunctorPlusIdIsoOf F e).hom =
      rightDerivedNatTrans F.rightDerivedFunctorPlus (𝟭 (DerivedCategory.Plus A))
        F.rightDerivedFunctorPlusUnith
        (rightUnitor (DerivedCategory.Plus.Qh (C := A))).inv
        (HomotopyCategory.Plus.quasiIso A)
        (isoWhiskerRight (mapHomotopyCategoryPlusIdIsoOf F e) DerivedCategory.Plus.Qh ≪≫
          leftUnitor DerivedCategory.Plus.Qh).hom := rfl

/-- `rightDerivedFunctorPlusIdIsoOf` unfolded in the backward direction. -/
theorem rightDerivedFunctorPlusIdIsoOf_inv :
    (rightDerivedFunctorPlusIdIsoOf F e).inv =
      rightDerivedNatTrans (𝟭 (DerivedCategory.Plus A)) F.rightDerivedFunctorPlus
        (rightUnitor (DerivedCategory.Plus.Qh (C := A))).inv
        F.rightDerivedFunctorPlusUnith
        (HomotopyCategory.Plus.quasiIso A)
        (isoWhiskerRight (mapHomotopyCategoryPlusIdIsoOf F e) DerivedCategory.Plus.Qh ≪≫
          leftUnitor DerivedCategory.Plus.Qh).inv := rfl

/-- **The characterizing factorization of `rightDerivedFunctorPlusIdIsoOf`.** On a bounded below
complex `N`, the derived-functor unit of `RF` followed by the comparison is the degreewise
identity comparison.

Since `RF` is a right derived functor with that unit, this determines the comparison. -/
theorem rightDerivedFunctorPlusIdIsoOf_fac (N : HomotopyCategory.Plus A) :
    F.rightDerivedFunctorPlusUnith.app N ≫
        (rightDerivedFunctorPlusIdIsoOf F e).hom.app (DerivedCategory.Plus.Qh.obj N) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIdIsoOf F e).hom.app N) := by
  rw [rightDerivedFunctorPlusIdIsoOf_hom]
  simp

/-- **The characterizing factorization, solved for the inverse of the comparison.** This is the
form a descent along the unit of a right derived functor consumes, since there the comparison
enters contravariantly. It is again a component of
`CategoryTheory.Functor.rightDerivedNatTrans`, so the derived-functor unit of `F` appears
positively and no invertibility of it is needed. -/
theorem rightDerivedFunctorPlusIdIsoOf_inv_app (N : HomotopyCategory.Plus A) :
    (rightDerivedFunctorPlusIdIsoOf F e).inv.app (DerivedCategory.Plus.Qh.obj N) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIdIsoOf F e).inv.app N) ≫
        F.rightDerivedFunctorPlusUnith.app N := by
  rw [rightDerivedFunctorPlusIdIsoOf_inv]
  simpa using rightDerivedNatTrans_app (𝟭 (DerivedCategory.Plus A)) F.rightDerivedFunctorPlus
    (rightUnitor (DerivedCategory.Plus.Qh (C := A))).inv F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
    (isoWhiskerRight (mapHomotopyCategoryPlusIdIsoOf F e) DerivedCategory.Plus.Qh ≪≫
      leftUnitor DerivedCategory.Plus.Qh).inv N

end Identity

end CategoryTheory.Functor

end
