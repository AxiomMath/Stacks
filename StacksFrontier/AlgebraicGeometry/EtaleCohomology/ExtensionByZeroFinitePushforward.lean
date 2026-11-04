module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroCharacterization
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero commutes with the direct image along a finite morphism

Consider a cartesian diagram of schemes of a big étale site
```
U --j'--> X
|g        |f
V --j---> Y
```
with `f` finite and `j` an open immersion, with `j` and `j'` viewed as objects of the small
étale sites of `Y` and of `X`. Then `f_* ∘ j'_!` and `j_! ∘ g_*` agree as functors
`Ab(U_étale) ⥤ Ab(Y_étale)`.

The comparison between the two composites is built once and for all, with no hypothesis on
the square beyond a given base-change identification `g_* ∘ (j')^{-1} ≅ j^{-1} ∘ f_*` of the
restriction functors: it is the mate of that identification along the two
extension-by-zero adjunctions `j'_! ⊣ (j')^{-1}` and `j_! ⊣ j^{-1}`, so it is a natural
transformation of functors by construction and no separate verification of functoriality is
needed.

That comparison is an isomorphism by the uniqueness characterisation of extension by zero,
`AlgebraicGeometry.abelianExtensionByZeroAdjunction_hom_isIso_of_stalk_isZero`. Its component
at `F` is the map `j_!(g_*F) ⟶ f_*(j'_!F)` adjoint to the composite
`g_*F ⟶ g_*((j')^{-1}j'_!F) ⟶ j^{-1}f_*j'_!F` of the unit of `j'_! ⊣ (j')^{-1}` with the
base-change identification; the unit is an isomorphism because `j'` is an open immersion, so
that composite identifies `g_*F` with the restriction of `f_*j'_!F` to `V`. The
characterisation then applies as soon as `f_*j'_!F` has vanishing stalks at the geometric
points of `Y` outside `V`.

## Main definitions

* `AlgebraicGeometry.extensionByZeroFinitePushforwardComparison` — the comparison
  `j_! ∘ g_* ⟶ f_* ∘ j'_!`, as the mate of a base-change identification of the restriction
  functors.

## Main results

* `AlgebraicGeometry.extensionByZeroFinitePushforwardComparison_app` — the component of the
  comparison at `F` is the adjoint of the restriction identification of `g_*F`.
* `AlgebraicGeometry.isIso_extensionByZeroFinitePushforwardComparison` — the comparison is an
  isomorphism when `j'` is an open immersion and `f_* ∘ j'_!` has vanishing stalks off `V`.

## Implementation notes

The two inputs that the source draws from results cited elsewhere are carried as explicit
hypotheses, because neither is available for abelian sheaves in this repository.

* `hbc` stands in for Stacks 0959, the base change of a direct image along a finite morphism,
  for abelian sheaves: the identification `g_* ∘ (j')^{-1} ≅ j^{-1} ∘ f_*`. The repository
  has the comparison map of that statement for sheaves of sets,
  `AlgebraicGeometry.smallEtaleBaseChangeNatTrans`, and the stalk computation showing it
  bijective, but not the conclusion itself, and not for abelian sheaves. The inverse images
  along the étale morphisms `j` and `j'` are spelled as the restriction functors
  `AlgebraicGeometry.abelianRestriction`, which is the same functor:
  `AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward`.
* `hzero` stands in for Stacks 03QP together with the vanishing half of Stacks 0F70: the
  stalk of `f_*j'_!F` at a geometric point `y` of `Y` outside `V` is the direct sum of the
  stalks of `j'_!F` over the points of `X` above `y`, and each of those vanishes because
  `j'` has open image missing them. Finiteness of `f` enters only here.

Both are hypotheses of the statement, so the conclusion is weaker than the source's, not
stronger; the commutation itself is never assumed. The natural isomorphism is derived, with
its naturality proved rather than carried.

## References

* [Stacks Project, Tag 0GJ1](https://stacks.math.columbia.edu/tag/0GJ1)
* [Stacks Project, Tag 0F70](https://stacks.math.columbia.edu/tag/0F70)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (U : SmallEtale B X.1 X.property) (V : SmallEtale B Y.1 Y.property)
  (g : U.obj.left ⟶ V.obj.left)

/-- The comparison `j_! ∘ g_* ⟶ f_* ∘ j'_!` attached to an identification
`hbc : g_* ∘ (j')^{-1} ≅ j^{-1} ∘ f_*` of the restriction functors around a square
`g ≫ j = j' ≫ f`: the mate of `hbc` along the extension-by-zero adjunctions of `j'` and of
`j`. Being a mate, it is natural in the abelian sheaf on `U` by construction. -/
public def extensionByZeroFinitePushforwardComparison
    (hbc : abelianRestriction B X.1 X.property U ⋙
        B.smallPushforward g AddCommGrpCat.{u + 1} ≅
      B.smallPushforward f AddCommGrpCat.{u + 1} ⋙
        abelianRestriction B Y.1 Y.property V) :
    B.smallPushforward g AddCommGrpCat.{u + 1} ⋙
        abelianExtensionByZero B Y.1 Y.property V ⟶
      abelianExtensionByZero B X.1 X.property U ⋙
        B.smallPushforward f AddCommGrpCat.{u + 1} :=
  (mateEquiv (abelianExtensionByZeroAdjunction B X.1 X.property U)
    (abelianExtensionByZeroAdjunction B Y.1 Y.property V)).symm hbc.hom

/-- The component of the comparison at an abelian sheaf `F` on `U` is the map adjoint, for
`j_! ⊣ j^{-1}`, to the composite of `g_*` applied to the unit of `j'_! ⊣ (j')^{-1}` with the
given base-change identification. -/
public theorem extensionByZeroFinitePushforwardComparison_app
    (hbc : abelianRestriction B X.1 X.property U ⋙
        B.smallPushforward g AddCommGrpCat.{u + 1} ≅
      B.smallPushforward f AddCommGrpCat.{u + 1} ⋙
        abelianRestriction B Y.1 Y.property V)
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}) :
    (extensionByZeroFinitePushforwardComparison B f U V g hbc).app F =
      ((abelianExtensionByZeroAdjunction B Y.1 Y.property V).homEquiv
          ((B.smallPushforward g AddCommGrpCat.{u + 1}).obj F)
          ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj
            ((abelianExtensionByZero B X.1 X.property U).obj F))).symm
        ((B.smallPushforward g AddCommGrpCat.{u + 1}).map
            ((abelianExtensionByZeroAdjunction B X.1 X.property U).unit.app F) ≫
          hbc.hom.app ((abelianExtensionByZero B X.1 X.property U).obj F)) := by
  refine (Equiv.eq_symm_apply _).2 ?_
  rw [Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (abelianExtensionByZeroAdjunction B X.1 X.property U)
    (abelianExtensionByZeroAdjunction B Y.1 Y.property V) hbc.hom F).symm

/-- The comparison is an isomorphism as soon as `j'` is an open immersion and every
`f_*(j'_!F)` has vanishing stalks at the geometric points of `Y` outside `V`: its component
at `F` is then the adjoint of an identification of `g_*F` with the restriction of `f_*j'_!F`
to `V`, which the uniqueness characterisation of extension by zero turns into an
isomorphism. -/
public theorem isIso_extensionByZeroFinitePushforwardComparison
    [IsOpenImmersion (B.inclusion.map U.obj.hom)]
    [IsOpenImmersion (B.inclusion.map V.obj.hom)]
    (hbc : abelianRestriction B X.1 X.property U ⋙
        B.smallPushforward g AddCommGrpCat.{u + 1} ≅
      B.smallPushforward f AddCommGrpCat.{u + 1} ⋙
        abelianRestriction B Y.1 Y.property V)
    (hzero : ∀ (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        AddCommGrpCat.{u + 1}) (y : GeometricPoint Y.1),
      y.hom default ∉ Set.range (B.inclusion.map V.obj.hom).base →
        IsZero (etaleStalk B Y.1 Y.property y
          ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj
            ((abelianExtensionByZero B X.1 X.property U).obj F)).obj)) :
    IsIso (extensionByZeroFinitePushforwardComparison B f U V g hbc) := by
  have happ : ∀ F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1},
      IsIso ((extensionByZeroFinitePushforwardComparison B f U V g hbc).app F) := by
    intro F
    have hunit : IsIso ((abelianExtensionByZeroAdjunction B X.1 X.property U).unit.app F) :=
      abelianExtensionByZeroAdjunction_unit_isIso B X.1 X.property U F
    have he : IsIso ((B.smallPushforward g AddCommGrpCat.{u + 1}).map
        ((abelianExtensionByZeroAdjunction B X.1 X.property U).unit.app F) ≫
        hbc.hom.app ((abelianExtensionByZero B X.1 X.property U).obj F)) := inferInstance
    rw [extensionByZeroFinitePushforwardComparison_app]
    exact abelianExtensionByZeroAdjunction_hom_isIso_of_stalk_isZero B Y.1 Y.property V
      ((B.smallPushforward g AddCommGrpCat.{u + 1}).obj F)
      ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj
        ((abelianExtensionByZero B X.1 X.property U).obj F))
      (asIso ((B.smallPushforward g AddCommGrpCat.{u + 1}).map
        ((abelianExtensionByZeroAdjunction B X.1 X.property U).unit.app F) ≫
        hbc.hom.app ((abelianExtensionByZero B X.1 X.property U).obj F)))
      (hzero F)
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry

end
