module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
import StacksCore.Tactic.StacksAttribute

/-! # `Ext` out of a fixed object, and its transport along an exact functor

Let `A` be an abelian category with enough injective resolutions whose `Ext`-groups live in the
universe of its morphisms. For `X : A` the functor `Ext^n(X, -)` is the `n`-th right derived
functor of `Hom(X, -)`: this is `extFunctorObjIsoRightDerivedCoyoneda`, the `Ext`-to-derived-`Hom`
bridge, obtained by instantiating
`ModuleSheafCohomology.extFunctorObjIsoRightDerived` at its own corepresenting functor.

The bridge is what lets Stacks 015Z — an exact functor preserving injectives commutes with right
derived functors, `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` — be read as a
statement about `Ext`.
That reading is `extFunctorObjIsoComp`: if `L : A ⥤ B` is exact and preserves injective objects,
and `Hom_B(Y, L -)` is isomorphic to `Hom_A(X, -)`, then

  `Ext_A^n(X, -) ≅ L ⋙ Ext_B^n(Y, -)`.

This is the shape every "cohomology over `X` is cohomology on a localized site" comparison takes:
there `L` is an inverse-image functor, `Y` is the unit coefficient sheaf, and the hypothesis `α` is
the adjunction `L` participates in, applied to the identification of `X` with the image of `Y`
under the left adjoint.

## Main definitions

* `Stacks.Cohomology.ExtComparison.extFunctorObjIsoRightDerivedCoyoneda`: `Ext^n(X, -)` is the
  `n`-th right derived functor of `Hom(X, -)`.
* `Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp`: the transport of `Ext` out of a fixed
  object along an exact, injective-preserving functor.
* `Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfAdjunctionOfAcyclic` and
  `Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIsoOfAcyclic`: the same transport with
  preservation of injective objects weakened to *acyclicity*, `Ext^{≥1}(Y, G I) = 0` for every
  injective `I`. That is the only hypothesis available when the right adjoint is the restriction
  functor of a subsite which is not closed under fibre products, so that its left adjoint `g_!`
  is not exact: the lisse-étale and flat-fppf sites of Stacks 0787 are of that kind.

## Implementation notes

Both statements need the `Ext`-universe to be the morphism universe of the ambient category, which
is what `ModuleSheafCohomology.extFunctorObjIsoRightDerived` assumes; the hypothesis `α` forces the
two categories to share that universe. `PreservesFiniteLimits (preadditiveCoyoneda.obj (op X))` is
Mathlib's `preservesLimits_preadditiveCoyoneda_obj`, which is why
`Mathlib.CategoryTheory.Preadditive.Yoneda.Limits` is imported here.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits CategoryTheory.Abelian

namespace Stacks.Cohomology.ExtComparison

universe v u u'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]

/-- **`Ext` out of a fixed object is the right derived functor of `Hom` out of it.** For `X : A`,
the functor `Ext^n(X, -)` is the `n`-th right derived functor of `Hom(X, -)`.

This is `ModuleSheafCohomology.extFunctorObjIsoRightDerived` at the corepresenting functor itself,
that is, with the identity corepresentation. -/
def extFunctorObjIsoRightDerivedCoyoneda (X : A) (n : ℕ) :
    extFunctorObj X n ≅ (preadditiveCoyoneda.obj (op X)).rightDerived n :=
  ModuleSheafCohomology.extFunctorObjIsoRightDerived _ X (Iso.refl _) n

variable {B : Type u'} [Category.{v} B] [Abelian B] [HasExt.{v} B] [HasInjectiveResolutions B]

/-- **`Ext` out of a fixed object transported along an exact functor preserving injectives.** Let
`L : A ⥤ B` be exact and preserve injective objects, let `X : A` and `Y : B`, and suppose
`Hom_B(Y, L -)` is isomorphic to `Hom_A(X, -)`. Then `Ext_A^n(X, -) ≅ L ⋙ Ext_B^n(Y, -)`.

The proof reads Stacks 015Z (`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`)
through the bridge `extFunctorObjIsoRightDerivedCoyoneda`: the derived functors of
`Hom_A(X, -)` and of `L ⋙ Hom_B(Y, -)` agree because the two functors do, and the latter is
computed by `L` followed by the derived functors of `Hom_B(Y, -)` because `L` carries an
injective resolution to an injective resolution. -/
def extFunctorObjIsoComp (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] [L.PreservesInjectiveObjects] {X : A} {Y : B}
    (α : L ⋙ preadditiveCoyoneda.obj (op Y) ≅ preadditiveCoyoneda.obj (op X)) (n : ℕ) :
    extFunctorObj X n ≅ L ⋙ extFunctorObj Y n :=
  extFunctorObjIsoRightDerivedCoyoneda X n ≪≫
    Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso α.symm n ≪≫
      Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L
        (preadditiveCoyoneda.obj (op Y)) n ≪≫
        Functor.isoWhiskerLeft L (extFunctorObjIsoRightDerivedCoyoneda Y n).symm

/-! ### The adjunction form

The hypothesis `α` of `extFunctorObjIsoComp` is what an adjunction supplies: for `F ⊣ G` with `F`
additive, `Hom(Y, G -)` *is* `Hom(F Y, -)`. So `Ext` out of the image of the left adjoint is
computed on the other side, which is the shape of Stacks 03F3 and 07A0. -/

section Adjunction

variable {F : B ⥤ A} {G : A ⥤ B}

/-- **The hom-set adjunction as an isomorphism of `preadditiveCoyoneda` functors.** For an
adjunction `F ⊣ G` between preadditive categories with the same morphism universe and with `F`
additive, `Hom(Y, G -)` is isomorphic to `Hom(F Y, -)`.

This is the covariant counterpart of Mathlib's `Adjunction.compPreadditiveYonedaIso`, which moves
the object and so needs universe lifting; here the two hom-universes already agree. -/
def compPreadditiveCoyonedaIso (adj : F ⊣ G) [F.Additive] (Y : B) :
    G ⋙ preadditiveCoyoneda.obj (op Y) ≅ preadditiveCoyoneda.obj (op (F.obj Y)) :=
  NatIso.ofComponents (fun Z => (adj.homAddEquiv Y Z).symm.toAddCommGrpIso)
    (fun {_ _} g => by ext f; exact adj.homEquiv_naturality_right_symm f g)

/-- **`Ext` out of the image of a left adjoint, Stacks 015Z for `Ext`.** Let `F ⊣ G` be an
adjunction between abelian categories with `F` additive, and suppose the right adjoint `G` is
right exact and preserves injective objects. Then for `Y` in the source of `F`,

  `Ext_A^n(F Y, -) ≅ G ⋙ Ext_B^n(Y, -)`.

The left exactness of `G` needs no hypothesis: it is a right adjoint. This is the engine of the
localization comparisons of Stacks 03F3 and 07A0, where `F = j_!` is extension by zero, `G = j⁻¹`
is the inverse image, and `Y` is the unit coefficient object of the localized site. -/
@[sga "4 V 2.2" "more general"]
def extFunctorObjIsoCompOfAdjunction (adj : F ⊣ G) [F.Additive] [PreservesFiniteColimits G]
    [G.PreservesInjectiveObjects] (Y : B) (n : ℕ) :
    extFunctorObj (F.obj Y) n ≅ G ⋙ extFunctorObj Y n :=
  have : G.Additive := adj.right_adjoint_additive
  have : G.IsRightAdjoint := adj.isRightAdjoint
  have : PreservesFiniteLimits G := inferInstance
  extFunctorObjIsoComp G (compPreadditiveCoyonedaIso adj Y) n

/-- **`Ext` out of an object identified with the image of a left adjoint.** The form in which
`extFunctorObjIsoCompOfAdjunction` is used: the object `X` whose `Ext` is wanted is given only up
to isomorphism with `F.obj Y`. -/
def extFunctorObjIsoCompOfIso (adj : F ⊣ G) [F.Additive] [PreservesFiniteColimits G]
    [G.PreservesInjectiveObjects] {Y : B} {X : A} (e : F.obj Y ≅ X) (n : ℕ) :
    extFunctorObj X n ≅ G ⋙ extFunctorObj Y n :=
  (extFunctor n).mapIso e.op ≪≫ extFunctorObjIsoCompOfAdjunction adj Y n

/-- **`Ext` out of the image of a left adjoint, from acyclicity.** Let `F ⊣ G` be an adjunction
between abelian categories with `F` additive and `G` right exact, and let `Y` be an object of the
source of `F` such that `Ext^{≥1}(Y, G I)` vanishes for every injective `I`. Then

  `Ext_A^n(F Y, -) ≅ G ⋙ Ext_B^n(Y, -)`.

This is `Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfAdjunction` with preservation of
injective objects by `G` — which would force `F` to be exact — replaced by the vanishing it is
only ever used to produce. The two δ-functors `Ext_A^n(F Y, -)` and `G ⋙ Ext_B^n(Y, -)` on `A`
agree in degree zero by the adjunction and are both universal, the second by the hypothesis; the
extension to all degrees is `ModuleSheafCohomology.extComparisonIso`, i.e. Stacks 010T and
010U. -/
def extFunctorObjIsoCompOfAdjunctionOfAcyclic [EnoughInjectives A] (adj : F ⊣ G) [F.Additive]
    [PreservesFiniteColimits G] (Y : B)
    (h : ∀ (I : A) [Injective I] (n : ℕ) (e : Ext Y (G.obj I) (n + 1)), e = 0) (n : ℕ) :
    extFunctorObj (F.obj Y) n ≅ G ⋙ extFunctorObj Y n :=
  have : G.Additive := adj.right_adjoint_additive
  have : G.IsRightAdjoint := adj.isRightAdjoint
  have : PreservesFiniteLimits G := inferInstance
  ModuleSheafCohomology.extComparisonIso G Y (F.obj Y) h
    (compPreadditiveCoyonedaIso adj Y).symm n

/-- **`Ext` out of an object identified with the image of a left adjoint, from acyclicity.** The
form in which `extFunctorObjIsoCompOfAdjunctionOfAcyclic` is used: the object `X` whose `Ext` is
wanted is given only up to isomorphism with `F.obj Y`. -/
def extFunctorObjIsoCompOfIsoOfAcyclic [EnoughInjectives A] (adj : F ⊣ G) [F.Additive]
    [PreservesFiniteColimits G] {Y : B} {X : A} (e : F.obj Y ≅ X)
    (h : ∀ (I : A) [Injective I] (n : ℕ) (a : Ext Y (G.obj I) (n + 1)), a = 0) (n : ℕ) :
    extFunctorObj X n ≅ G ⋙ extFunctorObj Y n :=
  (extFunctor n).mapIso e.op ≪≫ extFunctorObjIsoCompOfAdjunctionOfAcyclic adj Y h n

end Adjunction

end Stacks.Cohomology.ExtComparison

end
