module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unbounded derived category of abelian sheaves on a small étale site

The étale cohomology of this library is developed on bounded below derived categories, through
`CategoryTheory.Functor.rightDerivedFunctorPlus`. Several constructions in the étale theory are
however stated on the *unbounded* derived category `D(X_étale)` of abelian sheaves on the small
étale site of a scheme, with unbounded derived global sections `RΓ(X, -)` and unbounded derived
inverse image as its basic functors. This file introduces those three.

Unbounded derived global sections are the total right derived functor of the global sections
functor, taken on the localization of the homotopy category of cochain complexes; the existence
of that derivation is an instance argument here, as for
`AlgebraicGeometry.Stack.derivedGlobalSections` on the fppf site, so that this file depends only
on the site itself. It is not a hypothesis of the theory:
`Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor` discharges it for
every scheme, abelian sheaves on a small étale site being a Grothendieck abelian category and
hence having unbounded K-injective resolutions. Derived inverse image and the derived stalk at a
geometric point need no such hypothesis at all, both functors being exact, so each acts on
unbounded derived categories degreewise through
`CategoryTheory.Functor.mapDerivedCategory`.

The file also provides the descent construction those three are used with. A natural
transformation `τ : F ⟶ G ⋙ H` out of an *exact* functor `F` extends canonically to the derived
categories, as a transformation `F.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ RH` into the
composite of the degreewise action of `G` with a right derived functor of `H`: the degreewise
action of an exact functor is a right derived functor of itself, so the extension is the unique
one factoring the degreewise comparison through the unit of `RH`. This is what produces a
canonical map out of a derived stalk, and it is why the hypotheses on `F` and `G` are exactness
while `H` is only additive.

## Main definitions

* `Stacks.DerivedFunctor.mapHomotopyCategoryOfComp` — the degreewise action of a natural
  transformation `F ⟶ G ⋙ H` on homotopy categories, landing in the composite of the degreewise
  actions of `G` and `H`.
* `Stacks.DerivedFunctor.exactDerivedDescUnit` — the comparison it induces on the homotopy
  category of the source, after the unit of a right derived functor of `H`.
* `Stacks.DerivedFunctor.exactDerivedDesc` — the induced transformation
  `F.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ RH` on unbounded derived categories.
* `Stacks.EtaleCohomology.smallEtaleDerivedCategory` — the unbounded derived category
  `D(X_étale)` of abelian sheaves on the small étale site of a scheme.
* `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections` and
  `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsUnit` — unbounded derived global
  sections `RΓ(X, -)` on the small étale site, and the unit of that derivation.
* `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAb` — unbounded derived inverse image along a
  morphism of schemes, the degreewise action of the exact functor
  `Stacks.EtaleCohomology.smallEtalePullbackAb`.
* `Stacks.EtaleCohomology.smallEtaleStalkAb` and
  `Stacks.EtaleCohomology.smallEtaleDerivedStalkAb` — the stalk of an abelian étale sheaf at a
  geometric point, and its degreewise action on unbounded derived categories.

## Main results

* `Stacks.DerivedFunctor.isRightDerivedFunctor_mapDerivedCategory` — the degreewise action of an
  exact functor on unbounded derived categories is a right derived functor of that action on
  homotopy categories, because it inverts quasi-isomorphisms.
* `Stacks.DerivedFunctor.exactDerivedDesc_fac_app` — the induced transformation on derived
  categories factors the degreewise comparison through the unit of `RH` on every complex, which
  determines it.

## References

* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.DerivedFunctor

/-! ### Descending a transformation out of an exact functor to unbounded derived categories -/

section Descent

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂] [HasDerivedCategory.{w₂} A₂]
  {A₃ : Type u₃} [Category.{v₃} A₃] [Abelian A₃] [HasDerivedCategory.{w₃} A₃]
  (F : A₁ ⥤ A₃) [F.Additive] (G : A₁ ⥤ A₂) [G.Additive] (H : A₂ ⥤ A₃) [H.Additive]

/-- The degreewise action on homotopy categories of a natural transformation `τ : F ⟶ G ⋙ H`
between additive functors, landing in the composite of the degreewise actions of `G` and of `H`:
the degreewise action of `τ` itself, read through the comparison of the action of a composite
with the composite of the actions. -/
def mapHomotopyCategoryOfComp (τ : F ⟶ G ⋙ H) :
    F.mapHomotopyCategory (.up ℤ) ⟶
      G.mapHomotopyCategory (.up ℤ) ⋙ H.mapHomotopyCategory (.up ℤ) :=
  NatTrans.mapHomotopyCategory τ (.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ H)) (.up ℤ)).inv

section

variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (RH : DerivedCategory A₂ ⥤ DerivedCategory A₃)
  (η : H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
  (τ : F ⟶ G ⋙ H)

/-- The comparison on the homotopy category of the source induced by `τ : F ⟶ G ⋙ H` and the
unit `η` of a right derived functor `RH` of `H`: apply `τ` degreewise, pass to the derived
category by `η`, and identify the degreewise action of `G` with its action on the derived
category. -/
def exactDerivedDescUnit :
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ G.mapDerivedCategory ⋙ RH :=
  Functor.whiskerRight (mapHomotopyCategoryOfComp F G H τ) DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (G.mapHomotopyCategory (.up ℤ)) η ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight G.mapDerivedCategoryFactorsh.inv RH ≫
    (Functor.associator _ _ _).hom

/-- On a complex, the comparison induced by `τ` and `η` is the degreewise action of `τ`, followed
by `η` and by the identification of the two actions of `G`. -/
theorem exactDerivedDescUnit_app (J : HomotopyCategory A₁ (.up ℤ)) :
    (exactDerivedDescUnit F G H RH η τ).app J =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp F G H τ).app J) ≫
        η.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
          RH.map (G.mapDerivedCategoryFactorsh.inv.app J) := by
  simp [exactDerivedDescUnit]

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The degreewise action of an exact functor on unbounded derived categories is a right derived
functor of its action on homotopy categories: that action inverts quasi-isomorphisms, the
witness being the identification of the two actions. -/
instance isRightDerivedFunctor_mapDerivedCategory :
    F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso A₁ (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh

/-- The transformation on unbounded derived categories induced by `τ : F ⟶ G ⋙ H` out of an
exact functor `F`, along the unit `η` of a right derived functor `RH` of `H`: the unique
transformation `F.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ RH` whose composite with the
identification of the two actions of `F` is the comparison `exactDerivedDescUnit`. -/
def exactDerivedDesc : F.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ RH :=
  F.mapDerivedCategory.rightDerivedDesc F.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso A₁ (.up ℤ)) (G.mapDerivedCategory ⋙ RH)
    (exactDerivedDescUnit F G H RH η τ)

/-- The transformation induced on unbounded derived categories factors the degreewise action of
`τ` through the unit of `RH` on every complex. Since the degreewise action of `F` is a right
derived functor of itself, this property determines the transformation. -/
theorem exactDerivedDesc_fac_app (J : HomotopyCategory A₁ (.up ℤ)) :
    F.mapDerivedCategoryFactorsh.inv.app J ≫
        (exactDerivedDesc F G H RH η τ).app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp F G H τ).app J) ≫
        η.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
          RH.map (G.mapDerivedCategoryFactorsh.inv.app J) := by
  rw [← exactDerivedDescUnit_app]
  exact F.mapDerivedCategory.rightDerived_fac_app F.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso A₁ (.up ℤ)) (G.mapDerivedCategory ⋙ RH)
    (exactDerivedDescUnit F G H RH η τ) J

end

end Descent

end Stacks.DerivedFunctor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The unbounded derived category of abelian sheaves on a small étale site -/

/-- The unbounded derived category `D(X_étale)` of abelian sheaves on the small étale site of a
scheme `X`, with coefficients in the universe in which étale cohomology of `X` is computed. -/
abbrev smallEtaleDerivedCategory (X : Scheme.{u}) :=
  DerivedCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1})

/-- Global sections of abelian sheaves on a small étale site form an additive functor: it is a
right adjoint, so it preserves binary products. -/
instance smallEtaleGlobalSectionsAb_additive (X : Scheme.{u}) :
    (Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Unbounded derived global sections `RΓ(X, -)` of abelian sheaves on the small étale site: the
total right derived functor of global sections, on the localization of the homotopy category of
cochain complexes at the quasi-isomorphisms. -/
abbrev smallEtaleDerivedGlobalSections (X : Scheme.{u})
    [((Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))] :
    smallEtaleDerivedCategory X ⥤ DerivedCategory Ab.{u + 1} :=
  ((Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))

/-- The unit of the derivation of global sections on the small étale site: the comparison from
degreewise global sections of a complex to its unbounded derived global sections. -/
abbrev smallEtaleDerivedGlobalSectionsUnit (X : Scheme.{u})
    [((Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))] :
    (Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ smallEtaleDerivedGlobalSections X :=
  ((Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))

/-- Unbounded derived inverse image of abelian sheaves on the small étale sites along
`f : X ⟶ Y`: inverse image is exact, so it acts on unbounded derived categories degreewise. -/
@[sga "7 XIII 2.1.6"]
abbrev smallEtaleDerivedPullbackAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleDerivedCategory Y ⥤ smallEtaleDerivedCategory X :=
  (smallEtalePullbackAb f).mapDerivedCategory

/-! ### The stalk of an abelian étale sheaf at a geometric point -/

section Stalk

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)

/-- The stalk `F ↦ F_x` of an abelian sheaf on the small étale site of `X` at the point of that
site determined by a geometric point `x` of `X`: the filtered colimit of the sections of `F` over
the étale neighbourhoods of `x`. -/
abbrev smallEtaleStalkAb : Sheaf (smallEtaleTopology X) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  (Scheme.pointSmallEtale x).sheafFiber (A := Ab.{u + 1})

/-- The stalk at a geometric point preserves finite limits: the category of étale neighbourhoods
of the point is cofiltered, and abelian groups satisfy AB5 in every universe they are large
enough for. -/
instance smallEtaleStalkAb_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleStalkAb x) := by
  let : AB5OfSize.{u, u} Ab.{u + 1} := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  infer_instance

/-- The stalk at a geometric point preserves finite colimits, being a left adjoint. -/
instance smallEtaleStalkAb_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleStalkAb x) :=
  inferInstance

/-- The stalk at a geometric point is an additive functor, being exact. -/
instance smallEtaleStalkAb_additive : (smallEtaleStalkAb x).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The stalk at a geometric point on unbounded derived categories, `K ↦ K_x`: the stalk functor
is exact, so it acts degreewise. -/
abbrev smallEtaleDerivedStalkAb :
    smallEtaleDerivedCategory X ⥤ DerivedCategory Ab.{u + 1} :=
  (smallEtaleStalkAb x).mapDerivedCategory

end Stalk

end Stacks.EtaleCohomology

end
