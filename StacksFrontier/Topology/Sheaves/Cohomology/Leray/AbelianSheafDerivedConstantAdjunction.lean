module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Sites.Sheafification.ConstantAbelianSheaf
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianSheavesOnSpace
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived constant sheaf is left adjoint to the unbounded derived global sections

Let `X` be a topological space and `AbelianSheaf X` the abelian sheaves on its open-cover site.
This file constructs the two functors

`Lπ^{-1} : D(Ab) ⥤ D(AbelianSheaf X)` and `RΓ(X, -) : D(AbelianSheaf X) ⥤ D(Ab)`

on the *unbounded* derived categories and proves that the first is left adjoint to the second.
The left adjoint is the constant sheaf functor promoted by
`CategoryTheory.Functor.mapDerivedCategory`, which applies because the constant sheaf functor is
exact; the right adjoint is the total right derived functor of the global sections, which exists
because the abelian sheaves on a space form a Grothendieck abelian category and therefore admit
K-injective resolutions of unbounded complexes.

## Main definitions

* `Stacks.Cohomology.Leray.derivedSectionsUnbounded`: **`RΓ(U, -)` on the unbounded derived
  category of abelian sheaves**, the total right derived functor of the sections over `U`
  followed by the localization, together with its unit
  `Stacks.Cohomology.Leray.derivedSectionsUnboundedUnit`.
* `Stacks.Cohomology.Leray.derivedConstantAbelianSheaf`: **`Lπ^{-1}` on the unbounded derived
  categories**, the constant sheaf functor promoted to derived categories, with the
  factorization `Stacks.Cohomology.Leray.derivedConstantAbelianSheafFactors` through the
  degreewise functor.

## Main results

* `Stacks.Cohomology.Leray.derivedConstantAbelianSheafAdjunction`: **the derived adjunction
  `Lπ^{-1} ⊣ RΓ(X, -)`** on the unbounded derived categories.
* `Stacks.Cohomology.Leray.derivedConstantAbelianSheafAdjunction_unit_fac`: the unit of the
  derived adjunction at the class of a complex `K` is the class of the degreewise unit
  `K ⟶ Γ(X, π^{-1}K)` followed by the comparison map of the derived global sections.

## Implementation notes

The right adjoint is stated for the sections over an arbitrary open `U`, since nothing in its
construction uses `U = ⊤`; the adjunction is the case `U = ⊤`, where the sections functor is the
right adjoint of the constant sheaf functor because `⊤` is the terminal object of `Opens X`.

The functor `Γ(X, -)` is not exact, so `CategoryTheory.Adjunction.mapDerivedCategory` does not
apply. The adjunction is obtained from `CategoryTheory.Adjunction.derived` applied to the
degreewise adjunction `CategoryTheory.Adjunction.mapHomologicalComplexAdjunction` of
`CategoryTheory.constantSheafAdj` at the terminal open, with the localizations taken at the
cochain complexes. This requires that both functors be derived functors of the composites with
the localizations, and that the composites `Lπ^{-1} ⋙ RΓ` and `RΓ ⋙ Lπ^{-1}` be derived functors
as well. Three of these hold because the comparison map is invertible, the constant sheaf functor
being exact; the fourth is the K-injective criterion
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`
applied to `RΓ` followed by an arbitrary functor.

The two exactness properties of the constant sheaf functor, `constantSheaf_preservesFiniteLimits`
and `constantSheaf_preservesFiniteColimits`, are theorems rather than instances, and are made
local instances here.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.Leray

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] constantSheaf_preservesFiniteLimits
  constantSheaf_preservesFiniteColimits

open Stacks.Injectives.KInjectiveResolution

variable (X : TopCat.{u})

/-! ### The unbounded derived global sections -/

/-- **The global sections over `U` on cochain complexes, followed by the localization to
`D(Ab)`, has a right derived functor** on the whole unbounded derived category of abelian
sheaves. The abelian sheaves on a space are a Grothendieck abelian category, so every cochain
complex of them receives a quasi-isomorphism into a K-injective one, and that is all the
criterion
`Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q`
needs. -/
instance hasRightDerivedFunctor_sectionsFunctor_comp_Q (U : Opens X) :
    ((sectionsFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (AbelianSheaf X) (ComplexShape.up ℤ)) :=
  hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (sectionsFunctor X U)

/-- **`RΓ(U, -) : D(AbelianSheaf X) ⥤ D(Ab)` on the unbounded derived category.** This is the
total right derived functor of the sections over `U` on cochain complexes followed by the
localization, along the localization `DerivedCategory.Q` of the abelian sheaves.

It is not the restriction of a functor defined by applying `Γ(U, -)` degreewise: the global
sections are left exact and not exact, so `CategoryTheory.Functor.mapDerivedCategory` does not
apply to them. The bounded below derived sections
`CategoryTheory.Functor.rightDerivedFunctorPlus` of `sectionsFunctor X U` is the restriction of
this one to the bounded below complexes in the sense that both are right derived functors of the
same functor; no such comparison is proved here. -/
@[sga "4 XVII 1.2.3" "(i), special case", sga "4½ Etat_0 4.1.3" "special case"]
def derivedSectionsUnbounded (U : Opens X) :
    DerivedCategory (AbelianSheaf X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  ((sectionsFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (AbelianSheaf X) (ComplexShape.up ℤ))

/-- **The unit of the unbounded derived global sections**: the comparison map
`Γ(U, K) ⟶ RΓ(U, K)` in `D(Ab)`, natural in the cochain complex `K` of abelian sheaves. It is
invertible at every K-injective complex, by
`Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective`. -/
def derivedSectionsUnboundedUnit (U : Opens X) :
    (sectionsFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedSectionsUnbounded X U :=
  ((sectionsFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (AbelianSheaf X) (ComplexShape.up ℤ))

/-- `RΓ(U, -)` is a right derived functor of the sections over `U` followed by the localization,
with unit `derivedSectionsUnboundedUnit X U`, with respect to the quasi-isomorphisms. -/
instance isRightDerivedFunctor_derivedSectionsUnbounded (U : Opens X) :
    (derivedSectionsUnbounded X U).IsRightDerivedFunctor (derivedSectionsUnboundedUnit X U)
      (HomologicalComplex.quasiIso (AbelianSheaf X) (ComplexShape.up ℤ)) :=
  inferInstanceAs (Functor.IsRightDerivedFunctor _
    (Functor.totalRightDerivedUnit _ _ _) _)

/-! ### The derived constant sheaf -/

/-- **`Lπ^{-1} : D(Ab) ⥤ D(AbelianSheaf X)`**, the constant sheaf functor promoted to the
unbounded derived categories. The constant sheaf functor is exact — it preserves finite limits by
`constantSheaf_preservesFiniteLimits` and finite colimits by
`constantSheaf_preservesFiniteColimits` — so `CategoryTheory.Functor.mapDerivedCategory` applies
to it, and no derivation is needed: it is its own left and right derived functor. -/
def derivedConstantAbelianSheaf :
    DerivedCategory AddCommGrpCat.{u} ⥤ DerivedCategory (AbelianSheaf X) :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapDerivedCategory

/-- **The derived constant sheaf is induced by the degreewise one**: the comparison between
applying the constant sheaf functor degreewise and then localizing, and localizing and then
applying the derived functor, is invertible. -/
def derivedConstantAbelianSheafFactors :
    DerivedCategory.Q ⋙ derivedConstantAbelianSheaf X ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapDerivedCategoryFactors

/-- `Lπ^{-1}` is a left derived functor of the degreewise constant sheaf functor followed by the
localization, with comparison map `(derivedConstantAbelianSheafFactors X).hom`, with respect to
the quasi-isomorphisms. -/
instance isLeftDerivedFunctor_derivedConstantAbelianSheaf :
    (derivedConstantAbelianSheaf X).IsLeftDerivedFunctor
      (derivedConstantAbelianSheafFactors X).hom
      (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ (derivedConstantAbelianSheafFactors X)

/-! ### The two composites are derived functors -/

/-- The global sections on cochain complexes followed by the localization and then by any functor
inverts the quasi-isomorphisms between K-injective complexes, because the first two steps already
do. -/
private lemma invertsQuasiIso_sections_comp_Q_comp {D : Type*} [Category D] (U : Opens X)
    (T : DerivedCategory AddCommGrpCat.{u} ⥤ D) :
    InvertsQuasiIsoOfIsKInjective
      ((sectionsFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⋙ T) := by
  intro K L f hK hL hf
  have := invertsQuasiIso_mapHomologicalComplex_comp_Q (sectionsFunctor X U) f hK hL hf
  exact inferInstanceAs (IsIso (T.map
    (((sectionsFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).map f)))

/-- **The composite `Lπ^{-1} ⋙ RΓ` is a left derived functor**, with the comparison map induced
by the one of `Lπ^{-1}`: that comparison is invertible, so there is nothing to derive. -/
instance isLeftDerivedFunctor_derivedConstantAbelianSheaf_comp :
    (derivedConstantAbelianSheaf X ⋙ derivedSectionsUnbounded X ⊤).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        (derivedConstantAbelianSheafFactors X).hom (derivedSectionsUnbounded X ⊤))
      (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    (asIso ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
      (derivedConstantAbelianSheafFactors X).hom (derivedSectionsUnbounded X ⊤)))

/-- **The composite `RΓ ⋙ Lπ^{-1}` is a right derived functor**, with the comparison map induced
by the unit of `RΓ`. By the K-injective criterion it suffices that the comparison be invertible
at every K-injective complex, and there it is the image under `Lπ^{-1}` of the unit of `RΓ`,
which is invertible. -/
instance isRightDerivedFunctor_derivedSectionsUnbounded_comp :
    (derivedSectionsUnbounded X ⊤ ⋙ derivedConstantAbelianSheaf X).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedSectionsUnboundedUnit X ⊤) (derivedConstantAbelianSheaf X) ≫
        (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso (AbelianSheaf X) (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective (L := DerivedCategory.Q) _ _
    (invertsQuasiIso_sections_comp_Q_comp X ⊤ (derivedConstantAbelianSheaf X))]
  intro K hK
  have := isIso_app_of_isKInjective DerivedCategory.Q (derivedSectionsUnbounded X ⊤)
    (derivedSectionsUnboundedUnit X ⊤)
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (sectionsFunctor X ⊤)) K hK
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id]
  exact Functor.map_isIso _ _

/-! ### The derived adjunction -/

/-- **The derived constant sheaf is left adjoint to the unbounded derived global sections**,

`Lπ^{-1} ⊣ RΓ(X, -)` on `D(Ab) ⇄ D(AbelianSheaf X)`,

obtained by deriving the degreewise adjunction of Mathlib's `CategoryTheory.constantSheafAdj` at
the terminal open `⊤`. The right adjoint is not exact and is not claimed to be; only the left one
is, and `CategoryTheory.Adjunction.derived` asks exactness of neither. -/
def derivedConstantAbelianSheafAdjunction :
    derivedConstantAbelianSheaf X ⊣ derivedSectionsUnbounded X ⊤ :=
  (Adjunction.mapHomologicalComplexAdjunction
      (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        (T := (⊤ : Opens X)) isTerminalTop) (ComplexShape.up ℤ)).derived
    (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso (AbelianSheaf X) (ComplexShape.up ℤ))
    (derivedConstantAbelianSheafFactors X).hom (derivedSectionsUnboundedUnit X ⊤)

/-- **The unit of the derived adjunction on the class of a complex** `K` of abelian groups is the
class of the degreewise unit `K ⟶ Γ(X, π^{-1}K)` followed by the comparison map of the derived
global sections, read through the factorization of the derived constant sheaf. -/
theorem derivedConstantAbelianSheafAdjunction_unit_fac
    (K : CochainComplex AddCommGrpCat.{u} ℤ) :
    (derivedConstantAbelianSheafAdjunction X).unit.app (DerivedCategory.Q.obj K) ≫
        (derivedSectionsUnbounded X ⊤).map
          ((derivedConstantAbelianSheafFactors X).hom.app K) =
      DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
          (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
            (T := (⊤ : Opens X)) isTerminalTop) (ComplexShape.up ℤ)).unit.app K) ≫
        (derivedSectionsUnboundedUnit X ⊤).app
          (((constantSheaf (Opens.grothendieckTopology X)
            AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Adjunction.derivedη_fac_app _
    (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.up ℤ))
    (derivedConstantAbelianSheafFactors X).hom (derivedSectionsUnboundedUnit X ⊤) K

end Stacks.Cohomology.Leray

end
