module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupportDetection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedGlobalSectionsExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedAlongEquivalence

/-!
# The bounded small étale site of Stacks 021B and Mathlib's small étale site

Let `B` be a big étale site containing a scheme `X`. The library carries two small étale sites
of `X`: the bounded one `AlgebraicGeometry.SmallEtale.topology B X hX` of Stacks 021B, on which
for instance [Stacks, Tag 0F1G] is stated, and Mathlib's `X.smallEtaleTopology`, on which the
inverse and direct images, the base change maps and the derived categories `D(X_étale, Λ)` of
the étale cohomology chapter are built. The embedding `AlgebraicGeometry.SmallEtale.toEtaleSite`
is a dense subsite (`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`), so the two sheaf
categories are equivalent (`AlgebraicGeometry.SmallEtale.sheafEquiv`). This file carries across
that equivalence the three things a statement on one site needs in order to be read on the
other:

* the **derived categories**: an equivalence of abelian categories induces one of the unbounded
  derived categories, in either direction;
* the **stalks** at a geometric point `s`: the stalk `etaleStalk B X hX s` of [Stacks, Tag 040R]
  on the bounded site is the stalk of Mathlib's point `Scheme.pointSmallEtale s.hom`, for sheaves
  with values in any category with enough limits and colimits, and so also for the cohomology
  sheaves of a complex;
* the **derived global sections**: global sections on the bounded site are sections over its
  final object `X / X`, which the embedding sends to a terminal object of `X.Etale`, so global
  sections agree; their unbounded derived functors then agree by the transport of a right
  derived functor along an equivalence (`Stacks.Injectives.totalRightDerivedPrecompIso`), and so
  do all hypercohomology groups.

## Main definitions

* `AlgebraicGeometry.SmallEtale.derivedSheafEquiv` — `D(Sh(B-site)) ≌ D(Sh(X_étale))`.
* `AlgebraicGeometry.SmallEtale.sheafEquivFunctorCompSheafFiberIso` — the stalk functor of
  `Scheme.pointSmallEtale s.hom`, read through `sheafEquiv`, is the stalk functor of the bounded
  site at `s`.
* `AlgebraicGeometry.SmallEtale.etaleStalkSheafEquivInverseIso` — the stalk of
  [Stacks, Tag 040R] of the restriction of a sheaf on `X_étale` is its stalk at
  `Scheme.pointSmallEtale s.hom`.
* `AlgebraicGeometry.SmallEtale.etaleStalkHomologyIso` — the same for the cohomology sheaves of
  an object of `D(X_étale)` and of its image in `D(Sh(B-site))`.
* `AlgebraicGeometry.SmallEtale.sheafEquivInverseCompΓIso` — global sections agree.
* `AlgebraicGeometry.SmallEtale.smallEtaleDerivedGlobalSectionsIso` —
  `RΓ(X_étale, -) ≅ RΓ(B-site, -) ∘ (restriction)` on unbounded derived categories.
* `AlgebraicGeometry.SmallEtale.hypercohomologyIso` — the hypercohomology groups agree.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_iff_forall_isZero_hypercohomology_of_closedPointSupport`
  — [Stacks, Tag 0F1G] for an object of `D(X_étale)` on Mathlib's small étale site, with the
  stalks taken at Mathlib's points and the hypercohomology of
  `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections`.

## Implementation notes

The derived equivalences are stated for any choice of derived categories. The derived global
sections are the two total right derived functors of the base,
`AlgebraicGeometry.smallEtaleDerivedGlobalSectionsAb` and
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections`, which are formed for the standard
model; that fixes the model in the last section only.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
* [Stacks Project, Tag 0F1G](https://stacks.math.columbia.edu/tag/0F1G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v' u' u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-! ### Stalks at a geometric point -/

section Stalks

variable (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A] [HasColimitsOfSize.{u, u} A]
  (s : GeometricPoint X)

/-- **The stalk functor of Mathlib's point of `X_étale` at a geometric point, read through the
identification `sheafEquiv` of the two sheaf categories, is the stalk functor of the bounded
site at that point**, for sheaves with values in any category with enough limits and
colimits. -/
def sheafEquivFunctorCompSheafFiberIso :
    (sheafEquiv B X hX A).functor ⋙ (Scheme.pointSmallEtale s.hom).sheafFiber ≅
      (geometricPointSitePoint B X hX s).sheafFiber :=
  sheafFiberIsoOfAdjOfFiberIso (geometricPointSitePoint B X hX s)
    (Scheme.pointSmallEtale s.hom) (toEtaleSite B X hX) (toEtaleSiteFiberIso B X hX s)
    (sheafEquiv B X hX A).toAdjunction

/-- **The stalk of [Stacks, Tag 040R] of a sheaf on the bounded site is the stalk at
`Scheme.pointSmallEtale s.hom` of the corresponding sheaf on `X_étale`.** -/
def etaleStalkIsoSheafFiber (F : Sheaf (topology B X hX) A) :
    etaleStalk B X hX s F.obj ≅
      (Scheme.pointSmallEtale s.hom).sheafFiber.obj ((sheafEquiv B X hX A).functor.obj F) :=
  ((sheafEquivFunctorCompSheafFiberIso B X hX A s).app F).symm

/-- **The stalk of [Stacks, Tag 040R] of the restriction of a sheaf on `X_étale` to the bounded
site is its stalk at `Scheme.pointSmallEtale s.hom`.** -/
def etaleStalkSheafEquivInverseIso (F : Sheaf X.smallEtaleTopology A) :
    etaleStalk B X hX s ((sheafEquiv B X hX A).inverse.obj F).obj ≅
      (Scheme.pointSmallEtale s.hom).sheafFiber.obj F :=
  etaleStalkIsoSheafFiber B X hX A s _ ≪≫
    (Scheme.pointSmallEtale s.hom).sheafFiber.mapIso ((sheafEquiv B X hX A).counitIso.app F)

end Stalks

/-! ### Derived categories -/

section Derived

/-- The functor `Sh(B-site) ⥤ Sh(X_étale)` of `sheafEquiv` on abelian sheaves is additive. -/
instance sheafEquiv_functor_additive :
    (sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The restriction functor `Sh(X_étale) ⥤ Sh(B-site)` of `sheafEquiv` on abelian sheaves is
additive. -/
instance sheafEquiv_inverse_additive :
    (sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

variable [HasDerivedCategory (Sheaf (topology B X hX) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The unbounded derived categories of abelian sheaves on the two small étale sites are
equivalent**, through the equivalence `sheafEquiv` applied degreewise. -/
def derivedSheafEquiv :
    DerivedCategory (Sheaf (topology B X hX) AddCommGrpCat.{u + 1}) ≌
      DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  have := Stacks.DerivedCategory.mapDerivedCategory_isEquivalence
    (sheafEquiv B X hX AddCommGrpCat.{u + 1})
  (sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.mapDerivedCategory.asEquivalence

/-- The functor of `derivedSheafEquiv` is the functor of `sheafEquiv` applied degreewise. -/
@[simp]
theorem derivedSheafEquiv_functor :
    (derivedSheafEquiv B X hX).functor =
      (sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.mapDerivedCategory :=
  rfl

/-- Restriction to the bounded site, applied degreewise, is an equivalence of unbounded derived
categories. -/
instance isEquivalence_sheafEquiv_inverse_mapDerivedCategory :
    (sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.mapDerivedCategory.IsEquivalence :=
  have : (sheafEquiv B X hX AddCommGrpCat.{u + 1}).symm.functor.Additive :=
    sheafEquiv_inverse_additive B X hX
  Stacks.DerivedCategory.mapDerivedCategory_isEquivalence
    (sheafEquiv B X hX AddCommGrpCat.{u + 1}).symm

/-- **The cohomology sheaves of the restriction of a complex are the restrictions of its
cohomology sheaves**: restriction is exact. -/
def homologySheafEquivInverseIso (q : ℤ)
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (DerivedCategory.homologyFunctor (Sheaf (topology B X hX) AddCommGrpCat.{u + 1}) q).obj
        ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.mapDerivedCategory.obj Q) ≅
      (sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.obj
        ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          Q) :=
  (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
    (sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse q).app Q

/-- **The geometric stalks of the cohomology sheaves of the restriction of an object `Q` of
`D(X_étale)` to the bounded site are the stalks of the cohomology sheaves of `Q` at Mathlib's
points.** -/
def etaleStalkHomologyIso (s : GeometricPoint X) (q : ℤ)
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    etaleStalk B X hX s
        ((DerivedCategory.homologyFunctor (Sheaf (topology B X hX) AddCommGrpCat.{u + 1}) q).obj
          ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.mapDerivedCategory.obj Q)).obj ≅
      (Scheme.pointSmallEtale s.hom).sheafFiber.obj
        ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          Q) :=
  (geometricPointSitePoint B X hX s).sheafFiber.mapIso (homologySheafEquivInverseIso B X hX q Q) ≪≫
    etaleStalkSheafEquivInverseIso B X hX AddCommGrpCat.{u + 1} s _

/-- An object of `D(X_étale)` vanishes exactly when its restriction to the bounded site does. -/
theorem isZero_sheafEquiv_inverse_mapDerivedCategory_obj_iff
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsZero ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.mapDerivedCategory.obj Q) ↔
      IsZero Q :=
  ⟨fun h => (Functor.map_isZero
      (sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.mapDerivedCategory.asEquivalence.inverse
      h).of_iso
      ((sheafEquiv B X hX
        AddCommGrpCat.{u + 1}).inverse.mapDerivedCategory.asEquivalence.unitIso.app Q),
    fun h => Functor.map_isZero _ h⟩

end Derived

/-! ### Global sections and derived global sections -/

section GlobalSections

/-- **Global sections on `X_étale` are global sections on the bounded site after restriction.** -/
def sheafEquivInverseCompΓIso :
    (sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse ⋙
        Sheaf.Γ (topology B X hX) AddCommGrpCat.{u + 1} ≅
      Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft _ (smallEtaleΓNatIsoSectionsAtFinal.{u, u + 1} B X hX) ≪≫
    (Stacks.Cohomology.ΓNatIsoSectionsAtTerminal _ _ (isTerminalToEtaleSiteFinal B X hX)).symm

/-- The global sections functor on abelian sheaves on the bounded site is additive. -/
instance : (Sheaf.Γ (topology B X hX) AddCommGrpCat.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The global sections functor on abelian sheaves on `X_étale` is additive. -/
instance : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_succ
open Stacks.EtaleCohomology in
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Unbounded derived global sections on `X_étale` are unbounded derived global sections on the
bounded site, after restriction.** -/
def smallEtaleDerivedGlobalSectionsIso :
    Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections X ≅
      (sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.mapDerivedCategory ⋙
        smallEtaleDerivedGlobalSectionsAb.{u, u + 1} B X hX :=
  Functor.rightDerivedNatIso _ _
      (Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsUnit X)
      (((sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
            smallEtaleHomotopyGlobalSectionsAb.{u, u + 1} B X hX).totalRightDerivedUnit
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso (sheafEquivInverseCompΓIso B X hX)
          (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫ Functor.associator _ _ _) ≪≫
    Stacks.Injectives.totalRightDerivedPrecompIso
      (sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse
      (smallEtaleHomotopyGlobalSectionsAb.{u, u + 1} B X hX)
      (smallEtaleDerivedGlobalSectionsAb.{u, u + 1} B X hX)
      ((smallEtaleHomotopyGlobalSectionsAb.{u, u + 1} B X hX).totalRightDerivedUnit
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf (topology B X hX) AddCommGrpCat.{u + 1})
          (ComplexShape.up ℤ)))

/-- **The hypercohomology groups `H^q(X_étale, Q)` are those of the restriction of `Q` to the
bounded site**, in every degree and for every object of the unbounded derived category. -/
def hypercohomologyIso (q : ℤ)
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections X).obj Q) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((smallEtaleDerivedGlobalSectionsAb.{u, u + 1} B X hX).obj
          ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.mapDerivedCategory.obj Q)) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
    ((smallEtaleDerivedGlobalSectionsIso B X hX).app Q)

/-- **[Stacks, Tag 0F1G] read on Mathlib's small étale site.** Let `K` be a separably closed
field, `X` a scheme of finite type over `K` and `Q` an object of the unbounded derived category of
abelian sheaves on `X.smallEtaleTopology` whose cohomology sheaves have vanishing stalks at the
geometric points of `X` lying over non-closed points. Then `Q` is zero if and only if all its
hypercohomology groups `H^q(X_étale, Q)` vanish. -/
theorem isZero_iff_forall_isZero_hypercohomology_of_closedPointSupport
    (K : Type u) [Field K] [IsSepClosed K] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hQ : ∀ (p : GeometricPoint X) (q : ℤ), ¬ IsClosed ({p.hom default} : Set X) →
      IsZero ((Scheme.pointSmallEtale p.hom).sheafFiber.obj
        ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          q).obj Q))) :
    IsZero Q ↔
      ∀ q : ℤ, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections X).obj Q)) := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  rw [← isZero_sheafEquiv_inverse_mapDerivedCategory_obj_iff B X hX,
    isZero_iff_forall_isZero_etaleHypercohomology_of_closedPointSupport B X hX K f _
      (fun p q hp => (hQ p q hp).of_iso (etaleStalkHomologyIso B X hX p q Q))]
  exact forall_congr' fun q => (hypercohomologyIso B X hX q Q).isZero_iff.symm

end GlobalSections

end AlgebraicGeometry.SmallEtale

end
