module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EvaluationRestrictionSquare

/-!
# The evaluation restriction square, with the derived functors removed

Let `(C, O)` be a ringed site and `g : U' ⟶ U` a morphism of `C`.  The naturality in the object of
the site of `Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso` is one of the two halves
of the restriction compatibility of
`Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyEvaluationIso`, hence an input of
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv`, hence of the
uniqueness clause of [Stacks, Tag 0D68].

`StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EvaluationRestrictionSquare`
reduced that square to the equation obtained by composing with the unit
`Stacks.Cohomology.HypercohomologyEdge.totalRightDerivedCompUnit` of the right derived functor the
two sides come out of.  That equation is still written with *two* right derived functors — the
derived sections over `U'` occur inside
`Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrict`, which is itself defined by
`CategoryTheory.Functor.rightDerivedDesc` — so it is not yet a statement about complexes.

This file removes all of them.  What is left,
`Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict_natTrans_of_homotopySquare`,
is a square between transformations out of a functor on the homotopy category in which no right
derived functor, no `rightDerivedDesc` and no unit occurs: only the underived comparison
`Stacks.Cohomology.HypercohomologyEdge.homotopySectionsEvaluationIso`, the termwise restriction
`Stacks.Cohomology.HypercohomologyEdge.homotopySectionsRestrict`, the homology comparison
`Stacks.Homology.derivedHomologyIso` of restriction of scalars, and the restriction map
`CategoryTheory.PresheafOfModules.restriction` of the presheaf of modules.

Three cancellations do it, and each is an equation the development already determines:

* the two `sectionsEvaluationIso`s are `CategoryTheory.Functor.rightDerivedNatIso` of
  `homotopySectionsEvaluationIso`, so each is pinned to its underived comparison by
  `CategoryTheory.Functor.rightDerivedNatTrans_fac` — this is `sectionsEvaluationIso_fac`;
* the derived restriction is pinned to the termwise one by
  `Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrict_fac`, and that survives being
  read on degree-`q` homology — `derivedSectionsRestrict_fac_homology`;
* the unit of derived sections over `U'` then occurs on both sides, once inside
  `Stacks.Cohomology.HypercohomologyEdge.sectionsRestrictUnit` and once inside the unit at `U'`,
  and the two are carried to one another by the *naturality of*
  `Stacks.Homology.derivedHomologyIso` — `derivedHomologyIso_totalRightDerivedUnit`.  This is the
  step at which the derived functors disappear rather than merely moving.

## Main definitions

All names below are in the namespace `Stacks.Cohomology.HypercohomologyEdge`.

* `homotopySectionsRestrict`: the termwise part of `sectionsRestrictUnit` — restriction of
  sections from `U` to `U'` on the homotopy category, with the derived unit removed.

## Main results

* `sectionsRestrictUnit_eq`: the prescribing transformation of the derived restriction is the
  termwise restriction followed by the derived unit.
* `sectionsEvaluationIso_restrict_natTrans_of_homotopySquare`: the transformation form of the
  evaluation restriction square follows from the unit-free square on the homotopy category.  The
  hypothesis is not discharged here, and it is what remains of this half of the square.
* `sectionsEvaluationIso_restrict_of_homotopySquare`: the object-wise square, the shape its
  consumer needs, from the same hypothesis.

## Implementation notes

*Every step is stated as its own lemma with the objects and morphisms variables, and applied by
`exact`.*  On these goals `rw` is unreliable: `rw [Category.assoc]` reports *no occurrence of the
pattern `(?f ≫ ?g) ≫ ?h`* on a goal whose right-hand side visibly contains one — the four-fold
composite of `sectionsRestrictUnit` — and rewriting `derivedSectionsRestrictHomology` underneath a
`Functor.whiskerLeft` is a 200000-heartbeat `whnf` timeout.  Both are cured the same way: the
reassociation is `comp_assoc4` and the diagram chase is `squares_chain`, each with every object
and morphism a variable, and the chase is run *object by object* after
`CategoryTheory.NatTrans.ext`, where the whiskering lemmas are ordinary `simp` lemmas.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.SiteCohomologyPresheaf

attribute [local instance] restrictScalars_preservesFiniteLimits
  restrictScalars_preservesFiniteColimits evaluation_additive

/-! ### Two diagram lemmas, stated with every object and morphism a variable -/

/-- Reassociation of a four-fold composite.  Stated with variables because `rw [Category.assoc]`
reports no occurrence of `(?f ≫ ?g) ≫ ?h` on the goal this is used for; see the implementation
notes.  It is not private: the same reassociation is needed for the Leray half of the layer-3
square, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayRestrictionHomotopySquare`. -/
theorem comp_assoc4 {X : Type*} [Category* X] {a b c d e : X}
    (f : a ⟶ b) (p : b ⟶ c) (h : c ⟶ d) (k : d ⟶ e) :
    f ≫ p ≫ h ≫ k = (f ≫ p ≫ h) ≫ k := by
  simp

/-- **The diagram chase behind the reduction.**  Two paths out of `a`: one through `eU`, `rho1`,
`rho2`, one through `q1`, `q2`.  Four commuting squares relate the two paths to a fifth equation
`hsq`, which is the one that is not formal.

Stated with every object and morphism a variable so that the chase is run once, in a category
where `Category.assoc` is available, rather than on the natural transformations themselves.

It is not private: the Leray half of the layer-3 square is reduced by the same chase. -/
theorem squares_chain {X : Type*} [Category* X] {x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ v₁ w₁ : X}
    {a : x₁ ⟶ x₂} {eU : x₂ ⟶ x₃} {rho1 : x₃ ⟶ x₄} {rho2 : x₄ ⟶ x₅}
    {hE : x₁ ⟶ y₁} {aS : y₁ ⟶ x₃} {dRes : y₁ ⟶ y₂} {unit : y₂ ⟶ x₄}
    {dh : y₂ ⟶ y₃} {aSR : y₃ ⟶ x₅} {q1 : x₂ ⟶ w₁} {q2 : w₁ ⟶ x₅}
    {r : x₁ ⟶ v₁} {b : v₁ ⟶ w₁} {hE' : v₁ ⟶ y₃}
    (h1 : a ≫ eU = hE ≫ aS) (h2 : aS ≫ rho1 = dRes ≫ unit)
    (h4 : unit ≫ rho2 = dh ≫ aSR) (h3 : a ≫ q1 = r ≫ b)
    (h5 : b ≫ q2 = hE' ≫ aSR) (hsq : hE ≫ dRes ≫ dh = r ≫ hE') :
    a ≫ eU ≫ rho1 ≫ rho2 = a ≫ q1 ≫ q2 := by
  rw [reassoc_of% h1, reassoc_of% h2, h4, reassoc_of% hsq, reassoc_of% h3, h5]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing}) [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]

/-! ### The termwise restriction, separated from the derived unit -/

/-- **Restriction of sections on the homotopy category.**  The termwise part of
`Stacks.Cohomology.HypercohomologyEdge.sectionsRestrictUnit`: restrict the complex of sections
over `U` to sections over `U'` degreewise, then compare the termwise image with the derived
action of restriction of scalars.  No right derived functor occurs. -/
def homotopySectionsRestrict {U U' : C} (g : U' ⟶ U) :
    homotopySections O U ⟶ homotopySections O U' ⋙ restrictScalarsDerived O g :=
  Functor.whiskerRight (NatTrans.mapHomotopyCategory (sectionsRestrict O g)
      (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (SheafOfModules.evaluation O (.op U') ⋙
        ModuleCat.restrictScalars (O.obj.map g.op).hom))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((SheafOfModules.evaluation O (.op U')).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars (O.obj.map g.op).hom).mapDerivedCategoryFactorsh.inv

/-- **The prescribing transformation of the derived restriction splits.**  The transformation
`Stacks.Cohomology.HypercohomologyEdge.sectionsRestrictUnit` through which
`derivedSectionsRestrict` is defined is the termwise restriction
`Stacks.Cohomology.HypercohomologyEdge.homotopySectionsRestrict` followed by the unit of derived
sections over `U'`, read through restriction of scalars.

Only a reassociation of a four-fold composite is involved; it is `comp_assoc4` rather than
`Category.assoc`, see the implementation notes. -/
theorem sectionsRestrictUnit_eq {U U' : C} (g : U' ⟶ U) :
    sectionsRestrictUnit O g = homotopySectionsRestrict O g ≫
      Functor.whiskerRight ((homotopySections O U').totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
        (restrictScalarsDerived O g) := by
  rw [sectionsRestrictUnit, homotopySectionsRestrict]
  exact comp_assoc4 _ _ _ _

/-! ### The three cancellations -/

/-- **The evaluation comparison is pinned to its underived form.**
`Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso` is
`CategoryTheory.Functor.rightDerivedNatIso` of
`Stacks.Cohomology.HypercohomologyEdge.homotopySectionsEvaluationIso`, so composing it with the
unit of the derived sections presheaf recovers the underived comparison followed by the unit of
derived sections over `U`. -/
theorem sectionsEvaluationIso_fac (U : C) (q : ℤ) :
    totalRightDerivedCompUnit (homotopySectionsPresheaf O)
          (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
            PresheafOfModules.evaluation O.obj (.op U)) ≫
        Functor.whiskerLeft DerivedCategory.Qh (sectionsEvaluationIso O U q).hom =
      (homotopySectionsEvaluationIso O U q).hom ≫
        totalRightDerivedCompUnit (homotopySections O U)
          (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) := by
  have := isRightDerivedFunctor_totalRightDerived_comp (homotopySectionsPresheaf O)
    (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
      PresheafOfModules.evaluation O.obj (.op U))
  have := isRightDerivedFunctor_totalRightDerived_comp (homotopySections O U)
    (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q)
  exact Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) _

/-- **The characterizing equation of the derived restriction, read on degree-`q` homology.**
Composing the unit of derived sections over `U` with the derived restriction recovers
`Stacks.Cohomology.HypercohomologyEdge.sectionsRestrictUnit`, by
`derivedSectionsRestrict_fac`; applying the homology functor to that equation is this
statement. -/
theorem derivedSectionsRestrict_fac_homology {U U' : C} (g : U' ⟶ U) (q : ℤ) :
    totalRightDerivedCompUnit (homotopySections O U)
          (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerRight (derivedSectionsRestrict O g)
            (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q)) =
      Functor.whiskerRight (sectionsRestrictUnit O g)
        (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) := by
  refine NatTrans.ext (funext fun K => ?_)
  have h := NatTrans.congr_app (derivedSectionsRestrict_fac O g) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    totalRightDerivedCompUnit_app, ← Functor.map_comp]
  exact congrArg _ h

/-- **The unit of the presheaf of derived sections is natural in the object of the site.**
Evaluating at `U` and then restricting along `g` is restricting and then evaluating at `U'`: both
sides are the restriction map of the presheaf applied to the image under `H^q` of the unit, so
this is the naturality of `CategoryTheory.PresheafOfModules.restriction`. -/
theorem totalRightDerivedCompUnit_restriction_naturality {U U' : C} (g : U' ⟶ U) (q : ℤ) :
    totalRightDerivedCompUnit (homotopySectionsPresheaf O)
          (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
            PresheafOfModules.evaluation O.obj (.op U)) ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerLeft (derivedSectionsPresheaf O ⋙
            DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
            (PresheafOfModules.restriction O.obj g.op)) =
      Functor.whiskerLeft (homotopySectionsPresheaf O ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
          (PresheafOfModules.restriction O.obj g.op) ≫
        Functor.whiskerRight (totalRightDerivedCompUnit (homotopySectionsPresheaf O)
          (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
            PresheafOfModules.evaluation O.obj (.op U')))
          (ModuleCat.restrictScalars (O.obj.map g.op).hom) := by
  refine NatTrans.ext (funext fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    totalRightDerivedCompUnit_app, Functor.comp_map]
  exact (PresheafOfModules.restriction O.obj g.op).naturality _

/-- **The unit of derived sections over `U'` passes through the homology comparison of restriction
of scalars.**  This is the naturality of `Stacks.Homology.derivedHomologyIso`, and it is the step
at which the right derived functors leave the square: the unit occurring inside
`Stacks.Cohomology.HypercohomologyEdge.sectionsRestrictUnit` on one side, and the unit at `U'` on
the other, are carried to one another. -/
theorem derivedHomologyIso_totalRightDerivedUnit {U U' : C} (g : U' ⟶ U) (q : ℤ) :
    Functor.whiskerRight (Functor.whiskerRight
          ((homotopySections O U').totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
          (restrictScalarsDerived O g))
          (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ≫
        Functor.whiskerLeft (DerivedCategory.Qh ⋙ derivedSections O U')
          (Stacks.Homology.derivedHomologyIso
            (ModuleCat.restrictScalars (O.obj.map g.op).hom) q).hom =
      Functor.whiskerLeft (homotopySections O U')
          (Stacks.Homology.derivedHomologyIso
            (ModuleCat.restrictScalars (O.obj.map g.op).hom) q).hom ≫
        Functor.whiskerRight (totalRightDerivedCompUnit (homotopySections O U')
            (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U'))) q))
          (ModuleCat.restrictScalars (O.obj.map g.op).hom) := by
  refine NatTrans.ext (funext fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    totalRightDerivedCompUnit_app]
  exact (Stacks.Homology.derivedHomologyIso
    (ModuleCat.restrictScalars (O.obj.map g.op).hom) q).hom.naturality _

/-! ### The reduction -/

/-- **The evaluation restriction square, reduced to a square with no derived functor in it.**
The transformation form of the naturality in the object of the site of
`Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso` — the form in which
`Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict_of_natTrans` consumes it —
follows from the corresponding square between transformations out of
`homotopySectionsPresheaf O ⋙ H^q ⋙ evaluation U` in which only the underived comparison
`homotopySectionsEvaluationIso`, the termwise restriction `homotopySectionsRestrict`, the homology
comparison `Stacks.Homology.derivedHomologyIso` of restriction of scalars and the restriction map
of the presheaf occur.

So the residual of this half of the square carries no right derived functor, no
`CategoryTheory.Functor.rightDerivedDesc` and no unit: it is a statement about complexes of
sheaves of modules, which is what the route recorded for it in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolution` asserts it should
become.

The hypothesis is not discharged here. -/
theorem sectionsEvaluationIso_restrict_natTrans_of_homotopySquare {U U' : C} (g : U' ⟶ U) (q : ℤ)
    (hsq : (homotopySectionsEvaluationIso O U q).hom ≫
        Functor.whiskerRight (homotopySectionsRestrict O g)
            (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ≫
          Functor.whiskerLeft (homotopySections O U')
            (Stacks.Homology.derivedHomologyIso
              (ModuleCat.restrictScalars (O.obj.map g.op).hom) q).hom =
      Functor.whiskerLeft (homotopySectionsPresheaf O ⋙
            DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
          (PresheafOfModules.restriction O.obj g.op) ≫
        Functor.whiskerRight (homotopySectionsEvaluationIso O U' q).hom
          (ModuleCat.restrictScalars (O.obj.map g.op).hom)) :
    (sectionsEvaluationIso O U q).hom ≫ derivedSectionsRestrictHomology O g q =
      Functor.whiskerLeft (derivedSectionsPresheaf O ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
        (PresheafOfModules.restriction O.obj g.op) ≫
        Functor.whiskerRight (sectionsEvaluationIso O U' q).hom
          (ModuleCat.restrictScalars (O.obj.map g.op).hom) := by
  refine sectionsEvaluationIso_restrict_natTrans_of_unit O g q ?_
  have h2 : Functor.whiskerRight (homotopySectionsRestrict O g)
        (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ≫
      Functor.whiskerRight (Functor.whiskerRight
          ((homotopySections O U').totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
          (restrictScalarsDerived O g))
        (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) =
      Functor.whiskerRight (sectionsRestrictUnit O g)
        (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) := by
    rw [← Functor.whiskerRight_comp, ← sectionsRestrictUnit_eq O g]
  have h5 : Functor.whiskerRight (totalRightDerivedCompUnit (homotopySectionsPresheaf O)
          (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
            PresheafOfModules.evaluation O.obj (.op U')))
        (ModuleCat.restrictScalars (O.obj.map g.op).hom) ≫
      Functor.whiskerRight (Functor.whiskerLeft DerivedCategory.Qh
          (sectionsEvaluationIso O U' q).hom)
        (ModuleCat.restrictScalars (O.obj.map g.op).hom) =
      Functor.whiskerRight (homotopySectionsEvaluationIso O U' q).hom
          (ModuleCat.restrictScalars (O.obj.map g.op).hom) ≫
        Functor.whiskerRight (totalRightDerivedCompUnit (homotopySections O U')
            (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U'))) q))
          (ModuleCat.restrictScalars (O.obj.map g.op).hom) := by
    rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp,
      sectionsEvaluationIso_fac O U' q]
  refine NatTrans.ext (funext fun K => ?_)
  have e1 := NatTrans.congr_app (sectionsEvaluationIso_fac O U q) K
  have e2 := NatTrans.congr_app (derivedSectionsRestrict_fac_homology O g q) K
  have e2' := NatTrans.congr_app h2 K
  have e3 := NatTrans.congr_app (totalRightDerivedCompUnit_restriction_naturality O g q) K
  have e4 := NatTrans.congr_app (derivedHomologyIso_totalRightDerivedUnit O g q) K
  have e5 := NatTrans.congr_app h5 K
  have e6 := NatTrans.congr_app hsq K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at e1 e2 e2' e3 e4 e5 e6 ⊢
  exact squares_chain e1 (e2.trans e2'.symm) e4 e3 e5 e6

/-- **The object-wise evaluation restriction square from the unit-free square.**  The shape in
which the restriction compatibility of
`Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyEvaluationIso` consumes this half,
obtained from the reduction above through
`Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict_of_natTrans`.

The hypothesis is not discharged here. -/
theorem sectionsEvaluationIso_restrict_of_homotopySquare {U U' : C} (g : U' ⟶ U) (q : ℤ)
    (hsq : (homotopySectionsEvaluationIso O U q).hom ≫
        Functor.whiskerRight (homotopySectionsRestrict O g)
            (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ≫
          Functor.whiskerLeft (homotopySections O U')
            (Stacks.Homology.derivedHomologyIso
              (ModuleCat.restrictScalars (O.obj.map g.op).hom) q).hom =
      Functor.whiskerLeft (homotopySectionsPresheaf O ⋙
            DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
          (PresheafOfModules.restriction O.obj g.op) ≫
        Functor.whiskerRight (homotopySectionsEvaluationIso O U' q).hom
          (ModuleCat.restrictScalars (O.obj.map g.op).hom))
    (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    (sectionsEvaluationIso O U q).hom.app K ≫ (derivedSectionsRestrictHomology O g q).app K =
      (PresheafOfModules.restriction O.obj g.op).app
          ((DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q).obj
            ((derivedSectionsPresheaf O).obj K)) ≫
        (ModuleCat.restrictScalars (O.obj.map g.op).hom).map
          ((sectionsEvaluationIso O U' q).hom.app K) :=
  sectionsEvaluationIso_restrict_of_natTrans O g q
    (sectionsEvaluationIso_restrict_natTrans_of_homotopySquare O g q hsq) K

end Stacks.Cohomology.HypercohomologyEdge

end
