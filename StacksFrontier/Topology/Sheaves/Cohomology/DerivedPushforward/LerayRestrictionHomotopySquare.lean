module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EvaluationRestrictionHomotopySquare
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayRestrictionSquare

/-!
# The Leray restriction square, with the derived functors removed

Let `f : X ⟶ Y` be a morphism of ringed spaces and `V' ≤ V` opens of `Y`. The naturality in the
open of the Leray isomorphism `derivedSectionsPushforwardIso`, one half of the restriction
compatibility in [Stacks, Tag 0D68], follows from a square between transformations out of
`homotopyPreimageSections f V` in which no right derived functor, no
`CategoryTheory.Functor.rightDerivedDesc` and no unit occurs: on one side the identification
`Γ(V, f_* -) = Γ(f⁻¹ V, -)` of `pushforwardPreimageSectionsIso` followed by the termwise
restriction of sections over `V`, `Stacks.Cohomology.HypercohomologyEdge.homotopySectionsRestrict`;
on the other the termwise restriction of sections over `f⁻¹ V`, `homotopyPreimageSectionsRestrict`,
followed by the same identification over `V'`.

All names are in the namespace `Stacks.Cohomology.DerivedSectionsLeray`.

## Main definitions

* `homotopyPreimageSectionsRestrict`: restriction of sections over an inverse image on the
  homotopy category, the termwise part of `preimageSectionsRestrictUnit`.

## Main results

* `preimageSectionsRestrictUnit_eq`: the prescribing transformation of the derived restriction on
  an inverse image is the termwise restriction followed by the derived unit.
* `lerayComparison_comp_derivedSectionsOverOpenRestrict_of_homotopySquare`: the transformation
  form of the Leray restriction square follows from the unit-free square on the homotopy category.
* `derivedSectionsPushforwardIso_restrict_of_homotopySquare`: the object-wise square, from the
  same hypothesis.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit
  pushforwardToDerivedCategory)
open Stacks.Cohomology.HypercohomologyEdge (sectionsRestrictUnit homotopySectionsRestrict
  derivedSectionsRestrict_fac sectionsRestrictUnit_eq comp_assoc4)

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits

/-- If `a = p1 ≫ p2 ≫ p3` and `b = q1 ≫ q2`, then `a ≫ p4 = b ≫ q3` follows from the five
commuting squares `hL1`, `hL2`, `hsq`, `hL3` and `hL4`. -/
private theorem leray_chain {Z : Type*} [Category* Z] {o1 o2 o3 o4 o5 n1 t1 m1 m2 : Z}
    {a : o1 ⟶ o4} {p1 : o1 ⟶ o2} {p2 : o2 ⟶ o3} {p3 : o3 ⟶ o4} {p4 : o4 ⟶ o5}
    {wl : o3 ⟶ n1} {cres : n1 ⟶ o5} {hsr : o2 ⟶ t1} {wru : t1 ⟶ n1}
    {b : o1 ⟶ m2} {q1 : o1 ⟶ m1} {q2 : m1 ⟶ m2} {q3 : m2 ⟶ o5} {k : m1 ⟶ t1} {w : m1 ⟶ o5}
    (hA : a = p1 ≫ p2 ≫ p3) (hB : b = q1 ≫ q2)
    (hL1 : p3 ≫ p4 = wl ≫ cres) (hL2 : p2 ≫ wl = hsr ≫ wru)
    (hsq : p1 ≫ hsr = q1 ≫ k) (hL3 : q2 ≫ q3 = w) (hL4 : w = k ≫ wru ≫ cres) :
    a ≫ p4 = b ≫ q3 := by
  subst hA hB
  simp only [Category.assoc]
  rw [hL1, reassoc_of% hL2, reassoc_of% hsq, hL3, hL4]

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The termwise restriction on an inverse image, separated from the derived unit -/

/-- **Restriction of sections over an inverse image, on the homotopy category.**  The termwise
part of `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsRestrictUnit`: restrict the
complex of sections over `f⁻¹ V` to sections over `f⁻¹ V'` degreewise, then compare the termwise
image with the derived action of restriction of scalars.  No right derived functor occurs. -/
def homotopyPreimageSectionsRestrict {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    homotopyPreimageSections f V ⟶
      homotopyPreimageSections f V' ⋙ restrictScalarsDerived Y hV :=
  Functor.whiskerRight (NatTrans.mapHomotopyCategory (preimageSectionsRestrict f hV)
      (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (preimageSections f V' ⋙
        ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((preimageSections f V').mapHomotopyCategory (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars
        ((structureSheafRing Y).obj.map hV.hom.op).hom).mapDerivedCategoryFactorsh.inv

/-- **The prescribing transformation of the derived restriction on an inverse image splits.** It
is the termwise restriction `homotopyPreimageSectionsRestrict` followed by the unit of
`RΓ(f⁻¹ V', -)`, read through restriction of scalars. -/
theorem preimageSectionsRestrictUnit_eq {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    preimageSectionsRestrictUnit f hV = homotopyPreimageSectionsRestrict f hV ≫
      Functor.whiskerRight (derivedPreimageSectionsUnit f V') (restrictScalarsDerived Y hV) := by
  rw [preimageSectionsRestrictUnit, homotopyPreimageSectionsRestrict]
  exact comp_assoc4 _ _ _ _

/-! ### The four cancellations -/

/-- **The derived restriction in the open commutes with the unit of `Rf_*`**: an instance of the
naturality of `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenRestrict`. -/
theorem derivedSectionsOverOpenRestrict_naturality_derivedPushforwardUnit
    {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    Functor.whiskerRight (derivedPushforwardUnit f) (derivedSectionsOverOpen Y V) ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerLeft (derivedPushforward f)
            (derivedSectionsOverOpenRestrict Y hV)) =
      Functor.whiskerLeft (pushforwardToDerivedCategory f)
          (derivedSectionsOverOpenRestrict Y hV) ≫
        Functor.whiskerRight (derivedPushforwardUnit f)
          (derivedSectionsOverOpen Y V' ⋙ restrictScalarsDerived Y hV) := by
  refine NatTrans.ext (funext fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  exact (derivedSectionsOverOpenRestrict Y hV).naturality _

/-- **The derived restriction in the open, at the direct image of a complex, is termwise.**  After
degreewise pushforward along `f`, the unit of `RΓ(V, -)` followed by the derived restriction is
the termwise restriction `Stacks.Cohomology.HypercohomologyEdge.homotopySectionsRestrict`
followed by the unit of `RΓ(V', -)`. -/
theorem derivedSectionsOverOpenUnit_comp_derivedSectionsOverOpenRestrict
    {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
          (derivedSectionsOverOpenUnit Y V) ≫
        Functor.whiskerLeft (pushforwardToDerivedCategory f)
          (derivedSectionsOverOpenRestrict Y hV) =
      Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
          (homotopySectionsRestrict (structureSheafRing Y) hV.hom) ≫
        Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
          (Functor.whiskerRight (derivedSectionsOverOpenUnit Y V')
            (restrictScalarsDerived Y hV)) := by
  have hfac : Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
        (derivedSectionsOverOpenUnit Y V) ≫
      Functor.whiskerLeft (pushforwardToDerivedCategory f)
        (derivedSectionsOverOpenRestrict Y hV) =
      Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
        (sectionsRestrictUnit (structureSheafRing Y) hV.hom) := by
    refine NatTrans.ext (funext fun K => ?_)
    have h := NatTrans.congr_app (derivedSectionsRestrict_fac (structureSheafRing Y) hV.hom)
      (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h ⊢
    exact h
  rw [hfac, sectionsRestrictUnit_eq, Functor.whiskerLeft_comp]

/-- **The Leray comparison at `V'`, read through restriction of scalars, is pinned to
`lerayUnit`.**  This is `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac` with
restriction of scalars applied to it. -/
theorem lerayComparison_fac_restrictScalars {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    Functor.whiskerRight (derivedPreimageSectionsUnit f V') (restrictScalarsDerived Y hV) ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerRight (lerayComparison f V') (restrictScalarsDerived Y hV)) =
      Functor.whiskerRight (lerayUnit f V') (restrictScalarsDerived Y hV) := by
  refine NatTrans.ext (funext fun K => ?_)
  have h := NatTrans.congr_app (lerayComparison_fac f V') K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    ← Functor.map_comp]
  exact congrArg _ h

/-- **`lerayUnit` at `V'`, read through restriction of scalars, written out.**  Its three legs are
the identification `Γ(V', f_* -) = Γ(f⁻¹ V', -)`, the unit of `RΓ(V', -)` and the unit of
`Rf_*`. -/
theorem whiskerRight_lerayUnit_eq {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    Functor.whiskerRight (lerayUnit f V') (restrictScalarsDerived Y hV) =
      Functor.whiskerRight (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (pushforwardPreimageSectionsIso f V') (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
          (restrictScalarsDerived Y hV) ≫
        Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
            (Functor.whiskerRight (derivedSectionsOverOpenUnit Y V')
              (restrictScalarsDerived Y hV)) ≫
          Functor.whiskerRight (derivedPushforwardUnit f)
            (derivedSectionsOverOpen Y V' ⋙ restrictScalarsDerived Y hV) := by
  rw [lerayUnit]
  refine NatTrans.ext (funext fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.map_comp]

/-! ### The reduction -/

/-- **The Leray restriction square, reduced to a square with no derived functor in it.**  The
transformation form of the naturality in the open of the Leray comparison follows from the square
between transformations out of `homotopyPreimageSections f V` in which only the identification
`Stacks.Cohomology.DerivedSectionsLeray.pushforwardPreimageSectionsIso` and the two termwise
restrictions `Stacks.Cohomology.HypercohomologyEdge.homotopySectionsRestrict` and
`Stacks.Cohomology.DerivedSectionsLeray.homotopyPreimageSectionsRestrict` occur. -/
theorem lerayComparison_comp_derivedSectionsOverOpenRestrict_of_homotopySquare
    {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (hsq : Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (pushforwardPreimageSectionsIso f V) (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
          Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
            (homotopySectionsRestrict (structureSheafRing Y) hV.hom) =
        homotopyPreimageSectionsRestrict f hV ≫
          Functor.whiskerRight (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
              (pushforwardPreimageSectionsIso f V') (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
            (restrictScalarsDerived Y hV)) :
    lerayComparison f V ≫
        Functor.whiskerLeft (derivedPushforward f) (derivedSectionsOverOpenRestrict Y hV) =
      derivedPreimageSectionsRestrict f hV ≫
        Functor.whiskerRight (lerayComparison f V') (restrictScalarsDerived Y hV) :=
  lerayComparison_comp_derivedSectionsOverOpenRestrict_of_lerayUnit f hV
    (leray_chain rfl (preimageSectionsRestrictUnit_eq f hV)
      (derivedSectionsOverOpenRestrict_naturality_derivedPushforwardUnit f hV)
      (derivedSectionsOverOpenUnit_comp_derivedSectionsOverOpenRestrict f hV) hsq
      (lerayComparison_fac_restrictScalars f hV) (whiskerRight_lerayUnit_eq f hV))

/-- **The object-wise Leray restriction square from the unit-free square.**  For every complex
`K`, the Leray isomorphisms over `V` and `V'` commute with the derived restrictions. -/
theorem derivedSectionsPushforwardIso_restrict_of_homotopySquare
    {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (hsq : Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (pushforwardPreimageSectionsIso f V) (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
          Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
            (homotopySectionsRestrict (structureSheafRing Y) hV.hom) =
        homotopyPreimageSectionsRestrict f hV ≫
          Functor.whiskerRight (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
              (pushforwardPreimageSectionsIso f V') (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
            (restrictScalarsDerived Y hV))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedSectionsOverOpenRestrict Y hV).app ((derivedPushforward f).obj K) ≫
        (restrictScalarsDerived Y hV).map ((derivedSectionsPushforwardIso f V').hom.app K) =
      (derivedSectionsPushforwardIso f V).hom.app K ≫
        (derivedPreimageSectionsRestrict f hV).app K :=
  derivedSectionsPushforwardIso_restrict_of_lerayComparison f hV
    (lerayComparison_comp_derivedSectionsOverOpenRestrict_of_homotopySquare f hV hsq) K

end Stacks.Cohomology.DerivedSectionsLeray

end
