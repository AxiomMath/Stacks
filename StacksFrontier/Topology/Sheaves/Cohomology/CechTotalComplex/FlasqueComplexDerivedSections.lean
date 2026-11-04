module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueModulesAreAcyclic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AcyclicCoveringComputesDerivedSections
import StacksCore.Tactic.StacksAttribute

/-!
# A bounded below complex of flasque modules computes its derived global sections

Let `(X, O_X)` be a ringed space and let `U : I → Opens X` be an open covering of `X`. For a
bounded below complex `K^•` of flasque `O_X`-modules the three comparison maps

`Γ(X, K^•) ⟶ Tot(Č^•(U, K^•)) ⟶ RΓ(X, K^•)`

and their composite are all isomorphisms in `D(Ab)`.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Cech.Flasque.isZero_rightDerived_evaluation_of_isFlasque`: the higher derived sections
  of a flasque sheaf of modules vanish over every open subset.
* `Stacks.Cech.Flasque.isIso_globalSectionsToDerived_of_isFlasque`: ordinary global sections of a
  bounded below complex of flasque modules compute derived global sections.
* `Stacks.Cech.Flasque.isIso_cechToDerivedGlobalSections_app_of_isFlasque`: the comparison of
  Tag 08BN is invertible on such a complex, for every open covering.
* `Stacks.Cech.Flasque.isIso_comparisons_of_isFlasque`: all three comparisons at once.

## Implementation notes

Each step is an instance of a known result. Flasqueness gives right acyclicity for sections over
every open subset (Tag 09SY), which through Tag 015C is the vanishing of the higher derived
sections there; that vanishing is the hypothesis of Tag 0FLH for the intersections of the
covering, and it is also what makes each term of the complex right acyclic for global sections,
so Leray's acyclicity lemma (Tag 015E) applies to the complex. The third comparison is then not
proved separately: the comparison system of Tag 08BN carries the identity saying that the Čech
augmentation followed by the Čech comparison is the unit `Γ(X, K^•) ⟶ RΓ(X, K^•)`, so two of the
three isomorphisms give the remaining one.

The ordinary-to-derived comparison is written out as the composite of its five factors, four of
which are components of natural isomorphisms; this is the same factorisation that the injective
case uses, and only the right-acyclicity input changes.

Global sections are taken on the abelian sheaf underlying a sheaf of modules, as in the total
Čech complex API; the common universe is the one that API is stated at.

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 09SY](https://stacks.math.columbia.edu/tag/09SY)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0FLH](https://stacks.math.columbia.edu/tag/0FLH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u

namespace Stacks.Cech.Flasque

variable (X : TopCat.{u})

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- The canonical map from ordinary to derived global sections, written out as the composite of
its five factors. -/
private theorem globalSectionsToDerivedNat_app_factors
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (K : CochainComplex.Plus (SheafOfModules.{u} R)) :
    (globalSectionsToDerivedNat X R).app K =
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.app
          ((CochainComplex.Plus.ι (SheafOfModules.{u} R) ⋙
            (abelianGlobalSections X R).mapHomologicalComplex (up ℤ)).obj K) ≫
        (DerivedCategory.Qh (C := AddCommGrpCat.{u})).map
          ((globalSectionsHomotopyBridgeIso X R).inv.app K) ≫
        (DerivedCategory.Plus.QhCompιIsoιCompQh AddCommGrpCat.{u}).inv.app
          ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} R) ⋙
            (abelianGlobalSections X R).mapHomotopyCategoryPlus).obj K) ≫
        (DerivedCategory.Plus.ι (C := AddCommGrpCat.{u})).map
          ((abelianGlobalSections X R).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} R)).obj K)) ≫
        (DerivedCategory.Plus.ι (C := AddCommGrpCat.{u})).map
          ((abelianGlobalSections X R).rightDerivedFunctorPlus.map
            ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ
              (SheafOfModules.{u} R)).hom.app K)) :=
  rfl

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **A bounded below complex whose terms are right acyclic for global sections computes derived
global sections.** This is Leray's acyclicity lemma read through the four natural isomorphisms
that relate the localisation of the complex of global sections to the value of the derived
functor. -/
theorem isIso_globalSectionsToDerived_of_rightAcyclic
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (K : CochainComplex.Plus (SheafOfModules.{u} R))
    (hK : ∀ n : ℤ, (abelianGlobalSections X R).rightAcyclic (K.1.X n)) :
    IsIso ((globalSectionsToDerivedNat X R).app K) := by
  have hunit : IsIso ((abelianGlobalSections X R).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} R)).obj K)) :=
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ hK
  have h1 : IsIso ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.app
      ((CochainComplex.Plus.ι (SheafOfModules.{u} R) ⋙
        (abelianGlobalSections X R).mapHomologicalComplex (up ℤ)).obj K)) :=
    Iso.isIso_hom (((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app
      ((CochainComplex.Plus.ι (SheafOfModules.{u} R) ⋙
        (abelianGlobalSections X R).mapHomologicalComplex (up ℤ)).obj K)).symm)
  have h2 : IsIso ((globalSectionsHomotopyBridgeIso X R).inv.app K) :=
    Iso.isIso_hom (((globalSectionsHomotopyBridgeIso X R).app K).symm)
  have h3 : IsIso ((DerivedCategory.Plus.QhCompιIsoιCompQh AddCommGrpCat.{u}).inv.app
      ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} R) ⋙
        (abelianGlobalSections X R).mapHomotopyCategoryPlus).obj K)) :=
    Iso.isIso_hom (((DerivedCategory.Plus.QhCompιIsoιCompQh AddCommGrpCat.{u}).app
      ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} R) ⋙
        (abelianGlobalSections X R).mapHomotopyCategoryPlus).obj K)).symm)
  have h5 : IsIso ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ
      (SheafOfModules.{u} R)).hom.app K) :=
    Iso.isIso_hom
      ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ (SheafOfModules.{u} R)).app K)
  rw [globalSectionsToDerivedNat_app_factors X R K]
  refine IsIso.comp_isIso' h1 (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' h3
    (IsIso.comp_isIso' ?_ ?_)))
  · exact @Functor.map_isIso _ _ _ _ _ _
      (DerivedCategory.Qh (C := AddCommGrpCat.{u})) _ h2
  · exact @Functor.map_isIso _ _ _ _ _ _
      (DerivedCategory.Plus.ι (C := AddCommGrpCat.{u})) _ hunit
  · exact @Functor.map_isIso _ _ _ _ _ _
      (DerivedCategory.Plus.ι (C := AddCommGrpCat.{u})) _
      (@Functor.map_isIso _ _ _ _ _ _
        (abelianGlobalSections X R).rightDerivedFunctorPlus _ h5)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **The higher derived sections of a flasque sheaf of modules vanish over every open subset.**
A flasque sheaf is right acyclic for sections (Tag 09SY), and for a left exact functor right
acyclicity is the vanishing of all higher right derived functors (Tag 015C). -/
@[ega "0 12.1.7" "partial", sga "2 I 2.12" "special case", sga "4 V 4.6" "special case"]
theorem isZero_rightDerived_evaluation_of_isFlasque
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (V : Opens X)
    (A : SheafOfModules.{u} R)
    (hA : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj A))
    (i : ℕ) (hi : 0 < i) :
    IsZero (((SheafOfModules.evaluation.{u} R (op V)).rightDerived i).obj A) :=
  (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived
    (SheafOfModules.evaluation.{u} R (op V)) A).1
    (Stacks.Cohomology.FlasqueAcyclic.rightAcyclic_evaluation_of_isFlasque R A V hA) i hi

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **A flasque sheaf of modules is right acyclic for global sections of the underlying abelian
sheaf.** Its higher derived sections over `X` vanish, and forgetting the module structure is
exact. -/
@[ega "0 12.1.7" "partial", sga "2 I 2.12" "special case", sga "4 V 4.6" "partial"]
theorem rightAcyclic_abelianGlobalSections_of_isFlasque
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (A : SheafOfModules.{u} R)
    (hA : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj A)) :
    (abelianGlobalSections X R).rightAcyclic A := by
  have h : (abelianSections X R ⊤).rightAcyclic A := by
    rw [Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived]
    intro i hi
    exact isZero_rightDerived_abelianSections X ⊤ A i
      (isZero_rightDerived_evaluation_of_isFlasque X R ⊤ A hA i hi)
  exact h

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **Ordinary global sections of a bounded below complex of flasque modules compute derived
global sections.** Every term is right acyclic for global sections, so Leray's acyclicity lemma
applies. -/
theorem isIso_globalSectionsToDerived_of_isFlasque
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (K : CochainComplex.Plus (SheafOfModules.{u} R))
    (hK : ∀ q : ℤ, TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj (K.1.X q))) :
    IsIso (globalSectionsToDerived X R K) :=
  isIso_globalSectionsToDerived_of_rightAcyclic X R K fun n =>
    rightAcyclic_abelianGlobalSections_of_isFlasque X R (K.1.X n) (hK n)

/-- **The total Čech complex of a bounded below complex of flasque modules computes its derived
global sections**, for every open covering. The derived sections of a flasque module vanish over
every open subset, in particular over the intersections of the covering, which is the vanishing
hypothesis of Tag 0FLH. -/
theorem isIso_cechToDerivedGlobalSections_app_of_isFlasque
    {I : Type u} (U : I → Opens X)
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (hU : ⊤ = iSup U)
    (K : CochainComplex.Plus (SheafOfModules.{u} R))
    (hK : ∀ q : ℤ, TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj (K.1.X q))) :
    IsIso (((cechToDerivedGlobalSections X R).map U hU).app K) :=
  isIso_cechToDerivedGlobalSections_app X U R hU K fun _ _ q i hi =>
    isZero_rightDerived_evaluation_of_isFlasque X R _ (K.1.X q) (hK q) i hi

/-- **For a bounded below complex `K^•` of flasque `O_X`-modules and any open covering `U` of `X`
one has `Γ(X, K^•) = Tot(Č^•(U, K^•)) = RΓ(X, K^•)` in the derived category**: the Čech
augmentation of Tag 07M9, the comparison of Tag 08BN and their composite, the unit
`Γ(X, K^•) ⟶ RΓ(X, K^•)`, are all isomorphisms.

This is the identification that the proof of Tag 0FKV reduces its diagram to, after replacing
the two coefficient complexes by bounded below complexes of flasque modules. -/
theorem isIso_comparisons_of_isFlasque
    {I : Type u} (U : I → Opens X)
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (hU : ⊤ = iSup U)
    (K : CochainComplex.Plus (SheafOfModules.{u} R))
    (hK : ∀ q : ℤ, TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj (K.1.X q))) :
    IsIso ((globalSectionsToCechDerived X R U).app K) ∧
      IsIso (((cechToDerivedGlobalSections X R).map U hU).app K) ∧
        IsIso (globalSectionsToDerived X R K) := by
  have hcech : IsIso (((cechToDerivedGlobalSections X R).map U hU).app K) :=
    isIso_cechToDerivedGlobalSections_app_of_isFlasque X U R hU K hK
  have hunit : IsIso (globalSectionsToDerived X R K) :=
    isIso_globalSectionsToDerived_of_isFlasque X R K hK
  refine ⟨?_, hcech, hunit⟩
  have hcomp : IsIso ((globalSectionsToCechDerived X R U).app K ≫
      ((cechToDerivedGlobalSections X R).map U hU).app K) := by
    rw [(cechToDerivedGlobalSections X R).globalSections U hU K]
    exact hunit
  exact IsIso.of_isIso_comp_right _ (((cechToDerivedGlobalSections X R).map U hU).app K)

end Stacks.Cech.Flasque

end
