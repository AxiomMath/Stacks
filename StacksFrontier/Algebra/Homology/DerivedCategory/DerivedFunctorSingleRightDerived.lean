module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-! # `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)`, naturally in `X`

Let `A` and `B` be abelian categories with unbounded derived categories, `A` with enough
injectives, let `w : A ⥤ B` be additive and let `Rw : D(A) ⥤ D(B)`, with unit `α`, be a right
derived functor of `w` on the unbounded derived category. For every `n : ℕ` there is a natural
isomorphism

`singleFunctor A 0 ⋙ Rw ⋙ homologyFunctor B n ≅ w.rightDerived n`

between the degree-`n` cohomology of `Rw` applied to an object placed in degree `0` and
Mathlib's classical, `ℕ`-indexed right derived functor `CategoryTheory.Functor.rightDerived`,
which is defined from an injective resolution. This file constructs it, as
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`.

It compares the two forms a statement about higher right derived functors can take: one in
`D(A)` is phrased through `Rw` and the cohomology functors, one in the source or in Mathlib
through `rightDerived`. The object-level comparison is
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso`, which carries no naturality.

## The argument

Everything is read off the chosen injective resolution, which Mathlib takes functorially into
the homotopy category. Write `resH` for the chosen injective resolution extended by zero to a
cochain complex indexed by `ℤ` and read in `K(A)`, and `resUnit : X[0] ⟶ resH X` for the
augmentation, both from `Stacks.DerivedIndexing`; the augmentation is natural there because
`CategoryTheory.InjectiveResolution.Hom.ι'_comp_hom'` is an honest commuting square of
complexes. Then:

* `resUnit` is a quasi-isomorphism, so `X[0] ≅ Qh(resH X)` naturally
  (`singleIsoResCompQh`);
* `resH X` is a complex of injectives vanishing below degree `0`, hence K-injective, so the
  unit `α` is invertible there as soon as K-injective resolutions exist
  (`isIso_unit_app_resH_obj`), giving `Qh(w(resH X)) ≅ Rw(Qh(resH X))` naturally
  (`resCompUnitIso`);
* degree-`n` cohomology on `D(B)` restricted along `Qh` is degree-`n` cohomology on `K(B)`
  (`CategoryTheory.DerivedCategory.homologyFunctorFactorsh`);
* and the degree-`n` cohomology of `w` applied to the extended chosen resolution is
  `Rⁿw`, which is `Stacks.DerivedIndexing.rightDerivedIsoRes`.

Composing the four gives the isomorphism. Nothing is chosen: `Rw` and its unit are taken as
data, and any two such pairs are uniquely isomorphic compatibly with their units.

## Main definitions

* `Stacks.DerivedFunctor.singleIsoResCompQh`: an object placed in degree `0` of the derived
  category is its extended chosen injective resolution.
* `Stacks.DerivedFunctor.resCompUnitIso`: the unit of `Rw` is invertible on the extended chosen
  injective resolutions.
* `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`:
  `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)`, naturally in `X`.
* `Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived`: the same with the
  object placed in degree `a` and the cohomology read in degree `m`, for `m - a = n`.

## Main results

* `Stacks.DerivedFunctor.isIso_unit_app_resH_obj`: the unit of `Rw` is invertible at the
  extended chosen injective resolution of an object.
* `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_res`: the
  component of that isomorphism is the composite of the four steps above.

## Implementation notes

`Rw` is taken as data together with its unit `α`, as a right derived functor of
`w(-) : K(A) ⥤ D(B)` along the localization `Qh : K(A) ⥤ D(A)` at quasi-isomorphisms, exactly
as in `StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero`. Without a unit
there is no canonical map to be an isomorphism.

The existence of K-injective resolutions is a hypothesis `hres` rather than an instance; over a
Grothendieck abelian category it is `Stacks.Cohomology.Localization.enoughKInjectives`.

Two intermediate steps are stated as separate declarations with their source and target written
out, `resCompQhReassocIso` and `resCompMapQhHomologyIso`. They are identities, but an `Iso.trans`
chain whose middle functor is left as a **metavariable** fails to elaborate: the unifier is asked
to solve `?E ⋙ ?G =?= (E ⋙ G) ⋙ H`, and the two groupings of a threefold composite give different
solutions, `CategoryTheory.Functor.comp` carrying universe arguments for the intermediate category
that they instantiate differently. The same device is used in
`StacksFrontier.Homology.DerivedIndexing.Basic`. When both groupings are fully elaborated closed
terms, the unifier only checks a definitional equality and succeeds.

In degree `0` this isomorphism and `Stacks.DerivedFunctor.derivedZeroNatIso` have the same
source but different targets, `w.rightDerived 0` against `w`; the two are compatible through
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` when `w` is left exact.

## References

* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- **An object placed in degree `0` of the derived category is its extended chosen injective
resolution**, through the augmentation, naturally in the object. -/
def singleIsoResCompQh :
    DerivedCategory.singleFunctor A 0 ≅
      Stacks.DerivedIndexing.resH ⋙ DerivedCategory.Qh :=
  DerivedCategory.singleFunctorIsoCompQh A 0 ≪≫
    asIso (Functor.whiskerRight (Stacks.DerivedIndexing.resUnit (C := A)) DerivedCategory.Qh)

variable (w : A ⥤ B) [w.Additive]
  (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **The unit of `Rw` is invertible at the extended chosen injective resolution of an object**,
when K-injective resolutions exist. -/
lemma isIso_unit_app_resH_obj
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (X : A) :
    IsIso (α.app (Stacks.DerivedIndexing.resH.obj X)) := by
  have hK : ((injectiveResolution X).cochainComplex).IsKInjective :=
    CochainComplex.isKInjective_of_injective _ 0
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres).2
      DerivedCategory.Qh Rw α _ hK

/-- **The unit of `Rw` on the extended chosen injective resolutions**, as a natural
isomorphism. -/
def resCompUnitIso
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    Stacks.DerivedIndexing.resH ⋙ w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ≅
      Stacks.DerivedIndexing.resH ⋙ DerivedCategory.Qh ⋙ Rw :=
  have : ∀ X, IsIso ((Functor.whiskerLeft
      (Stacks.DerivedIndexing.resH (C := A)) α).app X) := fun X ↦
    isIso_unit_app_resH_obj w Rw α hres X
  have : IsIso (Functor.whiskerLeft (Stacks.DerivedIndexing.resH (C := A)) α) :=
    NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft (Stacks.DerivedIndexing.resH (C := A)) α)

/-- The identity isomorphism between two groupings of the same composite of functors. -/
def resCompQhReassocIso (n : ℤ) :
    (Stacks.DerivedIndexing.resH (C := A) ⋙ DerivedCategory.Qh) ⋙
        (Rw ⋙ DerivedCategory.homologyFunctor B n) ≅
      (Stacks.DerivedIndexing.resH (C := A) ⋙ DerivedCategory.Qh ⋙ Rw) ⋙
        DerivedCategory.homologyFunctor B n :=
  Iso.refl _

/-- The identity isomorphism between two groupings of the same composite of functors. -/
def resCompMapQhHomologyIso (n : ℤ) :
    (Stacks.DerivedIndexing.resH (C := A) ⋙ w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙ DerivedCategory.homologyFunctor B n ≅
      Stacks.DerivedIndexing.resH (C := A) ⋙ w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor B n) :=
  Iso.refl _

/-- **`Hⁿ(Rw(X[0])) ≅ Rⁿw(X)`, naturally in `X`.** The degree-`n` cohomology of a right derived
functor of `w` applied to an object placed in degree `0` of the unbounded derived category is
Mathlib's classical right derived functor `Rⁿw`. -/
def singleCompDerivedCompHomologyIsoRightDerived
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (n : ℕ) :
    DerivedCategory.singleFunctor A 0 ⋙ Rw ⋙ DerivedCategory.homologyFunctor B (n : ℤ) ≅
      w.rightDerived n :=
  Functor.isoWhiskerRight (singleIsoResCompQh (A := A))
      (Rw ⋙ DerivedCategory.homologyFunctor B (n : ℤ)) ≪≫
    resCompQhReassocIso Rw (n : ℤ) ≪≫
    Functor.isoWhiskerRight (resCompUnitIso w Rw α hres).symm
      (DerivedCategory.homologyFunctor B (n : ℤ)) ≪≫
    resCompMapQhHomologyIso w (n : ℤ) ≪≫
    Functor.isoWhiskerLeft (Stacks.DerivedIndexing.resH (C := A) ⋙
        w.mapHomotopyCategory (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)) ≪≫
    (Stacks.DerivedIndexing.rightDerivedIsoRes w n).symm

/-- **The component of `singleCompDerivedCompHomologyIsoRightDerived` at `X`** is the
degree-`n` cohomology of `Rw` applied to the comparison `X[0] ≅ Qh(resH X)`, then of the unit of
`Rw` at the extended chosen resolution inverted, then the factorisation of the cohomology
functor of `D(B)` through the homotopy category, then the comparison of the two indexings of
`Rⁿw` inverted. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_hom_app_res
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (n : ℕ) (X : A) :
    (singleCompDerivedCompHomologyIsoRightDerived w Rw α hres n).hom.app X =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
          (Rw.map ((singleIsoResCompQh (A := A)).hom.app X)) ≫
        (DerivedCategory.homologyFunctor B (n : ℤ)).map
            ((resCompUnitIso w Rw α hres).inv.app X) ≫
          (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
              ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj
                (Stacks.DerivedIndexing.resH.obj X)) ≫
            (Stacks.DerivedIndexing.rightDerivedIsoRes w n).inv.app X := by
  simp [singleCompDerivedCompHomologyIsoRightDerived, resCompQhReassocIso,
    resCompMapQhHomologyIso]

/-- **`Hᵐ(Rw(X[a])) ≅ Rⁿw(X)` for `m - a = n`, naturally in `X`.** The degree-`0` statement
`singleCompDerivedCompHomologyIsoRightDerived` transported by the shift, which the single
functors, the derived functor and the cohomology functors all commute with. -/
def singleShiftCompDerivedCompHomologyIsoRightDerived [Rw.CommShift ℤ]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (a m : ℤ) (n : ℕ) (hn : m - a = n) :
    DerivedCategory.singleFunctor A a ⋙ Rw ⋙ DerivedCategory.homologyFunctor B m ≅
      w.rightDerived n :=
  Functor.isoWhiskerRight
        ((DerivedCategory.singleFunctors A).shiftIso (-a) a 0 (by omega)).symm
        (Rw ⋙ DerivedCategory.homologyFunctor B m) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.singleFunctor A 0)
        (Functor.isoWhiskerRight (Rw.commShiftIso (-a)) (DerivedCategory.homologyFunctor B m) ≪≫
          Functor.isoWhiskerLeft Rw
            ((DerivedCategory.homologyFunctor B 0).shiftIso (-a) m (n : ℤ) (by omega))) ≪≫
    singleCompDerivedCompHomologyIsoRightDerived w Rw α hres n

end Stacks.DerivedFunctor

end
