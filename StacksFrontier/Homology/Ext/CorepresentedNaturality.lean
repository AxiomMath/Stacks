module

public import StacksFrontier.Homology.DerivedIndexing.RightDerivedAbsolute
public import StacksFrontier.Homology.Ext.CorepresentedHomotopyComparison

/-!
# Naturality of the hypercohomology corepresentation

Let `A` be an abelian category with enough injectives and `T : A ⥤ AddCommGrpCat` an additive
functor corepresented by an object `Z`, so `T ≅ Hom(Z, -)`. The degree-`n` cohomology of the
right derived functor of `T` is identified with morphisms out of `Z[0]` in the derived category,
as an isomorphism of functors on the bounded below derived category:

`H^n(RT(-)) ≅ Hom_{D(A)}(Z[0], (-)⟦n⟧)`.

The two sides lie in different universes, so the isomorphism of functors is taken after a
universe lift on each side; at a single object it is an additive equivalence of the two groups.

## Main definitions

* `Stacks.Cohomology.Corepresented.corepresentedRightDerivedHomologyFunctor`: `K ↦ H^n(RT(K))`.
* `Stacks.Cohomology.Corepresented.corepresentedDerivedHomFunctor`:
  `K ↦ Hom_{D(A)}(Z[0], K⟦n⟧)`.
* `Stacks.Cohomology.Corepresented.corepresentedDerivedHomUnit`: the natural transformation
  exhibiting the second functor as a right derived functor.
* `Stacks.Cohomology.Corepresented.corepresentedHomologyNatIso`: the natural isomorphism
  `H^n(RT(-)) ≅ Hom_{D(A)}(Z[0], (-)⟦n⟧)`.
* `Stacks.Cohomology.Corepresented.corepresentedRightDerivedHomologyAddEquiv`: its component at
  an object, as an additive equivalence between the two groups.

## Main results

* `Stacks.Cohomology.Corepresented.isRightDerivedFunctor_corepresentedDerivedHomUnit`:
  `Hom_{D(A)}(Z[0], (-)⟦n⟧)` is a right derived functor of `L ↦ H^n(T(L))`.
* `Stacks.Cohomology.Corepresented.corepresentedRightDerivedHomologyAddEquiv_naturality`: the
  identification carries the map induced on cohomology by a morphism `φ` of the derived
  category to postcomposition with `φ⟦n⟧`.

## References

* [Stacks Project, Tag 0A64](https://stacks.math.columbia.edu/tag/0A64)
* [Stacks Project, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u

namespace Stacks.Cohomology.Corepresented

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] [EnoughInjectives A]
  (T : A ⥤ AddCommGrpCat.{v}) [T.Additive] [HasDerivedCategory.{w'} AddCommGrpCat.{v}]
  (Z : A) (e : preadditiveCoyoneda.obj (op Z) ≅ T) (n : ℤ)

/-- The functor `K ↦ H^n(RT(K))` on the bounded below derived category, universe-lifted to
`AddCommGrpCat.{max v w}`. -/
abbrev corepresentedRightDerivedHomologyFunctor :
    DerivedCategory.Plus A ⥤ AddCommGrpCat.{max v w} :=
  T.rightDerivedFunctorPlus ⋙
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n ⋙
      AddCommGrpCat.uliftFunctor.{w, v})

/-- The functor `K ↦ Hom_{D(A)}(Z[0], K⟦n⟧)` on the bounded below derived category,
universe-lifted to `AddCommGrpCat.{max v w}`. -/
abbrev corepresentedDerivedHomFunctor : DerivedCategory.Plus A ⥤ AddCommGrpCat.{max v w} :=
  DerivedCategory.Plus.ι ⋙ shiftFunctor (DerivedCategory A) n ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj Z)) ⋙
      AddCommGrpCat.uliftFunctor.{v, w}

/-- The natural transformation exhibiting `Hom_{D(A)}(Z[0], (-)⟦n⟧)` as a right derived functor
of `L ↦ H^n(T(L))` on the bounded below homotopy category:
`Stacks.Cohomology.Corepresented.homotopyComparison` restricted along the inclusion of the
bounded below homotopy category. -/
def corepresentedDerivedHomUnit :
    T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n ⋙
          AddCommGrpCat.uliftFunctor.{w, v}) ⟶
      DerivedCategory.Plus.Qh ⋙ corepresentedDerivedHomFunctor (A := A) Z n :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι A) (homotopyComparison T Z e n)

/-- `Hom_{D(A)}(Z[0], (-)⟦n⟧)` is a right derived functor of `L ↦ H^n(T(L))`. -/
instance isRightDerivedFunctor_corepresentedDerivedHomUnit :
    (corepresentedDerivedHomFunctor (A := A) Z n).IsRightDerivedFunctor
      (corepresentedDerivedHomUnit T Z e n) (HomotopyCategory.Plus.quasiIso A) := by
  refine (HomotopyCategory.Plus.localizerMorphism_derives
    (T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n ⋙
        AddCommGrpCat.uliftFunctor.{w, v}))).isRightDerivedFunctor_of_isIso _ fun X ↦ ?_
  obtain ⟨Y, hY⟩ := X
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  rw [HomotopyCategory.plus_quotient_obj_iff] at hY
  obtain ⟨m, hm⟩ := hY
  have hinj : ∀ j : ℤ, Injective
      ((((InjectiveObject.ι A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).X j) :=
    fun j ↦ (L.X j).property
  have : CochainComplex.IsKInjective
      (((InjectiveObject.ι A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    CochainComplex.isKInjective_of_injective _ m
  exact inferInstanceAs (IsIso ((homotopyComparison T Z e n).app
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
      (((InjectiveObject.ι A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L))))

/-- The universe-lifted functors `H^n(RT(-))` and `Hom_{D(A)}(Z[0], (-)⟦n⟧)` on the bounded below
derived category are isomorphic: the isomorphism is the unique one compatible with their
structures of right derived functors of `L ↦ H^n(T(L))`. -/
def corepresentedHomologyNatIso :
    corepresentedRightDerivedHomologyFunctor T n ≅ corepresentedDerivedHomFunctor (A := A) Z n :=
  Functor.rightDerivedUnique _ _
    (Stacks.DerivedIndexing.rightDerivedFunctorPlusCompUnit T
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n ⋙
        AddCommGrpCat.uliftFunctor.{w, v}))
    (corepresentedDerivedHomUnit T Z e n) (HomotopyCategory.Plus.quasiIso A)

/-- The component of `Stacks.Cohomology.Corepresented.corepresentedHomologyNatIso` at `K` with
the universe lift undone: `H^n(RT(K)) ≃+ Hom_{D(A)}(Z[0], K⟦n⟧)`. -/
def corepresentedRightDerivedHomologyAddEquiv (K : DerivedCategory.Plus A) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).obj
        (T.rightDerivedFunctorPlus.obj K)) ≃+
      ((DerivedCategory.singleFunctor A 0).obj Z ⟶ (DerivedCategory.Plus.ι.obj K)⟦n⟧) :=
  AddEquiv.ulift.symm.trans
    ((((corepresentedHomologyNatIso T Z e n).app K).addCommGroupIsoToAddEquiv).trans
      AddEquiv.ulift)

/-- `corepresentedRightDerivedHomologyAddEquiv` carries the map induced on cohomology by a
morphism `φ` of the bounded below derived category to postcomposition with `φ⟦n⟧`. -/
theorem corepresentedRightDerivedHomologyAddEquiv_naturality
    {K K' : DerivedCategory.Plus A} (φ : K ⟶ K')
    (x : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).obj
      (T.rightDerivedFunctorPlus.obj K)) :
    corepresentedRightDerivedHomologyAddEquiv T Z e n K'
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).map
          (T.rightDerivedFunctorPlus.map φ) x) =
      corepresentedRightDerivedHomologyAddEquiv T Z e n K x ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Plus.ι.map φ) :=
  congrArg ULift.down <| ConcreteCategory.congr_hom
    ((corepresentedHomologyNatIso T Z e n).hom.naturality φ) (ULift.up x)

end Stacks.Cohomology.Corepresented

end
