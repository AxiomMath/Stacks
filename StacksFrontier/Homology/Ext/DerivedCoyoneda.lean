module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# The right derived functor of a corepresentable functor is Ext

For an object `M` of an abelian category `𝒜` with enough injectives, the functor
`Hom_𝒜(M, -)` is corepresented in the bounded below derived category by `M` placed in degree `0`.
Its right derived functor on `D⁺(𝒜)` computes the Ext groups out of `M`: the cohomology of
`R Hom_𝒜(M, -)` applied to an object `K` of `D⁺(𝒜)` is `Ext^n(M, K)`, and in particular
`R^i Hom_𝒜(M, -)` applied to an object `N` of `𝒜` is `Ext^i(M, N)`.

## Main definitions

* `StacksDraft.DerivedCoyoneda.smallCoyoneda`: the functor `Hom_𝒜(M, -)` with values in the
  universe of the derived category, obtained by corepresenting it on `D(𝒜)` rather than on `𝒜`.

## Main results

* `StacksDraft.DerivedCoyoneda.rightDerivedSmallCoyonedaHomologyIso`:
  `H^n(R Hom(M, -)(K)) ≅ Ext^n(M, K)` for `K` in `D⁺(𝒜)`.
* `StacksDraft.DerivedCoyoneda.rightDerivedSmallCoyonedaIso`:
  `R^i Hom(M, -)(N) ≅ Ext^i(M, N)` for `N` in `𝒜`.

## Implementation notes

`Hom_𝒜(M, N)` lives in the universe of the morphisms of `𝒜`, which need not be the universe of
the derived category. `smallCoyoneda` therefore corepresents the functor by the image of `M` in
`D(𝒜)`, so that its values are the morphism groups of the derived category. The two are
identified degreewise inside `homologySmallCoyonedaAddEquiv`, where the single functor into the
derived category is fully faithful.

The derived functor is computed by choosing a bounded below complex `J` of injective objects
representing `K`; then `R Hom(M, -)(K)` is `Hom(M, -)` applied termwise to `J`, whose cohomology
is the group of cohomology classes of degree-`n` cochains from `M` to `J`, which is the group of
morphisms `M ⟶ J[n]` in the derived category because `J` is K-injective.

## References

* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 0AVH](https://stacks.math.columbia.edu/tag/0AVH)
-/

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.DerivedCoyoneda

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

open CochainComplex CochainComplex.HomComplex

section

variable [HasDerivedCategory.{w} C]

/-- Cohomology classes into a K-injective complex compute morphisms in the derived category.

The body is exposed because the identification carries no equation lemma, and a consumer that
upgrades it to an identification of modules over a ring acting on the category —
`StacksDraft.DerivedCoyoneda.cocycleLinearMapDerivedHom` of
`StacksFrontier/Homology/Ext/DerivedCoyonedaLinear.lean` — has to unfold the composite to move a
scalar across it. -/
@[expose]
public noncomputable def cohomologyClassAddEquivDerivedHom
    (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    CohomologyClass K L n ≃+
      (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :=
  CohomologyClass.homAddEquiv.trans
    ((AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
      (CochainComplex.IsKInjective.Qh_map_bijective _ (L⟦n⟧))).trans
      (CategoryTheory.Linear.homCongr ℤ
        ((DerivedCategory.quotientCompQhIso C).app K)
        ((DerivedCategory.quotientCompQhIso C).app (L⟦n⟧) ≪≫
          (DerivedCategory.Q.commShiftIso n).app L)).toAddEquiv)

/-- The corepresentable functor `Hom(M, -)`, with values in the universe of the derived
category. -/
public noncomputable abbrev smallCoyoneda (M : C) : C ⥤ AddCommGrpCat.{w} :=
  DerivedCategory.singleFunctor C 0 ⋙
    preadditiveCoyoneda.obj (Opposite.op ((DerivedCategory.singleFunctor C 0).obj M))

end

/-- Degreewise additive equivalences commuting with the differentials induce an additive
equivalence on homology, in possibly different universes. -/
public noncomputable def homologyAddEquivOfComponents
    {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex AddCommGrpCat.{v} c)
    (L : HomologicalComplex AddCommGrpCat.{w} c)
    (e : ∀ i, K.X i ≃+ L.X i)
    (he : ∀ i j (x : K.X i), e j ((K.d i j).hom x) = (L.d i j).hom (e i x))
    (n : ι) : K.homology n ≃+ L.homology n := by
  let F := AddCommGrpCat.uliftFunctor.{w, v}
  let G := AddCommGrpCat.uliftFunctor.{v, w}
  let h : (F.mapHomologicalComplex c).obj K ≅ (G.mapHomologicalComplex c).obj L :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => ((AddEquiv.ulift.trans (e i)).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro i j hij
        ext x
        exact congrArg ULift.up (he i j x.down).symm)
  exact AddEquiv.ulift.symm.trans
    (((K.sc n).mapHomologyIso F).symm.addCommGroupIsoToAddEquiv.trans
      ((HomologicalComplex.homologyMapIso h n).addCommGroupIsoToAddEquiv.trans
        (((L.sc n).mapHomologyIso G).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)))

section

variable [HasDerivedCategory.{w} C]

/-- The cohomology of `Hom(M, -)` applied termwise to a K-injective complex computes Ext. -/
public noncomputable def homologySmallCoyonedaAddEquiv (M : C)
    (L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    (((smallCoyoneda M).mapHomologicalComplex (.up ℤ)).obj L).homology n ≃+
      ((DerivedCategory.singleFunctor C 0).obj M ⟶ (DerivedCategory.Q.obj L)⟦n⟧) := by
  let S := (CochainComplex.singleFunctor C 0).obj M
  let F := DerivedCategory.singleFunctor C 0
  let e (i : ℤ) : (S.HomComplex L).X i ≃+
      (((smallCoyoneda M).mapHomologicalComplex (.up ℤ)).obj L).X i :=
    (Cochain.fromSingleEquiv (X := M) (K := L) (p := 0) (q := i) (n := i)
      (by omega)).trans (AddEquiv.ofBijective F.mapAddHom ⟨F.map_injective, F.map_surjective⟩)
  have he (i j : ℤ) (x : (S.HomComplex L).X i) :
      e j (((S.HomComplex L).d i j).hom x) =
        ((((smallCoyoneda M).mapHomologicalComplex (.up ℤ)).obj L).d i j).hom (e i x) := by
    obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective x i (by omega)
    change F.map (Cochain.fromSingleEquiv (by omega : (0 : ℤ) + j = j)
      (δ i j (Cochain.fromSingleMk f (by omega : (0 : ℤ) + i = i)))) =
      F.map (Cochain.fromSingleEquiv (by omega : (0 : ℤ) + i = i)
        (Cochain.fromSingleMk f (by omega : (0 : ℤ) + i = i))) ≫ F.map (L.d i j)
    rw [Cochain.δ_fromSingleMk f (by omega : (0 : ℤ) + i = i) j j (by omega),
      Cochain.fromSingleEquiv_fromSingleMk, Cochain.fromSingleEquiv_fromSingleMk, F.map_comp]
  exact (homologyAddEquivOfComponents (S.HomComplex L) _ e he n).symm.trans
    ((HomComplex.homologyAddEquiv S L n).trans
      ((cohomologyClassAddEquivDerivedHom S L n).trans
        (CategoryTheory.Linear.homCongr ℤ
          ((DerivedCategory.singleFunctorIsoCompQ C 0).app M).symm
          (Iso.refl _)).toAddEquiv))

end

/-- The localization through the bounded below homotopy category agrees with localization
of bounded below complexes. -/
private noncomputable def plusQuotientCompQhIso
    (A : Type*) [Category* A] [Abelian A] [HasDerivedCategory A] :
    HomotopyCategory.Plus.quotient A ⋙ DerivedCategory.Plus.Qh ≅ DerivedCategory.Plus.Q :=
  (Functor.FullyFaithful.whiskeringRight
    (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := A)))
      (CochainComplex.Plus A)).preimageIso
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι A) (DerivedCategory.quotientCompQhIso A))

/-- An additive functor's right derived functor is computed on a bounded below complex
of injective objects by applying the functor termwise. -/
public noncomputable def homologyRightDerivedIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (J : CochainComplex.Plus (InjectiveObject A)) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
        ((InjectiveObject.ι A).mapCochainComplexPlus.obj J))) ≅
    (((F.mapHomologicalComplex (.up ℤ)).obj
      (((InjectiveObject.ι A).mapCochainComplexPlus.obj J).obj)).homology n) := by
  let L := (InjectiveObject.ι A).mapCochainComplexPlus.obj J
  have : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj L)) := by
    dsimp [L]
    infer_instance
  exact (DerivedCategory.Plus.homologyFunctor B n).mapIso
    (F.rightDerivedFunctorPlus.mapIso ((plusQuotientCompQhIso A).app L).symm ≪≫
    (asIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj L))).symm ≪≫
    (plusQuotientCompQhIso B).app (F.mapCochainComplexPlus.obj L)) ≪≫
    (DerivedCategory.homologyFunctorFactors B n).app _

section

variable [HasDerivedCategory.{w} C] [EnoughInjectives C] [HasDerivedCategory AddCommGrpCat.{w}]

/-- The cohomology of the right derived functor of `Hom(M, -)` at a bounded below derived object
is the Ext group of that object. -/
public noncomputable def rightDerivedSmallCoyonedaHomologyIso
    (M : C) (K : DerivedCategory.Plus C) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{w} n).obj
      ((smallCoyoneda M).rightDerivedFunctorPlus.obj K) ≅
      AddCommGrpCat.of (DerivedCategory.Ext.{u, v, w}
        ((DerivedCategory.singleFunctor C 0).obj M) (DerivedCategory.Plus.ι.obj K) n) := by
  apply Classical.choice
  obtain ⟨b, hb⟩ := K.property
  have : K.IsGE b := (K.isGE_ι_obj_iff b).1 hb
  obtain ⟨J, hJ, ⟨e⟩⟩ := K.exists_injective_nonempty_iso b
  let L := (InjectiveObject.ι C).mapCochainComplexPlus.obj J
  have : L.obj.IsKInjective :=
    inferInstanceAs
      (IsKInjective (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj J.obj))
  exact ⟨(DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{w} n).mapIso
      ((smallCoyoneda M).rightDerivedFunctorPlus.mapIso e.symm) ≪≫
    homologyRightDerivedIso (smallCoyoneda M) J n ≪≫
    ((homologySmallCoyonedaAddEquiv M L.obj n).trans
      (CategoryTheory.Linear.homCongr ℤ
        (Iso.refl ((DerivedCategory.singleFunctor C 0).obj M))
        ((CategoryTheory.shiftFunctor (DerivedCategory C) n).mapIso
          (DerivedCategory.Plus.ι.mapIso e))).toAddEquiv).toAddCommGrpIso⟩

/-- The higher right derived functors of `Hom(M, -)` on objects of the abelian category are the
Ext groups out of `M`. -/
public noncomputable def rightDerivedSmallCoyonedaIso (M N : C) (n : ℤ) :
    ((smallCoyoneda M).rightDerivedPlus n).obj N ≅
      AddCommGrpCat.of (Abelian.zExt.{u, v, w} M N n) :=
  rightDerivedSmallCoyonedaHomologyIso M ((DerivedCategory.Plus.singleFunctor C 0).obj N) n

end

end StacksDraft.DerivedCoyoneda
