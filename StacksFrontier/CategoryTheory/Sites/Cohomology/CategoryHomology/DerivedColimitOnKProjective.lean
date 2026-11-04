module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KProjectiveLeftDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitCoefficientTensor

/-!
# Derived lower shriek on a K-projective complex

Let `A` be an abelian category with enough projectives in which countable filtered colimits are
exact, and let `F : A ⥤ B` be a right exact functor preserving them, so that `F` has a total
left derived functor on the unbounded derived category by Stacks 0794 at the projective objects
(`Stacks.CategoryHomology.totalDerivedLeftAdjoint`). On a K-projective complex that derived
functor is computed by applying `F` degreewise: the comparison is invertible there, by
`Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective`.

The instance of interest is `F = colim` over `Cᵒᵖ` for a small category `C` with the chaotic
topology, where the total left derived functor is derived lower shriek
`Lπ_! : D(Cᵒᵖ ⥤ D) ⥤ D(D)` of Stacks 08Q6. On a projective abelian presheaf placed in degree
zero it says `Lπ_!(ℱ) = π_!(ℱ)` with no higher terms, which is the vanishing that makes the left
derived functors of the colimit a universal δ-functor in Stacks 08Q9.

The second instance is extension of scalars along a map `a : O ⟶ O'` of presheaves of rings on a
chaotic site. The generator `j_{W!}O_W = (free O)(yoneda W)` of the proof of [Stacks, Tag 08RX]
is projective (`Stacks.ChaoticSite.freeYonedaProjective`), so it is K-projective in degree zero
and the derived tensor product is computed there by the underived one. Combined with
`Stacks.ChaoticSite.freeCompExtendScalarsIso` this gives the identification
`j_{W!}O_W ⊗^L_O O' ≅ j_{W!}O'_W` *in the derived category*, which is the step of the source's
proof that the generators are unchanged by the change of coefficients.

## Main results

* `Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective`: a total left derived functor of
  `F` at a K-projective complex is `F` applied degreewise.
* `Stacks.CategoryHomology.leftDerivedObjSingleIso`: at a projective object placed in degree zero
  it is `F` of that object placed in degree zero.
* `Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective_naturality`: that computation is
  natural in the K-projective complex.
* `Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective` and
  `Stacks.CategoryHomology.totalDerivedColimitObjSingleIso`: the two statements for `Lπ_!`,
  the first of them together with its naturality
  `Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective_naturality`.
* `Stacks.ChaoticSite.derivedExtendScalarsFreeYonedaIso`:
  **`j_{W!}O_W ⊗^L_O O' ≅ j_{W!}O'_W`** in `D(Mod(O'))`.

## Implementation notes

The general statements are made for an arbitrary total left derived functor with its comparison,
not for the particular model `Stacks.CategoryHomology.totalDerivedLeftAdjoint`: the two
applications below are to `Stacks.CategoryHomology.totalDerivedColimit` with
`totalDerivedColimitCounit` and to `Stacks.ChaoticSite.derivedExtendScalars` with
`derivedExtendScalarsCounit`, and neither definition is exposed outside the module that defines
it.

## References

* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe uD vD u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.CategoryHomology

section General

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (F : A ⥤ B) [F.Additive]
  [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (LF : DerivedCategory A ⥤ DerivedCategory B)
  (α : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **A total left derived functor at a K-projective complex is the underived functor applied
degreewise.** The comparison is invertible there, and the remaining identifications are the
canonical comparisons of the homotopy category with the derived category. -/
def leftDerivedObjIsoOfIsKProjective (P : CochainComplex A ℤ) [P.IsKProjective] :
    LF.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  have := Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective LF α P
  LF.mapIso ((DerivedCategory.quotientCompQhIso A).app P).symm ≪≫
    asIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso B).app ((F.mapHomologicalComplex _).obj P)

/-- **A total left derived functor has no higher terms at a projective object**: on a projective
object placed in degree zero it is the underived functor of that object placed in degree
zero. -/
def leftDerivedObjSingleIso (X : A) [Projective X] :
    LF.obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X)) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj (F.obj X)) :=
  have := Stacks.Homology.isKProjective_single (A := A) X
  leftDerivedObjIsoOfIsKProjective F LF α _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app X)

/-- **The computation of a total left derived functor at a K-projective complex is natural in
the complex.** For a morphism `f : P ⟶ P'` of K-projective complexes the square relating
`LF(f)` with `F(f)` applied degreewise commutes. Each of the four identifications composing
`Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective` is a component of a natural
transformation — the comparison of the homotopy category with the derived category, the
comparison `α` exhibiting `LF` as a left derived functor, and the factorisation of
`F.mapHomotopyCategory` through the quotient — so the square is the composite of their four
naturality squares. -/
lemma leftDerivedObjIsoOfIsKProjective_naturality {P P' : CochainComplex A ℤ}
    [P.IsKProjective] [P'.IsKProjective] (f : P ⟶ P') :
    LF.map (DerivedCategory.Q.map f) ≫
        (leftDerivedObjIsoOfIsKProjective F LF α P').hom =
      (leftDerivedObjIsoOfIsKProjective F LF α P).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have h1 := (DerivedCategory.quotientCompQhIso A).inv.naturality f
  have h2 := α.naturality ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)
  have h3 := (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.naturality f
  have h4 := (DerivedCategory.quotientCompQhIso B).hom.naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  simp only [Functor.comp_map, Functor.comp_obj] at h1 h2 h3 h4
  dsimp only [leftDerivedObjIsoOfIsKProjective, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, asIso_hom]
  simp only [Iso.app_inv, Iso.app_hom]
  slice_lhs 1 2 => rw [← LF.map_comp, h1, LF.map_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [h2]
  slice_lhs 3 4 => rw [← DerivedCategory.Qh.map_comp, h3, DerivedCategory.Qh.map_comp]
  slice_lhs 4 5 => rw [h4]

end General

section LowerShriek

variable (C : Type u) [SmallCategory C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D]

/-- **Derived lower shriek on a chaotic site is the degreewise colimit on a K-projective
complex.** -/
def totalDerivedColimitObjIsoOfIsKProjective (P : CochainComplex (Cᵒᵖ ⥤ D) ℤ)
    [P.IsKProjective] :
    (totalDerivedColimit C D).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  have := colim_hasPointwiseLeftDerivedFunctor C D
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  leftDerivedObjIsoOfIsKProjective (colim : (Cᵒᵖ ⥤ D) ⥤ D) (totalDerivedColimit C D)
    (totalDerivedColimitCounit C D) P

/-- **The computation of derived lower shriek on a K-projective complex is natural in the
complex**: for a morphism of K-projective complexes the identification of `Lπ_!` with the
degreewise colimit commutes with the morphism. -/
lemma totalDerivedColimitObjIsoOfIsKProjective_naturality
    {P P' : CochainComplex (Cᵒᵖ ⥤ D) ℤ} [P.IsKProjective] [P'.IsKProjective] (f : P ⟶ P') :
    (totalDerivedColimit C D).map (DerivedCategory.Q.map f) ≫
        (totalDerivedColimitObjIsoOfIsKProjective C D P').hom =
      (totalDerivedColimitObjIsoOfIsKProjective C D P).hom ≫
        DerivedCategory.Q.map
          (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  have := colim_hasPointwiseLeftDerivedFunctor C D
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  leftDerivedObjIsoOfIsKProjective_naturality (colim : (Cᵒᵖ ⥤ D) ⥤ D)
    (totalDerivedColimit C D) (totalDerivedColimitCounit C D) f

/-- **Derived lower shriek on a chaotic site has no higher terms at a projective abelian
presheaf**: `Lπ_!(ℱ) = π_!(ℱ)` for a projective `ℱ` placed in degree zero. This is the vanishing
that makes the left derived functors of the colimit a universal homological δ-functor in
[Stacks, Tag 08Q9]. -/
def totalDerivedColimitObjSingleIso (P : Cᵒᵖ ⥤ D) [Projective P] :
    (totalDerivedColimit C D).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj P)) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (colimit P)) :=
  have := colim_hasPointwiseLeftDerivedFunctor C D
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  leftDerivedObjSingleIso (colim : (Cᵒᵖ ⥤ D) ⥤ D) (totalDerivedColimit C D)
    (totalDerivedColimitCounit C D) P

end LowerShriek

end Stacks.CategoryHomology

namespace Stacks.ChaoticSite

open Stacks.CategoryHomology

variable {C : Type u} [SmallCategory C] {O O' : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ O') (W : C)

/-- **`j_{W!}O_W ⊗^L_O O' ≅ j_{W!}O'_W` in `D(Mod(O'))`.** The generator `j_{W!}O_W` is the free
`O`-module on the presheaf represented by `W`, which is projective
(`Stacks.ChaoticSite.freeYonedaProjective`), so placed in degree zero it is a K-projective
complex and the derived tensor product with `O'` is computed there by the underived extension of
scalars; that takes it to the free `O'`-module on the same representable
(`Stacks.ChaoticSite.freeCompExtendScalarsIso`).

This is the step of the proof of [Stacks, Tag 08RX] which says the generators are unchanged by
the change of coefficients. It is unconditional: no flatness and no K-flatness is discharged,
because on a chaotic site the generator is projective. -/
def derivedExtendScalarsFreeYonedaIso :
    (derivedExtendScalars a).obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj
          ((PresheafOfModules.free.{u} O).obj (yoneda.obj W)))) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (PresheafOfModules.{u} O') (ComplexShape.up ℤ) 0).obj
          ((PresheafOfModules.free.{u} O').obj (yoneda.obj W))) :=
  have := hasPointwiseLeftDerivedFunctor_of_enoughProjectives (extendScalars a)
  have := derivedExtendScalars_isLeftDerivedFunctor a
  leftDerivedObjSingleIso (extendScalars a) (derivedExtendScalars a)
    (derivedExtendScalarsCounit a) _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.single (PresheafOfModules.{u} O') (ComplexShape.up ℤ) 0).mapIso
        ((freeCompExtendScalarsIso a).app (yoneda.obj W)))

end Stacks.ChaoticSite

end
