module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulHomColimitSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf
public import StacksFrontier.Homology.HomComplex.HomologyFunctoriality
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyBijective

/-!
# The Koszul Hom complexes compute morphisms out of the derived Koszul system

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`
and let `X = Spec A`.  Stage `e` of the Koszul Hom diagram is the Hom complex
`Hom^•(I^•(f^{e+1}), M^•)`, and `I^•(f^{e+1})` is a bounded above complex of projective
`A`-modules, so by [Stacks, Tag 0A66] the degree-zero cohomology of that Hom complex is
`Hom_{D(A)}(I^•(f^{e+1}), M^•)`.  Derived sheafification `D(A) ⥤ D(𝒪_X)` is fully faithful by
[Stacks, Tag 06Z0], so that group is also `Hom_{D(𝒪_X)}(Iₑ, M̃^•)`.

The resulting identification

`H⁰(Hom^•(I^•(f^{e+1}), M^•)) ≃+ Hom_{D(𝒪_X)}(Iₑ, M̃^•)`

is natural in `M^•` and in `e`, which is what this file provides.

## Main definitions

* `Koszul.DerivedSystem.homGroupSystemFunctor` is the direct system `e ↦ Hom_{D(𝒪_X)}(Iₑ, E)`
  of `Koszul.DerivedSystem.homGroupSystem`, read as a functor of `E`.
* `Koszul.DerivedSystem.homStageDerivedEquiv` is the identification
  `H⁰(Hom^•(P^•, L^•)) ≃+ Hom_{D(A)}(P^•, L^•)` for `P^•` a bounded above complex of
  projectives, read on the Hom complex of `A`-modules with its module structure forgotten.
* `Koszul.DerivedSystem.koszulHomStageDerivedIso` is the identification above, as an isomorphism
  of functors of `M^•` with values in `ℕ`-diagrams of abelian groups.

## Main results

* `Koszul.DerivedSystem.homStageDerivedEquiv_naturality`: the identification
  `H⁰(Hom^•(P^•, L^•)) ≃+ Hom_{D(A)}(P^•, L^•)` is natural in both variables.

## Implementation notes

The Hom complex of complexes of `A`-modules is a complex of `A`-modules, and the Koszul Hom
diagram uses it with that module structure, whereas the comparison of [Stacks, Tag 0A66] is
stated for the Hom complex of abelian groups.  The two agree after applying the forgetful functor
degreewise, but only up to unfolding the two definitions, so the comparison
`Koszul.DerivedSystem.homComplexRForgetIso` is introduced explicitly rather than left to
unification; this keeps every rewrite below type-correct at the transparency that `rewrite` uses.

Derived sheafification is `AlgebraicGeometry.tilde.functor` with its codomain spelled as the
modules over `(Spec A).ringCatSheaf`, so its full faithfulness is
`AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful`, at the standard model of both
derived categories.

## References

* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
* [Stacks Project, Tag 0A64](https://stacks.math.columbia.edu/tag/0A64)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open CochainComplex.HomComplex

universe u

namespace Koszul.DerivedSystem

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The Hom complex of `A`-modules and the Hom complex of abelian groups -/

section Stage

variable {A : CommRingCat.{u}}

/-- The forgetful functor from `A`-modules to abelian groups, applied degreewise to complexes. -/
public abbrev forgetComplexes (A : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)

/-- **The Hom complex of `A`-modules is the Hom complex of abelian groups.**  Forgetting the
module structure of `Hom^•(P^•, L^•)` degreewise gives the Hom complex of abelian groups, both
being `Cochain P^• L^• n` in degree `n` with the differential `δ`. -/
public def homComplexRForgetIso (P L : CochainComplex (ModuleCat.{u} A) ℤ) :
    (forgetComplexes A).obj (CochainComplex.HomComplexR A P L) ≅ P.HomComplex L :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- Forgetting the module structure carries precomposition on Hom complexes of `A`-modules to
precomposition on Hom complexes of abelian groups. -/
public lemma forgetComplexes_map_precomp (P P' L : CochainComplex (ModuleCat.{u} A) ℤ)
    (g : P' ⟶ P) :
    (forgetComplexes A).map (Stacks.HomComplex.TensorHomMap.precomp A P' P L g) ≫
        (homComplexRForgetIso P' L).hom =
      (homComplexRForgetIso P L).hom ≫ homComplexPrecomp g L := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

/-- Forgetting the module structure carries postcomposition on Hom complexes of `A`-modules to
postcomposition on Hom complexes of abelian groups. -/
public lemma forgetComplexes_map_postcomp (P L L' : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : L ⟶ L') :
    (forgetComplexes A).map (Stacks.HomComplex.TensorHomMap.postcomp A P L L' h) ≫
        (homComplexRForgetIso P L').hom =
      (homComplexRForgetIso P L).hom ≫ homComplexPostcomp P h := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

/-- An isomorphism of complexes of abelian groups induces an isomorphism on homology. -/
public def homologyIsoOfIso {K L : CochainComplex AddCommGrpCat.{u} ℤ} (e : K ≅ L) (n : ℤ) :
    K.homology n ≅ L.homology n where
  hom := HomologicalComplex.homologyMap e.hom n
  inv := HomologicalComplex.homologyMap e.inv n
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp, e.hom_inv_id, HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp, e.inv_hom_id, HomologicalComplex.homologyMap_id]

/-- The degree-zero cohomology of the Hom complex of `A`-modules, read as a group of degree-zero
cohomology classes. -/
public def homStageClassEquiv (P L : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((forgetComplexes A).obj (CochainComplex.HomComplexR A P L)).homology 0 ≃+
      CohomologyClass P L 0 :=
  ((homologyIsoOfIso (homComplexRForgetIso P L) 0).addCommGroupIsoToAddEquiv).trans
    (homologyAddEquiv P L 0)

/-- A commuting square of complexes of abelian groups gives a commuting square on `H⁰`. -/
private lemma homologyMap_apply_comm {K K' L L' : CochainComplex AddCommGrpCat.{u} ℤ}
    (a : K ⟶ K') (b : K' ⟶ L') (c : K ⟶ L) (d : L ⟶ L') (h : a ≫ b = c ≫ d)
    (x : K.homology 0) :
    HomologicalComplex.homologyMap b 0 (HomologicalComplex.homologyMap a 0 x) =
      HomologicalComplex.homologyMap d 0 (HomologicalComplex.homologyMap c 0 x) := by
  simp only [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp, h]

/-- `homStageClassEquiv` carries the map induced by precomposition to `cohomologyClassPrecomp`. -/
public lemma homStageClassEquiv_precomp (P P' L : CochainComplex (ModuleCat.{u} A) ℤ)
    (g : P' ⟶ P)
    (x : ((forgetComplexes A).obj (CochainComplex.HomComplexR A P L)).homology 0) :
    homStageClassEquiv P' L
        (HomologicalComplex.homologyMap ((forgetComplexes A).map
          (Stacks.HomComplex.TensorHomMap.precomp A P' P L g)) 0 x) =
      cohomologyClassPrecomp g L 0 (homStageClassEquiv P L x) := by
  exact (congrArg (homologyAddEquiv P' L 0) (homologyMap_apply_comm _ _ _ _
    (forgetComplexes_map_precomp P P' L g) x)).trans
    (homologyAddEquiv_precomp g L 0 _).symm

/-- `homStageClassEquiv` carries the map induced by postcomposition to
`cohomologyClassPostcomp`. -/
public lemma homStageClassEquiv_postcomp (P L L' : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : L ⟶ L')
    (x : ((forgetComplexes A).obj (CochainComplex.HomComplexR A P L)).homology 0) :
    homStageClassEquiv P L'
        (HomologicalComplex.homologyMap ((forgetComplexes A).map
          (Stacks.HomComplex.TensorHomMap.postcomp A P L L' h)) 0 x) =
      cohomologyClassPostcomp P h 0 (homStageClassEquiv P L x) := by
  exact (congrArg (homologyAddEquiv P L' 0) (homologyMap_apply_comm _ _ _ _
    (forgetComplexes_map_postcomp P L L' h) x)).trans
    (homologyAddEquiv_postcomp P h 0 _).symm

/-! ### The comparison with morphisms in the derived category of `A`-modules -/

/-- Morphisms in the homotopy category out of a complex and into its zero shift are morphisms in
the derived category: the identification transporting the comparison of [Stacks, Tag 0A66] in
degree zero to `Hom_{D(A)}(P^•, L^•)`. -/
public def homotopyShiftZeroCongr (P L : CochainComplex (ModuleCat.{u} A) ℤ) :
    (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)).obj P) ⟶
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)).obj (L⟦(0 : ℤ)⟧))) ≃+
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) :=
  homCongrAddEquiv ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P)
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (L⟦(0 : ℤ)⟧) ≪≫
      DerivedCategory.Q.mapIso ((shiftFunctorZero _ ℤ).app L))

/-- `homotopyShiftZeroCongr` transports a morphism along the identifications of its source and
its target. -/
public lemma homotopyShiftZeroCongr_apply (P L : CochainComplex (ModuleCat.{u} A) ℤ)
    (v : DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)).obj P) ⟶
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)).obj (L⟦(0 : ℤ)⟧))) :
    homotopyShiftZeroCongr P L v =
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P).inv ≫ v ≫
        (((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (L⟦(0 : ℤ)⟧)).hom ≫
          DerivedCategory.Q.map
            (((shiftFunctorZero (CochainComplex (ModuleCat.{u} A) ℤ) ℤ).app L).hom)) :=
  rfl

/-- **The degree-zero cohomology of the Hom complex is `Hom` in `D(A)`.**  For `P^•` a bounded
above complex of projective `A`-modules, the degree-zero cohomology of the Hom complex
`Hom^•(P^•, L^•)` — read on the complex of abelian groups underlying the Hom complex of
`A`-modules — is the group of morphisms `P^• ⟶ L^•` in `D(A)`.  This is [Stacks, Tag 0A66] in
degree zero, in the spelling the Koszul Hom diagram uses; the covering set of the tag is in
`StacksFrontier/Homology/HomComplex/RHom.lean`, so this carries no attribute. -/
public def homStageDerivedEquiv (P L : CochainComplex (ModuleCat.{u} A) ℤ)
    [CochainComplex.IsStrictlyLE P 0] [∀ i, Projective (P.X i)] :
    ((forgetComplexes A).obj (CochainComplex.HomComplexR A P L)).homology 0 ≃+
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) :=
  (homStageClassEquiv P L).trans
    ((cohomologyClassRHomAddEquiv P L 0 0).trans (homotopyShiftZeroCongr P L))

/-- The comparison of `homStageDerivedEquiv` is natural in the first variable. -/
public lemma homStageDerivedEquiv_precomp (P P' L : CochainComplex (ModuleCat.{u} A) ℤ)
    (g : P' ⟶ P) [CochainComplex.IsStrictlyLE P 0] [∀ i, Projective (P.X i)]
    [CochainComplex.IsStrictlyLE P' 0] [∀ i, Projective (P'.X i)]
    (x : ((forgetComplexes A).obj (CochainComplex.HomComplexR A P L)).homology 0) :
    homStageDerivedEquiv P' L
        (HomologicalComplex.homologyMap ((forgetComplexes A).map
          (Stacks.HomComplex.TensorHomMap.precomp A P' P L g)) 0 x) =
      DerivedCategory.Q.map g ≫ homStageDerivedEquiv P L x := by
  have hq : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)).map g) ≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P).hom =
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P').hom ≫
          DerivedCategory.Q.map g :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.naturality g
  have hnat0 : ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P').inv ≫
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)).map g) =
        DerivedCategory.Q.map g ≫
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hq
  have hnat : ∀ w : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)).obj P) ⟶
        DerivedCategory.Q.obj L,
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P').inv ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)).map g) ≫ w =
        DerivedCategory.Q.map g ≫
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P).inv ≫ w := by
    intro w
    rw [← Category.assoc, hnat0, Category.assoc]
  simp only [homStageDerivedEquiv, AddEquiv.trans_apply, homStageClassEquiv_precomp P P' L g x,
    cohomologyClassRHomAddEquiv_naturality_left P P' L g 0 0 0]
  rw [homotopyShiftZeroCongr_apply, homotopyShiftZeroCongr_apply]
  simp only [Category.assoc]
  rw [hnat]

/-- The comparison of `homStageDerivedEquiv` is natural in the second variable. -/
public lemma homStageDerivedEquiv_postcomp (P L L' : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : L ⟶ L') [CochainComplex.IsStrictlyLE P 0] [∀ i, Projective (P.X i)]
    (x : ((forgetComplexes A).obj (CochainComplex.HomComplexR A P L)).homology 0) :
    homStageDerivedEquiv P L'
        (HomologicalComplex.homologyMap ((forgetComplexes A).map
          (Stacks.HomComplex.TensorHomMap.postcomp A P L L' h)) 0 x) =
      homStageDerivedEquiv P L x ≫ DerivedCategory.Q.map h := by
  have hshift : DerivedCategory.Q.map (h⟦(0 : ℤ)⟧') ≫
      DerivedCategory.Q.map
        (((shiftFunctorZero (CochainComplex (ModuleCat.{u} A) ℤ) ℤ).app L').hom) =
        DerivedCategory.Q.map
            (((shiftFunctorZero (CochainComplex (ModuleCat.{u} A) ℤ) ℤ).app L).hom) ≫
          DerivedCategory.Q.map h := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    exact congrArg DerivedCategory.Q.map
      ((shiftFunctorZero (CochainComplex (ModuleCat.{u} A) ℤ) ℤ).hom.naturality h)
  have hq : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)).map (h⟦(0 : ℤ)⟧')) ≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (L'⟦(0 : ℤ)⟧)).hom =
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (L⟦(0 : ℤ)⟧)).hom ≫
          DerivedCategory.Q.map (h⟦(0 : ℤ)⟧') :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.naturality (h⟦(0 : ℤ)⟧')
  have hnat : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)).map (h⟦(0 : ℤ)⟧')) ≫
          (((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (L'⟦(0 : ℤ)⟧)).hom ≫
            DerivedCategory.Q.map
              (((shiftFunctorZero (CochainComplex (ModuleCat.{u} A) ℤ) ℤ).app L').hom)) =
      (((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (L⟦(0 : ℤ)⟧)).hom ≫
          DerivedCategory.Q.map
            (((shiftFunctorZero (CochainComplex (ModuleCat.{u} A) ℤ) ℤ).app L).hom)) ≫
        DerivedCategory.Q.map h := by
    rw [← Category.assoc, hq, Category.assoc, Category.assoc, hshift]
  simp only [homStageDerivedEquiv, AddEquiv.trans_apply, homStageClassEquiv_postcomp P L L' h x,
    cohomologyClassRHomAddEquiv_naturality_right P L L' h 0 0]
  rw [homotopyShiftZeroCongr_apply, homotopyShiftZeroCongr_apply, Category.assoc, hnat]
  simp only [Category.assoc]

/-- **The comparison of `homStageDerivedEquiv` is natural in both variables.** -/
public lemma homStageDerivedEquiv_naturality (P P' L L' : CochainComplex (ModuleCat.{u} A) ℤ)
    (g : P' ⟶ P) (h : L ⟶ L') [CochainComplex.IsStrictlyLE P 0] [∀ i, Projective (P.X i)]
    [CochainComplex.IsStrictlyLE P' 0] [∀ i, Projective (P'.X i)]
    (x : ((forgetComplexes A).obj (CochainComplex.HomComplexR A P L)).homology 0) :
    homStageDerivedEquiv P' L'
        (HomologicalComplex.homologyMap ((forgetComplexes A).map
          (Stacks.HomComplex.TensorHomMap.precomp A P' P L g ≫
            Stacks.HomComplex.TensorHomMap.postcomp A P' L L' h)) 0 x) =
      DerivedCategory.Q.map g ≫ homStageDerivedEquiv P L x ≫ DerivedCategory.Q.map h := by
  have hstep : HomologicalComplex.homologyMap ((forgetComplexes A).map
        (Stacks.HomComplex.TensorHomMap.precomp A P' P L g ≫
          Stacks.HomComplex.TensorHomMap.postcomp A P' L L' h)) 0 =
      HomologicalComplex.homologyMap ((forgetComplexes A).map
          (Stacks.HomComplex.TensorHomMap.precomp A P' P L g)) 0 ≫
        HomologicalComplex.homologyMap ((forgetComplexes A).map
          (Stacks.HomComplex.TensorHomMap.postcomp A P' L L' h)) 0 := by
    rw [(forgetComplexes A).map_comp, HomologicalComplex.homologyMap_comp]
  have hcomp := ConcreteCategory.congr_hom hstep x
  simp only [ConcreteCategory.comp_apply] at hcomp
  rw [hcomp, homStageDerivedEquiv_postcomp P' L L' h, homStageDerivedEquiv_precomp P P' L g,
    Category.assoc]

end Stage

/-! ### The Koszul stages as morphisms out of the derived Koszul system -/

section Diagram

variable {A : CommRingCat.{u}} {r : ℕ} (f : Fin r → A)

/-- The Koszul system of cochain complexes `I^•(f₁^{e+1}, …, f_r^{e+1})`, as an `ℕᵒᵖ`-diagram:
the inverse system of truncated Koszul complexes, extended from nonnegative chain degrees to
nonpositive cochain degrees.  Sheafifying its image in `D(A)` gives
`Koszul.DerivedSystem.koszulDerivedSystem`. -/
public abbrev koszulCochainDiagram : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  (Koszul.koszulIdealComplexSystem f).diagram ⋙ embeddingDownNat.extendFunctor (ModuleCat.{u} A)

/-- Stage `e` of the Koszul system of cochain complexes: the truncated Koszul complex on the
`(e + 1)`st powers of `f`, extended from nonnegative chain degrees to nonpositive cochain
degrees. -/
public abbrev koszulCochainStage (e : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  (Koszul.koszulIdealComplexPower f e).extend embeddingDownNat

/-- The Koszul ideal complex is concentrated in nonpositive degrees. -/
public instance koszulCochainStage_isStrictlyLE (e : ℕ) :
    CochainComplex.IsStrictlyLE (koszulCochainStage f e) 0 := by
  dsimp only [koszulCochainStage]
  infer_instance

/-- **The Koszul ideal complex is a complex of projective modules**: its degree-`n` term is an
exterior power of a finite free module, hence free. -/
public instance koszulCochainStage_projective (e : ℕ) (i : ℤ) :
    Projective ((koszulCochainStage f e).X i) := by
  have h : ∀ n : ℕ, Projective ((Koszul.koszulIdealComplexPower f e).X n) := by
    intro n
    change Projective (ModuleCat.of A (⋀[A]^(n + 1) (Fin r → A)))
    let b := (Pi.basisFun A (Fin r)).exteriorPower (n + 1)
    let _ := Module.Free.of_basis b
    infer_instance
  dsimp only [koszulCochainStage]
  infer_instance

-- NO `@[stacks 06Z0]` ATTRIBUTE HERE, DELIBERATELY.  Tag 06Z0 is decomposed into thirteen
-- clause-labelled declarations, whose roll-call is in the implementation notes of
-- `StacksFrontier/AlgebraicGeometry/DerivedTilde.lean`; this is
-- `AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful` with its codomain spelled as
-- the modules over `(Spec A).ringCatSheaf`, and adds nothing to the tag's content.
/-- The direct system `e ↦ Hom_{D(𝒪_X)}(Iₑ, E)` of `Koszul.DerivedSystem.homGroupSystem`, read
as a functor of `E`. -/
public abbrev homGroupSystemFunctor : derivedCat A ⥤ (ℕ ⥤ AddCommGrpCat.{u + 1}) :=
  preadditiveYoneda ⋙
    (Functor.whiskeringLeft ℕ (derivedCat A)ᵒᵖ AddCommGrpCat.{u + 1}).obj
      (koszulDerivedSystem f).rightOp

/-- **Stage `e` of the Koszul Hom diagram computes morphisms `Iₑ ⟶ M̃^•` in `D(𝒪_X)`.**  The
degree-zero cohomology of `Hom^•(I^•(f^{e+1}), M^•)` is `Hom_{D(A)}(I^•(f^{e+1}), M^•)` by
[Stacks, Tag 0A66], and derived sheafification is fully faithful by [Stacks, Tag 06Z0]. -/
public def koszulHomStageEquiv (e : ℕ) (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((forgetComplexes A).obj
        (CochainComplex.HomComplexR A (koszulCochainStage f e) M)).homology 0 ≃+
      ((koszulDerivedSystem f).obj (op e) ⟶ (derivedSheafify A).obj (DerivedCategory.Q.obj M)) :=
  (homStageDerivedEquiv (koszulCochainStage f e) M).trans
    (mapHomAddEquiv (derivedSheafify A) (DerivedCategory.Q.obj (koszulCochainStage f e))
      (DerivedCategory.Q.obj M))

/-- `koszulHomStageEquiv` sends a class to the sheafification of the corresponding morphism of
`D(A)`. -/
public lemma koszulHomStageEquiv_apply (e : ℕ) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (x : ((forgetComplexes A).obj
      (CochainComplex.HomComplexR A (koszulCochainStage f e) M)).homology 0) :
    koszulHomStageEquiv f e M x =
      (derivedSheafify A).map (homStageDerivedEquiv (koszulCochainStage f e) M x) :=
  rfl

/-- **The Koszul Hom stages are the morphism groups out of the derived Koszul system**, naturally
in the coefficient complex and in the stage.  Universes force the shift: the morphism groups of
`D(𝒪_X)` live one universe up from the cohomology of the Koszul Hom complexes, so the latter is
lifted. -/
public def koszulHomStageDerivedIso :
    koszulHomStageFunctor f ⋙
        (Functor.whiskeringRight ℕ AddCommGrpCat.{u} AddCommGrpCat.{u + 1}).obj
          AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      DerivedCategory.Q ⋙ derivedSheafify A ⋙ homGroupSystemFunctor f :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents
      (fun e ↦ (AddEquiv.ulift.trans (koszulHomStageEquiv f e M)).toAddCommGrpIso)
      (by
        intro i j h
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        change ULift.{u + 1} (((forgetComplexes A).obj
          (CochainComplex.HomComplexR A (koszulCochainStage f i) M)).homology 0) at x
        change koszulHomStageEquiv f j M
            (HomologicalComplex.homologyMap ((forgetComplexes A).map
              (Stacks.HomComplex.TensorHomMap.precomp A (koszulCochainStage f j)
                  (koszulCochainStage f i) M ((koszulCochainDiagram f).map h.op) ≫
                Stacks.HomComplex.TensorHomMap.postcomp A (koszulCochainStage f j) M M
                  (𝟙 M))) 0 x.down) =
          (koszulDerivedSystem f).map h.op ≫ koszulHomStageEquiv f i M x.down
        rw [koszulHomStageEquiv_apply, koszulHomStageEquiv_apply,
          homStageDerivedEquiv_naturality (koszulCochainStage f i) (koszulCochainStage f j) M M
            ((koszulCochainDiagram f).map h.op) (𝟙 M) x.down]
        rw [DerivedCategory.Q.map_id, Category.comp_id, (derivedSheafify A).map_comp]
        rfl))
    (by
      intro M N g
      apply NatTrans.ext
      funext e
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      change ULift.{u + 1} (((forgetComplexes A).obj
        (CochainComplex.HomComplexR A (koszulCochainStage f e) M)).homology 0) at x
      change koszulHomStageEquiv f e N
          (HomologicalComplex.homologyMap ((forgetComplexes A).map
            (Stacks.HomComplex.TensorHomMap.precomp A (koszulCochainStage f e)
                (koszulCochainStage f e) M (𝟙 (koszulCochainStage f e)) ≫
              Stacks.HomComplex.TensorHomMap.postcomp A (koszulCochainStage f e) M N
                g)) 0 x.down) =
        koszulHomStageEquiv f e M x.down ≫
          (derivedSheafify A).map (DerivedCategory.Q.map g)
      rw [koszulHomStageEquiv_apply, koszulHomStageEquiv_apply,
        homStageDerivedEquiv_naturality (koszulCochainStage f e) (koszulCochainStage f e) M N
          (𝟙 (koszulCochainStage f e)) g x.down]
      rw [DerivedCategory.Q.map_id, Category.id_comp, (derivedSheafify A).map_comp]
      rfl)

end Diagram

end Koszul.DerivedSystem

end
