module

public import Mathlib.Algebra.Homology.Homotopy
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquareHomotopy
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare

/-!
# The composite map of naive cotangent complexes of a tower is null homotopic

Let `a : A ⟶ B` and `b : B ⟶ C` be morphisms of sheaves of commutative rings on a site. The
commutative square
```
B ──b──▸ C
▲        ▲
a        b
│        │
A ──a──▸ B
```
induces a `B`-linear chain map `NL_{B/A} ⟶ NL_{C/B}`, and this chain map is null homotopic. The
null homotopy is concentrated in the single bidegree `(0, -1)`, where it is the map

`B ⊗_{A[B]} Ω_{A[B]/A} ⟶ K/K²`

determined on local sections by `x ⊗ d f ↦ x · ([f] - f)`, with `K` the kernel of the canonical
presentation `B[C] ⟶ C`.

## Main definitions

* `Stacks.SheafOfModules.towerConstMap`: the morphism `A[B] ⟶ B[C]` of presentations sending
  the variable `[f]` to the coefficient `f`.
* `Stacks.SheafOfModules.naiveCotangentTowerHomotopy`: the homotopy on the conormal terms.
* `Stacks.SheafOfModules.naiveCotangentComplexMapOfTower`: the chain map `NL_{B/A} ⟶ NL_{C/B}`
  attached to the tower.
* `Stacks.SheafOfModules.naiveCotangentTowerNullHomotopy`: the null homotopy of the chain map
  `NL_{B/A} ⟶ NL_{C/B}` attached to the tower.
* `Stacks.SheafOfModules.variableSection`: the variable `[t]` of `A[B]` attached to a local
  section `t` of `B`.
* `Stacks.SheafOfModules.towerHomotopyRelation`: the relation `[β t] - γ t` of the canonical
  presentation `B[C] ⟶ C`.

## Main results

* `Stacks.SheafOfModules.naiveCotangentConormalMapOfTower_eq` and
  `Stacks.SheafOfModules.naiveCotangentTensorMapOfTower_eq`: the two components of the chain
  map are the homotopy composed with the differentials.
* `Stacks.SheafOfModules.naiveCotangentTowerHomotopy_tensorDifferential_variableSection`: the
  homotopy sends the local section `1 ⊗ d[t]` to the conormal class of `[β t] - γ t`.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), part (2).
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), the functoriality of
  the naive cotangent complex in a square of sheaves of rings.
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the exact sequence of
  naive cotangent complexes of a composition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)
open Stacks.Sites.Conormal Stacks.Sites.FreeAlgebra

variable {S : Type u} [Category.{v} S] (J : GrothendieckTopology S)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (A B C : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (b : B ⟶ C)

/-! ### The second morphism of presentations -/

variable (f : A ⟶ B) (β : B ⟶ C) (γ : B ⟶ B) (hβ : γ ≫ b = β) (hf : a ≫ γ = f)

omit [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hβ hf in
/-- The data `γ` makes the two morphisms `f` and `β` into a commutative square from `a` to
`b`. -/
theorem towerSquare : a ≫ β = f ≫ b := by
  rw [← hβ, ← hf, Category.assoc]

/-- The morphism of presentations `A[B] ⟶ B[C]` sending the variable `[x]` to the coefficient
`γ(x)`: it is the canonical presentation `A[B] ⟶ B` followed by `γ` and by the inclusion of the
coefficients of `B[C]`. -/
noncomputable abbrev towerConstMap :
    freeAlgebraSheaf J A (underlyingPresheaf J B) ⟶
      freeAlgebraSheaf J B (underlyingPresheaf J C) :=
  canonicalPresentation J A B a ≫ γ ≫
    freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hβ in
/-- The second morphism of presentations is compatible with the two canonical
presentations. -/
theorem towerConstMap_comp_presentation :
    towerConstMap J A B C a γ ≫ canonicalPresentation J B C b =
      canonicalPresentation J A B a ≫ β := by
  change (canonicalPresentation J A B a ≫ γ ≫
    freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C)) ≫
      canonicalPresentation J B C b = _
  rw [Category.assoc, Category.assoc, canonicalPresentation_comp_coefficientMap, hβ]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hf in
/-- On coefficients the second morphism of presentations is `f`. -/
theorem coefficientMap_comp_towerConstMap :
    f ≫ freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C) =
      freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B) ≫
        towerConstMap J A B C a γ := by
  change _ = freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B) ≫
    (canonicalPresentation J A B a ≫ γ ≫
      freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C))
  rw [← Category.assoc, ← Category.assoc, canonicalPresentation_comp_coefficientMap, hf]

/-! ### The homotopy on the conormal terms -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
  /-- The morphism of presentations `A[B] ⟶ B[C]` attached to the square is compatible with the
  two canonical presentations. -/
  private theorem canonicalFreeAlgebraMapOfSquare_comp_presentation (hβ : γ ≫ b = β)
      (hf : a ≫ γ = f) :
      canonicalFreeAlgebraMapOfSquare J A B B C f β ≫ canonicalPresentation J B C b =
        canonicalPresentation J A B a ≫ β :=
    freeAlgebraMapOfSquare_comp_canonicalPresentation J A B B C a b f β
      (towerSquare J A B C a b f β γ hβ hf)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
  /-- On coefficients the morphism of presentations `A[B] ⟶ B[C]` attached to the square is `f`. -/
  private theorem coefficientMap_comp_canonicalFreeAlgebraMapOfSquare :
      f ≫ freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C) =
        freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B) ≫
          canonicalFreeAlgebraMapOfSquare J A B B C f β :=
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A B _ _ f
      (underlyingPresheafMap J B C β)).symm

/-- The homotopy `B ⊗_{A[B]} Ω_{A[B]/A} ⟶ K/K²` attached to the tower `A ⟶ B ⟶ C`: on local
sections it sends `x ⊗ d t` to `x · ([β t] - γ t)`, the conormal class in the canonical
presentation `B[C] ⟶ C` of the difference between the variable `[β t]` and the coefficient
`γ t`. -/
noncomputable def naiveCotangentTowerHomotopy :
    (canonicalConormalSequence.{v, u, w, z} J A B a).X₂ ⟶
      (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).obj
        ((canonicalConormalSequence.{v, u, w, z} J B C b).X₁) :=
  conormalHomotopyOfSquare.{v, u, w, z} J A B
    (freeAlgebraSheaf J A (underlyingPresheaf J B))
    (freeAlgebraSheaf J B (underlyingPresheaf J C)) B C
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C))
    (canonicalPresentation J A B a) (canonicalPresentation J B C b)
    (canonicalFreeAlgebraMapOfSquare J A B B C f β) (towerConstMap J A B C a γ) β f
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A B B C a b f β
      (towerSquare J A B C a b f β γ hβ hf))
    (towerConstMap_comp_presentation J A B C a b β γ hβ)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A B _ _ f
      (underlyingPresheafMap J B C β)).symm
    (coefficientMap_comp_towerConstMap J A B C a f γ hf)

/-- In degree `-1` the chain map attached to the tower is the homotopy precomposed with the
left-hand map of the conormal sequence of `B` over `A`. -/
theorem naiveCotangentConormalMapOfTower_eq :
    naiveCotangentConormalMapOfSquare.{v, u, w, z} J A B a B C b f β
        (towerSquare J A B C a b f β γ hβ hf) =
      (canonicalConormalSequence.{v, u, w, z} J A B a).f ≫
        naiveCotangentTowerHomotopy.{v, u, w, z} J A B C a b f β γ hβ hf :=
  conormalSheafMapOfSquare_eq_comp_homotopy.{v, u, w, z} J A B
    (freeAlgebraSheaf J A (underlyingPresheaf J B))
    (freeAlgebraSheaf J B (underlyingPresheaf J C)) B C
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C))
    (canonicalPresentation J A B a) (canonicalPresentation J B C b) γ β f
    (towerConstMap_comp_presentation J A B C a b β γ hβ)
    (coefficientMap_comp_towerConstMap J A B C a f γ hf)
    (canonicalFreeAlgebraMapOfSquare J A B B C f β)
    (canonicalFreeAlgebraMapOfSquare_comp_presentation J A B C a b f β γ hβ hf)
    (coefficientMap_comp_canonicalFreeAlgebraMapOfSquare J A B C f β)

/-- In degree `0` the chain map attached to the tower is the homotopy postcomposed with the
left-hand map of the conormal sequence of `C` over `B`. -/
theorem naiveCotangentTensorMapOfTower_eq :
    naiveCotangentTensorMapOfSquare.{v, u, w, z} J A B a B C b f β
        (towerSquare J A B C a b f β γ hβ hf) =
      naiveCotangentTowerHomotopy.{v, u, w, z} J A B C a b f β γ hβ hf ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite β)).map
          (canonicalConormalSequence.{v, u, w, z} J B C b).f :=
  tensorSheafMapOfSquare_eq_homotopy_comp.{v, u, w, z} J A B
    (freeAlgebraSheaf J A (underlyingPresheaf J B))
    (freeAlgebraSheaf J B (underlyingPresheaf J C)) B C
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C))
    (canonicalPresentation J A B a) (canonicalPresentation J B C b) γ β f
    (towerConstMap_comp_presentation J A B C a b β γ hβ)
    (coefficientMap_comp_towerConstMap J A B C a f γ hf)
    (canonicalFreeAlgebraMapOfSquare J A B B C f β)
    (canonicalFreeAlgebraMapOfSquare_comp_presentation J A B C a b f β γ hβ hf)
    (coefficientMap_comp_canonicalFreeAlgebraMapOfSquare J A B C f β)

/-! ### The null homotopy of chain complexes -/

/-- The target of the chain map attached to the tower: the naive cotangent complex of `C` over
`B`, read termwise as a complex of sheaves of `B`-modules. -/
noncomputable abbrev towerTargetComplex :
    CochainComplex
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) ℤ :=
  ((_root_.SheafOfModules.restrictScalars.{max w u v z}
    (underlyingRingHomOfSite β)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (naiveCotangentComplex.{v, u, w, z} J B C b)

/-- The canonical `B`-linear chain map `NL_{B/A} ⟶ NL_{C/B}` attached to the tower
`A ⟶ B ⟶ C`. -/
noncomputable abbrev naiveCotangentComplexMapOfTower :
    naiveCotangentComplex.{v, u, w, z} J A B a ⟶
      towerTargetComplex.{v, u, w, z} J B C b β :=
  naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a B C b f β
    (towerSquare J A B C a b f β γ hβ hf)

/-- The degree `0` to degree `-1` component of the null homotopy, read inside the two
complexes. -/
noncomputable def naiveCotangentTowerHomotopyHom :
    (naiveCotangentComplex.{v, u, w, z} J A B a).X 0 ⟶
      (towerTargetComplex.{v, u, w, z} J B C b β).X (-1) :=
  eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A B a) ≫
    naiveCotangentTowerHomotopy.{v, u, w, z} J A B C a b f β γ hβ hf ≫
      (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).map
        (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J B C b).symm)

/-- The bigraded map underlying the null homotopy: it is concentrated in bidegree
`(0, -1)`. -/
noncomputable def naiveCotangentTowerHomotopyBigraded (i j : ℤ) :
    (naiveCotangentComplex.{v, u, w, z} J A B a).X i ⟶
      (towerTargetComplex.{v, u, w, z} J B C b β).X j :=
  if hij : i = 0 ∧ j = -1 then
    eqToHom (congrArg (naiveCotangentComplex.{v, u, w, z} J A B a).X hij.1) ≫
      naiveCotangentTowerHomotopyHom.{v, u, w, z} J A B C a b f β γ hβ hf ≫
        eqToHom (congrArg (towerTargetComplex.{v, u, w, z} J B C b β).X hij.2.symm)
  else 0

/-- The bigraded map underlying the null homotopy vanishes outside bidegree `(0, -1)`. -/
theorem naiveCotangentTowerHomotopyBigraded_eq_zero (i j : ℤ) (hij : ¬(i = 0 ∧ j = -1)) :
    naiveCotangentTowerHomotopyBigraded.{v, u, w, z} J A B C a b f β γ hβ hf i j = 0 :=
  dite_eq_right hij

/-- In bidegree `(0, -1)` the bigraded map underlying the null homotopy is
`naiveCotangentTowerHomotopyHom`. -/
theorem naiveCotangentTowerHomotopyBigraded_zero_negOne :
    naiveCotangentTowerHomotopyBigraded.{v, u, w, z} J A B C a b f β γ hβ hf 0 (-1) =
      naiveCotangentTowerHomotopyHom.{v, u, w, z} J A B C a b f β γ hβ hf := by
  rw [naiveCotangentTowerHomotopyBigraded, dite_eq_left ⟨rfl, rfl⟩]
  simp

/-- The differential of the target complex out of degree `-1`. -/
private theorem towerTargetComplex_d_negOne_zero :
    (towerTargetComplex.{v, u, w, z} J B C b β).d (-1) 0 =
      (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).map
          (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J B C b)) ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).map
          (canonicalConormalSequence.{v, u, w, z} J B C b).f ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).map
          (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J B C b).symm) := by
  change (_root_.SheafOfModules.restrictScalars.{max w u v z}
    (underlyingRingHomOfSite β)).map ((naiveCotangentComplex.{v, u, w, z} J B C b).d (-1) 0) = _
  rw [naiveCotangentComplex_d_negOne_zero, Functor.map_comp, Functor.map_comp]

/-- The chain map `NL_{B/A} ⟶ NL_{C/B}` attached to a tower `A ⟶ B ⟶ C` is null homotopic, by
a homotopy concentrated in bidegree `(0, -1)`, where it is the map determined on local sections
by `x ⊗ d t ↦ x · ([β t] - γ t)`. -/
noncomputable def naiveCotangentTowerNullHomotopy :
    Homotopy (naiveCotangentComplexMapOfTower.{v, u, w, z} J A B C a b f β γ hβ hf) 0 where
  hom := naiveCotangentTowerHomotopyBigraded.{v, u, w, z} J A B C a b f β γ hβ hf
  zero i j hij :=
    naiveCotangentTowerHomotopyBigraded_eq_zero.{v, u, w, z} J A B C a b f β γ hβ hf i j
      (by rintro ⟨rfl, rfl⟩; exact hij (by decide))
  comm i := by
    by_cases h1 : i = -1
    · subst h1
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) from by decide),
        naiveCotangentTowerHomotopyBigraded_eq_zero J A B C a b f β γ hβ hf (-1) (-2)
          (by rintro ⟨h0, -⟩; exact absurd h0 (by decide)),
        zero_comp, add_zero, HomologicalComplex.zero_f, add_zero,
        naiveCotangentTowerHomotopyBigraded_zero_negOne,
        naiveCotangentComplexMapOfSquare_f_negOne,
        naiveCotangentComplex_d_negOne_zero,
        naiveCotangentTowerHomotopyHom,
        naiveCotangentConormalMapOfTower_eq.{v, u, w, z} J A B C a b f β γ hβ hf]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    · by_cases h0 : i = 0
      · subst h0
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from by decide),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide),
          naiveCotangentTowerHomotopyBigraded_eq_zero J A B C a b f β γ hβ hf 1 0
            (by rintro ⟨h0, -⟩; exact absurd h0 (by decide)),
          comp_zero, zero_add, HomologicalComplex.zero_f, add_zero,
          naiveCotangentTowerHomotopyBigraded_zero_negOne,
          naiveCotangentComplexMapOfSquare_f_zero,
          towerTargetComplex_d_negOne_zero,
          naiveCotangentTowerHomotopyHom,
          naiveCotangentTensorMapOfTower_eq.{v, u, w, z} J A B C a b f β γ hβ hf]
        simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
      · exact (naiveCotangentComplex_isZero_X J A B a i h1 h0).eq_of_src _ _

/-! ### The local formula for the homotopy -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The variable `[t]` of `A[B]` attached to a local section `t` of `B`, as a local section of
the sheaf of rings `A[B]`. -/
noncomputable def variableSection (X : Sᵒᵖ) (t : (underlyingPresheaf J B).obj X) :
    (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj X :=
  (freeAlgebraSheafVariable J A (underlyingPresheaf J B)).app X t

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The canonical presentation `A[B] ⟶ B` sends the variable `[t]` to `t`. -/
theorem canonicalPresentation_variableSection (X : Sᵒᵖ) (t : (underlyingPresheaf J B).obj X) :
    (canonicalPresentation J A B a).hom.app X (variableSection J A B X t) = t := by
  have h := congrArg (fun φ : (underlyingPresheaf J B) ⟶ (underlyingPresheaf J B) ↦ φ.app X t)
    (freeAlgebraSheafVariable_comp_canonicalPresentation J A B a)
  simpa [variableSection] using h

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- On the coefficients `B` of `B[C]` the canonical presentation `B[C] ⟶ C` is `b`. -/
theorem canonicalPresentation_coefficientSection (X : Sᵒᵖ) (t : B.obj.obj X) :
    (canonicalPresentation J B C b).hom.app X
        ((freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C)).hom.app X t) =
      b.hom.app X t := by
  have h := congrArg (fun φ : B ⟶ C ↦ φ.hom.app X t)
    (canonicalPresentation_comp_coefficientMap J B C b)
  simpa using h

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The morphism of presentations `A[B] ⟶ B[C]` attached to the square sends the variable `[t]`
to the variable `[β t]`. -/
theorem canonicalFreeAlgebraMapOfSquare_variableSection (X : Sᵒᵖ) (t : B.obj.obj X) :
    (canonicalFreeAlgebraMapOfSquare J A B B C f β).hom.app X (variableSection J A B X t) =
      variableSection J B C X (β.hom.app X t) := by
  have h := congrArg (fun φ : (underlyingPresheaf J B) ⟶
      underlyingPresheaf J (freeAlgebraSheaf J B (underlyingPresheaf J C)) ↦ φ.app X t)
    (freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare J A B (underlyingPresheaf J B)
      (underlyingPresheaf J C) f (underlyingPresheafMap J B C β))
  simpa [variableSection] using h

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The second morphism of presentations `A[B] ⟶ B[C]` sends the variable `[t]` to the
coefficient `γ t`. -/
theorem towerConstMap_variableSection (X : Sᵒᵖ) (t : B.obj.obj X) :
    (towerConstMap J A B C a γ).hom.app X (variableSection J A B X t) =
      (freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C)).hom.app X
        (γ.hom.app X t) := by
  simp only [towerConstMap, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [canonicalPresentation_variableSection J A B a X t]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hβ in
/-- For a local section `t` of `B`, the difference `[β t] - γ t` between the variable `[β t]`
and the coefficient `γ t`, as an element of the kernel of the canonical presentation
`B[C] ⟶ C`. -/
noncomputable def towerHomotopyRelation (X : Sᵒᵖ) (t : B.obj.obj X) :
    kernelIdeal (canonicalPresentation J B C b).hom X :=
  ⟨variableSection J B C X (β.hom.app X t) -
      (freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C)).hom.app X (γ.hom.app X t),
    by
      change (canonicalPresentation J B C b).hom.app X
        (variableSection J B C X (β.hom.app X t) -
          (freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C)).hom.app X
            (γ.hom.app X t)) = 0
      rw [map_sub, canonicalPresentation_variableSection J B C b X (β.hom.app X t),
        canonicalPresentation_coefficientSection J B C b X (γ.hom.app X t)]
      have h2 : b.hom.app X (γ.hom.app X t) = β.hom.app X t :=
        congrArg (fun φ : B ⟶ C ↦ φ.hom.app X t) hβ
      rw [h2, sub_self]⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hβ in
/-- The relation attached to a local section `t` of `B` is literally `[β t] - γ t`. -/
theorem towerHomotopyRelation_coe (X : Sᵒᵖ) (t : B.obj.obj X) :
    ((towerHomotopyRelation J B C b β γ hβ X t :
        (freeAlgebraSheaf J B (underlyingPresheaf J C)).obj.obj X)) =
      variableSection J B C X (β.hom.app X t) -
        (freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C)).hom.app X
          (γ.hom.app X t) := rfl

include hβ hf in
/-- The homotopy `B ⊗_{A[B]} Ω_{A[B]/A} ⟶ K/K²` of the tower sends the local section `1 ⊗ d[t]`
to the conormal class of `[β t] - γ t`. -/
theorem naiveCotangentTowerHomotopy_tensorDifferential_variableSection (X : Sᵒᵖ)
    (t : B.obj.obj X) :
    (naiveCotangentTowerHomotopy.{v, u, w, z} J A B C a b f β γ hβ hf).val.app X
        (tensorDifferential.{v, u, w, z} J A
          (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
          (canonicalPresentation J A B a) X (variableSection J A B X t)) =
      conormalClass.{v, u, w, z} J B
        (freeAlgebraSheaf J B (underlyingPresheaf J C)) C
        (freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C))
        (canonicalPresentation J B C b) X
        (towerHomotopyRelation J B C b β γ hβ X t) := by
  refine (conormalHomotopyOfSquare_tensorDifferential.{v, u, w, z} J A B
    (freeAlgebraSheaf J A (underlyingPresheaf J B))
    (freeAlgebraSheaf J B (underlyingPresheaf J C)) B C
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C))
    (canonicalPresentation J A B a) (canonicalPresentation J B C b)
    (canonicalFreeAlgebraMapOfSquare J A B B C f β) (towerConstMap J A B C a γ) β f
    (canonicalFreeAlgebraMapOfSquare_comp_presentation J A B C a b f β γ hβ hf)
    (towerConstMap_comp_presentation J A B C a b β γ hβ)
    (coefficientMap_comp_canonicalFreeAlgebraMapOfSquare J A B C f β)
    (coefficientMap_comp_towerConstMap J A B C a f γ hf)
    X (variableSection J A B X t)).trans ?_
  congr 1
  apply Subtype.ext
  rw [subOfSquare_coe, towerHomotopyRelation_coe,
    canonicalFreeAlgebraMapOfSquare_variableSection J A B C f β X t,
    towerConstMap_variableSection J A B C a γ X t]

end Stacks.SheafOfModules

end
