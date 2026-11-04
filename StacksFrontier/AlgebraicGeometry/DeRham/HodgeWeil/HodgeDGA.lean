module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismCupProduct
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamExistence
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DeRhamComparisonAdjoint
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapOnSections
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFiltrationWedgeRespects
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.NaiveCupProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardIdealLift

/-!
# The Hodge complex as a sheaf of differential graded algebras

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^p` be the sheaf of relative differential `p`-forms. The *Hodge complex*

`ℋ = ⨁_p Ω^p[-p]`

is the complex whose degree-`p` term is `Ω^p` and whose differential is zero. Wedge
multiplication makes it a sheaf of differential graded `A`-algebras: the Leibniz rule holds
trivially, since the differential vanishes. Its cohomology is Hodge cohomology,
`H^n(X, ℋ) = ⨁_{p + q = n} H^q(X, Ω^p)`, and through this structure the construction
`ξ ↦ ξ'` of Remark 0FU7 applies to Hodge cohomology in the same way as to de Rham cohomology.

This file builds that structure and proves property (3) of Remark 0FU7 for it: for a class
`ξ ∈ H^n(X, ℋ)`, the morphism `ξ' : ℋ ⟶ ℋ[n]` of `D(A)` attached to `ξ` sends `η` to the cup
product `ξ ∪ η`. That statement is first proved for an arbitrary sheaf of differential graded
`A`-algebras whose underlying complex is bounded below.

For a commutative square of schemes with `g' : X' ⟶ X` over `g : S' ⟶ S`, and
`g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` the induced morphism of ringed spaces, pulling back
differential forms is a map of complexes `ℋ_{X/S} ⟶ (g₀)_*ℋ_{X'/S'}` which is multiplicative and
unital on local sections.

## Main definitions

* `Stacks.HodgeWeil.hodgeComplexInt`: the complex `⨁_p Ω^p[-p]`, indexed by `ℤ`, with zero
  differential.
* `Stacks.HodgeWeil.hodgeDGA`: **the Hodge complex as a sheaf of differential graded
  `A`-algebras**, with wedge multiplication.
* `Stacks.HodgeWeil.dgaCohomologyCup`: the cup product `H^n(X, 𝒜) × H^m(X, 𝒜) ⟶ H^{n+m}(X, 𝒜)`
  on the cohomology of a sheaf of differential graded algebras `𝒜`: the global cup product of
  Section 0FKU followed by the multiplication `Tot(𝒜 ⊗ 𝒜) ⟶ 𝒜`.
* `Stacks.HodgeWeil.hodgeDgaPushforward`: the canonical map `ℋ_{X/S} ⟶ (g₀)_*ℋ_{X'/S'}` of a
  commutative square of schemes.

## Main results

* `Stacks.HodgeWeil.isStrictlyGE_hodgeDGA`: the Hodge complex lives in nonnegative degrees.
* `Stacks.HodgeWeil.hodgeDGA_mul`, `Stacks.HodgeWeil.hodgeDGA_one`: the multiplication and the
  unit of `ℋ` are wedge multiplication and the unit of the exterior algebra.
* `Stacks.HodgeWeil.dgaCohomologyCup_eq_dgaClassMorphism`: for a bounded below sheaf of
  differential graded algebras `𝒜` and `ξ ∈ H^n(X, 𝒜)`, the morphism `ξ' : 𝒜 ⟶ 𝒜[n]` of
  Section 0FU3 acts on cohomology by `η ↦ ξ ∪ η`.
* `Stacks.HodgeWeil.hodgeDgaCup_eq_dgaClassMorphism`: **property (3) of Remark 0FU7 for the
  Hodge complex.**
* `Stacks.HodgeWeil.hodgeDgaPushforward_mul`, `Stacks.HodgeWeil.hodgeDgaPushforward_one`: the
  canonical map of Hodge complexes is multiplicative and unital on local sections.

## Implementation notes

The terms of `Stacks.HodgeWeil.hodgeComplexInt` are taken to be *literally* the terms of the
relative de Rham complex extended by zero, `AlgebraicGeometry.SheafOfModules.deRhamComplexInt`,
for the de Rham differential `AlgebraicGeometry.SheafOfModules.deRhamDifferential`. The
multiplication and the unit of the de Rham differential graded algebra
`AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra` are maps between those terms,
and their associativity and unit laws never involve the differential, so they are reused as they
stand. Only the Leibniz rule changes, and it reads `0 = 0`. Likewise the components of
`Stacks.HodgeWeil.hodgeDgaPushforward` are those of
`Stacks.DeRhamBaseChange.deRhamPushforwardInt`, and they commute with the zero differentials.

## References

* [Stacks Project, Remark 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Section 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
* [Stacks Project, Tag 0FU6](https://stacks.math.columbia.edu/tag/0FU6)
* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open scoped TensorProduct

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}

/-! ### The cup product on the cohomology of a sheaf of differential graded algebras -/

section Generic

variable (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
  (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A))

/-- **The cup product on the cohomology of a sheaf of differential graded algebras**

`∪ : H^n(X, 𝒜) × H^m(X, 𝒜) ⟶ H^{n + m}(X, 𝒜)`:

the global cup product of Cohomology, Section 0FKU, followed by the canonical map from the derived
to the ordinary tensor product, and by the multiplication `Tot(𝒜 ⊗_A 𝒜) ⟶ 𝒜`, the action of `𝒜`
on itself as a right differential graded module. The class `ξ` is the first factor. -/
def dgaCohomologyCup (n m : ℤ) (ξ : dgaCohomology 𝒜 n) (η : dgaCohomology 𝒜 m) :
    dgaCohomology 𝒜 (n + m) :=
  (totalCupPairing (S := baseRingedSpace A) 𝒜.complex 𝒜.complex n m ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) (n + m)).map
      ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map
        (dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))))).hom
    (ξ ⊗ₜ η)

/-- **Section 0FU3, property (3) of Remark 0FU7, for a bounded below sheaf of differential graded
algebras.** The morphism `ξ' : 𝒜 ⟶ 𝒜[n]` of `D(A)` attached to `ξ ∈ H^n(X, 𝒜)` sends
`η ∈ H^m(X, 𝒜)` to `ξ ∪ η ∈ H^{n + m}(X, 𝒜)`: the map `ξ'` induces on `H^m(X, -)`, read through
`H^m(X, 𝒜[n]) = H^{n + m}(X, 𝒜)`, is left cup product with `ξ`. -/
theorem dgaCohomologyCup_eq_dgaClassMorphism (h𝒜 : ∃ k : ℤ, 𝒜.complex.IsStrictlyGE k)
    (n m : ℤ) (ξ : dgaCohomology 𝒜 n) (η : dgaCohomology 𝒜 m) :
    dgaCohomologyCup 𝒜 n m ξ η =
      (dgaShiftHomologyIso 𝒜 n m (n + m) rfl).hom
        ((DerivedCategory.homologyFunctor _ m).map
          ((derivedSectionsBase A).map (dgaClassMorphism 𝒜 n ξ)) η) := by
  have G := derivedForgetShiftedHom_cup (S := baseRingedSpace A) 𝒜 h𝒜 n m
    (dgaClassDerivedEquiv 𝒜 n ξ)
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing (baseRingedSpace A))
      (cohomologyModule (S := baseRingedSpace A) (DerivedCategory.Q.obj 𝒜.complex) m) η))
  have G1 := ConcreteCategory.congr_hom G 1
  have hξ := (globalCycleClass_unitCycleHom_comp_apply (S := baseRingedSpace A)
    (DerivedCategory.Q.map (dgUnitComplexHom 𝒜)) (dgaClassMorphism 𝒜 n ξ)
    (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU (baseSections (baseRingedSpace A))
      (DerivedCategory.Q.obj 𝒜.complex) n 0 n (add_zero n)).hom).trans
    (dgaEvalOne_dgaClassMorphism 𝒜 n ξ)
  have hη : (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing (baseRingedSpace A))
      (cohomologyModule (S := baseRingedSpace A) (DerivedCategory.Q.obj 𝒜.complex) m) η)).hom 1 =
      η :=
    one_smul _ _
  refine Eq.trans ?_ (G1.symm.trans ?_)
  · exact (congrArg (fun t => (totalCupPairing (S := baseRingedSpace A) 𝒜.complex 𝒜.complex n m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) (n + m)).map
          ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map
            (dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))))).hom
          (t ⊗ₜ η)) hξ.symm).trans
      (congrArg (fun t => (totalCupPairing (S := baseRingedSpace A) 𝒜.complex 𝒜.complex n m ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) (n + m)).map
          ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map
            (dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))))).hom
          (_ ⊗ₜ t)) hη.symm)
  · exact congrArg (fun t => (dgaShiftHomologyIso 𝒜 n m (n + m) rfl).hom.hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) (m)).map
          ((baseSections (baseRingedSpace A)).map ((dgaClassMorphism 𝒜 n ξ)))).hom t)) hη

end Generic

/-! ### The Hodge complex -/

variable {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- **The Hodge complex** `ℋ = ⨁_p Ω^p[-p]`, indexed by `ℤ`: its degree-`p` term is the sheaf
`Ω^p` of relative differential `p`-forms, zero in negative degrees, and its differential is zero.
The terms are those of the relative de Rham complex extended by zero. -/
def hodgeComplexInt : CochainComplex
    (_root_.SheafOfModules.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A)) ℤ where
  X := (deRhamComplexInt B (deRhamDifferential B)).X
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := Limits.zero_comp

/-- The terms of the Hodge complex are those of the extended relative de Rham complex. -/
@[simp]
theorem hodgeComplexInt_X (i : ℤ) :
    (hodgeComplexInt B).X i = (deRhamComplexInt B (deRhamDifferential B)).X i := rfl

/-- The differential of the Hodge complex vanishes. -/
@[simp]
theorem hodgeComplexInt_d (i j : ℤ) : (hodgeComplexInt B).d i j = 0 := rfl

/-- In a nonnegative degree `i` the term of the Hodge complex **is** the sheaf `Ω^i` of relative
differential `i`-forms. -/
theorem hodgeComplexInt_X_of_nonneg (i : ℤ) (hi : 0 ≤ i) :
    (hodgeComplexInt B).X i = deRhamTermInt B i :=
  deRhamComplexInt_X_of_nonneg B (deRhamDifferential B) i hi

/-- The Hodge complex lives in nonnegative degrees. -/
instance isStrictlyGE_hodgeComplexInt : (hodgeComplexInt B).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact CochainComplex.isZero_of_isStrictlyGE (deRhamComplexInt B (deRhamDifferential B)) 0 i hi

/-- The local sections of a negative-degree term of the Hodge complex vanish. -/
theorem hodgeComplexInt_section_eq_zero (a : ℤ) (ha : a < 0) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((hodgeComplexInt B).X a).val.obj U) : x = 0 := by
  have hz : Limits.IsZero ((hodgeComplexInt B).X a) :=
    CochainComplex.isZero_of_isStrictlyGE (hodgeComplexInt B) 0 a ha
  exact (ModuleCat.isZero_iff_subsingleton.mp
    (Functor.map_isZero (_root_.SheafOfModules.evaluation _ U) hz)).elim x 0

/-- **The Hodge complex `⨁_p Ω^p[-p]` as a sheaf of differential graded `A`-algebras**: wedge
multiplication and the unit of the exterior algebra, with zero differential. -/
def hodgeDGA : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
    (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A) where
  complex := hodgeComplexInt B
  mul := (deRhamDifferentialGradedAlgebra B (deRhamDifferential B)).mul
  one := (deRhamDifferentialGradedAlgebra B (deRhamDifferential B)).one
  mul_assoc := (deRhamDifferentialGradedAlgebra B (deRhamDifferential B)).mul_assoc
  one_mul := (deRhamDifferentialGradedAlgebra B (deRhamDifferential B)).one_mul
  mul_one := (deRhamDifferentialGradedAlgebra B (deRhamDifferential B)).mul_one
  leibniz n m U x y := by
    have h0 : ∀ {i j : ℤ} (z : ((hodgeComplexInt B).X i).val.obj U),
        ((hodgeComplexInt B).d i j).val.app U z = 0 := fun _ => rfl
    simp only [h0, map_zero, AddMonoidHom.zero_apply, _root_.SheafOfModules.gradedCast_zero,
      smul_zero, add_zero]

/-- The complex underlying the Hodge differential graded algebra is the Hodge complex. -/
@[simp]
theorem hodgeDGA_complex : (hodgeDGA B).complex = hodgeComplexInt B := rfl

/-- The Hodge complex lives in nonnegative degrees. -/
instance isStrictlyGE_hodgeDGA : (hodgeDGA B).complex.IsStrictlyGE 0 :=
  isStrictlyGE_hodgeComplexInt B

/-- Multiplication in the Hodge differential graded algebra is wedge multiplication of
differential forms, on every pair of homogeneous local sections. -/
theorem hodgeDGA_mul (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : ((hodgeDGA B).complex.X (p : ℤ)).val.obj U)
    (η : ((hodgeDGA B).complex.X (q : ℤ)).val.obj U)
    (ω' : (B.exteriorPower p).val.obj U) (η' : (B.exteriorPower q).val.obj U)
    (hω : HEq ω ω') (hη : HEq η η') :
    HEq (((hodgeDGA B).mul (p : ℤ) (q : ℤ)).app U ω η) (formProduct B p q U ω' η') :=
  deRhamDifferentialGradedAlgebra_mul B (deRhamDifferential B) p q U ω η ω' η' hω hη

/-- The unit of the Hodge differential graded algebra is the unit of the exterior algebra. -/
theorem hodgeDGA_one (U : (Opens X.carrier)ᵒᵖ) :
    HEq ((hodgeDGA B).one.eval U) (B.exterior.one.eval U) :=
  deRhamDifferentialGradedAlgebra_one B (deRhamDifferential B) U

/-! ### Property (3) of Remark 0FU7 for Hodge cohomology -/

/-- The cup product on the cohomology `H^*(X, ℋ)` of the Hodge complex. -/
abbrev hodgeDgaCup (n m : ℤ) (ξ : dgaCohomology (hodgeDGA B) n)
    (η : dgaCohomology (hodgeDGA B) m) : dgaCohomology (hodgeDGA B) (n + m) :=
  dgaCohomologyCup (hodgeDGA B) n m ξ η

/-- **Stacks Project, Remark 0FU7, property (3), for the Hodge complex.** The morphism
`ξ' : ℋ ⟶ ℋ[n]` of `D(A)` attached by Section 0FU3 to `ξ ∈ H^n(X, ℋ)` sends `η ∈ H^m(X, ℋ)` to
`ξ ∪ η ∈ H^{n + m}(X, ℋ)`. -/
theorem hodgeDgaCup_eq_dgaClassMorphism (n m : ℤ) (ξ : dgaCohomology (hodgeDGA B) n)
    (η : dgaCohomology (hodgeDGA B) m) :
    hodgeDgaCup B n m ξ η =
      (dgaShiftHomologyIso (hodgeDGA B) n m (n + m) rfl).hom
        ((DerivedCategory.homologyFunctor _ m).map
          ((derivedSectionsBase A).map (dgaClassMorphism (hodgeDGA B) n ξ)) η) :=
  dgaCohomologyCup_eq_dgaClassMorphism (hodgeDGA B) ⟨0, isStrictlyGE_hodgeDGA B⟩ n m ξ η

/-! ### Pulling back the Hodge complex along a commutative square of schemes -/

section Pushforward

open Stacks.DeRhamBaseChange Stacks.DeRhamDirectImage

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **The canonical map of Hodge complexes `ℋ_{X/S} ⟶ (g₀)_*ℋ_{X'/S'}`** of a commutative square
of schemes, for `g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)`: in degree `p` it is the pullback of
differential `p`-forms, the degree-`p` component of the canonical map of extended de Rham
complexes `Stacks.DeRhamBaseChange.deRhamPushforwardInt`. Both differentials vanish, so these
components form a map of complexes. -/
def hodgeDgaPushforward :
    (hodgeDGA (Scheme.Hom.deRhamAlgebras f)).complex ⟶
      (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (inverseImageBaseMap g' f' f g w :
          baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf) ⟶
            baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).obj
        (hodgeDGA (Scheme.Hom.deRhamAlgebras f')).complex where
  f n := (deRhamPushforwardInt g' f' f g w).f n
  comm' i j _ := by
    refine (congrArg ((deRhamPushforwardInt g' f' f g w).f i ≫ ·)
      ((StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g' f' f g w)).map_zero _
        _)).trans (Limits.comp_zero.trans ?_)
    exact Limits.zero_comp.symm

/-- In each degree the canonical map of Hodge complexes is that of extended de Rham complexes. -/
theorem hodgeDgaPushforward_f (n : ℤ) :
    (hodgeDgaPushforward g' f' f g w).f n = (deRhamPushforwardInt g' f' f g w).f n := rfl

/-- **The canonical map of Hodge complexes on local sections** is the pullback of differential
forms, in every nonnegative degree. -/
theorem hodgeDgaPushforward_f_app_heq (i : ℤ) (q : ℕ) (hi : i = q) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((hodgeDGA (Scheme.Hom.deRhamAlgebras f)).complex.X i).val.obj U)
    (x' : Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), U.unop)) (hx : HEq x x') :
    HEq (((hodgeDgaPushforward g' f' f g w).f i).val.app U x)
      (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (q : ℤ) U.unop x') := by
  subst hi
  rw [hodgeDgaPushforward_f, deRhamPushforwardInt_f g' f' f g w q]
  refine (heq_of_eq (_root_.SheafOfModules.comp_comp_val_app_eq _ _ _ rfl rfl rfl)).trans ?_
  refine (Stacks.DeRhamSmooth.extendXIso_inv_val_app_heq _ _ _ _).trans ?_
  have h₁ : ((ProperSmoothDeRham.deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat
      (i := q) rfl).hom.val.app U x = x' := by
    refine eq_of_heq (HEq.trans ?_ hx)
    simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.hom]
    exact Stacks.DeRhamSmooth.eqToHom_val_app_heq_of_eq _ _ _
  exact heq_of_eq ((congrArg (fun z => ((deRhamPushforwardChain g' f' f g w).f q).val.app U z)
    h₁).trans rfl)

/-- **The canonical map of Hodge complexes is multiplicative on local sections**: it carries the
wedge product of two local forms to the wedge product of their pullbacks. -/
theorem hodgeDgaPushforward_mul (a b : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((hodgeDGA (Scheme.Hom.deRhamAlgebras f)).complex.X a).val.obj U)
    (y : ((hodgeDGA (Scheme.Hom.deRhamAlgebras f)).complex.X b).val.obj U) :
    ((hodgeDgaPushforward g' f' f g w).f (a + b)).val.app U
        (((hodgeDGA (Scheme.Hom.deRhamAlgebras f)).mul a b).app U x y) =
      ((hodgeDGA (Scheme.Hom.deRhamAlgebras f')).mul a b).app
        ((Opens.map (inverseImageBaseMap g' f' f g w :
          baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf) ⟶
            baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
              S.sheaf)).hom.base).op.obj U)
        (((hodgeDgaPushforward g' f' f g w).f a).val.app U x)
        (((hodgeDgaPushforward g' f' f g w).f b).val.app U y) := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb
      let x' : Γ(Scheme.Hom.relativeDifferentialForms f (m : ℤ), U.unop) :=
        cast (congrArg (fun M : _root_.SheafOfModules.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) =>
              (M.val.obj U : Type u))
          (hodgeComplexInt_X_of_nonneg (Scheme.Hom.deRhamAlgebras f) (m : ℤ)
            (Int.natCast_nonneg m))) x
      let y' : Γ(Scheme.Hom.relativeDifferentialForms f (n : ℤ), U.unop) :=
        cast (congrArg (fun M : _root_.SheafOfModules.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) =>
              (M.val.obj U : Type u))
          (hodgeComplexInt_X_of_nonneg (Scheme.Hom.deRhamAlgebras f) (n : ℤ)
            (Int.natCast_nonneg n))) y
      have hx : HEq x x' := (cast_heq _ x).symm
      have hy : HEq y y' := (cast_heq _ y).symm
      have hL := hodgeDgaPushforward_f_app_heq g' f' f g w ((m : ℤ) + (n : ℤ)) (m + n)
        (by push_cast; rfl) U
        (((hodgeDGA (Scheme.Hom.deRhamAlgebras f)).mul m n).app U x y)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra f).mul m n).app (op U.unop) x' y')
        (hodgeDGA_mul (Scheme.Hom.deRhamAlgebras f) m n U x y x' y' hx hy)
      have hM := Scheme.Hom.relativeDifferentialFormsPullback_mul g' f f' g w (m : ℤ) (n : ℤ)
        U.unop x' y'
      have hR := hodgeDGA_mul (Scheme.Hom.deRhamAlgebras f') m n
        ((Opens.map (inverseImageBaseMap g' f' f g w :
          baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf) ⟶
            baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
              S.sheaf)).hom.base).op.obj U)
        (((hodgeDgaPushforward g' f' f g w).f m).val.app U x)
        (((hodgeDgaPushforward g' f' f g w).f n).val.app U y)
        (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (m : ℤ) U.unop x')
        (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (n : ℤ) U.unop y')
        (hodgeDgaPushforward_f_app_heq g' f' f g w m m rfl U x x' hx)
        (hodgeDgaPushforward_f_app_heq g' f' f g w n n rfl U y y' hy)
      exact eq_of_heq (hL.trans ((heq_of_eq hM).trans hR.symm))
    · have hy := hodgeComplexInt_section_eq_zero (Scheme.Hom.deRhamAlgebras f) b (by omega) U y
      subst hy
      refine (congrArg (fun z => ((hodgeDgaPushforward g' f' f g w).f (a + b)).val.app U z)
        (map_zero ((((hodgeDGA (Scheme.Hom.deRhamAlgebras f)).mul a b).app U) x))).trans ?_
      refine (map_zero _).trans ?_
      refine (map_zero ((((hodgeDGA (Scheme.Hom.deRhamAlgebras f')).mul a b).app _)
        (((hodgeDgaPushforward g' f' f g w).f a).val.app U x))).symm.trans ?_
      exact congrArg _ (map_zero _).symm
  · have hx := hodgeComplexInt_section_eq_zero (Scheme.Hom.deRhamAlgebras f) a (by omega) U x
    subst hx
    refine (congrArg (fun z => ((hodgeDgaPushforward g' f' f g w).f (a + b)).val.app U z)
      ((DFunLike.congr_fun (map_zero (((hodgeDGA (Scheme.Hom.deRhamAlgebras f)).mul a b).app
        U)) y).trans (AddMonoidHom.zero_apply y))).trans ?_
    refine (map_zero _).trans ?_
    refine ((DFunLike.congr_fun (map_zero (((hodgeDGA (Scheme.Hom.deRhamAlgebras f')).mul a
      b).app _)) (((hodgeDgaPushforward g' f' f g w).f b).val.app U y)).trans
        (AddMonoidHom.zero_apply _)).symm.trans ?_
    exact congrArg (fun z => (((hodgeDGA (Scheme.Hom.deRhamAlgebras f')).mul a b).app _ z)
      (((hodgeDgaPushforward g' f' f g w).f b).val.app U y)) (map_zero _).symm

/-- **The canonical map of Hodge complexes is unital**: it carries the unit of `ℋ_{X/S}` to the
unit of `ℋ_{X'/S'}`. -/
theorem hodgeDgaPushforward_one (U : (Opens X.carrier)ᵒᵖ) :
    ((hodgeDgaPushforward g' f' f g w).f 0).val.app U
        ((hodgeDGA (Scheme.Hom.deRhamAlgebras f)).one.eval U) =
      (hodgeDGA (Scheme.Hom.deRhamAlgebras f')).one.eval
        ((Opens.map (inverseImageBaseMap g' f' f g w :
          baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf) ⟶
            baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
              S.sheaf)).hom.base).op.obj U) := by
  have hL := hodgeDgaPushforward_f_app_heq g' f' f g w 0 0 rfl U
    ((hodgeDGA (Scheme.Hom.deRhamAlgebras f)).one.eval U)
    ((Scheme.Hom.relativeDifferentialFormsAlgebra f).one.eval (op U.unop))
    (hodgeDGA_one (Scheme.Hom.deRhamAlgebras f) U)
  have hM := Scheme.Hom.relativeDifferentialFormsPullback_one g' f f' g w U.unop
  have hR := hodgeDGA_one (Scheme.Hom.deRhamAlgebras f')
    ((Opens.map (inverseImageBaseMap g' f' f g w :
      baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf) ⟶
        baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
          S.sheaf)).hom.base).op.obj U)
  exact eq_of_heq (hL.trans ((heq_of_eq hM).trans hR.symm))

end Pushforward

end Stacks.HodgeWeil

end
