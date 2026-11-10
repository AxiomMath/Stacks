module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeLerayHirschMorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LocalLerayHirsch

/-!
# The Leray--Hirsch isomorphism for Hodge cohomology, checked on a basis

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, let `ℋ_{X/S} = ⨁_p Ω^p_{X/S}[-p]` be the
Hodge complex, with zero differential, and let `ξ_i ∈ H^{n_i}(X, ℋ_{X/S})`. The proof of
Proposition 0FMR, run on `ℋ` in place of the de Rham complex, shows that the morphism

`ξ̃ = ⨁ ξ̃_i[-n_i] : ⨁ ℋ_{Y/S}[-n_i] ⟶ Rf_*ℋ_{X/S}`

of `D(Y, g⁻¹𝒪_S)` is an isomorphism by checking it on the cohomology over the members of a basis
of `Y`. This file carries out the two formal steps of that argument.

First, over an open `V ⊆ g⁻¹W` with `W ⊆ S` open, the formation of `ξ̃` commutes with restriction
to `f⁻¹V ⟶ V` over `W`: the map that `ξ̃` induces on `H^k(V, -)` is identified, through the
canonical maps of the squares of open immersions `(f⁻¹V ⟶ X, W ⟶ S)` and `(V ⟶ Y, W ⟶ S)`, with the
map induced on `H^k(V, -)` by the morphism `ξ̃` of `f ∣_ V` for the restricted classes
`ξ_i|_{f⁻¹V}`.

Second, a morphism of `D(Y, g⁻¹𝒪_S)` inducing bijections on hypercohomology over the members of a
basis is an isomorphism ([Stacks, Tag 0BKJ]). Hence if for every member `V` of a basis the formula
`(a_i) ↦ ∑ ξ_i|_{f⁻¹V} ∪ (f ∣_ V)^*a_i` is bijective in every degree, then `ξ̃` is an isomorphism
and `(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is bijective in every degree.

## Main definitions

* `Stacks.HodgeWeil.hodgeComparisonQ`: the canonical map `ℋ_{X/S} ⟶ Rh_*ℋ_{X'/S'}` of a
  commutative square.
* `Stacks.HodgeWeil.hodgePullbackSquare`: the pullback `H^m(X, ℋ_{X/S}) ⟶ H^m(X', ℋ_{X'/S'})` of a
  commutative square.
* `Stacks.HodgeWeil.hodgeRestrictClass`: the restriction of a class of `H^m(X, ℋ_{X/S})` to
  `H^m(f⁻¹V, ℋ_{f⁻¹V/W})`.

## Main results

* `Stacks.HodgeWeil.comparisonQ_comp_dgaClassMorphism`: for a map `d : 𝒜 ⟶ h_*𝒜'` of sheaves of
  differential graded algebras, multiplicative and unital on local sections, the canonical map
  `c : 𝒜 ⟶ Rh_*𝒜'` satisfies `c ≫ Rh_*((h^*ξ)') = ξ' ≫ c[n]`.
* `Stacks.HodgeWeil.isIso_derivedSectionsOverOpen_map_comparisonQ_of_isIso_app`: a map of complexes
  into the direct image along an open immersion, bijective on sections over the opens of the
  image, induces isomorphisms on derived sections over every open of the image.
* `Stacks.HodgeWeil.hodgeComparisonQ_comp`: the canonical maps of two composable squares compose.
* `Stacks.HodgeWeil.bijective_homology_hodgeLerayHirschMorphism_of_restrict`: over `V ⊆ g⁻¹W`,
  `H^k(V, ξ̃)` is bijective as soon as the morphism `ξ̃` of `f ∣_ V` is bijective on cohomology.
* `Stacks.HodgeWeil.isIso_hodgeLerayHirschMorphism_of_isBasis` and
  `Stacks.HodgeWeil.isIso_hodgeLerayHirschMorphism_of_isBasis_of_bijective`: `ξ̃` is an
  isomorphism as soon as it is so on cohomology over the members of a basis.
* `Stacks.HodgeWeil.bijective_sum_dgaCohomologyCup_of_isBasis`: then
  `(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is bijective in every degree.

## References

* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (dgaCohomology)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open scoped CategoryTheory.Prod Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] structureSheafRing StacksDraft.KFlat.modulePushforward
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.HodgeWeil

/-! ### The morphisms `ξ'` along a map of differential graded algebras -/

section ClassMorphismSquare

open AlgebraicGeometry.SheafOfModules (baseRingedSpace baseSite dgaCohomology
  dgaUnitHom dgaClassMorphism dgaShiftHomologyIso structureSheafEval)

attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X X' : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}
  {A' : TopCat.Sheaf CommRingCat.{u} X'.carrier}
  (h : baseRingedSpace A' ⟶ baseRingedSpace A)
  {𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
    (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A)}
  {𝒜' : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
    (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A')}
  (d : 𝒜.complex ⟶ (pushforwardComplex h).obj 𝒜'.complex)

/-- The unit `A ⟶ 𝒜` carries the global section `1` of `A` to the global section `1` of `𝒜`. -/
private theorem unitComplexRingHom_f_app_unitSection
    (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A)) :
    ((_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
      (X := baseSite A) 𝒜).f 0).val.app (op ⊤)
        (Stacks.Cohomology.DerivedGlobalCupProduct.unitSection (baseRingedSpace A) 0) =
      𝒜.one.eval (op ⊤) := by
  have h₁ := _root_.SheafOfModules.DifferentialGradedAlgebra.unitAlgebraHomF_app_zero 𝒜 (op ⊤)
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitSection (baseRingedSpace A) 0)
  have h₂ := Stacks.Cohomology.DerivedGlobalCupProduct.singleObjXSelf_hom_unitSection
    (X := baseRingedSpace A) 0
  exact h₁.trans ((congrArg (· • _) (by exact h₂)).trans (one_smul _ _))

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **A unital map into a direct image commutes with the units**: if `d : 𝒜 ⟶ h_*𝒜'` carries the
global section `1` of `𝒜` to `1`, then `d` composed with the unit `A ⟶ 𝒜` is the structure map
`A ⟶ h_*A'` followed by the direct image of the unit `A' ⟶ 𝒜'`. -/
theorem unitComplexRingHom_comp_eq_of_one
    (hone : ((d.f 0).val.app (op ⊤)) (𝒜.one.eval (op ⊤)) = 𝒜'.one.eval (op ⊤)) :
    Eq (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
        (X := baseSite A) 𝒜 ≫ d)
      (Stacks.Cohomology.UnitClassPullback.unitToPushforward h 0 ≫
        (pushforwardComplex h).map
          (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
            (X := baseSite A') 𝒜')) := by
  refine Stacks.Cohomology.DerivedGlobalCupProduct.unitComplex_hom_ext
    (X := baseRingedSpace A) _ _ ?_
  have e₁ := unitComplexRingHom_f_app_unitSection 𝒜
  have e₂ : ((Stacks.Cohomology.UnitClassPullback.unitToPushforward h 0).f 0).val.app (op ⊤)
        (Stacks.Cohomology.DerivedGlobalCupProduct.unitSection (baseRingedSpace A) 0) =
      Stacks.Cohomology.DerivedGlobalCupProduct.unitSection (baseRingedSpace A') 0 :=
    Stacks.Cohomology.UnitClassPullback.unitToPushforward_unitSection _ 0
  have e₃ := unitComplexRingHom_f_app_unitSection 𝒜'
  refine (congrArg (fun z => ((d.f 0).val.app (op ⊤)) z) e₁).trans ?_
  refine Eq.trans ?_ (congrArg (fun z =>
      ((_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
        (X := baseSite A') 𝒜').f 0).val.app (op ⊤) z) e₂).symm
  exact hone.trans e₃.symm

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **A unital map into a direct image commutes with the units in the derived category**: the unit
`A ⟶ 𝒜` followed by `c = Q(d) ≫ (h_* ⟶ Rh_*)` is `v_h : A ⟶ Rh_*A'` followed by `Rh_*` of the
unit `A' ⟶ 𝒜'`. -/
theorem dgaUnitHom_comp_comparisonQ_eq_of_one
    (hone : ((d.f 0).val.app (op ⊤)) (𝒜.one.eval (op ⊤)) = 𝒜'.one.eval (op ⊤)) :
    Eq (dgaUnitHom 𝒜 ≫ DerivedCategory.Q.map d ≫ pushforwardComparisonQ h 𝒜'.complex)
      (Stacks.Cohomology.UnitClassPullback.unitToDerivedPushforward h 0 ≫
        (derivedPushforward h).map (dgaUnitHom 𝒜')) := by
  have h₁ := congrArg DerivedCategory.Q.map (unitComplexRingHom_comp_eq_of_one h d hone)
  have h₂ :=
    Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ_naturality
    h (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom (X := baseSite A') 𝒜')
  have h₃ := (DerivedCategory.Q.map_comp _ _).symm.trans (h₁.trans (DerivedCategory.Q.map_comp _ _))
  have h₄ := congrArg (DerivedCategory.Q.map
    (Stacks.Cohomology.UnitClassPullback.unitToPushforward h 0) ≫ ·) h₂
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₃).trans
    ((Category.assoc _ _ _).trans (h₄.trans (Category.assoc _ _ _).symm)))

/-- The value at the unit of `ξ'`, read in `H^n(X, 𝒜)`, is `ξ` (property (2) of Section 0FU3, in
the form `ξ'` precomposed with the unit `A ⟶ 𝒜`). -/
theorem dgaShiftHomologyIso_structureSheafEval_dgaClassMorphism (n : ℤ)
    (ξ : dgaCohomology 𝒜 n) :
    (dgaShiftHomologyIso 𝒜 n 0 n (add_zero n)).hom
        (structureSheafEval A _ (dgaUnitHom 𝒜 ≫ dgaClassMorphism 𝒜 n ξ)) = ξ :=
  (AlgebraicGeometry.SheafOfModules.dgaEvalOne_eq 𝒜 n _).symm.trans
    (AlgebraicGeometry.SheafOfModules.dgaEvalOne_dgaClassMorphism 𝒜 n ξ)

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **The formation of `ξ'` commutes with pullback along a map of differential graded algebras**
(Remark 0FU7, as used in the proof of Proposition 0FMR): for a map `d : 𝒜 ⟶ h_*𝒜'` of complexes
which is multiplicative and unital on local sections, with `c = Q(d) ≫ (h_* ⟶ Rh_*)`, and for
`ξ ∈ H^n(X, 𝒜)` with pullback `h^*ξ ∈ H^n(X', 𝒜')` along `d`, one has
`c ≫ Rh_*((h^*ξ)') = ξ' ≫ c[n]`. -/
theorem comparisonQ_comp_dgaClassMorphism
    (hmul : ∀ (a b : ℤ) (U : (Opens X.carrier)ᵒᵖ) (x : (𝒜.complex.X a).val.obj U)
      (y : (𝒜.complex.X b).val.obj U),
      (d.f (a + b)).val.app U ((𝒜.mul a b).app U x y) =
        (𝒜'.mul a b).app ((Opens.map h.hom.base).op.obj U) ((d.f a).val.app U x)
          ((d.f b).val.app U y))
    (hone : ((d.f 0).val.app (op ⊤)) (𝒜.one.eval (op ⊤)) = 𝒜'.one.eval (op ⊤))
    (n : ℤ) (ξ : dgaCohomology 𝒜 n) :
    (DerivedCategory.Q.map d ≫ pushforwardComparisonQ h 𝒜'.complex) ≫
        (derivedPushforward h).map (dgaClassMorphism 𝒜' n ((cohomologyPullback h d n).hom ξ)) =
      dgaClassMorphism 𝒜 n ξ ≫ (DerivedCategory.Q.map d ≫ pushforwardComparisonQ h 𝒜'.complex)⟦n⟧' ≫
        ((derivedPushforward h).commShiftIso n).inv.app _ := by
  refine AlgebraicGeometry.SheafOfModules.comp_derivedPushforward_map_eq_of_linear
    (S := baseRingedSpace A) (S' := baseRingedSpace A') h d hmul n _
    (AlgebraicGeometry.SheafOfModules.derivedForgetShiftedHom_derivedAction
      (S := baseRingedSpace A) 𝒜 n
      (AlgebraicGeometry.SheafOfModules.dgaClassDerivedEquiv 𝒜 n ξ)) _
    (AlgebraicGeometry.SheafOfModules.derivedForgetShiftedHom_derivedAction
      (S := baseRingedSpace A') 𝒜' n
      (AlgebraicGeometry.SheafOfModules.dgaClassDerivedEquiv 𝒜' n
        ((cohomologyPullback h d n).hom ξ)))
    (dgaUnitHom 𝒜) (AlgebraicGeometry.SheafOfModules.isIso_dgaUnitHom_derivedAction 𝒜) ?_
  have hU := dgaUnitHom_comp_comparisonQ_eq_of_one h d hone
  have eL := (Category.assoc _ _ _).symm.trans ((congrArg (fun g => g ≫
      (derivedPushforward h).map (dgaClassMorphism 𝒜' n ((cohomologyPullback h d n).hom ξ)))
      hU).trans ((Category.assoc _ _ _).trans (congrArg
        (Stacks.Cohomology.UnitClassPullback.unitToDerivedPushforward h 0 ≫ ·)
        (Functor.map_comp _ _ _).symm)))
  have hL := Stacks.Cohomology.UnitClassPullback.lerayCohomologyIso_evalUnit_classPushforward h 0
    (dgaUnitHom 𝒜' ≫ dgaClassMorphism 𝒜' n ((cohomologyPullback h d n).hom ξ))
  have hR := Stacks.Cohomology.UnitClassPullback.shiftHomologyIsoU_lerayMap_evalUnit_comp_shift h
    (DerivedCategory.Q.map d ≫ pushforwardComparisonQ h 𝒜'.complex) n
    (dgaUnitHom 𝒜 ≫ dgaClassMorphism 𝒜 n ξ)
  have hev' := dgaShiftHomologyIso_structureSheafEval_dgaClassMorphism (𝒜 := 𝒜') n
    ((cohomologyPullback h d n).hom ξ)
  have hev := dgaShiftHomologyIso_structureSheafEval_dgaClassMorphism n ξ
  refine (AlgebraicGeometry.SheafOfModules.structureSheafEval_bijective A _).1 ?_
  refine Stacks.Cohomology.LerayCupPairing.lerayMap_injective h _ 0 ?_
  refine (ConcreteCategory.bijective_of_isIso (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
    (Stacks.Cohomology.GlobalKunneth.baseSections (baseRingedSpace A'))
    (DerivedCategory.Q.obj 𝒜'.complex) n 0 n (add_zero n)).hom).1 ?_
  refine (congrArg (fun φ => (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
    (Stacks.Cohomology.GlobalKunneth.baseSections (baseRingedSpace A'))
    (DerivedCategory.Q.obj 𝒜'.complex) n 0 n (add_zero n)).hom.hom
      (Stacks.Cohomology.LerayCupPairing.lerayMap h _ 0 (structureSheafEval A _ φ))) eL).trans ?_
  refine (congrArg (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
    (Stacks.Cohomology.GlobalKunneth.baseSections (baseRingedSpace A'))
    (DerivedCategory.Q.obj 𝒜'.complex) n 0 n (add_zero n)).hom.hom hL).trans (hev'.trans ?_)
  refine Eq.trans ?_ (congrArg (fun φ => (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
    (Stacks.Cohomology.GlobalKunneth.baseSections (baseRingedSpace A'))
    (DerivedCategory.Q.obj 𝒜'.complex) n 0 n (add_zero n)).hom.hom
      (Stacks.Cohomology.LerayCupPairing.lerayMap h _ 0 (structureSheafEval A _ φ)))
    (Category.assoc _ _ _))
  refine Eq.trans ?_ hR.symm
  exact (congrArg (fun z => Stacks.Cohomology.LerayCupPairing.lerayMap h _ n
    (((DerivedCategory.homologyFunctor _ n).map
      ((Stacks.Cohomology.GlobalKunneth.baseSections (baseRingedSpace A)).map
        (DerivedCategory.Q.map d ≫ pushforwardComparisonQ h 𝒜'.complex))).hom z)) hev).symm

end ClassMorphismSquare

/-! ### Canonical maps into the direct image along an open immersion -/

section OpenImmersion

open RingedSpaceModuleAdjunction

variable {X' X : RingedSpace.{u, u}} (h : X' ⟶ X) [hh : SheafedSpace.IsOpenImmersion h]
  {M : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ}
  {N : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X')) ℤ}
  (d : M ⟶ (pushforwardComplex h).obj N)

/-- **A map of complexes `d : M ⟶ h_*N` along an open immersion `h`, bijective on sections over the
opens inside the image of `h`, induces isomorphisms on derived sections over every open inside the
image**: `RΓ(U, M) ≅ RΓ(U, Rh_*N)` for `U ⊆ h(X')`. The transpose `h^*M ⟶ N` of `d` is an
isomorphism, and the unit `M ⟶ h_*h^*M` induces isomorphisms on derived sections over `U`
([Stacks, Tag 0D5V]). -/
theorem isIso_derivedSectionsOverOpen_map_comparisonQ_of_isIso_app
    (hd : ∀ (n : ℤ) (W : Opens X'.carrier),
      IsIso ((d.f n).val.app (op (hh.base_open.functor.obj W))))
    (U : Opens X.carrier) (hU : (U : Set X.carrier) ⊆ Set.range h.hom.base) :
    IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen X U).map
      (DerivedCategory.Q.map d ≫ pushforwardComparisonQ h N)) := by
  let adj := Adjunction.mapHomologicalComplexAdjunction (modulePullbackPushforwardAdjunction h)
    (ComplexShape.up ℤ)
  let d' := (adj.homEquiv _ _).symm d
  have hdd : d = adj.unit.app M ≫
      ((modulePushforward h).mapHomologicalComplex (ComplexShape.up ℤ)).map d' :=
    ((adj.homEquiv _ _).apply_symm_apply d).symm.trans (Adjunction.homEquiv_unit _ _ _ _)
  have hiso : IsIso d' := by
    have : ∀ n, IsIso (d'.f n) := by
      intro n
      have e : d'.f n = (modulePullback h).map (d.f n) ≫
          (modulePullbackPushforwardAdjunction h).counit.app (N.X n) := by
        change (((adj.homEquiv _ _).symm d).f n) = _
        rw [Adjunction.homEquiv_counit]
        rfl
      rw [e]
      have h₁ := Stacks.Cohomology.openImmersionPullback_map_isIso h (d.f n) (hd n)
      have h₂ := Stacks.Cohomology.openImmersionPullback_counit_isIso h (N.X n)
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
    exact HomologicalComplex.Hom.isIso_of_components _
  have e : DerivedCategory.Q.map d ≫ pushforwardComparisonQ h N =
      Stacks.Cohomology.OpenImmersionSections.pullbackUnitQ h M ≫
        (derivedPushforward h).map (DerivedCategory.Q.map d') := by
    have h₁ := congrArg (fun φ => DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h N) hdd
    have h₂ :=
      Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ_naturality
      h d'
    exact h₁.trans ((congrArg (· ≫ _) (DerivedCategory.Q.map_comp _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg (DerivedCategory.Q.map
        (Stacks.Cohomology.OpenImmersionSections.pullbackUnitComplex h M) ≫ ·) h₂).trans
          (Category.assoc _ _ _).symm)))
  have h₁ := Stacks.Cohomology.OpenImmersionSections.isIso_derivedSectionsOverOpen_map_pullbackUnitQ
    h U hU M
  rw [e]
  refine (congrArg IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
    X U).map_comp _ _)).mpr ?_
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (Functor.map_isIso _ _)

end OpenImmersion

/-! ### The canonical map of Hodge complexes of a commutative square -/

section Square

variable {X X' S S' : Scheme.{u}} (ι : X' ⟶ X) (p' : X' ⟶ S') (p : X ⟶ S) (h₀ : S' ⟶ S)
  (w : ι ≫ p = p' ≫ h₀)

/-- **The canonical map `ℋ_{X/S} ⟶ Rh_*ℋ_{X'/S'}`** of a commutative square, in `D(X, p⁻¹𝒪_S)`:
the canonical map of Hodge complexes followed by the comparison `h_* ⟶ Rh_*`. -/
def hodgeComparisonQ :
    hodgeObject p ⟶ (derivedPushforward (inverseImageBaseMap ι p' p h₀ w)).obj (hodgeObject p') :=
  DerivedCategory.Q.map (hodgeDgaPushforward ι p' p h₀ w) ≫
    pushforwardComparisonQ (inverseImageBaseMap ι p' p h₀ w)
      (hodgeDGA (Scheme.Hom.deRhamAlgebras p')).complex

/-- The pullback `H^m(X, ℋ_{X/S}) ⟶ H^m(X', ℋ_{X'/S'})` of a commutative square, along the
canonical map of Hodge complexes. -/
abbrev hodgePullbackSquare (m : ℤ) (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras p)) m) :
    dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras p')) m :=
  (cohomologyPullback (inverseImageBaseMap ι p' p h₀ w) (hodgeDgaPushforward ι p' p h₀ w) m).hom ξ

/-- **The formation of `ξ'` commutes with pullback along a commutative square**, for Hodge
cohomology (Remark 0FU7): for `ξ ∈ H^n(X, ℋ_{X/S})`, the canonical map
`c : ℋ_{X/S} ⟶ Rh_*ℋ_{X'/S'}` satisfies `c ≫ Rh_*((ι^*ξ)') = ξ' ≫ c[n]`. -/
theorem hodgeComparisonQ_comp_hodgeClassMorphism (n : ℤ)
    (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras p)) n) :
    hodgeComparisonQ ι p' p h₀ w ≫ (derivedPushforward (inverseImageBaseMap ι p' p h₀ w)).map
        (hodgeClassMorphism p' n (hodgePullbackSquare ι p' p h₀ w n ξ)) =
      hodgeClassMorphism p n ξ ≫ (hodgeComparisonQ ι p' p h₀ w)⟦n⟧' ≫
        ((derivedPushforward (inverseImageBaseMap ι p' p h₀ w)).commShiftIso n).inv.app _ :=
  comparisonQ_comp_dgaClassMorphism (inverseImageBaseMap ι p' p h₀ w)
    (hodgeDgaPushforward ι p' p h₀ w) (hodgeDgaPushforward_mul ι p' p h₀ w)
    (hodgeDgaPushforward_one ι p' p h₀ w (op ⊤)) n ξ

/-- **On derived sections over an open inside the image of `ι`, the canonical map of Hodge
complexes of a square of open immersions is an isomorphism**: `ℋ_{X/S}|_{X'} = ℋ_{X'/S'}`
([Stacks, Tag 0FLV]) and derived sections over `U ⊆ ι(X')` may be computed on `X'`
([Stacks, Tag 0D5V]). -/
theorem isIso_derivedSectionsOverOpen_map_hodgeComparisonQ [IsOpenImmersion ι]
    [IsOpenImmersion h₀] (U : X.Opens) (hU : U ≤ ι.opensRange) :
    IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
      (inverseImageBase p) U).map (hodgeComparisonQ ι p' p h₀ w)) := by
  have := AlgebraicGeometry.DeRhamLerayHirsch.isOpenImmersion_inverseImageBaseMap ι p' p h₀ w
  refine isIso_derivedSectionsOverOpen_map_comparisonQ_of_isIso_app
    (inverseImageBaseMap ι p' p h₀ w) (hodgeDgaPushforward ι p' p h₀ w) (fun n W =>
      AlgebraicGeometry.DeRhamLerayHirsch.isIso_deRhamPushforwardInt_f_app ι p' p h₀ w n _
        (AlgebraicGeometry.DeRhamLerayHirsch.functor_obj_le_opensRange ι p' p h₀ w W)) U ?_
  rw [AlgebraicGeometry.DeRhamLerayHirsch.inverseImageBaseMap_base]
  exact hU

end Square

section Composite

variable {X X' X'' S S' S'' : Scheme.{u}} (b : X' ⟶ X) (s : X ⟶ S) (s' : X' ⟶ S') (g₁ : S' ⟶ S)
  (h₁ : b ≫ s = s' ≫ g₁) (a : X'' ⟶ X') (s'' : X'' ⟶ S'') (g₂ : S'' ⟶ S')
  (h₂ : a ≫ s' = s'' ≫ g₂) (c : X'' ⟶ X) (t : S'' ⟶ S) (h₃ : c ≫ s = s'' ≫ t)

/-- **The canonical maps of Hodge complexes of two horizontally composable squares compose** to
the canonical map of the outer square, through the composition isomorphism of derived direct
images. -/
theorem hodgeComparisonQ_comp (hc : a ≫ b = c) (ht : g₂ ≫ g₁ = t) :
    hodgeComparisonQ b s' s g₁ h₁ ≫
        (derivedPushforward (inverseImageBaseMap b s' s g₁ h₁)).map
          (hodgeComparisonQ a s'' s' g₂ h₂) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
          (inverseImageBaseMap a s'' s' g₂ h₂) (inverseImageBaseMap b s' s g₁ h₁)).hom.app
          (hodgeObject s'') ≫
        eqToHom (congrArg (fun k => (derivedPushforward k).obj (hodgeObject s''))
          (AlgebraicGeometry.DeRhamLerayHirsch.inverseImageBaseMap_comp b s s' g₁ h₁ a s'' g₂ h₂
            c t h₃ hc ht)) =
      hodgeComparisonQ c s'' s t h₃ := by
  unfold hodgeComparisonQ
  refine (Stacks.Cohomology.LerayComposite.comparisonQ_comp_of_heq
      (inverseImageBaseMap a s'' s' g₂ h₂) (inverseImageBaseMap b s' s g₁ h₁)
      (inverseImageBaseMap c s'' s t h₃)
      (AlgebraicGeometry.DeRhamLerayHirsch.inverseImageBaseMap_comp b s s' g₁ h₁ a s'' g₂ h₂ c t
        h₃ hc ht)
      (hodgeDgaPushforward b s' s g₁ h₁) (hodgeDgaPushforward a s'' s' g₂ h₂)
      (hodgeDgaPushforward c s'' s t h₃) fun n V x => ?_)
  subst hc ht
  by_cases hn : 0 ≤ n
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    let x' : Γ(Scheme.Hom.relativeDifferentialForms s (q : ℤ), V.unop) :=
      cast (congrArg (fun M : _root_.SheafOfModules.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} s.base).obj S.sheaf)) =>
            (M.val.obj V : Type u))
        (hodgeComplexInt_X_of_nonneg (Scheme.Hom.deRhamAlgebras s) (q : ℤ)
          (Int.natCast_nonneg q))) x
    have hx : HEq x x' := (cast_heq _ x).symm
    have hL := hodgeDgaPushforward_f_app_heq (a ≫ b) s'' s (g₂ ≫ g₁) h₃ q q rfl V x x' hx
    have hM := hodgeDgaPushforward_f_app_heq b s' s g₁ h₁ q q rfl V x x' hx
    have hR := hodgeDgaPushforward_f_app_heq a s'' s' g₂ h₂ q q rfl
      ((Opens.map (inverseImageBaseMap b s' s g₁ h₁).hom.base).op.obj V) _ _ hM
    have hC := Stacks.Gysin.relativeDifferentialFormsPullback_comp b a s s' s'' g₁ g₂ (g₂ ≫ g₁)
      h₁ h₂ h₃ (q : ℤ) V.unop x'
    exact hL.trans ((heq_of_eq hC).trans hR.symm)
  · exact heq_of_eq ((hodgeComplexInt_section_eq_zero (Scheme.Hom.deRhamAlgebras s'') n
      (by omega) _ _).trans
      (hodgeComplexInt_section_eq_zero (Scheme.Hom.deRhamAlgebras s'') n (by omega) _ _).symm)

end Composite

/-! ### The morphism `ξ̃` over an open of the base -/

section Restrict

open AlgebraicGeometry.DeRhamLerayHirsch (restrictBase_w restrict_w restrictOuter_w restrictMapX
  restrictMapY restrictMapOuter restrictMapX_comp baseMap_comp_restrictMapY baseMap
  relativeDirectImage cohomologyFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforwardCompIso)

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (V : Y.Opens) (W : S.Opens)
  (hVW : V ≤ g ⁻¹ᵁ W)

/-- The restriction of a class of `H^m(X, ℋ_{X/S})` to `H^m(f⁻¹V, ℋ_{f⁻¹V/W})`: the pullback
along the square of open immersions `(f⁻¹V ⟶ X, W ⟶ S)`. -/
abbrev hodgeRestrictClass (m : ℤ)
    (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :
    dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ∣_ V ≫ g.resLE W V hVW))) m :=
  hodgePullbackSquare (f ⁻¹ᵁ V).ι (f ∣_ V ≫ g.resLE W V hVW) (f ≫ g) W.ι
    (restrict_w f g V W hVW) m ξ

/-- The canonical map of Hodge complexes of the square `(f⁻¹V ⟶ X, W ⟶ S)`. -/
abbrev hodgeRestrictComparisonX :=
  hodgeComparisonQ (f ⁻¹ᵁ V).ι (f ∣_ V ≫ g.resLE W V hVW) (f ≫ g) W.ι (restrict_w f g V W hVW)

/-- The canonical map of Hodge complexes of the square `(V ⟶ Y, W ⟶ S)`. -/
abbrev hodgeRestrictComparisonY :=
  hodgeComparisonQ V.ι (g.resLE W V hVW) g W.ι (restrictBase_w g V W hVW)

/-- The canonical map of Hodge complexes of the outer square `(f⁻¹V ⟶ Y, W ⟶ S)`. -/
abbrev hodgeRestrictComparisonOuter :=
  hodgeComparisonQ ((f ⁻¹ᵁ V).ι ≫ f) (f ∣_ V ≫ g.resLE W V hVW) g W.ι
    (restrictOuter_w f g V W hVW)

/-- The composition isomorphism along `f⁻¹V ⟶ X ⟶ Y`, at `ℋ_{f⁻¹V/W}`, landing in the direct
image along the outer square. -/
abbrev hodgeRestrictCompX :=
  (derivedPushforwardCompIso (restrictMapX f g V W hVW) (baseMap f g)).hom.app
      (hodgeObject (f ∣_ V ≫ g.resLE W V hVW)) ≫
    eqToHom (congrArg (fun k => (derivedPushforward k).obj
      (hodgeObject (f ∣_ V ≫ g.resLE W V hVW))) (restrictMapX_comp f g V W hVW))

/-- The composition isomorphism along `f⁻¹V ⟶ V ⟶ Y`, at `ℋ_{f⁻¹V/W}`, landing in the direct
image along the outer square. -/
abbrev hodgeRestrictCompY :=
  (derivedPushforwardCompIso (baseMap (f ∣_ V) (g.resLE W V hVW)) (restrictMapY g V W hVW)).hom.app
      (hodgeObject (f ∣_ V ≫ g.resLE W V hVW)) ≫
    eqToHom (congrArg (fun k => (derivedPushforward k).obj
      (hodgeObject (f ∣_ V ≫ g.resLE W V hVW))) (baseMap_comp_restrictMapY f g V W hVW))

/-- The canonical maps of `f` and of `(f⁻¹V ⟶ X, W ⟶ S)` compose to that of the outer square. -/
theorem hodgeDirectImageMap_comp_hodgeRestrictComparisonX :
    hodgeDirectImageMap f g ≫
        (relativeDirectImage f g).map (hodgeRestrictComparisonX f g V W hVW) ≫
        hodgeRestrictCompX f g V W hVW =
      hodgeRestrictComparisonOuter f g V W hVW :=
  hodgeComparisonQ_comp f g (f ≫ g) (𝟙 S) (Category.comp_id _).symm (f ⁻¹ᵁ V).ι
    (f ∣_ V ≫ g.resLE W V hVW) W.ι (restrict_w f g V W hVW) ((f ⁻¹ᵁ V).ι ≫ f) W.ι
    (restrictOuter_w f g V W hVW) rfl (Category.comp_id _)

/-- The canonical maps of `(V ⟶ Y, W ⟶ S)` and of `f ∣_ V` compose to that of the outer square. -/
theorem hodgeRestrictComparisonY_comp_hodgeDirectImageMap :
    hodgeRestrictComparisonY g V W hVW ≫ (derivedPushforward (restrictMapY g V W hVW)).map
        (hodgeDirectImageMap (f ∣_ V) (g.resLE W V hVW)) ≫ hodgeRestrictCompY f g V W hVW =
      hodgeRestrictComparisonOuter f g V W hVW :=
  hodgeComparisonQ_comp V.ι g (g.resLE W V hVW) W.ι (restrictBase_w g V W hVW) (f ∣_ V)
    (f ∣_ V ≫ g.resLE W V hVW) (𝟙 W.toScheme) (Category.comp_id _).symm ((f ⁻¹ᵁ V).ι ≫ f) W.ι
    (restrictOuter_w f g V W hVW) (morphismRestrict_ι f V) (Category.id_comp _)

/-- **`ξ̃` followed by the canonical map of `(f⁻¹V ⟶ X, W ⟶ S)`** is the canonical map of the
outer square followed by `(ξ|_{f⁻¹V})'`, by Remark 0FU7 for the square. -/
theorem hodgeClassDirectImageMorphism_comp_hodgeRestrictComparisonX (m : ℤ)
    (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :
    Eq (hodgeClassDirectImageMorphism f g m ξ ≫
        ((relativeDirectImage f g).map (hodgeRestrictComparisonX f g V W hVW) ≫
          hodgeRestrictCompX f g V W hVW)⟦m⟧' :
        hodgeObject g ⟶ ((derivedPushforward (restrictMapOuter f g V W hVW)).obj
          (hodgeObject (f ∣_ V ≫ g.resLE W V hVW)))⟦m⟧)
      (hodgeRestrictComparisonOuter f g V W hVW ≫
        (derivedPushforward (restrictMapOuter f g V W hVW)).map
          (hodgeClassMorphism (f ∣_ V ≫ g.resLE W V hVW) m
            (hodgeRestrictClass f g V W hVW m ξ)) ≫
        ((derivedPushforward (restrictMapOuter f g V W hVW)).commShiftIso m).hom.app _) := by
  have hstar := hodgeComparisonQ_comp_hodgeClassMorphism (f ⁻¹ᵁ V).ι (f ∣_ V ≫ g.resLE W V hVW)
    (f ≫ g) W.ι (restrict_w f g V W hVW) m ξ
  have e₁ := comp_map_commShiftIso_hom_app_shift_eq
    (derivedPushforwardCompIso (restrictMapX f g V W hVW) (baseMap f g)).hom
    (hodgeDirectImageMap f g ≫ (relativeDirectImage f g).map
      (hodgeRestrictComparisonX f g V W hVW)) _ rfl m
    (hodgeClassMorphism (f ∣_ V ≫ g.resLE W V hVW) m (hodgeRestrictClass f g V W hVW m ξ))
  have e₂ := AlgebraicGeometry.DeRhamLerayHirsch.derivedPushforward_eqToHom_shift
    (restrictMapX_comp f g V W hVW)
    ((hodgeDirectImageMap f g ≫ (relativeDirectImage f g).map
      (hodgeRestrictComparisonX f g V W hVW)) ≫
      (derivedPushforwardCompIso (restrictMapX f g V W hVW) (baseMap f g)).hom.app _) m
    (hodgeClassMorphism (f ∣_ V ≫ g.resLE W V hVW) m (hodgeRestrictClass f g V W hVW m ξ))
  have hDC := hodgeDirectImageMap_comp_hodgeRestrictComparisonX f g V W hVW
  have hs := map_comp_eq_of_eq_comp_inv (relativeDirectImage f g) _ _ _ _
    (((derivedPushforward (restrictMapX f g V W hVW)).commShiftIso m).app
      (hodgeObject (f ∣_ V ≫ g.resLE W V hVW))) hstar
  have h'' := Functor.commShiftIso_comp_hom_app (derivedPushforward (restrictMapX f g V W hVW))
    (relativeDirectImage f g) m (hodgeObject (f ∣_ V ≫ g.resLE W V hVW))
  refine restrict_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by simp only [Functor.map_comp]) (Functor.commShiftIso_hom_naturality _ _ _) hs h'' e₁ e₂ hDC

/-- **The canonical map of `(V ⟶ Y, W ⟶ S)` followed by the direct image of the morphism `ξ̃` of
`f ∣_ V`** is the canonical map of the outer square followed by `(ξ|_{f⁻¹V})'`. -/
theorem hodgeRestrictComparisonY_comp_hodgeClassDirectImageMorphism (m : ℤ)
    (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :
    Eq (hodgeRestrictComparisonY g V W hVW ≫ (derivedPushforward (restrictMapY g V W hVW)).map
          (hodgeClassDirectImageMorphism (f ∣_ V) (g.resLE W V hVW) m
            (hodgeRestrictClass f g V W hVW m ξ)) ≫
        ((derivedPushforward (restrictMapY g V W hVW)).commShiftIso m).hom.app _ ≫
        (hodgeRestrictCompY f g V W hVW)⟦m⟧' :
        hodgeObject g ⟶ ((derivedPushforward (restrictMapOuter f g V W hVW)).obj
          (hodgeObject (f ∣_ V ≫ g.resLE W V hVW)))⟦m⟧)
      (hodgeRestrictComparisonOuter f g V W hVW ≫
        (derivedPushforward (restrictMapOuter f g V W hVW)).map
          (hodgeClassMorphism (f ∣_ V ≫ g.resLE W V hVW) m
            (hodgeRestrictClass f g V W hVW m ξ)) ≫
        ((derivedPushforward (restrictMapOuter f g V W hVW)).commShiftIso m).hom.app _) := by
  have e₁ := comp_map_commShiftIso_hom_app_shift_eq
    (derivedPushforwardCompIso (baseMap (f ∣_ V) (g.resLE W V hVW)) (restrictMapY g V W hVW)).hom
    (hodgeRestrictComparisonY g V W hVW ≫ (derivedPushforward (restrictMapY g V W hVW)).map
      (hodgeDirectImageMap (f ∣_ V) (g.resLE W V hVW))) _ rfl m
    (hodgeClassMorphism (f ∣_ V ≫ g.resLE W V hVW) m (hodgeRestrictClass f g V W hVW m ξ))
  have e₂ := AlgebraicGeometry.DeRhamLerayHirsch.derivedPushforward_eqToHom_shift
    (baseMap_comp_restrictMapY f g V W hVW)
    ((hodgeRestrictComparisonY g V W hVW ≫ (derivedPushforward (restrictMapY g V W hVW)).map
      (hodgeDirectImageMap (f ∣_ V) (g.resLE W V hVW))) ≫
      (derivedPushforwardCompIso (baseMap (f ∣_ V) (g.resLE W V hVW))
        (restrictMapY g V W hVW)).hom.app _) m
    (hodgeClassMorphism (f ∣_ V ≫ g.resLE W V hVW) m (hodgeRestrictClass f g V W hVW m ξ))
  have hDC := hodgeRestrictComparisonY_comp_hodgeDirectImageMap f g V W hVW
  have h'' := Functor.commShiftIso_comp_hom_app (derivedPushforward (baseMap (f ∣_ V)
    (g.resLE W V hVW))) (derivedPushforward (restrictMapY g V W hVW)) m
    (hodgeObject (f ∣_ V ≫ g.resLE W V hVW))
  exact restrict_paste₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by simp only [hodgeClassDirectImageMorphism, Functor.map_comp, Functor.comp_map]) h''
    (Functor.map_comp _ _ _) e₁ e₂ hDC

/-- **A summand of `ξ̃`, followed by the canonical map of `(f⁻¹V ⟶ X, W ⟶ S)`**, is the shifted
canonical map of `(V ⟶ Y, W ⟶ S)` followed by the direct image of the corresponding summand of the
morphism `ξ̃` of `f ∣_ V` for the restricted class. -/
theorem hodgeClassDirectImageSummand_comp_restrict (m : ℤ)
    (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :
    hodgeClassDirectImageSummand f g m ξ ≫
        (relativeDirectImage f g).map (hodgeRestrictComparisonX f g V W hVW) ≫
        hodgeRestrictCompX f g V W hVW =
      (hodgeRestrictComparisonY g V W hVW)⟦-m⟧' ≫
        ((derivedPushforward (restrictMapY g V W hVW)).commShiftIso (-m)).inv.app _ ≫
        (derivedPushforward (restrictMapY g V W hVW)).map
          (hodgeClassDirectImageSummand (f ∣_ V) (g.resLE W V hVW) m
            (hodgeRestrictClass f g V W hVW m ξ)) ≫
        hodgeRestrictCompY f g V W hVW := by
  have l2a := shift_map_comp_shiftFunctorCompIsoId_hom_app_comp m
    (hodgeClassDirectImageMorphism f g m ξ)
    ((relativeDirectImage f g).map (hodgeRestrictComparisonX f g V W hVW) ≫
      hodgeRestrictCompX f g V W hVW)
  have l3 := shift_comp_shiftFunctorCompIsoId_hom_app_eq_map
    (derivedPushforward (restrictMapY g V W hVW)) m
    (hodgeClassDirectImageMorphism (f ∣_ V) (g.resLE W V hVW) m
      (hodgeRestrictClass f g V W hVW m ξ))
  have l2b := shift_map_comp_shiftFunctorCompIsoId_hom_app_comp m
    ((derivedPushforward (restrictMapY g V W hVW)).map
      (hodgeClassDirectImageMorphism (f ∣_ V) (g.resLE W V hVW) m
        (hodgeRestrictClass f g V W hVW m ξ)) ≫
      ((derivedPushforward (restrictMapY g V W hVW)).commShiftIso m).hom.app _)
    (hodgeRestrictCompY f g V W hVW)
  have hT := hodgeClassDirectImageMorphism_comp_hodgeRestrictComparisonX f g V W hVW m ξ
  have hB := hodgeRestrictComparisonY_comp_hodgeClassDirectImageMorphism f g V W hVW m ξ
  refine (Category.assoc _ _ _).trans (l2a.trans ((congrArg (fun z => z⟦-m⟧' ≫
    (shiftFunctorCompIsoId _ m (-m) (add_neg_cancel m)).hom.app _) (hT.trans hB.symm)).trans ?_))
  exact summand_paste (shiftFunctor _ (-m)) _ _ _ _ _ _ _ _ _ l3 l2b

variable {N : ℕ} (n : Fin N → ℕ)
  (ξ : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ))

/-- **The morphism `ξ̃` of `f`, followed by the canonical map of `(f⁻¹V ⟶ X, W ⟶ S)`**, is the
canonical map of `(V ⟶ Y, W ⟶ S)` followed by the direct image of the morphism `ξ̃` of `f ∣_ V` for
the restricted classes. -/
theorem hodgeLerayHirschMorphism_comp_restrict :
    hodgeLerayHirschMorphism f g n ξ ≫
        (relativeDirectImage f g).map (hodgeRestrictComparisonX f g V W hVW) ≫
        hodgeRestrictCompX f g V W hVW =
      biproduct.map (fun i => (hodgeRestrictComparisonY g V W hVW)⟦-(n i : ℤ)⟧') ≫
        biproductShiftComparison (derivedPushforward (restrictMapY g V W hVW))
          (fun i => -(n i : ℤ)) (hodgeObject (g.resLE W V hVW)) ≫
        (derivedPushforward (restrictMapY g V W hVW)).map
          (hodgeLerayHirschMorphism (f ∣_ V) (g.resLE W V hVW) n
            fun i => hodgeRestrictClass f g V W hVW (n i) (ξ i)) ≫
        hodgeRestrictCompY f g V W hVW :=
  biproduct_desc_comp_eq (derivedPushforward (restrictMapY g V W hVW)) (fun i => -(n i : ℤ)) _ _ _
    _ _ fun i => hodgeClassDirectImageSummand_comp_restrict f g V W hVW (n i) (ξ i)

include hVW in
/-- The derived sections over `V` of the canonical map of `(V ⟶ Y, W ⟶ S)` are an isomorphism. -/
theorem isIso_derivedSectionsOverOpen_map_hodgeRestrictComparisonY :
    IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
      (inverseImageBase g) V).map (hodgeRestrictComparisonY g V W hVW)) :=
  isIso_derivedSectionsOverOpen_map_hodgeComparisonQ V.ι (g.resLE W V hVW) g W.ι
    (restrictBase_w g V W hVW) V (Scheme.Opens.opensRange_ι V).ge

/-- The derived sections over `f⁻¹V` of the canonical map of `(f⁻¹V ⟶ X, W ⟶ S)` are an
isomorphism. -/
theorem isIso_derivedSectionsOverOpen_map_hodgeRestrictComparisonX :
    IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
      (inverseImageBase (f ≫ g))
      ((RingedSpaceModuleAdjunction.opensMap (baseMap f g)).obj V)).map
      (hodgeRestrictComparisonX f g V W hVW)) :=
  isIso_derivedSectionsOverOpen_map_hodgeComparisonQ (f ⁻¹ᵁ V).ι (f ∣_ V ≫ g.resLE W V hVW)
    (f ≫ g) W.ι (restrict_w f g V W hVW) _ (fun x hx => by
      rwa [Scheme.Opens.opensRange_ι])

/-- **Over an open `V ⊆ g⁻¹W`, the map induced by the Hodge morphism `ξ̃` on `H^k(V, -)` is
bijective as soon as the morphism `ξ̃` of `f ∣_ V` over `W`, for the restricted classes, induces
bijections on cohomology.** -/
theorem bijective_homology_hodgeLerayHirschMorphism_of_restrict
    (h : ∀ k, Function.Bijective ((cohomologyFunctor (g.resLE W V hVW) k).map
      (hodgeLerayHirschMorphism (f ∣_ V) (g.resLE W V hVW) n
        fun i => hodgeRestrictClass f g V W hVW (n i) (ξ i))).hom) (k : ℤ) :
    Function.Bijective ((DerivedCategory.homologyFunctor _ k).map
      ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (inverseImageBase g) V).map
        (hodgeLerayHirschMorphism f g n ξ))) := by
  let H := Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (inverseImageBase g) V ⋙
    DerivedCategory.homologyFunctor _ k
  have hY := isIso_derivedSectionsOverOpen_map_hodgeRestrictComparisonY g V W hVW
  have hX := isIso_derivedSectionsOverOpen_map_hodgeRestrictComparisonX f g V W hVW
  have h₁ : Function.Bijective (H.map (biproduct.map fun i =>
      (hodgeRestrictComparisonY g V W hVW)⟦-(n i : ℤ)⟧')) := by
    refine bijective_map_biproduct_map H _ fun i => ?_
    have := AlgebraicGeometry.DeRhamLerayHirsch.isIso_derivedSectionsOverOpen_map_shift
      (Z := inverseImageBase g) V _ hY (-(n i : ℤ))
    exact (ConcreteCategory.isIso_iff_bijective _).1 (Functor.map_isIso
      (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing (inverseImageBase g)).obj.obj (op V))) k)
      ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (inverseImageBase g) V).map
        ((hodgeRestrictComparisonY g V W hVW)⟦-(n i : ℤ)⟧')))
  have h₂ : Function.Bijective (H.map (biproductShiftComparison
      (derivedPushforward (restrictMapY g V W hVW)) (fun i => -(n i : ℤ))
        (hodgeObject (g.resLE W V hVW)))) :=
    ConcreteCategory.bijective_of_isIso _
  have h₃ : Function.Bijective (H.map ((derivedPushforward (restrictMapY g V W hVW)).map
      (hodgeLerayHirschMorphism (f ∣_ V) (g.resLE W V hVW) n
        fun i => hodgeRestrictClass f g V W hVW (n i) (ξ i)))) := by
    refine (Stacks.Cohomology.OpenImmersionSections.bijective_homology_map_derivedPushforward_iff
      (restrictMapY g V W hVW) V _ k).2 ?_
    have key : ∀ (U' : TopologicalSpace.Opens (inverseImageBase (g.resLE W V hVW)).carrier),
        U' = ⊤ → Function.Bijective ((DerivedCategory.homologyFunctor _ k).map
          ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen _ U').map
            (hodgeLerayHirschMorphism (f ∣_ V) (g.resLE W V hVW) n
              fun i => hodgeRestrictClass f g V W hVW (n i) (ξ i)))) := by
      rintro _ rfl
      exact h k
    exact key _ (Scheme.Opens.ι_preimage_self V)
  have h₄ : Function.Bijective (H.map (hodgeRestrictCompY f g V W hVW)) :=
    ConcreteCategory.bijective_of_isIso _
  have h₅ : Function.Bijective (H.map ((relativeDirectImage f g).map
      (hodgeRestrictComparisonX f g V W hVW))) :=
    (Stacks.Cohomology.OpenImmersionSections.bijective_homology_map_derivedPushforward_iff
      (baseMap f g) V _ k).2 (ConcreteCategory.bijective_of_isIso _)
  have h₆ : Function.Bijective (H.map (hodgeRestrictCompX f g V W hVW)) :=
    ConcreteCategory.bijective_of_isIso _
  exact bijective_map_of_comp_eq H _ _ _ _ _ _ _
    (hodgeLerayHirschMorphism_comp_restrict f g V W hVW n ξ) h₅ h₆ h₁ h₂ h₃ h₄

end Restrict

/-! ### `ξ̃` is an isomorphism as soon as it is so over the members of a basis -/

section Basis

open AlgebraicGeometry.DeRhamLerayHirsch (cohomologyFunctor)

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) {N : ℕ} (n : Fin N → ℕ)
  (ξ : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ))
  {𝔅 : Set Y.Opens}

/-- **The Hodge morphism `ξ̃` is an isomorphism if it is so on cohomology over a basis**: let `𝔅`
be a basis of the topology of `Y` such that each `V ∈ 𝔅` lies in `g⁻¹W` for an open `W ⊆ S` over
which the morphism `ξ̃` of `f ∣_ V ⟶ W`, for the restricted classes, induces bijections on
cohomology. Then `ξ̃ : ⨁ ℋ_{Y/S}[-n_i] ⟶ Rf_*ℋ_{X/S}` is an isomorphism in `D(Y, g⁻¹𝒪_S)`. -/
theorem isIso_hodgeLerayHirschMorphism_of_isBasis (h𝔅 : Opens.IsBasis 𝔅)
    (h : ∀ V ∈ 𝔅, ∃ (W : S.Opens) (hVW : V ≤ g ⁻¹ᵁ W), ∀ k, Function.Bijective
      ((cohomologyFunctor (g.resLE W V hVW) k).map
        (hodgeLerayHirschMorphism (f ∣_ V) (g.resLE W V hVW) n
          fun i => hodgeRestrictClass f g V W hVW (n i) (ξ i))).hom) :
    IsIso (hodgeLerayHirschMorphism f g n ξ) := by
  refine Stacks.Cohomology.DerivedIsoOnABasis.isIso_of_bijective_homology_derivedSectionsOverOpen
    (Z := inverseImageBase g) h𝔅 (hodgeLerayHirschMorphism f g n ξ) fun V hV k => ?_
  obtain ⟨W, hVW, hk⟩ := h V hV
  exact bijective_homology_hodgeLerayHirschMorphism_of_restrict f g V W hVW n ξ hk k

/-- **The Hodge morphism `ξ̃` is an isomorphism if the Leray--Hirsch formula holds over a basis**:
let `𝔅` be a basis of the topology of `Y` such that each `V ∈ 𝔅` lies in `g⁻¹W` for an open
`W ⊆ S` for which, in every degree `k`, the map
`⨁_i H^{k - n_i}(V, ℋ_{V/W}) ⟶ H^k(f⁻¹V, ℋ_{f⁻¹V/W}), (a_i) ↦ ∑ ξ_i|_{f⁻¹V} ∪ (f ∣_ V)^*a_i` is
bijective. Then `ξ̃ : ⨁ ℋ_{Y/S}[-n_i] ⟶ Rf_*ℋ_{X/S}` is an isomorphism in `D(Y, g⁻¹𝒪_S)`. -/
theorem isIso_hodgeLerayHirschMorphism_of_isBasis_of_bijective (h𝔅 : Opens.IsBasis 𝔅)
    (h : ∀ V ∈ 𝔅, ∃ (W : S.Opens) (hVW : V ≤ g ⁻¹ᵁ W), ∀ k, Function.Bijective
      (fun a : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (g.resLE W V hVW)))
          (k - n i) =>
        ∑ i, (eqToHom (congrArg (dgaCohomology (hodgeDGA
            (Scheme.Hom.deRhamAlgebras (f ∣_ V ≫ g.resLE W V hVW))))
            (add_sub_cancel (n i : ℤ) k))).hom
          (dgaCohomologyCup (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ∣_ V ≫ g.resLE W V hVW)))
            (n i) (k - n i) (hodgeRestrictClass f g V W hVW (n i) (ξ i))
            (hodgeDgaPullback (f ∣_ V) (g.resLE W V hVW) (k - n i) (a i))))) :
    IsIso (hodgeLerayHirschMorphism f g n ξ) := by
  refine isIso_hodgeLerayHirschMorphism_of_isBasis f g n ξ h𝔅 fun V hV => ?_
  obtain ⟨W, hVW, hk⟩ := h V hV
  exact ⟨W, hVW, fun k => (bijective_cohomologyFunctor_hodgeLerayHirschMorphism_iff (f ∣_ V)
    (g.resLE W V hVW) n (fun i => hodgeRestrictClass f g V W hVW (n i) (ξ i)) k).2 (hk k)⟩

/-- **The Leray--Hirsch theorem for Hodge cohomology, from the formula over a basis**: under the
hypotheses of `Stacks.HodgeWeil.isIso_hodgeLerayHirschMorphism_of_isBasis_of_bijective`, in every
degree `k` the map

`⨁_i H^{k - n_i}(Y, ℋ_{Y/S}) ⟶ H^k(X, ℋ_{X/S}), (a_i) ↦ ∑ ξ_i ∪ f^*a_i`

is bijective. -/
theorem bijective_sum_dgaCohomologyCup_of_isBasis (h𝔅 : Opens.IsBasis 𝔅)
    (h : ∀ V ∈ 𝔅, ∃ (W : S.Opens) (hVW : V ≤ g ⁻¹ᵁ W), ∀ k, Function.Bijective
      (fun a : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (g.resLE W V hVW)))
          (k - n i) =>
        ∑ i, (eqToHom (congrArg (dgaCohomology (hodgeDGA
            (Scheme.Hom.deRhamAlgebras (f ∣_ V ≫ g.resLE W V hVW))))
            (add_sub_cancel (n i : ℤ) k))).hom
          (dgaCohomologyCup (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ∣_ V ≫ g.resLE W V hVW)))
            (n i) (k - n i) (hodgeRestrictClass f g V W hVW (n i) (ξ i))
            (hodgeDgaPullback (f ∣_ V) (g.resLE W V hVW) (k - n i) (a i)))))
    (k : ℤ) :
    Function.Bijective
      (fun a : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
        ∑ i, (eqToHom (congrArg (dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))))
            (add_sub_cancel (n i : ℤ) k))).hom
          (dgaCohomologyCup (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i) (k - n i)
            (ξ i) (hodgeDgaPullback f g (k - n i) (a i)))) :=
  have := isIso_hodgeLerayHirschMorphism_of_isBasis_of_bijective f g n ξ h𝔅 h
  bijective_sum_dgaCohomologyCup_of_isIso f g n ξ k

end Basis

end Stacks.HodgeWeil

end
