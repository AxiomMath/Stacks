module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulAdicReductionIdentity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCommutesCompletionKoszulTower
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtAugmentationFormula
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeShift

/-!
# The coefficient-free identity of Tag 0A0K in degree zero, and the sign `(-1)^r`

`KoszulAdicReductionUnit.lean` reduces part (1) of [Stacks, Tag 0A0K] over the tower
`n ↦ 𝒪/ℐⁿ⁺¹` to an identity in which the coefficient object does not appear
(`AlgebraicGeometry.RingedSite.eq_adicQuotientReduction_of_dual_comp_eq`), and
`KoszulAdicReductionIdentity.lean` names the comparison `ψ` of towers that identity is about and
collapses every step of it that is a cancellation. **This file proves what is left**: a single
chain-level identity in degree zero, with no derived category in it, and then closes the chain.

## The identity, and the sign

Written out, what survives of the composite
`𝒪[0] ≅ R𝑆heafHom_𝒪(𝒪[0], 𝒪[0]) ⟶ R𝑆heafHom_𝒪(K^n, 𝒪[0]) ⟶ 𝒪/ℐⁿ⁺¹[0]` is the class of a
morphism of complexes `𝒪[0] ⟶ H^r(K^n ⊗ 𝒪)[0]`, namely the trivialisation of
`SheafHom•(𝒪[0], 𝒪[0])`, the dual of the morphism of complexes `K^n ⟶ Č(f) ⟶ 𝒪[0]`, the
self-duality `AlgebraicGeometry.RingedSite.koszulDualComplexIsoCoeff` of the Koszul complex, and
the comparison `AlgebraicGeometry.RingedSite.koszulShiftedToTopSingleComplexMap` across the shift
by `r`. A morphism out of a complex concentrated in degree zero is its degree-zero component
(`HomologicalComplex.from_single_hom_ext`), and that component is **`(-1)^r` times** the canonical
map `𝒪 ⟶ H^r(K^n ⊗ 𝒪)` onto the top Koszul cohomology sheaf.

The sign is not an artefact: the degree-zero component of the self-duality of the Koszul complex
reads the top-degree factor through `CategoryTheory.AlternatingCech.koszulDualIsoAt`, which
multiplies the factor indexed by `T` by `CategoryTheory.AlternatingCech.dualSign T`, and at the
unique top-degree index `T = Finset.univ` that twist is
`(-1)^{r(r-1)/2 + r(r+1)/2} = (-1)^{r²} = (-1)^r` (`AlgebraicGeometry.RingedSite.dualSign_univ`).
So the identity of [Stacks, Tag 0A0K] holds on the nose not for the pigeonhole comparison of
towers itself but for that comparison twisted by `(-1)^r`, which is
`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientSigned` of
`KoszulAdicReductionIdentity.lean` and which
`AlgebraicGeometry.RingedSite.derivedSheafHomToAdicQuotientTower` is built from. The two signs
then multiply to one.

## Main results

* `RingedSite.structureSheafHomIso_inv_comp_homMap_comp_koszulDualComplexIsoCoeff_comp`
  — **the chain-level identity**, as an equality of morphisms of complexes.
* `RingedSite.derivedStructureSheafHomIso_inv_comp_map_comp_derivedSheafHomToAdicQuotientTower`
  — **the coefficient-free identity in the derived category**, which is the hypothesis `hψ` of
  `AlgebraicGeometry.RingedSite.eq_adicQuotientReduction_of_dual_comp_eq`.
* `AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_adicReductionTower_completion`
  — **part (1) of [Stacks, Tag 0A0K] with its projections named**: the Čech completion `K^∧` of
  an arbitrary `K ∈ D(𝒪)` is a derived limit of `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` through the canonical
  factorizations `AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor` of
  [Stacks, Tag 0CQH]. This is
  `AlgebraicGeometry.RingedSite.exists_isDerivedLimitWithProjections_adicReductionTower_completion`
  with the `∃ p` eliminated.
* `AlgebraicGeometry.RingedSite.homDegreeIsoSingle_comp_internalHomPre_unit` — the section-level
  input: the trivialisation `Hom_𝒪(𝒪, N) ≅ N` of [Stacks, Tag 03EM] agrees, in degree zero, with
  evaluation at the unit section.
* `AlgebraicGeometry.RingedSite.completionUnit_app_comp_koszulTopSingleProjection_eq` — **the same
  cone computation with coefficients**, which is what part (3) of [Stacks, Tag 0A0K] needs: the
  completion unit followed by the `n`-th projection of
  `AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion` is
  `(-1)^r` times the quotient map `ℱ ⟶ ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ` in degree zero. Part (1)
  cannot be read off it and it cannot be read off part (1): the two towers are
  `n ↦ ℱ ⊗^𝐋_𝒪 𝒪/𝓘ⁿ` and `n ↦ ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`, and the coefficient leaves the
  Koszul complex only in the first.

## The chain-level identity is stated with coefficients

Every statement of this file below `dualSign_univ` is now at an **arbitrary** coefficient sheaf
`ℱ`, the coefficient-free ones being their instances at `ℱ = 𝒪`. Nothing in the degree-zero
computation used the unit: the inclusion of the top-degree factor
(`AlgebraicGeometry.RingedSite.koszulTopTermInj`), the dual factor
(`AlgebraicGeometry.RingedSite.koszulDualFactor`), the self-duality
(`AlgebraicGeometry.RingedSite.koszulDualComplexIsoCoeff`) and the trivialisation
(`AlgebraicGeometry.RingedSite.unitHomSheafIso`) all take the coefficient as a parameter, and the
one genuinely coefficient-free step — the degree-zero component of the Koszul–Čech comparison
followed by the Čech augmentation,
`AlgebraicGeometry.RingedSite.termι_comp_koszulCechComplexMap_f_zero_comp_cechAugmentationZero` —
is about the map `K^n ⟶ 𝒪[0]` alone and stays where it was.

## Why the trivialisation of `Hom_𝒪(𝒪, N)` has to be computed

`AlgebraicGeometry.RingedSite.koszulDualComplexIsoCoeff` ends with the transport of coefficients
along `Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso`, which is produced from
uniqueness of right adjoints and so says nothing about sections; and the identity to be proved is
that a particular endomorphism of `𝒪` is the identity, which an isomorphism `Hom_𝒪(𝒪, 𝒪) ≅ 𝒪`
natural in the second variable does not by itself decide — it could be multiplication by any
global unit. So the trivialisation is computed here:
`Stacks.SheafOfModules.InternalHom.unitInternalHomIso_inv_eq` identifies its inverse with the
currying of the right unitor, using that the comparison of two right adjoints is the unit of the
second (`CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app`), and
`AlgebraicGeometry.RingedSite.unitHomSheafIso_inv_val_app_app` reads that off on sections as
`x ↦ (y ↦ y • x)`.

There is a second trivialisation of `ℰom_𝒪(𝒪, -)` in the tree,
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso`, got from the monoidal-closed
structure, whose sections are computed by
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso_hom_val_app`; the two
trivialisations are identified only over a topological space
(`Stacks.SheafOfModules.internalHomSecondFunctorUnitIso_hom_app_eq_internalHomSheafUnitIso`), and
it is the adjunction-uniqueness one that
`AlgebraicGeometry.RingedSite.koszulDualComplexIsoCoeff` is built from, so its sections are what
has to be computed here.

The degree-zero component of the shift isomorphism of the single functors of complexes is read off
by `Stacks.DerivedIndexing.singleFunctors_shiftIso_hom_app_f` of `StacksFrontier/Homology/DerivedIndexing/SingleDegreeShift.lean`, which
already states, for an arbitrary degree and an arbitrary proof of the equality of the two objects,
that that component is the corresponding `eqToHom`.

## Implementation notes

**Three spellings of the top degree.** The top-degree term of the Koszul complex is met here in
the degrees `0 + r` (which is what the degree-zero term of an `r`-fold shift unfolds to), `r`
(the degree the tower of top cohomology sheaves is taken in) and
`AlgebraicGeometry.RingedSite.koszulTopDeg r = r - 1 + 1` (the degree the index type of that term
carries). The three integers are equal and not definitionally equal, so each passage between them
is an explicit transport: `HomologicalComplex.XIsoOfEq` for the terms of the complex, and the
`hp ▸` transports `AlgebraicGeometry.RingedSite.koszulToTopHomologyAt` and
`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientAt` for the maps, whose statements
are proved by `subst` on the equation of degrees.

**Term mode, not rewriting.** `(K⟦r⟧).X 0`, `K.X (0 + r)` and
`∏_{|S| = 0 + r} (K^n ⊗ 𝒪)_S` are three definitionally equal spellings of one object which no
rewriting tactic can pass between: a goal mixing them is not type-correct at the `implicit`
transparency level at which `rw` checks its motive, and the symptom is `rw` reporting that it did
not find a pattern that is visibly present. The degree-zero computation is therefore assembled
from `Eq.trans`, `CategoryTheory.eq_whisker` and `CategoryTheory.whisker_eq` rather than by
rewriting, which is also why the statements of its steps are ascribed as carefully as they are.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace Stacks.SheafOfModules.InternalHom

open Stacks.PresheafOfModules.InternalHom

variable {C : Type u} [Category.{u} C] (O : Cᵒᵖ ⥤ CommRingCat.{u})

/-- The inverse of the trivialisation `unitInternalHomIso O M : Hom_𝒪(𝒪, M) ≅ M` is the currying
`M ⟶ Hom_𝒪(𝒪, M)` of the right unitor `M ⊗ 𝒪 ⟶ M`. -/
theorem unitInternalHomIso_inv_eq (M : PresheafOfModules.{u} (Oforget O)) :
    (unitInternalHomIso O M).inv =
      curryGlobal O M (PresheafOfModules.unit (Oforget O)) M (ρ_ M).hom := by
  have h := Adjunction.unit_rightAdjointUniq_hom_app Adjunction.id
    ((presheafTensorHomAdjunction O (PresheafOfModules.unit (Oforget O))).ofNatIsoLeft
      (rightUnitorNatIso (PresheafOfModules.{u} (Oforget O)))) M
  have h2 := NatTrans.congr_app
    (Adjunction.ofNatIsoLeft_unit
      (presheafTensorHomAdjunction O (PresheafOfModules.unit (Oforget O)))
      (rightUnitorNatIso (PresheafOfModules.{u} (Oforget O)))) M
  exact ((Category.id_comp _).symm.trans h).trans h2

end Stacks.SheafOfModules.InternalHom

namespace AlgebraicGeometry.RingedSite

open Stacks.PresheafOfModules.InternalHom Stacks.SheafOfModules.InternalHom

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The sheaf-level trivialisation, inverted, on underlying presheaves. -/
theorem unitHomSheafIso_inv_val
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (unitHomSheafIso X G).inv.val =
      curryGlobal X.O.obj G.val (PresheafOfModules.unit (Oforget X.O.obj)) G.val
        (ρ_ G.val).hom := by
  refine Eq.trans ?_ (unitInternalHomIso_inv_eq X.O.obj G.val)
  exact (SheafOfModules.fullyFaithfulForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map_preimage
    (show (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj G ⟶
        (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
          (unitHomSheaf X G) from
      (unitInternalHomIso X.O.obj G.val).inv)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The trivialisation, inverted, on sections: a section `x` of `G` over `U` goes to the
morphism `𝒪|_U ⟶ G|_U` sending `y` to `y • x`. -/
theorem unitHomSheafIso_inv_val_app_app
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (x : G.val.obj (op U)) {T : X.C} (q : T ⟶ U)
    (y : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T)) :
    sectionOfRestr X.O.obj G.val U q
        (((((unitHomSheafIso X G).inv.val.app (op U)).hom x).app (op (Over.mk q))).hom
          (restrSection X.O.obj (PresheafOfModules.unit (Oforget X.O.obj)) U q y)) =
      y • G.val.restrictₛₗ q.op x := by
  have h := congrArg (fun φ : G.val ⟶
      internalHom X.O.obj (PresheafOfModules.unit (Oforget X.O.obj)) G.val =>
      sectionOfRestr X.O.obj G.val U q ((((φ.app (op U)).hom x).app (op (Over.mk q))).hom
        (restrSection X.O.obj (PresheafOfModules.unit (Oforget X.O.obj)) U q y)))
    (unitHomSheafIso_inv_val X G)
  refine h.trans ?_
  refine (curryGlobalMap_apply X.O.obj G.val (PresheafOfModules.unit (Oforget X.O.obj)) G.val
    (ρ_ G.val).hom U x q y).trans ?_
  exact ModuleCat.MonoidalCategory.rightUnitor_hom_apply _ _

example (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) A).hom = 𝟙 A := rfl

/-- **The two trivialisations of the internal Hom out of the structure sheaf agree in degree
zero.** Reading a degree-zero section of `SheafHom•(𝒪[0], N[0])` as a homomorphism out of the
degree-zero term of `𝒪[0]` (`AlgebraicGeometry.RingedSite.homDegreeIsoSingle`), precomposing with
the identification of that term with `𝒪` and trivialising, is evaluation at the unit section. -/
theorem homDegreeIsoSingle_comp_internalHomPre_unit
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (homDegreeIsoSingle X (structureSheafComplex X) N 0).hom ≫
        internalHomPre X (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv =
      evalAtOneHom X (singleSheafComplex X N) 0 ≫ (unitHomSheafIso X N).inv := by
  ext U s
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  obtain ⟨z, rfl⟩ : ∃ z' : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V.unop.left),
      (z' : (((restrFun X.O.obj U.unop).obj
        (valOf X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj V)) = z :=
    ⟨z, rfl⟩
  refine Eq.trans ?_ (unitHomSheafIso_inv_val_app_app X N U.unop
    (evalAtOneFun X (singleSheafComplex X N) 0 U.unop s) V.unop.hom z).symm
  refine Eq.trans (homDegreeIsoSingle_app_apply X (structureSheafComplex X) N 0 U.unop
    V.unop.left V.unop.hom s z) ?_
  have hz : (z • structureSheafOne X V.unop.left :
      ((structureSheafComplex X).X 0).val.obj (op V.unop.left)) = z := mul_one z
  show applyHomSectionOver X (sheafHomComplex X (structureSheafComplex X)
      (singleSheafComplex X N)) U.unop V.unop.left V.unop.hom 0 0 0 (by omega) s z = _
  refine Eq.trans (congrArg (applyHomSectionOver X (sheafHomComplex X (structureSheafComplex X)
    (singleSheafComplex X N)) U.unop V.unop.left V.unop.hom 0 0 0 (by omega) s) hz.symm) ?_
  refine Eq.trans (applyHomSectionOver_smul_right X (sheafHomComplex X (structureSheafComplex X)
    (singleSheafComplex X N)) U.unop V.unop.left V.unop.hom 0 0 0 (by omega) s z
    (structureSheafOne X V.unop.left)) ?_
  refine congrArg (fun w => z • w) ?_
  refine Eq.trans (congrArg (applyHomSectionOver X (sheafHomComplex X (structureSheafComplex X)
    (singleSheafComplex X N)) U.unop V.unop.left V.unop.hom 0 0 0 (by omega) s)
    (structureSheafOne_restrict X V.unop.hom).symm) ?_
  exact applyHomSectionOver_map X (sheafHomComplex X (structureSheafComplex X)
    (singleSheafComplex X N)) U.unop V.unop.left V.unop.hom 0 0 0 (by omega) s
    (structureSheafOne X U.unop)

section KoszulAugmentation

open CategoryTheory.AlternatingCech

variable [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

open scoped IsMulCommutative

attribute [local instance]
  hasFiniteBiproducts_sheafOfModules

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Multiplication by the empty subproduct is the identity. -/
theorem awaySmul_pow_app_prodGlobalSection_empty (k : ℕ)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((awaySmul X (prodGlobalSection f (∅ : Finset (Fin r))) ^ k).asHom.app M) = 𝟙 M :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext
    (LinearMap.ext fun x => by
      rw [awaySmul_pow_app_apply, globalSectionVal_prodGlobalSection, Finset.prod_empty,
        one_pow, one_smul]
      rfl))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The leg of the cocone at the empty subset is the canonical map. -/
theorem awayModuleCoconeι_prodGlobalSection_empty (k : ℕ) :
    awayModuleCoconeι X (prodGlobalSection f (∅ : Finset (Fin r))) k =
      unitToAwayModule X (prodGlobalSection f (∅ : Finset (Fin r))) := by
  have hinv : inv ((awaySmul X (prodGlobalSection f (∅ : Finset (Fin r))) ^ k).asHom.app
      (awayModule X (prodGlobalSection f (∅ : Finset (Fin r))))) =
      𝟙 (awayModule X (prodGlobalSection f (∅ : Finset (Fin r)))) :=
    IsIso.inv_eq_of_hom_inv_id (by
      rw [awaySmul_pow_app_prodGlobalSection_empty]
      exact Category.id_comp _)
  show unitToAwayModule X (prodGlobalSection f (∅ : Finset (Fin r))) ≫
    inv ((awaySmul X (prodGlobalSection f (∅ : Finset (Fin r))) ^ k).asHom.app
      (awayModule X (prodGlobalSection f (∅ : Finset (Fin r))))) = _
  exact (congrArg (fun w => unitToAwayModule X (prodGlobalSection f (∅ : Finset (Fin r))) ≫ w)
    hinv).trans (Category.comp_id _)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The degree-zero component of the Koszul–Čech comparison followed by the augmentation is the
identity**, read through the unique degree-zero factor. -/
theorem termι_comp_koszulCechComplexMap_f_zero_comp_cechAugmentationZero (n : ℕ)
    (S : Idx r (0 : ℤ)) :
    termι (koszulPowerFunctor X f n) S ≫ (koszulCechComplexMap X f n).f 0 ≫
        cechAugmentationZero X f =
      𝟙 (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  obtain rfl : S = default := Subsingleton.elim _ _
  have h1 : termι (koszulPowerFunctor X f n) (default : Idx r (0 : ℤ)) ≫
      (koszulCechComplexMap X f n).f 0 =
      awayModuleCoconeι X (prodGlobalSection f (∅ : Finset (Fin r))) (n + 1) ≫
        termι (awayLocalizationFunctor X f) (default : Idx r (0 : ℤ)) :=
    termι_comp_mapX (koszulCechTrans X f n) default
  have h2 : termι (awayLocalizationFunctor X f) (default : Idx r (0 : ℤ)) ≫
      cechAugmentationZero X f = (unitIsoAwayModuleEmpty X f).inv :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun w => w ≫ (unitIsoAwayModuleEmpty X f).inv)
        (termι_comp_π_self (awayLocalizationFunctor X f) (default : Idx r (0 : ℤ)))).trans
        (Category.id_comp _))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (h1 =≫ cechAugmentationZero X f).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (awayModuleCoconeι X (prodGlobalSection f (∅ : Finset (Fin r))) (n + 1) ≫= h2).trans ?_
  rw [awayModuleCoconeι_prodGlobalSection_empty, ← unitIsoAwayModuleEmpty_hom, Iso.hom_inv_id]

end KoszulAugmentation

section TopDegree

open CategoryTheory.AlternatingCech

variable [HasWeakSheafify X.J CommRingCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

open scoped IsMulCommutative

attribute [local instance]
  hasFiniteBiproducts_sheafOfModules hasSheafCompose_forget₂_ringCat

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
/-- `koszulToTopHomologyOn` at an arbitrary spelling of the top degree, written out. -/
theorem koszulToTopHomologyAt_eq (p : ℤ) (hp : koszulTopDeg r = p) (n : ℕ)
    (hnext : (ComplexShape.up ℤ).next p = p + 1)
    (hz : (koszulPowerComplexOn X f ℱ n).d p (p + 1) = 0) :
    koszulToTopHomologyAt X f ℱ p hp n =
      koszulTopTermInj X f ℱ n ≫
        ((koszulPowerComplexOn X f ℱ n).XIsoOfEq hp).hom ≫
        HomologicalComplex.topToHomology
          (koszulPowerComplexOn X f ℱ n) hnext hz := by
  subst hp
  rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- The three identifications of the top-degree term of the single complex compose to the
identity. -/
theorem singleShiftIso_f_zero
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (r : ℤ) A).inv ≫
        (((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
          (r : ℤ)).obj A).XIsoOfEq
            (show (0 : ℤ) + (r : ℤ) = (r : ℤ) from zero_add _)).inv ≫
        (((CochainComplex.singleFunctors
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso
          (r : ℤ) 0 (r : ℤ) (by ring)).hom.app A).f 0 = 𝟙 A := by
  rw [Stacks.DerivedIndexing.singleFunctors_shiftIso_hom_app_f
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (r : ℤ) 0 (r : ℤ)
    (by ring) A 0
    (show (((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (r : ℤ)).obj
          A)⟦(r : ℤ)⟧).X 0 =
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj A).X 0 from by
      rw [CochainComplex.shiftFunctor_obj_X', zero_add]
      exact (HomologicalComplex.single_obj_X_self _ _ _).trans
        (HomologicalComplex.single_obj_X_self _ _ _).symm)]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.XIsoOfEq, eqToIso.inv, eqToHom_trans]
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- The same, absorbed into a precomposition. -/
theorem comp_singleShiftIso_f_zero
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : Z ⟶ A) :
    g ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (r : ℤ) A).inv ≫
        (((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
          (r : ℤ)).obj A).XIsoOfEq
            (show (0 : ℤ) + (r : ℤ) = (r : ℤ) from zero_add _)).inv ≫
        (((CochainComplex.singleFunctors
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso
          (r : ℤ) 0 (r : ℤ) (by ring)).hom.app A).f 0 = g := by
  rw [singleShiftIso_f_zero]
  exact Category.comp_id g

omit [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **The inclusion of the unique top-degree factor, followed by the degree-zero component of
the comparison across the shift, is the canonical map onto the top cohomology sheaf.** -/
theorem koszulTopTermInj_comp_koszulShiftedToTopSingleComplexMap_f_zero (n : ℕ) :
    koszulTopTermInj X f ℱ n ≫
        ((koszulPowerComplexOn X f ℱ n).XIsoOfEq
          (show koszulTopDeg r = (0 : ℤ) + (r : ℤ) by ring)).hom ≫
        (koszulShiftedToTopSingleComplexMap X f ℱ n).f 0 =
      koszulToTopHomologyAt X f ℱ (r : ℤ) koszulTopDeg_eq n := by
  have hr : (0 : ℤ) + (r : ℤ) = (r : ℤ) := zero_add _
  have hψ := (Iso.eq_comp_inv _).2 (HomologicalComplex.XIsoOfEq_hom_naturality
    (HomologicalComplex.toSingleTopCohomology
      (koszulPowerComplexOn X f ℱ n) (next_top_eq (r := r))
      (koszulPowerComplexOn_d_at_top_eq_zero X f ℱ n)) hr)
  refine Eq.trans ?_ (koszulToTopHomologyAt_eq X f ℱ (r : ℤ) koszulTopDeg_eq n
    (next_top_eq (r := r))
    (koszulPowerComplexOn_d_at_top_eq_zero X f ℱ n)).symm
  show koszulTopTermInj X f ℱ n ≫
      ((koszulPowerComplexOn X f ℱ n).XIsoOfEq
        (show koszulTopDeg r = (0 : ℤ) + (r : ℤ) by ring)).hom ≫
      (HomologicalComplex.toSingleTopCohomology
        (koszulPowerComplexOn X f ℱ n) (next_top_eq (r := r))
        (koszulPowerComplexOn_d_at_top_eq_zero X f
          ℱ n)).f ((0 : ℤ) + (r : ℤ)) ≫
      (((CochainComplex.singleFunctors
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso
        (r : ℤ) 0 (r : ℤ) (by ring)).hom.app
          ((koszulPowerComplexOn X f ℱ n).homology
            (r : ℤ))).f 0 = _
  rw [hψ, HomologicalComplex.toSingleTopCohomology_f]
  simp only [Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc]
  rw [comp_singleShiftIso_f_zero]
  rfl

end TopDegree

section DegreeZero

open CategoryTheory.AlternatingCech

variable [HasWeakSheafify X.J CommRingCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

open scoped IsMulCommutative

attribute [local instance]
  hasFiniteBiproducts_sheafOfModules hasSheafCompose_forget₂_ringCat

/-- **The dual twist at the full subset is `(-1)^r`.** The exponent is
`r(r-1)/2 + r(r+1)/2 = r²`. -/
theorem dualSign_univ : dualSign (Finset.univ : Finset (Fin r)) = (-1 : ℤ) ^ r := by
  rw [dualSign, Finset.card_univ, Fintype.card_fin, triangleSum, Finset.sum_range_succ,
    Fin.sum_univ_eq_sum_range (fun i => i) r,
    show (∑ i ∈ Finset.range r, i) + ((∑ i ∈ Finset.range r, i) + r) =
      2 * (∑ i ∈ Finset.range r, i) + r by ring, pow_add, pow_mul]
  norm_num

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- `koszulTopTermInj` transported to an arbitrary spelling of the top degree is the lift all of
whose components are the identity. -/
theorem koszulTopTermInj_comp_XIsoOfEq
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) (p : ℤ)
    (hp : koszulTopDeg r = p) :
    koszulTopTermInj X f M n ≫ ((koszulPowerComplexOn X f M n).XIsoOfEq hp).hom =
      Pi.lift fun _ : Idx r p => 𝟙 M := by
  subst hp
  rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- **The dual of the Koszul augmentation with coefficients in `ℱ`, in degree zero.** The
trivialisation of `SheafHom•(𝒪[0], ℱ[0])`, the dual of the morphism of complexes `K^n ⟶ 𝒪[0]`,
and the self-duality of the Koszul complex compose, in degree zero, to `(-1)^r` times the
inclusion of the unique top-degree factor of `K^n ⊗ ℱ`.

At `ℱ = 𝒪` this is the coefficient-free statement part (1) of [Stacks, Tag 0A0K] consumes; at a
general `ℱ` it is what part (3) consumes, where the coefficient stays inside the Koszul complex
and does not drop out of the tower comparison. -/
theorem structureSheafHomIso_inv_comp_homMap_comp_koszulDualComplexIsoCoeff_f_zero (n : ℕ) :
    (structureSheafHomIso X (singleSheafComplex X ℱ)).inv.f 0 ≫
        (homMap X (koszulCechComplexMap X f n ≫ cechAugmentation X f)
          (𝟙 (singleSheafComplex X ℱ))).f 0 ≫
        (koszulDualComplexIsoCoeff X f ℱ n).hom.f 0 =
      (-1 : ℤ) ^ r • (koszulTopTermInj X f ℱ n ≫
        ((koszulPowerComplexOn X f ℱ n).XIsoOfEq
          (show koszulTopDeg r = (0 : ℤ) + (r : ℤ) by ring)).hom) := by
  refine Pi.hom_ext _ _ fun S => ?_
  have hS : S.1 = (Finset.univ : Finset (Fin r)) := by
    have hc : S.1.card = Fintype.card (Fin r) := by
      have h : (S.1.card : ℤ) = (0 : ℤ) + (r : ℤ) := S.2
      rw [Fintype.card_fin]
      omega
    rw [Finset.card_eq_iff_eq_univ] at hc
    exact hc
  have hR : ((-1 : ℤ) ^ r • (koszulTopTermInj X f ℱ n ≫
        ((koszulPowerComplexOn X f ℱ n).XIsoOfEq
          (show koszulTopDeg r = (0 : ℤ) + (r : ℤ) by ring)).hom)) ≫
        Pi.π (fun T : Idx r ((0 : ℤ) + (r : ℤ)) =>
          (koszulPowerFunctorOn X f ℱ n).obj T.1) S =
      (-1 : ℤ) ^ r • 𝟙 ℱ :=
    (Preadditive.zsmul_comp _ _ _).trans
      (congrArg (fun w => (-1 : ℤ) ^ r • w)
        ((koszulTopTermInj_comp_XIsoOfEq X f ℱ n
            ((0 : ℤ) + (r : ℤ)) (show koszulTopDeg r = (0 : ℤ) + (r : ℤ) by ring) =≫
          Pi.π (fun T : Idx r ((0 : ℤ) + (r : ℤ)) =>
            (koszulPowerFunctorOn X f ℱ n).obj T.1) S).trans
          (Pi.lift_comp_π _ S)))
  refine Eq.trans ?_ hR.symm
  have hA : (structureSheafHomIso X (singleSheafComplex X ℱ)).inv.f 0 ≫
      evalAtOneHom X (singleSheafComplex X ℱ) 0 =
      𝟙 ((singleSheafComplex X ℱ).X 0) :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ 0)
      (structureSheafHomIso X (singleSheafComplex X ℱ)).inv_hom_id
  have haug : termι (koszulPowerFunctor X f n)
        (Idx.compl (show ((0 : ℤ) + (r : ℤ)) + (-0 : ℤ) = (r : ℤ) by ring) S) ≫
      (koszulCechComplexMap X f n ≫ cechAugmentation X f).f (-0) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv := by
    refine Eq.trans (congrArg (fun w => termι (koszulPowerFunctor X f n)
      (Idx.compl (show ((0 : ℤ) + (r : ℤ)) + (-0 : ℤ) = (r : ℤ) by ring) S) ≫
      (koszulCechComplexMap X f n).f 0 ≫ w) (cechAugmentation_f_zero X f)) ?_
    refine Eq.trans (congrArg (fun w => termι (koszulPowerFunctor X f n)
      (Idx.compl (show ((0 : ℤ) + (r : ℤ)) + (-0 : ℤ) = (r : ℤ) by ring) S) ≫ w)
      (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (termι_comp_koszulCechComplexMap_f_zero_comp_cechAugmentationZero X f n
      (Idx.compl (show ((0 : ℤ) + (r : ℤ)) + (-0 : ℤ) = (r : ℤ) by ring) S) =≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv) ?_
    exact Category.id_comp _
  have hkey : (structureSheafHomIso X (singleSheafComplex X ℱ)).inv.f 0 ≫
      (homMap X (koszulCechComplexMap X f n ≫ cechAugmentation X f)
        (𝟙 (singleSheafComplex X ℱ))).f 0 ≫
      ((homDegreeIsoSingle X (koszulPowerComplex X f n)
          ℱ 0).hom ≫
        koszulDualFactor X f ℱ n (-0)
          (Idx.compl (show ((0 : ℤ) + (r : ℤ)) + (-0 : ℤ) = (r : ℤ) by ring) S) ≫
        (unitHomSheafIso X ℱ).hom) =
      𝟙 ℱ := by
    rw [← Category.assoc ((homMap X (koszulCechComplexMap X f n ≫ cechAugmentation X f)
        (𝟙 (singleSheafComplex X ℱ))).f 0),
      homDegreeIsoSingle_homMap, Category.assoc]
    show (structureSheafHomIso X (singleSheafComplex X ℱ)).inv.f 0 ≫
      (homDegreeIsoSingle X (structureSheafComplex X)
          ℱ 0).hom ≫
        internalHomPre X ((koszulCechComplexMap X f n ≫ cechAugmentation X f).f (-0)) ≫
          internalHomPre X (termι (koszulPowerFunctor X f n)
            (Idx.compl (show ((0 : ℤ) + (r : ℤ)) + (-0 : ℤ) = (r : ℤ) by ring) S)) ≫
          (unitHomSheafIso X ℱ).hom = _
    have hihp : internalHomPre X ((koszulCechComplexMap X f n ≫ cechAugmentation X f).f (-0)) ≫
        koszulDualFactor X f ℱ n (-0)
          (Idx.compl (show ((0 : ℤ) + (r : ℤ)) + (-0 : ℤ) = (r : ℤ) by ring) S) =
        internalHomPre X (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv :=
      (internalHomPre_comp X (termι (koszulPowerFunctor X f n)
          (Idx.compl (show ((0 : ℤ) + (r : ℤ)) + (-0 : ℤ) = (r : ℤ) by ring) S))
          ((koszulCechComplexMap X f n ≫ cechAugmentation X f).f (-0))).trans
        (congrArg (fun w => internalHomPre X w) haug)
    refine Eq.trans ?_ hA
    refine whisker_eq _ ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker hihp _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (homDegreeIsoSingle_comp_internalHomPre_unit X ℱ) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (Iso.inv_hom_id _)) ?_
    exact Category.comp_id _
  have hC : (koszulDualComplexIsoCoeff X f ℱ n).hom.f 0 ≫
      Pi.π (fun T : Idx r ((0 : ℤ) + (r : ℤ)) =>
        (koszulPowerFunctorOn X f ℱ n).obj T.1) S =
      dualSign S.1 • ((homDegreeIsoSingle X (koszulPowerComplex X f n)
          ℱ 0).hom ≫
        koszulDualFactor X f ℱ n (-0)
          (Idx.compl (show ((0 : ℤ) + (r : ℤ)) + (-0 : ℤ) = (r : ℤ) by ring) S) ≫
        (unitHomSheafIso X ℱ).hom) := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (AlternatingCech.mapX_comp_pi
      (koszulPowerFunctorOnMapIso X f n (unitHomSheafIso X
        ℱ)).hom S)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (Category.assoc _ _ _) _) ?_
    refine Eq.trans (eq_whisker (whisker_eq _ (koszulDualIsoAt_hom_π X f
      ℱ n (-0) ((0 : ℤ) + (r : ℤ)) (by omega) S)) _) ?_
    refine Eq.trans (eq_whisker (Preadditive.comp_zsmul _ _ _) _) ?_
    refine Eq.trans (Preadditive.zsmul_comp _ _ _) ?_
    exact congrArg (fun w => dualSign S.1 • w) (Category.assoc _ _ _)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ hC)) ?_
  refine Eq.trans (whisker_eq _ (Preadditive.comp_zsmul _ _ _)) ?_
  refine Eq.trans (Preadditive.comp_zsmul _ _ _) ?_
  refine Eq.trans (congrArg (fun w => dualSign S.1 • w) hkey) ?_
  rw [hS, dualSign_univ]
  rfl

/-- **The dual of the Koszul augmentation with coefficients in `ℱ`, as a morphism of
complexes.** The trivialisation of `SheafHom•(𝒪[0], ℱ[0])`, the dual of the morphism of complexes
`K^n ⟶ Č(f) ⟶ 𝒪[0]`, the self-duality of the Koszul complex and the comparison across the shift
by `r` compose to `(-1)^r` times the canonical map `ℱ ⟶ H^r(K^n ⊗ ℱ)` onto the top Koszul
cohomology sheaf, placed in degree zero. -/
theorem structureSheafHomIso_inv_comp_homMap_comp_koszulDualComplexIsoCoeff_comp (n : ℕ) :
    (structureSheafHomIso X (singleSheafComplex X ℱ)).inv ≫
        homMap X (koszulCechComplexMap X f n ≫ cechAugmentation X f)
          (𝟙 (singleSheafComplex X ℱ)) ≫
        (koszulDualComplexIsoCoeff X f ℱ n).hom ≫
        koszulShiftedToTopSingleComplexMap X f ℱ n =
      (CochainComplex.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
        ((-1 : ℤ) ^ r • koszulToTopHomologyAt X f ℱ (r : ℤ) koszulTopDeg_eq n) := by
  refine HomologicalComplex.from_single_hom_ext ?_
  show (structureSheafHomIso X (singleSheafComplex X ℱ)).inv.f 0 ≫
      (homMap X (koszulCechComplexMap X f n ≫ cechAugmentation X f)
        (𝟙 (singleSheafComplex X ℱ))).f 0 ≫
      (koszulDualComplexIsoCoeff X f ℱ n).hom.f 0 ≫
      (koszulShiftedToTopSingleComplexMap X f ℱ n).f 0 =
    (-1 : ℤ) ^ r • koszulToTopHomologyAt X f ℱ (r : ℤ) koszulTopDeg_eq n
  refine Eq.trans ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).symm ?_
  refine Eq.trans (eq_whisker
    (structureSheafHomIso_inv_comp_homMap_comp_koszulDualComplexIsoCoeff_f_zero X f ℱ n) _) ?_
  refine Eq.trans (Preadditive.zsmul_comp _ _ _) ?_
  refine Eq.trans (congrArg (fun w => (-1 : ℤ) ^ r • w) (Category.assoc _ _ _)) ?_
  exact congrArg (fun w => (-1 : ℤ) ^ r • w)
    (koszulTopTermInj_comp_koszulShiftedToTopSingleComplexMap_f_zero X f ℱ n)

/-- The chain-level identity, pushed through `DerivedCategory.Q`. -/
private theorem Q_map_structureSheafHomIso_inv_comp_homMap_comp_eq
    [HasDerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    DerivedCategory.Q.map ((structureSheafHomIso X (singleSheafComplex X ℱ)).inv ≫
        homMap X (koszulCechComplexMap X f n ≫ cechAugmentation X f)
          (𝟙 (singleSheafComplex X ℱ))) ≫
      DerivedCategory.Q.map (koszulDualComplexIsoCoeff X f ℱ n).hom ≫
        DerivedCategory.Q.map (koszulShiftedToTopSingleComplexMap X f ℱ n) =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
        ((-1 : ℤ) ^ r • koszulToTopHomologyAt X f ℱ (r : ℤ) koszulTopDeg_eq n) := by
  refine Eq.trans (whisker_eq _ (DerivedCategory.Q.map_comp _ _).symm) ?_
  refine Eq.trans (DerivedCategory.Q.map_comp _ _).symm ?_
  exact congrArg DerivedCategory.Q.map
    (structureSheafHomIso_inv_comp_homMap_comp_koszulDualComplexIsoCoeff_comp X f ℱ n)

end DegreeZero

section DerivedChain

open CategoryTheory.AlternatingCech

attribute [local instance 100000] HasDerivedCategory.standard
/- `Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian` is a second, definitionally
equal but syntactically different, `Abelian` instance on these sheaves of modules; letting it
into the derived categories of this section makes the kernel unfold both to compare them. -/
attribute [-instance] Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

open scoped IsMulCommutative

attribute [local instance]
  hasFiniteBiproducts_sheafOfModules hasSheafCompose_forget₂_ringCat

/-- **The coefficient-free identity of part (1) of [Stacks, Tag 0A0K].** The trivialisation of
`R𝑆heafHom_𝒪(𝒪[0], 𝒪[0])`, the dual of the morphism `K^n ⟶ Č(f) ⟶ 𝒪[0]` of complexes, and the
named comparison of the coefficient-free dual Koszul tower with the tower `n ↦ 𝒪/ℐⁿ⁺¹` compose
to the projection `𝒪 ⟶ 𝒪/ℐⁿ⁺¹` placed in degree zero.

This is the hypothesis `hψ` of
`AlgebraicGeometry.RingedSite.eq_adicQuotientReduction_of_dual_comp_eq`. Three cancellations take
it to the chain-level identity
`structureSheafHomIso_inv_comp_homMap_comp_koszulDualComplexIsoCoeff_comp`:
the comparison of [Stacks, Tag 08JH] against the one inside the tower comparison, by
`koszulDerivedSheafHomSystemComparison_app_comp_koszulTensorDualSystemIso_inv_app`;
the shift commutation of `DerivedCategory.Q`, by
`AlgebraicGeometry.RingedSite.koszulShiftedDualToTopSingle_app`; and the sign `(-1)^r` of the
Koszul self-duality against the twist in
`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientSigned`. -/
theorem derivedStructureSheafHomIso_inv_comp_map_comp_derivedSheafHomToAdicQuotientTower
    (n : ℕ) :
    (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv ≫
        ((derivedSheafHomBifunctor X).map
            (DerivedCategory.Q.map
              (koszulCechComplexMap X f n ≫ cechAugmentation X f)).op).app
          (derivedStructureSheaf X) ≫
        (derivedSheafHomToAdicQuotientTower X f).app (op n) =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
        (Stacks.Sites.adicQuotientModuleπ (X := X) (generatedIdealSheaf f) (n + 1)) := by
  have h1 := derivedStructureSheafHomIso_inv_comp_map_eq_Q_map_comp X
    (koszulPowerComplex X f n) (structureSheafComplex X)
    (koszulCechComplexMap X f n ≫ cechAugmentation X f)
  have hshift := koszulShiftedDualToTopSingle_app X f
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n
  have hmid : strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
        (koszulPowerComplex X f n) (structureSheafComplex X) ≫
        (derivedSheafHomToAdicQuotientTower X f).app (op n) =
      DerivedCategory.Q.map (koszulDualComplexIsoCoeff X f
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).hom ≫
        ((koszulShiftedDualToTopSingle X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).app (op n) ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
            ((koszulTopHomologyToAdicQuotientSigned X f (r : ℤ) koszulTopDeg_eq).app (op n))) :=
    ((whisker_eq _ (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm).trans
      (eq_whisker (koszulDerivedSheafHomSystemComparison_app_comp_koszulTensorDualSystemIso_inv_app
        X f (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n) _)
  have hQ := Q_map_structureSheafHomIso_inv_comp_homMap_comp_eq X f
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n
  have hπ := zsmul_koszulToTopHomologyAt_comp_koszulTopHomologyToAdicQuotientSigned X f
    (r : ℤ) koszulTopDeg_eq n
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker h1 _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ hmid) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (eq_whisker hshift _))) ?_
  refine Eq.trans ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).symm ?_
  refine Eq.trans (eq_whisker hQ _) ?_
  refine Eq.trans ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map_comp
    _ _).symm ?_
  exact congrArg (DerivedCategory.singleFunctor
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map hπ

attribute [local instance] isRightAdjoint_ι_isDerivedComplete_generatedIdealSheaf

/-- **The `n`-th canonical factorization is the `n`-th projection of the Koszul presentation.**
Through the identification `AlgebraicGeometry.RingedSite.reflectorIsoCompletionFunctor` of the
reflector with the Čech completion, the canonical factorization of [Stacks, Tag 0CQH] at level
`n + 1` is the `n`-th projection of the presentation of [Stacks, Tag 0A0E], followed by the
comparison of the dual Koszul tower with the adic quotient tower. Both restrict along the
completion map to the derived reduction, and a map into a derived-complete object is determined
by that restriction (`AlgebraicGeometry.RingedSite.derivedCompletion_hom_ext`). -/
theorem reflectorIsoCompletionFunctor_inv_comp_derivedCompletionAdicFactor
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℕ) :
    (reflectorIsoCompletionFunctor X f K).inv ≫
        derivedCompletionAdicFactor X (generatedIdealSheaf f) K (n + 1) =
      (((derivedSheafHomBifunctor X).flip.obj K).map
            (DerivedCategory.Q.map (koszulCechComplexMap X f n)).op ≫
          (koszulTensorDualSystemIso X f K).inv.app (op n)) ≫
        (Functor.whiskerRight (derivedSheafHomToAdicQuotientTower X f)
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).tensor.obj K)).app ⟨n⟩ := by
  refine (Iso.inv_comp_eq _).2 ?_
  refine derivedCompletion_hom_ext X (generatedIdealSheaf f)
    (isDerivedComplete_derivedTensor_adicQuotient X (generatedIdealSheaf f) K (n + 1)) ?_
  refine Eq.trans (derivedCompletionUnit_comp_derivedCompletionAdicFactor X
    (generatedIdealSheaf f) K (n + 1)) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_
    (eq_whisker (derivedCompletionUnit_comp_reflectorToCompletionFunctor X f K).symm _)
  symm
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (completionUnit_app_comp_tensorDerivedDualSystem_π X f K n) _) ?_
  exact eq_adicQuotientReduction_of_dual_comp_eq X (generatedIdealSheaf f) f K n (n + 1)
    (DerivedCategory.Q.map (koszulCechComplexMap X f n ≫ cechAugmentation X f))
    ((derivedSheafHomToAdicQuotientTower X f).app (op n))
    (derivedStructureSheafHomIso_inv_comp_map_comp_derivedSheafHomToAdicQuotientTower X f n)

/-- **Part (1) of [Stacks, Tag 0A0K] over the adic quotient tower, with its projections named.**
The Čech completion `K^∧` of an **arbitrary** object `K` of `D(𝒪)` is a derived limit of the
tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` through the canonical factorizations
`AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor` of [Stacks, Tag 0CQH], read across the
identification `AlgebraicGeometry.RingedSite.reflectorIsoCompletionFunctor` of the reflector of
[Stacks, Tag 099F] with the Čech completion.

This is
`AlgebraicGeometry.RingedSite.exists_isDerivedLimitWithProjections_adicReductionTower_completion`
with the existential over the projections eliminated. The projections that
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses` produces are
pinned by `AlgebraicGeometry.RingedSite.derivedCompletion_hom_ext`: both they and the canonical
factorizations restrict along the completion map to the derived reduction of [Stacks, Tag 0CQH],
which is the content of the coefficient-free identity. The pro-vanishing hypothesis `hpz` is the
only hypothesis, exactly as in the existential form. -/
theorem isDerivedLimitWithProjections_adicReductionTower_completion
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    [HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦ (tensorDerivedDualSystem X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦ (adicReductionTower X (generatedIdealSheaf f) K).obj (op n)]
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap
        ((koszulDualSystemOn X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map
          (homOfLE ‹n ≤ m›).op) p = 0) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicReductionTower X (generatedIdealSheaf f) K)
      ((completionFunctor X f).obj K)
      (fun n : ℕ => (reflectorIsoCompletionFunctor X f K).inv ≫
        derivedCompletionAdicFactor X (generatedIdealSheaf f) K (n + 1)) := by
  have hlim := NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses
    (Functor.whiskerRight (derivedSheafHomToAdicQuotientTower X f)
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).tensor.obj K))
    ((hasEventualInverses_derivedSheafHomToAdicQuotientTower X f hpz).whiskerRight _)
    (isDerivedLimitWithProjections_tensorDerivedDualSystem_koszulPowerSystem_completion X f K)
  have hfam : (fun n : ℕ => (reflectorIsoCompletionFunctor X f K).inv ≫
        derivedCompletionAdicFactor X (generatedIdealSheaf f) K (n + 1)) =
      fun n : ℕ => (((derivedSheafHomBifunctor X).flip.obj K).map
            (DerivedCategory.Q.map (koszulCechComplexMap X f n)).op ≫
          (koszulTensorDualSystemIso X f K).inv.app (op n)) ≫
        (Functor.whiskerRight (derivedSheafHomToAdicQuotientTower X f)
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).tensor.obj K)).app ⟨n⟩ :=
    funext fun n => reflectorIsoCompletionFunctor_inv_comp_derivedCompletionAdicFactor X f K n
  exact hfam ▸ hlim

/-- **The cone of the pinned Koszul presentation of `ℱ^∧` over the tower of top Koszul cohomology
sheaves, computed.** The completion unit `ℱ[0] ⟶ ℱ^∧` followed by the `n`-th projection of
`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion` is
`(-1)^r` times the canonical map `ℱ ⟶ H^r(K(𝒪, f_1^{n+1}, …, f_r^{n+1}) ⊗ ℱ)`, placed in degree
zero — that is, `(-1)^r` times the quotient map `ℱ ⟶ ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`.

This is the coefficient-ful counterpart of
`derivedStructureSheafHomIso_inv_comp_map_comp_derivedSheafHomToAdicQuotientTower`, which is the
same computation at `ℱ = 𝒪` and is what part (1) of [Stacks, Tag 0A0K] consumes. Part (3) cannot
use that one: its tower is `n ↦ ℱ/𝓘ⁿℱ` rather than `n ↦ ℱ ⊗^𝐋_𝒪 𝒪/𝓘ⁿ`, so the coefficient stays
inside the Koszul complex instead of entering through the functor `ℱ ⊗^𝐋_𝒪 -`, and the cone has
to be computed with it there.

Four steps compose, and none of them is new mathematics — each is the coefficient-ful reading of
a step the coefficient-free computation already took. The cone of the pinned presentation of
[Stacks, Tag 0A0E] along the unit is
`AlgebraicGeometry.RingedSite.completionUnit_app_comp_koszulTopSingleProjection`; the comparison
of [Stacks, Tag 08JH] out of `𝒪[0]` cancels by
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_inv_comp_map_eq_Q_map_comp`; the
identification of [Stacks, Tag 0A0E]'s tower with the dual Koszul tower cancels against its own
inverse by
`koszulDerivedSheafHomSystemComparison_app_comp_koszulTensorDualSystemIso_inv_app`;
and the shift commutation of `DerivedCategory.Q` cancels by
`AlgebraicGeometry.RingedSite.koszulShiftedDualToTopSingle_app`. What is left is the chain-level
identity `structureSheafHomIso_inv_comp_homMap_comp_koszulDualComplexIsoCoeff_comp`, whose
degree-zero component carries the sign.

A map out of `ℱ^∧` into a derived-complete object is determined by its restriction along the
unit, so this identity *pins* the projections of that presentation. What it does **not** yet give
is part (3) of [Stacks, Tag 0A0K]: the tower here is the Koszul top-cohomology tower
`n ↦ ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`, and turning it into the adic quotient tower `n ↦ ℱ/𝓘ⁿℱ`
needs the pigeonhole comparison of the two at ringed-site level with coefficients. That
comparison is
`exists_hasEventualInverses_koszulTopHomologySystem_adicQuotientTowerOn`,
over the tower `Stacks.Sites.adicQuotientTowerOn`. That comparison, composed with the interleaving
`Stacks.Sites.adicQuotientTowerOnOffset` onto `n ↦ ℱ/𝓘ⁿℱ` and twisted so that the sign above
cancels, is `AlgebraicGeometry.RingedSite.koszulTopHomologyToIdealSmulQuotientTower` of
`KoszulAdicQuotientTowerOffset.lean`, and the identity above carried along it is
`AlgebraicGeometry.RingedSite.completionUnit_app_comp_koszulTopSingleProjection_comp_map_eq`
there; part (3) at the tag's own hypotheses is
`Stacks.Algebraization.isIso_comparisonDerivedCompletionLimitAdicQuotient` of
`Completion/AdicQuotientSliceTowerKoszul.lean`. -/
theorem completionUnit_app_comp_koszulTopSingleProjection_eq
    (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    (completionUnit X f).app (DerivedCategory.Q.obj (singleSheafComplex X ℱ)) ≫
        koszulTopSingleProjection X f ℱ n =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
        ((-1 : ℤ) ^ r • koszulToTopHomologyAt X f ℱ (r : ℤ) koszulTopDeg_eq n) := by
  have h1 := derivedStructureSheafHomIso_inv_comp_map_eq_Q_map_comp X
    (koszulPowerComplex X f n) (singleSheafComplex X ℱ)
    (koszulCechComplexMap X f n ≫ cechAugmentation X f)
  have hshift := koszulShiftedDualToTopSingle_app X f ℱ n
  have hmid : strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
        (koszulPowerComplex X f n) (singleSheafComplex X ℱ) ≫
        ((koszulTensorDualSystemIso X f
            (DerivedCategory.Q.obj (singleSheafComplex X ℱ))).inv.app (op n) ≫
          (koszulTensorDualSystemCoefficientIso X f ℱ).hom.app (op n)) =
      DerivedCategory.Q.map (koszulDualComplexIsoCoeff X f ℱ n).hom :=
    koszulDerivedSheafHomSystemComparison_app_comp_koszulTensorDualSystemIso_inv_app X f ℱ n
  have hQ := Q_map_structureSheafHomIso_inv_comp_homMap_comp_eq X f ℱ n
  refine Eq.trans (completionUnit_app_comp_koszulTopSingleProjection X f ℱ n) ?_
  refine Eq.trans ?_ hQ
  refine Eq.trans (eq_whisker (Category.assoc _ _ _).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (eq_whisker h1 _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hmid _) ?_
  exact whisker_eq _ hshift

end DerivedChain

end AlgebraicGeometry.RingedSite

end
