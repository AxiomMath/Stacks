module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedDirectSums
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupExceptionalTwistDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections.DualBasisOne
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaFree
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPushforwardOpenBase
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Locality
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineUnitCoherence
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohCoproducts

/-!
# A criterion for `ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪_L(D))` to be an isomorphism

Let `b : L ⟶ X` be a quasi-compact and quasi-separated morphism of schemes with `X` affine, and
let `D ⊆ L` be an effective Cartier divisor, with invertible sheaf `𝒪_L(D)` and canonical section
`1_D`.  For an `𝒪_X`-module `ℰ` there is a canonical map

`ℰ ⟶ Rb_*(b^*ℰ ⊗_{𝒪_L} 𝒪_L(D))`

in `D(𝒪_X)`: the unit `ℰ ⟶ Rb_*b^*ℰ` of `b^* ⊣ b_*`, read in the derived category, followed by
`Rb_*` of multiplication by `1_D`, which is the inclusion `b^*ℰ ⟶ b^*ℰ ⊗ 𝒪_L(D)`.  This file
proves that the map is an isomorphism for every locally free `ℰ`, of arbitrary rank, as soon as

* `𝒪_X ⟶ b_*𝒪_L(D)`, the adjoint of the canonical section, is an isomorphism, and
* `H^q(L, 𝒪_L(D)) = 0` for every `q > 0`.

This is the shape of the argument of [Stacks, Tag 0G5H], with the geometry of the blowup
removed: there `b` is a blowing up, `D = iE` is a multiple of its exceptional divisor, and the
two hypotheses are what the source checks by computation on the blowup.

## Main definitions

* `Stacks.DeRham.TwistDerived.derivedPullbackUnit`: the unit `ℰ ⟶ Rb_*b^*ℰ` in `D(𝒪_X)`.
* `Stacks.DeRham.TwistDerived.twistDerivedMap`: the canonical map
  `ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪_L(D))` above, as `derivedPullbackUnit` followed by `Rb_*` of the
  inclusion.
* `Stacks.DeRham.TwistDerived.twistUnderivedMap`: its underived form `ℰ ⟶ b_*(b^*ℰ ⊗ 𝒪_L(D))`.

## Main results

* `Stacks.DeRham.TwistDerived.twistDerivedMap_eq`: the derived map is the underived map
  followed by the comparison `b_*G ⟶ Rb_*G` at `G = b^*ℰ ⊗ 𝒪_L(D)`.
* `Stacks.DeRham.TwistDerived.isZero_higherDirectImage_twist`: `R^q b_*𝒪_L(D) = 0` for `q > 0`,
  by [Stacks, Tag 01XK] and quasi-coherence of the higher direct images.
* `Stacks.DeRham.TwistDerived.isIso_twistDerivedMap_of_isFiniteLocallyFree`: the criterion
  for a finite locally free `ℰ`, by the projection formula.
* `Stacks.DeRham.TwistDerived.isIso_twistDerivedMap_free`: the criterion for a free `ℰ` of
  arbitrary rank, by commuting both sides with direct sums.
* `Stacks.DeRham.TwistDerived.isIso_twistDerivedMap`: **the criterion for a locally free `ℰ` of
  arbitrary rank.**
* `Stacks.DeRham.TwistDerived.isIso_twistUnitComparison_of_bijective`: the first hypothesis
  follows from bijectivity of `a ↦ b^♯(a) • 1_D` on global sections; with it,
  `isIso_twistDerivedMap_of_isLocallyFree_of_bijective` and `isIso_twistDerivedMap_of_bijective`
  state the criterion with that hypothesis instead.

## The argument

Write `T = 𝒪_L(D)` and `G = b^*ℰ ⊗ T`.  By naturality of the comparison `b_*(-) ⟶ Rb_*(-)`
the derived map factors as the underived map `ℰ ⟶ b_*G` placed in degree zero, followed by the
comparison at `G`.

* *Degree zero.*  Up to the symmetry of the tensor product, the underived map is the map
  `Stacks.DeRham.BlowupTwist.twistComparison` of
  `StacksFrontier/AlgebraicGeometry/DeRham/BlowupExceptionalTwistDirectImage.lean`, which is an
  isomorphism at a finite locally free `ℰ` once the map at `𝒪_X` is, by the projection formula of
  [Stacks, Tag 01E8] in degree zero.  The identification uses that multiplication by `1_D`,
  followed by the symmetry, is the left unitor followed by `1_D ⊗ id`
  (`tensorCanonicalSection_comp_commIso`).
* *Higher degrees.*  `R^q b_*T` is quasi-coherent ([Stacks, Tag 01XJ]) with global sections
  `H^q(L, T) = 0` over the affine `X` ([Stacks, Tag 01XK]), so it vanishes; by the projection
  formula of [Stacks, Tag 01E8] in degree `q`, `R^q b_*(T ⊗ b^*ℰ) ≅ R^q b_*T ⊗ ℰ = 0`.  So `G`
  is right acyclic for `b_*`, and as it is quasi-coherent, the comparison `b_*G ⟶ Rb_*G` is an
  isomorphism by [Stacks, Tag 0G9N].
* *Arbitrary rank.*  At a free `ℰ = 𝒪_X^{(I)}` the degree-zero map is an isomorphism because
  both of its sides commute with direct sums, `b_*` because `b` is quasi-compact; and
  `R^q b_*G` vanishes because by [Stacks, Tag 01XK] it is the cohomology `H^q(L, G)`, which is a
  direct sum of copies of `H^q(L, T) = 0` on the quasi-compact quasi-separated `L`.  For a
  locally free `ℰ` invertibility is checked on the members of an open cover of `X` on which `ℰ`
  is free (`isIso_of_isIso_mapDerivedCategory_pullback`), and there it is transported from the
  free case along restriction units, using that the derived map is natural in `ℰ` and that
  `Rb_*` commutes with restriction to an open of `X` ([Stacks, Tag 08FE]).

## Implementation notes

`HasDerivedCategory.standard` is installed with raised priority, as in
`StacksFrontier/AlgebraicGeometry/DeRham/BlowupFormsDerivedRetraction.lean`, so that the derived
categories here are those of `Stacks.DeRham.formsDerivedDirectImage` and of [Stacks, Tag 0G9N].
The higher-degree projection formula of
`StacksFrontier/AlgebraicGeometry/ProjectionFormula/HigherDirectImageFiniteLocallyFree.lean` is
elaborated against the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`
instead; the vanishing it carries is moved between the two models through Mathlib's
`ℕ`-indexed right derived functors, which see no derived category at all
(`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`).

The first hypothesis is stated as invertibility of
`Stacks.DeRham.BlowupTwist.twistUnitComparison`, the adjoint transpose `𝒪_X ⟶ b_*𝒪_L(D)` of the
canonical section, which is the hypothesis `hunit` of the base file.

## References

* [Stacks Project, Tag 0G5H](https://stacks.math.columbia.edu/tag/0G5H)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.DeRham.TwistDerived

variable {L X : Scheme.{u}} (b : L ⟶ X)

/-- **The unit `ℰ ⟶ Rb_*b^*ℰ` in `D(𝒪_X)`**: the unit of `b^* ⊣ b_*` at `ℰ`, placed in degree
zero, followed by the comparison `b_*(-) ⟶ Rb_*(-)` of the right-derived-functor structure of
`AlgebraicGeometry.schemeDerivedPushforward`. -/
def derivedPullbackUnit (E : X.Modules) :
    (DerivedCategory.singleFunctor X.Modules 0).obj E ⟶
      (schemeDerivedPushforward b).obj
        ((DerivedCategory.singleFunctor L.Modules 0).obj ((Scheme.Modules.pullback b).obj E)) :=
  (DerivedCategory.singleFunctor X.Modules 0).map
      ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app E) ≫
    pushforwardSingleToDerived b _

variable (D : L.IdealSheafData)

/-- **The canonical map `ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪_L(D))` in `D(𝒪_X)`**: the unit `ℰ ⟶ Rb_*b^*ℰ`
followed by `Rb_*` of the inclusion `b^*ℰ ⟶ b^*ℰ ⊗ 𝒪_L(D)`, multiplication by the canonical
section of `𝒪_L(D)`. -/
def twistDerivedMap (E : X.Modules) :
    (DerivedCategory.singleFunctor X.Modules 0).obj E ⟶
      (schemeDerivedPushforward b).obj
        ((DerivedCategory.singleFunctor L.Modules 0).obj
          (Scheme.Modules.tensorObj ((Scheme.Modules.pullback b).obj E)
            (Stacks.Divisors.invertibleSheaf' D))) :=
  derivedPullbackUnit b E ≫ (schemeDerivedPushforward b).map
    ((DerivedCategory.singleFunctor L.Modules 0).map
      (Stacks.Divisors.tensorCanonicalSection D ((Scheme.Modules.pullback b).obj E)))

/-- **The comparison `b_*N ⟶ Rb_*N` is natural in `N`.** -/
theorem pushforwardSingleToDerived_naturality {N N' : L.Modules} (g : N ⟶ N') :
    (DerivedCategory.singleFunctor X.Modules 0).map ((Scheme.Modules.pushforward b).map g) ≫
        pushforwardSingleToDerived b N' =
      pushforwardSingleToDerived b N ≫
        (schemeDerivedPushforward b).map ((DerivedCategory.singleFunctor L.Modules 0).map g) := by
  have h1 := (DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.naturality
    ((Scheme.Modules.pushforward b).map g)
  have h2 := ((Scheme.Modules.pushforward b).mapHomotopyCategorySingleFunctor 0).inv.naturality g
  have h3 := (schemeDerivedPushforwardUnit b).naturality
    ((HomotopyCategory.singleFunctor L.Modules 0).map g)
  have h4 := (DerivedCategory.singleFunctorIsoCompQh L.Modules 0).inv.naturality g
  simp only [Functor.comp_map] at h1 h2 h3 h4
  simp only [pushforwardSingleToDerived, Category.assoc]
  rw [reassoc_of% h1, ← Functor.map_comp_assoc, h2, Functor.map_comp_assoc, reassoc_of% h3,
    ← Functor.map_comp, ← Functor.map_comp, h4]

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **Multiplication by the canonical section, followed by the symmetry, is the left unitor
followed by `1_D ⊗ id`**: `F ⟶ F ⊗ 𝒪_L(D) ⟶ 𝒪_L(D) ⊗ F` is `F ⟶ 𝒪_L ⊗ F ⟶ 𝒪_L(D) ⊗ F`.  This
is naturality of the symmetry in the second variable, together with the symmetry carrying the
left unitor to the right unitor. -/
theorem tensorCanonicalSection_comp_commIso (F : L.Modules) :
    Stacks.Divisors.tensorCanonicalSection D F ≫
        (tensorSheafSchemeCommIso L F (Stacks.Divisors.invertibleSheaf' D)).hom =
      (Stacks.RingedSpace.tensorSheafUnitLeftIso L.toRingedSpace F).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          L.toRingedSpace.sheaf)).map
          ((Stacks.Divisors.canonicalSectionHom D ×ₘ 𝟙 F :
            ((SheafOfModules.unit (Stacks.RingedSpace.structureRingSheaf L.toRingedSpace), F) :
              _ × _) ⟶ (Stacks.Divisors.invertibleSheaf' D, F))) := by
  have hnat := tensorSheafSchemeCommIso_naturality L F (Stacks.Divisors.canonicalSectionHom D)
  have hunit := tensorSheafSchemeCommIso_hom_comp_tensorSheafUnitLeftIso L F
  have h2 : (Scheme.Modules.tensorRightUnitor F).inv ≫
      (tensorSheafSchemeCommIso L F L.unitModule).hom =
        (Stacks.RingedSpace.tensorSheafUnitLeftIso L.toRingedSpace F).inv :=
    (Iso.inv_comp_eq _).2 ((Iso.eq_comp_inv _).2 hunit)
  have htl : Scheme.Modules.tensorLeftMap F (Stacks.Divisors.canonicalSectionHom D) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨L.toRingedSpace.presheaf, L.toRingedSpace.IsSheaf⟩)).map
        ((𝟙 F ×ₘ Stacks.Divisors.canonicalSectionHom D :
          ((F, SheafOfModules.unit L.ringCatSheaf) : _ × _) ⟶
            (F, Stacks.Divisors.invertibleSheaf' D))) := by
    have e := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨L.toRingedSpace.presheaf, L.toRingedSpace.IsSheaf⟩).map_id F
    refine (Category.id_comp _).symm.trans ?_
    exact congrArg (fun φ => NatTrans.app φ (SheafOfModules.unit L.ringCatSheaf) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨L.toRingedSpace.presheaf, L.toRingedSpace.IsSheaf⟩).obj F).map
          (Stacks.Divisors.canonicalSectionHom D)) e.symm
  have hnat' : Scheme.Modules.tensorLeftMap F (Stacks.Divisors.canonicalSectionHom D) ≫
      (tensorSheafSchemeCommIso L F (Stacks.Divisors.invertibleSheaf' D)).hom =
        (tensorSheafSchemeCommIso L F (SheafOfModules.unit L.ringCatSheaf)).hom ≫
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨L.toRingedSpace.presheaf, L.toRingedSpace.IsSheaf⟩)).map
            ((Stacks.Divisors.canonicalSectionHom D ×ₘ 𝟙 F :
              ((SheafOfModules.unit L.ringCatSheaf, F) : _ × _) ⟶
                (Stacks.Divisors.invertibleSheaf' D, F))) := by
    rw [htl]; exact hnat
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hnat').trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h2)))

/-- **The underived map `ℰ ⟶ b_*(b^*ℰ ⊗ 𝒪_L(D))`**: the unit of `b^* ⊣ b_*` at `ℰ`, followed by
`b_*` of multiplication by the canonical section of `𝒪_L(D)`. -/
def twistUnderivedMap (E : X.Modules) :
    E ⟶ (Scheme.Modules.pushforward b).obj
      (Scheme.Modules.tensorObj ((Scheme.Modules.pullback b).obj E)
        (Stacks.Divisors.invertibleSheaf' D)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app E ≫
    (Scheme.Modules.pushforward b).map
      (Stacks.Divisors.tensorCanonicalSection D ((Scheme.Modules.pullback b).obj E))

/-- The symmetry `b^*ℰ ⊗ 𝒪_L(D) ≅ 𝒪_L(D) ⊗ b^*ℰ`, read as an isomorphism of `L.Modules`. -/
def pullbackTwistCommIso (E : X.Modules) :
    Scheme.Modules.tensorObj ((Scheme.Modules.pullback b).obj E)
        (Stacks.Divisors.invertibleSheaf' D) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        L.toRingedSpace.sheaf)).obj
        (Stacks.Divisors.invertibleSheaf' D, (Scheme.Modules.pullback b).obj E) :=
  Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorSheafSchemeCommIso L _ _

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **The underived map is `Stacks.DeRham.BlowupTwist.twistComparison` up to the symmetry of the
tensor product.** -/
theorem twistUnderivedMap_comp_commIso (E : X.Modules) :
    twistUnderivedMap b D E ≫ (Scheme.Modules.pushforward b).map
        (pullbackTwistCommIso b D E).hom =
      Stacks.DeRham.BlowupTwist.twistComparison b (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.canonicalSectionHom D) E := by
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans
    (congrArg (Scheme.Modules.pushforward b).map
      (tensorCanonicalSection_comp_commIso D ((Scheme.Modules.pullback b).obj E)))))

/-- **The underived map is an isomorphism at a finite locally free `ℰ`** as soon as the map
`𝒪_X ⟶ b_*𝒪_L(D)` is: this is `Stacks.DeRham.BlowupTwist.isIso_twistComparison`, the projection
formula of [Stacks, Tag 01E8] in degree zero. -/
theorem isIso_twistUnderivedMap (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hunit : IsIso (Stacks.DeRham.BlowupTwist.twistUnitComparison b
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D))) :
    IsIso (twistUnderivedMap b D E) := by
  have h := Stacks.DeRham.BlowupTwist.isIso_twistComparison b
    (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D) E
    (fun x => (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators E).mpr hE x) hunit
  rw [← twistUnderivedMap_comp_commIso] at h
  exact (isIso_comp_right_iff (twistUnderivedMap b D E)
    ((Scheme.Modules.pushforward b).mapIso (pullbackTwistCommIso b D E)).hom).mp h

/-- **The derived map is the underived map followed by the comparison `b_*G ⟶ Rb_*G`**, at
`G = b^*ℰ ⊗ 𝒪_L(D)`: naturality of the comparison. -/
theorem twistDerivedMap_eq (E : X.Modules) :
    twistDerivedMap b D E =
      (DerivedCategory.singleFunctor X.Modules 0).map (twistUnderivedMap b D E) ≫
        pushforwardSingleToDerived b _ := by
  rw [twistDerivedMap, derivedPullbackUnit, twistUnderivedMap, Functor.map_comp, Category.assoc,
    Category.assoc, pushforwardSingleToDerived_naturality]

/-- **The comparison `b_*G ⟶ Rb_*G` is an isomorphism at a quasi-coherent `G` right acyclic for
`b_*`**: [Stacks, Tag 0G9N] at the complex `G[0]`. -/
theorem isIso_pushforwardSingleToDerived [QuasiCompact b] [QuasiSeparated b] (G : L.Modules)
    [G.IsQuasicoherent] (hG : (Scheme.Modules.pushforward b).rightAcyclic G) :
    IsIso (pushforwardSingleToDerived b G) := by
  have hqc : ∀ n, (((CochainComplex.singleFunctor L.Modules 0).obj G).X n).IsQuasicoherent := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact (SheafOfModules.isQuasicoherent L.ringCatSheaf).prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm inferInstance
    · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
        (R := L.ringCatSheaf)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G n hn)
  have hac : ∀ n, (Scheme.Modules.pushforward b).rightAcyclic
      (((CochainComplex.singleFunctor L.Modules 0).obj G).X n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact (Scheme.Modules.pushforward b).rightAcyclic.prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm hG
    · have : Injective (((CochainComplex.singleFunctor L.Modules 0).obj G).X n) :=
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G n hn).injective
      exact Functor.rightAcyclic_of_injective (Scheme.Modules.pushforward b)
        (((CochainComplex.singleFunctor L.Modules 0).obj G).X n)
  have h := isIso_to_rightDerived_of_termwise_acyclic b
    ((CochainComplex.singleFunctor L.Modules 0).obj G) hqc hac (schemeDerivedPushforward b)
    (schemeDerivedPushforwardUnit b)
  rw [pushforwardSingleToDerived]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' h inferInstance))

/-- The sheaf `𝒪_L(D)` of an effective Cartier divisor is quasi-coherent, being invertible. -/
theorem isQuasicoherent_twist [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    (Stacks.Divisors.invertibleSheaf' D : L.Modules).IsQuasicoherent :=
  have := Stacks.Divisors.isTensorInvertible_invertibleSheaf D
  Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible L _

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **`R^q b_*𝒪_L(D) = 0` for `q > 0`** when `H^q(L, 𝒪_L(D)) = 0` for `q > 0` and `X` is
affine: the higher direct image is quasi-coherent ([Stacks, Tag 01XJ]) with global sections
`H^q(L, 𝒪_L(D))` ([Stacks, Tag 01XK]). -/
theorem isZero_higherDirectImage_twist [IsAffine X] [QuasiCompact b] [QuasiSeparated b]
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hq : ∀ q : ℕ, 0 < q → IsZero (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (i : ℤ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward b).rightDerivedPlus i).obj
      (Stacks.Divisors.invertibleSheaf' D)) := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = i := ⟨i.toNat, by omega⟩
  refine @isZero_rightDerivedPlus_pushforward_of_isZero_cohomology L X b _ _ _ (q : ℤ)
    (Stacks.Divisors.invertibleSheaf' D) (isQuasicoherent_twist D) ?_
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q _).1 (hq q (by omega))

/-- **`R^q b_*(b^*ℰ ⊗ 𝒪_L(D)) = 0` for `q > 0`** at a finite locally free `ℰ`: by the projection
formula of [Stacks, Tag 01E8] it is `R^q b_*𝒪_L(D) ⊗ ℰ`, and the first factor vanishes. -/
theorem isZero_higherDirectImage_pullbackTwist [IsAffine X] [QuasiCompact b] [QuasiSeparated b]
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hq : ∀ q : ℕ, 0 < q → IsZero (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (i : ℤ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward b).rightDerivedPlus i).obj
      (Scheme.Modules.tensorObj ((Scheme.Modules.pullback b).obj E)
        (Stacks.Divisors.invertibleSheaf' D))) := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = i := ⟨i.toNat, by omega⟩
  have hstd : IsZero (((Scheme.Modules.pushforward b).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)) :=
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q _).2
      (isZero_higherDirectImage_twist b D hq q hi)
  have hsm := (@Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ _ _ _ _ _ _
    (Scheme.Modules.pushforward b) _ (Scheme.Modules.hasDerivedCategory L)
    (Scheme.Modules.hasDerivedCategory X) q _).1 hstd
  have h₁ := (Functor.map_isZero (Stacks.ProjectionFormula.tensorRightInvertible X E) hsm).of_iso
    ((Stacks.ProjectionFormula.higherDirectImageTensorRightFiniteLocallyFreeIso b E q).app
      (Stacks.Divisors.invertibleSheaf' D))
  have h₂ := (@Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ _ _ _ _ _ _
    (Scheme.Modules.pushforward b) _ (Scheme.Modules.hasDerivedCategory L)
    (Scheme.Modules.hasDerivedCategory X) q _).2 h₁
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q _).1
    (h₂.of_iso (((Scheme.Modules.pushforward b).rightDerived q).mapIso
      (pullbackTwistCommIso b D E)))

/-- `b^*ℰ ⊗ 𝒪_L(D)` is quasi-coherent for a quasi-coherent `ℰ`. -/
theorem isQuasicoherent_pullbackTwist [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (E : X.Modules) [E.IsQuasicoherent] :
    (Scheme.Modules.tensorObj ((Scheme.Modules.pullback b).obj E)
      (Stacks.Divisors.invertibleSheaf' D)).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_tensorObj _ _
    (@AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _ b.toLRSHom.toShHom E
      ‹E.IsQuasicoherent›)
    (isQuasicoherent_twist D)

/-- **The derived map is an isomorphism** as soon as the underived map is and
`b^*ℰ ⊗ 𝒪_L(D)` is quasi-coherent with vanishing higher direct images. -/
private theorem isIso_twistDerivedMap_of_isIso_underived [QuasiCompact b] [QuasiSeparated b]
    (E : X.Modules) [(Scheme.Modules.tensorObj ((Scheme.Modules.pullback b).obj E)
      (Stacks.Divisors.invertibleSheaf' D)).IsQuasicoherent]
    (hu : IsIso (twistUnderivedMap b D E))
    (hz : ∀ i : ℤ, 0 < i → IsZero (((Scheme.Modules.pushforward b).rightDerivedPlus i).obj
      (Scheme.Modules.tensorObj ((Scheme.Modules.pullback b).obj E)
        (Stacks.Divisors.invertibleSheaf' D)))) :
    IsIso (twistDerivedMap b D E) := by
  have hac : (Scheme.Modules.pushforward b).rightAcyclic
      (Scheme.Modules.tensorObj ((Scheme.Modules.pullback b).obj E)
        (Stacks.Divisors.invertibleSheaf' D)) :=
    (((Scheme.Modules.pushforward b).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
      _).2 inferInstance).mpr hz
  have := isIso_pushforwardSingleToDerived b _ hac
  rw [twistDerivedMap_eq]
  infer_instance

/-- **The criterion for `ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪_L(D))` to be an isomorphism, for a finite locally
free `ℰ`.**  Let `b : L ⟶ X` be quasi-compact and quasi-separated with `X` affine and let `D` be an
effective Cartier divisor on `L`.  If `𝒪_X ⟶ b_*𝒪_L(D)` is an isomorphism (`h0`) and
`H^q(L, 𝒪_L(D)) = 0` for every `q > 0` (`hq`), then the canonical map
`ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪_L(D))` is an isomorphism in `D(𝒪_X)` for every finite locally free `ℰ`. -/
theorem isIso_twistDerivedMap_of_isFiniteLocallyFree [IsAffine X] [QuasiCompact b]
    [QuasiSeparated b] [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (h0 : IsIso (Stacks.DeRham.BlowupTwist.twistUnitComparison b
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D)))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsIso (twistDerivedMap b D E) := by
  have := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have := isQuasicoherent_pullbackTwist b D E
  exact isIso_twistDerivedMap_of_isIso_underived b D E (isIso_twistUnderivedMap b D E h0)
    fun i hi => isZero_higherDirectImage_pullbackTwist b D hq E i hi

/-! ### Arbitrary rank -/

/-- The functor `ℰ ↦ b^*ℰ ⊗_{𝒪_L} 𝒪_L(D)`. -/
abbrev pullbackTwistFunctor : X.Modules ⥤ L.Modules :=
  Scheme.Modules.pullback b ⋙
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨L.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ L.sheaf.obj (forget₂ CommRingCat RingCat)
        L.ringCatSheaf.property⟩).flip.obj (Stacks.Divisors.invertibleSheaf' D)

/-- **Multiplication by the canonical section is natural.** -/
theorem tensorCanonicalSection_naturality {M N : L.Modules} (g : M ⟶ N) :
    g ≫ Stacks.Divisors.tensorCanonicalSection D N =
      Stacks.Divisors.tensorCanonicalSection D M ≫
        Scheme.Modules.tensorRightMap g (Stacks.Divisors.invertibleSheaf' D) := by
  have hρ := Stacks.RingedSpace.tensorSheafUnitRightIso_naturality L.toRingedSpace g
  have hρ' : g ≫ (Scheme.Modules.tensorRightUnitor N).inv =
      (Scheme.Modules.tensorRightUnitor M).inv ≫
        Scheme.Modules.tensorRightMap g (SheafOfModules.unit L.ringCatSheaf) := by
    have e := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨L.toRingedSpace.presheaf, L.toRingedSpace.IsSheaf⟩).obj N).map_id
        (SheafOfModules.unit L.ringCatSheaf)
    have h1 : Scheme.Modules.tensorRightMap g (SheafOfModules.unit L.ringCatSheaf) ≫
        (Scheme.Modules.tensorRightUnitor N).hom = (Scheme.Modules.tensorRightUnitor M).hom ≫ g :=
      Eq.trans (congrArg (· ≫ (Scheme.Modules.tensorRightUnitor N).hom)
        ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) e.symm))) hρ
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact h1.symm
  rw [Stacks.Divisors.tensorCanonicalSection, Stacks.Divisors.tensorCanonicalSection,
    ← Category.assoc, hρ', Category.assoc,
    ← Stacks.Divisors.tensorLeftMap_canonicalSectionHom_comp_tensorRightMap, Category.assoc]

/-- **The underived map is natural in `ℰ`.** -/
theorem twistUnderivedMap_naturality {E E' : X.Modules} (k : E ⟶ E') :
    k ≫ twistUnderivedMap b D E' =
      twistUnderivedMap b D E ≫ (Scheme.Modules.pushforward b).map
        ((pullbackTwistFunctor b D).map k) := by
  have h1 := (Scheme.Modules.pullbackPushforwardAdjunction b).unit.naturality k
  have h2 := tensorCanonicalSection_naturality D ((Scheme.Modules.pullback b).map k)
  simp only [Functor.id_map, Functor.comp_map] at h1
  rw [twistUnderivedMap, twistUnderivedMap, reassoc_of% h1, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, h2]
  rfl

/-- **The derived map is natural in `ℰ`.** -/
theorem twistDerivedMap_naturality {E E' : X.Modules} (k : E ⟶ E') :
    (DerivedCategory.singleFunctor X.Modules 0).map k ≫ twistDerivedMap b D E' =
      twistDerivedMap b D E ≫ (schemeDerivedPushforward b).map
        ((DerivedCategory.singleFunctor L.Modules 0).map ((pullbackTwistFunctor b D).map k)) := by
  rw [twistDerivedMap_eq, twistDerivedMap_eq, ← Category.assoc, ← Functor.map_comp,
    twistUnderivedMap_naturality, Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) (pushforwardSingleToDerived_naturality b _)

/-- `ℰ ↦ b^*ℰ ⊗ 𝒪_L(D)` commutes with direct sums. -/
instance preservesColimitsOfShape_pullbackTwistFunctor (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (pullbackTwistFunctor b D) := by
  have h1 : PreservesColimitsOfShape (Discrete I) (Scheme.Modules.pullback b) := inferInstance
  have h2 : PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.sheaf).flip.obj
        (Stacks.Divisors.invertibleSheaf' D)) :=
    (Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesColimits
      (Opens.grothendieckTopology L) L.sheaf
      (Stacks.Divisors.invertibleSheaf' D)).preservesColimitsOfShape
  exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ h1 h2

open Stacks.Cohomology in
/-- **The underived map at a free module of arbitrary rank is an isomorphism** as soon as the
map `𝒪_X ⟶ b_*𝒪_L(D)` is, for a quasi-compact `b`: both sides commute with direct sums, the
direct image because `b` is quasi-compact. -/
theorem isIso_twistUnderivedMap_free [QuasiCompact b]
    (hunit : IsIso (Stacks.DeRham.BlowupTwist.twistUnitComparison b
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D)))
    (I : Type u) :
    IsIso (twistUnderivedMap b D (SheafOfModules.free (R := X.ringCatSheaf) I)) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.RelativeSpec.AlgebraSheaf.isFiniteLocallyFree_unitModule X
  have h1 : PreservesColimitsOfShape (Discrete I) (Scheme.Modules.pushforward b) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.preservesColimitsOfShape_modulePushforward b I
  have h2 : PreservesColimitsOfShape (Discrete I)
      (pullbackTwistFunctor b D ⋙ Scheme.Modules.pushforward b) :=
    comp_preservesColimitsOfShape _ _
  let Z : I → X.Modules := fun _ => SheafOfModules.unit X.ringCatSheaf
  exact ProjectionFormulaQCohCoproducts.isIso_of_isIso_app_of_isIso_sigmaComparison
    (𝟭 X.Modules) (pullbackTwistFunctor b D ⋙ Scheme.Modules.pushforward b)
    (twistUnderivedMap b D) (fun g => twistUnderivedMap_naturality b D g) Z inferInstance
    inferInstance
    (fun _ => isIso_twistUnderivedMap b D (SheafOfModules.unit X.ringCatSheaf) hunit)

/-- `b^*𝒪_X ⊗ 𝒪_L(D) ≅ 𝒪_L ⊗ 𝒪_L(D)`. -/
def pullbackTwistUnitIso :
    (pullbackTwistFunctor b D).obj (Scheme.unitModule X) ≅
      Scheme.Modules.tensorObj (Scheme.unitModule L) (Stacks.Divisors.invertibleSheaf' D) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨L.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ L.sheaf.obj (forget₂ CommRingCat RingCat)
        L.ringCatSheaf.property⟩).mapIso (Scheme.Modules.pullbackUnitIso b)).app
    (Stacks.Divisors.invertibleSheaf' D)

/-- `𝒪_L ⊗ 𝒪_L(D) ≅ 𝒪_L(D)`. -/
def unitTwistIso :
    Scheme.Modules.tensorObj (SheafOfModules.unit L.ringCatSheaf)
        (Stacks.Divisors.invertibleSheaf' D) ≅ (Stacks.Divisors.invertibleSheaf' D : L.Modules) :=
  Stacks.RingedSpace.tensorSheafUnitLeftIso L.toRingedSpace (Stacks.Divisors.invertibleSheaf' D)

open Stacks.AlgebraicGeometry in
/-- **`R^q b_*(b^*ℰ ⊗ 𝒪_L(D)) = 0` for `q > 0` at a free `ℰ` of arbitrary rank**, over an affine
`X`: by [Stacks, Tag 01XK] it is the cohomology `H^q(L, b^*ℰ ⊗ 𝒪_L(D))`, which is a direct sum of
copies of `H^q(L, 𝒪_L(D)) = 0` because cohomology of the quasi-compact and quasi-separated
scheme `L` commutes with direct sums. -/
theorem isZero_higherDirectImage_pullbackTwist_free [IsAffine X] [QuasiCompact b]
    [QuasiSeparated b] [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hq : ∀ q : ℕ, 0 < q → IsZero (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (I : Type u) (i : ℤ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward b).rightDerivedPlus i).obj
      ((pullbackTwistFunctor b D).obj (SheafOfModules.free (R := X.ringCatSheaf) I))) := by
  have : CompactSpace L := QuasiCompact.compactSpace_of_compactSpace b
  have : QuasiSeparatedSpace L := quasiSeparatedSpace_of_quasiSeparated b
  have : (SheafOfModules.free (R := X.ringCatSheaf) I).IsQuasicoherent := inferInstance
  have hqc := isQuasicoherent_pullbackTwist b D (SheafOfModules.free (R := X.ringCatSheaf) I)
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = i := ⟨i.toNat, by omega⟩
  let Z : I → X.Modules := fun _ => Scheme.unitModule X
  have hσ : IsIso (sigmaComparison (pullbackTwistFunctor b D) Z) := inferInstance
  have hsum := isZero_rightDerived_sectionsFunctor_coproduct L
    (fun _ : I => (pullbackTwistFunctor b D).obj (Scheme.unitModule X)) q
    (fun _ => ((hq q (by omega)).of_iso
      (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).mapIso (unitTwistIso D))).of_iso
      (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).mapIso (pullbackTwistUnitIso b D)))
  have hcoh := hsum.of_iso (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).mapIso
    (asIso (sigmaComparison (pullbackTwistFunctor b D) Z)).symm)
  exact @TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_isZero_cohomology
    L X b _ _ _ (q : ℤ) _ hqc ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q _).1 hcoh)

/-- **The criterion at a free `ℰ` of arbitrary rank.** -/
theorem isIso_twistDerivedMap_free [IsAffine X] [QuasiCompact b]
    [QuasiSeparated b] [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (h0 : IsIso (Stacks.DeRham.BlowupTwist.twistUnitComparison b
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D)))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (I : Type u) :
    IsIso (twistDerivedMap b D (SheafOfModules.free (R := X.ringCatSheaf) I)) := by
  have := isQuasicoherent_pullbackTwist b D (SheafOfModules.free (R := X.ringCatSheaf) I)
  exact isIso_twistDerivedMap_of_isIso_underived b D _ (isIso_twistUnderivedMap_free b D h0 I)
    fun i hi => isZero_higherDirectImage_pullbackTwist_free b D hq I i hi

open Opposite in
/-- **The map `𝒪_X ⟶ b_*𝒪_L(D)` is an isomorphism as soon as it is bijective on global
sections**, that is, as soon as `a ↦ b^♯(a) • 1_D` is a bijection `Γ(X, 𝒪_X) ⟶ Γ(L, 𝒪_L(D))`:
both modules are quasi-coherent and `X` is affine, and on global sections the adjoint transpose
of the canonical section is multiplication of `1_D` by `b^♯`. -/
theorem isIso_twistUnitComparison_of_bijective [IsAffine X] [QuasiCompact b]
    [QuasiSeparated b] [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (h : Function.Bijective (fun a : Γ(X, ⊤) =>
      Stacks.SheafOfModules.smulSectionMap (𝒪 := L.presheaf)
        (h𝒪 := (structureSheafRing L.toRingedSpace).property)
        (L := Stacks.Divisors.invertibleSheaf' D)
        ((Stacks.Divisors.canonicalSection' D).val (op ⊤)) (b.appTop.hom a))) :
    IsIso (Stacks.DeRham.BlowupTwist.twistUnitComparison b
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D)) := by
  have : ((Scheme.Modules.pushforward b).obj
      (Stacks.Divisors.invertibleSheaf' D)).IsQuasicoherent :=
    @Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs _ _ b _ _ _
      (isQuasicoherent_twist D)
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top
    (M := Scheme.unitModule X)
    (N := (Scheme.Modules.pushforward b).obj (Stacks.Divisors.invertibleSheaf' D)) _ ?_
  have hsplit : Stacks.DeRham.BlowupTwist.twistUnitComparison b
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D) =
        SheafOfModules.unitToPushforwardObjUnit
            (RingedSpaceModuleAdjunction.structureSheafHom b.toLRSHom.toShHom) ≫
          (SheafOfModules.pushforward
            (RingedSpaceModuleAdjunction.structureSheafHom b.toLRSHom.toShHom)).map
            (Stacks.Divisors.canonicalSectionHom D) := by
    refine ((Stacks.RingedSpace.pullbackAdjunction b.toLRSHom.toShHom).homEquiv_naturality_right
      _ _).trans ?_
    exact congrArg (· ≫ _)
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)
  have key : ∀ a : Γ(X, ⊤), (Stacks.DeRham.BlowupTwist.twistUnitComparison b
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D)).val.app
        (op ⊤) a = Stacks.SheafOfModules.smulSectionMap (𝒪 := L.presheaf)
        (h𝒪 := (structureSheafRing L.toRingedSpace).property)
        (L := Stacks.Divisors.invertibleSheaf' D)
        ((Stacks.Divisors.canonicalSection' D).val (op ⊤)) (b.appTop.hom a) := by
    rw [hsplit]
    intro a
    have h1 : (Stacks.Divisors.canonicalSectionHom D).val.app (op ⊤) (1 : Γ(L, ⊤)) =
        (Stacks.Divisors.canonicalSection' D).val (op ⊤) :=
      congrArg (fun σ => σ.val (op ⊤))
        ((Stacks.Divisors.invertibleSheaf' D).unitHomEquiv.apply_symm_apply
          (Stacks.Divisors.canonicalSection' D))
    change (Stacks.Divisors.canonicalSectionHom D).val.app (op ⊤) (b.appTop.hom a) = _
    have h2 : (Stacks.Divisors.canonicalSectionHom D).val.app (op ⊤) (b.appTop.hom a) =
        b.appTop.hom a • (Stacks.Divisors.canonicalSectionHom D).val.app (op ⊤) (1 : Γ(L, ⊤)) := by
      have h3 := ((Stacks.Divisors.canonicalSectionHom D).val.app (op ⊤)).hom.map_smul
        (b.appTop.hom a) (1 : Γ(L, ⊤))
      exact (congrArg ((Stacks.Divisors.canonicalSectionHom D).val.app (op ⊤)).hom
        (mul_one (b.appTop.hom a))).symm.trans h3
    exact h2.trans (congrArg (b.appTop.hom a • ·) h1)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (congrArg Function.Bijective (funext key)).mpr h

/-! ### Locality on the base -/

open StacksDraft.PseudoCoherence in
/-- **Invertibility of a morphism of `D(𝒪_Y)` is local on `Y`**: it may be checked after
restriction to the members of an open cover, cohomology sheaf by cohomology sheaf. -/
theorem isIso_of_isIso_mapDerivedCategory_pullback {Y : Scheme.{u}}
    {K K' : DerivedCategory Y.Modules} (φ : K ⟶ K') {ι : Type*} (V : ι → Y.Opens)
    (hV : TopologicalSpace.IsOpenCover V)
    (h : ∀ i, IsIso ((Scheme.Modules.pullback (V i).ι).mapDerivedCategory.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro q
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _ V hV fun i => ?_
  have : PreservesFiniteLimits (Scheme.Modules.pullback (V i).ι) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion (V i).ι
  have hi : IsIso (((Scheme.Modules.pullback (V i).ι).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor (V i).toScheme.Modules q).map φ) :=
    have := h i
    Functor.map_isIso (DerivedCategory.homologyFunctor (V i).toScheme.Modules q) _
  have hpb := (NatIso.isIso_map_iff
    (mapDerivedCategoryCompHomologyFunctorIso (Scheme.Modules.pullback (V i).ι) q) φ).1 hi
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (V i).ι) _).2 hpb

open Stacks.SchemeCohomology (hom) in
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (pushforwardToDerivedCategory
  derivedPushforward derivedPushforwardUnit) in
/-- **[Stacks, Tag 08FE] as a natural isomorphism**, at the restriction of `b` over an open `V`
of `X`: `Rb_*(-)|_V ≅ R(b|_V)_*((-)|_{b⁻¹V})`.  This is the natural isomorphism out of which
`AlgebraicGeometry.schemeDerivedPushforwardRestrictOpenIso` is built objectwise. -/
def derivedPushforwardRestrictNatIso (V : X.Opens) :
    schemeDerivedPushforward b ⋙ (Scheme.Modules.pullback V.ι).mapDerivedCategory ≅
      (Scheme.Modules.pullback (b ⁻¹ᵁ V).ι).mapDerivedCategory ⋙
        schemeDerivedPushforward (b ∣_ V) := by
  have hsq := (isPullback_morphismRestrict b V).flip
  have hli : PreservesFiniteLimits (Scheme.Modules.pullback (b ⁻¹ᵁ V).ι) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion _
  have hlj : PreservesFiniteLimits (Scheme.Modules.pullback V.ι) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion V.ι
  have hiR : (Scheme.Modules.pullback (b ⁻¹ᵁ V).ι).mapDerivedCategory.IsRightDerivedFunctor
      (Scheme.Modules.pullback (b ⁻¹ᵁ V).ι).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso L.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      (Scheme.Modules.pullback (b ⁻¹ᵁ V).ι).mapDerivedCategoryFactorsh
  have hjR : (Scheme.Modules.pullback V.ι).mapDerivedCategory.IsRightDerivedFunctor
      (Scheme.Modules.pullback V.ι).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      (Scheme.Modules.pullback V.ι).mapDerivedCategoryFactorsh
  have hfR : (schemeDerivedPushforward b).IsRightDerivedFunctor (schemeDerivedPushforwardUnit b)
      (HomotopyCategory.quasiIso L.Modules (ComplexShape.up ℤ)) := inferInstance
  have hf'R : (schemeDerivedPushforward (b ∣_ V)).IsRightDerivedFunctor
      (schemeDerivedPushforwardUnit (b ∣_ V))
      (HomotopyCategory.quasiIso (b ⁻¹ᵁ V).toScheme.Modules (ComplexShape.up ℤ)) :=
    inferInstance
  exact @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _
    (hom b) (hom (b ⁻¹ᵁ V).ι) (hom V.ι) (hom (b ∣_ V)) _ _
    (isPullback_toShHom _ _ _ _ hsq) _ _ _ _
    (schemeDerivedPushforward b) (schemeDerivedPushforward (b ∣_ V))
    (Scheme.Modules.pullback (b ⁻¹ᵁ V).ι).mapDerivedCategory
    (Scheme.Modules.pullback V.ι).mapDerivedCategory
    (schemeDerivedPushforwardUnit b) (schemeDerivedPushforwardUnit (b ∣_ V))
    (Scheme.Modules.pullback (b ⁻¹ᵁ V).ι).mapDerivedCategoryFactorsh.inv
    (Scheme.Modules.pullback V.ι).mapDerivedCategoryFactorsh.inv
    hfR hf'R hiR hjR

/-- Restriction to an open commutes with placing a module in degree zero, so it carries
`single(k)` to an isomorphism as soon as it carries `k` to one. -/
theorem isIso_mapDerivedCategory_pullback_single_map {Y Z : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] {M N : Y.Modules} (k : M ⟶ N)
    (hk : IsIso ((Scheme.Modules.pullback j).map k)) :
    IsIso ((Scheme.Modules.pullback j).mapDerivedCategory.map
      ((DerivedCategory.singleFunctor Y.Modules 0).map k)) := by
  have : PreservesFiniteLimits (Scheme.Modules.pullback j) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion j
  have h : IsIso ((Scheme.Modules.pullback j ⋙ DerivedCategory.singleFunctor Z.Modules 0).map k) :=
    Functor.map_isIso (DerivedCategory.singleFunctor Z.Modules 0) _
  exact Stacks.AffineProjectionFormula.isIso_functor_map_of_natIso
    ((Scheme.Modules.pullback j).mapDerivedCategorySingleFunctor 0) k h

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- Inverse image carries `m ⊗ id_A` to an isomorphism as soon as it carries `m` to one: the
pullback tensor comparison of [Stacks, Tag 01CD] is a natural isomorphism. -/
theorem isIso_pullback_tensorRightMap {Y Z : Scheme.{u}} (j : Z ⟶ Y) {M M' : Y.Modules}
    (m : M ⟶ M') (A : Y.Modules) (hm : IsIso ((Scheme.Modules.pullback j).map m)) :
    IsIso ((Scheme.Modules.pullback j).map (Scheme.Modules.tensorRightMap m A)) := by
  have hnat := tensorSheafSchemeCommIso_naturality Y A m
  have e : Scheme.Modules.tensorRightMap m A =
      (tensorSheafSchemeCommIso Y A M).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).map
          ((𝟙 A ×ₘ m : ((A, M) : _ × _) ⟶ (A, M'))) ≫
        (tensorSheafSchemeCommIso Y A M').hom := by
    have e2 := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj M').map_id A
    refine Eq.trans ?_ (congrArg (_ ≫ ·) hnat).symm
    refine Eq.trans ?_ (Iso.inv_hom_id_assoc _ _).symm
    exact ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) e2.symm))
  have h1 := Stacks.AffineProjectionFormula.isIso_pullback_tensorSheaf_map
    j.toLRSHom.toShHom A m hm
  rw [e]
  have h2 := @IsIso.comp_isIso _ _ _ _ _ _ _
    ((Scheme.Modules.pullback j).mapIso (tensorSheafSchemeCommIso Y A M).symm).isIso_hom
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h1
      ((Scheme.Modules.pullback j).mapIso (tensorSheafSchemeCommIso Y A M')).isIso_hom)
  exact (congrArg (fun φ => IsIso φ) (((Scheme.Modules.pullback j).map_comp _ _).trans
    (congrArg (_ ≫ ·) ((Scheme.Modules.pullback j).map_comp _ _)))).mpr h2

/-- The canonical maps `ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪_L(D))`, as a natural transformation in `ℰ`. -/
def twistDerivedNatTrans :
    DerivedCategory.singleFunctor X.Modules 0 ⟶
      pullbackTwistFunctor b D ⋙ DerivedCategory.singleFunctor L.Modules 0 ⋙
        schemeDerivedPushforward b where
  app E := twistDerivedMap b D E
  naturality _ _ k := twistDerivedMap_naturality b D k

/-- **Invertibility of the restriction to an open `V` of the canonical map is transported along
any morphism of modules whose restriction to `V` is invertible.** -/
theorem isIso_restrict_twistDerivedMap_congr (V : X.Opens) {E E' : X.Modules} (k : E ⟶ E')
    (hk : IsIso ((Scheme.Modules.pullback V.ι).map k)) :
    IsIso ((Scheme.Modules.pullback V.ι).mapDerivedCategory.map (twistDerivedMap b D E)) ↔
      IsIso ((Scheme.Modules.pullback V.ι).mapDerivedCategory.map (twistDerivedMap b D E')) := by
  have hF := isIso_mapDerivedCategory_pullback_single_map V.ι k hk
  have h1 := Stacks.AffineProjectionFormula.isIso_pullback_pullback_map b V k hk
  have h2 := isIso_pullback_tensorRightMap (b ⁻¹ᵁ V).ι ((Scheme.Modules.pullback b).map k)
    (Stacks.Divisors.invertibleSheaf' D) h1
  have h3 := isIso_mapDerivedCategory_pullback_single_map (b ⁻¹ᵁ V).ι
    ((pullbackTwistFunctor b D).map k) h2
  have h4 : IsIso (((Scheme.Modules.pullback (b ⁻¹ᵁ V).ι).mapDerivedCategory ⋙
      schemeDerivedPushforward (b ∣_ V)).map
        ((DerivedCategory.singleFunctor L.Modules 0).map ((pullbackTwistFunctor b D).map k))) :=
    Functor.map_isIso (schemeDerivedPushforward (b ∣_ V)) _
  have hG := Stacks.AffineProjectionFormula.isIso_functor_map_of_natIso
    (derivedPushforwardRestrictNatIso b V) _ h4
  exact Stacks.AffineProjectionFormula.isIso_natTrans_app_iff_of_isIso_map
    (Functor.whiskerRight (twistDerivedNatTrans b D)
      (Scheme.Modules.pullback V.ι).mapDerivedCategory) k hF hG

/-- The restriction of a free module to an open subscheme is free on the same index type. -/
def restrictFreeIso {Y Z : Scheme.{u}} (j : Z ⟶ Y) [IsOpenImmersion j] (I : Type u) :
    (Scheme.Modules.restrictFunctor j).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := Z.ringCatSheaf) I :=
  haveI : (TopologicalSpace.Opens.map j.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  haveI : (SheafOfModules.pushforward j.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction j).isRightAdjoint
  (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫
    SheafOfModules.pullbackObjFreeIso j.toRingCatSheafHom I

/-- **The restriction of the canonical map to an open on which `ℰ` is free is an
isomorphism**: transport along the restriction unit at `𝒪_X^{(I)}`, the direct image of the
trivialisation, and the restriction unit at `ℰ`, starting from the free case. -/
theorem isIso_restrict_twistDerivedMap_of_free [IsAffine X] [QuasiCompact b]
    [QuasiSeparated b] [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (h0 : IsIso (Stacks.DeRham.BlowupTwist.twistUnitComparison b
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D)))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (E : X.Modules) (V : X.Opens) (I : Type u)
    (e : E.restrict V.ι ≅ SheafOfModules.free (R := V.toScheme.ringCatSheaf) I) :
    IsIso ((Scheme.Modules.pullback V.ι).mapDerivedCategory.map (twistDerivedMap b D E)) := by
  let F : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) I
  have c0 : IsIso ((Scheme.Modules.pullback V.ι).mapDerivedCategory.map
      (twistDerivedMap b D F)) :=
    have := isIso_twistDerivedMap_free b D h0 hq I
    Functor.map_isIso _ _
  let uF := (Scheme.Modules.restrictAdjunction V.ι).unit.app F
  let uE := (Scheme.Modules.restrictAdjunction V.ι).unit.app E
  let k : (Scheme.Modules.pushforward V.ι).obj (F.restrict V.ι) ⟶
      (Scheme.Modules.pushforward V.ι).obj (E.restrict V.ι) :=
    (Scheme.Modules.pushforward V.ι).map (restrictFreeIso V.ι I ≪≫ e.symm).hom
  have hk : IsIso ((Scheme.Modules.pullback V.ι).map k) :=
    have : IsIso k := ((Scheme.Modules.pushforward V.ι).mapIso
      (restrictFreeIso V.ι I ≪≫ e.symm)).isIso_hom
    Functor.map_isIso _ _
  exact (isIso_restrict_twistDerivedMap_congr b D V uE
    (Stacks.AffineProjectionFormula.isIso_pullback_openRestrictUnit V E)).mpr
    ((isIso_restrict_twistDerivedMap_congr b D V k hk).mp
      ((isIso_restrict_twistDerivedMap_congr b D V uF
        (Stacks.AffineProjectionFormula.isIso_pullback_openRestrictUnit V F)).mp c0))

/-- **The criterion for `ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪_L(D))` to be an isomorphism, for a locally free `ℰ`
of arbitrary rank.**  Let `b : L ⟶ X` be quasi-compact and quasi-separated with `X` affine and
let `D` be an effective Cartier divisor on `L`.  If `𝒪_X ⟶ b_*𝒪_L(D)` is an isomorphism (`h0`)
and `H^q(L, 𝒪_L(D)) = 0` for every `q > 0` (`hq`), then the canonical map
`ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪_L(D))` is an isomorphism in `D(𝒪_X)` for every locally free `ℰ`.

Invertibility in `D(𝒪_X)` is local on `X`, and on an open where `ℰ` is free it is transported
from the free case `isIso_twistDerivedMap_free` by `isIso_restrict_twistDerivedMap_of_free`. -/
theorem isIso_twistDerivedMap [IsAffine X] [QuasiCompact b]
    [QuasiSeparated b] [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (h0 : IsIso (Stacks.DeRham.BlowupTwist.twistUnitComparison b
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D)))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (E : X.Modules) [hE : SheafOfModules.IsLocallyFree.{u, u, u} E] :
    IsIso (twistDerivedMap b D E) := by
  choose V hV I e using (Stacks.Modules.isLocallyFree_iff_localGenerators E).mpr hE
  exact isIso_of_isIso_mapDerivedCategory_pullback _ V
    (TopologicalSpace.IsOpenCover.mk (le_antisymm le_top fun x _ =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hV x⟩))
    fun x => isIso_restrict_twistDerivedMap_of_free b D h0 hq E (V x) (I x) (e x).some

open Opposite in
/-- **The criterion for a locally free `ℰ` of arbitrary rank, with the degree-zero hypothesis on
global sections**: `isIso_twistDerivedMap` with `h0` supplied by
`isIso_twistUnitComparison_of_bijective`. -/
theorem isIso_twistDerivedMap_of_isLocallyFree_of_bijective [IsAffine X] [QuasiCompact b]
    [QuasiSeparated b] [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (h : Function.Bijective (fun a : Γ(X, ⊤) =>
      Stacks.SheafOfModules.smulSectionMap (𝒪 := L.presheaf)
        (h𝒪 := (structureSheafRing L.toRingedSpace).property)
        (L := Stacks.Divisors.invertibleSheaf' D)
        ((Stacks.Divisors.canonicalSection' D).val (op ⊤)) (b.appTop.hom a)))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (E : X.Modules) [SheafOfModules.IsLocallyFree.{u, u, u} E] :
    IsIso (twistDerivedMap b D E) :=
  isIso_twistDerivedMap b D (isIso_twistUnitComparison_of_bijective b D h) hq E

/-- **The criterion for a finite locally free `ℰ`, with the degree-zero hypothesis on global
sections**: the case of `isIso_twistDerivedMap_of_isLocallyFree_of_bijective` at a finite locally
free `ℰ`, which is locally free. -/
theorem isIso_twistDerivedMap_of_bijective [IsAffine X] [QuasiCompact b] [QuasiSeparated b]
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (h : Function.Bijective (fun a : Γ(X, ⊤) =>
      Stacks.SheafOfModules.smulSectionMap (𝒪 := L.presheaf)
        (h𝒪 := (structureSheafRing L.toRingedSpace).property)
        (L := Stacks.Divisors.invertibleSheaf' D)
        ((Stacks.Divisors.canonicalSection' D).val (Opposite.op ⊤)) (b.appTop.hom a)))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (E : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsIso (twistDerivedMap b D E) :=
  have : SheafOfModules.IsLocallyFree.{u, u, u} E :=
    hE.exists_isFiniteLocallyFreeData.elim fun q hq => ⟨q, hq.1⟩
  isIso_twistDerivedMap_of_isLocallyFree_of_bijective b D h hq E

end Stacks.DeRham.TwistDerived

end
