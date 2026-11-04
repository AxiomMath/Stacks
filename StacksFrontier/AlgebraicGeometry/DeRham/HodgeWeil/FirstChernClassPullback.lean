module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Pullback
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationEdge
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.ShiftedUnitsPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.RealizationIsoAgreement
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple

/-!
# The Hodge first Chern class commutes with pullback, in the module realization

Consider a commutative square of schemes

```
X' --g--> X
|f'       |f
v         v
S' --h--> S
```

and write `g₀ : (X', f'⁻¹𝒪_{S'}) ⟶ (X, f⁻¹𝒪_S)` for its morphism of ringed spaces. The groups
`H^q(X, Ω^p_{X/S})` have two realizations: as the cohomology `R^qΓ(X, Ω^p_{X/S})` of the
underlying sheaf of abelian groups, in which the Hodge first Chern class
`AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass` and its pullback
`AlgebraicGeometry.Scheme.Hom.hodgeCohomologyOnePullback` (the map induced by
`Ω_{X/S} ⟶ g_*Ω_{X'/S'}` followed by the first Leray edge map) are formed, and as the cohomology
of the derived global sections of `Ω^p_{X/S}[0]` as a complex of `f⁻¹𝒪_S`-modules, on which the
cup product and the pullback `Stacks.HodgeWeil.hodgePullback` of the Weil cohomology theory
(Stacks, Remark 0FWE) are formed. The two are identified by
`AlgebraicGeometry.SheafOfModules.hodgeComponentAbelianIso` ([Stacks, Tag 01F1]).

This file shows that the identification carries the abelian pullback to the module pullback,
for every `p` and `q`. Both pullbacks are a map induced by the canonical map of forms
`Ω^p_{X/S} ⟶ g_*Ω^p_{X'/S'}` followed by an identification of the cohomology of `g_*(-)` on `X`
with cohomology on `X'`: the Leray edge map in abelian sheaves, the comparison
`g₀_* ⟶ Rg₀_*` and the Leray identification `H^q(X, Rg₀_* -) = H^q(X', -)` of Tag 0D5W in
modules. The edge map is transported to bounded below derived categories through
`Stacks.DerivedIndexing.map_comp_edge_comp_rightDerivedIso`, and the comparison of the two
identifications is the edge identity
`Stacks.DeRhamBaseChange.realizationUnbounded_pushforwardPullback` of the realization comparison.

In degree one, with the degree-one generator `Ω_{X/S} ⟶ ⋀¹Ω_{X/S}`, which commutes with the
canonical maps of the square, this gives axiom (A2) of Weil cohomology theories for Hodge
cohomology, `f^*c₁^{Hodge}(ℒ) = c₁^{Hodge}(f^*ℒ)` (Stacks, Section 0FID, "Ad (A2)", and
Remark 0FWE), in the module realization.

## Main definitions

* `Stacks.HodgeWeil.formsAbelianPushforward`: the canonical map `Ω^p_{X/S} ⟶ g_*Ω^p_{X'/S'}` of
  underlying sheaves of abelian groups.
* `Stacks.HodgeWeil.formsExtendPushforward`: the canonical map of the complexes `Ω^p[0]`,
  extended from `ℕ` to `ℤ`, of `f⁻¹𝒪_S`-modules.

## Main results

* `Stacks.HodgeWeil.hodgeComponentAbelianIso_hodgePullback`: **the comparison of the two
  realizations of `H^q(X, Ω^p_{X/S})` carries the abelian pullback to the module pullback.**
* `Stacks.HodgeWeil.hodgeCohomologyOneIsoComponent_hodgeCohomologyOnePullback`: the same for the
  identification `Stacks.HodgeWeil.hodgeCohomologyOneIsoComponent` of `H¹(X, Ω_{X/S})` with
  `H¹(X, Ω¹_{X/S})`.
* `Stacks.HodgeWeil.hodgePullback_hodgeFirstChernClassModule`: **the module-realization Hodge
  first Chern class commutes with pullback**, on Picard classes.
* `Stacks.HodgeWeil.hodgePullback_hodgeFirstChernClassModule_picardClassOf`: the same on the
  class of an invertible module, in the spelling of
  `Stacks.WeilCohomology.FirstChernClassData.PullbackAxiom`.

## Implementation notes

The complex `Ω^p[0]` enters in three spellings: the sheaf of abelian groups placed in degree `0`
of the abelian realization, the `ℕ`-indexed complex extended to `ℤ` on which
`AlgebraicGeometry.SheafOfModules.hodgeComponentAbelianIso` lands, and the `ℤ`-indexed complex
`Stacks.HodgeWeil.formsSingle` on which `Stacks.HodgeWeil.hodgePullback` is defined. The canonical
map of the square is compared across the three in degree `0` only, the complexes being
concentrated there. The objects `g_*` of the underlying complex and the underlying complex of
`g₀_*` agree by definition, but checking it is expensive; the map
`Stacks.HodgeWeil.formsExtendPushforwardUnderlying` is stated with the first as its target, so
that the check is made once.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cohomology.LerayLowDegree (abelianPushforward abelianEdgeMap abelianCohomology)
open Stacks.DeRhamBaseChange Stacks.DeRhamDirectImage
open AlgebraicGeometry.SheafOfModules (moduleComplexPlus)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Three functors applied to a composite, split into the composite of the applications. -/
private theorem map_map_map_comp {C D E F : Type*} [Category* C] [Category* D] [Category* E]
    [Category* F] {Q : C ⥤ D} {R : D ⥤ E} {H : E ⥤ F} {A B Z : C} (a : A ⟶ B) (b : B ⟶ Z) :
    H.map (R.map (Q.map (a ≫ b))) = H.map (R.map (Q.map a)) ≫ H.map (R.map (Q.map b)) := by
  simp

/-! ### The comparison of the two realizations, written out -/

section Realization

open AlgebraicGeometry.SheafOfModules

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {Y : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} Y.carrier}
  {φ : A ⟶ Y.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology Y.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **`Ω^p` placed in degree `0` in abelian sheaves is the underlying complex of abelian sheaves
of `Ω^p[0]`**, the `ℕ`-indexed complex of `A`-modules extended to `ℤ`. -/
abbrev hodgeSingleUnderlyingIso (p : ℕ) :
    (Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf Y.carrier) 0).obj
        ((deRhamAbelianComplex B D).X p) ≅
      (_root_.SheafOfModules.toSheaf
        (structureSheafRing (baseRingedSpace A))).mapCochainComplexPlus.obj
          (moduleComplexPlus (X := Y) (A := A) (hodgeSingle B D p)) :=
  hodgeSinglePlusIso B D p ≪≫ modulePlusIso (X := Y) (A := A) (hodgeSingle B D p)

/-- **The comparison `R^iΓ(X, Ω^p) ≅ H^i(X, Ω^p)` of the two realizations, written out**: the
comparison of the two indexings of right derived functors, the identification
`hodgeSingleUnderlyingIso`, the realization comparison
`Stacks.Cech.Hypercohomology.realizationUnbounded` of Tag 01F1 and the identification of the
extended complex with `Ω^p` placed in degree `0`. -/
theorem hodgeComponentAbelianIso_hom_apply (p i : ℕ)
    (y : ((sectionsFunctor Y.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X p)) :
    (hodgeComponentAbelianIso B D p i i rfl).hom.hom y =
      (hodgeComponentIso B p i).hom.hom
        ((Stacks.Cech.Hypercohomology.realizationUnbounded (baseRingedSpace A)
          (moduleComplexPlus (X := Y) (A := A) (hodgeSingle B D p)) i).hom.hom
          (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
            ((sectionsFunctor Y.carrier ⊤).rightDerivedFunctorPlus.map
              (DerivedCategory.Plus.Q.map (hodgeSingleUnderlyingIso B D p).hom))).hom
            ((Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y.carrier ⊤) i).hom.app _
              y))) := by
  have hρ : (Stacks.Cech.Hypercohomology.realizationUnbounded (baseRingedSpace A)
      (moduleComplexPlus (X := Y) (A := A) (hodgeSingle B D p)) i).hom =
      (Stacks.Cohomology.RealizationShift.realizationIsoAt (baseRingedSpace A)
        (moduleComplexPlus (X := Y) (A := A) (hodgeSingle B D p)) i).hom :=
    Stacks.Cohomology.RealizationAgreement.realizationIso_hom_comp_derivedSectionsFunctorIso
      _ _ _
  have hE : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
      ((sectionsFunctor Y.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (hodgeSingleUnderlyingIso B D p).hom)) =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
        ((sectionsFunctor Y.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (hodgeSinglePlusIso B D p).hom)) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
        ((sectionsFunctor Y.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (modulePlusIso (X := Y) (A := A) (hodgeSingle B D p)).hom)) :=
    map_map_map_comp _ _
  exact (congrArg₂ (fun a b => (hodgeComponentIso B p i).hom.hom (AddCommGrpCat.Hom.hom b
    (AddCommGrpCat.Hom.hom a ((Stacks.DerivedIndexing.rightDerivedIso
      (sectionsFunctor Y.carrier ⊤) i).hom.app _ y)))) hE hρ).symm

/-- In degree `0`, `hodgeSingleUnderlyingIso` is the identity of `Ω^p`, read through the
identifications of the terms of the complexes concentrated in degree `0`. -/
theorem hodgeSingleUnderlyingIso_hom_f_zero (p : ℕ) :
    (hodgeSingleUnderlyingIso B D p).hom.hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((deRhamAbelianComplex B D).X p)).hom ≫
        (_root_.SheafOfModules.toSheaf.{u, u, u, u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A)).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
              ((deRhamComplex B D).X p)).inv ≫
            ((hodgeSingle B D p).extendXIso ComplexShape.embeddingUpNat
              (i := 0) (i' := 0) rfl).inv) := by
  change (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat _ 0 0 rfl).inv.f 0 ≫
    (HomologicalComplex.extendMap ((HomologicalComplex.singleMapHomologicalComplex
        (_root_.SheafOfModules.toSheaf.{u, u, u, u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A)) (ComplexShape.up ℕ) 0).inv.app
          ((deRhamComplex B D).X p)) ComplexShape.embeddingUpNat ≫
      (HomologicalComplex.mapHomologicalComplexExtendIso
        (_root_.SheafOfModules.toSheaf.{u, u, u, u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A)) (hodgeSingle B D p)
        ComplexShape.embeddingUpNat).hom).f 0 = _
  refine (congrArg₂ (· ≫ ·) (HomologicalComplex.extendSingleIso_inv_f ..)
    (HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f _ _ _ _ rfl)).trans ?_
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  rfl

end Realization

/-- A chain of isomorphisms and their inverses around a morphism `N ⟶ k(N')`, cancelled. -/
private theorem iso_chain {C D : Type*} [Category* C] [Category* D] (k : D ⥤ C)
    {N sN eN zN : C} {N' sN' eN' zN' : D} (σ : sN ≅ N) (ε : eN ≅ sN) (τ : zN ≅ N)
    (m : N ⟶ k.obj N') (τ' : zN' ≅ N') (σ' : sN' ≅ N') (ε' : eN' ≅ sN') :
    (σ.inv ≫ ε.inv) ≫ (ε.hom ≫ σ.hom ≫ τ.inv) ≫ (τ.hom ≫ m ≫ k.map τ'.inv) ≫
        k.map (τ'.hom ≫ σ'.inv ≫ ε'.inv) = m ≫ k.map (σ'.inv ≫ ε'.inv) := by
  simp

variable {X X' S S' : Scheme.{u}} (g : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (h : S' ⟶ S)
  (w : g ≫ f = f' ≫ h)

/-! ### The canonical maps of the square -/

/-- **The degree-one generator commutes with the canonical maps of the square**: the canonical
map `Ω_{X/S} ⟶ g_*Ω_{X'/S'}` followed by the generator `Ω_{X'/S'} ⟶ ⋀¹Ω_{X'/S'}` is the
generator `Ω_{X/S} ⟶ ⋀¹Ω_{X/S}` followed by the canonical map of forms of degree one. Both are
`𝒪_X`-linear and agree on the universal differentials `d t`. -/
theorem relativeDifferentialsPushforwardMap_exteriorGenerator :
    Scheme.Hom.relativeDifferentialsPushforwardMap g f f' h w ≫
        (Scheme.Modules.pushforward g).map
          (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials f')) =
      Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials f) ≫
        formsAdjoint g f' f h w 1 := by
  refine Stacks.ConormalSequenceRight.relativeDifferentials_hom_ext f _ _ fun V t => ?_
  exact (congrArg _ (Scheme.Hom.relativeDifferentialsPushforwardMap_d g f f' h w V t)).trans
    (Scheme.Hom.relativeDifferentialFormsPullback_exteriorGenerator_d g f f' h w V t).symm

/-- **The canonical map `Ω^p_{X/S} ⟶ g_*Ω^p_{X'/S'}` of underlying sheaves of abelian groups**
of a commutative square, the canonical map of forms of Tag 07HX. -/
abbrev formsAbelianPushforward (p : ℕ) :
    (SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))).X p ⟶
      (abelianPushforward.{u, u} g.base).obj
        ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).X p) :=
  (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map (formsAdjoint g f' f h w p)

/-- The identification of `Ω^p_{X/S}[0]`, extended from `ℕ` to `ℤ`, with `Ω^p_{X/S}` placed in
degree `0` as a complex indexed by `ℤ`. -/
abbrev formsSingleExtendIso (p : ℕ) :
    (moduleComplexPlus (X := X.toRingedSpace)
      (A := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
      (SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p)).obj ≅
      formsSingle f p :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat _ 0 0 rfl

/-- `formsSingleExtendIso` in degree `0`. -/
theorem formsSingleExtendIso_hom_f_zero (p : ℕ) :
    (formsSingleExtendIso f p).hom.f 0 =
      ((SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p).extendXIso
          ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((Scheme.Hom.deRhamComplex f).X p)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((Scheme.Hom.deRhamComplex f).X p)).inv :=
  HomologicalComplex.extendSingleIso_hom_f _ _ _ _ rfl

/-- The inverse of `formsSingleExtendIso` in degree `0`. -/
theorem formsSingleExtendIso_inv_f_zero (p : ℕ) :
    (formsSingleExtendIso f p).inv.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((Scheme.Hom.deRhamComplex f).X p)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((Scheme.Hom.deRhamComplex f).X p)).inv ≫
        ((SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p).extendXIso
          ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv :=
  HomologicalComplex.extendSingleIso_inv_f _ _ _ _ rfl

/-- **The canonical map `Ω^p_{X/S}[0] ⟶ g₀_*(Ω^p_{X'/S'}[0])` of the extended complexes** of a
commutative square: `Stacks.HodgeWeil.formsSinglePushforward` read through the identifications
`formsSingleExtendIso` on `X` and on `X'`. -/
def formsExtendPushforward (p : ℕ) :
    moduleComplexPlus (X := X.toRingedSpace)
        (A := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
        (SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p) ⟶
      (StacksDraft.KFlat.modulePushforward
          (inverseImageBaseMap g f' f h w)).mapCochainComplexPlus.obj
        (moduleComplexPlus (X := X'.toRingedSpace)
          (A := (TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf)
          (SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f')
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p)) :=
  ObjectProperty.homMk ((formsSingleExtendIso f p).hom ≫ formsSinglePushforward g f' f h w p ≫
    (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
      (inverseImageBaseMap g f' f h w)).map (formsSingleExtendIso f' p).inv)

/-- `formsExtendPushforward` on the underlying complexes of abelian sheaves, with target the
abelian direct image along `g` of the underlying complex on `X'`. -/
def formsExtendPushforwardUnderlying (p : ℕ) :
    (_root_.SheafOfModules.toSheaf
        (structureSheafRing (inverseImageBase f))).mapCochainComplexPlus.obj
        (moduleComplexPlus (X := X.toRingedSpace)
          (A := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
          (SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f)
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p)) ⟶
      (abelianPushforward.{u, u} g.base).mapCochainComplexPlus.obj
        ((_root_.SheafOfModules.toSheaf
          (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
          (moduleComplexPlus (X := X'.toRingedSpace)
            (A := (TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf)
            (SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f')
              (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p))) :=
  (_root_.SheafOfModules.toSheaf
    (structureSheafRing (inverseImageBase f))).mapCochainComplexPlus.map
    (formsExtendPushforward g f' f h w p)

/-- **The canonical maps of forms of the abelian and of the module realization agree** through
the identifications `hodgeSingleUnderlyingIso` on `X` and on `X'`. Both sides are morphisms out
of a complex concentrated in degree `0`, and in degree `0` both are the pullback of forms on
local sections. -/
theorem formsExtendPushforward_square (p : ℕ) :
    ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
        (formsAbelianPushforward g f' f h w p) ≫
      (Stacks.DerivedIndexing.mapSinglePlus (abelianPushforward.{u, u} g.base) 0).app _) ≫
      (abelianPushforward.{u, u} g.base).mapCochainComplexPlus.map
        (hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p).hom =
    (hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p).hom ≫
      formsExtendPushforwardUnderlying g f' f h w p := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.from_single_hom_ext ?_)
  have hL : (((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
        (formsAbelianPushforward g f' f h w p) ≫
      (Stacks.DerivedIndexing.mapSinglePlus (abelianPushforward.{u, u} g.base) 0).app _) ≫
      (abelianPushforward.{u, u} g.base).mapCochainComplexPlus.map
        (hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p).hom).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f)
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))).X p)).hom ≫
        formsAbelianPushforward g f' f h w p ≫
        (abelianPushforward.{u, u} g.base).map
          ((_root_.SheafOfModules.toSheaf.{u, u, u, u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
              ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf))).map
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
                ((Scheme.Hom.deRhamComplex f').X p)).inv ≫
              ((SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f')
                (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p).extendXIso
                ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv)) := by
    change (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        (formsAbelianPushforward g f' f h w p)).f 0 ≫
      ((HomologicalComplex.singleMapHomologicalComplex (abelianPushforward.{u, u} g.base)
        (ComplexShape.up ℤ) 0).inv.app
        ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).X p)).f 0) ≫
      (abelianPushforward.{u, u} g.base).map
        ((hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p).hom.hom.f 0) = _
    rw [HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      hodgeSingleUnderlyingIso_hom_f_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (_ ≫ _ ≫ ·) (((abelianPushforward.{u, u} g.base).map_comp _ _).symm.trans
      (congrArg (abelianPushforward.{u, u} g.base).map (Iso.inv_hom_id_assoc _ _)))
  have hR : ((hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p).hom ≫
        formsExtendPushforwardUnderlying g f' f h w p).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f)
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))).X p)).hom ≫
        (_root_.SheafOfModules.toSheaf.{u, u, u, u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).map
          (formsPushforward g f' f h w p ≫
            (StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g f' f h w)).map
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
                  ((Scheme.Hom.deRhamComplex f').X p)).inv ≫
                ((SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f')
                  (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p).extendXIso
                  ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv)) := by
    change (hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p).hom.hom.f 0 ≫
      (_root_.SheafOfModules.toSheaf.{u, u, u, u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).map
        ((formsSingleExtendIso f p).hom.f 0 ≫ (formsSinglePushforward g f' f h w p).f 0 ≫
          (StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g f' f h w)).map
            ((formsSingleExtendIso f' p).inv.f 0)) = _
    rw [hodgeSingleUnderlyingIso_hom_f_zero]
    refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (((_root_.SheafOfModules.toSheaf.{u, u, u, u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).map_comp _ _).symm.trans
        (congrArg (_root_.SheafOfModules.toSheaf.{u, u, u, u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).map ?_)))
    rw [formsSingleExtendIso_hom_f_zero, formsSinglePushforward_f_zero,
      formsSingleExtendIso_inv_f_zero]
    exact iso_chain _ _ _ _ _ _ _ _
  have hcore : formsAbelianPushforward g f' f h w p ≫
      (abelianPushforward.{u, u} g.base).map
        ((_root_.SheafOfModules.toSheaf.{u, u, u, u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
            ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf))).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
              ((Scheme.Hom.deRhamComplex f').X p)).inv ≫
            ((SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f')
              (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p).extendXIso
              ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv)) =
      (_root_.SheafOfModules.toSheaf.{u, u, u, u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).map
        (formsPushforward g f' f h w p ≫
          (StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g f' f h w)).map
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
                ((Scheme.Hom.deRhamComplex f').X p)).inv ≫
              ((SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f')
                (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p).extendXIso
                ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv)) :=
    Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl))
  exact hL.trans ((congrArg (_ ≫ ·) hcore).trans hR.symm)

/-! ### The abelian pullback on bounded below derived categories -/

/-- **The abelian pullback, carried to bounded below derived categories**: the map induced on
`R^iΓ` by `Ω^p_{X/S} ⟶ g_*Ω^p_{X'/S'}` followed by the Leray edge map is, through the comparison
of the two indexings of right derived functors, the map induced by the same morphism on the
complexes placed in degree `0` followed by the pullback from the derived sections of a direct
image `AlgebraicGeometry.Scheme.Hom.pushforwardPullback`. -/
theorem abelianEdgeMap_formsAbelianPushforward_rightDerivedIso (p i : ℕ) :
    (abelianCohomology.{u, u} _ ⊤ i).map (formsAbelianPushforward g f' f h w p) ≫
      (abelianEdgeMap.{u, u} g.base i).app
        ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).X p) ≫
      (Stacks.DerivedIndexing.rightDerivedIso
        (sectionsFunctor X'.toRingedSpace.carrier ⊤) i).hom.app
        ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).X p) =
    (Stacks.DerivedIndexing.rightDerivedIso
        (sectionsFunctor X.toRingedSpace.carrier ⊤) i).hom.app _ ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
              (formsAbelianPushforward g f' f h w p) ≫
            (Stacks.DerivedIndexing.mapSinglePlus (abelianPushforward.{u, u} g.base) 0).app
              ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f')
                (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).X p)))) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        (Scheme.Hom.pushforwardPullback g
          ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X'.carrier) 0).obj
            ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f')
              (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).X p))) := by
  refine (Stacks.DerivedIndexing.map_comp_edge_comp_rightDerivedIso
    (abelianPushforward.{u, u} g.base) (sectionsFunctor X.toRingedSpace.carrier ⊤) i
    (formsAbelianPushforward g f' f h w p)).trans (congrArg (_ ≫ ·) ?_)
  have hedge := (Stacks.DerivedIndexing.rightDerivedPlusEdge_app_eq
    (abelianPushforward.{u, u} g.base) (sectionsFunctor X.carrier ⊤) (i : ℤ)
      ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f')
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).X p)).trans
    (congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
      ((Scheme.Hom.derivedSectionsPullback_mapSinglePlus g 0 _).symm.trans
        (Scheme.Hom.derivedSectionsPullback_eq_comp g _)))
  refine (congrArg (_ ≫ ·) (hedge.trans
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map_comp _ _))).trans ?_
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ?_)
  exact Eq.symm (map_map_map_comp _ _)

/-- **The abelian pullback, carried to the underlying complexes of abelian sheaves of the
complexes of modules `Ω^p[0]`**: through `hodgeSingleUnderlyingIso` it is the map induced by
`formsExtendPushforwardUnderlying` followed by the pullback from the derived sections of a
direct image. -/
theorem abelianEdgeMap_formsAbelianPushforward_hodgeSingleUnderlyingIso (p i : ℕ) :
    (abelianCohomology.{u, u} _ ⊤ i).map (formsAbelianPushforward g f' f h w p) ≫
      (abelianEdgeMap.{u, u} g.base i).app
        ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).X p) ≫
      (Stacks.DerivedIndexing.rightDerivedIso
        (sectionsFunctor X'.toRingedSpace.carrier ⊤) i).hom.app
        ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).X p) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        ((sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f')
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p).hom)) =
    (Stacks.DerivedIndexing.rightDerivedIso
        (sectionsFunctor X.toRingedSpace.carrier ⊤) i).hom.app _ ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f)
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p).hom)) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (formsExtendPushforwardUnderlying g f' f h w p))) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        (Scheme.Hom.pushforwardPullback g
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
            (moduleComplexPlus (X := X'.toRingedSpace)
              (A := (TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf)
              (SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f')
                (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p)))) := by
  have hnat := congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
    (Scheme.Hom.pushforwardPullback_naturality g
      (hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f')
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p).hom)
  rw [Functor.map_comp, Functor.map_comp] at hnat
  have hsq : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
      ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map
          ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
              (formsAbelianPushforward g f' f h w p) ≫
            (Stacks.DerivedIndexing.mapSinglePlus (abelianPushforward.{u, u} g.base) 0).app
              ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f')
                (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))).X p)))) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            ((abelianPushforward.{u, u} g.base).mapCochainComplexPlus.map
              (hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f')
                (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p).hom))) =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f)
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p).hom)) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (formsExtendPushforwardUnderlying g f' f h w p))) := by
    have h1 := congrArg (fun t =>
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map t))) (formsExtendPushforward_square g f' f h w p)
    simp only [Functor.map_comp, Category.assoc] at h1 ⊢
    exact h1.trans (map_map_map_comp _ _)
  refine ((reassoc_of% (abelianEdgeMap_formsAbelianPushforward_rightDerivedIso
    g f' f h w p i)) _).trans ?_
  refine (congrArg (_ ≫ _ ≫ ·) hnat.symm).trans ?_
  exact congrArg (_ ≫ ·) ((reassoc_of% hsq) _)

/-! ### The comparison of the two realizations carries one pullback to the other -/

/-- **The comparison of the two realizations of `H^i(X, Ω^p_{X/S})` carries the abelian pullback
to the module pullback**: for a commutative square `g ≫ f = f' ≫ h` of schemes, the map induced
on `R^iΓ` by the canonical map `Ω^p_{X/S} ⟶ g_*Ω^p_{X'/S'}` followed by the Leray edge map is
carried by `AlgebraicGeometry.SheafOfModules.hodgeComponentAbelianIso` on `X` and on `X'` to the
pullback `Stacks.HodgeWeil.hodgePullback` on the module realization. -/
theorem hodgeComponentAbelianIso_hodgePullback (p i : ℕ)
    (y : ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerived i).obj
      ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))).X p)) :
    (SheafOfModules.hodgeComponentAbelianIso (X := X'.toRingedSpace)
        (Scheme.Hom.deRhamAlgebras f')
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p i i rfl).hom.hom
      ((abelianEdgeMap.{u, u} g.base i).app _
        ((abelianCohomology.{u, u} _ ⊤ i).map (formsAbelianPushforward g f' f h w p) y)) =
    hodgePullback g f' f h w p i
      ((SheafOfModules.hodgeComponentAbelianIso (X := X.toRingedSpace)
        (Scheme.Hom.deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p i i rfl).hom.hom
        y) := by
  have T := ConcreteCategory.congr_hom
    (abelianEdgeMap_formsAbelianPushforward_hodgeSingleUnderlyingIso g f' f h w p i) y
  simp only [ConcreteCategory.comp_apply] at T
  have hχ : (formsExtendPushforward g f' f h w p).hom ≫
      (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (inverseImageBaseMap g f' f h w)).map (formsSingleExtendIso f' p).hom =
      (formsSingleExtendIso f p).hom ≫ formsSinglePushforward g f' f h w p := by
    change ((formsSingleExtendIso f p).hom ≫ formsSinglePushforward g f' f h w p ≫
      (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (inverseImageBaseMap g f' f h w)).map (formsSingleExtendIso f' p).inv) ≫ _ = _
    exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (inverseImageBaseMap g f' f h w)).mapIso (formsSingleExtendIso f' p)).inv_hom_id).trans
        (Category.comp_id _))))
  refine (hodgeComponentAbelianIso_hom_apply (Y := X'.toRingedSpace) _ _ p i _).trans ?_
  refine (congrArg (fun t =>
    (SheafOfModules.hodgeComponentIso (Scheme.Hom.deRhamAlgebras f') p i).hom.hom
      ((Stacks.Cech.Hypercohomology.realizationUnbounded
        (SheafOfModules.baseRingedSpace
          ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf))
        (moduleComplexPlus (X := X'.toRingedSpace)
          (A := (TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf)
          (SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f')
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p)) i).hom.hom t))
      T).trans ?_
  refine (congrArg (SheafOfModules.hodgeComponentIso (Scheme.Hom.deRhamAlgebras f') p i).hom.hom
    (realizationUnbounded_pushforwardPullback g f' f h w _ i _)).trans ?_
  have hN := ConcreteCategory.congr_hom
    (Stacks.Cech.Hypercohomology.realizationUnbounded_naturality (inverseImageBase f)
      (formsExtendPushforward g f' f h w p) i)
    (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
      ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (hodgeSingleUnderlyingIso (Scheme.Hom.deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) p).hom))).hom
      ((Stacks.DerivedIndexing.rightDerivedIso
        (sectionsFunctor X.toRingedSpace.carrier ⊤) i).hom.app _ y))
  refine (congrArg (fun t =>
    (SheafOfModules.hodgeComponentIso (Scheme.Hom.deRhamAlgebras f') p i).hom.hom
      ((Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso (inverseImageBaseMap g f' f h w)
        (DerivedCategory.Q.obj (moduleComplexPlus (X := X'.toRingedSpace)
          (A := (TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf)
          (SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f')
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) p)).obj) i).hom
        (((DerivedCategory.homologyFunctor _ (i : ℤ)).map
          ((Stacks.Cohomology.GlobalKunneth.baseSections (inverseImageBase f)).map
            (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
              (inverseImageBaseMap g f' f h w) (moduleComplexPlus (X := X'.toRingedSpace)
                (A := (TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf)
                (SheafOfModules.hodgeSingle (Scheme.Hom.deRhamAlgebras f')
                  (SheafOfModules.deRhamDifferential
                    (Scheme.Hom.deRhamAlgebras f')) p)).obj))).hom t))) hN).trans ?_
  refine Eq.trans ?_ (congrArg (hodgePullback g f' f h w p i)
    (hodgeComponentAbelianIso_hom_apply (Y := X.toRingedSpace) _ _ p i y).symm)
  refine Eq.trans ?_ (cohomologyPullback_naturality (inverseImageBaseMap g f' f h w)
    (formsExtendPushforward g f' f h w p).hom (formsSinglePushforward g f' f h w p)
    (formsSingleExtendIso f p).hom (formsSingleExtendIso f' p).hom hχ i _).symm
  exact congrArg (fun t =>
    (SheafOfModules.hodgeComponentIso (Scheme.Hom.deRhamAlgebras f') p i).hom.hom
      ((Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso
        (inverseImageBaseMap g f' f h w) _ i).hom t))
    (Stacks.Cohomology.HomologyPullback.map_map_comp_apply
      (Stacks.Cohomology.GlobalKunneth.baseSections (inverseImageBase f))
      (DerivedCategory.homologyFunctor _ (i : ℤ))
      (DerivedCategory.Q.map (formsExtendPushforward g f' f h w p).hom)
      (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
        (inverseImageBaseMap g f' f h w) _) _).symm

/-- **The identification `H¹(X, Ω_{X/S}) ≅ H¹(X, Ω¹_{X/S})` carries the abelian pullback to the
module pullback**: `hodgeCohomologyOneIsoComponent` on `X'` after the pullback
`AlgebraicGeometry.Scheme.Hom.hodgeCohomologyOnePullback` of the abelian realization is the
pullback `Stacks.HodgeWeil.hodgePullback` in bidegree `(1, 1)` after
`hodgeCohomologyOneIsoComponent` on `X`. -/
theorem hodgeCohomologyOneIsoComponent_hodgeCohomologyOnePullback
    (x : Scheme.Hom.hodgeCohomologyOne f) :
    (hodgeCohomologyOneIsoComponent f').hom.hom
        ((Scheme.Hom.hodgeCohomologyOnePullback g f f' h w).hom x) =
      hodgePullback g f' f h w 1 1 ((hodgeCohomologyOneIsoComponent f).hom.hom x) := by
  let genX := (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
    (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials f))
  let genX' := (_root_.SheafOfModules.toSheaf X'.ringCatSheaf).map
    (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials f'))
  have e1 : ∀ z, (hodgeCohomologyOneIsoComponent f').hom.hom z =
      (SheafOfModules.hodgeComponentAbelianIso (X := X'.toRingedSpace)
        (Scheme.Hom.deRhamAlgebras f')
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) 1 1 1 rfl).hom.hom
        ((abelianCohomology.{u, u} _ ⊤ 1).map genX' z) := fun _ => rfl
  have e2 : (hodgeCohomologyOneIsoComponent f).hom.hom x =
      (SheafOfModules.hodgeComponentAbelianIso (X := X.toRingedSpace)
        (Scheme.Hom.deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) 1 1 1 rfl).hom.hom
        ((abelianCohomology.{u, u} _ ⊤ 1).map genX x) := rfl
  have e3 : (Scheme.Hom.hodgeCohomologyOnePullback g f f' h w).hom x =
      (abelianEdgeMap.{u, u} g.base 1).app _ ((abelianCohomology.{u, u} _ ⊤ 1).map
        (Scheme.Hom.relativeDifferentialsPushforwardSheafHom g f f' h w) x) := rfl
  have hnat := ConcreteCategory.congr_hom
    ((abelianEdgeMap.{u, u} g.base 1).naturality genX')
    (((abelianCohomology.{u, u} _ ⊤ 1).map
      (Scheme.Hom.relativeDifferentialsPushforwardSheafHom g f f' h w)) x)
  have hsq : Scheme.Hom.relativeDifferentialsPushforwardSheafHom g f f' h w ≫
      (abelianPushforward.{u, u} g.base).map genX' =
      genX ≫ formsAbelianPushforward g f' f h w 1 :=
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map_comp _ _).symm.trans
      ((congrArg (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
        (relativeDifferentialsPushforwardMap_exteriorGenerator g f' f h w)).trans
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map_comp _ _))
  have hH := ConcreteCategory.congr_hom
    (((abelianCohomology.{u, u} _ ⊤ 1).map_comp _ _).symm.trans
      ((congrArg (abelianCohomology.{u, u} _ ⊤ 1).map hsq).trans
        ((abelianCohomology.{u, u} _ ⊤ 1).map_comp _ _))) x
  have core := hodgeComponentAbelianIso_hodgePullback g f' f h w 1 1
    ((abelianCohomology.{u, u} _ ⊤ 1).map genX x)
  simp only [ConcreteCategory.comp_apply] at hnat hH
  refine (e1 _).trans (Eq.trans ?_ (core.trans (congrArg _ e2.symm)))
  refine congrArg (SheafOfModules.hodgeComponentAbelianIso (X := X'.toRingedSpace)
    _ _ 1 1 1 rfl).hom.hom ?_
  rw [e3]
  exact hnat.symm.trans (congrArg ((abelianEdgeMap.{u, u} g.base 1).app _).hom hH)

/-! ### Axiom (A2) -/

/-- **The module-realization Hodge first Chern class commutes with pullback** ([Stacks,
Tag 0FMD], axiom (A2) of Section 0FID for Hodge cohomology, Remark 0FWE): for a commutative
square `g ≫ f = f' ≫ h` of schemes, the pullback `H¹(X, Ω¹_{X/S}) ⟶ H¹(X', Ω¹_{X'/S'})` of
`c₁^{Hodge}` of a Picard class is `c₁^{Hodge}` of its pullback. -/
theorem hodgePullback_hodgeFirstChernClassModule (c : Stacks.Picard.ofScheme X) :
    hodgePullback g f' f h w 1 1 (hodgeFirstChernClassModule f c) =
      hodgeFirstChernClassModule f' (Stacks.Picard.schemePullbackClassHom g c) := by
  have h1 := hodgeFirstChernClassModule_schemePullbackClassHom f g f' h w c
  have h2 := hodgeCohomologyOneIsoComponent_hodgeCohomologyOnePullback g f' f h w
    ((hodgeCohomologyOneIsoComponent f).inv.hom (hodgeFirstChernClassModule f c))
  have h3 : (hodgeCohomologyOneIsoComponent f).hom.hom
      ((hodgeCohomologyOneIsoComponent f).inv.hom (hodgeFirstChernClassModule f c)) =
      hodgeFirstChernClassModule f c :=
    ConcreteCategory.congr_hom (hodgeCohomologyOneIsoComponent f).inv_hom_id _
  rw [h1, h2, h3]

/-- **Axiom (A2) for Hodge cohomology, on invertible modules**: `f^*c₁^{Hodge}(ℒ) =
c₁^{Hodge}(f^*ℒ)` for an invertible `𝒪_X`-module `ℒ`, in the spelling
`Stacks.WeilCohomology.picardClassOf` of `Stacks.WeilCohomology.FirstChernClassData.PullbackAxiom`,
the pulled-back module being invertible by `Stacks.WeilCohomology.isInvertible_pullback_obj`. -/
theorem hodgePullback_hodgeFirstChernClassModule_picardClassOf (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    hodgePullback g f' f h w 1 1
        (hodgeFirstChernClassModule f (Stacks.WeilCohomology.picardClassOf X L hL)) =
      hodgeFirstChernClassModule f'
        (Stacks.WeilCohomology.picardClassOf X' ((Scheme.Modules.pullback g).obj L)
          (Stacks.WeilCohomology.isInvertible_pullback_obj g L hL)) :=
  (hodgePullback_hodgeFirstChernClassModule g f' f h w _).trans
    (congrArg (hodgeFirstChernClassModule f') (Stacks.Picard.pullbackClass_classOf _ L _))

end Stacks.HodgeWeil

end
