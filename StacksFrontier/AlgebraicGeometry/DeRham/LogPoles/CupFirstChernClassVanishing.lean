module

public import StacksFrontier.AlgebraicGeometry.DeRham.ClosedImmersionPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueBoundaryChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DivisorChernClassCup
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DivisorDeRhamPushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ResidueLogPolesMorphism

/-!
# Cup product with the first Chern class of a divisor kills classes vanishing on it

Let `p : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor for which the
de Rham complex of log poles is defined (Tag 0FMV). **Stacks Tag 0FMX** says that if
`b ∈ H^m_{dR}(X/S)` restricts to zero on `Y`, then

`c₁^{dR}(𝒪_X(Y)) ∪ b = 0` in `H^{m + 2}_{dR}(X/S)`.

The source's proof is the chain

`c₁^{dR}(𝒪_X(Y)) ∪ b = -c₁^{dR}(𝒪_X(-Y)) ∪ b = -ξ'(b) = -δ(b|_Y) = 0`,

and each link is a declaration of the library:

* `c₁^{dR}(𝒪_X(Y)) = -c₁^{dR}(𝒪_X(-Y))`:
  `AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass_invertibleSheaf`, and the
  cup product is additive in its first variable (Tag 0FM3);
* `ξ ∪ b = ξ'(b)`, Remark 0FU7 property (3):
  `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_eq_deRhamClassMorphism`;
* `ξ'` is the boundary of the residue sequence of `𝒪_X(-Y)` (Tag 0FUG,
  `Stacks.LineBundle.Situation.residueShiftedSequence_boundary_eq_deRhamClassMorphism`), and that
  boundary is `δ ∘ (restriction of forms)`, the upper left triangle of Tag 0FUQ
  (`Stacks.LineBundle.residueShiftedSequence_boundary_eq`);
* the restriction of forms `Ω^•_{X/S} ⟶ ι_*Ω^•_{Y/S}` kills `b` because `b|_Y = 0`: the pullback
  along the closed immersion `ι : Y ⟶ X` is that map followed by an isomorphism
  (`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback_apply_eq_zero_iff`), carried to the
  sheaf-of-modules realization by
  `AlgebraicGeometry.SheafOfModules.derivedSectionsBase_map_realization_eq_zero` along the
  identification of this file.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.divisorDeRhamPlus`, `AlgebraicGeometry.Scheme.Hom
  .divisorRestrictionPlus`: `Ω^•_{Y/S}` read on `X` and the restriction of forms, as bounded below
  complexes of sheaves of `p^{-1}𝒪_S`-modules.
* `AlgebraicGeometry.Scheme.Hom.divisorDeRhamPlusAbelianIso`: the direct image
  `ι_*Ω^•_{Y/S}` of abelian sheaves is the underlying complex of `Ω^•_{Y/S}` read on `X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMapPlus_comp_divisorDeRhamPlusAbelianIso`:
  under that identification the canonical map `Ω^•_{X/S} ⟶ ι_*Ω^•_{Y/S}` of Tag 07HX is the
  restriction of forms.
* `AlgebraicGeometry.Scheme.Hom.deRhamCohomologyCup_firstChernClass_eq_zero`: **Tag 0FMX.**

## Implementation notes

**The statement.** `H^m_{dR}(X/S)` is `AlgebraicGeometry.SheafOfModules.deRhamCohomology`, the
cohomology of `RΓ(X, Ω^•_{X/S})` computed in sheaves of `p^{-1}𝒪_S`-modules, the realization in
which the cup product of Tag 0FM3 is defined. The restriction of `b` to `Y` is the pullback map
`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback` of Section 0FL6 along the square
`Y ⟶ X` over `S`, which is defined in the abelian-sheaf realization; `b` is carried there by the
comparison `AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology` of Tag
01F1. `𝒪_X(Y)` is `Stacks.Divisors.invertibleSheaf'`, the dual of the ideal sheaf (Tag 01WX).

**The model of the derived category.** The morphisms of Tag 0FU7 are built on
`HasDerivedCategory.standard`. The upper left triangle of Tag 0FUQ is stated for any model; the
proof instantiates it at the standard one by a local `letI`, and the statement itself involves no
derived category.

## References

* [Stacks Project, Tag 0FMX](https://stacks.math.columbia.edu/tag/0FMX)
* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree

variable {X S : Scheme.{u}} (p : X ⟶ S) (Y : X.IdealSheafData)

/-- `Ω^•_{Y/S}` read on `X`, as a bounded below complex of sheaves of `p^{-1}𝒪_S`-modules. -/
def divisorDeRhamPlus :
    CochainComplex.Plus (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf))) :=
  ⟨divisorDeRhamInt p Y, 0, by
    change CochainComplex.IsStrictlyGE ((divisorDeRhamBase p Y).extend
      ComplexShape.embeddingUpNat) 0
    infer_instance⟩

/-- The restriction of forms `Ω^•_{X/S} ⟶ Ω^•_{Y/S}`, as a morphism of bounded below complexes. -/
def divisorRestrictionPlus :
    SheafOfModules.deRhamComplexPlus (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) ⟶ divisorDeRhamPlus p Y :=
  ObjectProperty.homMk (divisorRestrictionInt p Y)

/-- The direct image `ι_*Ω^•_{Y/S}` of abelian sheaves is the underlying complex of abelian sheaves
of `Ω^•_{Y/S}` read on `X`. -/
def divisorDeRhamPlusAbelianIso :
    deRhamPushforwardPlus Y.subschemeι (Y.subschemeι ≫ p) ≅
      (_root_.SheafOfModules.toSheaf (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf))).mapCochainComplexPlus.obj
        (divisorDeRhamPlus p Y) :=
  ObjectProperty.isoMk _
    ((HomologicalComplex.mapHomologicalComplexExtendIso (abelianPushforward.{u, u}
        Y.subschemeι.base) _ ComplexShape.embeddingUpNat).symm ≪≫
      (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (divisorDeRhamAbIso p Y).symm ≪≫
      HomologicalComplex.mapHomologicalComplexExtendIso _ (divisorDeRhamBase p Y)
        ComplexShape.embeddingUpNat)

/-- **Under `AlgebraicGeometry.Scheme.Hom.divisorDeRhamPlusAbelianIso`, the
canonical map `Ω^•_{X/S} ⟶ ι_*Ω^•_{Y/S}` of Tag 07HX is the restriction of forms.** -/
theorem deRhamAbelianPushforwardMapPlus_comp_divisorDeRhamPlusAbelianIso :
    deRhamAbelianPushforwardMapPlus Y.subschemeι p (Y.subschemeι ≫ p) (𝟙 S) (by simp) ≫
        (divisorDeRhamPlusAbelianIso p Y).hom =
      (SheafOfModules.deRhamAbelianComplexPlusIso (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).hom ≫
        (_root_.SheafOfModules.toSheaf (SheafOfModules.underlyingRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf))).mapCochainComplexPlus.map
          (divisorRestrictionPlus p Y) := by
  refine ObjectProperty.hom_ext _ ?_
  have h1 : deRhamAbelianPushforwardMap Y.subschemeι p (Y.subschemeι ≫ p) (𝟙 S) (by simp) ≫
      (divisorDeRhamAbIso p Y).inv =
      ((_root_.SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (divisorRestrictionBase p Y) :=
    (Iso.comp_inv_eq _).2 (toSheaf_divisorRestrictionBase_comp_divisorDeRhamAbIso p Y).symm
  show ((ComplexShape.embeddingUpNat.extendFunctor _).map
        (deRhamAbelianPushforwardMap Y.subschemeι p (Y.subschemeι ≫ p) (𝟙 S) (by simp)) ≫
      (HomologicalComplex.mapHomologicalComplexExtendIso _ _ ComplexShape.embeddingUpNat).hom) ≫
      ((HomologicalComplex.mapHomologicalComplexExtendIso _ _ ComplexShape.embeddingUpNat).inv ≫
        (ComplexShape.embeddingUpNat.extendFunctor _).map (divisorDeRhamAbIso p Y).inv ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso _ (divisorDeRhamBase p Y)
          ComplexShape.embeddingUpNat).hom) =
    (HomologicalComplex.mapHomologicalComplexExtendIso _ _ ComplexShape.embeddingUpNat).hom ≫
      ((_root_.SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap (divisorRestrictionBase p Y) ComplexShape.embeddingUpNat)
  have h2 : (ComplexShape.embeddingUpNat.extendFunctor _).map
        (deRhamAbelianPushforwardMap Y.subschemeι p (Y.subschemeι ≫ p) (𝟙 S) (by simp)) ≫
      (ComplexShape.embeddingUpNat.extendFunctor _).map (divisorDeRhamAbIso p Y).inv =
      HomologicalComplex.extendMap (((_root_.SheafOfModules.toSheaf _).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (divisorRestrictionBase p Y)) ComplexShape.embeddingUpNat := by
    rw [← Functor.map_comp, h1]
    rfl
  rw [CochainComplex.mapHomologicalComplexExtendIso_hom_naturality, ← h2]
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _))).trans
    (Category.assoc _ _ _).symm

section Vanishing

variable [Stacks.Divisors.IsEffectiveCartierDivisor Y]

/-- **Stacks Project, Tag 0FMX.** Let `p : X ⟶ S` be a morphism of schemes and let `Y ⊆ X` be an
effective Cartier divisor for which the de Rham complex of log poles is defined over `S`. If a
class `b ∈ H^m_{dR}(X/S)` restricts to zero on `Y`, then

`c₁^{dR}(𝒪_X(Y)) ∪ b = 0`

in `H^{2 + m}_{dR}(X/S)`. The restriction of `b` is its image under the pullback map
`H^m_{dR}(X/S) ⟶ H^m_{dR}(Y/S)` of the closed immersion `Y ⟶ X`. -/
@[stacks 0FMX]
theorem deRhamCohomologyCup_firstChernClass_eq_zero (hlog : p.HasLogPolesDeRhamComplex Y)
    (m : ℤ)
    (b : SheafOfModules.deRhamCohomology (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) m)
    (hb : (deRhamCohomologyPullback Y.subschemeι p (Y.subschemeι ≫ p) (𝟙 S)
      (Category.comp_id _).symm m).hom
        ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) m).inv.hom b) = 0) :
    SheafOfModules.deRhamCohomologyCup (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) 2 m
        (SheafOfModules.deRhamCohomologyFirstChernClass (X := X.toRingedSpace) (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))
          (Stacks.Divisors.invertibleSheaf' Y) inferInstance) b = 0 := by
  set e := SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) m
  have hbb : b = e.hom.hom (e.inv.hom b) := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  have hr := (deRhamCohomologyPullback_apply_eq_zero_iff Y.subschemeι p (Y.subschemeι ≫ p) (𝟙 S)
    (Category.comp_id _).symm m _).1 hb
  have h0 := SheafOfModules.derivedSectionsBase_map_realization_eq_zero (deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) (divisorRestrictionPlus p Y)
    (divisorDeRhamPlusAbelianIso p Y) _
    (deRhamAbelianPushforwardMapPlus_comp_divisorDeRhamPlusAbelianIso p Y) m _ hr
  rw [← hbb] at h0
  let cupB := AddMonoidHom.mk' (fun ξ => SheafOfModules.deRhamCohomologyCup (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) 2 m ξ b)
    (fun x y => SheafOfModules.deRhamCohomologyCup_add_left _ _ 2 m x y b)
  show cupB _ = 0
  rw [SheafOfModules.deRhamCohomologyFirstChernClass_invertibleSheaf, map_neg, neg_eq_zero]
  show SheafOfModules.deRhamCohomologyCup _ _ 2 m _ b = 0
  rw [SheafOfModules.deRhamCohomologyCup_eq_deRhamClassMorphism,
    ← Stacks.LineBundle.Situation.residueShiftedSequence_boundary_eq_deRhamClassMorphism
      (Stacks.LineBundle.idealSituation p Y)]
  let _ : HasDerivedCategory (_root_.SheafOfModules.{u} (baseRingSheaf p)) :=
    HasDerivedCategory.standard _
  rw [Stacks.LineBundle.residueShiftedSequence_boundary_eq p Y hlog]
  exact (congrArg _ (SheafOfModules.derivedSectionsBase_homology_map_comp_apply_eq_zero _ _ m b
    h0)).trans (map_zero _)

end Vanishing

end AlgebraicGeometry.Scheme.Hom
