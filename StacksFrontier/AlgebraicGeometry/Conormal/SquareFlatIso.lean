module

public import StacksFrontier.AlgebraicGeometry.Conormal.DegreeOne
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.BaseChange

/-!
# Flat base change of the conormal sheaf of an immersion

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a cartesian square of schemes with `i` and `i'` immersions. The canonical map
`f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 01R4] is surjective, which is
`Stacks.Immersion.epi_immersionConormalSheafMap`; this file proves that it is an isomorphism when
`g` is flat.

## Main results

* `Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat`: the canonical map is an
  isomorphism when `g` is flat.
* `Stacks.Immersion.immersionConormalSheafMap_eq_degreeOne`: the canonical map is the degree-one
  component of the canonical morphism of graded conormal algebras, read through the degree-one
  identifications.

## Implementation notes

The canonical map is identified, by the uniqueness clause
`Stacks.Immersion.immersionConormalSheafMap_unique`, with the degree-one component of the
canonical morphism of graded conormal algebras, for which the flat base-change isomorphism is
`AlgebraicGeometry.conormalAlgebraMap_isIso_of_flat`.

`Stacks.Conormal.conormalDegreeOneIso` is `no_expose`, so `Stacks.Immersion.degreeOneIso`
re-forms the isomorphism from `Stacks.Conormal.conormalDegreeOneHom` and its invertibility. The
affine formula for the degree-one comparison is the definition
`Stacks.Immersion.IsDegreeOneAffineFormulaAt`, abstracted over the affine open and its
affineness: instantiating the formula itself at an anonymous constructor exhausts the
elaborator's recursion budget inside the affine identification.

## References

* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
* [Stacks Project, Tag 0635](https://stacks.math.columbia.edu/tag/0635)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.Conormal
open Stacks.ClosedImmersion.AffineConormal Stacks.ClosedImmersion.IdealSheafAffine

universe u

namespace Stacks.Immersion

variable {Z X Z' X' : Scheme.{u}}

/-- The degree-one identification `𝒞_{Z/X} ≅ 𝒞_{Z/X,1}` of [Stacks Project, Tag 0632], with
forward direction `Stacks.Conormal.conormalDegreeOneHom`. -/
private def degreeOneIso (i : Z ⟶ X) [IsImmersion i] :
    Stacks.ClosedImmersion.conormalSheaf i.liftCoborder.toLRSHom.toShHom ≅
      AlgebraicGeometry.conormalPiece i 1 :=
  @asIso _ _ _ _ (Stacks.Conormal.conormalDegreeOneHom i)
    (Stacks.Conormal.conormalDegreeOneHom_isIso i)

/-- The map `f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of conormal sheaves of a commutative square given by the
degree-one component of the canonical morphism of graded conormal algebras of
[Stacks Project, Tag 0634], conjugated by the degree-one identifications of
[Stacks Project, Tag 0632] on both sides. -/
private def squareMapOfConormalAlgebra (i : Z ⟶ X) (i' : Z' ⟶ X') [IsImmersion i] [IsImmersion i']
    (f : Z ⟶ Z') (g : X ⟶ X') (comm : i ≫ g = f ≫ i') :
    (modulePullback f.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.conormalSheaf i'.liftCoborder.toLRSHom.toShHom) ⟶
      Stacks.ClosedImmersion.conormalSheaf i.liftCoborder.toLRSHom.toShHom :=
  (modulePullback f.toLRSHom.toShHom).map (degreeOneIso i').hom ≫
    (AlgebraicGeometry.canonicalPullbackHom i i' f g comm.symm).hom 1 ≫
      (degreeOneIso i).inv

/-- `Stacks.Immersion.squareMapOfConormalAlgebra` is an isomorphism for a flat base change. -/
private theorem isIso_squareMapOfConormalAlgebra (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsImmersion i] [IsImmersion i']
    (f : Z ⟶ Z') (g : X ⟶ X') [Flat g] (sq : IsPullback i f g i') :
    IsIso (squareMapOfConormalAlgebra i i' f g sq.w) := by
  have h : IsIso ((AlgebraicGeometry.canonicalPullbackHom i i' f g sq.w.symm).hom 1) :=
    AlgebraicGeometry.conormalAlgebraMap_isIso_of_flat i i' f g sq 1
  have h1 : IsIso ((modulePullback f.toLRSHom.toShHom).map
      (degreeOneIso i').hom) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom _)
  have h2 : IsIso ((degreeOneIso i).inv) := Iso.isIso_inv _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (@IsIso.comp_isIso _ _ _ _ _ _ _ h h2)

/-- The affine formula for the degree-one comparison of [Stacks Project, Tag 0632], over one
affine open and in the vocabulary of `Stacks.Conormal.affineConormalIsoCotangent`: the comparison
carries the class in `I/I²` of `c ∈ I` to the degree-one local associated-graded class of `c`. -/
private def IsDegreeOneAffineFormulaAt (i : Z ⟶ X) [IsImmersion i] (U : X.Opens)
    (hU : IsAffineOpen U) : Prop :=
  ∀ (hcl : IsClosedImmersion (i.resLE U (i ⁻¹ᵁ U) le_rfl))
    (I : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (quotRing I))
    (he : pullback.snd i U.ι ≫ hU.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, U) I)
    (c : I) (hc : (c : Γ(X, U)) ∈ chartIdeal i ⟨U, hU⟩ ^ 1),
    (Stacks.Conormal.conormalDegreeOneHom i).val.app (op (i ⁻¹ᵁ U))
        ((Stacks.Conormal.affineConormalIsoCotangent i U hU I e he).inv.hom (I.toCotangent c))
      = (Stacks.Conormal.conormalAlgebra i).localMap ⟨U, hU⟩ hcl 1 ⟨(c : Γ(X, U)), hc⟩

/-- The affine formula for the degree-one comparison of [Stacks Project, Tag 0632] in the
vocabulary of `Stacks.Conormal.affineConormalIsoCotangent`, over every affine open. -/
private def IsDegreeOneAffineFormula (i : Z ⟶ X) [IsImmersion i] : Prop :=
  ∀ (U : X.Opens) (hU : IsAffineOpen U), IsDegreeOneAffineFormulaAt i U hU

/-- The chart ideal of an immersion over an affine open is the ideal of any affine model. -/
private theorem chartIdeal_eq_of_affineModel (i : Z ⟶ X) [IsImmersion i] (U : X.Opens)
    (hU : IsAffineOpen U) (I : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (quotRing I))
    (he : pullback.snd i U.ι ≫ hU.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, U) I) :
    chartIdeal i ⟨U, hU⟩ = I := by
  rw [chartIdeal, Scheme.Hom.app_eq_appLE]
  exact ker_appLE_eq_of_affineModel i U hU I e he

/-- The restriction of an immersion over an affine open with an affine model is a closed
immersion. -/
private theorem isClosedImmersion_resLE_of_affineModel (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (quotRing I))
    (he : pullback.snd i U.ι ≫ hU.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, U) I) :
    IsClosedImmersion (i.resLE U (i ⁻¹ᵁ U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact isClosedImmersion_morphismRestrict_of_affineModel i U hU I e he

/-- `Stacks.Immersion.squareMapOfConormalAlgebra` satisfies the affine characterisation of
[Stacks Project, Tag 01R4]: over a compatible pair of affine charts its transpose carries the
class of `a ∈ J` to the class of `g^♯ a`. -/
private theorem isInducedConormalSheafMap_squareMapOfConormalAlgebra (i : Z ⟶ X)
    (i' : Z' ⟶ X') [IsImmersion i] [IsImmersion i']
    (f : Z ⟶ Z') (g : X ⟶ X') (comm : i ≫ g = f ≫ i')
    (hi : IsDegreeOneAffineFormula i) (hi' : IsDegreeOneAffineFormula i') :
    Stacks.Immersion.IsInducedConormalSheafMap i i' f g comm
      (squareMapOfConormalAlgebra i i' f g comm) := by
  intro U hU V hV hUV I J eZ heZ eW heW a b hab
  have hclU := isClosedImmersion_resLE_of_affineModel i U hU I eZ heZ
  have hclV := isClosedImmersion_resLE_of_affineModel i' V hV J eW heW
  have ha1 : (a : Γ(X', V)) ∈ chartIdeal i' ⟨V, hV⟩ ^ 1 := by
    rw [pow_one, chartIdeal_eq_of_affineModel i' V hV J eW heW]; exact a.2
  have hb1 : (b : Γ(X, U)) ∈ chartIdeal i ⟨U, hU⟩ ^ 1 := by
    rw [pow_one, chartIdeal_eq_of_affineModel i U hU I eZ heZ]; exact b.2
  have hST : i ⁻¹ᵁ U ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ V) :=
    Stacks.Immersion.preimage_le_preimage_of_square comm U V hUV
  have hΦ : ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
        (squareMapOfConormalAlgebra i i' f g comm)) =
      (degreeOneIso i').hom ≫
        (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _)
          ((AlgebraicGeometry.canonicalPullbackHom i i' f g comm.symm).hom 1)) ≫
        (modulePushforward f.toLRSHom.toShHom).map
          (degreeOneIso i).inv := by
    have h1 := (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv_naturality_left
      (degreeOneIso i').hom
      ((AlgebraicGeometry.canonicalPullbackHom i i' f g comm.symm).hom 1 ≫
        (degreeOneIso i).inv)
    have h2 := (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv_naturality_right
      ((AlgebraicGeometry.canonicalPullbackHom i i' f g comm.symm).hom 1)
      (degreeOneIso i).inv
    exact h1.trans (congrArg
      (fun z => (degreeOneIso i').hom ≫ z) h2)
  have eA : ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
        (squareMapOfConormalAlgebra i i' f g comm)).val.app (op (i' ⁻¹ᵁ V))
          ((Stacks.Conormal.affineConormalIsoCotangent i' V hV J eW heW).inv.hom
            (J.toCotangent a)) =
      (degreeOneIso i).inv.val.app (op (f ⁻¹ᵁ (i' ⁻¹ᵁ V)))
        ((((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _)
            ((AlgebraicGeometry.canonicalPullbackHom i i' f g comm.symm).hom 1)).val.app
          (op (i' ⁻¹ᵁ V))
          ((Stacks.Conormal.conormalDegreeOneHom i').val.app (op (i' ⁻¹ᵁ V))
            ((Stacks.Conormal.affineConormalIsoCotangent i' V hV J eW heW).inv.hom
              (J.toCotangent a)))) := by
    rw [hΦ]
    rfl
  have eB : (Stacks.Conormal.conormalDegreeOneHom i').val.app (op (i' ⁻¹ᵁ V))
        ((Stacks.Conormal.affineConormalIsoCotangent i' V hV J eW heW).inv.hom (J.toCotangent a)) =
      (Stacks.Conormal.conormalAlgebra i').localMap ⟨V, hV⟩ hclV 1
        ⟨(a : Γ(X', V)), ha1⟩ :=
    hi' V hV hclV J eW heW a ha1
  have eC := (AlgebraicGeometry.canonicalPullbackHom i i' f g comm.symm).agrees 1 (i' ⁻¹ᵁ V)
    ((Stacks.Conormal.conormalAlgebra i').localMap ⟨V, hV⟩ hclV 1 ⟨(a : Γ(X', V)), ha1⟩)
  have eD := AlgebraicGeometry.conormalHomSection_restrict_target i i' f
    (AlgebraicGeometry.conormalAlgebraHom i i' f g comm.symm).hom 1
    (f ⁻¹ᵁ (i' ⁻¹ᵁ V)) (i ⁻¹ᵁ U) hST (i' ⁻¹ᵁ V) le_rfl
    ((Stacks.Conormal.conormalAlgebra i').localMap ⟨V, hV⟩ hclV 1 ⟨(a : Γ(X', V)), ha1⟩)
  have eE := (AlgebraicGeometry.conormalAlgebraHom i i' f g comm.symm).chart
    ⟨U, hU⟩ ⟨V, hV⟩ hUV hclU hclV hST 1
    ⟨(a : Γ(X', V)), ha1⟩ ⟨(b : Γ(X, U)), hb1⟩ hab
  have eF := hi U hU hclU I eZ heZ b hb1
  have e1 : (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _)
          ((AlgebraicGeometry.canonicalPullbackHom i i' f g comm.symm).hom 1)).val.app
        (op (i' ⁻¹ᵁ V))
        ((Stacks.Conormal.conormalDegreeOneHom i').val.app (op (i' ⁻¹ᵁ V))
          ((Stacks.Conormal.affineConormalIsoCotangent i' V hV J eW heW).inv.hom
            (J.toCotangent a))) =
      (AlgebraicGeometry.conormalAlgebraHom i i' f g comm.symm).hom.map 1
        (f ⁻¹ᵁ (i' ⁻¹ᵁ V)) (i' ⁻¹ᵁ V) le_rfl
        ((Stacks.Conormal.conormalAlgebra i').localMap ⟨V, hV⟩ hclV 1
          ⟨(a : Γ(X', V)), ha1⟩) := by
    rw [eB]
    exact eC
  have einner : (AlgebraicGeometry.conormalPiece i 1).val.map (homOfLE hST).op
        ((((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _)
            ((AlgebraicGeometry.canonicalPullbackHom i i' f g comm.symm).hom 1)).val.app
          (op (i' ⁻¹ᵁ V))
          ((Stacks.Conormal.conormalDegreeOneHom i').val.app (op (i' ⁻¹ᵁ V))
            ((Stacks.Conormal.affineConormalIsoCotangent i' V hV J eW heW).inv.hom
              (J.toCotangent a)))) =
      (Stacks.Conormal.conormalAlgebra i).localMap ⟨U, hU⟩ hclU 1
        ⟨(b : Γ(X, U)), hb1⟩ := by
    rw [e1]
    exact eD.trans eE
  refine Eq.trans (val_map_congr _ eA) ?_
  refine Eq.trans (val_app_naturality (degreeOneIso i).inv
    (homOfLE hST) _).symm ?_
  refine Eq.trans (congrArg
    (fun z => ((degreeOneIso i).inv.val.app (op (i ⁻¹ᵁ U))) z)
    einner) ?_
  rw [← eF]
  exact congrArg (fun k : Stacks.ClosedImmersion.conormalSheaf
      i.liftCoborder.toLRSHom.toShHom ⟶ _ => k.val.app (op (i ⁻¹ᵁ U))
    ((Stacks.Conormal.affineConormalIsoCotangent i U hU I eZ heZ).inv.hom (I.toCotangent b)))
    (degreeOneIso i).hom_inv_id

/-- The affine formula for the degree-one comparison, in the vocabulary of
`Stacks.Conormal.affineConormalIsoCotangent`, over one affine open. -/
private theorem isDegreeOneAffineFormulaAt (i : Z ⟶ X) [IsImmersion i] (Ua : X.affineOpens) :
    IsDegreeOneAffineFormulaAt i Ua.1 Ua.2 := by
  intro hcl I e he c hc
  have hI := chartIdeal_eq_of_affineModel i Ua.1 Ua.2 I e he
  subst hI
  exact Stacks.Conormal.conormalDegreeOneHom_localMap i Ua hcl e he c

/-- The affine formula for the degree-one comparison, over every affine open. -/
private theorem isDegreeOneAffineFormula (i : Z ⟶ X) [IsImmersion i] : IsDegreeOneAffineFormula i :=
  fun U hU => isDegreeOneAffineFormulaAt i ⟨U, hU⟩

/-- For a cartesian square of schemes whose horizontal maps `i` and `i'` are immersions and
whose ambient vertical map `g` is flat, the canonical map `f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of
[Stacks Project, Tag 01R4] is an isomorphism. -/
@[stacks 0473 "flat base change"]
theorem isIso_immersionConormalSheafMap_of_flat (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsImmersion i] [IsImmersion i']
    (f : Z ⟶ Z') (g : X ⟶ X') [Flat g] (sq : IsPullback i f g i') :
    IsIso (Stacks.Immersion.immersionConormalSheafMap i i' f g
      (Stacks.Immersion.toShHom_square sq.w)) := by
  have heq := Stacks.Immersion.immersionConormalSheafMap_unique i i' f g sq.w
    (squareMapOfConormalAlgebra i i' f g sq.w)
    (isInducedConormalSheafMap_squareMapOfConormalAlgebra i i' f g sq.w
      (isDegreeOneAffineFormula i) (isDegreeOneAffineFormula i'))
  rw [← heq]
  exact isIso_squareMapOfConormalAlgebra i i' f g sq

/-- For a commutative square of immersions, the canonical map `f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of
conormal sheaves is the degree-one component of the canonical morphism of conormal algebras,
read through the degree-one identifications of [Stacks Project, Tag 0632] on both sides. -/
theorem immersionConormalSheafMap_eq_degreeOne (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsImmersion i] [IsImmersion i'] (f : Z ⟶ Z') (g : X ⟶ X') (comm : i ≫ g = f ≫ i') :
    Stacks.Immersion.immersionConormalSheafMap i i' f g (Stacks.Immersion.toShHom_square comm) =
      (modulePullback f.toLRSHom.toShHom).map (Stacks.Conormal.conormalDegreeOneHom i') ≫
        (AlgebraicGeometry.canonicalPullbackHom i i' f g comm.symm).hom 1 ≫
          @inv _ _ _ _ (Stacks.Conormal.conormalDegreeOneHom i)
            (Stacks.Conormal.conormalDegreeOneHom_isIso i) :=
  (Stacks.Immersion.immersionConormalSheafMap_unique i i' f g comm
    (squareMapOfConormalAlgebra i i' f g comm)
    (isInducedConormalSheafMap_squareMapOfConormalAlgebra i i' f g comm
      (isDegreeOneAffineFormula i) (isDegreeOneAffineFormula i'))).symm

end Stacks.Immersion

end
