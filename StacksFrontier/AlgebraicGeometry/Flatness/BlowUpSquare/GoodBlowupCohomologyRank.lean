module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.BlowupSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartDecalage
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.DivisorRankStrata
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupLocallyFree
import all StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.BlowupSubscheme

/-!
# Ranks of the cohomology of `Lb^*M` over the locally free locus

Let `(X, D, M)` be a triple as in Situation 0F8S, `W ⊆ X` the maximal open over which the
cohomology sheaves of `M` are locally free, and `b : X' ⟶ X` a morphism for which
`b⁻¹W ↪ X' ⟶ X` is flat, for instance the morphism of tag 0GTY (by tag 0F8W).  At a point
`y ∈ b⁻¹W` the stalk of `H^n(Lb^*M)` is finite free of the same rank as `H^n(M)_{b(y)}`.

## Main definitions

* `Stacks.BlowUpComplexes.homologyUniqIso`: the cohomology of an object of the derived category
  does not depend on the model of the derived category.

## Main results

In the namespace `AlgebraicGeometry.ComplexAndDivisorSituation`:

* `freeAndFiniteStalk_and_finrank_homology_derivedPullbackObject`: the statement above.
* `freeAndFiniteStalk_and_finrank_homology_goodBlowup`: the statement for the morphism of tag
  0GTY.

## Implementation notes

Over the flat composite `j ≫ b`, with `j` the inclusion of `b⁻¹W`, `H^n(L(j ≫ b)^*M)` is the
pullback of `H^n(M)`, whose stalk is a base change of `H^n(M)_{b(y)}` (Stacks 0098); derived
pullback along `j ≫ b` is derived pullback along `b` followed by `j` (Stacks 0D5S); and along the
open immersion `j` the germ map is bijective, so the stalk of `H^n(Lb^*M)` at `y` is recovered.

## References

* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe w₁ w₂ v u d

namespace Stacks.BlowUpComplexes

/-- The cohomology of an object of the derived category of an abelian category does not depend
on the model of the derived category: it is the cohomology of a representing complex in both. -/
def homologyUniqIso {C : Type u} [Category.{v} C] [Abelian C] (h₁ : HasDerivedCategory.{w₁} C)
    (h₂ : HasDerivedCategory.{w₂} C) (K : @DerivedCategory C _ _ h₁) (n : ℤ) :
    (@DerivedCategory.homologyFunctor C _ _ h₁ n).obj K ≅
      (@DerivedCategory.homologyFunctor C _ _ h₂ n).obj
        ((Localization.uniq (@DerivedCategory.Q _ _ _ h₁) (@DerivedCategory.Q _ _ _ h₂)
          (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))).functor.obj K) :=
  ((@DerivedCategory.homologyFunctor _ _ _ h₁ n).mapIso
      ((@DerivedCategory.Q _ _ _ h₁).objObjPreimageIso K)).symm ≪≫
    (@DerivedCategory.homologyFunctorFactors _ _ _ h₁ n).app
      ((@DerivedCategory.Q _ _ _ h₁).objPreimage K) ≪≫
    ((@DerivedCategory.homologyFunctorFactors _ _ _ h₂ n).app
      ((@DerivedCategory.Q _ _ _ h₁).objPreimage K)).symm ≪≫
    (@DerivedCategory.homologyFunctor _ _ _ h₂ n).mapIso
      (((Localization.compUniqFunctor (@DerivedCategory.Q _ _ _ h₁)
            (@DerivedCategory.Q _ _ _ h₂)
            (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))).app
          ((@DerivedCategory.Q _ _ _ h₁).objPreimage K)).symm ≪≫
        (Localization.uniq (@DerivedCategory.Q _ _ _ h₁) (@DerivedCategory.Q _ _ _ h₂)
            (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))).functor.mapIso
          ((@DerivedCategory.Q _ _ _ h₁).objObjPreimageIso K))

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
  [Limits.PreservesFiniteLimits (modulePullback f)]
  [Limits.PreservesFiniteColimits (modulePullback f)]

/-- **Finite free cohomology stalks and their ranks are carried by an exact pullback.**  If
`H^n(E)` has a finite free stalk at `f x`, then `H^n(Lf^*E) = f^*H^n(E)` has a finite free stalk
at `x`, of the same rank (the local ring at `x` being nonzero): it is the base change of the
stalk of `H^n(E)` (Stacks 0098). -/
theorem freeAndFiniteStalk_and_finrank_homology_derivedPullback
    (E : DerivedCategory (OXMod.{u, u} Y)) (x : X.carrier) (n : ℤ)
    [Nontrivial (ToType (X.presheaf.stalk x))]
    (h : RingedSpace.FreeAndFiniteStalk
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) n).obj E) (f.hom.base x)) :
    RingedSpace.FreeAndFiniteStalk
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).obj ((derivedPullback f).obj E)) x ∧
      Module.finrank (ToType (X.presheaf.stalk x))
          (ToType (TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor (OXMod.{u, u} X)
            n).obj ((derivedPullback f).obj E)).val.presheaf x)) =
        Module.finrank (ToType (Y.presheaf.stalk (f.hom.base x)))
          (ToType (TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y)
            n).obj E).val.presheaf (f.hom.base x))) := by
  let : Algebra (ToType (Y.presheaf.stalk (f.hom.base x))) (ToType (X.presheaf.stalk x)) :=
    (f.hom.stalkMap x).hom.toAlgebra
  obtain ⟨e⟩ := exists_pullbackStalkLinearEquiv f _
    (homologyDerivedPullbackIso f E n) x
  have : Nontrivial (ToType (Y.presheaf.stalk (f.hom.base x))) :=
    (f.hom.stalkMap x).hom.domain_nontrivial
  have _ := h.1
  have _ := h.2
  exact ⟨⟨Module.Free.of_equiv' inferInstance e.symm, Module.Finite.equiv e.symm⟩,
    e.finrank_eq.trans (Module.finrank_baseChange (R := ToType (X.presheaf.stalk x)))⟩

/-- **Finite free cohomology stalks and their ranks descend along an exact pullback whose germ
map at `x` is bijective**, for instance along an open immersion, the local ring at `x` being
nonzero. -/
theorem freeAndFiniteStalk_and_finrank_homology_of_derivedPullback
    (E : DerivedCategory (OXMod.{u, u} Y)) (x : X.carrier) (n : ℤ)
    [Nontrivial (ToType (X.presheaf.stalk x))]
    (hbij : Function.Bijective (f.hom.stalkMap x).hom)
    (h : RingedSpace.FreeAndFiniteStalk
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).obj ((derivedPullback f).obj E)) x) :
    RingedSpace.FreeAndFiniteStalk
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) n).obj E) (f.hom.base x) ∧
      Module.finrank (ToType (X.presheaf.stalk x))
          (ToType (TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor (OXMod.{u, u} X)
            n).obj ((derivedPullback f).obj E)).val.presheaf x)) =
        Module.finrank (ToType (Y.presheaf.stalk (f.hom.base x)))
          (ToType (TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y)
            n).obj E).val.presheaf (f.hom.base x))) := by
  have h' := freeAndFiniteStalk_of_freeAndFiniteStalk_of_iso_modulePullback f _
    (homologyDerivedPullbackIso f E n) x hbij h
  exact ⟨h', (freeAndFiniteStalk_and_finrank_homology_derivedPullback f E x n h').2⟩

end Stacks.BlowUpComplexes

namespace AlgebraicGeometry.ComplexAndDivisorSituation

open Stacks.BlowUpComplexes

variable (S : ComplexAndDivisorSituation.{u, d})

/-- At a point `y` of `b⁻¹W`, where `b⁻¹W ↪ X' ⟶ X` is flat, the stalk of `H^n(Lb^*M)` is finite
free of the rank of `H^n(M)_{b(y)}`. -/
theorem freeAndFiniteStalk_and_finrank_homology_derivedPullbackObject {X' : Scheme.{u}}
    (b : X' ⟶ S.X) (hflat : AlgebraicGeometry.Flat ((b ⁻¹ᵁ S.locallyFreeLocus).ι ≫ b))
    (y : X') (hy : b.base y ∈ S.locallyFreeLocus) (n : ℤ) :
    RingedSpace.FreeAndFiniteStalk
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X'.toRingedSpace) n).obj
          (S.derivedPullbackObject b)) y ∧
      Module.finrank (ToType (X'.presheaf.stalk y))
          (ToType (TopCat.Presheaf.stalk
            ((DerivedCategory.homologyFunctor (OXMod.{u, u} X'.toRingedSpace) n).obj
              (S.derivedPullbackObject b)).val.presheaf y)) =
        Module.finrank (ToType (S.X.presheaf.stalk (b.base y)))
          (ToType (TopCat.Presheaf.stalk (S.cohomologySheaf n).val.presheaf (b.base y))) := by
  let j := (b ⁻¹ᵁ S.locallyFreeLocus).ι
  let z : (b ⁻¹ᵁ S.locallyFreeLocus).toScheme := ⟨y, hy⟩
  let fj := j.toLRSHom.toShHom
  let fb := b.toLRSHom.toShHom
  have flat_exact : ∀ {A B : RingedSpace.{u, u}} (g : A ⟶ B), AlgebraicGeometry.IsFlat g →
      Limits.PreservesFiniteLimits (modulePullback g) ∧
        Limits.PreservesFiniteColimits (modulePullback g) := fun g hg =>
    ⟨preservesFiniteLimits_modulePullback_of_isFlat _ hg, preservesFiniteColimits_modulePullback _⟩
  obtain ⟨_, _⟩ := flat_exact (fj ≫ fb) (Flat.stalkMap (j ≫ b))
  obtain ⟨_, _⟩ := flat_exact fj (Flat.stalkMap j)
  let eM := homologyUniqIso S.hasDerivedCategory
    (HasDerivedCategory.standard (OXMod.{u, u} S.X.toRingedSpace)) S.M n
  have hE : RingedSpace.FreeAndFiniteStalk
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} S.X.toRingedSpace) n).obj S.standardM)
      ((fj ≫ fb).hom.base z) := FreeAndFiniteStalk.of_iso eM (hy n)
  -- along the flat composite `j ≫ b`
  obtain ⟨hA, rA⟩ := freeAndFiniteStalk_and_finrank_homology_derivedPullback (fj ≫ fb)
    S.standardM z n hE
  -- `L(j ≫ b)^* = Lj^* ∘ Lb^*`
  let eC := (DerivedCategory.homologyFunctor (OXMod.{u, u}
      (b ⁻¹ᵁ S.locallyFreeLocus).toScheme.toRingedSpace) n).mapIso
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical fj fb).app S.standardM)
  -- descent along the open immersion `j`
  obtain ⟨hB, rB⟩ := freeAndFiniteStalk_and_finrank_homology_of_derivedPullback fj
    (S.derivedPullbackObject b) z n
    ((ConcreteCategory.isIso_iff_bijective (j.stalkMap z)).1 inferInstance)
    (FreeAndFiniteStalk.of_iso eC.symm hA)
  exact ⟨hB, rB.symm.trans (((stalkLinearEquivOfIso eC z).finrank_eq.trans rA).trans
    (stalkLinearEquivOfIso eM ((fj ≫ fb).hom.base z)).finrank_eq.symm)⟩

/-- At a point `y` of `X'` over the locally free locus `W`, for the morphism `b` of tag 0GTY,
the stalk of `H^n(Lb^*M)` is finite free of the rank of `H^n(M)_{b(y)}`. -/
theorem freeAndFiniteStalk_and_finrank_homology_goodBlowup (y : S.goodBlowup)
    (hy : S.goodBlowupToBase.base y ∈ S.locallyFreeLocus) (n : ℤ) :
    RingedSpace.FreeAndFiniteStalk
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} S.goodBlowup.toRingedSpace) n).obj
          (S.derivedPullbackObject S.goodBlowupToBase)) y ∧
      Module.finrank (ToType (S.goodBlowup.presheaf.stalk y))
          (ToType (TopCat.Presheaf.stalk
            ((DerivedCategory.homologyFunctor (OXMod.{u, u} S.goodBlowup.toRingedSpace) n).obj
              (S.derivedPullbackObject S.goodBlowupToBase)).val.presheaf y)) =
        Module.finrank (ToType (S.X.presheaf.stalk (S.goodBlowupToBase.base y)))
          (ToType (TopCat.Presheaf.stalk (S.cohomologySheaf n).val.presheaf
            (S.goodBlowupToBase.base y))) :=
  S.freeAndFiniteStalk_and_finrank_homology_derivedPullbackObject S.goodBlowupToBase
    S.flat_ι_comp_goodBlowupToBase_locallyFreeLocus y hy n

end AlgebraicGeometry.ComplexAndDivisorSituation

end
