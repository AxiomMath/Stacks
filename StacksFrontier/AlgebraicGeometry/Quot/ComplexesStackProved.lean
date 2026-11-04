module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDescentBridges
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDiagonalReduction
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackPerfectDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackPushoutGluing
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackRelativelyPerfectColimit
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackThickeningPerfectProved
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualProved

/-!
# Stacks 0DLG, 0DLJ, 0DLH and 0DLK with the inputs proved on this branch discharged

The proofs of Stacks 0DLG, 0DLJ, 0DLH and 0DLK on this branch take Stacks 0DKW, 0DLC, 0DLD
and 0DL4 as hypotheses. These are now proved with no pending input
(`StacksFrontier/AlgebraicGeometry/Quot/RelativeDerivedHomDualProved.lean`,
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackThickeningPerfectProved.lean` and
`AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectColimit_proved`). This file
discharges them.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.complexes_hasRepresentableDiagonal_proved`:
  **Stacks 0DLG**.
* `AlgebraicGeometry.Space.ComplexesSituation.isLimitPreserving_complexes`: **Stacks 0DLJ**.
* `AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectColimit_baseChanges`: Stacks 0DKW
  for the base changes of Situation 0DLE, the form Stacks 0DLJ consumes.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesFunctor_isStackInGroupoids_of_cechDescent`:
  Stacks 0DLH, granted only Stacks 0DLA (Čech case; not yet proved here). Not registered.
* `Space.ComplexesSituation.isEquivalence_complexesFiberSquareComparison_of_pushouts`
  and `satisfiesRS_complexesFunctor_of_pushouts`: Stacks 0DLK and the condition (RS) it gives,
  granted only Stacks 07W3 and 0DL7. Not registered.

## References

* [Stacks Project, Tag 0DLG](https://stacks.math.columbia.edu/tag/0DLG)
* [Stacks Project, Tag 0DLJ](https://stacks.math.columbia.edu/tag/0DLJ)
* [Stacks Project, Tag 0DLH](https://stacks.math.columbia.edu/tag/0DLH)
* [Stacks Project, Tag 0DLK](https://stacks.math.columbia.edu/tag/0DLK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory instModulesHasDerivedCategory

variable (D : ComplexesSituation B S hS)

/-! ### Stacks 0DLG -/

/-- **Stacks 0DLG.** In Situation 0DLE (`f : X ⟶ Y` proper, flat and of finite presentation),
the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` of `𝒳 = Complexes_{X/Y}` is representable by algebraic spaces:
`AlgebraicGeometry.Space.ComplexesSituation.complexes_hasRepresentableDiagonal` with Stacks 0DLC,
parts (1) and (3), discharged. -/
@[stacks 0DLG]
theorem complexes_hasRepresentableDiagonal_proved :
    Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D)
        (complexesFunctor_isFiberedInGroupoids D)) :=
  complexes_hasRepresentableDiagonal D (existsNegativeExtLocus_proved B S hS)
    (relativeDerivedHomRepresentableOfFibres_proved B S hS) _

/-! ### Stacks 0DLJ -/

/-- **Stacks 0DKW for the base changes of Situation 0DLE**, in the shape
`AlgebraicGeometry.Space.ComplexesSituation.RelativelyPerfectColimit` that the proof of
Stacks 0DLJ consumes:
`AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectColimit_of_relativeDescentSituation`
with Stacks 0DKW in Situation 0DKU discharged by
`AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectColimit_proved`. -/
theorem relativelyPerfectColimit_baseChanges : D.RelativelyPerfectColimit :=
  D.relativelyPerfectColimit_of_relativeDescentSituation fun _ _ _ D' =>
    D'.relativelyPerfectColimit_proved

/-- **Stacks 0DLJ.** In Situation 0DLE assume that `Y ⟶ S` is locally of finite presentation.
Then `p : Complexes_{X/Y} ⥤ (Sch/S)_fppf` is limit preserving (Stacks 07XL):
`AlgebraicGeometry.Space.ComplexesSituation.isLimitPreserving_of_existsNegativeExtLocus` with
Stacks 0DKW and Stacks 0DLC (1) discharged. -/
@[stacks 0DLJ]
theorem isLimitPreserving_complexes
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1)) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D)
        (complexesFunctor_isFiberedInGroupoids D)) :=
  isLimitPreserving_of_existsNegativeExtLocus hY D.relativelyPerfectColimit_baseChanges
    (existsNegativeExtLocus_proved B S hS)

/-! ### Stacks 0DLH -/

/-- **Stacks 0DLH, granted Stacks 0DLA** (unregistered): `Complexes_{X/Y}` is a stack in
groupoids over `(Sch/S)_fppf`, given the Čech case of Stacks 0DLA (`h0DLA`, not yet proved here).
`Space.ComplexesSituation.complexesFunctor_isStackInGroupoids_of_remaining_pending`
with Stacks 0DLG
(`AlgebraicGeometry.Space.ComplexesSituation.complexes_hasRepresentableDiagonal_proved`), Stacks
0DLD (b) at `V = T`
(`AlgebraicGeometry.Space.ComplexesSituation.hasNoNegativeSelfExt_of_negativeExtVanishesOfFibres`)
and Stacks 0DLC (1)
(`AlgebraicGeometry.Space.ComplexesSituation.noNegativeFibreExtDescends_of_existsNegativeExtLocus`)
discharged. -/
theorem complexesFunctor_isStackInGroupoids_of_cechDescent (h0DLA : D.CechDescent) :
    (complexesFunctor D).IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS) :=
  complexesFunctor_isStackInGroupoids_of_remaining_pending (D := D)
    D.complexes_hasRepresentableDiagonal_proved h0DLA
    (D.hasNoNegativeSelfExt_of_negativeExtVanishesOfFibres
      (negativeExtVanishesOfFibres_proved B S hS))
    (D.noNegativeFibreExtDescends_of_existsNegativeExtLocus (existsNegativeExtLocus_proved B S hS))

/-! ### Stacks 0DLK -/

/-- **Stacks 0DLK, granted Stacks 07W3 and 0DL7** (unregistered). In Situation 0DLE, let
`i ≫ a = f ≫ b` be a commutative square of the site whose image in schemes is a pushout
`Y' = Y ⨿_Z Z'` along the finite order thickening `i : Z ⟶ Z'` and the affine morphism
`f : Z ⟶ Y`. Then the functor on fibre categories
`Complexes_{X/B, Y'} ⟶ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}` is an
equivalence, given `h07W3` (Stacks 07W3, not yet proved here) and `h0DL7` (Stacks 0DL7, not yet
proved here):
`AlgebraicGeometry.Space.ComplexesSituation.isEquivalence_complexesFiberSquareComparison` with
Stacks 0DLG and Stacks 0DL4 discharged. -/
theorem isEquivalence_complexesFiberSquareComparison_of_pushouts
    (h07W3 : ∀ {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y')
      (b : Y ⟶ Y'),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) →
      IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) →
      ∀ {W WY WZ' WZ : AlgebraicSpaces B S hS} (π : W ⟶ schemeSpace Y')
        (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
        (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ'),
        IsFlat B S hS π.hom →
        IsPullback n πY π (schemeSpaceMap b) → IsPullback m πZ' π (schemeSpaceMap a) →
        IsPullback l πZ πY (schemeSpaceMap f) → k ≫ πZ' = πZ ≫ schemeSpaceMap i →
        l ≫ n = k ≫ m → IsPushout k l m n)
    (h0DL7 : ∀ {P P' Q Q' : AlgebraicSpaces B S hS} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B S hS k → IsAffineHom B S hS l.hom →
      ∀ (M : derivedModules B S hS Q) (K' : derivedModules B S hS P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B S hS).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B S hS).pull k).obj K',
          ∃ (N : derivedModules B S hS Q')
            (eQ : ((smallEtaleDerivedPullbackData B S hS).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B S hS).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B S hS).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B S hS).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B S hS).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B S hS).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B S hS).pull k).map eP'.hom)
    {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : (complexesFunctor D).IsFibered := (complexesFunctor_isFiberedInGroupoids D).isFibered
    (Deformation.Artin.fiberSquareComparison (complexesFunctor D)
      (Functor.chosenPullbacks (complexesFunctor D)) f i b a w.symm).IsEquivalence :=
  isEquivalence_complexesFiberSquareComparison D (complexesFunctor_isFiberedInGroupoids D)
    D.complexes_hasRepresentableDiagonal_proved h07W3 h0DL7
    (fun h hfin E' E e hE =>
      D.isRelativelyPerfect_of_isFiniteOrderThickening_proved h hfin E' E e hE)
    i f a b w hi hpush

/-- **Condition (RS) for `Complexes_{X/B}`, granted Stacks 07W3 and 0DL7** (unregistered): the
hypothesis `h0DLK` of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`,
`AlgebraicGeometry.Space.ComplexesSituation.satisfiesRS_complexesFunctor` with Stacks 0DLG and
Stacks 0DL4 discharged. The two hypotheses are those of
`Space.ComplexesSituation.isEquivalence_complexesFiberSquareComparison_of_pushouts`. -/
theorem satisfiesRS_complexesFunctor_of_pushouts
    (h07W3 : ∀ {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y')
      (b : Y ⟶ Y'),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) →
      IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) →
      ∀ {W WY WZ' WZ : AlgebraicSpaces B S hS} (π : W ⟶ schemeSpace Y')
        (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
        (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ'),
        IsFlat B S hS π.hom →
        IsPullback n πY π (schemeSpaceMap b) → IsPullback m πZ' π (schemeSpaceMap a) →
        IsPullback l πZ πY (schemeSpaceMap f) → k ≫ πZ' = πZ ≫ schemeSpaceMap i →
        l ≫ n = k ≫ m → IsPushout k l m n)
    (h0DL7 : ∀ {P P' Q Q' : AlgebraicSpaces B S hS} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B S hS k → IsAffineHom B S hS l.hom →
      ∀ (M : derivedModules B S hS Q) (K' : derivedModules B S hS P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B S hS).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B S hS).pull k).obj K',
          ∃ (N : derivedModules B S hS Q')
            (eQ : ((smallEtaleDerivedPullbackData B S hS).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B S hS).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B S hS).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B S hS).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B S hS).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B S hS).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B S hS).pull k).map eP'.hom) :
    Deformation.Artin.SatisfiesRS B S hS (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) :=
  satisfiesRS_complexesFunctor D (complexesFunctor_isFiberedInGroupoids D)
    D.complexes_hasRepresentableDiagonal_proved h07W3 h0DL7
    (fun h hfin E' E e hE =>
      D.isRelativelyPerfect_of_isFiniteOrderThickening_proved h hfin E' E e hE)

end AlgebraicGeometry.Space.ComplexesSituation

end
