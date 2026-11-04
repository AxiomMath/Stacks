module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityProved
public import StacksFrontier.Deformation.Artin.FormalObject.Effectiveness
public import StacksFrontier.Deformation.Artin.Versality.OpennessOfVersality
public import StacksFrontier.RingTheory.Nilpotent.Ideal

/-!
# Openness of versality for `Complexes_{X/S}`

The last paragraph of the proof of Stacks 0DLN: for `S = Spec Λ` with `Λ` of finite type over `ℤ`
and `Y = S`, the category `Complexes_{X/S}` satisfies openness of versality, by Stacks 0CXU. Its
diagonal is representable by algebraic spaces (Stacks 0DLG), it has (RS*) (Stacks 0DLK), it is
limit preserving (Stacks 0DLJ), and it is strongly formally effective (Stacks 0DLM).

This is Stacks 0CXU at terminal `Y`, the case the proof of Stacks 0DLN uses. The proof takes
Stacks 0DIQ, 07W3 and 0DL7 as hypotheses.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.openVersality_complexes_of_isTerminal`: openness
  of versality for `Complexes_{X/S}` at terminal `Y`, granted Stacks 0DIQ, 07W3 and 0DL7.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0DLM](https://stacks.math.columbia.edu/tag/0DLM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}}

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

attribute [local instance] complexesCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- **Stacks 0CXU for `Complexes_{X/S}`, at terminal `Y`, the case the source uses.** For `Λ` of
finite type over `ℤ` and Situation 0DLE over `S = Spec Λ` with `Y` final, `Complexes_{X/Y}`
satisfies openness of versality: an object over a scheme `U` locally of finite type over `S` which
is versal at a finite type point `u` is versal at every finite type point of an open neighbourhood
of `u`.

It is `Deformation.Artin.isOpenVersality_of_isSquareZeroEffective` (Stacks 0CXU) with
* the diagonal from Stacks 0DLG
  (`AlgebraicGeometry.Space.ComplexesSituation.complexes_hasRepresentableDiagonal_proved`);
* (RS*) from Stacks 0DLK
  (`AlgebraicGeometry.Space.ComplexesSituation.satisfiesRSStar_complexesFunctor`);
* limit preservation from Stacks 0DLJ
  (`AlgebraicGeometry.Space.ComplexesSituation.isLimitPreserving_complexes`);
* condition (4) from the strong formal effectiveness of Stacks 0DLM, a square-zero kernel being
  locally nilpotent (`Ideal.Nilpotent.locallyNilpotent`)
  (`AlgebraicGeometry.Space.ComplexesSituation.isStronglyFormallyEffective_complexes_of`).

The remaining hypotheses:
* `h0DIQ`: Stacks 0DIQ;
* `h07W3`: Stacks 07W3;
* `h0DL7`: Stacks 0DL7. -/
theorem openVersality_complexes_of_isTerminal
    (h0DIQ : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
      (L : D.SpecLimitTower level transition)
      (K : ∀ n, derivedModules B _ hΛ (D.space (level n))),
      (∀ n, (smallEtaleRingedSite B _ hΛ (D.space (level n)).1
        (D.space (level n)).2).IsPseudoCoherent (K n)) →
      ∀ (φ : ∀ n, ((smallEtaleDerivedPullbackData B _ hΛ).pull
        (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n), (∀ n, IsIso (φ n)) →
      ∃ (E : derivedModules B _ hΛ (D.space L.T)),
        (smallEtaleRingedSite B _ hΛ (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
        ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B _ hΛ).pull
          (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
          ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
              (ψ (n + 1)) =
            (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n)
    (h07W3 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      {Z Z' Y Y' : BigFppfOver B _ hΛ} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y'),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B _ hΛ).map i) →
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B _ hΛ).map f) →
      IsPushout ((BigFppfOver.toScheme B _ hΛ).map i) ((BigFppfOver.toScheme B _ hΛ).map f)
        ((BigFppfOver.toScheme B _ hΛ).map a) ((BigFppfOver.toScheme B _ hΛ).map b) →
      ∀ {W WY WZ' WZ : AlgebraicSpaces B _ hΛ} (π : W ⟶ schemeSpace Y')
        (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
        (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ'),
        IsFlat B _ hΛ π.hom →
        IsPullback n πY π (schemeSpaceMap b) → IsPullback m πZ' π (schemeSpaceMap a) →
        IsPullback l πZ πY (schemeSpaceMap f) → k ≫ πZ' = πZ ≫ schemeSpaceMap i →
        l ≫ n = k ≫ m → IsPushout k l m n)
    (h0DL7 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      {P P' Q Q' : AlgebraicSpaces B _ hΛ} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B _ hΛ k → IsAffineHom B _ hΛ l.hom →
      ∀ (M : derivedModules B _ hΛ Q) (K' : derivedModules B _ hΛ P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B _ hΛ).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B _ hΛ).pull k).obj K',
          ∃ (N : derivedModules B _ hΛ Q')
            (eQ : ((smallEtaleDerivedPullbackData B _ hΛ).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B _ hΛ).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B _ hΛ).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B _ hΛ).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B _ hΛ).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B _ hΛ).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B _ hΛ).pull k).map eP'.hom) :
    ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ),
      IsTerminal D.Y → ∀ (U : Over (Spec (CommRingCat.of Λ))), LocallyOfFiniteType U.hom →
      ∀ (y : ComplexesObject D) (hy : (complexesFunctor D ⋙ Over.post B.inclusion).obj y = U)
        (u : U.left), _root_.AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u' y
              hy := by
  intro Λ _ _ hΛ D hY
  have : IsNoetherianRing Λ := Algebra.FiniteType.isNoetherianRing ℤ Λ
  have hfib := complexesFunctor_isFiberedInGroupoids D
  have h0DLG := complexes_hasRepresentableDiagonal_proved D
  have hSFE := isStronglyFormallyEffective_complexes_of (D := D) (h0DIQ Λ hΛ D)
    (existsNegativeExtLocus_proved B _ hΛ) hY
  intro U hU y hy u hu hv
  exact isOpenVersality_of_isSquareZeroEffective.{u, u + 1, u + 1} B _ hΛ
    (CatFiberedInGroupoids.mk (complexesBasedCategory D) hfib) h0DLG
    (satisfiesRSStar_complexesFunctor D hfib h0DLG (h07W3 Λ hΛ) (h0DL7 Λ hΛ)
      (fun h hfin E' E e hE => D.isRelativelyPerfect_of_isFiniteOrderThickening_proved h hfin E' E
        e hE))
    (isLimitPreserving_complexes D (isLocallyOfFinitePresentation_terminal_from_of_isTerminal hY))
    (fun Λ' _ chart _ R cR hcR hsurj hsq => hSFE Λ' chart R cR hcR hsurj
      (fun f => Ideal.Nilpotent.locallyNilpotent ⟨2, hsq f⟩))
    U hU y hy u hu hv

end AlgebraicGeometry.Space.ComplexesSituation

end
