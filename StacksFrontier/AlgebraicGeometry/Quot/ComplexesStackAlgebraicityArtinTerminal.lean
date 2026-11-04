module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityArtin
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityProvedTerminal
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackOpennessOfVersality

/-!
# Stacks 0DLN with Stacks 07Y4 from the library and Stacks 0CXU proved

`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_external_of_baseArtin`
with the hypothesis `h0CXU` (Stacks 0CXU) asked only at a situation whose `Y` is terminal, the
case the source uses, and then with `h0CXU` discharged by
`AlgebraicGeometry.Space.ComplexesSituation.openVersality_complexes_of_isTerminal`. Nothing is
registered: Stacks 0DLN still carries results not yet proved here.

## Main results

* `ComplexesSituation.isAlgebraicStack_complexes_of_external_of_baseArtin_of_terminalVersality`:
  Stacks 0DLN with `h07Y4` discharged and `h0CXU` asked only at terminal `Y`.
* `ComplexesSituation.isAlgebraicStack_complexes_of_external_of_baseArtin_of_openVersality`:
  Stacks 0DLN with `h07Y4` and `h0CXU` discharged.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift

universe u z

namespace AlgebraicGeometry.Space

namespace ComplexesSituation

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

/-- **Stacks 0DLN, granted results not yet proved here and the two running Stacks 0DLL steps,
with Stacks 07Y4 from the library** (unregistered).
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_external` with `h07Y4`
discharged by `AlgebraicGeometry.Space.artinCriterion_overSpec_of_finiteType`.

The remaining hypotheses:
* `h0DLA`: Stacks 0DLA (Čech case), not yet proved here;
* `hcomp`: Stacks 04X4 for `Complexes` (`ChangeOfBaseComparison`), not yet proved here;
* `h0DIQ`: Stacks 0DIQ, not yet proved here;
* `h0CXU`: Stacks 0CXU at terminal Y, the case the source uses (openness of versality for
  `Complexes` when `Y` is final), not yet proved here;
* `h07W3`: Stacks 07W3, not yet proved here;
* `h0DL7`: Stacks 0DL7, not yet proved here;
* `hnat`, `hpull`: internal steps of Stacks 0DLL, being proved on this branch.

The hypothesis `h0CXU` is asked only at terminal `Y` (Stacks 0CXU at terminal Y, the case
the source uses); narrowing it strengthens the statement. -/
theorem isAlgebraicStack_complexes_of_external_of_baseArtin_of_terminalVersality
    (h0DLA : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.CechDescent)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
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
    (h0CXU : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ),
      IsTerminal D.Y → ∀ (U : Over (Spec (CommRingCat.of Λ))), LocallyOfFiniteType U.hom →
      ∀ (y : ComplexesObject D) (hy : (complexesFunctor D ⋙ Over.post B.inclusion).obj y = U)
        (u : U.left), _root_.AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u' y
              hy)
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
                ((smallEtaleDerivedPullbackData B _ hΛ).pull k).map eP'.hom)
    (hnat : ∀ {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)
      {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hk : B.Contains (Spec (.of k)))
      [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
      (hK : DerivedCategory.TStructure.t.minus x₀.E),
      FibreTrivialAutNatural (hDer' := hDer) (complexesFunctor_isFiberedInGroupoids D) hK)
    (hpull : ∀ {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)
      {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hk : B.Contains (Spec (.of k)))
      [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
      (hK : DerivedCategory.TStructure.t.minus x₀.E)
      (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧)),
      FibreLiftClassPullback (hDer := hDer) hK m hKm)
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_external_of_terminalVersality (h0CXU := h0CXU) h0DLA hcomp h0DIQ
    (artinCriterion_overSpec_of_finiteType B) h07W3 h0DL7 hnat hpull hS D

/-- **Stacks 0DLN, granted results not yet proved here and the two running Stacks 0DLL steps,
with Stacks 07Y4 from the library and Stacks 0CXU proved** (unregistered).
`isAlgebraicStack_complexes_of_external_of_baseArtin_of_terminalVersality` with `h0CXU`
(Stacks 0CXU at terminal Y, the case the source uses) discharged by
`openVersality_complexes_of_isTerminal`, from `h0DIQ`, `h07W3` and `h0DL7`.

The remaining hypotheses:
* `h0DLA`: Stacks 0DLA (Čech case), not yet proved here;
* `hcomp`: Stacks 04X4 for `Complexes` (`ChangeOfBaseComparison`), not yet proved here;
* `h0DIQ`: Stacks 0DIQ, not yet proved here;
* `h07W3`: Stacks 07W3, not yet proved here;
* `h0DL7`: Stacks 0DL7, not yet proved here;
* `hnat`, `hpull`: internal steps of Stacks 0DLL, being proved on this branch. -/
theorem isAlgebraicStack_complexes_of_external_of_baseArtin_of_openVersality
    (h0DLA : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.CechDescent)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
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
                ((smallEtaleDerivedPullbackData B _ hΛ).pull k).map eP'.hom)
    (hnat : ∀ {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)
      {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hk : B.Contains (Spec (.of k)))
      [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
      (hK : DerivedCategory.TStructure.t.minus x₀.E),
      FibreTrivialAutNatural (hDer' := hDer) (complexesFunctor_isFiberedInGroupoids D) hK)
    (hpull : ∀ {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)
      {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hk : B.Contains (Spec (.of k)))
      [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
      (hK : DerivedCategory.TStructure.t.minus x₀.E)
      (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧)),
      FibreLiftClassPullback (hDer := hDer) hK m hKm)
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_external_of_baseArtin_of_terminalVersality h0DLA hcomp h0DIQ
    (openVersality_complexes_of_isTerminal h0DIQ h07W3 h0DL7) h07W3 h0DL7 hnat hpull hS D

end ComplexesSituation

end AlgebraicGeometry.Space

end
