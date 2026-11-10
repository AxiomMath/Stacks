module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityFibreFinite
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackProved

/-!
# Algebraicity of `Complexes_{X/Y}` from the remaining hypotheses

In the namespace `AlgebraicGeometry.Space.ComplexesSituation`, the theorem
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt_properInSite` states
Stacks 0DLN under fourteen hypotheses. Five of them are theorems: Stacks 0DLC (2) at `W = Y`
(`h0DLC2`), Stacks 0DKY (`h0DKY`), Stacks 0DLC (3) at `W = Y` (`h0DLC3`), Stacks 0DKW for the
base changes of Situation 0DLE (`h0DKW`) and Stacks 0DL4 (`h0DL4`). This file discharges them.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_external`: Stacks
  0DLN, granted Stacks 0DLA (Čech case), `ChangeOfBaseComparison` (Stacks 04X4 for
  `Complexes`), Stacks 0DIQ, Stacks 07Y4, Stacks 0CXU, Stacks 07W3, Stacks 0DL7, and the two
  steps of Stacks 0DLL `AlgebraicGeometry.Space.ComplexesSituation.FibreTrivialAutNatural` and
  `AlgebraicGeometry.Space.ComplexesSituation.FibreLiftClassPullback`.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift

universe u z

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

/-- **Stacks 0DLN** under the remaining hypotheses. For every `S` in the site and every
Situation 0DLE over `S`, `Complexes_{X/Y}` is an algebraic stack. This is
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt_properInSite` with
`h0DLC2`, `h0DKY`, `h0DLC3`, `h0DKW` and `h0DL4` discharged by
`AlgebraicGeometry.Space.negativeExtVanishesOfFibres_proved`,
`AlgebraicGeometry.Space.relativeDerivedHomDualExists_proved`,
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_proved`,
`relativelyPerfectColimit_baseChanges` and
`isRelativelyPerfect_of_isFiniteOrderThickening_proved`.

The remaining hypotheses are:
* `h0DLA`: Stacks 0DLA (Čech case);
* `hcomp`: Stacks 04X4 for `Complexes` (`ChangeOfBaseComparison`);
* `h0DIQ`: Stacks 0DIQ;
* `h07Y4`: Stacks 07Y4 (Artin's criterion);
* `h0CXU`: Stacks 0CXU (openness of versality for `Complexes`);
* `h07W3`: Stacks 07W3;
* `h0DL7`: Stacks 0DL7;
* `hnat`, `hpull`: the steps `FibreTrivialAutNatural` and `FibreLiftClassPullback` of
  Stacks 0DLL. -/
theorem isAlgebraicStack_complexes_of_external
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
    (h07Y4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      (𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}
        (BigFppfOver B (Spec (CommRingCat.of Λ)) hΛ)),
      Stack.HasRepresentableDiagonal B _ hΛ 𝒳 →
      (∃ T : BigFppfOver B _ hΛ,
        ∀ (U : BigFppfOver B _ hΛ) (k : Type u) [Field k],
          U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B _ hΛ U →
          Cardinal.lift.{u, u + 1}
              (Cardinal.mk (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber U)))) ≤
            Cardinal.lift.{u + 1, u} T.left.1.size) →
      𝒳.val.p.IsStackInGroupoids.{u + 1} ((etaleTopology B).over (B.obj hΛ)) →
      Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B _ hΛ 𝒳 →
      Deformation.Artin.SatisfiesRS B _ hΛ 𝒳.val.p 𝒳.property →
      (∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ Spec (CommRingCat.of Λ))
          (x₀ : 𝒳.val.obj)
          (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
          LocallyOfFiniteType i₀ → QuasiCompact i₀ →
          ∀ (s : Spec (CommRingCat.of Λ)), i₀ (IsLocalRing.closedPoint k) = s →
          ∀ (Λ' : Type u) [CommRing Λ'] [Algebra Λ' k]
            (_hΛstalk : Λ' = (Spec (CommRingCat.of Λ)).presheaf.stalk s)
            (iΛ : Spec (.of Λ') ⟶ Spec (CommRingCat.of Λ))
            (_hiΛ : HEq iΛ ((Spec (CommRingCat.of Λ)).fromSpecStalk s))
            (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ = i₀),
            let hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ) :=
              hx₀.trans (congrArg Over.mk hbase.symm)
            let D := Deformation.Artin.predeformationCategory iΛ
              (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx
            letI : Category D.carrier := D.category
            ∀ hD : Deformation.IsDeformationCategory D.projection,
              let 𝓕 := BasedCategory.ofFunctor D.projection
              let hS2 :=
                schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
              letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
              letI : Fact (Deformation.SchlessingerConditionS2
                (Functor.Elements.π
                  (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
              let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
              let T := Deformation.artinianTangentSpace Λ' k F
              letI : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
              letI : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
              FiniteDimensional k T) →
      (∀ ξ : Deformation.Artin.FormalObject B _ hΛ 𝒳.val.p,
        Deformation.Artin.FormalObject.IsEffective B _ hΛ 𝒳.val.p 𝒳.property ξ) →
      (∀ U : Over (Spec (CommRingCat.of Λ)), LocallyOfFiniteType U.hom →
        ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
          _root_.AlgebraicGeometry.IsFiniteTypePoint u →
          Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
          ∃ V : U.left.Opens, u ∈ V.1 ∧
            ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
              Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy) →
      (∀ s : Spec (CommRingCat.of Λ), _root_.AlgebraicGeometry.IsFiniteTypePoint s →
        IsGRing ((Spec (CommRingCat.of Λ)).presheaf.stalk s)) →
      Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ 𝒳.val)
    (h0CXU : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      (U : Over (Spec (CommRingCat.of Λ))), LocallyOfFiniteType U.hom →
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
  isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt_properInSite hnat hpull
    hcomp (fun hS => negativeExtVanishesOfFibres_proved B _ hS)
    (fun hS => relativeDerivedHomDualExists_proved B _ hS)
    (fun hS => relativeDerivedHomRepresentableOfFibres_proved B _ hS)
    (fun _ D => D.relativelyPerfectColimit_baseChanges) h0DIQ h0DLA h07Y4 h0CXU h07W3 h0DL7
    (fun _ _ _ _ D _ _ h hfin E' E e hE =>
      D.isRelativelyPerfect_of_isFiniteOrderThickening_proved h hfin E' E e hE)
    hS D

end AlgebraicGeometry.Space.ComplexesSituation

end
