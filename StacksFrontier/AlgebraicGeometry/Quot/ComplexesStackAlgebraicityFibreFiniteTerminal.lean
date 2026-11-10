module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityFibreFinite
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityHeldFlatTerminal

/-!
# Stacks 0DLN with the fibre hypotheses of Stacks 0DLL discharged, asking Stacks 0CXU only at
terminal `Y`

The three forms of Stacks 0DLN of
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackAlgebraicityFibreFinite.lean`, with the
hypothesis `h0CXU` (Stacks 0CXU) asked only at a situation whose `Y` is terminal, the case the
source uses. They are proved as there, from
`ComplexesSituation.isAlgebraicStack_complexes_of_held_of_adjoinDescent_of_terminalVersality`.
Nothing is registered.

## Main results

In `AlgebraicGeometry.Space.ComplexesSituation`, the declarations named
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_` followed by

* `of_terminalVersality`: `Complexes_{X/Y}` is an algebraic stack;
* `finiteExt_of_terminalVersality`: the same, with the hypothesis `h0D0T` discharged;

and `isAlgebraicStack_complexes_of_fibreLiftPullback_finiteExt_properInSite_of_terminalVersality`:
the same, with `h0D0T` and `h08K1` discharged.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
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

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0DLN, granted results not yet proved here, with the fibre hypotheses of Stacks
0DLL discharged.** This is
`ComplexesSituation.isAlgebraicStack_complexes_of_held_of_adjoinDescent` with `h0DLLT` proved by
`AlgebraicGeometry.Space.ComplexesSituation.fibreTangentFinite_of_fibreLiftClassPullback` and
`h0DLLInf` by `ComplexesSituation.fibreInfFinite_of_fibreTrivialAutNatural`, from

* `h0D0T`: **Stacks 0D0T, not yet proved here**;
* `hpull`: the compatibility of the classes of lifts of `E₀⟦m⟧` with pullback of lifts of the
  base point of the fibre (`AlgebraicGeometry.Space.ComplexesSituation.FibreLiftClassPullback`),
  **internal, 0DLL-G4-2, pending**;
* `hnat`: the naturality of `g ↦ 1 + g` on the trivial deformations
  (`AlgebraicGeometry.Space.ComplexesSituation.FibreTrivialAutNatural`), **internal, pending**.

The other hypotheses are those of
`ComplexesSituation.isAlgebraicStack_complexes_of_held_of_adjoinDescent`, with the same marks;
condition (RS*) of `Complexes_{X/Y}` comes from `h0DKY`, `h0DLC3`, `h07W3`, `h0DL7` and `h0DL4`.

The hypothesis `h0CXU` is asked only at terminal `Y` (Stacks 0CXU at terminal Y, the case
the source uses); narrowing it strengthens the statement. -/
theorem isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_of_terminalVersality
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS)
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
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
    (h08K1 : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (hZ : B.Contains (⊤_ Scheme.{u})) (i : (Finset A)ᵒᵖ)
      {X Y : Over ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i)} (f : X ⟶ Y),
      IsQuasiCompactSpace B _ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAbsolutelyQuasiSeparated B _ hZ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAlgebraicSpace B _ hZ X.left → IsAlgebraicSpace B _ hZ Y.left →
      IsQuasiCompactSpace B _ hZ X.left → IsAbsolutelyQuasiSeparated B _ hZ hZ X.left →
      IsQuasiCompactSpace B _ hZ Y.left → IsAbsolutelyQuasiSeparated B _ hZ hZ Y.left →
      IsProper B _ hZ
        ((Over.pullback (limit.π (adjoinSiteDiagram B hZ A hA ⋙ yoneda) i)).map f).left →
      IsLocallyOfFiniteType B _ hZ f.left →
      ∃ (j : (Finset A)ᵒᵖ) (e : j ⟶ i),
        IsProper B _ hZ
          ((Over.pullback ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).map e)).map f).left)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLC2 : ∀ {S : Scheme.{u}} (hS : B.Contains S), NegativeExtVanishesOfFibres B S hS)
    (h0DKY : ∀ {S : Scheme.{u}} (hS : B.Contains S), RelativeDerivedHomDualExists B S hS)
    (h0DLC3 : ∀ {S : Scheme.{u}} (hS : B.Contains S),
      RelativeDerivedHomRepresentableOfFibres B S hS)
    (h0DKW : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.RelativelyPerfectColimit)
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
    (h0DLA : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.CechDescent)
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
                schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
                  𝓕 hD
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
    (h0DL4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B _ hΛ).map h.left) →
      ∀ (E' : derivedModules B _ hΛ (D.space T')) (E : derivedModules B _ hΛ (D.space T)),
        (((smallEtaleDerivedPullbackData B _ hΛ).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E') :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  have hrs Λ₀ [CommRing Λ₀] [Algebra.FiniteType ℤ Λ₀] (hΛ : B.Contains (Spec (.of Λ₀)))
      (D' : ComplexesSituation B _ hΛ) :=
    satisfiesRSStar_complexesFunctor D' (complexesFunctor_isFiberedInGroupoids D')
      (complexes_hasRepresentableDiagonal D'
        (existsNegativeExtLocus_of_dualExists B _ hΛ (h0DKY hΛ)) (h0DLC3 hΛ)
        (complexesFunctor_isFiberedInGroupoids D'))
      (h07W3 Λ₀ hΛ) (h0DL7 Λ₀ hΛ) (h0DL4 Λ₀ hΛ D')
  isAlgebraicStack_complexes_of_held_of_adjoinDescent_of_terminalVersality (h0CXU := h0CXU)
    h08K1 hcomp h0DLC2 h0DKY h0DLC3 h0DKW h0DIQ
    (fun Λ₀ _ _ hΛ D' _ _ _ _ _ iΛ x₀ hx₀ hfinite hqc =>
      fibreTangentFinite_of_fibreLiftClassPullback D' h0D0T
        (complexesFunctor_isFiberedInGroupoids D')
        (hrs Λ₀ hΛ D')
        iΛ x₀ hx₀ hfinite hqc (contains_spec_of_fieldPoint hx₀)
        (hDer := fun _ => HasDerivedCategory.standard _)
        (hpull D' iΛ x₀ hx₀ (contains_spec_of_fieldPoint hx₀)
          (hDer := fun _ => HasDerivedCategory.standard _)))
    (fun Λ₀ _ _ hΛ D' _ _ _ _ _ iΛ x₀ hx₀ _ _ =>
      fibreInfFinite_of_fibreTrivialAutNatural D' h0D0T
        (hrs Λ₀ hΛ D')
        iΛ x₀ hx₀ (contains_spec_of_fieldPoint hx₀)
        (hDer := fun _ => HasDerivedCategory.standard _)
        (hnat D' iΛ x₀ hx₀ (contains_spec_of_fieldPoint hx₀)
          (hDer := fun _ => HasDerivedCategory.standard _)))
    h0DLA h07Y4 h07W3 h0DL7 h0DL4 hS D

/-- **Stacks 0DLN, granted results not yet proved here other than Stacks 0D0T, with the fibre
hypotheses of Stacks 0DLL discharged** (unregistered).
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback`
with its hypothesis `h0D0T` discharged by Stacks 0D0T,
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper_ofRingHom` (the base's
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`). The other hypotheses are those of
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback`, with the same marks:
`hpull` and `hnat`
**internal, pending** (0DLL-G4c).

The hypothesis `h0CXU` is asked only at terminal `Y` (Stacks 0CXU at terminal Y, the case
the source uses); narrowing it strengthens the statement. -/
theorem isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt_of_terminalVersality
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS)
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
    (h08K1 : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (hZ : B.Contains (⊤_ Scheme.{u})) (i : (Finset A)ᵒᵖ)
      {X Y : Over ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i)} (f : X ⟶ Y),
      IsQuasiCompactSpace B _ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAbsolutelyQuasiSeparated B _ hZ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAlgebraicSpace B _ hZ X.left → IsAlgebraicSpace B _ hZ Y.left →
      IsQuasiCompactSpace B _ hZ X.left → IsAbsolutelyQuasiSeparated B _ hZ hZ X.left →
      IsQuasiCompactSpace B _ hZ Y.left → IsAbsolutelyQuasiSeparated B _ hZ hZ Y.left →
      IsProper B _ hZ
        ((Over.pullback (limit.π (adjoinSiteDiagram B hZ A hA ⋙ yoneda) i)).map f).left →
      IsLocallyOfFiniteType B _ hZ f.left →
      ∃ (j : (Finset A)ᵒᵖ) (e : j ⟶ i),
        IsProper B _ hZ
          ((Over.pullback ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).map e)).map f).left)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLC2 : ∀ {S : Scheme.{u}} (hS : B.Contains S), NegativeExtVanishesOfFibres B S hS)
    (h0DKY : ∀ {S : Scheme.{u}} (hS : B.Contains S), RelativeDerivedHomDualExists B S hS)
    (h0DLC3 : ∀ {S : Scheme.{u}} (hS : B.Contains S),
      RelativeDerivedHomRepresentableOfFibres B S hS)
    (h0DKW : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.RelativelyPerfectColimit)
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
    (h0DLA : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.CechDescent)
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
                schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
                  𝓕 hD
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
    (h0DL4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B _ hΛ).map h.left) →
      ∀ (E' : derivedModules B _ hΛ (D.space T')) (E : derivedModules B _ hΛ (D.space T)),
        (((smallEtaleDerivedPullbackData B _ hΛ).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E') :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_of_terminalVersality
    (h0CXU := h0CXU) hS D
    (fun A _ hA X hX => moduleFinite_hom_shift_of_isProper_ofRingHom B A hA X hX)
    hpull hnat h08K1 hcomp h0DLC2 h0DKY h0DLC3 h0DKW h0DIQ h0DLA h07Y4 h07W3 h0DL7 h0DL4

/-- **Stacks 0DLN, granted results not yet proved here other than Stacks 0D0T, 08K0 and 08K1,
with the fibre hypotheses of Stacks 0DLL discharged** (unregistered).
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt`
with its hypothesis `h08K1` (at the systems of finitely generated subrings) also discharged, by
`AlgebraicGeometry.Space.exists_isProper_overPullback_map_of_chartLimitsInSite_properInSite` (the
base's Stacks 08K1 under the convention). The other hypotheses are those of
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback`, with the same marks; `hnat` is put
before `hpull`, so that the statement text differs from that of
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt` at its start.

The hypothesis `h0CXU` is asked only at terminal `Y` (Stacks 0CXU at terminal Y, the case
the source uses); narrowing it strengthens the statement. -/
theorem isAlgebraicStack_complexes_of_fibreLiftPullback_finiteExt_properInSite_of_terminalVersality
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS)
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
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLC2 : ∀ {S : Scheme.{u}} (hS : B.Contains S), NegativeExtVanishesOfFibres B S hS)
    (h0DKY : ∀ {S : Scheme.{u}} (hS : B.Contains S), RelativeDerivedHomDualExists B S hS)
    (h0DLC3 : ∀ {S : Scheme.{u}} (hS : B.Contains S),
      RelativeDerivedHomRepresentableOfFibres B S hS)
    (h0DKW : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.RelativelyPerfectColimit)
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
    (h0DLA : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.CechDescent)
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
                schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
                  𝓕 hD
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
    (h0DL4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B _ hΛ).map h.left) →
      ∀ (E' : derivedModules B _ hΛ (D.space T')) (E : derivedModules B _ hΛ (D.space T)),
        (((smallEtaleDerivedPullbackData B _ hΛ).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E') :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt_of_terminalVersality
    (h0CXU := h0CXU) hS D
    hpull hnat
    (fun A _ hA hZ i _ _ f =>
      exists_isProper_overPullback_map_of_chartLimitsInSite_properInSite B _ hZ hZ _
      (adjoinSiteDiagram_chartLimitsInSite B hZ A hA)
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).1
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).2.1 i f)
    hcomp h0DLC2 h0DKY h0DLC3 h0DKW h0DIQ h0DLA h07Y4 h07W3 h0DL7 h0DL4

end AlgebraicGeometry.Space.ComplexesSituation

end
