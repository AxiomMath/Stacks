module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityHeldBridged
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFiniteTypeReductionUnbounded

/-!
# Stacks 0DLN from results not yet proved here, with Stacks 08K0 discharged

`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held'` proves Stacks
0DLN granted results not yet proved here and the steps still internal to this chapter. One of
those hypotheses, `h08K0`, is Stacks 08K0 (flatness of the morphism) for every cofiltered
inverse system. Its only use is in the reduction to a base of finite type over `ℤ`, at the
system of the spectra of the finitely generated subrings of a ring, which is indexed by the
opposite of a directed preorder. In that case it is proved, from the form of Stacks 08K0 under
the convention 07SD on the base:
`AlgebraicGeometry.Space.exists_isFlat_overPullback_map_of_chartLimitsInSite`.

This file states Stacks 0DLN without the hypothesis `h08K0`. The proof is that of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held`, with the
reduction step taken from
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case_unbounded'`
and the two descent inputs of Stacks 0DLH discharged as in
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held'`. Stacks 08K1
remains a hypothesis: the base has no bound-free form of it. Nothing is registered.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held''`: Stacks 0DLN,
  granted results not yet proved here other than Stacks 08K0, and the steps still internal to
  this chapter.
* `ComplexesSituation.isAlgebraicStack_complexes_of_held_of_adjoinDescent`: the same, with Stacks
  08K1 asked only of the systems of the finitely generated subrings of a ring.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

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

/-- **Stacks 0DLN, granted results not yet proved here, with Stacks 08K1 asked only of the
systems of finitely generated subrings.** This is
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held''` with its
hypothesis `h08K1` asked only of the systems `adjoinSiteDiagram B hZ A hA ⋙ yoneda` of the spectra
of the finitely generated subrings of a ring `A`, indexed by the opposite of the directed preorder
`Finset A`: the only systems at which the proof uses Stacks 08K1. The other hypotheses are those
of `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held''`, with the
same marks. The hypothesis `h08K1` is put first. Both
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held''` and
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held'''` are
corollaries. -/
theorem isAlgebraicStack_complexes_of_held_of_adjoinDescent
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
    (h0DLLT : ∀ (Λ₀ : Type u) [CommRing Λ₀] [Algebra.FiniteType ℤ Λ₀]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ₀))) (D : ComplexesSituation B _ hΛ)
      (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k]
      (iΛ : Spec (.of Λ) ⟶ Spec (CommRingCat.of Λ₀)) (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      FibreTangentFinite D iΛ x₀ hx₀)
    (h0DLLInf : ∀ (Λ₀ : Type u) [CommRing Λ₀] [Algebra.FiniteType ℤ Λ₀]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ₀))) (D : ComplexesSituation B _ hΛ)
      (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k]
      (iΛ : Spec (.of Λ) ⟶ Spec (CommRingCat.of Λ₀)) (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      FibreInfFinite D iΛ x₀ hx₀)
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
              Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
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
    (h0DL4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B _ hΛ).map h.left) →
      ∀ (E' : derivedModules B _ hΛ (D.space T')) (E : derivedModules B _ hΛ (D.space T)),
        (((smallEtaleDerivedPullbackData B _ hΛ).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E')
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) := by
  -- Stacks 0DLF, registered
  have h0DLF : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      (complexesFunctor D).IsFiberedInGroupoids := fun _ D =>
    complexesFunctor_isFiberedInGroupoids D
  -- Stacks 0DLC, part (1), from Stacks 0DKY
  have h0DLC1 : ∀ {S : Scheme.{u}} (hS : B.Contains S), ExistsNegativeExtLocus B S hS :=
    fun hS => existsNegativeExtLocus_of_dualExists B _ hS (h0DKY hS)
  -- Stacks 0DLG, from Stacks 0DLC, parts (1) and (3)
  have h0DLG : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      Stack.HasRepresentableDiagonal B S hS
        (CatFiberedInGroupoids.mk (complexesBasedCategory D)
          (complexesFunctor_isFiberedInGroupoids D)) := fun hS D =>
    complexes_hasRepresentableDiagonal D (h0DLC1 hS) (h0DLC3 hS)
      (complexesFunctor_isFiberedInGroupoids D)
  -- Stacks 0DLD (b) at `V = T`, from Stacks 0DLC (2) at `W = Y`
  have h0DLDb : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.HasNoNegativeSelfExt := fun hS D =>
    D.hasNoNegativeSelfExt_of_negativeExtVanishesOfFibres (h0DLC2 hS)
  -- the descent form of Stacks 0DLC (1), from Stacks 0DLC (1)
  have h0DLC1desc : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.NoNegativeFibreExtDescends := fun hS D =>
    D.noNegativeFibreExtDescends_of_existsNegativeExtLocus (h0DLC1 hS)
  -- Stacks 0DLH, from Stacks 0DLG, 0DLA, 0DLD (b), 0DL1 and the descent form of 0DLC (1)
  have h0DLH : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      (complexesFunctor D).IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS) :=
    fun hS D => complexesFunctor_isStackInGroupoids_of_pending (D := D) (h0DLG hS D)
      (h0DLA hS D) (h0DLDb hS D) (relativelyPerfectDescends D) (h0DLC1desc hS D)
  -- Stacks 0DLJ, from Stacks 0DKW and Stacks 0DLC, part (1), when `Y` is final
  have h0DLJ : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      IsTerminal D.Y →
      Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS
        (CatFiberedInGroupoids.mk (complexesBasedCategory D)
          (complexesFunctor_isFiberedInGroupoids D)) := fun hS D hY =>
    isLimitPreserving_of_existsNegativeExtLocus
      (isLocallyOfFinitePresentation_terminal_from_of_isTerminal hY) (h0DKW hS D) (h0DLC1 hS)
  -- step 5: the case `S = B = Spec Λ`, `Λ` of finite type over `ℤ`, by Artin's criterion
  have hcase : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D' : ComplexesSituation B _ hΛ),
      Nonempty (IsTerminal D'.Y) →
        Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D') := by
    intro Λ _ _ hΛ D' ⟨hY⟩
    have hRS : Deformation.Artin.SatisfiesRS B _ hΛ (complexesFunctor D') (h0DLF hΛ D') :=
      satisfiesRS_complexesFunctor D' (h0DLF hΛ D') (h0DLG hΛ D') (h07W3 Λ hΛ)
      (h0DL7 Λ hΛ) (h0DL4 Λ hΛ D')
    exact isAlgebraicStack_of_artinCriterion Λ D' (h07Y4 Λ hΛ) (h0DLF hΛ D') (h0DLG hΛ D')
      (exists_isSizeBounded Λ D')
      ((h0DLH hΛ D').of_le (Space.etaleTopologyOver_le_topology B _ hΛ)) (h0DLJ hΛ D' hY) hRS
      (finiteDimensional_artinianTangentSpace_stalk_of_isTerminal D' hY (h0DLF hΛ D') hRS
        (h0DLLT Λ hΛ D') (h0DLLInf Λ hΛ D'))
      (fun ξ => isEffective_formalObject_of (h0DIQ Λ hΛ D') (h0DLC1 hΛ) hY ξ) (h0CXU Λ hΛ D')
  -- step 4: the case `S = B = Spec A` for every ring `A`
  have haff : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (D' : ComplexesSituation B _ hA), Nonempty (IsTerminal D'.Y) →
        Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hA (complexesBasedCategory D') :=
    fun A _ hA D' hD' =>
      isAlgebraicStack_spec_of_finiteType_case_unbounded_of_adjoinDescent h08K1
        (fun A _ hA hZ i _ _ f => exists_isFlat_overPullback_map_of_chartLimitsInSite B _ hZ hZ _
          (adjoinSiteDiagram_chartLimitsInSite B hZ A hA)
          (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).1
          (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).2.1 i f)
        hcomp h0DLF (fun hS D => h0DLG hS D) (fun _ D _ g => D.exists_baseChangeSquare g) hcase
        A hA D' hD'
  -- step 3: the case `S = B` for every scheme `S` of the site, by an affine open covering
  have hterm : ∀ {T : Scheme.{u}} (hT : B.Contains T) (D' : ComplexesSituation B T hT),
      Nonempty (IsTerminal D'.Y) →
        Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B T hT (complexesBasedCategory D') := by
    intro T hT D' ⟨hY⟩
    have : LocallySmall.{u} (complexesBasedCategory D').obj :=
      Stack.locallySmall_of_isAlgebraicSpaceIsomPresheaf B T hT
        (CatFiberedInGroupoids.mk (complexesBasedCategory D') (h0DLF hT D'))
        ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B T hT _).mp
          (h0DLG hT D'))
    let e := BasedCategory.shrinkHomsEquivalenceOver (complexesBasedCategory D')
    let 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B T hT) :=
      CatFiberedInGroupoids.mk (complexesBasedCategory D').shrinkHoms
        (StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e.symm (h0DLF hT D'))
    have hV : ∀ V : T.affineOpens, B.Contains (Spec Γ(T, V)) := fun V =>
      have := V.2.isOpenImmersion_fromSpec
      Scheme.size_lt_of_isOpenImmersion V.2.fromSpec hT
    let g : ∀ V : T.affineOpens, B.obj (hV V) ⟶ B.obj hT :=
      fun V => ObjectProperty.homMk V.2.fromSpec
    let U : T.affineOpens → BigFppfOver B T hT := fun V => Over.mk (g V)
    have hopen : ∀ V, AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (U V).hom) :=
      fun V => V.2.isOpenImmersion_fromSpec
    refine isAlgebraicStack_of_restrictSquare_openCover D' (h0DLF hT D') (h0DLH hT D')
      (h0DLG hT D') (h0DLJ hT D' hY) 𝒴 e.symm U hopen ?_ ?_
    · intro s
      obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ s)
      refine ⟨⟨W, hW⟩, ?_⟩
      change s ∈ Set.range hW.fromSpec
      rwa [IsAffineOpen.range_fromSpec]
    · intro V
      let g' : (schemeSpaceFunctor B T hT).obj (U V) ⟶ D'.Y := hY.from _
      exact isAlgebraicStack_restrictSquare_of_baseChange hT D' ⟨hY⟩ 𝒴 e.symm (U V) (hopen V) g'
        ((isAlgebraicStack_overSmallerBase_iff (g V) (D'.baseChange g') (Iso.refl _) hcomp).1
          (haff Γ(T, V) (hV V) (overSmallerBase (g V) (D'.baseChange g') (Iso.refl _))
            (overSmallerBase_isTerminal _ _ _)))
  -- step 2: the case of a base which is a scheme, by Section 04X4
  have hscheme : ∀ D' : ComplexesSituation B S hS,
      (∃ T : BigFppfOver B S hS, Nonempty (D'.Y ≅ (schemeSpaceFunctor B S hS).obj T)) →
        Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D') := by
    rintro D' ⟨T, ⟨φ⟩⟩
    let gT : B.obj T.left.2 ⟶ B.obj hS := T.hom
    let eY : D'.Y.obj ≅ yoneda.obj (Over.mk gT) := (ObjectProperty.ι _).mapIso φ
    exact (isAlgebraicStack_overSmallerBase_iff gT D' eY hcomp).1
      (hterm _ _ (overSmallerBase_isTerminal _ _ _))
  -- step 1: the general case, by Remark 0DLI and Section 03YJ
  exact isAlgebraicStack_of_isAlgebraicStack_schemeBase (h0DLF hS) (h0DLG hS) (h0DLH hS)
    (fun D _ g => D.exists_baseChangeSquare g) hscheme D


/-- **Stacks 0DLN, granted results not yet proved here and the steps still internal.** For every
scheme `S` of the site and every situation `D` of Stacks 0DLE over `S`, `Complexes_{X/B}` is an
algebraic stack over `S`.

This is `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held'`
without its hypothesis `h08K0`, Stacks 08K0. The proof uses Stacks 08K0 only for the systems of
the spectra of the finitely generated subrings of a ring, which are indexed by the opposite of a
directed preorder; there it is
`AlgebraicGeometry.Space.exists_isFlat_overPullback_map_of_chartLimitsInSite`. The hypothesis
`hcomp` is put first, so that the statement text differs from that of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held'` before any `:=`.
Each hypothesis is marked either *not yet proved here* (a Stacks tag) or *internal* (a step of
this chapter not yet proved):

* `h0DLC2` (internal): Stacks 0DLC, part (2), in the case `W = Y`
  (`AlgebraicGeometry.Space.NegativeExtVanishesOfFibres`).
* `h0DKY` (not yet proved here): Stacks 0DKY, the dual of the relative derived Hom
  (`AlgebraicGeometry.Space.RelativeDerivedHomDualExists`); it gives Stacks 0DLC, part (1).
* `h0DLC3` (internal): Stacks 0DLC, part (3), in the case `W = Y`
  (`AlgebraicGeometry.Space.RelativeDerivedHomRepresentableOfFibres`).
* `h0DKW` (not yet proved here): Stacks 0DKW, relatively perfect objects over a limit are the
  colimit (`AlgebraicGeometry.Space.ComplexesSituation.RelativelyPerfectColimit`).
* `h0DIQ` (not yet proved here): Stacks 0DIQ, Grothendieck existence for pseudo-coherent complexes,
  over `Spec Λ`, in the form of
  `AlgebraicGeometry.Space.ComplexesSituation.isEffective_formalObject_of`.
* `h0DLLT`, `h0DLLInf` (internal): over `Spec Λ`, the finiteness of the
  tangent space and of the infinitesimal automorphisms of the fibre at every field point of finite
  type (`AlgebraicGeometry.Space.ComplexesSituation.FibreTangentFinite`,
  `AlgebraicGeometry.Space.ComplexesSituation.FibreInfFinite`).
* `h0DLA` (not yet proved here): Stacks 0DLA, descent of complexes along Čech covers
  (`AlgebraicGeometry.Space.ComplexesSituation.CechDescent`).
* `h07Y4` (not yet proved here): Stacks 07Y4, Artin's criterion, over `Spec Λ`.
* `h0CXU` (not yet proved here): openness of versality for `Complexes_{X/B}` over `Spec Λ`.
* `h07W3` (not yet proved here): Stacks 07W3 over `Spec Λ`.
* `h0DL7` (not yet proved here): Stacks 0DL7 over `Spec Λ`.
* `h0DL4` (not yet proved here): Stacks 0DL4 over `Spec Λ`.
* `h08K1` (not yet proved here): Stacks 08K1 in its bound-free form.
* `hcomp` (not yet proved here): the change-of-base comparison of Section 04X4 for `Complexes`, not
  a Stacks tag. -/
theorem isAlgebraicStack_complexes_of_held''
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
    (h0DLLT : ∀ (Λ₀ : Type u) [CommRing Λ₀] [Algebra.FiniteType ℤ Λ₀]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ₀))) (D : ComplexesSituation B _ hΛ)
      (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k]
      (iΛ : Spec (.of Λ) ⟶ Spec (CommRingCat.of Λ₀)) (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      FibreTangentFinite D iΛ x₀ hx₀)
    (h0DLLInf : ∀ (Λ₀ : Type u) [CommRing Λ₀] [Algebra.FiniteType ℤ Λ₀]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ₀))) (D : ComplexesSituation B _ hΛ)
      (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k]
      (iΛ : Spec (.of Λ) ⟶ Spec (CommRingCat.of Λ₀)) (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      FibreInfFinite D iΛ x₀ hx₀)
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
              Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
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
    (h0DL4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B _ hΛ).map h.left) →
      ∀ (E' : derivedModules B _ hΛ (D.space T')) (E : derivedModules B _ hΛ (D.space T)),
        (((smallEtaleDerivedPullbackData B _ hΛ).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E')
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      (∀ (i : I) (Z : BigAffineFppf B S hS)
        (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i)
        (W : Over i ⥤ BigAffineFppf B S hS),
        (W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
          (Over.post (X := i) D ⋙ Over.pullback g) ⋙
            Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) →
        ∀ c : Cone (((W ⋙ BigAffineFppf.inclusion B S hS) ⋙
            BigFppfOver.forget B S hS) ⋙ B.inclusion),
          IsLimit c → B.Contains c.pt) →
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) →
      ∀ (i : I) {X Y : Over (D.obj i)} (f : X ⟶ Y),
        IsQuasiCompactSpace B S hS (D.obj i) → IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i) →
        IsAlgebraicSpace B S hS X.left → IsAlgebraicSpace B S hS Y.left →
        IsQuasiCompactSpace B S hS X.left → IsAbsolutelyQuasiSeparated B S hS hZ X.left →
        IsQuasiCompactSpace B S hS Y.left → IsAbsolutelyQuasiSeparated B S hS hZ Y.left →
        IsProper B S hS ((Over.pullback (limit.π D i)).map f).left →
        IsLocallyOfFiniteType B S hS f.left →
        ∃ (j : I) (e : j ⟶ i), IsProper B S hS ((Over.pullback (D.map e)).map f).left)
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_held_of_adjoinDescent
    (fun A _ hA hZ i _ _ f => h08K1 hZ hZ _ (adjoinSiteDiagram_chartLimitsInSite B hZ A hA)
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).1
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).2.1 i f)
    hcomp h0DLC2 h0DKY h0DLC3 h0DKW h0DIQ h0DLLT h0DLLInf h0DLA h07Y4 h0CXU h07W3 h0DL7 h0DL4 hS D

end AlgebraicGeometry.Space.ComplexesSituation

end
