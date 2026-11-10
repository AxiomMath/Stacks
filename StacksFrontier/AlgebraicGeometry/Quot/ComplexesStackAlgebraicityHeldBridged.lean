module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityHeld
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDescentBridges

/-!
# Stacks 0DLN from results not yet proved here, with the descent inputs of 0DLH discharged

`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held` proves Stacks
0DLN granted the results not yet proved here and some steps internal to this chapter. Two of
its hypotheses feed only Stacks 0DLH (the third input of its descent step, Stacks 0DL1 with 0DL2,
is `AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectDescends`, applied inside it),
and both are now proved on this branch:

* the fibre condition descends along fppf coverings, from Stacks 0DLC (1), which follows from
  Stacks 0DKY: `ComplexesSituation.noNegativeFibreExtDescends_of_existsNegativeExtLocus`;
* objects of `Complexes_{X/B}` have no negative self-extensions (Stacks 0DLD (b) at `V = T`),
  from Stacks 0DLC (2) at `W = Y`:
  `ComplexesSituation.hasNoNegativeSelfExt_of_negativeExtVanishesOfFibres`.

This file states Stacks 0DLN with those two hypotheses replaced by Stacks 0DLC (2) at `W = Y`.
Nothing is registered.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held'`: Stacks 0DLN,
  granted results not yet proved here and the steps still internal to this chapter, which are
  now Stacks 0DLC (2) and (3) at `W = Y` and the two finiteness statements of 0DLL.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0DLH](https://stacks.math.columbia.edu/tag/0DLH)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
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

/-- **Stacks 0DLN, granted results not yet proved here and the steps still internal.** For every
scheme `S` of the site and every situation `D` of Stacks 0DLE over `S`, `Complexes_{X/B}` is an
algebraic stack over `S`.

This is `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held` with
two of its hypotheses discharged: the fibre condition descends along fppf coverings (from
Stacks 0DLC (1), hence from `h0DKY`), and objects of `Complexes_{X/B}` have no negative
self-extensions (from `h0DLC2`). Each hypothesis is marked either *not yet proved here* (a Stacks
tag) or *internal* (a step of this chapter not yet proved):

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
* `h08K0`, `h08K1` (not yet proved here): Stacks 08K0 and 08K1 in their bound-free form.
* `hcomp` (not yet proved here): the change-of-base comparison of Section 04X4 for `Complexes`, not
  a Stacks tag. -/
theorem isAlgebraicStack_complexes_of_held'
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
    (h08K0 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
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
        IsFlat B S hS ((Over.pullback (limit.π D i)).map f).left →
        IsLocallyOfFinitePresentation B S hS f.left →
        ∃ (j : I) (e : j ⟶ i), IsFlat B S hS ((Over.pullback (D.map e)).map f).left)
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
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_held h0DKY h0DLC3 h0DKW h0DIQ h0DLLT h0DLLInf h0DLA
    (fun hS D => D.hasNoNegativeSelfExt_of_negativeExtVanishesOfFibres (h0DLC2 hS))
    (fun hS D => D.noNegativeFibreExtDescends_of_existsNegativeExtLocus
      (existsNegativeExtLocus_of_dualExists B _ hS (h0DKY hS)))
    h07Y4 h0CXU h07W3 h0DL7 h0DL4 h08K0 h08K1 hcomp hS D

end AlgebraicGeometry.Space.ComplexesSituation

end
