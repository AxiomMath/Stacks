module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFiniteTypeReductionUnbounded
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackOpenCoverRestriction
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackPushoutGluing
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackRestrictSquare
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackSizeBound
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackTangentSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlasCriterion
public import StacksFrontier.CategoryTheory.Sites.Stack.CoarserTopology

/-!
# Stacks 0DLN from the remaining inputs of its proof

Stacks 0DLN: for every situation of Stacks 0DLE over a scheme `S`, that is a proper, flat,
finitely presented morphism `f : X ⟶ B` of algebraic spaces over `S`, the category
`Complexes_{X/B}` is an algebraic stack over `S`.

This file chains the reductions of the source's proof:

1. the reduction to a base which is a scheme (Remark 0DLI and Section 03YJ,
   `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_isAlgebraicStack_schemeBase`);
2. the replacement of `S` by that scheme (Section 04X4,
   `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_overSmallerBase_iff`);
3. the covering by affine opens
   (`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_restrictSquare_openCover`),
   with the restriction to an affine open identified with `Complexes` of the base change to it
   (`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_restrictSquare_of_baseChange`);
4. the descent to a base of finite type over `ℤ` (Stacks 07SK, 08K0, 08K1,
   `AlgebraicGeometry.Space.ComplexesSituation.`
   `isAlgebraicStack_spec_of_finiteType_case_unbounded`);
5. Artin's criterion in the finite type case
   (`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`).

It discharges these inputs of those reductions: Stacks 0DLF
(`AlgebraicGeometry.Space.ComplexesSituation.complexesFunctor_isFiberedInGroupoids`), Remark 0DLI
(`AlgebraicGeometry.Space.ComplexesSituation.exists_baseChangeSquare`), axiom [-1]
(`AlgebraicGeometry.Space.ComplexesSituation.exists_isSizeBounded`), condition (RS) through
Stacks 0DLK (`AlgebraicGeometry.Space.ComplexesSituation.satisfiesRS_complexesFunctor`), the
passage from the tangent spaces of Stacks 07WY to the form of Stacks 07Y4
(`Deformation.Artin.finiteDimensional_artinianTangentSpace_stalk_of_finiteDimensional`), the
étale stack condition from the fppf one (Stacks 02ZI for a coarser topology), and the G-ring
condition (Stacks 07PX). Every other input is a hypothesis stated at its content and named
after its tag, one hypothesis per tag.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_pending`: Stacks
  0DLN, granted the remaining inputs.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u z

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}}

attribute [local instance] complexesCategory

/-- **Stacks 0DLN, granted the remaining inputs of its proof.** For every scheme `S` of the site
and every situation `D` of Stacks 0DLE over `S`, `Complexes_{X/B}` is an algebraic stack over `S`.

The hypotheses are the inputs of the proof that are not proved here. Each one is stated at the
content of its tag, at the bases where the proof uses it: every scheme of the site, or the
spectra `Spec Λ` with `Λ` of finite type over `ℤ` for the finite type case:

* `h07Y4`: Stacks 07Y4, Artin's criterion, over `Spec Λ`, in the form of
  `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`.
* `h0CXU`: openness of versality for `Complexes_{X/B}` over `Spec Λ`, which is Stacks 0CXU
  applied with 0DLG, 0DLK, 0DLJ and 0DLM.
* `h0DLG`: Stacks 0DLG, the diagonal of `Complexes_{X/B}` is representable by algebraic spaces.
* `h0DLH`: Stacks 0DLH, `Complexes_{X/B}` is a stack in groupoids for the fppf topology.
* `h0DLJ`: Stacks 0DLJ, `Complexes_{X/B}` is limit preserving.
* `h0DLL`: Stacks 0DLL over `Spec Λ`, its tangent space half in the form of Stacks 07WY. For
  every (RS) witness, the tangent spaces `T_{x₀}` at the field points of finite type are finite
  dimensional.
* `h0DLM`: Stacks 0DLM over `Spec Λ`, formal objects of `Complexes_{X/B}` are effective.
* `h07W3`: Stacks 07W3 over `Spec Λ`, pushouts of algebraic spaces along a thickening and an
  affine morphism and their flat base changes, at the instance of
  `AlgebraicGeometry.Space.ComplexesSituation.essSurj_complexesFiberSquareComparison`.
* `h0DL7`: Stacks 0DL7 over `Spec Λ`, gluing pseudo-coherent objects of the derived category
  along a pushout by a thickening and an affine morphism.
* `h0DL4`: Stacks 0DL4 over `Spec Λ`, relative perfectness descends along a finite order
  thickening of test schemes.
* `h08K0`: Stacks 08K0, the flatness of a morphism descends to a stage of a limit, in its
  bound-free form under the convention 07SD.
* `h08K1`: Stacks 08K1, the properness of a morphism descends to a stage of a limit, in the same
  form.
* `hcomp`: the change-of-base comparison of Section 04X4 for `Complexes`
  (`AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseComparison`), not a Stacks tag. -/
theorem isAlgebraicStack_complexes_of_pending
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
    (h0DLG : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      Stack.HasRepresentableDiagonal B S hS
        (CatFiberedInGroupoids.mk (complexesBasedCategory D)
          (complexesFunctor_isFiberedInGroupoids D)))
    (h0DLH : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      (complexesFunctor D).IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS))
    (h0DLJ : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS
        (CatFiberedInGroupoids.mk (complexesBasedCategory D)
          (complexesFunctor_isFiberedInGroupoids D)))
    (h0DLL : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      (hRS : Deformation.Artin.SatisfiesRS B _ hΛ (complexesFunctor D)
        (complexesFunctor_isFiberedInGroupoids D))
      (Λ' k : Type u) [CommRing Λ'] [Field k] [Algebra Λ' k]
      (iΛ : Spec (.of Λ') ⟶ Spec (CommRingCat.of Λ)) (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ))
      (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ))
      (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ)),
      FiniteDimensional k (Deformation.Artin.tangentSpaceModuleOfSatisfiesRS B _ hΛ
        (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D) hRS iΛ x₀ hx₀ hfinite
        hqc))
    (h0DLM : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      (ξ : Deformation.Artin.FormalObject B _ hΛ (complexesFunctor D)),
      Deformation.Artin.FormalObject.IsEffective B _ hΛ (complexesFunctor D)
        (complexesFunctor_isFiberedInGroupoids D) ξ)
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
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) := by
  -- Stacks 0DLF
  have h0DLF : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      (complexesFunctor D).IsFiberedInGroupoids := fun _ D =>
    complexesFunctor_isFiberedInGroupoids D
  -- step 5: the case `S = B = Spec Λ`, `Λ` of finite type over `ℤ`, by Artin's criterion
  have hcase : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D' : ComplexesSituation B _ hΛ),
      Nonempty (IsTerminal D'.Y) →
        Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D') := by
    intro Λ _ _ hΛ D' _
    have hRS : Deformation.Artin.SatisfiesRS B _ hΛ (complexesFunctor D') (h0DLF hΛ D') :=
      satisfiesRS_complexesFunctor D' (h0DLF hΛ D') (h0DLG hΛ D') (h07W3 Λ hΛ)
      (h0DL7 Λ hΛ) (h0DL4 Λ hΛ D')
    exact isAlgebraicStack_of_artinCriterion Λ D' (h07Y4 Λ hΛ) (h0DLF hΛ D') (h0DLG hΛ D')
      (exists_isSizeBounded Λ D')
      ((h0DLH hΛ D').of_le (Space.etaleTopologyOver_le_topology B _ hΛ)) (h0DLJ hΛ D') hRS
      (Deformation.Artin.finiteDimensional_artinianTangentSpace_stalk_of_finiteDimensional
        (complexesFunctor D') (h0DLF hΛ D') hRS (h0DLL Λ hΛ D' hRS))
      (h0DLM Λ hΛ D') (h0CXU Λ hΛ D')
  -- step 4: the case `S = B = Spec A` for every ring `A`
  have haff : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (D' : ComplexesSituation B _ hA), Nonempty (IsTerminal D'.Y) →
        Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hA (complexesBasedCategory D') :=
    fun A _ hA D' hD' =>
      isAlgebraicStack_spec_of_finiteType_case_unbounded h08K0 h08K1 hcomp h0DLF
        (fun hS D => h0DLG hS D) (fun _ D _ g => D.exists_baseChangeSquare g) hcase A hA D' hD'
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
      (h0DLG hT D') (h0DLJ hT D') 𝒴 e.symm U hopen ?_ ?_
    · intro s
      obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ s)
      refine ⟨⟨W, hW⟩, ?_⟩
      change s ∈ Set.range hW.fromSpec
      rwa [IsAffineOpen.range_fromSpec]
    · intro V
      let g' : (schemeSpaceFunctor B T hT).obj (U V) ⟶ D'.Y := hY.from _
      -- `Complexes` of the base change to `V`, read over `Spec Γ(T, V)`, is algebraic by step 4
      have h₁ := haff Γ(T, V) (hV V)
        (overSmallerBase (g V) (D'.baseChange g') (Iso.refl _))
        (overSmallerBase_isTerminal _ _ _)
      exact isAlgebraicStack_restrictSquare_of_baseChange hT D' ⟨hY⟩ 𝒴 e.symm (U V) (hopen V) g'
        ((isAlgebraicStack_overSmallerBase_iff (g V) (D'.baseChange g') (Iso.refl _) hcomp).1 h₁)
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

end AlgebraicGeometry.Space.ComplexesSituation

end
