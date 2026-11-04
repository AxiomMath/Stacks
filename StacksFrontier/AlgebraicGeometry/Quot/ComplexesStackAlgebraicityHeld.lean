module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityPending
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackPerfectDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDiagonalReduction
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFormalEffectiveness
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackTangentSpaceBase
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints

/-!
# Stacks 0DLN from the inputs of 0DLG, 0DLJ, 0DLL and 0DLM

`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_pending` proves
Stacks 0DLN granted one hypothesis for each of its inputs, among them the lemmas 0DLG, 0DLJ,
0DLL and 0DLM of the same chapter. Those lemmas follow from deeper results: 0DLG from
Stacks 0DLC, parts (1) and (3)
(`AlgebraicGeometry.Space.ComplexesSituation.complexes_hasRepresentableDiagonal`), 0DLJ from
Stacks 0DKW and 0DLC (1)
(`AlgebraicGeometry.Space.ComplexesSituation.isLimitPreserving_of_existsNegativeExtLocus`),
0DLM from Stacks 0DIQ and 0DLC (1)
(`AlgebraicGeometry.Space.ComplexesSituation.isEffective_formalObject_of`), 0DLL from (RS) and the
finiteness of the tangent space and the infinitesimal automorphisms of the fibre
(`ComplexesSituation.finiteDimensional_artinianTangentSpace_stalk_of_isTerminal`),
and 0DLC (1) from Stacks 0DKY
(`AlgebraicGeometry.Space.existsNegativeExtLocus_of_dualExists`). This file states Stacks 0DLN
granted those deeper results instead, with the same proof.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_terminal_from_of_isTerminal`: the final
  algebraic space over `S` is locally of finite presentation over `S`.
* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held`: Stacks 0DLN,
  granted the results its proof uses as hypotheses.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u z

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The final algebraic space over `S` is locally of finite presentation over `S`.** Its
functor of points takes the value a point at every scheme, so it is limit preserving. -/
theorem isLocallyOfFinitePresentation_terminal_from_of_isTerminal {Y : AlgebraicSpaces B S hS}
    (hY : IsTerminal Y) : IsLocallyOfFinitePresentation B S hS (terminal.from Y.obj) := by
  let e : Y ≅ schemeSpace (Over.mk (𝟙 (B.obj hS))) :=
    hY.uniqueUpToIso BeauvilleLaszlo.Space.isTerminal_schemeSpace_terminal
  have hsub : ∀ U, Subsingleton (Y.obj.obj U) := fun U =>
    ⟨fun x y => (((ObjectProperty.ι _).mapIso e).app U).toEquiv.injective
      (Over.mkIdTerminal.hom_ext _ _)⟩
  refine isLocallyOfFinitePresentation_terminal_of_affineLimit_surjective B S hS Y.property ?_
  intro I _ _ D c _ _ _ x
  obtain ⟨j⟩ : Nonempty I := IsCofiltered.nonempty
  exact ⟨colimit.ι (D.op ⋙ Y.obj) (op j)
    (((ObjectProperty.ι _).map e.inv).app (op (D.obj j)) (Over.mkIdTerminal.from (D.obj j))),
    @Subsingleton.elim _ (hsub (op c.pt)) _ _⟩

namespace ComplexesSituation

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

/-- **Stacks 0DLN, granted the results its proof uses.** For every scheme `S` of the site and
every situation `D` of Stacks 0DLE over `S`, `Complexes_{X/B}` is an algebraic stack over `S`.

This is `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_pending` with
its hypotheses for Stacks 0DLG, 0DLJ, 0DLL and 0DLM replaced by those of the lemmas which prove
them. The hypotheses are stated at the bases where the proof uses them:

* `h07Y4`: Stacks 07Y4, Artin's criterion, over `Spec Λ`.
* `h0CXU`: openness of versality for `Complexes_{X/B}` over `Spec Λ`.
* `h0DKY`: Stacks 0DKY, the dual of the relative derived Hom
  (`AlgebraicGeometry.Space.RelativeDerivedHomDualExists`); it gives Stacks 0DLC, part (1).
* `h0DLC3`: Stacks 0DLC, part (3), in the case `W = Y`
  (`AlgebraicGeometry.Space.RelativeDerivedHomRepresentableOfFibres`).
* `h0DKW`: Stacks 0DKW, relatively perfect objects over a limit are the colimit
  (`AlgebraicGeometry.Space.ComplexesSituation.RelativelyPerfectColimit`).
* `h0DIQ`: Stacks 0DIQ, Grothendieck existence for pseudo-coherent complexes, over `Spec Λ`, in
  the form of `AlgebraicGeometry.Space.ComplexesSituation.isEffective_formalObject_of`.
* `h0DLLT`, `h0DLLInf`: over `Spec Λ`, the finiteness of the tangent space and of the
  infinitesimal automorphisms of the fibre at every field point of finite type
  (`AlgebraicGeometry.Space.ComplexesSituation.FibreTangentFinite`,
  `AlgebraicGeometry.Space.ComplexesSituation.FibreInfFinite`).
* `h0DLA`: Stacks 0DLA, descent of complexes along Čech covers
  (`AlgebraicGeometry.Space.ComplexesSituation.CechDescent`); with the next two and Stacks 0DL1
  with 0DL2 (`AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectDescends`) it gives
  Stacks 0DLH (`ComplexesSituation.complexesFunctor_isStackInGroupoids_of_pending`).
* `h0DLDb`: Stacks 0DLD (b) at `V = T`, no negative self-extensions
  (`AlgebraicGeometry.Space.ComplexesSituation.HasNoNegativeSelfExt`).
* `h0DLC1desc`: the fibre condition descends along fppf coverings
  (`AlgebraicGeometry.Space.ComplexesSituation.NoNegativeFibreExtDescends`), the form of
  Stacks 0DLC (1) that the descent of 0DLH uses.
* `h07W3`: Stacks 07W3 over `Spec Λ`.
* `h0DL7`: Stacks 0DL7 over `Spec Λ`.
* `h0DL4`: Stacks 0DL4 over `Spec Λ`.
* `h08K0`, `h08K1`: Stacks 08K0 and 08K1 in their bound-free form.
* `hcomp`: the change-of-base comparison of Section 04X4 for `Complexes`, not a Stacks tag. -/
theorem isAlgebraicStack_complexes_of_held
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
    (h0DLDb : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.HasNoNegativeSelfExt)
    (h0DLC1desc : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.NoNegativeFibreExtDescends)
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
                (CategoryOfElements.π
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
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) := by
  -- Stacks 0DLF
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
      (h0DLG hT D') (h0DLJ hT D' hY) 𝒴 e.symm U hopen ?_ ?_
    · intro s
      obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ s)
      refine ⟨⟨W, hW⟩, ?_⟩
      show s ∈ Set.range hW.fromSpec
      rw [IsAffineOpen.range_fromSpec]
      exact hsW
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

end ComplexesSituation

end AlgebraicGeometry.Space

end
