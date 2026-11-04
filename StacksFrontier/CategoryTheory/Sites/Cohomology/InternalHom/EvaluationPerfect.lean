module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationStrictlyPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.StrictlyPerfectIsKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
import StacksCore.Tactic.StacksAttribute

/-!
# The bidual map of a perfect object is an isomorphism

Let `(C, O)` be a ringed site and let `K` be a perfect object of `D(O)`. This file proves that
the canonical map `K ⟶ (K^∨)^∨`, `AlgebraicGeometry.RingedSite.derivedBidual`, is an
isomorphism.

## Main results

* `AlgebraicGeometry.RingedSite.quasiIso_evaluationMap_of_quasiIsoModels`: model independence of
  quasi-isomorphy of the evaluation morphism of Stacks 0A92 in its K-flat source.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_isPerfect`: the evaluation
  morphism of Stacks 0A97 is an isomorphism as soon as its tensor factor is perfect, with no
  condition on the other two objects.
* `AlgebraicGeometry.RingedSite.isIso_derivedBidual_of_isPerfect`: the map `K ⟶ (K^∨)^∨` is an
  isomorphism for a perfect `K`.

## References

* [Stacks Project, Lemma 36.10.12 (Tag 08JJ)](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Lemma 20.49.6 (Tag 0A92)](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Lemma 20.49.7 (Tag 0A97)](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Lemma 20.26.6 (Tag 06YU)](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Quasi-isomorphy of the evaluation morphism of Stacks 0A92 does not depend on which K-flat
model of the source is used.** Let `A` and `A₀` be K-flat complexes of `O`-modules with the same
class in `D(O)`, and let `B`, `C` be K-injective. Then

`Tot(SheafHom(B, C) ⊗_O A) ⟶ SheafHom(SheafHom(A, B), C)`

is a quasi-isomorphism, then so is the same morphism formed at `A₀`. -/
theorem quasiIso_evaluationMap_of_quasiIsoModels
    {A A₀ B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hA₀ : Stacks.SheafOfModules.IsKFlat X.O A₀)
    [B.IsKInjective] [C.IsKInjective]
    (e : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj A₀)
    (h : QuasiIso (evaluationMap X A B C)) :
    QuasiIso (evaluationMap X A₀ B C) :=
  (isIso_derivedSheafHomEvaluation_iff_quasiIso_ofModels X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) (derivedInternalHomOfBifunctor X)
      (DerivedCategory.Q.obj A₀) (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C)
      hA₀ (Iso.refl _) (Iso.refl _) (Iso.refl _)).1
    ((isIso_derivedSheafHomEvaluation_iff_quasiIso_ofModels X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) (derivedInternalHomOfBifunctor X)
      (DerivedCategory.Q.obj A₀) (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C)
      hA e (Iso.refl _) (Iso.refl _)).2 h)

section Perfect

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)

/-- The isomorphism in `D(O)` induced by a quasi-isomorphism of complexes. -/
private def asIsoQMap {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
    {K L : CochainComplex 𝒜 ℤ} {φ : K ⟶ L} (hφ : QuasiIso φ) :
    DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L :=
  @asIso _ _ _ _ _ ((DerivedCategory.isIso_Q_map_iff_quasiIso (φ := φ)).2 hφ)

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **The evaluation morphism of derived internal Homs of Stacks 0A97 is an isomorphism at a
perfect tensor factor.** For objects `K`, `L`, `M` of `D(O)` with `K` perfect,

`ev : RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`

is an isomorphism. -/
theorem isIso_derivedSheafHomEvaluation_of_isPerfect
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    IsIso (derivedSheafHomEvaluation X T Hd K L M) := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := hK
  obtain ⟨ι, V, hV, hP⟩ := exists_coversTop_isStrictlyPerfect_of_isPerfectComplex X E hE
  obtain ⟨A, fA, hAkf, hAflat, hAq, hAepi, hArestr⟩ :=
    Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall X.O E
  refine isIso_derivedSheafHomEvaluation_of_coversTop X T Hd K L M hAkf
    (asIsoQMap hAq ≪≫ eE) (kInjectiveModelIso X L) (kInjectiveModelIso X M) hV ?_
  intro i
  let : HasSheafify (X.over (V i)).J AddCommGrpCat.{u} :=
    show HasSheafify (X.J.over (V i)) AddCommGrpCat.{u} from inferInstance
  let : (X.over (V i)).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    show (X.J.over (V i)).WEqualsLocallyBijective AddCommGrpCat.{u} from inferInstance
  obtain ⟨P, hPsp, q, hq⟩ := hP i
  have : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (V i)).PreservesHomology :=
    Stacks.SheafOfModules.preservesHomology_overFunctor (V i)
  have hKi (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      [N.IsKInjective] :
      (show CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (V i)).O)) ℤ from
        restrictComplex X N (V i)).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i) N
  have := hKi (kInjectiveModel X L)
  have := hKi (kInjectiveModel X M)
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
    (X.over (V i)).O
  exact quasiIso_evaluationMap_of_quasiIsoModels (X.over (V i))
    (kFlat_of_isStrictlyPerfect (X.over (V i)) P hPsp) (hArestr (V i))
    (asIsoQMap hq ≪≫ (asIsoQMap (inferInstance : QuasiIso (restrictComplexMap X (V i) fA))).symm)
    (quasiIso_evaluationMap_of_isStrictlyPerfect (X.over (V i)) P _ _ hPsp)

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **The bidual map of a perfect object is an isomorphism.** For a perfect object
`K` of `D(O)` the canonical map

`K ⟶ (K^∨)^∨`

of `AlgebraicGeometry.RingedSite.derivedBidual` is an isomorphism, where `K^∨` is the derived
dual `RSheafHom(K, O)`. -/
@[stacks 08JJ "the canonical map `K ⟶ (K^∨)^∨` is an isomorphism for a perfect object `K` of \
`D(O)`, where `K^∨` is the derived dual `RSheafHom_O(K, O)`; this is one of the four assertions \
of the tag, and the hypothesis is perfection of `K` alone"]
theorem isIso_derivedBidual_of_isPerfect
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    IsIso (derivedBidual X T K) :=
  (isIso_derivedBidual_iff X T K).2
    (isIso_derivedSheafHomEvaluation_of_isPerfect X T (derivedInternalHomOfBifunctor X) K
      (derivedStructureSheaf X) (derivedStructureSheaf X) hK)

end Perfect

end AlgebraicGeometry.RingedSite

end
