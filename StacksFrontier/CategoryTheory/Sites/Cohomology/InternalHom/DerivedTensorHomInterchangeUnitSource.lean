module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf

/-!
# The interchange morphism of Tag 0BYU at the structure sheaf as internal-Hom source

Let `(𝒞, 𝒪)` be a ringed site. [Stacks, Tag 0BYU] supplies the canonical morphism

`Φ_{K, L, M} : K ⊗^𝐋_𝒪 R𝑆heafHom(M, L) ⟶ R𝑆heafHom(M, K ⊗^𝐋_𝒪 L)`,

`AlgebraicGeometry.RingedSite.derivedTensorHomInterchange`. This file computes it at
`M = 𝒪[0]`: there both sides are identified with `K ⊗^𝐋_𝒪 L` by the trivialisation
`R𝑆heafHom(𝒪[0], -) ≅ 𝟭` of `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`, and
**the interchange is the identity**.

That is the unit law of Tag 0BYU in its internal-Hom source, and it is the statement which,
combined with the functoriality of `Φ` in that slot, computes `Φ` against an arbitrary morphism
`P ⟶ 𝒪[0]`. The consumer is the comparison
`AlgebraicGeometry.RingedSite.interchangeDualComparison` of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPerfectDual`, whose
value against such a morphism the cone computation of [Stacks, Tag 0A0K] needs.

## Main results

* `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_hom_comp_kInjectiveAugmentation`:
  the value of the trivialisation `R𝑆heafHom(𝒪[0], -) ≅ 𝟭` at the class of an **arbitrary**
  complex, through the comparison with the chosen K-injective resolution.
* `AlgebraicGeometry.RingedSite.derivedTensorHomInterchange_comp_derivedStructureSheafHomIso`:
  **the unit law for the internal-Hom source of [Stacks, Tag 0BYU]**, for arbitrary `K` and `L`.

## The proof

At a model triple — `A` K-flat, `I` K-injective, and the structure sheaf complex as the
internal-Hom source — `AlgebraicGeometry.RingedSite.derivedTensorHomInterchange_comparison`
writes `Φ` as the class of the interchange morphism of complexes followed by the K-injective
resolution augmentation of `Tot(A ⊗_𝒪 I)`, read between the two identifications
`AlgebraicGeometry.RingedSite.interchangeSourceIso` and
`AlgebraicGeometry.RingedSite.interchangeTargetIso`. Against those two identifications the
statement becomes the chain-level one, because:

* evaluation at the unit section is natural in the target
  (`AlgebraicGeometry.RingedSite.structureSheafHomEvaluation_naturality`), which absorbs the
  resolution augmentation; and
* the identification of the source is literally the K-injective model comparison of the
  internal Hom followed by the K-flat comparison of the tensor product, so the naturality of
  the latter (`AlgebraicGeometry.RingedSite.tensorTotalKFlatComparison_natural`) turns the
  chain-level right-hand side into it.

The target `Tot(A ⊗_𝒪 I)` of the interchange is not K-injective even when `I` is, so the
trivialisation has to be evaluated at the class of an arbitrary complex; that is what
`derivedStructureSheafHomIso_hom_comp_kInjectiveAugmentation` is for. Its proof is the
K-injective case `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_model` released
along the resolution augmentation, the one point of interest being that the augmentation of a
chosen resolution and the resolution of an augmentation agree in the derived category — they
differ by a morphism which the augmentation, invertible there, cancels.

The passage from a model triple to arbitrary `K` and `L` is the functoriality of `Φ`
(`AlgebraicGeometry.RingedSite.derivedTensorHomInterchange_natural`) with an identity in the
internal-Hom source, together with the naturality of the trivialisation.

## Nothing here carries a Stacks attribute

Tag 0BYU asserts the morphism and its functoriality, both attributed in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomInterchange`; Tag 0BYT
asserts its chain-level counterpart. Neither tag, and no other tag of the Stacks Project,
asserts that either morphism is unital — the same judgement
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionUnit` makes for the
unit law of the composition morphism of Tag 0A98.

## References

* [Stacks Project, Tag 0BYU](https://stacks.math.columbia.edu/tag/0BYU)
* [Stacks Project, Tag 0BYT](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})

/-! ## The chain-level unit law

The chain-level statement — the interchange morphism of complexes of [Stacks, Tag 0BYT] out of a
structure-sheaf source, followed by evaluation at the unit section, is evaluation at the unit
section inside the tensor product — is
`AlgebraicGeometry.RingedSite.tensorHomInterchange_comp_structureSheafHomEvaluation` of
`StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.TensorHomTorAmplitudeComparison`. That
module is not imported here: its import closure carries the global instances of
`StacksFrontier.Homology.DerivedCategory.LocallySmall`, which displace the standard derived category
this file and its consumers work with. The one step below that needs the chain-level law proves
it in place, on homogeneous local pure tensors.
-/

/-! ## The trivialisation at the class of an arbitrary complex -/

section Derived

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] HasDerivedCategory.standard

/-- The class of the augmentation into the chosen K-injective resolution is invertible. -/
private lemma isIso_q_map_kInjectiveAugmentation
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app N)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

/-- Evaluation at the unit section is natural in the target, on classes in the derived
category. -/
private lemma q_map_homMap_comp_structureSheafHomEvaluation
    {N N' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : N ⟶ N') :
    DerivedCategory.Q.map (homMap X (𝟙 (structureSheafComplex X)) f) ≫
        DerivedCategory.Q.map (structureSheafHomEvaluation X N') =
      DerivedCategory.Q.map (structureSheafHomEvaluation X N) ≫ DerivedCategory.Q.map f := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (structureSheafHomEvaluation_naturality X f)

/-- The augmentation into the chosen K-injective resolution of a complex and the chosen
resolution of that augmentation become the same morphism in the derived category: the
augmentation, which is invertible there, cancels from the naturality square of the augmentation
at itself. -/
private lemma q_map_kInjectiveAugmentation_app_resolution
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.map
        ((kInjectiveAugmentation X).app ((kInjectiveResolution X).obj N)) =
      DerivedCategory.Q.map
        ((kInjectiveResolution X).map ((kInjectiveAugmentation X).app N)) := by
  have hnat := (kInjectiveAugmentation X).naturality ((kInjectiveAugmentation X).app N)
  rw [CategoryTheory.Functor.id_map] at hnat
  have h := congrArg DerivedCategory.Q.map hnat
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  exact (cancel_epi (DerivedCategory.Q.map ((kInjectiveAugmentation X).app N))).1 h

/-- **The trivialisation `R𝑆heafHom(𝒪[0], Z) ≅ Z` at the class of a K-injective complex**,
stated through the comparison with the chosen K-injective resolution rather than through the
K-injective model comparison: the resolution comparison followed by evaluation at the unit
section of the resolution. The two differ by the induced map of the augmentation, which
evaluation at the unit section is natural against. -/
private lemma derivedStructureSheafHomIso_hom_comp_kInjectiveAugmentation_of_isKInjective
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [N.IsKInjective] :
    (derivedStructureSheafHomIso X (DerivedCategory.Q.obj N)).hom ≫
        DerivedCategory.Q.map ((kInjectiveAugmentation X).app N) =
      (derivedSheafHomResolutionComparison X (structureSheafComplex X) N).hom ≫
        DerivedCategory.Q.map
          (structureSheafHomEvaluation X ((kInjectiveResolution X).obj N)) := by
  have hev := q_map_homMap_comp_structureSheafHomEvaluation X (N := N)
    ((kInjectiveAugmentation X).app N)
  rw [derivedStructureSheafHomIso_model X N]
  dsimp only [derivedSheafHomComparison, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [Category.assoc, Category.assoc, ← hev, IsIso.inv_hom_id_assoc]

/-- **The trivialisation `R𝑆heafHom(𝒪[0], Z) ≅ Z` at the class of an arbitrary complex.** Its
composite with the class of the augmentation into the chosen K-injective resolution is the
comparison with that resolution followed by evaluation at the unit section.

The augmentation is a quasi-isomorphism, so this determines the trivialisation at the class of
any complex; stating it in this composed form avoids naming the inverse. The proof releases the
K-injective case along the augmentation, using the naturality of the trivialisation, the
naturality of the resolution comparison, the naturality of evaluation at the unit section and
`q_map_kInjectiveAugmentation_app_resolution`. -/
theorem derivedStructureSheafHomIso_hom_comp_kInjectiveAugmentation
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedStructureSheafHomIso X (DerivedCategory.Q.obj N)).hom ≫
        DerivedCategory.Q.map ((kInjectiveAugmentation X).app N) =
      (derivedSheafHomResolutionComparison X (structureSheafComplex X) N).hom ≫
        DerivedCategory.Q.map
          (structureSheafHomEvaluation X ((kInjectiveResolution X).obj N)) := by
  have := isIso_q_map_kInjectiveAugmentation X ((kInjectiveResolution X).obj N)
  refine (cancel_mono (DerivedCategory.Q.map
    ((kInjectiveAugmentation X).app ((kInjectiveResolution X).obj N)))).1 ?_
  -- the trivialisation at `Q N`, pushed along the augmentation, is the one at its resolution
  have hnat : ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
          (DerivedCategory.Q.map ((kInjectiveAugmentation X).app N)) ≫
        (derivedStructureSheafHomIso X
          (DerivedCategory.Q.obj ((kInjectiveResolution X).obj N))).hom =
      (derivedStructureSheafHomIso X (DerivedCategory.Q.obj N)).hom ≫
        DerivedCategory.Q.map ((kInjectiveAugmentation X).app N) :=
    derivedStructureSheafHomIso_naturality X _
  -- the K-injective case, at the resolution
  have hJcase := derivedStructureSheafHomIso_hom_comp_kInjectiveAugmentation_of_isKInjective X
    ((kInjectiveResolution X).obj N)
  -- the resolution comparison, natural in the target
  have hres : ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
          (DerivedCategory.Q.map ((kInjectiveAugmentation X).app N)) ≫
        (derivedSheafHomResolutionComparison X (structureSheafComplex X)
          ((kInjectiveResolution X).obj N)).hom =
      (derivedSheafHomResolutionComparison X (structureSheafComplex X) N).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 (structureSheafComplex X))
          ((kInjectiveResolution X).map ((kInjectiveAugmentation X).app N))) := by
    have h := derivedSheafHomResolutionComparison_naturality X
      (𝟙 (structureSheafComplex X)) ((kInjectiveAugmentation X).app N)
    rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h
    exact h
  -- evaluation at the unit section, natural in the target
  have hev := q_map_homMap_comp_structureSheafHomEvaluation X (N := (kInjectiveResolution X).obj N)
    ((kInjectiveResolution X).map ((kInjectiveAugmentation X).app N))
  rw [← hnat, Category.assoc, hJcase, ← Category.assoc, hres, Category.assoc, hev,
    ← q_map_kInjectiveAugmentation_app_resolution, Category.assoc]

end Derived

/-! ## The unit law for the internal-Hom source of Tag 0BYU -/

section Interchange

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] HasDerivedCategory.standard

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The interchange morphism of complexes out of a structure-sheaf source, followed by the
K-injective resolution augmentation and then by evaluation at the unit section, is evaluation at
the unit section inside the tensor product followed by that augmentation. This is the chain-level
unit law with the augmentation moved across by the naturality of evaluation at the unit
section. -/
private lemma interchangeComplexMap_comp_structureSheafHomEvaluation
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    interchangeComplexMap X A I (structureSheafComplex X) ≫
        structureSheafHomEvaluation X
          ((kInjectiveResolution X).obj (tensorTotal X A I)) =
      tensorTotalMap X (𝟙 A) (structureSheafHomEvaluation X I) ≫
        (kInjectiveAugmentation X).app (tensorTotal X A I) := by
  have hev : homMap X (𝟙 (structureSheafComplex X))
          ((kInjectiveAugmentation X).app (tensorTotal X A I)) ≫
        structureSheafHomEvaluation X ((kInjectiveResolution X).obj (tensorTotal X A I)) =
      structureSheafHomEvaluation X (tensorTotal X A I) ≫
        (kInjectiveAugmentation X).app (tensorTotal X A I) :=
    structureSheafHomEvaluation_naturality X _
  have hunit : tensorHomInterchange X A I (structureSheafComplex X) ≫
        structureSheafHomEvaluation X (tensorTotal X A I) =
      tensorTotalMap X (𝟙 A) (structureSheafHomEvaluation X I) := by
    refine tensorTotal_hom_ext X fun U t r x φ ↦ ?_
    rw [HomologicalComplex.comp_f, comp_val_app_apply', structureSheafHomEvaluation_apply,
      tensorHomInterchange_applyHomSection X A I (structureSheafComplex X) U t r 0 r (t + r)
        (zero_add r) (by omega) x φ (structureSheafOne X U),
      tensorTotalMap_tensorTotalSection, ← structureSheafHomEvaluation_apply,
      tensorTotalSectionAt_self, HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app]
    rfl
  rw [interchangeComplexMap, Category.assoc, hev, ← Category.assoc, hunit]

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The unit law for the internal-Hom source of [Stacks, Tag 0BYU] at a model pair**: a K-flat
tensor factor `A` and a K-injective internal-Hom target `I`. -/
private lemma derivedTensorHomInterchange_comp_derivedStructureSheafHomIso_model
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] :
    derivedTensorHomInterchange X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I)
          (derivedStructureSheaf X) ≫
        (derivedStructureSheafHomIso X
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj I))).hom =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).map
        (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom := by
  have := isIso_q_map_kInjectiveAugmentation X (tensorTotal X A I)
  have : IsIso ((tensorTotalKFlatComparison X A I hA).hom ≫
      DerivedCategory.Q.map ((kInjectiveAugmentation X).app (tensorTotal X A I))) :=
    inferInstance
  -- the two identifications of Stacks 0BYU at a model triple, spelled out
  have hITI : (interchangeTargetIso X A I (structureSheafComplex X) hA).hom =
      ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
          (tensorTotalKFlatComparison X A I hA).hom ≫
        (derivedSheafHomResolutionComparison X (structureSheafComplex X)
          (tensorTotal X A I)).hom := rfl
  have hISI : (interchangeSourceIso X A I (structureSheafComplex X) hA).hom =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).map
            (derivedSheafHomComparison X (structureSheafComplex X) I).hom ≫
        (tensorTotalKFlatComparison X A
          (sheafHomComplex X (structureSheafComplex X) I).obj hA).hom := rfl
  -- the trivialisation of the target, carried across the K-flat comparison and down to the
  -- chosen K-injective resolution of the total tensor complex
  have htriv : (derivedStructureSheafHomIso X
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj I))).hom ≫
        (tensorTotalKFlatComparison X A I hA).hom ≫
          DerivedCategory.Q.map ((kInjectiveAugmentation X).app (tensorTotal X A I)) =
      (interchangeTargetIso X A I (structureSheafComplex X) hA).hom ≫
        DerivedCategory.Q.map (structureSheafHomEvaluation X
          ((kInjectiveResolution X).obj (tensorTotal X A I))) := by
    have hnat : ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
            (tensorTotalKFlatComparison X A I hA).hom ≫
          (derivedStructureSheafHomIso X
            (DerivedCategory.Q.obj (tensorTotal X A I))).hom =
        (derivedStructureSheafHomIso X
            (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
              (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj I))).hom ≫
          (tensorTotalKFlatComparison X A I hA).hom :=
      derivedStructureSheafHomIso_naturality X _
    rw [← reassoc_of% hnat, derivedStructureSheafHomIso_hom_comp_kInjectiveAugmentation, hITI]
    exact (Category.assoc _ _ _).symm
  -- the identification of the source, against the chain-level unit law
  have hsrc : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).map
            (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom ≫
        (tensorTotalKFlatComparison X A I hA).hom ≫
          DerivedCategory.Q.map ((kInjectiveAugmentation X).app (tensorTotal X A I)) =
      (interchangeSourceIso X A I (structureSheafComplex X) hA).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) (structureSheafHomEvaluation X I) ≫
          (kInjectiveAugmentation X).app (tensorTotal X A I)) := by
    have hcomp : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (DerivedCategory.Q.obj A)).map
              (DerivedCategory.Q.map (structureSheafHomEvaluation X I)) ≫
          (tensorTotalKFlatComparison X A I hA).hom =
        (tensorTotalKFlatComparison X A
            (sheafHomComplex X (structureSheafComplex X) I).obj hA).hom ≫
          DerivedCategory.Q.map
            (tensorTotalMap X (𝟙 A) (structureSheafHomEvaluation X I)) := by
      have h := tensorTotalKFlatComparison_natural X hA hA (𝟙 A)
        (structureSheafHomEvaluation X I)
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
        Category.id_comp] at h
      exact h
    rw [derivedStructureSheafHomIso_model X I, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, hISI]
    simp only [Category.assoc]
    rw [reassoc_of% hcomp]
    exact (Category.assoc _ _ _).symm
  -- the comparison of Stacks 0BYU with the interchange morphism of complexes, at this model
  have hcompar : derivedTensorHomInterchange X (DerivedCategory.Q.obj A)
          (DerivedCategory.Q.obj I) (derivedStructureSheaf X) ≫
        (interchangeTargetIso X A I (structureSheafComplex X) hA).hom =
      (interchangeSourceIso X A I (structureSheafComplex X) hA).hom ≫
        DerivedCategory.Q.map (interchangeComplexMap X A I (structureSheafComplex X)) :=
    derivedTensorHomInterchange_comparison X A I (structureSheafComplex X) hA
  have hcompar' : derivedTensorHomInterchange X (DerivedCategory.Q.obj A)
          (DerivedCategory.Q.obj I) (derivedStructureSheaf X) ≫
        (interchangeTargetIso X A I (structureSheafComplex X) hA).hom ≫
          DerivedCategory.Q.map (structureSheafHomEvaluation X
            ((kInjectiveResolution X).obj (tensorTotal X A I))) =
      (interchangeSourceIso X A I (structureSheafComplex X) hA).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) (structureSheafHomEvaluation X I) ≫
          (kInjectiveAugmentation X).app (tensorTotal X A I)) := by
    have h : (derivedTensorHomInterchange X (DerivedCategory.Q.obj A)
            (DerivedCategory.Q.obj I) (derivedStructureSheaf X) ≫
          (interchangeTargetIso X A I (structureSheafComplex X) hA).hom) ≫
            DerivedCategory.Q.map (structureSheafHomEvaluation X
              ((kInjectiveResolution X).obj (tensorTotal X A I))) =
        ((interchangeSourceIso X A I (structureSheafComplex X) hA).hom ≫
            DerivedCategory.Q.map (interchangeComplexMap X A I (structureSheafComplex X))) ≫
          DerivedCategory.Q.map (structureSheafHomEvaluation X
            ((kInjectiveResolution X).obj (tensorTotal X A I))) :=
      congrArg (fun z ↦ z ≫ DerivedCategory.Q.map (structureSheafHomEvaluation X
        ((kInjectiveResolution X).obj (tensorTotal X A I)))) hcompar
    refine (Category.assoc _ _ _).symm.trans (h.trans ((Category.assoc _ _ _).trans ?_))
    rw [← CategoryTheory.Functor.map_comp,
      interchangeComplexMap_comp_structureSheafHomEvaluation]
  refine (cancel_mono ((tensorTotalKFlatComparison X A I hA).hom ≫
    DerivedCategory.Q.map ((kInjectiveAugmentation X).app (tensorTotal X A I)))).1 ?_
  have key := ((congrArg (fun z ↦ derivedTensorHomInterchange X (DerivedCategory.Q.obj A)
      (DerivedCategory.Q.obj I) (derivedStructureSheaf X) ≫ z) htriv).trans
    hcompar').trans hsrc.symm
  exact (Category.assoc _ _ _).trans key

/-- **The unit law for the internal-Hom source of [Stacks, Tag 0BYU].** The interchange

`Φ_{K, L, 𝒪[0]} : K ⊗^𝐋_𝒪 R𝑆heafHom(𝒪[0], L) ⟶ R𝑆heafHom(𝒪[0], K ⊗^𝐋_𝒪 L)`,

read through the trivialisation `R𝑆heafHom(𝒪[0], -) ≅ 𝟭` on both sides, is the identity of
`K ⊗^𝐋_𝒪 L`: the trivialisation of the target is the trivialisation of `L` tensored with `K`.

The model case is the chain-level unit law
`AlgebraicGeometry.RingedSite.tensorHomInterchange_comp_structureSheafHomEvaluation`; the
passage to arbitrary `K` and `L` is the functoriality of `Φ` in its tensor factor and its
internal-Hom target, with an identity in its source, together with the naturality of the
trivialisation. -/
theorem derivedTensorHomInterchange_comp_derivedStructureSheafHomIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorHomInterchange X K L (derivedStructureSheaf X) ≫
        (derivedStructureSheafHomIso X
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L)).hom =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
        (derivedStructureSheafHomIso X L).hom := by
  have hmodel := derivedTensorHomInterchange_comp_derivedStructureSheafHomIso_model X
    (kFlatModel X K) (kInjectiveModel X L) (isKFlat_kFlatModel X K)
  -- the functoriality of the interchange, with an identity in the internal-Hom source
  have hnatΦ := derivedTensorHomInterchange_natural X (kFlatModelIso X K).hom
    (kInjectiveModelIso X L).hom (𝟙 (derivedStructureSheaf X))
  rw [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    NatTrans.id_app, Category.id_comp] at hnatΦ
  -- the naturality of the trivialisation at the comparison of the two model objects
  have htriv := derivedStructureSheafHomIso_naturality X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map (kFlatModelIso X K).hom).app
        (DerivedCategory.Q.obj (kInjectiveModel X L)) ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
        (kInjectiveModelIso X L).hom)
  -- the naturality of the trivialisation in the internal-Hom target
  have htrivL := derivedStructureSheafHomIso_naturality X (kInjectiveModelIso X L).hom
  -- the naturality of the tensor comparison in the tensor factor
  have htens := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
    (kFlatModelIso X K).hom).naturality
      (derivedStructureSheafHomIso X (DerivedCategory.Q.obj (kInjectiveModel X L))).hom
  have : IsIso (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        (kFlatModelIso X K).hom).app
      (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj
        (DerivedCategory.Q.obj (kInjectiveModel X L)))) :=
    NatIso.isIso_app_of_isIso _ _
  have : IsIso (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
      (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
        (kInjectiveModelIso X L).hom)) :=
    ((((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).mapIso
      (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).mapIso
        (kInjectiveModelIso X L))).isIso_hom)
  refine (cancel_epi (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (kFlatModelIso X K).hom).app
        (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj
          (DerivedCategory.Q.obj (kInjectiveModel X L))) ≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
      (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
        (kInjectiveModelIso X L).hom))).1 ?_
  simp only [Category.assoc]
  rw [reassoc_of% hnatΦ, htriv, reassoc_of% hmodel, reassoc_of% htens]
  simp only [← CategoryTheory.Functor.map_comp, htrivL]

end Interchange

end AlgebraicGeometry.RingedSite

end
