module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalStrictlyPerfect

/-!
# The diagonal of Stacks 0BYS at a perfect source: Stacks 0ATN part (1)

Let `X` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. The diagonal morphism of
Stacks 0BYS

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism as soon as `M` is **perfect**: locally on the site, `M` is represented by a
strictly perfect complex. This is Stacks 0ATN part (1), stated by
`isIso_derivedTensorHomDiagonal_of_isPerfect` at the site-level notion
`AlgebraicGeometry.RingedSite.IsPerfect` of Stacks 08G5
— the notion carrying the quasi-isomorphism slack, so that the strictly perfect complex found on
a member of the covering is only required to receive a quasi-isomorphism to the restriction of a
representative of `M`, not to be one.

The globally strictly perfect case is
`isIso_derivedTensorHomDiagonal_of_isFiniteFreeSummand`; everything here is the passage from
local to global. Invertibility of the diagonal is first replaced, once and for all, by
quasi-isomorphy of the complex-level morphism of Stacks 0BYR at one choice of models
(`isIso_derivedTensorHomDiagonal_of_coversTop`), because quasi-isomorphy of a morphism of
complexes is local on the site while the diagonal itself has no restriction compatibility to
hand. What remains is to identify the restriction of that morphism to a member `U` of a covering
with the same morphism formed on the site over `U`, which is
`restrictComplexMap_derivedTensorHomMapOfModels_comp_complexMap`: the interchange half is the
square `tensorHomInterchange_restrict_square` and the half induced by the resolution is
`complexMap_naturality_right`, and the two are joined by inserting the isomorphism
`tensorTotalOverIso` between the restriction of a total tensor complex and the total tensor
complex of the restrictions. The identification is an equality of morphisms up to the two
comparison maps `(derivedHomRestriction X U).complexMap`, which are isomorphisms by
`isIso_of_isInternalHomRestrictionMap`, so quasi-isomorphy transfers across it.

The models on the slice are then the restrictions of the chosen global ones. For this the
restriction of the chosen K-flat representative must itself be K-flat at every member of every
covering, which is what `exists_kFlatResolution_restriction_forall` provides, and the
restrictions of the K-injective representatives are K-injective by Stacks 08FI.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Remark 20.49.12 (Tag 0BYS)](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Lemma 20.47.3 (Tag 08FI)](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

section Kit

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Factoring an isomorphism of the target out of a map of internal Hom complexes.** For an
isomorphism `e : B ≅ B'` and a morphism `g : B ⟶ C`, the map `SheafHom(M, g)` is `SheafHom(M, e)`
followed by `SheafHom(M, e⁻¹ ≫ g)`. This is the device for rewriting a morphism of complexes
whose source is a restricted total tensor complex in terms of the total tensor complex of the
restrictions. -/
theorem homMap_id_factor_iso
    (M B B' C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : B ≅ B') (g : B ⟶ C) :
    homMap X (𝟙 M) g = homMap X (𝟙 M) e.hom ≫ homMap X (𝟙 M) (e.inv ≫ g) := by
  rw [homMap_comp, Category.comp_id, Iso.hom_inv_id_assoc]

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The total tensor product of an identity with an isomorphism is an isomorphism.** This is
`isIso_tensorTotalMap` in the shape in which the second factor is presented as an isomorphism
rather than as a morphism carrying an `IsIso` instance. -/
theorem isIso_tensorTotalMap_id_iso
    (A B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : B ≅ B') : IsIso (tensorTotalMap X (𝟙 A) e.hom) :=
  isIso_tensorTotalMap X (𝟙 A) e.hom

end Kit

section Slice

variable (U : X.C)
    {A I N J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The complex-level morphism of Stacks 0BYR commutes with restriction to a member of a
covering.** Restricting `Tot(A ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, J)` to the site over `U` and
composing with the comparison `SheafHom(N, J)|_U ⟶ SheafHom(N|_U, J|_U)` gives the same morphism
formed on the site over `U`, at the models `A|_U`, `I|_U`, `N|_U` and `J|_U` and the morphism
`tensorTotalOverIso⁻¹ ≫ q|_U`, read through the isomorphism `tensorTotalOverIso` of the source
and the isomorphism induced on the first factor by the comparison for `SheafHom(N, I)`. -/
theorem restrictComplexMap_derivedTensorHomMapOfModels_comp_complexMap
    [I.IsKInjective] [J.IsKInjective] (q : tensorTotal X A I ⟶ J) :
    restrictComplexMap X U (derivedTensorHomMapOfModels X (N := N) q) ≫
        (derivedHomRestriction X U).complexMap N J =
      (tensorTotalOverIso X U A (sheafHomComplex X N I).obj).hom ≫
        tensorTotalMap (X.over U) (𝟙 (restrictComplex X A U))
            ((derivedHomRestriction X U).complexMap N I) ≫
          derivedTensorHomMapOfModels (X.over U) (N := restrictComplex X N U)
            ((tensorTotalOverIso X U A I).inv ≫ restrictComplexMap X U q) :=
  calc restrictComplexMap X U (derivedTensorHomMapOfModels X (N := N) q) ≫
          (derivedHomRestriction X U).complexMap N J
      = restrictComplexMap X U (tensorHomInterchange X A I N) ≫
          (restrictComplexMap X U (homMap X (𝟙 N) q) ≫
            (derivedHomRestriction X U).complexMap N J) :=
        (congrArg (fun z => z ≫ (derivedHomRestriction X U).complexMap N J)
          (Functor.map_comp _ (tensorHomInterchange X A I N)
            (homMap X (𝟙 N) q))).trans (Category.assoc _ _ _)
    _ = restrictComplexMap X U (tensorHomInterchange X A I N) ≫
          ((derivedHomRestriction X U).complexMap N (tensorTotal X A I) ≫
            homMap (X.over U) (𝟙 (restrictComplex X N U)) (restrictComplexMap X U q)) :=
        congrArg (fun z => restrictComplexMap X U (tensorHomInterchange X A I N) ≫ z)
          (complexMap_naturality_right X U N (tensorTotal X A I) J q)
    _ = restrictComplexMap X U (tensorHomInterchange X A I N) ≫
          ((derivedHomRestriction X U).complexMap N (tensorTotal X A I) ≫
            (homMap (X.over U) (𝟙 (restrictComplex X N U))
                (tensorTotalOverIso X U A I).hom ≫
              homMap (X.over U) (𝟙 (restrictComplex X N U))
                ((tensorTotalOverIso X U A I).inv ≫ restrictComplexMap X U q))) :=
        congrArg (fun z => restrictComplexMap X U (tensorHomInterchange X A I N) ≫
          ((derivedHomRestriction X U).complexMap N (tensorTotal X A I) ≫ z))
          (homMap_id_factor_iso (X.over U) (restrictComplex X N U) _ _ _
            (tensorTotalOverIso X U A I) (restrictComplexMap X U q))
    _ = (restrictComplexMap X U (tensorHomInterchange X A I N) ≫
          (derivedHomRestriction X U).complexMap N (tensorTotal X A I) ≫
            homMap (X.over U) (𝟙 (restrictComplex X N U))
              (tensorTotalOverIso X U A I).hom) ≫
          homMap (X.over U) (𝟙 (restrictComplex X N U))
            ((tensorTotalOverIso X U A I).inv ≫ restrictComplexMap X U q) :=
        (congrArg (fun z => restrictComplexMap X U (tensorHomInterchange X A I N) ≫ z)
          (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm
    _ = ((tensorTotalOverIso X U A (sheafHomComplex X N I).obj).hom ≫
          tensorTotalMap (X.over U) (𝟙 (restrictComplex X A U))
              ((derivedHomRestriction X U).complexMap N I) ≫
            tensorHomInterchange (X.over U) (restrictComplex X A U) (restrictComplex X I U)
              (restrictComplex X N U)) ≫
          homMap (X.over U) (𝟙 (restrictComplex X N U))
            ((tensorTotalOverIso X U A I).inv ≫ restrictComplexMap X U q) :=
        congrArg (fun z => z ≫ homMap (X.over U) (𝟙 (restrictComplex X N U))
          ((tensorTotalOverIso X U A I).inv ≫ restrictComplexMap X U q))
          (tensorHomInterchange_restrict_square X U A I N)
    _ = _ := (Category.assoc _ _ _).trans (congrArg (fun z =>
          (tensorTotalOverIso X U A (sheafHomComplex X N I).obj).hom ≫ z)
          (Category.assoc _ _ _))

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The complex-level morphism of Stacks 0BYR restricts to a quasi-isomorphism over a member of
a covering on which the source is strictly perfect.** The hypotheses are the data of the models
on the site over `U`: `A|_U` is K-flat, `I` and `J` are K-injective — so that their restrictions
are, by Stacks 08FI — and `N|_U` receives a quasi-isomorphism from a strictly perfect complex
`P`, through `hqP`. Invertibility of the diagonal over `U` at the source `P` is the globally
strictly perfect theorem, the models criterion turns it back into quasi-isomorphy of the
morphism of complexes formed over `U`, and
`restrictComplexMap_derivedTensorHomMapOfModels_comp_complexMap` carries that to the
restriction of the morphism formed on `X`. -/
theorem quasiIso_restrictComplexMap_derivedTensorHomMapOfModels_of_isStrictlyPerfect
    [I.IsKInjective] [J.IsKInjective]
    (hA : letI : HasSheafify (X.over U).J AddCommGrpCat.{u} :=
            inferInstanceAs (HasSheafify (X.J.over U) AddCommGrpCat.{u})
          letI : (X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
            inferInstanceAs ((X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
          Stacks.SheafOfModules.IsKFlat (X.over U).O (restrictComplex X A U))
    (q : tensorTotal X A I ⟶ J) [QuasiIso q]
    {P : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P)
    (qP : P ⟶ restrictComplex X N U) (hqP : QuasiIso qP) :
    QuasiIso (restrictComplexMap X U (derivedTensorHomMapOfModels X (N := N) q)) := by
  have hcmJ : IsIso ((derivedHomRestriction X U).complexMap N J) :=
    isIso_of_isInternalHomRestrictionMap X U N J _
      ((derivedHomRestriction X U).complexMap_isRestriction N J)
  have hcmI : IsIso ((derivedHomRestriction X U).complexMap N I) :=
    isIso_of_isInternalHomRestrictionMap X U N I _
      ((derivedHomRestriction X U).complexMap_isRestriction N I)
  have htt : IsIso (tensorTotalMap (X.over U) (𝟙 (restrictComplex X A U))
      ((derivedHomRestriction X U).complexMap N I)) :=
    isIso_tensorTotalMap_id_iso (X.over U) (restrictComplex X A U) _ _
      (@asIso _ _ _ _ ((derivedHomRestriction X U).complexMap N I) hcmI)
  have hQq : IsIso (DerivedCategory.Q.map (restrictComplexMap X U q)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hQqP : IsIso (DerivedCategory.Q.map qP) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqP
  have : (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ from
      restrictComplex X I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
  have : (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ from
      restrictComplex X J U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U J
  have hq2 : IsIso (DerivedCategory.Q.map ((tensorTotalOverIso X U A I).inv ≫
      restrictComplexMap X U q)) := by
    have hmap : DerivedCategory.Q.map ((tensorTotalOverIso X U A I).inv ≫
          restrictComplexMap X U q) =
        DerivedCategory.Q.map (tensorTotalOverIso X U A I).inv ≫
          DerivedCategory.Q.map (restrictComplexMap X U q) :=
      Functor.map_comp _ _ _
    rw [hmap]
    exact Iso.isIso_hom (DerivedCategory.Q.mapIso (tensorTotalOverIso X U A I).symm ≪≫
      @asIso _ _ _ _ (DerivedCategory.Q.map (restrictComplexMap X U q)) hQq)
  let _ : HasSheafify (X.over U).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify (X.J.over U) AddCommGrpCat.{u})
  let _ : (X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
  have hdiag : IsIso (derivedTensorHomDiagonal (X.over U)
      (DerivedCategory.Q.obj (restrictComplex X A U))
      (DerivedCategory.Q.obj (restrictComplex X I U))
      (DerivedCategory.Q.obj (restrictComplex X N U))) :=
    isIso_derivedTensorHomDiagonal_of_isFiniteFreeSummand (X.over U)
      (DerivedCategory.Q.obj (restrictComplex X A U))
      (DerivedCategory.Q.obj (restrictComplex X I U))
      (DerivedCategory.Q.obj (restrictComplex X N U))
      (@asIso _ _ _ _ (DerivedCategory.Q.map qP) hQqP) hP.bounded
      (fun i => IsDirectSummandOfFiniteFree.isFiniteFreeSummand (X.over U)
        (hP.termDirectSummand i))
  have hinner : QuasiIso (derivedTensorHomMapOfModels (X.over U)
      (N := restrictComplex X N U) ((tensorTotalOverIso X U A I).inv ≫
        restrictComplexMap X U q)) :=
    (isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels (X.over U)
      (DerivedCategory.Q.obj (restrictComplex X A U))
      (DerivedCategory.Q.obj (restrictComplex X I U))
      (DerivedCategory.Q.obj (restrictComplex X N U))
      hA (Iso.refl _) (Iso.refl _) (Iso.refl _) _ hq2).1 hdiag
  have hQdthm : IsIso (DerivedCategory.Q.map (derivedTensorHomMapOfModels (X.over U)
      (N := restrictComplex X N U) ((tensorTotalOverIso X U A I).inv ≫
        restrictComplexMap X U q))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hinner
  have hQcmJ : IsIso (DerivedCategory.Q.map ((derivedHomRestriction X U).complexMap N J)) :=
    Iso.isIso_hom (DerivedCategory.Q.mapIso
      (@asIso _ _ _ _ ((derivedHomRestriction X U).complexMap N J) hcmJ))
  have hR : IsIso (DerivedCategory.Q.map
        (tensorTotalOverIso X U A (sheafHomComplex X N I).obj).hom ≫
      DerivedCategory.Q.map (tensorTotalMap (X.over U) (𝟙 (restrictComplex X A U))
          ((derivedHomRestriction X U).complexMap N I)) ≫
        DerivedCategory.Q.map (derivedTensorHomMapOfModels (X.over U)
          (N := restrictComplex X N U) ((tensorTotalOverIso X U A I).inv ≫
            restrictComplexMap X U q))) :=
    Iso.isIso_hom (DerivedCategory.Q.mapIso
        (tensorTotalOverIso X U A (sheafHomComplex X N I).obj) ≪≫
      DerivedCategory.Q.mapIso (@asIso _ _ _ _ (tensorTotalMap (X.over U)
          (𝟙 (restrictComplex X A U)) ((derivedHomRestriction X U).complexMap N I)) htt) ≪≫
        @asIso _ _ _ _ (DerivedCategory.Q.map (derivedTensorHomMapOfModels (X.over U)
          (N := restrictComplex X N U) ((tensorTotalOverIso X U A I).inv ≫
            restrictComplexMap X U q))) hQdthm)
  have hfac : DerivedCategory.Q.map (restrictComplexMap X U
          (derivedTensorHomMapOfModels X (N := N) q)) ≫
        DerivedCategory.Q.map ((derivedHomRestriction X U).complexMap N J) =
      DerivedCategory.Q.map (tensorTotalOverIso X U A (sheafHomComplex X N I).obj).hom ≫
        DerivedCategory.Q.map (tensorTotalMap (X.over U) (𝟙 (restrictComplex X A U))
            ((derivedHomRestriction X U).complexMap N I)) ≫
          DerivedCategory.Q.map (derivedTensorHomMapOfModels (X.over U)
            (N := restrictComplex X N U) ((tensorTotalOverIso X U A I).inv ≫
              restrictComplexMap X U q)) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg DerivedCategory.Q.map
      (restrictComplexMap_derivedTensorHomMapOfModels_comp_complexMap X U q)).trans
        ((Functor.map_comp _ _ _).trans
          (congrArg (fun z => DerivedCategory.Q.map
            (tensorTotalOverIso X U A (sheafHomComplex X N I).obj).hom ≫ z)
            (Functor.map_comp _ _ _))))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
    (@IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ hQcmJ hR hfac)

end Slice

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 0ATN part (1): the diagonal of Stacks 0BYS is an isomorphism at a perfect source.**
For objects `K`, `L`, `M` of `D(O)` with `M` perfect,

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism.

The only hypothesis is `X.IsPerfect M`, the site-level notion of Stacks 08G5: there is a complex
`N` representing `M` and a covering of the site on each member of which the restriction of `N`
receives a quasi-isomorphism from a strictly perfect complex. Nothing is assumed of `K` or `L`.

The instances in the ambient variable block are setup, not hypotheses on the lemma: a ringed site
whose slices admit sheafification and on which the tensor product of sheaves of modules is
additive and totalisable is what it takes for the objects in the statement — the derived tensor
product, the derived internal Hom, and their restrictions to the slices appearing in the
definition of perfection — to exist at all. A class needed only by the proof would have been an
extra hypothesis, and there is none. -/
@[stacks 0ATN "part (1)"]
theorem isIso_derivedTensorHomDiagonal_of_isPerfect
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hM : X.IsPerfect M) :
    IsIso (derivedTensorHomDiagonal X K L M) := by
  obtain ⟨N, hN, ⟨eN⟩⟩ := hM
  obtain ⟨Kidx, V, hV, hP⟩ := exists_coversTop_isStrictlyPerfect_of_isPerfectComplex X N hN
  obtain ⟨A, fA, hAkf, hAflat, hAq, hAepi, hArestr⟩ :=
    Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall X.O
      (kFlatModel X K)
  have hfA : IsIso (DerivedCategory.Q.map fA) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hAq
  refine isIso_derivedTensorHomDiagonal_of_coversTop X K L M hAkf
    (asIso (DerivedCategory.Q.map fA) ≪≫ kFlatModelIso X K) (kInjectiveModelIso X L) eN
    ((kInjectiveAugmentation X).app (tensorTotal X A (kInjectiveModel X L))) ?_ hV ?_
  · exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  · intro i
    obtain ⟨P, hPsp, qP, hqP⟩ := hP i
    exact quasiIso_restrictComplexMap_derivedTensorHomMapOfModels_of_isStrictlyPerfect X (V i)
      (hArestr (V i)) _ hPsp qP hqP

end AlgebraicGeometry.RingedSite

end
