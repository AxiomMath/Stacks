module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedBidual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedEvaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomRestrictionIsIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexCompositionComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility of the evaluation morphism of derived internal Homs is local on the site

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. Consider the evaluation
morphism of Stacks 0A97

`ev : RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`,

`AlgebraicGeometry.RingedSite.derivedSheafHomEvaluation`. This file proves that `ev` is an
isomorphism as soon as the evaluation morphism of internal Hom *complexes* of Stacks 0A92 formed
over each member of a family of objects covering the final object is a quasi-isomorphism.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_iff_quasiIso_ofModels`:
  invertibility of `ev` at arbitrary objects is quasi-isomorphy of `evaluationMap` at any choice
  of models — K-flat source, K-injective intermediate and target.
* `AlgebraicGeometry.RingedSite.quasiIso_restrictComplexMap_evaluationMap`: the restriction of
  `evaluationMap` to the site over `U` is a quasi-isomorphism as soon as the `evaluationMap`
  formed over `U` is.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_coversTop`: `ev` is an
  isomorphism as soon as the `evaluationMap` formed over each member of a family of objects
  covering the final object is a quasi-isomorphism.
* `AlgebraicGeometry.RingedSite.isIso_derivedBidual_iff`: the bidual map `K ⟶ (K^∨)^∨` is
  invertible exactly when `ev` at intermediate and target object the structure sheaf is.

## References

* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0G40](https://stacks.math.columbia.edu/tag/0G40)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

namespace AlgebraicGeometry.RingedSite

section Kit

variable (Y : RingedSite.{u, u, u})

/-- **The induced map of internal Hom complexes of two isomorphisms is an isomorphism.** -/
theorem isIso_homMap
    {K K' M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (k : K' ⟶ K) (m : M ⟶ M') [IsIso k] [IsIso m] : IsIso (homMap Y k m) := by
  refine ⟨homMap Y (inv k) (inv m), ?_, ?_⟩
  · rw [homMap_comp, IsIso.inv_hom_id, IsIso.hom_inv_id, homMap_id]
  · rw [homMap_comp, IsIso.hom_inv_id, IsIso.inv_hom_id, homMap_id]

/-- `isIso_homMap` with the first factor presented as an isomorphism and the second an
identity. -/
theorem isIso_homMap_hom_id
    {K K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (e : K ≅ K')
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    IsIso (homMap Y e.hom (𝟙 M)) :=
  isIso_homMap Y e.hom (𝟙 M)

/-- `isIso_tensorTotalMap` with the first factor presented as an isomorphism and the second an
identity. -/
theorem isIso_tensorTotalMap_hom_id
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (e : B ≅ B')
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    IsIso (tensorTotalMap Y e.hom (𝟙 A)) :=
  isIso_tensorTotalMap Y e.hom (𝟙 A)

/-- A commuting square whose two vertical edges are invertible: the two horizontal edges are
invertible together. -/
private theorem isIso_iff_of_square {D : Type*} [Category D] {P₁ P₂ P₃ P₄ : D}
    {f : P₁ ⟶ P₂} {v : P₂ ⟶ P₄} {uu : P₁ ⟶ P₃} {g : P₃ ⟶ P₄} [IsIso uu] [IsIso v]
    (h : f ≫ v = uu ≫ g) : IsIso f ↔ IsIso g := by
  rw [← isIso_comp_right_iff f v, h, isIso_comp_left_iff]

end Kit

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

section Maps

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)
variable
  {A₁ A₂ B₁ B₂ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- **The morphism of derived internal Homs induced by two isomorphisms is an isomorphism.** The
first variable is contravariant, so the isomorphism supplied there points from the second object
to the first. -/
theorem isIso_derivedSheafHomMap (a : A₂ ⟶ A₁) (b : B₁ ⟶ B₂) [IsIso a] [IsIso b] :
    IsIso (derivedSheafHomMap X Hd a b) := by
  refine ⟨derivedSheafHomMap X Hd (inv a) (inv b), ?_, ?_⟩
  · rw [derivedSheafHomMap_comp, IsIso.inv_hom_id, IsIso.hom_inv_id, derivedSheafHomMap_id]
  · rw [derivedSheafHomMap_comp, IsIso.hom_inv_id, IsIso.inv_hom_id, derivedSheafHomMap_id]

end Maps

section Models

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Invertibility of the evaluation morphism of derived internal Homs is quasi-isomorphy of
the evaluation morphism of internal Hom complexes at any models.** Let `A` be a K-flat complex
representing `K`, and let `B` and `C` be K-injective complexes representing `L` and `M`. Then the
morphism `ev` of Stacks 0A97 at `K`, `L`, `M` is invertible exactly when the morphism
`evaluationMap` of Stacks 0A92 at `A`, `B`, `C` is a quasi-isomorphism. -/
theorem isIso_derivedSheafHomEvaluation_iff_quasiIso_ofModels
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [B.IsKInjective] [C.IsKInjective]
    (eA : DerivedCategory.Q.obj A ≅ K) (eB : DerivedCategory.Q.obj B ≅ L)
    (eC : DerivedCategory.Q.obj C ≅ M) :
    IsIso (derivedSheafHomEvaluation X T Hd K L M) ↔ QuasiIso (evaluationMap X A B C) := by
  have : IsIso (derivedSheafHomMap X Hd eB.inv eC.hom) :=
    isIso_derivedSheafHomMap X Hd eB.inv eC.hom
  have : IsIso (derivedSheafHomMap X Hd eA.hom eB.inv) :=
    isIso_derivedSheafHomMap X Hd eA.hom eB.inv
  have : IsIso (derivedTensorMap X T (derivedSheafHomMap X Hd eB.inv eC.hom) eA.hom) :=
    isIso_derivedTensorMap X T _ _
  have : IsIso (derivedSheafHomMap X Hd
      (derivedSheafHomMap X Hd eA.hom eB.inv) eC.hom) :=
    isIso_derivedSheafHomMap X Hd _ _
  have htransport : IsIso (derivedSheafHomEvaluation X T Hd (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C)) ↔
      IsIso (derivedSheafHomEvaluation X T Hd K L M) :=
    isIso_iff_of_square
      (derivedSheafHomEvaluation_natural X T Hd eA.hom eB.inv eC.hom).symm
  have hmodel : IsIso (derivedSheafHomEvaluation X T Hd (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C)) ↔
      IsIso (DerivedCategory.Q.map (evaluationMap X A B C)) :=
    isIso_iff_of_square (derivedSheafHomEvaluation_model X T Hd A B C hA)
  exact htransport.symm.trans (hmodel.trans (DerivedCategory.isIso_Q_map_iff_quasiIso _ _))

end Models

section Slice

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The restriction of the evaluation morphism of Stacks 0A92 to a slice is a
quasi-isomorphism as soon as the evaluation morphism formed over that slice is.** -/
theorem quasiIso_restrictComplexMap_evaluationMap (U : X.C)
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (h : QuasiIso (evaluationMap (X.over U) (restrictComplex X A U) (restrictComplex X B U)
      (restrictComplex X C U))) :
    QuasiIso (restrictComplexMap X U (evaluationMap X A B C)) := by
  have hcm : ∀ P Q, IsIso ((derivedHomRestriction X U).complexMap P Q) := fun P Q =>
    isIso_of_isInternalHomRestrictionMap X U P Q _
      ((derivedHomRestriction X U).complexMap_isRestriction P Q)
  have htt : IsIso (tensorTotalMap (X.over U) ((derivedHomRestriction X U).complexMap B C)
      (𝟙 (restrictComplex X A U))) :=
    isIso_tensorTotalMap_hom_id (X.over U) (@asIso _ _ _ _ _ (hcm B C)) _
  have hhm : IsIso (homMap (X.over U) ((derivedHomRestriction X U).complexMap A B)
      (𝟙 (restrictComplex X C U))) :=
    isIso_homMap_hom_id (X.over U) (@asIso _ _ _ _ _ (hcm A B)) _
  have hQev : IsIso (DerivedCategory.Q.map (evaluationMap (X.over U)
      (restrictComplex X A U) (restrictComplex X B U) (restrictComplex X C U))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h
  have hQcm : IsIso (DerivedCategory.Q.map ((derivedHomRestriction X U).complexMap
      (sheafHomComplex X A B).obj C)) :=
    Iso.isIso_hom (DerivedCategory.Q.mapIso
      (@asIso _ _ _ _ _ (hcm (sheafHomComplex X A B).obj C)))
  have hQR : IsIso (DerivedCategory.Q.map
        (tensorTotalOverIso X U (sheafHomComplex X B C).obj A).hom ≫
      DerivedCategory.Q.map (tensorTotalMap (X.over U)
          ((derivedHomRestriction X U).complexMap B C) (𝟙 (restrictComplex X A U))) ≫
        DerivedCategory.Q.map (evaluationMap (X.over U) (restrictComplex X A U)
            (restrictComplex X B U) (restrictComplex X C U)) ≫
          DerivedCategory.Q.map (homMap (X.over U)
            ((derivedHomRestriction X U).complexMap A B) (𝟙 (restrictComplex X C U)))) :=
    Iso.isIso_hom
      (DerivedCategory.Q.mapIso (tensorTotalOverIso X U (sheafHomComplex X B C).obj A) ≪≫
        DerivedCategory.Q.mapIso (@asIso _ _ _ _ _ htt) ≪≫
          @asIso _ _ _ _ _ hQev ≪≫ DerivedCategory.Q.mapIso (@asIso _ _ _ _ _ hhm))
  have hsq : restrictComplexMap X U (evaluationMap X A B C) ≫
        (derivedHomRestriction X U).complexMap (sheafHomComplex X A B).obj C =
      (tensorTotalOverIso X U (sheafHomComplex X B C).obj A).hom ≫
        (tensorTotalMap (X.over U) ((derivedHomRestriction X U).complexMap B C)
            (𝟙 (restrictComplex X A U)) ≫
          evaluationMap (X.over U) (restrictComplex X A U) (restrictComplex X B U)
              (restrictComplex X C U) ≫
            homMap (X.over U) ((derivedHomRestriction X U).complexMap A B)
              (𝟙 (restrictComplex X C U))) :=
    (Iso.hom_inv_id_assoc (tensorTotalOverIso X U (sheafHomComplex X B C).obj A) _).symm.trans
      (congrArg
        (fun z => (tensorTotalOverIso X U (sheafHomComplex X B C).obj A).hom ≫ z)
        (evaluationMap_restrict_square X U A B C))
  have hfac : DerivedCategory.Q.map (restrictComplexMap X U (evaluationMap X A B C)) ≫
        DerivedCategory.Q.map ((derivedHomRestriction X U).complexMap
          (sheafHomComplex X A B).obj C) =
      DerivedCategory.Q.map (tensorTotalOverIso X U (sheafHomComplex X B C).obj A).hom ≫
        DerivedCategory.Q.map (tensorTotalMap (X.over U)
            ((derivedHomRestriction X U).complexMap B C) (𝟙 (restrictComplex X A U))) ≫
          DerivedCategory.Q.map (evaluationMap (X.over U) (restrictComplex X A U)
              (restrictComplex X B U) (restrictComplex X C U)) ≫
            DerivedCategory.Q.map (homMap (X.over U)
              ((derivedHomRestriction X U).complexMap A B) (𝟙 (restrictComplex X C U))) :=
    (CategoryTheory.Functor.map_comp _ _ _).symm.trans
      ((congrArg DerivedCategory.Q.map hsq).trans
        ((CategoryTheory.Functor.map_comp _ _ _).trans
          (congrArg
            (fun z => DerivedCategory.Q.map
                (tensorTotalOverIso X U (sheafHomComplex X B C).obj A).hom ≫ z)
            ((CategoryTheory.Functor.map_comp _ _ _).trans
              (congrArg
                (fun z => DerivedCategory.Q.map (tensorTotalMap (X.over U)
                    ((derivedHomRestriction X U).complexMap B C)
                    (𝟙 (restrictComplex X A U))) ≫ z)
                (CategoryTheory.Functor.map_comp _ _ _))))))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
    (@IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ hQcm hQR hfac)

end Slice

section Locality

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Invertibility of the evaluation morphism of derived internal Homs is local on the site.**
Let `V : ι → C` be a family of objects covering the final object of the site, let `A` be a K-flat
complex representing `K`, and let `B` and `C` be K-injective complexes representing `L` and `M`.
If the evaluation morphism of internal Hom complexes of Stacks 0A92 formed over each `V i`, at
the restrictions of `A`, `B` and `C`, is a quasi-isomorphism, then the evaluation morphism of
derived internal Homs of Stacks 0A97 at `K`, `L`, `M` is an isomorphism. -/
@[stacks 08JJ "the locality step for the evaluation morphism of Tag 0A97 only: invertibility of \
`ev : RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`, and hence of the bidual map \
`K ⟶ (K^∨)^∨` of `AlgebraicGeometry.RingedSite.derivedBidual`, may be checked after restriction \
to the slices over a family of objects covering the final object, where it becomes \
quasi-isomorphy of the evaluation morphism of internal Hom complexes of Tag 0A92. NONE of the \
four assertions of Tag 08JJ is proved here and in particular the bidual map is NOT shown to be \
invertible for a perfect K: quasi-isomorphy over each member of the covering family is a \
HYPOTHESIS below. The base case that discharges it — that `evaluationMap` is a \
quasi-isomorphism when its source complex is strictly perfect (Tag 08FL) — is \
`AlgebraicGeometry.RingedSite.quasiIso_evaluationMap_of_isStrictlyPerfect`, and the second \
assertion of Tag 08JJ follows from the two together, in \
`AlgebraicGeometry.RingedSite.isIso_derivedBidual_of_isPerfect`. The reduction performed here \
is the same one \
`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` performs for an arbitrary \
morphism of `D(Mod(O))`, but carried out at the chain level, because the derived evaluation \
morphism has no restriction compatibility of its own; the chain-level square it uses is \
`AlgebraicGeometry.RingedSite.evaluationMap_restrict_square`"]
theorem isIso_derivedSheafHomEvaluation_of_coversTop
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [B.IsKInjective] [C.IsKInjective]
    (eA : DerivedCategory.Q.obj A ≅ K) (eB : DerivedCategory.Q.obj B ≅ L)
    (eC : DerivedCategory.Q.obj C ≅ M)
    {ι : Type*} {V : ι → X.C} (hV : X.J.CoversTop V)
    (h : ∀ i, QuasiIso (evaluationMap (X.over (V i)) (restrictComplex X A (V i))
      (restrictComplex X B (V i)) (restrictComplex X C (V i)))) :
    IsIso (derivedSheafHomEvaluation X T Hd K L M) :=
  (isIso_derivedSheafHomEvaluation_iff_quasiIso_ofModels X T Hd K L M hA eA eB eC).2
    (Stacks.SheafOfModules.quasiIso_of_coversTop hV _
      fun i => quasiIso_restrictComplexMap_evaluationMap X (V i) A B C (h i))

end Locality

section Bidual

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X)

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The bidual map is invertible exactly when the evaluation morphism of Stacks 0A97 at
intermediate and target object the structure sheaf is.** The canonical map `K ⟶ (K^∨)^∨`,
`AlgebraicGeometry.RingedSite.derivedBidual`, is that evaluation morphism preceded by the unit
constraint `K ≅ O ⊗^L_O K` of Stacks 0FPT and by the identification `O ≅ RSheafHom(O, O)` of the
tensor factor. -/
theorem isIso_derivedBidual_iff
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (derivedBidual X T K) ↔
      IsIso (derivedSheafHomEvaluation X T (derivedInternalHomOfBifunctor X) K
        (derivedStructureSheaf X) (derivedStructureSheaf X)) := by
  have : IsIso ((T.tensor.map
      (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv).app K) :=
    NatIso.isIso_app_of_isIso
      (T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv) K
  exact (isIso_comp_left_iff
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
        (derivedTensorProductDatumOfSite X T) K).inv _).trans
    (isIso_comp_left_iff
      ((T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv).app K) _)

end Bidual

end AlgebraicGeometry.RingedSite

end
