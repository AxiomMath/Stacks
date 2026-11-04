module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalStrictlyPerfectTensorFactor

/-!
# The diagonal of Stacks 0BYS at a perfect tensor factor: Stacks 0ATN part (2)

Let `X` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. The diagonal morphism of
Stacks 0BYS

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism as soon as `K` is **perfect**. This is Stacks 0ATN part (2), stated by
`isIso_derivedTensorHomDiagonal_of_isPerfect_tensorFactor` at the site-level notion
`AlgebraicGeometry.RingedSite.IsPerfect` of Stacks 08G5 — the notion carrying the
quasi-isomorphism slack, the same one part (1) is stated at. Nothing is assumed of `L` or `M`.

The globally strictly perfect case is
`isIso_derivedTensorHomDiagonal_of_isStrictlyPerfect_tensorFactor`; everything here is the
passage from local to global, and it is part (1)'s passage with only the slice-level input
changed. Two things make that possible, both established for part (1):
`isIso_derivedTensorHomDiagonal_of_coversTop` is indifferent to which of `K`, `L`, `M` the
covering came from, and `restrictComplexMap_derivedTensorHomMapOfModels_comp_complexMap` — the
identification of the restriction of the complex-level morphism of Stacks 0BYR with the morphism
formed over `U` — is a pure identity, so it is reused verbatim rather than reproved.

One difference of substance. For part (1) the perfection variable enters the invertibility
criterion only through its `eN`, and the complex the covering resolves is the very model the
criterion uses. Here the perfection variable is the tensor factor, whose model the criterion
requires to be K-flat, while the covering resolves an arbitrary representative of `K`. So the
K-flat resolution is taken **of that representative**, which makes the comparison between the
two a quasi-isomorphism of complexes; the slice-level input is then a derived isomorphism
assembled from it and from the covering's quasi-isomorphism.

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
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

section Slice

variable (U : X.C)
  {A I N J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The complex-level morphism of Stacks 0BYR restricts to a quasi-isomorphism over a member of
a covering on which the tensor factor is strictly perfect.** The hypotheses are the data of the
models on the site over `U`: `A|_U` is K-flat, `I` and `J` are K-injective — so that their
restrictions are, by Stacks 08FI — and `A|_U` is isomorphic in the derived category of the slice
to a strictly perfect complex `P`, through `eP`.

This is the companion of
`quasiIso_restrictComplexMap_derivedTensorHomMapOfModels_of_isStrictlyPerfect`, which is the same
step with the strict perfection on the source of the internal Hom. Only the slice-level input
differs: there the strictly perfect complex represents `N|_U` and enters through the criterion's
`eN`, here it represents `A|_U` and enters through its `eA`. The identification of the restricted
morphism with the one formed over `U`,
`restrictComplexMap_derivedTensorHomMapOfModels_comp_complexMap`, is a pure identity and is
reused verbatim.

The hypothesis is a derived isomorphism rather than a quasi-isomorphism of complexes because the
covering furnished by perfection resolves a representative of `K` which need not be the K-flat
model the criterion uses; the two are compared in the derived category of the slice. -/
theorem quasiIso_restrictComplexMap_derivedTensorHomMapOfModels_of_isStrictlyPerfect_tensorFactor
    [I.IsKInjective] [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat (X.O.over U) (restrictComplex X A U))
    (q : tensorTotal X A I ⟶ J) [QuasiIso q]
    {P : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P)
    (eP : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (restrictComplex X A U)) :
    QuasiIso (restrictComplexMap X U (derivedTensorHomMapOfModels X (N := N) q)) := by
  have hcm : ∀ B, IsIso ((derivedHomRestriction X U).complexMap N B) := fun B =>
    isIso_of_isInternalHomRestrictionMap X U N B _
      ((derivedHomRestriction X U).complexMap_isRestriction N B)
  have htt : IsIso (tensorTotalMap (X.over U) (𝟙 (restrictComplex X A U))
      ((derivedHomRestriction X U).complexMap N I)) :=
    isIso_tensorTotalMap_id_iso (X.over U) (restrictComplex X A U) _ _
      (@asIso _ _ _ _ ((derivedHomRestriction X U).complexMap N I) (hcm I))
  have hQq : IsIso (DerivedCategory.Q.map (restrictComplexMap X U q)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hinj : ∀ B : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ, B.IsKInjective →
      (show CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ from
        restrictComplex X B U).IsKInjective := fun B _ =>
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U B
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
  have hdiag :=
    @isIso_derivedTensorHomDiagonal_of_isStrictlyPerfect_tensorFactor (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ A, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj A).Additive)
      (inferInstance : ∀ K L : CochainComplex (SheafOfModules.{u}
          (ringSheaf (X.O.over U))) ℤ,
        HomologicalComplex.HasMapBifunctor K L
          (sheafTensor.{u, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ))
      (DerivedCategory.Q.obj (restrictComplex X A U))
      (DerivedCategory.Q.obj (restrictComplex X I U))
      (DerivedCategory.Q.obj (restrictComplex X N U)) P eP hP
  have hinner : QuasiIso (derivedTensorHomMapOfModels (X.over U)
      (N := restrictComplex X N U) ((tensorTotalOverIso X U A I).inv ≫
        restrictComplexMap X U q)) :=
    (@isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ A, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj A).Additive)
      (inferInstance : ∀ K L : CochainComplex (SheafOfModules.{u}
          (ringSheaf (X.O.over U))) ℤ,
        HomologicalComplex.HasMapBifunctor K L
          (sheafTensor.{u, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ))
      (DerivedCategory.Q.obj (restrictComplex X A U))
      (DerivedCategory.Q.obj (restrictComplex X I U))
      (DerivedCategory.Q.obj (restrictComplex X N U))
      (restrictComplex X A U) hA (Iso.refl _)
      (restrictComplex X I U) (hinj I ‹_›) (Iso.refl _)
      (restrictComplex X N U) (Iso.refl _)
      (restrictComplex X J U) (hinj J ‹_›) _ hq2).1 hdiag
  have hQdthm : IsIso (DerivedCategory.Q.map (derivedTensorHomMapOfModels (X.over U)
      (N := restrictComplex X N U) ((tensorTotalOverIso X U A I).inv ≫
        restrictComplexMap X U q))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hinner
  have hQcmJ : IsIso (DerivedCategory.Q.map ((derivedHomRestriction X U).complexMap N J)) :=
    Iso.isIso_hom (DerivedCategory.Q.mapIso
      (@asIso _ _ _ _ ((derivedHomRestriction X U).complexMap N J) (hcm J)))
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
/-- **Stacks 0ATN part (2): the diagonal of Stacks 0BYS is an isomorphism at a perfect tensor
factor.** For objects `K`, `L`, `M` of `D(O)` with `K` perfect,

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism.

The only hypothesis is `X.IsPerfect K`, the site-level notion of Stacks 08G5: there is a complex
`A₀` representing `K` and a covering of the site on each member of which the restriction of `A₀`
receives a quasi-isomorphism from a strictly perfect complex. Nothing is assumed of `L` or `M`.
This is the same notion, with the same slack, that part (1) assumes of `M`.

The instances in the ambient variable block are setup, not hypotheses on the lemma, exactly as
for part (1): a ringed site whose slices admit sheafification and on which the tensor product of
sheaves of modules is additive and totalisable is what it takes for the objects named in the
statement to exist. A class needed only by the proof would have been an extra hypothesis, and
there is none.

The K-flat resolution is taken of `A₀` itself rather than of the chosen K-flat model of `K`, so
that the comparison between the criterion's model and the complex the covering resolves is a
quasi-isomorphism of complexes and the slice-level input can be assembled from chain maps. -/
@[stacks 0ATN "part (2)"]
theorem isIso_derivedTensorHomDiagonal_of_isPerfect_tensorFactor
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    IsIso (derivedTensorHomDiagonal X K L M) := by
  obtain ⟨A₀, hA₀, ⟨eA₀⟩⟩ := hK
  obtain ⟨Kidx, V, hV, hP⟩ := exists_coversTop_isStrictlyPerfect_of_isPerfectComplex X A₀ hA₀
  obtain ⟨A, fA, hAkf, hAflat, hAq, hAepi, hArestr⟩ :=
    Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall X.O A₀
  have hfA : IsIso (DerivedCategory.Q.map fA) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hAq
  refine isIso_derivedTensorHomDiagonal_of_coversTop X K L M hAkf
    (asIso (DerivedCategory.Q.map fA) ≪≫ eA₀) (kInjectiveModelIso X L)
    (kInjectiveModelIso X M)
    ((kInjectiveAugmentation X).app (tensorTotal X A (kInjectiveModel X L))) ?_ hV ?_
  · exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  · intro i
    obtain ⟨P, hPsp, qP, hqP⟩ := hP i
    have hQqP : IsIso (DerivedCategory.Q.map qP) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqP
    have hQfA : IsIso (DerivedCategory.Q.map (restrictComplexMap X (V i) fA)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (by have := hAq; infer_instance)
    exact
      quasiIso_restrictComplexMap_derivedTensorHomMapOfModels_of_isStrictlyPerfect_tensorFactor
        X (V i) (hArestr (V i)) _ hPsp
        ((@asIso _ _ _ _ _ hQqP) ≪≫ (@asIso _ _ _ _ _ hQfA).symm)

end AlgebraicGeometry.RingedSite

end
