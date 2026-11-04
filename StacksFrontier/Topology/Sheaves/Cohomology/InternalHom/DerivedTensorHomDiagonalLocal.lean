module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPseudoCoherent

/-!
# The diagonal of Stacks 0BYS is local on the site, degree by degree

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. This file proves two
statements about the diagonal of Stacks 0BYS,

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`.

*Locality.* If for every integer `n` there is a covering family `V` of the final object such
that, on each slice `C/V i`, the diagonal at the restrictions `K|_{V i}`, `L|_{V i}`, `M|_{V i}`
is invertible on `Hⁿ`, then the diagonal on `C` is an isomorphism. The covering is allowed to
depend on `n`.

*Comparison along a triangle.* Let `P ⟶ M ⟶ Z ⟶ P[1]` be a distinguished triangle with the
diagonal invertible at `P`. If `K ⊗^L_O RSheafHom(Z, L)` has no cohomology below `d₁` and
`RSheafHom(Z, K ⊗^L_O L)` none below `d₂`, the diagonal at `M` is invertible on `Hⁿ` for
`n < d₁ - 1` and `n < d₂ - 1`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedTensorHomDiagonal_iff_of_iso`: the
  degree-`n` invertibility of the diagonal depends only on the isomorphism classes of `K`, `L`,
  `M`.
* `AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedTensorHomDiagonal_of_distTriang`: the
  comparison along a triangle.
* `AlgebraicGeometry.RingedSite.isIso_homologyMap_restrictComplexMap_of_isIso_homologyMap`: the
  restriction to a slice of the complex-level morphism of Stacks 0BYR is invertible on `Hⁿ` as
  soon as the diagonal on the slice is.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_of_locally`: locality.
* `AlgebraicGeometry.RingedSite.nonempty_restrict_derivedTensor_iso`: restriction to a slice
  commutes with the derived tensor product, on objects.
* `isIso_homologyMap_restrictDerived_derivedTensorHomDiagonal_of_distTriang` (in the same
  namespace): the comparison along a triangle on a slice, for a triangle on the site.

## References

* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-- Invertibility of the image of a morphism under a functor is unchanged along an isomorphism
of arrows. -/
theorem isIso_map_iff_of_arrow_iso {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) (e₁ : a ≅ c) (e₂ : b ≅ d)
    (h : e₁.hom ≫ g = f ≫ e₂.hom) : IsIso (F.map f) ↔ IsIso (F.map g) :=
  (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
    (Arrow.isoMk (F.mapIso e₁) (F.mapIso e₂) (by
      simp only [Arrow.mk_hom, Functor.mapIso_hom, ← F.map_comp, h]))

section Diagonal

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- **The degree-`n` invertibility of the diagonal of Stacks 0BYS depends only on the isomorphism
classes of its three arguments.** -/
theorem isIso_homologyMap_derivedTensorHomDiagonal_iff_of_iso
    {K K' L L' M M' : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (eK : K ≅ K') (eL : L ≅ L') (eM : M ≅ M') (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map (derivedTensorHomDiagonal X K L M)) ↔
      IsIso ((DerivedCategory.homologyFunctor _ n).map
        (derivedTensorHomDiagonal X K' L' M')) := by
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n
  let T := Stacks.SheafOfModules.derivedTensorProductFunctor X
  let R := derivedSheafHomBifunctor X
  have h₁ : IsIso (H.map (derivedTensorHomDiagonal X K L M)) ↔
      IsIso (H.map (derivedTensorHomDiagonal X K' L M)) :=
    isIso_map_iff_of_arrow_iso H _ _ ((T.mapIso eK).app ((R.obj (op M)).obj L))
      ((R.obj (op M)).mapIso ((T.mapIso eK).app L))
      (derivedTensorHomDiagonal_natural_left X L M eK.hom)
  have h₂ : IsIso (H.map (derivedTensorHomDiagonal X K' L M)) ↔
      IsIso (H.map (derivedTensorHomDiagonal X K' L' M)) :=
    isIso_map_iff_of_arrow_iso H _ _ ((T.obj K').mapIso ((R.obj (op M)).mapIso eL))
      ((R.obj (op M)).mapIso ((T.obj K').mapIso eL))
      (derivedTensorHomDiagonal_natural_right X K' M eL.hom)
  have h₃ : IsIso (H.map (derivedTensorHomDiagonal X K' L' M')) ↔
      IsIso (H.map (derivedTensorHomDiagonal X K' L' M)) :=
    isIso_map_iff_of_arrow_iso H _ _ ((T.obj K').mapIso ((R.mapIso eM.op).app L'))
      ((R.mapIso eM.op).app ((T.obj K').obj L'))
      (derivedTensorHomDiagonal_natural_hom X K' L' eM.hom)
  exact h₁.trans (h₂.trans h₃.symm)

/-- **The diagonal of Stacks 0BYS is invertible on `Hⁿ` along a distinguished triangle.** Let
`P ⟶ M ⟶ Z ⟶ P[1]` be a distinguished triangle of `D(O)` such that the diagonal at `P` is an
isomorphism. If `K ⊗^L_O RSheafHom(Z, L)` has no cohomology below `d₁` and
`RSheafHom(Z, K ⊗^L_O L)` has none below `d₂`, then

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism on `Hⁿ` for every `n` with `n < d₁ - 1` and `n < d₂ - 1`. -/
theorem isIso_homologyMap_derivedTensorHomDiagonal_of_distTriang
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {P M Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (α : P ⟶ M) (g : M ⟶ Z) (δ : Z ⟶ P⟦(1 : ℤ)⟧)
    (hT : Triangle.mk α g δ ∈ distTriang _)
    (hP : IsIso (derivedTensorHomDiagonal X K L P)) (d₁ d₂ n : ℤ)
    (h₁ : (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
      (((derivedSheafHomBifunctor X).obj (op Z)).obj L)).IsGE d₁)
    (h₂ : (((derivedSheafHomBifunctor X).obj (op Z)).obj
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L)).IsGE d₂)
    (hn₁ : n < d₁ - 1) (hn₂ : n < d₂ - 1) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
        (derivedTensorHomDiagonal X K L M)) := by
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n
  obtain ⟨δ₁, hT₁⟩ := exists_distinguished_derivedSheafHom X L (Triangle.mk α g δ) hT
  obtain ⟨δ₂, hT₂⟩ := exists_distinguished_derivedSheafHom X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L)
    (Triangle.mk α g δ) hT
  have hTT := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map_distinguished
    _ hT₁
  have hu : IsIso (H.map (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
      (((derivedSheafHomBifunctor X).map α.op).app L))) :=
    DerivedCategory.isIso_homologyMap_mor₂_of_isGE₁ _ hTT n d₁ h₁ (by omega)
  have hv : IsIso (H.map (((derivedSheafHomBifunctor X).map α.op).app
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L))) :=
    DerivedCategory.isIso_homologyMap_mor₂_of_isGE₁ _ hT₂ n d₂ h₂ (by omega)
  have heq := congrArg H.map (derivedTensorHomDiagonal_natural_hom X K L α)
  rw [Functor.map_comp, Functor.map_comp] at heq
  have hcomp : IsIso (H.map (derivedTensorHomDiagonal X K L M) ≫
      H.map (((derivedSheafHomBifunctor X).map α.op).app
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L))) := by
    rw [← heq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (H.map (((derivedSheafHomBifunctor X).map α.op).app
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L)))

end Diagonal

section Slice

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The restriction to a slice of the complex-level morphism of Stacks 0BYR is invertible on `Hⁿ`
as soon as the diagonal on the slice is.** Here `A|_U` is K-flat, `I` and `J` are K-injective and
`q : Tot(A ⊗_O I) ⟶ J` is a quasi-isomorphism; the morphism is the one formed on `X` from these
models, restricted to `U`. -/
theorem isIso_homologyMap_restrictComplexMap_of_isIso_homologyMap
    (U : X.C) {A I N J : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat (X.over U).O (restrictComplex X A U))
    (q : tensorTotal X A I ⟶ J) [QuasiIso q] (n : ℤ)
    (hdiag : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) n).map
      (derivedTensorHomDiagonal (X.over U)
        (DerivedCategory.Q.obj (restrictComplex X A U))
        (DerivedCategory.Q.obj (restrictComplex X I U))
        (DerivedCategory.Q.obj (restrictComplex X N U))))) :
    IsIso (HomologicalComplex.homologyMap
      (restrictComplexMap X U (derivedTensorHomMapOfModels X (N := N) q)) n) := by
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
  have : (show CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ from
      restrictComplex X I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
  have : (show CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ from
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
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) n
  have hinner : IsIso (H.map (DerivedCategory.Q.map
      (derivedTensorHomMapOfModels (X.over U) (N := restrictComplex X N U)
        ((tensorTotalOverIso X U A I).inv ≫ restrictComplexMap X U q)))) := by
    rw [← derivedTensorHomDiagonal_eq_ofModels (X.over U)
      (DerivedCategory.Q.obj (restrictComplex X A U))
      (DerivedCategory.Q.obj (restrictComplex X I U))
      (DerivedCategory.Q.obj (restrictComplex X N U))
      hA (Iso.refl _) (Iso.refl _) (Iso.refl _) _ hq2]
    rw [Functor.map_comp, Functor.map_comp]
    have := hdiag
    infer_instance
  have hQcmJ : IsIso (DerivedCategory.Q.map ((derivedHomRestriction X U).complexMap N J)) :=
    Iso.isIso_hom (DerivedCategory.Q.mapIso
      (@asIso _ _ _ _ ((derivedHomRestriction X U).complexMap N J) hcmJ))
  have hQtt : IsIso (DerivedCategory.Q.map (tensorTotalMap (X.over U)
      (𝟙 (restrictComplex X A U)) ((derivedHomRestriction X U).complexMap N I))) :=
    Iso.isIso_hom (DerivedCategory.Q.mapIso (@asIso _ _ _ _ (tensorTotalMap (X.over U)
      (𝟙 (restrictComplex X A U)) ((derivedHomRestriction X U).complexMap N I)) htt))
  have hfacQ : DerivedCategory.Q.map (restrictComplexMap X U
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
  have hFfac : H.map (DerivedCategory.Q.map (restrictComplexMap X U
          (derivedTensorHomMapOfModels X (N := N) q))) ≫
        H.map (DerivedCategory.Q.map ((derivedHomRestriction X U).complexMap N J)) =
      H.map (DerivedCategory.Q.map
          (tensorTotalOverIso X U A (sheafHomComplex X N I).obj).hom) ≫
        H.map (DerivedCategory.Q.map (tensorTotalMap (X.over U) (𝟙 (restrictComplex X A U))
              ((derivedHomRestriction X U).complexMap N I))) ≫
          H.map (DerivedCategory.Q.map (derivedTensorHomMapOfModels (X.over U)
              (N := restrictComplex X N U) ((tensorTotalOverIso X U A I).inv ≫
                restrictComplexMap X U q))) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg H.map hfacQ).trans
        ((Functor.map_comp _ _ _).trans
          (congrArg (fun z => H.map (DerivedCategory.Q.map
            (tensorTotalOverIso X U A (sheafHomComplex X N I).obj).hom) ≫ z)
            (Functor.map_comp _ _ _))))
  refine (DerivedCategory.isIso_homologyFunctor_map_Q_map_iff _ n).1
    (@IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ ?_ ?_ hFfac)
  · exact Iso.isIso_hom (H.mapIso (@asIso _ _ _ _
      (DerivedCategory.Q.map ((derivedHomRestriction X U).complexMap N J)) hQcmJ))
  · refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ hinner)
    · exact Iso.isIso_hom (H.mapIso (DerivedCategory.Q.mapIso
        (tensorTotalOverIso X U A (sheafHomComplex X N I).obj)))
    · exact Iso.isIso_hom (H.mapIso (@asIso _ _ _ _
        (DerivedCategory.Q.map (tensorTotalMap (X.over U) (𝟙 (restrictComplex X A U))
          ((derivedHomRestriction X U).complexMap N I))) hQtt))

/-- The restriction of an object of `D(O)` to the slice over `U`. -/
abbrev restrictDerived (U : X.C) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) :=
  (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory

/-- The restriction to a slice of the class of a complex is the class of its restriction. -/
def restrictDerivedQIso (U : X.C)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (restrictDerived X U).obj (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj (restrictComplex X E U) :=
  (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    U).mapDerivedCategoryFactors.app E

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The diagonal of Stacks 0BYS is local on the site, degree by degree.** If for every integer
`n` there is a family `V` covering the final object such that, on every slice `C/V i`, the
diagonal at `K|_{V i}`, `L|_{V i}`, `M|_{V i}` is invertible on `Hⁿ`, then

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism. The covering may depend on `n`. -/
theorem isIso_derivedTensorHomDiagonal_of_locally
    [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ n : ℤ, ∃ (κ : Type u) (V : κ → X.C), X.J.CoversTop V ∧
      ∀ k, IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (V k)).O)) n).map
          (derivedTensorHomDiagonal (X.over (V k)) ((restrictDerived X (V k)).obj K)
            ((restrictDerived X (V k)).obj L) ((restrictDerived X (V k)).obj M)))) :
    IsIso (derivedTensorHomDiagonal X K L M) := by
  classical
  obtain ⟨A, fA, hAkf, hAflat, hAq, hAepi, hArestr⟩ :=
    Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall X.O
      (kFlatModel X K)
  have hfA : IsIso (DerivedCategory.Q.map fA) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hAq
  let eA : DerivedCategory.Q.obj A ≅ K := asIso (DerivedCategory.Q.map fA) ≪≫ kFlatModelIso X K
  let N := DerivedCategory.Q.objPreimage M
  let eN : DerivedCategory.Q.obj N ≅ M := DerivedCategory.Q.objObjPreimageIso M
  have hq : IsIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app
      (tensorTotal X A (kInjectiveModel X L)))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  rw [isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels X K L M hAkf eA
    (kInjectiveModelIso X L) eN
    ((kInjectiveAugmentation X).app (tensorTotal X A (kInjectiveModel X L))) hq]
  choose κ V hV hd using h
  refine Stacks.SheafOfModules.quasiIso_of_coversTop_degreewise hV _ ?_
  intro n k
  refine isIso_homologyMap_restrictComplexMap_of_isIso_homologyMap X (V n k) (hArestr (V n k))
    _ n ?_
  refine (isIso_homologyMap_derivedTensorHomDiagonal_iff_of_iso (X.over (V n k))
    ((restrictDerived X (V n k)).mapIso eA.symm ≪≫ restrictDerivedQIso X (V n k) A)
    ((restrictDerived X (V n k)).mapIso (kInjectiveModelIso X L).symm ≪≫
      restrictDerivedQIso X (V n k) _)
    ((restrictDerived X (V n k)).mapIso eN.symm ≪≫ restrictDerivedQIso X (V n k) N) n).1
    (hd n k)

/-- **Restriction to a slice commutes with the derived tensor product**, on objects: for
objects `K`, `L` of `D(O)` and an object `U` of the site,
`(K ⊗^L_O L)|_U ≅ K|_U ⊗^L_{O|_U} L|_U`. -/
theorem nonempty_restrict_derivedTensor_iso (U : X.C)
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    Nonempty ((restrictDerived X U).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) ≅
      ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).obj
        ((restrictDerived X U).obj K)).obj ((restrictDerived X U).obj L)) := by
  obtain ⟨A, fA, hAkf, hAflat, hAq, hAepi, hArestr⟩ :=
    Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall X.O
      (kFlatModel X K)
  have hfA : IsIso (DerivedCategory.Q.map fA) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hAq
  let eA : DerivedCategory.Q.obj A ≅ K := asIso (DerivedCategory.Q.map fA) ≪≫ kFlatModelIso X K
  let I := DerivedCategory.Q.objPreimage L
  let eI : DerivedCategory.Q.obj I ≅ L := DerivedCategory.Q.objObjPreimageIso L
  exact ⟨(restrictDerived X U).mapIso (derivedTensorObjectsIsoOfModels X hAkf eA eI) ≪≫
    restrictDerivedQIso X U _ ≪≫ DerivedCategory.Q.mapIso (tensorTotalOverIso X U A I) ≪≫
    (derivedTensorObjectsIsoOfModels (X.over U) (hArestr U)
      ((restrictDerived X U).mapIso eA.symm ≪≫ restrictDerivedQIso X U A).symm
      ((restrictDerived X U).mapIso eI.symm ≪≫ restrictDerivedQIso X U I).symm).symm⟩

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The diagonal of Stacks 0BYS on a slice, from a triangle on the site.** Let `U` be an object
of the site, `P ⟶ M ⟶ Z ⟶ P[1]` a distinguished triangle of `D(O)` and `f : L' ⟶ L` a morphism
of `D(O)` whose restriction to `U` is invertible. Suppose that `P|_U` is the class of a strictly
perfect complex, that `Z|_U` has no cohomology above `m - 1`,
and that `(K ⊗^L_O L')|_U` and `(K ⊗^L_O RSheafHom(Z, L'))|_U` have no cohomology below `c` and
`d`. Then the diagonal on the slice over `U`,

`K|_U ⊗^L RSheafHom(M|_U, L|_U) ⟶ RSheafHom(M|_U, K|_U ⊗^L L|_U)`,

is invertible on `Hⁿ` for every `n` with `n < d - 1` and `n < c - m`. -/
theorem isIso_homologyMap_restrictDerived_derivedTensorHomDiagonal_of_distTriang (U : X.C)
    (K L L' : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (f : L' ⟶ L) (hf : IsIso ((restrictDerived X U).map f))
    {P M Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (α : P ⟶ M) (g : M ⟶ Z) (δ : Z ⟶ P⟦(1 : ℤ)⟧) (hT : Triangle.mk α g δ ∈ distTriang _)
    {Ps : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ}
    (hPs : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) Ps)
    (ePs : DerivedCategory.Q.obj Ps ≅ (restrictDerived X U).obj P)
    (m c d n : ℤ) (hZ : ((restrictDerived X U).obj Z).IsLE (m - 1))
    (hc : ((restrictDerived X U).obj
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L')).IsGE c)
    (hd : ((restrictDerived X U).obj
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op Z)).obj L'))).IsGE d)
    (hn₁ : n < d - 1) (hn₂ : n < c - m) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) n).map
        (derivedTensorHomDiagonal (X.over U) ((restrictDerived X U).obj K)
          ((restrictDerived X U).obj L) ((restrictDerived X U).obj M))) := by
  refine (isIso_homologyMap_derivedTensorHomDiagonal_iff_of_iso (X.over U) (Iso.refl _)
    (@asIso _ _ _ _ ((restrictDerived X U).map f) hf) (Iso.refl _) n).1 ?_
  let : (restrictDerived X U).CommShift ℤ := inferInstanceAs ((SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.CommShift ℤ)
  have : (restrictDerived X U).IsTriangulated := inferInstanceAs
    ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.IsTriangulated)
  have hT' := (restrictDerived X U).map_distinguished _ hT
  obtain ⟨eKL⟩ := nonempty_restrict_derivedTensor_iso X U K L'
  obtain ⟨eKZ⟩ := nonempty_restrict_derivedTensor_iso X U K
    (((derivedSheafHomBifunctor X).obj (op Z)).obj L')
  have hKL : (((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).obj
      ((restrictDerived X U).obj K)).obj ((restrictDerived X U).obj L')).IsGE c :=
    DerivedCategory.TStructure.t.isGE_of_iso eKL c
  have hHZ : (((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).obj
      ((restrictDerived X U).obj K)).obj
        (((derivedSheafHomBifunctor (X.over U)).obj (op ((restrictDerived X U).obj Z))).obj
          ((restrictDerived X U).obj L'))).IsGE d :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (eKZ ≪≫ ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).obj
        ((restrictDerived X U).obj K)).mapIso ((derivedHomRestriction X U).iso Z L')) d
  have hP : IsIso (derivedTensorHomDiagonal (X.over U) ((restrictDerived X U).obj K)
      ((restrictDerived X U).obj L') ((restrictDerived X U).obj P)) :=
    isIso_derivedTensorHomDiagonal_of_isFiniteFreeSummand (X.over U) _ _ _ ePs hPs.bounded
      (fun i => IsDirectSummandOfFiniteFree.isFiniteFreeSummand (X.over U)
        (hPs.termDirectSummand i))
  exact isIso_homologyMap_derivedTensorHomDiagonal_of_distTriang (X.over U)
    ((restrictDerived X U).obj K) ((restrictDerived X U).obj L') _ _ _ hT' hP d (c - (m - 1)) n hHZ
    (isGE_derivedSheafHom (X.over U) _ _ (m - 1) c hZ hKL) hn₁ (by omega)

end Slice

end AlgebraicGeometry.RingedSite

end
