module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryExtOne
public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedClasses

/-!
# The classes of `𝒪'₁` and `𝒪'₂` of Stacks 0GQ8 through canonical complexes

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi and `𝒪_{𝒞'}`, `𝒪_{𝒟'}`, `c : g^*ℱ ⟶ 𝒢` as in **Stacks 0GQ7**. **Stacks 0GQ8**
builds two extensions `𝒪'₁` (pushout of `g⁻¹𝒪_{𝒞'}` along `c`) and `𝒪'₂` (pullback of `𝒪_{𝒟'}`
along `g^♯`) of `g⁻¹𝒪_𝒞` by `𝒢` over `g⁻¹f⁻¹𝒪_ℬ`. This file writes their classes of
**Stacks 0GQ5** through the canonical naive cotangent complexes, by the formula
`squareZeroExtensionClassesEquiv_mk_eq_canonical` and the naturality of its ingredients along the
maps `g⁻¹𝒪_{𝒞'} ⟶ 𝒪'₁` and `𝒪'₂ ⟶ 𝒪_{𝒟'}`.

## Main results

* `Deformation.ToposThickening.LiftingMorphismDerived.pullbackSolution_class`: the class of `𝒪'₂`
  is the map of naive cotangent complexes of the square `(f ∘ g)⁻¹𝒪_ℬ ⟶ 𝒪_{𝒟'}` over `g^♯`,
  followed by the restriction of scalars of the formula for the class of `𝒪_{𝒟'}`.

## References

* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Deformation.ToposThickening.InverseImageExtension
open Deformation.ToposThickening.RingedToposExtensionProblem (ofTrivialBase)
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)
open Stacks.Sites.Conormal (conormalSheaf conormalSheafMapOfSquare conormalDesc kernelIdeal
  conormalClass)
open Stacks.Sites.SqZeroPullback (fibreSheaf fibreFst fibreSnd fibreLift fibreVal fibreMk
  fibreInr)

universe u v' u' w'

attribute [local instance 10000] HasDerivedCategory.standard

namespace Deformation.ToposThickening.LiftingMorphismDerived

variable {Y X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [Y.J.WEqualsLocallyBijective CommRingCat.{u}]
  {f : RingedToposHom X B} (g : RingedToposHom Y X)
  {F : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
  {G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)}
  (QC : (ofTrivialBase f F).CompatibleFirstOrderThickening)
  (QD : (ofTrivialBase (f.comp g) G).CompatibleFirstOrderThickening)
  (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G)

/-! ### The pullback `𝒪'₂ = 𝒪_{𝒟'} ×_{𝒪_𝒟} g⁻¹𝒪_𝒞` -/

section Pullback

/-- The first projection `𝒪'₂ ⟶ 𝒪_{𝒟'}`. -/
abbrev pullbackFst : (pullbackSolution g QC QD c).extension ⟶ QD.extension :=
  fibreFst QD.reduction g.fSharpInverseImage

/-- The square `𝒪'₂ ⟶ 𝒪_{𝒟'}` over `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟`. -/
theorem pullbackFst_comp_reduction :
    (pullbackSolution g QC QD c).reduction ≫ g.fSharpInverseImage =
      pullbackFst g QC QD c ≫ QD.reduction :=
  (Stacks.Sites.SqZeroPullback.fibreFst_comp_eq QD.reduction g.fSharpInverseImage).symm

/-- The structure map of `𝒪'₂` followed by the first projection is that of `𝒪_{𝒟'}`. -/
theorem baseMap_comp_pullbackFst :
    (pullbackSolution g QC QD c).baseMap ≫ pullbackFst g QC QD c = QD.baseMap :=
  (Category.assoc _ _ _).trans ((congrArg ((baseIso f g).symm.hom ≫ ·)
    (Stacks.Sites.SqZeroPullback.fibreLift_comp_fst QD.reduction g.fSharpInverseImage
      ((baseIso f g).hom ≫ QD.baseMap) _ (Data.ofSolutions g QC QD c).toData.base_comm)).trans
    (Iso.inv_hom_id_assoc (baseIso f g) QD.baseMap))

/-- The reduction map `𝒪'₂ ⟶ g⁻¹𝒪_𝒞` of the pullback solution is locally surjective. -/
instance isLocallySurjective_pullbackSolution_reduction :
    Presheaf.IsLocallySurjective Y.J (pullbackSolution g QC QD c).reduction.hom :=
  (pullbackSolution g QC QD c).locallySurjective

/-- The reduction map `𝒪_{𝒟'} ⟶ 𝒪_𝒟` is locally surjective. -/
instance isLocallySurjective_QD_reduction :
    Presheaf.IsLocallySurjective Y.J QD.reduction.hom :=
  QD.locallySurjective

/-- The first projection of `𝒪'₂` carries its square-zero ideal `𝒢` identically onto the
square-zero ideal `𝒢` of `𝒪_{𝒟'}`. -/
theorem pullbackFst_incl {U : Y.Cᵒᵖ} (n : G.val.obj U) :
    (pullbackFst g QC QD c).hom.app U ((pullbackSolution g QC QD c).incl n) = QD.incl n :=
  rfl

/-- The map of conormal sheaves along a square over `Q.reduction`, followed by the identification
`Ker/Ker² ⟶ 𝒢` of `Q`, sends a conormal class to the preimage under `Q.incl` of its image. -/
private theorem incl_kernelConormalToModule_conormalMap {S : RingedTopos.{u, u, u}}
    [S.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {f' : RingedToposHom S B}
    {G' : SheafOfModules.{u} ((sheafCompose S.J (forget₂ CommRingCat.{u} RingCat.{u})).obj S.O)}
    (Q : (ofTrivialBase f' G').CompatibleFirstOrderThickening) {A₁ B₁ : Sheaf S.J CommRingCat.{u}}
    (φ : A₁ ⟶ B₁) [Presheaf.IsLocallySurjective S.J φ.hom] (ψ : A₁ ⟶ Q.extension) (β : B₁ ⟶ S.O)
    (hsq : ψ ≫ Q.reduction = φ ≫ β) (U : S.Cᵒᵖ) (x : kernelIdeal φ.hom U) :
    Q.incl (Q.kernelConormalToModule.val.app U
      ((conormalSheafMapOfSquare.{u, u, u, u} S.J _ _ _ _ φ Q.reduction ψ β hsq).val.app U
        (Stacks.Sites.Conormal.conormalClass S.J _ _ _ (𝟙 _) φ U x))) = ψ.hom.app U x.1 := by
  have e₁ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} S.J _ _
    _ _ _ _ (𝟙 _) (𝟙 _) φ Q.reduction ψ β hsq U x
  have e₂ := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule Q.reduction
    (ofTrivialBase f' G').G Q.kernelIdentification U
    ⟨ψ.hom.app U x.1, Stacks.Sites.Conormal.kernelIdeal_le_comap_square _ _ _ _
      (Stacks.Sites.Conormal.hom_of_square hsq) U x.2⟩
  exact (congrArg Q.incl ((congrArg (fun t ↦ Q.kernelConormalToModule.val.app U t) e₁).trans
    e₂)).trans (Q.incl_kernelPreimage _)

/-- **The identification of the conormal sheaf of `𝒪'₂ ⟶ g⁻¹𝒪_𝒞` with `𝒢` factors through that
of `𝒪_{𝒟'} ⟶ 𝒪_𝒟`**: the map of conormal sheaves induced by the first projection, followed by
the identification for `𝒪_{𝒟'}`. -/
theorem conormalMap_comp_kernelConormalToModule :
    conormalSheafMapOfSquare.{u, u, u, u} Y.J _ _ _ _ (pullbackSolution g QC QD c).reduction
        QD.reduction (pullbackFst g QC QD c) g.fSharpInverseImage
        (pullbackFst_comp_reduction g QC QD c).symm ≫
      (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage)).map
        QD.kernelConormalToModule =
      (pullbackSolution g QC QD c).kernelConormalToModule := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun U x ↦ ?_)
  have e₃ := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule
    (pullbackSolution g QC QD c).reduction _ (pullbackSolution g QC QD c).kernelIdentification U x
  refine QD.incl_injective ((incl_kernelConormalToModule_conormalMap QD _ _ _
    (pullbackFst_comp_reduction g QC QD c).symm U x).trans ?_)
  refine Eq.trans ?_ (pullbackFst_incl g QC QD c _)
  exact congrArg ((pullbackFst g QC QD c).hom.app U)
    (((pullbackSolution g QC QD c).incl_kernelPreimage x).symm.trans (congrArg _ e₃.symm))

omit [HasWeakSheafify Y.J CommRingCat] [Y.J.WEqualsLocallyBijective CommRingCat] in
/-- The structure maps of `(Sh(𝒟), g⁻¹𝒪_𝒞)` and `(Sh(𝒟), 𝒪_𝒟)` over `(Sh(ℬ), 𝒪_ℬ)` form a
square over `g^♯`. -/
theorem fSharp_comp_fSharp_eq :
    (f.comp (toInverseImage g)).fSharpInverseImage ≫ g.fSharpInverseImage =
      𝟙 _ ≫ (f.comp g).fSharpInverseImage := by
  rw [Category.id_comp, comp_fSharpInverseImage_eq f g, ← baseIso_inv_comp_invImage_map f g]
  exact Category.assoc _ _ _

/-- The map `NL_{g⁻¹𝒪_𝒞/(f ∘ g)⁻¹𝒪_ℬ} ⟶ NL_{𝒪_𝒟/(f ∘ g)⁻¹𝒪_ℬ}` of **Stacks 08TX** attached to
`g^♯`, read through restriction of scalars along `g^♯`. -/
abbrev structureSquareMap :
    Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
        ((inverseImageCommRingFunctor (f.comp (toInverseImage g)).toToposHom).obj B.O)
        ((invImage g).obj X.O) (f.comp (toInverseImage g)).fSharpInverseImage ⟶
      ((SheafOfModules.restrictScalars
            (underlyingRingHomOfSite g.fSharpInverseImage)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
          ((inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O) Y.O
          (f.comp g).fSharpInverseImage) :=
  Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u, u, u} Y.J _ _
    (f.comp (toInverseImage g)).fSharpInverseImage _ Y.O (f.comp g).fSharpInverseImage (𝟙 _)
    g.fSharpInverseImage (fSharp_comp_fSharp_eq g)

/-- The base change of `𝒪'₂` followed by the map along `𝒪'₂ ⟶ 𝒪_{𝒟'}` over `g^♯` is the map along
`g^♯` followed by the base change of `𝒪_{𝒟'}` (the rectangle of Stacks 08TX maps). -/
theorem pullbackSolution_baseChange_rectangle :
    (pullbackSolution g QC QD c).naiveCotangentBaseChange ≫
        Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u, u, u} Y.J _ _
          (pullbackSolution g QC QD c).reduction _ Y.O QD.reduction (pullbackFst g QC QD c)
          g.fSharpInverseImage (pullbackFst_comp_reduction g QC QD c) =
      structureSquareMap g ≫
        ((SheafOfModules.restrictScalars
              (underlyingRingHomOfSite g.fSharpInverseImage)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map QD.naiveCotangentBaseChange :=
  Stacks.SheafOfModules.naiveCotangentComplexMap_rectangle Y.J
    (A := (inverseImageCommRingFunctor (f.comp (toInverseImage g)).toToposHom).obj B.O)
    (O := (invImage g).obj X.O) (B := Y.O)
    (A'' := (inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O)
    (E' := QD.extension) (E₂ := (pullbackSolution g QC QD c).extension)
    (f.comp (toInverseImage g)).fSharpInverseImage g.fSharpInverseImage (𝟙 _)
    (f.comp g).fSharpInverseImage
    (fSharp_comp_fSharp_eq g) QD.reduction QD.baseMap
    (RingedToposExtensionProblem.baseMap_comp_reduction_ofTrivialBase QD).symm
    (pullbackSolution g QC QD c).reduction (pullbackSolution g QC QD c).baseMap
    (RingedToposExtensionProblem.baseMap_comp_reduction_ofTrivialBase
      (pullbackSolution g QC QD c)).symm
    (pullbackFst g QC QD c) (pullbackFst_comp_reduction g QC QD c)
    ((baseMap_comp_pullbackFst g QC QD c).trans (Category.id_comp _).symm)

/-- The map of conormal sheaves along `𝒪'₂ ⟶ 𝒪_{𝒟'}` over `g^♯`. -/
abbrev pullbackConormalMap :
    conormalSheaf.{u, u, u, u} Y.J (pullbackSolution g QC QD c).extension ((invImage g).obj X.O)
        (pullbackSolution g QC QD c).reduction ⟶
      (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage)).obj
        (conormalSheaf.{u, u, u, u} Y.J QD.extension Y.O QD.reduction) :=
  conormalSheafMapOfSquare.{u, u, u, u} Y.J _ _ _ _ (pullbackSolution g QC QD c).reduction
    QD.reduction (pullbackFst g QC QD c) g.fSharpInverseImage
    (pullbackFst_comp_reduction g QC QD c).symm

/-- `η` along `𝒪'₂ ⟶ 𝒪_{𝒟'}`, in the derived category. -/
theorem inv_Q_map_eta_comp_pullbackConormalMap :
    haveI := Functor.isIso_Q_map_mapHomologicalComplex_map
      (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage))
      (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J QD.extension Y.O QD.reduction)
    inv (DerivedCategory.Q.map (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J
        (pullbackSolution g QC QD c).extension ((invImage g).obj X.O)
        (pullbackSolution g QC QD c).reduction)) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O))) (-1)).map
        (pullbackConormalMap g QC QD c)) =
      DerivedCategory.Q.map (Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u, u, u}
          Y.J _ _ (pullbackSolution g QC QD c).reduction _ Y.O QD.reduction
          (pullbackFst g QC QD c) g.fSharpInverseImage (pullbackFst_comp_reduction g QC QD c)) ≫
        inv (DerivedCategory.Q.map (((SheafOfModules.restrictScalars
          (underlyingRingHomOfSite g.fSharpInverseImage)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J QD.extension Y.O
            QD.reduction))) ≫
        DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage))
          (ComplexShape.up ℤ) (-1)).hom.app _) := by
  have h := Stacks.SheafOfModules.conormalToNaiveCotangentComplex_comp_mapOfSquare Y.J _ _
    (pullbackSolution g QC QD c).reduction _ _ QD.reduction (pullbackFst g QC QD c)
    g.fSharpInverseImage (pullbackFst_comp_reduction g QC QD c)
  rw [IsIso.inv_comp_eq, ← Category.assoc, ← Functor.map_comp, h]
  simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (DerivedCategory.Q.map_id _).symm)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [Y.J.HasSheafCompose (forget CommRingCat)] [Y.J.WEqualsLocallyBijective CommRingCat] in
/-- Restriction of scalars along `g^♯` of the formula for the class of `𝒪_{𝒟'}`. -/
theorem mapExtOne_canonical :
    haveI := Functor.isIso_Q_map_mapHomologicalComplex_map
      (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage))
      (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J QD.extension Y.O QD.reduction)
    (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage)).mapExtOne
        (DerivedCategory.Q.map QD.naiveCotangentBaseChange ≫
          inv (DerivedCategory.Q.map
            (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J QD.extension Y.O
              QD.reduction)) ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (-1)).map
            QD.kernelConormalToModule) ≫
          ((DerivedCategory.singleFunctors
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).shiftIso
            (1 : ℤ) (-1) 0 (by decide)).inv.app G) =
      DerivedCategory.Q.map (((SheafOfModules.restrictScalars
          (underlyingRingHomOfSite g.fSharpInverseImage)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map QD.naiveCotangentBaseChange) ≫
        inv (DerivedCategory.Q.map (((SheafOfModules.restrictScalars
          (underlyingRingHomOfSite g.fSharpInverseImage)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J QD.extension Y.O
            QD.reduction))) ≫
        DerivedCategory.Q.map (((SheafOfModules.restrictScalars
            (underlyingRingHomOfSite g.fSharpInverseImage)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (-1)).map
            QD.kernelConormalToModule) ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage))
            (ComplexShape.up ℤ) (-1)).hom.app G) ≫
        ((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app
          ((SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage)).obj G) :=
  (Functor.mapExtOne_Q_map_comp _ _ _).trans (congrArg (_ ≫ ·)
    ((Functor.mapExtOne_inv_Q_map_comp _ _ _).trans (congrArg (_ ≫ ·)
      (Functor.mapExtOne_Q_map_shiftIso _ _))))

/-- The composite of the base change of `𝒪'₂`, the inverse of its conormal comparison and the map
of conormal sheaves to `𝒢` equals the structure square map followed by the restriction of
scalars along `g^♯` of the corresponding composite for `𝒪_{𝒟'}`, in the derived category. -/
theorem pullbackSolution_class_aux :
    haveI := Functor.isIso_Q_map_mapHomologicalComplex_map
      (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage))
      (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J QD.extension Y.O QD.reduction)
    ((DerivedCategory.Q.map (pullbackSolution g QC QD c).naiveCotangentBaseChange ≫
        inv (DerivedCategory.Q.map (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J _ _
          (pullbackSolution g QC QD c).reduction))) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O))) (-1)).map
        (pullbackConormalMap g QC QD c ≫
          (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage)).map
            QD.kernelConormalToModule))) =
      ((DerivedCategory.Q.map (structureSquareMap g) ≫
        DerivedCategory.Q.map (((SheafOfModules.restrictScalars
          (underlyingRingHomOfSite g.fSharpInverseImage)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map QD.naiveCotangentBaseChange)) ≫
        inv (DerivedCategory.Q.map (((SheafOfModules.restrictScalars
          (underlyingRingHomOfSite g.fSharpInverseImage)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J QD.extension Y.O
            QD.reduction)))) ≫
        DerivedCategory.Q.map (((SheafOfModules.restrictScalars
            (underlyingRingHomOfSite g.fSharpInverseImage)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (-1)).map
            QD.kernelConormalToModule) ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage))
            (ComplexShape.up ℤ) (-1)).hom.app G) := by
  have hnat := (HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage))
    (ComplexShape.up ℤ) (-1)).hom.naturality QD.kernelConormalToModule
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, reassoc_of%
    inv_Q_map_eta_comp_pullbackConormalMap g QC QD c, ← Functor.map_comp_assoc,
    pullbackSolution_baseChange_rectangle g QC QD c, Functor.map_comp]
  simp only [Category.assoc]
  congr 3
  exact (Functor.map_comp _ _ _).symm.trans (congrArg DerivedCategory.Q.map hnat.symm)

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})] [HasWeakSheafify Y.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- Reassociation of an equality of composites followed by one more morphism. -/
private theorem comp_eq_of_assoc {𝒞 : Type*} [Category 𝒞] {V W X Y Z X' Y' Z' : 𝒞}
    {a : V ⟶ W} {b : W ⟶ X} {c : X ⟶ Y} {a' : V ⟶ X'} {b' : X' ⟶ Y'} {c' : Y' ⟶ Z'}
    {d' : Z' ⟶ Y} (h : (a ≫ b) ≫ c = ((a' ≫ b') ≫ c') ≫ d') (s : Y ⟶ Z) :
    a ≫ b ≫ c ≫ s = a' ≫ b' ≫ c' ≫ d' ≫ s := by
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc]

/-- **The class of `𝒪'₂` is the image of the class of `𝒪_{𝒟'}`** under restriction of scalars
along `g^♯`, precomposed with the map `NL_{g⁻¹𝒪_𝒞/(f ∘ g)⁻¹𝒪_ℬ} ⟶ NL_{𝒪_𝒟/(f ∘ g)⁻¹𝒪_ℬ}` of
Stacks 08TX attached to `g^♯`. -/
theorem pullbackSolution_class :
    RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp (toInverseImage g))
        (restrictedIdeal g G)
        (Quotient.mk (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
          (pullbackSolution g QC QD c)) =
      DerivedCategory.Q.map (structureSquareMap g) ≫
        (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage)).mapExtOne
          (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp g) G
            (Quotient.mk
              (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
              QD)) := by
  open RingedToposExtensionProblem in
  rw [CompatibleFirstOrderThickening.squareZeroExtensionClassesEquiv_mk_eq_canonical,
    CompatibleFirstOrderThickening.squareZeroExtensionClassesEquiv_mk_eq_canonical]
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (mapExtOne_canonical g QD).symm)
  rw [← conormalMap_comp_kernelConormalToModule g QC QD c]
  exact comp_eq_of_assoc (pullbackSolution_class_aux g QC QD c) _

end Pullback

/-! ### The pushout `𝒪'₁` of `g⁻¹𝒪_{𝒞'}` along `c` -/

section Pushout

/-- The map `g⁻¹𝒪_{𝒞'} ⟶ 𝒪'₁` of the first displayed diagram of Stacks 0GQ8. -/
abbrev pushoutIncl : (invImage g).obj QC.extension ⟶ (pushoutSolution g QC QD c).extension :=
  (Data.ofSolutions g QC QD c).toData.pushoutMap

/-- `g⁻¹𝒪_{𝒞'} ⟶ 𝒪'₁` lies over `g⁻¹𝒪_𝒞`. -/
theorem pushoutIncl_comp_reduction :
    pushoutIncl g QC QD c ≫ (pushoutSolution g QC QD c).reduction = (invImage g).map QC.reduction :=
  (Data.ofSolutions g QC QD c).toData.pushoutMap_comp_pushoutProj

/-- The map `g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞`, the inverse image of the reduction, is locally surjective. -/
instance isLocallySurjective_invImage_reduction :
    Presheaf.IsLocallySurjective Y.J ((invImage g).map QC.reduction).hom :=
  isLocallySurjective_invImage_map g QC.reduction QC.locallySurjective

/-- The reduction map `𝒪'₁ ⟶ g⁻¹𝒪_𝒞` of the pushout solution is locally surjective. -/
instance isLocallySurjective_pushoutSolution_reduction :
    Presheaf.IsLocallySurjective Y.J (pushoutSolution g QC QD c).reduction.hom :=
  (pushoutSolution g QC QD c).locallySurjective

/-- The map `Ker/Ker² ⟶ 𝒢` of the pushout datum: a local section of the kernel of
`g⁻¹`(reduction) is a section of `g⁻¹ℱ`, to which the adjoint of `c` is applied. -/
abbrev pushoutConormalToModule :
    conormalSheaf.{u, u, u, u} Y.J ((invImage g).obj QC.extension) ((invImage g).obj X.O)
        ((invImage g).map QC.reduction) ⟶ restrictedIdeal g G :=
  conormalDesc.{u, u, u, u} ((invImage g).map QC.reduction) (restrictedIdeal g G)
    (prescribedRestriction QC g c)

/-- **The identification of the conormal sheaf of `𝒪'₁ ⟶ g⁻¹𝒪_𝒞` with `𝒢` restricts to the
pushout datum** along `g⁻¹𝒪_{𝒞'} ⟶ 𝒪'₁`. -/
theorem conormalMapOfFac_comp_kernelConormalToModule :
    Stacks.SheafOfModules.conormalMapOfFac Y.J ((invImage g).obj QC.extension)
        ((invImage g).map QC.reduction) (pushoutIncl g QC QD c)
        (pushoutSolution g QC QD c).reduction (pushoutIncl_comp_reduction g QC QD c).symm ≫
      (pushoutSolution g QC QD c).kernelConormalToModule = pushoutConormalToModule g QC c := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun U x ↦ ?_)
  have e₃ := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule
    ((invImage g).map QC.reduction) (restrictedIdeal g G) (prescribedRestriction QC g c) U x
  have : Presheaf.IsLocallySurjective (inverseImageRingedTopos g).J
      ((invImage g).map QC.reduction).hom := isLocallySurjective_invImage_reduction g QC
  refine (pushoutSolution g QC QD c).incl_injective
    ((incl_kernelConormalToModule_conormalMap (pushoutSolution g QC QD c)
      ((invImage g).map QC.reduction) (pushoutIncl g QC QD c) (𝟙 _)
      (Stacks.SheafOfModules.comp_id_eq_comp_of_fac Y.J _ _ ((invImage g).map QC.reduction) _
        (pushoutSolution g QC QD c).reduction (pushoutIncl g QC QD c)
        (pushoutIncl_comp_reduction g QC QD c).symm).symm U x).trans ?_)
  refine Eq.trans ?_ (congrArg (pushoutSolution g QC QD c).incl e₃.symm)
  exact (Data.ofSolutions g QC QD c).toData.pushoutMap_app_kernel U x

end Pushout

/-- `g⁻¹` of the structure map `f⁻¹𝒪_ℬ ⟶ 𝒪_{𝒞'}` of the extension `𝒪_{𝒞'}`. -/
abbrev invBaseMap :
    (invImage g).obj ((inverseImageCommRingFunctor f.toToposHom).obj B.O) ⟶
      (invImage g).obj QC.extension :=
  (invImage g).map QC.baseMap

omit [HasWeakSheafify Y.J CommRingCat] [Y.J.WEqualsLocallyBijective CommRingCat] in
/-- The structure map `(f ∘ g)⁻¹𝒪_ℬ ⟶ g⁻¹f⁻¹𝒪_ℬ ⟶ g⁻¹𝒪_𝒞` of `(Sh(𝒟), g⁻¹𝒪_𝒞)`. -/
theorem fSharpInverseImage_toInverseImage_eq :
    (f.comp (toInverseImage g)).fSharpInverseImage =
      (baseIso f g).inv ≫ (invImage g).map f.fSharpInverseImage :=
  (baseIso_inv_comp_invImage_map f g).symm

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat]
  [Y.J.HasSheafCompose (forget CommRingCat)] [HasWeakSheafify Y.J CommRingCat]
  [Y.J.WEqualsLocallyBijective CommRingCat] in
/-- `g⁻¹` of the factorisation `f^♯ = (structure map) ≫ (reduction)` of `𝒪_{𝒞'}`. -/
theorem invImage_fSharp_eq :
    (invImage g).map f.fSharpInverseImage =
      invBaseMap g QC ≫ (invImage g).map QC.reduction :=
  (congrArg (invImage g).map
    (RingedToposExtensionProblem.baseMap_comp_reduction_ofTrivialBase QC)).symm.trans
    ((invImage g).map_comp _ _)

/-- The change of base ring `NL_{g⁻¹𝒪_𝒞/(f ∘ g)⁻¹𝒪_ℬ} ⟶ NL_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ}` of
**Stacks 08TX** along the identification `(f ∘ g)⁻¹𝒪_ℬ ≅ g⁻¹f⁻¹𝒪_ℬ`. -/
abbrev baseIsoChange :
    Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
        ((inverseImageCommRingFunctor (f.comp (toInverseImage g)).toToposHom).obj B.O)
        ((invImage g).obj X.O) (f.comp (toInverseImage g)).fSharpInverseImage ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
        ((invImage g).obj ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
        ((invImage g).obj X.O) ((invImage g).map f.fSharpInverseImage) :=
  Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{u, u, u, u} Y.J _
    ((invImage g).obj X.O) (f.comp (toInverseImage g)).fSharpInverseImage _
    ((invImage g).map f.fSharpInverseImage) (baseIso f g).inv
    (fSharpInverseImage_toInverseImage_eq g)

/-- The base change `NL_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ} ⟶ NL_{g⁻¹𝒪_𝒞/g⁻¹𝒪_{𝒞'}}` of **Stacks 08TX** along
`g⁻¹` of the structure map of `𝒪_{𝒞'}`. -/
abbrev invBaseChange :
    Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
        ((invImage g).obj ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
        ((invImage g).obj X.O) ((invImage g).map f.fSharpInverseImage) ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J ((invImage g).obj QC.extension)
        ((invImage g).obj X.O) ((invImage g).map QC.reduction) :=
  Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{u, u, u, u} Y.J _ _
    ((invImage g).map f.fSharpInverseImage) _ ((invImage g).map QC.reduction)
    (invBaseMap g QC) (invImage_fSharp_eq g QC)

/-- `g⁻¹𝒪_{𝒞'} ⟶ 𝒪'₁` lies over `g⁻¹𝒪_𝒞`, as a factorisation. -/
theorem invImage_reduction_eq :
    (invImage g).map QC.reduction =
      pushoutIncl g QC QD c ≫ (pushoutSolution g QC QD c).reduction :=
  (pushoutIncl_comp_reduction g QC QD c).symm

/-- The base change `NL_{g⁻¹𝒪_𝒞/g⁻¹𝒪_{𝒞'}} ⟶ NL_{g⁻¹𝒪_𝒞/𝒪'₁}` along `g⁻¹𝒪_{𝒞'} ⟶ 𝒪'₁`. -/
abbrev pushoutBaseChange :
    Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J ((invImage g).obj QC.extension)
        ((invImage g).obj X.O) ((invImage g).map QC.reduction) ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
        (pushoutSolution g QC QD c).extension ((invImage g).obj X.O)
        (pushoutSolution g QC QD c).reduction :=
  Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{u, u, u, u} Y.J _ _
    ((invImage g).map QC.reduction) _ (pushoutSolution g QC QD c).reduction
    (pushoutIncl g QC QD c) (invImage_reduction_eq g QC QD c)

/-- The map `(f ∘ g)^♯` factors as `(f ∘ g)⁻¹𝒪_ℬ ≅ g⁻¹f⁻¹𝒪_ℬ ⟶ g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞`. -/
theorem fSharp_eq_comp_invBaseMap :
    (f.comp (toInverseImage g)).fSharpInverseImage =
      ((baseIso f g).inv ≫ invBaseMap g QC) ≫ (invImage g).map QC.reduction := by
  rw [Category.assoc, ← invImage_fSharp_eq, fSharpInverseImage_toInverseImage_eq]

/-- The map `(f ∘ g)^♯` factors as `(f ∘ g)⁻¹𝒪_ℬ ≅ g⁻¹f⁻¹𝒪_ℬ ⟶ g⁻¹𝒪_{𝒞'} ⟶ 𝒪'₁ ⟶ g⁻¹𝒪_𝒞`. -/
theorem fSharp_eq_comp_pushoutIncl :
    (f.comp (toInverseImage g)).fSharpInverseImage =
      (((baseIso f g).inv ≫ invBaseMap g QC) ≫ pushoutIncl g QC QD c) ≫
        (pushoutSolution g QC QD c).reduction := by
  rw [Category.assoc, ← invImage_reduction_eq, ← fSharp_eq_comp_invBaseMap]

/-- The base change of `𝒪'₁` factors through those of `(f ∘ g)⁻¹𝒪_ℬ ≅ g⁻¹f⁻¹𝒪_ℬ`,
`g⁻¹f⁻¹𝒪_ℬ ⟶ g⁻¹𝒪_{𝒞'}` and `g⁻¹𝒪_{𝒞'} ⟶ 𝒪'₁`. -/
theorem pushoutSolution_naiveCotangentBaseChange_eq :
    (pushoutSolution g QC QD c).naiveCotangentBaseChange =
      (baseIsoChange g ≫ invBaseChange g QC) ≫ pushoutBaseChange g QC QD c :=
  (Stacks.SheafOfModules.naiveCotangentComplexMapOfBase_congr Y.J _ _ _
    (fSharp_eq_comp_pushoutIncl g QC QD c) (Category.assoc _ _ _).symm).trans
    ((congrArg (· ≫ pushoutBaseChange g QC QD c)
      (Stacks.SheafOfModules.naiveCotangentComplexMapOfBase_comp Y.J
        (f.comp (toInverseImage g)).fSharpInverseImage ((invImage g).map f.fSharpInverseImage)
        ((invImage g).map QC.reduction) (baseIso f g).inv (invBaseMap g QC)
        (fSharpInverseImage_toInverseImage_eq g) (invImage_fSharp_eq g QC)
        (fSharp_eq_comp_invBaseMap g QC))).trans
      (Stacks.SheafOfModules.naiveCotangentComplexMapOfBase_comp Y.J
        (f.comp (toInverseImage g)).fSharpInverseImage ((invImage g).map QC.reduction)
        (pushoutSolution g QC QD c).reduction ((baseIso f g).inv ≫ invBaseMap g QC)
        (pushoutIncl g QC QD c) (fSharp_eq_comp_invBaseMap g QC)
        (invImage_reduction_eq g QC QD c) (fSharp_eq_comp_pushoutIncl g QC QD c))).symm

/-- `η` along `g⁻¹𝒪_{𝒞'} ⟶ 𝒪'₁`, in the derived category. -/
theorem Q_map_pushoutBaseChange_comp_inv :
    DerivedCategory.Q.map (pushoutBaseChange g QC QD c) ≫
        inv (DerivedCategory.Q.map (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J _ _
          (pushoutSolution g QC QD c).reduction)) =
      inv (DerivedCategory.Q.map (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J
          ((invImage g).obj QC.extension) ((invImage g).obj X.O) ((invImage g).map QC.reduction))) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor
          (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O))) (-1)).map
          (Stacks.SheafOfModules.conormalMapOfFac Y.J ((invImage g).obj QC.extension)
            ((invImage g).map QC.reduction) (pushoutIncl g QC QD c)
            (pushoutSolution g QC QD c).reduction (invImage_reduction_eq g QC QD c))) := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, ← Functor.map_comp,
    Stacks.SheafOfModules.conormalToNaiveCotangentComplex_comp_mapOfBase, Functor.map_comp,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The class of `𝒪'₁` through canonical complexes**: the change of base ring
`(f ∘ g)⁻¹𝒪_ℬ ≅ g⁻¹f⁻¹𝒪_ℬ`, the base change of the naive cotangent complex of `g⁻¹𝒪_𝒞`
along `g⁻¹f⁻¹𝒪_ℬ ⟶ g⁻¹𝒪_{𝒞'}`, the inverse of `η` for `g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞`, and the
pushout datum `Ker/Ker² ⟶ 𝒢`. -/
theorem pushoutSolution_class :
    RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp (toInverseImage g))
        (restrictedIdeal g G)
        (Quotient.mk (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
          (pushoutSolution g QC QD c)) =
      DerivedCategory.Q.map
          (baseIsoChange g ≫ invBaseChange g QC) ≫
        inv (DerivedCategory.Q.map (Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J
          ((invImage g).obj QC.extension) ((invImage g).obj X.O) ((invImage g).map QC.reduction))) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor
          (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O))) (-1)).map
          (pushoutConormalToModule g QC c)) ≫
        ((DerivedCategory.singleFunctors
          (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O)))).shiftIso
          (1 : ℤ) (-1) 0 (by decide)).inv.app (restrictedIdeal g G) := by
  open RingedToposExtensionProblem in
  rw [CompatibleFirstOrderThickening.squareZeroExtensionClassesEquiv_mk_eq_canonical,
    pushoutSolution_naiveCotangentBaseChange_eq, Functor.map_comp, Category.assoc,
    reassoc_of% Q_map_pushoutBaseChange_comp_inv]
  congr 2
  rw [← conormalMapOfFac_comp_kernelConormalToModule g QC QD c]
  refine Eq.trans ?_ (congrArg (· ≫ _) (congrArg DerivedCategory.Q.map
    ((CochainComplex.singleFunctor
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O))) (-1)).map_comp
      _ _))).symm
  rw [Functor.map_comp, Category.assoc]
  rfl

end Deformation.ToposThickening.LiftingMorphismDerived

end
