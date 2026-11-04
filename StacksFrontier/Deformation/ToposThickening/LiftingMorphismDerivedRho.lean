module

public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedUnit
public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismInverseImageClasses

/-!
# Reading classes on `Lg^*NL_{𝒪_𝒞/𝒪_ℬ}` over `g⁻¹𝒪_𝒞`

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi. **Stacks 0GQ8** compares `Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)` with
`Ext¹_{g⁻¹𝒪_𝒞}(NL_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ}, 𝒢)`, through `NL_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ} = g⁻¹NL_{𝒪_𝒞/𝒪_ℬ}`
(**Stacks 08TZ**) and the adjunction between `Lg^*` and restriction of scalars along `g^♯`.
This file builds the map `rhoClass` in that direction: a class `e : Lg^*NL ⟶ 𝒢[1]` goes to
`g⁻¹NL ⟶ Lg^*NL ⟶ 𝒢[1]` read over `g⁻¹𝒪_𝒞`, through the derived unit `g⁻¹ ⟶ Lg^* ⋙ res`. It
computes `rhoClass` on the image of `ζ`: it is the class of the extension `𝒪'₂` of Stacks 0GQ8.

## Main definitions

* `Deformation.ToposThickening.LiftingMorphismDerived.rhoClass`.

## Main results

* `Deformation.ToposThickening.LiftingMorphismDerived.rhoClass_restrictExtClass`: `rhoClass`
  carries the image of `ζ` to the class of `𝒪'₂`.

## References

* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8)
* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sheaves.RingedToposModules (inverseImageModules)
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Deformation.ToposThickening.InverseImageExtension
open Deformation.ToposThickening.RingedToposExtensionProblem (ofTrivialBase)
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

universe u v' u' w'

attribute [local instance 10000] HasDerivedCategory.standard

namespace Deformation.ToposThickening.LiftingMorphismDerived

variable {X Y : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  {f : RingedToposHom X B} (g : RingedToposHom Y X)
  {G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)}

/-- **A class on `Lg^*NL_{𝒪_𝒞/𝒪_ℬ}` read over `g⁻¹𝒪_𝒞`**: for `e : Lg^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ 𝒢[1]`,
the composite `NL_{g⁻¹𝒪_𝒞/(f ∘ g)⁻¹𝒪_ℬ} ≅ g⁻¹NL_{𝒪_𝒞/𝒪_ℬ} ⟶ res(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}) ⟶ res(𝒢[1])`
of the change of base ring, the inverse of the identification of Stacks 08TZ, the derived unit
and the restriction of scalars of `e`, with `res(𝒢[1]) = (res 𝒢)[1]`. -/
def rhoClass
    (e : DerivedCategory.Ext ((derivedPullback g).obj (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage)))
      ((DerivedCategory.singleFunctor _ 0).obj G) 1) :
    DerivedCategory.Q.obj (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
        ((inverseImageCommRingFunctor (f.comp (toInverseImage g)).toToposHom).obj B.O)
        ((invImage g).obj X.O) (f.comp (toInverseImage g)).fSharpInverseImage) ⟶
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O))) 0).obj
          (restrictedIdeal g G))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (baseIsoChange g) ≫
    DerivedCategory.Q.map
      (Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso.{u, u, u, u, u, u}
        Y.J X.J g.toToposHom (A := (inverseImageCommRingFunctor f.toToposHom).obj B.O) (B := X.O)
        f.fSharpInverseImage).inv ≫
    (inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactors.inv.app _ ≫
    (derivedUnit g).app _ ≫ (restrictDerived g).map e ≫
    ((restrictAlong g).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
    (shiftFunctor (DerivedCategory (SheafOfModules.{u}
        (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) (1 : ℤ)).map
      (((restrictAlong g).mapDerivedCategorySingleFunctor 0).hom.app G)

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [Y.J.HasSheafCompose (forget CommRingCat)] [HasWeakSheafify Y.J CommRingCat]
  [HasWeakSheafify X.J CommRingCat] in
/-- The degreewise unit followed by the restriction of scalars of an adjoint chain map is the
chain map. -/
theorem pullbackUnitComplex_comp_pullbackTranspose
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (ψ : ((inverseImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶
      ((restrictAlong g).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :
    pullbackUnitComplex g K ≫ (restrictComplex g).map (pullbackTranspose g ψ) = ψ := by
  refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
  exact ((extendRestrictAdjunction g).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- The change of base ring `(f ∘ g)⁻¹𝒪_ℬ ≅ g⁻¹f⁻¹𝒪_ℬ` followed by the map of the square
`g⁻¹f⁻¹𝒪_ℬ ≅ (f ∘ g)⁻¹𝒪_ℬ` over `g^♯` is the map of the square `𝟙` over `g^♯`. -/
theorem baseIsoChange_comp_mapOfSquare :
    baseIsoChange (f := f) g ≫
        Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u, u, u} Y.J
          ((invImage g).obj ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
          ((invImage g).obj X.O) ((invImage g).map f.fSharpInverseImage)
          ((inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O) Y.O
          (f.comp g).fSharpInverseImage (baseIso f g).hom g.fSharpInverseImage
          (invImage_fSharp_comp_fSharp f g) =
      structureSquareMap g := by
  have h := Stacks.SheafOfModules.naiveCotangentComplexMap_rectangle Y.J
    (A := (inverseImageCommRingFunctor (f.comp (toInverseImage g)).toToposHom).obj B.O)
    (O := (invImage g).obj X.O) (B := Y.O)
    (A'' := (inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O)
    (E' := (inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O)
    (E₂ := (invImage g).obj ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
    (f.comp (toInverseImage g)).fSharpInverseImage g.fSharpInverseImage (𝟙 _)
    (f.comp g).fSharpInverseImage (fSharp_comp_fSharp_eq g) (f.comp g).fSharpInverseImage
    (𝟙 _) (Category.id_comp _).symm ((invImage g).map f.fSharpInverseImage) (baseIso f g).inv
    (fSharpInverseImage_toInverseImage_eq g) (baseIso f g).hom
    (invImage_fSharp_comp_fSharp f g) ((baseIso f g).inv_hom_id.trans (Category.comp_id _).symm)
  refine h.trans ?_
  have hid : Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{u, u, u, u} Y.J
      ((inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O) Y.O
      (f.comp g).fSharpInverseImage _ (f.comp g).fSharpInverseImage (𝟙 _)
      (Category.id_comp _).symm = 𝟙 _ :=
    Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare_id.{u, u, u, u} Y.J _ _ _ _
  rw [hid, CategoryTheory.Functor.map_id, Category.comp_id]

omit [Y.J.HasSheafCompose (forget CommRingCat)] [HasWeakSheafify Y.J CommRingCat]
  [HasWeakSheafify X.J CommRingCat] in
/-- The derived unit followed by the restriction of scalars of the comparison `Lg^* ⟶ g^*` and
of the image of a chain map `g^*K ⟶ N` is the degreewise unit followed by the restriction of
scalars of the chain map. -/
theorem derivedUnit_comp_restrictDerived_map
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (φ : (g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ N) :
    (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactors.inv.app K ≫
      (derivedUnit g).app (DerivedCategory.Q.obj K) ≫
      (restrictDerived g).map (derivedPullbackComparisonComplex g K ≫ DerivedCategory.Q.map φ) =
      DerivedCategory.Q.map (pullbackUnitComplex g K ≫ (restrictComplex g).map φ) ≫
        (restrictDerivedFactors g).inv.app N := by
  have hU := derivedUnit_app_Q g K
  have hU' := ((Iso.eq_comp_inv ((restrictDerivedFactors g).app _)).2
    ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans hU)))
  have hN := (restrictDerivedFactors g).inv.naturality φ
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, hU', Category.assoc,
    Iso.app_inv]
  simp only [Functor.comp_map] at hN
  rw [← hN, ← Category.assoc, ← Functor.map_comp]

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
private theorem comp_assoc_five {𝒞 : Type*} [Category 𝒞] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : 𝒞}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (d : P₃ ⟶ P₄) (x : P₂ ⟶ P₄) (h : c ≫ d = x)
    (e : P₄ ⟶ P₅) (k : P₅ ⟶ P₆) (l : P₆ ⟶ P₇) :
    a ≫ b ≫ c ≫ d ≫ e ≫ k ≫ l = (a ≫ b ≫ x) ≫ e ≫ k ≫ l := by
  rw [← h]
  simp only [Category.assoc]

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
private theorem comp_map_comp_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (R : 𝒞 ⥤ 𝒟)
    {P₀ P₁ P₂ P₃ : 𝒟} {Q₀ Q₁ Q₂ : 𝒞} {P₄ P₅ P₆ : 𝒟}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (d : P₃ ⟶ R.obj Q₀) (x : Q₀ ⟶ Q₁) (y : Q₁ ⟶ Q₂)
    (z : P₂ ⟶ P₄) (w : P₄ ⟶ R.obj Q₁) (k : R.obj Q₂ ⟶ P₅) (l : P₅ ⟶ P₆)
    (h : c ≫ d ≫ R.map x = z ≫ w) :
    a ≫ b ≫ c ≫ d ≫ R.map (x ≫ y) ≫ k ≫ l = a ≫ b ≫ z ≫ w ≫ R.map y ≫ k ≫ l := by
  have h' : c ≫ d ≫ R.map (x ≫ y) = z ≫ w ≫ R.map y := by
    rw [Functor.map_comp, reassoc_of% h]
  rw [reassoc_of% h']

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
private theorem comp_eq_of_eq {𝒞 : Type*} [Category 𝒞] {P₀ P₁ P₂ P₃ P₄ : 𝒞}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (r : P₃ ⟶ P₄) {x : P₀ ⟶ P₃}
    (h : a ≫ b ≫ c = x) : a ≫ b ≫ c ≫ r = x ≫ r := by
  rw [← h]
  simp only [Category.assoc]

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
private theorem map_inv_comp_map_hom_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {P : 𝒟} {X₀ Y₀ Z₀ : 𝒞} (a : P ⟶ F.obj X₀) (i : Y₀ ≅ X₀) (m : X₀ ⟶ Z₀) :
    a ≫ F.map i.inv ≫ F.map (i.hom ≫ m) = a ≫ F.map m := by
  rw [← Functor.map_comp, Iso.inv_hom_id_assoc]

/-- **`rhoClass` on the image of `ζ`**: it is the restriction of scalars of `ζ` along `g^♯`,
precomposed with the map `NL_{g⁻¹𝒪_𝒞/(f ∘ g)⁻¹𝒪_ℬ} ⟶ NL_{𝒪_𝒟/(f ∘ g)⁻¹𝒪_ℬ}` of `g^♯`. -/
theorem rhoClass_restrictExtClass
    (ζ : Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, u + 1} Y.J
      ((inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O) Y.O
      (f.comp g).fSharpInverseImage G 1) :
    rhoClass g (restrictExtClass f g ζ) =
      DerivedCategory.Q.map (structureSquareMap g) ≫ (restrictAlong g).mapExtOne ζ := by
  have hc := derivedUnit_comp_restrictDerived_map g
    (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
      ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage)
    (pullbackNaiveCotangentMap f g)
  have hT := pullbackUnitComplex_comp_pullbackTranspose g
    (inverseImageNaiveCotangentMapOfSquare g f.fSharpInverseImage (f.comp g).fSharpInverseImage
      (baseIso f g).hom (invImage_fSharp_comp_fSharp f g))
  unfold rhoClass restrictExtClass naiveCotangentDerivedComparison
  refine (comp_map_comp_eq (restrictDerived g) _ _ _ _ _ _ _ _ _ _ hc).trans
    (comp_eq_of_eq _ _ _ _ ?_)
  refine (congrArg (fun t ↦ _ ≫ _ ≫ DerivedCategory.Q.map t) hT).trans ?_
  rw [← baseIsoChange_comp_mapOfSquare g]
  exact (map_inv_comp_map_hom_comp DerivedCategory.Q _ _ _).trans (Functor.map_comp _ _ _).symm

section Solutions

variable [Y.J.WEqualsLocallyBijective CommRingCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  {F : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
  (QC : (ofTrivialBase f F).CompatibleFirstOrderThickening)
  (QD : (ofTrivialBase (f.comp g) G).CompatibleFirstOrderThickening)
  (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G)

/-- **The image of `ζ` read over `g⁻¹𝒪_𝒞` is the class of `𝒪'₂`** (Stacks 0GQ8). -/
theorem rhoClass_restrictExtClass_eq :
    rhoClass g (restrictExtClass f g
        (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp g) G
          (Quotient.mk
            (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _) QD))) =
      RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp (toInverseImage g))
        (restrictedIdeal g G)
        (Quotient.mk (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
          (pullbackSolution g QC QD c)) :=
  (rhoClass_restrictExtClass g _).trans (pullbackSolution_class g QC QD c).symm

end Solutions

end Deformation.ToposThickening.LiftingMorphismDerived

end
