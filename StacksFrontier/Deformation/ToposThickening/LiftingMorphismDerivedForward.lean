module

public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedRho

/-!
# A compatible morphism identifies the two images in `Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi, `𝒪_{𝒞'}`, `𝒪_{𝒟'}` and `c : g^*ℱ ⟶ 𝒢` as in **Stacks 0GQ7**. A comorphism
`h : g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}` of `g⁻¹f⁻¹𝒪_ℬ`-algebras over `g^♯` restricting to `c` on `g⁻¹ℱ` gives
a commutative square of sheaves of rings `g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}` over `g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟`, hence a
chain map `g^*NL_{𝒪_𝒞/𝒪_{𝒞'}} ⟶ NL_{𝒪_𝒟/𝒪_{𝒟'}}` (`liftNaiveCotangentMap`). This file
records how it interacts with the base changes of **Stacks 08TX**: the rectangle
`g^*NL_{𝒪_𝒞/f⁻¹𝒪_ℬ} ⟶ g^*NL_{𝒪_𝒞/𝒪_{𝒞'}} ⟶ NL_{𝒪_𝒟/𝒪_{𝒟'}}` and
`g^*NL_{𝒪_𝒞/f⁻¹𝒪_ℬ} ⟶ NL_{𝒪_𝒟/(f ∘ g)⁻¹𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_{𝒟'}}`.

## Main definitions

* `Deformation.ToposThickening.LiftingMorphismDerived.liftNaiveCotangentMap`: the chain map
  `g^*NL_{𝒪_𝒞/𝒪_{𝒞'}} ⟶ NL_{𝒪_𝒟/𝒪_{𝒟'}}` of a compatible comorphism.

## Main results

* `LiftingMorphismDerived.pullback_baseChange_comp_liftNaiveCotangentMap`: the two
  composites `g^*NL_{𝒪_𝒞/f⁻¹𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_{𝒟'}}` agree, given the naturality of the
  identification of Stacks 08TZ along `f⁻¹𝒪_ℬ ⟶ 𝒪_{𝒞'}`.

## References

* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
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
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  {f : RingedToposHom X B} (g : RingedToposHom Y X)
  {F : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
  {G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)}
  (QC : (ofTrivialBase f F).CompatibleFirstOrderThickening)
  (QD : (ofTrivialBase (f.comp g) G).CompatibleFirstOrderThickening)
  (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G)
  (h : (Data.ofSolutions g QC QD c).CompatibleHom)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J CommRingCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The square of a compatible comorphism: `g⁻¹`(reduction) followed by `g^♯` is the comorphism
followed by the reduction of `𝒪_{𝒟'}`. -/
theorem compatibleHom_square :
    (invImage g).map QC.reduction ≫ g.fSharpInverseImage = h.hom ≫ QD.reduction :=
  h.proj_comm.symm

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J CommRingCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The comorphism is a map of `g⁻¹f⁻¹𝒪_ℬ`-algebras. -/
theorem compatibleHom_base :
    invBaseMap g QC ≫ h.hom = (baseIso f g).hom ≫ QD.baseMap :=
  h.base_comm

/-- **The chain map `g⁻¹NL_{𝒪_𝒞/𝒪_{𝒞'}} ⟶ NL_{𝒪_𝒟/𝒪_{𝒟'}}` of a compatible comorphism**, linear
over `g^♯`: the inverse image identification of Stacks 08TZ followed by the map of naive
cotangent complexes of Stacks 08TX attached to the square `compatibleHom_square`. -/
def liftInverseImageNaiveCotangentMap :
    ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J QC.extension X.O QC.reduction) ⟶
      ((restrictAlong g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J QD.extension Y.O
          QD.reduction) :=
  inverseImageNaiveCotangentMapOfSquare g QC.reduction QD.reduction h.hom
    (compatibleHom_square g QC QD c h)

/-- **The chain map `g^*NL_{𝒪_𝒞/𝒪_{𝒞'}} ⟶ NL_{𝒪_𝒟/𝒪_{𝒟'}}` of a compatible comorphism**: the
adjoint of `liftInverseImageNaiveCotangentMap`. -/
abbrev liftNaiveCotangentMap :
    (g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J QC.extension X.O
          QC.reduction) ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J QD.extension Y.O QD.reduction :=
  pullbackNaiveCotangentMapOfSquare g QC.reduction QD.reduction h.hom
    (compatibleHom_square g QC QD c h)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **The rectangle of Stacks 08TX maps for a compatible comorphism**: the base change along
`g⁻¹f⁻¹𝒪_ℬ ⟶ g⁻¹𝒪_{𝒞'}` followed by the map of the comorphism is the map of the square
`g⁻¹f⁻¹𝒪_ℬ ≅ (f ∘ g)⁻¹𝒪_ℬ` over `g^♯` followed by the base change of `𝒪_{𝒟'}`. -/
theorem invBaseChange_comp_liftSquare :
    invBaseChange g QC ≫
        Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u, u, u} Y.J _ _
          ((invImage g).map QC.reduction) _ Y.O QD.reduction h.hom g.fSharpInverseImage
          (compatibleHom_square g QC QD c h) =
      Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u, u, u} Y.J
          ((invImage g).obj ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
          ((invImage g).obj X.O) ((invImage g).map f.fSharpInverseImage)
          ((inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O) Y.O
          (f.comp g).fSharpInverseImage (baseIso f g).hom g.fSharpInverseImage
          (invImage_fSharp_comp_fSharp f g) ≫
        ((SheafOfModules.restrictScalars
          (underlyingRingHomOfSite g.fSharpInverseImage)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map QD.naiveCotangentBaseChange :=
  Stacks.SheafOfModules.naiveCotangentComplexMap_rectangle Y.J
    (A := (invImage g).obj ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
    (O := (invImage g).obj X.O) (B := Y.O)
    (A'' := (inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O)
    (E' := QD.extension) (E₂ := (invImage g).obj QC.extension)
    ((invImage g).map f.fSharpInverseImage) g.fSharpInverseImage (baseIso f g).hom
    (f.comp g).fSharpInverseImage (invImage_fSharp_comp_fSharp f g) QD.reduction QD.baseMap
    (RingedToposExtensionProblem.baseMap_comp_reduction_ofTrivialBase QD).symm
    ((invImage g).map QC.reduction) (invBaseMap g QC) (invImage_fSharp_eq g QC) h.hom
    (compatibleHom_square g QC QD c h) (compatibleHom_base g QC QD c h)

/-- The map of conormal sheaves `Ker(g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞)/Ker² ⟶ Ker(𝒪_{𝒟'} ⟶ 𝒪_𝒟)/Ker²` of
the square of a compatible comorphism. -/
abbrev liftConormalMap :
    Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} Y.J ((invImage g).obj QC.extension)
        ((invImage g).obj X.O) ((invImage g).map QC.reduction) ⟶
      (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage)).obj
        (Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} Y.J QD.extension Y.O QD.reduction) :=
  Stacks.Sites.Conormal.conormalSheafMapOfSquare.{u, u, u, u} Y.J _ _ _ _
    ((invImage g).map QC.reduction) QD.reduction h.hom g.fSharpInverseImage
    (compatibleHom_square g QC QD c h).symm

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J CommRingCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **A compatible comorphism carries the pushout datum to the identification of
`Ker/Ker²` with `𝒢` for `𝒪_{𝒟'}`**: on a local section of the kernel of `g⁻¹`(reduction) the
comorphism is the adjoint of `c` (`CompatibleHom.kernel_comm`). -/
theorem liftConormalMap_comp_kernelConormalToModule :
    liftConormalMap g QC QD c h ≫
        (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage)).map
          QD.kernelConormalToModule =
      pushoutConormalToModule g QC c := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun U x ↦ ?_)
  have e₁ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} Y.J _ _
    _ _ _ _ (𝟙 _) (𝟙 _) ((invImage g).map QC.reduction) QD.reduction h.hom g.fSharpInverseImage
    (compatibleHom_square g QC QD c h).symm U x
  have e₂ := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule QD.reduction
    (ofTrivialBase (f.comp g) G).G QD.kernelIdentification U
    ⟨h.hom.hom.app U x.1,
      Stacks.Sites.Conormal.kernelIdeal_le_comap_square _ _ _ _
        (Stacks.Sites.Conormal.hom_of_square (compatibleHom_square g QC QD c h).symm) U x.2⟩
  have e₃ := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule
    ((invImage g).map QC.reduction) (restrictedIdeal g G) (prescribedRestriction QC g c) U x
  refine ((congrArg (fun t ↦ QD.kernelConormalToModule.val.app U t) e₁).trans e₂).trans
    (Eq.trans ?_ e₃.symm)
  refine QD.incl_injective ?_
  refine (QD.incl_kernelPreimage _).trans ?_
  exact h.kernel_comm U x

/-- The identification of Stacks 08TZ for the structure map of `𝒪_𝒞` over `f⁻¹𝒪_ℬ`. -/
abbrev inverseImageIsoBase :=
  Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso.{u, u, u, u, u, u} Y.J X.J
    g.toToposHom (A := (inverseImageCommRingFunctor f.toToposHom).obj B.O) (B := X.O)
    f.fSharpInverseImage

/-- The identification of Stacks 08TZ for the reduction `𝒪_{𝒞'} ⟶ 𝒪_𝒞`. -/
abbrev inverseImageIsoReduction :=
  Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso.{u, u, u, u, u, u} Y.J X.J
    g.toToposHom (A := QC.extension) (B := X.O) QC.reduction

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}] in
private theorem comp_comp_eq_of_eq {𝒞 : Type*} [Category 𝒞] {P₀ P₁ P₂ P₃ P₄ P₅ : 𝒞}
    {a : P₀ ⟶ P₁} {b : P₁ ⟶ P₂} {c : P₂ ⟶ P₃} {a' : P₀ ⟶ P₄} {b' : P₄ ⟶ P₂} {c' : P₄ ⟶ P₅}
    {d' : P₅ ⟶ P₃} (h₁ : a ≫ b = a' ≫ b') (h₂ : b' ≫ c = c' ≫ d') :
    a ≫ b ≫ c = (a' ≫ c') ≫ d' := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **The chain-level rectangle for a compatible comorphism**, from the naturality `hZ` of the
identification of Stacks 08TZ with respect to the base change along `f⁻¹𝒪_ℬ ⟶ 𝒪_{𝒞'}`. -/
theorem pullback_baseChange_comp_liftNaiveCotangentMap
    (hZ : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          QC.naiveCotangentBaseChange ≫ (inverseImageIsoReduction g QC).hom =
        (inverseImageIsoBase (f := f) g).hom ≫ invBaseChange g QC) :
    (g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
        QC.naiveCotangentBaseChange ≫ liftNaiveCotangentMap g QC QD c h =
      pullbackNaiveCotangentMap f g ≫ QD.naiveCotangentBaseChange := by
  refine (map_comp_pullbackTranspose g _ _).trans (Eq.trans ?_ (pullbackTranspose_comp g _ _).symm)
  congr 1
  unfold inverseImageNaiveCotangentMapOfSquare
  exact comp_comp_eq_of_eq hZ (invBaseChange_comp_liftSquare g QC QD c h)

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}] in
private theorem comp_comp_eq_of_eq₃ {𝒞 : Type*} [Category 𝒞]
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : 𝒞}
    {a : P₀ ⟶ P₁} {b : P₁ ⟶ P₂} {s : P₂ ⟶ P₃} {x : P₀ ⟶ P₄} {y : P₄ ⟶ P₅} {η : P₅ ⟶ P₂}
    {z : P₅ ⟶ P₆} {w : P₆ ⟶ P₇} {r : P₇ ⟶ P₃} {m : P₄ ⟶ P₆}
    (h₁ : a ≫ b = x ≫ y ≫ η) (h₂ : η ≫ s = z ≫ w ≫ r) (hm : y ≫ z = m) :
    a ≫ b ≫ s = (x ≫ m ≫ w) ≫ r := by
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc, h₂, ← hm]
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
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}] in
/-- For an adjunction `L ⊣ R` of additive functors and an additive `I`, the degreewise adjoint
`(I ⋙ L)K ⟶ N` of the single complex of the adjoint `I M ⟶ R N` of `x : L (I M) ⟶ N` is the
single complex of `x`. -/
private theorem transpose_single {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
    [Category ℬ] [Preadditive ℬ] [HasZeroObject ℬ] [Category 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞]
    {L : ℬ ⥤ 𝒞} {R : 𝒞 ⥤ ℬ} (adj : L ⊣ R) [hL : L.Additive] [hR : R.Additive] (I : 𝒜 ⥤ ℬ)
    [hI : I.Additive]
    {M : 𝒜} {N : 𝒞} (x : L.obj (I.obj M) ⟶ N) (y : I.obj M ⟶ R.obj N)
    (hxy : adj.homEquiv _ _ x = y)
    (T : ((I ⋙ L).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor 𝒜 (-1)).obj M) ⟶ (CochainComplex.singleFunctor 𝒞 (-1)).obj N)
    (hT : ∀ i, T.f i = (adj.homEquiv _ _).symm
      (((HomologicalComplex.singleMapHomologicalComplex I (ComplexShape.up ℤ) (-1)).hom.app M ≫
        (CochainComplex.singleFunctor ℬ (-1)).map y ≫
        (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℤ) (-1)).inv.app N).f
          i)) :
    T = (HomologicalComplex.singleMapHomologicalComplex (I ⋙ L) (ComplexShape.up ℤ)
          (-1)).hom.app M ≫
        (CochainComplex.singleFunctor 𝒞 (-1)).map x := by
  subst hxy
  refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
  by_cases hi : i = -1
  · subst hi
    rw [hT, HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    change (adj.homEquiv _ _).symm (_ ≫
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) (-1)).map _).f (-1) ≫ _) =
      _ ≫ ((HomologicalComplex.single _ (ComplexShape.up ℤ) (-1)).map x).f (-1)
    rw [HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.comp_map]
    rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm,
      Equiv.symm_apply_apply]
    exact congrArg _ (Iso.inv_hom_id_assoc
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) (L.obj (I.obj M))) _).symm
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1) _ i hi).eq_of_tgt _ _

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})] [HasWeakSheafify Y.J CommRingCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The adjoint of the single complex of the adjoint `M ⟶ res N` of `x : g^*M ⟶ N` is the single
complex of `x`. -/
theorem pullbackTranspose_single
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (x : g.toRingedToposModulesHom.pullbackModules.obj M ⟶ N) :
    pullbackTranspose g
        ((HomologicalComplex.singleMapHomologicalComplex
            (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) (-1)).hom.app M ≫
          (CochainComplex.singleFunctor _ (-1)).map ((extendRestrictAdjunction g).homEquiv _ _ x) ≫
          (HomologicalComplex.singleMapHomologicalComplex (restrictAlong g) (ComplexShape.up ℤ)
            (-1)).inv.app N) =
      (HomologicalComplex.singleMapHomologicalComplex g.toRingedToposModulesHom.pullbackModules
          (ComplexShape.up ℤ) (-1)).hom.app M ≫
        (CochainComplex.singleFunctor _ (-1)).map x :=
  have : (inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
    CategoryTheory.Sheaf.inverseImageTargetModules_additive.{u, u, u, u, u, u} Y.J X.J g.toToposHom
      (B := X.O)
  transpose_single (extendRestrictAdjunction g)
    (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL := extendScalars_additive g) (hR := (extendRestrictAdjunction g).right_adjoint_additive)
    (hI := this) x _ rfl _ (fun _ ↦ rfl)

section Eta

variable (e : (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
    (Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} X.J QC.extension X.O QC.reduction) ≅
    Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} Y.J ((invImage g).obj QC.extension)
      ((invImage g).obj X.O) ((invImage g).map QC.reduction))

/-- The chain map `g^*((Ker/Ker²)[1]) ⟶ (Ker/Ker²)[1]` from the conormal sheaf of
`𝒪_{𝒞'} ⟶ 𝒪_𝒞` to that of `𝒪_{𝒟'} ⟶ 𝒪_𝒟`: the adjoint of the identification `e` followed by the
map of conormal sheaves of a compatible comorphism. -/
def liftConormalComplexMap :
    (g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (-1)).obj
          (Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} X.J QC.extension X.O QC.reduction)) ⟶
      (CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (-1)).obj
          (Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} Y.J QD.extension Y.O QD.reduction) :=
  pullbackTranspose g
    ((HomologicalComplex.singleMapHomologicalComplex
        (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) (-1)).hom.app _ ≫
      (CochainComplex.singleFunctor _ (-1)).map (e.hom ≫ liftConormalMap g QC QD c h) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (SheafOfModules.restrictScalars (underlyingRingHomOfSite g.fSharpInverseImage))
        (ComplexShape.up ℤ) (-1)).inv.app _)

omit [Y.J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`η` along a compatible comorphism**, from the compatibility `hZ'` of the identification of
Stacks 08TZ with `η`. -/
theorem pullback_eta_comp_liftNaiveCotangentMap
    (hZ' : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (Stacks.SheafOfModules.conormalToNaiveCotangentComplex X.J QC.extension X.O
            QC.reduction) ≫ (inverseImageIsoReduction g QC).hom =
        (HomologicalComplex.singleMapHomologicalComplex
          (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) (-1)).hom.app _ ≫
          (CochainComplex.singleFunctor _ (-1)).map e.hom ≫
          Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J ((invImage g).obj QC.extension)
            ((invImage g).obj X.O) ((invImage g).map QC.reduction)) :
    (g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Stacks.SheafOfModules.conormalToNaiveCotangentComplex X.J QC.extension X.O
          QC.reduction) ≫ liftNaiveCotangentMap g QC QD c h =
      liftConormalComplexMap g QC QD c h e ≫
        Stacks.SheafOfModules.conormalToNaiveCotangentComplex Y.J QD.extension Y.O
          QD.reduction := by
  refine (map_comp_pullbackTranspose g _ _).trans (Eq.trans ?_ (pullbackTranspose_comp g _ _).symm)
  congr 1
  have hsq := Stacks.SheafOfModules.conormalToNaiveCotangentComplex_comp_mapOfSquare Y.J _ _
    ((invImage g).map QC.reduction) _ _ QD.reduction h.hom g.fSharpInverseImage
    (compatibleHom_square g QC QD c h)
  unfold inverseImageNaiveCotangentMapOfSquare
  exact comp_comp_eq_of_eq₃ hZ' hsq ((CochainComplex.singleFunctor _ (-1)).map_comp _ _).symm

/-- The map `g^*(Ker/Ker²) ⟶ Ker/Ker²` of conormal sheaves of a compatible comorphism, from the
conormal sheaf of `𝒪_{𝒞'} ⟶ 𝒪_𝒞` to that of `𝒪_{𝒟'} ⟶ 𝒪_𝒟`: the adjoint of `e` followed by
`liftConormalMap`. -/
def liftConormalModuleMap :
    g.toRingedToposModulesHom.pullbackModules.obj
        (Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} X.J QC.extension X.O QC.reduction) ⟶
      Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} Y.J QD.extension Y.O QD.reduction :=
  ((extendRestrictAdjunction g).homEquiv _ _).symm (e.hom ≫ liftConormalMap g QC QD c h)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The conormal chain map is the single complex of `liftConormalModuleMap`. -/
theorem liftConormalComplexMap_eq :
    liftConormalComplexMap g QC QD c h e =
      (HomologicalComplex.singleMapHomologicalComplex g.toRingedToposModulesHom.pullbackModules
          (ComplexShape.up ℤ) (-1)).hom.app _ ≫
        (CochainComplex.singleFunctor _ (-1)).map (liftConormalModuleMap g QC QD c h e) := by
  have := pullbackTranspose_single g (liftConormalModuleMap g QC QD c h e)
  unfold liftConormalModuleMap at this
  exact (congrArg (fun y ↦ pullbackTranspose g (_ ≫ (CochainComplex.singleFunctor _ (-1)).map y ≫
    _)) (Equiv.apply_symm_apply _ _).symm).trans this

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  [Y.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **The coefficients along a compatible comorphism**: `liftConormalModuleMap` followed by the
identification for `𝒪_{𝒟'}` is `g^*` of the identification for `𝒪_{𝒞'}` followed by `c`, given
the compatibility `hZ''` of `e` with the pushout datum. -/
theorem liftConormalModuleMap_comp
    (hZ'' : e.inv ≫ (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map QC.kernelConormalToModule ≫
        prescribedAdjoint g c = pushoutConormalToModule g QC c) :
    liftConormalModuleMap g QC QD c h e ≫ QD.kernelConormalToModule =
      g.toRingedToposModulesHom.pullbackModules.map QC.kernelConormalToModule ≫ c := by
  apply ((extendRestrictAdjunction g).homEquiv _ _).injective
  have hκ := liftConormalMap_comp_kernelConormalToModule g QC QD c h
  refine ((extendRestrictAdjunction g).homEquiv_naturality_right _ _).trans ?_
  refine Eq.trans ?_ ((extendRestrictAdjunction g).homEquiv_naturality_left _ _).symm
  unfold liftConormalModuleMap
  refine (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hκ).trans ?_)
  rw [← hZ'']
  exact e.hom_inv_id_assoc _

end Eta

end Deformation.ToposThickening.LiftingMorphismDerived

end
