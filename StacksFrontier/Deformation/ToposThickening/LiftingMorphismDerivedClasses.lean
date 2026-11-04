module

public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageComplex
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare
public import StacksFrontier.Deformation.ToposThickening.InverseImageExtensionSolutions
public import StacksFrontier.Deformation.ToposThickening.SquareZeroExtensionClassCanonical

/-!
# The two maps into `Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)` of Stacks 0GQ7

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi, `ℱ` an `𝒪_𝒞`-module, `𝒢` an `𝒪_𝒟`-module and `c : g^*ℱ ⟶ 𝒢` an `𝒪_𝒟`-linear map.
The statement of **Stacks 0GQ7** compares an element `ξ ∈ Ext¹_{𝒪_𝒞}(NL_{𝒪_𝒞/𝒪_ℬ}, ℱ)` and an
element `ζ ∈ Ext¹_{𝒪_𝒟}(NL_{𝒪_𝒟/𝒪_ℬ}, 𝒢)` in `Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`, through the two
maps its proof writes down:

* `Ext¹_{𝒪_𝒞}(NL_{𝒪_𝒞/𝒪_ℬ}, ℱ) ⟶ Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, Lg^*ℱ) ⟶
  Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`, applying `Lg^*` and pushing along
  `Lg^*ℱ ⟶ g^*ℱ ⟶ 𝒢` (`pullbackExtClass`);
* `Ext¹_{𝒪_𝒟}(NL_{𝒪_𝒟/𝒪_ℬ}, 𝒢) ⟶ Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`, precomposing with the
  canonical map `Lg^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}` (`restrictExtClass`).

`Lg^*` is the derived pullback of **Stacks 06YY**, which exists along every morphism of ringed
topoi. The canonical map is the comparison `Lg^* ⟶ g^*` followed by the canonical chain map
`g^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}` (`pullbackNaiveCotangentMap`): it is adjoint to the inverse
image identification `g⁻¹NL_{𝒪_𝒞/f⁻¹𝒪_ℬ} ≅ NL_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ}` of **Stacks 08TZ** followed by
the map of naive cotangent complexes of **Stacks 08TX** attached to the square
`g⁻¹f⁻¹𝒪_ℬ = (f ∘ g)⁻¹𝒪_ℬ ⟶ 𝒪_𝒟` over `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟`.

## Main definitions

* `Deformation.ToposThickening.LiftingMorphismDerived.derivedPullbackComparisonComplex`: the
  comparison `Lg^*K ⟶ g^*K` on a complex.
* `.derivedPullbackSingleObj`: the comparison `Lg^*(ℱ[0]) ⟶ (g^*ℱ)[0]`.
* `.pullbackExtClass`: the image of `ξ`.
* `.pullbackNaiveCotangentMap`: the canonical chain map `g^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}`.
* `.naiveCotangentDerivedComparison`: the canonical map `Lg^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}`.
* `.restrictExtClass`: the image of `ζ`.

## References

* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sheaves.RingedToposModules (inverseImageModules extendScalarsFSharp fSharpCommRing)
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Deformation.ToposThickening.InverseImageExtension (invImage baseIso
  comp_fSharpInverseImage_eq)
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

/-! ### The comparison on single complexes induced by a comparison on complexes -/

section SingleComparison

variable {C C' : Type*} [Category* C] [Category* C'] [Abelian C] [Abelian C']
  [HasDerivedCategory C] [HasDerivedCategory C']
  (L : DerivedCategory C ⥤ DerivedCategory C') (Φ : C ⥤ C') [Φ.Additive]
  (τ : DerivedCategory.Q ⋙ L ⟶ Φ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

/-- The comparison `L(M[-n]) ⟶ (ΦM)[-n]` on an object `M` placed in degree `n`, induced by a
comparison `τ : Q ⋙ L ⟶ Φ ⋙ Q` on complexes: `τ` at the single complex, followed by the
identification of the degreewise image of a single complex with a single complex. -/
def singleObjComparison (n : ℤ) (M : C) :
    L.obj ((DerivedCategory.singleFunctor C n).obj M) ⟶
      (DerivedCategory.singleFunctor C' n).obj (Φ.obj M) :=
  L.map ((DerivedCategory.singleFunctorIsoCompQ C n).hom.app M) ≫
    τ.app ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) n).hom.app M) ≫
    (DerivedCategory.singleFunctorIsoCompQ C' n).inv.app _

end SingleComparison

/-! ### The comparison `Lg^* ⟶ g^*` -/

section Comparison

variable (g : RingedToposHom Y X)

/-- The two readings `g.toModulesHom` and `g.toRingedToposModulesHom` of a morphism of ringed
topoi have the same pullback of sheaves of modules. -/
abbrev pullbackModulesIso :
    g.toModulesHom.pullbackModules ≅ g.toRingedToposModulesHom.pullbackModules :=
  eqToIso (congrArg (fun φ ↦ φ.pullbackModules)
    (AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom g))

/-- **The comparison `Lg^* ⟶ g^*` on complexes** of `𝒪_𝒞`-modules (Stacks 06YY): the canonical
comparison of the derived pullback with the degreewise pullback, read on the derived category
of complexes, as a natural transformation `Q ⋙ Lg^* ⟶ g^* ⋙ Q`. -/
def derivedPullbackComparisonNat :
    DerivedCategory.Q ⋙ derivedPullback g ⟶
      g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (derivedPullback g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (derivedPullbackComparison g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (g.toModulesHom.pullbackModules.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom ≫
    Functor.whiskerRight (NatIso.mapHomologicalComplex (pullbackModulesIso g)
      (ComplexShape.up ℤ)).hom DerivedCategory.Q

/-- **The comparison `Lg^*K ⟶ g^*K`** of the derived pullback with the degreewise pullback of
a complex of `𝒪_𝒞`-modules (Stacks 06YY). -/
abbrev derivedPullbackComparisonComplex
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedPullback g).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj
        ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K) :=
  (derivedPullbackComparisonNat g).app K

/-- The comparison `Lg^*K ⟶ g^*K` is natural in the complex `K`. -/
theorem derivedPullbackComparisonComplex_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : K ⟶ L) :
    (derivedPullback g).map (DerivedCategory.Q.map φ) ≫ derivedPullbackComparisonComplex g L =
      derivedPullbackComparisonComplex g K ≫
        DerivedCategory.Q.map
          ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) :=
  (derivedPullbackComparisonNat g).naturality φ

/-- **The comparison `Lg^*(ℱ[0]) ⟶ (g^*ℱ)[0]`** of the derived with the degreewise pullback on
a module placed in degree `0`. -/
def derivedPullbackSingleObj
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (derivedPullback g).obj ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (g.toRingedToposModulesHom.pullbackModules.obj F) :=
  singleObjComparison (derivedPullback g) g.toRingedToposModulesHom.pullbackModules
    (derivedPullbackComparisonNat g) 0 F

end Comparison

/-! ### The image of `ξ` -/

section PullbackClass

variable (g : RingedToposHom Y X)
  {F : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
  {G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)}
  (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G)

/-- **The image of `ξ ∈ Ext¹_{𝒪_𝒞}(K, ℱ)` in `Ext¹_{𝒪_𝒟}(Lg^*K, 𝒢)`** (Stacks 0GQ7): apply the
derived pullback `Lg^*`, commute it past the shift, and push the coefficients along
`Lg^*ℱ ⟶ g^*ℱ ⟶ 𝒢`. -/
def pullbackExtClass
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (ξ : DerivedCategory.Ext K ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F) 1) :
    DerivedCategory.Ext ((derivedPullback g).obj K) ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj G) 1 :=
  (derivedPullback g).map ξ ≫
    ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F) ≫
    (derivedPullbackSingleObj g F ≫ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).map c)⟦(1 : ℤ)⟧'

end PullbackClass

/-! ### The canonical map `Lg^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}` -/

section Canonical

variable [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  (f : RingedToposHom X B) (g : RingedToposHom Y X)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Y.J CommRingCat] [HasWeakSheafify X.J CommRingCat] in
/-- The square `g⁻¹f⁻¹𝒪_ℬ ⟶ g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟`, `g⁻¹f⁻¹𝒪_ℬ ≅ (f ∘ g)⁻¹𝒪_ℬ ⟶ 𝒪_𝒟` along which the
naive cotangent complex of `g⁻¹𝒪_𝒞` maps to that of `𝒪_𝒟`. -/
theorem invImage_fSharp_comp_fSharp :
    (invImage g).map f.fSharpInverseImage ≫ g.fSharpInverseImage =
      (baseIso f g).hom ≫ (f.comp g).fSharpInverseImage := by
  rw [comp_fSharpInverseImage_eq, Iso.hom_inv_id_assoc]

/-- The adjunction between extension and restriction of scalars along
`g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟` (Stacks 03CZ), the second half of `g^* ⊣ g_*`. -/
abbrev extendRestrictAdjunction :=
  Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction Y.J
    (fSharpCommRing g.toRingedToposModulesHom)
    (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property

/-- Restriction of scalars along `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟`, the right adjoint of
`extendRestrictAdjunction`. -/
abbrev restrictAlong :=
  SheafOfModules.restrictScalars (Stacks.Sheaves.RingedToposModules.commRingSheafMap Y.J
    (fSharpCommRing g.toRingedToposModulesHom)
    (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)

/-- Extension of scalars along `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟` is additive. -/
instance extendScalars_additive :
    (Stacks.Sheaves.RingedToposModules.extendScalars Y.J
      (fSharpCommRing g.toRingedToposModulesHom)
      (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property).Additive :=
  (extendRestrictAdjunction g).left_adjoint_additive

/-- The pullback `g^*` of sheaves of modules is additive. -/
instance pullbackModules_additive : g.toRingedToposModulesHom.pullbackModules.Additive :=
  (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    g.toRingedToposModulesHom).left_adjoint_additive

section Transpose

variable {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}

/-- The degreewise adjoint `g^*K ⟶ N` of a chain map `g⁻¹K ⟶ N` linear over `g^♯`, under
extension and restriction of scalars along `g^♯`. -/
def pullbackTranspose
    (ψ : ((inverseImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶
      ((restrictAlong g).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :
    (g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      N where
  f i := ((extendRestrictAdjunction g).homEquiv _ _).symm (ψ.f i)
  comm' i j _ := by
    have h := ψ.comm i j
    exact ((extendRestrictAdjunction g).homEquiv_naturality_right_symm _ _).symm.trans
      ((congrArg _ h).trans ((extendRestrictAdjunction g).homEquiv_naturality_left_symm _ _))

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [Y.J.HasSheafCompose (forget CommRingCat)] [HasWeakSheafify Y.J CommRingCat]
  [HasWeakSheafify X.J CommRingCat] in
/-- In degree `i`, `pullbackTranspose g ψ` is the adjoint of `ψ.f i`. -/
theorem pullbackTranspose_f
    (ψ : ((inverseImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶
      ((restrictAlong g).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
    (i : ℤ) :
    (pullbackTranspose g ψ).f i = ((extendRestrictAdjunction g).homEquiv _ _).symm (ψ.f i) :=
  rfl

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [Y.J.HasSheafCompose (forget CommRingCat)] [HasWeakSheafify Y.J CommRingCat]
  [HasWeakSheafify X.J CommRingCat] in
/-- The adjoint is natural in the target. -/
theorem pullbackTranspose_comp
    (ψ : ((inverseImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶
      ((restrictAlong g).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
    {N' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (χ : N ⟶ N') :
    pullbackTranspose g ψ ≫ χ =
      pullbackTranspose g
        (ψ ≫ ((restrictAlong g).mapHomologicalComplex (ComplexShape.up ℤ)).map χ) := by
  refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
  exact ((extendRestrictAdjunction g).homEquiv_naturality_right_symm _ _).symm

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [Y.J.HasSheafCompose (forget CommRingCat)] [HasWeakSheafify Y.J CommRingCat]
  [HasWeakSheafify X.J CommRingCat] in
/-- The adjoint is natural in the source. -/
theorem map_comp_pullbackTranspose
    {K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : K' ⟶ K)
    (ψ : ((inverseImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶
      ((restrictAlong g).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :
    (g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫
        pullbackTranspose g ψ =
      pullbackTranspose g (((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ ≫ ψ) := by
  refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
  exact ((extendRestrictAdjunction g).homEquiv_naturality_left_symm _ _).symm

end Transpose

section Square

variable {A : Sheaf X.J CommRingCat.{u}} (a : A ⟶ X.O) {A' : Sheaf Y.J CommRingCat.{u}}
  (a' : A' ⟶ Y.O) (φ : (invImage g).obj A ⟶ A')
  (hφ : (invImage g).map a ≫ g.fSharpInverseImage = φ ≫ a')

/-- The chain map `g⁻¹NL_{𝒪_𝒞/A} ⟶ NL_{𝒪_𝒟/A'}`, linear over `g^♯`, attached to a square
`φ : g⁻¹A ⟶ A'` over `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟`: the inverse image identification
`g⁻¹NL_{𝒪_𝒞/A} ≅ NL_{g⁻¹𝒪_𝒞/g⁻¹A}` of **Stacks 08TZ**, followed by the map of naive cotangent
complexes of **Stacks 08TX** attached to the square. -/
def inverseImageNaiveCotangentMapOfSquare :
    ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J A X.O a) ⟶
      ((restrictAlong g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J A' Y.O a') :=
  (Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso.{u, u, u, u, u, u} Y.J X.J
      g.toToposHom (A := A) (B := X.O) a).hom ≫
    Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u, u, u} Y.J
      ((invImage g).obj A) ((invImage g).obj X.O) ((invImage g).map a) A' Y.O a' φ
      g.fSharpInverseImage hφ

/-- **The chain map `g^*NL_{𝒪_𝒞/A} ⟶ NL_{𝒪_𝒟/A'}` of a square** `φ : g⁻¹A ⟶ A'` over `g^♯`:
the adjoint, degreewise under extension and restriction of scalars along `g^♯`, of
`inverseImageNaiveCotangentMapOfSquare`. -/
def pullbackNaiveCotangentMapOfSquare :
    (g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J A X.O a) ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J A' Y.O a' :=
  pullbackTranspose g (inverseImageNaiveCotangentMapOfSquare g a a' φ hφ)

end Square

/-- **The canonical chain map `g^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}`**: the map of the square
`g⁻¹f⁻¹𝒪_ℬ ≅ (f ∘ g)⁻¹𝒪_ℬ` over `g^♯` (`invImage_fSharp_comp_fSharp`). -/
abbrev pullbackNaiveCotangentMap :
    (g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage) ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
        ((inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O) Y.O
        (f.comp g).fSharpInverseImage :=
  pullbackNaiveCotangentMapOfSquare g f.fSharpInverseImage (f.comp g).fSharpInverseImage
    (baseIso f g).hom (invImage_fSharp_comp_fSharp f g)

/-- **The canonical map `Lg^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}`** of the proof of Stacks 0GQ7: the
comparison `Lg^* ⟶ g^*` of Stacks 06YY followed by the canonical chain map
`pullbackNaiveCotangentMap`. -/
def naiveCotangentDerivedComparison :
    (derivedPullback g).obj (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage)) ⟶
      DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
          ((inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O) Y.O
          (f.comp g).fSharpInverseImage) :=
  derivedPullbackComparisonComplex g _ ≫ DerivedCategory.Q.map (pullbackNaiveCotangentMap f g)

variable {G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)}

/-- **The image of `ζ ∈ Ext¹_{𝒪_𝒟}(NL_{𝒪_𝒟/𝒪_ℬ}, 𝒢)` in `Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`**
(Stacks 0GQ7): precomposition with the canonical map `Lg^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}`. -/
def restrictExtClass
    (ζ : Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, u + 1} Y.J
      ((inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O) Y.O
      (f.comp g).fSharpInverseImage G 1) :
    DerivedCategory.Ext ((derivedPullback g).obj (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage)))
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj G) 1 :=
  naiveCotangentDerivedComparison f g ≫ ζ

end Canonical

end Deformation.ToposThickening.LiftingMorphismDerived

end
