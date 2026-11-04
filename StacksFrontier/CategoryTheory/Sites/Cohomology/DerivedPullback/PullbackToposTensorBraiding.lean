module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackBraiding
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry

/-!
# The braided coherence of Stacks 03EL for the site-presented pullback

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor `f.u`
of the underlying sites which is a morphism of sites. The module-level comparison
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap` of **Stacks 03EL** for the pullback
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` attached to that presentation is compatible
with the symmetry of the tensor product:

`f^*(β_{A,B}) ≫ Φ_{B,A} = Φ_{A,B} ≫ β_{f^*A, f^*B}`,

where `β` is the symmetry `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` of the tensor product
of sheaves of modules.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMapDegIso`: the degreewise comparison, as an
  isomorphism.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap_braiding`: the coherence, for two
  sheaves of `𝒪_D`-modules.
* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMapDeg_braiding`: the same at the modules
  `K^p` and `L^q` of two cochain complexes, with the target spelled at the degrees of the pullback
  complexes. Both the complexes and the degrees swap on the right-hand factor: the comparison that
  follows the pullback of the braiding is the one at `(L^q, K^p)`.
* `Stacks.Sheaves.DerivedPullback.isIso_pullbackToposTensorMap` and
  `Stacks.Sheaves.DerivedPullback.isIso_pullbackToposTensorMapDeg`: the comparison is an
  isomorphism.

## Implementation notes

Everything is stated for `RingedTopos.{u, u, u}`, where `pullbackToposTensorMap` is defined: the
site-presented pullback asks the two sites and the coefficients to share a universe.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor sheafTensorBraiding)
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.DerivedPullback.KFlatPullback

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
  Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf

namespace Stacks.Sheaves.DerivedPullback

section SiteMorphism

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)

/-! ## The four-field coherence and the naturality of the symmetry -/

/-- The symmetry `sheafTensorBraiding` of the tensor product, at `A` and `B`, is the braiding
of the monoidal structure. -/
private lemma sheafTensorBraiding_app_eq_braiding {Z : RingedTopos.{u, u, u}}
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    ((sheafTensorBraiding Z.O).hom.app A).app B = (β_ A B).hom :=
  (congrArg Iso.hom (Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding Z.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).property A B)).symm

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- **The braided coherence of Stacks 03EL for the four-field pullback, at the
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` spelling of the symmetry.** -/
private lemma pullbackTensorIso_hom_app_braiding
    (g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    g.pullbackModules.map (((sheafTensorBraiding Y.O).hom.app A).app B) ≫
        (Stacks.SheafOfModules.pullbackTensorIso g).hom.app (B, A) =
      (Stacks.SheafOfModules.pullbackTensorIso g).hom.app (A, B) ≫
        ((sheafTensorBraiding X.O).hom.app (g.pullbackModules.obj A)).app
          (g.pullbackModules.obj B) := by
  rw [sheafTensorBraiding_app_eq_braiding, sheafTensorBraiding_app_eq_braiding]
  exact Stacks.SheafOfModules.RingedToposPullback.braiding g A B

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **The two-variable naturality of the symmetry of the tensor product of `𝒪_C`-modules**, with
the action of the bifunctor of Tag 0GMW on the pair `(a, b)` written out. -/
private lemma braidingX_naturality_pair
    {A A' B B' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (a : A ⟶ A') (b : B ⟶ B') :
    ((sheafTensorBraiding X.O).hom.app A).app B ≫
        ((sheafTensor.{u, u, u, u, u} X.O).map b).app A ≫
          ((sheafTensor.{u, u, u, u, u} X.O).obj B').map a =
      ((sheafTensor.{u, u, u, u, u} X.O).map a).app B ≫
        ((sheafTensor.{u, u, u, u, u} X.O).obj A').map b ≫
          ((sheafTensorBraiding X.O).hom.app A').app B' := by
  rw [sheafTensorBraiding_app_eq_braiding, sheafTensorBraiding_app_eq_braiding,
    ← Stacks.SheafOfModules.Strict.tensorHom_eq_tensorSheafBifunctor_map X.O b a,
    ← BraidedCategory.braiding_naturality a b,
    ← Category.assoc, Stacks.SheafOfModules.Strict.tensorHom_eq_tensorSheafBifunctor_map X.O a b]

/-! ## The coherence -/

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- **The braided coherence of Stacks 03EL for the site-presented pullback**: the module-level
comparison `pullbackToposTensorMap` is compatible with the symmetry
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` of the tensor product of sheaves of modules. -/
theorem pullbackToposTensorMap_braiding (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    f.pullbackTopos.map (((sheafTensorBraiding Y.O).hom.app A).app B) ≫
        pullbackToposTensorMap f hmos B A =
      pullbackToposTensorMap f hmos A B ≫
        ((sheafTensorBraiding X.O).hom.app (f.pullbackTopos.obj A)).app
          (f.pullbackTopos.obj B) := by
  have hinv : f.pullbackTopos.map (((sheafTensorBraiding Y.O).hom.app A).app B) ≫
        (pullbackModulesSiteIso f hmos).inv.app
          (((sheafTensor.{u, u, u, u, u} Y.O).obj B).obj A) =
      (pullbackModulesSiteIso f hmos).inv.app
          (((sheafTensor.{u, u, u, u, u} Y.O).obj A).obj B) ≫
        (modulesHomOfSiteHom f hmos).pullbackModules.map
          (((sheafTensorBraiding Y.O).hom.app A).app B) :=
    (pullbackModulesSiteIso f hmos).inv.naturality
      (((sheafTensorBraiding Y.O).hom.app A).app B)
  have h2 := pullbackTensorIso_hom_app_braiding (modulesHomOfSiteHom f hmos) A B
  have h3 := braidingX_naturality_pair ((pullbackModulesSiteIso f hmos).hom.app A)
    ((pullbackModulesSiteIso f hmos).hom.app B)
  simp only [pullbackToposTensorMap, Category.assoc]
  rw [reassoc_of% hinv, reassoc_of% h2, h3]

omit
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- **The braided coherence of Stacks 03EL for the site-presented pullback, at the modules of a
fixed bidegree of two cochain complexes.** Both the complexes and the degrees swap in the
right-hand factor of the left-hand side. -/
theorem pullbackToposTensorMapDeg_braiding (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q : ℤ) :
    f.pullbackTopos.map
          (((sheafTensorBraiding Y.O).hom.app (K.X p)).app (L.X q)) ≫
        pullbackToposTensorMapDeg f hmos L K q p =
      pullbackToposTensorMapDeg f hmos K L p q ≫
        ((sheafTensorBraiding X.O).hom.app (((pullbackComplex f).obj K).X p)).app
          (((pullbackComplex f).obj L).X q) := by
  rw [pullbackToposTensorMapDeg_eq, pullbackToposTensorMapDeg_eq]
  exact pullbackToposTensorMap_braiding f hmos (K.X p) (L.X q)

/-! ## The comparison is an isomorphism -/

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- The module-level comparison `pullbackToposTensorMap` for the site-presented pullback is an
isomorphism. -/
theorem isIso_pullbackToposTensorMap (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    IsIso (pullbackToposTensorMap f hmos A B) :=
  (inferInstance : IsIso ((pullbackModulesSiteIso f hmos).inv.app
        (((sheafTensor.{u, u, u, u, u} Y.O).obj A).obj B) ≫
      (Stacks.SheafOfModules.pullbackTensorIso (modulesHomOfSiteHom f hmos)).hom.app (A, B) ≫
      ((sheafTensor.{u, u, u, u, u} X.O).map
          ((pullbackModulesSiteIso f hmos).hom.app A)).app
        ((modulesHomOfSiteHom f hmos).pullbackModules.obj B) ≫
      ((sheafTensor.{u, u, u, u, u} X.O).obj
          (f.pullbackTopos.obj A)).map ((pullbackModulesSiteIso f hmos).hom.app B)))

omit
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- The degreewise comparison `pullbackToposTensorMapDeg` is an isomorphism. -/
theorem isIso_pullbackToposTensorMapDeg (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q : ℤ) :
    IsIso (pullbackToposTensorMapDeg f hmos K L p q) :=
  isIso_pullbackToposTensorMap f hmos (K.X p) (L.X q)

/-- The degreewise comparison of Stacks 03EL for the site-presented pullback, as an
isomorphism. -/
def pullbackToposTensorMapDegIso (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q : ℤ) :
    f.pullbackTopos.obj (((sheafTensor.{u, u, u, u, u} Y.O).obj (K.X p)).obj (L.X q)) ≅
      ((sheafTensor.{u, u, u, u, u} X.O).obj (((pullbackComplex f).obj K).X p)).obj
        (((pullbackComplex f).obj L).X q) :=
  @asIso _ _ _ _ (pullbackToposTensorMapDeg f hmos K L p q)
    (isIso_pullbackToposTensorMapDeg f hmos K L p q)

omit
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- The forward morphism of `pullbackToposTensorMapDegIso` is `pullbackToposTensorMapDeg`. -/
@[simp]
lemma pullbackToposTensorMapDegIso_hom (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q : ℤ) :
    (pullbackToposTensorMapDegIso f hmos K L p q).hom =
      pullbackToposTensorMapDeg f hmos K L p q :=
  rfl

end SiteMorphism

end Stacks.Sheaves.DerivedPullback

end
