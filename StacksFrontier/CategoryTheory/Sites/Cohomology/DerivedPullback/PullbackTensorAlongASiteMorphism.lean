module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackAlongRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorTotalNaturality
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos

/-! # Pullback and the total tensor complex, for a site-presented morphism of ringed topoi

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi presented by a functor `f.u`
of the underlying sites which is a morphism of sites, and let `K`, `L` be cochain complexes of
`O'`-modules. For the pullback `f^*` of sheaves of modules attached to that presentation there
is a comparison

`f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)`,

natural in `K` and in `L`, whose component on the summand of bidegree `(p, q)` is the
comparison `f^*(K^p ⊗_{O'} L^q) ≅ f^*K^p ⊗_O f^*L^q` of **Stacks 03EL**.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.mapBifunctorMapIso`: an isomorphism of each factor induces an
  isomorphism of the total complexes of the associated tensor-like bicomplexes.
* `Stacks.Sheaves.DerivedPullback.modulesHomOfSiteHom`: the four-field morphism of ringed topoi
  of Stacks 03D6 attached to a site-presented one whose underlying functor is a morphism of
  sites.
* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso`: the comparison
  `f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)` for the site-presented pullback.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_hom_naturality`: that comparison
  is natural in the pair of complexes.

## Implementation notes

Stacks 03EL, and with it the comparison of total tensor complexes, is proved for the pullback
of sheaves of modules built from the adjoint-pair presentation of the geometric morphism, while
the derived pullback of Stacks 06YY is built from the presentation by a functor of the
underlying sites. The two pullbacks agree by
`AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso`, by uniqueness of left adjoints, and
everything here is the transport of the comparison along that identification: degreewise by
`CategoryTheory.NatTrans.mapHomologicalComplex` and then in each tensor factor by
`mapBifunctorMapIso`. The morphism-of-sites hypothesis is what the passage from a
site-presented morphism of ringed topoi to a morphism of ringed sites consumes; it is the same
hypothesis the derived pullback of Stacks 06YY carries.

The algebra of the total tensor product of a pair of morphisms is read off the uncurried
bifunctor on cochain complexes: `uncurry_map₂CochainComplex_map` identifies
`HomologicalComplex.mapBifunctorMap` with its action on a pair, so composition and identities
are `CategoryTheory.Functor.map_comp` and `map_id` rather than summandwise calculations.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.DerivedPullback

/-! ## The total tensor product of a pair of isomorphisms -/

section MapBifunctor

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {A₁ : Type u₁} [Category.{v₁} A₁] [HasZeroMorphisms A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [HasZeroMorphisms A₂]
  {B : Type u₃} [Category.{v₃} B] [Preadditive B]
  (F : A₁ ⥤ A₂ ⥤ B) [F.PreservesZeroMorphisms] [∀ Z, (F.obj Z).PreservesZeroMorphisms]
  [∀ (K₁ : CochainComplex A₁ ℤ) (K₂ : CochainComplex A₂ ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]

/-- The total complex of the bicomplex `(p, q) ↦ F(K₁^p, K₂^q)` is the value at `(K₁, K₂)` of
the uncurried bifunctor on cochain complexes induced by `F`, and the total complex of a pair of
morphisms is its action on that pair. -/
lemma uncurry_map₂CochainComplex_map
    {K₁ L₁ : CochainComplex A₁ ℤ} {K₂ L₂ : CochainComplex A₂ ℤ}
    (φ : K₁ ⟶ L₁) (ψ : K₂ ⟶ L₂) :
    (Functor.uncurry.obj F.map₂CochainComplex).map ((φ, ψ) : ((K₁, K₂) : _ × _) ⟶ (L₁, L₂)) =
      HomologicalComplex.mapBifunctorMap φ ψ F (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n =>
    HomologicalComplex.mapBifunctor.hom_ext (fun p q hpq => ?_))
  refine Eq.trans ?_
    (HomologicalComplex.ι_mapBifunctorMap φ ψ F (ComplexShape.up ℤ) p q n hpq).symm
  show HomologicalComplex.ιMapBifunctor K₁ K₂ F (ComplexShape.up ℤ) p q n hpq ≫
      (HomologicalComplex.mapBifunctorMap φ (𝟙 K₂) F (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 L₁) ψ F (ComplexShape.up ℤ)).f n =
    (F.map (φ.f p)).app (K₂.X q) ≫ (F.obj (L₁.X p)).map (ψ.f q) ≫
      HomologicalComplex.ιMapBifunctor L₁ L₂ F (ComplexShape.up ℤ) p q n hpq
  rw [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap]
  simp

/-- The total tensor product of a pair of composites is the composite of the total tensor
products. -/
lemma mapBifunctorMap_comp {K₁ L₁ M₁ : CochainComplex A₁ ℤ} {K₂ L₂ M₂ : CochainComplex A₂ ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : L₁ ⟶ M₁) (ψ₁ : K₂ ⟶ L₂) (ψ₂ : L₂ ⟶ M₂) :
    HomologicalComplex.mapBifunctorMap φ₁ ψ₁ F (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap φ₂ ψ₂ F (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap (φ₁ ≫ φ₂) (ψ₁ ≫ ψ₂) F (ComplexShape.up ℤ) := by
  rw [← uncurry_map₂CochainComplex_map F φ₁ ψ₁, ← uncurry_map₂CochainComplex_map F φ₂ ψ₂,
    ← uncurry_map₂CochainComplex_map F (φ₁ ≫ φ₂) (ψ₁ ≫ ψ₂)]
  exact ((Functor.uncurry.obj F.map₂CochainComplex).map_comp
    ((φ₁, ψ₁) : ((K₁, K₂) : _ × _) ⟶ (L₁, L₂)) ((φ₂, ψ₂) : ((L₁, L₂) : _ × _) ⟶ (M₁, M₂))).symm

/-- The total tensor product of a pair of identities is the identity. -/
lemma mapBifunctorMap_id (K₁ : CochainComplex A₁ ℤ) (K₂ : CochainComplex A₂ ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 K₁) (𝟙 K₂) F (ComplexShape.up ℤ) =
      𝟙 (HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ)) := by
  rw [← uncurry_map₂CochainComplex_map F (𝟙 K₁) (𝟙 K₂)]
  exact (Functor.uncurry.obj F.map₂CochainComplex).map_id (K₁, K₂)

/-- An isomorphism of each tensor factor induces an isomorphism of total complexes. -/
@[simps]
def mapBifunctorMapIso {K₁ L₁ : CochainComplex A₁ ℤ} {K₂ L₂ : CochainComplex A₂ ℤ}
    (e₁ : K₁ ≅ L₁) (e₂ : K₂ ≅ L₂) :
    HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ) ≅
      HomologicalComplex.mapBifunctor L₁ L₂ F (ComplexShape.up ℤ) where
  hom := HomologicalComplex.mapBifunctorMap e₁.hom e₂.hom F (ComplexShape.up ℤ)
  inv := HomologicalComplex.mapBifunctorMap e₁.inv e₂.inv F (ComplexShape.up ℤ)
  hom_inv_id := by
    rw [mapBifunctorMap_comp, e₁.hom_inv_id, e₂.hom_inv_id, mapBifunctorMap_id]
  inv_hom_id := by
    rw [mapBifunctorMap_comp, e₁.inv_hom_id, e₂.inv_hom_id, mapBifunctorMap_id]

/-- The isomorphism of total complexes induced by an isomorphism of each factor is natural: a
pair of commuting squares of factors gives a commuting square of total complexes. -/
lemma mapBifunctorMapIso_naturality
    {K₁ L₁ K₁' L₁' : CochainComplex A₁ ℤ} {K₂ L₂ K₂' L₂' : CochainComplex A₂ ℤ}
    (e₁ : K₁ ≅ K₁') (e₂ : K₂ ≅ K₂') (e₁' : L₁ ≅ L₁') (e₂' : L₂ ≅ L₂')
    (φ : K₁ ⟶ L₁) (ψ : K₂ ⟶ L₂) (φ' : K₁' ⟶ L₁') (ψ' : K₂' ⟶ L₂')
    (h₁ : φ ≫ e₁'.hom = e₁.hom ≫ φ') (h₂ : ψ ≫ e₂'.hom = e₂.hom ≫ ψ') :
    HomologicalComplex.mapBifunctorMap φ ψ F (ComplexShape.up ℤ) ≫
        (mapBifunctorMapIso F e₁' e₂').hom =
      (mapBifunctorMapIso F e₁ e₂).hom ≫
        HomologicalComplex.mapBifunctorMap φ' ψ' F (ComplexShape.up ℤ) := by
  rw [mapBifunctorMapIso_hom, mapBifunctorMapIso_hom, mapBifunctorMap_comp,
    mapBifunctorMap_comp, h₁, h₂]

end MapBifunctor

/-! ## Composing two naturality squares -/

section Squares

universe v₀ u₀

variable {Z : Type u₀} [Category.{v₀} Z]

/-- Two commuting squares with a common middle column compose to a commuting square for the
composite of the two isomorphisms. -/
lemma trans_naturality {A A' B B' D D' : Z} {u : A ⟶ A'} {v : B ⟶ B'} {w : D ⟶ D'}
    {e : A ≅ B} {e' : A' ≅ B'} {i : B ≅ D} {i' : B' ≅ D'}
    (he : u ≫ e'.hom = e.hom ≫ v) (hi : v ≫ i'.hom = i.hom ≫ w) :
    u ≫ (e' ≪≫ i').hom = (e ≪≫ i).hom ≫ w := by
  conv_lhs => rw [Iso.trans_hom, ← Category.assoc, he, Category.assoc, hi]
  rw [Iso.trans_hom, Category.assoc]

end Squares

/-! ## The comparison for the site-presented pullback -/

section SiteMorphism

universe u

open Stacks.Sheaves.DerivedPullback.KFlatPullback

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

/-- The morphism of ringed topoi in the four-field presentation of Stacks 03D6 attached to a
site-presented morphism of ringed topoi whose underlying continuous functor is a morphism of
sites. -/
def modulesHomOfSiteHom (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom X Y :=
  (RingedSite.Hom.ofRingedToposSiteHom f hmos).ringedToposHom.toRingedToposModulesHom

/-- The pullback of sheaves of modules along `modulesHomOfSiteHom f hmos` is the pullback along
the site-presented morphism `f`: both are left adjoints of the two pushforwards, which agree. -/
def pullbackModulesSiteIso (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    (modulesHomOfSiteHom f hmos).pullbackModules ≅ f.pullbackTopos :=
  (RingedSite.Hom.ofRingedToposSiteHom f hmos).pullbackModulesToposIso

/-- The identification of the two pullbacks, read degreewise on cochain complexes. -/
def pullbackComplexSiteIso (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    pullbackComplexFunctor (modulesHomOfSiteHom f hmos) ≅ pullbackComplex f :=
  NatIso.mapHomologicalComplex (pullbackModulesSiteIso f hmos) (ComplexShape.up ℤ)

/-- **The comparison `f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)` for the site-presented
pullback**, for unbounded cochain complexes `K`, `L` of `O'`-modules.

It is the comparison of `pullbackTensorTotalIso`, whose component on the summand of bidegree
`(p, q)` is Stacks 03EL, transported along the identification of the two pullbacks of sheaves
of modules. -/
def pullbackToposTensorTotalIso (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  ((pullbackComplexSiteIso f hmos).app (HomologicalComplex.mapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))).symm ≪≫
    pullbackTensorTotalIso (modulesHomOfSiteHom f hmos) K L ≪≫
    mapBifunctorMapIso (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      ((pullbackComplexSiteIso f hmos).app K) ((pullbackComplexSiteIso f hmos).app L)

/-- The second and third isomorphisms of `pullbackToposTensorTotalIso` compose to a square
natural in the pair of complexes: the comparison of Stacks 03EL for the four-field pullback,
followed by the identification of the two pullbacks in each tensor factor. -/
private lemma pullbackToposTensorTotalIso_hom_naturality_aux
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    {K K' L L' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    (pullbackComplexFunctor (modulesHomOfSiteHom f hmos)).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)) ≫
        (pullbackTensorTotalIso (modulesHomOfSiteHom f hmos) K' L' ≪≫
          mapBifunctorMapIso (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
            ((pullbackComplexSiteIso f hmos).app K')
            ((pullbackComplexSiteIso f hmos).app L')).hom =
      (pullbackTensorTotalIso (modulesHomOfSiteHom f hmos) K L ≪≫
          mapBifunctorMapIso (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
            ((pullbackComplexSiteIso f hmos).app K)
            ((pullbackComplexSiteIso f hmos).app L)).hom ≫
        HomologicalComplex.mapBifunctorMap ((pullbackComplex f).map a)
          ((pullbackComplex f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  trans_naturality (pullbackTensorTotalIso_hom_naturality (modulesHomOfSiteHom f hmos) a b)
    (mapBifunctorMapIso_naturality (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      ((pullbackComplexSiteIso f hmos).app K) ((pullbackComplexSiteIso f hmos).app L)
      ((pullbackComplexSiteIso f hmos).app K') ((pullbackComplexSiteIso f hmos).app L')
      ((pullbackComplexFunctor (modulesHomOfSiteHom f hmos)).map a)
      ((pullbackComplexFunctor (modulesHomOfSiteHom f hmos)).map b)
      ((pullbackComplex f).map a) ((pullbackComplex f).map b)
      ((pullbackComplexSiteIso f hmos).hom.naturality a)
      ((pullbackComplexSiteIso f hmos).hom.naturality b))

/-- **The comparison of total tensor complexes for the site-presented pullback is natural in
the pair of complexes.** -/
lemma pullbackToposTensorTotalIso_hom_naturality (hmos : f.u.IsMorphismOfSites Y.J X.J)
    {K K' L L' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    (pullbackComplex f).map (HomologicalComplex.mapBifunctorMap a b
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)) ≫
        (pullbackToposTensorTotalIso f hmos K' L').hom =
      (pullbackToposTensorTotalIso f hmos K L).hom ≫
        HomologicalComplex.mapBifunctorMap ((pullbackComplex f).map a)
          ((pullbackComplex f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  trans_naturality
    ((pullbackComplexSiteIso f hmos).inv.naturality (HomologicalComplex.mapBifunctorMap a b
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)))
    (pullbackToposTensorTotalIso_hom_naturality_aux f hmos a b)

end SiteMorphism

end Stacks.Sheaves.DerivedPullback

end
