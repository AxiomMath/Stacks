module

public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackAlongRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.DerivedRestrictionOfScalars
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.UnderivedBifunctor

/-!
# Restriction of scalars commutes with the total tensor complex of Stacks 08I6

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi, let `F` be a cochain complex
of `O`-modules and let `G` be a cochain complex of `O'`-modules.  The underived identity of
Stacks 08I6 holds in each bidegree, so the two tensor double complexes

`(p, q) ↦ F^p|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G^q`  and  `(p, q) ↦ (F^p ⊗_O f^*G^q)|_{f⁻¹O'}`

are isomorphic, and passing to total complexes gives

`Tot(F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G) ≅ Tot(F ⊗_O f^*G)|_{f⁻¹O'}`,

naturally in `F` and in `G`.  There is no boundedness hypothesis on `F` or `G`.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.MixedTensorSetup`: the data the identity of total tensor
  complexes is assembled from, and `Stacks.Cohomology.MixedDerivedTensor.setupOfHom`, its
  instance at a morphism of ringed topoi.
* `Stacks.Cohomology.MixedDerivedTensor.MixedTensorSetup.totalComplexIso`: the identity of total
  tensor complexes for a `MixedTensorSetup`.
* `Stacks.Cohomology.MixedDerivedTensor.mixedTensorBicomplexIso`: the underived identity of
  Stacks 08I6 in each bidegree, assembled into an isomorphism of tensor double complexes.
* `Stacks.Cohomology.MixedDerivedTensor.mixedTensorTotalIso`: the identity of total tensor
  complexes `Tot(F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G) ≅ Tot(F ⊗_O f^*G)|_{f⁻¹O'}`.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.ι_mixedTensorTotalIso_hom`: the identity of total
  complexes acts on the summand of bidegree `(p, q)` by the underived identity of Stacks 08I6
  at `(F^p, G^q)`.
* `Stacks.Cohomology.MixedDerivedTensor.mixedTensorTotalIso_hom_naturality`: the identity of
  total tensor complexes is natural in the pair of complexes.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Cohomology.MixedDerivedTensor

open StacksPullbackFactorization HomologicalComplex₂.TotalMap
open Stacks.Sheaves.DerivedPullback.KFlatPullback

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

/-- Two commuting squares pasted along their common edge give a commuting rectangle. -/
lemma pasteTwoSquares {D : Type*} [Category D] {A A' A'' B B' B'' : D}
    {x : A ⟶ A'} {z : A' ⟶ A''} {y : B ⟶ B'} {w : B' ⟶ B''}
    {a : A ⟶ B} {a' : A' ⟶ B'} {a'' : A'' ⟶ B''}
    (h₁ : x ≫ a' = a ≫ y) (h₂ : z ≫ a'' = a' ≫ w) :
    (x ≫ z) ≫ a'' = a ≫ y ≫ w := by
  rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

/-- Three commuting squares pasted along their common edges give a commuting diagram. -/
lemma pasteThreeSquares {D : Type*} [Category D] {A A' B C C₂ E W Z : D}
    {a : A ⟶ A'} {x : A' ⟶ B} {y : A ⟶ C} {s : C ⟶ B} {u' : B ⟶ E} {u : C ⟶ C₂}
    {r : C₂ ⟶ E} {h' : E ⟶ Z} {h : C₂ ⟶ W} {b : W ⟶ Z}
    (h₁ : a ≫ x = y ≫ s) (h₂ : s ≫ u' = u ≫ r) (h₃ : r ≫ h' = h ≫ b) :
    a ≫ x ≫ u' ≫ h' = (y ≫ u ≫ h) ≫ b := by
  rw [← Category.assoc a, h₁, Category.assoc, ← Category.assoc s, h₂, Category.assoc, h₃]
  simp only [Category.assoc]

/-- Five commuting squares `hR`, `h₂`, `hnat`, `h₁` and `hfin`, pasted along their common edges,
give the commuting square `ι ≫ M ≫ A' = ι ≫ A ≫ N`. -/
lemma pasteSummandSquare {D : Type*} [Category D] {S P P' W Q₁ Q₂ Z R R' : D}
    {ι : S ⟶ P} {M : P ⟶ P'} {A' : P' ⟶ W} {x : S ⟶ Q₁} {y : Q₁ ⟶ Q₂} {ι' : Q₂ ⟶ P'}
    {A : P ⟶ Z} {N : Z ⟶ W} {m : S ⟶ R} {r : R ⟶ Z} {m' : Q₂ ⟶ R'} {r' : R' ⟶ W} {k : R ⟶ R'}
    (hR : ι ≫ M = x ≫ y ≫ ι') (h₂ : ι' ≫ A' = m' ≫ r')
    (hnat : (x ≫ y) ≫ m' = m ≫ k) (h₁ : ι ≫ A = m ≫ r) (hfin : r ≫ N = k ≫ r') :
    ι ≫ M ≫ A' = ι ≫ A ≫ N := by
  rw [← Category.assoc, hR, Category.assoc, Category.assoc, h₂, ← Category.assoc,
    ← Category.assoc, hnat, Category.assoc, ← hfin, ← Category.assoc, ← h₁, Category.assoc]

/-! ### The data the identity of total tensor complexes is assembled from -/

/-- Weak sheafification of abelian presheaves on a small site, from the global instance
`Stacks.SheafOfModules.coefficientSheafification`. It is made a local instance of high priority
so that the definitions below find it rather than the section variables
`[HasSheafify J₀ AddCommGrpCat.{u}]`, `[HasSheafify J₁ AddCommGrpCat.{u}]`, and so do not depend
on those variables. -/
abbrev hasWeakSheafifyAddCommGrpCat {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    HasWeakSheafify J AddCommGrpCat.{u} :=
  inferInstance

attribute [local instance high] hasWeakSheafifyAddCommGrpCat

section Setup

variable {C₀ : Type u} [SmallCategory C₀] {J₀ : GrothendieckTopology C₀}
  [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {C₁ : Type u} [SmallCategory C₁] {J₁ : GrothendieckTopology C₁}
  [J₁.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J₁ AddCommGrpCat.{u}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The data the identity of total tensor complexes is assembled from: a sheaf `R₀` of commutative
rings on one site and two, `R₁` and `R₂`, on another; a restriction of scalars `Mod(R₁) ⥤ Mod(R₂)`;
two functors `Mod(R₀) ⥤ Mod(R₁)` and `Mod(R₀) ⥤ Mod(R₂)` on the second tensor factor; and the
underived identity comparing the two ways of tensoring, with its naturality in the `R₀`-module. -/
structure MixedTensorSetup (R₀ : Sheaf J₀ CommRingCat.{u})
    (R₁ R₂ : Sheaf J₁ CommRingCat.{u}) where
  /-- Restriction of scalars from `R₁`-modules to `R₂`-modules. -/
  res : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₁) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₂)
  /-- Restriction of scalars is additive. -/
  resAdditive : res.Additive
  /-- Restriction of scalars preserves the coproducts indexed by the antidiagonal of a total
  degree. -/
  resPreserves : ∀ n : ℤ, Limits.PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) res
  /-- The functor on the second tensor factor landing in `R₁`-modules. -/
  pb : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₀) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₁)
  /-- It preserves zero morphisms. -/
  pbPreservesZero : pb.PreservesZeroMorphisms
  /-- The functor on the second tensor factor landing in `R₂`-modules. -/
  ii : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₀) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₂)
  /-- It preserves zero morphisms. -/
  iiPreservesZero : ii.PreservesZeroMorphisms
  /-- The underived identity: `M|_{R₂} ⊗_{R₂} ii G ≅ (M ⊗_{R₁} pb G)|_{R₂}`, naturally in
  the `R₁`-module `M`. -/
  iso : ∀ G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₀),
    res ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).flip.obj (ii.obj G) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).flip.obj (pb.obj G) ⋙ res
  /-- The underived identity is natural in the `R₀`-module as well. -/
  iso_naturality_snd : ∀ {G G' : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf R₀)} (γ : G ⟶ G')
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₁)),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).obj (res.obj M)).map (ii.map γ) ≫
        (iso G').hom.app M =
      (iso G).hom.app M ≫ res.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).obj M).map (pb.map γ))

namespace MixedTensorSetup

variable {R₀ : Sheaf J₀ CommRingCat.{u}} {R₁ R₂ : Sheaf J₁ CommRingCat.{u}}
  (S : MixedTensorSetup R₀ R₁ R₂)

/-- The restriction of scalars of a `MixedTensorSetup` is additive. -/
instance additive_res : S.res.Additive := S.resAdditive

/-- The functor `pb` of a `MixedTensorSetup` preserves zero morphisms. -/
instance preservesZeroMorphisms_pb : S.pb.PreservesZeroMorphisms := S.pbPreservesZero

/-- The functor `ii` of a `MixedTensorSetup` preserves zero morphisms. -/
instance preservesZeroMorphisms_ii : S.ii.PreservesZeroMorphisms := S.iiPreservesZero

/-- The restriction of scalars of a `MixedTensorSetup` preserves the coproducts indexed by the
antidiagonal of a total degree. -/
instance preservesColimitsOfShape_res (n : ℤ) :
    Limits.PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n})) S.res :=
  S.resPreserves n

/-- Degreewise restriction of scalars on cochain complexes. -/
abbrev resComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₁)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₂)) ℤ :=
  S.res.mapHomologicalComplex (ComplexShape.up ℤ)

/-- `pb` degreewise on cochain complexes. -/
abbrev pbComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₀)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₁)) ℤ :=
  S.pb.mapHomologicalComplex (ComplexShape.up ℤ)

/-- `ii` degreewise on cochain complexes. -/
abbrev iiComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₀)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₂)) ℤ :=
  S.ii.mapHomologicalComplex (ComplexShape.up ℤ)

omit [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J₁ AddCommGrpCat.{u}] in
/-- The underived identity is natural in both modules at once. -/
lemma iso_naturality_map
    {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₀)} (γ : G ⟶ G')
    {M M' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₁)} (φ : M ⟶ M') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).map (S.res.map φ)).app
      (S.ii.obj G) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).obj
            (S.res.obj M')).map (S.ii.map γ)) ≫
        (S.iso G').hom.app M' =
      (S.iso G).hom.app M ≫ S.res.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).map φ).app (S.pb.obj G) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).obj M').map
            (S.pb.map γ)) :=
  (pasteTwoSquares ((S.iso G).hom.naturality φ) (S.iso_naturality_snd γ M')).trans
    (congrArg (fun z => (S.iso G).hom.app M ≫ z) (S.res.map_comp _ _).symm)

section Bicomplex

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).obj M).Additive]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₁)) ℤ)
  (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₀)) ℤ)

/-- The tensor double complex `(p, q) ↦ F^p ⊗_{R₁} pb G^q`. -/
abbrev tensorBicomplex :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj F).obj
      (S.pbComplex.obj G)

/-- The double complex `(p, q) ↦ (F^p ⊗_{R₁} pb G^q)|_{R₂}`. -/
abbrev bicomplexPullback : HomologicalComplex₂
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R₂))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  mapBicomplex S.res (S.tensorBicomplex F G)

/-- The tensor double complex `(p, q) ↦ F^p|_{R₂} ⊗_{R₂} ii G^q`. -/
abbrev bicomplexInverseImage :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj (S.resComplex.obj F)).obj
      (S.iiComplex.obj G)

omit [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J₁ AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).obj M).Additive] in
/-- The differential of `bicomplexPullback` in the second index. -/
lemma d_bicomplexPullback_snd (p q q' : ℤ) :
    ((S.bicomplexPullback F G).X p).d q q' =
      S.res.map (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).obj (F.X p)).map
        (S.pb.map (G.d q q'))) :=
  rfl

omit [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J₁ AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).obj M).Additive] in
/-- The differential of `bicomplexInverseImage` in the second index. -/
lemma d_bicomplexInverseImage_snd (p q q' : ℤ) :
    ((S.bicomplexInverseImage F G).X p).d q q' =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).obj (S.res.obj (F.X p))).map
        (S.ii.map (G.d q q')) :=
  rfl

omit [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J₁ AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).obj M).Additive] in
/-- The differential of `bicomplexPullback` in the first index. -/
lemma d_bicomplexPullback_fst (p p' q : ℤ) :
    ((S.bicomplexPullback F G).d p p').f q =
      S.res.map (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).map (F.d p p')).app
        (S.pb.obj (G.X q))) :=
  rfl

omit [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J₁ AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁).obj M).Additive] in
/-- The differential of `bicomplexInverseImage` in the first index. -/
lemma d_bicomplexInverseImage_fst (p p' q : ℤ) :
    ((S.bicomplexInverseImage F G).d p p').f q =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂).map (S.res.map (F.d p p'))).app
        (S.ii.obj (G.X q)) :=
  rfl

/-- The underived identity in the bidegrees `(p, q)` with `p` fixed, assembled into an
isomorphism of the two columns. -/
def bicomplexIsoX (p : ℤ) :
    (S.bicomplexInverseImage F G).X p ≅ (S.bicomplexPullback F G).X p :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (S.iso (G.X q)).app (F.X p))
    (fun q q' _ =>
      (congrArg (fun z => ((S.iso (G.X q)).app (F.X p)).hom ≫ z)
          (S.d_bicomplexPullback_snd F G p q q')).trans
        ((S.iso_naturality_snd (G.d q q') (F.X p)).symm.trans
          (congrArg (fun z => z ≫ ((S.iso (G.X q')).app (F.X p)).hom)
            (S.d_bicomplexInverseImage_snd F G p q q').symm)))

/-- The underived identity in each bidegree, assembled into an isomorphism of tensor double
complexes. -/
def bicomplexIso : S.bicomplexInverseImage F G ≅ S.bicomplexPullback F G :=
  HomologicalComplex.Hom.isoOfComponents (fun p => S.bicomplexIsoX F G p)
    (fun p p' _ => HomologicalComplex.hom_ext _ _ (fun q =>
      (congrArg (fun z => ((S.iso (G.X q)).app (F.X p)).hom ≫ z)
          (S.d_bicomplexPullback_fst F G p p' q)).trans
        (((S.iso (G.X q)).hom.naturality (F.d p p')).symm.trans
          (congrArg (fun z => z ≫ ((S.iso (G.X q)).app (F.X p')).hom)
            (S.d_bicomplexInverseImage_fst F G p p' q).symm))))

omit [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J₁ AddCommGrpCat.{u}] in
/-- The component of the double-complex identity in bidegree `(p, q)` is the underived identity
at `(F^p, G^q)`. -/
lemma bicomplexIso_hom_f_f (p q : ℤ) :
    ((S.bicomplexIso F G).hom.f p).f q = ((S.iso (G.X q)).app (F.X p)).hom :=
  rfl


/-! #### The identity of total tensor complexes -/

section Total

variable
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf R₁)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf R₂)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂)
      (ComplexShape.up ℤ)]

/-- The restriction of scalars of the tensor double complex has a total complex. -/
instance hasTotal_bicomplexPullback :
    (S.bicomplexPullback F G).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_iso (S.bicomplexIso F G) _

/-- The identity of total tensor complexes
`Tot(F|_{R₂} ⊗_{R₂} ii G) ≅ Tot(F ⊗_{R₁} pb G)|_{R₂}`, for unbounded cochain complexes `F` of
`R₁`-modules and `G` of `R₀`-modules. -/
def totalComplexIso :
    HomologicalComplex.mapBifunctor (S.resComplex.obj F) (S.iiComplex.obj G)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂) (ComplexShape.up ℤ) ≅
      S.resComplex.obj (HomologicalComplex.mapBifunctor F (S.pbComplex.obj G)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁) (ComplexShape.up ℤ)) :=
  HomologicalComplex₂.total.mapIso (S.bicomplexIso F G) (ComplexShape.up ℤ) ≪≫
    totalIso S.res (S.tensorBicomplex F G)

omit [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J₁ AddCommGrpCat.{u}] in
/-- The identity of total tensor complexes acts on the summand of bidegree `(p, q)` by the
underived identity at `(F^p, G^q)`. -/
lemma ι_totalComplexIso_hom (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor (S.resComplex.obj F) (S.iiComplex.obj G)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂) (ComplexShape.up ℤ)
          p q n hpq ≫ (S.totalComplexIso F G).hom.f n =
      (S.iso (G.X q)).hom.app (F.X p) ≫
        S.res.map (HomologicalComplex.ιMapBifunctor F (S.pbComplex.obj G)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁)
            (ComplexShape.up ℤ) p q n hpq) := by
  dsimp only [totalComplexIso, Iso.trans_hom]
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  exact (congrArg (· ≫ (totalIso S.res (S.tensorBicomplex F G)).hom.f n)
    (HomologicalComplex₂.ιTotal_map (S.bicomplexInverseImage F G) (S.bicomplexPullback F G)
      (S.bicomplexIso F G).hom (ComplexShape.up ℤ) p q n hpq)).trans <|
    (Category.assoc _ _ _).trans (congrArg (((S.bicomplexIso F G).hom.f p).f q ≫ ·)
      (ι_totalMapf (c₁₂ := ComplexShape.up ℤ) S.res (S.tensorBicomplex F G) n p q hpq))

section Naturality

variable {F F' : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf R₁)) ℤ} (a : F ⟶ F')
  {G G' : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf R₀)) ℤ} (b : G ⟶ G')

omit [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J₁ AddCommGrpCat.{u}] in
/-- The identity of total tensor complexes is natural in the pair of complexes. -/
lemma totalComplexIso_hom_naturality :
    HomologicalComplex.mapBifunctorMap (S.resComplex.map a) (S.iiComplex.map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₂) (ComplexShape.up ℤ) ≫
        (S.totalComplexIso F' G').hom =
      (S.totalComplexIso F G).hom ≫ S.resComplex.map
        (HomologicalComplex.mapBifunctorMap a (S.pbComplex.map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R₁) (ComplexShape.up ℤ)) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦
    HomologicalComplex.mapBifunctor.hom_ext fun p q hpq ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  exact pasteSummandSquare (HomologicalComplex.ι_mapBifunctorMap ..)
    (S.ι_totalComplexIso_hom F' G' p q n hpq) (S.iso_naturality_map (b.f q) (a.f p))
    (S.ι_totalComplexIso_hom F G p q n hpq)
    (by rw [Functor.mapHomologicalComplex_map_f, ← Functor.map_comp,
      HomologicalComplex.ι_mapBifunctorMap, ← S.res.map_comp, Category.assoc]; rfl)

end Naturality

end Total

end Bicomplex

end MixedTensorSetup

end Setup

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y)

/-! ### The three functors and the underived identity, at the tensor spelling -/

/-- Restriction of scalars along `f⁻¹O' ⟶ O`, with the sheaves of rings written as the tensor
product of Tag 06YM writes them. -/
def restrictToInvRingTensor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f)) :=
  restrictToInvRing f

/-- Restriction of scalars along `f⁻¹O' ⟶ O`, at the tensor spelling, is additive. -/
instance additive_restrictToInvRingTensor : (restrictToInvRingTensor f).Additive :=
  inferInstanceAs (restrictToInvRing f).Additive

/-- Restriction of scalars along `f⁻¹O' ⟶ O`, at the tensor spelling, preserves the colimits
that exist in abelian groups. -/
instance preservesColimitsOfShape_restrictToInvRingTensor {K : Type*} [Category K]
    [HasColimitsOfShape K AddCommGrpCat.{u}] :
    PreservesColimitsOfShape K (restrictToInvRingTensor f) :=
  inferInstanceAs (PreservesColimitsOfShape K (restrictToInvRing f))

/-- Degreewise restriction of scalars along `f⁻¹O' ⟶ O` on cochain complexes, at the same
spelling. -/
abbrev restrictComplexTensor :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ :=
  (restrictToInvRingTensor f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `f^*` on sheaves of modules, at the same spelling. -/
def pullbackToposTensor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  f.pullbackTopos

/-- `f⁻¹` on sheaves of modules, from `O'`-modules to `f⁻¹O'`-modules, at the same spelling. -/
def inverseImageToposTensor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f)) :=
  (auxHomG f).pullbackTopos

/-- `f^*` on sheaves of modules, at the tensor spelling, preserves zero morphisms. -/
instance preservesZeroMorphisms_pullbackToposTensor :
    (pullbackToposTensor f).PreservesZeroMorphisms :=
  inferInstanceAs (f.pullbackTopos).PreservesZeroMorphisms

/-- `f⁻¹` on sheaves of modules, at the tensor spelling, preserves zero morphisms. -/
instance preservesZeroMorphisms_inverseImageToposTensor :
    (inverseImageToposTensor f).PreservesZeroMorphisms :=
  pullbackTopos_preservesZeroMorphisms (auxHomG f)

/-- The `MixedTensorSetup` of Stacks 08I6 at a morphism of ringed topoi: restriction of scalars
along `f⁻¹O' ⟶ O`, the two functors `f^*` and `f⁻¹` on the second tensor factor, and the
underived identity of the tag. -/
def setupOfHom : MixedTensorSetup Y.O X.O (invRing f) where
  res := restrictToInvRingTensor f
  resAdditive := inferInstance
  resPreserves _ := inferInstance
  pb := pullbackToposTensor f
  pbPreservesZero := inferInstance
  ii := inverseImageToposTensor f
  iiPreservesZero := inferInstance
  iso := underivedTensorInverseImageLinearIso f
  iso_naturality_snd γ M := underivedTensorInverseImageLinearIso_naturality_snd f γ M

/-! ### The two tensor double complexes -/

section Bicomplex

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} (invRing f)).obj M).Additive]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)

/-- The tensor double complex `(p, q) ↦ F^p ⊗_O f^*G^q`. -/
abbrev tensorBicomplexPullback :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj F).obj ((pullbackComplex f).obj G)

/-- The double complex `(p, q) ↦ (F^p ⊗_O f^*G^q)|_{f⁻¹O'}`. -/
abbrev mixedTensorBicomplexPullback : HomologicalComplex₂
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f)))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  mapBicomplex (restrictToInvRingTensor f) (tensorBicomplexPullback f F G)

/-- The tensor double complex `(p, q) ↦ F^p|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G^q`, at the same spelling. -/
abbrev mixedTensorBicomplexInverseImage :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      (invRing f)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj ((restrictComplexTensor f).obj F)).obj
      ((pullbackComplex (auxHomG f)).obj G)

/-- The underived identity of Stacks 08I6 in each bidegree, assembled into an isomorphism of
tensor double complexes. -/
def mixedTensorBicomplexIso :
    mixedTensorBicomplexInverseImage f F G ≅ mixedTensorBicomplexPullback f F G :=
  (setupOfHom f).bicomplexIso F G

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The component of the double-complex identity in bidegree `(p, q)` is the underived identity
of Stacks 08I6 at `(F^p, G^q)`. -/
lemma mixedTensorBicomplexIso_hom_f_f (p q : ℤ) :
    ((mixedTensorBicomplexIso f F G).hom.f p).f q =
      ((underivedTensorInverseImageLinearIso f (G.X q)).app (F.X p)).hom :=
  rfl

end Bicomplex

/-! ### The identity of total tensor complexes -/

section Total

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} (invRing f)).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} (invRing f)) (ComplexShape.up ℤ)]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)

/-- The restriction of scalars of the tensor double complex has a total complex. -/
instance hasTotal_mixedTensorBicomplexPullback :
    (mixedTensorBicomplexPullback f F G).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_iso (mixedTensorBicomplexIso f F G) _

/-- The identity of total tensor complexes of Stacks 08I6,
`Tot(F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G) ≅ Tot(F ⊗_O f^*G)|_{f⁻¹O'}`, for unbounded cochain complexes
`F` of `O`-modules and `G` of `O'`-modules. -/
def mixedTensorTotalIso :
    HomologicalComplex.mapBifunctor ((restrictComplexTensor f).obj F)
        ((pullbackComplex (auxHomG f)).obj G)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} (invRing f)) (ComplexShape.up ℤ) ≅
      (restrictComplexTensor f).obj (HomologicalComplex.mapBifunctor F
        ((pullbackComplex f).obj G) (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O)
        (ComplexShape.up ℤ)) :=
  (setupOfHom f).totalComplexIso F G

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The identity of total tensor complexes acts on the summand of bidegree `(p, q)` by the
underived identity of Stacks 08I6 at `(F^p, G^q)`. -/
lemma ι_mixedTensorTotalIso_hom (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor ((restrictComplexTensor f).obj F)
          ((pullbackComplex (auxHomG f)).obj G)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} (invRing f)) (ComplexShape.up ℤ)
          p q n hpq ≫ (mixedTensorTotalIso f F G).hom.f n =
      (underivedTensorInverseImageLinearIso f (G.X q)).hom.app (F.X p) ≫
        (restrictToInvRingTensor f).map (HomologicalComplex.ιMapBifunctor F
          ((pullbackComplex f).obj G) (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O)
          (ComplexShape.up ℤ) p q n hpq) :=
  (setupOfHom f).ι_totalComplexIso_hom F G p q n hpq

section Naturality

variable {F F' : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (a : F ⟶ F')
  {G G' : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ} (b : G ⟶ G')

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The identity of total tensor complexes is natural in the pair of complexes: for morphisms
`a : F ⟶ F'` of cochain complexes of `O`-modules and `b : G ⟶ G'` of cochain complexes of
`O'`-modules, the identity commutes with the total tensor product of `a` and `b`. -/
lemma mixedTensorTotalIso_hom_naturality :
    HomologicalComplex.mapBifunctorMap ((restrictComplexTensor f).map a)
          ((pullbackComplex (auxHomG f)).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} (invRing f))
          (ComplexShape.up ℤ) ≫
        (mixedTensorTotalIso f F' G').hom =
      (mixedTensorTotalIso f F G).hom ≫ (restrictComplexTensor f).map
        (HomologicalComplex.mapBifunctorMap a ((pullbackComplex f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O) (ComplexShape.up ℤ)) :=
  (setupOfHom f).totalComplexIso_hom_naturality a b

end Naturality

end Total

end Stacks.Cohomology.MixedDerivedTensor

end
