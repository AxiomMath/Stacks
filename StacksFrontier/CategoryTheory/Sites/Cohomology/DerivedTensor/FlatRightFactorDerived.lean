module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatHomologyComparison
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.CategoryTheory.Localization.NatTransMapDerivedCategory

/-!
# Tensoring with a flat module in degree zero is the derived functor of tensoring with it

Let `R` be a sheaf of commutative rings on a small site and `N` a flat sheaf of `R`-modules. The
functor `- ⊗_R N` is exact, so it has a derived functor `(- ⊗_R N)~` on `D(R)` computed
termwise; and `N[0]` is K-flat, so the derived tensor product `- ⊗^L N[0]` of
[Stacks, Tag 06YU] is computed by the total tensor complex against `N[0]`, which is the termwise
tensor product. This file records the resulting **natural isomorphism of functors**

  `(- ⊗_R N)~ ≅ - ⊗^L N[0]`,

`Stacks.DerivedTensor.RingedSite.flatTwistNatIso`, built without any choice of representing
complex: it is the lift through the localization `DerivedCategory.Q` of the isomorphism of
functors on cochain complexes given by `CochainComplex.KFlatBifunctor.totalSingleIso` and the
right K-flat comparison of the derived tensor product. It is natural in `N` as well
(`Stacks.DerivedTensor.RingedSite.flatTwistNatIso_naturality_right`).

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedTensor.RingedSite

universe u d

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Modules R)]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

variable (T : DerivedTensorProduct R)

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Conjugating a commutative square by two isomorphisms. -/
theorem inv_comp_eq_comp_inv_of_square {𝒞 : Type*} [Category 𝒞] {a b c d : 𝒞} (i : a ≅ b)
    (j : c ≅ d) (x : b ⟶ d) (y : a ⟶ c) (h : y ≫ j.hom = i.hom ≫ x) :
    i.inv ≫ y = x ≫ j.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Pasting two commutative squares. -/
theorem paste_squares {𝒞 : Type*} [Category 𝒞] {a b c d e f : 𝒞} (u : a ⟶ b) (v : b ⟶ c)
    (w : c ⟶ d) (v' : a ⟶ e) (m : e ⟶ c) (w' : e ⟶ f) (t : f ⟶ d)
    (h₁ : u ≫ v = v' ≫ m) (h₂ : m ≫ w = w' ≫ t) : u ≫ (v ≫ w) = (v' ≫ w') ≫ t := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Transport two commutative squares, one of them along a functor, to a commutative square
between the inverse isomorphisms. -/
private theorem map_comp_inv_square {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] (F : 𝒜 ⥤ ℬ)
    {a b c d : 𝒜} {e e' : ℬ} {i : a ≅ b} {j : c ≅ d} {x : b ⟶ d} {y : a ⟶ c} {i₂ : e ≅ F.obj a}
    {j₂ : e' ≅ F.obj c} {y₂ : e ⟶ e'} (h₁ : y ≫ j.hom = i.hom ≫ x)
    (h₂ : y₂ ≫ j₂.hom = i₂.hom ≫ F.map y) :
    F.map x ≫ (F.map j.inv ≫ j₂.inv) = (F.map i.inv ≫ i₂.inv) ≫ y₂ :=
  paste_squares _ _ _ _ _ _ _
    (((F.map_comp _ _).symm.trans
      (congrArg F.map (inv_comp_eq_comp_inv_of_square _ _ _ _ h₁).symm)).trans (F.map_comp _ _))
    (inv_comp_eq_comp_inv_of_square _ _ _ _ h₂).symm

/-- `N[0]`, as a complex. -/
abbrev singleC (N : Modules R) : CochainComplex (Modules R) ℤ :=
  (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj N

/-- `- ⊗_R N` on sheaves of modules. -/
abbrev flatTwist (N : Modules R) : Modules R ⥤ Modules R :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).flip.obj N

/-- At a complex `L`: `Q(L ⊗ N) ≅ Q(L) ⊗^L N[0]`. -/
def flatTwistQIso (N : Modules R)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N)
    (L : CochainComplex (Modules R) ℤ) :
    DerivedCategory.Q.obj (((flatTwist R N).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≅
      (T.tensor.obj (DerivedCategory.Q.obj L)).obj (DerivedCategory.Q.obj (singleC R N)) :=
  DerivedCategory.Q.mapIso (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) L N).symm ≪≫
    (T.comparisonRight L (singleC R N)
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R N hN 0)).symm

/-- The isomorphism `flatTwistQIso` is natural in the complex `L`. -/
theorem flatTwistQIso_naturality (N : Modules R)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N)
    {L L' : CochainComplex (Modules R) ℤ} (g : L ⟶ L') :
    DerivedCategory.Q.map (((flatTwist R N).mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
        (flatTwistQIso R T N hN L').hom =
      (flatTwistQIso R T N hN L).hom ≫
        (T.tensor.map (DerivedCategory.Q.map g)).app (DerivedCategory.Q.obj (singleC R N)) := by
  have hK := Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R N hN 0
  have h1 := CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) g N
  have h2 := T.comparisonRight_naturality g (𝟙 (singleC R N)) hK hK
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h2
  exact map_comp_inv_square _ h1 h2

/-- The isomorphism `flatTwistQIso` is natural in the flat module `N`: a morphism `N ⟶ N'` of
flat modules induces a commutative square between `flatTwistQIso` at `N` and at `N'`. -/
theorem flatTwistQIso_naturality_right {N N' : Modules R}
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N)
    (hN' : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N') (h : N ⟶ N')
    (L : CochainComplex (Modules R) ℤ) :
    (flatTwistQIso R T N hN L).hom ≫ (T.tensor.obj (DerivedCategory.Q.obj L)).map
        (DerivedCategory.Q.map
          ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map h)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).flip.map h)
          (ComplexShape.up ℤ)).app L) ≫ (flatTwistQIso R T N' hN' L).hom := by
  have hK := Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R N hN 0
  have hK' := Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R N' hN' 0
  have h1 := CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) L h
  have h2 := T.comparisonRight_naturality (𝟙 L)
    ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map h) hK hK'
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h2
  exact (map_comp_inv_square _ h1 h2).symm

variable (N : Modules R) (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N)
  [hAdd : (flatTwist R N).Additive] [hLim : PreservesFiniteLimits (flatTwist R N)]
  [hColim : PreservesFiniteColimits (flatTwist R N)]

/-- **`(- ⊗_R N)~ ≅ - ⊗^L N[0]`** for a flat `N`, as a natural isomorphism of functors on
`D(R)`. -/
def flatTwistNatIso :
    (flatTwist R N).mapDerivedCategory ≅
      T.tensor.flip.obj (DerivedCategory.Q.obj (singleC R N)) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (flatTwist R N).mapDerivedCategory)
    (DerivedCategory.Q ⋙ T.tensor.flip.obj (DerivedCategory.Q.obj (singleC R N))) _ _
    ((flatTwist R N).mapDerivedCategoryFactors ≪≫
      NatIso.ofComponents (flatTwistQIso R T N hN) (fun g => flatTwistQIso_naturality R T N hN g))

/-- At the image `Q(L)` of a complex `L`, the component of `flatTwistNatIso` is the composite of
`mapDerivedCategoryFactors` at `L` with `flatTwistQIso` at `L`. -/
theorem flatTwistNatIso_hom_app_Q (L : CochainComplex (Modules R) ℤ) :
    (flatTwistNatIso R T N hN).hom.app (DerivedCategory.Q.obj L) =
      (flatTwist R N).mapDerivedCategoryFactors.hom.app L ≫ (flatTwistQIso R T N hN L).hom := by
  simp [flatTwistNatIso, Localization.liftNatTrans_app, Localization.Lifting.compLeft_iso]


/-- **`(- ⊗_R N)~ ≅ - ⊗^L N[0]` is natural in `N`.** -/
theorem flatTwistNatIso_naturality_right {N' : Modules R}
    (hN' : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N')
    [hAdd' : (flatTwist R N').Additive] [hLim' : PreservesFiniteLimits (flatTwist R N')]
    [hColim' : PreservesFiniteColimits (flatTwist R N')] (h : N ⟶ N') :
    (flatTwistNatIso R T N hN).hom ≫ T.tensor.flip.map
        (DerivedCategory.Q.map
          ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map h)) =
      NatTrans.mapDerivedCategory
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).flip.map h) ≫
        (flatTwistNatIso R T N' hN').hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ)) (fun L => ?_)
  simp only [NatTrans.comp_app, flatTwistNatIso_hom_app_Q, NatTrans.mapDerivedCategory_app_Q,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  congr 1
  exact flatTwistQIso_naturality_right R T hN hN' h L

end Stacks.DerivedTensor.RingedSite
