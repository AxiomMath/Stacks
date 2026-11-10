module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatModelsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatTensorComplexGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplexComposition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange

/-!
# Stacks 07A4 is compatible with composition of morphisms of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi and `c : Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` the compositor of Stacks 0D6D. The isomorphisms
`α_h : Lh^*(K ⊗^L L) ≅ Lh^*K ⊗^L Lh^*L` of Stacks 07A4 satisfy

`Lf^*(α_g) ≫ α_f ≫ (c ⊗^L c) = c ≫ α_{g ∘ f}`.

Both sides are computed on K-flat complexes with flat terms, where they reduce to the
compatibility of Stacks 03EL with the compositor of Stacks 03D6 on total tensor complexes
(`Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorTotalComplexIso_comp`), and the
identity descends since such pairs localize to `D(O_E) × D(O_E)`.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_comp`: the composition
  law, as an equality of natural transformations, and
  `derivedPullbackTensorIso_comp_app_model` its value at K-flat complexes with flat terms.
* `tensorComparisonCompatible_derivedPullbackTensorIso`: for a commutative square of
  morphisms of ringed topoi, the four isomorphisms of Stacks 07A4 satisfy
  `Stacks.AffineProjectionFormula.TensorComparisonCompatible`, the input of the hexagon of Stacks
  0E48.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackCompIso_hom_app_flatPullbackIso`:
  on a K-flat complex with flat terms the compositor of Stacks 0D6D is the compositor of
  degreewise pullbacks, after the identifications of Stacks 06YY.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_hom_app_comp_comparison`:
  Stacks 07A4 at a pair of K-flat complexes with flat terms, with no inverse left.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe u c c' c''

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}} {Z : RingedTopos.{u, c'', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

/-- The chase behind `derivedPullbackCompIso_hom_app_flatPullbackIso`, for abstract morphisms. -/
lemma compIso_chase {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P₁ P₂ P₃ P₄ P₇ P₉ : D} {A₀ A₅ A₆ A₈ : C}
    {c : F.obj A₀ ⟶ P₁} {Lqinv : P₁ ⟶ P₂} {cmp : P₂ ⟶ P₃} {qhom : P₃ ⟶ P₄}
    {b : A₀ ⟶ A₅} {c' : F.obj A₅ ⟶ P₂} {Lcmpg : F.obj A₅ ⟶ F.obj A₆}
    {cmpf : F.obj A₆ ⟶ P₇}
    {Qhκ : P₇ ⟶ P₃} {qh : A₆ ⟶ A₈} {qi : A₈ ⟶ A₆} {qhom' : P₇ ⟶ P₉} {Qκ : P₉ ⟶ P₄}
    {a : A₅ ⟶ A₆} (ha : F.map a = Lcmpg)
    (hnat : c ≫ Lqinv = F.map b ≫ c') (hfac : c' ≫ cmp = Lcmpg ≫ cmpf ≫ Qhκ)
    (hq : qh ≫ qi = 𝟙 A₆) (hκ : Qhκ ≫ qhom = qhom' ≫ Qκ) :
    c ≫ Lqinv ≫ cmp ≫ qhom =
      F.map (b ≫ a ≫ qh) ≫ (F.map qi ≫ cmpf ≫ qhom') ≫ Qκ := by
  rw [reassoc_of% hnat, reassoc_of% hfac, hκ, Category.assoc, ← F.map_comp_assoc,
    Category.assoc, Category.assoc, hq, Category.comp_id, F.map_comp, ha]
  simp only [Category.assoc]

omit [Z.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify Z.J (Type u)] in
/-- The identification `Lf^*(QK) ≅ Q(f^*K)` of Stacks 06YY, written out. -/
lemma flatPullbackIso_hom_eq
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i)) :
    (flatPullbackIso f K hK hflat).hom =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
        (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
            ((pullbackComplex f).obj K) := rfl

open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
/-- **The compositor of Stacks 0D6D on a K-flat complex with flat terms**: after the
identifications `Lh^*(QK) ≅ Q(h^*K)` of Stacks 06YY it is the compositor of degreewise
pullbacks. -/
lemma derivedPullbackCompIso_hom_app_flatPullbackIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c'', u, u} (O := Z.O) (K.X i)) :
    (derivedPullbackCompIso f g).hom.app (DerivedCategory.Q.obj K) ≫
        (flatPullbackIso (g.comp f) K hK hflat).hom =
      (derivedPullback f).map (flatPullbackIso g K hK hflat).hom ≫
        (flatPullbackIso f ((pullbackComplex g).obj K) (kFlat_pullbackComplex' g K hK hflat)
          (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isFlat_pullbackComplex_X g K
            hflat)).hom ≫
        DerivedCategory.Q.map (pullbackComplexCompIso f g K).hom := by
  have hnat := (derivedPullbackCompIso f g).hom.naturality
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).inv.app K)
  have hfac := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app f g
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have hq := (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom_inv_id_app
        ((pullbackComplex g).obj K)
  have hκ := (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.naturality
    (pullbackComplexCompIso f g K).hom
  rw [flatPullbackIso_hom_eq, flatPullbackIso_hom_eq, flatPullbackIso_hom_eq]
  have hκ' : DerivedCategory.Qh.map ((pullbackMapHomotopyCompIso f g).hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
          ((pullbackComplex (g.comp f)).obj K) =
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
          ((pullbackComplex f).obj ((pullbackComplex g).obj K)) ≫
        DerivedCategory.Q.map (pullbackComplexCompIso f g K).hom := hκ
  exact compIso_chase (derivedPullback f) rfl hnat.symm hfac hq hκ'

omit [X.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J (Type u)] in
/-- The total tensor complex of two K-flat complexes is K-flat, Stacks 079R, with the total
complex spelled through `HomologicalComplex.mapBifunctor`. -/
lemma kFlat_mapBifunctor
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor X.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor X.O) L) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)) :=
  Stacks.SheafOfModules.kFlat_tensorComplex X.O hK hL

omit [X.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify X.J (Type u)] in
/-- The terms of the total tensor complex of two complexes with flat terms are flat, with the
total complex spelled through `HomologicalComplex.mapBifunctor`. -/
lemma isFlat_mapBifunctor_X
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c, u, u} (O := X.O) (K.X i))
    (hL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c, u, u} (O := X.O) (L.X i))
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, c, u, u} (O := X.O)
      ((HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)).X n) :=
  Stacks.Sheaves.DerivedPullback.isFlat_tensorComplex_X_general X.O K L hK hL n

/-! ## Stacks 07A4 on K-flat complexes with flat terms, without inverses -/

/-- Cancelling the inverses of a two-step composite, for abstract morphisms. -/
lemma comp_hom_hom_of_eq_inv {C : Type*} [Category C] {P Q Q' R S T : C}
    {α : P ⟶ S} {l₁ : P ⟶ Q'} {l₂ : Q' ⟶ Q} {q : Q ⟶ R} {a : S ≅ T} {b : T ≅ R}
    (h : α = (l₁ ≫ l₂) ≫ (q ≫ b.inv) ≫ a.inv) : α ≫ a.hom ≫ b.hom = l₁ ≫ l₂ ≫ q := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

section Model

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)

/-- **Stacks 07A4 at a pair of K-flat complexes with flat terms**, followed by the
identifications `Lf^*(QK) ≅ Q(f^*K)` and the K-flat comparison of Stacks 06YU: it is the K-flat
comparison on the target, then the identification at the total tensor complex, then the
comparison of total tensor complexes of Stacks 03EL. -/
lemma derivedPullbackTensorIso_hom_app_comp_comparison
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i)) :
    (derivedPullbackTensorIso f TX TY).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
      (Functor.uncurry.obj TX.tensor).map
          ((flatPullbackIso f K hK hflatK).hom ×ₘ (flatPullbackIso f L hL hflatL).hom) ≫
        (TX.comparison ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (kFlat_pullbackComplex' f K hK hflatK) (kFlat_pullbackComplex' f L hL hflatL)).hom =
      (derivedPullback f).map (TY.comparison K L hK hL).hom ≫
        (flatPullbackIso f (HomologicalComplex.mapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
          (kFlat_mapBifunctor hK hL) (isFlat_mapBifunctor_X K L hflatK hflatL)).hom ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f K L).hom :=
  comp_hom_hom_of_eq_inv
    (a := (Functor.uncurry.obj TX.tensor).mapIso
      ((flatPullbackIso f K hK hflatK).prod (flatPullbackIso f L hL hflatL)))
    (b := TX.comparison ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
      (kFlat_pullbackComplex' f K hK hflatK) (kFlat_pullbackComplex' f L hL hflatL))
    ((derivedPullbackTensorIso_hom_app_model f TX TY K L hK hL hflatK hflatL).trans rfl)

end Model

/-! ## The composition law on K-flat complexes with flat terms -/

/-- A functor carries an identity of a two-fold and a three-fold composite to one. -/
lemma map_comp_eq_map_comp₃ {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q R S T : C} {a : P ⟶ Q} {b : Q ⟶ T} {c : P ⟶ R} {d : R ⟶ S} {e : S ⟶ T}
    (h : a ≫ b = c ≫ d ≫ e) : F.map a ≫ F.map b = F.map c ≫ F.map d ≫ F.map e := by
  rw [← F.map_comp, h, F.map_comp, F.map_comp]

section Composite

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)
  (TZ : Stacks.SheafOfModules.DerivedTensorProduct.{c'', u, u} Z.toRingedSite)

open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
  Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)] in
/-- The compatibility of the comparison of total tensor complexes with the compositor,
`pullbackTensorTotalComplexIso_comp`, read in the derived category. -/
lemma Q_map_pullbackTensorTotalComplexIso_comp
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    DerivedCategory.Q.map (pullbackComplexCompIso f g (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ))).hom ≫
      DerivedCategory.Q.map (pullbackTensorTotalComplexIso (g.comp f) K L).hom =
    DerivedCategory.Q.map ((pullbackComplex f).map (pullbackTensorTotalComplexIso g K L).hom) ≫
      DerivedCategory.Q.map (pullbackTensorTotalComplexIso f ((pullbackComplex g).obj K)
        ((pullbackComplex g).obj L)).hom ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
        (pullbackComplexCompIso f g K).hom (pullbackComplexCompIso f g L).hom
        (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ)) :=
  map_comp_eq_map_comp₃ DerivedCategory.Q (pullbackTensorTotalComplexIso_comp f g K L)

/-- The K-flat comparison of Stacks 06YU on the source is natural along the compositor of
degreewise pullbacks. -/
lemma comparison_naturality_pullbackComplexCompIso
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c'', u, u} (O := Z.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c'', u, u} (O := Z.O) (L.X i)) :
    (Functor.uncurry.obj TX.tensor).map
        (DerivedCategory.Q.map (pullbackComplexCompIso f g K).hom ×ₘ
          DerivedCategory.Q.map (pullbackComplexCompIso f g L).hom) ≫
      (TX.comparison ((pullbackComplex (g.comp f)).obj K) ((pullbackComplex (g.comp f)).obj L)
        (kFlat_pullbackComplex' (g.comp f) K hK hflatK)
        (kFlat_pullbackComplex' (g.comp f) L hL hflatL)).hom =
    (TX.comparison ((pullbackComplex f).obj ((pullbackComplex g).obj K))
        ((pullbackComplex f).obj ((pullbackComplex g).obj L))
        (kFlat_pullbackComplex' f _ (kFlat_pullbackComplex' g K hK hflatK)
          (isFlat_pullbackComplex_X g K hflatK))
        (kFlat_pullbackComplex' f _ (kFlat_pullbackComplex' g L hL hflatL)
          (isFlat_pullbackComplex_X g L hflatL))).hom ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
        (pullbackComplexCompIso f g K).hom (pullbackComplexCompIso f g L).hom
        (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ)) :=
  (Category.assoc _ _ _).trans (TX.comparison_naturality (pullbackComplexCompIso f g K).hom
    (pullbackComplexCompIso f g L).hom _ _ _ _)

/-- **Stacks 07A4 is compatible with composition, at a pair of K-flat complexes with flat
terms.** -/
theorem derivedPullbackTensorIso_comp_app_model
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c'', u, u} (O := Z.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c'', u, u} (O := Z.O) (L.X i)) :
    (derivedPullbackCompIso f g).hom.app
          ((Functor.uncurry.obj TZ.tensor).obj
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso (g.comp f) TX TZ).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (derivedPullback f).map ((derivedPullbackTensorIso g TY TZ).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso f TX TY).hom.app
          ((derivedPullback g).obj (DerivedCategory.Q.obj K),
            (derivedPullback g).obj (DerivedCategory.Q.obj L)) ≫
        (Functor.uncurry.obj TX.tensor).map
          ((derivedPullbackCompIso f g).hom.app (DerivedCategory.Q.obj K) ×ₘ
            (derivedPullbackCompIso f g).hom.app (DerivedCategory.Q.obj L)) := by
  have hK₁ := kFlat_pullbackComplex' g K hK hflatK
  have hL₁ := kFlat_pullbackComplex' g L hL hflatL
  have hfK₁ := isFlat_pullbackComplex_X g K hflatK
  have hfL₁ := isFlat_pullbackComplex_X g L hflatL
  have hA := derivedPullbackCompIso_hom_app_flatPullbackIso f g K hK hflatK
  have hB := derivedPullbackCompIso_hom_app_flatPullbackIso f g L hL hflatL
  have hM := derivedPullbackCompIso_hom_app_flatPullbackIso f g
    (HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)) (kFlat_mapBifunctor hK hL) (isFlat_mapBifunctor_X K L hflatK hflatL)
  have hν := flatPullbackIso_naturality f (pullbackTensorTotalComplexIso g K L).hom
    (kFlat_pullbackComplex' g (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ))
      (kFlat_mapBifunctor hK hL) (isFlat_mapBifunctor_X K L hflatK hflatL))
    (kFlat_mapBifunctor hK₁ hL₁)
    (isFlat_pullbackComplex_X g (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ))
      (isFlat_mapBifunctor_X K L hflatK hflatL))
    (isFlat_mapBifunctor_X ((pullbackComplex g).obj K) ((pullbackComplex g).obj L) hfK₁ hfL₁)
  have hg := derivedPullbackTensorIso_hom_app_comp_comparison g TY TZ K L hK hL hflatK hflatL
  have hf := derivedPullbackTensorIso_hom_app_comp_comparison f TX TY _ _ hK₁ hL₁ hfK₁ hfL₁
  have hh := derivedPullbackTensorIso_hom_app_comp_comparison (g.comp f) TX TZ K L hK hL
    hflatK hflatL
  exact Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models
    (a := (flatPullbackIso g K hK hflatK).hom) (b := (flatPullbackIso g L hL hflatL).hom)
    (a' := (flatPullbackIso f _ hK₁ hfK₁).hom) (b' := (flatPullbackIso f _ hL₁ hfL₁).hom)
    (a'' := (flatPullbackIso (g.comp f) K hK hflatK).hom)
    (b'' := (flatPullbackIso (g.comp f) L hL hflatL).hom)
    (κ := DerivedCategory.Q.map (pullbackComplexCompIso f g K).hom)
    (κ' := DerivedCategory.Q.map (pullbackComplexCompIso f g L).hom)
    (s := (TZ.comparison K L hK hL).hom)
    (m := (flatPullbackIso g (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ))
      (kFlat_mapBifunctor hK hL) (isFlat_mapBifunctor_X K L hflatK hflatL)).hom)
    (β := DerivedCategory.Q.map (pullbackTensorTotalComplexIso g K L).hom)
    (cmpY := (TY.comparison _ _ hK₁ hL₁).hom)
    (m' := (flatPullbackIso f (HomologicalComplex.mapBifunctor ((pullbackComplex g).obj K)
        ((pullbackComplex g).obj L) (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        (ComplexShape.up ℤ)) (kFlat_mapBifunctor hK₁ hL₁)
      (isFlat_mapBifunctor_X ((pullbackComplex g).obj K) ((pullbackComplex g).obj L)
        hfK₁ hfL₁)).hom)
    (β' := DerivedCategory.Q.map (pullbackTensorTotalComplexIso f _ _).hom)
    (cmpX := (TX.comparison _ _ (kFlat_pullbackComplex' f _ hK₁ hfK₁)
      (kFlat_pullbackComplex' f _ hL₁ hfL₁)).hom)
    (m₀ := (flatPullbackIso f ((pullbackComplex g).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ)))
      (kFlat_pullbackComplex' g (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ))
        (kFlat_mapBifunctor hK hL) (isFlat_mapBifunctor_X K L hflatK hflatL))
      (isFlat_pullbackComplex_X g (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ))
        (isFlat_mapBifunctor_X K L hflatK hflatL))).hom)
    (β₀ := DerivedCategory.Q.map
      ((pullbackComplex f).map (pullbackTensorTotalComplexIso g K L).hom))
    (m'' := (flatPullbackIso (g.comp f) (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ))
      (kFlat_mapBifunctor hK hL) (isFlat_mapBifunctor_X K L hflatK hflatL)).hom)
    (β'' := DerivedCategory.Q.map (pullbackTensorTotalComplexIso (g.comp f) K L).hom)
    (cmpX' := (TX.comparison _ _ (kFlat_pullbackComplex' (g.comp f) K hK hflatK)
      (kFlat_pullbackComplex' (g.comp f) L hL hflatL)).hom)
    (κM := DerivedCategory.Q.map (pullbackComplexCompIso f g _).hom)
    (κT := DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      (pullbackComplexCompIso f g K).hom (pullbackComplexCompIso f g L).hom
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ)))
    (derivedPullbackCompIso f g).hom (derivedPullbackTensorIso g TY TZ).hom
    (derivedPullbackTensorIso f TX TY).hom (derivedPullbackTensorIso (g.comp f) TX TZ).hom
    _ _ (inferInstanceAs (Mono ((Functor.uncurry.obj TX.tensor).mapIso
      ((flatPullbackIso (g.comp f) K hK hflatK).prod
        (flatPullbackIso (g.comp f) L hL hflatL))).hom))
    (mono_of_mono_fac (Iso.hom_inv_id _)) hA hB hM hν
    (comparison_naturality_pullbackComplexCompIso f g TX K L hK hL hflatK hflatL) hg hf hh
    (Q_map_pullbackTensorTotalComplexIso_comp f g K L)

/-- Two natural transformations agree at an object once they agree at an isomorphic one. -/
lemma app_eq_of_iso' {C E : Type*} [Category C] [Category E] {A B : C ⥤ E}
    (α β : A ⟶ B) {W W' : C} (e : W ≅ W') (h : α.app W' = β.app W') :
    α.app W = β.app W := by
  rw [← cancel_mono (B.map e.hom), ← α.naturality, ← β.naturality, h]

/-- **Stacks 07A4 is compatible with composition of morphisms of ringed topoi.** For
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)`, the compositor
`c : Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of Stacks 0D6D carries the isomorphism of Stacks 07A4 for
`g ∘ f` to `Lf^*` of the one for `g`, followed by the one for `f` and `c` in each tensor factor:
`c ≫ α_{g ∘ f} = Lf^*(α_g) ≫ α_f ≫ (c ⊗^L c)`. -/
theorem derivedPullbackTensorIso_comp :
    Functor.whiskerLeft (Functor.uncurry.obj TZ.tensor) (derivedPullbackCompIso f g).hom ≫
        (derivedPullbackTensorIso (g.comp f) TX TZ).hom =
      Functor.whiskerRight (derivedPullbackTensorIso g TY TZ).hom (derivedPullback f) ≫
        Functor.whiskerLeft ((derivedPullback g).prod (derivedPullback g))
          (derivedPullbackTensorIso f TX TY).hom ≫
        Functor.whiskerRight
          (NatTrans.prod (derivedPullbackCompIso f g).hom (derivedPullbackCompIso f g).hom)
          (Functor.uncurry.obj TX.tensor) := by
  have := Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQGeneral_isLocalization Z
  refine Localization.natTrans_ext (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQGeneral Z)
    (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsWGeneral Z) (fun P ↦ ?_)
  exact app_eq_of_iso' _ _ (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIsoGeneral Z P)
    (derivedPullbackTensorIso_comp_app_model f g TX TY TZ P.1.obj.as P.2.obj.as
      P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2)

end Composite

/-! ## The four comparisons around a commutative square -/

section Square

open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe d d' e e'

variable {X' : RingedTopos.{u, d, u}} {X₁ : RingedTopos.{u, d', u}} {Y' : RingedTopos.{u, e, u}}
  {Y₁ : RingedTopos.{u, e', u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X₁.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y₁.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X₁.J AddCommGrpCat.{u}] [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y₁.J AddCommGrpCat.{u}] [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X₁.J (Type u)] [HasSheafify Y'.J (Type u)]
  [HasSheafify Y₁.J (Type u)]
  (f : RingedToposHom X₁ Y₁) (g' : RingedToposHom X' X₁) (f' : RingedToposHom X' Y')
  (g : RingedToposHom Y' Y₁) (h : g.comp f' = f.comp g')
  (TX' : Stacks.SheafOfModules.DerivedTensorProduct.{d, u, u} X'.toRingedSite)
  (TX : Stacks.SheafOfModules.DerivedTensorProduct.{d', u, u} X₁.toRingedSite)
  (TY' : Stacks.SheafOfModules.DerivedTensorProduct.{e, u, u} Y'.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{e', u, u} Y₁.toRingedSite)

/-- **The four isomorphisms of Stacks 07A4 around a commutative square of ringed topoi are
compatible.** For a commutative square `g ∘ f' = f ∘ g'` of morphisms of ringed topoi, the two
iterated derived pullbacks `Lg^* ⋙ L(f')^*` and `Lf^* ⋙ L(g')^*` are identified with the derived
pullback along the common composite by Stacks 0D6D; across that identification, the comparison
of Stacks 07A4 along `g` followed by the one along `f'` is the comparison along `f` followed by
the one along `g'`. This is the input
`Stacks.AffineProjectionFormula.TensorComparisonCompatible` of the hexagon of Stacks 0E48, at
every pair of objects. -/
theorem tensorComparisonCompatible_derivedPullbackTensorIso
    (M N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O))) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible
      (derivedPullbackCompIso f' g ≪≫ eqToIso (congrArg (fun m ↦ derivedPullback m) h))
      (derivedPullbackCompIso g' f)
      (Functor.uncurry.obj TY.tensor) (Functor.uncurry.obj TY'.tensor)
      (Functor.uncurry.obj TX.tensor) (Functor.uncurry.obj TX'.tensor)
      (derivedPullbackTensorIso f TX TY).hom (derivedPullbackTensorIso f' TX' TY').hom
      (derivedPullbackTensorIso g TY' TY).hom (derivedPullbackTensorIso g' TX' TX).hom M N :=
  Stacks.Cohomology.DerivedProjectionFormula.tensorComparisonCompatible_of_comparisonSquare
    _ _ _ _ _ _ _ _
    (Stacks.Cohomology.DerivedRelativeCupProduct.comparisonCompatibleWithSquare_of_composition_laws
      _ _ _ _ _ _ _ _ (fun m : RingedToposHom X' Y₁ ↦ derivedPullback m)
      (fun m ↦ (derivedPullbackTensorIso m TX' TY).hom) h (derivedPullbackCompIso f' g)
      (derivedPullbackCompIso g' f) _ rfl
      (derivedPullbackTensorIso_comp f' g TX' TY' TY)
      (derivedPullbackTensorIso_comp g' f TX' TX TY)) M N

end Square

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
