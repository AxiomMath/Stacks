module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCompMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorOfToposHom

/-!
# The comparison of total tensor complexes along a composite of morphisms of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi. The comparison `h^*Tot(K ⊗ L) ≅ Tot(h^*K ⊗ h^*L)` of Stacks 03EL for `h = g ∘ f`
is the composite of those for `g` and `f`, read through the compositor of Stacks 03D6 of
degreewise pullbacks.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso_comp_ofComp`: the statement for three
  morphisms of ringed topoi in the four-field sense and an isomorphism of pullbacks along which
  Stacks 03EL composes.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackComplexCompIso`: the compositor of
  degreewise pullbacks of complexes.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorTotalComplexIso_comp`: the statement
  for a composite of morphisms of ringed topoi.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

namespace Stacks.Sheaves.DerivedPullback

open Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂ v₃ u₃

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

/-- A functor carries an identity of two-fold composites to one. -/
private lemma map_comp_map_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q Q' R : C} {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ Q'} {d : Q' ⟶ R} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, h, F.map_comp]

/-- In a category, six commuting relations among morphisms give the equation
`ι₁ ≫ T = ι₁ ≫ cT ≫ FTg ≫ Tf ≫ M`. -/
private lemma summand_chase {C : Type*} [Category C]
    {P₁ P₂ P₃ P₄ Q₀ Q₁ Q₂ Q₃ R₀ R₁ : C}
    {ι₁ : P₁ ⟶ P₂} {T : P₂ ⟶ R₁} {δ : P₁ ⟶ R₀} {ι : R₀ ⟶ R₁}
    {c : P₁ ⟶ Q₀} {fgι : Q₀ ⟶ P₃} {cT : P₂ ⟶ P₃} {Fδg : Q₀ ⟶ Q₁} {Fι' : Q₁ ⟶ P₄}
    {FTg : P₃ ⟶ P₄} {δf : Q₁ ⟶ Q₂} {ι'' : Q₂ ⟶ Q₃} {Tf : P₄ ⟶ Q₃} {m : Q₂ ⟶ R₀}
    {M : Q₃ ⟶ R₁}
    (hι : ι₁ ≫ T = δ ≫ ι) (hδ : δ = c ≫ Fδg ≫ δf ≫ m) (hnat : ι₁ ≫ cT = c ≫ fgι)
    (hg : fgι ≫ FTg = Fδg ≫ Fι') (hf : Fι' ≫ Tf = δf ≫ ι'') (hm : ι'' ≫ M = m ≫ ι) :
    ι₁ ≫ T = ι₁ ≫ cT ≫ FTg ≫ Tf ≫ M := by
  rw [reassoc_of% hnat, reassoc_of% hg, reassoc_of% hf, hm, hι, hδ]
  simp only [Category.assoc]

variable {X : RingedTopos.{v₁, u₁, w}} {Y : RingedTopos.{v₂, u₂, w}}
  {Z : RingedTopos.{v₃, u₃, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)]
  (φ : RingedToposModules.RingedToposHom X Y) (ψ : RingedToposModules.RingedToposHom Y Z)
  (χ : RingedToposModules.RingedToposHom X Z)
  (e : RingedToposHom.pullbackModules χ ≅
    RingedToposHom.pullbackModules ψ ⋙ RingedToposHom.pullbackModules φ)

/-- **The comparison of total tensor complexes of Stacks 03EL along a composite.** Let `e` be an
isomorphism `χ^* ≅ ψ^* ⋙ φ^*` along which the comparison of Stacks 03EL for `χ` is the composite
of those for `ψ` and `φ`, followed by `e⁻¹` in each tensor factor. Then the same holds for the
comparison `χ^*Tot(K ⊗ L) ≅ Tot(χ^*K ⊗ χ^*L)` of total tensor complexes. -/
lemma pullbackTensorTotalIso_comp_ofComp
    (he : ∀ A B : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O)),
      (Stacks.SheafOfModules.pullbackTensorIso χ).hom.app (A, B) =
        e.hom.app ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)).obj
            (A, B)) ≫
          (RingedToposHom.pullbackModules φ).map
            ((Stacks.SheafOfModules.pullbackTensorIso ψ).hom.app (A, B)) ≫
          (Stacks.SheafOfModules.pullbackTensorIso φ).hom.app
            ((RingedToposHom.pullbackModules ψ).obj A, (RingedToposHom.pullbackModules ψ).obj B) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (e.inv.app A)).app
              ((RingedToposHom.pullbackModules φ).obj ((RingedToposHom.pullbackModules ψ).obj B)) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              ((RingedToposHom.pullbackModules χ).obj A)).map (e.inv.app B))
    (E : ∀ K : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) ℤ,
      (pullbackComplexFunctor χ).obj K ≅
        (pullbackComplexFunctor φ).obj ((pullbackComplexFunctor ψ).obj K))
    (hE : ∀ K n, (E K).hom.f n = e.hom.app (K.X n))
    (hE' : ∀ K n, (E K).inv.f n = e.inv.app (K.X n))
    (K L : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) ℤ) :
    (pullbackTensorTotalIso χ K L).hom =
      (E (HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
            (ComplexShape.up ℤ))).hom ≫
        (pullbackComplexFunctor φ).map (pullbackTensorTotalIso ψ K L).hom ≫
        (pullbackTensorTotalIso φ ((pullbackComplexFunctor ψ).obj K)
          ((pullbackComplexFunctor ψ).obj L)).hom ≫
        HomologicalComplex.mapBifunctorMap (E K).inv (E L).inv
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  refine hom_ext_pullbackTotal χ K L n (fun p q hpq ↦ ?_)
  simp only [HomologicalComplex.comp_f, hE]
  have hι := ι_pullbackTensorTotalIso_hom χ K L p q n hpq
  have hδ := he (K.X p) (L.X q)
  have hnat := e.hom.naturality (HomologicalComplex.ιMapBifunctor K L
    (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ) p q n hpq)
  have hg := map_comp_map_eq (RingedToposHom.pullbackModules φ)
    (ι_pullbackTensorTotalIso_hom ψ K L p q n hpq)
  have hf := ι_pullbackTensorTotalIso_hom φ ((pullbackComplexFunctor ψ).obj K)
    ((pullbackComplexFunctor ψ).obj L) p q n hpq
  have hm := HomologicalComplex.ι_mapBifunctorMap (E K).inv (E L).inv
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p q n hpq
  rw [hE', hE'] at hm
  exact summand_chase hι hδ hnat hg hf (hm.trans (Category.assoc _ _ _).symm)

end Stacks.Sheaves.DerivedPullback

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe u c c' c''

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

/-! ## The compositor of degreewise pullbacks -/

/-- The compositor `f^*(g^*K) ≅ (g ∘ f)^*K` of degreewise pullbacks of a complex: Stacks 03D6 in
each degree. -/
def pullbackComplexCompIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    (pullbackComplex f).obj ((pullbackComplex g).obj K) ≅ (pullbackComplex (g.comp f)).obj K :=
  (NatIso.mapHomologicalComplex (RingedToposHom.pullbackModulesCompIso f g).symm
    (ComplexShape.up ℤ)).app K

omit [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)] in
/-- In degree `n`, the compositor `pullbackComplexCompIso` is the inverse of the compositor of
pullbacks of modules at `K.X n`. -/
lemma pullbackComplexCompIso_hom_f
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (n : ℤ) :
    (pullbackComplexCompIso f g K).hom.f n =
      (RingedToposHom.pullbackModulesCompIso f g).inv.app (K.X n) := rfl

omit [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)] in
/-- In degree `n`, the inverse of the compositor `pullbackComplexCompIso` is the compositor of
pullbacks of modules at `K.X n`. -/
lemma pullbackComplexCompIso_inv_f
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (n : ℤ) :
    (pullbackComplexCompIso f g K).inv.f n =
      (RingedToposHom.pullbackModulesCompIso f g).hom.app (K.X n) := rfl

/-! ## Stacks 03EL along a composite, at the curried tensor bifunctor -/

/-- If `t = e.inv ≫ r` for an isomorphism `e`, then `e.hom ≫ t = r`. -/
private lemma cancel_aux {C : Type*} [Category C] {P Q R : C} {e : P ≅ Q} {t : Q ⟶ R}
    {r : P ⟶ R} (h : t = e.inv ≫ r) : e.hom ≫ t = r := by
  rw [h, Iso.hom_inv_id_assoc]

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)] in
/-- **The comparison of total tensor complexes of Stacks 03EL is compatible with the compositor
of degreewise pullbacks**: the compositor at `Tot(K ⊗ L)` followed by the comparison for `g ∘ f`
is `f^*` of the comparison for `g`, then the comparison for `f`, then the compositor in each
tensor factor. -/
lemma pullbackTensorTotalComplexIso_comp
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    (pullbackComplexCompIso f g (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ))).hom ≫
        (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso (g.comp f).toModulesHom K L).hom =
      (Stacks.Sheaves.DerivedPullback.pullbackComplexFunctor f.toModulesHom).map
          (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso g.toModulesHom K L).hom ≫
        (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso f.toModulesHom
          ((Stacks.Sheaves.DerivedPullback.pullbackComplexFunctor g.toModulesHom).obj K)
          ((Stacks.Sheaves.DerivedPullback.pullbackComplexFunctor g.toModulesHom).obj L)).hom ≫
        HomologicalComplex.mapBifunctorMap (pullbackComplexCompIso f g K).symm.inv
          (pullbackComplexCompIso f g L).symm.inv (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) := by
  have h := Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso_comp_ofComp f.toModulesHom
    g.toModulesHom (g.comp f).toModulesHom (RingedToposHom.pullbackModulesCompIso f g)
    (fun A B ↦ RingedToposHom.pullbackTensorIso_hom_app_comp f g A B)
    (fun K ↦ (pullbackComplexCompIso f g K).symm) (fun K n ↦ pullbackComplexCompIso_inv_f f g K n)
    (fun K n ↦ pullbackComplexCompIso_hom_f f g K n) K L
  exact cancel_aux h

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
