module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatModelsGeneral

/-!
# Stacks 07A4 along an isomorphism of pullbacks

Let `φ ψ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be morphisms of ringed topoi and `θ : φ^* ≅ ψ^*` an
isomorphism of pullbacks of sheaves of modules compatible with the comparisons of Stacks 03EL.
The induced isomorphism `Lφ^* ≅ Lψ^*` of derived pullbacks
(`derivedPullbackIsoOfPullbackModulesIso`) carries the isomorphism of Stacks 07A4 for `φ` to the
one for `ψ`.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso_transport`: the statement for total
  tensor complexes.

In the namespace `Stacks.Cohomology.DerivedPullbackOfToposHom`:

* `derivedPullbackIsoOfPullbackModulesIso_hom_app_flatPullbackIso`: `Lφ^* ≅ Lψ^*` on a K-flat
  complex with flat terms.
* `derivedPullbackTensorIso_transport`: the isomorphism of Stacks 07A4 for `φ` is carried to the
  one for `ψ`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

open Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

/-- In a category, the five commuting squares `hnat`, `hψ`, `hφ`, `hm`, `hθ` give
`ι ≫ θT ≫ tψ = ι ≫ tφ ≫ m`. -/
private lemma transport_summand_chase {C : Type*} [Category C] {P₁ P₂ P₃ Q₁ Q₂ R₁ S₁ S₂ : C}
    {ι : P₁ ⟶ P₂} {θT : P₂ ⟶ P₃} {θs : P₁ ⟶ Q₁} {ιψ : Q₁ ⟶ P₃} {tψ : P₃ ⟶ R₁}
    {δψ : Q₁ ⟶ Q₂} {ι' : Q₂ ⟶ R₁} {tφ : P₂ ⟶ S₁} {δφ : P₁ ⟶ S₂} {ι'' : S₂ ⟶ S₁}
    {m : S₁ ⟶ R₁} {θθ : S₂ ⟶ Q₂}
    (hnat : ι ≫ θT = θs ≫ ιψ) (hψ : ιψ ≫ tψ = δψ ≫ ι') (hφ : ι ≫ tφ = δφ ≫ ι'')
    (hm : ι'' ≫ m = θθ ≫ ι') (hθ : θs ≫ δψ = δφ ≫ θθ) :
    ι ≫ θT ≫ tψ = ι ≫ tφ ≫ m := by
  rw [reassoc_of% hnat, hψ, reassoc_of% hθ, reassoc_of% hφ, hm]

variable {X : RingedTopos.{v₁, u₁, w}} {Y : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (φ ψ : RingedToposModules.RingedToposHom X Y)
  (θ : RingedToposHom.pullbackModules φ ≅ RingedToposHom.pullbackModules ψ)

/-- **The comparison of total tensor complexes of Stacks 03EL along an isomorphism of
pullbacks.** If `θ : φ^* ≅ ψ^*` is compatible with the comparisons of Stacks 03EL, then so is
its degreewise extension with the comparisons `h^*Tot(K ⊗ L) ≅ Tot(h^*K ⊗ h^*L)`. -/
lemma pullbackTensorTotalIso_transport
    (hθ : ∀ A B : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)),
      θ.hom.app ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)).obj
          (A, B)) ≫ (Stacks.SheafOfModules.pullbackTensorIso ψ).hom.app (A, B) =
        (Stacks.SheafOfModules.pullbackTensorIso φ).hom.app (A, B) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (θ.hom.app A)).app
              ((RingedToposHom.pullbackModules φ).obj B) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              ((RingedToposHom.pullbackModules ψ).obj A)).map (θ.hom.app B))
    (K L : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ) :
    (NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app
          (HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
            (ComplexShape.up ℤ)) ≫
        (pullbackTensorTotalIso ψ K L).hom =
      (pullbackTensorTotalIso φ K L).hom ≫
        HomologicalComplex.mapBifunctorMap
          ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K)
          ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app L)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  refine hom_ext_pullbackTotal φ K L n (fun p q hpq ↦ ?_)
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
  have hnat := θ.hom.naturality (HomologicalComplex.ιMapBifunctor K L
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p q n hpq)
  have hψ := ι_pullbackTensorTotalIso_hom ψ K L p q n hpq
  have hφ := ι_pullbackTensorTotalIso_hom φ K L p q n hpq
  have hm := HomologicalComplex.ι_mapBifunctorMap
    ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K)
    ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app L)
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p q n hpq
  simp only [NatTrans.mapHomologicalComplex_app_f] at hm
  exact transport_summand_chase hnat hψ hφ (hm.trans (Category.assoc _ _ _).symm)
    (hθ (K.X p) (L.X q))

end Stacks.Sheaves.DerivedPullback

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u c c'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  {φ ψ : RingedToposHom X Y}
  (θ : φ.toModulesHom.pullbackModules ≅ ψ.toModulesHom.pullbackModules)

/-- For a natural transformation `t : F ⟶ G` and morphisms `q`, `cG`, `cF`, `m`, `rG`, `rF`, `Qθ`
with `t.app A₁ ≫ cG = cF ≫ m` and `m ≫ rG = rF ≫ Qθ`, the composite `t.app A₀ ≫ G.map q ≫ cG ≫ rG`
equals `(F.map q ≫ cF ≫ rF) ≫ Qθ`. -/
private lemma transport_flat_chase {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    (t : F ⟶ G) {A₀ A₁ : C} {P₂ P₃ P₄ P₅ : D}
    (q : A₀ ⟶ A₁) (cG : G.obj A₁ ⟶ P₂) (cF : F.obj A₁ ⟶ P₃) (m : P₃ ⟶ P₂)
    (rG : P₂ ⟶ P₄) (rF : P₃ ⟶ P₅) (Qθ : P₅ ⟶ P₄)
    (hc : t.app A₁ ≫ cG = cF ≫ m) (hr : m ≫ rG = rF ≫ Qθ) :
    t.app A₀ ≫ G.map q ≫ cG ≫ rG = (F.map q ≫ cF ≫ rF) ≫ Qθ := by
  rw [← reassoc_of% (t.naturality q), reassoc_of% hc, hr]
  simp only [Category.assoc]

/-- **The isomorphism `Lφ^* ≅ Lψ^*` induced by `θ`, on a K-flat complex with flat terms**: after
the identifications `Lh^*(QK) ≅ Q(h^*K)` of Stacks 06YY it is `θ` in each degree. -/
lemma derivedPullbackIsoOfPullbackModulesIso_hom_app_flatPullbackIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i)) :
    (derivedPullbackIsoOfPullbackModulesIso θ).hom.app (DerivedCategory.Q.obj K) ≫
        (flatPullbackIso ψ K hK hflat).hom =
      (flatPullbackIso φ K hK hflat).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K) := by
  rw [flatPullbackIso_hom_eq, flatPullbackIso_hom_eq]
  exact transport_flat_chase (derivedPullback φ) (derivedPullback ψ)
    (derivedPullbackIsoOfPullbackModulesIso θ).hom _ _ _ _ _ _ _
    (derivedPullbackIsoOfPullbackModulesIso_hom_app θ
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.naturality
      ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K))

/-- **A transformation of functors carries one tensor comparison to another, from models**: if
`c : P ⟶ Q` commutes with the given models of `A`, `B` and `TY.obj (A, B)`, and the tensor
comparisons `tP`, `tQ` are computed on these models, then
`c.app (TY.obj (A, B)) ≫ tQ.app (A, B) = tP.app (A, B) ≫ TX.map (c.app A ×ₘ c.app B)`. -/
private lemma tensorComparison_transport_of_models
    {CY CX : Type*} [Category CY] [Category CX] {TY : CY × CY ⥤ CY} {TX : CX × CX ⥤ CX}
    {P Q : CY ⥤ CX} (c : P ⟶ Q) (tP : TY ⋙ P ⟶ P.prod P ⋙ TX) (tQ : TY ⋙ Q ⟶ Q.prod Q ⋙ TX)
    (A B : CY) {A₁ B₁ A₂ B₂ : CX}
    {a : P.obj A ⟶ A₁} {b : P.obj B ⟶ B₁} {a' : Q.obj A ⟶ A₂} {b' : Q.obj B ⟶ B₂}
    {κ : A₁ ⟶ A₂} {κ' : B₁ ⟶ B₂} {MZ : CY} {MP MQ NP NQ : CX} {s : TY.obj (A, B) ⟶ MZ}
    {mP : P.obj MZ ⟶ MP} {mQ : Q.obj MZ ⟶ MQ} {κM : MP ⟶ MQ} {βP : MP ⟶ NP} {βQ : MQ ⟶ NQ}
    {cmpP : TX.obj (A₁, B₁) ⟶ NP} {cmpQ : TX.obj (A₂, B₂) ⟶ NQ} {κT : NP ⟶ NQ}
    (hmono : Mono (TX.map (a' ×ₘ b'))) (hmono' : Mono cmpQ)
    (hA : c.app A ≫ a' = a ≫ κ) (hB : c.app B ≫ b' = b ≫ κ') (hM : c.app MZ ≫ mQ = mP ≫ κM)
    (hcmp : TX.map (κ ×ₘ κ') ≫ cmpQ = cmpP ≫ κT)
    (hP : tP.app (A, B) ≫ TX.map (a ×ₘ b) ≫ cmpP = P.map s ≫ mP ≫ βP)
    (hQ : tQ.app (A, B) ≫ TX.map (a' ×ₘ b') ≫ cmpQ = Q.map s ≫ mQ ≫ βQ)
    (hβ : κM ≫ βQ = βP ≫ κT) :
    c.app (TY.obj (A, B)) ≫ tQ.app (A, B) = tP.app (A, B) ≫ TX.map (c.app A ×ₘ c.app B) := by
  have hpair : (c.app A ×ₘ c.app B) ≫ (a' ×ₘ b') = (a ×ₘ b) ≫ (κ ×ₘ κ') := by
    ext
    · exact hA
    · exact hB
  apply (cancel_mono (TX.map (a' ×ₘ b'))).1
  apply (cancel_mono cmpQ).1
  simp only [Category.assoc]
  rw [hQ, ← TX.map_comp_assoc, hpair, TX.map_comp_assoc, hcmp, reassoc_of% hP,
    ← reassoc_of% (c.naturality s), reassoc_of% hM, hβ]

section Spelled

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)

omit [X.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasSheafify X.J (Type u)] in
/-- The K-flat comparison of Stacks 06YU is natural, with its target spelled through
`HomologicalComplex.mapBifunctor`. -/
private lemma comparison_naturality_mapBifunctor
    {K K' L L' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (a : K ⟶ K') (b : L ⟶ L')
    (hK : Stacks.SheafOfModules.IsKFlat X.O K) (hK' : Stacks.SheafOfModules.IsKFlat X.O K')
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) (hL' : Stacks.SheafOfModules.IsKFlat X.O L') :
    ((Functor.uncurry.obj TX.tensor).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (TX.comparison K' L' hK' hL').hom :
        (Functor.uncurry.obj TX.tensor).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
          DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K' L'
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) =
      ((TX.comparison K L hK hL).hom :
        (Functor.uncurry.obj TX.tensor).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
          DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  (Category.assoc _ _ _).trans (TX.comparison_naturality a b hK hK' hL hL')

/-- Stacks 07A4 on models, with the target of the K-flat comparison spelled through
`HomologicalComplex.mapBifunctor`. -/
private lemma derivedPullbackTensorIso_hom_app_comp_comparison_mapBifunctor
    (f : RingedToposHom X Y)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i)) :
    (derivedPullbackTensorIso f TX TY).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
      ((Functor.uncurry.obj TX.tensor).map
          ((flatPullbackIso f K hK hflatK).hom ×ₘ (flatPullbackIso f L hL hflatL).hom) ≫
        (TX.comparison ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (kFlat_pullbackComplex' f K hK hflatK) (kFlat_pullbackComplex' f L hL hflatL)).hom :
        (Functor.uncurry.obj TX.tensor).obj ((derivedPullback f).obj (DerivedCategory.Q.obj K),
            (derivedPullback f).obj (DerivedCategory.Q.obj L)) ⟶
          DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor ((pullbackComplex f).obj K)
            ((pullbackComplex f).obj L) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ))) =
      (derivedPullback f).map (TY.comparison K L hK hL).hom ≫
        (flatPullbackIso f (HomologicalComplex.mapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
          (kFlat_mapBifunctor hK hL) (isFlat_mapBifunctor_X K L hflatK hflatL)).hom ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f K L).hom :=
  derivedPullbackTensorIso_hom_app_comp_comparison f TX TY K L hK hL hflatK hflatL

end Spelled

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)
  (hθ : ∀ A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      θ.hom.app ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)).obj
          (A, B)) ≫ (Stacks.SheafOfModules.pullbackTensorIso ψ.toModulesHom).hom.app (A, B) =
        (Stacks.SheafOfModules.pullbackTensorIso φ.toModulesHom).hom.app (A, B) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (θ.hom.app A)).app
              ((φ.toModulesHom.pullbackModules).obj B) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              ((ψ.toModulesHom.pullbackModules).obj A)).map (θ.hom.app B))

include hθ in
/-- **Stacks 07A4 along an isomorphism of pullbacks, at a pair of K-flat complexes with flat
terms.** -/
theorem derivedPullbackTensorIso_transport_app_model
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i)) :
    (derivedPullbackIsoOfPullbackModulesIso θ).hom.app
          ((Functor.uncurry.obj TY.tensor).obj
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso ψ TX TY).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (derivedPullbackTensorIso φ TX TY).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (Functor.uncurry.obj TX.tensor).map
          ((derivedPullbackIsoOfPullbackModulesIso θ).hom.app (DerivedCategory.Q.obj K) ×ₘ
            (derivedPullbackIsoOfPullbackModulesIso θ).hom.app (DerivedCategory.Q.obj L)) := by
  have hiKL : (derivedPullbackIsoOfPullbackModulesIso θ).hom.app (DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj K).obj L)) ≫
        (flatPullbackIso ψ (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
          (kFlat_mapBifunctor hK hL) (isFlat_mapBifunctor_X K L hflatK hflatL)).hom =
      (flatPullbackIso φ (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
          (kFlat_mapBifunctor hK hL) (isFlat_mapBifunctor_X K L hflatK hflatL)).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app
          (HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
            (ComplexShape.up ℤ))) :=
    derivedPullbackIsoOfPullbackModulesIso_hom_app_flatPullbackIso θ
      (HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        (ComplexShape.up ℤ)) (kFlat_mapBifunctor hK hL) (isFlat_mapBifunctor_X K L hflatK hflatL)
  have htr : DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app
        (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) ≫
      DerivedCategory.Q.map (pullbackTensorTotalComplexIso ψ K L).hom =
      DerivedCategory.Q.map (pullbackTensorTotalComplexIso φ K L).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K)
          ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app L)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso_transport φ.toModulesHom
        ψ.toModulesHom θ hθ K L)
  exact tensorComparison_transport_of_models (derivedPullbackIsoOfPullbackModulesIso θ).hom
    (derivedPullbackTensorIso φ TX TY).hom (derivedPullbackTensorIso ψ TX TY).hom
    (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
    (by exact inferInstanceAs (Mono ((Functor.uncurry.obj TX.tensor).mapIso
      ((flatPullbackIso ψ K hK hflatK).prod (flatPullbackIso ψ L hL hflatL))).hom))
    (mono_of_mono_fac (Iso.hom_inv_id _))
    (derivedPullbackIsoOfPullbackModulesIso_hom_app_flatPullbackIso θ K hK hflatK)
    (derivedPullbackIsoOfPullbackModulesIso_hom_app_flatPullbackIso θ L hL hflatL) hiKL
    (comparison_naturality_mapBifunctor TX
      ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K)
      ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app L)
      (kFlat_pullbackComplex' φ K hK hflatK) (kFlat_pullbackComplex' ψ K hK hflatK)
      (kFlat_pullbackComplex' φ L hL hflatL) (kFlat_pullbackComplex' ψ L hL hflatL))
    (derivedPullbackTensorIso_hom_app_comp_comparison_mapBifunctor TX TY φ K L hK hL hflatK hflatL)
    (derivedPullbackTensorIso_hom_app_comp_comparison_mapBifunctor TX TY ψ K L hK hL hflatK hflatL)
    htr

include hθ in
/-- **Stacks 07A4 along an isomorphism of pullbacks.** If `θ : φ^* ≅ ψ^*` is compatible with the
comparisons of Stacks 03EL, the induced `Θ : Lφ^* ≅ Lψ^*` carries the isomorphism of Stacks 07A4
for `φ` to the one for `ψ`: `Θ ≫ α_ψ = α_φ ≫ (Θ ⊗^L Θ)`. -/
theorem derivedPullbackTensorIso_transport :
    Functor.whiskerLeft (Functor.uncurry.obj TY.tensor)
          (derivedPullbackIsoOfPullbackModulesIso θ).hom ≫
        (derivedPullbackTensorIso ψ TX TY).hom =
      (derivedPullbackTensorIso φ TX TY).hom ≫
        Functor.whiskerRight (NatTrans.prod (derivedPullbackIsoOfPullbackModulesIso θ).hom
          (derivedPullbackIsoOfPullbackModulesIso θ).hom) (Functor.uncurry.obj TX.tensor) := by
  have := Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQGeneral_isLocalization Y
  refine Localization.natTrans_ext (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQGeneral Y)
    (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsWGeneral Y) (fun P ↦ ?_)
  exact app_eq_of_iso' _ _ (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIsoGeneral Y P)
    (derivedPullbackTensorIso_transport_app_model θ TX TY hθ P.1.obj.as P.2.obj.as
      P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2)

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
