module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethWedgeSections
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct

/-!
# Steps (4) and (5) of the de Rham Künneth map are the wedge product of the pulled-back forms

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, `W = X ×_S Y` with projections `p` and
`q`, and `f = p ≫ a`. The de Rham Künneth map of [Stacks, Tag 0FMB]
(`Stacks.Cohomology.BoxKunneth.deRhamGlobalKunnethMap`) ends with steps (4) and (5) of
[Stacks, Tag 0G4A] and the isomorphism `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{W/S}` of
[Stacks, Tag 0FMA]. This file proves that the composite

`Lp^*Ω^•_{X/S} ⊗^𝐋 Lq^*Ω^•_{Y/S} ⟶ Tot(p^{-1}Ω^•_{X/S} ⊗ q^{-1}Ω^•_{Y/S})
  ⟶ Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ⟶ Ω^•_{W/S}`

is the comparison of the derived and the termwise pullback of forms in each factor, followed by
the canonical map to the total tensor complex and the wedge product of [Stacks, Tag 0FM2]. This is
what identifies the de Rham Künneth map on cohomology with the cup product of the pulled-back
classes.

The identity is first proved at the level of complexes
(`Stacks.WeilDeRham.boxTotalComparison_deRhamBoxTotalKunnethIso`), summand by summand of the total
complex: on a summand of nonnegative bidegree both sides are read through the identifications of
the extensions by zero with the terms, which reduces it to
`Stacks.WeilDeRham.relativeBoxComparison_deRhamBoxWedgeHom`; a summand of negative bidegree is
zero.

## Main results

* `Stacks.WeilDeRham.boxTotalComparison_deRhamBoxTotalKunnethIso`: the identity at the level of
  complexes.
* `Stacks.WeilDeRham.boxTotalDerivedComparison_deRhamBoxTotalKunnethIso`: **steps (4) and (5)
  followed by the isomorphism of Tag 0FMA are the wedge product of the pulled-back forms.**

## References

* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.Cohomology.BoxKunneth
open RingedSpaceModuleAdjunction AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open AlgebraicGeometry.Scheme.Hom
open scoped TensorProduct Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

attribute [local instance] AlgebraicGeometry.hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace Stacks.WeilDeRham

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The bookkeeping of the summand identity**: a composite out of a summand of a total complex,
computed along the two sides through the identifications of the extensions. -/
theorem summand_assemble {C D : Type*} [Category* C] [Category* D] (T : C ⥤ C ⥤ C) (I : D ⥤ C)
    {P₀ P₁ P₂ P₃ Q₀ Q₁ Q₂ Q₃ S₀ S₁ S₂ N E : C} {B₀ B₁ G G' : D}
    {a₀ : P₀ ⟶ P₁} {b₀ : Q₀ ⟶ Q₁} {φ : P₁ ⟶ P₂} {ψ : Q₁ ⟶ Q₂} {fC : P₀ ⟶ P₃} {gC : Q₀ ⟶ Q₃}
    {xP : P₃ ⟶ P₂} {xQ : Q₃ ⟶ Q₂}
    {ι : (T.obj P₀).obj Q₀ ⟶ S₀} {tm : S₀ ⟶ S₁} {ι' : (T.obj P₃).obj Q₃ ⟶ S₁} {mult : S₁ ⟶ E}
    {ιN : (T.obj P₂).obj Q₂ ⟶ N} {w : N ⟶ I.obj G} {xinv : I.obj G ⟶ E}
    {c : S₀ ⟶ S₂} {X : S₂ ⟶ I.obj G'} {Y : I.obj G' ⟶ E} {rb₀ : (T.obj P₀).obj Q₀ ⟶ I.obj B₀}
    {bι : I.obj B₀ ⟶ S₂} {bifIso : B₀ ⟶ B₁} {dW : B₁ ⟶ G} {xi : G ⟶ G'}
    {rb : (T.obj P₁).obj Q₁ ⟶ I.obj B₁}
    (hc : ι ≫ c = rb₀ ≫ bι) (hX : bι ≫ X = I.map (bifIso ≫ dW ≫ xi))
    (hnat : rb₀ ≫ I.map bifIso = (T.map a₀).app Q₀ ≫ (T.obj P₁).map b₀ ≫ rb)
    (hY : I.map xi ≫ Y = xinv)
    (hN : rb ≫ I.map dW = ((T.map φ).app Q₁ ≫ (T.obj P₂).map ψ) ≫ (ιN ≫ w))
    (hB : ι ≫ tm = (T.map fC).app Q₀ ≫ (T.obj P₃).map gC ≫ ι')
    (hM : ι' ≫ mult = (T.map xP).app Q₃ ≫ (T.obj P₂).map xQ ≫ ιN ≫ w ≫ xinv)
    (hF : fC ≫ xP = a₀ ≫ φ) (hG : gC ≫ xQ = b₀ ≫ ψ) :
    ι ≫ c ≫ X ≫ Y = ι ≫ tm ≫ mult := by
  have e₁ : (T.map a₀).app Q₀ ≫ (T.map φ).app Q₀ = (T.map fC).app Q₀ ≫ (T.map xP).app Q₀ := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp, hF]
  have e₂ : (T.obj P₂).map b₀ ≫ (T.obj P₂).map ψ = (T.obj P₂).map gC ≫ (T.obj P₂).map xQ := by
    rw [← Functor.map_comp, ← Functor.map_comp, hG]
  rw [reassoc_of% hc, reassoc_of% hX]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, hY, reassoc_of% hN, reassoc_of% hB, hM]
  simp only [NatTrans.naturality_assoc]
  rw [reassoc_of% e₁, reassoc_of% e₂]

/-- The comparison of a pair of isomorphisms under a curried bifunctor is the bifunctor on the
pair of morphisms. -/
theorem curryObj_bifunctorMapIso_hom {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂]
    [Category* D] (F : C₁ × C₂ ⥤ D) {X X' : C₁} {Y Y' : C₂} (e₁ : X ≅ X') (e₂ : Y ≅ Y') :
    ((Functor.curryObj F).bifunctorMapIso e₁ e₂).hom =
      F.map (X := (X, Y)) (Y := (X', Y')) (e₁.hom, e₂.hom) := by
  rw [Functor.bifunctorMapIso_hom]
  show F.map ((e₁.hom, 𝟙 Y) : (X, Y) ⟶ (X', Y)) ≫ F.map ((𝟙 X', e₂.hom) : (X', Y) ⟶ (X', Y')) = _
  rw [← F.map_comp]
  congr 1
  exact Prod.ext (Category.comp_id _) (Category.id_comp _)

/-- Collapsing a chain of composites through three factorizations. -/
theorem comp_chain_of_eq {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ A₅ B : C}
    {ι : A₀ ⟶ A₁} {r : A₁ ⟶ B} {xi : B ⟶ A₂} {xh : A₂ ⟶ B} {d : B ⟶ A₄} {xi' : A₄ ⟶ A₅}
    {β : A₀ ⟶ A₃} {ιN : A₃ ⟶ B} {w : A₃ ⟶ A₄} (h₁ : ι ≫ r = β ≫ ιN) (h₄ : xi ≫ xh = 𝟙 _)
    (h₅ : ιN ≫ d = w) : ι ≫ ((r ≫ xi) ≫ (xh ≫ d ≫ xi')) = β ≫ w ≫ xi' := by
  rw [Category.assoc, reassoc_of% h₁, reassoc_of% h₄, reassoc_of% h₅]

/-- **The isomorphism of Tag 0FMA on a summand of the `ℤ`-indexed total complex**: on
`Ω^p ⊠ Ω^q` it is the wedge product of the pulled-back forms. -/
theorem ι_deRhamBoxTotalKunnethIso_hom_f (p q m : ℕ) (h : (p : ℤ) + (q : ℤ) = (m : ℤ))
    (hpq : p + q = m) :
    HomologicalComplex.ιMapBifunctor (deRhamDiffOpCochainComplex a) (deRhamDiffOpCochainComplex b)
        (boxProductCurried a b) (ComplexShape.up ℤ) p q m h ≫
      (deRhamBoxTotalKunnethIso a b).hom.f (m : ℤ) =
    ((boxProductCurried a b).bifunctorMapIso (deRhamDiffOpCochainComplexXIso a p)
        (deRhamDiffOpCochainComplexXIso b q)).hom ≫
      deRhamBoxWedgeHom a b m p q hpq ≫
      ((deRhamDiffOpComplex (pullback.fst a b ≫ a)).extendXIso ComplexShape.embeddingUpNat
        (embeddingUpNat_f m)).inv := by
  have h₁ : (deRhamBoxTotalKunnethIso a b).hom.f (m : ℤ) =
      (deRhamBoxTotalExtendHom a b).f (m : ℤ) ≫
        (HomologicalComplex.extendMap (deRhamBoxTotalIso a b).hom ComplexShape.embeddingUpNat).f
          (m : ℤ) :=
    Category.id_comp _
  have h₂ : (deRhamBoxTotalExtendHom a b).f (m : ℤ) =
      deRhamBoxTotalRestrictionf a b m ≫
        ((deRhamBoxTotal a b).extendXIso ComplexShape.embeddingUpNat (embeddingUpNat_f m)).inv :=
    (ComplexShape.embeddingUpNat.liftExtend_f _ _ (embeddingUpNat_f m)).trans (Category.id_comp _)
  have h₃ := HomologicalComplex.extendMap_f (deRhamBoxTotalIso a b).hom ComplexShape.embeddingUpNat
    (embeddingUpNat_f m)
  have h₄ : ((deRhamBoxTotal a b).extendXIso ComplexShape.embeddingUpNat
        (embeddingUpNat_f m)).inv ≫
      ((deRhamBoxTotal a b).extendXIso ComplexShape.embeddingUpNat (embeddingUpNat_f m)).hom =
      𝟙 _ :=
    Iso.inv_hom_id _
  have h₅ : HomologicalComplex.ιMapBifunctor (deRhamDiffOpComplex a) (deRhamDiffOpComplex b)
        (boxProductCurried a b) (ComplexShape.up ℕ) p q m hpq ≫ (deRhamBoxTotalIso a b).hom.f m =
      deRhamBoxWedgeHom a b m p q hpq :=
    ιTotal_comp_deRhamBoxTotalDegreeIso_wedgeHom a b m p q hpq
  rw [h₁, h₂, h₃]
  exact comp_chain_of_eq ((ι_deRhamBoxTotalRestrictionf a b m p q h).trans
    (deRhamBoxTotalComponent_natCast a b m p q h)) h₄ h₅

section OfEq

variable {X₀ X₀' S₀ S₀' : Scheme.{u}} (g' : X₀' ⟶ X₀) (f' : X₀' ⟶ S₀') (f : X₀ ⟶ S₀)
  (g : S₀' ⟶ S₀) (w : g' ≫ f = f' ≫ g)

/-- **The extended canonical map of de Rham complexes in a nonnegative degree** is the
`ℕ`-indexed one, read through the identifications of the extensions with the terms. -/
theorem pullbackFormsChainOfEq_f (h : inverseImageBase f' ⟶ inverseImageBase f)
    (e : inverseImageBaseMap g' f' f g w = h) (p : ℕ) :
    (pullbackFormsChainOfEq g' f' f g w h e).f (p : ℤ) ≫
        ((AlgebraicGeometry.ProperSmoothDeRham.deRhamComplexNat f').extendXIso
          ComplexShape.embeddingUpNat (i := p) rfl).hom =
      (modulePullback h).map ((AlgebraicGeometry.ProperSmoothDeRham.deRhamComplexNat f).extendXIso
          ComplexShape.embeddingUpNat (i := p) rfl).hom ≫
        (pullbackFormsNatOfEq g' f' f g w h e).f p := by
  subst e
  exact (AlgebraicGeometry.ProperSmoothDeRham.deRhamPullbackInt_f (g' := g') (f' := f')
    (f := f) (g := g) w p).symm

end OfEq

/-- A functor on a composite in which an isomorphism cancels. -/
theorem map_comp_inv_map_hom_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B B' : C} {E' : D} (u : A ⟶ B) (i : B' ≅ B) (φ : F.obj B ⟶ E') :
    F.map (u ≫ i.inv) ≫ F.map i.hom ≫ φ = F.map u ≫ φ := by
  rw [← Category.assoc, ← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Forms

variable {V T : Scheme.{u}} (c : V ⟶ T)

/-- **The identification of the de Rham complex of differential operators read over `c^{-1}𝒪_T`
with the de Rham complex, in a nonnegative degree**: the two canonical identifications of the
extensions with the terms. -/
theorem leftComplexDeRhamIso_hom_f (n : ℕ) :
    (leftComplexDeRhamIso c).hom.f (n : ℤ) =
      (toInverseImageModules c).map (deRhamDiffOpCochainComplexXIso c n).hom ≫
        ((show CochainComplex (Modules (inverseImageBase c)) ℕ from
          Scheme.Hom.deRhamComplex c).extendXIso ComplexShape.embeddingUpNat
          (embeddingUpNat_f n)).inv := by
  have h₁ := Stacks.DerivedIndexing.mapExtendIso_inv_f_eq (toInverseImageModules c)
    ComplexShape.embeddingUpNat (deRhamDiffOpComplex c) (embeddingUpNat_f n)
  have h₂ := HomologicalComplex.extendMap_f (deRhamComplexInverseImageIso c).hom
    ComplexShape.embeddingUpNat (embeddingUpNat_f n)
  show (Stacks.DerivedIndexing.mapExtendIso (toInverseImageModules c) ComplexShape.embeddingUpNat
      (deRhamDiffOpComplex c)).inv.f (n : ℤ) ≫
    (HomologicalComplex.extendMap (deRhamComplexInverseImageIso c).hom
      ComplexShape.embeddingUpNat).f (n : ℤ) = _
  rw [h₁, h₂]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (_ ≫ ·) (Category.id_comp _)

end Forms

/-- The extended comparison of forms, precomposed with the comparison over `c^{-1}𝒪_T`, in a
nonnegative degree. -/
private theorem pullbackForms_comp_f {X₀ X₀' S₀ S₀' : Scheme.{u}} (g' : X₀' ⟶ X₀)
    (f' : X₀' ⟶ S₀') (f : X₀ ⟶ S₀) (g : S₀' ⟶ S₀) (w : g' ≫ f = f' ≫ g)
    (h : inverseImageBase f' ⟶ inverseImageBase f) (e : inverseImageBaseMap g' f' f g w = h)
    (p : ℕ) :
    (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (leftComplexDeRhamIso f).hom ≫ pullbackFormsChainOfEq g' f' f g w h e).f (p : ℤ) ≫
        (HomologicalComplex.extendXIso
          (show CochainComplex (Modules (inverseImageBase f')) ℕ from
            Scheme.Hom.deRhamComplex f') ComplexShape.embeddingUpNat (i := p) rfl).hom =
      (modulePullback h).map ((toInverseImageModules f).map
          (deRhamDiffOpCochainComplexXIso f p).hom) ≫
        (pullbackFormsNatOfEq g' f' f g w h e).f p := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (pullbackFormsChainOfEq_f _ _ _ _ _ _ _ p)).trans ?_
  refine (congrArg (fun u => (modulePullback h).map u ≫ _)
    (leftComplexDeRhamIso_hom_f f p)).trans ?_
  exact map_comp_inv_map_hom_comp _ _ _ _

/-- **The pulled-back forms along the first projection in a nonnegative degree.** -/
theorem fstFormsChain_f (p : ℕ) :
    (fstFormsChain a b).f (p : ℤ) ≫
        (show (deRhamCochainComplex (pullback.fst a b ≫ a)).X (p : ℤ) ⟶
            (Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a)).X p from
          (HomologicalComplex.extendXIso
            (show CochainComplex (Modules (inverseImageBase (pullback.fst a b ≫ a))) ℕ from
              Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a))
            ComplexShape.embeddingUpNat (i := p) rfl).hom) =
      (modulePullback (fstProjection a b)).map
          ((toInverseImageModules a).map (deRhamDiffOpCochainComplexXIso a p).hom) ≫
        (pullbackFormsNatOfEq (pullback.fst a b) (pullback.fst a b ≫ a) a (𝟙 S)
          (fst_comp_eq a b) (fstProjection a b)
          (inverseImageBaseMap_eq_fstProjection a b (fst_comp_eq a b))).f p := by
  exact pullbackForms_comp_f ..

/-- **The pulled-back forms along the second projection in a nonnegative degree.** -/
theorem sndFormsChain_f (q : ℕ) :
    (sndFormsChain a b).f (q : ℤ) ≫
        (show (deRhamCochainComplex (pullback.fst a b ≫ a)).X (q : ℤ) ⟶
            (Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a)).X q from
          (HomologicalComplex.extendXIso
            (show CochainComplex (Modules (inverseImageBase (pullback.fst a b ≫ a))) ℕ from
              Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a))
            ComplexShape.embeddingUpNat (i := q) rfl).hom) =
      (modulePullback (sndProjection a b)).map
          ((toInverseImageModules b).map (deRhamDiffOpCochainComplexXIso b q).hom) ≫
        (pullbackFormsNatOfEq (pullback.snd a b) (pullback.fst a b ≫ a) b (𝟙 S)
          (snd_comp_eq a b) (sndProjection a b)
          (inverseImageBaseMap_eq_sndProjection a b (snd_comp_eq a b))).f q := by
  exact pullbackForms_comp_f ..


/-- `ι_multiplicationInt_f` for the wedge product of the relative de Rham complex of the fibre
product, in the spelling of complexes of `f^{-1}𝒪_S`-modules. -/
theorem ι_multiplicationInt_wedgeProduct_f (p q m : ℕ) (h : (p : ℤ) + (q : ℤ) = (m : ℤ))
    (hpq : p + q = m) :
    @HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (deRhamCochainComplex (pullback.fst a b ≫ a)) (deRhamCochainComplex (pullback.fst a b ≫ a))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
        (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms
          _ M _ _)
        (ComplexShape.up ℤ) _
        (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
          (deRhamCochainComplex (pullback.fst a b ≫ a))
          (deRhamCochainComplex (pullback.fst a b ≫ a))) _
        p q m h ≫
      (show (@HomologicalComplex.mapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (deRhamCochainComplex (pullback.fst a b ≫ a))
          (deRhamCochainComplex (pullback.fst a b ≫ a))
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
          (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
          (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms
            _ M _ _)
          (ComplexShape.up ℤ) _
          (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
            (deRhamCochainComplex (pullback.fst a b ≫ a))
            (deRhamCochainComplex (pullback.fst a b ≫ a))) _).X (m : ℤ) ⟶
            (deRhamCochainComplex (pullback.fst a b ≫ a)).X (m : ℤ) from
        (AlgebraicGeometry.SheafOfModules.multiplicationInt
          (AlgebraicGeometry.SheafOfModules.wedgeProduct
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))).f (m : ℤ)) =
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).map
        (show (deRhamCochainComplex (pullback.fst a b ≫ a)).X (p : ℤ) ⟶
            (Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a)).X p from
          (HomologicalComplex.extendXIso
            (show CochainComplex (Modules (inverseImageBase (pullback.fst a b ≫ a))) ℕ from
              Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a))
            ComplexShape.embeddingUpNat (i := p) rfl).hom)).app
          ((deRhamCochainComplex (pullback.fst a b ≫ a)).X (q : ℤ)) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
          ((Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a)).X p)).map
        (show (deRhamCochainComplex (pullback.fst a b ≫ a)).X (q : ℤ) ⟶
            (Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a)).X q from
          (HomologicalComplex.extendXIso
            (show CochainComplex (Modules (inverseImageBase (pullback.fst a b ≫ a))) ℕ from
              Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a))
            ComplexShape.embeddingUpNat (i := q) rfl).hom) ≫
      HomologicalComplex.ιMapBifunctor
        (AlgebraicGeometry.SheafOfModules.deRhamComplex
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.deRhamComplex
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} _) (ComplexShape.up ℕ)
        p q m hpq ≫
      (AlgebraicGeometry.SheafOfModules.wedgeProduct
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a)))).f m ≫
      (HomologicalComplex.extendXIso
          (show CochainComplex (Modules (inverseImageBase (pullback.fst a b ≫ a))) ℕ from
            Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a)) ComplexShape.embeddingUpNat
        (embeddingUpNat_f m)).inv :=
  AlgebraicGeometry.SheafOfModules.ι_multiplicationInt_f _ m p q h

/-- The chain-level identity on a summand, with the target read as `f^{-1}𝒪_S`-modules. -/
theorem ι_boxTotalComparison_deRhamBoxTotalKunnethIso_f_modules (p q m : ℕ)
    (h : (p : ℤ) + (q : ℤ) = (m : ℤ)) (hpq : p + q = m) :
    @HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (leftInverseImageComplex a b (deRhamDiffOpCochainComplex a))
        (rightInverseImageComplex a b (deRhamDiffOpCochainComplex b))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
        (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms
          _ M _ _)
        (ComplexShape.up ℤ) _
        (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
          (leftInverseImageComplex a b (deRhamDiffOpCochainComplex a))
          (rightInverseImageComplex a b (deRhamDiffOpCochainComplex b))) _
        p q m h ≫
      (boxTotalComparison a b (deRhamDiffOpCochainComplex a) (deRhamDiffOpCochainComplex b)
          0 0).hom.f (m : ℤ) ≫
      (toInverseImageModules (pullback.fst a b ≫ a)).map
          ((deRhamBoxTotalKunnethIso a b).hom.f (m : ℤ)) ≫
      (leftComplexDeRhamIso (pullback.fst a b ≫ a)).hom.f (m : ℤ) =
    @HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (leftInverseImageComplex a b (deRhamDiffOpCochainComplex a))
        (rightInverseImageComplex a b (deRhamDiffOpCochainComplex b))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
        (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms
          _ M _ _)
        (ComplexShape.up ℤ) _
        (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
          (leftInverseImageComplex a b (deRhamDiffOpCochainComplex a))
          (rightInverseImageComplex a b (deRhamDiffOpCochainComplex b))) _
        p q m h ≫
      (@HomologicalComplex.mapBifunctorMap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (fstFormsChain a b) (sndFormsChain a b)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
        (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
        (ComplexShape.up ℤ) _ _ _ _).f (m : ℤ) ≫
      (show (@HomologicalComplex.mapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (deRhamCochainComplex (pullback.fst a b ≫ a))
          (deRhamCochainComplex (pullback.fst a b ≫ a))
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
          (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
          (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms
            _ M _ _)
          (ComplexShape.up ℤ) _
          (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
            (deRhamCochainComplex (pullback.fst a b ≫ a))
            (deRhamCochainComplex (pullback.fst a b ≫ a))) _).X (m : ℤ) ⟶
            (deRhamCochainComplex (pullback.fst a b ≫ a)).X (m : ℤ) from
        (AlgebraicGeometry.SheafOfModules.multiplicationInt
          (AlgebraicGeometry.SheafOfModules.wedgeProduct
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))).f (m : ℤ)) := by
  have hB := @HomologicalComplex.ι_mapBifunctorMap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fstFormsChain a b) (sndFormsChain a b)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
    (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
    (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
    (ComplexShape.up ℤ) _ _ _ _ (p : ℤ) (q : ℤ) (m : ℤ) h
  have hM := ι_multiplicationInt_wedgeProduct_f a b p q m h hpq
  have hF := fstFormsChain_f a b p
  have hG := sndFormsChain_f a b q
  have hc := (boxTotalComparison a b (deRhamDiffOpCochainComplex a) (deRhamDiffOpCochainComplex b)
    0 0).ι_hom p q m h
  have hX := ((toInverseImageModules (pullback.fst a b ≫ a)).map_comp _ _).symm.trans
    (congrArg (toInverseImageModules (pullback.fst a b ≫ a)).map
      ((ι_deRhamBoxTotalKunnethIso_hom_f a b p q m h hpq).trans
        (congrArg (· ≫ _) (curryObj_bifunctorMapIso_hom _ _ _))))
  have hnat := (relativeBoxComparison_naturality a b (deRhamDiffOpCochainComplexXIso a p).hom
    (deRhamDiffOpCochainComplexXIso b q).hom).symm.trans (Category.assoc _ _ _)
  have hY := (congrArg ((toInverseImageModules (pullback.fst a b ≫ a)).map
      (deRhamDiffOpCochainComplexXIso (pullback.fst a b ≫ a) m).inv ≫ ·)
      (leftComplexDeRhamIso_hom_f (pullback.fst a b ≫ a) m)).trans
    (((toInverseImageModules (pullback.fst a b ≫ a)).mapIso
      (deRhamDiffOpCochainComplexXIso (pullback.fst a b ≫ a) m)).inv_hom_id_assoc _)
  have hN := relativeBoxComparison_deRhamBoxWedgeHom a b p q m hpq
  have key := summand_assemble (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
    (toInverseImageModules (pullback.fst a b ≫ a)) hc hX hnat hY hN hB hM hF hG
  exact key

/-- **The chain-level identity on a summand of nonnegative bidegree.** -/
theorem ι_boxTotalComparison_deRhamBoxTotalKunnethIso_f (p q m : ℕ)
    (h : (p : ℤ) + (q : ℤ) = (m : ℤ)) (hpq : p + q = m) :
    @HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (leftInverseImageComplex a b (deRhamDiffOpCochainComplex a))
        (rightInverseImageComplex a b (deRhamDiffOpCochainComplex b))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
        (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms
          _ M _ _)
        (ComplexShape.up ℤ) _
        (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
          (leftInverseImageComplex a b (deRhamDiffOpCochainComplex a))
          (rightInverseImageComplex a b (deRhamDiffOpCochainComplex b))) _
        p q m h ≫
      (boxTotalComparison a b (deRhamDiffOpCochainComplex a) (deRhamDiffOpCochainComplex b)
          0 0).hom.f (m : ℤ) ≫
      (toInverseImageModules (pullback.fst a b ≫ a)).map
          ((deRhamBoxTotalKunnethIso a b).hom.f (m : ℤ)) ≫
      (leftComplexDeRhamIso (pullback.fst a b ≫ a)).hom.f (m : ℤ) =
    @HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (leftInverseImageComplex a b (deRhamDiffOpCochainComplex a))
        (rightInverseImageComplex a b (deRhamDiffOpCochainComplex b))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
        (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms
          _ M _ _)
        (ComplexShape.up ℤ) _
        (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
          (leftInverseImageComplex a b (deRhamDiffOpCochainComplex a))
          (rightInverseImageComplex a b (deRhamDiffOpCochainComplex b))) _
        p q m h ≫
      (@HomologicalComplex.mapBifunctorMap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (fstFormsChain a b) (sndFormsChain a b)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
        (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
        (ComplexShape.up ℤ) _ _ _ _).f (m : ℤ) ≫
      (AlgebraicGeometry.SheafOfModules.multiplicationInt
        (AlgebraicGeometry.SheafOfModules.wedgeProduct
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))).f (m : ℤ) :=
  ι_boxTotalComparison_deRhamBoxTotalKunnethIso_f_modules a b p q m h hpq

/-- A summand of `Tot(p^{-1}Ω^•_{X/S} ⊗ q^{-1}Ω^•_{Y/S})` with a negative index is zero. -/
theorem isZero_inverseImageTensor_summand (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
          ((leftInverseImageComplex a b (deRhamDiffOpCochainComplex a)).X i)).obj
        ((rightInverseImageComplex a b (deRhamDiffOpCochainComplex b)).X j)) := by
  rcases h with h | h
  · have h₁ := (modulePullback (fstProjection a b)).map_isZero
      ((toInverseImageModules a).map_isZero (isZero_deRhamDiffOpCochainComplex_X a i h))
    exact (@Functor.map_isZero _ _ _ _ _ _ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
      (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _) _ h₁).obj _
  · have h₁ := (modulePullback (sndProjection a b)).map_isZero
      ((toInverseImageModules b).map_isZero (isZero_deRhamDiffOpCochainComplex_X b j h))
    exact @Functor.map_isZero _ _ _ _ _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj _)
      (AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ _ _ _) _ h₁

/-- **Steps (5) and the isomorphism of Tag 0FMA, at the level of complexes**: the comparison
`Tot(p^{-1}Ω^•_{X/S} ⊗ q^{-1}Ω^•_{Y/S}) ⟶ Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ⟶ Ω^•_{W/S}` is the
pulled-back forms in each factor followed by the wedge product. -/
theorem boxTotalComparison_deRhamBoxTotalKunnethIso :
    (boxTotalComparison a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
        (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0).hom ≫
      ((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom ≫
      (leftComplexDeRhamIso (pullback.fst a b ≫ a)).hom =
    @HomologicalComplex.mapBifunctorMap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (fstFormsChain a b) (sndFormsChain a b)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
        (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
        (ComplexShape.up ℤ) _ _ _ _ ≫
      AlgebraicGeometry.SheafOfModules.multiplicationInt
        (AlgebraicGeometry.SheafOfModules.wedgeProduct
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a)))) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine @HomologicalComplex.mapBifunctor.hom_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (leftInverseImageComplex a b (deRhamDiffOpCochainComplex a))
    (rightInverseImageComplex a b (deRhamDiffOpCochainComplex b))
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
    (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
    (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
    (ComplexShape.up ℤ) _
    (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
      (leftInverseImageComplex a b (deRhamDiffOpCochainComplex a))
      (rightInverseImageComplex a b (deRhamDiffOpCochainComplex b))) _ _ _ _ _ fun i j hij => ?_
  have hij' : i + j = n := hij
  by_cases hpos : 0 ≤ i ∧ 0 ≤ j
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.1
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.2
    obtain rfl : n = ((p + q : ℕ) : ℤ) := by push_cast; omega
    exact ι_boxTotalComparison_deRhamBoxTotalKunnethIso_f a b p q (p + q) hij rfl
  · exact (isZero_inverseImageTensor_summand a b i j (by omega)).eq_of_src _ _


section Derived

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- `boxTotalComparison_deRhamBoxTotalKunnethIso` in the derived category. -/
theorem map_boxTotalComparison_deRhamBoxTotalKunnethIso :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    DerivedCategory.Q.map (boxTotalComparison a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
        (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0).hom ≫
      DerivedCategory.Q.map (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom) ≫
      DerivedCategory.Q.map (leftComplexDeRhamIso (pullback.fst a b ≫ a)).hom =
    DerivedCategory.Q.map (@HomologicalComplex.mapBifunctorMap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (fstFormsChain a b) (sndFormsChain a b)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
        (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
        (ComplexShape.up ℤ) _ _ _ _) ≫
      DerivedCategory.Q.map (AlgebraicGeometry.SheafOfModules.multiplicationInt
        (AlgebraicGeometry.SheafOfModules.wedgeProduct
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))) :=
  let := @HasDerivedCategory.standard.{u, u + 1}
  ((DerivedCategory.Q.map_comp _ _).trans
      (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _))).symm.trans
    ((congrArg DerivedCategory.Q.map (boxTotalComparison_deRhamBoxTotalKunnethIso a b)).trans
      (DerivedCategory.Q.map_comp _ _))

/-- The derived tensor product of `fstFormsQ` and `sndFormsQ`, split into the derived-to-termwise
comparisons followed by the termwise pulled-back forms. -/
theorem uncurry_map_fstFormsQ_sndFormsQ :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (Functor.uncurry.obj (derivedTensorProductFunctor
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))).map
        (fstFormsQ a b ×ₘ sndFormsQ a b) =
      ((derivedTensorProductFunctor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).map
          (pullbackComplexComparison (fstProjection a b)
            (leftComplex a (Scheme.Hom.deRhamDiffOpCochainComplex a)))).app
        ((derivedPullback (sndProjection a b)).obj
          (DerivedCategory.Q.obj (rightComplex b (Scheme.Hom.deRhamDiffOpCochainComplex b)))) ≫
      ((derivedTensorProductFunctor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
          (DerivedCategory.Q.obj
            (leftInverseImageComplex a b (Scheme.Hom.deRhamDiffOpCochainComplex a)))).map
        (pullbackComplexComparison (sndProjection a b)
          (rightComplex b (Scheme.Hom.deRhamDiffOpCochainComplex b))) ≫
      ((derivedTensorProductFunctor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).map
          (DerivedCategory.Q.map (fstFormsChain a b))).app
        (DerivedCategory.Q.obj
          (rightInverseImageComplex a b (Scheme.Hom.deRhamDiffOpCochainComplex b))) ≫
      ((derivedTensorProductFunctor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
          (DerivedCategory.Q.obj (deRhamCochainComplex (pullback.fst a b ≫ a)))).map
        (DerivedCategory.Q.map (sndFormsChain a b)) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  exact uncurry_map_prod_comp_comp _ (fstFormsQ_eq a b) (sndFormsQ_eq a b)

/-- **Steps (4) and (5) of the de Rham Künneth map, followed by the isomorphism of Tag 0FMA, are
the wedge product of the pulled-back forms**: the comparisons `Lp^*Ω^•_{X/S} ⟶ Ω^•_{W/S}` and
`Lq^*Ω^•_{Y/S} ⟶ Ω^•_{W/S}`, the canonical map from the derived to the termwise tensor product,
and the wedge product `Tot(Ω^•_{W/S} ⊗ Ω^•_{W/S}) ⟶ Ω^•_{W/S}` of Tag 0FM2. -/
theorem boxTotalDerivedComparison_deRhamBoxTotalKunnethIso :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    boxTotalDerivedComparison a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
        (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0
        (boxTotalComparison a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
          (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0) ≫
      DerivedCategory.Q.map (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom) ≫
      DerivedCategory.Q.map (leftComplexDeRhamIso (pullback.fst a b ≫ a)).hom =
    (Functor.uncurry.obj (derivedTensorProductFunctor
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))).map
        (fstFormsQ a b ×ₘ sndFormsQ a b) ≫
      (canonicalDerivedTensorProduct
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor
        (deRhamCochainComplex (pullback.fst a b ≫ a))
        (deRhamCochainComplex (pullback.fst a b ≫ a)) ≫
      DerivedCategory.Q.map (AlgebraicGeometry.SheafOfModules.multiplicationInt
        (AlgebraicGeometry.SheafOfModules.wedgeProduct
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have hT := (canonicalDerivedTensorProduct
    (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor_naturality
      (fstFormsChain a b) (sndFormsChain a b)
  exact comp_eq_of_tensor_naturality (map_boxTotalComparison_deRhamBoxTotalKunnethIso a b) hT
    (uncurry_map_fstFormsQ_sndFormsQ a b)

end Derived

end Stacks.WeilDeRham
