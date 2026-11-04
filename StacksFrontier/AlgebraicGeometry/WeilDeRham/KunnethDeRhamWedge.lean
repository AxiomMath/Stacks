module

public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethFormulaAffine
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProduct
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethDeRhamPullback
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethInverseImageBase
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethUnbounded

/-!
# The pulled-back forms along the two projections of a fibre product

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, `W = X ×_S Y` with projections `p` and
`q`, and `f = p ≫ a`. The de Rham Künneth map of [Stacks, Tag 0FMB] is formed along the morphisms
of ringed spaces `(W, f^{-1}𝒪_S) ⟶ (X, a^{-1}𝒪_S)` and `(W, f^{-1}𝒪_S) ⟶ (Y, b^{-1}𝒪_S)` of the
box product, while the pullback of de Rham cohomology of [Stacks, Section 0FL6] is formed along
the morphisms of inverse-image ringed spaces attached to the commutative squares of `p` and `q`
over the identity of `S`. The two agree, and this file transports the canonical maps of de Rham
complexes of [Stacks, Tag 0FL5] along that agreement: the comparisons
`Lp^*Ω^•_{X/S} ⟶ Ω^•_{W/S}` and `Lq^*Ω^•_{Y/S} ⟶ Ω^•_{W/S}`, and the canonical maps of
complexes they come from.

## Main definitions

* `Stacks.WeilDeRham.pullbackFormsChainOfEq`, `Stacks.WeilDeRham.pullbackFormsOfEq`: the
  canonical map `h^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}` of complexes and its derived form, for a morphism
  `h` of inverse-image ringed spaces equal to the one attached to a commutative square.
* `Stacks.WeilDeRham.fstFormsQ`, `Stacks.WeilDeRham.sndFormsQ`: the comparisons
  `Lp^*Ω^•_{X/S} ⟶ Ω^•_{W/S}` and `Lq^*Ω^•_{Y/S} ⟶ Ω^•_{W/S}` along the two projections.
* `Stacks.WeilDeRham.fstFormsChain`, `Stacks.WeilDeRham.sndFormsChain`: the canonical maps of
  complexes `p^{-1}Ω^•_{X/S} ⟶ Ω^•_{W/S}` and `q^{-1}Ω^•_{Y/S} ⟶ Ω^•_{W/S}`.

## Main results

* `Stacks.WeilDeRham.deRhamCohomologyPullback_eq_homologyPullback_ofEq`: the pullback of de Rham
  cohomology along a morphism of inverse-image ringed spaces equal to the one of a square.
* `Stacks.WeilDeRham.fstFormsQ_eq`, `Stacks.WeilDeRham.sndFormsQ_eq`: the comparisons are the
  comparison of derived and termwise pullback followed by the canonical maps of complexes.

## References

* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange AlgebraicGeometry.ProperSmoothDeRham
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.BoxKunneth
open Stacks.DerivedTensor.RingedSite
open RingedSpaceModuleAdjunction AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

namespace Stacks.WeilDeRham

/-- Rewriting the last two factors of a threefold composite. -/
theorem comp_comp_comp_eq_comp_comp {C : Type*} [Category* C] {P Q R T U R' : C} (a : P ⟶ Q)
    (b : Q ⟶ R) (c : R ⟶ T) (d : T ⟶ U) (e : R ⟶ R') (g : R' ⟶ U) (h : c ≫ d = e ≫ g) :
    a ≫ (b ≫ c) ≫ d = (a ≫ b ≫ e) ≫ g := by
  simp only [Category.assoc, h]

section OfEq

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The canonical map `h^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}` of extended de Rham complexes, along a
morphism `h` of inverse-image ringed spaces equal to the one attached to the square. -/
def pullbackFormsChainOfEq (h : inverseImageBase f' ⟶ inverseImageBase f)
    (e : inverseImageBaseMap g' f' f g w = h) :
    ((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj (deRhamComplexInt f) ⟶
      deRhamComplexInt f' := by
  subst e
  exact deRhamPullbackInt g' f' f g w

/-- The comparison `Lh^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`, along a morphism `h` of inverse-image ringed
spaces equal to the one attached to the square. -/
def pullbackFormsOfEq (h : inverseImageBase f' ⟶ inverseImageBase f)
    (e : inverseImageBaseMap g' f' f g w = h) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (derivedPullback h).obj (DerivedCategory.Q.obj (deRhamComplexInt f)) ⟶
      DerivedCategory.Q.obj (deRhamComplexInt f') := by
  letI := @HasDerivedCategory.standard.{u, u + 1}
  subst e
  exact deRhamPullbackComparisonQ g' f' f g w

/-- **The comparison is the comparison of derived and termwise pullback followed by the canonical
map of complexes.** -/
theorem pullbackFormsOfEq_eq (h : inverseImageBase f' ⟶ inverseImageBase f)
    (e : inverseImageBaseMap g' f' f g w = h) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    pullbackFormsOfEq g' f' f g w h e =
      pullbackComplexComparison h (deRhamComplexInt f) ≫
        DerivedCategory.Q.map (pullbackFormsChainOfEq g' f' f g w h e) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  subst e
  show deRhamPullbackComparisonQ g' f' f g w = _ ≫ DerivedCategory.Q.map
    (deRhamPullbackInt g' f' f g w)
  rw [deRhamPullbackComparisonQ, deRhamBaseChangeComparison, pullbackComplexComparison]
  have hnat := (DerivedCategory.quotientCompQhIso _).hom.naturality (deRhamPullbackInt g' f' f g w)
  rw [Functor.comp_map] at hnat
  exact comp_comp_comp_eq_comp_comp _ _ _ _ _ _ hnat

/-- `Stacks.WeilDeRham.deRhamCohomologyPullback_eq_homologyPullback` along a morphism `h` of
inverse-image ringed spaces equal to the one attached to the square. -/
theorem deRhamCohomologyPullback_eq_homologyPullback_ofEq
    (h : inverseImageBase f' ⟶ inverseImageBase f) (e : inverseImageBaseMap g' f' f g w = h)
    (m : ℤ) (ξ : Scheme.Hom.deRhamCohomology f m) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
        (Scheme.Hom.deRhamAlgebras f')
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))
        m).hom.hom ((Scheme.Hom.deRhamCohomologyPullback g' f f' g w m).hom ξ) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f'))) m).map
          ((baseSections (inverseImageBase f')).map (pullbackFormsOfEq g' f' f g w h e))).hom
        (Stacks.Cohomology.HomologyPullback.homologyPullback h
          (DerivedCategory.Q.obj (deRhamComplexInt f)) m
          ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
            (Scheme.Hom.deRhamAlgebras f)
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
            m).hom.hom ξ)) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  subst e
  exact deRhamCohomologyPullback_eq_homologyPullback g' f' f g w m ξ

end OfEq

section Box

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The square of the first projection over the identity of `S`. -/
theorem fst_comp_eq : pullback.fst a b ≫ a = (pullback.fst a b ≫ a) ≫ 𝟙 S :=
  (Category.comp_id _).symm

/-- The square of the second projection over the identity of `S`. -/
theorem snd_comp_eq : pullback.snd a b ≫ b = (pullback.fst a b ≫ a) ≫ 𝟙 S :=
  pullback.condition.symm.trans (Category.comp_id _).symm

/-- **The comparison `Lp^*Ω^•_{X/S} ⟶ Ω^•_{W/S}` along the first projection**, on the complex of
`a^{-1}𝒪_S`-modules the Künneth maps are formed on. -/
def fstFormsQ :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (derivedPullback (fstProjection a b)).obj
        (DerivedCategory.Q.obj (leftComplex a (Scheme.Hom.deRhamDiffOpCochainComplex a))) ⟶
      DerivedCategory.Q.obj (deRhamCochainComplex (pullback.fst a b ≫ a)) :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  (derivedPullback (fstProjection a b)).map
      (DerivedCategory.Q.map (leftComplexDeRhamIso a).hom) ≫
    pullbackFormsOfEq (pullback.fst a b) (pullback.fst a b ≫ a) a (𝟙 S) (fst_comp_eq a b)
      (fstProjection a b) (inverseImageBaseMap_eq_fstProjection a b (fst_comp_eq a b))

/-- **The comparison `Lq^*Ω^•_{Y/S} ⟶ Ω^•_{W/S}` along the second projection.** -/
def sndFormsQ :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (derivedPullback (sndProjection a b)).obj
        (DerivedCategory.Q.obj (rightComplex b (Scheme.Hom.deRhamDiffOpCochainComplex b))) ⟶
      DerivedCategory.Q.obj (deRhamCochainComplex (pullback.fst a b ≫ a)) :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  (derivedPullback (sndProjection a b)).map
      (DerivedCategory.Q.map (leftComplexDeRhamIso b).hom) ≫
    pullbackFormsOfEq (pullback.snd a b) (pullback.fst a b ≫ a) b (𝟙 S) (snd_comp_eq a b)
      (sndProjection a b) (inverseImageBaseMap_eq_sndProjection a b (snd_comp_eq a b))

/-- The canonical map `p^{-1}Ω^•_{X/S} ⟶ Ω^•_{W/S}` of complexes along the first projection. -/
def fstFormsChain :
    leftInverseImageComplex a b (Scheme.Hom.deRhamDiffOpCochainComplex a) ⟶
      deRhamCochainComplex (pullback.fst a b ≫ a) :=
  ((modulePullback (fstProjection a b)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (leftComplexDeRhamIso a).hom ≫
    pullbackFormsChainOfEq (pullback.fst a b) (pullback.fst a b ≫ a) a (𝟙 S) (fst_comp_eq a b)
      (fstProjection a b) (inverseImageBaseMap_eq_fstProjection a b (fst_comp_eq a b))

/-- The canonical map `q^{-1}Ω^•_{Y/S} ⟶ Ω^•_{W/S}` of complexes along the second projection. -/
def sndFormsChain :
    rightInverseImageComplex a b (Scheme.Hom.deRhamDiffOpCochainComplex b) ⟶
      deRhamCochainComplex (pullback.fst a b ≫ a) :=
  ((modulePullback (sndProjection a b)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (leftComplexDeRhamIso b).hom ≫
    pullbackFormsChainOfEq (pullback.snd a b) (pullback.fst a b ≫ a) b (𝟙 S) (snd_comp_eq a b)
      (sndProjection a b) (inverseImageBaseMap_eq_sndProjection a b (snd_comp_eq a b))

/-- Naturality of the derived/termwise pullback comparison, composed with a map of the form
`Q.map χ` after the comparison. -/
private theorem derivedPullback_map_comp_eq {Z Z' : RingedSpace.{u, u}} (g : Z ⟶ Z')
    {C C' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    {D : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ} (φ : C ⟶ C') :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ∀ (F : (derivedPullback.{u, u + 1, u + 1} g).obj (DerivedCategory.Q.obj C') ⟶
        DerivedCategory.Q.obj D)
      (χ : ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C' ⟶ D),
      F = pullbackComplexComparison g C' ≫ DerivedCategory.Q.map χ →
      (derivedPullback g).map (DerivedCategory.Q.map φ) ≫ F = pullbackComplexComparison g C ≫
        DerivedCategory.Q.map
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫ χ) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  intro F χ hF
  rw [hF, ← Category.assoc, pullbackComplexComparison_naturality, Category.assoc,
    Functor.map_comp]

/-- **The comparison along the first projection is the comparison of derived and termwise pullback
followed by `Stacks.WeilDeRham.fstFormsChain`.** -/
theorem fstFormsQ_eq :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    fstFormsQ a b = pullbackComplexComparison (fstProjection a b)
        (leftComplex a (Scheme.Hom.deRhamDiffOpCochainComplex a)) ≫
      DerivedCategory.Q.map (fstFormsChain a b) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  exact derivedPullback_map_comp_eq _ _ _ _ (pullbackFormsOfEq_eq (pullback.fst a b)
    (pullback.fst a b ≫ a) a (𝟙 S) (fst_comp_eq a b) (fstProjection a b)
    (inverseImageBaseMap_eq_fstProjection a b (fst_comp_eq a b)))

/-- **The comparison along the second projection is the comparison of derived and termwise
pullback followed by `Stacks.WeilDeRham.sndFormsChain`.** -/
theorem sndFormsQ_eq :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    sndFormsQ a b = pullbackComplexComparison (sndProjection a b)
        (rightComplex b (Scheme.Hom.deRhamDiffOpCochainComplex b)) ≫
      DerivedCategory.Q.map (sndFormsChain a b) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  exact derivedPullback_map_comp_eq _ _ _ _ (pullbackFormsOfEq_eq (pullback.snd a b)
    (pullback.fst a b ≫ a) b (𝟙 S) (snd_comp_eq a b) (sndProjection a b)
    (inverseImageBaseMap_eq_sndProjection a b (snd_comp_eq a b)))

/-- A bifunctor on two composites, with the middle factors interchanged. -/
theorem bifunctor_map_comp_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D ⥤ E) {A A' A'' : C} {B B' B'' : D} (f₁ : A ⟶ A') (f₂ : A' ⟶ A'')
    (g₁ : B ⟶ B') (g₂ : B' ⟶ B'') :
    (F.map (f₁ ≫ f₂)).app B ≫ (F.obj A'').map (g₁ ≫ g₂) =
      (F.map f₁).app B ≫ (F.obj A').map g₁ ≫ (F.map f₂).app B' ≫ (F.obj A'').map g₂ := by
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  congr 1
  rw [← Category.assoc ((F.map f₂).app B), ← NatTrans.naturality, Category.assoc]

/-- A bifunctor, uncurried, on a pair of composites. -/
theorem uncurry_map_prod_comp_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D ⥤ E) {A A' A'' : C} {B B' B'' : D} {f₁ : A ⟶ A'} {f₂ : A' ⟶ A''}
    {g₁ : B ⟶ B'} {g₂ : B' ⟶ B''} {f : A ⟶ A''} {g : B ⟶ B''} (hf : f = f₁ ≫ f₂)
    (hg : g = g₁ ≫ g₂) :
    (Functor.uncurry.obj F).map (f ×ₘ g) =
      (F.map f₁).app B ≫ (F.obj A').map g₁ ≫ (F.map f₂).app B' ≫ (F.obj A'').map g₂ := by
  subst hf hg
  rw [Functor.uncurry_obj_map]
  exact bifunctor_map_comp_comp F f₁ f₂ g₁ g₂

/-- Reassembling a composite through a naturality square and a factorization. -/
theorem comp_eq_of_tensor_naturality {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ B₁ B₂ B₃ : C}
    {α : A₀ ⟶ A₁} {β : A₁ ⟶ A₂} {τ : A₂ ⟶ A₃} {γ : A₃ ⟶ A₄} {x : A₄ ⟶ A₅} {y : A₅ ⟶ A₆}
    {μ : A₃ ⟶ B₃} {m : B₃ ⟶ A₆} {t₁ : A₂ ⟶ B₁} {t₂ : B₁ ⟶ B₂} {τ' : B₂ ⟶ B₃} {r : A₀ ⟶ B₂}
    (hC : γ ≫ x ≫ y = μ ≫ m) (hT : t₁ ≫ t₂ ≫ τ' = τ ≫ μ) (hR : r = α ≫ β ≫ t₁ ≫ t₂) :
    (α ≫ β ≫ τ ≫ γ) ≫ x ≫ y = r ≫ τ' ≫ m := by
  rw [hR]
  simp only [Category.assoc]
  rw [hC, reassoc_of% hT]

end Box

end Stacks.WeilDeRham

end
