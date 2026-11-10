module

public import StacksFrontier.Deformation.Artin.FormalObject.EffectiveDescent
public import StacksFrontier.Deformation.Artin.FormalObject.RealizationRepresentable
public import StacksFrontier.Deformation.Artin.FormalObject.BaseContains
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChartPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.OfIsSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints

/-!
# Every formal object of an algebraic stack is effective (Stacks 07X8)

Let `𝒳` be an algebraic stack over a scheme `S`. **Stacks 07X8** says that the approximation
functor of **Stacks 07X6**, from objects of `𝒳` over spectra of Noetherian complete local
`S`-algebras with finite type residue field to formal objects of `𝒳`, is an equivalence. Its full
faithfulness is `Deformation.Artin.fullyFaithful_approximationFunctor_of_isAlgebraicStack`; this
file proves the essential surjectivity.

## Main results

* `Deformation.Artin.FormalObject.isEffective_of_lift_closedPoint`: a formal object whose
  closed-point level lifts to a chart formally smooth on objects is effective.
* `Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack`: every formal object of an
  algebraic stack is effective, and its complete local base belongs to the site.
* `Deformation.Artin.essSurj_approximationFunctor_algebraicStacks`: the approximation functor
  of an algebraic stack is essentially surjective.
* `Deformation.Artin.isEquivalence_approximationFunctor_algebraicStacks`: **Stacks 07X8**.

## References

* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u w

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.Fiber.mapOfComp CategoryTheory.Functor.Fiber.inducedFunctor
  CategoryTheory.instCategoryObj

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **A formal object is effective as soon as its closed-point level lifts to a formally smooth
chart.** Let `g : (Sch/V) ⟶ 𝒳` be formally smooth on objects. If the closed-point level of a
formal object `η` of `𝒳` lifts along `g`, then `η` is effective. -/
theorem FormalObject.isEffective_of_lift_closedPoint
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (V : BigFppfOver B S hS)
    (g : Stack.schemeFibredCategory B S hS V ⟶ 𝒳)
    (hfs : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS V) 𝒳 g)
    (η : FormalObject B S hS 𝒳.val.p)
    (ξ₀ : (Stack.schemeFibredCategory B S hS V).val.p.Fiber
      (truncationOver B S hS η.base η.contains 0))
    (hξ₀ : (Functor.Fiber.mapOfComp (Stack.schemeFibredCategory B S hS V).val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor g) (CatFiberedInGroupoids.homFunctor_comp_p g)
      (truncationOver B S hS η.base η.contains 0)).obj ξ₀ ≅ ⟨η.level 0, η.level_eq 0⟩) :
    FormalObject.IsEffective B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids η := by
  obtain ⟨ξU, -, -, ⟨eU⟩⟩ := exists_formalObject_lift B S hS (Stack.schemeFibredCategory B S hS V)
    𝒳 g hfs η ξ₀ hξ₀
  obtain ⟨xU, hxU, ⟨RU⟩⟩ := FormalObject.exists_realization_overForget V ξU ξU.contains_spec_base
  exact Functor.essImage.ofIso eU (isEffective_of_realization 𝒳.isFiberedInGroupoids (RU.map g))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Every formal object of an algebraic stack is effective** (the essential surjectivity half of
Stacks 07X8), and its complete local base belongs to the site. -/
theorem FormalObject.isEffective_of_isAlgebraicStack (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (ξ : FormalObject B S hS 𝒳.val.val.p) :
    FormalObject.IsEffective B S hS 𝒳.val.val.p 𝒳.val.property ξ ∧
      B.Contains (Spec (.of ξ.base.R)) := by
  classical
  have hA := ξ.contains_spec_base
  refine ⟨?_, hA⟩
  have hp : 𝒳.val.val.p.IsFiberedInGroupoids := 𝒳.val.property
  let : 𝒳.val.val.p.IsFibered := hp.isFibered
  have hI : IsAlgebraicSpaceIsom 𝒳.val.val.p :=
    Stack.isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack B S hS 𝒳.val 𝒳.property
  obtain ⟨hfib, ⟨hst1, hstack⟩, hdiag, V, a, hrep, ha⟩ := 𝒳.property
  let g : Stack.schemeFibredCategory B S hS V ⟶ 𝒳.val := Bicategory.InducedBicategory.mkHom a
  have hsm : ∀ {X Y : AlgebraicSpaces B S hS} (m : X ⟶ Y), Space.IsSmooth B S hS m.hom →
      Space.FormallySmooth m.hom := fun {X Y} m hm => Space.formallySmooth_of_isSmooth' X.2 Y.2 hm
  have hfs : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS V) 𝒳.val g :=
    BigFppfOver.isFormallySmoothOnObjects_of_isRelativelyFormallySmooth B S hS g hrep
      (fun U y hy F hF hE => hsm _ (ha U y hy F hF hE).2)
  let R := ξ.base.R
  let k := ResidueField ξ.base.R
  have hR : IsNoetherianCompleteLocalRing ξ.base.R :=
    ⟨ξ.base.noetherian, inferInstance, ξ.base.complete⟩
  have hmpow : maximalIdeal ξ.base.R ^ (0 + 1) = maximalIdeal ξ.base.R := by simp
  let ε₀ : ξ.base.R ⧸ maximalIdeal ξ.base.R ^ (0 + 1) →+* k :=
    (Ideal.quotEquivOfEq hmpow).toRingHom
  let ε₀i : k →+* ξ.base.R ⧸ maximalIdeal ξ.base.R ^ (0 + 1) :=
    (Ideal.quotEquivOfEq hmpow).symm.toRingHom
  have hεε : ε₀i.comp ε₀ = RingHom.id _ :=
    RingHom.ext (Ideal.quotEquivOfEq hmpow).symm_apply_apply
  let U := 𝒳.val.val.p.obj (ξ.level 0)
  obtain ⟨T, m, hsmooth, hsurjm, z, φ, hφ⟩ :=
    Stack.exists_scheme_lift_of_representable_isSurjective_isSmooth B S hS g hrep ha U
      ⟨ξ.level 0, rfl⟩
  have hU : (BigFppfOver.toScheme B S hS).obj U =
      Spec (.of (ξ.base.R ⧸ maximalIdeal ξ.base.R ^ (0 + 1))) :=
    congrArg (BigFppfOver.toScheme B S hS).obj (ξ.level_eq 0)
  let X : Scheme.{u} := B.inclusion.obj T
  let gk : X ⟶ Spec (.of k) :=
    B.inclusion.map m ≫ eqToHom hU ≫ Spec.map (CommRingCat.ofHom ε₀i)
  have : IsIso (Spec.map (CommRingCat.ofHom ε₀i)) := by
    have : IsIso (CommRingCat.ofHom ε₀i) :=
      inferInstanceAs (IsIso (Ideal.quotEquivOfEq hmpow).symm.toCommRingCatIso.hom)
    infer_instance
  have : Smooth (B.inclusion.map m) := hsmooth
  have : Surjective (B.inclusion.map m) := hsurjm
  have : Smooth gk := by dsimp only [gk]; infer_instance
  have : Surjective gk := by dsimp only [gk]; infer_instance
  obtain ⟨t₀, -⟩ := gk.surjective (IsLocalRing.closedPoint k)
  have : Nonempty X := ⟨t₀⟩
  obtain ⟨t, -, hfin, hsep⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth gk).nonempty
  let algkl : Algebra k (X.residueField t) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ gk.appTop ≫ X.Γevaluation t).hom.toAlgebra
  let l := X.residueField t
  have : FiniteDimensional k l := hfin
  have : Algebra.IsSeparable k l := hsep
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k l)) = X.fromSpecResidueField t ≫ gk :=
    SpecMap_algebraMap_residueField gk t
  obtain ⟨R', _, _, _, _, _, _, hR', ⟨e⟩⟩ :=
    exists_finite_etale_isNoetherianCompleteLocalRing_residueField hR l
  let A' : FormalBase S := ξ.base.ofFinite R'
  let : Algebra ξ.base.R A'.R := ‹Algebra ξ.base.R R'›
  have : IsLocalHom (algebraMap ξ.base.R A'.R) :=
    inferInstanceAs (IsLocalHom (algebraMap ξ.base.R R'))
  have : Module.Finite ξ.base.R A'.R := inferInstanceAs (Module.Finite ξ.base.R R')
  have : Algebra.Etale ξ.base.R A'.R := inferInstanceAs (Algebra.Etale ξ.base.R R')
  have hA' : B.Contains (Spec (.of A'.R)) := ξ.base.contains_spec_ofFinite R' hA
  let c' : ∀ n, B.Contains (A'.truncation n) := truncationContains B S A' hA'
  let ξ' := ξ.baseChange hp A' (algebraMap ξ.base.R A'.R) rfl c'
  have hmpow' : maximalIdeal R' = maximalIdeal R' ^ (0 + 1) := by simp
  let e₁ : ResidueField R' →+* R' ⧸ maximalIdeal R' ^ (0 + 1) :=
    (Ideal.quotEquivOfEq hmpow').toRingHom
  let ε : l →+* R' ⧸ maximalIdeal R' ^ (0 + 1) := e₁.comp e.symm.toRingEquiv.toRingHom
  have hε : ∀ r : R, ε (algebraMap k l (algebraMap R k r)) =
      Ideal.Quotient.mk _ (algebraMap R R' r) := by
    intro r
    change e₁ (e.symm (algebraMap k l (algebraMap R k r))) = _
    rw [AlgEquiv.commutes]
    change e₁ (algebraMap k (ResidueField R') (residue R r)) = _
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    rfl
  have key : Spec.map (CommRingCat.ofHom ε) ≫ Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫
      Spec.map (CommRingCat.ofHom ε₀) =
      Spec.map (CommRingCat.ofHom (localQuotientMap (algebraMap ξ.base.R R') 0)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply Ideal.Quotient.ringHom_ext
    ext r
    change ε (algebraMap k l (ε₀ (Ideal.Quotient.mk _ r))) = _
    rw [show ε₀ (Ideal.Quotient.mk _ r) = algebraMap R k r from rfl, hε]
    rfl
  let jS : Spec (.of (R' ⧸ maximalIdeal R' ^ (0 + 1))) ⟶ X :=
    Spec.map (CommRingCat.ofHom ε) ≫ X.fromSpecResidueField t
  have hjS : jS ≫ B.inclusion.map m ≫ eqToHom hU =
      Spec.map (CommRingCat.ofHom (localQuotientMap (algebraMap ξ.base.R R') 0)) := by
    rw [← key]
    have hid : Spec.map (CommRingCat.ofHom ε₀i) ≫ Spec.map (CommRingCat.ofHom ε₀) =
        𝟙 (Spec (.of (ξ.base.R ⧸ maximalIdeal ξ.base.R ^ (0 + 1)))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hεε, CommRingCat.ofHom_id, Spec.map_id]
    have h1 : jS ≫ B.inclusion.map m ≫ eqToHom hU =
        jS ≫ B.inclusion.map m ≫ eqToHom hU ≫ (Spec.map (CommRingCat.ofHom ε₀i) ≫
            Spec.map (CommRingCat.ofHom ε₀)) := by
      rw [hid, Category.comp_id]
    rw [h1, hspec]
    simp only [jS, gk, Category.assoc]
  have hUhom : B.inclusion.map U.hom =
      eqToHom hU ≫ B.inclusion.map (truncationOver B S hS ξ.base ξ.contains 0).hom := by
    have hw := Over.w (eqToHom (ξ.level_eq 0))
    rw [Over.eqToHom_left] at hw
    have := congrArg (fun f => B.inclusion.map f) hw
    simp only [Functor.map_comp, eqToHom_map] at this
    exact this.symm
  have hjS' : jS ≫ B.inclusion.map (m ≫ U.hom) =
      B.inclusion.map (truncationOver B S hS A' c' 0).hom := by
    have e1 : B.inclusion.map (m ≫ U.hom) = B.inclusion.map m ≫ eqToHom hU ≫
        (adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) 0 ≫ ξ.base.toS) := by
      rw [Functor.map_comp, hUhom]; rfl
    have e2 : Spec.map (CommRingCat.ofHom (localQuotientMap (algebraMap ξ.base.R R') 0)) ≫
        adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) 0 ≫ ξ.base.toS =
        adicThickeningι R' (maximalIdeal R') 0 ≫
          Spec.map (CommRingCat.ofHom (algebraMap ξ.base.R R')) ≫ ξ.base.toS := by
      rw [adicThickeningι, adicThickeningι, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        localQuotientMap_comp_mk]
    calc jS ≫ B.inclusion.map (m ≫ U.hom)
        = (jS ≫ B.inclusion.map m ≫ eqToHom hU) ≫
            (adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) 0 ≫ ξ.base.toS) := by
          rw [e1]; simp only [Category.assoc]
      _ = _ := by rw [hjS]; exact e2
  let j' : truncationOver B S hS A' c' 0 ⟶ (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) :=
    Over.homMk (ObjectProperty.homMk (X := ⟨A'.truncation 0, c' 0⟩) (Y := T) jS) (by
      apply ObjectProperty.hom_ext; exact hjS')
  let Fg := CatFiberedInGroupoids.homFunctor g
  have hFg := CatFiberedInGroupoids.homFunctor_comp_p g
  have hz : z.left = (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) := by
    have h1 := Functor.congr_obj hFg z
    have := hφ
    exact h1.symm.trans (IsHomLift.domain_eq 𝒳.val.val.p
      (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ)
  let ξ₀o : Over V := Over.mk ((j' ≫ eqToHom hz.symm) ≫ z.hom)
  let ψ₀ : ξ₀o ⟶ z := Over.homMk (j' ≫ eqToHom hz.symm) rfl
  have hψ₀ : (Over.forget V).IsHomLift j' ψ₀ := by
    have h : (Over.forget V).IsHomLift (j' ≫ eqToHom hz.symm) ψ₀ :=
      IsHomLift.map (p := Over.forget V) ψ₀
    exact (IsHomLift.lift_comp_eqToHom_iff (p := Over.forget V) j' ψ₀ hz.symm).mp h
  have hFψ₀ : 𝒳.val.val.p.IsHomLift j' (Fg.map ψ₀) :=
    PresheafOfCategories.isHomLift_map_of_comp hFg j' ψ₀ hψ₀
  let π₀ := truncationOverMap (hS := hS) ξ.base A' (algebraMap ξ.base.R A'.R) rfl ξ.contains c' 0
  have hbase : (j' ≫ (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U)) ≫
      eqToHom (ξ.level_eq 0) = π₀ := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, Category.assoc]
    exact hjS
  have hφ₀ : 𝒳.val.val.p.IsHomLift π₀ (Fg.map ψ₀ ≫ φ) := by
    rw [← hbase, IsHomLift.lift_comp_eqToHom_iff]
    infer_instance
  let b₀ := ξ.baseChangeπ hp A' (algebraMap ξ.base.R A'.R) rfl c' 0
  have hbπ : 𝒳.val.val.p.IsHomLift π₀ b₀ :=
    ξ.isHomLift_baseChangeπ hp A' (algebraMap ξ.base.R A'.R) rfl c' 0
  let φ₁ : Fg.obj ξ₀o ⟶ ξ'.level 0 :=
    @Functor.IsFiberedInGroupoids.fill _ _ _ _ _ hp _ _ _ π₀ (𝟙 _) π₀ (by simp) _ _ _ b₀ hbπ
      (Fg.map ψ₀ ≫ φ) hφ₀
  have hφ₁ : 𝒳.val.val.p.IsHomLift (𝟙 (truncationOver B S hS A' c' 0)) φ₁ :=
    @Functor.IsFiberedInGroupoids.fill_isHomLift _ _ _ _ _ hp _ _ _ π₀ (𝟙 _) π₀ (by simp) _ _ _
      b₀ hbπ (Fg.map ψ₀ ≫ φ) hφ₀
  let ξ₀ : (Stack.schemeFibredCategory B S hS V).val.p.Fiber (truncationOver B S hS A' c' 0) :=
    ⟨ξ₀o, rfl⟩
  let φfib : (Functor.Fiber.mapOfComp (Stack.schemeFibredCategory B S hS V).val.p 𝒳.val.val.p Fg
      hFg (truncationOver B S hS A' c' 0)).obj ξ₀ ⟶ ⟨ξ'.level 0, ξ'.level_eq 0⟩ := ⟨φ₁, hφ₁⟩
  have hiso : IsIso φfib := (hp.fiber_isGroupoid (truncationOver B S hS A' c' 0)).all_isIso φfib
  have heff' : FormalObject.IsEffective B S hS 𝒳.val.val.p hp ξ' :=
    FormalObject.isEffective_of_lift_closedPoint 𝒳.val V g hfs ξ' ξ₀ (@asIso _ _ _ _ φfib hiso)
  exact FormalObject.isEffective_of_isEffective_baseChange hp hstack hI ξ hA A' rfl hA' heff'

/-- **Essential surjectivity of the approximation functor of an algebraic stack** (the essential
surjectivity half of Stacks 07X8). -/
theorem essSurj_approximationFunctor_algebraicStacks (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    (approximationFunctor B S hS 𝒳.val.val.p 𝒳.val.property).EssSurj :=
  ⟨fun ξ => (FormalObject.isEffective_of_isAlgebraicStack 𝒳 ξ).1⟩

/-- **Stacks 07X8.** Let `𝒳` be an algebraic stack over a scheme `S`. The functor (Stacks 07X6)
from objects of `𝒳` over spectra of Noetherian complete local `S`-algebras with residue field of
finite type over `S` (and morphisms inducing local homomorphisms) to formal objects of `𝒳`,
which restricts an object to the infinitesimal thickenings of the closed point, is an
equivalence: full and faithful (`Deformation.Artin.full_approximationFunctor_algebraicStacks`,
`Deformation.Artin.faithful_approximationFunctor_algebraicStacks`) and essentially surjective
(`Deformation.Artin.essSurj_approximationFunctor_algebraicStacks`). The scheme `S` is not
assumed locally Noetherian. -/
@[stacks 07X8]
theorem isEquivalence_approximationFunctor_algebraicStacks
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    (approximationFunctor B S hS 𝒳.val.val.p 𝒳.val.property).IsEquivalence where
  faithful := faithful_approximationFunctor_algebraicStacks 𝒳
  full := full_approximationFunctor_algebraicStacks 𝒳
  essSurj := essSurj_approximationFunctor_algebraicStacks 𝒳

end Deformation.Artin

end
