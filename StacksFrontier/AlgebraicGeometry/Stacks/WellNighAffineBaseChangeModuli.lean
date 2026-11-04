module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackModuliSpace

/-!
# The base change of the moduli morphism of a well-nigh affine stack is a moduli space

Let `𝒳` be a well-nigh affine algebraic stack with chart `x : U ⟶ 𝒳`, relation `s, t : R ⟶ U`
and moduli morphism `f : 𝒳 ⟶ M`, and let `a : T ⟶ M` be a morphism from an affine object of the
site. Let `U' = T ×_M U` and let `s', t' : R' ⟶ U'` be morphisms lying over `s, t` along some
`R' ⟶ R`, with `pr₁ ∘ s' = pr₁ ∘ t'`. If every morphism `U' ⟶ Z` to an affine scheme identifying
`s'` and `t'` factors uniquely through `pr₁ : U' ⟶ T`, then the base change `T ×_M 𝒳 ⟶ T` of `f`
is a categorical moduli space in the category of affine schemes
(`AlgebraicGeometry.Stack.WellNighAffineChart.isCategoricalModuliSpaceIn_baseChange`).

This is the step of the proof of Stacks 0DUP showing that `f` is a uniform categorical moduli
space: for flat `T ⟶ M` the hypothesis is the scheme-theoretic statement that `U' ⟶ T` is a
categorical quotient in affine schemes (Stacks 03BK and Stacks 01I1).

## Implementation notes

A 1-morphism `g : T ×_M 𝒳 ⟶ W` restricts along the base-changed chart `x'` to a morphism of
presheaves `U' ⟶ W`, which identifies `s'` and `t'` because `x' ∘ s'` and `x' ∘ t'` are joined by
a vertical morphism; it therefore factors through `T`, and the resulting `T ⟶ W` composed with
the projection agrees with `g` after restriction along `x'`, hence everywhere
(`AlgebraicGeometry.Stack.WellNighAffineChart.baseChart_ext`).

## References

* [Stacks Project, Tag 0DUP](https://stacks.math.columbia.edu/tag/0DUP)
* [Stacks Project, Tag 0DUG](https://stacks.math.columbia.edu/tag/0DUG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A 1-morphism from the stack of a scheme of the site to the category of elements of a
presheaf is the 1-morphism attached to a morphism of presheaves.** -/
theorem exists_eq_comp_sliceElementsComparison {U : BigFppfOver B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (θ : (schemeFibredCategory B S hS U).val ⥤ᵇ (fibredCategory B S hS W).val) :
    ∃ ψ : yoneda.obj U ⟶ W,
      θ = BasedFunctor.comp (sliceElementsComparison B S hS U) (associatedMap B S hS ψ).1.hom := by
  let θ' : (fibredCategory B S hS (yoneda.obj U)).val ⥤ᵇ (fibredCategory B S hS W).val :=
    BasedFunctor.comp ⟨(PresheafOfCategories.sliceElementsEquivalenceOver U).inv.functor,
      (PresheafOfCategories.sliceElementsEquivalenceOver U).inv.w⟩ θ
  refine ⟨PresheafOfCategories.natTransOfBasedFunctor θ'.toFunctor θ'.w, ?_⟩
  have : (fibredCategory B S hS W).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection W).IsFiberedInSets
  refine BasedCategory.BasedFunctor.ext' ?_
  refine Functor.IsFiberedInSets.eq_of_obj_eq _ _ _ _ θ.w
    (BasedFunctor.comp (sliceElementsComparison B S hS U)
      (associatedMap B S hS
        (PresheafOfCategories.natTransOfBasedFunctor θ'.toFunctor θ'.w)).1.hom).w
    (fun z => ?_)
  exact (obj_eq_mk_natTransOfBasedFunctor θ' ((sliceElementsComparison B S hS U).obj z)).trans
    (associatedMap_obj B S hS _ _).symm

/-- The value at an object `(V, v)` of the 1-morphism attached to a morphism of presheaves
`yoneda U ⟶ W`. -/
theorem comp_sliceElementsComparison_obj {U : BigFppfOver B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ψ : yoneda.obj U ⟶ W) (z : Over U) :
    (BasedFunctor.comp (sliceElementsComparison B S hS U) (associatedMap B S hS ψ).1.hom).obj z =
      ⟨z.left, Discrete.mk (ψ.app (op z.left) z.hom)⟩ :=
  associatedMap_obj B S hS ψ ((sliceElementsComparison B S hS U).obj z)

/-- If the 1-morphisms attached to `ψ₁, ψ₂ : yoneda U ⟶ W` agree at `(V, x)` and `(V, y)`, then
`ψ₁` at `x` equals `ψ₂` at `y`. -/
private theorem app_eq_of_comp_sliceElementsComparison_obj_eq {U : BigFppfOver B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ψ₁ ψ₂ : yoneda.obj U ⟶ W) {V : BigFppfOver B S hS}
    (x y : V ⟶ U)
    (h : (BasedFunctor.comp (sliceElementsComparison B S hS U) (associatedMap B S hS ψ₁).1.hom).obj
        (Over.mk x) =
      (BasedFunctor.comp (sliceElementsComparison B S hS U) (associatedMap B S hS ψ₂).1.hom).obj
        (Over.mk y)) : ψ₁.app (op V) x = ψ₂.app (op V) y := by
  rw [comp_sliceElementsComparison_obj, comp_sliceElementsComparison_obj] at h
  injection h with hb hf
  exact Discrete.mk.inj hf

/-- Two morphisms of presheaves out of a represented presheaf agree when their 1-morphisms agree
at the tautological object. -/
theorem eq_of_comp_sliceElementsComparison_obj_eq {U : BigFppfOver B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ψ₁ ψ₂ : yoneda.obj U ⟶ W)
    (h : (BasedFunctor.comp (sliceElementsComparison B S hS U) (associatedMap B S hS ψ₁).1.hom).obj
        (Over.mk (𝟙 U)) =
      (BasedFunctor.comp (sliceElementsComparison B S hS U) (associatedMap B S hS ψ₂).1.hom).obj
        (Over.mk (𝟙 U))) : ψ₁ = ψ₂ := by
  exact yonedaEquiv.injective (app_eq_of_comp_sliceElementsComparison_obj_eq _ _ _ _ h)

namespace WellNighAffineChart

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (K : WellNighAffineChart.{u, w} B S hS 𝒳)
  {T : BigFppfOver B S hS} {a₀ : T ⟶ K.moduliObject}
  {U' : BigFppfOver B S hS} {pr₁ : U' ⟶ T} {pr₂ : U' ⟶ K.U}
  {Y' : AlgebraicSpaces B S hS} {e : Y'.obj ≅ yoneda.obj T} {a : Y' ⟶ K.moduliSpace}
  (ha : e.inv ≫ a.hom = yoneda.map a₀) (hpb : IsPullback pr₂ pr₁ K.quotientMap a₀)

/-- The base-changed chart followed by the first projection is the first leg `U' ⟶ T ≅ Y'`. -/
theorem baseChart_comp_fst :
    BasedFunctor.comp (K.baseChart ha hpb.w).hom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).fst.hom = baseFst pr₁ e := rfl

include hpb in
/-- **A 1-morphism from `T ×_M 𝒳` to an algebraic space, restricted to `U'`, identifies `s'` and
`t'`.** -/
theorem yoneda_comp_eq_of_baseChart {W : AlgebraicSpaces B S hS} (ψ : yoneda.obj U' ⟶ W.obj)
    (g : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val ⥤ᵇ (fibredCategory B S hS W.obj).val)
    (hψ : BasedFunctor.comp (K.baseChart ha hpb.w).hom g =
      BasedFunctor.comp (sliceElementsComparison B S hS U') (associatedMap B S hS ψ).1.hom)
    {V' : BigFppfOver B S hS} (s' t' : V' ⟶ U') (ρ : V' ⟶ K.V)
    (hs : s' ≫ pr₂ = ρ ≫ K.s) (ht : t' ≫ pr₂ = ρ ≫ K.t) (hpr : s' ≫ pr₁ = t' ≫ pr₁) :
    yoneda.map s' ≫ ψ = yoneda.map t' ≫ ψ := by
  obtain ⟨φ, hφ⟩ := K.exists_vertical_baseChart ha hpb.w s' t' ρ hs ht hpr
  have hobj := obj_eq_of_isHomLift_id_fibredCategory g φ hφ
  have h₁ := congrArg (fun L : (schemeFibredCategory B S hS U').val ⥤ᵇ
    (fibredCategory B S hS W.obj).val => L.obj (Over.mk s')) hψ
  have h₂ := congrArg (fun L : (schemeFibredCategory B S hS U').val ⥤ᵇ
    (fibredCategory B S hS W.obj).val => L.obj (Over.mk t')) hψ
  have hv := app_eq_of_comp_sliceElementsComparison_obj_eq _ _ _ _ ((h₁.symm.trans hobj).trans h₂)
  apply yonedaEquiv.injective
  rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]

/-- The first leg followed by the 1-morphism attached to `h : Y' ⟶ W` is the 1-morphism attached to
the composite `U' ⟶ T ≅ Y' ⟶ W`. -/
theorem baseFst_comp_associatedMap {W : AlgebraicSpaces B S hS} (h : Y' ⟶ W) :
    BasedFunctor.comp (baseFst pr₁ e) (associatedMap B S hS h.hom).1.hom =
      BasedFunctor.comp (sliceElementsComparison B S hS U')
        (associatedMap B S hS (yoneda.map pr₁ ≫ e.inv ≫ h.hom)).1.hom := by
  rw [← Category.assoc, associatedMap_comp]
  rfl

include ha hpb in
/-- **The base change of `f : 𝒳 ⟶ M` along `T ⟶ M` is a categorical moduli space in the category of
affine schemes**, as soon as `U' ⟶ T` is a categorical quotient of `s', t' : R' ⇉ U'` in the
category of affine schemes. -/
theorem isCategoricalModuliSpaceIn_baseChange
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {V' : BigFppfOver B S hS} (s' t' : V' ⟶ U') (ρ : V' ⟶ K.V)
    (hs : s' ≫ pr₂ = ρ ≫ K.s) (ht : t' ≫ pr₂ = ρ ≫ K.t) (hpr : s' ≫ pr₁ = t' ≫ pr₁)
    (hmod : ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ ψ : U' ⟶ Z, s' ≫ ψ = t' ≫ ψ → ∃! h : T ⟶ Z, pr₁ ≫ h = ψ) :
    IsCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj) Y'
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).fst := by
  refine ⟨⟨T, hT, ⟨e⟩⟩, fun W hW g => ?_⟩
  obtain ⟨Z, hZ, ⟨eW⟩⟩ := hW
  obtain ⟨ψ, hψ⟩ := exists_eq_comp_sliceElementsComparison
    (BasedFunctor.comp (K.baseChart ha hpb.w).hom g.hom)
  have hinvψ := K.yoneda_comp_eq_of_baseChart ha hpb ψ g.hom hψ s' t' ρ hs ht hpr
  let ψ₀ : U' ⟶ Z := yoneda.preimage (ψ ≫ eW.hom)
  have hψ₀ : yoneda.map ψ₀ = ψ ≫ eW.hom := Functor.map_preimage _ _
  have hinv : s' ≫ ψ₀ = t' ≫ ψ₀ := yoneda.map_injective (by
    rw [yoneda.map_comp, yoneda.map_comp, hψ₀, ← Category.assoc, hinvψ, Category.assoc])
  obtain ⟨h₀, hh₀, hu⟩ := hmod Z hZ ψ₀ hinv
  let h : Y' ⟶ W := ObjectProperty.homMk (e.hom ≫ yoneda.map h₀ ≫ eW.inv)
  have hψh : yoneda.map pr₁ ≫ e.inv ≫ h.hom = ψ := by
    show yoneda.map pr₁ ≫ e.inv ≫ e.hom ≫ yoneda.map h₀ ≫ eW.inv = ψ
    rw [Iso.inv_hom_id_assoc, ← Category.assoc, ← yoneda.map_comp, hh₀, hψ₀, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have key : BasedFunctor.comp (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).fst.hom
      (associatedMap B S hS h.hom).1.hom = g.hom := by
    refine K.baseChart_ext ha hpb _ _ (Eq.trans ?_ hψ.symm)
    show BasedFunctor.comp (BasedFunctor.comp (K.baseChart ha hpb.w).hom
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (associatedMap B S hS a.hom).1 K.moduliMap.hom).fst.hom)
      (associatedMap B S hS h.hom).1.hom = _
    rw [K.baseChart_comp_fst ha hpb, baseFst_comp_associatedMap, hψh]
  refine ⟨h, ⟨eqToIso (Bicategory.InducedBicategory.hom_ext key)⟩, ?_⟩
  rintro h' ⟨i⟩
  have key' : BasedFunctor.comp (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).fst.hom
      (associatedMap B S hS h'.hom).1.hom = g.hom :=
    basedFunctor_eq_of_basedNatTrans i.hom.hom
  have hψh' : yoneda.map pr₁ ≫ e.inv ≫ h'.hom = ψ := by
    refine eq_of_comp_sliceElementsComparison_obj_eq _ _ ?_
    rw [← baseFst_comp_associatedMap, ← K.baseChart_comp_fst ha hpb, ← hψ]
    exact congrArg (fun L : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 K.moduliMap.hom).pt.val ⥤ᵇ
          (fibredCategory B S hS W.obj).val =>
      L.obj ((K.baseChart ha hpb.w).hom.obj (Over.mk (𝟙 U')))) key'
  let h'₀ : T ⟶ Z := yoneda.preimage (e.inv ≫ h'.hom ≫ eW.hom)
  have hh'₀ : yoneda.map h'₀ = e.inv ≫ h'.hom ≫ eW.hom := Functor.map_preimage _ _
  have hfac : pr₁ ≫ h'₀ = ψ₀ := yoneda.map_injective (by
    rw [yoneda.map_comp, hh'₀, hψ₀, ← hψh']
    simp only [Category.assoc])
  apply ObjectProperty.hom_ext
  show h'.hom = e.hom ≫ yoneda.map h₀ ≫ eW.inv
  rw [← hu h'₀ hfac, hh'₀]
  simp

end WellNighAffineChart

end AlgebraicGeometry.Stack

end
