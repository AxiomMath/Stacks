module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackSrcSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackArrowFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SpaceLiftCover
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale

/-!
# A chart of a stack over a scheme

Let `f : 𝒳 ⟶ (Sch/Z)` be a 1-morphism from a category fibred in groupoids to the one of an
object `Z` of the big fppf site, and let `a : (Sch/U₀) ⟶ 𝒳` be a chart. The composite
`a ≫ f` is the 1-morphism induced by a morphism `h : U₀ ⟶ Z` of the site, its underlying
morphism. If the point `ι : Spec P ⟶ U₀` of a small `Γ(T')`-algebra `P` is compatible with a
structure map `τ : T' ⟶ Z`, i.e. `ι ≫ h = Spec P ⟶ T' ⟶ Z`, then

* all the objects `ξ u = a(ι ∘ Spec u)` have the same image in `Z`, so the hypothesis
  `AlgebraicGeometry.Stack.SameImage` of the arrow chart of Stacks 0DNZ holds
  (`AlgebraicGeometry.Stack.GroupoidLift.StackChart.sameImage_pairObj`);
* the source map of the groupoid of the chart is formally smooth as soon as `a` is formally
  smooth on objects and `ι` lifts those points of `U₀` across square-zero thickenings which are
  compatible with `τ`
  (`AlgebraicGeometry.Stack.GroupoidLift.stackGroupoid_srcFormallySmooth_of_over`), which is the
  case for `ι = Spec Γ(U₁) ≅ U₁ ⟶ U₀` with `U₁` affine and étale over `U₀`
  (`AlgebraicGeometry.Stack.GroupoidLift.exists_lift_sectionsHom_of_etale`).

A smooth 1-morphism of represented algebraic stacks has smooth underlying morphism of the site
(`AlgebraicGeometry.Stack.smooth_siteMap_of_isSmooth`).

## Main results

* `AlgebraicGeometry.Stack.smooth_siteMap_of_isSmooth`.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.sameImage_pairObj`.
* `AlgebraicGeometry.Stack.GroupoidLift.stackGroupoid_srcFormallySmooth_of_over`.
* `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_sectionsHom_of_etale`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack

universe u w

/-- **A smooth 1-morphism of represented algebraic stacks comes from a smooth morphism of
schemes.** Smoothness of `c` (Stacks 075U) is the existential smooth-diagram test of Stacks 06FM,
which for represented source and target is smoothness of the induced morphism of representing
algebraic spaces, i.e. of `yoneda.map` of the morphism of the site underlying `c`. -/
theorem smooth_siteMap_of_isSmooth (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V)
    (hc : AlgebraicStacks.IsSmooth B S hS c) :
    Smooth ((BigFppfOver.toScheme B S hS).map (siteMap B S hS c)) := by
  have h := (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (schemeStack.{u, w} B S hS U).property (schemeStack.{u, w} B S hS V).property
      (yoneda.obj U) (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (PresheafOfCategories.sliceElementsEquivalenceOver V) c.hom).1 hc
  rw [representingMap_eq_yoneda_map_siteMap] at h
  exact Space.smooth_of_isSmooth_yonedaMap B S hS _ h

namespace GroupoidLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}
  {Z : BigFppfOver B S hS} (f : 𝒳 ⟶ schemeFibredCategory B S hS Z) (τ : T' ⟶ Z)

namespace StackChart

/-- The image in `Z` of the object `ξ u` of a point compatible with `τ` is `Spec C ⟶ T' ⟶ Z`. -/
theorem relPair_ξ (hιZ : ι ≫ schemeMapOfFunctor B S hS (a ≫ f).hom = specOverToBase P ≫ τ)
    {C : SmallAlg (ringOf B S hS T') B.cutoff} (u : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    eqToHom ((relPair_left_eq f.hom.toFunctor f.hom.w (ξ a ι u)).trans (ξ_obj a ι u)).symm ≫
      (f.hom.toFunctor.obj (ξ a ι u)).hom = specOverToBase C ≫ τ :=
  (schemeMapOfFunctor_naturality B S hS (a ≫ f).hom (pt ι u)).trans (by
    change (specOverMap (SmallAlg.homMk u) ≫ ι) ≫ _ = _
    rw [Category.assoc, hιZ, ← Category.assoc, specOverMap_comp_toBase])

/-- **The two objects of the arrow chart have the same image in `Z`.** -/
theorem sameImage_pairObj
    (hιZ : ι ≫ schemeMapOfFunctor B S hS (a ≫ f).hom = specOverToBase P ≫ τ) :
    SameImage f.hom.toFunctor f.hom.w (pairObj₀ a ι) (pairObj₁ a ι) :=
  (relPair_ξ f τ hιZ (vtx₀ _)).trans (relPair_ξ f τ hιZ (vtx₁ _)).symm

end StackChart

open StackChart

/-- **The source map of the groupoid of a chart over `Z` is formally smooth** when the chart
`a : (Sch/U₀) ⟶ 𝒳` is formally smooth on objects and `ι : Spec P ⟶ U₀`, compatible with
`τ : T' ⟶ Z`, lifts across square-zero thickenings those points of `U₀` which are compatible
with `τ`. The points of `U₀` produced by the formal smoothness of `a` are compatible with `τ`
because the image in `Z` of an object of `𝒳` is preserved by morphisms over the identity. -/
theorem stackGroupoid_srcFormallySmooth_of_over
    (hιZ : ι ≫ schemeMapOfFunctor B S hS (a ≫ f).hom = specOverToBase P ≫ τ)
    (ha : IsFormallySmoothOnObjects B S hS (schemeFibredCategory B S hS U₀) 𝒳 a)
    (hι : ∀ {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
      (m' : specOver C' ⟶ U₀) (u : P.obj →ₐ[ringOf B S hS T'] C.obj),
      m' ≫ schemeMapOfFunctor B S hS (a ≫ f).hom = specOverToBase C' ≫ τ →
      specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u) ≫ ι →
      ∃ u' : P.obj →ₐ[ringOf B S hS T'] C'.obj, e.q.hom.hom.comp u' = u ∧
        specOverMap (SmallAlg.homMk u') ≫ ι = m') :
    (stackGroupoid (a := a) (ι := ι)).SrcFormallySmooth := by
  intro C' C e r ℓ hℓ
  obtain ⟨u₁, u₂, φ, hl⟩ := r
  change e.q.hom.hom.comp ℓ = u₁ at hℓ
  subst hℓ
  have hthk : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (specOverMap e.q)) :=
    Stacks.Smooth.isFirstOrderThickening_specMap _ e.surj e.sq
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 (specOver C)) φ
  have hφi : IsIso φ :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (𝟙 (specOver C)) φ
  have hψ : 𝒳.val.p.IsHomLift (specOverMap e.q) (CategoryTheory.inv φ ≫
      StackChart.trans a ι e.q ℓ) := inferInstance
  obtain ⟨x', hx', β, hβ, γ', hγ', hfac⟩ := ha.exists_lift_of_obj_eq (specOverMap e.q) inferInstance
    inferInstance hthk (x := pt ι u₂) rfl (ξ_obj a ι ℓ)
    (CategoryTheory.inv φ ≫ StackChart.trans a ι e.q ℓ)
  obtain ⟨L, ⟨⟨⟩⟩, m⟩ := x'
  change L = specOver C' at hx'
  subst hx'
  have fβ := IsHomLift.fac' (schemeFibredCategory B S hS U₀).val.p (specOverMap e.q) β
  change β.left = 𝟙 _ ≫ specOverMap e.q ≫ 𝟙 _ at fβ
  rw [Category.id_comp, Category.comp_id] at fβ
  have hm : specOverMap e.q ≫ m = specOverMap (SmallAlg.homMk u₂) ≫ ι := by
    rw [← fβ]
    exact Over.w β
  have hmZ : m ≫ schemeMapOfFunctor B S hS (a ≫ f).hom = specOverToBase C' ≫ τ :=
    (schemeMapOfFunctor_naturality B S hS (a ≫ f).hom (Over.mk m)).symm.trans
      ((relPair_hom_eq f.hom.toFunctor f.hom.w (𝟙 (specOver C')) γ'
        (BasedFunctor.w_obj a.hom (Over.mk m)) (ξ_obj a ι ℓ)).trans
        ((Category.id_comp _).trans (relPair_ξ f τ hιZ ℓ)))
  obtain ⟨u₂', hu₂', hm'⟩ := hι e m u₂ hmZ hm
  subst hu₂' hm'
  have hβeq : β = Over.homMk (specOverMap e.q) (specOverMap_comp_pt ι e.q u₂') :=
    Over.OverMorphism.ext fβ
  subst hβeq
  change StackChart.trans a ι e.q u₂' ≫ γ' = _ at hfac
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 (specOver C')) γ'
  have : IsIso γ' :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (𝟙 (specOver C')) γ'
  have hl' : 𝒳.val.p.IsHomLift (𝟙 (specOver C')) (CategoryTheory.inv γ') := inferInstance
  have key : φ ≫ StackChart.trans a ι e.q u₂' =
      StackChart.trans a ι e.q ℓ ≫ CategoryTheory.inv γ' := by
    refine (IsIso.eq_comp_inv γ').2 ?_
    rw [Category.assoc, hfac, IsIso.hom_inv_id_assoc]
  have hmap := Arr.map_eq_mk (a := a) (ι := ι) e.q ⟨ℓ, u₂', CategoryTheory.inv γ', hl'⟩ φ hl key
  exact ⟨⟨ℓ, u₂', CategoryTheory.inv γ', hl'⟩, hmap, rfl⟩

/-- **An affine étale chart lifts compatible points across square-zero thickenings.** Let
`s : U₁ ⟶ U₀` be étale with `U₁` affine, and give `Γ(U₁)` the `Γ(T')`-algebra structure of
`s ≫ h` for a morphism `h : U₀ ⟶ T'`. A point `m'` of `U₀` over `Spec C'` lying over `T'` along
`h` and restricting over `Spec C` to the point of `u : Γ(U₁) → C` is the point of a unique lift
`u' : Γ(U₁) → C'` of `u`: lift `m'` through `s` by formal étaleness (Stacks 04AL) and read the
lift as an algebra map, which is `Γ(T')`-linear because `m'` lies over `T'`. -/
theorem exists_lift_sectionsHom_of_etale {U₁ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U₁)] (s : U₁ ⟶ U₀)
    (hs : Etale ((BigFppfOver.toScheme B S hS).map s)) (h : U₀ ⟶ T')
    {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
    (m' : specOver C' ⟶ U₀) (u : (sectionsAlg U₁ (s ≫ h)).obj →ₐ[ringOf B S hS T'] C.obj)
    (hm'h : m' ≫ h = specOverToBase C')
    (hm' : specOverMap e.q ≫ m' =
      specOverMap (SmallAlg.homMk u) ≫ sectionsHom U₁ (s ≫ h) ≫ s) :
    ∃ u' : (sectionsAlg U₁ (s ≫ h)).obj →ₐ[ringOf B S hS T'] C'.obj, e.q.hom.hom.comp u' = u ∧
      specOverMap (SmallAlg.homMk u') ≫ sectionsHom U₁ (s ≫ h) ≫ s = m' := by
  have hfe : Space.FormallyEtale (yoneda.map s) := Space.formallyEtale_of_etale B S hS _
    ((Space.presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mpr hs)
  obtain ⟨g, ⟨hg₁, hg₂⟩, -⟩ := hfe (specOver C) (specOver C') inferInstance inferInstance
    (specOverMap e.q) (isSquareZeroClosedImmersion_specOverMap e.q e.surj e.sq)
    (specOverMap (SmallAlg.homMk u) ≫ sectionsHom U₁ (s ≫ h)) m'
    (by change (_ ≫ _) ≫ s = specOverMap e.q ≫ m'; rw [Category.assoc, hm'])
  change specOverMap e.q ≫ g = specOverMap (SmallAlg.homMk u) ≫ sectionsHom U₁ (s ≫ h) at hg₁
  change g ≫ s = m' at hg₂
  have hbase : (g ≫ inv (sectionsHom U₁ (s ≫ h))) ≫ specOverToBase (sectionsAlg U₁ (s ≫ h)) =
      specOverToBase C' := by
    rw [Category.assoc, ← sectionsHom_comp U₁ (s ≫ h), IsIso.inv_hom_id_assoc, ← hm'h, ← hg₂,
      Category.assoc]
  obtain ⟨k, hk⟩ := exists_specOverMap _ hbase
  have hk' : specOverMap k ≫ sectionsHom U₁ (s ≫ h) = g := by
    rw [hk, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨k.hom.hom, ?_, ?_⟩
  · have hkq : k ≫ e.q = SmallAlg.homMk u := by
      apply specOverMap_injective
      rw [specOverMap_comp, ← cancel_mono (sectionsHom U₁ (s ≫ h)), Category.assoc, hk', hg₁]
    exact congrArg (fun t ↦ t.hom.hom) hkq
  · change specOverMap k ≫ sectionsHom U₁ (s ≫ h) ≫ s = m'
    rw [← Category.assoc, hk', hg₂]

end GroupoidLift

end AlgebraicGeometry.Stack

end
