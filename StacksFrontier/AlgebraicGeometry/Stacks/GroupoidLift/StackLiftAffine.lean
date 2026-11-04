module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackLiftCore
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackChartOver

/-!
# The lifting step for a stack over an affine base, from an affine étale chart

Let `f : 𝒳 ⟶ (Sch/T')` be a 1-morphism from an algebraic stack to an affine object `T'` of the
big fppf site, locally of finite presentation in the universal smooth-diagram sense, and let
`a : (Sch/U₀) ⟶ 𝒳` be a chart, formally smooth on objects, whose underlying morphism
`h : U₀ ⟶ T'` of the site (that of `a ≫ f`) is smooth. Let `i : T ⟶ T'` be a square-zero closed
immersion of affines and `x` an object of `𝒳` over `T` with image `i` in `T'`. Suppose that over
an affine `c` surjective and étale over `T`, `x` receives a morphism from `a(s ∘ m)` for an affine
`U₁` étale over `U₀` by `s` and `m : c ⟶ U₁`. Then `x` extends: there is a morphism `x ⟶ z` over
`i` to an object `z` over `T'` with image `𝟙 T'`
(`AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_affine_chart`).

The chart is `P = Γ(U₁)`, an `A'`-algebra through `s ≫ h`, smooth, with point
`ι : Spec P ≅ U₁ ⟶ U₀`; it is compatible with `𝟙 T'`, so its groupoid is formally smooth on sources
(`AlgebraicGeometry.Stack.GroupoidLift.stackGroupoid_srcFormallySmooth_of_over`) and its two
objects over `Spec (P ⊗ P)` have the same image in `T'`, so the arrows have a formally étale
finitely presented chart after a surjective étale refinement `C₁` of `Γ(c)`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_arrowChart_finitePresentation`). The cover
`Spec C₁ ⟶ T` lifts to a faithfully flat étale `A'`-algebra `C'` with `C' ⧸ I C' ≅ Γ(Spec C₁)`
(Stacks 04D1, `AlgebraicGeometry.Stack.GroupoidLift.exists_etale_lift_of_etale`), on which `x` is
the object of a chart point; the stack lifting step
`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_lift_of_chartPoint` produces the extension
over `Spec A' ≅ T'`, whose image in `T'` is the identity because `Spec C' ⟶ Spec A'` is an
epimorphism.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_affine_chart`: an object of `𝒳` over `T`
  extends along `i` to an object over `T'` with image `𝟙 T'`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe w u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (f : 𝒳 ⟶ schemeFibredCategory B S hS T')

open StackChart

/-- The image in `T'` of an object of `𝒳` over `W`, a morphism `W ⟶ T'`. -/
abbrev imageOf {W : BigFppfOver B S hS} (y : 𝒳.val.obj) (hy : 𝒳.val.p.obj y = W) : W ⟶ T' :=
  eqToHom ((relPair_left_eq f.hom.toFunctor f.hom.w y).trans hy).symm ≫
    (f.hom.toFunctor.obj y).hom

/-- The projection of `𝒳` to the big fppf site is a fibered category. -/
local instance : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered

/-- A morphism of `Spec` of a faithfully flat algebra is an epimorphism of the site. -/
theorem epi_specOverMap_baseMap (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) {C' : Type u}
    [CommRing C'] [Algebra (ringOf B S hS T') C'] (hC : Cardinal.mk C' < B.cutoff)
    [Module.FaithfullyFlat (ringOf B S hS T') C'] :
    Epi (specOverMap (baseMap B.aleph0_lt_cutoff (C' := C') hC hA)) := by
  have hFF := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C'))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  obtain ⟨_, _⟩ := hFF
  exact (BigFppfOver.toScheme B S hS).epi_of_epi_map
    (Flat.epi_of_flat_of_surjective
      (Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C'))))

variable {f}

/-- **The image in `T'` of the extension is the identity.** -/
theorem imageOf_eq_id {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
    {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}
    (hιZ : ι ≫ schemeMapOfFunctor B S hS (a ≫ f).hom = specOverToBase P ≫ 𝟙 T')
    (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) {C' : Type u}
    [CommRing C'] [Algebra (ringOf B S hS T') C'] (hC : Cardinal.mk C' < B.cutoff)
    [Module.FaithfullyFlat (ringOf B S hS T') C']
    (u : P.obj →ₐ[ringOf B S hS T'] (nerve (A' := ringOf B S hS T') B.aleph0_lt_cutoff C' hC 0).obj)
    {x' : 𝒳.val.obj} (hx' : 𝒳.val.p.obj x' = specOver (baseAlg (κ := B.cutoff) hA))
    (ζ : ξ a ι u ⟶ x')
    (hζ : 𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ)
    {z : 𝒳.val.obj} (hz : 𝒳.val.p.obj z = T')
    {k : T' ⟶ specOver (baseAlg (κ := B.cutoff) hA)} (hk : k ≫ specOverToBase (baseAlg hA) = 𝟙 T')
    (d : z ⟶ x') (hd : 𝒳.val.p.IsHomLift k d) :
    imageOf f z hz = 𝟙 T' := by
  have _ := epi_specOverMap_baseMap (T' := T') hA hC
  have h1 := relPair_hom_eq f.hom.toFunctor f.hom.w k d hz hx'
  have h2 := relPair_hom_eq f.hom.toFunctor f.hom.w
    (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ (ξ_obj a ι u) hx'
  have h3 := relPair_ξ f (𝟙 T') hιZ u
  have hx'im : imageOf f x' hx' = specOverToBase (T' := T') (baseAlg hA) := by
    rw [← cancel_epi (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)), specOverMap_comp_toBase]
    exact h2.symm.trans (h3.trans (Category.comp_id _))
  change imageOf f z hz = _ ≫ imageOf f x' hx' at h1
  rw [h1, hx'im, hk]

/-- **The lifting step from a chart point, transported to `T'`.** -/
theorem exists_lift_of_chartPoint_transport
    (hst : 𝒳.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
    {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}
    (hιZ : ι ≫ schemeMapOfFunctor B S hS (a ≫ f).hom = specOverToBase P ≫ 𝟙 T')
    (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) {C' : Type u}
    [CommRing C'] [Algebra (ringOf B S hS T') C'] (hC : Cardinal.mk C' < B.cutoff)
    [Module.FaithfullyFlat (ringOf B S hS T') C'] [Algebra.FinitePresentation (ringOf B S hS T') C']
    [Algebra.FormallySmooth (ringOf B S hS T') P.obj]
    [Module.FinitePresentation P.obj Ω[P.obj⁄ringOf B S hS T']]
    (hG : (stackGroupoid a ι).SrcFormallySmooth)
    {Q : Type u} [CommRing Q] [Algebra (ringOf B S hS T') Q]
    [Module.FinitePresentation Q Ω[Q⁄ringOf B S hS T']]
    (b : Chart (stackArr a ι) Q) (hb : b.IsFormallyEtale) (sV tV : P.obj →ₐ[ringOf B S hS T'] Q)
    (hsV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).src = v.comp sV)
    (htV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).tgt = v.comp tV)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (i : T ⟶ T')
    (hI : kerIdeal i ^ 2 = ⊥) (φT : specOver (red (kerIdeal i) (baseAlg (κ := B.cutoff) hA)) ⟶ T)
    [IsIso φT] (hφT : φT ≫ i = specOverToBase (red (kerIdeal i) (baseAlg (κ := B.cutoff) hA)))
    {x xb : 𝒳.val.obj} (c₀ : xb ⟶ x) [𝒳.val.p.IsHomLift φT c₀]
    (hxb : 𝒳.val.p.obj xb = specOver (red (kerIdeal i) (baseAlg (κ := B.cutoff) hA)))
    (ubar : P.obj →ₐ[ringOf B S hS T'] (red (kerIdeal i) (descNerve T' hC 0)).obj)
    (cm : ξ a ι ubar ⟶ xb)
    (hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) cm)
    (εbar : Q →ₐ[ringOf B S hS T'] (red (kerIdeal i) (descNerve T' hC 0)).obj)
    (hε : b.app _ εbar = Arr.idt ubar) :
    ∃ (z : 𝒳.val.obj) (hz : 𝒳.val.p.obj z = T') (φ : x ⟶ z),
      𝒳.val.p.IsHomLift i φ ∧ imageOf f z hz = 𝟙 T' := by
  have : 𝒳.val.p.IsStronglyCartesian φT c₀ :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift φT c₀
  obtain ⟨u, x', ζ, φ, hζ, hφ⟩ := exists_lift_of_chartPoint hA hC (kerIdeal i) hI hst hG b hb sV tV
    hsV htV hxb ubar cm hc εbar hε
  have hx' : 𝒳.val.p.obj x' = specOver (baseAlg (κ := B.cutoff) hA) :=
    @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _
      (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ hζ
  have := isIso_specOverToBase_baseAlg (T' := T') hA
  set toB := specOverToBase (T' := T') (baseAlg (κ := B.cutoff) hA)
  set z := Functor.IsPreFibered.pullbackObj hx' (inv toB)
  have hz : 𝒳.val.p.obj z = T' := Functor.IsPreFibered.pullbackObj_proj hx' (inv toB)
  set d : z ⟶ x' := Functor.IsPreFibered.pullbackMap hx' (inv toB)
  have hd : 𝒳.val.p.IsHomLift (inv toB) d := inferInstance
  have : IsIso c₀ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p φT c₀
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (inv toB) d
  have : IsIso d := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (inv toB) d
  have := hφ
  have hφ' : 𝒳.val.p.IsHomLift
      (inv φT ≫ specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q ≫ inv (inv toB))
      (inv c₀ ≫ φ ≫ inv d) := inferInstance
  have hi' : inv φT ≫ specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q ≫
      inv (inv toB) = i := by
    rw [IsIso.inv_inv, specOverMap_comp_toBase, ← hφT, IsIso.inv_hom_id_assoc]
  exact ⟨z, hz, inv c₀ ≫ φ ≫ inv d, isHomLift_of_eq hi' hφ',
    imageOf_eq_id hιZ hA hC u hx' ζ hζ hz (IsIso.inv_hom_id _) d hd⟩

/-- **The lifting step for a stack over an affine base, from an affine étale chart.** -/
theorem exists_lift_of_affine_chart (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    {U₀ U₁ c T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U₁)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
    (ha : IsFormallySmoothOnObjects B S hS (schemeFibredCategory B S hS U₀) 𝒳 a)
    (hsm : Smooth ((BigFppfOver.toScheme B S hS).map (schemeMapOfFunctor B S hS (a ≫ f).hom)))
    (s : U₁ ⟶ U₀) (hs : Etale ((BigFppfOver.toScheme B S hS).map s))
    (i : T ⟶ T') (hi : Space.IsSquareZeroClosedImmersion B S hS i)
    (g : c ⟶ T) (hgs : Surjective ((BigFppfOver.toScheme B S hS).map g))
    (hge : Etale ((BigFppfOver.toScheme B S hS).map g)) (m₁ : c ⟶ U₁)
    (hm : m₁ ≫ s ≫ schemeMapOfFunctor B S hS (a ≫ f).hom = g ≫ i)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = T)
    (θ : (CatFiberedInGroupoids.homFunctor a).obj (Over.mk (m₁ ≫ s)) ⟶ x)
    (hθ : 𝒳.val.p.IsHomLift g θ) :
    ∃ (z : 𝒳.val.obj) (hz : 𝒳.val.p.obj z = T') (φ : x ⟶ z),
      𝒳.val.p.IsHomLift i φ ∧ imageOf f z hz = 𝟙 T' := by
  classical
  obtain ⟨_, ⟨_, hst⟩, _⟩ := id h𝒳
  set h := schemeMapOfFunctor B S hS (a ≫ f).hom
  set A' := ringOf B S hS T'
  have hA : Cardinal.mk A' < B.cutoff := card_sections_lt T'
  set I := kerIdeal i
  have hthick : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i) := ⟨hi.1, hi.2⟩
  have hsurjI : Function.Surjective (algebraMap A' (sectionsAlg T i).obj) :=
    Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hthick
  have hI : I ^ 2 = ⊥ := Stacks.Smooth.ker_appTop_sq_eq_bot hthick
  set P := sectionsAlg U₁ (s ≫ h)
  set ι : specOver P ⟶ U₀ := sectionsHom U₁ (s ≫ h) ≫ s with hι
  have hιZ : ι ≫ h = specOverToBase P ≫ 𝟙 T' := by
    rw [hι, Category.assoc, sectionsHom_comp, Category.comp_id]
  have hPsm : RingHom.Smooth ((BigFppfOver.toScheme B S hS).map (s ≫ h)).appTop.hom := by
    have : Smooth ((BigFppfOver.toScheme B S hS).map (s ≫ h)) := by
      rw [Functor.map_comp]
      infer_instance
    exact HasRingHomProperty.appTop (P := @Smooth) _ this
  have : Algebra.Smooth A' P.obj := hPsm
  have hG : (stackGroupoid (a := a) (ι := ι)).SrcFormallySmooth :=
    stackGroupoid_srcFormallySmooth_of_over f (𝟙 T') hιZ ha
    (fun {_ _} e m' u hmZ hm' => exists_lift_sectionsHom_of_etale s hs h e m' u
      (hmZ.trans (Category.comp_id _)) hm')
  have hα := sameImage_pairObj f (𝟙 T') hιZ
  have hmj : m₁ ≫ s ≫ h = g ≫ i := hm
  obtain ⟨C₁, f₁, hf₁s, hf₁e, Q, _, _, b, hb, sV, tV, hsV, htV, ε, hε⟩ :=
    exists_arrowChart_finitePresentation a ι h𝒳 f hf hα (sectionsMap m₁ hmj).hom.hom
  set g₂ : specOver C₁ ⟶ T := specOverMap f₁ ≫ sectionsHom c (g ≫ i) ≫ g with hg₂
  have hg₂s : Surjective ((BigFppfOver.toScheme B S hS).map g₂) := by
    rw [hg₂, Functor.map_comp, Functor.map_comp]
    infer_instance
  have hg₂e : Etale ((BigFppfOver.toScheme B S hS).map g₂) := by
    rw [hg₂, Functor.map_comp, Functor.map_comp]
    infer_instance
  obtain ⟨C', _, _, hC, _, _, ⟨γ⟩⟩ := exists_etale_lift_of_etale i hi g₂ hg₂s hg₂e
  have hg₂i : g₂ ≫ i = specOverToBase C₁ := by
    rw [hg₂, Category.assoc, Category.assoc, sectionsHom_comp, specOverMap_comp_toBase]
  obtain ⟨κ, hκ⟩ := exists_specOverMap (sectionsHom (specOver C₁) (g₂ ≫ i)) (by
    rw [← hg₂i]
    exact sectionsHom_comp _ _)
  set N := nerve (A' := A') B.aleph0_lt_cutoff C' hC 0
  set γ₁ : C₁ ⟶ red I N := κ ≫ γ
  set w := (sectionsMap m₁ hmj).hom.hom
  set ubar : P.obj →ₐ[A'] (red I N).obj := γ₁.hom.hom.comp (f₁.hom.hom.comp w)
  set εbar : Q.obj →ₐ[A'] (red I N).obj := γ₁.hom.hom.comp ε
  have hε' : b.app _ εbar = Arr.idt ubar :=
    (b.natural γ₁ ε).symm.trans ((congrArg _ hε).trans (Arr.map_idt _ _))
  set φT := redToBase i hsurjI hA
  set xb := Functor.IsPreFibered.pullbackObj hx φT
  have hxb : 𝒳.val.p.obj xb = specOver (red I (baseAlg (κ := B.cutoff) hA)) :=
    Functor.IsPreFibered.pullbackObj_proj hx φT
  set c₀ : xb ⟶ x := Functor.IsPreFibered.pullbackMap hx φT
  have : 𝒳.val.p.IsStronglyCartesian φT c₀ :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift φT c₀
  have hν : specOverMap (SmallAlg.homMk ubar) ≫ ι =
      (specOverMap γ₁ ≫ specOverMap f₁ ≫ sectionsHom c (g ≫ i)) ≫ m₁ ≫ s := by
    rw [show SmallAlg.homMk ubar = sectionsMap m₁ hmj ≫ f₁ ≫ γ₁ from rfl, specOverMap_comp,
      specOverMap_comp, hι]
    simp only [Category.assoc]
    rw [reassoc_of% (specOverMap_sectionsMap m₁ hmj)]
  let e₁ : pt ι ubar ⟶ (Over.mk (m₁ ≫ s) : Over U₀) :=
    Over.homMk (specOverMap γ₁ ≫ specOverMap f₁ ≫ sectionsHom c (g ≫ i)) hν.symm
  have he₁ : (schemeFibredCategory B S hS U₀).val.p.IsHomLift
      (specOverMap γ₁ ≫ specOverMap f₁ ≫ sectionsHom c (g ≫ i)) e₁ :=
    IsHomLift.map (Over.forget U₀) e₁
  have he₁' : 𝒳.val.p.IsHomLift (specOverMap γ₁ ≫ specOverMap f₁ ≫ sectionsHom c (g ≫ i))
      ((CatFiberedInGroupoids.homFunctor a).map e₁) :=
    BasedFunctor.preserves_isHomLift a.hom _ e₁
  have hmono : Mono i := by
    have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) :=
      hi.1
    exact (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have hkey : (specOverMap γ₁ ≫ specOverMap f₁ ≫ sectionsHom c (g ≫ i)) ≫ g =
      specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT := by
    rw [← cancel_mono i]
    simp only [Category.assoc]
    rw [sectionsHom_comp, specOverMap_comp_toBase, specOverMap_comp_toBase, redToBase_comp,
      specOverMap_comp_toBase]
  have := hθ
  let cm : ξ a ι ubar ⟶ xb := Functor.IsStronglyCartesian.map 𝒳.val.p φT c₀ hkey
    ((CatFiberedInGroupoids.homFunctor a).map e₁ ≫ θ)
  have hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) cm :=
    inferInstance
  exact exists_lift_of_chartPoint_transport hst hιZ hA hC hG b hb sV tV hsV htV i hI φT
    (redToBase_comp i hsurjI hA) c₀ hxb ubar cm hc εbar hε'

end AlgebraicGeometry.Stack.GroupoidLift

end
