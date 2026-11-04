module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackEffectiveDescent

/-!
# Gluing a morphism into a stack from a chart point over a covering

Let `𝒳` be a stack in groupoids over the big fppf site and `(a, ι)` a chart over the affine
object `T'`. Let `f : N ⟶ N'` be a map of small algebras whose spectrum is an fppf covering, with
double overlap `N' ⊗_N N'`. If an object `xb` over `Spec N` and an object `x'` over `Z` receive
morphisms `c : ξ w ⟶ xb` and `ζ : ξ w ⟶ x'` from the object of one point `w` of `P` over
`Spec N'`, and one arrow over the double overlap intertwines both pairs of pullbacks, then `xb`
maps to `x'` over any `k : Spec N ⟶ Z` with `Spec f ≫ k` the base map of `ζ`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_hom_of_chart`). This is the comparison of
the descended object with the given one on the closed subscheme.

The double overlap of the reduction `C' ⧸ I C'` over `A' ⧸ I` is the reduction of `C' ⊗ C'`
(`AlgebraicGeometry.Stack.GroupoidLift.isPushout_red_nerve_one`).

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.isPushout_red_nerve_one`.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_hom_of_chart`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe w u

section Algebra

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
  (C' : Type u) [CommRing C'] [Algebra A' C'] (hC : Cardinal.mk C' < κ) (I : Ideal A')
  (hI : I ^ 2 = ⊥) (hA : Cardinal.mk A' < κ)

include hA in
/-- The reduction of a vertex of the double overlap is the base change of the vertex. -/
theorem isPushout_red_vertex (v : C' →ₐ[A'] cech A' C' 1) :
    IsPushout (CommRingCat.ofHom (v : C' →+* cech A' C' 1))
      (CommRingCat.ofHom ((thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom :
        C' →+* (red I (nerve (A' := A') hκ C' hC 0)).obj))
      (CommRingCat.ofHom ((thk I hI (nerve (A' := A') hκ C' hC 1)).q.hom.hom :
        cech A' C' 1 →+* (red I (nerve (A' := A') hκ C' hC 1)).obj))
      (CommRingCat.ofHom ((redMap I (N := nerve (A' := A') hκ C' hC 0)
        (N' := nerve (A' := A') hκ C' hC 1) v : (red I (nerve (A' := A') hκ C' hC 0)).obj →ₐ[A']
          (red I (nerve (A' := A') hκ C' hC 1)).obj) :
        (red I (nerve (A' := A') hκ C' hC 0)).obj →+*
          (red I (nerve (A' := A') hκ C' hC 1)).obj)) := by
  have t := isPushout_red hκ C' hC I hI hA
  have s := isPushout_red hκ (cech A' C' 1) (card_cech_lt A' C' hκ hC 1) I hI hA
  refine IsPushout.of_left (h₁₁ := CommRingCat.ofHom (algebraMap A' C'))
    (v₁₁ := CommRingCat.ofHom ((thk I hI (baseAlg hA)).q.hom.hom : A' →+* (red I (baseAlg hA)).obj))
    (h₂₁ := CommRingCat.ofHom ((baseThk hκ hC hI hA).bot.hom.hom :
      (red I (baseAlg hA)).obj →+* (red I (nerve (A' := A') hκ C' hC 0)).obj))
    (isPushout_congr s ?_ rfl rfl ?_) ?_ t
  · ext x
    exact (v.commutes x).symm
  · ext x
    exact congrArg (Ideal.Quotient.mk _) (v.commutes x).symm
  · ext x
    rfl

/-- **The double overlap of the reduction.** `(C' ⊗ C') ⧸ I` is the pushout of two copies of
`C' ⧸ I C'` over `A' ⧸ I`. -/
theorem isPushout_red_nerve_one :
    IsPushout (CommRingCat.ofHom ((baseThk hκ hC hI hA).bot.hom.hom :
        (red I (baseAlg hA)).obj →+* (red I (nerve (A' := A') hκ C' hC 0)).obj))
      (CommRingCat.ofHom ((baseThk hκ hC hI hA).bot.hom.hom :
        (red I (baseAlg hA)).obj →+* (red I (nerve (A' := A') hκ C' hC 0)).obj))
      (CommRingCat.ofHom ((redMap I (N := nerve (A' := A') hκ C' hC 0)
        (N' := nerve (A' := A') hκ C' hC 1) (v₀ A' C' 1) :
          (red I (nerve (A' := A') hκ C' hC 0)).obj →ₐ[A']
          (red I (nerve (A' := A') hκ C' hC 1)).obj) :
        (red I (nerve (A' := A') hκ C' hC 0)).obj →+* (red I (nerve (A' := A') hκ C' hC 1)).obj))
      (CommRingCat.ofHom ((redMap I (N := nerve (A' := A') hκ C' hC 0)
        (N' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1) :
          (red I (nerve (A' := A') hκ C' hC 0)).obj →ₐ[A']
          (red I (nerve (A' := A') hκ C' hC 1)).obj) :
        (red I (nerve (A' := A') hκ C' hC 0)).obj →+*
          (red I (nerve (A' := A') hκ C' hC 1)).obj)) := by
  have t := isPushout_red hκ C' hC I hI hA
  have s₁ := (CommRingCat.isPushout_tensorProduct A' C' C').flip
  have s₂ := isPushout_red_vertex hκ C' hC I hI hA (vₗ A' C' 1)
  have s := IsPushout.paste_vert (h₁₁ := CommRingCat.ofHom (algebraMap A' C'))
    (v₁₂ := CommRingCat.ofHom ((v₀ A' C' 1 : C' →ₐ[A'] cech A' C' 1) : C' →+* cech A' C' 1))
    (h₂₁ := CommRingCat.ofHom ((vₗ A' C' 1 : C' →ₐ[A'] cech A' C' 1) : C' →+* cech A' C' 1))
    (isPushout_congr s₁ rfl rfl rfl rfl) s₂
  refine IsPushout.of_top (isPushout_congr s rfl ?_ ?_ rfl) ?_ t
  · ext x
    rfl
  · ext x
    rfl
  · ext x
    exact congrArg (Ideal.Quotient.mk _)
      (((v₀ A' C' 1).commutes x).trans ((vₗ A' C' 1).commutes x).symm)

end Algebra

/-- A restriction from any morphism lying over the base map, in a category fibred in groupoids. -/
@[reducible] noncomputable def Functor.Restriction.ofHomLift {𝒞 : Type*} {𝒮 : Type*} [Category 𝒞]
    [Category 𝒮] (p : 𝒮 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {V U : 𝒞} (f : V ⟶ U) {x : 𝒮}
    (hx : p.obj x = U) {y : 𝒮} (hy : p.obj y = V) (φ : y ⟶ x) (hφ : p.IsHomLift f φ) :
    Functor.Restriction p f x hx where
  pt := y
  hpt := hy
  hom := φ
  isHomLift := by
    have := hφ
    infer_instance
  isCart := by
    have := hφ
    exact hp.isStronglyCartesian_homLift _ _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}

namespace StackChart

variable {N N' N₂ : SmallAlg (ringOf B S hS T') B.cutoff} (f : N ⟶ N') (i₁ i₂ : N' ⟶ N₂)

/-- **A morphism into a stack glued from a chart point.** Over an fppf covering `Spec N' ⟶ Spec N`
with double overlap `Spec N₂`, morphisms `c : ξ w ⟶ xb` over `Spec f` and `ζ : ξ w ⟶ x'` over
`Spec f ≫ k` whose pullbacks are intertwined by one arrow `ρ` give a morphism `xb ⟶ x'` over
`k`. -/
theorem exists_hom_of_chart (h𝒳 : 𝒳.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    (hpb : IsPullback (specOverMap i₁) (specOverMap i₂) (specOverMap f) (specOverMap f))
    (hcov : Sieve.ofArrows (fun _ : PUnit.{w + 1} ↦ specOver N') (fun _ ↦ specOverMap f) ∈
      BigFppfOver.topology B S hS (specOver N))
    {Z : BigFppfOver B S hS} (k : specOver N ⟶ Z) {xb x' : 𝒳.val.obj}
    (hxb : 𝒳.val.p.obj xb = specOver N) (hx' : 𝒳.val.p.obj x' = Z)
    (w : P.obj →ₐ[ringOf B S hS T'] N'.obj) (c : ξ a ι w ⟶ xb)
    (hc : 𝒳.val.p.IsHomLift (specOverMap f) c) (ζ : ξ a ι w ⟶ x')
    (hζ : 𝒳.val.p.IsHomLift (specOverMap f ≫ k) ζ)
    (ρ : ξ a ι (i₁.hom.hom.comp w) ⟶ ξ a ι (i₂.hom.hom.comp w))
    (hρ : 𝒳.val.p.IsHomLift (𝟙 (specOver N₂)) ρ)
    (hρc : ρ ≫ trans a ι i₂ w ≫ c = trans a ι i₁ w ≫ c)
    (hρζ : ρ ≫ trans a ι i₂ w ≫ ζ = trans a ι i₁ w ≫ ζ) :
    ∃ φ : xb ⟶ x', 𝒳.val.p.IsHomLift k φ ∧ c ≫ φ = ζ := by
  have hp := 𝒳.isFiberedInGroupoids
  let y := Functor.Restriction.ofIsFiberedInGroupoids 𝒳.val.p hp k x' hx'
  have hy : 𝒳.val.p.IsHomLift k y.hom := Functor.isHomLift_of_restriction _ y
  have : 𝒳.val.p.IsStronglyCartesian k y.hom := hp.isStronglyCartesian_homLift _ _
  have := hζ
  have := hρ
  let βy : ξ a ι w ⟶ y.pt := Functor.IsStronglyCartesian.map 𝒳.val.p k y.hom
    (g := specOverMap f) rfl ζ
  have hβl : 𝒳.val.p.IsHomLift (specOverMap f) βy :=
    Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have hβ : βy ≫ y.hom = ζ := Functor.IsStronglyCartesian.fac _ _ _ _ _
  have := hβl
  have := hc
  have h₁ : 𝒳.val.p.IsHomLift (specOverMap i₁ ≫ specOverMap f) (trans a ι i₁ w ≫ c) :=
    inferInstance
  have h₂ : 𝒳.val.p.IsHomLift (specOverMap i₁ ≫ specOverMap f) (trans a ι i₁ w ≫ βy) :=
    inferInstance
  have hρ₂ : 𝒳.val.p.IsHomLift (specOverMap i₂) (ρ ≫ trans a ι i₂ w) := inferInstance
  have hmy : (ρ ≫ trans a ι i₂ w) ≫ βy = trans a ι i₁ w ≫ βy := by
    have hl : 𝒳.val.p.IsHomLift (specOverMap i₁ ≫ specOverMap f) ((ρ ≫ trans a ι i₂ w) ≫ βy) := by
      rw [hpb.w]
      infer_instance
    refine Functor.IsStronglyCartesian.ext 𝒳.val.p k y.hom (specOverMap i₁ ≫ specOverMap f) ?_
    exact ((Category.assoc _ _ _).trans ((congrArg _ hβ).trans ((Category.assoc _ _ _).trans
      hρζ))).trans ((congrArg _ hβ).symm.trans (Category.assoc _ _ _).symm)
  have : 𝒳.val.p.IsHomLift (𝟙 (specOver N')) (𝟙 (ξ a ι w)) := IsHomLift.id (ξ_obj a ι w)
  have : 𝒳.val.p.IsHomLift (𝟙 (specOver N₂)) (𝟙 (ξ a ι (i₁.hom.hom.comp w))) :=
    IsHomLift.id (ξ_obj a ι _)
  have hiso := h𝒳.isom_isSheaf xb y.pt hxb y.hpt (fun _ : PUnit.{w + 1} ↦ specOver N')
    (fun _ ↦ specOverMap f) hcov (fun _ _ ↦ specOver N₂) (fun _ _ ↦ specOverMap i₁)
    (fun _ _ ↦ specOverMap i₂) (fun _ _ ↦ hpb)
    (fun _ ↦ Functor.Restriction.ofHomLift _ hp _ hxb (ξ_obj a ι w) c hc)
    (fun _ ↦ Functor.Restriction.ofHomLift _ hp _ y.hpt (ξ_obj a ι w) βy hβl)
    (fun _ _ ↦ Functor.Restriction.ofHomLift _ hp _ hxb (ξ_obj a ι _) _ h₁)
    (fun _ _ ↦ Functor.Restriction.ofHomLift _ hp _ y.hpt (ξ_obj a ι _) _ h₂)
  obtain ⟨g, ⟨hgf, -, hgc⟩, -⟩ := hiso (fun _ ↦ 𝟙 _)
    (fun _ ↦ fibreHom_of_isHomLift (W := specOver N') _ _ (𝟙 (ξ a ι w)))
    (fun _ ↦ inferInstance) (fun _ _ ↦ ⟨𝟙 _,
      fibreHom_of_isHomLift (W := specOver N₂) _ _ (𝟙 (ξ a ι (i₁.hom.hom.comp w))),
      Functor.isRestrictionOf_of_fac _ _ _ _ _ _ _ _ _ _ (trans a ι i₁ w)
        (trans_isHomLift a ι i₁ w) rfl (trans a ι i₁ w) (trans_isHomLift a ι i₁ w) rfl
        ((Category.id_comp _).trans (Category.comp_id _).symm),
      Functor.isRestrictionOf_of_fac _ _ _ _ _ _ _ _ _ _ (ρ ≫ trans a ι i₂ w) hρ₂
        ((Category.assoc _ _ _).trans hρc) (ρ ≫ trans a ι i₂ w) hρ₂ hmy
        ((Category.id_comp _).trans (Category.comp_id _).symm)⟩)
  have := Functor.isHomLift_id_of_fibreHom _ hgf
  refine ⟨g ≫ y.hom, inferInstance, ?_⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.hom) ((hgc PUnit.unit).trans
    (Category.id_comp _))).trans hβ)

end StackChart

end AlgebraicGeometry.Stack.GroupoidLift

end
