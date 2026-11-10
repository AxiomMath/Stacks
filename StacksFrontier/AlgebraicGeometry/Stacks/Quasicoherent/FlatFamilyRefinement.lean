module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectFibreLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatAffineObjectDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictionObjects

/-!
# Refining a flat object by the small étale sites of a flat jointly surjective family

Let `𝒳` be an algebraic stack and `x_i : U_i → 𝒳`, `i ∈ I`, objects of `𝒳` which are flat and
jointly surjective.  This file proves the covering statement in the proof of Stacks 0GQF: every
flat object `w` of `𝒳` over an affine scheme `W` admits a family of morphisms `v_k ⟶ w` from
objects over affine schemes, flat and jointly surjective on underlying schemes, each `v_k` having
a morphism, flat on underlying schemes, to the image of an affine open of some `U_i` under the
functor `U_{i,étale} ⥤ 𝒳`.  In the source this is the étale covering `{W_{i,j} ⟶ V ×_𝒳 U_i}` by
schemes, whose projections to `V` and to `U_i` are flat.

## Main results

* `AlgebraicGeometry.Stack.exists_flat_refinement_smallEtaleOpen`: the refinement.

## References

* [Stacks Project, Tag 0GQF](https://stacks.math.columbia.edu/tag/0GQF)
-/

@[expose] public section

open CategoryTheory Opposite

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u w v

namespace AlgebraicGeometry

/-- A morphism of schemes whose composite with an open immersion is flat is flat. -/
theorem flat_of_comp_isOpenImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion g] (hfg : Flat (f ≫ g)) : Flat f := by
  have h1 : (f ≫ g) ⁻¹ᵁ g.opensRange = ⊤ := by simp
  have e : f = X.topIso.inv ≫ (X.isoOfEq h1).inv ≫ (f ≫ g) ∣_ g.opensRange ≫
      (IsOpenImmersion.isoOfRangeEq g.opensRange.ι g (by simp)).hom := by
    rw [← cancel_mono g]
    simp only [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, morphismRestrict_ι,
      Scheme.isoOfEq_inv_ι_assoc, Scheme.toIso_inv_ι_assoc]
  rw [e]
  infer_instance

end AlgebraicGeometry

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

section HomLift

variable {B S hS} {𝒴 : Type v} [Category.{w} 𝒴] (p : 𝒴 ⥤ BigFppfOver B S hS)

/-- A morphism lying over `f : U ⟶ p b` has the same image on underlying schemes as `f`. -/
theorem range_toScheme_map_map_of_isHomLift {a b : 𝒴} {U : BigFppfOver B S hS}
    (f : U ⟶ p.obj b) (φ : a ⟶ b) (hφ : p.IsHomLift f φ) :
    Set.range ((BigFppfOver.toScheme B S hS).map (p.map φ)) =
      Set.range ((BigFppfOver.toScheme B S hS).map f) := by
  rw [IsHomLift.fac' p f φ, Functor.map_comp, Functor.map_comp, eqToHom_map,
    eqToHom_map, eqToHom_refl, Category.comp_id]
  ext t
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨(eqToHom (congrArg (BigFppfOver.toScheme B S hS).obj
        (IsHomLift.domain_eq p f φ)).symm) b, ?_⟩
    rw [Scheme.Hom.comp_apply]
    congr 1
    rw [← Scheme.Hom.comp_apply, eqToHom_trans, eqToHom_refl]
    rfl

end HomLift

section Refinement

variable {I : Type*} (x : I → 𝒳.val.val.obj) (hflat : ∀ i, flatObject B S hS 𝒳.val (x i))
  (hsurj : ∀ q : AlgebraicStacks.points B S hS 𝒳, ∃ i, q ∈ Set.range
    (AlgebraicStacks.pointsMap B S hS
      (fibreObjectStackMap B S hS 𝒳 (𝒳.val.val.p.obj (x i)) (Functor.Fiber.mk rfl))))

include hflat hsurj in
/-- **The refinement of Stacks 0GQF at one point.**  For a flat object `w` and a point `t` of
the scheme below it there are an object `v` over an affine scheme, a morphism `v ⟶ w` which is
flat on underlying schemes with `t` in its image, and a morphism, flat on underlying schemes,
from `v` to the image of an affine open of some `U_i` under `U_{i,étale} ⥤ 𝒳`. -/
theorem exists_flat_refinement_smallEtaleOpen_at_point {w : 𝒳.val.val.obj}
    (hw : flatObject B S hS 𝒳.val w)
    (t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj w)) :
    ∃ (v : 𝒳.val.val.obj) (a : v ⟶ w) (i : I)
      (W : ((𝒳.val.val.p.obj (x i)).left.1).affineOpens)
      (b : v ⟶ (smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (x i)).obj
        (smallEtaleOpen B E h S hS 𝒳.val.val.p (x i) W.1)),
      IsAffineOver B S hS (𝒳.val.val.p.obj v) ∧
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a)) ∧
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map b)) ∧
      t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a)) := by
  classical
  let J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf
  let _ := pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj w))
  let z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj w)) :=
    (pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj w)).symm t
  obtain ⟨i, hi⟩ := hsurj (AlgebraicStacks.pointsMap B S hS
    (fibreObjectStackMap B S hS 𝒳 (𝒳.val.val.p.obj w) (Functor.Fiber.mk rfl)) z)
  obtain ⟨T, m, hm, hmt, a', ha', α, hα⟩ := exists_flatObject_lift_of_isFlat_at_point B S hS
    (fibreObjectStackMap B S hS 𝒳 (𝒳.val.val.p.obj (x i)) (Functor.Fiber.mk rfl))
    (isFlat_fibreObjectStackMap B S hS (x i) (hflat i)) (𝒳.val.val.p.obj w) (Functor.Fiber.mk rfl)
        hw z hi
  rw [show pointsHomeomorphScheme B S hS _ z = t from Homeomorph.apply_symm_apply _ t] at hmt
  let L := Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (𝒳.val.val.p.obj (x i)) (Functor.Fiber.mk rfl) a'
  let β : (CatFiberedInGroupoids.homFunctor
      (fibreObjectStackMap B S hS 𝒳 (𝒳.val.val.p.obj (x i)) (Functor.Fiber.mk rfl)).hom).obj a' ⟶
        x i := L.φ
  have hαflat : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map α)) :=
    flat_toScheme_map_of_isHomLift B S hS 𝒳.val.val.p α hα hm
  have hβflat : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map β)) :=
    flat_toScheme_map_of_isHomLift B S hS 𝒳.val.val.p β L.isStronglyCartesian.toIsHomLift
      ((flatObject_schemeStack_iff.{u, w} B S hS (𝒳.val.val.p.obj (x i)) a').1 ha')
  obtain ⟨t', ht'⟩ : t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map α)) := by
    rwa [range_toScheme_map_map_of_isHomLift 𝒳.val.val.p _ α hα]
  obtain ⟨K₁, z₁, φ₁, hR₁, hfppf₁⟩ := FibredSite.exists_fppf_ofArrows_le B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (J.pullback_stable β
      (ofArrows_smallEtaleToStackArrow_affineOpens_mem B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (x i)))
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hfppf₁
  obtain ⟨k₁, t₁, ht₁⟩ := hfppf₁.1 t'
  obtain ⟨K₂, y₂, φ₂, haff₂, -, hfppf₂⟩ :=
    FibredSite.exists_affine_fppf_ofArrows B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (z₁ k₁)
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hfppf₂
  obtain ⟨k₂, t₂, ht₂⟩ := hfppf₂.1 t₁
  obtain ⟨W, g, hg⟩ := (Sieve.mem_ofArrows_iff _ _ _).1
    ((Sieve.pullback _ _).downward_closed (hR₁ k₁) (φ₂ k₂))
  have h₁ : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (φ₁ k₁))) := (hfppf₁.2 k₁).1
  have h₂ : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (φ₂ k₂))) := (hfppf₂.2 k₂).1
  refine ⟨y₂ k₂, φ₂ k₂ ≫ φ₁ k₁ ≫ α, i, W, g, haff₂ k₂, ?_, ?_, t₂, ?_⟩
  · change Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (φ₂ k₂ ≫ φ₁ k₁ ≫ α)))
    simp only [Functor.map_comp]
    infer_instance
  · have := isOpenImmersion_toScheme_map_smallEtaleToStackArrow_open B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (x i) W.1
    refine flat_of_comp_isOpenImmersion _ ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map
      (smallEtaleToStackArrow B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (x i)
        (smallEtaleOpen B E h S hS 𝒳.val.val.p (x i) W.1)))) ?_
    rw [← Functor.map_comp, ← Functor.map_comp, ← hg]
    simp only [Functor.map_comp]
    infer_instance
  · change (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (φ₂ k₂ ≫ φ₁ k₁ ≫ α)) t₂ = t
    simpa only [Functor.map_comp, Scheme.Hom.comp_apply, ht₂, ht₁] using ht'

include hflat hsurj in
/-- **The refinement of Stacks 0GQF.**  A flat object `w` admits a family of morphisms
`v_k ⟶ w` from objects over affine schemes, flat and jointly surjective on underlying schemes,
each `v_k` having a morphism, flat on underlying schemes, to the image of an affine open of some
`U_i` under `U_{i,étale} ⥤ 𝒳`. -/
theorem exists_flat_refinement_smallEtaleOpen {w : 𝒳.val.val.obj}
    (hw : flatObject B S hS 𝒳.val w) :
    ∃ (K : Type u) (v : K → 𝒳.val.val.obj) (a : ∀ k, v k ⟶ w) (i : K → I)
      (W : ∀ k, ((𝒳.val.val.p.obj (x (i k))).left.1).affineOpens)
      (b : ∀ k, v k ⟶ (smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (x (i k))).obj (smallEtaleOpen B E h S hS 𝒳.val.val.p (x (i k)) (W k).1)),
      (∀ k, IsAffineOver B S hS (𝒳.val.val.p.obj (v k))) ∧
      (∀ k, Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (a k)))) ∧
      (∀ k, Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (b k)))) ∧
      (∀ t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj w),
        ∃ k, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (a k)))) := by
  choose v a i W b haff ha hb hrange using
    exists_flat_refinement_smallEtaleOpen_at_point B E h S hS 𝒳 x hflat hsurj hw
  exact ⟨_, v, a, i, W, b, haff, ha, hb, fun t => ⟨t, hrange t⟩⟩

end Refinement

end AlgebraicGeometry.Stack

end
