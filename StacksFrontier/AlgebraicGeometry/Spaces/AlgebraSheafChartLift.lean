module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartCartesian

/-!
# Ring maps out of the sections of a quasi-coherent algebra over an affine chart

Let `𝒜` be a quasi-coherent sheaf of `𝒪_F`-algebras on the small étale site of an algebraic space
`F` and `κ : U ⟶ V` a morphism of affine étale charts.  Then `𝒜(U) = 𝒪(U) ⊗_{𝒪(V)} 𝒜(V)` as
rings (`AlgebraSheaf.bijective_sectionsBaseChange_of_isQuasicoherent` and
`AlgebraSheaf.sectionsBaseChange_tmul_mul_tmul`), so a ring map out of `𝒜(U)` is the same thing as
a pair of ring maps out of `𝒪(U)` and out of `𝒜(V)` agreeing on `𝒪(V)`.  This file proves that
universal property.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.exists_chartLift`: existence of the ring map.
* `AlgebraicGeometry.Space.AlgebraSheaf.ringHom_ext_chart`: its uniqueness.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

namespace AlgebraSheaf

variable (A : AlgebraSheaf.{u, u} B S hS F hF)

/-- The sections of the underlying module, read as sections of the algebra. -/
abbrev modToRing (U : SmallEtale B S hS F) :
    A.underlyingModule.val.obj (op U) → A.right.obj.obj (op U) := fun x => x

variable {A}

/-- **A ring map out of the sections over an affine chart is determined by its values on the
regular functions and on the restricted sections over a larger affine chart.** -/
theorem ringHom_ext_chart (hA : A.IsQuasicoherent) {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (κ : U ⟶ V) {G : Type u} [CommRing G] {ψ ψ' : A.right.obj.obj (op U) →+* G}
    (h₁ : ∀ b, ψ (A.algebraMap (op U) b) = ψ' (A.algebraMap (op U) b))
    (h₂ : ∀ a, ψ (A.right.obj.map κ.op a) = ψ' (A.right.obj.map κ.op a)) : ψ = ψ' := by
  let := chartAlgebra (hF := hF) κ
  ext s
  obtain ⟨t, rfl⟩ := (bijective_sectionsBaseChange_of_isQuasicoherent A hA hV hU κ).2 s
  induction t using TensorProduct.inductionOn with
  | tmul b a =>
    rw [← sectionsBaseChange_tmul_eq A κ b a, map_mul, map_mul]
    exact congrArg₂ (· * ·) (h₁ b) (h₂ a)
  | add t₁ t₂ ih₁ ih₂ =>
    have e := map_add (sectionsBaseChange A.underlyingModule κ) t₁ t₂
    rw [e]
    exact (map_add ψ _ _).trans ((congrArg₂ (· + ·) ih₁ ih₂).trans (map_add ψ' _ _).symm)

/-- **Existence of ring maps out of the sections over an affine chart**: a ring map `f` out of the
regular functions on `U` and a ring map `g` out of the sections over a larger affine chart `V`,
agreeing on `𝒪(V)`, extend to a ring map out of `𝒜(U) = 𝒪(U) ⊗_{𝒪(V)} 𝒜(V)`. -/
theorem exists_chartLift (hA : A.IsQuasicoherent) {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (κ : U ⟶ V) {G : Type u} [CommRing G]
    (f : (structureSheaf B S hS F hF).obj.obj (op U) →+* G) (g : A.right.obj.obj (op V) →+* G)
    (h : ∀ r, f (chartRestrict (hF := hF) κ r) = g (A.algebraMap (op V) r)) :
    ∃ ψ : A.right.obj.obj (op U) →+* G,
      (∀ b, ψ (A.algebraMap (op U) b) = f b) ∧ (∀ a, ψ (A.right.obj.map κ.op a) = g a) := by
  let := chartAlgebra (hF := hF) κ
  let f' : chartRing B S hS F hF U →+* G := f
  let : Algebra (chartRing B S hS F hF U) G := f'.toAlgebra
  let : Module (chartRing B S hS F hF V) G := Module.compHom G (f'.comp (chartRestrict κ))
  have : IsScalarTower (chartRing B S hS F hF V) (chartRing B S hS F hF U) G :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g' : A.underlyingModule.val.obj (op V) →ₗ[chartRing B S hS F hF V] G :=
    { toFun := fun a => g (modToRing A V a)
      map_add' := fun a a' => map_add g (modToRing A V a) (modToRing A V a')
      map_smul' := fun r a => by
        change g (A.algebraMap (op V) r * modToRing A V a) = f' (chartRestrict κ r) * g _
        rw [map_mul]
        exact congrArg (· * g (modToRing A V a)) (h r).symm }
  let L := LinearMap.liftBaseChange (chartRing B S hS F hF U) g'
  have hL : ∀ b a, L (b ⊗ₜ a) = f' b * g (modToRing A V a) := fun _ _ => rfl
  have hbij := bijective_sectionsBaseChange_of_isQuasicoherent A hA hV hU κ
  let e := LinearEquiv.ofBijective (sectionsBaseChange A.underlyingModule κ) hbij
  have he : ∀ t, e t = sectionsBaseChange A.underlyingModule κ t := fun _ => rfl
  let ψf : A.right.obj.obj (op U) → G := fun s => L (e.symm s)
  have hψ : ∀ t, ψf (modToRing A U (sectionsBaseChange A.underlyingModule κ t)) = L t := by
    intro t
    change L (e.symm (e t)) = L t
    rw [e.symm_apply_apply]
  have hψadd : ∀ x y, ψf (x + y) = ψf x + ψf y := fun x y =>
    (congrArg L (map_add e.symm x y)).trans (map_add L _ _)
  have hψzero : ψf 0 = 0 := (congrArg L (map_zero e.symm)).trans (map_zero L)
  have hsadd : ∀ t₁ t₂, modToRing A U (sectionsBaseChange A.underlyingModule κ (t₁ + t₂)) =
      modToRing A U (sectionsBaseChange A.underlyingModule κ t₁) +
        modToRing A U (sectionsBaseChange A.underlyingModule κ t₂) := fun t₁ t₂ =>
    map_add (sectionsBaseChange A.underlyingModule κ) t₁ t₂
  have hmul : ∀ t t', ψf (modToRing A U (sectionsBaseChange A.underlyingModule κ t) *
      modToRing A U (sectionsBaseChange A.underlyingModule κ t')) =
      L t * L t' := by
    intro t t'
    induction t using TensorProduct.inductionOn with
    | tmul b a =>
      induction t' using TensorProduct.inductionOn with
      | tmul b' a' =>
        have hp := sectionsBaseChange_tmul_mul_tmul A κ b b' (modToRing A V a) (modToRing A V a')
        rw [sectionsBaseChange_tmul_eq A κ b (modToRing A V a),
          sectionsBaseChange_tmul_eq A κ b' (modToRing A V a')] at hp
        change ψf (modToRing A U (sectionsBaseChange A.underlyingModule κ (b ⊗ₜ a)) *
          modToRing A U (sectionsBaseChange A.underlyingModule κ (b' ⊗ₜ a'))) = _
        rw [hp, hψ]
        refine (hL (b * b') (modToRing A V a * modToRing A V a')).trans ?_
        rw [hL, hL, map_mul, map_mul]
        ring
      | add t₁ t₂ ih₁ ih₂ => rw [hsadd, mul_add, hψadd, ih₁, ih₂, map_add L, mul_add]
    | add t₁ t₂ ih₁ ih₂ => rw [hsadd, add_mul, hψadd, ih₁, ih₂, map_add L, add_mul]
  refine ⟨{ toFun := ψf
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_ }, ?_, ?_⟩
  · have k : modToRing A U (sectionsBaseChange A.underlyingModule κ
        ((1 : chartRing B S hS F hF U) ⊗ₜ (1 : A.right.obj.obj (op V)))) = 1 :=
      (sectionsBaseChange_tmul_eq A κ 1 1).symm.trans (by rw [map_one, map_one, one_mul])
    change ψf 1 = 1
    rw [← k, hψ]
    exact (hL _ _).trans (by rw [map_one, map_one, one_mul])
  · intro s s'
    obtain ⟨t, rfl⟩ := hbij.2 s
    obtain ⟨t', rfl⟩ := hbij.2 s'
    exact (hmul t t').trans (congrArg₂ (· * ·) (hψ t).symm (hψ t').symm)
  · exact hψzero
  · exact hψadd
  · intro b
    have k : modToRing A U (sectionsBaseChange A.underlyingModule κ
        ((b : chartRing B S hS F hF U) ⊗ₜ (1 : A.right.obj.obj (op V)))) = A.algebraMap (op U) b :=
      (sectionsBaseChange_tmul_eq A κ b 1).symm.trans (by rw [map_one, mul_one])
    change ψf _ = _
    rw [← k, hψ]
    exact (hL _ _).trans (by rw [map_one, mul_one]; rfl)
  · intro a
    have k : modToRing A U (sectionsBaseChange A.underlyingModule κ
        ((1 : chartRing B S hS F hF U) ⊗ₜ a)) = A.right.obj.map κ.op a :=
      (sectionsBaseChange_tmul_eq A κ 1 a).symm.trans (by rw [map_one, one_mul])
    change ψf _ = _
    rw [← k, hψ]
    exact (hL _ _).trans (by rw [map_one, one_mul])

end AlgebraSheaf

end AlgebraicGeometry.Space

end
