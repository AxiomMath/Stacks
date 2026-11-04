module

public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The torsor of lifts along a first-order thickening

Let `f : X ⟶ S` be a morphism of schemes and let `i : T ⟶ T'` be a first-order thickening with
`T'` affine, presenting a lifting problem
```
T  --a--→ X
|         |
i         f
↓         ↓
T' --h--→ S
```
`Stacks.Smooth.exists_lift_of_range_subset` produces a solution as soon as `a` maps into a single
pair of affine charts `W ⊆ X`, `V ⊆ S`. Step (II) of the proof of [Stacks Project, Tag 02H6]
needs more than existence: it needs the *difference* of two solutions and the *action* of the
conormal module on solutions, because the local solutions of step (I) have to be corrected before
they can be glued. This file supplies that structure.

The ring-theoretic content is the torsor structure on the lifts of a ring map into a square-zero
extension. Mathlib's `derivationToSquareZeroEquivLift` already describes it, but only once an
`Algebra B A'` instance has been chosen, that is once a lift is fixed and installed as the
algebra structure. The version here keeps the reduction `β : B →+* A` as the datum and quantifies
over the lifts of `β`, which is what the geometric application needs: the two lifts coming from
two charts are on an equal footing, and the module structure on the conormal module must be the
one of `Stacks.Smooth.thickeningKerModule`, which is read off `β` alone.

## Main definitions

* `Stacks.Smooth.homEquivOfIsAffine`: morphisms into an affine scheme are the ring maps on global
  sections.
* `Stacks.Smooth.diffDerivation`: the difference of two lifts of `β : B →+* A` to a square-zero
  extension `π : A' →+* A`, as a derivation with values in the kernel of `π`, and
  `Stacks.Smooth.addDerivationAlgHom` the lift obtained by adding a derivation to a given lift.
* `Stacks.Smooth.liftDiffDerivation`: the difference of two solutions of one lifting problem,
  both with image in `W`, as a `Γ(S, V)`-derivation of `Γ(X, W)` with values in the conormal
  module of the thickening, and `Stacks.Smooth.addDerivationHom` the ring map obtained by adding
  a derivation to the sections of a solution.

## Main results

* `Stacks.Smooth.exists_hom_appLE` and `Stacks.Smooth.hom_ext_of_appLE`: for `W` an affine open of
  `X`, the morphisms `T' ⟶ X` whose image lies in `W` are exactly the ring maps
  `Γ(X, W) ⟶ Γ(T', ⊤)`, bijectively, through `AlgebraicGeometry.Scheme.Hom.appLE`.
* `Stacks.Smooth.diffDerivation_apply`, `Stacks.Smooth.addDerivationAlgHom_apply` and
  `Stacks.Smooth.diffDerivation_addDerivationAlgHom`: the difference and the action are inverse to
  one another, so the lifts of `β` form a torsor under the derivations.
* `Stacks.Smooth.algHom_eq_of_diffDerivation_eq_zero`: the action is free.
* `Stacks.Smooth.appLE_comp_appLE_of_lift` and `Stacks.Smooth.appLE_appTop_of_lift`: a solution of
  the lifting problem whose image lies in `W` induces a ring map `Γ(X, W) ⟶ Γ(T', ⊤)` compatible
  with the structure maps out of `Γ(S, V)` and lifting `a.appLE W ⊤`, and
  `Stacks.Smooth.exists_lift_of_algHom` is the converse.
* `Stacks.Smooth.liftDiffDerivation_apply` and `Stacks.Smooth.exists_lift_of_derivation`: the
  solutions of a lifting problem in a chart form a torsor under the `Γ(S, V)`-derivations of
  `Γ(X, W)` with values in the conormal module, in exactly the module structures that
  `Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module` consumes.

## Implementation notes

`Stacks.Smooth.homEquivOfIsAffine` is the unit-counit computation for `Γ ⊣ Spec`: the inverse of
`b ↦ b.appTop` sends `φ` to `X.toSpecΓ ≫ Spec.map φ ≫ Y.isoSpec.inv`, and the two round trips
are `AlgebraicGeometry.Scheme.toSpecΓ_naturality` and
`AlgebraicGeometry.Scheme.ΓSpecIso_naturality`. The chart version is obtained by factoring a
morphism with image in `W` through the open immersion `W.ι` and comparing
`AlgebraicGeometry.Scheme.Hom.appLE` with `AlgebraicGeometry.Scheme.Opens.topIso`; the comparison
is an equality of restriction maps of the structure sheaf along two inclusions of opens, which
agree because the hom-sets of a poset are subsingletons.

The derivation `Stacks.Smooth.diffDerivation` is built by hand rather than transported from
`derivationToSquareZeroEquivLift` precisely so that its module structure is
`Stacks.Smooth.kerModuleOfRingHom`, the restriction of scalars of
`Stacks.Smooth.kerModule` along `β`. At the geometric end `β` is instantiated to
`a.appLE W ⊤`, and then that module structure is literally
`Stacks.Smooth.moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)`, so no comparison of instances is
needed when the derivation is handed to
`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module`. The two computations the
construction turns on are that `ψ b` is a preimage under `π` of `β b`, so that the action of `b`
on the kernel is multiplication by `ψ b`, and that `(φ b - ψ b) * (φ c - ψ c)` lies in the square
of the kernel and so vanishes.

## References

* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-! ### Morphisms into an affine scheme -/

/-- **Morphisms into an affine scheme are the ring maps on global sections.** For `Y` affine the
map `b ↦ b.appTop` is a bijection from `X ⟶ Y` onto `Γ(Y, ⊤) ⟶ Γ(X, ⊤)`. -/
noncomputable def homEquivOfIsAffine {X Y : Scheme.{u}} [IsAffine Y] :
    (X ⟶ Y) ≃ (Γ(Y, (⊤ : Y.Opens)) ⟶ Γ(X, (⊤ : X.Opens))) where
  toFun b := b.appTop
  invFun φ := X.toSpecΓ ≫ Spec.map φ ≫ Y.isoSpec.inv
  left_inv b := by
    change X.toSpecΓ ≫ Spec.map b.appTop ≫ Y.isoSpec.inv = b
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom,
      Iso.hom_inv_id, Category.comp_id]
  right_inv φ := by
    change (X.toSpecΓ ≫ Spec.map φ ≫ Y.isoSpec.inv).appTop = φ
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Stacks.Modules.isoSpec_inv_appTop,
      Scheme.toSpecΓ_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- `Stacks.Smooth.homEquivOfIsAffine` is `AlgebraicGeometry.Scheme.Hom.appTop`. -/
theorem homEquivOfIsAffine_apply {X Y : Scheme.{u}} [IsAffine Y] (b : X ⟶ Y) :
    homEquivOfIsAffine b = b.appTop :=
  rfl

/-! ### Morphisms into an affine open -/

section Chart

variable {X T' : Scheme.{u}} {W : X.Opens}

/-- The restriction map of the structure sheaf along the inclusion `W.ι ''ᵁ ⊤ ⊆ W` is the
identification `Γ(W.toScheme, ⊤) ≅ Γ(X, W)`. -/
theorem opens_ι_appLE_top : W.ι.appLE W ⊤ (le_of_eq W.ι_preimage_self.symm) = W.topIso.inv := by
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  congr 1

/-- The sections of a morphism over `⊤` are its sections on global sections. -/
private theorem appLE_top_top_eq {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    g.appLE (⊤ : Z.Opens) ⊤ le_top = g.appTop := by
  simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, TopologicalSpace.Opens.map_top,
    homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The sections of a morphism into an affine open, read through the factorization of the
morphism through the open subscheme. -/
theorem appLE_top_eq (c : T' ⟶ (W : Scheme.{u}))
    (hb : (⊤ : T'.Opens) ≤ (c ≫ W.ι) ⁻¹ᵁ W) :
    (c ≫ W.ι).appLE W ⊤ hb = W.topIso.inv ≫ c.appTop := by
  rw [← Scheme.Hom.appLE_comp_appLE c W.ι W ⊤ ⊤ (le_of_eq W.ι_preimage_self.symm) le_top,
    opens_ι_appLE_top, appLE_top_top_eq]

/-- The sections over an affine open of a morphism factoring through the open subscheme. -/
theorem appLE_top_eq_of_fac {b : T' ⟶ X} (c : T' ⟶ (W : Scheme.{u})) (hf : c ≫ W.ι = b)
    (hb : (⊤ : T'.Opens) ≤ b ⁻¹ᵁ W) : b.appLE W ⊤ hb = W.topIso.inv ≫ c.appTop := by
  subst hf
  exact appLE_top_eq c hb

/-- **A ring map into the global sections of a scheme is realized by a morphism into an affine
open.** For `W` an affine open of `X`, every ring map `Γ(X, W) ⟶ Γ(T', ⊤)` is
`AlgebraicGeometry.Scheme.Hom.appLE` of a morphism `T' ⟶ X` whose image lies in `W`. -/
theorem exists_hom_appLE (hW : IsAffineOpen W) (φ : Γ(X, W) ⟶ Γ(T', (⊤ : T'.Opens))) :
    ∃ (b : T' ⟶ X) (hb : (⊤ : T'.Opens) ≤ b ⁻¹ᵁ W), b.appLE W ⊤ hb = φ := by
  have hWa : IsAffine (W : Scheme.{u}) := hW
  set c : T' ⟶ (W : Scheme.{u}) := homEquivOfIsAffine.symm (W.topIso.hom ≫ φ) with hc
  have hcapp : c.appTop = W.topIso.hom ≫ φ := homEquivOfIsAffine.apply_symm_apply _
  have hran : (⊤ : T'.Opens) ≤ (c ≫ W.ι) ⁻¹ᵁ W := by
    intro x _
    show (c ≫ W.ι).base x ∈ W
    rw [Scheme.Hom.comp_apply]
    exact (c.base x).2
  exact ⟨c ≫ W.ι, hran, by rw [appLE_top_eq c hran, hcapp, Iso.inv_hom_id_assoc]⟩

/-- **A morphism into an affine open is determined by its sections.** Two morphisms `T' ⟶ X`
whose images lie in an affine open `W` and which agree on the sections over `W` are equal. -/
theorem hom_ext_of_appLE (hW : IsAffineOpen W) {b₁ b₂ : T' ⟶ X}
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W)
    (h : b₁.appLE W ⊤ hb₁ = b₂.appLE W ⊤ hb₂) : b₁ = b₂ := by
  have hWa : IsAffine (W : Scheme.{u}) := hW
  have key : ∀ (b : T' ⟶ X) (hb : (⊤ : T'.Opens) ≤ b ⁻¹ᵁ W),
      ∃ c : T' ⟶ (W : Scheme.{u}),
        c ≫ W.ι = b ∧ b.appLE W ⊤ hb = W.topIso.inv ≫ c.appTop := by
    intro b hb
    have hran : Set.range b.base ⊆ Set.range W.ι.base := by
      rintro y ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hb (Set.mem_univ x)
    exact ⟨IsOpenImmersion.lift W.ι b hran, IsOpenImmersion.lift_fac _ _ _,
      appLE_top_eq_of_fac _ (IsOpenImmersion.lift_fac _ _ _) hb⟩
  obtain ⟨c₁, hf₁, e₁⟩ := key b₁ hb₁
  obtain ⟨c₂, hf₂, e₂⟩ := key b₂ hb₂
  rw [e₁, e₂] at h
  rw [← hf₁, ← hf₂, homEquivOfIsAffine.injective ((Iso.cancel_iso_inv_left W.topIso _ _).mp h)]

end Chart

/-! ### The torsor of lifts into a square-zero extension -/

section SquareZero

variable {R B A A' : Type u} [CommRing R] [CommRing B] [CommRing A] [CommRing A'] [Algebra R B]
  [Algebra R A'] {π : A' →+* A}

/-- The scalar tower `R → B → RingHom.ker π` for the module structure of
`Stacks.Smooth.kerModuleOfRingHom`, provided the reduction `β` is compatible with the two
structure maps out of `R`. -/
theorem isScalarTowerKerModuleOfRingHom (hπ : Function.Surjective π)
    (h2 : RingHom.ker π ^ 2 = ⊥) (β : B →+* A)
    (hβ : ∀ r : R, β (algebraMap R B r) = π (algebraMap R A' r)) :
    letI := kerModuleOfRingHom hπ h2 β
    IsScalarTower R B (RingHom.ker π) := by
  let := kerModule hπ h2
  let := kerModuleOfRingHom hπ h2 β
  refine IsScalarTower.of_algebraMap_smul fun r y ↦ ?_
  rw [kerModuleOfRingHom_smul hπ h2 β _ (algebraMap R A' r) (hβ r).symm]
  exact Subtype.ext (Algebra.smul_def r (y : A')).symm

/-- The product of two elements of a square-zero ideal vanishes. -/
private theorem mul_eq_zero_of_sq_eq_bot {S : Type*} [CommRing S] {I : Ideal S} (h2 : I ^ 2 = ⊥)
    {x y : S} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have hm : x * y ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hy
  rw [h2] at hm
  simpa using hm

/-- Two lifts of the same reduction differ by an element of the kernel. -/
theorem sub_mem_ker_of_lift (β : B →+* A) {φ ψ : B →ₐ[R] A'} (hφ : ∀ b, π (φ b) = β b)
    (hψ : ∀ b, π (ψ b) = β b) (b : B) : φ b - ψ b ∈ RingHom.ker π := by
  rw [RingHom.mem_ker, map_sub, hφ b, hψ b, sub_self]

/-- The product of two differences of lifts of the same reduction vanishes, because it lies in
the square of the kernel. -/
theorem mul_sub_sub_eq_zero (h2 : RingHom.ker π ^ 2 = ⊥) (β : B →+* A) {φ ψ : B →ₐ[R] A'}
    (hφ : ∀ b, π (φ b) = β b) (hψ : ∀ b, π (ψ b) = β b) (b c : B) :
    (φ b - ψ b) * (φ c - ψ c) = 0 := by
  exact mul_eq_zero_of_sq_eq_bot h2 (sub_mem_ker_of_lift β hφ hψ b)
    (sub_mem_ker_of_lift β hφ hψ c)

/-- A lift of the reduction makes the reduction compatible with the two structure maps out of
`R`, which is the hypothesis `Stacks.Smooth.isScalarTowerKerModuleOfRingHom` needs. -/
theorem algebraMap_reduction_eq (β : B →+* A) {ψ : B →ₐ[R] A'} (hψ : ∀ b, π (ψ b) = β b)
    (r : R) : β (algebraMap R B r) = π (algebraMap R A' r) := by
  rw [← hψ (algebraMap R B r), ψ.commutes]

/-- The difference `b ↦ φ b - ψ b` of two lifts of `β : B →+* A` along a surjection
`π : A' →+* A` with square-zero kernel, as an `R`-linear map into that kernel. This is the
underlying linear map of `Stacks.Smooth.diffDerivation`. -/
noncomputable def diffLinearMap (β : B →+* A) (φ ψ : B →ₐ[R] A') (hφ : ∀ b, π (φ b) = β b)
    (hψ : ∀ b, π (ψ b) = β b) : B →ₗ[R] RingHom.ker π :=
  { toFun := fun b ↦ ⟨φ b - ψ b, sub_mem_ker_of_lift β hφ hψ b⟩
    map_add' := fun b c ↦ Subtype.ext (by
      simp only [Submodule.coe_add, map_add]
      ring)
    map_smul' := fun r b ↦ Subtype.ext (by
      change φ (r • b) - ψ (r • b) = r • (φ b - ψ b)
      rw [map_smul, map_smul, smul_sub]) }

/-- The value of `Stacks.Smooth.diffLinearMap`. -/
theorem diffLinearMap_apply (β : B →+* A) (φ ψ : B →ₐ[R] A') (hφ : ∀ b, π (φ b) = β b)
    (hψ : ∀ b, π (ψ b) = β b) (b : B) :
    ((diffLinearMap β φ ψ hφ hψ b : RingHom.ker π) : A') = φ b - ψ b :=
  rfl

/-- **The difference of two lifts into a square-zero extension is a derivation.** For
`π : A' →+* A` a surjection with square-zero kernel and `φ`, `ψ : B →ₐ[R] A'` two lifts of the
same ring map `β : B →+* A`, the map `b ↦ φ b - ψ b` is an `R`-derivation of `B` with values in
the kernel of `π`, for the `B`-module structure `Stacks.Smooth.kerModuleOfRingHom` read off
`β`. -/
@[ega "0 20.1.1", ega "IV 16.5.14" "partial"]
noncomputable def diffDerivation (hπ : Function.Surjective π) (h2 : RingHom.ker π ^ 2 = ⊥)
    (β : B →+* A) (φ ψ : B →ₐ[R] A') (hφ : ∀ b, π (φ b) = β b) (hψ : ∀ b, π (ψ b) = β b) :
    letI := kerModuleOfRingHom hπ h2 β
    letI := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
    Derivation R B (RingHom.ker π) :=
  letI := kerModule hπ h2
  letI := kerModuleOfRingHom hπ h2 β
  letI := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
  { diffLinearMap β φ ψ hφ hψ with
    map_one_eq_zero' := Subtype.ext (by
      rw [diffLinearMap_apply, map_one, map_one, sub_self]
      rfl)
    leibniz' := fun b c ↦ Subtype.ext (by
      rw [Submodule.coe_add,
        kerModuleOfRingHom_smul hπ h2 β b (ψ b) (hψ b)
          (diffLinearMap β φ ψ hφ hψ c),
        kerModuleOfRingHom_smul hπ h2 β c (ψ c) (hψ c)
          (diffLinearMap β φ ψ hφ hψ b)]
      have hz := mul_sub_sub_eq_zero h2 β hφ hψ b c
      simp only [SetLike.val_smul, smul_eq_mul, diffLinearMap_apply, map_mul]
      linear_combination hz) }

/-- The value of `Stacks.Smooth.diffDerivation`. -/
theorem diffDerivation_apply (hπ : Function.Surjective π) (h2 : RingHom.ker π ^ 2 = ⊥)
    (β : B →+* A) (φ ψ : B →ₐ[R] A') (hφ : ∀ b, π (φ b) = β b) (hψ : ∀ b, π (ψ b) = β b)
    (b : B) :
    letI := kerModuleOfRingHom hπ h2 β
    letI := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
    ((diffDerivation hπ h2 β φ ψ hφ hψ b : RingHom.ker π) : A') = φ b - ψ b :=
  rfl

/-- **The action of the derivations on the lifts is free.** Two lifts of the same reduction whose
difference derivation vanishes are equal. -/
@[ega "IV 16.5.14" "partial"]
theorem algHom_eq_of_diffDerivation_eq_zero (hπ : Function.Surjective π)
    (h2 : RingHom.ker π ^ 2 = ⊥) (β : B →+* A) (φ ψ : B →ₐ[R] A')
    (hφ : ∀ b, π (φ b) = β b) (hψ : ∀ b, π (ψ b) = β b)
    (h : letI := kerModuleOfRingHom hπ h2 β
      letI := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
      diffDerivation hπ h2 β φ ψ hφ hψ = 0) : φ = ψ := by
  let := kerModuleOfRingHom hπ h2 β
  let := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
  refine AlgHom.ext fun b ↦ sub_eq_zero.mp ?_
  have hb := congrArg (fun δ : Derivation R B (RingHom.ker π) ↦ ((δ b : RingHom.ker π) : A')) h
  rw [diffDerivation_apply] at hb
  simpa using hb

/-- **A derivation acts on the lifts into a square-zero extension.** Adding a derivation with
values in the kernel of `π` to a lift `ψ` of `β` produces another lift of `β`. -/
@[ega "IV 16.5.14"]
noncomputable def addDerivationAlgHom (hπ : Function.Surjective π) (h2 : RingHom.ker π ^ 2 = ⊥)
    (β : B →+* A) (ψ : B →ₐ[R] A') (hψ : ∀ b, π (ψ b) = β b)
    (δ : letI := kerModuleOfRingHom hπ h2 β
      letI := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
      Derivation R B (RingHom.ker π)) : B →ₐ[R] A' :=
  letI := kerModule hπ h2
  letI := kerModuleOfRingHom hπ h2 β
  letI := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
  { toFun := fun b ↦ ψ b + δ b
    map_one' := by rw [map_one, δ.map_one_eq_zero, Submodule.coe_zero, add_zero]
    map_mul' := fun b c ↦ by
      have hz : ((δ b : RingHom.ker π) : A') * ((δ c : RingHom.ker π) : A') = 0 := by
        have hm : ((δ b : RingHom.ker π) : A') * ((δ c : RingHom.ker π) : A')
            ∈ RingHom.ker π ^ 2 := by
          rw [pow_two]; exact Ideal.mul_mem_mul (δ b).2 (δ c).2
        rw [h2] at hm
        simpa using hm
      rw [map_mul, δ.leibniz, Submodule.coe_add,
        kerModuleOfRingHom_smul hπ h2 β b (ψ b) (hψ b) (δ c),
        kerModuleOfRingHom_smul hπ h2 β c (ψ c) (hψ c) (δ b)]
      simp only [SetLike.val_smul, smul_eq_mul]
      linear_combination -hz
    map_zero' := by rw [map_zero, map_zero, Submodule.coe_zero, add_zero]
    map_add' := fun b c ↦ by rw [map_add, map_add, Submodule.coe_add]; ring
    commutes' := fun r ↦ by
      rw [AlgHom.commutes, Derivation.map_algebraMap, Submodule.coe_zero, add_zero] }

/-- The value of `Stacks.Smooth.addDerivationAlgHom`. -/
@[ega "IV 16.5.14" "partial"]
theorem addDerivationAlgHom_apply (hπ : Function.Surjective π) (h2 : RingHom.ker π ^ 2 = ⊥)
    (β : B →+* A) (ψ : B →ₐ[R] A') (hψ : ∀ b, π (ψ b) = β b)
    (δ : letI := kerModuleOfRingHom hπ h2 β
      letI := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
      Derivation R B (RingHom.ker π)) (b : B) :
    addDerivationAlgHom hπ h2 β ψ hψ δ b = ψ b + δ b :=
  rfl

/-- `Stacks.Smooth.addDerivationAlgHom` is again a lift of the same reduction. -/
@[ega "IV 16.5.14" "partial"]
theorem reduction_addDerivationAlgHom (hπ : Function.Surjective π)
    (h2 : RingHom.ker π ^ 2 = ⊥) (β : B →+* A) (ψ : B →ₐ[R] A')
    (hψ : ∀ b, π (ψ b) = β b)
    (δ : letI := kerModuleOfRingHom hπ h2 β
      letI := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
      Derivation R B (RingHom.ker π)) (b : B) :
    π (addDerivationAlgHom hπ h2 β ψ hψ δ b) = β b := by
  rw [addDerivationAlgHom_apply, map_add, hψ b, RingHom.mem_ker.mp (δ b).2, add_zero]

/-- **Difference and action are inverse to one another**: the difference derivation of
`Stacks.Smooth.addDerivationAlgHom` and `ψ` is the derivation one started with, so the lifts of
`β` form a torsor under the derivations with values in the kernel of `π`. -/
@[ega "IV 16.5.14" "Freeness"]
theorem diffDerivation_addDerivationAlgHom (hπ : Function.Surjective π)
    (h2 : RingHom.ker π ^ 2 = ⊥) (β : B →+* A) (ψ : B →ₐ[R] A')
    (hψ : ∀ b, π (ψ b) = β b)
    (δ : letI := kerModuleOfRingHom hπ h2 β
      letI := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
      Derivation R B (RingHom.ker π)) :
    letI := kerModuleOfRingHom hπ h2 β
    letI := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
    diffDerivation hπ h2 β (addDerivationAlgHom hπ h2 β ψ hψ δ) ψ
      (reduction_addDerivationAlgHom hπ h2 β ψ hψ δ) hψ = δ := by
  let := kerModuleOfRingHom hπ h2 β
  let := isScalarTowerKerModuleOfRingHom hπ h2 β (algebraMap_reduction_eq β hψ)
  refine Derivation.ext fun b ↦ Subtype.ext ?_
  rw [diffDerivation_apply, addDerivationAlgHom_apply]
  ring

end SquareZero

/-! ### Solutions of a lifting problem in a chart, as ring maps -/

section Lift

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {W : X.Opens}

/-- The sections of a morphism over `⊤` are its sections on global sections. -/
theorem appLE_top_top (b : T' ⟶ X) : b.appLE (⊤ : X.Opens) ⊤ le_top = b.appTop :=
  appLE_top_top_eq b

/-- The sections of `b` over `U` reduce along `i` to the sections of `i ≫ b` over `U`. -/
private theorem appLE_comp_appTop_of_comp {Y : Scheme.{u}} {U : Y.Opens} (i : T ⟶ T')
    (b : T' ⟶ Y) (hb : (⊤ : T'.Opens) ≤ b ⁻¹ᵁ U) (hib : (⊤ : T.Opens) ≤ (i ≫ b) ⁻¹ᵁ U) :
    b.appLE U ⊤ hb ≫ i.appTop = (i ≫ b).appLE U ⊤ hib := by
  rw [← appLE_top_top i]
  exact Scheme.Hom.appLE_comp_appLE i b U ⊤ ⊤ hb le_top

/- Not Mathlib's `AlgebraicGeometry.Scheme.Hom.appLE_congr`: that one keeps the morphism fixed
and transports a predicate along equalities of the two *opens*, whereas this one keeps the opens
fixed and transports along an equality of the two *morphisms*. -/

/-- Equal morphisms have equal sections; the two proofs that the open of the source maps into
the open of the target need not agree, since they are propositions. -/
theorem appLE_congr {Y Z : Scheme.{u}} {g₁ g₂ : Y ⟶ Z} (e : g₁ = g₂) {U : Z.Opens}
    {U' : Y.Opens} (p : U' ≤ g₁ ⁻¹ᵁ U) (q : U' ≤ g₂ ⁻¹ᵁ U) :
    g₁.appLE U U' p = g₂.appLE U U' q := by
  subst e
  rfl

/-- **A solution of the lifting problem is a `Γ(S, V)`-algebra map on sections.** If `b ≫ f = h`
and `b` maps into the affine open `W`, then the sections of `b` over `W` commute with the two
structure maps out of `Γ(S, V)`. -/
theorem appLE_comp_appLE_of_lift {b : T' ⟶ X} {h : T' ⟶ S} (hbf : b ≫ f = h)
    (hWV : W ≤ f ⁻¹ᵁ V) (hb : (⊤ : T'.Opens) ≤ b ⁻¹ᵁ W) (hV' : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ V) :
    f.appLE V W hWV ≫ b.appLE W ⊤ hb = h.appLE V ⊤ hV' := by
  subst hbf
  exact Scheme.Hom.appLE_comp_appLE b f V W ⊤ hWV hb

/-- **A solution of the lifting problem lifts the sections of `a`.** If `i ≫ b = a` then the
sections of `b` over `W` reduce, along `i`, to the sections of `a` over `W`. -/
theorem appLE_appTop_of_lift {i : T ⟶ T'} {a : T ⟶ X} {b : T' ⟶ X} (hba : i ≫ b = a)
    (hb : (⊤ : T'.Opens) ≤ b ⁻¹ᵁ W) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) :
    b.appLE W ⊤ hb ≫ i.appTop = a.appLE W ⊤ hUW := by
  subst hba
  exact appLE_comp_appTop_of_comp i b hb hUW

/-- **A `Γ(S, V)`-algebra map on sections is a solution of the lifting problem.** Let `V` be an
affine open of `S` and `W` an affine open of `X` with `W ≤ f ⁻¹ᵁ V`, and let `a : T ⟶ X`,
`h : T' ⟶ S` present a lifting problem with `a` mapping into `W` and `h` into `V`. Every ring map
`φ : Γ(X, W) ⟶ Γ(T', ⊤)` that commutes with the structure maps out of `Γ(S, V)` and reduces along
`i` to the sections of `a` is the sections of a solution of the lifting problem.

Together with `Stacks.Smooth.appLE_comp_appLE_of_lift` and
`Stacks.Smooth.appLE_appTop_of_lift` this identifies the solutions with the lifts of
`a.appLE W ⊤` to `Γ(T', ⊤)`, which is the form in which the ring-level torsor structure of this
file applies. -/
theorem exists_lift_of_algHom (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) {i : T ⟶ T'} {a : T ⟶ X} {h : T' ⟶ S}
    (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (hV' : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ V)
    (φ : Γ(X, W) ⟶ Γ(T', (⊤ : T'.Opens)))
    (hφf : f.appLE V W hWV ≫ φ = h.appLE V ⊤ hV')
    (hφa : φ ≫ i.appTop = a.appLE W ⊤ hUW) :
    ∃ (b : T' ⟶ X) (hb : (⊤ : T'.Opens) ≤ b ⁻¹ᵁ W),
      b ≫ f = h ∧ i ≫ b = a ∧ b.appLE W ⊤ hb = φ := by
  obtain ⟨b, hb, hbφ⟩ := exists_hom_appLE hW φ
  have hbfV : (⊤ : T'.Opens) ≤ (b ≫ f) ⁻¹ᵁ V := fun x _ ↦ hWV (hb (Set.mem_univ x))
  have hiW : (⊤ : T.Opens) ≤ (i ≫ b) ⁻¹ᵁ W := fun x _ ↦ hb (Set.mem_univ (i.base x))
  refine ⟨b, hb, hom_ext_of_appLE hV hbfV hV' ?_, hom_ext_of_appLE hW hiW hUW ?_, hbφ⟩
  · rw [← Scheme.Hom.appLE_comp_appLE b f V W ⊤ hWV hb, hbφ, hφf]
  · rw [← appLE_comp_appTop_of_comp i b hb hiW, hbφ, hφa]

/-- The difference of the sections of two solutions of one lifting problem lies in the conormal
module of the thickening. -/
theorem sub_appLE_mem_ker {i : T ⟶ T'} {a : T ⟶ X} {b₁ b₂ : T' ⟶ X}
    (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a)
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W) (x : Γ(X, W)) :
    (b₁.appLE W ⊤ hb₁).hom x - (b₂.appLE W ⊤ hb₂).hom x ∈ RingHom.ker i.appTop.hom := by
  have e₁ : i.appTop.hom ((b₁.appLE W ⊤ hb₁).hom x) = (a.appLE W ⊤ hUW).hom x := by
    rw [← CommRingCat.comp_apply, appLE_appTop_of_lift hb₁a hb₁ hUW]
  have e₂ : i.appTop.hom ((b₂.appLE W ⊤ hb₂).hom x) = (a.appLE W ⊤ hUW).hom x := by
    rw [← CommRingCat.comp_apply, appLE_appTop_of_lift hb₂a hb₂ hUW]
  rw [RingHom.mem_ker, map_sub, e₁, e₂, sub_self]

/-- The product of two differences of the sections of solutions of one lifting problem vanishes,
because it lies in the square of the conormal module. -/
theorem mul_sub_appLE_eq_zero [IsAffine T'] {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {b₁ b₂ : T' ⟶ X}
    (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a)
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W) (x y : Γ(X, W)) :
    ((b₁.appLE W ⊤ hb₁).hom x - (b₂.appLE W ⊤ hb₂).hom x) *
      ((b₁.appLE W ⊤ hb₁).hom y - (b₂.appLE W ⊤ hb₂).hom y) = 0 := by
  exact mul_eq_zero_of_sq_eq_bot (ker_appTop_sq_eq_bot hi)
    (sub_appLE_mem_ker hUW hb₁a hb₂a hb₁ hb₂ x) (sub_appLE_mem_ker hUW hb₁a hb₂a hb₁ hb₂ y)

/-! ### The torsor of solutions of a lifting problem in a chart -/

section Conormal

variable [IsAffine T'] {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X}
  {h : T' ⟶ S} (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W)
  (hV' : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ V)

omit [IsAffine T'] in
/-- The two structure maps out of `Γ(S, V)` into the conormal module agree: through the chart
`(V, W)` and `a`, and through `h` and `i`. -/
theorem appLE_base_comm (hcomm : a ≫ f = i ≫ h) (r : Γ(S, V)) :
    (a.appLE W ⊤ hUW).hom ((f.appLE V W hWV).hom r)
      = i.appTop.hom ((h.appLE V ⊤ hV').hom r) := by
  have hpa : (⊤ : T.Opens) ≤ (a ≫ f) ⁻¹ᵁ V := fun x _ ↦ hWV (hUW (Set.mem_univ x))
  have hpb : (⊤ : T.Opens) ≤ (i ≫ h) ⁻¹ᵁ V := fun x _ ↦ hV' (Set.mem_univ (i.base x))
  have h1 : f.appLE V W hWV ≫ a.appLE W ⊤ hUW = (a ≫ f).appLE V ⊤ hpa :=
    Scheme.Hom.appLE_comp_appLE a f V W ⊤ hWV hUW
  have h3 := h1.trans ((appLE_congr hcomm hpa hpb).trans
    (appLE_comp_appTop_of_comp i h hV' hpb).symm)
  simpa using congr($(h3).hom r)

/-- The action of `Γ(S, V)` on the conormal module through the chart is the action of the image
of the section under `h`. -/
theorem moduleOfAppLEBase_smul_ker (hcomm : a ≫ f = i ≫ h) (r : Γ(S, V))
    (y : RingHom.ker i.appTop.hom) :
    letI := thickeningKerModule hi
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    r • y = (h.appLE V ⊤ hV').hom r • y := by
  let := thickeningKerModule hi
  let := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  show ((f.appLE V W hWV ≫ a.appLE W ⊤ hUW).hom r) • y = _
  rw [CommRingCat.comp_apply, appLE_base_comm f hWV hUW hV' hcomm r,
    thickeningKerModule_smul hi]

/-- The action of `Γ(X, W)` on the conormal module through `a` is the action of the image of the
section under any solution of the lifting problem. -/
theorem moduleOfAppLE_smul_ker {b : T' ⟶ X} (hba : i ≫ b = a)
    (hb : (⊤ : T'.Opens) ≤ b ⁻¹ᵁ W) (x : Γ(X, W)) (y : RingHom.ker i.appTop.hom) :
    letI := thickeningKerModule hi
    letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
    x • y = (b.appLE W ⊤ hb).hom x • y := by
  let := thickeningKerModule hi
  let := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
  show ((a.appLE W ⊤ hUW).hom x) • y = _
  rw [← congr($(appLE_appTop_of_lift hba hb hUW).hom x), CommRingCat.comp_apply,
    thickeningKerModule_smul hi]

variable {b₁ b₂ : T' ⟶ X}

/-- The difference of two solutions of one lifting problem in a chart, as a `Γ(S, V)`-linear map
into the conormal module. This is the underlying linear map of
`Stacks.Smooth.liftDiffDerivation`. -/
noncomputable def liftDiffLinearMap (hcomm : a ≫ f = i ≫ h) (hb₁f : b₁ ≫ f = h)
    (hb₂f : b₂ ≫ f = h) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a)
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := thickeningKerModule hi
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    Γ(X, W) →ₗ[Γ(S, V)] RingHom.ker i.appTop.hom :=
  letI := algebraAppLE f hWV
  letI := thickeningKerModule hi
  letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  { toFun := fun x ↦ ⟨_, sub_appLE_mem_ker hUW hb₁a hb₂a hb₁ hb₂ x⟩
    map_add' := fun x y ↦ Subtype.ext (by
      simp only [Submodule.coe_add, map_add]
      ring)
    map_smul' := fun r x ↦ Subtype.ext (by
      have h1 := congr($(appLE_comp_appLE_of_lift f hb₁f hWV hb₁ hV').hom r)
      have h2 := congr($(appLE_comp_appLE_of_lift f hb₂f hWV hb₂ hV').hom r)
      simp only [CommRingCat.comp_apply] at h1 h2
      change (b₁.appLE W ⊤ hb₁).hom (r • x) - (b₂.appLE W ⊤ hb₂).hom (r • x)
        = ((r • (⟨_, sub_appLE_mem_ker hUW hb₁a hb₂a hb₁ hb₂ x⟩ : RingHom.ker i.appTop.hom) :
            RingHom.ker i.appTop.hom) : Γ(T', ⊤))
      rw [moduleOfAppLEBase_smul_ker f hi hWV hUW hV' hcomm]
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, map_mul, h1, h2]
      simp only [SetLike.val_smul, smul_eq_mul]
      ring) }

/-- The value of `Stacks.Smooth.liftDiffLinearMap`. -/
theorem liftDiffLinearMap_apply (hcomm : a ≫ f = i ≫ h) (hb₁f : b₁ ≫ f = h)
    (hb₂f : b₂ ≫ f = h) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a)
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W) (x : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := thickeningKerModule hi
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    ((liftDiffLinearMap f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ x :
        RingHom.ker i.appTop.hom) : Γ(T', (⊤ : T'.Opens)))
      = (b₁.appLE W ⊤ hb₁).hom x - (b₂.appLE W ⊤ hb₂).hom x :=
  rfl

/-- **The difference of two solutions of a lifting problem in a chart is a derivation.** Let
`i : T ⟶ T'` be a first-order thickening with `T'` affine and let `a : T ⟶ X`, `h : T' ⟶ S`
present a lifting problem for `f : X ⟶ S`, with `a` mapping into `W` and `h` into `V`. Two
solutions both mapping into `W` differ by a `Γ(S, V)`-derivation of `Γ(X, W)` with values in the
conormal module of the thickening.

The module structures are exactly the ones that
`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module` consumes, so for `V` and `W`
affine and `T` affine this derivation corresponds to a unique `Γ(T, ⊤)`-linear map
`Γ(a^*Ω_{X/S}, ⊤) ⟶ 𝒞_{T/T'}` — the chart-independent description of the difference that step (II)
of [Stacks Project, Tag 02H6] needs. -/
noncomputable def liftDiffDerivation (hcomm : a ≫ f = i ≫ h) (hb₁f : b₁ ≫ f = h)
    (hb₂f : b₂ ≫ f = h) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a)
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := thickeningKerModule hi
    letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    Derivation Γ(S, V) Γ(X, W) (RingHom.ker i.appTop.hom) :=
  letI := algebraAppLE f hWV
  letI := thickeningKerModule hi
  letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
  letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  { liftDiffLinearMap f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ with
    map_one_eq_zero' := Subtype.ext (by
      rw [liftDiffLinearMap_apply, map_one, map_one, sub_self]
      rfl)
    leibniz' := fun x y ↦ Subtype.ext (by
      rw [Submodule.coe_add,
        moduleOfAppLE_smul_ker hi hUW hb₂a hb₂ x
          (liftDiffLinearMap f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ y),
        moduleOfAppLE_smul_ker hi hUW hb₂a hb₂ y
          (liftDiffLinearMap f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ x)]
      have hz := mul_sub_appLE_eq_zero hi hUW hb₁a hb₂a hb₁ hb₂ x y
      simp only [SetLike.val_smul, smul_eq_mul, liftDiffLinearMap_apply, map_mul]
      linear_combination hz) }

/-- The value of `Stacks.Smooth.liftDiffDerivation`. -/
theorem liftDiffDerivation_apply (hcomm : a ≫ f = i ≫ h) (hb₁f : b₁ ≫ f = h)
    (hb₂f : b₂ ≫ f = h) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a)
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W) (x : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := thickeningKerModule hi
    letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    ((liftDiffDerivation f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ x :
        RingHom.ker i.appTop.hom) : Γ(T', (⊤ : T'.Opens)))
      = (b₁.appLE W ⊤ hb₁).hom x - (b₂.appLE W ⊤ hb₂).hom x :=
  rfl

/-- The ring map obtained by adding a derivation with values in the conormal module to the
sections of a solution of the lifting problem. -/
noncomputable def addDerivationHom
    (δ : letI := algebraAppLE f hWV
      letI := thickeningKerModule hi
      letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
      letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
      letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
      Derivation Γ(S, V) Γ(X, W) (RingHom.ker i.appTop.hom))
    (hb₂a : i ≫ b₂ = a) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W) :
    Γ(X, W) ⟶ Γ(T', (⊤ : T'.Opens)) :=
  letI := algebraAppLE f hWV
  letI := thickeningKerModule hi
  letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
  letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  CommRingCat.ofHom
    { toFun := fun x ↦ (b₂.appLE W ⊤ hb₂).hom x + δ x
      map_one' := by rw [map_one, δ.map_one_eq_zero, Submodule.coe_zero, add_zero]
      map_mul' := fun x y ↦ by
        have hz : ((δ x : RingHom.ker i.appTop.hom) : Γ(T', (⊤ : T'.Opens))) *
            ((δ y : RingHom.ker i.appTop.hom) : Γ(T', (⊤ : T'.Opens))) = 0 := by
          have hm : ((δ x : RingHom.ker i.appTop.hom) : Γ(T', (⊤ : T'.Opens))) *
              ((δ y : RingHom.ker i.appTop.hom) : Γ(T', (⊤ : T'.Opens)))
              ∈ RingHom.ker i.appTop.hom ^ 2 := by
            rw [pow_two]; exact Ideal.mul_mem_mul (δ x).2 (δ y).2
          rw [ker_appTop_sq_eq_bot hi] at hm
          simpa using hm
        rw [map_mul, δ.leibniz, Submodule.coe_add,
          moduleOfAppLE_smul_ker hi hUW hb₂a hb₂ x (δ y),
          moduleOfAppLE_smul_ker hi hUW hb₂a hb₂ y (δ x)]
        simp only [SetLike.val_smul, smul_eq_mul]
        linear_combination -hz
      map_zero' := by rw [map_zero, map_zero, Submodule.coe_zero, add_zero]
      map_add' := fun x y ↦ by rw [map_add, map_add, Submodule.coe_add]; ring }

/-- The value of `Stacks.Smooth.addDerivationHom`. -/
theorem addDerivationHom_apply
    (δ : letI := algebraAppLE f hWV
      letI := thickeningKerModule hi
      letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
      letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
      letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
      Derivation Γ(S, V) Γ(X, W) (RingHom.ker i.appTop.hom))
    (hb₂a : i ≫ b₂ = a) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W) (x : Γ(X, W)) :
    (addDerivationHom f hi hWV hUW δ hb₂a hb₂).hom x
      = (b₂.appLE W ⊤ hb₂).hom x + δ x :=
  rfl

/-- **The derivations act transitively on the solutions of a lifting problem in a chart.** Let
`V` be an affine open of `S` and `W` an affine open of `X` with `W ≤ f ⁻¹ᵁ V`, let `i : T ⟶ T'` be
a first-order thickening with `T'` affine, and let `b₂` be a solution of the lifting problem
mapping into `W`. For every `Γ(S, V)`-derivation `δ` of `Γ(X, W)` with values in the conormal
module there is another solution `b` mapping into `W` whose difference with `b₂` is `δ`.

Together with `Stacks.Smooth.liftDiffDerivation` and the freeness of the action — two solutions
with the same sections are equal, by `Stacks.Smooth.hom_ext_of_appLE` — this exhibits the
solutions of the lifting problem in a chart as a torsor under those derivations. -/
@[ega "IV 16.5.14" "Affine chart"]
theorem exists_lift_of_derivation (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hcomm : a ≫ f = i ≫ h)
    (δ : letI := algebraAppLE f hWV
      letI := thickeningKerModule hi
      letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
      letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
      letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
      Derivation Γ(S, V) Γ(X, W) (RingHom.ker i.appTop.hom))
    (hb₂f : b₂ ≫ f = h) (hb₂a : i ≫ b₂ = a) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := thickeningKerModule hi
    letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    ∃ (b : T' ⟶ X) (hb : (⊤ : T'.Opens) ≤ b ⁻¹ᵁ W) (hbf : b ≫ f = h) (hba : i ≫ b = a),
      liftDiffDerivation f hi hWV hUW hV' hcomm hbf hb₂f hba hb₂a hb hb₂ = δ := by
  let := algebraAppLE f hWV
  let := thickeningKerModule hi
  let := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
  let := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  let := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  have hφf : f.appLE V W hWV ≫ addDerivationHom f hi hWV hUW δ hb₂a hb₂
      = h.appLE V ⊤ hV' := by
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    rw [CommRingCat.hom_comp, RingHom.comp_apply, addDerivationHom_apply]
    have hd : δ ((f.appLE V W hWV).hom r) = 0 := by
      rw [← RingHom.algebraMap_toAlgebra (f.appLE V W hWV).hom]
      exact δ.map_algebraMap r
    rw [hd, Submodule.coe_zero, add_zero,
      ← CommRingCat.comp_apply, appLE_comp_appLE_of_lift f hb₂f hWV hb₂ hV']
  have hφa : addDerivationHom f hi hWV hUW δ hb₂a hb₂ ≫ i.appTop = a.appLE W ⊤ hUW := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    rw [CommRingCat.hom_comp, RingHom.comp_apply, addDerivationHom_apply, map_add,
      RingHom.mem_ker.mp (δ x).2, add_zero, ← CommRingCat.comp_apply,
      appLE_appTop_of_lift hb₂a hb₂ hUW]
  obtain ⟨b, hb, hbf, hba, hbφ⟩ := exists_lift_of_algHom f hV hW hWV hUW hV' _ hφf hφa
  refine ⟨b, hb, hbf, hba, Derivation.ext fun x ↦ Subtype.ext ?_⟩
  rw [liftDiffDerivation_apply, hbφ, addDerivationHom_apply]
  ring

end Conormal

end Lift

end Stacks.Smooth

end
