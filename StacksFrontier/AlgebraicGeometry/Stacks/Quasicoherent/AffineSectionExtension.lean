module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineMemberBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.QuasicoherentCokernelsAndDirectSums

/-!
# Extending linear maps out of the sections of a quasi-coherent module along affine morphisms

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `ℱ` be a quasi-coherent
module on the associated fppf site of `𝒳` (Stacks 06WG).  For a morphism `n : y ⟶ x` of `𝒳`
between two objects lying over affine schemes, the sections of `ℱ` over `y` are the base change
of the sections over `x`:

```
Γ(y) ⊗_{Γ(x)} ℱ(x) ≅ ℱ(y),   c ⊗ s ↦ c · n^*s.
```

This is the forward direction of Descent, Proposition 03DX, on the slice of `𝒳` at `x`, where
`ℱ` has a global presentation; both inputs are already in the library
(`AlgebraicGeometry.FibredSite.hasGlobalPresentation_over_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation`).  This file
draws the two consequences used to construct morphisms out of `ℱ` section by section:

* the sections over `y` are generated over `Γ(y)` by the restrictions of the sections over `x`,
  so two semilinear maps out of `ℱ(y)` agreeing on those restrictions are equal; and
* a `Γ(x)`-linear map `θ : ℱ(x) ⟶ N` into a `Γ(y)`-module extends uniquely to a `Γ(y)`-linear
  map `ℱ(y) ⟶ N` sending `n^*s` to `θ(s)`.

The extension is compatible with further restriction and with composition of the morphism along
which one extends.

## Main definitions

* `AlgebraicGeometry.FibredSite.objRing`, `AlgebraicGeometry.FibredSite.objModule` and
  `AlgebraicGeometry.FibredSite.objAlgebra`: the commutative ring of global functions of the
  scheme underlying an object of `𝒳`, the sections of a module over an object as a module over
  it, and the algebra structure along a morphism of `𝒳`.
* `AlgebraicGeometry.FibredSite.extendAlong`: the extension of a linear map out of `ℱ(x)` to a
  linear map out of `ℱ(y)`.

## Main results

* `AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_eq_restriction`: the base change
  comparison of the restriction map along a morphism between affine objects is bijective.
* `AlgebraicGeometry.FibredSite.semilinearMap_ext_of_restriction`: semilinear maps out of the
  sections over `y` are determined by their values on restrictions of sections over `x`.
* `AlgebraicGeometry.FibredSite.extendAlong_map`, `AlgebraicGeometry.FibredSite.map_extendAlong`
  and `AlgebraicGeometry.FibredSite.extendAlong_comp`: the extension sends `n^*s` to `θ(s)`, is
  compatible with restriction, and with composition.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The commutative ring of global functions on the scheme underlying an object of `𝒳`.  It is the
ring of sections of the structure sheaf of `𝒳` at that object. -/
abbrev objRing (x : 𝒳) : Type u := Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)

/-- The sections of a module on the associated fppf site of `𝒳` over an object, as a module over
the ring of global functions of the scheme underlying that object. -/
abbrev objModule (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (x : 𝒳) : Module (objRing B S hS p x) (M.val.obj (op x)) :=
  inferInstanceAs (Module ((ringStructureSheafCore B S hS p hp .fppf).obj.obj (op x))
    (M.val.obj (op x)))

/-- The algebra structure along a morphism `n : y ⟶ x` of `𝒳`: pullback of global functions along
the underlying morphism of schemes. -/
abbrev objAlgebra {x y : 𝒳} (n : y ⟶ x) : Algebra (objRing B S hS p x) (objRing B S hS p y) :=
  RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map (p.map n)).appTop.hom

variable {B S hS p hp}

variable (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
  (hM : M.IsQuasicoherentOnSite) {x y : 𝒳} (n : y ⟶ x)
  (hx : IsAffineOver B S hS (p.obj x)) (hy : IsAffineOver B S hS (p.obj y))

/-- The restriction map of a module along a morphism `n : y ⟶ x` of `𝒳`, as a linear map over the
ring of global functions of `x`. -/
noncomputable def restrictionLinear :
    letI := objModule B S hS p hp M x
    letI := objModule B S hS p hp M y
    letI := objAlgebra B S hS p n
    letI : Module (objRing B S hS p x) (M.val.obj (op y)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
    M.val.obj (op x) →ₗ[objRing B S hS p x] M.val.obj (op y) :=
  letI := objModule B S hS p hp M x
  letI := objModule B S hS p hp M y
  letI := objAlgebra B S hS p n
  letI : Module (objRing B S hS p x) (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  { toFun := fun s => M.val.map n.op s
    map_add' := map_add (M.val.map n.op).hom
    map_smul' := fun c s => M.val.map_smul n.op c s }

include hM hx hy in
/-- **The sections over `y` are the base change of the sections over `x`.**  For a morphism
`n : y ⟶ x` between objects of `𝒳` lying over affine schemes, the comparison
`Γ(y) ⊗_{Γ(x)} ℱ(x) ⟶ ℱ(y)` of any linear map agreeing with the restriction is bijective.  This is
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation` on the slice at
`x`, where a quasi-coherent module has a global presentation. -/
theorem bijective_liftBaseChange_of_eq_restriction :
    letI := objModule B S hS p hp M x
    letI := objModule B S hS p hp M y
    letI := objAlgebra B S hS p n
    letI : Module (objRing B S hS p x) (M.val.obj (op y)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
    haveI : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (M.val.obj (op y)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∀ (r : M.val.obj (op x) →ₗ[objRing B S hS p x] M.val.obj (op y)),
      (∀ s, r s = M.val.map n.op s) → Function.Bijective (r.liftBaseChange (objRing B S hS p y)) :=
          by
  intro r hr
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp M y
  let := objAlgebra B S hS p n
  let : Module (objRing B S hS p x) (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (M.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let i2 : Module (objRing B S hS p y) ((M.over x).val.obj (op (Over.mk n))) :=
    objModule B S hS p hp M y
  let i3 : Module (objRing B S hS p x) ((M.over x).val.obj (op (Over.mk n))) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  have i4 : IsScalarTower (objRing B S hS p x) (objRing B S hS p y)
      ((M.over x).val.obj (op (Over.mk n))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact @bijective_liftBaseChange_of_hasGlobalPresentation B S hS 𝒳 _ p hp x (M.over x)
    (hasGlobalPresentation_over_of_isQuasicoherentOnSite B S hS p hp M hM ⟨x, hx⟩)
    (Over.mk (𝟙 x)) (Over.mk n)
    (Over.homMk n : (Over.mk n : Over x) ⟶ Over.mk (𝟙 x)) hx hy
    (objRing B S hS p x) (objRing B S hS p y) _ _ (objAlgebra B S hS p n)
    (objModule B S hS p hp M x) i3 i2 i4
    (RingEquiv.refl _) (fun _ _ => rfl) (RingEquiv.refl _) (fun _ _ => rfl) (fun _ => rfl) r
    fun s => (hr s).trans rfl

include hM hx hy in
/-- **The sections over `y` are generated by the restrictions of the sections over `x`.** -/
theorem mem_span_range_restriction (t : M.val.obj (op y)) :
    letI := objModule B S hS p hp M y
    t ∈ Submodule.span (objRing B S hS p y)
      (Set.range (M.val.restrictₛₗ n.op)) := by
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp M y
  let := objAlgebra B S hS p n
  let : Module (objRing B S hS p x) (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (M.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨q, rfl⟩ := (bijective_liftBaseChange_of_eq_restriction M hM n hx hy
    (restrictionLinear M n) fun _ => rfl).2 t
  induction q using TensorProduct.inductionOn with
  | tmul c s =>
    rw [LinearMap.liftBaseChange_tmul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨s, rfl⟩)
  | add a b ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb

include hM hx hy in
/-- The restrictions of the sections over `x` span the sections over `y`. -/
theorem span_range_restrictₛₗ_eq_top :
    letI := objModule B S hS p hp M y
    Submodule.span (objRing B S hS p y) (Set.range (M.val.restrictₛₗ n.op)) = ⊤ := by
  let := objModule B S hS p hp M y
  exact Submodule.eq_top_iff'.2 (mem_span_range_restriction M hM n hx hy)

include hM hx hy in
/-- **Semilinear maps out of `ℱ(y)` are determined on restrictions.**  Two semilinear maps out of
the sections over `y` which agree on the restrictions of the sections over `x` are equal. -/
theorem semilinearMap_ext_of_restriction {R' : Type*} [Semiring R'] {Q : Type*} [AddCommMonoid Q]
    [Module R' Q]
    {σ : objRing B S hS p y →+* R'} :
    letI := objModule B S hS p hp M y
    ∀ {θ₁ θ₂ : M.val.obj (op y) →ₛₗ[σ] Q},
      (∀ s, θ₁ (M.val.map n.op s) = θ₂ (M.val.map n.op s)) → θ₁ = θ₂ := by
  let := objModule B S hS p hp M y
  intro θ₁ θ₂ h
  exact LinearMap.ext_on_range (span_range_restrictₛₗ_eq_top M hM n hx hy) h

variable (N : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))

/-- **The extension along a morphism between affine objects.**  A `Γ(x)`-linear map
`θ : ℱ(x) ⟶ 𝒩(y)` extends to the `Γ(y)`-linear map `ℱ(y) ⟶ 𝒩(y)` which is `θ` composed with
the inverse of the base change isomorphism `Γ(y) ⊗_{Γ(x)} ℱ(x) ≅ ℱ(y)`. -/
noncomputable def extendAlong :
    letI := objModule B S hS p hp M x
    letI := objModule B S hS p hp N y
    letI := objAlgebra B S hS p n
    letI : Module (objRing B S hS p x) (N.val.obj (op y)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
    (M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op y)) →
      letI := objModule B S hS p hp M y
      M.val.obj (op y) →ₗ[objRing B S hS p y] N.val.obj (op y) := fun θ =>
  letI := objModule B S hS p hp M x
  letI := objModule B S hS p hp M y
  letI := objModule B S hS p hp N y
  letI := objAlgebra B S hS p n
  letI : Module (objRing B S hS p x) (N.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  haveI : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (N.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module (objRing B S hS p x) (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  haveI : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (M.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  (θ.liftBaseChange (objRing B S hS p y)).comp
    (LinearEquiv.ofBijective _ (bijective_liftBaseChange_of_eq_restriction M hM n hx hy
      (restrictionLinear M n) (fun _ => rfl))).symm.toLinearMap

/-- The extension sends the restriction `n^*s` of a section over `x` to `θ(s)`. -/
theorem extendAlong_map :
    letI := objModule B S hS p hp M x
    letI := objModule B S hS p hp N y
    letI := objAlgebra B S hS p n
    letI : Module (objRing B S hS p x) (N.val.obj (op y)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
    ∀ (θ : M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op y)) (s : M.val.obj (op x)),
      extendAlong M hM n hx hy N θ (M.val.map n.op s) = θ s := by
  intro θ s
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp M y
  let := objModule B S hS p hp N y
  let := objAlgebra B S hS p n
  let : Module (objRing B S hS p x) (N.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (N.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module (objRing B S hS p x) (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (M.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have h1 : (LinearEquiv.ofBijective _ (bijective_liftBaseChange_of_eq_restriction M hM n hx hy
      (restrictionLinear M n) (fun _ => rfl))).symm (M.val.map n.op s) = 1 ⊗ₜ s := by
    have h0 : ((restrictionLinear M n).liftBaseChange (objRing B S hS p y)) (1 ⊗ₜ s) =
        M.val.map n.op s := by
      rw [LinearMap.liftBaseChange_tmul, one_smul]
      rfl
    exact (congrArg _ h0.symm).trans (LinearEquiv.ofBijective_symm_apply_apply _ _)
  change (θ.liftBaseChange (objRing B S hS p y)) ((LinearEquiv.ofBijective _ _).symm _) = _
  rw [h1, LinearMap.liftBaseChange_tmul, one_smul]

/-- **The extension is compatible with restriction** along a further morphism `k : z ⟶ y` to an
affine object: restricting the extension along `n` is extending, along `k ≫ n`, the restricted
linear map. -/
theorem map_extendAlong {z : 𝒳} (k : z ⟶ y) (hz : IsAffineOver B S hS (p.obj z)) :
    letI := objModule B S hS p hp M x
    letI := objModule B S hS p hp N y
    letI := objModule B S hS p hp N z
    letI := objAlgebra B S hS p n
    letI := objAlgebra B S hS p (k ≫ n)
    letI : Module (objRing B S hS p x) (N.val.obj (op y)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
    letI : Module (objRing B S hS p x) (N.val.obj (op z)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p z))
    ∀ (θ : M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op y))
      (θ' : M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op z)),
      (∀ s, θ' s = N.val.map k.op (θ s)) → ∀ t,
      N.val.map k.op (extendAlong M hM n hx hy N θ t) =
        extendAlong M hM (k ≫ n) hx hz N θ' (M.val.map k.op t) := by
  intro θ θ' hθ t
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp M y
  let := objModule B S hS p hp M z
  let := objModule B S hS p hp N y
  let := objModule B S hS p hp N z
  let := objAlgebra B S hS p n
  let := objAlgebra B S hS p (k ≫ n)
  let : Module (objRing B S hS p x) (N.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  let : Module (objRing B S hS p x) (N.val.obj (op z)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p z))
  let σ : objRing B S hS p y →+* objRing B S hS p z :=
    ((ringStructureSheafCore B S hS p hp .fppf).obj.map k.op).hom
  let E₁ := extendAlong M hM n hx hy N θ
  let E₂ := extendAlong M hM (k ≫ n) hx hz N θ'
  let L₁ : M.val.obj (op y) →ₛₗ[σ] N.val.obj (op z) :=
    { toFun := fun t => N.val.map k.op (E₁ t)
      map_add' := fun a b => (congrArg (N.val.map k.op) (map_add E₁ a b)).trans
        (map_add (N.val.map k.op).hom _ _)
      map_smul' := fun c a => (congrArg (N.val.map k.op) (map_smul E₁ c a)).trans
        (N.val.map_smul k.op c (E₁ a)) }
  let L₂ : M.val.obj (op y) →ₛₗ[σ] N.val.obj (op z) :=
    { toFun := fun t => E₂ (M.val.map k.op t)
      map_add' := fun a b => (congrArg E₂ (map_add (M.val.map k.op).hom a b)).trans
        (map_add E₂ _ _)
      map_smul' := fun c a => (congrArg E₂ (M.val.map_smul k.op c a)).trans
        (map_smul E₂ _ _) }
  refine LinearMap.congr_fun (semilinearMap_ext_of_restriction M hM n hx hy (θ₁ := L₁) (θ₂ := L₂)
    fun s => ?_) t
  change N.val.map k.op (extendAlong M hM n hx hy N θ (M.val.map n.op s)) =
    extendAlong M hM (k ≫ n) hx hz N θ' (M.val.map k.op (M.val.map n.op s))
  rw [extendAlong_map, ← hθ, ← extendAlong_map M hM (k ≫ n) hx hz N θ' s]
  exact congrArg (extendAlong M hM (k ≫ n) hx hz N θ') (M.val.map_comp_apply n.op k.op s)

/-- `AlgebraicGeometry.FibredSite.map_extendAlong`, with the composite morphism given as a
morphism `n'` equal to `k ≫ n`. -/
theorem map_extendAlong' {z : 𝒳} (k : z ⟶ y) (n' : z ⟶ x) (hn' : k ≫ n = n')
    (hz : IsAffineOver B S hS (p.obj z)) :
    letI := objModule B S hS p hp M x
    letI := objModule B S hS p hp N y
    letI := objModule B S hS p hp N z
    letI := objAlgebra B S hS p n
    letI := objAlgebra B S hS p n'
    letI : Module (objRing B S hS p x) (N.val.obj (op y)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
    letI : Module (objRing B S hS p x) (N.val.obj (op z)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p z))
    ∀ (θ : M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op y))
      (θ' : M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op z)),
      (∀ s, θ' s = N.val.map k.op (θ s)) → ∀ t,
      N.val.map k.op (extendAlong M hM n hx hy N θ t) =
        extendAlong M hM n' hx hz N θ' (M.val.map k.op t) := by
  subst hn'
  exact map_extendAlong M hM n hx hy N k hz

/-- **The extension is compatible with composition.**  Extending along `n ≫ c` a linear map
`θ'` out of `ℱ(x')` is extending along `n` the linear map `θ` with `θ' = θ ∘ c^*`. -/
theorem extendAlong_comp {x' : 𝒳} (c : x ⟶ x') (hx' : IsAffineOver B S hS (p.obj x')) :
    letI := objModule B S hS p hp M x
    letI := objModule B S hS p hp M x'
    letI := objModule B S hS p hp N y
    letI := objAlgebra B S hS p n
    letI := objAlgebra B S hS p (n ≫ c)
    letI : Module (objRing B S hS p x) (N.val.obj (op y)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
    letI : Module (objRing B S hS p x') (N.val.obj (op y)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x') (objRing B S hS p y))
    ∀ (θ : M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op y))
      (θ' : M.val.obj (op x') →ₗ[objRing B S hS p x'] N.val.obj (op y)),
      (∀ s, θ' s = θ (M.val.map c.op s)) →
      extendAlong M hM (n ≫ c) hx' hy N θ' = extendAlong M hM n hx hy N θ := by
  intro θ θ' hθ
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp M x'
  let := objModule B S hS p hp M y
  let := objModule B S hS p hp N y
  let := objAlgebra B S hS p n
  let := objAlgebra B S hS p (n ≫ c)
  let : Module (objRing B S hS p x) (N.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  let : Module (objRing B S hS p x') (N.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x') (objRing B S hS p y))
  refine semilinearMap_ext_of_restriction M hM (n ≫ c) hx' hy (fun s => ?_)
  rw [extendAlong_map]
  refine Eq.trans ?_ (congrArg (extendAlong M hM n hx hy N θ)
    (M.val.map_comp_apply c.op n.op s)).symm
  exact (hθ s).trans (extendAlong_map M hM n hx hy N θ _).symm

end AlgebraicGeometry.FibredSite

end
