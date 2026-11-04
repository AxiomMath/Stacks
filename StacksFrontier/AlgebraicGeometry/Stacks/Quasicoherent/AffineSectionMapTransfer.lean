module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSectionExtension
public import StacksFrontier.RingTheory.Flat.BaseChangeDetection

/-!
# Properties of maps of quasi-coherent modules on sections over affine objects

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `φ : ℳ ⟶ 𝒩` be a map of
quasi-coherent modules on the associated fppf site of `𝒳` (Stacks 06WG).  For a morphism
`n : y ⟶ x` of `𝒳` between objects lying over affine schemes, the sections over `y` are the base
change of the sections over `x`
(`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_eq_restriction`, the forward direction
of Descent, Proposition 03DX), compatibly with `φ`; so `φ_y` is the base change of `φ_x`.
This file draws the consequences:

* `φ_y` is surjective, resp. bijective, if `φ_x` is, and injective if `φ_x` is and the morphism
  of schemes underlying `n` is flat;
* conversely, for a family `n k : y k ⟶ x` of morphisms between affine objects whose underlying
  morphisms of schemes are flat and jointly surjective, `φ_x` is injective as soon as every
  `φ_{y k}` is, and a section of `𝒩` over `x` lies in the image of `φ_x` as soon as each of its
  restrictions lies in the image of `φ_{y k}`.

The family in the second item need not be finite, nor its members locally of finite
presentation: the argument works one prime of the ring of global functions on `x` at a time
(`Module.eq_zero_of_forall_one_tmul_eq_zero`).  This is the form in which the source's
"pullback by a jointly surjective family of flat morphisms of schemes reflects injective, resp.
surjective, resp. bijective maps of quasi-coherent modules" (proof of Stacks 0GQF) is used.

## Main results

* `AlgebraicGeometry.FibredSite.injective_app_of_flat`,
  `AlgebraicGeometry.FibredSite.surjective_app_of_hom` and
  `AlgebraicGeometry.FibredSite.bijective_app_of_hom`: the transfer along one morphism.
* `AlgebraicGeometry.FibredSite.injective_app_of_flat_family` and
  `AlgebraicGeometry.FibredSite.mem_range_app_of_flat_family`: the reflection along a flat jointly
  surjective family.
* `AlgebraicGeometry.Scheme.exists_comap_eq_of_jointlySurjective`: a jointly surjective family of
  morphisms of affine schemes is jointly surjective on primes of the rings of global functions.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 0GQF](https://stacks.math.columbia.edu/tag/0GQF)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u v w

namespace AlgebraicGeometry.Scheme

/-- **A jointly surjective family of morphisms of affine schemes is jointly surjective on
primes.**  Every prime of `Γ(X, ⊤)` is the contraction of a prime of some `Γ(Y k, ⊤)` along the
ring map induced by `f k`. -/
theorem exists_comap_eq_of_jointlySurjective {X : Scheme.{u}} [IsAffine X] {K : Type*}
    {Y : K → Scheme.{u}} [∀ k, IsAffine (Y k)] (f : ∀ k, Y k ⟶ X)
    (hf : ∀ t : X, ∃ k, t ∈ Set.range (f k)) (P : PrimeSpectrum Γ(X, ⊤)) :
    ∃ k, ∃ Q : PrimeSpectrum Γ(Y k, ⊤), Q.asIdeal.comap (f k).appTop.hom = P.asIdeal := by
  let P' : Spec Γ(X, ⊤) := P
  obtain ⟨k, s, hs⟩ := hf (X.isoSpec.inv P')
  refine ⟨k, (Y k).isoSpec.hom s, ?_⟩
  have h1 := congrArg (fun g => g s) (Scheme.isoSpec_hom_naturality (f k))
  simp only [Scheme.Hom.comp_apply, hs] at h1
  have h2 : X.isoSpec.hom (X.isoSpec.inv P') = P' := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [h2] at h1
  exact congrArg PrimeSpectrum.asIdeal h1

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}
  {M N : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)}

/-- The ring of global functions on the target of a morphism with flat underlying morphism of
affine schemes is flat over that of its source. -/
theorem flat_objAlgebra {x y : 𝒳} (n : y ⟶ x) (hx : IsAffineOver B S hS (p.obj x))
    (hy : IsAffineOver B S hS (p.obj y))
    (hn : Flat ((BigFppfOver.toScheme B S hS).map (p.map n))) :
    letI := objAlgebra B S hS p n
    Module.Flat (objRing B S hS p x) (objRing B S hS p y) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) := hx
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) := hy
  exact (HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 hn

section Single

variable (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
  {x y : 𝒳} (n : y ⟶ x) (hx : IsAffineOver B S hS (p.obj x))
  (hy : IsAffineOver B S hS (p.obj y))

include hM hN hx hy in
/-- **Flat base change preserves injectivity of a map of quasi-coherent modules on sections.**
If the morphism of affine schemes underlying `n : y ⟶ x` is flat and `φ` is injective on the
sections over `x`, it is injective on the sections over `y`. -/
theorem injective_app_of_flat (hn : Flat ((BigFppfOver.toScheme B S hS).map (p.map n)))
    (hφ : Function.Injective (φ.val.app (op x))) :
    Function.Injective (φ.val.app (op y)) := by
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp N x
  let := objModule B S hS p hp M y
  let := objModule B S hS p hp N y
  let := objAlgebra B S hS p n
  let : Module (objRing B S hS p x) (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  let : Module (objRing B S hS p x) (N.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (M.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (N.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have := flat_objAlgebra n hx hy hn
  let f : M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op x) := (φ.val.app (op x)).hom
  let f' : M.val.obj (op y) →ₗ[objRing B S hS p y] N.val.obj (op y) := (φ.val.app (op y)).hom
  exact LinearMap.injective_of_liftBaseChange_of_flat f f'
    (restrictionLinear M n) (restrictionLinear N n)
    (bijective_liftBaseChange_of_eq_restriction M hM n hx hy _ fun _ => rfl)
    (bijective_liftBaseChange_of_eq_restriction N hN n hx hy _ fun _ => rfl)
    (fun m => PresheafOfModules.naturality_apply φ.val n.op m) hφ

include hM hN n hx hy in
/-- **Base change preserves surjectivity of a map of quasi-coherent modules on sections.** -/
theorem surjective_app_of_hom (hφ : Function.Surjective (φ.val.app (op x))) :
    Function.Surjective (φ.val.app (op y)) := by
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp N x
  let := objModule B S hS p hp M y
  let := objModule B S hS p hp N y
  let := objAlgebra B S hS p n
  let : Module (objRing B S hS p x) (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  let : Module (objRing B S hS p x) (N.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (M.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (N.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op x) := (φ.val.app (op x)).hom
  let f' : M.val.obj (op y) →ₗ[objRing B S hS p y] N.val.obj (op y) := (φ.val.app (op y)).hom
  exact LinearMap.surjective_of_liftBaseChange f f'
    (restrictionLinear M n) (restrictionLinear N n)
    (bijective_liftBaseChange_of_eq_restriction M hM n hx hy _ fun _ => rfl)
    (bijective_liftBaseChange_of_eq_restriction N hN n hx hy _ fun _ => rfl)
    (fun m => PresheafOfModules.naturality_apply φ.val n.op m) hφ

include hM hN n hx hy in
/-- **Base change preserves bijectivity of a map of quasi-coherent modules on sections.** -/
theorem bijective_app_of_hom (hφ : Function.Bijective (φ.val.app (op x))) :
    Function.Bijective (φ.val.app (op y)) := by
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp N x
  let := objModule B S hS p hp M y
  let := objModule B S hS p hp N y
  let := objAlgebra B S hS p n
  let : Module (objRing B S hS p x) (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  let : Module (objRing B S hS p x) (N.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (M.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (N.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op x) := (φ.val.app (op x)).hom
  let f' : M.val.obj (op y) →ₗ[objRing B S hS p y] N.val.obj (op y) := (φ.val.app (op y)).hom
  exact LinearMap.bijective_of_liftBaseChange f f'
    (restrictionLinear M n) (restrictionLinear N n)
    (bijective_liftBaseChange_of_eq_restriction M hM n hx hy _ fun _ => rfl)
    (bijective_liftBaseChange_of_eq_restriction N hN n hx hy _ fun _ => rfl)
    (fun m => PresheafOfModules.naturality_apply φ.val n.op m) hφ

include hM hx hy in
/-- A section over `x` whose restriction to `y` vanishes becomes zero in `Γ(y) ⊗_{Γ(x)} ℳ(x)`. -/
theorem one_tmul_eq_zero_of_map_eq_zero {s : M.val.obj (op x)} (hs : M.val.map n.op s = 0) :
    letI := objModule B S hS p hp M x
    letI := objAlgebra B S hS p n
    (1 : objRing B S hS p y) ⊗ₜ[objRing B S hS p x] s = 0 := by
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp M y
  let := objAlgebra B S hS p n
  let : Module (objRing B S hS p x) (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (M.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact LinearMap.one_tmul_eq_zero_of_liftBaseChange (restrictionLinear M n)
    (bijective_liftBaseChange_of_eq_restriction M hM n hx hy _ fun _ => rfl) hs

include hM hN hx hy in
/-- A section over `x` whose restriction to `y` lies in the image of `φ_y` becomes zero in
`Γ(y) ⊗_{Γ(x)} coker φ_x`; here `f` is `φ_x` read as a `Γ(x)`-linear map. -/
theorem one_tmul_mkQ_eq_zero_of_map_mem_range
    (f : letI := objModule B S hS p hp M x
      letI := objModule B S hS p hp N x
      M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op x))
    (hf : ∀ s, f s = φ.val.app (op x) s) {t : N.val.obj (op x)}
    (ht : N.val.map n.op t ∈ Set.range (φ.val.app (op y))) :
    letI := objModule B S hS p hp M x
    letI := objModule B S hS p hp N x
    letI := objAlgebra B S hS p n
    (1 : objRing B S hS p y) ⊗ₜ[objRing B S hS p x] (LinearMap.range f).mkQ t = 0 := by
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp N x
  let := objModule B S hS p hp M y
  let := objModule B S hS p hp N y
  let := objAlgebra B S hS p n
  let : Module (objRing B S hS p x) (M.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  let : Module (objRing B S hS p x) (N.val.obj (op y)) :=
    Module.compHom _ (algebraMap (objRing B S hS p x) (objRing B S hS p y))
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (M.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (objRing B S hS p x) (objRing B S hS p y) (N.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨c, hc⟩ := ht
  let f' : M.val.obj (op y) →ₗ[objRing B S hS p y] N.val.obj (op y) := (φ.val.app (op y)).hom
  exact LinearMap.one_tmul_mkQ_eq_zero_of_liftBaseChange f f'
    (restrictionLinear M n) (restrictionLinear N n)
    (bijective_liftBaseChange_of_eq_restriction M hM n hx hy _ fun _ => rfl)
    (bijective_liftBaseChange_of_eq_restriction N hN n hx hy _ fun _ => rfl)
    (fun m => by rw [hf]; exact PresheafOfModules.naturality_apply φ.val n.op m) ⟨c, hc⟩

end Single

section Family

variable (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
  {x : 𝒳} (hx : IsAffineOver B S hS (p.obj x)) {K : Type*} {y : K → 𝒳} (n : ∀ k, y k ⟶ x)
  (hy : ∀ k, IsAffineOver B S hS (p.obj (y k)))
  (hflat : ∀ k, Flat ((BigFppfOver.toScheme B S hS).map (p.map (n k))))
  (hjs : ∀ t : (BigFppfOver.toScheme B S hS).obj (p.obj x),
    ∃ k, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p.map (n k))))

include hM hx hy hflat hjs in
/-- **A section vanishing on a flat jointly surjective family of affine objects vanishes.** -/
theorem eq_zero_of_map_eq_zero_of_flat_family {s : M.val.obj (op x)}
    (hs : ∀ k, M.val.map (n k).op s = 0) : s = 0 := by
  let := objModule B S hS p hp M x
  let : ∀ k, Algebra (objRing B S hS p x) (objRing B S hS p (y k)) :=
    fun k => objAlgebra B S hS p (n k)
  have : ∀ k, Module.Flat (objRing B S hS p x) (objRing B S hS p (y k)) :=
    fun k => flat_objAlgebra (n k) hx (hy k) (hflat k)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) := hx
  have : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y k))) := hy
  exact Module.eq_zero_of_forall_one_tmul_eq_zero (fun k => objRing B S hS p (y k))
    (Scheme.exists_comap_eq_of_jointlySurjective _ hjs)
    (fun k => one_tmul_eq_zero_of_map_eq_zero hM (n k) hx (hy k) (hs k))

include hM hN hx hy hflat hjs in
/-- **Injectivity is reflected by a flat jointly surjective family of affine objects.** -/
theorem injective_app_of_flat_family (hφ : ∀ k, Function.Injective (φ.val.app (op (y k)))) :
    Function.Injective (φ.val.app (op x)) := by
  rw [← LinearMap.ker_eq_bot (f := (φ.val.app (op x)).hom), LinearMap.ker_eq_bot']
  intro s hs
  refine eq_zero_of_map_eq_zero_of_flat_family hM hx n hy hflat hjs fun k => hφ k ?_
  have h1 := PresheafOfModules.naturality_apply φ.val (n k).op s
  have h2 : φ.val.app (op x) s = 0 := hs
  rw [h2, map_zero] at h1
  exact h1.trans (map_zero _).symm

include hM hN hx hy hflat hjs in
/-- **Surjectivity is reflected by a flat jointly surjective family of affine objects,** section
by section: a section of `𝒩` over `x` whose restrictions to the members lie in the images of
`φ` there lies in the image of `φ_x`. -/
theorem mem_range_app_of_flat_family {t : N.val.obj (op x)}
    (ht : ∀ k, N.val.map (n k).op t ∈ Set.range (φ.val.app (op (y k)))) :
    t ∈ Set.range (φ.val.app (op x)) := by
  let := objModule B S hS p hp M x
  let := objModule B S hS p hp N x
  let : ∀ k, Algebra (objRing B S hS p x) (objRing B S hS p (y k)) :=
    fun k => objAlgebra B S hS p (n k)
  have : ∀ k, Module.Flat (objRing B S hS p x) (objRing B S hS p (y k)) :=
    fun k => flat_objAlgebra (n k) hx (hy k) (hflat k)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) := hx
  have : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y k))) := hy
  let f : M.val.obj (op x) →ₗ[objRing B S hS p x] N.val.obj (op x) := (φ.val.app (op x)).hom
  have h0 := Module.eq_zero_of_forall_one_tmul_eq_zero (fun k => objRing B S hS p (y k))
    (Scheme.exists_comap_eq_of_jointlySurjective _ hjs)
    (fun k => one_tmul_mkQ_eq_zero_of_map_mem_range hM hN φ (n k) hx (hy k) f
      (fun _ => rfl) (ht k))
  exact (Submodule.Quotient.mk_eq_zero _).1 h0

include hM hN hx hy hflat hjs in
/-- **Surjectivity is reflected by a flat jointly surjective family of affine objects.** -/
theorem surjective_app_of_flat_family (hφ : ∀ k, Function.Surjective (φ.val.app (op (y k)))) :
    Function.Surjective (φ.val.app (op x)) := fun _ =>
  mem_range_app_of_flat_family hM hN φ hx n hy hflat hjs fun k => hφ k _

end Family

end AlgebraicGeometry.FibredSite

end
