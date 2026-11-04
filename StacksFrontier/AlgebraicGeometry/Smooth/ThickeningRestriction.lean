module

public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentAffineDerivations
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmooth

/-!
# The conormal module of an affine first-order thickening, and restriction to a basic open

Let `i : T ⟶ T'` be a first-order thickening of schemes with `T'` affine. Writing
`A' = Γ(T', ⊤)` and `A = Γ(T, ⊤)`, the map `i.appTop : A' ⟶ A` is a surjection whose kernel
`I` is square-zero, so that `I` — the *conormal module* `𝒞_{T/T'}` of the thickening — is a
module not merely over `A'` but over `A`. This file provides that module structure and the
two further ingredients that step (II) of the proof of [Stacks Project, Tag 02H6] needs before
the Čech argument can start:

* the chart-independent description of derivations of `Stacks.Smooth`, restated for an arbitrary
  module over `Γ(T, ⊤)` rather than for the global sections of a sheaf of modules, so that it
  applies to the conormal module; and
* the restriction of the thickening to a basic open of `T'`, which is again a first-order
  thickening of affine schemes, with its closed subscheme the matching basic open of `T`.

## Main definitions

* `Stacks.Smooth.kerModule` is the module structure over the quotient on the square-zero kernel
  of a surjection of commutative rings, and `Stacks.Smooth.kerModuleOfRingHom` is its restriction
  of scalars along a ring map into the quotient.
* `Stacks.Smooth.kerEquivPi` reads a finite basis of that module as a presentation of the kernel
  as a module of tuples, linear over the ring acting through the surjection, and
  `Stacks.Smooth.kerAddEquivOfRingEquiv`, `Stacks.Smooth.kerEquivPiOfRingEquiv` transport such a
  presentation along ring isomorphisms of the source and the target.
* `Stacks.Smooth.kerEquivQuotientOfLinearEquiv` upgrades an identification of the conormal
  module with the quotient from linearity over the ring to linearity over the quotient.
* `Stacks.Smooth.moduleOfAppLE` and `Stacks.Smooth.moduleOfAppLEBase` are the analogues of
  `Stacks.Smooth.moduleAppLE` and `Stacks.Smooth.moduleAppLEBase` for a bare module over
  `Γ(T, U)` instead of the sections of a sheaf of modules.

## Main results

* `Stacks.Smooth.kerModule_smul`: the action of the quotient on the square-zero kernel is the
  action of the ring, read through any preimage.
* `Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module`: for `V` an affine open of `S`,
  `W` an affine open of `X` with `W ≤ f ⁻¹ᵁ V`, `T` affine and `a : T ⟶ X` mapping into `W`,
  every `Γ(S, V)`-derivation of `Γ(X, W)` with values in a `Γ(T, ⊤)`-module `M` is induced by
  exactly one `Γ(T, ⊤)`-linear map `Γ(a^*Ω_{X/S}, ⊤) ⟶ M`.
* `Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening` and
  `Stacks.Smooth.ker_appTop_sq_eq_bot`: the ring-level presentation of an affine first-order
  thickening as a surjection with square-zero kernel.
* `Stacks.Smooth.preimage_basicOpen_appTop`: the closed subscheme of the thickening restricted to
  a basic open `D(g)` of `T'` is the basic open of `T` cut out by the image of `g`.
* `Stacks.Smooth.isFirstOrderThickening_basicOpen`: the restriction of a first-order thickening
  to a basic open of `T'` is a first-order thickening, and
  `Stacks.Smooth.isAffine_basicOpen_of_isFirstOrderThickening` records that both of its schemes
  are affine.

## Implementation notes

The module structure on the kernel is built in two steps. A square-zero ideal `I` of `A'` is
annihilated by itself, so `Module.IsTorsionBySet.module` makes it a module over `A' ⧸ I`;
composing with the ring isomorphism `A ≃ A' ⧸ RingHom.ker π` of
`RingHom.quotientKerEquivOfSurjective` transports that to a module over `A`. Taking the ideal to
be literally `RingHom.ker π`, rather than an ideal assumed equal to it, is what keeps the second
step free of transport along an equality of ideals.

`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module` is deduced from
`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD` by presenting `M` as the global sections of
a sheaf of modules with `Stacks.Modules.exists_modules_globalSections`; the derivation is carried
across by `LinearMap.compDer`, which is legitimate because the `Γ(X, W)`-module structures on
both sides are restrictions of scalars of the `Γ(T, ⊤)`-module structures along the same ring
map, so a `Γ(T, ⊤)`-linear map between them is automatically `Γ(X, W)`-linear.

For the restriction to a basic open nothing new is needed beyond
`Stacks.Smooth.isFirstOrderThickening_morphismRestrict`: the identification of the preimage of
`D(g)` is `AlgebraicGeometry.Scheme.preimage_basicOpen_top`, and affineness of the two schemes
follows from `AlgebraicGeometry.IsAffineOpen.basicOpen` on `T'` and, on `T`, from the fact that
a closed subscheme of an affine scheme is affine.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

universe u

namespace Stacks.Smooth

/-! ### The square-zero kernel of a surjection as a module over the quotient -/

section Ker

variable {A A' : Type u} [CommRing A] [CommRing A'] {π : A' →+* A}

/-- A square-zero ideal is annihilated by itself, hence is a module over the quotient ring. This
is the auxiliary step towards `Stacks.Smooth.kerModule`. -/
@[instance_reducible]
noncomputable def kerQuotModule (h2 : RingHom.ker π ^ 2 = ⊥) :
    Module (A' ⧸ RingHom.ker π) (RingHom.ker π) :=
  Module.IsTorsionBySet.module (R := A') (M := (RingHom.ker π)) (I := RingHom.ker π) fun x a ↦ by
    have hm : (a : A') * (x : A') ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul a.2 x.2
    rw [h2] at hm
    ext
    simpa using hm

/-- **The conormal module of a square-zero extension.** For `π : A' →+* A` a surjection of
commutative rings whose kernel is square-zero, the kernel is a module over `A`: the action of
`A'` on it factors through `π`. -/
@[instance_reducible]
noncomputable def kerModule (hπ : Function.Surjective π) (h2 : RingHom.ker π ^ 2 = ⊥) :
    Module A (RingHom.ker π) :=
  letI := kerQuotModule h2
  Module.compHom _ (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom

/-- The defining property of `Stacks.Smooth.kerModule`: the element `π x` of `A` acts on the
kernel as `x` does. -/
theorem kerModule_smul (hπ : Function.Surjective π) (h2 : RingHom.ker π ^ 2 = ⊥) (x : A')
    (y : RingHom.ker π) :
    letI := kerModule hπ h2
    π x • y = x • y := by
  let := kerQuotModule h2
  show ((RingHom.quotientKerEquivOfSurjective hπ).symm (π x)) • y = x • y
  have h : (RingHom.quotientKerEquivOfSurjective hπ).symm (π x) = Ideal.Quotient.mk _ x := by
    rw [RingEquiv.symm_apply_eq]; rfl
  rw [h]; rfl

/-- The module structure over a further ring `B` on the square-zero kernel of `π : A' →+* A`
obtained by restricting `Stacks.Smooth.kerModule` along a ring map `β : B →+* A`. -/
@[instance_reducible]
noncomputable def kerModuleOfRingHom {B : Type u} [CommRing B] (hπ : Function.Surjective π)
    (h2 : RingHom.ker π ^ 2 = ⊥) (β : B →+* A) : Module B (RingHom.ker π) :=
  letI := kerModule hπ h2
  Module.compHom _ β

/-- The action of `B` on the square-zero kernel of `π` through `β : B →+* A` is the action of
any preimage in `A'` of the image under `β`. -/
theorem kerModuleOfRingHom_smul {B : Type u} [CommRing B] (hπ : Function.Surjective π)
    (h2 : RingHom.ker π ^ 2 = ⊥) (β : B →+* A) (b : B) (x : A') (hx : π x = β b)
    (y : RingHom.ker π) :
    letI := kerModuleOfRingHom hπ h2 β
    b • y = x • y := by
  let := kerModule hπ h2
  show β b • y = x • y
  rw [← hx, kerModule_smul hπ h2]

/-- **A basis of the conormal module over the quotient trivialises it over the ring.** Let
`π : A' →+* A` carry a module structure over `A` on its kernel whose restriction of scalars
along `π` is the kernel's own `A'`-module structure as an ideal; for a surjection with
square-zero kernel that structure is `Stacks.Smooth.kerModule` and the compatibility is
`Stacks.Smooth.kerModule_smul`. A finite `A`-basis of the kernel then presents it as the module
of tuples `ι → A`, and the presentation is `A'`-linear for the action of `A'` on the tuples
through `π`.

The hypothesis `hsmul` is what makes the two scalar actions a tower, so that the `A`-linear
`Module.Basis.equivFun` of the basis restricts to an `A'`-linear equivalence. -/
noncomputable def kerEquivPi [Module A (RingHom.ker π)]
    (hsmul : ∀ (a : A') (x : RingHom.ker π), π a • x = a • x)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A (RingHom.ker π)) :
    letI := π.toAlgebra
    RingHom.ker π ≃ₗ[A'] (ι → A) :=
  letI := π.toAlgebra
  haveI : IsScalarTower A' A (RingHom.ker π) := IsScalarTower.of_algebraMap_smul hsmul
  b.equivFun.restrictScalars A'

/-- **An `A'`-linear identification of the conormal module with the quotient is `A`-linear.**
Both `A` and the square-zero kernel of a surjection `π : A' →+* A` carry `A'`-actions that are
restrictions along `π` of `A`-actions — on `A` tautologically, on the kernel by
`Stacks.Smooth.kerModule_smul` — so an `A'`-linear equivalence between them respects the
`A`-actions as well, each element of `A` being `π` of one of `A'`.

This is what lets a presentation of the conormal module obtained over the ring, such as
`Deformation.Examples.quotientEquivDualNumberKernel`, be used to compute its dimension over the
quotient. -/
noncomputable def kerEquivQuotientOfLinearEquiv (hπ : Function.Surjective π)
    (h2 : RingHom.ker π ^ 2 = ⊥) (E : letI := π.toAlgebra; A ≃ₗ[A'] RingHom.ker π) :
    letI := kerModule hπ h2
    A ≃ₗ[A] RingHom.ker π :=
  letI := π.toAlgebra
  letI := kerModule hπ h2
  { E with
    map_smul' := fun b x ↦ by
      obtain ⟨a, ha⟩ := hπ b
      subst ha
      change E (π a • x) = π a • E x
      rw [show (π a) • x = a • x from rfl, map_smul, kerModule_smul hπ h2] }

section KerTransport

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

/-- The kernels of two ring maps identified by ring isomorphisms of their sources and targets
forming a commuting square. -/
def kerAddEquivOfRingEquiv (q : R →+* S) (q' : R' →+* S') (α : R ≃+* R') (β : S ≃+* S')
    (hcomm : ∀ x, β (q x) = q' (α x)) : RingHom.ker q ≃+ RingHom.ker q' where
  toFun x := ⟨α x.val, by
    change q' (α x.val) = 0
    rw [← hcomm, show q x.val = 0 from x.property, map_zero]⟩
  invFun y := ⟨α.symm y.val, by
    change q (α.symm y.val) = 0
    rw [← β.injective.eq_iff, hcomm, α.apply_symm_apply, map_zero]
    exact y.property⟩
  left_inv x := Subtype.ext (α.symm_apply_apply x.val)
  right_inv y := Subtype.ext (α.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add α x.val y.val)

/-- **A trivialisation of the kernel transports along ring isomorphisms of source and target.**
If `α : R ≃+* R'` and `β : S ≃+* S'` carry `q : R →+* S` to `q' : R' →+* S'`, then a
presentation of the kernel of `q'` as the tuples `ι → S'`, linear over `R'` acting through `q'`,
gives one of the kernel of `q` as the tuples `ι → S`, linear over `R` acting through `q`.

This is what lets the conormal module of a square-zero extension be computed on a ring and the
answer read on the global sections of its spectrum, where the identification of the two rings is
`AlgebraicGeometry.Scheme.ΓSpecIso` and the commuting square is its naturality. -/
noncomputable def kerEquivPiOfRingEquiv (q : R →+* S) (q' : R' →+* S') (α : R ≃+* R')
    (β : S ≃+* S') (hcomm : ∀ x, β (q x) = q' (α x)) {ι : Type*}
    (e : letI := q'.toAlgebra; RingHom.ker q' ≃ₗ[R'] (ι → S')) :
    letI := q.toAlgebra
    RingHom.ker q ≃ₗ[R] (ι → S) :=
  letI := q.toAlgebra
  letI := q'.toAlgebra
  let φ := kerAddEquivOfRingEquiv q q' α β hcomm
  let ψ : (ι → S') ≃+ (ι → S) :=
    { toFun := fun c i ↦ β.symm (c i)
      invFun := fun c i ↦ β (c i)
      left_inv := fun c ↦ funext fun i ↦ β.apply_symm_apply (c i)
      right_inv := fun c ↦ funext fun i ↦ β.symm_apply_apply (c i)
      map_add' := fun c d ↦ funext fun i ↦ map_add β.symm (c i) (d i) }
  { ((φ.trans e.toAddEquiv).trans ψ) with
    map_smul' := fun a x ↦ by
      funext i
      change β.symm (e (φ (a • x)) i) = q a * β.symm (e (φ x) i)
      have hφ : φ (a • x) = α a • φ x := Subtype.ext (map_mul α a x.val)
      rw [hφ, map_smul]
      change β.symm (q' (α a) * e (φ x) i) = q a * β.symm (e (φ x) i)
      rw [map_mul, ← hcomm, β.symm_apply_apply] }

end KerTransport

end Ker

/-! ### Module structures along `appLE` for a bare module -/

/-- The `Γ(X, W)`-module structure on a `Γ(T, U)`-module `M`, for `a : T ⟶ X` and
`U ≤ a ⁻¹ᵁ W`, obtained by restricting scalars along `a.appLE W U`. This is the analogue of
`Stacks.Smooth.moduleAppLE` for a module that is not given as the sections of a sheaf. -/
@[instance_reducible]
noncomputable def moduleOfAppLE {X T : Scheme.{u}} (a : T ⟶ X) {W : X.Opens} {U : T.Opens}
    (hUW : U ≤ a ⁻¹ᵁ W) (M : Type*) [AddCommGroup M] [Module Γ(T, U) M] : Module Γ(X, W) M :=
  Module.compHom _ (a.appLE W U hUW).hom

/-- The scalar tower `Γ(X, W) → Γ(T, U) → M`. -/
theorem isScalarTowerOfAppLE {X T : Scheme.{u}} (a : T ⟶ X) {W : X.Opens} {U : T.Opens}
    (hUW : U ≤ a ⁻¹ᵁ W) (M : Type*) [AddCommGroup M] [Module Γ(T, U) M] :
    letI := algebraAppLE a hUW
    letI := moduleOfAppLE a hUW M
    IsScalarTower Γ(X, W) Γ(T, U) M :=
  let := algebraAppLE a hUW
  let := moduleOfAppLE a hUW M
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The `Γ(S, V)`-module structure on a `Γ(T, U)`-module `M` obtained by restricting scalars
along the composite `Γ(S, V) ⟶ Γ(X, W) ⟶ Γ(T, U)`. -/
@[instance_reducible]
noncomputable def moduleOfAppLEBase {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {V : S.Opens}
    {W : X.Opens} {U : T.Opens} (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) (M : Type*)
    [AddCommGroup M] [Module Γ(T, U) M] : Module Γ(S, V) M :=
  Module.compHom _ (f.appLE V W hWV ≫ a.appLE W U hUW).hom

/-- The scalar tower `Γ(S, V) → Γ(X, W) → M`. -/
theorem isScalarTowerOfAppLEBase {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {V : S.Opens}
    {W : X.Opens} {U : T.Opens} (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) (M : Type*)
    [AddCommGroup M] [Module Γ(T, U) M] :
    letI := algebraAppLE f hWV
    letI := moduleOfAppLE a hUW M
    letI := moduleOfAppLEBase f a hWV hUW M
    IsScalarTower Γ(S, V) Γ(X, W) M :=
  let := algebraAppLE f hWV
  let := moduleOfAppLE a hUW M
  let := moduleOfAppLEBase f a hWV hUW M
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-! ### Chart independence for a bare module -/

/-- **Derivations at an affine chart are the linear maps out of the sections of `a^*Ω_{X/S}`,
for an arbitrary coefficient module.** Let `f : X ⟶ S` be a morphism of schemes, let `V` be an
affine open of `S` and `W` an affine open of `X` with `W ≤ f ⁻¹ᵁ V`, let `T` be an affine scheme
and `a : T ⟶ X` a morphism mapping into `W`, and let `M` be a module over `Γ(T, ⊤)`. Every
`Γ(S, V)`-derivation of `Γ(X, W)` with values in `M` is induced by exactly one `Γ(T, ⊤)`-linear
map `Γ(a^*Ω_{X/S}, ⊤) ⟶ M`.

This is `Stacks.Smooth.existsUnique_linearMap_comp_pullbackD` with the coefficients freed from
the requirement of being the global sections of a sheaf of modules on `T`, which is what makes
it applicable to the conormal module `Stacks.Smooth.kerModule` of a first-order thickening. -/
theorem existsUnique_linearMap_comp_pullbackD_of_module {X S T : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ X) {V : S.Opens} {W : X.Opens} [IsAffine T] (M : Type u) [AddCommGroup M]
    [Module Γ(T, (⊤ : T.Opens)) M] (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := moduleOfAppLE a hUW M
    letI := moduleOfAppLEBase f a hWV hUW M
    ∀ δ : Derivation Γ(S, V) Γ(X, W) M,
      ∃! θ : Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, ⊤)] M,
        ∀ b : Γ(X, W), θ (pullbackD f a W hUW b) = δ b := by
  let := algebraAppLE f hWV
  let := algebraAppLE a hUW
  let := moduleOfAppLE a hUW M
  let := moduleOfAppLEBase f a hWV hUW M
  let := isScalarTowerOfAppLE a hUW M
  let := isScalarTowerOfAppLEBase f a hWV hUW M
  intro δ
  obtain ⟨N, e, -⟩ := Stacks.Modules.exists_modules_globalSections T M
  let := moduleAppLE a N hUW
  let := moduleAppLEBase f a N hWV hUW
  let := isScalarTowerAppLE a N hUW
  let := isScalarTowerAppLEBase f a N hWV hUW
  -- transport the derivation along `e : M ≃ₗ[Γ(T, ⊤)] Γ(N, ⊤)`
  let eB : M →ₗ[Γ(X, W)] Γ(N, (⊤ : T.Opens)) := e.toLinearMap.restrictScalars Γ(X, W)
  obtain ⟨θ', hθ', huniq'⟩ :=
    existsUnique_linearMap_comp_pullbackD f a N hV hW hWV hUW (eB.compDer δ)
  refine ⟨e.symm.toLinearMap ∘ₗ θ', fun b ↦ ?_, fun θ hθ ↦ ?_⟩
  · show e.symm (θ' (pullbackD f a W hUW b)) = δ b
    rw [hθ' b]
    exact e.symm_apply_apply (δ b)
  · have hθe : e.toLinearMap ∘ₗ θ = θ' := huniq' _ fun b ↦ by
      show e (θ (pullbackD f a W hUW b)) = eB (δ b)
      rw [hθ b]; rfl
    refine LinearMap.ext fun y ↦ ?_
    have h := LinearMap.congr_fun hθe y
    change e (θ y) = θ' y at h
    show θ y = e.symm (θ' y)
    rw [← h, e.symm_apply_apply]

/-! ### The ring-level presentation of an affine first-order thickening -/

variable {T T' : Scheme.{u}}

/-- The map on global sections induced by a closed immersion of affine schemes is surjective. -/
theorem surjective_appTop_of_isFirstOrderThickening [IsAffine T'] {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) : Function.Surjective i.appTop.hom :=
  let := hi.1
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

/-- The kernel on global sections of a first-order thickening of affine schemes is
square-zero. -/
theorem ker_appTop_sq_eq_bot [IsAffine T'] {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) : RingHom.ker i.appTop.hom ^ 2 = ⊥ :=
  let := hi.1
  (ker_pow_eq_bot_iff_of_isAffine i 2).mp hi.2

/-- **The conormal module of an affine first-order thickening.** For `i : T ⟶ T'` a first-order
thickening with `T'` affine, the kernel of `Γ(T', ⊤) ⟶ Γ(T, ⊤)` is a module over `Γ(T, ⊤)`. -/
@[instance_reducible]
noncomputable def thickeningKerModule [IsAffine T'] {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) :
    Module Γ(T, (⊤ : T.Opens)) (RingHom.ker i.appTop.hom) :=
  kerModule (surjective_appTop_of_isFirstOrderThickening hi) (ker_appTop_sq_eq_bot hi)

/-- The action of `Γ(T, ⊤)` on the conormal module of an affine first-order thickening is the
action of any preimage in `Γ(T', ⊤)`. -/
theorem thickeningKerModule_smul [IsAffine T'] {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) (x : Γ(T', (⊤ : T'.Opens)))
    (y : RingHom.ker i.appTop.hom) :
    letI := thickeningKerModule hi
    i.appTop.hom x • y = x • y :=
  kerModule_smul (surjective_appTop_of_isFirstOrderThickening hi) (ker_appTop_sq_eq_bot hi) x y

/-! ### Restriction of a thickening to a basic open -/

/-- **A first-order thickening restricts to a first-order thickening over a basic open.** -/
theorem isFirstOrderThickening_basicOpen {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) (g : Γ(T', (⊤ : T'.Opens))) :
    Thickenings.IsFirstOrderThickening (i ∣_ T'.basicOpen g) :=
  isFirstOrderThickening_morphismRestrict hi _

/-- Both schemes of a first-order thickening of an affine scheme restricted to a basic open are
affine: the basic open of `T'` is affine, and its preimage in `T` is a closed subscheme of
it. -/
theorem isAffine_basicOpen_of_isFirstOrderThickening [IsAffine T'] {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) (g : Γ(T', (⊤ : T'.Opens))) :
    IsAffine (T'.basicOpen g : Scheme.{u}) ∧
      IsAffine ((i ⁻¹ᵁ T'.basicOpen g : T.Opens) : Scheme.{u}) := by
  have hg : IsAffine (T'.basicOpen g : Scheme.{u}) := (isAffineOpen_top T').basicOpen g
  refine ⟨hg, ?_⟩
  have hci : IsClosedImmersion (i ∣_ T'.basicOpen g) := (isFirstOrderThickening_basicOpen hi g).1
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine (i ∣_ T'.basicOpen g)).1

end Stacks.Smooth

end
