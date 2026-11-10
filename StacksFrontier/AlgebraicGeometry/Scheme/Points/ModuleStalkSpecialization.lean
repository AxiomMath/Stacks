module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization

/-!
# The stalk of a quasi-coherent module at a generalization is a localization

Let `X` be a scheme, let `F` be a quasi-coherent `𝒪_X`-module and let `y ⤳ x` be a
specialization of points, so that `y` is a generalization of `x`. The comparison map
`TopCat.Presheaf.stalkSpecializes : F_x ⟶ F_y` is semilinear over the corresponding
comparison `𝒪_{X,x} ⟶ 𝒪_{X,y}` of local rings, and the content of this file is that it
exhibits `F_y` as the localization of the `𝒪_{X,x}`-module `F_x` at a prime ideal — namely
at the very prime that the ring-level statement
`Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes` produces, the
contraction of the maximal ideal of `𝒪_{X,y}`.

This is the module half of the comparison; the ring half is
`Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes`.

Mathlib has `TopCat.Presheaf.stalkSpecializes` only as a morphism of abelian groups, with no
scalar compatibility, and `AlgebraicGeometry.Modules.Tilde` identifies the stalk of `M^~` on
`Spec R` with a localization of `M` but says nothing about an arbitrary scheme. Nothing
identifies the specialization map of a module as a localization map, so a consumer that needs
to pass from a statement about `F_y` to a statement about a prime of the `𝒪_{X,x}`-module
`F_x` — the shape of the arguments about associated points and the relative assassin
(Tags 02OJ, 05AT) — has no handle at all. That passage is what this file supplies.

## Main definitions

* `Stacks.ModuleStalkSpecialization.stalkModule`: the `𝒪_{X,x}`-module structure on `F_x`,
  as a definition rather than an instance (see the implementation notes).
* `Stacks.ModuleStalkSpecialization.sectionsStalkModule`: the `Γ(X, U)`-module structure on
  `F_x` for `x ∈ U`, obtained by restricting scalars along the germ map.
* `Stacks.ModuleStalkSpecialization.germₗ`: the germ map `Γ(F, U) → F_x` as a
  `Γ(X, U)`-linear map.
* `Stacks.ModuleStalkSpecialization.stalkSpecializesModule`: the `𝒪_{X,x}`-module structure
  on `F_y` for `y ⤳ x`, by restricting scalars along the comparison of local rings.
* `Stacks.ModuleStalkSpecialization.stalkSpecializesₗ`: the comparison `F_x → F_y` as an
  `𝒪_{X,x}`-linear map.

## Main results

* `Stacks.ModuleStalkSpecialization.isLocalizedModule_of_le_of_comp`: if `f : M → M₁`
  exhibits `M₁` as the localization of `M` at `S₁`, and `g ∘ f` exhibits `M₂` as the
  localization of `M` at a larger `S₂`, then `g` exhibits `M₂` as the localization of `M₁`
  at `S₂`. Mathlib has this only for the canonical lift `IsLocalizedModule.liftOfLE`.
* `Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_map_of_submonoid_le`: the
  commutative-algebra core. For a prime `q` of `R`, a submonoid `N ≤ q.primeCompl`, `S` the
  localization of `R` at `N`, `M₁` the localization of an `R`-module `M` at `N` and `M₂` the
  localization of `M` at `q`, the map `M₁ → M₂` exhibits `M₂` as the localization of the
  `S`-module `M₁` at the prime `q S`. This is the module analogue of
  `IsLocalization.isLocalization_of_submonoid_le` followed by `IsLocalization.of_le`.
* `Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_map_of_le`: its case
  `N = p.primeCompl` for a prime `p ⊇ q`, the module analogue of
  `Stacks.StalkSpecialization.isLocalization_atPrime_map_of_le`.
* `Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`: the affine comparison, the
  module analogue of `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`. For `U` an affine
  open of `X`, `F` quasi-coherent and `x ∈ U`, the germ map exhibits `F_x` as the
  localization of `Γ(F, U)` at the prime of `x`.
* `Stacks.ModuleStalkSpecialization.stalkSpecializes_smul`: the specialization map of a
  module is semilinear over the specialization map of the structure sheaf.
* `Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes`: the main
  result. For `y ⤳ x` in a scheme `X` and `F` quasi-coherent, `F_y` is the localization of
  the `𝒪_{X,x}`-module `F_x` at the prime
  `(IsLocalRing.maximalIdeal 𝒪_{X,y}).under 𝒪_{X,x}`.

## Implementation notes

**The prime is named canonically, not through a chart**, exactly as in the ring half. The
proof picks an affine open neighbourhood `U` of `x` — which also contains `y`, by
`Specializes.mem_open` — and transports `isLocalizedModule_germₗ` at the two points of `U`.
The prime that comes out of that argument is `q Γ(X,U)·𝒪_{X,x}`, which depends on `U`; it is
converted to the chart-independent `(IsLocalRing.maximalIdeal 𝒪_{X,y}).under 𝒪_{X,x}` by
`IsLocalization.AtPrime.under_maximalIdeal`, so the statement carries no chart and no
existential.

**The module structures are definitions introduced by `letI`, not instances.** Instance
search cannot produce `Module 𝒪_{X,x} F_x`: Mathlib's instance is stated for
`PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)` and `Scheme.Modules.presheaf` is a
`def` that does not unfold at instance-reducible transparency. Registering
`stalkSpecializesModule` as an instance is worse still — it would put a module structure
between the stalks at every pair of specializing points of every scheme. So the statements
carry the structures in `letI` binders. Unlike the ring half, which offers both a form taking
`[Algebra 𝒪_{X,x} 𝒪_{X,y}]` as a hypothesis with an equation pinning its structure map and a
form at the canonical choice, only the canonical form is given here: a hypothesis form would
need four such pinning equations (the algebra, the two module structures and the linear map),
and a caller who has built its own structures can transport along
`IsLocalizedModule.of_linearEquiv`.

**Why `germ_smul` is restated here.** `PresheafOfModules.germ_smul` is about
`F.val.presheaf`, while every statement in this file is about `F.presheaf`
(`Scheme.Modules.presheaf`). The two are definitionally equal and not syntactically equal,
so the Mathlib lemma can be used by `exact` and never by `rw`. The restatement fixes one
spelling for the whole file.

**The quasi-coherence input is a single lemma.**
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ` — sections of
a quasi-coherent module over a basic open of an affine open are a localization of its
sections over that affine open — is the only place quasi-coherence is used. The three
clauses of `IsLocalizedModule` for the germ map are then read off from the fact that basic
opens of `U` form a neighbourhood basis of each of its points.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.ModuleStalkSpecialization

/-! ### Localization of a localization, for modules -/

/-- **Localization of a localization, for modules.** If `f` exhibits `M₁` as the localization
of `M` at `S₁` and `g ∘ₗ f` exhibits `M₂` as the localization of `M` at a larger submonoid
`S₂`, then `g` exhibits `M₂` as the localization of `M₁` at `S₂`.

Mathlib proves this only for the canonical comparison `IsLocalizedModule.liftOfLE`; the
content here is that any map with the right composite is that comparison. -/
theorem isLocalizedModule_of_le_of_comp {R : Type*} [CommSemiring R]
    {M M₁ M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M] [Module R M₁] [Module R M₂] (S₁ S₂ : Submonoid R) (hS : S₁ ≤ S₂)
    (f : M →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) [IsLocalizedModule S₁ f]
    [IsLocalizedModule S₂ (g ∘ₗ f)] : IsLocalizedModule S₂ g := by
  have h := IsLocalizedModule.lift_unique S₁ f (g ∘ₗ f)
    (fun x ↦ IsLocalizedModule.map_units (g ∘ₗ f) ⟨x.1, hS x.2⟩) g rfl
  rw [← h]
  exact inferInstanceAs (IsLocalizedModule S₂ (IsLocalizedModule.liftOfLE S₁ S₂ hS f (g ∘ₗ f)))

section Algebra

variable {R : Type*} [CommRing R] {p q : Ideal R} [p.IsPrime] [hq : q.IsPrime]

/-- If the localizing submonoid `N` misses `q`, then an element of `R` outside `q` stays
outside the ideal `q S` of the localization `S` of `R` at `N`. -/
theorem notMem_map_of_notMem_of_le {N : Submonoid R} (hNq : N ≤ q.primeCompl) (S : Type*)
    [CommRing S] [Algebra R S] [IsLocalization N S] {a : R} (ha : a ∉ q) :
    algebraMap R S a ∉ Ideal.map (algebraMap R S) q := by
  have hdisj : Disjoint (N : Set R) (q : Set R) :=
    Set.disjoint_left.mpr fun _ hb hqb => hNq hb hqb
  have hunder : (Ideal.map (algebraMap R S) q).under R = q :=
    IsLocalization.under_map_of_isPrime_disjoint N S hq hdisj
  exact fun hmem => ha (hunder ▸ Ideal.mem_comap.mpr hmem)

/-- The image in `S` of the complement of `q` is contained in the complement of `q S`, for `S`
a localization of `R` at a submonoid missing `q`. -/
theorem algebraMapSubmonoid_le_primeCompl_map_of_le {N : Submonoid R} (hNq : N ≤ q.primeCompl)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization N S]
    [(Ideal.map (algebraMap R S) q).IsPrime] :
    Algebra.algebraMapSubmonoid S q.primeCompl ≤ (Ideal.map (algebraMap R S) q).primeCompl := by
  rintro _ ⟨a, ha, rfl⟩
  exact notMem_map_of_notMem_of_le hNq S ha

/-- Every element of the complement of `q S` becomes, after multiplication by an element of
`S`, the image of an element of `R` outside `q`. This is what upgrades a localization at the
image of `q.primeCompl` to a localization at all of `(q S).primeCompl`. -/
theorem exists_mul_mem_algebraMapSubmonoid_of_le {N : Submonoid R} (hNq : N ≤ q.primeCompl)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization N S]
    [hmp : (Ideal.map (algebraMap R S) q).IsPrime]
    (z : (Ideal.map (algebraMap R S) q).primeCompl) :
    ∃ m : S, m * z ∈ Algebra.algebraMapSubmonoid S q.primeCompl := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj N (z : S)
  refine ⟨algebraMap R S s, a, ?_, by rw [← hs, mul_comm]⟩
  intro hmemq
  refine z.2 ?_
  have hmul : algebraMap R S s * (z : S) ∈ Ideal.map (algebraMap R S) q := by
    rw [mul_comm, hs]
    exact Ideal.mem_map_of_mem _ hmemq
  exact (hmp.mem_or_mem hmul).resolve_left (notMem_map_of_notMem_of_le hNq S (hNq s.2))

/-- **The localization of a localization of modules, at a submonoid.** Let `q` be a prime of
`R`, let `N ≤ q.primeCompl` be a submonoid, let `S` be the localization of `R` at `N`, let `M`
be an `R`-module, let `M₁` be its localization at `N` (so an `S`-module) and let `M₂` be its
localization at `q`. Then a comparison `M₁ →ₗ[S] M₂` whose composite with `f` is the
localization map at `q` exhibits `M₂` as the localization of `M₁` at the prime `q S`.

This is the module analogue of `IsLocalization.isLocalization_of_submonoid_le` followed by
`IsLocalization.of_le`. Mathlib has the two halves — the instance
`IsLocalizedModule S₂ (IsLocalizedModule.liftOfLE ..)` and
`IsLocalizedModule.of_restrictScalars`, which gives only the localization at the *image* of
`q.primeCompl` — but not their composite.

The point of taking an arbitrary `N` rather than `p.primeCompl` for a prime `p ⊇ q` is that
the localizing submonoid of a pushforward stalk is
`Algebra.algebraMapSubmonoid Γ(Z, g⁻¹U) p.primeCompl`, the image of a prime complement under a
ring map, which is not the complement of any prime. -/
theorem isLocalizedModule_atPrime_map_of_submonoid_le {N : Submonoid R}
    (hNq : N ≤ q.primeCompl) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization N S]
    [(Ideal.map (algebraMap R S) q).IsPrime]
    {M M₁ M₂ : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid M₁] [Module R M₁] [Module S M₁] [IsScalarTower R S M₁]
    [AddCommMonoid M₂] [Module R M₂] [Module S M₂] [IsScalarTower R S M₂]
    (f : M →ₗ[R] M₁) [IsLocalizedModule N f] (g : M₁ →ₗ[S] M₂)
    [IsLocalizedModule q.primeCompl (g.restrictScalars R ∘ₗ f)] :
    IsLocalizedModule.AtPrime (Ideal.map (algebraMap R S) q) g := by
  have : IsLocalizedModule q.primeCompl (g.restrictScalars R) :=
    isLocalizedModule_of_le_of_comp N q.primeCompl hNq f (g.restrictScalars R)
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid S q.primeCompl) g :=
    IsLocalizedModule.of_restrictScalars q.primeCompl g
  exact IsLocalizedModule.of_exists_mul_mem _ _
    (algebraMapSubmonoid_le_primeCompl_map_of_le hNq S)
    (exists_mul_mem_algebraMapSubmonoid_of_le hNq S) g

/-- For primes `q ≤ p` of `R`, the complement of `p` is contained in the complement of `q`. -/
theorem primeCompl_le_primeCompl (hqp : q ≤ p) : p.primeCompl ≤ q.primeCompl :=
  fun _ ha hqa => ha (hqp hqa)

/-- If `q ≤ p` are primes of `R` and `S` is a localization of `R` at `p`, then an element of
`R` outside `q` stays outside the ideal `q S`. -/
theorem notMem_map_of_notMem (hqp : q ≤ p) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S p] {a : R} (ha : a ∉ q) :
    algebraMap R S a ∉ Ideal.map (algebraMap R S) q :=
  notMem_map_of_notMem_of_le (primeCompl_le_primeCompl hqp) S ha

/-- The image in `S` of the complement of `q` is contained in the complement of `q S`. -/
theorem algebraMapSubmonoid_le_primeCompl_map (hqp : q ≤ p) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization.AtPrime S p] [(Ideal.map (algebraMap R S) q).IsPrime] :
    Algebra.algebraMapSubmonoid S q.primeCompl ≤ (Ideal.map (algebraMap R S) q).primeCompl :=
  algebraMapSubmonoid_le_primeCompl_map_of_le (primeCompl_le_primeCompl hqp) S

/-- Every element of the complement of `q S` becomes, after multiplication by an element of
`S`, the image of an element of `R` outside `q`. -/
theorem exists_mul_mem_algebraMapSubmonoid (hqp : q ≤ p) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S p] [(Ideal.map (algebraMap R S) q).IsPrime]
    (z : (Ideal.map (algebraMap R S) q).primeCompl) :
    ∃ m : S, m * z ∈ Algebra.algebraMapSubmonoid S q.primeCompl :=
  exists_mul_mem_algebraMapSubmonoid_of_le (primeCompl_le_primeCompl hqp) S z

/-- **The localization of a localization of modules, in `AtPrime` form.** Let `q ≤ p` be
prime ideals of `R`, let `S` be a localization of `R` at `p`, let `M` be an `R`-module, let
`N` be its localization at `p` (so an `S`-module) and let `P` be its localization at `q`.
Then the comparison `N →ₗ[S] P` exhibits `P` as the localization of `N` at the prime `q S`.

This is the case `N = p.primeCompl` of
`Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_map_of_submonoid_le`, and the
module analogue of `Stacks.StalkSpecialization.isLocalization_atPrime_map_of_le`. -/
theorem isLocalizedModule_atPrime_map_of_le (hqp : q ≤ p) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization.AtPrime S p] [(Ideal.map (algebraMap R S) q).IsPrime]
    {M N P : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P]
    (f : M →ₗ[R] N) [IsLocalizedModule p.primeCompl f] (g : N →ₗ[S] P)
    [IsLocalizedModule q.primeCompl (g.restrictScalars R ∘ₗ f)] :
    IsLocalizedModule.AtPrime (Ideal.map (algebraMap R S) q) g :=
  isLocalizedModule_atPrime_map_of_submonoid_le (primeCompl_le_primeCompl hqp) S f g

end Algebra

/-- `IsLocalizedModule.AtPrime` transported along an equality of primes. The two sides carry
different `Ideal.IsPrime` instance arguments, so `rw` cannot do this: its motive is not type
correct. -/
theorem isLocalizedModule_atPrime_of_eq {R M N : Type*} [CommRing R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] {I J : Ideal R} [I.IsPrime] [J.IsPrime]
    (hIJ : I = J) {f : M →ₗ[R] N} (hf : IsLocalizedModule.AtPrime I f) :
    IsLocalizedModule.AtPrime J f := by
  subst hIJ
  exact hf

/-! ### Stalks of modules on a scheme -/

variable {X : Scheme.{u}}

/-- The `𝒪_{X,x}`-module structure on the stalk of an `𝒪_X`-module at `x`. Instance search
does not find it because it cannot unfold `AlgebraicGeometry.Scheme.Modules.presheaf`, so it
is provided as a definition to be introduced with `letI`. -/
@[instance_reducible]
noncomputable def stalkModule (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x

/-- The `Γ(X, U)`-module structure on the stalk at a point of `U`, obtained by restricting
scalars along the germ map of the structure sheaf. -/
@[instance_reducible]
noncomputable def sectionsStalkModule (F : X.Modules) {U : X.Opens} {x : X} (hx : x ∈ U) :
    Module Γ(X, U) (F.presheaf.stalk x) :=
  letI := stalkModule F x
  Module.compHom _ (X.presheaf.germ U x hx).hom

/-- `PresheafOfModules.germ_smul` in the `Scheme.Modules.presheaf` spelling. -/
theorem germ_smul (F : X.Modules) {U : X.Opens} {x : X} (hx : x ∈ U)
    (r : Γ(X, U)) (m : Γ(F, U)) :
    letI := stalkModule F x
    F.presheaf.germ U x hx (r • m)
      = X.presheaf.germ U x hx r • F.presheaf.germ U x hx m :=
  PresheafOfModules.germ_smul F.val x U hx r m

/-- The germ map on sections of an `𝒪_X`-module, as a `Γ(X, U)`-linear map to the stalk. -/
noncomputable def germₗ (F : X.Modules) {U : X.Opens} {x : X} (hx : x ∈ U) :
    letI := sectionsStalkModule F hx
    Γ(F, U) →ₗ[Γ(X, U)] F.presheaf.stalk x :=
  letI := sectionsStalkModule F hx
  { toFun := F.presheaf.germ U x hx
    map_add' := map_add _
    map_smul' := fun r m ↦ germ_smul F hx r m }

/-- The scalar tower `Γ(X, U) → 𝒪_{X,x} → F_x`. -/
theorem isScalarTower_sectionsStalk (F : X.Modules) {U : X.Opens} {x : X} (hx : x ∈ U) :
    letI := (X.presheaf.germ U x hx).hom.toAlgebra
    letI := stalkModule F x
    letI := sectionsStalkModule F hx
    IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  let := (X.presheaf.germ U x hx).hom.toAlgebra
  let := stalkModule F x
  let := sectionsStalkModule F hx
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- A function on an affine open does not lie in the prime of a point of that open as soon as
the point lies in the corresponding basic open. -/
theorem mem_primeCompl_of_mem_basicOpen {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) (a : Γ(X, U)) (ha : x ∈ X.basicOpen a) :
    a ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  rw [← IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal a]
  exact (X.mem_basicOpen a x hx).mp ha

/-- On an affine open, scalar multiplication on the stalk by a function not vanishing at the
point is bijective. -/
theorem isUnit_smul_stalk (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) (a : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) :
    letI := sectionsStalkModule F hx
    IsUnit ((algebraMap Γ(X, U) (Module.End Γ(X, U) (F.presheaf.stalk x))) (a : Γ(X, U))) := by
  let := stalkModule F x
  let := sectionsStalkModule F hx
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have hu : IsUnit (algebraMap (X.presheaf.stalk x)
      (Module.End (X.presheaf.stalk x) (F.presheaf.stalk x))
      (algebraMap Γ(X, U) (X.presheaf.stalk x) (a : Γ(X, U)))) :=
    ((IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal (a : Γ(X, U))).mpr a.2).map _
  have hbij := (Module.End.isUnit_iff _).mp hu
  exact (Module.End.isUnit_iff _).mpr hbij

/-- On an affine open, two sections of a quasi-coherent module with the same germ at a point
agree after multiplication by a function not vanishing at that point. -/
theorem exists_smul_eq_of_germ_eq (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (s t : Γ(F, U))
    (h : F.presheaf.germ U x hx s = F.presheaf.germ U x hx t) :
    ∃ c ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl, c • s = c • t := by
  obtain ⟨W, hxW, iU, iV, hres⟩ := TopCat.Presheaf.germ_eq F.presheaf x hx hx s t h
  obtain ⟨a, haW, hxa⟩ := hU.exists_basicOpen_le (⟨x, hxW⟩ : W) hx
  have hbU : X.basicOpen a ≤ U := haW.trans iU.le
  let := moduleOfLE F hbU
  have hloc : IsLocalizedModule.Away a (restrictₗ F hbU) :=
    isLocalizedModule_restrictₗ F hU a rfl hbU
  have hr : restrictₗ F hbU s = restrictₗ F hbU t := by
    change F.presheaf.map (homOfLE hbU).op s = F.presheaf.map (homOfLE hbU).op t
    have e₁ : F.presheaf.map (homOfLE hbU).op s
        = F.presheaf.map (homOfLE haW).op (F.presheaf.map iU.op s) := by
      rw [← Functor.map_comp_apply]; congr 1
    have e₂ : F.presheaf.map (homOfLE hbU).op t
        = F.presheaf.map (homOfLE haW).op (F.presheaf.map iV.op t) := by
      rw [← Functor.map_comp_apply]; congr 1
    rw [e₁, e₂, hres]
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers a)
    (restrictₗ F hbU)).mp hr
  exact ⟨c.1, Submonoid.powers_le.mpr (mem_primeCompl_of_mem_basicOpen hU hx a hxa) c.2,
    by simpa [Submonoid.smul_def] using hc⟩

/-- On an affine open, every element of the stalk of a quasi-coherent module becomes the germ
of a section over the whole affine open after multiplication by a function not vanishing at
the point. -/
theorem exists_germ_smul_eq_germ (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (m : F.presheaf.stalk x) :
    letI := stalkModule F x
    ∃ (s : Γ(F, U)) (c : Γ(X, U)), c ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl ∧
      X.presheaf.germ U x hx c • m = F.presheaf.germ U x hx s := by
  let := stalkModule F x
  obtain ⟨V, hxV, t, ht⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
  obtain ⟨a, haVU, hxa⟩ := hU.exists_basicOpen_le (⟨x, ⟨hxV, hx⟩⟩ : (V ⊓ U : X.Opens)) hx
  have hbU : X.basicOpen a ≤ U := haVU.trans inf_le_right
  have hbV : X.basicOpen a ≤ V := haVU.trans inf_le_left
  let := moduleOfLE F hbU
  have hloc : IsLocalizedModule.Away a (restrictₗ F hbU) :=
    isLocalizedModule_restrictₗ F hU a rfl hbU
  obtain ⟨⟨s, c⟩, hsc⟩ := IsLocalizedModule.surj (Submonoid.powers a) (restrictₗ F hbU)
    (F.presheaf.map (homOfLE hbV).op t)
  refine ⟨s, c.1,
    Submonoid.powers_le.mpr (mem_primeCompl_of_mem_basicOpen hU hx a hxa) c.2, ?_⟩
  have hsc' : (X.presheaf.map (homOfLE hbU).op (c : Γ(X, U))) •
      F.presheaf.map (homOfLE hbV).op t
      = F.presheaf.map (homOfLE hbU).op s := hsc
  have key := congrArg (F.presheaf.germ (X.basicOpen a) x hxa) hsc'
  rwa [germ_smul F hxa, F.presheaf.germ_res_apply, X.presheaf.germ_res_apply, ht,
    F.presheaf.germ_res_apply] at key

/-- **The stalk of a quasi-coherent module on an affine open is a localization of its
sections.** The module analogue of `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`. -/
theorem isLocalizedModule_germₗ (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    letI := sectionsStalkModule F hx
    IsLocalizedModule.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal (germₗ F hx) := by
  let := stalkModule F x
  let := sectionsStalkModule F hx
  refine ⟨fun a ↦ isUnit_smul_stalk F hU hx a, fun m ↦ ?_, fun {s t} h ↦ ?_⟩
  · obtain ⟨s, c, hc, hcm⟩ := exists_germ_smul_eq_germ F hU hx m
    exact ⟨⟨s, ⟨c, hc⟩⟩, hcm⟩
  · obtain ⟨c, hc, hct⟩ := exists_smul_eq_of_germ_eq F hU hx s t h
    exact ⟨⟨c, hc⟩, hct⟩

/-! ### The comparison along a specialization -/

/-- `TopCat.Presheaf.germ_stalkSpecializes` for an `𝒪_X`-module, applied to a section. -/
theorem germ_stalkSpecializes_apply (F : X.Modules) {U : X.Opens} {x y : X} (hx : x ∈ U)
    (h : y ⤳ x) (s : Γ(F, U)) :
    F.presheaf.stalkSpecializes h (F.presheaf.germ U x hx s)
      = F.presheaf.germ U y (h.mem_open U.isOpen hx) s :=
  congrArg (fun f => (ConcreteCategory.hom f) s)
    (TopCat.Presheaf.germ_stalkSpecializes F.presheaf hx h)

/-- `TopCat.Presheaf.germ_stalkSpecializes` for the structure sheaf, applied to a section. -/
theorem ringGerm_stalkSpecializes_apply {U : X.Opens} {x y : X} (hx : x ∈ U)
    (h : y ⤳ x) (r : Γ(X, U)) :
    X.presheaf.stalkSpecializes h (X.presheaf.germ U x hx r)
      = X.presheaf.germ U y (h.mem_open U.isOpen hx) r :=
  congrArg (fun f => (ConcreteCategory.hom f) r)
    (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hx h)

/-- **The specialization map of a module is semilinear** over the specialization map of the
structure sheaf. Both arguments are germs on a common neighbourhood of `x`, and the identity
is `PresheafOfModules.germ_smul` at `x` and at `y`. -/
theorem stalkSpecializes_smul (F : X.Modules) {x y : X} (h : y ⤳ x)
    (r : X.presheaf.stalk x) (m : F.presheaf.stalk x) :
    letI := stalkModule F x
    letI := stalkModule F y
    F.presheaf.stalkSpecializes h (r • m)
      = X.presheaf.stalkSpecializes h r • F.presheaf.stalkSpecializes h m := by
  let := stalkModule F x
  let := stalkModule F y
  obtain ⟨V, hxV, u, hu⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  obtain ⟨W, hxW, t, ht⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
  have hxZ : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  have hur : X.presheaf.germ (V ⊓ W) x hxZ
      (X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op u) = r := by
    rwa [X.presheaf.germ_res_apply]
  have htm : F.presheaf.germ (V ⊓ W) x hxZ
      (F.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op t) = m := by
    rwa [F.presheaf.germ_res_apply]
  rw [← hur, ← htm, ← germ_smul F hxZ, germ_stalkSpecializes_apply F hxZ h,
    germ_stalkSpecializes_apply F hxZ h, ringGerm_stalkSpecializes_apply hxZ h,
    germ_smul F (h.mem_open (V ⊓ W).isOpen hxZ)]

/-- The `𝒪_{X,x}`-module structure on the stalk at a generalization `y ⤳ x`, obtained by
restricting scalars along the comparison `𝒪_{X,x} ⟶ 𝒪_{X,y}` of local rings. -/
@[instance_reducible]
noncomputable def stalkSpecializesModule (F : X.Modules) {x y : X} (h : y ⤳ x) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk y) :=
  letI := stalkModule F y
  Module.compHom _ (X.presheaf.stalkSpecializes h).hom

/-- The scalar tower `Γ(X, U) → 𝒪_{X,x} → F_y` for `y ⤳ x` and `x ∈ U`: acting through the
local ring at `x` and then specializing is acting through the germ at `y`. -/
theorem isScalarTower_stalkSpecializes (F : X.Modules) {U : X.Opens} {x y : X} (hx : x ∈ U)
    (h : y ⤳ x) :
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    letI := stalkModule F y
    letI := stalkSpecializesModule F h
    letI := sectionsStalkModule F (h.mem_open U.isOpen hx)
    IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk y) :=
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let := stalkModule F y
  let := stalkSpecializesModule F h
  let := sectionsStalkModule F (h.mem_open U.isOpen hx)
  IsScalarTower.of_algebraMap_smul fun r m ↦ by
    change (X.presheaf.stalkSpecializes h) (X.presheaf.germ U x hx r) • m
      = X.presheaf.germ U y (h.mem_open U.isOpen hx) r • m
    rw [ringGerm_stalkSpecializes_apply hx h]

/-- The comparison `F_x ⟶ F_y` along a specialization `y ⤳ x`, as an `𝒪_{X,x}`-linear map. -/
noncomputable def stalkSpecializesₗ (F : X.Modules) {x y : X} (h : y ⤳ x) :
    letI := stalkModule F x
    letI := stalkSpecializesModule F h
    F.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk y :=
  letI := stalkModule F x
  letI := stalkSpecializesModule F h
  { toFun := F.presheaf.stalkSpecializes h
    map_add' := map_add _
    map_smul' := stalkSpecializes_smul F h }

/-- `Stacks.ModuleStalkSpecialization.germ_stalkSpecializes_apply` for
`Stacks.ModuleStalkSpecialization.stalkSpecializesₗ`: the comparison carries the germ at `x` of
a section to its germ at `y`. The two statements are definitionally the same, but a `rw` cannot
see through the structure literal `stalkSpecializesₗ` is. -/
theorem stalkSpecializesₗ_germ (F : X.Modules) {U : X.Opens} {x y : X} (hx : x ∈ U)
    (h : y ⤳ x) (s : Γ(F, U)) :
    letI := stalkModule F x
    letI := stalkSpecializesModule F h
    stalkSpecializesₗ F h (F.presheaf.germ U x hx s)
      = F.presheaf.germ U y (h.mem_open U.isOpen hx) s :=
  germ_stalkSpecializes_apply F hx h s

/-- **The stalk of a quasi-coherent module at a generalization is a localization.** Let
`y ⤳ x` be a specialization of points of a scheme `X` and let `F` be a quasi-coherent
`𝒪_X`-module. Then the comparison `F_x ⟶ F_y` exhibits `F_y` as the localization of the
`𝒪_{X,x}`-module `F_x` at the prime ideal obtained by contracting the maximal ideal of
`𝒪_{X,y}` — the same prime that
`Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes` produces on the ring
side. -/
theorem isLocalizedModule_atPrime_stalkSpecializes (F : X.Modules) [F.IsQuasicoherent]
    {x y : X} (h : y ⤳ x) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    letI := stalkModule F x
    letI := stalkSpecializesModule F h
    IsLocalizedModule.AtPrime
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x))
      (stalkSpecializesₗ F h) := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let := stalkModule F x
  let := stalkModule F y
  let := stalkSpecializesModule F h
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  let := sectionsStalkModule F hxU
  let := sectionsStalkModule F hyU
  let pp : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let qq : Ideal Γ(X, U) := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
  have : pp.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  have : qq.IsPrime := (hU.primeIdealOf ⟨y, hyU⟩).isPrime
  have hlocx : IsLocalization.AtPrime (X.presheaf.stalk x) pp := hU.isLocalization_stalk _
  have hlocy : IsLocalization.AtPrime (X.presheaf.stalk y) qq := hU.isLocalization_stalk _
  have hqp : qq ≤ pp := (PrimeSpectrum.le_iff_specializes _ _).mpr (by
    change (Scheme.homeoOfIso hU.isoSpec) ⟨y, hyU⟩ ⤳ (Scheme.homeoOfIso hU.isoSpec) ⟨x, hxU⟩
    exact ((subtype_specializes_iff (⟨y, hyU⟩ : U) ⟨x, hxU⟩).mpr h).map
      (Scheme.homeoOfIso hU.isoSpec).continuous)
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq'
      (RingHom.ext fun r ↦ (ringGerm_stalkSpecializes_apply hxU h r).symm)
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    isScalarTower_sectionsStalk F hxU
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk y) :=
    isScalarTower_stalkSpecializes F hxU h
  have hf : IsLocalizedModule pp.primeCompl (germₗ F hxU) := isLocalizedModule_germₗ F hU hxU
  have hcomp : (stalkSpecializesₗ F h).restrictScalars Γ(X, U) ∘ₗ germₗ F hxU = germₗ F hyU :=
    LinearMap.ext fun s ↦ germ_stalkSpecializes_apply F hxU h s
  have hg : IsLocalizedModule qq.primeCompl
      ((stalkSpecializesₗ F h).restrictScalars Γ(X, U) ∘ₗ germₗ F hxU) := by
    rw [hcomp]
    exact isLocalizedModule_germₗ F hU hyU
  have hprime : (Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) qq).IsPrime :=
    Stacks.StalkSpecialization.isPrime_map_of_le hqp _
  have hring : IsLocalization.AtPrime (X.presheaf.stalk y)
      (Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) qq) :=
    Stacks.StalkSpecialization.isLocalization_atPrime_map_of_le hqp
      (X.presheaf.stalk x) (X.presheaf.stalk y)
  exact isLocalizedModule_atPrime_of_eq
    (IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y)
      (Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) qq)).symm
    (isLocalizedModule_atPrime_map_of_le hqp (X.presheaf.stalk x) (germₗ F hxU)
      (stalkSpecializesₗ F h))

end Stacks.ModuleStalkSpecialization

end
