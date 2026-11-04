module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor

/-!
# The conormal module of a thickening localizes

Let `i : T ⟶ T'` be a first-order thickening of schemes with `T'` affine, and write
`π = i.appTop : Γ(T', ⊤) ⟶ Γ(T, ⊤)` for the induced surjection of global sections. Its kernel
`𝒞_{T/T'} = RingHom.ker π` is the *conormal module* of the thickening, a module over `Γ(T, ⊤)` by
`Stacks.Smooth.thickeningKerModule`. This file proves that the conormal module is compatible with
passage to a basic open: for `g` a global section of `T'`, the conormal module of the restricted
thickening `i ∣_ T'.basicOpen g` is the localization of `𝒞_{T/T'}` away from the image
`i.appTop g`.

This is the input that step (II) of the proof of [Stacks Project, Tag 02H6] needs on the
*coefficient* side, matching `Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'`
on the side of `a^*Ω_{X/S}`: it is what makes the chart-local differences
`Stacks.Smooth.liftDiffDerivation` of two solutions of a lifting problem, which are derivations
with values in the conormal module of a restricted thickening, into a Čech cochain for one
`Γ(T, ⊤)`-module.

## Main definitions

* `Stacks.Smooth.moduleOfOpensAppTop` is the restriction of scalars of a module over `Γ(U, ⊤)`,
  for `U` an open of a scheme `Y`, to a module over `Γ(Y, ⊤)`.
* `Stacks.Smooth.conormalRestrict` is the restriction map `𝒞_{T/T'} ⟶ 𝒞_{T_g/T'_g}` of conormal
  modules attached to a basic open `D(g)` of `T'`, as a `Γ(T, ⊤)`-linear map.

## Main results

* `Stacks.Smooth.isLocalizedModule_ker_of_isLocalization_away`: the purely algebraic statement.
  Let `π : A' →+* A` be a ring map, let `g : A'`, let `A'g` be the localization of `A'` away from
  `g` and `Ac` the localization of `A` away from `π g`, and let `πg : A'g →+* Ac` be compatible
  with `π`. Then `RingHom.ker πg` is the localization of `RingHom.ker π` away from `g`.
* `Stacks.Smooth.isLocalizedModule_conormalRestrict`: the geometric statement, over the ring
  `Γ(T, ⊤)` and away from `i.appTop g`.

## Implementation notes

Mathlib already has the abstract form of the algebraic statement: localization of modules commutes
with kernels, `LinearMap.toKerLocalized_isLocalizedModule`. Instantiating it here would mean
producing the two localization ladders in the shape `IsLocalizedModule.map` and comparing that
map with the ring map `πg`, which is more work than verifying the three defining properties of
`IsLocalizedModule` by hand; the proof below does the latter. The three verifications are:
multiplication by a power of `g` is bijective on `RingHom.ker πg` because `g` becomes a unit in
`A'g` and the inverse of a unit preserves an ideal; a given element of `RingHom.ker πg` is
`g ^ -k` times the image of some `x : A'` by `IsLocalization.Away.surj`, and that `x` can be
corrected into `RingHom.ker π` by multiplying by a further power of `g`, because `π x` dies in
`Ac`; and two elements of `RingHom.ker π` with the same image differ by a power of `g` because
`A'g` is a localization.

Geometrically the two localizations are Mathlib's instance
`AlgebraicGeometry.Γ_restrict_isLocalization`, which presents `Γ(D(r), ⊤)` as the localization of
`Γ(X, ⊤)` away from `r` for `X` affine, with structure map the restriction `D(r).ι.appTop`. On the
source side the basic open is `T'.basicOpen g` on the nose; on the target side it is
`i ⁻¹ᵁ T'.basicOpen g`, which is `T.basicOpen (i.appTop g)` by
`Stacks.Smooth.preimage_basicOpen_appTop`. The compatibility of `π` and `πg` with the two
restriction maps is `AlgebraicGeometry.morphismRestrict_ι` on global sections.

The algebraic statement is over the ring `A'`, whereas the Čech argument runs over `A`. The
passage is `IsLocalizedModule.of_restrictScalars`, whose hypotheses are that the `A'`-actions on
the two conormal modules are the restrictions of their `A`-actions; that is
`Stacks.Smooth.thickeningKerModule_smul` on the source and
`Stacks.Smooth.conormal_smul` on the target, and it is also the reason the latter is
stated separately.

## References

* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-! ### Localization of the kernel of a ring map -/

section Algebraic

variable {A A' Ac A'g : Type u} [CommRing A] [CommRing A'] [CommRing Ac] [CommRing A'g]
  [Algebra A' A'g] [Algebra A Ac] {π : A' →+* A} {πg : A'g →+* Ac} {g : A'}

/-- The action of `A'` on an ideal of an `A'`-algebra `A'g` is multiplication by the image of the
scalar. -/
theorem coe_smul_ker (r : A') (y : RingHom.ker πg) :
    ((r • y : RingHom.ker πg) : A'g) = algebraMap A' A'g r * (y : A'g) := by
  rw [Submodule.coe_smul_of_tower, Algebra.smul_def]

/-- An element of `A'` whose image in `A'g` is a unit acts invertibly on the kernel of a ring map
out of `A'g`: the inverse of the unit preserves the kernel, because the kernel is an ideal. -/
theorem isUnit_algebraMap_end_ker (r : A') (hr : IsUnit (algebraMap A' A'g r)) :
    IsUnit (algebraMap A' (Module.End A' (RingHom.ker πg)) r) := by
  rw [Module.End.isUnit_iff]
  refine ⟨fun y z hyz ↦ ?_, fun y ↦ ?_⟩
  · have h : algebraMap A' A'g r * (y : A'g) = algebraMap A' A'g r * (z : A'g) := by
      rw [← coe_smul_ker, ← coe_smul_ker]
      exact congrArg _ (by simpa [Module.algebraMap_end_apply] using hyz)
    exact Subtype.ext (hr.mul_left_cancel h)
  · obtain ⟨u, hu⟩ := hr
    refine ⟨⟨(↑u⁻¹ : A'g) * (y : A'g), ?_⟩, Subtype.ext ?_⟩
    · rw [RingHom.mem_ker, map_mul, RingHom.mem_ker.mp y.2, mul_zero]
    · rw [Module.algebraMap_end_apply, coe_smul_ker, ← hu, ← mul_assoc, u.mul_inv, one_mul]

/-- **The kernel of a ring map localizes.** Let `π : A' →+* A` be a ring map and `g : A'`, let
`A'g` be the localization of `A'` away from `g` and `Ac` the localization of `A` away from `π g`,
and let `πg : A'g →+* Ac` be a ring map compatible with `π` and the two structure maps. Then every
`A'`-linear map `RingHom.ker π ⟶ RingHom.ker πg` which is the structure map `A' ⟶ A'g` on
underlying elements exhibits `RingHom.ker πg` as the localization of `RingHom.ker π` away
from `g`.

This is the exactness of localization applied to `0 → RingHom.ker π → A' → A`; compare
`LinearMap.toKerLocalized_isLocalizedModule`. -/
theorem isLocalizedModule_ker_of_isLocalization_away [IsLocalization.Away g A'g]
    [IsLocalization.Away (π g) Ac]
    (hcomm : ∀ x : A', πg (algebraMap A' A'g x) = algebraMap A Ac (π x))
    (ψ : RingHom.ker π →ₗ[A'] RingHom.ker πg)
    (hψ : ∀ x : RingHom.ker π, (ψ x : A'g) = algebraMap A' A'g (x : A')) :
    IsLocalizedModule.Away g ψ := by
  constructor
  · rintro ⟨s, k, rfl⟩
    exact isUnit_algebraMap_end_ker _
      (by simpa only [map_pow] using (IsLocalization.Away.algebraMap_isUnit g).pow k)
  · intro y
    obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj g (y : A'g)
    have hx0 : algebraMap A Ac (π x) = algebraMap A Ac 0 := by
      rw [map_zero, ← hcomm x, ← hx, map_mul, RingHom.mem_ker.mp y.2, zero_mul]
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (S := Ac) (x := π g) hx0
    refine ⟨⟨⟨g ^ m * x, ?_⟩, ⟨g ^ (m + k), m + k, rfl⟩⟩, ?_⟩
    · rw [RingHom.mem_ker, map_mul, map_pow]
      simpa using hm
    · rw [Submonoid.smul_def]
      refine Subtype.ext ?_
      rw [hψ, coe_smul_ker]
      show algebraMap A' A'g (g ^ (m + k)) * (y : A'g) = algebraMap A' A'g (g ^ m * x)
      rw [map_mul, ← hx, map_pow, map_pow, pow_add]
      ring
  · intro x z hxz
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (S := A'g) (x := g)
      (show algebraMap A' A'g (x : A') = algebraMap A' A'g (z : A') by rw [← hψ, ← hψ, hxz])
    refine ⟨⟨g ^ k, k, rfl⟩, Subtype.ext ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def]
    simpa [coe_smul_ker] using hk

end Algebraic

/-! ### Restriction of scalars along an open immersion -/

/-- The `Γ(Y, ⊤)`-module structure on a `Γ(U, ⊤)`-module `M`, for `U` an open of `Y`, obtained by
restricting scalars along the restriction map `Γ(Y, ⊤) ⟶ Γ(U, ⊤)`. This is
`Stacks.Smooth.moduleOfAppLE` for the open immersion `U.ι`, written with `appTop` in place of
`appLE` so that the action is the restriction map on the nose. -/
@[instance_reducible]
noncomputable def moduleOfOpensAppTop {Y : Scheme.{u}} (U : Y.Opens) (M : Type*) [AddCommGroup M]
    [Module Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) M] :
    Module Γ(Y, (⊤ : Y.Opens)) M :=
  Module.compHom _ U.ι.appTop.hom

/-- The action of `Γ(Y, ⊤)` through `Stacks.Smooth.moduleOfOpensAppTop` is the action of the
restriction of the section to `U`. -/
theorem moduleOfOpensAppTop_smul {Y : Scheme.{u}} (U : Y.Opens) (M : Type*) [AddCommGroup M]
    [Module Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) M] (r : Γ(Y, (⊤ : Y.Opens)))
    (m : M) :
    letI := moduleOfOpensAppTop U M
    r • m = U.ι.appTop.hom r • m :=
  rfl

/-! ### Localization of the conormal module -/

/-- **The sections of a morphism restricted to an open.** Restricting `i : T ⟶ T'` to an open
`U'` of `T'` and then including is the same as including the preimage of `U'` and then applying
`i`; on global sections this says that the sections of `i ∣_ U'` are compatible with the two
restriction maps. -/
theorem appTop_morphismRestrict_comm {T T' : Scheme.{u}} (i : T ⟶ T') (U' : T'.Opens)
    (x : Γ(T', (⊤ : T'.Opens))) :
    (i ∣_ U').appTop.hom (U'.ι.appTop.hom x) = (i ⁻¹ᵁ U').ι.appTop.hom (i.appTop.hom x) := by
  have h : U'.ι.appTop ≫ (i ∣_ U').appTop = i.appTop ≫ (i ⁻¹ᵁ U').ι.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, morphismRestrict_ι]
  simpa only [CommRingCat.comp_apply] using congr($(h).hom x)

section Geometric

variable {T T' : Scheme.{u}} [IsAffine T'] {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i)
  (g : Γ(T', (⊤ : T'.Opens)))

include hi

/-- The closed subscheme of a thickening restricted to a basic open of `T'` is affine. -/
theorem isAffine_preimage_basicOpen :
    IsAffine ((i ⁻¹ᵁ T'.basicOpen g : T.Opens) : Scheme.{u}) :=
  (isAffine_basicOpen_of_isFirstOrderThickening hi g).2

/-- The action of `Γ(T, ⊤)` on the conormal module of the thickening restricted to a basic open
`D(g)` of `T'`, read through the restriction map `Γ(T, ⊤) ⟶ Γ(T_g, ⊤)`, is the action of any
preimage in `Γ(T', ⊤)` through the restriction map `Γ(T', ⊤) ⟶ Γ(T'_g, ⊤)`.

This is the statement that makes the `Γ(T', ⊤)`-action on the conormal module of the restricted
thickening the restriction of its `Γ(T, ⊤)`-action, which is what
`IsLocalizedModule.of_restrictScalars` consumes in
`Stacks.Smooth.isLocalizedModule_conormalRestrict`. -/
theorem conormal_smul (r : Γ(T', (⊤ : T'.Opens)))
    (y : RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom) :
    letI := isAffine_preimage_basicOpen hi g
    letI : IsAffine ((T'.basicOpen g : T'.Opens) : Scheme.{u}) :=
      (isAffine_basicOpen_of_isFirstOrderThickening hi g).1
    letI := thickeningKerModule (isFirstOrderThickening_basicOpen hi g)
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen g)
      (RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom)
    i.appTop.hom r • y = (T'.basicOpen g).ι.appTop.hom r • y := by
  rw [moduleOfOpensAppTop_smul, ← appTop_morphismRestrict_comm i (T'.basicOpen g) r,
    thickeningKerModule_smul (isFirstOrderThickening_basicOpen hi g)]

/-- The action of `Γ(T, ⊤)` on the conormal module of `i` is multiplication by any preimage of
the scalar in `Γ(T', ⊤)`. -/
theorem coe_smul_conormal {r : Γ(T', (⊤ : T'.Opens))} {c : Γ(T, (⊤ : T.Opens))}
    (hr : i.appTop.hom r = c) (x : RingHom.ker i.appTop.hom) :
    letI := thickeningKerModule hi
    ((c • x : RingHom.ker i.appTop.hom) : Γ(T', (⊤ : T'.Opens)))
      = r * (x : Γ(T', (⊤ : T'.Opens))) := by
  rw [← hr, thickeningKerModule_smul hi, Submodule.coe_smul, smul_eq_mul]

/-- The action of `Γ(T, ⊤)` on the conormal module of the thickening restricted to `D(g)` is
multiplication by the restriction to `D(g)` of any preimage of the scalar in `Γ(T', ⊤)`. -/
theorem coe_smul_conormal_basicOpen {r : Γ(T', (⊤ : T'.Opens))} {c : Γ(T, (⊤ : T.Opens))}
    (hr : i.appTop.hom r = c) (y : RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom) :
    letI := isAffine_preimage_basicOpen hi g
    letI : IsAffine ((T'.basicOpen g : T'.Opens) : Scheme.{u}) :=
      (isAffine_basicOpen_of_isFirstOrderThickening hi g).1
    letI := thickeningKerModule (isFirstOrderThickening_basicOpen hi g)
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen g)
      (RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom)
    ((c • y : RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom) :
        Γ(((T'.basicOpen g : T'.Opens) : Scheme.{u}), (⊤ : _root_.TopologicalSpace.Opens _)))
      = (T'.basicOpen g).ι.appTop.hom r *
        (y : Γ(((T'.basicOpen g : T'.Opens) : Scheme.{u}),
          (⊤ : _root_.TopologicalSpace.Opens _))) := by
  rw [← hr, conormal_smul hi g r y, Submodule.coe_smul, smul_eq_mul]

/-- **The restriction map of conormal modules attached to a basic open.** For `i : T ⟶ T'` a
first-order thickening with `T'` affine and `g` a global section of `T'`, the restriction map
`Γ(T', ⊤) ⟶ Γ(T'_g, ⊤)` carries the conormal module of `i` into the conormal module of
`i ∣_ D(g)`, `Γ(T, ⊤)`-linearly. -/
noncomputable def conormalRestrict :
    letI := isAffine_preimage_basicOpen hi g
    letI : IsAffine ((T'.basicOpen g : T'.Opens) : Scheme.{u}) :=
      (isAffine_basicOpen_of_isFirstOrderThickening hi g).1
    letI := thickeningKerModule hi
    letI := thickeningKerModule (isFirstOrderThickening_basicOpen hi g)
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen g)
      (RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom)
    RingHom.ker i.appTop.hom →ₗ[Γ(T, (⊤ : T.Opens))]
      RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom :=
  let := isAffine_preimage_basicOpen hi g
  let : IsAffine ((T'.basicOpen g : T'.Opens) : Scheme.{u}) :=
    (isAffine_basicOpen_of_isFirstOrderThickening hi g).1
  let := thickeningKerModule hi
  let := thickeningKerModule (isFirstOrderThickening_basicOpen hi g)
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen g)
    (RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom)
  { toFun := fun x ↦ ⟨(T'.basicOpen g).ι.appTop.hom (x : Γ(T', (⊤ : T'.Opens))), by
      rw [RingHom.mem_ker, appTop_morphismRestrict_comm i (T'.basicOpen g),
        RingHom.mem_ker.mp x.2, map_zero]⟩
    map_add' := fun x y ↦ Subtype.ext (map_add _ _ _)
    map_smul' := fun c x ↦ Subtype.ext (by
      obtain ⟨r, hr⟩ := surjective_appTop_of_isFirstOrderThickening hi c
      rw [RingHom.id_apply, coe_smul_conormal_basicOpen hi g hr]
      change (T'.basicOpen g).ι.appTop.hom ((c • x : RingHom.ker i.appTop.hom) :
          Γ(T', (⊤ : T'.Opens))) = _
      rw [coe_smul_conormal hi hr, map_mul]) }

/-- The value of `Stacks.Smooth.conormalRestrict` is the restriction of the section to the basic
open. -/
theorem conormalRestrict_apply (x : RingHom.ker i.appTop.hom) :
    ((conormalRestrict hi g x : RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom) :
        Γ(((T'.basicOpen g : T'.Opens) : Scheme.{u}), (⊤ : _root_.TopologicalSpace.Opens _))) =
      (T'.basicOpen g).ι.appTop.hom (x : Γ(T', (⊤ : T'.Opens))) :=
  rfl

/-- **The conormal module of a thickening localizes.** Let `i : T ⟶ T'` be a first-order
thickening with `T'` affine and let `g` be a global section of `T'`. Then the conormal module of
the restricted thickening `i ∣_ T'.basicOpen g` is the localization of the conormal module of `i`
away from the image `i.appTop g`, through `Stacks.Smooth.conormalRestrict`.

This is the coefficient half of the Čech input of step (II) of [Stacks Project, Tag 02H6]; the
half for `a^*Ω_{X/S}` is `Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'`.

The statement is deduced from the algebraic
`Stacks.Smooth.isLocalizedModule_ker_of_isLocalization_away` over the ring `Γ(T', ⊤)`, with the
two localizations supplied by `AlgebraicGeometry.Γ_restrict_isLocalization`, and transported to
the ring `Γ(T, ⊤)` by `IsLocalizedModule.of_restrictScalars`. -/
theorem isLocalizedModule_conormalRestrict :
    letI := isAffine_preimage_basicOpen hi g
    letI : IsAffine ((T'.basicOpen g : T'.Opens) : Scheme.{u}) :=
      (isAffine_basicOpen_of_isFirstOrderThickening hi g).1
    letI := thickeningKerModule hi
    letI := thickeningKerModule (isFirstOrderThickening_basicOpen hi g)
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen g)
      (RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom)
    IsLocalizedModule.Away (i.appTop.hom g) (conormalRestrict hi g) := by
  have hci : IsClosedImmersion i := hi.1
  have hTa : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  let := isAffine_preimage_basicOpen hi g
  let : IsAffine ((T'.basicOpen g : T'.Opens) : Scheme.{u}) :=
    (isAffine_basicOpen_of_isFirstOrderThickening hi g).1
  let := thickeningKerModule hi
  let := thickeningKerModule (isFirstOrderThickening_basicOpen hi g)
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen g)
    (RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom)
  -- the localization of `Γ(T, ⊤)` away from `i.appTop g`, read on `i ⁻¹ᵁ D(g)`
  have hloc : IsLocalization.Away (i.appTop.hom g)
      Γ(((i ⁻¹ᵁ T'.basicOpen g : T.Opens) : Scheme.{u}),
        (⊤ : _root_.TopologicalSpace.Opens _)) :=
    (Scheme.preimage_basicOpen_top i g) ▸ Γ_restrict_isLocalization T (i.appTop.hom g)
  -- `Γ(T, ⊤)` is an algebra over `Γ(T', ⊤)`, and both conormal modules are towers
  let := i.appTop.hom.toAlgebra
  have htow₁ : IsScalarTower Γ(T', (⊤ : T'.Opens)) Γ(T, (⊤ : T.Opens))
      (RingHom.ker i.appTop.hom) :=
    IsScalarTower.of_algebraMap_smul (thickeningKerModule_smul hi)
  have htow₂ : IsScalarTower Γ(T', (⊤ : T'.Opens)) Γ(T, (⊤ : T.Opens))
      (RingHom.ker (i ∣_ T'.basicOpen g).appTop.hom) :=
    IsScalarTower.of_algebraMap_smul (conormal_smul hi g)
  have hcore : IsLocalizedModule.Away g
      ((conormalRestrict hi g).restrictScalars Γ(T', (⊤ : T'.Opens))) :=
    isLocalizedModule_ker_of_isLocalization_away (appTop_morphismRestrict_comm i (T'.basicOpen g)) _
      (conormalRestrict_apply hi g)
  have h := IsLocalizedModule.of_restrictScalars (Submonoid.powers g) (conormalRestrict hi g)
  rwa [Algebra.algebraMapSubmonoid_powers] at h

end Geometric

end Stacks.Smooth

end
