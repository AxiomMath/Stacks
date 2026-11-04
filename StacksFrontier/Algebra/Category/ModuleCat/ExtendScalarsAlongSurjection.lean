module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Extension of scalars along a surjection, on modules killed by the kernel

Let `f : R →+* S` be a surjective homomorphism of commutative rings and let `M` be an `R`-module
annihilated by `RingHom.ker f`. Such an `M` is really a module over `S`, and extension of scalars
does nothing to it: the map `m ↦ 1 ⊗ m` from `M` to `S ⊗_R M` is bijective. Surjectivity is the
computation `s ⊗ m = f a ⊗ m = 1 ⊗ a • m` for any `a : R` above `s`, and injectivity comes from
the left inverse `s ⊗ m ↦ a • m`, which is well defined precisely because two elements of `R` with
the same image under `f` differ by an element of `RingHom.ker f` and therefore act equally on `M`.

Categorically this says that the unit of the adjunction
`ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f` is an isomorphism at every such `M`, and
hence — by the naturality square of that unit — that extension of scalars along `f` reflects
isomorphisms between modules annihilated by `RingHom.ker f`.

## Main results

* `Stacks.ModuleCat.smul_eq_smul_of_apply_eq`: on a module annihilated by `RingHom.ker f`, two
  elements of `R` with the same image under `f` act by the same map.
* `Stacks.ModuleCat.bijective_one_tmul`: **for `f` surjective and `M` annihilated by
  `RingHom.ker f`, the map `m ↦ 1 ⊗ m` from `M` to `S ⊗_R M` is bijective.**
* `Stacks.ModuleCat.bijective_unit_app`: that map is the unit of
  `ModuleCat.extendRestrictScalarsAdj f` at `M`.
* `Stacks.ModuleCat.isIso_extendRestrictScalarsAdj_unit_app`: so the unit is an isomorphism at
  such an `M`.
* `Stacks.ModuleCat.isIso_of_isIso_extendScalars_map`: **extension of scalars along a surjection
  reflects isomorphisms between modules annihilated by its kernel.**
* `Stacks.ModuleCat.isIso_extendRestrictScalarsAdj_counit_app`: **for `f` surjective the counit
  `S ⊗_R N ⟶ N` is an isomorphism at every `S`-module `N`.**

## Implementation notes

The `Module R S` used by `ModuleCat.extendScalars` is `Module.compHom S f`, which is not an
instance; it is supplied by the scoped `⊗ₜ[R,f]` notation inside the statements, and introduced as
a local instance by a `let` inside the proofs. The left inverse of `m ↦ 1 ⊗ m` is built as a
`TensorProduct.lift` of the `R`-bilinear map `(s, m) ↦ g s • m` for an arbitrary set-theoretic
section `g` of `f`; no linearity of `g` is needed, because `smul_eq_smul_of_apply_eq` makes the
action of `g s` on `M` independent of the choice of `g`.

**The counit.** Restriction of scalars along `f` lands in modules annihilated by `RingHom.ker f`,
so the unit of the adjunction is an isomorphism at `(ModuleCat.restrictScalars f).obj N` for every
`S`-module `N`. The triangle identity then makes `(ModuleCat.restrictScalars f).map` of the counit
at `N` an isomorphism, and restriction of scalars reflects isomorphisms.
-/

@[expose] public section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe v u

namespace Stacks.ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- If `RingHom.ker f` annihilates `M`, then any two elements of `R` with the same image under
`f` act on `M` by the same map: their difference lies in `RingHom.ker f`. -/
theorem smul_eq_smul_of_apply_eq (hM : ∀ a ∈ RingHom.ker f, ∀ m : M, a • m = 0)
    {a b : R} (hab : f a = f b) (m : M) : a • m = b • m := by
  have h : (a - b) • m = 0 := hM _ (by simp [RingHom.mem_ker, hab]) m
  rwa [sub_smul, sub_eq_zero] at h

/-- **Extension of scalars along a surjection does nothing to a module killed by the kernel:**
if `f : R →+* S` is surjective and `RingHom.ker f` annihilates the `R`-module `M`, then
`m ↦ 1 ⊗ m` is a bijection from `M` onto `S ⊗_R M`. -/
theorem bijective_one_tmul (hf : Function.Surjective f)
    (hM : ∀ a ∈ RingHom.ker f, ∀ m : M, a • m = 0) :
    Function.Bijective (fun m : M => (1 : S) ⊗ₜ[R,f] m) := by
  let inst : Module R S := Module.compHom S f
  have hsmul : ∀ (r : R) (s : S), r • s = f r * s := fun _ _ => rfl
  obtain ⟨g, hfg⟩ : ∃ g : S → R, ∀ s, f (g s) = s :=
    ⟨Function.surjInv hf, fun s => Function.surjInv_eq hf s⟩
  let b : S →ₗ[R] M →ₗ[R] M :=
    { toFun := fun s => g s • LinearMap.id
      map_add' := fun s t => by
        ext m
        show g (s + t) • m = g s • m + g t • m
        rw [← add_smul]
        exact smul_eq_smul_of_apply_eq f hM (by rw [hfg, map_add, hfg, hfg]) m
      map_smul' := fun r s => by
        ext m
        show g (r • s) • m = r • (g s • m)
        rw [smul_smul]
        exact smul_eq_smul_of_apply_eq f hM (by rw [hfg, map_mul, hfg, hsmul]) m }
  have hb : ∀ m : M, TensorProduct.lift b ((1 : S) ⊗ₜ[R,f] m) = m := fun m => by
    show g (1 : S) • m = m
    rw [smul_eq_smul_of_apply_eq f hM (a := g 1) (b := 1) (by rw [hfg, map_one]) m, one_smul]
  refine ⟨Function.LeftInverse.injective hb, fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s m =>
      refine ⟨g s • m, ?_⟩
      show (1 : S) ⊗ₜ[R,f] (g s • m) = s ⊗ₜ[R,f] m
      rw [← TensorProduct.smul_tmul]
      congr 1
      rw [hsmul, mul_one, hfg]
  | add x y hx hy =>
      obtain ⟨mx, rfl⟩ := hx
      obtain ⟨my, rfl⟩ := hy
      exact ⟨mx + my, TensorProduct.tmul_add _ _ _⟩

/-- The unit of `ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f` at `M` is the map
`m ↦ 1 ⊗ m`, so it is bijective when `f` is surjective and `RingHom.ker f` annihilates `M`. -/
theorem bijective_unit_app (hf : Function.Surjective f) (M : ModuleCat.{u} R)
    (hM : ∀ a ∈ RingHom.ker f, ∀ m : M, a • m = 0) :
    Function.Bijective ((ModuleCat.extendRestrictScalarsAdj f).unit.app M) :=
  bijective_one_tmul f hf hM

/-- The unit of `ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f` is an isomorphism at an
`R`-module annihilated by `RingHom.ker f`, when `f` is surjective. -/
theorem isIso_extendRestrictScalarsAdj_unit_app (hf : Function.Surjective f)
    (M : ModuleCat.{u} R) (hM : ∀ a ∈ RingHom.ker f, ∀ m : M, a • m = 0) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj f).unit.app M) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_unit_app f hf M hM

/-- **Extension of scalars along a surjection reflects isomorphisms between modules annihilated
by its kernel.** The unit of the adjunction is an isomorphism at both ends, and its naturality
square factors `g` through the base change of `g`. -/
theorem isIso_of_isIso_extendScalars_map (hf : Function.Surjective f)
    {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (hM : ∀ a ∈ RingHom.ker f, ∀ m : M, a • m = 0)
    (hN : ∀ a ∈ RingHom.ker f, ∀ n : N, a • n = 0)
    (hg : IsIso ((ModuleCat.extendScalars f).map g)) : IsIso g := by
  have := isIso_extendRestrictScalarsAdj_unit_app f hf M hM
  have := isIso_extendRestrictScalarsAdj_unit_app f hf N hN
  have : IsIso ((ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f).map g) := by
    rw [Functor.comp_map]
    infer_instance
  exact IsIso.of_isIso_fac_right ((ModuleCat.extendRestrictScalarsAdj f).unit.naturality g)

/-- Restriction of scalars along `f` is annihilated by `RingHom.ker f`: an element of the kernel
acts through its image, which is `0`. -/
theorem smul_restrictScalars_eq_zero (N : ModuleCat.{u} S) (a : R) (ha : a ∈ RingHom.ker f)
    (n : (ModuleCat.restrictScalars f).obj N) : a • n = 0 := by
  rw [show a • n = f a • n from rfl, RingHom.mem_ker.1 ha, zero_smul]

/-- **The counit of `ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f` is an isomorphism
when `f` is surjective:** for an `S`-module `N`, the map `S ⊗_R N ⟶ N` sending `s ⊗ n` to `s • n`
is invertible. Indeed `N` read over `R` is annihilated by `RingHom.ker f`, so the unit of the
adjunction is invertible there; the triangle identity exhibits the restriction of the counit as a
factor of an identity with an invertible first factor, and restriction of scalars reflects
isomorphisms. -/
theorem isIso_extendRestrictScalarsAdj_counit_app (hf : Function.Surjective f)
    (N : ModuleCat.{u} S) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj f).counit.app N) := by
  have := isIso_extendRestrictScalarsAdj_unit_app f hf ((ModuleCat.restrictScalars f).obj N)
    (fun a ha n => smul_restrictScalars_eq_zero f N a ha n)
  have := IsIso.of_isIso_fac_left
    ((ModuleCat.extendRestrictScalarsAdj f).right_triangle_components N)
  exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars f)

end Stacks.ModuleCat

end
