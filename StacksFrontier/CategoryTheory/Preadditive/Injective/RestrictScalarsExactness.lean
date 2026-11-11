module

public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import StacksFrontier.CategoryTheory.Preadditive.Injective.ChangeOfRings

import StacksCore.Tactic.StacksAttribute

/-!
# Restriction and extension of scalars, and injective modules

For a map of commutative rings `f : R →+* S`, extension of scalars `v = - ⊗_R S` is left
adjoint to restriction of scalars `u`; `u` is exact and `v` is right exact. For the conditions
of Stacks, Tag 015Z (`v` preserves monomorphisms, `v` is exact, `u` preserves injectives) the
example `ℤ → ℤ/pℤ` shows that they fail in general: `ℤ/pℤ` is an injective `ℤ/pℤ`-module but
not an injective `ℤ`-module. Together with
`ModuleCat.flat_iff_restrictScalars_preservesInjectiveObjects` this is Stacks, Tag 03B8.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- For a prime `p`, the abelian group `ℤ/pℤ` is not an injective `ℤ`-module, whatever
`ℤ`-module structure it is given (there is only one). -/
theorem ZMod.not_module_injective_int (p : ℕ) [hp : Fact p.Prime] [inst : Module ℤ (ZMod p)] :
    ¬ Module.Injective ℤ (ZMod p) := by
  obtain rfl : inst = AddCommGroup.toIntModule (ZMod p) := Subsingleton.elim _ _
  intro h
  have hinj : Function.Injective ((p : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
    intro a b hab
    simpa [hp.out.ne_zero] using hab
  obtain ⟨g, hg⟩ := h.out ((p : ℤ) • LinearMap.id) hinj (Int.castAddHom (ZMod p)).toIntLinearMap
  have h1 := hg 1
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul, mul_one,
    AddMonoidHom.coe_toIntLinearMap] at h1
  rw [show g (p : ℤ) = (p : ℤ) • g 1 by rw [← map_zsmul, smul_eq_mul, mul_one]] at h1
  simp at h1

/-- **Stacks Project, Tag 03B8.**  Let `f : R →+* S` be a ring map, `u` restriction of scalars
and `v = - ⊗_R S` extension of scalars. Then `u` is right adjoint to `v` (Mathlib's
`ModuleCat.extendRestrictScalarsAdj`), `u` is exact and `v` is right exact. -/
@[stacks 03B8 "adjunction and exactness"]
theorem ModuleCat.extendScalars_adj_restrictScalars_exactness
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Nonempty (ModuleCat.extendScalars.{u, u, u} f ⊣ ModuleCat.restrictScalars.{u, u, u} f) ∧
      (PreservesFiniteLimits (ModuleCat.restrictScalars.{u, u, u} f) ∧
        PreservesFiniteColimits (ModuleCat.restrictScalars.{u, u, u} f)) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} f
  have : PreservesLimits (ModuleCat.restrictScalars.{u, u, u} f) :=
    adj.rightAdjoint_preservesLimits
  have : PreservesColimits (ModuleCat.restrictScalars.{u, u, u} f) :=
    (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  have : PreservesColimits (ModuleCat.extendScalars.{u, u, u} f) :=
    adj.leftAdjoint_preservesColimits.{u, u}
  exact ⟨⟨adj⟩, ⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- **Stacks Project, Tag 03B8.**  For a prime `p` and `f : ℤ → ℤ/pℤ`, the injective
`ℤ/pℤ`-module `ℤ/pℤ` is not an injective `ℤ`-module, so for this ring map none of the
conditions of Stacks, Tag 015Z holds: extension of scalars does not preserve monomorphisms,
is not exact, and restriction of scalars does not preserve injective objects. -/
@[stacks 03B8 "the counterexample ℤ → ℤ/pℤ"]
theorem ModuleCat.not_restrictScalars_preservesInjectiveObjects_intCast_zmod
    (p : ℕ) [hp : Fact p.Prime] :
    Injective (ModuleCat.of (ZMod p) (ZMod p)) ∧
      ¬ Injective ((ModuleCat.restrictScalars.{0, 0, 0} (Int.castRingHom (ZMod p))).obj
        (ModuleCat.of (ZMod p) (ZMod p))) ∧
      ¬ (ModuleCat.extendScalars.{0, 0, 0} (Int.castRingHom (ZMod p))).PreservesMonomorphisms ∧
      ¬ (PreservesFiniteLimits (ModuleCat.extendScalars.{0, 0, 0} (Int.castRingHom (ZMod p))) ∧
        PreservesFiniteColimits (ModuleCat.extendScalars.{0, 0, 0} (Int.castRingHom (ZMod p)))) ∧
      ¬ (ModuleCat.restrictScalars.{0, 0, 0}
        (Int.castRingHom (ZMod p))).PreservesInjectiveObjects := by
  set f := Int.castRingHom (ZMod p)
  let U := ModuleCat.restrictScalars.{0, 0, 0} f
  let V := ModuleCat.extendScalars.{0, 0, 0} f
  let adj : V ⊣ U := ModuleCat.extendRestrictScalarsAdj.{0, 0, 0} f
  have : V.Additive := adj.left_adjoint_additive
  have hS : Injective (ModuleCat.of (ZMod p) (ZMod p)) :=
    have := Module.injective_of_isSemisimpleRing (ZMod p) (ZMod p)
    Module.injective_object_of_injective_module (ZMod p) (ZMod p)
  have hR : ¬ Injective (U.obj (ModuleCat.of (ZMod p) (ZMod p))) := by
    intro h
    let : Module ℤ (ZMod p) := Module.compHom (ZMod p) f
    exact ZMod.not_module_injective_int p
      (Module.injective_module_of_injective_object (inj := h) ℤ (ZMod p))
  have hc : ¬ U.PreservesInjectiveObjects := fun h ↦ hR (U.injective_obj _)
  have hb : ¬ (PreservesFiniteLimits V ∧ PreservesFiniteColimits V) :=
    fun h ↦ hc (preservesInjectiveObjects_of_isExact U V adj h)
  refine ⟨hS, hR, fun h ↦ hb (@isExact_of_preservesMonomorphisms _ _ _ _ _ _ U V _ _ adj h), hb, hc⟩

/-- **Stacks Project, Tag 03B8**, all of it.  For every ring map `f : R →+* S`, extension of
scalars `v` is left adjoint to restriction of scalars `u`, `u` is exact, `v` is right exact, and
`u` takes all injective `S`-modules to injective `R`-modules if and only if `f` is flat; the
conditions of Stacks, Tag 015Z fail for `ℤ → ℤ/pℤ` with `p` prime, where `ℤ/pℤ` is an
injective `ℤ/pℤ`-module but not an injective `ℤ`-module. -/
@[stacks 03B8]
theorem ModuleCat.restrictScalars_extendScalars_injective_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (Nonempty (ModuleCat.extendScalars.{u, u, u} f ⊣ ModuleCat.restrictScalars.{u, u, u} f) ∧
      (PreservesFiniteLimits (ModuleCat.restrictScalars.{u, u, u} f) ∧
        PreservesFiniteColimits (ModuleCat.restrictScalars.{u, u, u} f)) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f)) ∧
    (∀ (p : ℕ) [Fact p.Prime],
      Injective (ModuleCat.of (ZMod p) (ZMod p)) ∧
      ¬ Injective ((ModuleCat.restrictScalars.{0, 0, 0} (Int.castRingHom (ZMod p))).obj
        (ModuleCat.of (ZMod p) (ZMod p))) ∧
      ¬ (ModuleCat.extendScalars.{0, 0, 0} (Int.castRingHom (ZMod p))).PreservesMonomorphisms ∧
      ¬ (PreservesFiniteLimits (ModuleCat.extendScalars.{0, 0, 0} (Int.castRingHom (ZMod p))) ∧
        PreservesFiniteColimits (ModuleCat.extendScalars.{0, 0, 0} (Int.castRingHom (ZMod p)))) ∧
      ¬ (ModuleCat.restrictScalars.{0, 0, 0}
        (Int.castRingHom (ZMod p))).PreservesInjectiveObjects) ∧
    (f.Flat ↔ (ModuleCat.restrictScalars.{u, u, u} f).PreservesInjectiveObjects) :=
  ⟨ModuleCat.extendScalars_adj_restrictScalars_exactness f,
    fun p _ ↦ ModuleCat.not_restrictScalars_preservesInjectiveObjects_intCast_zmod p,
    ModuleCat.flat_iff_restrictScalars_preservesInjectiveObjects f⟩
