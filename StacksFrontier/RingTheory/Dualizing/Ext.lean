module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsion
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Coreflection
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Ext from a power-torsion module is unchanged by flat base change

Let `A → B` be a flat ring map and let `I ⊆ A` be a finitely generated ideal such that
`A/I → B/IB` is an isomorphism. Then, for every object `K` of `D(A)` whose cohomology modules
are `I`-power torsion and every object `X` of `D(A)`, derived extension of scalars induces a
bijection `Hom_{D(A)}(K, X) ≃ Hom_{D(B)}(K ⊗ᴸ_A B, X ⊗ᴸ_A B)`. Taking `K` and `X` to be
modules placed in degree zero and their shifts gives the isomorphism
`Ext^i_A(M, N) ≅ Ext^i_B(M ⊗_A B, N ⊗_A B)` for `M` an `I`-power torsion module.

The proof runs through the coreflection of `D(A)` onto the objects with `I`-power-torsion
cohomology, which is built by iterating, over a finite generating set `f₁, …, f_r` of `I`, the
fibre of the localization map `X ⟶ X[1/f_j]`. Three things make the argument work: an object of
`D(A)` has `I`-power-torsion cohomology exactly when all its localizations `X[1/f_j]` vanish;
a morphism from such an object into an `f`-local object vanishes; and `- ⊗_A B` carries
`f`-local modules to `f`-local modules, since it preserves invertibility of multiplication by
`f`. Consequently the coreflection `Y ⟶ X` stays a coreflection after applying
`- ⊗ᴸ_A B` viewed in `D(A)`, while on `Y` itself the unit `Y ⟶ (Y ⊗ᴸ_A B)_A` is already an
isomorphism because `Y` is `I`-power torsion — this last point is where flatness and the
isomorphism `A/I ≅ B/IB` enter, through Stacks 05E9.

## Main definitions

* `Dualizing.PowerTorsionBaseChange.locFunctor`, `Dualizing.PowerTorsionBaseChange.locUnit` —
  localization away from an element, as an endofunctor of `A`-modules, and its unit.
* `Dualizing.PowerTorsionBaseChange.locDerived`,
  `Dualizing.PowerTorsionBaseChange.locDerivedUnit` — the same on the derived category.

## Main results

* `Dualizing.PowerTorsionBaseChange.exists_finite_localization_coreflection` — the coreflection
  onto the objects killed by a finite family of idempotent localizations, together with the
  statement that a compatible triangulated functor carries it to a coreflection.
* `Dualizing.PowerTorsionBaseChange.bijective_mapDerivedCategory_map_of_powerTorsion` —
  derived extension of scalars is bijective on morphisms out of an object with
  `I`-power-torsion cohomology.
* `Dualizing.PowerTorsionBaseChange.bijective_extBaseChange_of_powerTorsion` — the induced map
  on `Ext` groups out of an `I`-power torsion module is bijective in every degree.

## References

* [Stacks Project, Tag 05EH](https://stacks.math.columbia.edu/tag/05EH)
* [Stacks Project, Tag 05E9](https://stacks.math.columbia.edu/tag/05E9)
* [Stacks Project, Tag 0AM0](https://stacks.math.columbia.edu/tag/0AM0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

universe w u₁ u₂ v u

namespace Dualizing.PowerTorsionBaseChange

attribute [local instance] HasDerivedCategory.standard

section Localizations

variable {A : Type u} [CommRing A]

/-- Flat extension of scalars preserves finite limits, also when the source and target
rings inhabit different universes. -/
theorem preservesFiniteLimits_extendScalars_flat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (hflat : Module.Flat R S) :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, v, max v (max u w)} (algebraMap R S)) := by
  have hf : (algebraMap R S).Flat := RingHom.flat_algebraMap_iff.mpr hflat
  let := (algebraMap R S).toAlgebra
  have : Module.Flat R S := hf
  let F := ModuleCat.extendScalars.{u, v, max v (max u w)} (algebraMap R S)
  let : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} (algebraMap R S)).isLeftAdjoint
  have : F.Additive := by
    have : PreservesBinaryBiproducts F :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts F
    exact Functor.additive_of_preservesBinaryBiproducts F
  have h : ∀ S' : ShortComplex (ModuleCat.{max v (max u w)} R),
      S'.Exact → (S'.map F).Exact := by
    intro S' hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact Module.Flat.lTensor_exact S hS
  have hF : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    ((Functor.exact_tfae F).out 2 4).mp h
  exact hF.1

/-- `I`-power torsion transfers along an isomorphism of modules. -/
lemma isIPowerTorsion_of_moduleIso {R : Type u₁} [CommRing R] {I : Ideal R}
    (M N : ModuleCat.{w} R) (e : M ≅ N) (hN : IsIPowerTorsion R N I) :
    IsIPowerTorsion R M I := by
  intro m
  obtain ⟨k, hk, hkill⟩ := hN (e.hom m)
  refine ⟨k, hk, fun a ha ↦ ?_⟩
  simpa only [map_smul, map_zero, ← ModuleCat.comp_apply, e.hom_inv_id, ModuleCat.id_apply]
    using congrArg e.inv (hkill a ha)

/-- A zero module is `I`-power torsion. -/
lemma isIPowerTorsion_of_isZero {R : Type u₁} [CommRing R] (I : Ideal R) (Y : ModuleCat.{w} R)
    (h : IsZero Y) : IsIPowerTorsion R Y I := by
  have : Subsingleton Y := ModuleCat.isZero_iff_subsingleton.mp h
  exact fun m => ⟨1, Nat.one_pos, fun a _ => Subsingleton.elim _ _⟩

/-- Postcomposition with an isomorphism is bijective on morphisms. -/
lemma bijective_comp_right {D' : Type*} [Category D'] {X Y Z : D'} (e : Y ⟶ Z) [IsIso e] :
    Function.Bijective (fun f : X ⟶ Y => f ≫ e) :=
  ⟨fun _ _ h => (cancel_mono e).1 h, fun g => ⟨g ≫ inv e, by simp⟩⟩

/-- Precomposition with an isomorphism is bijective on morphisms. -/
lemma bijective_comp_left {D' : Type*} [Category D'] {X Y Z : D'} (e : X ⟶ Y) [IsIso e] :
    Function.Bijective (fun f : Y ⟶ Z => e ≫ f) :=
  ⟨fun _ _ h => (cancel_epi e).1 h, fun g => ⟨inv e ≫ g, by simp⟩⟩

/-! ### Localization away from an element, as an endofunctor of modules -/

/-- Localization away from `f`, as an endofunctor of the category of `A`-modules: it is
extension of scalars to `A[1/f]` followed by restriction of scalars. -/
def locFunctor (f : A) : ModuleCat.{max v u} A ⥤ ModuleCat.{max v u} A :=
  ModuleCat.extendScalars.{u, u, max v u} (algebraMap A (Localization.Away f)) ⋙
    ModuleCat.restrictScalars.{max v u, u, u} (algebraMap A (Localization.Away f))

/-- The localization maps `M ⟶ M[1/f]`, as a natural transformation out of the identity. -/
def locUnit (f : A) : 𝟭 (ModuleCat.{max v u} A) ⟶ locFunctor.{v} f :=
  (ModuleCat.extendRestrictScalarsAdj.{v, u, u} (algebraMap A (Localization.Away f))).unit

/-- The localization map is `n ↦ 1 ⊗ n`. -/
lemma locUnit_app_apply (f : A) (N : ModuleCat.{max v u} A) (n : N) :
    (locUnit.{v} f).app N n
      = IPowerTorsion.tensorModuleCatEquiv.{u, u, v} (R := A) (S := Localization.Away f) N
          ((1 : Localization.Away f) ⊗ₜ[A] n) := rfl

/-- Localization away from `f` is additive. -/
instance locFunctor_additive (f : A) : (locFunctor.{v} f).Additive := by
  let F := ModuleCat.extendScalars.{u, u, max v u} (algebraMap A (Localization.Away f))
  let : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u}
      (algebraMap A (Localization.Away f))).isLeftAdjoint
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  exact inferInstanceAs ((F ⋙ _).Additive)

/-- Localization away from `f` is left exact. -/
instance locFunctor_preservesFiniteLimits (f : A) :
    PreservesFiniteLimits (locFunctor.{v} f) := by
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u}
      (algebraMap A (Localization.Away f))) :=
    preservesFiniteLimits_extendScalars_flat (R := A) (S := Localization.Away f)
      (IsLocalization.flat _ (Submonoid.powers f))
  exact comp_preservesFiniteLimits _ _

/-- Localization away from `f` is right exact. -/
instance locFunctor_preservesFiniteColimits (f : A) :
    PreservesFiniteColimits (locFunctor.{v} f) :=
  comp_preservesFiniteColimits _ _

/-- The carrier of `M[1/f]` is `A[1/f] ⊗[A] M`, `A`-linearly. -/
def locCarrierEquiv (f : A) (M : ModuleCat.{max v u} A) :
    TensorProduct A (Localization.Away f) M ≃ₗ[A] (locFunctor.{v} f).obj M where
  toFun x := IPowerTorsion.tensorModuleCatEquiv.{u, u, v} (R := A) (S := Localization.Away f) M x
  invFun y := (IPowerTorsion.tensorModuleCatEquiv.{u, u, v}
    (R := A) (S := Localization.Away f) M).symm y
  left_inv := (IPowerTorsion.tensorModuleCatEquiv.{u, u, v}
    (R := A) (S := Localization.Away f) M).left_inv
  right_inv := (IPowerTorsion.tensorModuleCatEquiv.{u, u, v}
    (R := A) (S := Localization.Away f) M).right_inv
  map_add' := map_add _
  map_smul' a x := by
    change IPowerTorsion.tensorModuleCatEquiv.{u, u, v}
      (R := A) (S := Localization.Away f) M (a • x) = _
    rw [show (a • x) = (algebraMap A (Localization.Away f) a) • x from
      (IsScalarTower.algebraMap_smul _ a x).symm, map_smul]
    rfl

/-- The map `M ⟶ M[1/f]` exhibits `M[1/f]` as the localization of `M` at the powers of `f`. -/
lemma isLocalizedModule_locUnit (f : A) (M : ModuleCat.{max v u} A) :
    IsLocalizedModule (Submonoid.powers f) ((locUnit.{v} f).app M).hom := by
  have h : ((locUnit.{v} f).app M).hom
      = (locCarrierEquiv.{v} f M : TensorProduct A (Localization.Away f) M →ₗ[A]
          (locFunctor.{v} f).obj M).comp
        (TensorProduct.mk A (Localization.Away f) M 1) := rfl
  rw [h]
  exact IsLocalizedModule.of_linearEquiv _ (TensorProduct.mk A (Localization.Away f) M 1)
    (locCarrierEquiv.{v} f M)


/-- Multiplication by a unit is invertible on any module. -/
lemma isIso_smul_of_isUnit {S : Type u₂} [CommRing S] {s : S} (hs : IsUnit s)
    (X : ModuleCat.{w} S) : IsIso (s • 𝟙 X) := by
  obtain ⟨t, rfl⟩ := hs
  refine ⟨(↑t⁻¹ : S) • 𝟙 X, ?_, ?_⟩ <;>
    rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul]
  · rw [Units.mul_inv, one_smul]
  · rw [Units.inv_mul, one_smul]

/-- Multiplication by `c` on a module restricted along a ring map is multiplication by the
image of `c`. -/
lemma smul_restrictScalars_eq {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    (φ : R →+* S) (c : R) (X : ModuleCat.{w} S) :
    c • 𝟙 ((ModuleCat.restrictScalars.{w, u₁, u₂} φ).obj X)
      = (ModuleCat.restrictScalars.{w, u₁, u₂} φ).map ((φ c) • 𝟙 X) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Extension of scalars turns multiplication by `c` into multiplication by the image of `c`. -/
lemma extendScalars_map_smul {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    (φ : R →+* S) (c : R) (N : ModuleCat.{max w u₂} R) :
    (ModuleCat.extendScalars.{u₁, u₂, max w u₂} φ).map (c • 𝟙 N)
      = (φ c) • 𝟙 ((ModuleCat.extendScalars.{u₁, u₂, max w u₂} φ).obj N) := by
  have key : ∀ (m : (ModuleCat.restrictScalars.{u₂, u₁, u₂} φ).obj (ModuleCat.of S S))
      (x : N), (m ⊗ₜ[R] (c • x) : TensorProduct R _ _) = (c • m) ⊗ₜ[R] x :=
    fun m x => TensorProduct.tmul_smul c m x
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  show ((1 : S) ⊗ₜ[R, φ] (c • n) : (ModuleCat.extendScalars.{u₁, u₂, max w u₂} φ).obj N)
      = (φ c * (1 : S)) ⊗ₜ[R, φ] n
  exact key (1 : S) n

/-- Multiplication by `c` is invertible on a module obtained by restriction of scalars along a
ring map sending `c` to a unit. -/
lemma isIso_smul_restrictScalars {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    {φ : R →+* S} {c : R} (hc : IsUnit (φ c)) (X : ModuleCat.{w} S) :
    IsIso (c • 𝟙 ((ModuleCat.restrictScalars.{w, u₁, u₂} φ).obj X)) := by
  rw [smul_restrictScalars_eq]
  have := isIso_smul_of_isUnit hc X
  infer_instance

/-- Extension followed by restriction of scalars preserves invertibility of multiplication
by a ring element. -/
lemma isIso_smul_extendRestrictScalars {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    (φ : R →+* S) {c : R} (N : ModuleCat.{max w u₂} R) (h : IsIso (c • 𝟙 N)) :
    IsIso (c • 𝟙 ((ModuleCat.extendScalars.{u₁, u₂, max w u₂} φ ⋙
      ModuleCat.restrictScalars.{max w u₂, u₁, u₂} φ).obj N)) := by
  have hEq : c • 𝟙 ((ModuleCat.extendScalars.{u₁, u₂, max w u₂} φ ⋙
      ModuleCat.restrictScalars.{max w u₂, u₁, u₂} φ).obj N) =
      (ModuleCat.extendScalars.{u₁, u₂, max w u₂} φ ⋙
        ModuleCat.restrictScalars.{max w u₂, u₁, u₂} φ).map (c • 𝟙 N) := by
    rw [Functor.comp_map, extendScalars_map_smul, ← smul_restrictScalars_eq]
    rfl
  rw [hEq]
  have := h
  infer_instance

/-- The element `f` becomes a unit in `A[1/f]`. -/
lemma isUnit_algebraMap_away (f : A) :
    IsUnit (algebraMap A (Localization.Away f) f) :=
  IsLocalization.map_units (Localization.Away f) ⟨f, Submonoid.mem_powers f⟩

/-- Multiplication by `f` is invertible on `M[1/f]`. -/
lemma isIso_smul_locFunctor (f : A) (M : ModuleCat.{max v u} A) :
    IsIso (f • 𝟙 ((locFunctor.{v} f).obj M)) :=
  isIso_smul_restrictScalars (isUnit_algebraMap_away f) _

/-- If multiplication by `f` is invertible on `N`, then `N ⟶ N[1/f]` is an isomorphism. -/
lemma isIso_locUnit_of_isIso_smul (f : A) (N : ModuleCat.{max v u} A)
    (h : IsIso (f • 𝟙 N)) : IsIso ((locUnit.{v} f).app N) := by
  have hu : ∀ s : Submonoid.powers f,
      IsUnit (algebraMap A (Module.End A N) (s : A)) := by
    rintro ⟨s, n, rfl⟩
    have h1 : IsUnit (algebraMap A (Module.End A N) f) := by
      refine ⟨⟨(f • 𝟙 N).hom, (inv (f • 𝟙 N)).hom, ?_, ?_⟩, ?_⟩
      · exact congrArg ModuleCat.Hom.hom (IsIso.inv_hom_id (f • 𝟙 N))
      · exact congrArg ModuleCat.Hom.hom (IsIso.hom_inv_id (f • 𝟙 N))
      · apply LinearMap.ext
        intro x
        simp [Module.algebraMap_end_apply]
    simpa only [map_pow] using h1.pow n
  let : IsLocalizedModule (Submonoid.powers f) (LinearMap.id : N →ₗ[A] N) :=
    { map_units := hu
      surj x := ⟨⟨x, 1⟩, by simp⟩
      exists_of_eq h := ⟨1, by simpa using h⟩ }
  let : IsLocalizedModule (Submonoid.powers f) ((locUnit.{v} f).app N).hom :=
    isLocalizedModule_locUnit.{v} f N
  have he : (IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LinearMap.id : N →ₗ[A] N) ((locUnit.{v} f).app N).hom).toLinearMap =
      ((locUnit.{v} f).app N).hom :=
    LinearMap.ext fun x => IsLocalizedModule.linearEquiv_apply (Submonoid.powers f) _ _ x
  have hb : Function.Bijective (((locUnit.{v} f).app N).hom) := by
    rw [← he]
    exact (IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LinearMap.id : N →ₗ[A] N) ((locUnit.{v} f).app N).hom).bijective
  exact (ConcreteCategory.isIso_iff_bijective _).2 hb

/-- `M[1/f] ⟶ M[1/f]` is already a localization: the two canonical maps agree. -/
lemma locFunctor_map_locUnit_eq (f : A) (M : ModuleCat.{max v u} A) :
    (locFunctor.{v} f).map ((locUnit.{v} f).app M)
      = (locUnit.{v} f).app ((locFunctor.{v} f).obj M) := by
  apply ModuleCat.hom_ext
  let : IsLocalizedModule (Submonoid.powers f) ((locUnit.{v} f).app M).hom :=
    isLocalizedModule_locUnit.{v} f M
  let : IsLocalizedModule (Submonoid.powers f)
      ((locUnit.{v} f).app ((locFunctor.{v} f).obj M)).hom :=
    isLocalizedModule_locUnit.{v} f _
  refine IsLocalizedModule.ext (Submonoid.powers f) ((locUnit.{v} f).app M).hom
    (IsLocalizedModule.map_units
      ((locUnit.{v} f).app ((locFunctor.{v} f).obj M)).hom) ?_
  apply LinearMap.ext
  intro m
  rfl

/-- `M[1/f] ⟶ M[1/f][1/f]` is an isomorphism. -/
lemma isIso_locUnit_locFunctor (f : A) (M : ModuleCat.{max v u} A) :
    IsIso ((locUnit.{v} f).app ((locFunctor.{v} f).obj M)) :=
  isIso_locUnit_of_isIso_smul f _ (isIso_smul_locFunctor f M)

/-- Localization is idempotent: the localization of the localization map is an isomorphism. -/
lemma isIso_locFunctor_map_locUnit (f : A) (M : ModuleCat.{max v u} A) :
    IsIso ((locFunctor.{v} f).map ((locUnit.{v} f).app M)) := by
  rw [locFunctor_map_locUnit_eq]
  exact isIso_locUnit_locFunctor f M

/-- `M[1/f]` vanishes exactly when every element of `M` is killed by a power of `f`. -/
lemma locFunctor_isZero_iff (f : A) (M : ModuleCat.{max v u} A) :
    IsZero ((locFunctor.{v} f).obj M) ↔ ∀ m : M, ∃ n : ℕ, f ^ n • m = 0 := by
  let : IsLocalizedModule (Submonoid.powers f) ((locUnit.{v} f).app M).hom :=
    isLocalizedModule_locUnit.{v} f M
  rw [ModuleCat.isZero_iff_subsingleton,
    IsLocalizedModule.subsingleton_iff (Submonoid.powers f) ((locUnit.{v} f).app M).hom]
  refine ⟨fun h m => ?_, fun h m => ?_⟩
  · obtain ⟨r, ⟨n, rfl⟩, hr⟩ := h m
    exact ⟨n, hr⟩
  · obtain ⟨n, hn⟩ := h m
    exact ⟨f ^ n, ⟨n, rfl⟩, hn⟩

/-- Vanishing after inverting `g` is inherited by the localization at any other element. -/
lemma locFunctor_isZero_locFunctor (g f : A) (M : ModuleCat.{max v u} A)
    (h : IsZero ((locFunctor.{v} g).obj M)) :
    IsZero ((locFunctor.{v} g).obj ((locFunctor.{v} f).obj M)) := by
  let : IsLocalizedModule (Submonoid.powers f) ((locUnit.{v} f).app M).hom :=
    isLocalizedModule_locUnit.{v} f M
  rw [locFunctor_isZero_iff] at h ⊢
  intro x
  obtain ⟨⟨m, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers f)
    ((locUnit.{v} f).app M).hom x
  obtain ⟨n, hn⟩ := h m
  refine ⟨n, ?_⟩
  rw [Function.uncurry_apply_pair, ← IsLocalizedModule.mk'_smul, hn,
    IsLocalizedModule.mk'_zero]

/-- A module is `I`-power torsion, for `I` spanned by a finite set, exactly when all the
localizations at the elements of that set vanish. -/
lemma isIPowerTorsion_iff_locFunctor_isZero (s : Finset A) (M : ModuleCat.{max v u} A) :
    IsIPowerTorsion A M (Ideal.span (s : Set A)) ↔
      ∀ f ∈ s, IsZero ((locFunctor.{v} f).obj M) := by
  constructor
  · intro h f hf
    rw [locFunctor_isZero_iff]
    intro m
    obtain ⟨n, _, hn⟩ := h m
    exact ⟨n, hn _ (Ideal.pow_mem_pow (Ideal.subset_span hf) n)⟩
  · intro h m
    have hle : Ideal.span (s : Set A) ≤ (A ∙ m).annihilator.radical := by
      rw [Ideal.span_le]
      intro f hf
      obtain ⟨n, hn⟩ := (locFunctor_isZero_iff.{v} f M).mp (h f hf) m
      exact ⟨n, (Submodule.mem_annihilator_span_singleton m _).2 hn⟩
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
      (Submodule.fg_span s.finite_toSet)
    refine ⟨n + 1, Nat.succ_pos _, fun a ha => ?_⟩
    exact (Submodule.mem_annihilator_span_singleton m a).1
      (hn (Ideal.pow_le_pow_right n.le_succ ha))

end Localizations

/-! ### Natural transformations out of the identity on derived categories

The degreewise unit of an exact endofunctor, the unit it induces on the derived category, the
comparison between the two, the transport of invertibility along an isomorphism, and the
vanishing criteria are *not* declared here. They are the repository's canonical declarations in
`StacksFrontier.RingTheory.Dualizing.LocalCohomology.Coreflection`. The four names that consumers
already address through this namespace are re-exported below, so that
`Dualizing.PowerTorsionBaseChange.derivedUnit` and `Dualizing.Coreflection.derivedUnit` are one
constant rather than two; the remaining ones are used here under their canonical names.

A second copy of each here would be content-identical but a distinct constant, and the results
proved here would then not compose with the other consumers of the coreflection. -/

export Dualizing.Coreflection (complexUnit derivedUnit derivedUnit_app_Q isIso_app_of_iso)

section Derived

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  (L : C ⥤ C) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (τ : 𝟭 C ⟶ L)

/-- An exact endofunctor kills a derived object exactly when it kills all its cohomology. -/
lemma mapDerivedCategory_isZero_iff (X : DerivedCategory C) :
    IsZero (L.mapDerivedCategory.obj X) ↔
      ∀ i, IsZero (L.obj ((DerivedCategory.homologyFunctor C i).obj X)) := by
  rw [Coreflection.isZero_iff_homology]
  exact forall_congr' fun i =>
    ((Dualizing.mapDerivedCategoryHomologyIso L i).app X).isZero_iff

omit [HasDerivedCategory C] in
/-- A natural transformation out of the identity which is invertible on the cohomology of a
complex is invertible on the cohomology of the degreewise transformation. -/
lemma homologyMap_complexUnit_isIso (K : CochainComplex C ℤ) (i : ℤ)
    (hi : IsIso (τ.app ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj K))) :
    IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).map
      ((complexUnit L τ).app K)) := by
  let S := K.sc i
  show IsIso (ShortComplex.homologyMap (S.mapNatTrans τ))
  rw [ShortComplex.homologyMap_mapNatTrans]
  have : IsIso ((S.mapHomologyIso (𝟭 C)).hom) := inferInstance
  have : IsIso (τ.app S.homology) := hi
  have : IsIso ((S.mapHomologyIso L).inv) := inferInstance
  infer_instance

/-- A natural transformation out of the identity which is invertible on all cohomology of a
derived object is invertible on that object. -/
lemma isIso_derivedUnit_app (X : DerivedCategory C)
    (hX : ∀ i, IsIso (τ.app ((DerivedCategory.homologyFunctor C i).obj X))) :
    IsIso ((derivedUnit L τ).app X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hK : ∀ i, IsIso (τ.app
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj K)) := by
    intro i
    have h1 : IsIso (τ.app ((DerivedCategory.homologyFunctor C i).obj
        (DerivedCategory.Q.obj K))) :=
      isIso_app_of_iso τ ((DerivedCategory.homologyFunctor C i).mapIso e) (hX i)
    exact isIso_app_of_iso τ ((DerivedCategory.homologyFunctorFactors C i).app K).symm h1
  have hq : HomologicalComplex.quasiIso C (ComplexShape.up ℤ) ((complexUnit L τ).app K) := by
    rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact homologyMap_complexUnit_isIso L τ K i (hK i)
  have hQ : IsIso ((derivedUnit L τ).app (DerivedCategory.Q.obj K)) := by
    rw [derivedUnit_app_Q]
    have : IsIso (DerivedCategory.Q.map ((complexUnit L τ).app K)) :=
      (Localization.inverts DerivedCategory.Q
        (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))) _ hq
    infer_instance
  exact isIso_app_of_iso (derivedUnit L τ) e.symm hQ

/-- A morphism of derived objects whose cohomology becomes invertible after applying an exact
endofunctor becomes invertible on the derived category. -/
lemma isIso_mapDerivedCategory_map {X Y : DerivedCategory C} (g : X ⟶ Y)
    (h : ∀ i, IsIso (L.map ((DerivedCategory.homologyFunctor C i).map g))) :
    IsIso (L.mapDerivedCategory.map g) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  let α := Dualizing.mapDerivedCategoryHomologyIso L i
  have hnat : (DerivedCategory.homologyFunctor C i).map (L.mapDerivedCategory.map g) ≫
      α.hom.app Y = α.hom.app X ≫ L.map ((DerivedCategory.homologyFunctor C i).map g) :=
    α.hom.naturality g
  have h1 : IsIso ((DerivedCategory.homologyFunctor C i).map (L.mapDerivedCategory.map g) ≫
      α.hom.app Y) := by
    rw [hnat]
    have := h i
    infer_instance
  exact (isIso_comp_right_iff _ (α.hom.app Y)).mp h1

end Derived

/-! ### Coreflection onto the objects killed by a finite family of localizations -/

section Coreflection

open CategoryTheory.Pretriangulated

/-- A morphism from an object killed by an idempotent localization into an object on which the
localization unit is invertible vanishes. -/
lemma hom_eq_zero_of_isLocal {D' : Type*} [Category D'] [HasZeroMorphisms D']
    (F : D' ⥤ D') (η : 𝟭 D' ⟶ F) {T Z : D'}
    (hT : IsZero (F.obj T)) (hZ : IsIso (η.app Z)) (g : T ⟶ Z) : g = 0 := by
  have := hZ
  apply (cancel_mono (η.app Z)).1
  rw [zero_comp, ← Functor.id_map (f := g), η.naturality,
    hT.eq_of_tgt (η.app T) 0, zero_comp]

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- In a distinguished triangle whose third object receives only zero morphisms from `W`,
together with its shift, composition with the first map is bijective on morphisms from `W`. -/
lemma bijective_comp_mor₁ (T : Triangle D) (hT : T ∈ distTriang D) (W : D)
    (h₃ : ∀ k : W ⟶ T.obj₃, k = 0)
    (h₃' : ∀ k : W ⟶ T.obj₃⟦(-1 : ℤ)⟧, k = 0) :
    Function.Bijective (fun g : W ⟶ T.obj₁ => g ≫ T.mor₁) := by
  have hker : ∀ k : W ⟶ T.obj₁, k ≫ T.mor₁ = 0 → k = 0 := by
    intro k hk
    obtain ⟨k', hk'⟩ := Triangle.coyoneda_exact₂ T.invRotate
      (inv_rot_of_distTriang _ hT) k hk
    rw [hk', h₃' k']
    exact zero_comp
  refine ⟨?_, ?_⟩
  · intro k l hkl
    rw [← sub_eq_zero]
    apply hker
    change k ≫ T.mor₁ = l ≫ T.mor₁ at hkl
    rw [Preadditive.sub_comp, hkl, sub_self]
  · intro k
    obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₂ T hT k (h₃ _)
    exact ⟨l, hl.symm⟩

/-- The fibre of the localization unit is the universal object with vanishing localization
mapping to `X`; the same holds after applying a triangulated functor `Φ` which carries
`F`-local objects to `F`-local objects. -/
lemma exists_fiber_localization
    (F : D ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (η : 𝟭 D ⟶ F) (hη : ∀ X, IsIso (η.app (F.obj X)))
    (hFη : ∀ X, IsIso (F.map (η.app X)))
    (Φ : D ⥤ D) [Φ.Additive] [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (hΦ : ∀ X, IsIso (η.app (Φ.obj (F.obj X)))) (X : D) :
    ∃ T : Triangle D, T ∈ distTriang D ∧ T.obj₂ = X ∧ T.obj₃ = F.obj X ∧
      IsZero (F.obj T.obj₁) ∧
      (∀ W, IsZero (F.obj W) →
        Function.Bijective (fun g : W ⟶ T.obj₁ => g ≫ T.mor₁)) ∧
      (∀ W, IsZero (F.obj W) →
        Function.Bijective (fun g : W ⟶ Φ.obj T.obj₁ => g ≫ Φ.map T.mor₁)) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (η.app X)
  let T := (Triangle.mk (η.app X) g h).invRotate
  have hT' : T ∈ distTriang D := inv_rot_of_distTriang _ hT
  refine ⟨T, hT', rfl, rfl, ?_, ?_, ?_⟩
  · exact Triangle.isZero₁_of_isIso₂ _ (F.map_distinguished _ hT') (hFη X)
  · intro W hW
    exact bijective_comp_mor₁ T hT' W (fun k => hom_eq_zero_of_isLocal F η hW (hη X) k)
      fun k => (cancel_mono ((F.commShiftIso (-1 : ℤ)).app X).inv).1
        ((hom_eq_zero_of_isLocal F η hW (hη (X⟦(-1 : ℤ)⟧)) _).trans zero_comp.symm)
  · intro W hW
    have hΦT : Φ.mapTriangle.obj T ∈ distTriang D := Φ.map_distinguished _ hT'
    exact bijective_comp_mor₁ (Φ.mapTriangle.obj T) hΦT W
      (fun k => hom_eq_zero_of_isLocal F η hW (hΦ X) k)
      fun k => (cancel_mono (((Φ.commShiftIso (-1 : ℤ)).app (F.obj X)).inv ≫
        (Φ.mapIso ((F.commShiftIso (-1 : ℤ)).app X)).inv)).1
        ((hom_eq_zero_of_isLocal F η hW (hΦ (X⟦(-1 : ℤ)⟧)) _).trans zero_comp.symm)

/-- Iterating the fibre construction over a finite family of idempotent localizations produces
the universal object killed by all of them, together with the corresponding statement after
applying a compatible triangulated functor. -/
lemma exists_finite_localization_coreflection
    {ι : Type*} (F : ι → D ⥤ D) [∀ i, (F i).Additive]
    [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]
    (η : ∀ i, 𝟭 D ⟶ F i)
    (hη : ∀ i X, IsIso ((η i).app ((F i).obj X)))
    (hFη : ∀ i X, IsIso ((F i).map ((η i).app X)))
    (hpres : ∀ i j X, IsZero ((F j).obj X) → IsZero ((F j).obj ((F i).obj X)))
    (Φ : D ⥤ D) [Φ.Additive] [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (hΦ : ∀ i X, IsIso ((η i).app (Φ.obj ((F i).obj X))))
    (s : Finset ι) (X : D) :
    ∃ (Y : D) (a : Y ⟶ X), (∀ i ∈ s, IsZero ((F i).obj Y)) ∧
      (∀ W, (∀ i ∈ s, IsZero ((F i).obj W)) →
        Function.Bijective (fun g : W ⟶ Y => g ≫ a)) ∧
      (∀ W, (∀ i ∈ s, IsZero ((F i).obj W)) →
        Function.Bijective (fun g : W ⟶ Φ.obj Y => g ≫ Φ.map a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨X, 𝟙 X, by simp, ?_, ?_⟩
    · intro W _
      exact ⟨fun _ _ h => by simpa only [Category.comp_id] using h,
        fun g => ⟨g, Category.comp_id g⟩⟩
    · intro W _
      rw [Φ.map_id]
      exact ⟨fun _ _ h => by simpa only [Category.comp_id] using h,
        fun g => ⟨g, Category.comp_id g⟩⟩
  | @insert i s hi ih =>
    obtain ⟨U, b, hU, hb, hbΦ⟩ := ih
    obtain ⟨T, hT, h₂, h₃, hFT, ha, haΦ⟩ :=
      exists_fiber_localization (F i) (η i) (hη i) (hFη i) Φ (hΦ i) U
    let e : T.obj₂ ≅ U := eqToIso h₂
    refine ⟨T.obj₁, T.mor₁ ≫ e.hom ≫ b, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hFT
      · apply Triangle.isZero₁_of_isZero₂₃ _ ((F j).map_distinguished _ hT)
        · exact (hU j hj).of_iso ((F j).mapIso e)
        · rw [show ((F j).mapTriangle.obj T).obj₃ = (F j).obj T.obj₃ from rfl, h₃]
          exact hpres i j U (hU j hj)
    · intro W hW
      have h₁ := ha W (hW i (Finset.mem_insert_self _ _))
      have h₂' : Function.Bijective (fun g : W ⟶ T.obj₂ => g ≫ e.hom) :=
        bijective_comp_right e.hom
      have h₃' := hb W (fun j hj => hW j (Finset.mem_insert_of_mem hj))
      simpa only [Function.comp_def, Category.assoc] using h₃'.comp (h₂'.comp h₁)
    · intro W hW
      have h₁ := haΦ W (hW i (Finset.mem_insert_self _ _))
      have h₂' : Function.Bijective (fun g : W ⟶ Φ.obj T.obj₂ => g ≫ Φ.map e.hom) :=
        bijective_comp_right (Φ.map e.hom)
      have h₃' := hbΦ W (fun j hj => hW j (Finset.mem_insert_of_mem hj))
      have := h₃'.comp (h₂'.comp h₁)
      simpa only [Function.comp_def, Category.assoc, Φ.map_comp] using this

end Coreflection

/-! ### Derived extension and restriction of scalars along a flat map -/

section FlatBaseChange

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]

/-- The unit of an adjunction is invertible at an object as soon as it is invertible at an
isomorphic one. -/
lemma adjunction_unit_isIso_of_iso {C' E' : Type*} [Category C'] [Category E']
    {P : C' ⥤ E'} {Q : E' ⥤ C'} (adj : P ⊣ Q) {M N : C'}
    (e : M ≅ N) (hη : IsIso (adj.unit.app N)) : IsIso (adj.unit.app M) :=
  isIso_app_of_iso adj.unit e hη

variable {P : C ⥤ E} {Q : E ⥤ C} [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]

omit [HasDerivedCategory C] [HasDerivedCategory E] in
/-- The unit of an adjunction of exact functors, read degreewise on complexes, is a
quasi-isomorphism in each degree where the unit inverts the cohomology. -/
lemma homologyMap_unit_isIso (adj : P ⊣ Q) (K : CochainComplex C ℤ) (i : ℤ)
    (hi : IsIso (adj.unit.app
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj K))) :
    IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).map
      ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K)) := by
  let S := K.sc i
  have : PreservesFiniteLimits (P ⋙ Q) := comp_preservesFiniteLimits P Q
  have : PreservesFiniteColimits (P ⋙ Q) := comp_preservesFiniteColimits P Q
  show IsIso (ShortComplex.homologyMap ((K.sc i).mapNatTrans adj.unit))
  rw [ShortComplex.homologyMap_mapNatTrans]
  have : IsIso ((S.mapHomologyIso (𝟭 C)).hom) := inferInstance
  have : IsIso (adj.unit.app S.homology) := hi
  have : IsIso ((S.mapHomologyIso (P ⋙ Q)).inv) := inferInstance
  infer_instance

/-- The unit of the derived adjunction is invertible on the image of `Q` at a complex whose
cohomology the unit already inverts. -/
lemma mapDerivedAdjunction_unit_app_isIso (adj : P ⊣ Q) (K : CochainComplex C ℤ)
    (hη : ∀ i, IsIso (adj.unit.app
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj K))) :
    IsIso (adj.mapDerivedCategory.unit.app (DerivedCategory.Q.obj K)) := by
  let η := (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K
  have hq : HomologicalComplex.quasiIso C (ComplexShape.up ℤ) η := by
    rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact homologyMap_unit_isIso adj K i (hη i)
  have hηQ : IsIso (DerivedCategory.Q.map η) :=
    (Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))) η hq
  rw [Adjunction.mapDerivedCategory, Adjunction.localization_unit_app]
  infer_instance

/-- The unit of the derived adjunction is invertible at an object whose cohomology the unit
already inverts. -/
lemma mapDerivedAdjunction_unit_isIso (adj : P ⊣ Q) (X : DerivedCategory C)
    (hη : ∀ i, IsIso (adj.unit.app ((DerivedCategory.homologyFunctor C i).obj X))) :
    IsIso (adj.mapDerivedCategory.unit.app X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hηK : ∀ i, IsIso (adj.unit.app
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj K)) := by
    intro i
    have h1 : IsIso (adj.unit.app ((DerivedCategory.homologyFunctor C i).obj
        (DerivedCategory.Q.obj K))) :=
      adjunction_unit_isIso_of_iso adj ((DerivedCategory.homologyFunctor C i).mapIso e) (hη i)
    exact adjunction_unit_isIso_of_iso adj
      ((DerivedCategory.homologyFunctorFactors C i).app K).symm h1
  exact adjunction_unit_isIso_of_iso adj.mapDerivedCategory e.symm
    (mapDerivedAdjunction_unit_app_isIso adj K hηK)

end FlatBaseChange

/-! ### Derived localization of modules -/

section DerivedLocalization

variable {A : Type u} [CommRing A]

/-- Derived localization away from `f`, as an endofunctor of `D(A)`. -/
def locDerived (f : A) :
    DerivedCategory (ModuleCat.{max v u} A) ⥤ DerivedCategory (ModuleCat.{max v u} A) :=
  (locFunctor.{v} f).mapDerivedCategory

/-- The derived localization maps, as a natural transformation out of the identity. -/
def locDerivedUnit (f : A) :
    𝟭 (DerivedCategory (ModuleCat.{max v u} A)) ⟶ locDerived.{v} f :=
  derivedUnit (locFunctor.{v} f) (locUnit.{v} f)

/-- Derived localization is additive. -/
instance locDerived_additive (f : A) : (locDerived.{v} f).Additive :=
  inferInstanceAs ((locFunctor.{v} f).mapDerivedCategory.Additive)

/-- Derived localization commutes with the shift. -/
instance locDerived_commShift (f : A) : (locDerived.{v} f).CommShift ℤ :=
  inferInstanceAs ((locFunctor.{v} f).mapDerivedCategory.CommShift ℤ)

/-- Derived localization is triangulated. -/
instance locDerived_isTriangulated (f : A) : (locDerived.{v} f).IsTriangulated :=
  inferInstanceAs ((locFunctor.{v} f).mapDerivedCategory.IsTriangulated)

/-- Derived localization is idempotent: the unit is invertible on its image. -/
lemma isIso_locDerivedUnit_locDerived (f : A)
    (X : DerivedCategory (ModuleCat.{max v u} A)) :
    IsIso ((locDerivedUnit.{v} f).app ((locDerived.{v} f).obj X)) :=
  Coreflection.derivedUnit_obj_isIso _ _ (fun M => isIso_locUnit_locFunctor f M) X

/-- Derived localization inverts its own unit. -/
lemma isIso_locDerived_map_locDerivedUnit (f : A)
    (X : DerivedCategory (ModuleCat.{max v u} A)) :
    IsIso ((locDerived.{v} f).map ((locDerivedUnit.{v} f).app X)) :=
  Coreflection.derivedUnit_map_isIso _ _ (fun M => isIso_locFunctor_map_locUnit f M) X

/-- Derived localization kills an object exactly when it kills all its cohomology. -/
lemma locDerived_isZero_iff (f : A) (X : DerivedCategory (ModuleCat.{max v u} A)) :
    IsZero ((locDerived.{v} f).obj X) ↔
      ∀ i, IsZero ((locFunctor.{v} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj X)) :=
  mapDerivedCategory_isZero_iff _ X

/-- Vanishing of the derived localization at `g` is inherited by the derived localization at
any other element. -/
lemma locDerived_isZero_locDerived (g f : A)
    (X : DerivedCategory (ModuleCat.{max v u} A))
    (h : IsZero ((locDerived.{v} g).obj X)) :
    IsZero ((locDerived.{v} g).obj ((locDerived.{v} f).obj X)) := by
  rw [locDerived_isZero_iff] at h ⊢
  intro i
  refine (locFunctor_isZero_locFunctor g f _ (h i)).of_iso ?_
  exact (locFunctor.{v} g).mapIso
    ((Dualizing.mapDerivedCategoryHomologyIso (locFunctor.{v} f) i).app X)

/-- An object of `D(A)` has `I`-power-torsion cohomology exactly when all its derived
localizations at a finite generating set of `I` vanish. -/
lemma derivedPowerTorsion_iff_locDerived_isZero (I : Ideal A) (hI : I.FG)
    (s : Finset A) (hs : Ideal.span (s : Set A) = I)
    (X : DerivedCategory (ModuleCat.{max v u} A)) :
    Dualizing.derivedPowerTorsionProperty A I hI X ↔
      ∀ f ∈ s, IsZero ((locDerived.{v} f).obj X) := by
  show (∀ i, IsIPowerTorsion A
    ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj X) I) ↔ _
  constructor
  · intro h f hf
    rw [locDerived_isZero_iff]
    intro i
    refine (isIPowerTorsion_iff_locFunctor_isZero.{v} s _).mp ?_ f hf
    rw [hs]
    exact h i
  · intro h i
    rw [← hs, isIPowerTorsion_iff_locFunctor_isZero]
    intro f hf
    exact (locDerived_isZero_iff.{v} f X).mp (h f hf) i

/-- A module placed in degree zero has `I`-power-torsion cohomology as soon as it is itself
`I`-power torsion. -/
lemma derivedPowerTorsionProperty_singleFunctor {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max v u} A) (hM : IsIPowerTorsion A M I) :
    Dualizing.derivedPowerTorsionProperty A I hI
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M) := by
  intro j
  rcases eq_or_ne j 0 with rfl | hj
  · exact isIPowerTorsion_of_moduleIso _ _
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} A) 0).app M) hM
  · refine isIPowerTorsion_of_isZero I _ (IsZero.of_iso ?_
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} A) j).app
        ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).obj M)))
    exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M j hj

end DerivedLocalization

/-! ### Morphisms out of a power-torsion object are unchanged by flat base change -/

section Main

universe uR uA uM

variable (A : Type uR) (B : Type uA) [CommRing A] [CommRing B] [Algebra A B]

/-- Flat extension of scalars preserves finite limits, also when the source and target
rings inhabit different universes. -/
theorem preservesFiniteLimits_extendScalars_of_flat (hflat : Module.Flat A B) :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{uR, uA, max uA (max uR uM)} (algebraMap A B)) := by
  exact preservesFiniteLimits_extendScalars_flat.{uM, uA, uR} A B hflat

/-- **Stacks 05E9**, in categorical form: for an `I`-power torsion module, the unit of the
extension–restriction adjunction is an isomorphism. -/
lemma extendRestrictScalars_unit_isIso_of_powerTorsion
    (I : Ideal A) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (M : ModuleCat.{max uR (max uA uM)} A) (hM : IsIPowerTorsion A M I) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA}
      (algebraMap A B)).unit.app M) := by
  have hbase := (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective.{uR, uA, uM}
    A B I hflat).2 hquot M hM
  let e := TensorProduct.comm A B M
  have hunit0 : Function.Bijective (fun m : M => (1 : B) ⊗ₜ[A] m) := by
    have he (m : M) : e ((1 : B) ⊗ₜ[A] m) = m ⊗ₜ[A] (1 : B) := by simp [e]
    constructor
    · intro x y hxy
      apply hbase.1
      have hh := congrArg e hxy
      rw [he, he] at hh
      exact hh
    · intro z
      obtain ⟨m, hm⟩ := hbase.2 (e z)
      refine ⟨m, ?_⟩
      apply e.injective
      rw [he m]
      simpa using hm
  let E := IPowerTorsion.tensorModuleCatEquiv.{uR, uA, uM} (R := A) (S := B) M
  have hunit : Function.Bijective (fun m : M => E ((1 : B) ⊗ₜ[A] m)) :=
    E.bijective.comp hunit0
  apply (ConcreteCategory.isIso_iff_bijective _).2
  convert hunit using 1 <;> try rfl

/-- Base change preserves `f`-locality of modules. -/
lemma isIso_locUnit_extendRestrict (f : A) (M : ModuleCat.{max uR (max uA uM)} A)
    (h : IsIso (f • 𝟙 M)) :
    IsIso ((locUnit.{max uA uM} f).app
      ((ModuleCat.extendScalars.{uR, uA, max uR (max uA uM)} (algebraMap A B) ⋙
        ModuleCat.restrictScalars.{max uR (max uA uM), uR, uA} (algebraMap A B)).obj M)) :=
  isIso_locUnit_of_isIso_smul f _
    (isIso_smul_extendRestrictScalars.{max uR uM, uR, uA} (algebraMap A B) M h)

/-- **The key comparison.** If `A → B` is flat and induces an isomorphism modulo a finitely
generated ideal `I`, then derived extension of scalars is bijective on morphisms out of an
object of `D(A)` with `I`-power-torsion cohomology. -/
theorem bijective_mapDerivedCategory_map_of_powerTorsion
    [(ModuleCat.extendScalars.{uR, uA, max uR (max uA uM)} (algebraMap A B)).Additive]
    [PreservesFiniteLimits
      (ModuleCat.extendScalars.{uR, uA, max uR (max uA uM)} (algebraMap A B))]
    [PreservesFiniteColimits
      (ModuleCat.extendScalars.{uR, uA, max uR (max uA uM)} (algebraMap A B))]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (K X : DerivedCategory (ModuleCat.{max uR (max uA uM)} A))
    (hK : Dualizing.derivedPowerTorsionProperty A I hI K) :
    Function.Bijective (fun g : K ⟶ X =>
      (ModuleCat.extendScalars.{uR, uA, max uR (max uA uM)}
        (algebraMap A B)).mapDerivedCategory.map g) := by
  obtain ⟨s, hs⟩ := hI
  let F := ModuleCat.extendScalars.{uR, uA, max uR (max uA uM)} (algebraMap A B)
  let G := ModuleCat.restrictScalars.{max uR (max uA uM), uR, uA} (algebraMap A B)
  let adj : F ⊣ G :=
    ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} (algebraMap A B)
  let adjD := adj.mapDerivedCategory
  let Φ := F.mapDerivedCategory ⋙ G.mapDerivedCategory
  have hΦ : ∀ (f : A) (Z : DerivedCategory (ModuleCat.{max uR (max uA uM)} A)),
      IsIso ((locDerivedUnit.{max uA uM} f).app
        (Φ.obj ((locDerived.{max uA uM} f).obj Z))) := by
    intro f Z
    refine isIso_derivedUnit_app _ _ _ (fun i => ?_)
    refine isIso_app_of_iso (locUnit.{max uA uM} f) ?_
      (isIso_locUnit_extendRestrict A B f _ (isIso_smul_locFunctor f
        ((DerivedCategory.homologyFunctor (ModuleCat.{max uR (max uA uM)} A) i).obj Z)))
    refine ((Dualizing.mapDerivedCategoryHomologyIso G i).app
        (F.mapDerivedCategory.obj ((locDerived.{max uA uM} f).obj Z)) ≪≫
      G.mapIso ((Dualizing.mapDerivedCategoryHomologyIso F i).app
        ((locDerived.{max uA uM} f).obj Z))) ≪≫ ?_
    exact (F ⋙ G).mapIso
      ((Dualizing.mapDerivedCategoryHomologyIso (locFunctor.{max uA uM} f) i).app Z)
  obtain ⟨Y, a, hY, hb, hbΦ⟩ := exists_finite_localization_coreflection
    (fun f : A => locDerived.{max uA uM} f) (fun f => locDerivedUnit.{max uA uM} f)
    (fun f Z => isIso_locDerivedUnit_locDerived f Z)
    (fun f Z => isIso_locDerived_map_locDerivedUnit f Z)
    (fun i j Z h => locDerived_isZero_locDerived j i Z h) Φ hΦ s X
  have hKloc : ∀ f ∈ s, IsZero ((locDerived.{max uA uM} f).obj K) :=
    (derivedPowerTorsion_iff_locDerived_isZero I ⟨s, hs⟩ s hs K).mp hK
  have hYtors : Dualizing.derivedPowerTorsionProperty A I ⟨s, hs⟩ Y :=
    (derivedPowerTorsion_iff_locDerived_isZero I ⟨s, hs⟩ s hs Y).mpr hY
  have hunitY : IsIso (adjD.unit.app Y) := by
    refine mapDerivedAdjunction_unit_isIso adj Y (fun i => ?_)
    exact extendRestrictScalars_unit_isIso_of_powerTorsion A B I hflat hquot _ (hYtors i)
  have hα := hb K hKloc
  have hδ := hbΦ K hKloc
  have hγ : Function.Bijective (fun g : K ⟶ Y => g ≫ adjD.unit.app Y) :=
    bijective_comp_right (adjD.unit.app Y)
  have hcomp : Function.Bijective
      ((fun h : K ⟶ X => h ≫ adjD.unit.app X) ∘ (fun g : K ⟶ Y => g ≫ a)) := by
    have heq : (fun h : K ⟶ X => h ≫ adjD.unit.app X) ∘ (fun g : K ⟶ Y => g ≫ a)
        = (fun h : K ⟶ Φ.obj Y => h ≫ Φ.map a) ∘
          (fun g : K ⟶ Y => g ≫ adjD.unit.app Y) := by
      funext g
      simp only [Function.comp_apply, Category.assoc]
      congr 1
      simpa only [Functor.id_map] using adjD.unit.naturality a
    rw [heq]
    exact hδ.comp hγ
  have hβ : Function.Bijective (fun h : K ⟶ X => h ≫ adjD.unit.app X) :=
    (Function.Bijective.of_comp_iff _ hα).mp hcomp
  have hfinal : (fun h : K ⟶ X => h ≫ adjD.unit.app X)
      = (adjD.homEquiv K (F.mapDerivedCategory.obj X)) ∘
        (fun g : K ⟶ X => F.mapDerivedCategory.map g) := by
    funext g
    rw [Function.comp_apply, Adjunction.homEquiv_unit]
    simpa only [Functor.id_map, Functor.comp_map] using (adjD.unit.naturality g)
  rw [hfinal] at hβ
  exact (Function.Bijective.of_comp_iff' (adjD.homEquiv K
    (F.mapDerivedCategory.obj X)).bijective _).mp hβ

/-- **Stacks 05EH.** The canonical scalar-extension map on Ext groups from an
`I`-power-torsion module is bijective in every degree. -/
@[stacks 05EH "Ext"]
theorem bijective_extBaseChange_of_powerTorsion
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map))
    (M N : ModuleCat.{max uA (max uR uM)} A) (hM : IsIPowerTorsion A M I) (i : ℕ) :
    let F := ModuleCat.extendScalars.{uR, uA, max uA (max uR uM)} (algebraMap A B)
    letI : F.IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA}
        (algebraMap A B)).isLeftAdjoint
    letI : PreservesFiniteLimits F :=
      preservesFiniteLimits_extendScalars_of_flat.{uR, uA, uM} A B hflat
    letI : F.Additive := F.additive_of_preserves_binary_products
    letI := CategoryTheory.HasExt.standard (ModuleCat.{max uA (max uR uM)} A)
    letI := CategoryTheory.HasExt.standard (ModuleCat.{max uA (max uR uM)} B)
    Function.Bijective (F.mapExtAddHom M N i) := by
  intro F
  let : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} (algebraMap A B)).isLeftAdjoint
  let : PreservesFiniteLimits F :=
    preservesFiniteLimits_extendScalars_of_flat.{uR, uA, uM} A B hflat
  let : F.Additive := F.additive_of_preserves_binary_products
  let := CategoryTheory.HasExt.standard (ModuleCat.{max uA (max uR uM)} A)
  let := CategoryTheory.HasExt.standard (ModuleCat.{max uA (max uR uM)} B)
  set SM := (DerivedCategory.singleFunctor (ModuleCat.{max uA (max uR uM)} A) 0).obj M with hSM
  set SN := (DerivedCategory.singleFunctor (ModuleCat.{max uA (max uR uM)} A) 0).obj N with hSN
  have hcore := bijective_mapDerivedCategory_map_of_powerTorsion.{uR, uA, uM}
    A B I hI hflat hquot
    SM (SN⟦(i : ℤ)⟧)
    (derivedPowerTorsionProperty_singleFunctor.{max uA uM, uR} I hI M hM)
  have hmap : Function.Bijective
      (fun f : ShiftedHom SM SN (i : ℤ) => f.map F.mapDerivedCategory) :=
    (bijective_comp_right
      ((F.mapDerivedCategory.commShiftIso (i : ℤ)).hom.app SN)).comp hcore
  have hΨ : Function.Bijective (fun f : ShiftedHom SM SN (i : ℤ) =>
      (F.mapDerivedCategorySingleFunctor 0).inv.app M ≫ f.map F.mapDerivedCategory ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app N)⟦(i : ℤ)⟧') :=
    (bijective_comp_left ((F.mapDerivedCategorySingleFunctor 0).inv.app M)).comp
      ((bijective_comp_right
        (((F.mapDerivedCategorySingleFunctor 0).hom.app N)⟦(i : ℤ)⟧')).comp hmap)
  have h1 : Function.Bijective (fun e => (F.mapExtAddHom M N i e).hom) := by
    have heq : (fun e => (F.mapExtAddHom M N i e).hom) =
        (fun f : ShiftedHom SM SN (i : ℤ) =>
          (F.mapDerivedCategorySingleFunctor 0).inv.app M ≫ f.map F.mapDerivedCategory ≫
            ((F.mapDerivedCategorySingleFunctor 0).hom.app N)⟦(i : ℤ)⟧') ∘
          (fun e => Abelian.Ext.hom e) :=
      funext fun e => Abelian.Ext.mapExactFunctor_hom F e
    rw [heq]
    exact hΨ.comp (Abelian.Ext.homEquiv).bijective
  exact (Function.Bijective.of_comp_iff' (Abelian.Ext.homEquiv).bijective _).mp h1

end Main

end Dualizing.PowerTorsionBaseChange
