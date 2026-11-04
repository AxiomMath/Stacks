module

public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality
public import StacksFrontier.RingTheory.Dualizing.NormalizedResidueFieldExt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The socle of an injective hull of the residue field

Let `(A, 𝔪, κ)` be a local ring and let `i : κ ⟶ E` be an injective hull of the residue field,
the residue field being lifted to whatever module universe is at hand. The *socle* of `E`, the
largest semisimple submodule, is `i(κ)`; read through `i` this says

`Hom_A(κ, E) ≅ κ`.

This file proves that identification and reads it in the derived category. For a *normalized*
dualizing complex `ω_A^•` over a Noetherian local ring, Matlis duality on finite-length modules
(`Dualizing.derivedHomFiniteLengthIsoMatlisDual`) identifies `RHom_A(κ, ω_A^•)` with
`Hom_A(κ, E)` placed in degree zero, so the identification above becomes

`RHom_A(κ, ω_A^•) ≅ κ`     in `D(A)`.

## Main definitions

* `Dualizing.residueFieldHomInjectiveHullEquiv` — **the socle identification**, as an `A`-linear
  equivalence `Hom_A(κ, E) ≃ₗ[A] κ`.
* `Dualizing.residueFieldInternalHomInjectiveHullIso` — the same identification written with the
  internal Hom of the category of `A`-modules, which is the spelling
  `Dualizing.matlisDualFiniteLengthFunctor` produces.

## Main results

* `Dualizing.nonempty_iso_dualizingDerivedHom_residueFieldSingle` — `RHom_A(κ, ω_A^•) ≅ κ` in
  `D(A)` for a normalized dualizing complex, with derived Hom the contravariant functor
  `Dualizing.dualizingDerivedHomFunctor` on the derived category of `A`-modules.

## The proof

An `A`-linear map `f : κ → E` has image either zero or simple, since `κ` is simple. If it is
nonzero, then it is a nonzero submodule of `E`, hence meets the image of `i` because `i` is an
essential monomorphism; and two atoms of the submodule lattice of `E` whose meet is nonzero are
equal. So the image of `f` is the image of `i`, and composition with `i` is a bijection from
`End_A(κ)` onto `Hom_A(κ, E)`. Finally an `A`-linear endomorphism of `κ` is multiplication by
its value at `1`, because every element of `κ` is the class of a scalar.

Nothing but locality of `A` is used for the socle identification; the Noetherian hypothesis
enters only with the dualizing complex.

## Implementation notes

The normalization convention `Dualizing.IsNormalizedDualizingComplex` is stated with
`Dualizing.derivedHom`, the derived *coextension of scalars* along `A → κ`, so it is an
isomorphism in the derived category of `κ`-modules. The statement proved here is the companion
one for the *internal* derived Hom `Dualizing.dualizingDerivedHomFunctor`, an isomorphism in the
derived category of `A`-modules; the two are different statements about different functors, and
the second is what a consumer working inside `D(A)` — for instance anything using the duality of
[Stacks, Tag 0A7C] — can compose with.

The derived category of `A`-modules is taken at the standard model, as in
`StacksFrontier/RingTheory/Dualizing/DualizingDerivedHom.lean`: that model is baked into the type of
`Dualizing.dualizingDerivedHomFunctor`, so it is forced here rather than chosen.

## References

* [Stacks Project, Tag 08Z0](https://stacks.math.columbia.edu/tag/08Z0)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0A7Q](https://stacks.math.columbia.edu/tag/0A7Q)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

/-! ### Maps from a simple module into an injective hull of a simple module -/

section Simple

variable {A : Type u} [CommRing A]

/-- The range of an injective linear map out of a simple module is an atom of the submodule
lattice. -/
private theorem isAtom_range_of_injective {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [IsSimpleModule A M] (f : M →ₗ[A] N)
    (hf : Function.Injective f) : IsAtom (LinearMap.range f) :=
  isSimpleModule_iff_isAtom.mp <| IsSimpleModule.congr (LinearEquiv.ofInjective f hf).symm

/-- For an injective hull `i : S ⟶ E` of a simple module and a simple module `N`, every
`A`-linear map `N → E` has its image inside the image of `i`.

The image of a nonzero such map is a simple submodule of `E`, essentiality of `i` makes it meet
the simple submodule `i(S)`, and two atoms of the submodule lattice of `E` whose meet is nonzero
are equal. -/
lemma range_le_range_of_isInjectiveHull_of_simple {S E N : ModuleCat.{w} A}
    [IsSimpleModule A S] [IsSimpleModule A N] (i : S ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) (f : N →ₗ[A] E) :
    LinearMap.range f ≤ LinearMap.range i.hom := by
  by_cases hf : f = 0
  · simp [hf]
  have hfatom := isAtom_range_of_injective f (LinearMap.injective_of_ne_zero hf)
  have hiatom := isAtom_range_of_injective i.hom ((ModuleCat.mono_iff_injective i).mp inferInstance)
  have hmeet : LinearMap.range f ⊓ LinearMap.range i.hom ≠ ⊥ := by
    let e := ModuleCat.subobjectModule E
    have hmk : e (Subobject.mk i) = LinearMap.range i.hom := by
      apply le_antisymm
      · rintro x ⟨y, rfl⟩
        exact ⟨(Subobject.underlyingIso i).hom y,
          ConcreteCategory.congr_hom (Subobject.underlyingIso_hom_comp_eq_mk i) y⟩
      · rintro x ⟨y, rfl⟩
        refine ⟨(Subobject.underlyingIso i).inv y, ?_⟩
        simp
    have hne : e.symm (LinearMap.range f) ≠ ⊥ := fun h =>
      hfatom.1 (by simpa [e.map_bot] using congrArg e h)
    intro hz
    refine hi.2 (e.symm (LinearMap.range f)) hne ?_
    apply e.injective
    rwa [e.map_inf, e.map_bot, e.apply_symm_apply, hmk]
  exact (((hfatom.le_iff_eq hmeet).mp inf_le_left).symm.trans
    ((hiatom.le_iff_eq hmeet).mp inf_le_right)).le

/-- Composition with an injective hull `i : S ⟶ E` of a simple module is a bijection on the
`A`-linear maps out of a simple module `N`: it is injective because `i` is, and surjective
because every map `N → E` factors through the image of `i`. -/
lemma bijective_compRight_of_isInjectiveHull_of_simple {S E N : ModuleCat.{w} A}
    [IsSimpleModule A S] [IsSimpleModule A N] (i : S ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Function.Bijective
      (LinearMap.compRight A i.hom : (N →ₗ[A] S) →ₗ[A] (N →ₗ[A] E)) := by
  have hinj : Function.Injective i.hom := (ModuleCat.mono_iff_injective i).mp inferInstance
  refine ⟨fun f g h => ?_, fun f => ?_⟩
  · ext x
    exact hinj (LinearMap.congr_fun h x)
  · have hle := range_le_range_of_isInjectiveHull_of_simple i hi f
    refine ⟨(LinearEquiv.ofInjective i.hom hinj).symm.toLinearMap ∘ₗ
      f.codRestrict (LinearMap.range i.hom) (fun c => hle (LinearMap.mem_range_self f c)), ?_⟩
    ext x
    exact congrArg Subtype.val ((LinearEquiv.ofInjective i.hom hinj).apply_symm_apply
      ⟨f x, hle (LinearMap.mem_range_self f x)⟩)

/-- Composition with an injective hull `i : S ⟶ E` of a simple module identifies the `A`-linear
maps from a simple module `N` into `S` with those into `E`. -/
def homEquivOfIsInjectiveHullOfSimple {S E N : ModuleCat.{w} A}
    [IsSimpleModule A S] [IsSimpleModule A N] (i : S ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    (N →ₗ[A] S) ≃ₗ[A] (N →ₗ[A] E) :=
  LinearEquiv.ofBijective _ (bijective_compRight_of_isInjectiveHull_of_simple i hi)

end Simple

/-! ### The endomorphisms of the residue field -/

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The residue field of a local ring is a simple module over the ring. -/
@[sga "3 VIIB 0.2.1" "simplicity of S_m"]
lemma isSimpleModule_residueField_of_isLocalRing :
    IsSimpleModule A (IsLocalRing.ResidueField A) :=
  isSimpleModule_iff_isCoatom.2
    (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal A))

/-- **Evaluation at `1` identifies the `A`-linear endomorphisms of the residue field with the
residue field**, after lifting the residue field to an arbitrary universe. Every element of the
residue field is the class of a scalar, so an endomorphism is determined by its value at `1`,
and multiplication by a fixed element realizes every value. -/
def uliftResidueFieldEndEquiv :
    (ULift.{w} (IsLocalRing.ResidueField A) →ₗ[A] ULift.{w} (IsLocalRing.ResidueField A)) ≃ₗ[A]
      ULift.{w} (IsLocalRing.ResidueField A) :=
  LinearEquiv.ofBijective
    { toFun := fun f => f (ULift.up 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (by
      refine ⟨fun f g h => ?_, fun y => ?_⟩
      · have h' : f (ULift.up (1 : IsLocalRing.ResidueField A)) =
            g (ULift.up (1 : IsLocalRing.ResidueField A)) := h
        refine LinearMap.ext fun x => ?_
        obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective x.down
        have hx : x = r • (ULift.up (1 : IsLocalRing.ResidueField A)) := by
          apply ULift.down_injective
          change x.down = r • (1 : IsLocalRing.ResidueField A)
          rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, mul_one, hr]
        rw [hx, map_smul, map_smul, h']
      · exact ⟨{ toFun := fun x => ULift.up (x.down * y.down)
                 map_add' := fun a b => ULift.ext _ _ (add_mul a.down b.down y.down)
                 map_smul' := fun r a => ULift.ext _ _ (smul_mul_assoc r a.down y.down) },
          ULift.ext _ _ (one_mul y.down)⟩)

/-! ### The socle identification -/

/-- **The socle of an injective hull of the residue field is the residue field.** Let `A` be a
local ring with residue field `κ` and let `i : κ ⟶ E` be an injective hull of `κ`, the residue
field being lifted to an arbitrary module universe. Then composition with `i`, followed by
evaluation at `1`, identifies `Hom_A(κ, E)` with `κ`.

Every `A`-linear map `κ → E` lands in the image of `i`: its image is zero or a simple submodule
of `E`, and a simple submodule of an essential extension of the simple module `i(κ)` is `i(κ)`
itself. Hence composition with `i` is a bijection from `End_A(κ)` onto `Hom_A(κ, E)`, and an
`A`-linear endomorphism of `κ` is multiplication by its value at `1`. -/
@[sga "2 IV 4.8" "Hom_A(k"]
def residueFieldHomInjectiveHullEquiv
    (E : ModuleCat.{max w u} A)
    (i : (ModuleCat.uliftFunctor.{w} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ((ModuleCat.uliftFunctor.{w} A).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A)) →ₗ[A] E) ≃ₗ[A]
      ULift.{w} (IsLocalRing.ResidueField A) :=
  haveI := isSimpleModule_residueField_of_isLocalRing A
  haveI : IsSimpleModule A ((ModuleCat.uliftFunctor.{w} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A))) :=
    IsSimpleModule.congr
      (ULift.moduleEquiv : ULift.{w} (IsLocalRing.ResidueField A) ≃ₗ[A] _)
  (homEquivOfIsInjectiveHullOfSimple i hi).symm ≪≫ₗ uliftResidueFieldEndEquiv.{u, w} A

/-- **`Hom_A(κ, E) ≅ κ` in the category of `A`-modules**, for `i : κ ⟶ E` an injective hull of
the residue field. This is `Dualizing.residueFieldHomInjectiveHullEquiv` written with the
internal Hom of the category of `A`-modules, which is the spelling the Matlis-duality functor
`Dualizing.matlisDualFiniteLengthFunctor` produces. -/
def residueFieldInternalHomInjectiveHullIso
    (E : ModuleCat.{max w u} A)
    (i : (ModuleCat.uliftFunctor.{w} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    (MonoidalClosed.internalHom.obj (Opposite.op
          (ModuleCat.of A (ULift.{w} (IsLocalRing.ResidueField A))))).obj E ≅
      ModuleCat.of A (ULift.{w} (IsLocalRing.ResidueField A)) :=
  (ModuleCat.homLinearEquiv (R := A) (S := A) ≪≫ₗ
    residueFieldHomInjectiveHullEquiv.{u, w} A E i hi).toModuleIso

/-! ### Derived Hom from the residue field into a normalized dualizing complex -/

/-- **`RHom_A(κ, ω_A^•) ≅ κ` in `D(A)` for a normalized dualizing complex.** Let `A` be a
Noetherian local ring with residue field `κ` and let `ω_A^•` be a dualizing complex for `A`
which is normalized in the sense of [Stacks, Section 47.16]. Then the internal derived Hom from
the residue field placed in degree zero into `ω_A^•` is again the residue field placed in degree
zero.

Matlis duality on finite-length modules identifies `RHom_A(κ, ω_A^•)` with `Hom_A(κ, E)` placed
in degree zero, for `E` an injective hull of the residue field
(`Dualizing.derivedHomFiniteLengthIsoMatlisDual`); the socle of such a hull is the residue field
(`Dualizing.residueFieldInternalHomInjectiveHullIso`).

Note that the normalization convention is recorded with the derived coextension of scalars along
`A → κ`, hence as an isomorphism in `D(κ)`; the isomorphism below is the companion statement for
the internal derived Hom, in `D(A)`. -/
theorem nonempty_iso_dualizingDerivedHom_residueFieldSingle
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{max v u} A))
    (hω : IsNormalizedDualizingComplex.{u, v} ω) :
    Nonempty ((dualizingDerivedHomFunctor A ω).obj
        (Opposite.op (residueFieldSingle.{u, v} A)) ≅ residueFieldSingle.{u, v} A) := by
  obtain ⟨E, j, hj, hHull⟩ := Module.exists_isInjectiveHull.{u, v} A
    ((ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)))
  have : Mono j := hj
  let N : FiniteLengthModules.{u, v} A :=
    ⟨ModuleCat.of A (ULift.{v} (IsLocalRing.ResidueField A)),
      isFiniteLength_uliftResidueField.{u, v}⟩
  obtain ⟨e⟩ := derivedHomFiniteLengthIsoMatlisDual A ω hω E j hHull
  let H : ModuleCat.{max v u} A :=
    (MonoidalClosed.internalHom.obj (Opposite.op
      (ModuleCat.of A (ULift.{v} (IsLocalRing.ResidueField A))))).obj E
  have eD : (dualizingDerivedHomFunctor A ω).obj
      (Opposite.op (residueFieldSingle.{u, v} A)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj H :=
    e.app (Opposite.op N)
  exact ⟨eD ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).mapIso
    (residueFieldInternalHomInjectiveHullIso.{u, v} A E j hHull)⟩

end Dualizing

end
