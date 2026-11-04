module

public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.BeauvilleLaszlo.ModuleEquivalence
public import StacksFrontier.RingTheory.BeauvilleLaszlo.Surjectivity

/-!
# Glueing algebras along a Beauville--Laszlo pair

Let `(R → R', f)` be a glueing pair. A *glueing datum of algebras* consists of an `R'`-algebra
`A'`, an `R_f`-algebra `A₁` and an isomorphism of the two base changes to `R'_f`. The module
version of the Beauville--Laszlo theorem (Stacks 0BP2) recovers from such a datum a glueable
`R`-module, namely the module of compatible pairs; this file observes that the compatible pairs
form a *subring* of `A' × A₁`, and that the two comparison maps of the module theorem are the
structure maps of an `R`-algebra.

## Main definitions

* `BeauvilleLaszlo.glueAlpha` is the glueing isomorphism of the datum in the shape the
  module-level theorem uses, and `BeauvilleLaszlo.glueSubalgebra` the subalgebra of compatible
  pairs, with projections `BeauvilleLaszlo.gluedToGeneric`, `BeauvilleLaszlo.gluedToLocal`,
  `BeauvilleLaszlo.gluedGenericAlgHom` and `BeauvilleLaszlo.gluedLocalAlgHom`.

## Main results

* `BeauvilleLaszlo.isGlueableFor_iff_beauvilleLaszloModuleSequence_shortExact` translates
  between the elementwise form of glueability and short exactness of the module sequence.
* `BeauvilleLaszlo.isGlueableFor_glueSubalgebra`: the glued algebra is glueable.
* `BeauvilleLaszlo.isPushout_glueSubalgebra_generic` and
  `BeauvilleLaszlo.isPushout_glueSubalgebra_local`: the two members of the datum are the base
  changes of the glued algebra along `R → R'` and along `R → R_f`.
* `BeauvilleLaszlo.existsUnique_ringHom_of_baseChanges_compatible`: a pair of compatible ring
  maps into the two base changes of a glueable algebra comes from a unique ring map into the
  algebra itself.

## Implementation notes

The compatibility condition is phrased with the *module* localization
`LocalizedModule.Away (algebraMap R R' f) A'` used by the module theorem, together with the
`R'`-linear isomorphism `glueAlpha` of the datum. The condition is multiplicative because it is
read through `θ`, a ring map, so the compatible pairs cut out a *subalgebra*
(`AlgHom.equalizer`) of `A' × A₁` and not merely a submodule; that submodule is the glued
module `BeauvilleLaszlo.glueKernel` of the module-level theorem, which is
`BeauvilleLaszlo.toSubmodule_glueSubalgebra`.

Glueability of the glued algebra needs nothing beyond its being a submodule of a product of an
`R'`-module and an `R_f`-module, which is `BeauvilleLaszlo.shortExact_submodule_prod`.

## References

* [Stacks Project, Tag 0BP2](https://stacks.math.columbia.edu/tag/0BP2)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace BeauvilleLaszlo

universe u v w

section Bridge

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Glueability of a module in the elementwise sense of `BeauvilleLaszlo.IsGlueableFor` is
short exactness of its Beauville--Laszlo module sequence. -/
theorem isGlueableFor_iff_beauvilleLaszloModuleSequence_shortExact
    (M : Type w) [AddCommGroup M] [Module R M] (f : R) :
    IsGlueableFor (S := S) M f ↔
      (beauvilleLaszloModuleSequence.{u, v, w} (S := S) M f).ShortExact := by
  have hmono : Mono (beauvilleLaszloModuleSequence (S := S) M f).f ↔
      Function.Injective (toTensorBaseChanges (S := S) M f) := by
    rw [AddCommGrpCat.mono_iff_injective]
    show Function.Injective (ULift.map (toTensorBaseChanges (S := S) M f)) ↔ _
    rw [ULift.map_injective]
  have hepi : Epi (beauvilleLaszloModuleSequence (S := S) M f).g ↔
      Function.Surjective (tensorAwayDifference (S := S) M f) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    show Function.Surjective (ULift.map (tensorAwayDifference (S := S) M f)) ↔ _
    rw [ULift.map_surjective]
  have hexact : (beauvilleLaszloModuleSequence (S := S) M f).Exact ↔
      Function.Exact (toTensorBaseChanges (S := S) M f)
        (tensorAwayDifference (S := S) M f) := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    show Function.Exact (ULift.map (toTensorBaseChanges (S := S) M f))
      (ULift.map (tensorAwayDifference (S := S) M f)) ↔ _
    simp only [Function.Exact, ULift.forall, ULift.map, ULift.ext_iff,
      Set.mem_range, ULift.exists]
    rfl
  constructor
  · rintro ⟨hi, he, hs⟩
    exact ShortComplex.ShortExact.mk' (hexact.2 he) (hmono.2 hi) (hepi.2 hs)
  · intro h
    exact ⟨hmono.1 h.mono_f, hexact.1 h.exact, hepi.1 h.epi_g⟩

end Bridge

section Glue

variable {R R' A' A₁ : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  [CommRing A'] [Algebra R' A'] [Algebra R A'] [IsScalarTower R R' A']
  [CommRing A₁] [Algebra R A₁] (f : R)
  [Algebra (Localization.Away f) A₁] [IsScalarTower R (Localization.Away f) A₁]

variable (θ : A' →ₐ[R'] R' ⊗[R] A₁)
  (hθ : IsLocalizedModule (Submonoid.powers ((algebraMap R R') f)) θ.toLinearMap)

/-- The glueing isomorphism of the datum `(A', A₁, θ)`, in the shape the module-level
Beauville--Laszlo theorem uses: `θ` presents `R' ⊗[R] A₁` as the localization of `A'` away from
the image of `f`. -/
noncomputable def glueAlpha :
    LocalizedModule.Away ((algebraMap R R') f) A' ≃ₗ[R'] R' ⊗[R] A₁ :=
  letI := hθ
  IsLocalizedModule.linearEquiv (Submonoid.powers ((algebraMap R R') f))
    (LocalizedModule.mkLinearMap (Submonoid.powers ((algebraMap R R') f)) A') θ.toLinearMap

omit [Algebra R A'] [IsScalarTower R R' A'] [Algebra (Localization.Away f) A₁]
  [IsScalarTower R (Localization.Away f) A₁] in
/-- The glueing isomorphism sends the image of `a : A'` in the localization to `θ a`. -/
theorem glueAlpha_mk (a : A') :
    glueAlpha f θ hθ
        (LocalizedModule.mkLinearMap (Submonoid.powers ((algebraMap R R') f)) A' a) = θ a :=
  let := hθ
  IsLocalizedModule.linearEquiv_apply (Submonoid.powers ((algebraMap R R') f))
    (LocalizedModule.mkLinearMap (Submonoid.powers ((algebraMap R R') f)) A') θ.toLinearMap a

/-- **The algebra glued from a Beauville--Laszlo datum**: the subalgebra of `A' × A₁` of pairs
whose two images in `R' ⊗[R] A₁` agree. -/
def glueSubalgebra : Subalgebra R (A' × A₁) :=
  AlgHom.equalizer ((θ.restrictScalars R).comp (AlgHom.fst R A' A₁))
    (Algebra.TensorProduct.includeRight.comp (AlgHom.snd R A' A₁))

/-- A pair `x` lies in the glued algebra exactly when `θ x.1 = 1 ⊗ₜ x.2`. -/
theorem mem_glueSubalgebra_iff (x : A' × A₁) :
    x ∈ glueSubalgebra θ ↔ θ x.1 = (1 : R') ⊗ₜ[R] x.2 :=
  Iff.rfl

/-- The projection of the glued algebra to the `R'`-algebra of the datum. -/
def gluedToGeneric : glueSubalgebra θ →ₗ[R] A' :=
  (LinearMap.fst R A' A₁).comp (Subalgebra.toSubmodule (glueSubalgebra θ)).subtype

/-- The projection of the glued algebra to the `R_f`-algebra of the datum. -/
def gluedToLocal : glueSubalgebra θ →ₗ[R] A₁ :=
  (LinearMap.snd R A' A₁).comp (Subalgebra.toSubmodule (glueSubalgebra θ)).subtype

omit [Algebra (Localization.Away f) A₁] [IsScalarTower R (Localization.Away f) A₁] in
/-- A pair `x` lies in the glued module of the datum exactly when `θ x.1 = 1 ⊗ₜ x.2`. -/
theorem mem_kernel_glueAlpha_iff (x : A' × A₁) :
    x ∈ glueKernel f (glueAlpha f θ hθ) ↔ θ x.1 = (1 : R') ⊗ₜ[R] x.2 := by
  have hd : glueDifference f (glueAlpha f θ hθ) x =
      LocalizedModule.mkLinearMap (Submonoid.powers ((algebraMap R R') f)) A' x.1 -
        (glueAlpha f θ hθ).symm ((1 : R') ⊗ₜ[R] x.2) := rfl
  rw [LinearMap.mem_ker, hd, sub_eq_zero, ← (glueAlpha f θ hθ).injective.eq_iff,
    glueAlpha_mk, LinearEquiv.apply_symm_apply]

omit [Algebra (Localization.Away f) A₁] [IsScalarTower R (Localization.Away f) A₁] in
/-- The underlying `R`-submodule of the glued algebra is the glued module
`BeauvilleLaszlo.glueKernel` of the datum. -/
theorem toSubmodule_glueSubalgebra :
    Subalgebra.toSubmodule (glueSubalgebra θ) = glueKernel f (glueAlpha f θ hθ) :=
  SetLike.ext fun x ↦ by
    rw [Subalgebra.mem_toSubmodule, mem_glueSubalgebra_iff, mem_kernel_glueAlpha_iff]

/-- The glued algebra, as an `R`-submodule, is the glued module of the datum. -/
noncomputable def gluedEquivKernel :
    glueSubalgebra θ ≃ₗ[R] glueKernel f (glueAlpha f θ hθ) :=
  LinearEquiv.ofEq _ _ (toSubmodule_glueSubalgebra f θ hθ)

omit [Algebra (Localization.Away f) A₁] [IsScalarTower R (Localization.Away f) A₁] in
/-- The projection `gluedToGeneric` is the generic projection of the glued module, composed with
`gluedEquivKernel`. -/
theorem gluedToGeneric_eq :
    gluedToGeneric θ =
      (glueGenericProjection f (glueAlpha f θ hθ)).comp
        (gluedEquivKernel f θ hθ).toLinearMap :=
  rfl

omit [Algebra (Localization.Away f) A₁] [IsScalarTower R (Localization.Away f) A₁] in
/-- The projection `gluedToLocal` is the local projection of the glued module, composed with
`gluedEquivKernel`. -/
theorem gluedToLocal_eq :
    gluedToLocal θ =
      (glueLocalProjection f (glueAlpha f θ hθ)).comp
        (gluedEquivKernel f θ hθ).toLinearMap :=
  rfl

/-- **The glued algebra is glueable.** It is a submodule of the product of an `R'`-module and
an `R_f`-module, which for a glueing pair is enough. -/
theorem isGlueableFor_glueSubalgebra
    (hglue : IsGlueingPair (algebraMap R R') f) :
    IsGlueableFor (S := R') (glueSubalgebra θ) f := by
  rw [isGlueableFor_iff_beauvilleLaszloModuleSequence_shortExact]
  exact shortExact_submodule_prod (S := R') (A := A') (B := A₁) f hglue.1 hglue.2
    (Subalgebra.toSubmodule (glueSubalgebra θ))

include hθ in
/-- **The glued algebra recovers the local member of the datum**: its projection to `A₁`
presents `A₁` as the localization away from `f`. -/
theorem isLocalizedModule_gluedToLocal :
    IsLocalizedModule (Submonoid.powers f) (gluedToLocal θ) := by
  rw [gluedToLocal_eq f θ hθ]
  let := glueLocalProjection_isLocalizedModule f (glueAlpha f θ hθ)
  exact IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    (glueLocalProjection f (glueAlpha f θ hθ)) (gluedEquivKernel f θ hθ)

include hθ in
/-- **The glued algebra recovers the generic member of the datum**: the base change of its
projection to `A'` along `R → R'` is bijective. -/
theorem bijective_extendScalars_gluedToGeneric
    (hglue : IsGlueingPair (algebraMap R R') f) :
    Function.Bijective (extendScalarsMap (S := R') (gluedToGeneric θ)) := by
  have he : extendScalarsMap (S := R') (gluedToGeneric θ) =
      (extendScalarsMap (S := R') (glueGenericProjection f (glueAlpha f θ hθ))).comp
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R')
          (gluedEquivKernel f θ hθ)).toLinearMap := by
    ext s
    rfl
  rw [he]
  exact (glueGenericProjection_baseChange_bijective f (glueAlpha f θ hθ)
      hglue.1 hglue.2).comp
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R')
      (gluedEquivKernel f θ hθ)).bijective

/-- The projection of the glued algebra to the generic member, as an `R`-algebra map. -/
def gluedGenericAlgHom : glueSubalgebra θ →ₐ[R] A' :=
  (AlgHom.fst R A' A₁).comp (glueSubalgebra θ).val

/-- The projection of the glued algebra to the local member, as an `R`-algebra map. -/
def gluedLocalAlgHom : glueSubalgebra θ →ₐ[R] A₁ :=
  (AlgHom.snd R A' A₁).comp (glueSubalgebra θ).val

variable {θ}

include hθ in
/-- **`A'` is the base change of the glued algebra along `R → R'`.** -/
theorem isPushout_glueSubalgebra_generic
    [Algebra (glueSubalgebra θ) A'] [IsScalarTower R (glueSubalgebra θ) A']
    (hcompat : ∀ x : glueSubalgebra θ, algebraMap (glueSubalgebra θ) A' x =
      gluedToGeneric θ x)
    (hglue : IsGlueingPair (algebraMap R R') f) :
    Algebra.IsPushout R R' (glueSubalgebra θ) A' := by
  have hbij := bijective_extendScalars_gluedToGeneric f θ hθ hglue
  refine ⟨IsBaseChange.of_equiv
    (LinearEquiv.ofBijective (extendScalarsMap (S := R') (gluedToGeneric θ)) hbij) ?_⟩
  intro x
  show (1 : R') • gluedToGeneric θ x = _
  rw [one_smul]
  exact (hcompat x).symm

include hθ in
/-- **`A₁` is the base change of the glued algebra along `R → R_f`.** -/
theorem isPushout_glueSubalgebra_local
    [Algebra (glueSubalgebra θ) A₁] [IsScalarTower R (glueSubalgebra θ) A₁]
    (hcompat : ∀ x : glueSubalgebra θ, algebraMap (glueSubalgebra θ) A₁ x =
      gluedToLocal θ x) :
    Algebra.IsPushout R (Localization.Away f) (glueSubalgebra θ) A₁ := by
  let := isLocalizedModule_gluedToLocal f θ hθ
  have hbc : IsBaseChange (Localization.Away f) (gluedToLocal θ) :=
    IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f) (gluedToLocal θ)
  refine ⟨IsBaseChange.of_equiv hbc.equiv ?_⟩
  intro x
  rw [IsBaseChange.equiv_tmul, one_smul]
  exact (hcompat x).symm

end Glue

section Full

variable {R R' A C : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing A]
  [Algebra R A] [CommRing C] (f : R)

/-- **A glueable algebra is the fibre product of its two base changes.** A pair of ring maps
into the two base changes of a glueable `R`-algebra which agree in the base change to `R'_f`
comes from a unique ring map into the algebra itself. -/
theorem existsUnique_ringHom_of_baseChanges_compatible
    (hA : IsGlueableFor (S := R') A f)
    (φ : C →+* TensorProduct R A R')
    (ψ : C →+* TensorProduct R A (Localization.Away f))
    (hcomp : ∀ c, baseChangeToAway (S := R') (M := A) f (φ c) =
      localizedBaseChangeToAway (S := R') (M := A) f (ψ c)) :
    ∃! θ : C →+* A,
      (∀ c, (θ c) ⊗ₜ[R] (1 : R') = φ c) ∧
        ∀ c, (θ c) ⊗ₜ[R] (1 : Localization.Away f) = ψ c := by
  classical
  have hzero (c : C) :
      tensorAwayDifference (S := R') (M := A) f (φ c, ψ c) = 0 := by
    rw [tensorAwayDifference_apply, hcomp c, sub_self]
  let lift (c : C) : A := Classical.choose ((hA.2.1 (φ c, ψ c)).mp (hzero c))
  have hlift (c : C) :
      toTensorBaseChanges (S := R') (M := A) f (lift c) = (φ c, ψ c) :=
    Classical.choose_spec ((hA.2.1 (φ c, ψ c)).mp (hzero c))
  have hleft (c : C) : lift c ⊗ₜ[R] (1 : R') = φ c := congrArg Prod.fst (hlift c)
  have hright (c : C) : lift c ⊗ₜ[R] (1 : Localization.Away f) = ψ c :=
    congrArg Prod.snd (hlift c)
  have key : ∀ x y : A, x ⊗ₜ[R] (1 : R') = y ⊗ₜ[R] (1 : R') →
      x ⊗ₜ[R] (1 : Localization.Away f) = y ⊗ₜ[R] (1 : Localization.Away f) → x = y := by
    intro x y h1 h2
    exact hA.1 (Prod.ext h1 h2)
  let θ : C →+* A :=
    { toFun := lift
      map_zero' := key _ _ (by rw [hleft, map_zero, TensorProduct.zero_tmul])
        (by rw [hright, map_zero, TensorProduct.zero_tmul])
      map_add' := fun a b ↦ by
        refine key _ _ ?_ ?_ <;> simp [hleft, hright, TensorProduct.add_tmul]
      map_one' := by
        refine key _ _ ?_ ?_ <;> simp [hleft, hright, Algebra.TensorProduct.one_def]
      map_mul' := fun a b ↦ by
        refine key _ _ ?_ ?_
        · rw [hleft, map_mul, ← hleft a, ← hleft b, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul]
        · rw [hright, map_mul, ← hright a, ← hright b, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul] }
  exact ⟨θ, ⟨hleft, hright⟩, fun ρ ⟨h1, h2⟩ ↦
    RingHom.ext fun c ↦ key _ _ ((h1 c).trans (hleft c).symm) ((h2 c).trans (hright c).symm)⟩

end Full

end BeauvilleLaszlo

end
