module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Sectionwise criteria for exactness of a short complex of sheaves of modules

A short complex of presheaves of modules is exact as soon as it is exact on sections over
every object, because the evaluation functors are jointly faithful and
`PresheafOfModules R₀` is abelian, hence balanced.  For *sheaves* of modules the same
criterion holds, even though a sectionwise exact sequence of sheaves is in general only
"locally exact": the forgetful functor to presheaves of modules is fully faithful, so it
reflects monomorphisms, epimorphisms and limits, and exactness can be read off the kernel of
the first map.

## Main results

* `PresheafOfModules.exact_of_sectionwise` and `PresheafOfModules.shortExact_of_sectionwise`:
  the criteria for presheaves of modules.
* `SheafOfModules.mono_of_sectionwise_injective` and
  `SheafOfModules.epi_of_sectionwise_surjective`: a sectionwise injective (surjective)
  morphism of sheaves of modules is a monomorphism (epimorphism).
* `SheafOfModules.exact_of_sectionwise`: a short complex of sheaves of modules whose maps
  on sections are injective and exact in the middle is exact.
* `SheafOfModules.shortExact_of_sectionwise` and
  `SheafOfModules.shortExact_of_sectionwise'`: the short exactness criterion, the second in
  the form in which the middle hypothesis is a lifting statement.
* `SheafOfModules.shortExact_of_sectionwise_of_epi`: the variant taking `Epi` of the second
  map as a hypothesis rather than sectionwise surjectivity.

## Implementation notes

Exactness in the middle needs only sectionwise injectivity of the first map and sectionwise
exactness; sectionwise surjectivity of the second map is used solely to produce `Epi`, which
is strictly weaker, whence the `_of_epi` variant.

The transport of exactness from presheaves back to sheaves goes through the kernel-fork
description of exactness: `CategoryTheory.ShortComplex.Exact.fIsKernel` upstairs,
`CategoryTheory.Limits.KernelFork.isLimitMapConeEquiv` to move the cone along the fully
faithful forgetful functor, `CategoryTheory.Limits.isLimitOfReflects`, and finally
`CategoryTheory.ShortComplex.exact_of_f_is_kernel`.  Sheafification is not involved.

The instances `HasSheafify` and `GrothendieckTopology.WEqualsLocallyBijective` on the sheaf
statements are those of Mathlib's `Abelian (SheafOfModules R)` instance: `ShortComplex.Exact`
needs homology, hence cokernels, hence sheafification.  The two `Mono`/`Epi` lemmas are stated
before them and so do not need them.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits Opposite

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R₀ : Cᵒᵖ ⥤ RingCat.{u}}

/-- The evaluation functors `PresheafOfModules R₀ ⥤ ModuleCat (R₀.obj X)` are jointly
faithful: a morphism of presheaves of modules is determined by its components. -/
lemma jointlyFaithful_evaluation :
    JointlyFaithful (fun (X : Cᵒᵖ) ↦ evaluation.{v} R₀ X) where
  map_injective h := by
    ext X x
    exact ConcreteCategory.congr_hom (h X) x

/-- A short complex of presheaves of modules which is exact on sections over every object is
exact. -/
lemma exact_of_sectionwise (S : ShortComplex (PresheafOfModules.{v} R₀))
    (hex : ∀ X : Cᵒᵖ, Function.Exact (S.f.app X) (S.g.app X)) :
    S.Exact :=
  (jointlyFaithful_evaluation.jointlyReflectsIsomorphisms.exact_iff S).2 fun X ↦
    ModuleCat.shortComplex_exact _ (hex X)

/-- A short complex of presheaves of modules which is short exact on sections over every
object is short exact. -/
lemma shortExact_of_sectionwise (S : ShortComplex (PresheafOfModules.{v} R₀))
    (hinj : ∀ X : Cᵒᵖ, Function.Injective (S.f.app X))
    (hex : ∀ X : Cᵒᵖ, Function.Exact (S.f.app X) (S.g.app X))
    (hsur : ∀ X : Cᵒᵖ, Function.Surjective (S.g.app X)) :
    S.ShortExact :=
  (jointlyFaithful_evaluation.jointlyReflectsIsomorphisms.shortExact_iff S).2 fun X ↦
    ModuleCat.shortComplex_shortExact _ (hex X) (hinj X) (hsur X)

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A morphism of sheaves of modules which is injective on sections over every object is a
monomorphism. -/
lemma mono_of_sectionwise_injective {M N : SheafOfModules.{v} R} (φ : M ⟶ N)
    (hφ : ∀ T : Cᵒᵖ, Function.Injective (φ.val.app T)) :
    Mono φ :=
  (forget R).mono_of_mono_map (PresheafOfModules.mono_of_injective (f := φ.val) hφ)

/-- A morphism of sheaves of modules which is surjective on sections over every object is an
epimorphism. -/
lemma epi_of_sectionwise_surjective {M N : SheafOfModules.{v} R} (φ : M ⟶ N)
    (hφ : ∀ T : Cᵒᵖ, Function.Surjective (φ.val.app T)) :
    Epi φ :=
  (forget R).epi_of_epi_map (PresheafOfModules.epi_of_surjective (f := φ.val) hφ)

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  (S : ShortComplex (SheafOfModules.{v} R))

/-- On sections over `T`, the two maps of a short complex of sheaves of modules compose to
zero. -/
lemma sections_apply_apply_eq_zero (T : Cᵒᵖ) (y : S.X₁.val.obj T) :
    S.g.val.app T (S.f.val.app T y) = 0 :=
  (S.map (evaluation R T)).moduleCat_zero_apply y

/-- **A short complex of sheaves of modules which is sectionwise left exact is exact.**
Only injectivity of the first map on sections and exactness in the middle on sections are
needed; no surjectivity. -/
lemma exact_of_sectionwise
    (hinj : ∀ T : Cᵒᵖ, Function.Injective (S.f.val.app T))
    (hex : ∀ T : Cᵒᵖ, Function.Exact (S.f.val.app T) (S.g.val.app T)) :
    S.Exact := by
  have hmono : Mono (S.map (forget R)).f :=
    PresheafOfModules.mono_of_injective (f := S.f.val) hinj
  have hP : (S.map (forget R)).Exact :=
    PresheafOfModules.exact_of_sectionwise _ hex
  exact S.exact_of_f_is_kernel (isLimitOfReflects (forget R)
    ((KernelFork.isLimitMapConeEquiv (KernelFork.ofι S.f S.zero)
      (forget R)).symm hP.fIsKernel))

/-- **A short complex of sheaves of modules which is sectionwise short exact is short
exact.** -/
lemma shortExact_of_sectionwise
    (hinj : ∀ T : Cᵒᵖ, Function.Injective (S.f.val.app T))
    (hex : ∀ T : Cᵒᵖ, Function.Exact (S.f.val.app T) (S.g.val.app T))
    (hsur : ∀ T : Cᵒᵖ, Function.Surjective (S.g.val.app T)) :
    S.ShortExact where
  exact := exact_of_sectionwise S hinj hex
  mono_f := mono_of_sectionwise_injective _ hinj
  epi_g := epi_of_sectionwise_surjective _ hsur

/-- `SheafOfModules.shortExact_of_sectionwise` assuming only `Epi` of the second map instead
of its sectionwise surjectivity. -/
lemma shortExact_of_sectionwise_of_epi
    (hinj : ∀ T : Cᵒᵖ, Function.Injective (S.f.val.app T))
    (hex : ∀ T : Cᵒᵖ, Function.Exact (S.f.val.app T) (S.g.val.app T))
    [Epi S.g] :
    S.ShortExact where
  exact := exact_of_sectionwise S hinj hex
  mono_f := mono_of_sectionwise_injective _ hinj
  epi_g := inferInstance

/-- `SheafOfModules.shortExact_of_sectionwise` with the middle hypothesis phrased as a
lifting statement: a section of the middle term killed by the second map comes from a section
of the first term. -/
lemma shortExact_of_sectionwise'
    (hinj : ∀ T : Cᵒᵖ, Function.Injective (S.f.val.app T))
    (hex : ∀ (T : Cᵒᵖ) (x : S.X₂.val.obj T), S.g.val.app T x = 0 →
      ∃ y : S.X₁.val.obj T, S.f.val.app T y = x)
    (hsur : ∀ T : Cᵒᵖ, Function.Surjective (S.g.val.app T)) :
    S.ShortExact :=
  shortExact_of_sectionwise S hinj
    (fun T x ↦ ⟨hex T x, by rintro ⟨y, rfl⟩; exact sections_apply_apply_eq_zero S T y⟩) hsur

end SheafOfModules

end
