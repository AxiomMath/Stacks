module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Abelian
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Exactness

/-!
# The functor `M ↦ M̃` on `Proj` is additive and exact

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ` and `X = Proj 𝒮`. The
construction which takes a `ℤ`-graded `S`-module to the sheaf of `𝒪_X`-modules it generates is
a functor `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor` out of
the abelian category of graded modules. This file proves that it is **additive** and **exact**,
which is the last assertion of Stacks 01M7 ("the functor `M ↦ M̃` is exact") in its categorical
form, and the input the proof of Stacks 0BXF uses to see the irrelevant modules as the kernel of
an exact functor.

## Main results

* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_add` and
  `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_zero`: the
  associated-sheaf morphism is additive in the degree-preserving linear map it is built from.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.instAdditiveAssociatedModuleSheafFunctor`:
  **`M ↦ M̃` is an additive functor.**
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.shortExact_map_associatedModuleSheafFunctor`:
  **`M ↦ M̃` sends a short exact sequence of graded modules to a short exact sequence of sheaves
  of modules.**
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.preservesHomology_associatedModuleSheafFunctor`,
  `preservesFiniteLimits_associatedModuleSheafFunctor` and
  `preservesFiniteColimits_associatedModuleSheafFunctor`: **`M ↦ M̃` is exact** — it preserves
  homology, finite limits and finite colimits, hence kernels, cokernels, monomorphisms and
  epimorphisms (`mono_map_associatedModuleSheafFunctor`, `epi_map_associatedModuleSheafFunctor`).

## Implementation notes

Additivity is elementwise: on sections over an open the morphism `M̃ ⟶ Ñ` attached to `φ` is
pointwise `LocalizedModule.map _ φ`, which is additive in `φ` because a fraction `m / s` is sent
to `φ m / s`. That is `associatedModuleSheafMap_add`, and it holds at every pair of universes;
the hypothesis argument of `associatedModuleSheafMap` is a proposition, so no compatibility
lemma for it is needed.

Exactness is read on stalks. The stalk of `M̃` at a homogeneous prime is the degree-zero part
`M₍𝔭₎` of the localization of `M` there, and a short exact sequence of graded modules stays short
exact after that operation: this is
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkMap_shortExact`,
already proved. What this file supplies is the two ends of the bridge. On the source side, a
short exact sequence of graded modules has injective, exact and surjective underlying linear
maps (`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat.mono_iff_injective`,
`epi_iff_surjective` and `exact_of_shortExact`). On the target side,
`AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact` says short
exactness of sheaves of modules on a space is short exactness of every sequence of stalk
modules, and the stalk map of the functor's value is the hand-built stalk map on the nose
(`stalkMap_map_associatedModuleSheafFunctor`, a `rfl`). From short exactness Mathlib's
`CategoryTheory.Functor.exact_tfae` produces `PreservesHomology`, and from that finite limits
and finite colimits.

The stalkwise criterion is available for `SheafOfModules.{u}` over a sheaf of rings in the same
universe `u`, while `associatedModuleSheafFunctor` lands in `SheafOfModules.{max u v}` for
carriers in `Type v`. The exactness statements are therefore at `v = u`, carriers in the
universe of the ring; the additivity statements are at every `v`. Nothing in the source's
statement is lost: a graded module over `S : Type u` whose carrier is a subquotient of a free
module on a set in `Type u` — in particular every finitely generated one, which is all Stacks
0BXE and 0BXF speak about — lives at `v = u`.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry DirectSum
open Stacks.GradedLocalization
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections

namespace Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u v w t t'

open GradedModuleCat

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! ### Additivity -/

section Additive

variable {S : Type u} {M N : Type v} {σ : Type w} {τ : Type t} {υ : Type t'}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

omit [Decomposition 𝒨] [Decomposition 𝒩] in
/-- **The associated-sheaf morphism is additive in the degree-preserving map it localizes.** On
each fibre it is `LocalizedModule.map _ φ`, which sends `m / s` to `φ m / s`. -/
public theorem associatedModuleSheafMap_add (φ ψ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (hψ : ∀ i (m : M), m ∈ 𝒨 i → ψ m ∈ 𝒩 i)
    (hφψ : ∀ i (m : M), m ∈ 𝒨 i → (φ + ψ) m ∈ 𝒩 i) :
    associatedModuleSheafMap 𝒮 𝒨 𝒩 (φ + ψ) hφψ =
      associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ + associatedModuleSheafMap 𝒮 𝒨 𝒩 ψ hψ := by
  ext U a
  apply Subtype.ext
  funext y
  show LocalizedModule.map y.1.asHomogeneousIdeal.toIdeal.primeCompl (φ + ψ) (a.1 y) =
    LocalizedModule.map y.1.asHomogeneousIdeal.toIdeal.primeCompl φ (a.1 y) +
      LocalizedModule.map y.1.asHomogeneousIdeal.toIdeal.primeCompl ψ (a.1 y)
  induction a.1 y using LocalizedModule.induction_on with
  | _ m s => simp

omit [Decomposition 𝒨] [Decomposition 𝒩] in
/-- The associated-sheaf morphism of the zero map is zero. -/
public theorem associatedModuleSheafMap_zero
    (h0 : ∀ i (m : M), m ∈ 𝒨 i → (0 : M →ₗ[S] N) m ∈ 𝒩 i) :
    associatedModuleSheafMap 𝒮 𝒨 𝒩 0 h0 = 0 := by
  ext U a
  apply Subtype.ext
  funext y
  show LocalizedModule.map y.1.asHomogeneousIdeal.toIdeal.primeCompl 0 (a.1 y) = 0
  induction a.1 y using LocalizedModule.induction_on with
  | _ m s => simp

end Additive

section Functor

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **`M ↦ M̃` is an additive functor** from the graded modules over `S` to the sheaves of
`𝒪_{Proj 𝒮}`-modules. -/
public instance instAdditiveAssociatedModuleSheafFunctor :
    (associatedModuleSheafFunctor.{u, v, w} 𝒮).Additive where
  map_add {X Y f g} :=
    associatedModuleSheafMap_add 𝒮 X.grade Y.grade f.toLinearMap g.toLinearMap
      f.map_grade g.map_grade (f + g).map_grade

/-! ### Exactness -/

/-- The stalk map of the functor's value is the stalk map built by hand from the underlying
linear map. -/
public theorem stalkMap_map_associatedModuleSheafFunctor
    {X Y : GradedModuleCat.{u, u, w} 𝒮} (f : X ⟶ Y) (x : ProjectiveSpectrum.top 𝒮)
    (a : associatedModuleSheafStalk 𝒮 X.grade x) :
    (SheafOfModules.stalkMap
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) x
        ((associatedModuleSheafFunctor 𝒮).map f)).hom a =
      associatedModuleSheafStalkMap 𝒮 X.grade Y.grade f.toLinearMap f.map_grade x a := rfl

/-- **Stacks 01M7: the functor `M ↦ M̃` is exact**, in the form that it carries a short exact
sequence of graded `S`-modules to a short exact sequence of sheaves of `𝒪_{Proj 𝒮}`-modules.

Short exactness of sheaves of modules is short exactness on every stalk, the stalk of `M̃` at a
homogeneous prime `𝔭` is the degree-zero part of the localization of `M` at `𝔭`, and that
operation is exact. -/
@[stacks 01M7 "the functor M ↦ M~ is exact, in its categorical form: a short exact sequence \
of graded S-modules goes to a short exact sequence of sheaves of modules on Proj S"]
public theorem shortExact_map_associatedModuleSheafFunctor
    (T : ShortComplex (GradedModuleCat.{u, u, w} 𝒮)) (hT : T.ShortExact) :
    (T.map (associatedModuleSheafFunctor 𝒮)).ShortExact := by
  have hinj : Function.Injective T.f.toLinearMap := (mono_iff_injective T.f).1 hT.mono_f
  have hsurj : Function.Surjective T.g.toLinearMap := (epi_iff_surjective T.g).1 hT.epi_g
  have hexact : Function.Exact T.f.toLinearMap T.g.toLinearMap := exact_of_shortExact hT
  rw [SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact]
  intro x
  obtain ⟨h₁, h₂, h₃⟩ := associatedModuleSheafStalkMap_shortExact 𝒮 T.X₁.grade T.X₂.grade
    T.X₃.grade T.f.toLinearMap T.f.map_grade T.g.toLinearMap T.g.map_grade hinj hsurj hexact x
  refine ModuleCat.shortComplex_shortExact _ (fun z => ?_) (fun a b hab => ?_) (fun c => ?_)
  · exact (h₂ z).trans (exists_congr fun a => Iff.rfl)
  · exact h₁ hab
  · exact h₃ c

/-- **`M ↦ M̃` preserves homology**, which is the exactness of Stacks 01M7 in the form Mathlib's
`CategoryTheory.Functor.PreservesHomology` records. -/
@[sga "6 VI 2.3.3" "special case"]
public theorem preservesHomology_associatedModuleSheafFunctor :
    (associatedModuleSheafFunctor.{u, u, w} 𝒮).PreservesHomology :=
  ((Functor.exact_tfae (associatedModuleSheafFunctor.{u, u, w} 𝒮)).out 1 3).1
    (shortExact_map_associatedModuleSheafFunctor 𝒮)

attribute [local instance] preservesHomology_associatedModuleSheafFunctor

/-- **`M ↦ M̃` preserves finite limits**, so in particular kernels. -/
public theorem preservesFiniteLimits_associatedModuleSheafFunctor :
    PreservesFiniteLimits (associatedModuleSheafFunctor.{u, u, w} 𝒮) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- **`M ↦ M̃` preserves finite colimits**, so in particular cokernels. -/
public theorem preservesFiniteColimits_associatedModuleSheafFunctor :
    PreservesFiniteColimits (associatedModuleSheafFunctor.{u, u, w} 𝒮) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

attribute [local instance] preservesFiniteLimits_associatedModuleSheafFunctor
  preservesFiniteColimits_associatedModuleSheafFunctor

/-- An injective degree-preserving map of graded modules induces a monomorphism of associated
sheaves. -/
public theorem mono_map_associatedModuleSheafFunctor
    {X Y : GradedModuleCat.{u, u, w} 𝒮} (f : X ⟶ Y)
    (hf : Function.Injective f.toLinearMap) :
    Mono ((associatedModuleSheafFunctor 𝒮).map f) :=
  have := mono_of_injective hf
  Functor.map_mono _ f

/-- A surjective degree-preserving map of graded modules induces an epimorphism of associated
sheaves. -/
public theorem epi_map_associatedModuleSheafFunctor
    {X Y : GradedModuleCat.{u, u, w} 𝒮} (f : X ⟶ Y)
    (hf : Function.Surjective f.toLinearMap) :
    Epi ((associatedModuleSheafFunctor 𝒮).map f) :=
  have := epi_of_surjective hf
  Functor.map_epi _ f

end Functor

end Stacks.AlgebraicGeometry.ProjSheafFunctoriality

end
