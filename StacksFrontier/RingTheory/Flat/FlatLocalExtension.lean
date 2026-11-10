module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Finiteness
public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
public import StacksFrontier.RingTheory.Flat.DevissageProjectiveStages
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat local extensions over which a finite module becomes finitely presented

Let `S` be a ring, `q` a prime of `S` and `T` a localization of `S` at `q`, and let `M` be a
finite `T`-module. The question of Stacks 05I7 is whether there is a flat local extension
`T → T'` of local rings such that `T' ⊗[T] M` is a finitely presented `T'`-module.

This file produces such an extension out of a *spreading out* of the data: a flat `S`-algebra
`S'`, a prime `q'` of `S'` contracting to `q`, and a base change of `M`'s model over `S` to `S'`
which is finitely presented over `S'`. The extension is the localization `T' = S'_{q'}`, and the
three properties asked of it — locality of `T'`, locality of `T → T'` and flatness of `T'` over
`T` — are the two lemmas `Stacks.Flatness.flat_of_flat_of_isLocalization` and
`Stacks.Flatness.isLocalHom_of_isLocalization_of_comap` below. Finite presentation of
`T' ⊗[T] M` is obtained by identifying it with the localization of the spread-out module at
`q'`, which is done entirely through `IsBaseChange`: both `T' ⊗[T] M` and that localization are
base changes of the model along `S → T'`, so they are canonically isomorphic as `T'`-modules
without any manipulation of tensor products.

The spreading out itself is *not* proved here; it is the content of Stacks 05I5, equivalently of
Stacks 05I1 (existence of a complete dévissage after an elementary étale localization) followed
by Stacks 05I4. Since Stacks 05I4 is available in this repository as
`Module.CompleteDevissageAt.finitePresentation_of_flat`, the last result below takes a complete
dévissage of the spread-out module over a local base and feeds it into the construction, leaving
exactly the existence of the dévissage open.

## Main results

* `Module.exists_fg_submodule_isLocalizedModule`: a finite module over a localization of `S` is
  the localization of a finitely generated `S`-submodule of itself. This is what turns a module
  over the local ring `T` into a module over `S` that can be spread out.
* `Stacks.Flatness.flat_of_flat_of_isLocalization`: if `S'` is a flat `S`-algebra and `q'` is a
  prime of `S'`, then `S'_{q'}` is flat over `S_q` for any prime `q` of `S` — no condition
  relating `q` and `q'` is needed beyond the scalar towers.
* `Stacks.Flatness.isLocalHom_of_isLocalization_of_comap`: if moreover `q` is the contraction of
  `q'`, then `S_q → S'_{q'}` is a local homomorphism.
* `Stacks.Flatness.exists_flatLocalExtension_finitePresentation_of_isBaseChange`: the flat local
  extension of `T` over which `M` becomes finitely presented, granted the spread-out finite
  presentation.
* `Stacks.Flatness.exists_flatLocalExtension_finitePresentation_of_completeDevissage`: the same
  conclusion with the spread-out finite presentation replaced by a complete dévissage of the
  spread-out module over a local base, via Stacks 05I4.

## Implementation notes

The extension is built as `Localization.AtPrime q'` rather than taken as an abstract localization
of `S'`, because the conclusion is an existential statement and because the `T'`-module structure
on the localization of the spread-out module is then the one Mathlib already knows is finitely
presented. The `T`-algebra structure on it is `IsLocalization.lift`, whose universal property
also supplies the scalar tower `S → T → T'`.

The hypothesis that `M` is the localization of the model `N` is phrased as
`IsLocalizedModule q.primeCompl f` for a map `f : N →ₗ[S] M`, and the hypothesis that `N'` is the
base change of `N` as `IsBaseChange S' g` for a map `g : N →ₗ[S] N'`. Both are closed under the
composition `IsBaseChange.comp`, which is why no tensor product has to be written down: the
canonical isomorphism comes from `IsBaseChange.equiv` applied to two base changes of the same
module `N` along the same ring map `S → T'`.

## References

* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05I1](https://stacks.math.columbia.edu/tag/05I1)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-- A finite module over a localization `T` of `S` is the localization of a finitely generated
`S`-submodule of itself.

Concretely, generators of `M` over `T` span an `S`-submodule `N` whose inclusion into `M`
exhibits `M` as the localization of `N`: the elements of the submonoid act invertibly on `M`
because `M` is a `T`-module, every element of `M` has a multiple in `N` by
`multiple_mem_span_of_mem_localization_span`, and the inclusion is injective. -/
theorem Module.exists_fg_submodule_isLocalizedModule {S : Type u} [CommRing S] (P : Submonoid S)
    (T : Type v) [CommRing T] [Algebra S T] [IsLocalization P T]
    {M : Type w} [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower S T M]
    [Module.Finite T M] :
    ∃ N : Submodule S M, N.FG ∧ IsLocalizedModule P N.subtype := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := T) (M := M)
  refine ⟨Submodule.span S (Set.range g), Submodule.fg_span (Set.finite_range g), ?_, ?_, ?_⟩
  · have : IsLocalizedModule P (LinearMap.id : M →ₗ[S] M) := isLocalizedModule_id P M T
    exact fun x => IsLocalizedModule.map_units (LinearMap.id : M →ₗ[S] M) x
  · intro y
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span P T (Set.range g) y
      (by rw [hg]; exact Submodule.mem_top)
    exact ⟨⟨⟨t • y, ht⟩, t⟩, rfl⟩
  · intro x₁ x₂ h
    exact ⟨1, by rw [show x₁ = x₂ from Subtype.ext h]⟩

namespace Stacks.Flatness

/-- **A localization of a flat algebra at a prime is flat over a localization of the base.**
If `S'` is a flat `S`-algebra, `T` is a localization of `S` at a prime `q` and `T'` is a
localization of `S'` at a prime `q'`, then `T'` is flat over `T`.

Flatness of `T'` over `S` is flatness of a localization of a flat algebra, and an `S`-flat module
which is a module over the localization `T` is flat over `T`. -/
theorem flat_of_flat_of_isLocalization {S : Type u} [CommRing S] {S' : Type v} [CommRing S']
    [Algebra S S'] (q : Ideal S) [q.IsPrime] (q' : Ideal S') [q'.IsPrime]
    (T : Type w) [CommRing T] [Algebra S T] [IsLocalization.AtPrime T q]
    (T' : Type*) [CommRing T'] [Algebra S' T'] [IsLocalization.AtPrime T' q']
    [Algebra S T'] [IsScalarTower S S' T'] [Algebra T T'] [IsScalarTower S T T']
    [Module.Flat S S'] : Module.Flat T T' :=
  (Module.flat_iff_of_isLocalization T q.primeCompl T').mpr
    (have : Module.Flat S' T' := IsLocalization.flat T' q'.primeCompl
     Module.Flat.trans S S' T')

/-- An element outside `q = q'.comap (algebraMap S S')` is a unit in the localization at `q'`. -/
private theorem isUnit_algebraMap_of_notMem_comap {S : Type u} [CommRing S] {S' : Type v}
    [CommRing S'] [Algebra S S'] {q : Ideal S} [q.IsPrime] {q' : Ideal S'} [q'.IsPrime]
    (hq : q = q'.comap (algebraMap S S')) (T' : Type*) [CommRing T'] [Algebra S' T']
    [IsLocalization.AtPrime T' q'] [Algebra S T'] [IsScalarTower S S' T'] (b : q.primeCompl) :
    IsUnit (algebraMap S T' (b : S)) := by
  rw [IsScalarTower.algebraMap_apply S S' T']
  refine IsLocalization.map_units T' (⟨algebraMap S S' (b : S), ?_⟩ : q'.primeCompl)
  intro hmem
  exact b.2 ((SetLike.ext_iff.mp hq _).mpr (Ideal.mem_comap.mpr hmem))

/-- **A localization at a prime over `q` is a local extension of the localization at `q`.**
If `q` is the contraction of `q'` along `S → S'`, then the induced map from the localization of
`S` at `q` to the localization of `S'` at `q'` is a local homomorphism.

An element of the maximal ideal of `T` is `a / b` with `a ∈ q` and `b ∉ q`; its image in `T'`,
multiplied by the image of `b`, is the image of `a`, which lies in the maximal ideal of `T'`
because `a ∈ q` forces the image of `a` into `q'`, while the image of `b` is a unit because
`b ∉ q` keeps the image of `b` out of `q'`. -/
@[ega "I 8.1.1" "(i) ⇒ (ii)", ega "IV 1.3.10" "locality of A_p → B"]
theorem isLocalHom_of_isLocalization_of_comap {S : Type u} [CommRing S] {S' : Type v}
    [CommRing S'] [Algebra S S'] (q : Ideal S) [q.IsPrime] (q' : Ideal S') [q'.IsPrime]
    (T : Type w) [CommRing T] [Algebra S T] [IsLocalization.AtPrime T q]
    (T' : Type*) [CommRing T'] [Algebra S' T'] [IsLocalization.AtPrime T' q']
    [Algebra S T'] [IsScalarTower S S' T'] [Algebra T T'] [IsScalarTower S T T']
    (hq : q = q'.comap (algebraMap S S')) : IsLocalHom (algebraMap T T') := by
  have hT : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T q
  have hT' : IsLocalRing T' := IsLocalization.AtPrime.isLocalRing T' q'
  have key : IsLocalRing.maximalIdeal T ≤
      Ideal.comap (algebraMap T T') (IsLocalRing.maximalIdeal T') := by
    intro x hx
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    have ha : a ∈ q := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff T q a]
      exact IsLocalization.mk'_mem_iff.mp hx
    have hbunit := isUnit_algebraMap_of_notMem_comap hq T' b
    have hamem : algebraMap S T' a ∈ IsLocalRing.maximalIdeal T' := by
      rw [IsScalarTower.algebraMap_apply S S' T',
        IsLocalization.AtPrime.to_map_mem_maximal_iff T' q']
      rw [hq] at ha
      exact Ideal.mem_comap.mp ha
    have heq : algebraMap S T' (b : S) * algebraMap T T' (IsLocalization.mk' T a b) =
        algebraMap S T' a := by
      rw [IsScalarTower.algebraMap_apply S T T', IsScalarTower.algebraMap_apply S T T',
        ← map_mul, mul_comm, IsLocalization.mk'_spec]
    simp only [Ideal.mem_comap]
    refine (Ideal.unit_mul_mem_iff_mem _ hbunit).mp ?_
    rw [heq]
    exact hamem
  exact ((IsLocalRing.local_hom_TFAE (algebraMap T T')).out 4 1).mp key

/-- **The flat local extension over which a finite flat module becomes finitely presented,
granted the spreading out.**

Let `T` be a localization of `S` at a prime `q` and let `M` be a `T`-module which is the
localization at `q` of an `S`-module `N`. Suppose `N` spreads out to a finitely presented module
`N'` over a flat `S`-algebra `S'`, at a prime `q'` of `S'` contracting to `q`. Then there is a
flat local extension `T → T'` of local rings with `T' ⊗[T] M` finitely presented over `T'`,
namely the localization of `S'` at `q'`.

This is the passage from the conclusion of Stacks 05I5 in local algebra to the conclusion of
Stacks 05I7; the spreading out is the part that is not proved here. -/
theorem exists_flatLocalExtension_finitePresentation_of_isBaseChange
    {S : Type u} [CommRing S] (q : Ideal S) [q.IsPrime]
    (T : Type u) [CommRing T] [Algebra S T] [IsLocalization.AtPrime T q]
    {M : Type u} [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower S T M]
    {N : Type u} [AddCommGroup N] [Module S N] (f : N →ₗ[S] M)
    [IsLocalizedModule q.primeCompl f]
    (S' : Type u) [CommRing S'] [Algebra S S'] [Module.Flat S S']
    (q' : Ideal S') [q'.IsPrime] (hq : q = q'.comap (algebraMap S S'))
    {N' : Type u} [AddCommGroup N'] [Module S N'] [Module S' N'] [IsScalarTower S S' N']
    (g : N →ₗ[S] N') (hg : IsBaseChange S' g) [Module.FinitePresentation S' N'] :
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T'), IsLocalRing T' ∧
      IsLocalHom (algebraMap T T') ∧ Module.Flat T T' ∧
      Module.FinitePresentation T' (T' ⊗[T] M) := by
  have hunits := isUnit_algebraMap_of_notMem_comap hq (Localization.AtPrime q')
  let algTT' : Algebra T (Localization.AtPrime q') :=
    (IsLocalization.lift (S := T) hunits).toAlgebra
  have htower : IsScalarTower S T (Localization.AtPrime q') :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunits x).symm
  refine ⟨Localization.AtPrime q', inferInstance, algTT', inferInstance,
    isLocalHom_of_isLocalization_of_comap q q' T _ hq, flat_of_flat_of_isLocalization q q' T _,
    ?_⟩
  have hA : IsBaseChange (Localization.AtPrime q')
      ((TensorProduct.mk T (Localization.AtPrime q') M 1).restrictScalars S ∘ₗ f) :=
    (IsLocalizedModule.isBaseChange q.primeCompl T f).comp
      (TensorProduct.isBaseChange T M (Localization.AtPrime q'))
  have hB : IsBaseChange (Localization.AtPrime q')
      ((LocalizedModule.mkLinearMap q'.primeCompl N').restrictScalars S ∘ₗ g) :=
    hg.comp (IsLocalizedModule.isBaseChange q'.primeCompl (Localization.AtPrime q')
      (LocalizedModule.mkLinearMap q'.primeCompl N'))
  exact Module.FinitePresentation.of_equiv (hB.equiv.symm.trans hA.equiv)

/-- **The flat local extension over which a finite flat module becomes finitely presented,
granted a complete dévissage of the spread-out module.**

This is `Stacks.Flatness.exists_flatLocalExtension_finitePresentation_of_isBaseChange` with its
finite-presentation hypothesis discharged by Stacks 05I4, in the form
`Module.CompleteDevissageAt.finitePresentation_of_flat`: the spread-out algebra `S'` is of finite
presentation over a local ring `R'`, the spread-out module `N'` is finite over `S'` and flat over
`R'` after localizing at `q'`, and `N'/S'/R'` has a complete dévissage at `q'`.

What remains open for Stacks 05I7 is therefore the *existence* of the dévissage, which is
Stacks 05I1, together with its base change to the local ring `R'`. -/
theorem exists_flatLocalExtension_finitePresentation_of_completeDevissage
    {S : Type u} [CommRing S] (q : Ideal S) [q.IsPrime]
    (T : Type u) [CommRing T] [Algebra S T] [IsLocalization.AtPrime T q]
    {M : Type u} [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower S T M]
    {N : Type u} [AddCommGroup N] [Module S N] (f : N →ₗ[S] M)
    [IsLocalizedModule q.primeCompl f]
    (R' : Type u) [CommRing R'] [IsLocalRing R']
    (S' : Type u) [CommRing S'] [Algebra R' S'] [Algebra.FinitePresentation R' S']
    [Algebra S S'] [Module.Flat S S']
    (q' : Ideal S') [q'.IsPrime] (hq : q = q'.comap (algebraMap S S'))
    {N' : Type u} [AddCommGroup N'] [Module S N'] [Module S' N'] [IsScalarTower S S' N']
    [Module R' N'] [IsScalarTower R' S' N'] [Module.Finite S' N']
    (g : N →ₗ[S] N') (hg : IsBaseChange S' g)
    (hq'R : q'.under R' = IsLocalRing.maximalIdeal R')
    (hflat' : Module.Flat R' (LocalizedModule q'.primeCompl N'))
    (D : Module.CompleteDevissageAt R' S' N' q') :
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T'), IsLocalRing T' ∧
      IsLocalHom (algebraMap T T') ∧ Module.Flat T T' ∧
      Module.FinitePresentation T' (T' ⊗[T] M) :=
  have : Module.FinitePresentation S' N' := D.finitePresentation_of_flat hq'R hflat'
  exists_flatLocalExtension_finitePresentation_of_isBaseChange q T f S' q' hq g hg

end Stacks.Flatness

/-- **A local homomorphism essentially of finite presentation presents its target as a
localization at a prime.**

Let `φ : R →+* T` be a local homomorphism of local rings which is essentially of finite
presentation. Then `T` is, as an `R`-algebra, the localization of an `R`-algebra `A` of finite
presentation *at a prime*, and that prime contracts to the maximal ideal of `R`.

Being essentially of finite presentation only says that `T` is the localization of such an `A` at
some submonoid. The prime is the contraction of the maximal ideal of `T`: every element of the
submonoid becomes a unit in `T`, hence lies outside that contraction, and conversely every
element outside the contraction already becomes a unit in `T` because `T` is local, so the
localization at the submonoid is also the localization at the prime. -/
@[ega "IV 1.3.10" "special case"]
theorem RingHom.EssentiallyOfFinitePresentation.exists_isLocalization_atPrime
    {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T] (φ : R →+* T)
    [IsLocalHom φ] (hφ : φ.EssentiallyOfFinitePresentation) :
    letI := φ.toAlgebra
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra A T)
      (_ : IsScalarTower R A T) (_ : Algebra.FinitePresentation R A) (q : Ideal A)
      (_ : q.IsPrime), IsLocalization.AtPrime T q ∧
        q.comap (algebraMap R A) = IsLocalRing.maximalIdeal R := by
  let := φ.toAlgebra
  obtain ⟨A, _, _, _, _, _, P, hP⟩ := hφ
  set q : Ideal A := (IsLocalRing.maximalIdeal T).comap (algebraMap A T) with hqdef
  have hqp : q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : IsLocalization.AtPrime T q :=
    IsLocalization.of_le P _
      (fun y hy => IsLocalRing.notMem_maximalIdeal.mpr (IsLocalization.map_units T ⟨y, hy⟩))
      fun _ hr => IsLocalRing.notMem_maximalIdeal.mp hr
  have hcomap : q.comap (algebraMap R A) = IsLocalRing.maximalIdeal R := by
    rw [hqdef, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R A T]
    exact ((IsLocalRing.local_hom_TFAE φ).out 1 5).mp ‹IsLocalHom φ›
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, q, hqp,
    hloc, hcomap⟩

namespace Stacks.Flatness

/-- **The local-algebra content of Stacks 05I5**: a finite module over an algebra of finite
presentation over a local ring, flat over that ring after localizing at a prime of the closed
fibre, becomes finitely presented after a flat local base change together with a flat extension
of the algebra.

The local ring `R'` and the finite presentation of `A'` over it are what make this statement
stronger than its consequence
`Stacks.Flatness.ExistsFlatLocalExtensionFinitePresentation`-style existentials: `A'` must again
be spread out over a local base, so it cannot be taken to be the localization one is trying to
produce. In the Stacks Project this is Proposition 38.10.3 in algebraic form, obtained from the
existence of a complete dévissage after an elementary étale localization (Stacks 05I1), its base
change to the local ring of the base, and Stacks 05I4. -/
def ExistsSpreadOutFinitePresentation : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [IsLocalRing R] [Algebra R A]
    [Algebra.FinitePresentation R A] (q : Ideal A) [q.IsPrime],
    q.comap (algebraMap R A) = IsLocalRing.maximalIdeal R →
    ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N] [Module R N]
      [IsScalarTower R A N], Module.Flat R (LocalizedModule q.primeCompl N) →
      ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
        (_ : IsLocalHom (algebraMap R R')) (_ : Module.Flat R R')
        (A' : Type u) (_ : CommRing A') (_ : Algebra R' A')
        (_ : Algebra.FinitePresentation R' A') (_ : Algebra A A') (_ : Module.Flat A A')
        (q' : Ideal A') (_ : q'.IsPrime),
        q = q'.comap (algebraMap A A') ∧ Module.FinitePresentation A' (A' ⊗[A] N)

/-- **Stacks 05I7 in local algebra, granted the spreading out of Stacks 05I5.**

For a local homomorphism `φ : R →+* T` of local rings which is essentially of finite presentation
and a finite `T`-module `M` which is flat over `R`, there is a flat local extension `T → T'` of
local rings over which `M` becomes finitely presented.

The proof writes `T` as the localization of an `R`-algebra `A` of finite presentation at a prime
`q` over the maximal ideal of `R`, replaces `M` by a finitely generated `A`-submodule of itself
localizing to it, applies the spreading out to that submodule, and feeds the result to
`Stacks.Flatness.exists_flatLocalExtension_finitePresentation_of_isBaseChange`.

This is literally the statement
`Stacks.Flatness.ExistsFlatLocalExtensionFinitePresentation` of
`StacksFrontier.AlgebraicGeometry.Flatness.FinitePresentationStalk`, so that the geometric Stacks
05I7 proved there is reduced to `Stacks.Flatness.ExistsSpreadOutFinitePresentation`, i.e. to
Stacks 05I5, rather than to itself. -/
theorem exists_flatLocalExtension_finitePresentation_of_existsSpreadOut
    (H : ExistsSpreadOutFinitePresentation.{u}) :
    ∀ (R T : Type u) [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
      (φ : R →+* T) [IsLocalHom φ], φ.EssentiallyOfFinitePresentation →
        ∀ (M : Type u) [AddCommGroup M] [Module T M] [Module.Finite T M],
          (letI := Module.compHom M φ; Module.Flat R M) →
          ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T'),
            IsLocalRing T' ∧ IsLocalHom (algebraMap T T') ∧ Module.Flat T T' ∧
              Module.FinitePresentation T' (TensorProduct T T' M) := by
  intro R T _ _ _ _ φ _ hφ M _ _ _ hM
  let := φ.toAlgebra
  obtain ⟨A, _, _, _, _, _, q, _, hloc, hcomap⟩ := hφ.exists_isLocalization_atPrime φ
  let : Module R M := Module.compHom M φ
  let : Module A M := Module.compHom M (algebraMap A T)
  have htAT : IsScalarTower A T M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have htRA : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun r x => by
    change algebraMap A T (algebraMap R A r) • x = φ r • x
    rw [← IsScalarTower.algebraMap_apply R A T]
    rfl
  obtain ⟨N, hNfg, hNloc⟩ :=
    Module.exists_fg_submodule_isLocalizedModule (M := M) q.primeCompl T
  have hNfin : Module.Finite A N := Module.Finite.iff_fg.mpr hNfg
  have hflatN : Module.Flat R (LocalizedModule q.primeCompl N) :=
    Module.Flat.of_linearEquiv (LinearEquiv.restrictScalars R
      (IsLocalizedModule.linearEquiv q.primeCompl
        (LocalizedModule.mkLinearMap q.primeCompl (N : Type u)) N.subtype))
  obtain ⟨R', _, _, _, _, _, A', _, _, _, _, _, q', _, hqq', hfpA'⟩ :=
    H R A q hcomap (N : Type u) hflatN
  exact exists_flatLocalExtension_finitePresentation_of_isBaseChange q T N.subtype A' q' hqq'
    (TensorProduct.mk A A' (N : Type u) 1) (TensorProduct.isBaseChange A (N : Type u) A')

end Stacks.Flatness

end
