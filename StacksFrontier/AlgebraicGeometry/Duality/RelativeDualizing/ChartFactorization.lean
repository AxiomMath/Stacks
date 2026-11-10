module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartInfrastructure
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.AssociatedPrimes
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Pairing
public import StacksFrontier.RingTheory.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Existence and finiteness of the finite-open factorizations of an affine chart

Every statement about the algebraic relative dualizing module of a quasi-finite ring map
`A → B` takes a finite-open factorization `A → B' → B` as a hypothesis: `B'` finite over `A`
and `Spec B → Spec B'` an open immersion. This file supplies the two facts about that
hypothesis that the hypothesis-taking statements never establish — that it is *satisfiable*,
and that the module it produces is *finite*.

## Main results

* `Stacks.Discriminant.nonempty_finiteOpenFactorization`: a quasi-finite algebra of finite type
  admits a finite-open factorization. This is Zariski's Main Theorem in the form of Tag 00QB
  part (3), assembled into the structure of Tag 0BSZ: the finite `A`-subalgebra `S''` produced
  there has exactly the three non-trivial fields of a `FiniteOpenFactorization`.
* `Stacks.Discriminant.nonempty_relativeDualizingChartFactorization`: the same for the affine
  charts of a morphism of schemes locally of finite type and locally quasi-finite — a chart being
  an affine open `V` of the source lying over an affine open `U` of the base.
* `Stacks.Discriminant.finite_dualizingModule` and
  `Stacks.Discriminant.finitePresentation_dualizingModule`: the algebraic relative dualizing
  module `Hom_A(B', A) ⊗_{B'} B` is a finite `B`-module, and finitely presented when `B` is
  Noetherian.
* `Stacks.Discriminant.localEquiv_natural_of_chartEquiv`: a family of identifications obtained
  from one chosen factorization by composing with the canonical comparisons is automatically
  natural in the factorization.
* `Stacks.Discriminant.nontrivial_dualizingModule_self` and
  `Stacks.Discriminant.exists_finiteOpenFactorization_nontrivial_dualizingModule`: the
  factorization supplied above is not a degenerate one — the dualizing module of *any*
  finite-open factorization of a field by itself is nonzero, so the existence statement really
  does produce usable data.

## Implementation notes

The factorization is built from `Stacks.quasiFinite_exists_finite_subalgebra` with no further
input: for a subalgebra `C` of `B` the algebra instances `Algebra A C`, `Algebra C B` and the
scalar tower are the ones Mathlib already provides, and `algebraMap C B` *is* `C.val.toRingHom`,
so the open-embedding and away-map fields transfer unchanged. Note that `Algebra.QuasiFinite`
in Mathlib does not include finite type (its docstring records the divergence from Tag 00PL), so
both hypotheses are needed; on the scheme side they come from `LocallyOfFiniteType` and
`LocallyQuasiFinite` through their `appLE` fields.

Finiteness of the dualizing module is read off the commuted model
`Stacks.Discriminant.dualizingModuleCommEquiv : dualizingModule F ≃ₗ[B] B ⊗[B'] Hom_A(B', A)`:
the dual `Hom_A(B', A)` is a finite `A`-module because `A` is Noetherian and `B'` is a finite
`A`-module, hence a finite `B'`-module, and base change to `B` preserves finiteness. The scalar
tower `A → B' → Hom_A(B', A)` that the restriction-of-scalars step needs is not an instance —
the `B'`-action on the dual is the local instance `Stacks.Discriminant.algebraDualModule` — so it
is supplied from `A`-linearity of the functionals.

## References

* [Stacks Project, Tag 00QB](https://stacks.math.columbia.edu/tag/00QB)
* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry TensorProduct

universe u v w x y z

namespace Stacks.Discriminant

open _root_.Stacks.Topology

attribute [local instance] algebraDualModule

/- Needed by `localEquiv_natural_of_chartEquiv`: unfolding the construction of the canonical
comparison makes unification unfold `SetLike.coe` without bound, and the statement dies on
`maxRecDepth`.  `dualizingModuleEquiv` is declared `[irreducible]` at its definition site, so
no attribute is needed here. -/

/-- **Zariski's Main Theorem gives a finite-open factorization.** A quasi-finite algebra of
finite type over a commutative ring factors through a finite subalgebra whose spectrum receives
an open immersion, i.e. it admits a finite-open factorization in the sense of Tag 0BSZ. -/
public theorem nonempty_finiteOpenFactorization {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [Algebra.QuasiFinite A B] :
    Nonempty (FiniteOpenFactorization.{u, v, v} A B) := by
  obtain ⟨C, _, hfin, hopen, hbij⟩ :=
    quasiFinite_exists_finite_subalgebra (R := A) (S := B)
  exact ⟨{ middle := C
           commRingMiddle := inferInstance
           algebraMiddle := inferInstance
           algebraTarget := inferInstance
           scalarTower := inferInstance
           finite_middle := hfin
           isOpenEmbedding_comap := hopen
           awayMap_bijective := hbij }⟩

/-- The algebraic relative dualizing module of a finite-open factorization over a Noetherian
base is a finite module over the target. -/
public theorem finite_dualizingModule {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Module.Finite B (dualizingModule F) := by
  have h1 : Module.Finite A (Module.Dual A F.middle) := inferInstance
  let : IsScalarTower A F.middle (Module.Dual A F.middle) :=
    IsScalarTower.of_algebraMap_smul fun a g => by
      ext x
      change g (algebraMap A F.middle a * x) = a • g x
      rw [← Algebra.smul_def, map_smul]
  have h2 : Module.Finite F.middle (Module.Dual A F.middle) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have h3 : Module.Finite B (B ⊗[F.middle] Module.Dual A F.middle) :=
    Module.Finite.base_change _ _ _
  exact Module.Finite.equiv (dualizingModuleCommEquiv F).symm

/-- Over a Noetherian base with Noetherian target, the algebraic relative dualizing module of a
finite-open factorization is a finitely presented module over the target. -/
public theorem finitePresentation_dualizingModule {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Module.FinitePresentation B (dualizingModule F) :=
  have := finite_dualizingModule F
  Module.finitePresentation_of_finite B (dualizingModule F)

/-- **Independence of the chosen factorization comes for free.** Fix one finite-open
factorization `F₀` and one identification `e₀` of a module `M` with its dualizing module, and
define the identification at an arbitrary factorization `F` by composing `e₀` with the canonical
comparison `F₀ → F`. Then the resulting family is automatically natural in the factorization:
this is the composition law for the canonical comparisons, read at one element.

This is the content of the `localEquiv_natural` field of the relative dualizing module data, for
the only sensible definition of its `localEquiv` field. -/
public theorem localEquiv_natural_of_chartEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    {M : Type w} [AddCommGroup M] [Module B M]
    (F₀ : FiniteOpenFactorization.{u, v, x} A B)
    (e₀ : M ≃ₗ[B] dualizingModule F₀)
    (F : FiniteOpenFactorization.{u, v, y} A B)
    (G : FiniteOpenFactorization.{u, v, z} A B) (s : M) :
    (e₀.trans (dualizingModuleEquiv F₀ G)) s =
      dualizingModuleEquiv F G ((e₀.trans (dualizingModuleEquiv F₀ F)) s) :=
  (DFunLike.congr_fun (dualizingModuleEquiv_trans F₀ F G) (e₀ s)).symm

/-- **The factorizations produced above are not degenerate.** The dualizing module of any
finite-open factorization of a field by itself is nonzero: Tag 0BVD identifies its associated
primes with those of the base over itself, and `(0)` is one of them, while a module with an
associated prime cannot be zero. -/
public theorem nontrivial_dualizingModule_self {K : Type u} [Field K]
    (F : FiniteOpenFactorization.{u, u, w} K K) : Nontrivial (dualizingModule F) := by
  have hz : (⊥ : Ideal K) ∈ associatedPrimes K K := by
    refine ⟨inferInstance, 1, ?_⟩
    have hcol : Submodule.colon (⊥ : Submodule K K) {(1 : K)} = ⊥ := by
      ext r; simp [Submodule.mem_colon_singleton]
    rw [hcol, (inferInstance : (⊥ : Ideal K).IsPrime).radical]
  set q : PrimeSpectrum K := ⟨⊥, inferInstance⟩ with hq
  obtain ⟨-, x, hx⟩ :=
    (mem_associatedPrimes_dualizingModule_iff F q).2 (by simpa [hq] using hz)
  rcases subsingleton_or_nontrivial (dualizingModule F) with hs | hn
  · exfalso
    have hone : (1 : K) ∈ q.asIdeal := by
      rw [hx]
      exact Ideal.le_radical (Submodule.mem_colon.2
        (fun p _ => (Submodule.mem_bot _).2 (Subsingleton.elim _ _)))
    rw [hq] at hone
    simp at hone
  · exact hn

/-- Existence and non-degeneracy together: a field admits a finite-open factorization of itself
whose dualizing module is nonzero. -/
public theorem exists_finiteOpenFactorization_nontrivial_dualizingModule
    (K : Type u) [Field K] :
    ∃ F : FiniteOpenFactorization.{u, u, u} K K, Nontrivial (dualizingModule F) :=
  ⟨nonempty_finiteOpenFactorization.some, nontrivial_dualizingModule_self _⟩

/-- **The finite-open factorizations of an affine chart are nonempty.** For a morphism of schemes
locally of finite type and locally quasi-finite, an affine open `V` of the source contained in
the preimage of an affine open `U` of the base, the coordinate-ring map `Γ(X, U) → Γ(Y, V)`
admits a finite-open factorization. -/
public theorem nonempty_relativeDualizingChartFactorization {X Y : Scheme.{u}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    Nonempty (FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra.FiniteType Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.finiteType_algebraMap.mp (LocallyOfFiniteType.finiteType_appLE f U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  exact nonempty_finiteOpenFactorization

end Stacks.Discriminant

end
