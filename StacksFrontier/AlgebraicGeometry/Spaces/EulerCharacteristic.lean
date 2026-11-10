module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyOverBaseFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCohomologyUniformVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase
public import StacksFrontier.AlgebraicGeometry.Topologies.BaseIdealMultiple
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear

/-!
# Euler characteristic of a coherent module on a proper algebraic space over a field

Let `k` be a field and `X` a proper algebraic space over `k`. For a coherent `𝒪_X`-module `F`
the Euler characteristic is the alternating sum
`χ(X, F) = ∑ᵢ (-1)ⁱ dim_k Hⁱ(X, F)`
of the dimensions over `k` of the cohomology modules of `F` on the small étale site of `X`.

Alongside the definition this file proves additivity of `χ` along a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of coherent modules (Stacks 0DN2):

`χ(X, F₂) = χ(X, F₁) + χ(X, F₃)`.

The proof is the source's: the long exact cohomology sequence of a short exact sequence of
`𝒪_X`-modules, followed by rank-nullity. It uses the two facts that make `χ` a finite
alternating sum of finite dimensions, namely that each `Hⁱ(X, F)` is finite-dimensional over `k`
(Stacks 08AS) and that `Hⁱ(X, F)` vanishes for `i` beyond a bound independent of the coherent
module `F` (Stacks 072C, for `X` quasi-compact and quasi-separated). The rank-nullity step is
also recorded with these two facts as hypotheses, for all three modules or for the outer two
only, together with the propagation of both facts from the outer two terms of the sequence to
the middle one; those forms make no use of properness or coherence.

## Main definitions

* `AlgebraicGeometry.Space.eulerCharacteristic`: the Euler characteristic of a coherent module on
  a proper algebraic space over a field.
* `AlgebraicGeometry.Space.cohomologyOverBaseMap`: for an algebraic space over a base ring `A`,
  the `A`-linear map `Hⁱ(X, F) ⟶ Hⁱ(X, G)` induced by a morphism `F ⟶ G` of `𝒪_X`-modules, that
  is, functoriality of `AlgebraicGeometry.Space.cohomologyOverBase` in the module. Its two
  functor laws are `AlgebraicGeometry.Space.cohomologyOverBaseMap_id` and
  `AlgebraicGeometry.Space.cohomologyOverBaseMap_comp`.

## Main results

* `AlgebraicGeometry.Space.eulerCharacteristic_eq_finsum`: the defining alternating sum.
* `AlgebraicGeometry.Space.eulerCharacteristic_congr`: isomorphic coherent modules have the same
  Euler characteristic.
* `AlgebraicGeometry.Space.exists_cohomologyOverBase_longExactSequence`: **the long exact
  sequence of cohomology over the base.** For a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of
  `𝒪_X`-modules there are connecting maps `Hⁱ(X, F₃) ⟶ Hⁱ⁺¹(X, F₁)` of `A`-modules making
  `0 ⟶ H⁰(X, F₁) ⟶ H⁰(X, F₂) ⟶ H⁰(X, F₃) ⟶ H¹(X, F₁) ⟶ ⋯` exact. There is no hypothesis on the
  base ring, on a morphism to the base, or on the modules.
* `AlgebraicGeometry.Space.finiteDimensional_cohomologyOverBase_of_shortExact` and
  `AlgebraicGeometry.Space.isZero_cohomologyOverBase_of_shortExact`: finite dimensionality and
  vanishing of `Hⁱ(X, F₂)` follow from the same for `Hⁱ(X, F₁)` and `Hⁱ(X, F₃)`.
* `AlgebraicGeometry.Space.finsum_alternating_finrank_cohomologyOverBase_add_of_shortExact`, and
  its variant `..._of_outer`: additivity of the alternating sum of dimensions of cohomology, with
  the two inputs assumed for all three modules and for the outer two only, respectively.
* `AlgebraicGeometry.Space.eulerCharacteristic_add_of_shortExact_of_finiteDimensional_of_isZero`:
  additivity of `χ` itself, with the finiteness and vanishing assumed for all three modules.
* `AlgebraicGeometry.Space.eulerCharacteristic_add_of_shortExact_of_outer`: **Stacks 0DN2.**
  Additivity of `χ` along a short exact sequence of coherent modules on a proper algebraic space
  over a field, with no further hypothesis.

## Implementation notes

**The cohomology used.** `AlgebraicGeometry.Space.cohomologyOverBase` is cohomology on the small
étale ringed site of `X`, with scalars restricted along
`AlgebraicGeometry.Space.baseRingHom` to the base ring; instantiated at the base ring `k` this is
the `k`-vector space `Hⁱ(X, F)` of the source. Its module universe is `max (u + 1) w` rather than
the universe `u` of the schemes, because the derived global sections of a ringed site take values
in a module universe containing the site, and the small étale site of an algebraic space over a
`Scheme.{u}` lives in `Type (u + 1)`.

**The proof of additivity.** The source's proof of additivity is the long exact sequence of
cohomology followed by rank-nullity: the sequence is
`AlgebraicGeometry.Space.exists_cohomologyOverBase_longExactSequence`, obtained from
`Stacks.Cohomology.SiteModules.cohomologyDeltaFunctor` by pushing its exactness through
restriction of scalars, and the rank-nullity computation is
`Module.finsum_alternating_finrank_add_of_exact`. What makes `χ` a well-defined integer, and the
alternating sums finite, is that for proper structure morphism and coherent module

* `Hⁱ(X, F)` is a finite `k`-module ([Stacks, Tag 08AS]), which is
  `AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_isProper_of_isCoherent`, and
* `Hⁱ(X, F) = 0` for all `i ≥ N`, with `N` depending only on `X` ([Stacks, Tag 072C]), which is
  `AlgebraicGeometry.Space.exists_forall_isZero_cohomologyOverBase_of_isCoherent_of_qcqs`, `X`
  being quasi-compact and quasi-separated as it is proper over `Spec k`.

The source states these in the introduction of its section rather than in the lemma. The
rank-nullity step itself is stated separately with both facts as hypotheses, exactly as the
finite dimensionality of [Stacks, Tag 02O6] and the vanishing of [Stacks, Tag 01XJ] are
hypotheses of the scheme-level
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional_of_isZero`; in
that form neither properness nor coherence is used.

**Transport through restriction of scalars.** Restriction of scalars along
`AlgebraicGeometry.Space.baseRingHom` changes neither the underlying types nor the underlying
functions, so exactness and injectivity of the maps produced by the `δ`-functor transport to the
`A`-linear maps by applying the hypothesis to the same element. Exactness is stated as
`Function.Exact` on the underlying maps and the connecting maps are existentially quantified,
which keeps `CategoryTheory.HasDerivedCategory` — needed to construct the connecting map, with no
global instance, and not mentioned by `AlgebraicGeometry.Space.cohomologyOverBase` — out of the
statement.

**Reuse.** The two linear-algebra inputs, `Module.finsum_alternating_finrank_add_of_exact` and
`Module.finiteDimensional_of_exact`, are universe-polymorphic statements about `k`-vector spaces
proved for the scheme-level theory and are used verbatim. Only the analogue of
`AlgebraicGeometry.finiteDimensional_of_isZero` has to be restated, since that one is stated for
`ModuleCat.{u} k` while the cohomology of an algebraic space lives in `ModuleCat.{max (u + 1) w}`.

## References

* [Stacks Project, Tag 0DN1](https://stacks.math.columbia.edu/tag/0DN1)
* [Stacks Project, Tag 0DN2](https://stacks.math.columbia.edu/tag/0DN2)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

/-! ### Functoriality of cohomology over the base -/

section Functoriality

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- The map `Hⁱ(X, F) ⟶ Hⁱ(X, G)` of `A`-modules induced by a morphism `F ⟶ G` of
`𝒪_X`-modules: functoriality of `AlgebraicGeometry.Space.cohomologyOverBase` in the module.

Like `AlgebraicGeometry.Space.cohomologyOverBaseIso` this is a composite of the functoriality of
the derived global sections of the small étale ringed site and of restriction of scalars along
`AlgebraicGeometry.Space.baseRingHom`. -/
def cohomologyOverBaseMap {M N : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX}
    (φ : M ⟶ N) (i : ℕ) :
    cohomologyOverBase.{u, w} A B hA X hX M i ⟶ cohomologyOverBase.{u, w} A B hA X hX N i :=
  (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).map
    ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) i).map φ)

/-- **`AlgebraicGeometry.Space.cohomologyOverBaseMap` takes the identity to the identity**, since
both functors it is composed from do. -/
theorem cohomologyOverBaseMap_id (M : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX)
    (i : ℕ) :
    cohomologyOverBaseMap.{u, w} A B hA X hX (𝟙 M) i =
      𝟙 (cohomologyOverBase.{u, w} A B hA X hX M i) :=
  (congrArg (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).map
    ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) i).map_id M)).trans
    ((ModuleCat.restrictScalars (baseRingHom A B hA X hX)).map_id _)

/-- **`AlgebraicGeometry.Space.cohomologyOverBaseMap` takes a composite to the composite**, since
both functors it is composed from do. -/
theorem cohomologyOverBaseMap_comp
    {M N P : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX} (φ : M ⟶ N) (ψ : N ⟶ P)
    (i : ℕ) :
    cohomologyOverBaseMap.{u, w} A B hA X hX (φ ≫ ψ) i =
      cohomologyOverBaseMap.{u, w} A B hA X hX φ i ≫
        cohomologyOverBaseMap.{u, w} A B hA X hX ψ i :=
  (congrArg (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).map
    ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) i).map_comp φ ψ)).trans
    ((ModuleCat.restrictScalars (baseRingHom A B hA X hX)).map_comp _ _)

end Functoriality

/-! ### The long exact sequence of cohomology over the base -/

section LongExactSequence

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- Restriction of scalars along `AlgebraicGeometry.Space.baseRingHom` changes neither the
underlying types nor the underlying functions, so it carries exactness of a short complex of
modules over the global functions to exactness of the pair of `A`-linear maps. -/
private lemma function_exact_restrictScalars
    {T : ShortComplex (ModuleCat.{max (u + 1) w} (Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))))}
    (h : T.Exact) :
    Function.Exact ((ModuleCat.restrictScalars (baseRingHom A B hA X hX)).map T.f)
      ((ModuleCat.restrictScalars (baseRingHom A B hA X hX)).map T.g) :=
  fun x => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h x

/-- **The long exact sequence of cohomology of `𝒪_X`-modules over the base ring.** For a short
exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of modules on an algebraic space `X` over `Spec A` there
are connecting maps `Hⁱ(X, F₃) ⟶ Hⁱ⁺¹(X, F₁)` of `A`-modules for which
`0 ⟶ H⁰(X, F₁) ⟶ H⁰(X, F₂) ⟶ H⁰(X, F₃) ⟶ H¹(X, F₁) ⟶ H¹(X, F₂) ⟶ ⋯` is exact. There is no
hypothesis on the base ring, on a morphism to the base, or on the modules. -/
theorem exists_cohomologyOverBase_longExactSequence
    {S : ShortComplex (Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX)}
    (hS : S.ShortExact) :
    ∃ d : ∀ i : ℕ, cohomologyOverBase.{u, w} A B hA X hX S.X₃ i ⟶
        cohomologyOverBase.{u, w} A B hA X hX S.X₁ (i + 1),
      Function.Injective (cohomologyOverBaseMap.{u, w} A B hA X hX S.f 0) ∧
        (∀ i, Function.Exact (cohomologyOverBaseMap.{u, w} A B hA X hX S.f i)
          (cohomologyOverBaseMap.{u, w} A B hA X hX S.g i)) ∧
        (∀ i, Function.Exact (cohomologyOverBaseMap.{u, w} A B hA X hX S.g i) (d i)) ∧
        ∀ i, Function.Exact (d i) (cohomologyOverBaseMap.{u, w} A B hA X hX S.f (i + 1)) := by
  let E := Stacks.Cohomology.SiteModules.cohomologyDeltaFunctor.{u + 1, u, u, max (u + 1) w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
  refine ⟨fun i => (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).map (E.δ hS i),
    ?_, ?_, ?_, ?_⟩
  · exact fun _ _ hab => (ModuleCat.mono_iff_injective _).1 (E.mono_map_f hS) hab
  · exact fun i => function_exact_restrictScalars A B hA X hX (E.exact_map hS i)
  · exact fun i => function_exact_restrictScalars A B hA X hX (E.exact_δ₁ hS i)
  · exact fun i => function_exact_restrictScalars A B hA X hX (E.exact_δ₂ hS i)

end LongExactSequence

/-! ### Propagation of finiteness and vanishing across a short exact sequence -/

section Propagation

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)

/-- A cohomology module over a field that vanishes is finite-dimensional. This restates
`AlgebraicGeometry.finiteDimensional_of_isZero`, which is available only for `ModuleCat.{u} k`,
in the module universe in which the cohomology of an algebraic space lives. -/
private theorem finiteDimensional_of_isZero {M : ModuleCat.{max (u + 1) w} k} (h : IsZero M) :
    FiniteDimensional k M :=
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  have : Finite M := Finite.of_subsingleton
  inferInstance

/-- **Finite dimensionality of the middle cohomology of a short exact sequence.** If `Hⁱ(X, F₁)`
and `Hⁱ(X, F₃)` are finite-dimensional over `k`, so is `Hⁱ(X, F₂)`: the three sit in an exact
sequence by `AlgebraicGeometry.Space.exists_cohomologyOverBase_longExactSequence`. There is no
hypothesis on a morphism to the base or on the modules. -/
theorem finiteDimensional_cohomologyOverBase_of_shortExact
    {S : ShortComplex (Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX)} (hS : S.ShortExact)
    (i : ℕ) (h₁ : FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₁ i))
    (h₃ : FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₃ i)) :
    FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₂ i) := by
  obtain ⟨_, _, hfg, _, _⟩ := exists_cohomologyOverBase_longExactSequence.{u, w} k B hk X hX hS
  have := h₁
  have := h₃
  exact Module.finiteDimensional_of_exact (cohomologyOverBaseMap.{u, w} k B hk X hX S.f i).hom
    (cohomologyOverBaseMap.{u, w} k B hk X hX S.g i).hom (hfg i)

/-- **Vanishing of the middle cohomology of a short exact sequence.** If `Hⁱ(X, F₁)` and
`Hⁱ(X, F₃)` vanish then so does `Hⁱ(X, F₂)`: a class in the middle maps to zero, hence comes from
the left, which is zero. There is no hypothesis on a morphism to the base or on the modules. -/
theorem isZero_cohomologyOverBase_of_shortExact
    {S : ShortComplex (Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX)} (hS : S.ShortExact)
    (i : ℕ) (h₁ : IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₁ i))
    (h₃ : IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₃ i)) :
    IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₂ i) := by
  obtain ⟨_, _, hfg, _, _⟩ := exists_cohomologyOverBase_longExactSequence.{u, w} k B hk X hX hS
  have hs₁ := ModuleCat.subsingleton_of_isZero h₁
  have hs₃ := ModuleCat.subsingleton_of_isZero h₃
  have hz : ∀ z : cohomologyOverBase.{u, w} k B hk X hX S.X₂ i, z = 0 := by
    intro z
    obtain ⟨y, hy⟩ := (hfg i z).1 (Subsingleton.elim _ _)
    rw [← hy, Subsingleton.elim y 0, map_zero]
  exact ModuleCat.isZero_iff_subsingleton.2 ⟨fun x y => by rw [hz x, hz y]⟩

end Propagation

/-! ### The Euler characteristic and its additivity -/

section EulerCharacteristic

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)

/-- **Stacks 0DN1.** The Euler characteristic of a coherent module `F` on a proper algebraic
space `X` over a field `k`: the alternating sum `∑ᵢ (-1)ⁱ dim_k Hⁱ(X, F)` of the dimensions over
`k` of the cohomology modules of `F` on the small étale site of `X`. -/
@[stacks 0DN1]
def eulerCharacteristic (f : X ⟶ yoneda.obj (baseObject k B hk))
    (_hf : IsProper B (Spec (.of k)) hk f)
    (F : Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX)
    [IsCoherent B (Spec (.of k)) hk X hX F] : ℤ :=
  ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k (cohomologyOverBase.{u, w} k B hk X hX F i) : ℤ)

/-- The defining alternating-sum formula for the Euler characteristic. -/
theorem eulerCharacteristic_eq_finsum (f : X ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)
    (F : Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX)
    [IsCoherent B (Spec (.of k)) hk X hX F] :
    eulerCharacteristic.{u, w} k B hk X hX f hf F =
      ∑ᶠ i : ℕ,
        (-1 : ℤ) ^ i * (Module.finrank k (cohomologyOverBase.{u, w} k B hk X hX F i) : ℤ) :=
  rfl

/-- **The Euler characteristic depends on its module only up to isomorphism.**  Isomorphic
coherent `𝒪_X`-modules on a proper algebraic space over a field have the same Euler
characteristic.

The isomorphism induces one of the cohomology modules in every degree, by
`AlgebraicGeometry.Space.cohomologyOverBaseIso`, and isomorphic `k`-modules have the same
dimension, so the two alternating sums agree term by term. -/
theorem eulerCharacteristic_congr (f : X ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)
    {M N : Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX} (e : M ≅ N)
    [IsCoherent B (Spec (.of k)) hk X hX M] [IsCoherent B (Spec (.of k)) hk X hX N] :
    eulerCharacteristic.{u, w} k B hk X hX f hf M =
      eulerCharacteristic.{u, w} k B hk X hX f hf N := by
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  refine finsum_congr fun i => ?_
  rw [(cohomologyOverBaseIso.{u, w} k B hk X hX e i).toLinearEquiv.finrank_eq]

/-- **Additivity of the alternating sum of dimensions of cohomology along a short exact
sequence**: the two steps of the proof of Stacks 0DN2, namely the long exact sequence and
rank-nullity, with the finiteness of Stacks 08AS and the vanishing in large degrees carried as
hypotheses for all three modules. -/
theorem finsum_alternating_finrank_cohomologyOverBase_add_of_shortExact
    {S : ShortComplex (Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX)} (hS : S.ShortExact)
    (hfin₁ : ∀ i, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₁ i))
    (hfin₂ : ∀ i, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₂ i))
    (hfin₃ : ∀ i, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₃ i)) (N : ℕ)
    (hvan₁ : ∀ i, N ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₁ i))
    (hvan₂ : ∀ i, N ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₂ i))
    (hvan₃ : ∀ i, N ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₃ i)) :
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        (Module.finrank k (cohomologyOverBase.{u, w} k B hk X hX S.X₂ i) : ℤ)) =
      (∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
          (Module.finrank k (cohomologyOverBase.{u, w} k B hk X hX S.X₁ i) : ℤ)) +
        ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
          (Module.finrank k (cohomologyOverBase.{u, w} k B hk X hX S.X₃ i) : ℤ) := by
  obtain ⟨d, hinj, hfg, hgd, hdf⟩ :=
    exists_cohomologyOverBase_longExactSequence.{u, w} k B hk X hX hS
  have hzero {F : Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX} {i : ℕ}
      (h : IsZero (cohomologyOverBase.{u, w} k B hk X hX F i)) :
      Module.finrank k (cohomologyOverBase.{u, w} k B hk X hX F i) = 0 :=
    have := ModuleCat.subsingleton_of_isZero h
    Module.finrank_zero_of_subsingleton
  have := hfin₁
  have := hfin₂
  have := hfin₃
  exact Module.finsum_alternating_finrank_add_of_exact
    (fun i => (cohomologyOverBaseMap.{u, w} k B hk X hX S.f i).hom)
    (fun i => (cohomologyOverBaseMap.{u, w} k B hk X hX S.g i).hom) (fun i => (d i).hom)
    hfg hgd hdf hinj N (fun i hi => hzero (hvan₁ i hi)) (fun i hi => hzero (hvan₂ i hi))
    fun i hi => hzero (hvan₃ i hi)

/-- **Additivity of the alternating sum of dimensions of cohomology along a short exact sequence,
from the outer two terms.** The finiteness of Stacks 08AS and the vanishing in large degrees are
assumed for `F₁` and `F₃` only, the finiteness only in the degrees below the vanishing bound;
for `F₂` both follow from the long exact sequence. -/
theorem finsum_alternating_finrank_cohomologyOverBase_add_of_shortExact_of_outer
    {S : ShortComplex (Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX)} (hS : S.ShortExact)
    (N : ℕ)
    (hfin₁ : ∀ i < N, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₁ i))
    (hfin₃ : ∀ i < N, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₃ i))
    (hvan₁ : ∀ i, N ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₁ i))
    (hvan₃ : ∀ i, N ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₃ i)) :
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        (Module.finrank k (cohomologyOverBase.{u, w} k B hk X hX S.X₂ i) : ℤ)) =
      (∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
          (Module.finrank k (cohomologyOverBase.{u, w} k B hk X hX S.X₁ i) : ℤ)) +
        ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
          (Module.finrank k (cohomologyOverBase.{u, w} k B hk X hX S.X₃ i) : ℤ) := by
  have hall : ∀ F : Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX,
      (∀ i < N, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX F i)) →
      (∀ i, N ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X hX F i)) →
      ∀ i, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX F i) := fun F hfin hvan i =>
    if h : i < N then hfin i h else finiteDimensional_of_isZero.{u, w} k (hvan i (by omega))
  have hall₁ := hall _ hfin₁ hvan₁
  have hall₃ := hall _ hfin₃ hvan₃
  exact finsum_alternating_finrank_cohomologyOverBase_add_of_shortExact.{u, w} k B hk X hX hS
    hall₁
    (fun i => finiteDimensional_cohomologyOverBase_of_shortExact.{u, w} k B hk X hX hS i
      (hall₁ i) (hall₃ i))
    hall₃ N hvan₁
    (fun i hi => isZero_cohomologyOverBase_of_shortExact.{u, w} k B hk X hX hS i (hvan₁ i hi)
      (hvan₃ i hi))
    hvan₃

/-- **Stacks 0DN2 with its two finiteness inputs as hypotheses.** For a proper algebraic space
over a field and a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of coherent modules,
`χ(X, F₂) = χ(X, F₁) + χ(X, F₃)`, given that every `Hⁱ(X, Fⱼ)` is finite-dimensional over `k`
and vanishes beyond a common bound. Properness and coherence are hypotheses of
`AlgebraicGeometry.Space.eulerCharacteristic` and are used nowhere in the proof. -/
theorem eulerCharacteristic_add_of_shortExact_of_finiteDimensional_of_isZero
    (f : X ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    {S : ShortComplex (Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX)} (hS : S.ShortExact)
    [IsCoherent B (Spec (.of k)) hk X hX S.X₁] [IsCoherent B (Spec (.of k)) hk X hX S.X₂]
    [IsCoherent B (Spec (.of k)) hk X hX S.X₃]
    (hfin₁ : ∀ i, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₁ i))
    (hfin₂ : ∀ i, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₂ i))
    (hfin₃ : ∀ i, FiniteDimensional k (cohomologyOverBase.{u, w} k B hk X hX S.X₃ i)) (N : ℕ)
    (hvan₁ : ∀ i, N ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₁ i))
    (hvan₂ : ∀ i, N ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₂ i))
    (hvan₃ : ∀ i, N ≤ i → IsZero (cohomologyOverBase.{u, w} k B hk X hX S.X₃ i)) :
    eulerCharacteristic.{u, w} k B hk X hX f hf S.X₂ =
      eulerCharacteristic.{u, w} k B hk X hX f hf S.X₁ +
        eulerCharacteristic.{u, w} k B hk X hX f hf S.X₃ := by
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  exact finsum_alternating_finrank_cohomologyOverBase_add_of_shortExact.{u, w} k B hk X hX hS
    hfin₁ hfin₂ hfin₃ N hvan₁ hvan₂ hvan₃

/-- **Stacks 0DN2.** Let `k` be a field, `X` a proper algebraic space over `k` and
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` a short exact sequence of coherent `𝒪_X`-modules. Then
`χ(X, F₂) = χ(X, F₁) + χ(X, F₃)`.

`X` is quasi-compact and quasi-separated, being proper over `Spec k`, so by Stacks 072C there is
`N` beyond which the cohomology of every coherent module vanishes; below `N` the cohomology of
`F₁` and `F₃` is finite-dimensional by Stacks 08AS; and the long exact sequence with
rank-nullity is
`AlgebraicGeometry.Space.finsum_alternating_finrank_cohomologyOverBase_add_of_shortExact_of_outer`.
-/
@[stacks 0DN2]
theorem eulerCharacteristic_add_of_shortExact_of_outer
    (f : X ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    {S : ShortComplex (Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX)} (hS : S.ShortExact)
    [IsCoherent B (Spec (.of k)) hk X hX S.X₁] [IsCoherent B (Spec (.of k)) hk X hX S.X₂]
    [IsCoherent B (Spec (.of k)) hk X hX S.X₃] :
    eulerCharacteristic.{u, w} k B hk X hX f hf S.X₂ =
      eulerCharacteristic.{u, w} k B hk X hX f hf S.X₁ +
        eulerCharacteristic.{u, w} k B hk X hX f hf S.X₃ := by
  -- `X` is quasi-compact, being universally closed over the affine `Spec k`, and absolutely
  -- quasi-separated, being separated over the quasi-separated `Spec k`.
  have hqc : IsQuasiCompactSpace B (Spec (.of k)) hk X :=
    isQuasiCompactSpace_of_universallyClosed_of_isAffine B (Spec (.of k)) hk
      (baseObject k B hk) (inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))) hX
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) f hf.universallyClosed
  have hqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of k)) hk B.contains_terminal hX
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (Spec (.of k)) hk
        (yoneda.obj (baseObject k B hk)) B.contains_terminal
        ⟨baseObject k B hk, inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of k))),
          ⟨Functor.RepresentableBy.yoneda _⟩⟩)
      (isQuasiSeparated_of_isSeparated B (Spec (.of k)) hk hf.1)
  obtain ⟨N, hN⟩ := exists_forall_isZero_cohomologyOverBase_of_isCoherent_of_qcqs.{u, w} k B hk
    B.contains_terminal X hX hqc hqs
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  exact finsum_alternating_finrank_cohomologyOverBase_add_of_shortExact_of_outer.{u, w} k B hk X hX
    hS N
    (fun i _ => moduleFinite_cohomologyOverBase_of_isProper_of_isCoherent.{u, w} k B hk X hX f hf
      S.X₁ i)
    (fun i _ => moduleFinite_cohomologyOverBase_of_isProper_of_isCoherent.{u, w} k B hk X hX f hf
      S.X₃ i)
    (hN S.X₁ inferInstance) (hN S.X₃ inferInstance)

end EulerCharacteristic

end AlgebraicGeometry.Space

end
