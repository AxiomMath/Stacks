module

public import StacksFrontier.AlgebraicGeometry.AffineMorphismEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerCharacteristicComparison
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsLength
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryStepBranch
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ZeroDimensionalTestModules
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
public import StacksFrontier.Topology.Dimension.Krull

/-!
# The Euler characteristic across one elementary step

Let `f : X' ⟶ X` be a finite morphism of schemes over a field `k`, with `X` proper over `k`,
whose structure-sheaf map `𝒪_X ⟶ f_*𝒪_{X'}` is a monomorphism and which is an isomorphism over
the complement of a single point `x`. This is the shape of one step of the factorization of
[Stacks, Tag 0C1L]: the glueing of two rational points and the squishing of a tangent vector are
both isomorphisms away from one rational point of `X`.

This file computes the effect of such a step on the Euler characteristic of the structure sheaf,
which is the bookkeeping the induction of [Stacks, Tag 0C20] runs alongside the `ℓ`-torsion of
the Picard group:

`χ(X', 𝒪_{X'}) = χ(X, 𝒪_X) + dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X)`.

The three inputs are all results of the library. The cokernel `Q = f_*𝒪_{X'}/𝒪_X` sits in a short
exact sequence of `X.Modules` whose other two terms are `𝒪_X` and `f_*𝒪_{X'}`, so [Stacks, Tag 08AA]
gives `χ(f_*𝒪_{X'}) = χ(𝒪_X) + χ(Q)`; [Stacks, Tag 089W] identifies `χ(f_*𝒪_{X'})` with
`χ(𝒪_{X'})`, a finite morphism being affine; and `Q` is supported inside `{x}`, so clauses (3)
and (4) of [Stacks, Tag 0AYT] collapse `χ(Q)` to `dim_k H⁰(Q)`.

What is *not* proved here is the evaluation `dim_k H⁰(X, Q) = 1`. The source reads it off the
identification of `Q` with the skyscraper sheaf `k_x`, which for a glueing is the content of the
last two clauses of `AlgebraicGeometry.IsGlueingTwoPoints` and for a squishing the content of
the short exact sequence inside `AlgebraicGeometry.IsSquishingTangentVector`. Both of those
identifications live in sheaves of abelian groups, not in `X.Modules`, and neither is available
`k`-linearly, which is what a statement about `Module.finrank k` needs; clause (2) of
[Stacks, Tag 0AYT] is likewise only an `AddEquiv`. So the dimension is carried as the honest
quantity `dim_k H⁰(X, Q)` rather than replaced by `1`.

## Main results

* `Stacks.GlueSquishFactor.shortExact_structureUnitHom` — the short exact sequence
  `0 ⟶ 𝒪_X ⟶ f_*𝒪_{X'} ⟶ Q ⟶ 0` of `X.Modules`.
* `Stacks.GlueSquishFactor.topologicalKrullDim_supp_cokernel_structureUnitHom_le_zero` — `Q` has
  zero-dimensional support, being supported inside the one point off which `f` is an
  isomorphism.
* `Stacks.GlueSquishFactor.eulerCharacteristic_unit_eq_add_finrank` — the Euler characteristic
  across the step.
* `Stacks.GlueSquishFactor.finrank_globalSections_sub_genus_eq` — the same in the `h⁰`–`h¹` form
  the induction tracks, on a scheme of dimension at most one.
* `Stacks.GlueSquishFactor.genus_eq_add_finrank_of_finrank_globalSections_eq` — the genus falls
  by `dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X)` across a step on which `h⁰` does not change.

## References

* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.GlueSquishFactor

/-! ### The cokernel of the structure-sheaf map -/

/-- **`f_*𝒪_{X'}/𝒪_X` is supported in zero dimensions** when `f` is an isomorphism over the
complement of a single point: its support is contained in that point, and a one-point space has
Krull dimension `0`. -/
theorem topologicalKrullDim_supp_cokernel_structureUnitHom_le_zero {X' X : Scheme.{u}}
    (f : X' ⟶ X) {x : X} {U : X.Opens} (hU : (U : Set X) = {x}ᶜ) [IsIso (f ∣_ U)] :
    topologicalKrullDim (SheafOfModules.supp (cokernel (structureUnitHom f))) ≤ 0 := by
  have hsub : SheafOfModules.supp (cokernel (structureUnitHom f)) ⊆ ({x} : Set X) := by
    have h := supp_subset_compl_cokernel_structureUnitHom f U
    rwa [hU, compl_compl] at h
  refine (topologicalKrullDim_le_of_subset hsub).trans ?_
  have : Subsingleton ({x} : Set X) := ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
  have : Nonempty ({x} : Set X) := ⟨⟨x, rfl⟩⟩
  exact le_of_eq topologicalKrullDim_eq_zero_of_nonempty_subsingleton

/-- **The short exact sequence `0 ⟶ 𝒪_X ⟶ f_*𝒪_{X'} ⟶ f_*𝒪_{X'}/𝒪_X ⟶ 0` of `X.Modules`**,
for a morphism whose structure-sheaf map is a monomorphism. This is the source's
`𝒪_X ⊂ f_*𝒪_{X'}` together with its quotient, in the category in which [Stacks, Tag 08AA]
reads additivity of the Euler characteristic. -/
theorem shortExact_structureUnitHom {X' X : Scheme.{u}} (f : X' ⟶ X)
    (hmono : Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).hom) :
    (ShortComplex.mk (structureUnitHom f) (cokernel.π (structureUnitHom f))
      (cokernel.condition _)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := mono_structureUnitHom f hmono
  epi_g := inferInstance

/-! ### The Euler characteristic across the step -/

/-- **The Euler characteristic of the structure sheaf across one elementary step of
[Stacks, Tag 0C1L].** For a finite `f : X' ⟶ X` with `𝒪_X ⊂ f_*𝒪_{X'}` which is an isomorphism
over `{x}ᶜ`, with `X` proper over `k`,

`χ(X', 𝒪_{X'}) = χ(X, 𝒪_X) + dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X)`.

Additivity along the short exact sequence of
`Stacks.GlueSquishFactor.shortExact_structureUnitHom` is [Stacks, Tag 08AA]; the left-hand side
is `χ(X, f_*𝒪_{X'})` because a finite morphism is affine ([Stacks, Tag 089W]); and the cokernel
term collapses to its `H⁰` because its support is zero-dimensional (clauses (3) and (4) of
[Stacks, Tag 0AYT]).

Properness of `X'` over `k` is not a hypothesis: it is the properness of `X` composed with the
finiteness of `f`, which is how `Stacks.GlueSquishFactor.IsElementaryChain.isProper_source`
reads it along a chain. -/
theorem eulerCharacteristic_unit_eq_add_finrank (k : Type u) [Field k] {X' X : Scheme.{u}}
    (f : X' ⟶ X) [IsFinite f] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hmono : Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).hom)
    {x : X} {U : X.Opens} (hU : (U : Set X) = {x}ᶜ) [IsIso (f ∣_ U)] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    letI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
    letI : (unitModule X).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
    letI : (unitModule X').IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
    letI : (cokernel (structureUnitHom f)).IsCoherent :=
      AlgebraicGeometry.IrreducibleDevissage.isCoherent_cokernel' _
        Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
        (pushforward_obj_unitModule f ▸
          Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
            f (unitModule X'))
    eulerCharacteristic k (f ≫ p) (unitModule X') =
      eulerCharacteristic k p (unitModule X) +
        (Module.finrank k (cohomologyOverField k p (cokernel (structureUnitHom f)) 0) : ℤ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  have h1 : (unitModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have h1' : (unitModule X').IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have h2' : ((Scheme.Modules.pushforward f).obj (unitModule X')).IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
      f (unitModule X')
  have h2 : ((Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).underlyingModule
      : X.Modules).IsCoherent := h2'
  have h3 : (cokernel (structureUnitHom f)).IsCoherent :=
    AlgebraicGeometry.IrreducibleDevissage.isCoherent_cokernel' _ h1 h2
  have hadd := eulerCharacteristic_add_of_shortExact k p (shortExact_structureUnitHom f hmono)
  have hpush := eulerCharacteristic_pushforward_of_isAffineHom k f p (unitModule X') h1' h2'
  have hQ := eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero k p
    (cokernel (structureUnitHom f))
    (topologicalKrullDim_supp_cokernel_structureUnitHom_le_zero f hU)
  have key : eulerCharacteristic k p ((Scheme.Modules.pushforward f).obj (unitModule X')) =
      eulerCharacteristic k p (unitModule X) +
        eulerCharacteristic k p (cokernel (structureUnitHom f)) := hadd
  rw [← hpush, key, hQ]

/-! ### The genus across the step -/

/-- **The `h⁰`–`h¹` form of the bookkeeping across one elementary step.** On a scheme of
dimension at most one the Euler characteristic of the structure sheaf is
`h⁰ - h¹ = dim_k Γ(-, 𝒪) - genus`, so
`Stacks.GlueSquishFactor.eulerCharacteristic_unit_eq_add_finrank` reads

`h⁰(X') - h¹(X') = h⁰(X) - h¹(X) + dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X)`.

This is the comparison of `dim_k H¹(X_i, 𝒪_{X_i})` across a step that the induction of
[Stacks, Tag 0C20] runs alongside the `ℓ`-torsion of the Picard group. -/
theorem finrank_globalSections_sub_genus_eq (k : Type u) [Field k] {X' X : Scheme.{u}}
    (f : X' ⟶ X) [IsFinite f] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hmono : Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).hom)
    {x : X} {U : X.Opens} (hU : (U : Set X) = {x}ᶜ) [IsIso (f ∣_ U)]
    (hdim : topologicalKrullDim X ≤ 1) (hdim' : topologicalKrullDim X' ≤ 1) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    letI : Algebra k Γ(X', ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ p).appTop).hom.toAlgebra
    (Module.finrank k Γ(X', ⊤) : ℤ) - (genus (f ≫ p) : ℤ) =
      (Module.finrank k Γ(X, ⊤) : ℤ) - (genus p : ℤ) +
        (Module.finrank k (cohomologyOverField k p (cokernel (structureUnitHom f)) 0) : ℤ) := by
  have hX := eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus k p hdim
  have hX' := eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus k (f ≫ p) hdim'
  have hmain := eulerCharacteristic_unit_eq_add_finrank k f p hmono hU
  rw [← hX, ← hX']
  exact hmain

/-- **The genus drops by `dim_k H⁰(f_*𝒪_{X'}/𝒪_X)` across one elementary step on which `h⁰`
does not change.** Rearranging
`Stacks.GlueSquishFactor.finrank_globalSections_sub_genus_eq`: the two `h⁰` terms cancel, so

`genus(X) = genus(X') + dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X)`,

that is, the genus falls on passing up the chain of [Stacks, Tag 0C1L] towards the
normalization. The hypothesis is the equality of global sections, which for a glueing of two
points on the same connected component of a proper `X'` holds because any global function takes
the same value at the two glued points. -/
theorem genus_eq_add_finrank_of_finrank_globalSections_eq (k : Type u) [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hmono : Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).hom)
    {x : X} {U : X.Opens} (hU : (U : Set X) = {x}ᶜ) [IsIso (f ∣_ U)]
    (hdim : topologicalKrullDim X ≤ 1) (hdim' : topologicalKrullDim X' ≤ 1) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    letI : Algebra k Γ(X', ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ p).appTop).hom.toAlgebra
    Module.finrank k Γ(X', ⊤) = Module.finrank k Γ(X, ⊤) →
      (genus p : ℤ) = (genus (f ≫ p) : ℤ) +
        (Module.finrank k (cohomologyOverField k p (cokernel (structureUnitHom f)) 0) : ℤ) := by
  intro hsec
  have h := finrank_globalSections_sub_genus_eq k f p hmono hU hdim hdim'
  rw [hsec] at h
  linarith

end Stacks.GlueSquishFactor

end
