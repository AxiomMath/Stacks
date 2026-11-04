module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.DisjointDivisors
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDivisorPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrimeDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ClosedSections

/-!
# The irreducible components of the fibres of a family over the projective line

Let `X` be a scheme locally of finite type over a field and `W ⊆ X × ℙ¹` an integral closed
subscheme of dimension `r + 1`, contained in neither of the two distinguished sections. Then every
irreducible component of the support of the zero fibre `W₀ ⊆ X`, and of the infinity fibre
`W_∞ ⊆ X`, has dimension exactly `r`.

The fibre `W₀` is identified, as a topological space, with the zero divisor of `W`, an effective
Cartier divisor on the integral scheme `W` (Tag 02S4 part (1)); every irreducible component of an
effective Cartier divisor drops the dimension by exactly one (Tag 02RK).

## Main results

* `Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_component_zeroFiber`,
  `Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_component_infinityFiber`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

/-- An irreducible component of a space is carried by a homeomorphism to an irreducible
component. -/
theorem image_mem_irreducibleComponents_of_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) {c : Set A} (hc : c ∈ irreducibleComponents A) :
    e '' c ∈ irreducibleComponents B :=
  image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous e.isOpenMap
    (fun y => by
      have : (e ⁻¹' {y} : Set A) = {e.symm y} := by
        ext x; simp [Homeomorph.eq_symm_apply]
      rw [this]
      exact isPreirreducible_singleton)
    e.surjective hc

/-- **The components of a closed subscheme identified topologically with a subset.** Let
`g : Q ⟶ Y` and `σ : X ⟶ Y` be closed immersions and `S ⊆ X` a subset with `range g = σ '' S`.
Every irreducible component `c` of `S` has the dimension of some irreducible component of `Q`. -/
theorem exists_mem_irreducibleComponents_topologicalKrullDim_eq {Q X Y : Scheme.{u}}
    (g : Q ⟶ Y) [IsClosedImmersion g] (σ : X ⟶ Y) [IsClosedImmersion σ] (S : Set X)
    (hS : Set.range g.base = σ.base '' S) {c : Set ↥S} (hc : c ∈ irreducibleComponents ↥S) :
    ∃ c' ∈ irreducibleComponents Q,
      topologicalKrullDim ↥c' = topologicalKrullDim ↥(Subtype.val '' c) := by
  let eQ : Q ≃ₜ ↥(Set.range g.base) := g.isClosedEmbedding.isEmbedding.toHomeomorph
  let eS : ↥S ≃ₜ ↥(σ.base '' S) :=
    (σ.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal).toHomeomorph.trans
      (Homeomorph.setCongr (by rw [Set.range_comp, Subtype.range_coe]))
  let e : ↥S ≃ₜ Q := (eS.trans (Homeomorph.setCongr hS.symm)).trans eQ.symm
  refine ⟨e '' c, image_mem_irreducibleComponents_of_homeomorph e hc, ?_⟩
  have h1 : topologicalKrullDim ↥(e '' c) = topologicalKrullDim ↥c :=
    (IsHomeomorph.topologicalKrullDim_eq _ (e.image c).isHomeomorph).symm
  have h2 : topologicalKrullDim ↥(Subtype.val '' c) = topologicalKrullDim ↥c :=
    topologicalKrullDim_image_eq_of_isEmbedding Topology.IsEmbedding.subtypeVal c
  rw [h1, h2]

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType p] (W : (projectiveLineProduct p).IdealSheafData)

/-- **Every irreducible component of an effective Cartier divisor of an integral member of the
family has dimension one less than the member.** -/
theorem topologicalKrullDim_component_of_isEffectiveCartierDivisor [IsIntegral W.subscheme]
    {r : ℤ} (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p W) ξ.1 = r + 1)
    (D : W.subscheme.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    {c : Set D.subscheme} (hc : c ∈ irreducibleComponents D.subscheme) :
    topologicalKrullDim ↥c = (r.toNat : WithBot ℕ∞) := by
  have hdelta := deltaDimension_irreducibleComponent_isEffectiveCartierDivisor
    (fieldChowSituation k) (familyBase p W) D hD ⟨c, hc⟩
  rw [schemeDeltaDimension_familyBase (fieldChowSituation k) p W hDim,
    coe_add_neg_one] at hdelta
  have hdelta' : deltaDimension (fieldChowSituation k) (D.subschemeι ≫ familyBase p W)
      ⟨c, hc.1, isClosed_of_mem_irreducibleComponents c hc⟩ = r :=
    WithBotTop.coe_injective hdelta
  rw [deltaDimension] at hdelta'
  have hcl := topologicalKrullDim_closure_eq_toNat_relativeDimension k
    (D.subschemeι ≫ familyBase p W) hc.1.genericPoint
  rw [hdelta', (hc.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents c hc)).def] at hcl
  exact hcl

/-- Components of a set `S ⊆ X` whose image under a section `σ` is the support of an effective
Cartier divisor `D` of `W` have dimension `r`. -/
private theorem topologicalKrullDim_component_of_image_support_eq [IsIntegral W.subscheme]
    {r : ℤ} (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p W) ξ.1 = r + 1)
    (D : W.subscheme.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (σ : X ⟶ projectiveLineProduct p) [IsClosedImmersion σ] (S : Set X)
    (hS : W.subschemeι '' (D.support : Set W.subscheme) = σ '' S)
    {c : Set ↥S} (hc : c ∈ irreducibleComponents ↥S) :
    topologicalKrullDim ↥(Subtype.val '' c) = (r.toNat : WithBot ℕ∞) := by
  have hS' : Set.range (D.subschemeι ≫ W.subschemeι).base = σ.base '' S := by
    have h := range_comp_scheme D.subschemeι W.subschemeι
    rw [Scheme.IdealSheafData.range_subschemeι] at h
    exact h.trans hS
  obtain ⟨c', hc', hdim⟩ := exists_mem_irreducibleComponents_topologicalKrullDim_eq
    (D.subschemeι ≫ W.subschemeι) σ S hS' hc
  rw [← hdim]
  exact topologicalKrullDim_component_of_isEffectiveCartierDivisor k p W hDim D hD hc'

/-- **Every irreducible component of the zero fibre has dimension `r`.** For `W ⊆ X × ℙ¹`
integral of relative dimension `r + 1`, not contained in the zero section. -/
theorem topologicalKrullDim_component_zeroFiber [IsIntegral W.subscheme] {r : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p W) ξ.1 = r + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection p))
    {c : Set ↥((zeroFiber p W).support : Set X)}
    (hc : c ∈ irreducibleComponents ↥((zeroFiber p W).support : Set X)) :
    topologicalKrullDim ↥(Subtype.val '' c) = (r.toNat : WithBot ℕ∞) :=
  topologicalKrullDim_component_of_image_support_eq k p W hDim (zeroDivisor p W)
    (zeroDivisor_isEffectiveCartierDivisor p W h₀) (zeroSection p) _
    (image_support_zeroDivisor_eq_image_support_zeroFiber p W) hc

/-- **Every irreducible component of the infinity fibre has dimension `r`.** -/
theorem topologicalKrullDim_component_infinityFiber [IsIntegral W.subscheme] {r : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p W) ξ.1 = r + 1)
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p))
    {c : Set ↥((infinityFiber p W).support : Set X)}
    (hc : c ∈ irreducibleComponents ↥((infinityFiber p W).support : Set X)) :
    topologicalKrullDim ↥(Subtype.val '' c) = (r.toNat : WithBot ℕ∞) :=
  topologicalKrullDim_component_of_image_support_eq k p W hDim (infinityDivisor p W)
    (infinityDivisor_isEffectiveCartierDivisor p W hInf) (infinitySection p) _
    (image_support_infinityDivisor_eq_image_support_infinityFiber p W) hc

end Stacks.Intersection.RationalEquivalenceProduct

end
