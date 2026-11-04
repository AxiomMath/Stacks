module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.NowhereDense.Defs
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CartierPart
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization

/-!
# Covering a nowhere dense closed subscheme by integral effective Cartier divisors

Let `X` be a Noetherian scheme and `Z ⊆ X` a nowhere dense closed subscheme whose ambient local
rings are unique factorization domains — for instance, `X` regular.  Then `Z` is contained in the
union of finitely many integral effective Cartier divisors together with a closed subset all of
whose points have codimension at least two.

## Main results

* `AlgebraicGeometry.exists_integral_effectiveCartierDivisors_cover`: the support of `Z` lies in
  the union of a set of integral effective Cartier divisors and a closed subset all of whose
  points have codimension at least two.

## References

* [Stacks Project, Tag 0AGB](https://stacks.math.columbia.edu/tag/0AGB)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors TopologicalSpace

universe u

namespace AlgebraicGeometry

private noncomputable def componentSupport {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i]
    (C : irreducibleComponents Y) : IrreducibleCloseds X :=
  ⟨i.base '' (C : Set Y), C.property.1.image i.base i.continuous.continuousOn,
    i.isClosedEmbedding.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ C.property)⟩

private noncomputable def componentIdeal {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i]
    (C : irreducibleComponents Y) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨componentSupport i C, (componentSupport i C).isClosed⟩

private lemma componentIdeal_support {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (C : irreducibleComponents Y) :
    ((componentIdeal i C).support : Set X) = (componentSupport i C : Set X) := by
  simp [componentIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]

open Stacks.AlgebraicGeometry.IrreducibleDevissage in
private lemma componentIdeal_isIntegral {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i]
    (C : irreducibleComponents Y) : IsIntegral (componentIdeal i C).subscheme := by
  unfold componentIdeal
  exact isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
    (componentSupport i C).isIrreducible

private lemma componentIdeal_genericPoint_closure {X Y : Scheme.{u}}
    (i : Y ⟶ X) [IsClosedImmersion i] (C : irreducibleComponents Y)
    [IsIntegral (componentIdeal i C).subscheme] :
    closure ({(componentIdeal i C).subschemeι
      (_root_.genericPoint (componentIdeal i C).subscheme)} : Set X) =
        (componentSupport i C : Set X) := by
  let I := componentIdeal i C
  rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
    genericPoint_closure, Set.image_univ, I.range_subschemeι, componentIdeal_support]

private lemma codimension_antitone_of_le {X : Type u} [TopologicalSpace X]
    {A B : IrreducibleCloseds X} (h : A ≤ B) : codimension B ≤ codimension A := by
  rw [codimension_eq_coheight, codimension_eq_coheight]
  exact Order.coheight_le_iff.mpr fun p hp => Order.length_le_coheight (le_trans h hp)

/-- A nowhere dense closed subscheme of a Noetherian scheme with factorial local rings
along it, or of a regular scheme, is covered by integral effective Cartier divisors
up to a closed subset of codimension at least two. -/
@[stacks 0AGB "supply_divisors"]
theorem exists_integral_effectiveCartierDivisors_cover
    (X : Scheme.{u}) [IsNoetherian X] (Z : X.IdealSheafData)
    (hZ : IsNowhereDense (Z.support : Set X))
    (h : (∀ x : X, x ∈ Z.support →
        UniqueFactorizationMonoid (X.presheaf.stalk x)) ∨ IsRegular X) :
    ∃ (D : Set X.IdealSheafData) (Z' : Closeds X),
      (∀ I ∈ D, IsIntegral I.subscheme ∧
        IsEffectiveCartierDivisor I) ∧
      (∀ x : X, x ∈ (Z' : Set X) →
        (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) ∧
      (Z.support : Set X) ⊆ (Z' : Set X) ∪ ⋃ I ∈ D, (I.support : Set X) := by
  have hfactor : ∀ x : X, x ∈ Z.support →
      UniqueFactorizationMonoid (X.presheaf.stalk x) := by
    rcases h with hfactor | hregular
    · exact hfactor
    · have hregularStalk : IsLocallyNoetherian X ∧
          ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
        ((isRegular_tfae X).out 1 2 (by simp) (by simp)).mp hregular
      intro x hx
      let _ : IsRegularLocalRing (X.presheaf.stalk x) := hregularStalk.2 x
      exact IsRegularLocalRing.uniqueFactorizationMonoid _
  let Y := Z.subscheme
  let i : Y ⟶ X := Z.subschemeι
  have hiEmbedding : Topology.IsEmbedding i.base := IsPreimmersion.isEmbedding i
  let _ : NoetherianSpace Y := hiEmbedding.isInducing.noetherianSpace
  let K := irreducibleComponents Y
  let _ : Finite K := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let good : Set K := {C | codimension (componentSupport i C) = 1}
  let bad : Set K := {C | 2 ≤ codimension (componentSupport i C)}
  let D : Set X.IdealSheafData := (componentIdeal i) '' good
  have hZrange : Set.range i.base = (Z.support : Set X) := Z.range_subschemeι
  change interior (closure (Z.support : Set X)) = ∅ at hZ
  have hinterior : interior (Z.support : Set X) = ∅ := by
    simpa only [Z.support.isClosed.closure_eq] using hZ
  have hcomponentSubset (C : K) : (componentSupport i C : Set X) ⊆ Z.support := by
    rintro _ ⟨y, -, rfl⟩
    rw [← hZrange]
    exact ⟨y, rfl⟩
  have hcomponentCodim (C : K) : 1 ≤ codimension (componentSupport i C) := by
    let S := componentSupport i C
    obtain ⟨T, hT, hSTsubset⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible
        (S : Set X) S.isIrreducible
    let T' : IrreducibleCloseds X :=
      ⟨T, hT.1, isClosed_of_mem_irreducibleComponents T hT⟩
    have hST : S < T' := lt_of_le_of_ne hSTsubset (by
      intro h
      obtain ⟨U, hUopen, hUne, hUT⟩ :=
        NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent T hT
      have hU : U ⊆ (Z.support : Set X) := by
        intro x hx
        have hxS : x ∈ (S : Set X) := by
          rw [show (S : Set X) = (T' : Set X) from congrArg _ h]
          exact hUT hx
        exact hcomponentSubset C hxS
      exact hUne.ne_empty
        (Set.subset_empty_iff.mp ((interior_maximal hU hUopen).trans_eq hinterior)))
    let p : LTSeries (IrreducibleCloseds X) :=
      (RelSeries.singleton _ T').cons S hST
    refine (codimension_iff_exists_chain S 1).2 ⟨p, ?_, ?_⟩
    · exact RelSeries.head_cons _ _ _
    · simp [p, RelSeries.cons, RelSeries.singleton]
  have hsplit (C : K) : C ∈ good ∨ C ∈ bad :=
    (eq_or_ne _ 1).imp id (codimension_ge_two_of_ge_one_ne_one _ (hcomponentCodim C))
  let Z' : Closeds X :=
    ⟨⋃₀ ((fun C : K => (componentSupport i C : Set X)) '' bad),
      ((Set.toFinite bad).image fun C => (componentSupport i C : Set X)).isClosed_sUnion
        (by
          rintro _ ⟨C, hC, rfl⟩
          exact (componentSupport i C).isClosed)⟩
  refine ⟨D, Z', ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨C, hC, rfl⟩ := hI
    let _ : IsIntegral (componentIdeal i C).subscheme := componentIdeal_isIntegral i C
    refine ⟨inferInstance, ?_⟩
    apply isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid
    · have hclosure : IrreducibleCloseds.closureSingleton
          ((componentIdeal i C).subschemeι
            (_root_.genericPoint (componentIdeal i C).subscheme)) =
            componentSupport i C :=
        IrreducibleCloseds.ext (componentIdeal_genericPoint_closure i C)
      rw [hclosure]
      exact hC
    · exact fun x hx ↦ hfactor x (hcomponentSubset C (by rwa [← componentIdeal_support]))
  · intro x hx
    obtain ⟨S, ⟨C, hC, rfl⟩, hxS⟩ := Set.mem_sUnion.mp hx
    have hle : closure ({x} : Set X) ≤ componentSupport i C :=
      closure_minimal (Set.singleton_subset_iff.mpr hxS)
        (componentSupport i C).isClosed
    exact le_trans hC (codimension_antitone_of_le hle)
  · intro x hx
    obtain ⟨y, hy⟩ : x ∈ Set.range i.base := by rw [hZrange]; exact hx
    have hyUnion : y ∈ ⋃₀ (irreducibleComponents Y) := by
      rw [sUnion_irreducibleComponents]
      exact Set.mem_univ y
    obtain ⟨C, hC, hyC⟩ := Set.mem_sUnion.mp hyUnion
    let C' : K := ⟨C, hC⟩
    have hxC : x ∈ componentSupport i C' := ⟨y, hyC, hy⟩
    rcases hsplit C' with hgood | hbad
    · right
      simp only [Set.mem_iUnion]
      exact ⟨componentIdeal i C', ⟨C', hgood, rfl⟩, by rwa [componentIdeal_support]⟩
    · exact Or.inl (Set.mem_sUnion.mpr ⟨componentSupport i C', ⟨C', hbad, rfl⟩, hxC⟩)

end AlgebraicGeometry

end
