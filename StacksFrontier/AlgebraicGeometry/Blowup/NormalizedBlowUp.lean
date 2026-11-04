module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.OpenImmersionCriterion

/-!
# The normalized blowup of a scheme at a closed point

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components, and let
`x` be a point of `X` whose singleton is closed. The *normalized blowup of `X` at `x`* is the
normalization of the blowup of `X` in the reduced closed subscheme supported at `x`, together
with the composite of the normalization morphism and the blowup morphism.

The construction needs the normalization of the blowup to exist, which is the finiteness
hypothesis of `AlgebraicGeometry.Scheme.normalization` for the blowup rather than for `X`. That
hypothesis is transported along the blowup morphism in
`Stacks.Blowup.finite_irreducibleComponents_blowUp`: the blowup morphism is injective on generic
points and sends them to generic points of the base, because the generic points of the blowup
avoid its exceptional divisor and the blowup is an isomorphism away from its centre.

## Main definitions

* `Stacks.Blowup.normalizedBlowUpScheme` is the normalized blowup of `X` at `x`, as a scheme.
* `Stacks.Blowup.normalizedBlowUp` is its structure morphism to `X`.

## Main results

* `Stacks.Blowup.finite_irreducibleComponents_blowUp`: quasi-compact opens of a blowup inherit
  finiteness of irreducible components from quasi-compact opens of the base.

## Implementation notes

The point is specified together with closedness of its singleton, and its reduced closed
subscheme is the vanishing ideal sheaf of that singleton. The finiteness result is stated for an
arbitrary blowup centre, so that it is available for subsequent point blowups without changing
its form. The normalized blowup morphism is the literal composite of the normalization and
blowup morphisms, and the scheme is an abbreviation, so the existing normalization API applies
to both.

## References

* [Stacks Project, Tag 0BBS](https://stacks.math.columbia.edu/tag/0BBS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

namespace Stacks.Blowup

open _root_.AlgebraicGeometry (genericPoints_preimage_of_isOpenImmersion)

/-! ### Generic points under an open immersion -/

/-- A point of a scheme is a generic point exactly when it has no proper generalization. -/
private theorem mem_genericPoints_iff_forall_specializes_eq {A : Scheme.{u}} (a : A) :
    a ∈ genericPoints A ↔ ∀ b : A, b ⤳ a → b = a := by
  refine ⟨fun ha b hba => ?_, fun h => ?_⟩
  · have hback : closure ({b} : Set A) ⊆ closure ({a} : Set A) :=
      (genericPoints.component ⟨a, ha⟩).2.2 isIrreducible_singleton.closure
        (specializes_iff_closure_subset.mp hba)
    exact (hba.antisymm (specializes_iff_closure_subset.mpr hback)).eq
  · let Z : irreducibleComponents A :=
      ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a⟩
    rw [← h (genericPoints.ofComponent Z)
      ((genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent)]
    exact (genericPoints.ofComponent Z).2

/-- An open immersion carries generic points to generic points. -/
private alias mem_genericPoints_of_isOpenImmersion :=
  AlgebraicGeometry.genericPoints_map_of_openImmersion

/-! ### The blowup morphism on generic points

The three results of this section are the part of Stacks tag 0BFM that the normalized blowup
consumes. They are deliberately stated as the two halves of a bijection rather than as the
bijection itself, and are `private`, so that they neither claim nor collide with that tag.
-/

/-- A section of an affine open vanishing at a point lies in the prime ideal of that point. -/
private theorem mem_primeIdealOf_of_notMem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) (f : Γ(X, U)) (h : (x : X) ∉ X.basicOpen f) :
    f ∈ (hU.primeIdealOf x).asIdeal := by
  by_contra hc
  have hmem : hU.primeIdealOf x ∈ PrimeSpectrum.basicOpen f :=
    (PrimeSpectrum.mem_basicOpen f _).2 hc
  rw [← hU.fromSpec_preimage_basicOpen] at hmem
  rw [← hU.fromSpec_primeIdealOf x] at h
  exact h hmem

/-- Every generic point of a blowup lies over the complement of the centre: it avoids the
exceptional divisor, which is an effective Cartier divisor by
`AlgebraicGeometry.notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor`. -/
private theorem mem_preimage_compl_support_of_mem_genericPoints {X : Scheme.{u}}
    (I : X.IdealSheafData) {y : blowUp I} (hy : y ∈ genericPoints (blowUp I)) :
    y ∈ blowUpToBase I ⁻¹ᵁ I.support.compl := by
  have hsupp : y ∉ (I.comap (blowUpToBase I)).support := fun h =>
    notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor (exceptionalIdeal I)
      inferInstance hy (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr h)
  rwa [Scheme.IdealSheafData.support_comap] at hsupp

/-- The blowup morphism sends generic points of the blowup to generic points of the base, and is
injective on them: the generic points of the blowup lie over the complement of the centre, where
the blowup morphism is an isomorphism.

This is a `private` stand-in for the part of Stacks tag 0BFM that
`Stacks.Blowup.normalizedBlowUpScheme` consumes; delete it when that tag lands. -/
private theorem mapsTo_injOn_genericPoints_blowUpToBase {X : Scheme.{u}} (I : X.IdealSheafData) :
    Set.MapsTo (blowUpToBase I) (genericPoints (blowUp I)) (genericPoints X) ∧
      Set.InjOn (blowUpToBase I) (genericPoints (blowUp I)) := by
  set W : X.Opens := I.support.compl
  set b : blowUp I ⟶ X := blowUpToBase I
  have hcomp (z : (b ⁻¹ᵁ W).toScheme) : (W.ι ((b ∣_ W) z) : X) = b z.1 :=
    congrArg (fun k : (b ⁻¹ᵁ W).toScheme ⟶ X => k z) (morphismRestrict_ι b W)
  refine ⟨fun y hy => ?_, fun y hy z hz hyz => ?_⟩
  · have hy' := mem_preimage_compl_support_of_mem_genericPoints I hy
    have hz : (⟨y, hy'⟩ : (b ⁻¹ᵁ W).toScheme) ∈ genericPoints (b ⁻¹ᵁ W).toScheme :=
      genericPoints_preimage_of_isOpenImmersion (b ⁻¹ᵁ W).ι hy
    have hgen : (W.ι ((b ∣_ W) ⟨y, hy'⟩) : X) ∈ genericPoints X :=
      mem_genericPoints_of_isOpenImmersion W.ι
        (mem_genericPoints_of_isOpenImmersion (b ∣_ W) hz)
    rwa [hcomp ⟨y, hy'⟩] at hgen
  · have hy' := mem_preimage_compl_support_of_mem_genericPoints I hy
    have hz' := mem_preimage_compl_support_of_mem_genericPoints I hz
    have hgz : (b ∣_ W) ⟨y, hy'⟩ = (b ∣_ W) ⟨z, hz'⟩ :=
      Subtype.ext ((hcomp ⟨y, hy'⟩).trans (hyz.trans (hcomp ⟨z, hz'⟩).symm))
    exact congrArg Subtype.val ((b ∣_ W).isOpenEmbedding.injective hgz)

/-! ### The normalized blowup -/

/-- Quasi-compact opens of a blowup inherit finiteness of irreducible components from
quasi-compact opens of the base. This is the hypothesis under which the blowup has a
normalization, and so is what makes the normalized blowup of Stacks tag 0BBS available. -/
theorem finite_irreducibleComponents_blowUp {X : Scheme.{u}} (I : X.IdealSheafData)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∀ U : (blowUp I).Opens, IsCompact (U : Set (blowUp I)) →
      (irreducibleComponents U).Finite := by
  classical
  obtain ⟨hmaps, hinj⟩ := mapsTo_injOn_genericPoints_blowUpToBase I
  set b : blowUp I ⟶ X := blowUpToBase I
  let V (i : X.affineCover.I₀) : X.Opens := (X.affineCover.f i).opensRange
  have hfiniteV (i : X.affineCover.I₀) : {η : genericPoints X | η.1 ∈ V i}.Finite := by
    have hlocal : (genericPoints (V i : Set X)).Finite :=
      genericPoints.finite (hX (V i) (isAffineOpen_opensRange (X.affineCover.f i)).isCompact)
    exact hlocal.of_injective (Scheme.genericPointsInOpenEquiv X (V i))
      (Scheme.genericPointsInOpenEquiv X (V i)).injective
  intro U hU
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i => b ⁻¹ᵁ V i)
    (fun i => (b ⁻¹ᵁ V i).isOpen) (by
      intro y _
      obtain ⟨i, hi⟩ := X.affineCover.exists_eq (b y)
      exact Set.mem_iUnion.mpr ⟨i, Scheme.Hom.mem_opensRange.mpr hi⟩)
  let S : Set (genericPoints X) :=
    ⋃ i ∈ (t : Set X.affineCover.I₀), {η : genericPoints X | η.1 ∈ V i}
  have hS : S.Finite := t.finite_toSet.biUnion fun i _ => hfiniteV i
  let g : {η : genericPoints (blowUp I) // η.1 ∈ U} → {ξ : genericPoints X // ξ ∈ S} :=
    fun η => ⟨⟨b η.1.1, hmaps η.1.2⟩, by
      obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.mp (ht η.2)
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hiy⟩⟩
  have hginj : Function.Injective g := fun η ξ heq =>
    Subtype.ext (Subtype.ext (hinj η.1.2 ξ.1.2
      (congrArg (fun z : {ξ : genericPoints X // ξ ∈ S} => z.1.1) heq)))
  have : Finite {ξ : genericPoints X // ξ ∈ S} := hS.to_subtype
  have : Finite {η : genericPoints (blowUp I) // η.1 ∈ U} := Finite.of_injective g hginj
  have : Finite (genericPoints (U : Set (blowUp I))) :=
    Finite.of_equiv _ (Scheme.genericPointsInOpenEquiv (blowUp I) U)
  have : QuasiSober (U : Set (blowUp I)) := U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  have : Finite (irreducibleComponents (U : Set (blowUp I))) :=
    Finite.of_equiv _ (genericPoints.equiv (α := (U : Set (blowUp I))))
  rw [Set.finite_def]
  exact ⟨Fintype.ofFinite (irreducibleComponents (U : Set (blowUp I)))⟩

/-- **Stacks Project, Tag 0BBS.** The normalized blowup of `X` at a closed point `x`: the
normalization of the blowup of `X` in the reduced closed subscheme supported at `x`. -/
@[stacks 0BBS "normalized blowup scheme"]
abbrev normalizedBlowUpScheme (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) : Scheme.{u} :=
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  Scheme.normalizationScheme (blowUp I) (finite_irreducibleComponents_blowUp I hX)

/-- **Stacks Project, Tag 0BBS.** The normalized blowup of `X` at a closed point `x`, as a
morphism to `X`: the normalization of the blowup followed by the blowup morphism. -/
@[stacks 0BBS "normalized blowup morphism"]
abbrev normalizedBlowUp (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) : normalizedBlowUpScheme X hX x hx ⟶ X :=
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  Scheme.normalization (blowUp I) (finite_irreducibleComponents_blowUp I hX) ≫ blowUpToBase I

end Stacks.Blowup

end
