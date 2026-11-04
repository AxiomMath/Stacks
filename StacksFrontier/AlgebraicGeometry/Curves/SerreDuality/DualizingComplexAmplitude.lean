module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.Curves.SerreDuality.PushforwardAmplitude
public import StacksFrontier.AlgebraicGeometry.Duality.SingleQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow

/-!
# The relative dualizing complex of a curve over a field lies in degrees `≥ -1`

Let `k` be a field and let `f : X ⟶ Spec(k)` be proper with `X` of topological Krull dimension at
most one. The relative dualizing complex `ω_X^• = f^×(𝒪_{Spec(k)})` of [Stacks, Tag 0AWI], the
value of the twisted inverse image of [Stacks, Tag 0A9E] on the structure sheaf of the base, has
no cohomology below degree `-1`. This is the first clause of [Stacks, Tag 0BS2] for the
constructed complex.

The argument is the lowest-cohomology one, not the sharp cohomological-dimension bound. The
complex is bounded below by [Stacks, Tag 0A9I], so it is `IsGE c` for some `c`. Suppose `c ≤ -2`
and let `G = H^c(ω_X^•)`, which is quasi-coherent because `ω_X^•` lies in `D_QCoh(𝒪_X)`. Since
`ω_X^•` is `IsGE c`, the object `G[c]` corepresents `H^c` on it
(`DerivedCategory.bijective_homologyFromSingle_of_isGE`, which needs no projectivity), so there is
a map `u : G[c] ⟶ ω_X^•` inducing the identity on `H^c`. The defining adjunction
`Hom_X(G[c], ω_X^•) ≃ Hom_{Spec(k)}(Rf_*(G[c]), 𝒪)` carries `u` into a Hom-group whose source
lies in degrees `≤ c + 1 ≤ -1` — that is
`Stacks.Duality.isLE_derivedPushforward_singleFunctor_obj` — and whose target lies in degrees
`≥ 0`, so that group vanishes by the orthogonality of the canonical t-structure. Hence `u = 0`,
so the identity of `G` is zero and `H^c(ω_X^•) = 0`, which upgrades `IsGE c` to `IsGE (c + 1)`.
Iterating raises the bound to `-1`.

## Main results

* `Stacks.Duality.isGE_neg_one_relativeDualizingComplex_derivedStructureSheaf` — the relative
  dualizing complex of the structure sheaf lies in degrees `≥ -1`.

## Implementation notes

The model of the derived categories is the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model at which
[Stacks, Tag 0A9E] holds: the adjointness instance is
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs` and is
found by instance search from `CompactSpace` and `QuasiSeparatedSpace` on the two schemes. Those
two hypotheses are instance arguments here rather than consequences of properness because
instance search cannot see the morphism `f`; a consumer holding `[IsProper f]` discharges them
with `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace` and
`AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated`.

`Stacks.Duality.isLE_derivedPushforward_singleFunctor_obj` is used at the same locally small
model, which is why it is stated there at a free `[HasDerivedCategory.{w}]` binder.

The quasi-coherence input `hpush` ([Stacks, Tag 08D5] part (1)) is a `Prop`-valued hypothesis, so
the bound of [Stacks, Tag 0A9I] — which is stated for
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` — applies to any other proof
of it without transport.

Morphisms of `D_QCoh(𝒪_X)` are a one-field structure over the morphisms of `D(𝒪_X)`
(`CategoryTheory.InducedCategory.Hom`), so the t-structure orthogonality is applied to the
underlying morphism and `CategoryTheory.ObjectProperty.hom_ext` puts the conclusion back in the
subcategory.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Duality

/-- The structure sheaf in degree zero has no cohomology in negative degrees. This is the
`Mathlib` instance for a single complex, read through the packaging of
`Stacks.Duality.DerivedPushforward.derivedStructureSheaf`. -/
theorem isGE_zero_derivedStructureSheaf (Z : Scheme.{u}) :
    (DerivedPushforward.derivedStructureSheaf Z).obj.IsGE 0 := by
  have h : ∀ M : Z.Modules, ((DerivedCategory.singleFunctor Z.Modules 0).obj M).IsGE 0 :=
    fun M => inferInstance
  exact h _

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [CompactSpace X] [QuasiSeparatedSpace X]
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of k)).Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

include f hpush in
omit [IsProper f] in
/-- **A map into the relative dualizing complex out of an object whose derived direct image lies
in degrees `≤ -1` vanishes.** The duality isomorphism of [Stacks, Tag 0AWP] turns it into a map
from `Rf_*K`, which lies in degrees `≤ -1`, to the structure sheaf of the base, which lies in
degrees `≥ 0`; the canonical t-structure has no such nonzero map. -/
private theorem hom_to_relativeDualizingComplex_eq_zero_of_isLE
    (K : quasiCoherentDerivedCategory X)
    (hK : ((derivedPushforward f).obj K.obj).IsLE (-1))
    (u : K.obj ⟶ (relativeDualizingComplex f hpush
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj) : u = 0 := by
  have := isGE_zero_derivedStructureSheaf (Spec (CommRingCat.of k))
  have hzero : ∀ g : (quasiCoherentDerivedPushforward f hpush).obj K ⟶
      DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)), g = 0 := fun g => by
    refine ObjectProperty.hom_ext _ ?_
    have : ((quasiCoherentDerivedPushforward f hpush).obj K).obj.IsLE (-1) := hK
    have hg : g.hom = 0 := DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g.hom (-1) 0
      (by omega) inferInstance inferInstance
    rw [hg]
    rfl
  have hu0 : (ObjectProperty.homMk u : K ⟶ relativeDualizingComplex f hpush
      (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))) = 0 :=
    (relativeDualizingComplexHomEquiv f hpush _ K).injective ((hzero _).trans (hzero _).symm)
  exact congrArg (fun g : K ⟶ relativeDualizingComplex f hpush
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) => g.hom) hu0

include f hpush in
/-- **The lowest-cohomology step.** If the relative dualizing complex of the structure sheaf lies
in degrees `≥ c` with `c ≤ -2`, then its cohomology sheaf in degree `c` vanishes, so it lies in
degrees `≥ c + 1`. -/
private theorem isGE_add_one_relativeDualizingComplex
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (c : ℤ) (hc : c ≤ -2)
    (h : (relativeDualizingComplex f hpush
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj.IsGE c) :
    (relativeDualizingComplex f hpush
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj.IsGE (c + 1) := by
  have := h
  set ω := relativeDualizingComplex f hpush
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) with hωdef
  set G := (DerivedCategory.homologyFunctor X.Modules c).obj ω.obj with hGdef
  have hGqc : G.IsQuasicoherent := ω.property c
  obtain ⟨u, hu⟩ := (DerivedCategory.bijective_homologyFromSingle_of_isGE G ω.obj c).2 (𝟙 G)
  have hG0 : IsZero G := by
    rw [IsZero.iff_id_eq_zero]
    have hle : ((derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules c).obj G)).IsLE (-1) := by
      have := isLE_derivedPushforward_singleFunctor_obj k f G hdim c
      exact DerivedCategory.TStructure.t.isLE_of_le _ (c + 1) (-1) (by omega)
    have hu0 : u = 0 := hom_to_relativeDualizingComplex_eq_zero_of_isLE f hpush
      (singleQuasiCoherent G hGqc c) hle u
    rw [← hu, hu0]
    exact map_zero _
  rw [DerivedCategory.isGE_iff]
  intro i hi
  rcases lt_or_eq_of_le (show i ≤ c by omega) with hic | rfl
  · exact (DerivedCategory.isGE_iff ω.obj c).1 h i hic
  · exact hG0

include f hpush in
/-- **Clause (1) of [Stacks, Tag 0BS2] for the constructed relative dualizing complex.** Let `k`
be a field and let `f : X ⟶ Spec(k)` be proper with `X` of topological Krull dimension at most
one. Then `ω_X^• = f^×(𝒪_{Spec(k)})` has no cohomology below degree `-1`.

[Stacks, Tag 0A9I] bounds `ω_X^•` below in some degree, and
`Stacks.Duality.isGE_add_one_relativeDualizingComplex` raises that bound one degree at a time
until it reaches `-1`. -/
theorem isGE_neg_one_relativeDualizingComplex_derivedStructureSheaf
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    (relativeDualizingComplex f hpush
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj.IsGE (-1) := by
  obtain ⟨N, hN⟩ := exists_isGE_twistedInverseImage_obj f
  have hstart : (relativeDualizingComplex f hpush
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj.IsGE (0 - N) :=
    hN (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) 0
      (isGE_zero_derivedStructureSheaf (Spec (CommRingCat.of k)))
  have main : ∀ (m : ℕ) (c : ℤ), -1 - c ≤ (m : ℤ) →
      (relativeDualizingComplex f hpush
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj.IsGE c →
      (relativeDualizingComplex f hpush
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj.IsGE (-1) := by
    intro m
    induction m with
    | zero =>
      intro c hcm hc
      have := hc
      exact DerivedCategory.TStructure.t.isGE_of_ge _ (-1) c (by omega)
    | succ n ih =>
      intro c hcm hc
      by_cases hcle : c ≤ -2
      · exact ih (c + 1) (by omega)
          (isGE_add_one_relativeDualizingComplex f hpush hdim c hcle hc)
      · exact ih c (by omega) hc
  exact main (-1 - (0 - N)).toNat (0 - N) (by omega) hstart

end Stacks.Duality

end
