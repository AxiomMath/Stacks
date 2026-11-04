module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksCore.Tactic.StacksAttribute

/-!
# The Cohen–Macaulay locus of a flat morphism

For a flat morphism locally of finite presentation, the locus where the morphism is
Cohen–Macaulay is cut out by Cohen–Macaulayness of the fibre local rings alone, and it meets
every fibre in a dense subset.

## Main results

* `AlgebraicGeometry.isCohenMacaulayAt_set_eq_fiberLocalRing` is the characterization of the
  Cohen–Macaulay locus as an equality of sets of points.
* `AlgebraicGeometry.dense_cohenMacaulayAt_fiber` states fibrewise density of the
  Cohen–Macaulay locus.

## Implementation notes

The locally Noetherian fibres required by `AlgebraicGeometry.Scheme.Hom.IsCohenMacaulayAt`
follow from local finite presentation, so the witness is supplied from the morphism by
`AlgebraicGeometry.isLocallyNoetherian_fiber_of_locallyOfFinitePresentation` rather than taken
as a hypothesis. The point of the fibre corresponding to `x` is `f.asFiber x`, and density is
expressed on each scheme-theoretic fibre by pulling the pointwise locus back along the
canonical morphism to the source.

## References

* [Stacks Project, Tag 045U](https://stacks.math.columbia.edu/tag/045U)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The Cohen–Macaulay locus of a flat, locally finitely presented morphism is exactly the locus
where the local ring of its fibre is Cohen–Macaulay. -/
@[stacks 045U "fibre_local_ring_characterization"]
public theorem isCohenMacaulayAt_set_eq_fiberLocalRing
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    let hf : ∀ y : S, IsLocallyNoetherian (f.fiber y) := fun y =>
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y
    {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x} =
      {x : X | letI := hf (f x)
        IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))} := by
  ext x
  simpa only [Set.mem_ofPred_eq, Scheme.Hom.IsCohenMacaulayAt] using
    (and_iff_right (show IsFlatAt f.toLRSHom.toShHom x from Flat.stalkMap f x))

/-- A point of a fibre at which the fibre local ring is Cohen–Macaulay is a point of the
Cohen–Macaulay locus of a flat morphism. -/
private theorem cohenMacaulayAt_of_fiberPoint {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f]
    (hf : ∀ y : S, IsLocallyNoetherian (f.fiber y)) (x : X) (y : S)
    (hxy : f x = y) (z : f.fiber y) (hz : f.fiberι y z = x)
    (hN : IsNoetherianRing ((f.fiber y).presheaf.stalk z))
    (hCM : @IsCohenMacaulayLocalRing ((f.fiber y).presheaf.stalk z) _ hN inferInstance) :
    Scheme.Hom.IsCohenMacaulayAt f hf x := by
  cases hxy
  have hza : z = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (by rwa [f.fiberι_asFiber])
  show IsFlatAt f.toLRSHom.toShHom x ∧
    IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
  exact ⟨Flat.stalkMap f x, by rw [← hza]; exact hCM⟩

/-- Every point of a locally Noetherian scheme specializes from a point whose local ring is
Cohen–Macaulay. -/
private theorem exists_specializes_localCohenMacaulay (Y : Scheme.{u})
    [IsLocallyNoetherian Y] (x : Y) :
    ∃ z : Y, z ⤳ x ∧ ∃ hN : IsNoetherianRing (Y.presheaf.stalk z),
      @IsCohenMacaulayLocalRing (Y.presheaf.stalk z) _ hN inferInstance := by
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hxV, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U : Y.affineOpens := ⟨V, hV⟩
  have hUaff : IsAffineOpen (U : Y.Opens) := hV
  let xV : V := ⟨x, hxV⟩
  let q : Spec Γ(Y, U) := hUaff.isoSpec.hom xV
  let _ : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨m, hm, hmq⟩ := Ideal.exists_minimalPrimes_le
    (I := ⊥) (J := q.asIdeal) bot_le
  have hmprime : m.IsPrime := hm.1.1
  let p : Spec Γ(Y, U) := ⟨m, hmprime⟩
  let z : Y := hUaff.fromSpec p
  have hzV : z ∈ V := hUaff.range_fromSpec.subset ⟨p, rfl⟩
  let zV : V := ⟨z, hzV⟩
  have hsp : z ⤳ x := by
    have hqx : hUaff.fromSpec q = x := by
      simpa [IsAffineOpen.primeIdealOf] using hUaff.fromSpec_primeIdealOf xV
    rw [← hqx]
    have hdual : OrderDual.toDual (⟨q.asIdeal, q.isPrime⟩ : PrimeSpectrum Γ(Y, U)) ≤
        OrderDual.toDual (⟨m, hmprime⟩ : PrimeSpectrum Γ(Y, U)) := hmq
    have hqp : q ≤ p := (specOrderIsoPrimeSpectrum (Γ(Y, U))).map_rel_iff.mp hdual
    exact (Scheme.le_iff_specializes.mp hqp).map hUaff.fromSpec.continuous
  let _ : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian U
  let _ : Algebra Γ(Y, U) (Y.presheaf.stalk z) :=
    Y.presheaf.algebra_section_stalk zV
  let _ : IsLocalization.AtPrime (Y.presheaf.stalk z) p.asIdeal :=
    hUaff.isLocalization_stalk' p hzV
  let _ : IsNoetherianRing (Y.presheaf.stalk z) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl (Y.presheaf.stalk z)
      (IsLocallyNoetherian.component_noetherian U)
  have hpmin : p.asIdeal ∈ minimalPrimes Γ(Y, U) := hm
  have hdim : ringKrullDim (Y.presheaf.stalk z) = 0 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Y.presheaf.stalk z),
      Ideal.height_eq_zero_iff.mpr hpmin]
    rfl
  have hcm := Module.isMaximalCohenMacaulay_self_of_ringKrullDim_eq_zero hdim
  exact ⟨z, hsp, inferInstance,
    (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mpr hcm⟩

/-- The Cohen–Macaulay locus of a flat, locally finitely presented morphism is dense in every
fibre. -/
@[stacks 045U "cm_locus_fibrewise_dense", sga "4 XVIII 2.3" "fibrewise density"]
public theorem dense_cohenMacaulayAt_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    let hf : ∀ s : S, IsLocallyNoetherian (f.fiber s) := fun s =>
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f s
    ∀ s : S, Dense ((f.fiberι s) ⁻¹' {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x}) := by
  intro hf s
  let _ : IsLocallyNoetherian (f.fiber s) := hf s
  intro z
  obtain ⟨w, hsp, hN, hCM⟩ := exists_specializes_localCohenMacaulay (f.fiber s) z
  have hws : f (f.fiberι s w) = s := (f.range_fiberι s).subset ⟨w, rfl⟩
  have hw : Scheme.Hom.IsCohenMacaulayAt f hf (f.fiberι s w) :=
    cohenMacaulayAt_of_fiberPoint f hf _ s hws w rfl hN hCM
  have hw' : w ∈ (f.fiberι s) ⁻¹' {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x} := hw
  exact closure_mono (Set.singleton_subset_iff.mpr hw') (specializes_iff_mem_closure.mp hsp)

end AlgebraicGeometry
