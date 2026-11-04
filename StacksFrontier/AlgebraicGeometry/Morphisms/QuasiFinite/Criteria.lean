module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.Topology.Inseparable
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.Topology.Separation.IsolatedPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Criteria for quasi-finiteness at a point

For a morphism locally of finite type, quasi-finiteness at a point has three further
descriptions. Topologically, the point is isolated in its scheme-theoretic fibre; equivalently
it is closed in that fibre and nothing properly specializes to it there. Algebraically, the
induced map of affine coordinate rings is quasi-finite at the corresponding prime, for every
compatible choice of affine neighbourhoods.

The equivalence of the two topological conditions is where the finite-type hypothesis is used:
the fibre is then locally Noetherian and Jacobson, and in a Noetherian Jacobson local picture a
closed point with no proper generalization inside the fibre is already open.

## Main results

* `AlgebraicGeometry.quasiFiniteAt_tfae` gives the four equivalent characterizations of
  quasi-finiteness at a point.

## Implementation notes

The four entries of `List.TFAE` occur in the order of the source. The point `x` in the fibre
over `f x` is represented canonically by `Scheme.Hom.asFiber x`. In the affine criterion,
`Scheme.Hom.appLE` is the induced map of coordinate rings and `IsAffineOpen.primeIdealOf`
identifies `x` with the corresponding prime ideal. The specialization relation is Mathlib's
`Specializes`, written `⤳`.

## References

* [Stacks Project, Tag 01TH](https://stacks.math.columbia.edu/tag/01TH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- In a locally Noetherian Jacobson scheme, a closed point admitting no proper generalization
is open. The statement is reduced to an affine chart, where it is the corresponding fact about
a Noetherian Jacobson ring. -/
private lemma isOpen_singleton_of_isClosed_of_no_specialization
    {Y : Scheme} [JacobsonSpace Y] (y : Y)
    (h : IsClosed ({y} : Set Y) ∧
      ¬ ∃ y' : Y, y' ≠ y ∧ y' ⤳ y)
    (hnoeth : ∀ i, IsNoetherianRing Γ(Y.affineCover.X i, ⊤)) : IsOpen ({y} : Set Y) := by
  obtain ⟨i, z, rfl⟩ := Y.affineCover.exists_eq y
  let ι := Y.affineCover.f i
  rw [← Set.image_singleton]
  apply ι.isOpenEmbedding.isOpen_iff_image_isOpen.mp
  show IsOpen ({z} : Set (Y.affineCover.X i))
  let e : (Y.affineCover.X i) ≃ₜ PrimeSpectrum Γ(Y.affineCover.X i, ⊤) :=
    (Y.affineCover.X i).isoSpec.hom.homeomorph
  apply e.isOpen_image.mp
  rw [Set.image_singleton]
  have : IsNoetherianRing Γ(Y.affineCover.X i, ⊤) := hnoeth i
  have : JacobsonSpace (Y.affineCover.X i) := JacobsonSpace.of_isOpenEmbedding ι.isOpenEmbedding
  have : IsJacobsonRing Γ(Y.affineCover.X i, ⊤) :=
    PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr
      (JacobsonSpace.of_isClosedEmbedding e.symm.isClosedEmbedding)
  apply ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing (e z)).out 3 1).mp
  constructor
  · have hc : IsClosed ({z} : Set (Y.affineCover.X i)) := by
      have heq : ι ⁻¹' ({ι z} : Set Y) = {z} := by
        ext w
        simp only [Set.mem_preimage, Set.mem_singleton_iff, ι.injective.eq_iff]
      exact heq ▸ h.1.preimage ι.continuous
    simpa using e.isClosed_image.mpr hc
  · intro a b hba ha
    simp only [Set.mem_singleton_iff] at ha ⊢
    subst a
    by_contra hb
    apply h.2
    refine ⟨ι (e.symm b), ?_, ?_⟩
    · exact fun heq ↦ hb (by simpa using congrArg e (ι.injective heq))
    · simpa using (hba.map e.symm.continuous).map ι.continuous

/-- **Stacks Project, Tag 01TH.** For a morphism locally of finite type, quasi-finiteness at a
point is equivalent to isolation of that point in the fibre, to the corresponding closedness
and specialization condition, and to quasi-finiteness at the corresponding prime for every
compatible pair of affine open neighbourhoods. -/
@[stacks 01TH, ega "II 6.2.2" "a) <=> c)", ega "II 6.2.1"]
public theorem quasiFiniteAt_tfae {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) :
    List.TFAE [
      quasiFiniteAt f x,
      IsIsolatedPoint (f.asFiber x),
      IsClosed ({f.asFiber x} : Set (f.fiber (f x))) ∧
        (¬ ∃ x' : f.fiber (f x),
          x' ≠ f.asFiber x ∧ x' ⤳ f.asFiber x),
      ∀ (U : S.affineOpens) (V : X.affineOpens) (hxV : x ∈ V.1)
        (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
        (f.appLE U V hVU).hom.QuasiFiniteAt
          (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal] := by
  have hfinite : AlgebraicGeometry.finiteTypeAt f x := by
    obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, hfx, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hfx (f ⁻¹ᵁ U).2
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, f.finiteType_appLE hU hV hVU⟩
  tfae_have 1 ↔ 2 :=
    ⟨fun h ↦ Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp h.2,
      fun h ↦ ⟨hfinite, Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr h⟩⟩
  tfae_have 2 → 3 := by
    intro h
    refine ⟨isClosed_singleton_of_isLocallyClosed_singleton h.isLocallyClosed, ?_⟩
    rintro ⟨x', hx', hsp⟩
    exact hx' (hsp.mem_open h (by simp))
  tfae_have 3 → 2 := by
    intro h
    apply isOpen_singleton_of_isClosed_of_no_specialization _ h
    have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
      show LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x)))
      infer_instance
    exact (isLocallyNoetherian_iff_of_affine_openCover (f.fiber (f x)).affineCover).mp
      (LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x)))
  tfae_have 1 ↔ 4 := by
    constructor
    · rintro ⟨_, hx⟩ U V hxV hVU
      exact hx.quasiFiniteAt V.2 U.2 hVU hxV
    · intro h
      obtain ⟨U, V, hxV, hVU, hft⟩ := hfinite
      exact (quasiFiniteAt_iff_exists_affineOpens f x).mpr ⟨U, V, hxV, hVU, hft, h U V hxV hVU⟩
  tfae_finish

end AlgebraicGeometry
