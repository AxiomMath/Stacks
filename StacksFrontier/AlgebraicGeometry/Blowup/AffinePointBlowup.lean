module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupOpenCover
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap

/-!
# The blowup of an affine scheme at a closed point

Let `A` be a commutative ring and `p` a point of `Spec A` whose singleton is closed, that is a
maximal ideal of `A`. The reduced closed subscheme supported at `p` is cut out by the ideal sheaf
`Scheme.IdealSheafData.vanishingIdeal {p}`, and this file identifies the blowup of `Spec A` in
that ideal sheaf with the affine blowup `Proj A[𝔭 t]` of `A` in the ideal `𝔭` itself, over
`Spec A`.

Together with
`AlgebraicGeometry.exists_iso_blowUp_comap_opens` and
`AlgebraicGeometry.pointIdeal_comap_open` of
`StacksFrontier/AlgebraicGeometry/Blowup/PointBlowupOpenCover.lean`, this is what makes a blowup of
an arbitrary scheme at a closed point computable: on an affine open containing the point the
blowup is the `Proj` of the Rees algebra of a ring ideal, and over the complement of the point it
is an isomorphism.

## Main results

* `AlgebraicGeometry.primeIdealOf_top_asIdeal` — on `Spec A` the prime ideal that the affine open
  `⊤` attaches to a point is the transport of that point along `Γ(Spec A, ⊤) ≅ A`.
* `AlgebraicGeometry.vanishingIdeal_singleton_eq_ofIdealTop` — the reduced ideal sheaf of a
  closed point of an affine scheme is the ideal sheaf attached to the corresponding maximal
  ideal.
* `AlgebraicGeometry.nonempty_over_iso_blowUpToBase_vanishingIdeal` — **the blowup of `Spec A` at
  a closed point is the affine blowup of `A` in the maximal ideal of that point**, over `Spec A`.

## Implementation notes

Two ideal sheaves on an affine scheme are equal as soon as their ideals of global sections are
(`Scheme.IdealSheafData.ext_of_isAffine`), and the ideal of global sections of the reduced ideal
sheaf of a closed point is the prime ideal of that point
(`AlgebraicGeometry.vanishingIdeal_singleton_ideal` with the affine open `⊤`). Identifying that
with the ideal one starts from is the transport along the counit `Γ(Spec A, ⊤) ≅ A`, which is
also the transport appearing in `Stacks.Blowup.nonempty_over_iso_blowUpToBase`; the two cancel.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **On `Spec A` the prime ideal attached to a point by the affine open `⊤` is the transport of
that point along the counit `Γ(Spec A, ⊤) ≅ A`.** -/
public theorem primeIdealOf_top_asIdeal {A : CommRingCat.{u}} (p : PrimeSpectrum A) :
    ((isAffineOpen_top (Spec A)).primeIdealOf ⟨p, trivial⟩).asIdeal
      = Ideal.map (Scheme.ΓSpecIso A).inv.hom p.asIdeal := by
  set e := Scheme.ΓSpecIso A with he
  set q := (isAffineOpen_top (Spec A)).primeIdealOf ⟨p, trivial⟩ with hq
  have h1 : (isAffineOpen_top (Spec A)).fromSpec.base q = p :=
    (isAffineOpen_top (Spec A)).fromSpec_primeIdealOf ⟨p, trivial⟩
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h1
  have h2 : Ideal.comap e.inv.hom q.asIdeal = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal (h1 : PrimeSpectrum.comap e.inv.hom q = p)
  have hmap : Ideal.map e.inv.hom p.asIdeal = Ideal.comap e.hom.hom p.asIdeal := by
    have := Stacks.IdealSheaf.ideal_map_hom_eq_comap_inv e.symm p.asIdeal
    simpa using this
  rw [hmap, ← h2, Ideal.comap_comap, ← CommRingCat.hom_comp, e.hom_inv_id]
  exact (Ideal.comap_id q.asIdeal).symm

/-- **The reduced ideal sheaf of a closed point of an affine scheme is the ideal sheaf attached
to the corresponding maximal ideal**, transported along the counit `Γ(Spec A, ⊤) ≅ A`. -/
public theorem vanishingIdeal_singleton_eq_ofIdealTop {A : CommRingCat.{u}}
    (p : PrimeSpectrum A) (hp : IsClosed ({p} : Set (Spec A))) :
    Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds (Spec A)) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso A).inv.hom p.asIdeal) := by
  have h1 := vanishingIdeal_singleton_ideal p hp ⟨⊤, isAffineOpen_top (Spec A)⟩
    (show p ∈ ((⊤ : (Spec A).Opens) : Set (Spec A)) from trivial)
  have h2 := Stacks.Blowup.ideal_ofIdealTop_top (X := Spec A)
    (Ideal.map (Scheme.ΓSpecIso A).inv.hom p.asIdeal)
  exact Scheme.IdealSheafData.ext_of_isAffine
    ((h1.trans (primeIdealOf_top_asIdeal p)).trans h2.symm)

/-- **The blowup of `Spec A` at a closed point is the affine blowup of `A` in the maximal ideal
of that point**, over `Spec A`: the `Proj` of the Rees algebra `A[𝔭 t]`. -/
public theorem nonempty_over_iso_blowUpToBase_vanishingIdeal (A : Type u) [CommRing A]
    (p : PrimeSpectrum (CommRingCat.of A))
    (hp : IsClosed ({p} : Set (Spec (CommRingCat.of A)))) :
    Nonempty (Over.mk (Stacks.Blowup.toSpec p.asIdeal) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds (Spec (CommRingCat.of A)))))) :=
  (vanishingIdeal_singleton_eq_ofIdealTop p hp) ▸
    Stacks.Blowup.nonempty_over_iso_blowUpToBase A p.asIdeal

end AlgebraicGeometry

end
