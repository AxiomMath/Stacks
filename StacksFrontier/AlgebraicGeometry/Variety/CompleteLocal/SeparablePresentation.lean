module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.PowerSeriesPresentation
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.FormallySmooth.LocalRings

/-!
# Presenting a completed local ring over its residue field

Let `X` be a locally Noetherian scheme over a field `k`, and let `x` be a point whose residue
field is separable over `k`. The completion of the local ring at `x` is a quotient of a formal
power series ring over that residue field, as an algebra over `k`.

## Main results

* `AlgebraicGeometry.exists_quotient_mvPowerSeries_algEquiv_adicCompletion` presents the
  completed local ring as a quotient of a multivariate formal power series ring.

## Implementation notes

The `k`-algebra structures on the local ring and on the residue field at `x` are the canonical ones
induced by the structure morphism. The condition on the displayed equivalence says that, after
reducing both sides to the residue field, it induces the identity of `X.residueField x`.

## References

* [Stacks Project, Tag 0C52](https://stacks.math.columbia.edu/tag/0C52)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open IsLocalRing

universe u

namespace AlgebraicGeometry

/- Elaborating the statement below needs the plain category-structure route to the quiver
instance; the formally smooth imports also supply a reflexive-quiver route to it. -/
attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver

/-- If the residue field at a point of a locally Noetherian scheme over `k` is separable over
`k`, then the completed local ring is a quotient of a formal power series ring over the residue
field, as a `k`-algebra, and the equivalence induces the identity on residue fields. -/
@[stacks 0C52 "separable_completed_local_ring_presentation",
  ega "0 19.6.3" "(a) ⇒ (c), special case",
  ega "0 19.8.8" "(i), special case"]
public theorem exists_quotient_mvPowerSeries_algEquiv_adicCompletion
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsLocallyNoetherian X] (x : X) :
    let R := X.presheaf.stalk x
    let κ := X.residueField x
    letI : Algebra k R :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
    letI : Algebra k κ :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Algebra.IsSeparableExtension k κ →
      ∃ (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) κ))
        (hI : I ≤ RingHom.ker
          (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) κ →+* κ)),
        ∃ e : (MvPowerSeries (Fin n) κ ⧸ I) ≃ₐ[k]
            AdicCompletion (maximalIdeal R) R,
          (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom.comp
              e.toRingEquiv.toRingHom =
            Ideal.Quotient.lift I
              (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) κ →+* κ) hI := by
  dsimp only
  intro hsep
  let R := X.presheaf.stalk x
  let κ := X.residueField x
  let : Algebra k R :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
  let : Algebra k κ :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let A := AdicCompletion (maximalIdeal R) R
  let : Algebra k A := (algebraMap R A |>.comp (algebraMap k R)).toAlgebra
  have : Algebra.FormallySmooth k κ :=
    ((Algebra.isSeparableExtension_of_charZero_and_tfae k κ).2.out 1 6).mp hsep
  obtain ⟨σ, hσ⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq
    (AlgHom.id k κ)
  have : IsLocalRing A := Scheme.completedLocalRing_isLocal X x
  have : IsNoetherianRing A := Scheme.completedLocalRing_isNoetherian X x
  have : IsAdicComplete (maximalIdeal A) A :=
    Scheme.completedLocalRing_isAdicComplete X x
  obtain ⟨n, y, hy⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      ((maximalIdeal A).fg_of_isNoetherianRing)
  have hker : RingHom.ker (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom =
      maximalIdeal A := by
    change RingHom.ker (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom =
      maximalIdeal (AdicCompletion (maximalIdeal R) R)
    rw [AdicCompletion.ker_evalOneₐ_eq_map (maximalIdeal R)
      ((maximalIdeal R).fg_of_isNoetherianRing), AdicCompletion.maximalIdeal_eq_map]
  have hmem (a b : A) : a - b ∈ maximalIdeal A ↔
      AdicCompletion.evalOneₐ (maximalIdeal R) a = AdicCompletion.evalOneₐ (maximalIdeal R) b := by
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    rfl
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal A)).comp σ.toRingHom) := by
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨AdicCompletion.evalOneₐ (maximalIdeal R) a,
      Ideal.Quotient.eq.mpr ((hmem _ _).2 (DFunLike.congr_fun hσ _))⟩
  obtain ⟨F, hF, hFX, hFC, hmapF⟩ :=
    exists_surjective_eval₂Hom (maximalIdeal A) y hy σ.toRingHom hsurj
  let J : Ideal (MvPowerSeries (Fin n) κ) :=
    Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) κ))
  have hres (p : MvPowerSeries (Fin n) κ) :
      AdicCompletion.evalOneₐ (maximalIdeal R) (F p) =
        MvPowerSeries.constantCoeff p := by
    have hp : p - MvPowerSeries.C (MvPowerSeries.constantCoeff p) ∈ J :=
      Stacks.CompleteLocalRing.RegularSubring.mem_span_range_X n _ (by simp)
    have hp' : F (p - MvPowerSeries.C (MvPowerSeries.constantCoeff p)) ∈
        maximalIdeal A := hmapF ▸ Ideal.mem_map_of_mem F hp
    rw [map_sub, hmem] at hp'
    rw [hFC] at hp'
    exact hp'.trans (DFunLike.congr_fun hσ _)
  let Φ : MvPowerSeries (Fin n) κ →ₐ[k] A :=
    { F with
      commutes' := by
        intro c
        rw [MvPowerSeries.algebraMap_apply]
        change F (MvPowerSeries.C (algebraMap k κ c)) = algebraMap k A c
        rw [hFC]
        exact σ.commutes c }
  refine ⟨n, RingHom.ker Φ.toRingHom, ?_,
    Ideal.quotientKerAlgEquivOfSurjective hF, ?_⟩
  · intro p hp
    change MvPowerSeries.constantCoeff p = 0
    change F p = 0 at hp
    rw [← hres p, hp, map_zero]
    rfl
  · apply RingHom.ext
    intro p
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective p
    change AdicCompletion.evalOneₐ (maximalIdeal R)
      ((Ideal.quotientKerAlgEquivOfSurjective hF) (Ideal.Quotient.mk _ q)) =
        MvPowerSeries.constantCoeff q
    simpa [Ideal.quotientKerAlgEquivOfSurjective_mk, Φ] using hres q

end AlgebraicGeometry
