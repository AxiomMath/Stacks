module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MinimalPrimesOfAffineOpen
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent
public import StacksFrontier.RingTheory.Etale.TotalFractionRing
public import StacksFrontier.RingTheory.Localization.NonZeroDivisorsOfSpan

/-!
# Global sections of an étale base change of the total fraction rings

Let `X₀` be a scheme all of whose weakly associated points are generic points of irreducible
components and whose quasi-compact opens have finitely many irreducible components, and let
`q : Y ⟶ X₀` be an affine morphism such that over every affine open `V` of `X₀` the ring
`Γ(Y, q⁻¹V)` is the total ring of fractions of `Γ(X₀, V)` — for instance the relative spectrum
of the sheaf of meromorphic functions of `X₀`.  Let `g : U ⟶ X₀` be étale with `U` affine and
satisfying the same two hypotheses.  Then the global sections of `W = U ×_{X₀} Y` form the total
ring of fractions of `Γ(U, ⊤)`.

Over a principal open `D(r)` of `U` mapping into an affine open `V` of `X₀` the sections of `W`
are `Γ(U, D(r)) ⊗_{Γ(X₀, V)} Q(Γ(X₀, V))`, which is the total ring of fractions of `Γ(U, D(r))`
because `Γ(X₀, V) → Γ(U, D(r))` is étale (`IsLocalization.nonZeroDivisors_of_etale`); these
principal opens cover `U`, and total rings of fractions glue along such a cover
(`IsLocalization.nonZeroDivisors_of_away_span`).

## Main results

* `AlgebraicGeometry.isLocalization_appLE_basicOpen_of_isPullback`: the statement over a
  principal open mapping into an affine open.
* `AlgebraicGeometry.isLocalization_appTop_of_isPullback_of_etale`: the statement over `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

variable {X₀ Y U W : Scheme.{u}} {q : Y ⟶ X₀} {g : U ⟶ X₀} {p : W ⟶ U} {k : W ⟶ Y}

/-- The pullback of an affine morphism to an affine scheme is affine. -/
private theorem isAffine_of_isPullback [IsAffineHom q] [IsAffine U] (H : IsPullback p k g q) :
    IsAffine W :=
  have : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip ‹_›
  isAffine_of_isAffineHom p

/-- **Sections over a principal open mapping into an affine open.**  In a cartesian square
`W = U ×_{X₀} Y` with `U` affine, `g` étale and `Γ(Y, q⁻¹V)` the total ring of fractions of
`Γ(X₀, V)` over an affine open `V` of `X₀`, the sections of `W` over the preimage of a principal
open `D(r) ⊆ g⁻¹V` of `U` form the total ring of fractions of `Γ(U, D(r))`. -/
theorem isLocalization_appLE_basicOpen_of_isPullback
    (hwa : Stacks.Divisors.schemeWeaklyAssociatedPoints X₀ ⊆ genericPoints X₀)
    (hfin : ∀ V : X₀.Opens, IsCompact (V : Set X₀) → (irreducibleComponents V).Finite)
    [IsAffineHom q] [IsAffine U] [Etale g] (H : IsPullback p k g q)
    (V : X₀.Opens) (hV : IsAffineOpen V)
    (hqV : letI := (q.app V).hom.toAlgebra; IsLocalization Γ(X₀, V)⁰ Γ(Y, q ⁻¹ᵁ V))
    (r : Γ(U, ⊤)) (hr : U.basicOpen r ≤ g ⁻¹ᵁ V) :
    letI := (p.appLE (U.basicOpen r) (W.basicOpen (p.appTop r))
      (Scheme.preimage_basicOpen_top p r).ge).hom.toAlgebra
    IsLocalization Γ(U, U.basicOpen r)⁰ Γ(W, W.basicOpen (p.appTop r)) := by
  have : IsAffine W := isAffine_of_isPullback H
  have hUW : W.basicOpen (p.appTop r) = p ⁻¹ᵁ U.basicOpen r ⊓ k ⁻¹ᵁ (q ⁻¹ᵁ V) := by
    rw [Scheme.preimage_basicOpen_top, eq_comm, inf_eq_left, ← Scheme.preimage_basicOpen_top]
    calc p ⁻¹ᵁ U.basicOpen r ≤ p ⁻¹ᵁ (g ⁻¹ᵁ V) := p.preimage_mono hr
      _ = k ⁻¹ᵁ (q ⁻¹ᵁ V) := by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]
  have hP := isPushout_appLE_of_isPullback_of_isAffineOpen H V hV (q ⁻¹ᵁ V) (hV.preimage q)
    le_rfl (U.basicOpen r) ((isAffineOpen_top U).basicOpen r) hr _ hUW
    ((isAffineOpen_top W).basicOpen _)
  rw [Scheme.Hom.appLE_eq_app] at hP
  let : Algebra Γ(X₀, V) Γ(Y, q ⁻¹ᵁ V) := (q.app V).hom.toAlgebra
  let : Algebra Γ(X₀, V) Γ(U, U.basicOpen r) := (g.appLE V (U.basicOpen r) hr).hom.toAlgebra
  let : Algebra Γ(Y, q ⁻¹ᵁ V) Γ(W, W.basicOpen (p.appTop r)) :=
    (k.appLE (q ⁻¹ᵁ V) (W.basicOpen (p.appTop r)) (hUW.trans_le inf_le_right)).hom.toAlgebra
  let : Algebra Γ(U, U.basicOpen r) Γ(W, W.basicOpen (p.appTop r)) :=
    (p.appLE (U.basicOpen r) (W.basicOpen (p.appTop r))
      (Scheme.preimage_basicOpen_top p r).ge).hom.toAlgebra
  let : Algebra Γ(X₀, V) Γ(W, W.basicOpen (p.appTop r)) :=
    ((algebraMap Γ(U, U.basicOpen r) Γ(W, W.basicOpen (p.appTop r))).comp
      (algebraMap Γ(X₀, V) Γ(U, U.basicOpen r))).toAlgebra
  have : IsScalarTower Γ(X₀, V) Γ(U, U.basicOpen r) Γ(W, W.basicOpen (p.appTop r)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(X₀, V) Γ(Y, q ⁻¹ᵁ V) Γ(W, W.basicOpen (p.appTop r)) :=
    IsScalarTower.of_algebraMap_eq fun x => (ConcreteCategory.congr_hom hP.w x).symm
  have hpush : Algebra.IsPushout Γ(X₀, V) Γ(Y, q ⁻¹ᵁ V) Γ(U, U.basicOpen r)
      Γ(W, W.basicOpen (p.appTop r)) :=
    CommRingCat.isPushout_iff_isPushout.mp hP
  have : IsLocalization Γ(X₀, V)⁰ Γ(Y, q ⁻¹ᵁ V) := hqV
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Γ(U, U.basicOpen r) Γ(X₀, V)⁰)
      Γ(W, W.basicOpen (p.appTop r)) :=
    (Algebra.isLocalization_iff_isPushout Γ(X₀, V)⁰ Γ(Y, q ⁻¹ᵁ V)).mpr hpush.symm
  have : Algebra.Etale Γ(X₀, V) Γ(U, U.basicOpen r) :=
    HasRingHomProperty.appLE (P := @Etale) g ‹_› ⟨V, hV⟩
      ⟨U.basicOpen r, (isAffineOpen_top U).basicOpen r⟩ hr
  exact IsLocalization.nonZeroDivisors_of_etale (A := Γ(X₀, V))
    (finite_minimalPrimes_of_affine_open hfin V hV.isoSpec.symm)
    (exists_mem_minimalPrimes_of_notMem_nonZeroDivisors V hV hwa) _

/-- **Global sections of an étale base change of the total fraction rings.**  Let `X₀` satisfy
the two hypotheses of Stacks 0EN6, let `q : Y ⟶ X₀` be affine with `Γ(Y, q⁻¹V)` the total ring
of fractions of `Γ(X₀, V)` over every affine open `V`, and let `g : U ⟶ X₀` be étale with `U`
affine and satisfying the same two hypotheses.  Then `Γ(U ×_{X₀} Y, ⊤)` is the total ring of
fractions of `Γ(U, ⊤)`. -/
theorem isLocalization_appTop_of_isPullback_of_etale
    (hwa : Stacks.Divisors.schemeWeaklyAssociatedPoints X₀ ⊆ genericPoints X₀)
    (hfin : ∀ V : X₀.Opens, IsCompact (V : Set X₀) → (irreducibleComponents V).Finite)
    [IsAffineHom q]
    (hq : ∀ V : X₀.Opens, IsAffineOpen V →
      letI := (q.app V).hom.toAlgebra; IsLocalization Γ(X₀, V)⁰ Γ(Y, q ⁻¹ᵁ V))
    [IsAffine U] [Etale g]
    (hwaU : Stacks.Divisors.schemeWeaklyAssociatedPoints U ⊆ genericPoints U)
    (hfinU : ∀ V : U.Opens, IsCompact (V : Set U) → (irreducibleComponents V).Finite)
    (H : IsPullback p k g q) :
    letI := p.appTop.hom.toAlgebra
    IsLocalization Γ(U, ⊤)⁰ Γ(W, ⊤) := by
  have : IsAffine W := isAffine_of_isPullback H
  let : Algebra Γ(U, ⊤) Γ(W, ⊤) := p.appTop.hom.toAlgebra
  let s : Set Γ(U, ⊤) := {r | ∃ V : X₀.Opens, IsAffineOpen V ∧ U.basicOpen r ≤ g ⁻¹ᵁ V}
  have hs : Ideal.span s = ⊤ := by
    rw [← (isAffineOpen_top U).iSup_basicOpen_eq_self_iff]
    refine le_antisymm le_top fun x _ => ?_
    obtain ⟨V, hV, hxV, -⟩ := (Opens.isBasis_iff_nbhd.mp X₀.isBasis_affineOpens)
      (by simp : g x ∈ (⊤ : X₀.Opens))
    obtain ⟨f, hf, hxf⟩ := (isAffineOpen_top U).exists_basicOpen_le
      (V := g ⁻¹ᵁ V) ⟨x, hxV⟩ (Set.mem_univ x)
    exact Opens.mem_iSup.mpr ⟨⟨f, V, hV, hf⟩, hxf⟩
  let : ∀ r : s, Algebra Γ(U, ⊤) Γ(W, W.basicOpen (p.appTop r.1)) := fun r =>
    ((algebraMap Γ(W, ⊤) Γ(W, W.basicOpen (p.appTop r.1))).comp p.appTop.hom).toAlgebra
  let : ∀ r : s, Algebra Γ(U, U.basicOpen r.1) Γ(W, W.basicOpen (p.appTop r.1)) := fun r =>
    (p.appLE (U.basicOpen r.1) (W.basicOpen (p.appTop r.1))
      (Scheme.preimage_basicOpen_top p r.1).ge).hom.toAlgebra
  have : ∀ r : s, IsScalarTower Γ(U, ⊤) Γ(W, ⊤) Γ(W, W.basicOpen (p.appTop r.1)) := fun r =>
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : ∀ r : s, IsScalarTower Γ(U, ⊤) Γ(U, U.basicOpen r.1)
      Γ(W, W.basicOpen (p.appTop r.1)) := fun r => by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    have e : U.presheaf.map (homOfLE (U.basicOpen_le r.1)).op ≫
        p.appLE (U.basicOpen r.1) (W.basicOpen (p.appTop r.1))
          (Scheme.preimage_basicOpen_top p r.1).ge =
        p.appTop ≫ W.presheaf.map (homOfLE (W.basicOpen_le (p.appTop r.1))).op := by
      rw [Scheme.Hom.map_appLE]
      rfl
    exact (ConcreteCategory.congr_hom e x).symm
  have : ∀ r : s, IsLocalization.Away (algebraMap Γ(U, ⊤) Γ(W, ⊤) r.1)
      Γ(W, W.basicOpen (p.appTop r.1)) := fun r =>
    (isAffineOpen_top W).isLocalization_basicOpen (p.appTop r.1)
  have : ∀ r : s, IsLocalization.Away r.1 Γ(U, U.basicOpen r.1) := fun r =>
    (isAffineOpen_top U).isLocalization_basicOpen r.1
  refine IsLocalization.nonZeroDivisors_of_away_span s hs (fun r => Γ(U, U.basicOpen r.1))
    (fun r => Γ(W, W.basicOpen (p.appTop r.1))) (finite_minimalPrimes_appTop U hfinU)
    (exists_mem_minimalPrimes_of_notMem_nonZeroDivisors ⊤ (isAffineOpen_top U) hwaU)
    fun r => ?_
  obtain ⟨V, hV, hr⟩ := r.2
  exact isLocalization_appLE_basicOpen_of_isPullback hwa hfin H V hV (hq V hV) r.1 hr

end AlgebraicGeometry
