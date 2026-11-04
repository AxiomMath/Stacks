module

public import StacksFrontier.Deformation.Formal.MinimalVersal.StageTowerComplete

/-!
# The filtration of the stage tower limit by projection kernels

The kernels of the projections of the inverse limit of the stage tower onto the terms of the tower
are cofinal with the powers of the maximal ideal, hence form an ideal filtration of the complete
local algebra they define. Its `n`-th quotient is the `n`-th term of the tower.

## Main definitions

* `Deformation.stageBaseTowerIdealFiltration`: the filtration of `stageBaseTowerCompleteLocal` by
  the kernels of the projections onto the terms of the tower.
* `Deformation.stageBaseTowerQuotientEquiv`: the algebra isomorphism between the `n`-th quotient
  of `stageBaseTowerIdealFiltration` and the `n`-th term of `stageBaseTower`.
* `Deformation.stageBaseTowerQuotientIso`: the isomorphism of `𝒞_Λ` between the `n`-th quotient of
  `stageBaseTowerIdealFiltration` and the `n`-th term of `stageBaseTower`.

## Main results

* `Deformation.stageBaseTowerProjection_surjective`: the projections of the inverse limit of
  `stageBaseTower` onto its terms are surjective.
* `Deformation.stageBaseTowerQuotientIso_mk`: `stageBaseTowerQuotientIso` is the `n`-th
  projection, computed on representatives.
* `Deformation.stageBaseTowerQuotientIso_transition_fac`: `stageBaseTowerQuotientIso` commutes
  with the transition maps of the filtration and of the tower.
* `Deformation.stageBaseTowerQuotientIso_inv_transition_fac`: the inverse of
  `stageBaseTowerQuotientIso` commutes with the transition maps of the tower and of the filtration.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}


section
variable [IsNoetherianRing Λ] [Module.Finite Λ k]
/-- The filtration of `stageBaseTowerCompleteLocal` by the kernels of the projections onto the
terms of the tower. -/
noncomputable def stageBaseTowerIdealFiltration
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d) :
    IdealFiltration (stageBaseTowerCompleteLocal hp hS1 ξ hbound) := by
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  let S := inverseLimit A f
  letI : IsLocalRing S :=
    (Classical.choose (stageBaseTower_cotangent_bounded hp hS1 ξ hbound)).isLocal
  let hadic := kernel_projections_define_maximalIdeal_adicTopology A f
    (fun n => stageBaseTowerTransition_surjective hp hS1 ξ n)
    (Classical.choose (stageBaseTower_cotangent_bounded hp hS1 ξ hbound))
  refine
    { ideal := fun n => RingHom.ker (inverseLimitProj A f n)
      antitone := ?_
      isProper := ?_
      pow_le := ?_
      le_pow := ?_ }
  · apply antitone_nat_of_succ_le
    intro n x hx
    apply RingHom.mem_ker.mpr
    have hzero : inverseLimitProj A f (n + 1) x = 0 :=
      RingHom.mem_ker.mp hx
    have hzero' : x.1 (n + 1) = 0 := by
      change x.1 (n + 1) = 0 at hzero
      exact hzero
    have hcoord : x.1 n = 0 := by
      rw [← x.2 n, hzero', map_zero]
    change x.1 n = 0
    exact hcoord
  · intro n
    rw [lt_top_iff_ne_top, Ideal.ne_top_iff_one]
    intro hone
    have hzero := RingHom.mem_ker.mp hone
    have h1 : inverseLimitProj A f n (1 : S) = 1 := map_one _
    exact one_ne_zero (h1.symm.trans hzero)
  · intro n
    obtain ⟨m, hm⟩ := hadic.2 n
    refine ⟨m, ?_⟩
    exact (Ideal.pow_le_pow_right (Nat.le_succ m)).trans hm
  · intro n
    obtain ⟨m, hm⟩ := hadic.1 (n + 1)
    exact ⟨m, hm⟩

/-- The projections of the inverse limit of `stageBaseTower` onto its terms are surjective. -/
theorem stageBaseTowerProjection_surjective
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (n : ℕ) :
    Function.Surjective (inverseLimitProj (stageBaseTower hp hS1 ξ)
      (stageBaseTowerTransition hp hS1 ξ) n) := by
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  let t : ∀ n, A (n + 1) →ₗ[ℤ] A n := fun n =>
    (f n).hom.toRingHom.toAddMonoidHom.toIntLinearMap
  intro b
  obtain ⟨x, hx⟩ := invLimit.proj_surjective (M := fun n => A n) (t := t)
    (stageBaseTowerTransition_surjective hp hS1 ξ) n b
  exact ⟨⟨x.1, x.2⟩, hx⟩

/-- The algebra isomorphism between the `n`-th quotient of `stageBaseTowerIdealFiltration` and the
`n`-th term of `stageBaseTower`. -/
noncomputable def stageBaseTowerQuotientEquiv
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    (stageBaseTowerCompleteLocal hp hS1 ξ hbound ⧸
      RingHom.ker (inverseLimitProj (stageBaseTower hp hS1 ξ)
        (stageBaseTowerTransition hp hS1 ξ) n)) ≃ₐ[Λ]
      stageBaseTower hp hS1 ξ n := by
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  let R := stageBaseTowerCompleteLocal hp hS1 ξ hbound
  let S := inverseLimit A f
  letI : IsLocalRing S := R.completeLocal.isLocal
  let π := inverseLimitProj A f n
  let K := RingHom.ker π
  let q : (S ⧸ K) →ₐ[Λ] A n := Ideal.Quotient.liftₐ K π
    (by intro x hx; exact RingHom.mem_ker.mpr hx)
  apply AlgEquiv.ofBijective q
  refine ⟨fun x y hxy => ?_, fun b => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact Ideal.Quotient.eq.mpr
      (RingHom.mem_ker.mpr ((map_sub π a b).trans (sub_eq_zero.mpr hxy)))
  · obtain ⟨a, ha⟩ := stageBaseTowerProjection_surjective hp hS1 ξ n b
    exact ⟨Ideal.Quotient.mk K a, ha⟩

/-- The isomorphism of `𝒞_Λ` between the `n`-th quotient of `stageBaseTowerIdealFiltration` and the
`n`-th term of `stageBaseTower`. -/
noncomputable def stageBaseTowerQuotientIso
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    (stageBaseTowerIdealFiltration hp hS1 ξ hbound).quotient n ≅
      stageBaseTower hp hS1 ξ n := by
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let S := stageBaseTowerCompleteLocal hp hS1 ξ hbound
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  letI : IsLocalRing (inverseLimit A f) := S.completeLocal.isLocal
  let π := inverseLimitProj A f n
  let e := stageBaseTowerQuotientEquiv hp hS1 ξ hbound n
  let K := RingHom.ker π
  letI : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr (I.isProper n).ne
  letI : IsLocalRing (S ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  let q : I.quotient n ⟶ A n :=
    { hom := e.toAlgHom
      isLocal := IsLocalHom.of_surjective e.toAlgHom.toRingHom
        (fun y => ⟨e.symm y, e.apply_symm_apply y⟩)
      residue_comm := by
        intro x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact (stageBaseTowerProjection_residue hp hS1 ξ hbound r n).trans
          (I.residueEquiv_residue_mk n r).symm }
  haveI : IsIso q := ArtinianLocalAlgCat.isIso_of_bijective_hom q e.bijective
  exact asIso q

/-- `stageBaseTowerQuotientIso` is the `n`-th projection, computed on representatives. -/
theorem stageBaseTowerQuotientIso_mk
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) (r : stageBaseTowerCompleteLocal hp hS1 ξ hbound) :
    ((stageBaseTowerQuotientIso hp hS1 ξ hbound n).hom).hom
        (Ideal.Quotient.mk
          ((stageBaseTowerIdealFiltration hp hS1 ξ hbound).ideal n) r) =
      inverseLimitProj (stageBaseTower hp hS1 ξ)
        (stageBaseTowerTransition hp hS1 ξ) n r :=
  rfl

/-- `stageBaseTowerQuotientIso` commutes with the transition maps of the filtration and of the
tower. -/
theorem stageBaseTowerQuotientIso_transition_fac
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    (stageBaseTowerIdealFiltration hp hS1 ξ hbound).transition n ≫
        (stageBaseTowerQuotientIso hp hS1 ξ hbound n).hom =
      (stageBaseTowerQuotientIso hp hS1 ξ hbound (n + 1)).hom ≫
        stageBaseTowerTransition hp hS1 ξ n := by
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let S := stageBaseTowerCompleteLocal hp hS1 ξ hbound
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (stageBaseTowerQuotientIso hp hS1 ξ hbound n).hom.hom
      ((I.transition n).hom (Ideal.Quotient.mk (I.ideal (n + 1)) r)) =
    (f n).hom ((stageBaseTowerQuotientIso hp hS1 ξ hbound (n + 1)).hom.hom
      (Ideal.Quotient.mk (I.ideal (n + 1)) r))
  have htr : (I.transition n).hom
      (Ideal.Quotient.mk (I.ideal (n + 1)) r) =
        Ideal.Quotient.mk (I.ideal n) r := by
    rfl
  rw [htr, stageBaseTowerQuotientIso_mk,
    stageBaseTowerQuotientIso_mk]
  exact (r.2 n).symm

/-- The inverse of `stageBaseTowerQuotientIso` commutes with the transition maps of the tower and
of the filtration. -/
theorem stageBaseTowerQuotientIso_inv_transition_fac
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    (stageBaseTowerQuotientIso hp hS1 ξ hbound (n + 1)).inv ≫
        (stageBaseTowerIdealFiltration hp hS1 ξ hbound).transition n =
      stageBaseTowerTransition hp hS1 ξ n ≫
        (stageBaseTowerQuotientIso hp hS1 ξ hbound n).inv := by
  rw [Iso.eq_comp_inv, Category.assoc, Iso.inv_comp_eq]
  exact stageBaseTowerQuotientIso_transition_fac hp hS1 ξ hbound n

end

end Deformation

end
