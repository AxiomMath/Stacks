module

public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.PointAvoidingFunction
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.FermatCurveProperties
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.TorusChart
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.TorusFermatPoints

/-!
# A point of the affine Fermat curve that is not the zero locus of a function

Let `k` be an uncountable algebraically closed field of characteristic other than three. The
affine curve `1 + x ^ 3 + y ^ 3 = 0` in the torus `x y ≠ 0`, with coordinate ring
`A = k[x, y][1 / (x y)] ⧸ (1 + x ^ 3 + y ^ 3)`, has a maximal ideal `P` which is not the exact
zero locus of any `a ∈ A`: no `a` lies in `P` and in no other prime ideal.

This is the choice of the point `y` of Stacks 0D5E on the torus chart of the central fibre `Y₀`.
The chart is the open `U = D₊(T₀ T₁ T₂)` of the Fermat cubic curve, a smooth proper curve of
genus one; `U` has finite complement and uncountably many closed points, so
`AlgebraicGeometry.IsCurve.exists_isClosed_forall_basicOpen_ne` gives a closed point `x ∈ U` at
which no function on `U` vanishes alone, and `P` is the prime ideal of `x` under `Spec A ≅ U`.

## Main results

* `AlgebraicGeometry.Scheme.Opens.mem_basicOpen_topIso_hom_iff`: through an isomorphism
  `ψ : Spec A ≅ U`, a function `a ∈ A` becomes a section of `X` over `U` whose basic open is the
  set of points of `U` at whose prime `a` does not vanish.
* `Stacks.Examples.CurveFamilyNotScheme.exists_isMaximal_forall_not_zeroLocus_eq`: the
  statement above.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Opens

/-- **Functions on an affine open through a chart.** Let `ψ : Spec A ≅ U` identify an open
subscheme `U` of `X` with an affine scheme. A function `a ∈ A` gives the section
`U.topIso.hom (ψ.inv.appTop a)` of `X` over `U`; a point `z ∈ U` lies in its basic open exactly
when `a` is not in the prime ideal `ψ⁻¹(z)`. -/
theorem mem_basicOpen_topIso_hom_iff {X : Scheme.{u}} {U : X.Opens} {A : CommRingCat.{u}}
    (ψ : Spec A ≅ U.toScheme) (a : A) (z : U) :
    (z : X) ∈ X.basicOpen (U.topIso.hom (ψ.inv.appTop ((Scheme.ΓSpecIso A).inv a))) ↔
      a ∉ (ψ.inv z).asIdeal := by
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv, Iso.hom_inv_id_apply,
    ← Scheme.preimage_basicOpen_top]
  change U.ι z ∈ U.ι '' _ ↔ _
  refine U.ι.isOpenEmbedding.injective.mem_set_image.trans ?_
  change ψ.inv z ∈ (Spec A).basicOpen _ ↔ _
  rw [basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen _ _

end AlgebraicGeometry.Scheme.Opens

namespace Stacks.Examples.CurveFamilyNotScheme

open _root_.AlgebraicGeometry

/-- **A point of the affine Fermat curve on the torus avoided by every function** (the choice of
the point `y` in Stacks 0D5E). Over an uncountable algebraically closed field of characteristic
other than three, the coordinate ring `k[x, y][1 / (x y)] ⧸ (1 + x ^ 3 + y ^ 3)` has a maximal
ideal `P` such that no element `a` has `P` as its only prime ideal containing it. -/
theorem exists_isMaximal_forall_not_zeroLocus_eq (k : Type u) [Field k] [IsAlgClosed k]
    [Uncountable k] (h3 : ringChar k ≠ 3) :
    ∃ P : Ideal (torusFermatRing k), P.IsMaximal ∧
      ∀ a : torusFermatRing k, ¬ ∀ Q : Ideal (torusFermatRing k), Q.IsPrime → (a ∈ Q ↔ Q = P) := by
  obtain ⟨ψ⟩ := nonempty_iso_fermatTorusOpen k
  set X := fermatCurve k
  set U := fermatTorusOpen k
  set A := CommRingCat.of (torusFermatRing k)
  have := smooth_fermatCurveToSpec k h3
  have := isCurve_fermatCurveToSpec k h3
  have := irreducibleSpace_fermatCurve h3
  have := IsCurve.isNoetherian_of_isCurve k (fermatCurveToSpec k)
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (fermatCurveToSpec k)
  let e : Spec A ≃ₜ {x : X // x ∈ U} := Scheme.homeoOfIso ψ
  -- closed points of `U` are the closed points of `X` lying in `U`
  have hclosedU : ∀ z : U, IsClosed ({z} : Set U) ↔ IsClosed ({(z : X)} : Set X) := fun z => by
    have := congrArg (z ∈ ·) U.isOpenEmbedding.preimage_closedPoints
    exact this.to_iff.symm
  -- closed points of `Spec A` are the maximal ideals, and `e` preserves closed points
  have hclosedSpec : ∀ p : Spec A, IsClosed ({p} : Set (Spec A)) ↔ IsClosed ({e p} : Set U) :=
    fun p => by
      have := e.isClosed_image (s := ({p} : Set (Spec A)))
      rw [Set.image_singleton] at this
      exact this.symm
  have hmax : ∀ p : Spec A, p.asIdeal.IsMaximal ↔ IsClosed ({(e p : X)} : Set X) := fun p => by
    rw [← hclosedU, ← hclosedSpec]
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).symm
  -- (a) the complement of `U` is finite
  have hnotcount := not_countable_setOf_isMaximal_torusFermatRing (k := k)
  obtain ⟨M, hM⟩ : {M : Ideal (torusFermatRing k) | M.IsMaximal}.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun h => hnotcount (h ▸ Set.countable_empty)
  have hUne : (U : Set X).Nonempty := ⟨(e ⟨M, hM.isPrime⟩ : X), (e ⟨M, hM.isPrime⟩).2⟩
  have hUc : ((U : Set X)ᶜ).Finite := by
    refine (Stacks.CurveProjectiveCompletion.finite_compl_of_genericPoints_subset U.isOpen
      (topologicalKrullDim_fermatCurve k).le ?_).1
    rw [genericPoints_eq_singleton, Set.singleton_subset_iff]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hUne)
  -- (b) `U` has uncountably many closed points
  have hunc : ¬ {x : X | x ∈ U ∧ IsClosed ({x} : Set X)}.Countable := by
    intro hc
    apply hnotcount
    have hT : {p : Spec A | p.asIdeal.IsMaximal}.Countable :=
      Set.MapsTo.countable_of_injOn (f := fun p => (e p : X))
        (fun p hp => show (e p : X) ∈ U ∧ IsClosed ({(e p : X)} : Set X) from
          ⟨(e p).2, (hmax p).mp hp⟩)
        (fun p _ q _ h => e.injective (Subtype.ext h)) hc
    refine (hT.image PrimeSpectrum.asIdeal).mono fun M hM => ?_
    have hM' : M.IsMaximal := hM
    exact ⟨(PrimeSpectrum.mk M hM'.isPrime : Spec A), hM', rfl⟩
  -- (c) the chosen point
  obtain ⟨x, hxU, hxcl, hx⟩ := IsCurve.exists_isClosed_forall_basicOpen_ne k
    (fermatCurveToSpec k) (genus_fermatCurveToSpec k h3) U hUc hunc
  set p : Spec A := e.symm ⟨x, hxU⟩
  have hep : e p = ⟨x, hxU⟩ := e.apply_symm_apply _
  have hpmax : p.asIdeal.IsMaximal := (hmax p).mpr (by rw [hep]; exact hxcl)
  refine ⟨p.asIdeal, hpmax, fun a ha => hx (U.topIso.hom (ψ.inv.appTop
    ((Scheme.ΓSpecIso A).inv a))) ?_⟩
  ext z
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · intro hz
    have hzU : z ∈ U := X.basicOpen_le _ hz
    refine ⟨hzU, fun hzx => ?_⟩
    have := (Scheme.Opens.mem_basicOpen_topIso_hom_iff ψ a ⟨z, hzU⟩).mp hz
    apply this
    rw [ha _ (ψ.inv ⟨z, hzU⟩).isPrime]
    subst hzx
    rfl
  · rintro ⟨hzU, hzx⟩
    refine (Scheme.Opens.mem_basicOpen_topIso_hom_iff ψ a ⟨z, hzU⟩).mpr fun hmem => hzx ?_
    have h2 : e.symm ⟨z, hzU⟩ = e.symm ⟨x, hxU⟩ :=
      PrimeSpectrum.ext ((ha _ (ψ.inv ⟨z, hzU⟩).isPrime).mp hmem)
    exact congrArg Subtype.val (e.symm.injective h2)

end Stacks.Examples.CurveFamilyNotScheme

end
