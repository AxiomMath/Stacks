module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Height
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.RingTheory.QuasiFinite.Dimension

/-!
# The dimension of the local ring of an algebraic space at a point

The dimension of the local ring of an algebraic space `X` over `S` at a point `x`,
`AlgebraicGeometry.Space.localRingDimension`, is the Krull dimension of the local ring of an
étale scheme chart of `X` at any point above `x`. This file shows that inside a locally
Noetherian étale scheme chart a fibre carries no nontrivial specialization, and that a locally
quasi-finite morphism of algebraic spaces does not increase the dimension of the local ring.

## Main results

* `AlgebraicGeometry.eq_of_specializes_of_ringKrullDim_stalk_eq`: on a locally Noetherian
  scheme a specialization between points whose local rings have equal Krull dimension is
  trivial.
* `AlgebraicGeometry.ringKrullDim_stalk_le_of_locallyQuasiFinite`: a locally quasi-finite
  morphism of schemes does not increase the Krull dimension of the local ring.
* `AlgebraicGeometry.Space.eq_of_specializes_of_chartPoint_of_isLocallyNoetherian`: two points
  of a locally Noetherian étale scheme chart above the same point of `|X|`, one specializing to
  the other, are equal.
* `AlgebraicGeometry.Space.localRingDimension_le_of_isLocallyQuasiFinite`: a locally
  quasi-finite morphism of algebraic spaces does not increase the dimension of the local ring.

## References

* [Stacks Project, Tag 0ABW](https://stacks.math.columbia.edu/tag/0ABW)
* [Stacks Project, Tag 0H1Q](https://stacks.math.columbia.edu/tag/0H1Q)
* [Stacks Project, Tag 00QF](https://stacks.math.columbia.edu/tag/00QF)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 0BAM](https://stacks.math.columbia.edu/tag/0BAM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- On a locally Noetherian scheme a specialization `y ⤳ x` between points whose local rings
have the same Krull dimension is trivial. -/
theorem eq_of_specializes_of_ringKrullDim_stalk_eq (X : Scheme.{u}) [IsLocallyNoetherian X]
    {x y : X} (hxy : y ⤳ x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk y)) :
    x = y := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have hyV : y ∈ V := hxy.mem_open V.2 hxV
  let xV : V := ⟨x, hxV⟩
  let yV : V := ⟨y, hyV⟩
  let _ : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let p : Ideal Γ(X, V) := (hV.primeIdealOf yV).asIdeal
  let q : Ideal Γ(X, V) := (hV.primeIdealOf xV).asIdeal
  have hp : p.IsPrime := by dsimp [p]; infer_instance
  have hq : q.IsPrime := by dsimp [q]; infer_instance
  let _ : Algebra Γ(X, V) (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk yV
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk xV
  have hpLoc : IsLocalization.AtPrime (X.presheaf.stalk y) p := by
    dsimp [p]; exact hV.isLocalization_stalk yV
  have hqLoc : IsLocalization.AtPrime (X.presheaf.stalk x) q := by
    dsimp [q]; exact hV.isLocalization_stalk xV
  have hdimP : p.height = q.height := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (X.presheaf.stalk y),
      IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk x)] at hdim
    exact WithBot.coe_eq_coe.mp hdim.symm
  have hpq : p ≤ q := by
    change (hV.primeIdealOf yV).asIdeal ≤ (hV.primeIdealOf xV).asIdeal
    have hxyV : yV ⤳ xV := by
      rw [specializes_iff_forall_open]
      intro W hW hxW
      obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.mp hW
      exact hxy.mem_open hW' hxW
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr
      (hV.isoSpec.hom.base.hom.map_specializes hxyV)
  have hpqEq : p = q := by
    by_contra hne
    exact (Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hpq hne)).ne hdimP
  simpa only [hV.fromSpec_primeIdealOf] using
    (congrArg hV.fromSpec (PrimeSpectrum.ext hpqEq)).symm

/-- A locally quasi-finite morphism of schemes does not increase the Krull dimension of the
local ring: the dimension at a point of the source is at most the dimension at its image. -/
@[ega "IV 13.2.4" "partial, special case"]
theorem ringKrullDim_stalk_le_of_locallyQuasiFinite {X Y : Scheme.{u}} (g : X ⟶ Y)
    [LocallyQuasiFinite g] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim (Y.presheaf.stalk (g x)) := by
  let A := Y.presheaf.stalk (g x)
  let C := X.presheaf.stalk x
  let _ : Algebra A C := (g.stalkMap x).hom.toAlgebra
  let p : Ideal A := IsLocalRing.maximalIdeal A
  let q : Ideal C := IsLocalRing.maximalIdeal C
  have hp : p.IsPrime := by dsimp [p]; infer_instance
  have hq : q.IsPrime := by dsimp [q]; infer_instance
  have : IsLocalHom (g.stalkMap x).hom := inferInstance
  have : q.LiesOver p := ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A C)).symm⟩
  have hqf : (g.stalkMap x).hom.QuasiFinite := g.quasiFiniteAt x
  have : Algebra.QuasiFinite A C := hqf
  have : Algebra.QuasiFiniteAt A q := by
    change Algebra.QuasiFinite A (Localization.AtPrime q)
    infer_instance
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast Ideal.height_le_height_of_liesOver_of_quasiFiniteAt p q

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `X` be an algebraic space over `S` and let `a : h_U ⟶ X` be an étale scheme chart of `X`
whose scheme is locally Noetherian. Two points `u`, `u'` of `U` lying above the same point `x` of
`|X|` with `u' ⤳ u` are then equal. -/
@[stacks 0H1Q]
theorem eq_of_specializes_of_chartPoint_of_isLocallyNoetherian
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (u u' : (BigFppfOver.toScheme B S hS).obj U) (x : points B S hS X)
    (hu : ChartPoint B S hS U a u x) (hu' : ChartPoint B S hS U a u' x)
    (hs : u' ⤳ u) : u = u' := by
  refine eq_of_specializes_of_ringKrullDim_stalk_eq _ hs ?_
  exact (localRingDimension_eq_of_chartPoint B S hS hX U a ha u x hu).symm.trans
    (localRingDimension_eq_of_chartPoint B S hS hX U a ha u' x hu')

/-- A locally quasi-finite morphism of algebraic spaces over `S` does not increase the dimension
of the local ring: for a point `x` of the source, the dimension of the local ring there is at
most the dimension of the local ring of the target at the image of `x`. -/
@[stacks 0ABW]
theorem localRingDimension_le_of_isLocallyQuasiFinite
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyQuasiFinite B S hS f)
    (x : points B S hS X) :
    localRingDimension B S hS x ≤
      localRingDimension B S hS (pointsMap B S hS X f x) := by
  classical
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, h, hcomm, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U a).mp haSurj x
  obtain ⟨p, hp⟩ := Quot.exists_rep z
  have hpx : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x := by
    rwa [← hp] at hz
  let T := BigFppfOver.toScheme B S hS
  let u := schemePoint B S hS U p
  let y := pointsMap B S hS X f x
  have huChart : ChartPoint B S hS U a u x := ⟨p, rfl, hpx⟩
  have hvChart : ChartPoint B S hS V b (T.map h u) y := by
    refine ⟨FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map h) p,
      schemePoint_map_yoneda B S hS h p, ?_⟩
    change pointsMap B S hS (yoneda.obj V) b (pointsMap B S hS (yoneda.obj U) (yoneda.map h)
      (p.class B S hS (yoneda.obj U))) = y
    calc pointsMap B S hS (yoneda.obj V) b (pointsMap B S hS (yoneda.obj U) (yoneda.map h)
            (p.class B S hS (yoneda.obj U)))
        = pointsMap B S hS (yoneda.obj U) (yoneda.map h ≫ b)
            (p.class B S hS (yoneda.obj U)) :=
            (pointsMap_comp_apply B S hS (yoneda.map h) b _).symm
      _ = pointsMap B S hS (yoneda.obj U) (a ≫ f) (p.class B S hS (yoneda.obj U)) := by
            rw [hcomm]
      _ = y := by rw [pointsMap_comp_apply, hpx]
  have : LocallyQuasiFinite (T.map h) :=
    (hf U V a b h haEtale hbEtale hcomm.symm).2
  have hxDim := localRingDimension_eq_of_chartPoint B S hS hX U a haEtale u x huChart
  have hyDim := localRingDimension_eq_of_chartPoint B S hS hY V b hbEtale (T.map h u) y hvChart
  apply WithBot.coe_le_coe.mp
  calc (localRingDimension B S hS x : WithBot ℕ∞)
      = ringKrullDim ((T.obj U).presheaf.stalk u) := hxDim
    _ ≤ ringKrullDim ((T.obj V).presheaf.stalk (T.map h u)) :=
        ringKrullDim_stalk_le_of_locallyQuasiFinite (T.map h) u
    _ = (localRingDimension B S hS y : WithBot ℕ∞) := hyDim.symm

end Space

end AlgebraicGeometry

end
