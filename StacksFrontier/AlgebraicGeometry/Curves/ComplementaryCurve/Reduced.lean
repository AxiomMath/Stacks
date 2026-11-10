module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A curve with at-worst-nodal singularities is reduced

Let `k` be a field and let `X` be a locally algebraic scheme over `k` whose singularities are at
worst nodal: every closed point of `X` is either a smooth point of `X → Spec k` or a node. Then
`X` is reduced.

The proof is local at closed points and splits along the two cases of the definition. At a
smooth point the local ring is regular, hence normal, hence reduced. At a node the completed
local ring of a point of `X_{k̄}` above it is the two-branch multicross ring, a subring of a
product of power series rings and therefore reduced; reducedness descends from the completion to
the local ring because the completion map of a Noetherian local ring is injective, and from
`X_{k̄}` to `X` because the projection is faithfully flat on local rings. Finally, a scheme whose
underlying space is Jacobson is reduced as soon as the local rings at its closed points are: on
an affine chart it suffices to check reducedness after localizing at maximal ideals, and those
localizations are local rings at closed points.

## Main results

* `Stacks.Curves.isReduced_multicross` — the multicross ring over a field is reduced.
* `Stacks.Curves.isReduced_stalk_of_hasMulticrossCompletion` — a local ring whose completion is
  the two-branch multicross ring is reduced.
* `Stacks.Curves.isReduced_stalk_of_smoothAt` — the local ring at a smooth point of a scheme
  over a field is reduced.
* `Stacks.Curves.isReduced_stalk_of_isNode` — the local ring at a node is reduced.
* `Stacks.Curves.isReduced_of_isReduced_stalk_closedPoints` — a scheme with Jacobson underlying
  space whose local rings at closed points are reduced is reduced.
* `Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities` — a locally algebraic scheme over a
  field with at-worst-nodal singularities is reduced.

## Implementation notes

The reducedness statement proved here is the part of Tag 0E37 that the contraction of a rational
tail (Tag 0E3H) actually uses, namely reducedness of `X` itself over the given field. No
`@[stacks 0E37]` attribute is placed on any declaration: the covering set of that tag also
contains the stronger geometric reducedness over every field extension and the Gorenstein
assertion, and the audit scanner keys on the bare four-character tag, so an attribute here would
render the whole tag formalized.

The node case is stated and proved at a point of `X` itself rather than after base change: the
definition of a node already quantifies over a point of `X_{k̄}` lying above it, so no comparison
of nodality before and after a field extension is needed.

## References

* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

/-- The multicross ring with two branches over a field is reduced, being a subring of a product
of power series rings. -/
theorem isReduced_multicross (K : Type u) [Field K] : IsReduced ↥(multicross K 2) := by
  have : IsReduced (Fin 2 → PowerSeries K) := inferInstance
  exact isReduced_of_injective (multicross K 2).subtype Subtype.val_injective

/-- If the completed local ring at a point of a locally Noetherian scheme over a field is the
two-branch multicross ring, then the local ring at that point is reduced. -/
theorem isReduced_stalk_of_hasMulticrossCompletion (K : Type u) [Field K] (Y : Scheme.{u})
    [Y.Over (Spec (.of K))] [IsLocallyNoetherian Y] (y : Y)
    (hy : HasMulticrossCompletion K Y y 2) :
    IsReduced (Y.presheaf.stalk y) := by
  let R := Y.presheaf.stalk y
  let kToStalk : K →+* R :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ Spec (.of K)).appTop ≫
      Y.presheaf.germ ⊤ y trivial).hom
  let _ : Algebra K R := kToStalk.toAlgebra
  let _ : Algebra K ↥(multicross K 2) := multicrossAlgebra K 2
  have : IsReduced ↥(multicross K 2) := isReduced_multicross K
  have : IsReduced (AdicCompletion (maximalIdeal R) R) :=
    isReduced_of_injective hy.some.toRingHom hy.some.injective
  exact isReduced_of_injective (algebraMap R (AdicCompletion (maximalIdeal R) R))
    (AdicCompletion.of_injective (maximalIdeal R) R)

/-- The local ring at a point at which a scheme is smooth over a field is reduced: it is regular,
hence normal, hence reduced. -/
theorem isReduced_stalk_of_smoothAt (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (x : X)
    (hx : InfinitesimalLifting.SmoothAt (X ↘ Spec (.of k)) x) :
    IsReduced (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, hs⟩ := hx
  let z : U.toScheme := ⟨x, hxU⟩
  have : Smooth ((X ↘ Spec (.of k)).resLE ⊤ U le_top) := hs
  have : Smooth (U.ι ≫ (X ↘ Spec (.of k))) := by
    rw [← Scheme.Hom.resLE_comp_ι (X ↘ Spec (.of k)) (U := ⊤) (V := U) (e := le_top)]
    infer_instance
  have : IsNormal U.toScheme :=
    isNormal_of_isRegular U.toScheme
      (isRegular_of_smooth_over_field (U.ι ≫ (X ↘ Spec (.of k))))
  have : IsReduced (U.toScheme.presheaf.stalk z) := inferInstance
  exact isReduced_of_injective (U.ι.stalkMap z).hom
    (asIso (U.ι.stalkMap z)).commRingCatIsoToRingEquiv.injective

/-- The local ring at a node of a locally algebraic scheme over a field is reduced. The local
ring at the ordinary double point of `X_{k̄}` above it is reduced because its completion is the
two-branch multicross ring, and reducedness descends along the faithfully flat local map induced
by the projection `X_{k̄} ⟶ X`. -/
theorem isReduced_stalk_of_isNode (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] (x : X)
    (hx : IsNode k X x) :
    IsReduced (X.presheaf.stalk x) := by
  let K := AlgebraicClosure k
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback (X ↘ Spec (.of k)) g : Scheme.{u})
  let p : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
  let _ : Y.Over (Spec (.of K)) := ⟨pullback.snd (X ↘ Spec (.of k)) g⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of K)) :=
    show LocallyOfFiniteType (pullback.snd (X ↘ Spec (.of k)) g) from inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  obtain ⟨-, y, hyx, hy⟩ := hx
  have : IsReduced (Y.presheaf.stalk y) :=
    isReduced_stalk_of_hasMulticrossCompletion K Y y hy.hasMulticrossCompletion
  have hflat : (p.stalkMap y).hom.Flat := Flat.stalkMap p y
  have hfaithful : (p.stalkMap y).hom.FaithfullyFlat := by
    algebraize [(p.stalkMap y).hom]
    exact (@Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ hflat (p.toLRSHom.prop y) :
      Module.FaithfullyFlat (X.presheaf.stalk (p.base y)) (Y.presheaf.stalk y))
  have hred : IsReduced (X.presheaf.stalk (p.base y)) :=
    isReduced_of_injective (p.stalkMap y).hom hfaithful.injective
  change p.base y = x at hyx
  rwa [hyx] at hred

/-- A scheme whose underlying topological space is Jacobson is reduced as soon as its local rings
at closed points are reduced. On an affine chart it suffices to check reducedness after
localizing at each maximal ideal, and such a localization is the local ring at a closed point. -/
@[ega "IV 10.10.4" "Reverse implication"]
theorem isReduced_of_isReduced_stalk_closedPoints (X : Scheme.{u}) [JacobsonSpace X]
    (h : ∀ x : X, IsClosed ({x} : Set X) → IsReduced (X.presheaf.stalk x)) :
    AlgebraicGeometry.IsReduced X := by
  apply +allowSynthFailures @AlgebraicGeometry.IsReduced.of_openCover X X.affineCover
  intro i
  let Y := X.affineCover.X i
  let f := X.affineCover.f i
  let R := Γ(Y, ⊤)
  have hR : IsReduced R := by
    apply isReduced_ofLocalizationMaximal R
    intro J hJ
    let y : Y := Y.isoSpec.inv ⟨J, hJ.isPrime⟩
    have hback : Y.isoSpec.hom (Y.isoSpec.inv (⟨J, hJ.isPrime⟩ : PrimeSpectrum R)) =
        (⟨J, hJ.isPrime⟩ : PrimeSpectrum R) :=
      TopCat.inv_hom_id_apply (Scheme.forgetToTop.mapIso Y.isoSpec) _
    have hy : IsClosed ({y} : Set Y) := by
      have hj : IsClosed ({(⟨J, hJ.isPrime⟩ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hJ
      have hh : IsClosed (Y.isoSpec.hom.base ⁻¹'
          ({(⟨J, hJ.isPrime⟩ : PrimeSpectrum R)} : Set (PrimeSpectrum R))) :=
        hj.preimage Y.isoSpec.hom.continuous
      convert hh using 1
      ext z
      simp only [Set.mem_singleton_iff]
      refine ⟨fun hz ↦ hz ▸ hback, fun hz ↦ ?_⟩
      change Y.isoSpec.hom z = (⟨J, hJ.isPrime⟩ : PrimeSpectrum R) at hz
      exact Y.isoSpec.hom.homeomorph.injective (hz.trans hback.symm)
    have hfy : IsClosed ({f.base y} : Set X) := by
      change y ∈ f.base ⁻¹' closedPoints X
      rwa [f.isOpenEmbedding.preimage_closedPoints]
    have : IsReduced (X.presheaf.stalk (f.base y)) := h (f.base y) hfy
    have : IsReduced (Y.presheaf.stalk y) :=
      isReduced_of_injective (asIso (f.stalkMap y)).inv.hom
        (asIso (f.stalkMap y)).symm.commRingCatIsoToRingEquiv.injective
    have htop : IsAffineOpen (⊤ : Y.Opens) := isAffineOpen_top Y
    let _ : Algebra R (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, by trivial⟩
    have hJstalk : (htop.primeIdealOf ⟨y, trivial⟩).asIdeal = J := by
      have hp : htop.primeIdealOf ⟨y, trivial⟩ = (⟨J, hJ.isPrime⟩ : PrimeSpectrum R) := by
        apply htop.fromSpec.isOpenEmbedding.injective
        rw [htop.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_top]
      exact congrArg PrimeSpectrum.asIdeal hp
    have : IsLocalization.AtPrime (Y.presheaf.stalk y) J := by
      simpa [hJstalk] using htop.isLocalization_stalk ⟨y, trivial⟩
    let e := IsLocalization.algEquiv J.primeCompl (Localization.AtPrime J) (Y.presheaf.stalk y)
    exact isReduced_of_injective e.toRingHom e.injective
  exact AlgebraicGeometry.isReduced_of_isAffine_isReduced Y

/-- A locally algebraic scheme over a field whose singularities are at worst nodal is reduced.
This is the reducedness half of Tag 0E37, in the form used by the contraction of a rational
tail. -/
theorem isReduced_of_hasAtWorstNodalSingularities (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hnodal : HasAtWorstNodalSingularities k X) :
    AlgebraicGeometry.IsReduced X := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  refine isReduced_of_isReduced_stalk_closedPoints X fun x hx ↦ ?_
  rcases hnodal x hx with hs | hn
  · exact isReduced_stalk_of_smoothAt k X x hs
  · exact isReduced_stalk_of_isNode k X x hn

end Stacks.Curves

end
