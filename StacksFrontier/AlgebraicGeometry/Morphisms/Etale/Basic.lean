module

public import Mathlib.RingTheory.Unramified.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale morphisms are the smooth unramified morphisms

A morphism of schemes is étale at a point if and only if it is both smooth and unramified at that
point.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.etaleAt_iff_smoothAt_and_unramifiedAt` characterizes étaleness at a point in
  terms of smoothness and unramifiedness there.

## Implementation notes

The three pointwise conditions are the predicates for smoothness, unramifiedness and étaleness at
a point. Étaleness of a ring map is formal unramifiedness together with smoothness, so the forward
direction is a matter of splitting that conjunction; the converse has to reconcile two
independently chosen pairs of affine neighbourhoods, and does so by passing through formal
unramifiedness of the stalk map, which is neighbourhood-independent. The auxiliary lemma
`AlgebraicGeometry.formallyUnramified_stalkMap_iff` expresses that condition as membership of the
corresponding prime in `Algebra.unramifiedLocus`, which is where the shrinking to a basic open
takes place.

## References

* [Stacks Project, Tag 02GK](https://stacks.math.columbia.edu/tag/02GK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Formal unramifiedness of the stalk map at a point is membership of the corresponding prime in
the unramified locus of the map on sections over affine neighbourhoods. -/
public lemma formallyUnramified_stalkMap_iff
    {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X} (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyUnramified ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.unramifiedLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyUnramified_algebraMap]
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) := h
    exact Algebra.FormallyUnramified.comp Γ(Y, U) (Localization.AtPrime p) (Localization.AtPrime q)
  · have : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime q) := h
    exact Algebra.FormallyUnramified.of_restrictScalars Γ(Y, U)
      (Localization.AtPrime p) (Localization.AtPrime q)

/-- A morphism that is smooth on an affine chart around `x` and whose stalk map at `x` is formally
unramified is étale at `x`. -/
private theorem etaleAt_of_smooth_appLE_of_formallyUnramified_stalkMap {X S : Scheme.{u}}
    (f : X ⟶ S) {x : X} {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U) (hs : (f.appLE V U e).hom.Smooth)
    (hstalk : (f.stalkMap x).hom.FormallyUnramified) :
    EtaleAt f x := by
  simp only [EtaleAt]
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have : Algebra.Smooth Γ(S, V) Γ(X, U) := RingHom.smooth_algebraMap.mp hs
  have : Algebra.IsUnramifiedAt Γ(S, V) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    (formallyUnramified_stalkMap_iff V hV U hU e hx).mp hstalk
  obtain ⟨r, hr, hur⟩ := Algebra.exists_unramified_of_isUnramifiedAt
    (R := Γ(S, V)) (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let W : X.Opens := X.basicOpen r
  let hW : W ≤ f ⁻¹ᵁ V := (X.basicOpen_le r).trans e
  refine ⟨W, hU.basicOpen r, ?_, V, hV, hW, ?_⟩
  · show (⟨x, hx⟩ : U).1 ∈ X.basicOpen r
    rw [← hU.fromSpec_primeIdealOf ⟨x, hx⟩]
    show hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r
    rw [hU.fromSpec_preimage_basicOpen]
    exact hr
  · have := hU.isLocalization_basicOpen r
    let : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W hW).hom.toAlgebra
    have : Algebra.Smooth Γ(S, V) (Localization.Away r) := ⟨inferInstance, inferInstance⟩
    have he : (algebraMap Γ(S, V) (Localization.Away r)).Etale :=
      (RingHom.etale_iff_formallyUnramified_and_smooth _).mpr
        ⟨RingHom.formallyUnramified_algebraMap.mpr hur.formallyUnramified,
          RingHom.smooth_algebraMap.mpr inferInstance⟩
    convert! RingHom.Etale.respectsIso.1 _
      (IsLocalization.algEquiv (.powers r) _ Γ(X, W)).toRingEquiv he
    ext
    dsimp
    rw [IsScalarTower.algebraMap_apply Γ(S, V) Γ(X, U) (Localization _),
      (IsLocalization.algEquiv (.powers r) _ Γ(X, W)).commutes]
    exact DFunLike.congr_fun
      (CommRingCat.hom_ext_iff.mp (f.appLE_map e (homOfLE (X.basicOpen_le r)).op).symm) _

/-- A morphism of schemes is étale at a point if and only if it is smooth and
unramified at that point. -/
@[stacks 02GK, ega "IV 17.6.2" "more general", sga "3 XI 1.4" "more general"]
public theorem etaleAt_iff_smoothAt_and_unramifiedAt {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    EtaleAt f x ↔
      (InfinitesimalLifting.SmoothAt f x ∧ UnramifiedAt f x) := by
  rw [InfinitesimalLifting.smoothAt_iff_exists_affine]
  constructor
  · simp only [EtaleAt, UnramifiedAt]
    rintro ⟨U, hU, hxU, V, hV, e, h⟩
    have hs := (RingHom.etale_iff_formallyUnramified_and_smooth _).mp h |>.2
    let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    have : Algebra.Smooth Γ(S, V) Γ(X, U) := RingHom.smooth_algebraMap.mp hs
    have hu : Algebra.Unramified Γ(S, V) Γ(X, U) :=
      ⟨RingHom.formallyUnramified_algebraMap.mp h.formallyUnramified, inferInstance⟩
    exact ⟨⟨U, V, hU, hV, hxU, e, hs⟩, ⟨U, hU, hxU, V, hV, e, hu⟩⟩
  · simp only [UnramifiedAt]
    rintro ⟨⟨Us, Vs, hUs, hVs, hxs, es, hs⟩, ⟨Uu, hUu, hxu, Vu, hVu, eu, hu⟩⟩
    refine etaleAt_of_smooth_appLE_of_formallyUnramified_stalkMap f hUs hVs es hxs hs ?_
    let : Algebra Γ(S, Vu) Γ(X, Uu) := (f.appLE Vu Uu eu).hom.toAlgebra
    have : Algebra.FormallyUnramified Γ(S, Vu) Γ(X, Uu) := hu.formallyUnramified
    exact (formallyUnramified_stalkMap_iff Vu hVu Uu hUu eu hxu).mpr
      (show hUu.primeIdealOf ⟨x, hxu⟩ ∈ Algebra.unramifiedLocus Γ(S, Vu) Γ(X, Uu) from
        Algebra.FormallyUnramified.comp Γ(S, Vu) Γ(X, Uu) _)

end AlgebraicGeometry
