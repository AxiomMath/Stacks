module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Unramified.Properties

/-!
# Étale morphisms as flat G-unramified morphisms

A morphism of schemes is étale at a point precisely when it is flat and G-unramified there.
Consequently, a morphism is étale precisely when it is flat and G-unramified.

An étale ring map is G-unramified, which gives one direction at once. For the converse, flatness
and G-unramifiedness of the map on sections over a pair of affine neighbourhoods pass to the
localizations at the corresponding primes, where `Algebra.IsEtaleAt` applies; shrinking to a
basic open on which the map is étale produces the affine neighbourhood required by the pointwise
definition of étaleness.

## Main results

* `AlgebraicGeometry.etaleAt_iff_isFlatAt_and_gUnramifiedAt` characterizes étaleness at a point.
* `AlgebraicGeometry.etale_iff_flat_and_gUnramified` characterizes étale morphisms.

## Implementation notes

The first declaration is the pointwise assertion in the source, using flatness of the stalk map
as a morphism of ringed spaces. The second declaration is its global assertion, using the
corresponding predicates on morphisms of schemes.

## References

* [Stacks Project, Tag 02GV](https://stacks.math.columbia.edu/tag/02GV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism étale at a point is flat and G-unramified at that point. -/
public theorem isFlatAt_and_gUnramifiedAt_of_etaleAt {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (hEt : EtaleAt f x) :
    IsFlatAt (LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom) x ∧ GUnramifiedAt f x := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hEtUV⟩ := hEt
  let g := f.resLE V U hUV
  have hEtg : Etale g := by
    have : IsAffine U.toScheme := hU
    have : IsAffine V.toScheme := hV
    exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).2
      ((RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f V U hUV)).2 hEtUV)
  have hflat : (f.stalkMap x).hom.Flat :=
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff (Scheme.Hom.resLEStalkMap f hUV ⟨x, hxU⟩)).mp
      ((Flat.iff_flat_stalkMap g).mp inferInstance ⟨x, hxU⟩)
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Etale Γ(S, V) Γ(X, U) := RingHom.etale_algebraMap.mp hEtUV
  exact ⟨hflat, ⟨U, hU, hxU, V, hV, hUV, Algebra.GUnramified.of_etale⟩⟩

/-- A morphism flat and G-unramified at a point is étale at that point. -/
public theorem etaleAt_of_isFlatAt_of_gUnramifiedAt {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (hflat : IsFlatAt (LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom) x)
    (hGU : GUnramifiedAt f x) : EtaleAt f x := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hG⟩ := hGU
  let A := Γ(S, V)
  let B := Γ(X, U)
  let : Algebra A B := (f.appLE V U hUV).hom.toAlgebra
  let p : Ideal A := (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal
  let q : Ideal B := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have : p.IsPrime := inferInstance
  have : q.IsPrime := inferInstance
  have hcomap : q.comap (f.appLE V U hUV).hom = p :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU)
  have : q.LiesOver p := ⟨hcomap.symm⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  have hlocalFlat : (Localization.localRingHom p q (f.appLE V U hUV).hom hcomap.symm).Flat :=
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f V hV U hU hUV hxU)).mp hflat
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    RingHom.flat_algebraMap_iff.mp hlocalFlat
  have : Algebra.IsUnramifiedAt A q :=
    (Algebra.formallyUnramified_iff_forall (R := A) (A := B)).mp
      hG.formallyUnramified ⟨q, inferInstance⟩
  have : Module.Finite p.ResidueField q.ResidueField := inferInstance
  have : Algebra.IsSeparable p.ResidueField q.ResidueField := inferInstance
  have : Algebra.IsEtaleAt A q :=
    Algebra.IsEtaleAt.of_flat_of_map_eq_maximalIdeal p q
      ((Algebra.isUnramifiedAt_iff_map_eq A p q).mp ‹_›).2
  obtain ⟨r, hr, hEtaleAway⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) q
  let W : X.Opens := X.basicOpen r
  have hWU : W ≤ U := Scheme.basicOpen_le X r
  have hWV : W ≤ f ⁻¹ᵁ V := hWU.trans hUV
  have hxW : x ∈ W := by
    have hpre : hU.primeIdealOf ⟨x, hxU⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hr
    have hx' : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ∈ X.basicOpen r := hpre
    simpa [W, hU.fromSpec_primeIdealOf] using hx'
  let : Algebra B Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  have : IsLocalization.Away r Γ(X, W) := hU.isLocalization_basicOpen r
  let : Algebra A Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
  have : IsScalarTower A B Γ(X, W) := IsScalarTower.of_algebraMap_eq fun a =>
    (congrArg (fun φ : Γ(S, V) ⟶ Γ(X, W) => φ.hom a)
      (Scheme.Hom.appLE_map (f := f) (U := V) (V := U) hUV (homOfLE hWU).op)).symm
  have : Algebra.Etale A (Localization.Away r) := hEtaleAway
  have : Algebra.Etale A Γ(X, W) :=
    Algebra.Etale.of_equiv
      ((IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r)
        Γ(X, W)).restrictScalars A)
  exact ⟨W, hU.basicOpen r, hxW, V, hV, hWV,
    RingHom.etale_algebraMap.mpr ‹Algebra.Etale A Γ(X, W)›⟩

/-- A morphism of schemes is étale at a point if and only if it is flat and
G-unramified at that point. -/
@[stacks 02GV "at a point", ega "IV 17.6.2" "more general", sga "3 XI 1.4" "more general"]
public theorem etaleAt_iff_isFlatAt_and_gUnramifiedAt {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    EtaleAt f x ↔
      (IsFlatAt (LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom) x ∧
        GUnramifiedAt f x) :=
  ⟨isFlatAt_and_gUnramifiedAt_of_etaleAt, fun h => etaleAt_of_isFlatAt_of_gUnramifiedAt h.1 h.2⟩

/-- A morphism of schemes is étale if and only if it is flat and G-unramified. -/
@[stacks 02GV "globally", ega "IV 17.6.2", sga "3 XI 1.4" "more general"]
public theorem etale_iff_flat_and_gUnramified {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔ (Flat f ∧ GUnramified f) := by
  constructor
  · intro hEt
    exact ⟨inferInstance, ⟨fun x => ((etaleAt_iff_isFlatAt_and_gUnramifiedAt f x).mp
      ((etale_iff_forall_etaleAt f).mp hEt x)).2⟩⟩
  · rintro ⟨hflat, hGU⟩
    exact (etale_iff_forall_etaleAt f).mpr (fun x =>
      (etaleAt_iff_isFlatAt_and_gUnramifiedAt f x).mpr
        ⟨(Flat.iff_flat_stalkMap f).mp hflat x, hGU.gUnramifiedAt x⟩)

end AlgebraicGeometry

end
