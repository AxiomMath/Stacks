module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.EtaleSiteOfFppfSite
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Smooth.Reduced

/-!
# Geometrically reduced algebraic spaces over a field

Let `k` be a field and let `X` be an algebraic space over `k`. Then `X` is *geometrically
reduced at* a point `x` of `X` when the étale local ring of `X` at a geometric point above
`x` is geometrically reduced as a `k`-algebra, and *geometrically reduced* when this holds at
every point.

The `k`-algebra structure on the étale local ring is the canonical one: a constant function
on the base pulls back to every étale chart, and the germs of those pullbacks agree, so they
define a single element of the local ring. That map is constructed here, for an arbitrary
commutative base ring, together with the characterization which pins it down.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseMap` pulls a global function on an affine base scheme
  back to a small étale chart.
* `AlgebraicGeometry.Space.baseToEtaleLocalRing` is the canonical ring map from the base ring
  to the étale local ring at a geometric point, together with its characterization by germs.
* `AlgebraicGeometry.Space.IsGeometricallyReducedAt` and
  `AlgebraicGeometry.Space.IsGeometricallyReduced` are geometric reducedness at a point and
  over the field.

Both conditions are étale local: they can be tested on one, or on every, étale scheme chart.

## Main results

* `AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_common_refinement`: two small étale
  neighbourhoods of a geometric point are refined by a third.
* `AlgebraicGeometry.Space.chartBaseMap_natural` and
  `AlgebraicGeometry.Space.chartBaseMap_germ_eq`: the pullbacks of a constant function are
  compatible with refinement, hence have a common germ.
* `AlgebraicGeometry.Space.isGeometricallyReducedAt_iff_exists_etaleChart` and
  `AlgebraicGeometry.Space.isGeometricallyReducedAt_iff_forall_etaleChart` are Stacks 0DMR:
  geometric reducedness at a point is geometric reducedness of some, equivalently of every,
  étale scheme neighbourhood at a point above it.
* `AlgebraicGeometry.Space.isGeometricallyReduced_iff_exists_surjective_etaleChart` and
  `AlgebraicGeometry.Space.isGeometricallyReduced_iff_forall_etaleChart` are Stacks 0DMS, the
  same statement for the whole space and a surjective, respectively arbitrary, étale scheme
  chart.

## Implementation notes

The base map is specified rather than merely constructed: `baseToEtaleLocalRing` returns the
ring homomorphism bundled with the statement that it is the germ of the pullback of the
constant function on *every* small étale neighbourhood, so a client never depends on the
neighbourhood used to build it. Its construction uses one such neighbourhood, obtained by
refining `AlgebraicGeometry.Space.EtaleNeighborhood.self` to a scheme chart, and the common
refinement lemma to compare any two.

Geometric reducedness at a point quantifies over *all* geometric points above it rather than
choosing one, so no choice enters the predicate. That this agrees with the condition at a
single geometric point above `x` is part of Stacks 0DMR, which is proved here: both the
one-chart and the every-chart criterion are obtained from the same comparison of the étale
local ring with the local ring of a chart, so the universally quantified form of the
definition is matched against each of them in turn.

Both predicates are abbreviations, so the pointwise test and the underlying algebra
condition are directly available to clients.

The three conditions of Stacks 0DMR and of Stacks 0DMS are formalized as the two equivalences
(1) ⟺ (2) and (1) ⟺ (3), whose conjunction is the source's statement. An étale neighbourhood
`(U, u) → (X, x)` with `U` a scheme is an object `U` of the big fppf site together with an
étale `a : h_U ⟶ X` and a field-valued point of `h_U` whose class maps to `x`; the point `u`
is the scheme point `AlgebraicGeometry.Space.schemePoint` that field-valued point selects.

The ring-theoretic heart of Stacks 0DMR is that a local `k`-algebra is geometrically reduced
over `k` exactly when its strict henselization is. Only base change to an algebraic closure
of `k` is needed for this, since `Algebra.IsGeometricallyReduced` over a field is reducedness
after that one base change; the source argues with an arbitrary extension because it uses the
definition of Stacks 030S instead.

## References

* [Stacks Project, Tag 0DMQ](https://stacks.math.columbia.edu/tag/0DMQ)
* [Stacks Project, Tag 0DMR](https://stacks.math.columbia.edu/tag/0DMR)
* [Stacks Project, Tag 0DMS](https://stacks.math.columbia.edu/tag/0DMS)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Space

/-- Two small étale neighbourhoods of a geometric point are refined by a third: the
corresponding étale neighbourhoods have a common refinement by Stacks 04JW, that refinement
is in turn refined by a scheme chart, and
`AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale` is fully faithful, so the two
comparison morphisms come from morphisms of small étale neighbourhoods. -/
theorem SmallEtaleNeighborhood.exists_common_refinement {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {x : GeometricPoint B S hS F}
    (U V : SmallEtaleNeighborhood x) :
    ∃ W : SmallEtaleNeighborhood x, Nonempty ((W ⟶ U) × (W ⟶ V)) := by
  obtain ⟨W, ⟨fU, fV⟩⟩ := EtaleNeighborhood.exists_common_refinement
    ((EtaleNeighborhood.ofSmallEtale hF x).obj U)
    ((EtaleNeighborhood.ofSmallEtale hF x).obj V)
  obtain ⟨W', ⟨g⟩⟩ := EtaleNeighborhood.exists_smallEtaleNeighborhood_refinement W
  exact ⟨W', ⟨(EtaleNeighborhood.ofSmallEtale hF x).preimage (g ≫ fU),
    (EtaleNeighborhood.ofSmallEtale hF x).preimage (g ≫ fV)⟩⟩

section BaseMap

variable (R : Type u) [CommRing R] (B : BigFppfSite.{u})
  (hR : B.Contains (Spec (.of R)))
  (X : (BigFppfOver B (Spec (.of R)) hR)ᵒᵖ ⥤ Type u)
  (x : GeometricPoint B (Spec (.of R)) hR X)

/-- The pullback of a global function on the affine base scheme `Spec R` to the chart of a
small étale neighbourhood of a geometric point. -/
noncomputable def chartBaseMap (U : SmallEtaleNeighborhood x) :
    R →+* (structurePresheaf B (Spec (.of R)) hR X).obj (Opposite.op U.chart) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫
    Scheme.Γ.map (B.inclusion.map
      (((SmallEtale.toOver B (Spec (.of R)) hR X).obj U.chart).hom)).op).hom

/-- The pullbacks of a global function on the base to two small étale neighbourhoods agree
after restriction along a refinement. -/
theorem chartBaseMap_natural {U V : SmallEtaleNeighborhood x} (f : U ⟶ V) (a : R) :
    (structurePresheaf B (Spec (.of R)) hR X).map f.hom.op
      (chartBaseMap R B hR X x V a) = chartBaseMap R B hR X x U a := by
  have hbase : B.inclusion.map (f.hom.hom.left.left ≫ V.chart.obj.left.hom) =
      B.inclusion.map U.chart.obj.left.hom := by
    simpa only [Functor.map_comp] using congrArg B.inclusion.map f.hom.hom.left.w
  let gV := (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map
    (B.inclusion.map V.chart.obj.left.hom).op
  let gU := (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map
    (B.inclusion.map U.chart.obj.left.hom).op
  have hspec : B.inclusion.obj (B.obj hR) = Spec (.of R) := rfl
  have hpaths : (B.inclusion.map V.chart.obj.left.hom).op ≫
        (B.inclusion.map f.hom.hom.left.left).op =
      (B.inclusion.map U.chart.obj.left.hom).op := by
    rw [← op_comp, ← Functor.map_comp, hbase]
  have hcomp : gV ≫ Scheme.Γ.map (B.inclusion.map f.hom.hom.left.left).op = gU := by
    simpa [gV, gU, Functor.map_comp, hspec] using
      congrArg (fun q => (Scheme.ΓSpecIso (.of R)).inv ≫ q) (congrArg Scheme.Γ.map hpaths)
  change (gV ≫ Scheme.Γ.map (B.inclusion.map f.hom.hom.left.left).op) a = gU a
  exact congrArg (fun q : CommRingCat.of R ⟶ _ => q a) hcomp

/-- The pullbacks of a global function on the base to two small étale neighbourhoods have the
same germ in the étale local ring, as soon as one neighbourhood refines the other. -/
theorem chartBaseMap_germ_eq {U V : SmallEtaleNeighborhood x} (f : U ⟶ V) (a : R) :
    etaleLocalRingGerm B (Spec (.of R)) hR X x (Opposite.op U)
        (chartBaseMap R B hR X x U a) =
      etaleLocalRingGerm B (Spec (.of R)) hR X x (Opposite.op V)
        (chartBaseMap R B hR X x V a) := by
  let D := SmallEtaleNeighborhood.sections
    (x := x) (liftedStructurePresheaf B (Spec (.of R)) hR X)
  change (CategoryTheory.Limits.colimit.ι D (Opposite.op U)).hom
      (ULift.up (chartBaseMap R B hR X x U a)) =
    (CategoryTheory.Limits.colimit.ι D (Opposite.op V)).hom
      (ULift.up (chartBaseMap R B hR X x V a))
  simpa [D, SmallEtaleNeighborhood.sections, liftedStructurePresheaf, Functor.comp_map,
    RingHom.ulift_apply, chartBaseMap_natural R B hR X x f a] using
    congrArg (fun q => q.hom (ULift.up (chartBaseMap R B hR X x V a)))
      (CategoryTheory.Limits.colimit.w D (Opposite.op f))

/-- The canonical ring homomorphism from the base ring to the étale local ring of an
algebraic space over `Spec R` at a geometric point, specified by the property that it sends
an element of `R` to the germ of the pullback of the corresponding constant function on every
small étale neighbourhood of the point. -/
noncomputable def baseToEtaleLocalRing (hX : IsAlgebraicSpace B (Spec (.of R)) hR X) :
    {φ : R →+* etaleLocalRing B (Spec (.of R)) hR X x //
      ∀ (a : R) (U : (SmallEtaleNeighborhood x)ᵒᵖ),
        φ a = etaleLocalRingGerm B (Spec (.of R)) hR X x U
          (chartBaseMap R B hR X x U.unop a)} := by
  let U₀ := (EtaleNeighborhood.exists_smallEtaleNeighborhood_refinement
    (EtaleNeighborhood.self hX x)).choose
  refine ⟨(etaleLocalRingGerm B (Spec (.of R)) hR X x (Opposite.op U₀)).comp
    (chartBaseMap R B hR X x U₀), fun a U => ?_⟩
  obtain ⟨W, ⟨f₀W, fWU⟩⟩ :=
    SmallEtaleNeighborhood.exists_common_refinement hX U₀ U.unop
  exact (chartBaseMap_germ_eq R B hR X x f₀W a).symm.trans
    (chartBaseMap_germ_eq R B hR X x fWU a)

end BaseMap

/-- **Stacks 0DMQ, part (1).** An algebraic space `X` over a field `k` is *geometrically
reduced at* a point `x` of `X` when the étale local ring of `X` at every geometric point
above `x` is geometrically reduced as a `k`-algebra. -/
@[stacks 0DMQ "part (1): at a point"]
abbrev IsGeometricallyReducedAt (k : Type u) [Field k] (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (x : points B (Spec (.of k)) hk X) : Prop :=
  ∀ xbar : GeometricPoint B (Spec (.of k)) hk X, xbar.LiesOver x →
    letI : Algebra k (etaleLocalRing B (Spec (.of k)) hk X xbar) :=
      (baseToEtaleLocalRing k B hk X xbar hX).val.toAlgebra
    Algebra.IsGeometricallyReduced k (etaleLocalRing B (Spec (.of k)) hk X xbar)

/-- **Stacks 0DMQ, part (2).** An algebraic space over a field `k` is *geometrically
reduced* when it is geometrically reduced at every one of its points. -/
@[stacks 0DMQ "part (2): over the field"]
abbrev IsGeometricallyReduced (k : Type u) [Field k] (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) : Prop :=
  ∀ x : points B (Spec (.of k)) hk X, IsGeometricallyReducedAt k B hk X hX x


/-! ### Geometric reducedness of a strict henselization -/

section Henselization

open scoped TensorProduct

open IsLocalRing in
/-- An ind-étale algebra over a reduced ring is reduced: a nilpotent element of the algebra is
the image of a root of `X ^ n` in an étale algebra over the base, and an étale algebra over a
reduced ring is reduced because it is smooth over it. -/
private theorem isReduced_of_ind_etale {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [_root_.IsReduced R] (h : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R A)) :
    _root_.IsReduced A := by
  rw [CommAlgCat.ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk,
    CommRingCat.ind_under_iff_exists_factorization _ (fun _ he ↦ he.finitePresentation)] at h
  constructor
  rintro x ⟨n, hn⟩
  let p : Polynomial R := Polynomial.X ^ n
  let g : AdjoinRoot p →ₐ[R] A :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId R A) x (by simpa [p] using hn)
  have hp : (algebraMap R (AdjoinRoot p)).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  let P : Under (CommRingCat.of R) := Under.mk (CommRingCat.ofHom (algebraMap R (AdjoinRoot p)))
  let Λ : Under (CommRingCat.of R) := Under.mk (CommRingCat.ofHom (algebraMap R A))
  let φ : P ⟶ Λ := Under.homMk (CommRingCat.ofHom g) (by ext r; exact g.commutes r)
  obtain ⟨W, a, b, hab, ha⟩ := h P hp φ
  let : Algebra R W.right := W.hom.hom.toAlgebra
  have : Algebra.Etale R W.right := ha
  have hW : _root_.IsReduced W.right := Algebra.isReduced_of_smooth R W.right
  have hroot : (AdjoinRoot.root p) ^ n = 0 := by simpa [p] using AdjoinRoot.eval₂_root p
  have hy : a.right.hom (AdjoinRoot.root p) = 0 :=
    IsReduced.eq_zero _ ⟨n, by rw [← map_pow, hroot, map_zero]⟩
  have hbx : b.right.hom (a.right.hom (AdjoinRoot.root p)) = x := by
    have hcomp := congrArg (fun f : P ⟶ Λ ↦ f.right.hom (AdjoinRoot.root p)) hab
    change b.right.hom (a.right.hom (AdjoinRoot.root p)) = g (AdjoinRoot.root p) at hcomp
    exact hcomp.trans (AdjoinRoot.liftAlgHom_root (p := p) (Algebra.ofId R A) x _)
  rw [← hbx, hy, map_zero]

/-- Geometric reducedness over a field transports along an isomorphism of algebras. -/
private theorem isGeometricallyReduced_congr {k : Type u} [Field k] {A : Type v} {A' : Type w}
    [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] (e : A ≃ₐ[k] A') :
    Algebra.IsGeometricallyReduced k A ↔ Algebra.IsGeometricallyReduced k A' := by
  rw [Algebra.isGeometricallyReduced_field_iff, Algebra.isGeometricallyReduced_field_iff]
  let E := Algebra.TensorProduct.congr (AlgEquiv.refl (R := k) (A₁ := AlgebraicClosure k)) e
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : _root_.IsReduced (AlgebraicClosure k ⊗[k] A) := h
    exact isReduced_of_injective E.symm.toRingEquiv E.symm.injective
  · have : _root_.IsReduced (AlgebraicClosure k ⊗[k] A') := h
    exact isReduced_of_injective E.toRingEquiv E.injective

/-- Geometric reducedness over a field depends only on the ring homomorphism from the field. -/
private theorem isGeometricallyReduced_toAlgebra_congr {k : Type u} [Field k] {A : Type v}
    [CommRing A] {φ ψ : k →+* A} (h : ∀ a, φ a = ψ a) :
    (letI := φ.toAlgebra; Algebra.IsGeometricallyReduced k A) ↔
      (letI := ψ.toAlgebra; Algebra.IsGeometricallyReduced k A) := by
  rw [show φ = ψ from RingHom.ext h]

open IsLocalRing in
/-- **The ring-theoretic content of Stacks 0DMR.** A local `k`-algebra is geometrically reduced
over `k` exactly when its strict henselization is: an algebraic closure `k̄` of `k` turns the
ind-étale map `A → A^{sh}` into the ind-étale map `k̄ ⊗ A → k̄ ⊗ A^{sh}`, which transports
reducedness forwards, and that map is faithfully flat, which transports it back. -/
private theorem isGeometricallyReduced_strictHenselization_iff
    (k A : Type u) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep] (T : HenselizationTower A κsep)
    [Algebra k T.strictHenselization] [IsScalarTower k A T.strictHenselization] :
    Algebra.IsGeometricallyReduced k A ↔
      Algebra.IsGeometricallyReduced k T.strictHenselization := by
  have hind : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A T.strictHenselization) :=
    IsHenselization.ind_etale_of_universe_le (R := A) (L := κsep) (Rh := T.strictHenselization)
  let K := AlgebraicClosure k
  let : Algebra K (K ⊗[k] A) := Algebra.TensorProduct.leftAlgebra
  let : Algebra K (K ⊗[k] T.strictHenselization) := Algebra.TensorProduct.leftAlgebra
  let : Algebra A (K ⊗[k] A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra T.strictHenselization (K ⊗[k] T.strictHenselization) :=
    Algebra.TensorProduct.rightAlgebra
  let φ : (K ⊗[k] A) →ₐ[K] (K ⊗[k] T.strictHenselization) :=
    Algebra.TensorProduct.map (AlgHom.id K K)
      (IsScalarTower.toAlgHom k A T.strictHenselization)
  let : Algebra A (K ⊗[k] T.strictHenselization) :=
    (φ.toRingHom.comp (algebraMap A (K ⊗[k] A))).toAlgebra
  let : Algebra (K ⊗[k] A) (K ⊗[k] T.strictHenselization) := φ.toRingHom.toAlgebra
  have : IsScalarTower A (K ⊗[k] A) (K ⊗[k] T.strictHenselization) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A T.strictHenselization (K ⊗[k] T.strictHenselization) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change φ ((1 : K) ⊗ₜ[k] a) = (1 : K) ⊗ₜ[k] (algebraMap A T.strictHenselization a)
      simp [φ, Algebra.TensorProduct.map_tmul])
  have : IsScalarTower k T.strictHenselization (K ⊗[k] T.strictHenselization) :=
    Algebra.TensorProduct.right_isScalarTower
  have : IsScalarTower k A (K ⊗[k] T.strictHenselization) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change (algebraMap k K a) ⊗ₜ[k] (1 : T.strictHenselization) =
        φ ((1 : K) ⊗ₜ[k] (algebraMap k A a))
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
      simp [φ, Algebra.TensorProduct.map_tmul,
        IsScalarTower.algebraMap_apply k A T.strictHenselization])
  have : IsScalarTower k (K ⊗[k] A) (K ⊗[k] T.strictHenselization) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change (algebraMap k K a) ⊗ₜ[k] (1 : T.strictHenselization) =
        φ ((algebraMap k K a) ⊗ₜ[k] (1 : A))
      exact (φ.commutes _).symm)
  have : IsScalarTower K (K ⊗[k] A) (K ⊗[k] T.strictHenselization) :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (φ.commutes a).symm)
  have : Algebra.IsPushout A (K ⊗[k] A) T.strictHenselization
      (K ⊗[k] T.strictHenselization) := by
    have htop : Algebra.IsPushout k T.strictHenselization K
        (K ⊗[k] T.strictHenselization) :=
      (TensorProduct.isPushout (R := k) (S := K) (T := T.strictHenselization)).symm
    exact ((Algebra.IsPushout.comp_iff k A (R' := K) (S' := K ⊗[k] A)
      (T := T.strictHenselization) (T' := K ⊗[k] T.strictHenselization)).mp htop).symm
  have hindK : (CommAlgCat.etale.{u} (K ⊗[k] A)).ind.{u}
      (CommAlgCat.of (K ⊗[k] A) (K ⊗[k] T.strictHenselization)) :=
    CommAlgCat.ind_etale_of_isPushout A (K ⊗[k] A) T.strictHenselization
      (K ⊗[k] T.strictHenselization) hind
  rw [Algebra.isGeometricallyReduced_field_iff, Algebra.isGeometricallyReduced_field_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : _root_.IsReduced (K ⊗[k] A) := h
    exact isReduced_of_ind_etale hindK
  · have : _root_.IsReduced (K ⊗[k] T.strictHenselization) := h
    have : Module.FaithfullyFlat A T.strictHenselization :=
      IsHenselization.faithfullyFlat (R := A) (L := κsep)
    have hff : Module.FaithfullyFlat (K ⊗[k] A) (K ⊗[k] T.strictHenselization) :=
      Module.FaithfullyFlat.of_linearEquiv (K ⊗[k] A)
        ((K ⊗[k] A) ⊗[A] T.strictHenselization)
        ((Algebra.IsPushout.equiv A (K ⊗[k] A) T.strictHenselization
          (K ⊗[k] T.strictHenselization)).symm.toLinearEquiv)
    exact RingHom.FaithfullyFlat.isReduced (R := K ⊗[k] A)
      (S := K ⊗[k] T.strictHenselization) (φ := algebraMap _ _) hff

open IsLocalRing in
/-- Geometric reducedness of a local `k`-algebra, transported along a ring isomorphism from its
strict henselization: the two structure maps from `k` are given as ring homomorphisms, so that
the statement can be applied to the canonically constructed algebra structures of a stalk and
of an étale local ring, which are not instances. -/
private theorem isGeometricallyReduced_iff_of_strictHenselizationEquiv
    (k A : Type u) [Field k] [CommRing A] [IsLocalRing A] (φ : k →+* A)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep] (T : HenselizationTower A κsep)
    {L : Type v} [CommRing L] (e : T.strictHenselization ≃+* L) (ψ : k →+* L)
    (he : ∀ a : k, e (algebraMap A T.strictHenselization (φ a)) = ψ a) :
    (letI := φ.toAlgebra; Algebra.IsGeometricallyReduced k A) ↔
      (letI := ψ.toAlgebra; Algebra.IsGeometricallyReduced k L) := by
  let : Algebra k A := φ.toAlgebra
  let : Algebra k T.strictHenselization :=
    ((algebraMap A T.strictHenselization).comp φ).toAlgebra
  have : IsScalarTower k A T.strictHenselization := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra k L := ψ.toAlgebra
  exact (isGeometricallyReduced_strictHenselization_iff k A κsep T).trans
    (isGeometricallyReduced_congr (AlgEquiv.ofRingEquiv (f := e) he))

end Henselization

/-! ### Reducedness on étale scheme charts -/

section Charts

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
  (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)

open IsLocalRing in
/-- The point of the scheme underlying a small étale neighbourhood of a geometric point at
which the local ring of the chart is taken: the image of the closed point of the field
spectrum defining the geometric point. -/
private noncomputable abbrev chartSchemePoint {x : GeometricPoint B (Spec (.of k)) hk X}
    (V : SmallEtaleNeighborhood x) : neighborhoodChartScheme V :=
  (chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)

open IsLocalRing in
/-- **The chart comparison behind Stacks 0DMR.** The étale local ring of `X` at a geometric
point is geometrically reduced over `k` exactly when a scheme chart carrying that geometric
point is geometrically reduced at the induced point: the étale local ring is the strict
henselization of the local ring of the chart (Stacks 04KF), geometric reducedness of a scheme
at a point is geometric reducedness of its local ring (Stacks 035W), and geometric reducedness
is unchanged by strict henselization. -/
private theorem isGeometricallyReduced_etaleLocalRing_iff_chart
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (x : GeometricPoint B (Spec (.of k)) hk X) (V : SmallEtaleNeighborhood x) :
    (letI : Algebra k (etaleLocalRing B (Spec (.of k)) hk X x) :=
      (baseToEtaleLocalRing k B hk X x hX).val.toAlgebra
     Algebra.IsGeometricallyReduced k (etaleLocalRing B (Spec (.of k)) hk X x)) ↔
      _root_.AlgebraicGeometry.IsGeometricallyReducedAt
        (B.inclusion.map V.chart.obj.left.hom)
        (schemePoint B (Spec (.of k)) hk V.chart.obj.left
          (chartFieldValuedPoint (B := B) (S := Spec (.of k)) (hS := hk) (F := X) V)) := by
  have hE : (bigEtaleSiteOfFppfSite B).Contains (neighborhoodChartScheme V) :=
    V.chart.obj.left.left.property
  let b : k →+* Γ(neighborhoodChartScheme V, ⊤) := chartBaseMap k B hk X x V
  let φ : k →+* ((neighborhoodChartScheme V).presheaf.stalk (chartSchemePoint k B hk X V)) :=
    ((neighborhoodChartScheme V).presheaf.germ ⊤ (chartSchemePoint k B hk X V)
      trivial).hom.comp b
  have step : (let := φ.toAlgebra; Algebra.IsGeometricallyReduced k
        ((neighborhoodChartScheme V).presheaf.stalk (chartSchemePoint k B hk X V))) ↔
      (let := (baseToEtaleLocalRing k B hk X x hX).val.toAlgebra;
        Algebra.IsGeometricallyReduced k (etaleLocalRing B (Spec (.of k)) hk X x)) :=
    isGeometricallyReduced_iff_of_strictHenselizationEquiv k _ φ _ (henselizationTower _ _)
      (strictHenselizationEquivEtaleLocalRing hX V (bigEtaleSiteOfFppfSite B) hE
        (henselizationTower _ _))
      (baseToEtaleLocalRing k B hk X x hX).val
      (fun a ↦ (strictHenselizationEquivEtaleLocalRing_germ hX V (bigEtaleSiteOfFppfSite B) hE
        (henselizationTower _ _) (b a)).trans
          ((baseToEtaleLocalRing k B hk X x hX).property a (Opposite.op V)).symm)
  refine step.symm.trans (Iff.trans (isGeometricallyReduced_toAlgebra_congr fun a ↦ ?_)
    (_root_.AlgebraicGeometry.isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk
      (B.inclusion.map V.chart.obj.left.hom) (chartSchemePoint k B hk X V)).symm)
  exact ((B.inclusion.map V.chart.obj.left.hom).germ_stalkMap_apply ⊤
    (chartSchemePoint k B hk X V) trivial ((Scheme.ΓSpecIso (.of k)).inv a)).symm

/-- **Stacks 0DMR, from a chart whose point lies over `x`.** Geometric reducedness of the étale
local ring at a geometric point `x̄` of `X` is geometric reducedness of any étale scheme chart
at any field-valued point above the image of `x̄`: by Stacks 05VN the geometric point lifts to
the chart, so the chart is a small étale neighbourhood of it, and by Stacks 03BU the lift and
the given field-valued point select the same scheme point. -/
private theorem isGeometricallyReduced_etaleLocalRing_iff_chart_of_liesOver
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X)
    (ha : IsEtale B (Spec (.of k)) hk a)
    (p : FieldValuedPoint B (Spec (.of k)) hk (yoneda.obj U))
    (x : GeometricPoint B (Spec (.of k)) hk X)
    (hp : pointsMap B (Spec (.of k)) hk (yoneda.obj U) a
      (p.class B (Spec (.of k)) hk (yoneda.obj U)) = x.image) :
    (letI : Algebra k (etaleLocalRing B (Spec (.of k)) hk X x) :=
      (baseToEtaleLocalRing k B hk X x hX).val.toAlgebra
     Algebra.IsGeometricallyReduced k (etaleLocalRing B (Spec (.of k)) hk X x)) ↔
      _root_.AlgebraicGeometry.IsGeometricallyReducedAt (B.inclusion.map U.hom)
        (schemePoint B (Spec (.of k)) hk U p) := by
  have ha' : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf a :=
    (isEtale_iff_presheaf_of_yoneda B (Spec (.of k)) hk a).mp ha
  obtain ⟨y, hy, hmap⟩ := exists_geometricPoint_lift_of_isEtale B (Spec (.of k)) hk
    (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk U) hX a ha x
    (p.class B (Spec (.of k)) hk (yoneda.obj U)) hp
  obtain rfl : (⟨FieldValuedPoint.map B (Spec (.of k)) hk (yoneda.obj U) a y.val, y.property⟩ :
      GeometricPoint B (Spec (.of k)) hk X) = x := Subtype.ext hmap
  rw [← schemePoint_eq_of_class_eq B (Spec (.of k)) hk U y.val p hy]
  exact isGeometricallyReduced_etaleLocalRing_iff_chart k B hk X hX
    ⟨FieldValuedPoint.map B (Spec (.of k)) hk (yoneda.obj U) a y.val, y.property⟩
    ⟨⟨CostructuredArrow.mk a, ha'⟩, y.val.value, rfl⟩

/-- An algebraic space has a surjective étale morphism from a scheme chart. -/
private theorem exists_surjective_etale_chart
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    ∃ (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X),
      IsSurjective B (Spec (.of k)) hk a ∧ IsEtale B (Spec (.of k)) hk a := by
  obtain ⟨U, a, hsurj, ha⟩ := hX.exists_atlas
  exact ⟨U, a, (surjective_iff_surjective_pointsMap B (Spec (.of k)) hk X hX U a).mp hsurj,
    (isEtale_iff_presheaf_of_yoneda B (Spec (.of k)) hk a).mpr ha⟩

/-- Every point of an algebraic space lies under a field-valued point of some étale chart. -/
private theorem exists_etale_chart_point
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (x : points B (Spec (.of k)) hk X) :
    ∃ (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X),
      IsEtale B (Spec (.of k)) hk a ∧
        ∃ p : FieldValuedPoint B (Spec (.of k)) hk (yoneda.obj U),
          pointsMap B (Spec (.of k)) hk (yoneda.obj U) a
            (p.class B (Spec (.of k)) hk (yoneda.obj U)) = x := by
  obtain ⟨U, a, hsurj, ha⟩ := exists_surjective_etale_chart k B hk X hX
  obtain ⟨z, hz⟩ := hsurj x
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  exact ⟨U, a, ha, p, hz⟩

/-- Geometric reducedness of `X` at `x` gives geometric reducedness of any étale chart at any
field-valued point above `x`. -/
private theorem isGeometricallyReducedAt_chart_of_pointsMap_eq
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) {x : points B (Spec (.of k)) hk X}
    (h : IsGeometricallyReducedAt k B hk X hX x)
    (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X)
    (ha : IsEtale B (Spec (.of k)) hk a)
    (p : FieldValuedPoint B (Spec (.of k)) hk (yoneda.obj U))
    (hp : pointsMap B (Spec (.of k)) hk (yoneda.obj U) a
      (p.class B (Spec (.of k)) hk (yoneda.obj U)) = x) :
    _root_.AlgebraicGeometry.IsGeometricallyReducedAt (B.inclusion.map U.hom)
      (schemePoint B (Spec (.of k)) hk U p) := by
  obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B (Spec (.of k)) hk X x
  exact (isGeometricallyReduced_etaleLocalRing_iff_chart_of_liesOver
    k B hk X hX U a ha p xbar (hp.trans hxbar.symm)).mp (h xbar hxbar)

/-- **Stacks 0DMR, conditions (1) and (2).** An algebraic space over a field `k` is
geometrically reduced at a point `x` exactly when *some* étale neighbourhood `(U, u) → (X, x)`
with `U` a scheme is geometrically reduced at `u`. -/
@[stacks 0DMR "conditions (1) and (2): some étale neighbourhood"]
theorem isGeometricallyReducedAt_iff_exists_etaleChart
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (x : points B (Spec (.of k)) hk X) :
    IsGeometricallyReducedAt k B hk X hX x ↔
      ∃ (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X),
        IsEtale B (Spec (.of k)) hk a ∧
          ∃ p : FieldValuedPoint B (Spec (.of k)) hk (yoneda.obj U),
            pointsMap B (Spec (.of k)) hk (yoneda.obj U) a
                (p.class B (Spec (.of k)) hk (yoneda.obj U)) = x ∧
              _root_.AlgebraicGeometry.IsGeometricallyReducedAt (B.inclusion.map U.hom)
                (schemePoint B (Spec (.of k)) hk U p) := by
  constructor
  · intro h
    obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_point k B hk X hX x
    exact ⟨U, a, ha, p, hp,
      isGeometricallyReducedAt_chart_of_pointsMap_eq k B hk X hX h U a ha p hp⟩
  · rintro ⟨U, a, ha, p, hp, hred⟩ xbar hxbar
    exact (isGeometricallyReduced_etaleLocalRing_iff_chart_of_liesOver
      k B hk X hX U a ha p xbar (hp.trans hxbar.symm)).mpr hred

/-- **Stacks 0DMR, conditions (1) and (3).** An algebraic space over a field `k` is
geometrically reduced at a point `x` exactly when *every* étale neighbourhood `(U, u) → (X, x)`
with `U` a scheme is geometrically reduced at `u`. -/
@[stacks 0DMR "conditions (1) and (3): every étale neighbourhood"]
theorem isGeometricallyReducedAt_iff_forall_etaleChart
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (x : points B (Spec (.of k)) hk X) :
    IsGeometricallyReducedAt k B hk X hX x ↔
      ∀ (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X),
        IsEtale B (Spec (.of k)) hk a →
          ∀ p : FieldValuedPoint B (Spec (.of k)) hk (yoneda.obj U),
            pointsMap B (Spec (.of k)) hk (yoneda.obj U) a
                (p.class B (Spec (.of k)) hk (yoneda.obj U)) = x →
              _root_.AlgebraicGeometry.IsGeometricallyReducedAt (B.inclusion.map U.hom)
                (schemePoint B (Spec (.of k)) hk U p) := by
  constructor
  · intro h U a ha p hp
    exact isGeometricallyReducedAt_chart_of_pointsMap_eq k B hk X hX h U a ha p hp
  · intro h
    obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_point k B hk X hX x
    exact (isGeometricallyReducedAt_iff_exists_etaleChart k B hk X hX x).mpr
      ⟨U, a, ha, p, hp, h U a ha p hp⟩

/-- An étale scheme chart of `X` is geometrically reduced over `k` exactly when it is
geometrically reduced at the scheme point of every field-valued point of the chart: every
scheme point has a canonical field-valued representative above it. -/
private theorem geometricallyReduced_iff_forall_fieldValuedPoint
    (U : BigFppfOver B (Spec (.of k)) hk) :
    _root_.AlgebraicGeometry.GeometricallyReduced (B.inclusion.map U.hom) ↔
      ∀ p : FieldValuedPoint B (Spec (.of k)) hk (yoneda.obj U),
        _root_.AlgebraicGeometry.IsGeometricallyReducedAt (B.inclusion.map U.hom)
          (schemePoint B (Spec (.of k)) hk U p) := by
  rw [_root_.AlgebraicGeometry.geometricallyReduced_iff_forall_isGeometricallyReducedAt]
  refine ⟨fun h p ↦ h _, fun h u ↦ ?_⟩
  simpa only [schemePointRepresentative_point B (Spec (.of k)) hk U u] using
    h (schemePointRepresentative B (Spec (.of k)) hk U u)

/-- Every étale scheme chart of a geometrically reduced algebraic space is geometrically
reduced. -/
private theorem geometricallyReduced_chart_of_isGeometricallyReduced
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (h : IsGeometricallyReduced k B hk X hX)
    (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X)
    (ha : IsEtale B (Spec (.of k)) hk a) :
    _root_.AlgebraicGeometry.GeometricallyReduced (B.inclusion.map U.hom) :=
  (geometricallyReduced_iff_forall_fieldValuedPoint k B hk U).mpr fun p ↦
    isGeometricallyReducedAt_chart_of_pointsMap_eq k B hk X hX (h _) U a ha p rfl

/-- **Stacks 0DMS, conditions (1) and (2).** An algebraic space over a field `k` is
geometrically reduced exactly when *some* surjective étale morphism `U → X` with `U` a scheme
has `U` geometrically reduced over `k`. -/
@[stacks 0DMS "conditions (1) and (2): some surjective étale chart"]
theorem isGeometricallyReduced_iff_exists_surjective_etaleChart
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsGeometricallyReduced k B hk X hX ↔
      ∃ (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X),
        IsSurjective B (Spec (.of k)) hk a ∧ IsEtale B (Spec (.of k)) hk a ∧
          _root_.AlgebraicGeometry.GeometricallyReduced (B.inclusion.map U.hom) := by
  constructor
  · intro h
    obtain ⟨U, a, hsurj, ha⟩ := exists_surjective_etale_chart k B hk X hX
    exact ⟨U, a, hsurj, ha,
      geometricallyReduced_chart_of_isGeometricallyReduced k B hk X hX h U a ha⟩
  · rintro ⟨U, a, hsurj, ha, hU⟩ x
    obtain ⟨z, hz⟩ := hsurj x
    obtain ⟨p, rfl⟩ := Quot.exists_rep z
    exact (isGeometricallyReducedAt_iff_exists_etaleChart k B hk X hX x).mpr
      ⟨U, a, ha, p, hz, (geometricallyReduced_iff_forall_fieldValuedPoint k B hk U).mp hU p⟩

/-- **Stacks 0DMS, conditions (1) and (3).** An algebraic space over a field `k` is
geometrically reduced exactly when *every* étale morphism `U → X` with `U` a scheme has `U`
geometrically reduced over `k`. -/
@[stacks 0DMS "conditions (1) and (3): every étale chart"]
theorem isGeometricallyReduced_iff_forall_etaleChart
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsGeometricallyReduced k B hk X hX ↔
      ∀ (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X),
        IsEtale B (Spec (.of k)) hk a →
          _root_.AlgebraicGeometry.GeometricallyReduced (B.inclusion.map U.hom) := by
  exact ⟨geometricallyReduced_chart_of_isGeometricallyReduced k B hk X hX,
    fun h x ↦ (isGeometricallyReducedAt_iff_forall_etaleChart k B hk X hX x).mpr
      fun U a ha p _ ↦ (geometricallyReduced_iff_forall_fieldValuedPoint k B hk U).mp (h U a ha) p⟩

end Charts

end AlgebraicGeometry.Space

end
