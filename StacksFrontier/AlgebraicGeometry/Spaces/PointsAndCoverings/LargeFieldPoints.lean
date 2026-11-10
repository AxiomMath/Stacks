module

public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.RingTheory.Jacobson.Nullstellensatz
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Field-valued points over a sufficiently large field

A field-valued point of a presheaf on the big fppf site of `S` is a section over the spectrum
of a field in the site. Two constructions are made for such points. First, the spectrum of a
residue field of a scheme in the site is again an object of the site, so every point of such a
scheme carries a canonical field-valued point, and for a representable presheaf that canonical
point represents the same point of the presheaf as any field-valued point above it. Second, a
point of a scheme lifts along a morphism through a prescribed algebraically closed field,
provided that field is larger than the residue field at the point.

## Main definitions

* `AlgebraicGeometry.Space.schemeFieldPoint` reads a field-valued point of a representable
  presheaf on the big fppf site of `S` as a field-valued point of the underlying scheme.
* `AlgebraicGeometry.Space.siteMapOfSchemeMap` and
  `AlgebraicGeometry.Space.siteFieldPointOfSchemeMap` read a morphism of schemes from the
  spectrum of a field in the site as a morphism of the site, respectively as a field-valued
  point of the represented presheaf.
* `AlgebraicGeometry.Space.canonicalSiteFieldPoint` is the field-valued point of a
  representable presheaf given by the residue field at a point of the underlying scheme.

## Main results

* `Algebra.nonempty_algHom_of_card_lt`: a field extension of cardinality smaller than that of
  an algebraically closed field embeds into it over any common subfield.
* `AlgebraicGeometry.exists_spec_lift_of_large_field`: a morphism from the spectrum of a
  sufficiently large algebraically closed field lifts along a morphism of schemes, through any
  prescribed point of the source above its image point.
* `AlgebraicGeometry.Space.dominates_of_scheme_map`: a morphism of field spectra compatible
  with the sections of two field-valued points of a representable presheaf exhibits the first
  as dominated by the second.
* `AlgebraicGeometry.Space.canonicalSiteFieldPoint_class_eq`: the canonical field-valued point
  at the image of a field-valued point represents the same point of the presheaf.

## Implementation notes

The embedding of a field extension `L` of `k` into a large algebraically closed `K` is
obtained from a maximal ideal `m` of `K ⊗[k] L`: the residue field is algebraic over `K` by
the cardinality form of the Nullstellensatz, hence `K` itself, and `L` maps to it through the
right inclusion of the tensor product.

The lift of a point along a morphism of schemes is produced through
`AlgebraicGeometry.Scheme.SpecToEquivOfField`, which presents a morphism from the spectrum of
a field as a point together with a homomorphism from the residue field there. The lift is the
prescribed point together with the embedding of its residue field, and the commuting triangle
is the compatibility of that embedding with the residue field map of the morphism.

That the canonical field-valued point represents the same point of a representable presheaf is
the smallest-representative property of `Spec κ(x) ⟶ X`, that is
`AlgebraicGeometry.FieldValuedPoint.canonical_isSmallest`: the resulting morphism of field
spectra is a morphism over `S` of the two objects of the site, hence exhibits one field-valued
point as dominating the other.

## References

* [Stacks Project, Tag 01J9](https://stacks.math.columbia.edu/tag/01J9)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 046V](https://stacks.math.columbia.edu/tag/046V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

/-! ### Embedding a small field extension into a large algebraically closed field -/

/-- A field extension `L` of `k` whose cardinality is smaller than that of an algebraically
closed extension `K` of `k` admits a `k`-algebra map to `K`.

A maximal ideal of `K ⊗[k] L` has residue field algebraic over `K`, hence equal to `K` since
`K` is algebraically closed, and `L` maps to that residue field. -/
theorem Algebra.nonempty_algHom_of_card_lt {k L K : Type u} [Field k] [Field L] [Field K]
    [Algebra k L] [Algebra k K] [IsAlgClosed K]
    (hcard : Cardinal.mk L < Cardinal.mk K) :
    Nonempty (L →ₐ[k] K) := by
  classical
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] L)
  let : Field ((K ⊗[k] L) ⧸ m) := Ideal.Quotient.field m
  let : Algebra K ((K ⊗[k] L) ⧸ m) := Ideal.Quotient.algebra K
  have halg : Algebra.IsAlgebraic K ((K ⊗[k] L) ⧸ m) :=
    Algebra.isAlgebraic_tensorProduct_quotient_of_card_lt k L K (by simpa using hcard) m
  have : Algebra.IsIntegral K ((K ⊗[k] L) ⧸ m) := Algebra.isAlgebraic_iff_isIntegral.mp halg
  have hbij : Function.Bijective (algebraMap K ((K ⊗[k] L) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := (K ⊗[k] L) ⧸ m)
  let e : K ≃ₐ[K] ((K ⊗[k] L) ⧸ m) :=
    AlgEquiv.ofBijective (Algebra.ofId K ((K ⊗[k] L) ⧸ m)) hbij
  exact ⟨(e.symm.toAlgHom.restrictScalars k).comp
    (((Ideal.Quotient.mkₐ K m).restrictScalars k).comp
      (Algebra.TensorProduct.includeRight : L →ₐ[k] K ⊗[k] L))⟩

namespace AlgebraicGeometry

/-! ### Lifting a point of a scheme over a large algebraically closed field -/

/-- A morphism `Spec K ⟶ Y` from the spectrum of an algebraically closed field lifts along
`f : X ⟶ Y` through a prescribed point `x` of `X` above its image point, provided `K` is
larger than the residue field of `X` at `x`.

The lift is `x` together with the embedding of `κ(x)` into `K` over `κ(f x)` supplied by
`Algebra.nonempty_algHom_of_card_lt`, read as a morphism from `Spec K` through
`AlgebraicGeometry.Scheme.SpecToEquivOfField`. -/
theorem exists_spec_lift_of_large_field
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (K : Type u) [Field K] [IsAlgClosed K]
    (g : Spec (.of K) ⟶ Y)
    (hpoint : f x = g (IsLocalRing.closedPoint K))
    (hcard : Cardinal.mk (X.residueField x) < Cardinal.mk K) :
    ∃ l : Spec (.of K) ⟶ X,
      l (IsLocalRing.closedPoint K) = x ∧ l ≫ f = g := by
  classical
  let gp := Scheme.SpecToEquivOfField K Y g
  have hgp : gp.1 = f x := hpoint.symm
  let base := Y.residueField gp.1
  let srcMap : base →+* X.residueField x :=
    ((Y.residueFieldCongr hgp).hom ≫ f.residueFieldMap x).hom
  let tgtMap : base →+* K := gp.2.hom
  let : Algebra base (X.residueField x) := srcMap.toAlgebra
  let : Algebra base K := tgtMap.toAlgebra
  obtain ⟨φ⟩ := Algebra.nonempty_algHom_of_card_lt
    (k := base) (L := X.residueField x) (K := K) hcard
  let l : Spec (.of K) ⟶ X :=
    (Scheme.SpecToEquivOfField K X).symm ⟨x, CommRingCat.ofHom φ.toRingHom⟩
  have hl_repr : Scheme.SpecToEquivOfField K X l =
      ⟨x, CommRingCat.ofHom φ.toRingHom⟩ := Equiv.apply_symm_apply _ _
  have hlpoint : l (IsLocalRing.closedPoint K) = x := by
    simpa only [Scheme.SpecToEquivOfField_apply_fst] using
      congrArg (fun z => z.1) hl_repr
  refine ⟨l, hlpoint, ?_⟩
  have hpoint' : f (l (IsLocalRing.closedPoint K)) = g (IsLocalRing.closedPoint K) := by
    rw [hlpoint, hpoint]
  apply (Scheme.SpecToEquivOfField K Y).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨hpoint', ?_⟩
  rw [Scheme.SpecToEquivOfField_apply_snd, Scheme.SpecToEquivOfField_apply_snd]
  have hcomp := Scheme.descResidueField_stalkClosedPointTo_comp (f := f) (g := l)
  change Scheme.descResidueField (Scheme.stalkClosedPointTo (l ≫ f)) =
    f.residueFieldMap (l (IsLocalRing.closedPoint ↑(CommRingCat.of K))) ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo l) at hcomp
  have hlsnd : Scheme.descResidueField (Scheme.stalkClosedPointTo l) =
      (Scheme.residueFieldCongr hlpoint).hom ≫ CommRingCat.ofHom φ.toRingHom := by
    obtain ⟨hfst, hsnd⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hl_repr
    change l (IsLocalRing.closedPoint K) = x at hfst
    rw [Subsingleton.elim hfst hlpoint] at hsnd
    convert hsnd using 1
    · exact (congrArg (fun z : X => X.residueField z ⟶ CommRingCat.of K)
        (Scheme.SpecToEquivOfField_apply_fst K X l)).symm
    · rfl
    · exact HEq.rfl
  have hφ₀ : (Y.residueFieldCongr hgp).hom ≫ f.residueFieldMap x ≫
      CommRingCat.ofHom φ.toRingHom = gp.2 := by
    ext a
    exact φ.commutes a
  have hφ : f.residueFieldMap x ≫ CommRingCat.ofHom φ.toRingHom =
      (Y.residueFieldCongr hpoint).hom ≫ gp.2 := by
    calc
      f.residueFieldMap x ≫ CommRingCat.ofHom φ.toRingHom =
          (Y.residueFieldCongr hgp).inv ≫
            ((Y.residueFieldCongr hgp).hom ≫ f.residueFieldMap x ≫
              CommRingCat.ofHom φ.toRingHom) := by simp
      _ = (Y.residueFieldCongr hgp).inv ≫ gp.2 := by rw [hφ₀]
      _ = (Y.residueFieldCongr hpoint).hom ≫ gp.2 := rfl
  rw [hcomp, hlsnd,
    Scheme.Hom.residueFieldMap_congr'_assoc hlpoint (CommRingCat.ofHom φ.toRingHom),
    hφ, ← Scheme.SpecToEquivOfField_apply_snd K Y g]
  exact Scheme.residueFieldCongr_trans_hom_assoc Y (congrArg f hlpoint) hpoint gp.2

namespace Space

/-! ### Field-valued points of a representable presheaf -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A field-valued point of a presheaf represented by an object of the big fppf site of `S`,
read as a field-valued point of the underlying scheme. -/
noncomputable def schemeFieldPoint {T : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (yoneda.obj T)) :
    _root_.AlgebraicGeometry.FieldValuedPoint ((BigFppfOver.toScheme B S hS).obj T) where
  carrier := p.carrier
  map := B.inclusion.map p.value.left

/-- The canonical morphism from the spectrum of a residue field is quasi-compact, its source
being a one-point scheme. -/
@[ega "IV 3.2.9" "partial"]
private instance fromSpecResidueField_quasiCompact {Y : Scheme.{u}} (y : Y) :
    QuasiCompact (Y.fromSpecResidueField y) := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  exact fun V _ => (Set.toFinite (Y.fromSpecResidueField y ⁻¹' (V : Set Y))).isCompact

/-- The morphism of the big fppf site of `S` underlying a morphism of schemes from the spectrum
of a field in the site to the scheme underlying an object `U` of the site. -/
noncomputable def siteMapOfSchemeMap (U : BigFppfOver B S hS) {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K)))
    (ρ : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj U) :
    B.obj hK ⟶ U.left :=
  B.inclusion.preimage ρ

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.siteMapOfSchemeMap` is the
given one. -/
theorem map_siteMapOfSchemeMap (U : BigFppfOver B S hS) {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K)))
    (ρ : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj U) :
    B.inclusion.map (siteMapOfSchemeMap B S hS U hK ρ) = ρ :=
  B.inclusion.map_preimage _

/-- The field-valued point of the presheaf represented by an object `U` of the big fppf site of
`S` given by a morphism of schemes from the spectrum of a field in the site to the scheme
underlying `U`. -/
noncomputable def siteFieldPointOfSchemeMap (U : BigFppfOver B S hS) {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K)))
    (ρ : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj U) :
    FieldValuedPoint B S hS (yoneda.obj U) :=
  ⟨K, hK, B.inclusion.map (siteMapOfSchemeMap B S hS U hK ρ ≫ U.hom),
    Over.homMk (siteMapOfSchemeMap B S hS U hK ρ)⟩

/-- The section of `AlgebraicGeometry.Space.siteFieldPointOfSchemeMap`, read as a morphism of
schemes, is the morphism it was built from. -/
theorem map_siteFieldPointOfSchemeMap_value_left (U : BigFppfOver B S hS) {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K)))
    (ρ : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj U) :
    B.inclusion.map (siteFieldPointOfSchemeMap B S hS U hK ρ).value.left = ρ :=
  map_siteMapOfSchemeMap B S hS U hK ρ

/-- The field-valued point of a presheaf represented by an object `U` of the big fppf site of
`S` attached to a point `x` of the underlying scheme: its field is the residue field at `x`
and its section is the canonical morphism `Spec κ(x) ⟶ U`. -/
noncomputable def canonicalSiteFieldPoint (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    FieldValuedPoint B S hS (yoneda.obj U) :=
  siteFieldPointOfSchemeMap B S hS U (B.residueField_spec_contains U.left.property x)
    (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x)

/-- The canonical field-valued point at `x` lies over `x`. -/
theorem canonicalSiteFieldPoint_point (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    (schemeFieldPoint B S hS (canonicalSiteFieldPoint B S hS U x)).point = x := by
  have h : (schemeFieldPoint B S hS (canonicalSiteFieldPoint B S hS U x)).map =
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x :=
    map_siteFieldPointOfSchemeMap_value_left B S hS U _ _
  change (schemeFieldPoint B S hS (canonicalSiteFieldPoint B S hS U x)).map _ = x
  rw [h]
  exact Scheme.fromSpecResidueField_apply x _

/-- A morphism of field spectra compatible with the sections of two field-valued points of a
presheaf represented by an object of the big fppf site of `S` exhibits the first point as
dominated by the second.

Compatibility with the sections forces compatibility with the structure morphisms to `S`, so
the morphism of field spectra is a morphism of the two objects of the site. -/
theorem dominates_of_scheme_map (U : BigFppfOver B S hS)
    (p q : FieldValuedPoint B S hS (yoneda.obj U))
    (c : Spec (.of p.carrier) ⟶ Spec (.of q.carrier))
    (hc : c ≫ B.inclusion.map q.value.left = B.inclusion.map p.value.left) :
    FieldValuedPoint.Dominates B S hS (yoneda.obj U) p q := by
  have hq : B.inclusion.map q.value.left ≫ B.inclusion.map U.hom = q.toBase := by
    rw [← B.inclusion.map_comp]
    exact congrArg B.inclusion.map q.value.w
  have hp : B.inclusion.map p.value.left ≫ B.inclusion.map U.hom = p.toBase := by
    rw [← B.inclusion.map_comp]
    exact congrArg B.inclusion.map p.value.w
  have hbase : B.inclusion.preimage (X := B.obj p.contained) (Y := B.obj q.contained) c ≫
      (⟨q.toBase⟩ : B.obj q.contained ⟶ B.obj hS) =
      (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS) := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    calc
      c ≫ q.toBase = c ≫ B.inclusion.map q.value.left ≫ B.inclusion.map U.hom := by rw [hq]
      _ = (c ≫ B.inclusion.map q.value.left) ≫ B.inclusion.map U.hom := by
        rw [Category.assoc]
      _ = B.inclusion.map p.value.left ≫ B.inclusion.map U.hom := by rw [hc]
      _ = p.toBase := hp
  refine ⟨Over.homMk (B.inclusion.preimage (X := B.obj p.contained)
    (Y := B.obj q.contained) c) hbase, ?_⟩
  change Over.homMk (B.inclusion.preimage (X := B.obj p.contained)
    (Y := B.obj q.contained) c) hbase ≫ q.value = p.value
  ext
  change B.inclusion.map (B.inclusion.preimage (X := B.obj p.contained)
    (Y := B.obj q.contained) c ≫ q.value.left) = B.inclusion.map p.value.left
  rw [B.inclusion.map_comp, B.inclusion.map_preimage]
  exact hc

/-- The canonical field-valued point at the image of a field-valued point represents the same
point of the presheaf.

The two are compared through the smallest-representative property of `Spec κ(x) ⟶ X`,
`AlgebraicGeometry.FieldValuedPoint.canonical_isSmallest`: the factorization it provides is a
morphism of field spectra compatible with the two sections. -/
theorem canonicalSiteFieldPoint_class_eq (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (x : (BigFppfOver.toScheme B S hS).obj U)
    (hx : (schemeFieldPoint B S hS p).point = x) :
    (canonicalSiteFieldPoint B S hS U x).class B S hS (yoneda.obj U) =
      p.class B S hS (yoneda.obj U) := by
  classical
  obtain ⟨e, he, -⟩ := _root_.AlgebraicGeometry.FieldValuedPoint.canonical_isSmallest x
    (schemeFieldPoint B S hS p) (hx.trans (Scheme.fromSpecResidueField_apply x _).symm)
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj U)
    (FieldValuedPoint.hasCommonExtension_symm B S hS (yoneda.obj U)
      ⟨p, FieldValuedPoint.dominates_refl B S hS (yoneda.obj U) p,
        dominates_of_scheme_map B S hS U p (canonicalSiteFieldPoint B S hS U x) e ?_⟩)
  have h : B.inclusion.map (canonicalSiteFieldPoint B S hS U x).value.left =
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x :=
    map_siteFieldPointOfSchemeMap_value_left B S hS U _ _
  rw [h]
  exact he

end Space

end AlgebraicGeometry

end
