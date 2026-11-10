module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.TangentIdentity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Unramified
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derivative of multiplication by an integer on a group scheme

Multiplication by an integer `d` on a group scheme `G` over a base is the `d`-th power of the
identity in the group `G ⟶ G` of morphisms into the group object.  It fixes the identity point,
and this file computes its derivative there: on the relative tangent space at the identity it is
multiplication by `d`.  The consequence recorded at the end is that multiplication by `d` is
unramified at the identity exactly when `d` is invertible in the ground field.

## Main results

* `Stacks.Groupoids.tangentArrow_add_val`: addition of tangent vectors at the identity of a
  group scheme is the group operation on morphisms from the spectrum of the dual numbers.
* `Stacks.Groupoids.tangentArrow_zsmul_val`: consequently `d • v` is the `d`-th power of `v` in
  that group.
* `Stacks.Groupoids.zpow_tangentMap_apply_at_identity`: **the derivative of `[d]` at the
  identity is multiplication by `d`**, the step the source proofs of Tags 0BFH and 0C0Y take
  from Tag 0BF5.
* `Stacks.Groupoids.tangentArrow_nontrivial_of_positiveDimension`: the relative tangent space at
  a point of a positive-dimensional irreducible variety is nonzero.
* `Stacks.Groupoids.unramifiedAt_zpow_id_identity_of_isUnit`: multiplication by an invertible
  integer is unramified at the identity, with no hypothesis on the dimension.
* `Stacks.Groupoids.unramifiedAt_zpow_id_identity_iff_isUnit`: multiplication by `d` on a
  positive-dimensional irreducible group scheme over a field is unramified at the identity if
  and only if `d` is invertible in the ground field.

## Implementation notes

The derivative is computed from Tag 0BF5, `AlgebraicGeometry.tangentMap_mul_at_identity`, which
says that the derivative of the multiplication morphism at the pair of identity points is
addition.  Read through the product decomposition of the tangent space of a fibre product, that
statement identifies the sum of two tangent vectors with the product of the two corresponding
morphisms `Spec (DualNumber κ(e)) ⟶ G` in the group `Over.mk (dualNumberBasePoint G.hom e) ⟶ G`;
that is `Stacks.Groupoids.tangentArrow_add_val`.  So sending a tangent vector to that morphism is
an additive map into an additive group, hence commutes with integer multiples, and the `d`-th
power of the identity acts on a morphism into `G` by raising it to the `d`-th power.

The derivative of `[d]` is only defined once the residue field at the identity is not changed by
`[d]`, which holds because `[d]` fixes the identity and the structure morphism has a section
through it; this is `Stacks.Groupoids.zpow_residueFieldMap_isIso_at_identity`.  The point
equality `[d] e = e` is propositional, so the derivative lands in the tangent space at `[d] e`
and has to be transported back; the transport bookkeeping is the group of lemmas
`AlgebraicGeometry.tangentMap_fixed_apply` and `AlgebraicGeometry.tangentMap_transport_*`, which
live next to Tag 0BF5 in
`StacksFrontier/AlgebraicGeometry/Groupoids/GroupSchemeProperties/TangentIdentity.lean`.

Nonvanishing of the tangent space is proved by contradiction from Tag 0B2G: a vanishing relative
tangent space at `x` makes the structure morphism unramified at `x`, hence quasi-finite there, so
an affine open neighbourhood of `x` is locally Artinian and therefore zero-dimensional, which on
an irreducible variety forces the whole space to be zero-dimensional.

## References

* [Stacks Project, Tag 0BF5](https://stacks.math.columbia.edu/tag/0BF5)
* [Stacks Project, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- Multiplication by `d` fixes the identity point. -/
theorem zpow_id_fixes_identity (s : S) (d : ℤ) :
    (((𝟙 G : G ⟶ G) ^ d).left) ((η[G]).left s) = (η[G]).left s := by
  have hpow : η[G] ≫ (𝟙 G : G ⟶ G) ^ d = η[G] := by
    rw [GrpObj.comp_zpow, Category.comp_id, MonObj.one_eq_one G]
    simp
  exact congrArg (fun f : S ⟶ G.left => f s) (congrArg Over.Hom.left hpow)

/-- Multiplication by `d` does not change the residue field at the identity point: it fixes that
point, and the structure morphism, which has the unit as a section there, does not change the
residue field either. -/
theorem zpow_residueFieldMap_isIso_at_identity (s : S) (d : ℤ) :
    IsIso (((𝟙 G : G ⟶ G) ^ d).left.residueFieldMap ((η[G]).left s)) := by
  have : IsIso (G.hom.residueFieldMap ((η[G]).left s)) :=
    AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left (η[G]).w s
  rw [residueFieldMap_eq_residueFieldCongr_of_fixed G.hom _ ((𝟙 G : G ⟶ G) ^ d).w
    ((η[G]).left s) (zpow_id_fixes_identity G s d)]
  infer_instance

end Stacks.Groupoids

namespace Stacks.Groupoids

/-- Transporting a tangent vector along an equality of points and back returns it. -/
theorem tangentArrow_transport_symm {X S : Scheme.{u}} (f : X ⟶ S) {x y : X} (h : x = y)
    (v : DottedTangentArrow f y) :
    (h ▸ h.symm ▸ v : DottedTangentArrow f y) = v := by
  subst y
  rfl

/-- **Addition of tangent vectors at the identity of a group scheme is the group operation.**
A tangent vector of `G` over `S` at the identity point is a morphism to `G` over the dual-number
base point, and the sum of two tangent vectors is their product in that group of morphisms.

This is the content of Tag 0BF5 read through the product decomposition of the tangent space of
the fibre product. -/
@[sga "3 II 3.9.0" "special case", sga "3 VIIB 2.6" "2.6 b)"]
theorem tangentArrow_add_val {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S)
    (v w : DottedTangentArrow G.hom ((η[G]).left s)) :
    (v + w).val =
      ((Over.homMk v.val v.property.2 :
        Over.mk (dualNumberBasePoint G.hom ((η[G]).left s)) ⟶ G) *
        Over.homMk w.val w.property.2).left := by
  obtain ⟨h₁, h₂, hm, hbase, hfield₁, hfield₂, hfieldm, hadd⟩ :=
    tangentMap_mul_at_identity G s
  let e : G.left := (η[G]).left s
  let z : ↑(pullback G.hom G.hom) := ((lift (η[G]) (η[G])).left s)
  let m : pullback G.hom G.hom ⟶ G.left := (μ[G]).left
  let p := pullback.fst G.hom G.hom
  let q := pullback.snd G.hom G.hom
  change p z = e at h₁
  change q z = e at h₂
  change m z = e at hm
  change m ≫ G.hom = p ≫ G.hom at hbase
  have : IsIso (G.hom.residueFieldMap (p z)) := hfield₁
  have : IsIso (G.hom.residueFieldMap (q z)) := hfield₂
  have : IsIso (m.residueFieldMap z) := hfieldm
  have : IsIso (G.hom.residueFieldMap e) :=
    AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left (η[G]).w s
  let product := tangentSpaceProductEquiv G.hom G.hom z
  have := product.fst_residueField_isIso
  have := product.snd_residueField_isIso
  let θ := product.toLinearEquiv.symm (h₁.symm ▸ v, h₂.symm ▸ w)
  have hprojection := product.toLinearEquiv_apply θ
  have hpair : product.toLinearEquiv θ = (h₁.symm ▸ v, h₂.symm ▸ w) :=
    product.toLinearEquiv.apply_symm_apply _
  have hp : (h₁ ▸ tangentMap p (p ≫ G.hom) G.hom rfl z θ :
      DottedTangentArrow G.hom e) = v :=
    (congrArg (fun vector => h₁ ▸ vector) ((congrArg Prod.fst hprojection).symm.trans
      (congrArg Prod.fst hpair))).trans (tangentArrow_transport_symm G.hom h₁ v)
  have hq : (h₂ ▸ tangentMap q (p ≫ G.hom) G.hom pullback.condition.symm z θ :
      DottedTangentArrow G.hom e) = w :=
    (congrArg (fun vector => h₂ ▸ vector) ((congrArg Prod.snd hprojection).symm.trans
      (congrArg Prod.snd hpair))).trans (tangentArrow_transport_symm G.hom h₂ w)
  let c := Spec.map (CommRingCat.ofHom
    (dualNumberCongr
      (asIso ((G.left.residueFieldCongr hm).inv ≫
        m.residueFieldMap z)).commRingCatIsoToRingEquiv.symm).toRingHom) ≫ θ.val
  have hpval : c ≫ p = v.val :=
    (tangentMap_transport_apply_eq G.hom (p ≫ G.hom) p m rfl hbase z e h₁ hm θ).symm.trans
      (congrArg Subtype.val hp)
  have hqval : c ≫ q = w.val :=
    (tangentMap_transport_apply_eq G.hom (p ≫ G.hom) q m pullback.condition.symm hbase
      z e h₂ hm θ).symm.trans (congrArg Subtype.val hq)
  have hc : c = pullback.lift v.val w.val (v.property.2.trans w.property.2.symm) :=
    pullback.hom_ext (hpval.trans (pullback.lift_fst _ _ _).symm)
      (hqval.trans (pullback.lift_snd _ _ _).symm)
  have hmval := tangentMap_transport_apply m (p ≫ G.hom) G.hom hbase z e hm θ
  have hsum : (hm ▸ tangentMap m (p ≫ G.hom) G.hom hbase z θ :
      DottedTangentArrow G.hom e) = v + w := hadd v w
  rw [← hsum, hmval]
  change c ≫ m = _
  rw [hc]
  rfl

/-- **An integer multiple of a tangent vector at the identity is an integer power.** -/
theorem tangentArrow_zsmul_val {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S)
    (v : DottedTangentArrow G.hom ((η[G]).left s)) (d : ℤ) :
    (d • v).val =
      ((Over.homMk v.val v.property.2 :
        Over.mk (dualNumberBasePoint G.hom ((η[G]).left s)) ⟶ G) ^ d).left := by
  let toPoint : DottedTangentArrow G.hom ((η[G]).left s) →
      Additive (Over.mk (dualNumberBasePoint G.hom ((η[G]).left s)) ⟶ G) :=
    fun vector => Additive.ofMul (Over.homMk vector.val vector.property.2)
  exact congrArg (fun point => (Additive.toMul point).left)
    ((AddMonoidHom.mk' toPoint fun first second =>
      Over.OverMorphism.ext (tangentArrow_add_val G s first second)).map_zsmul d v)

/-- **The derivative of multiplication by `d` at the identity is multiplication by `d`.**
This is the step the source proofs of Tags 0BFH and 0C0Y take from Tag 0BF5. -/
@[sga "3 II 4.1.1.2" "b), special case"]
theorem zpow_tangentMap_apply_at_identity {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (s : S) (d : ℤ) (v : DottedTangentArrow G.hom ((η[G]).left s)) :
    letI := zpow_residueFieldMap_isIso_at_identity G s d
    (zpow_id_fixes_identity G s d ▸ tangentMap (((𝟙 G : G ⟶ G) ^ d).left) G.hom G.hom
      ((𝟙 G : G ⟶ G) ^ d).w ((η[G]).left s) v :
        DottedTangentArrow G.hom ((η[G]).left s)) = d • v := by
  have := zpow_residueFieldMap_isIso_at_identity G s d
  have := AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left
    (η[G]).w s
  apply Subtype.ext
  rw [tangentMap_fixed_apply G.hom _ ((𝟙 G : G ⟶ G) ^ d).w
    ((η[G]).left s) (zpow_id_fixes_identity G s d) v, tangentArrow_zsmul_val]
  let point : Over.mk (dualNumberBasePoint G.hom ((η[G]).left s)) ⟶ G :=
    Over.homMk v.val v.property.2
  exact congrArg Over.Hom.left
    ((GrpObj.comp_zpow point (𝟙 G) d).trans (by simp [point]))

/-- The relative tangent space at a point of an irreducible variety of positive dimension is
nonzero: a vanishing tangent space makes the structure morphism unramified, hence quasi-finite,
at that point, so an affine open neighbourhood is locally Artinian and zero-dimensional. -/
theorem tangentArrow_nontrivial_of_positiveDimension (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IrreducibleSpace X] (x : X)
    [IsIso (f.residueFieldMap x)] (hX : 0 < topologicalKrullDim X) :
    Nontrivial (DottedTangentArrow f x) := by
  by_contra hnontrivial
  have : Subsingleton (DottedTangentArrow f x) :=
    not_nontrivial_iff_subsingleton.mp hnontrivial
  obtain ⟨U, hU, hxU, V, hV, hUV, hAlgebra⟩ :=
    (injective_tangentMap_iff_unramifiedAt f f (𝟙 _) x (by simp)).mp
      fun _ _ _ => Subsingleton.elim _ _
  let : Algebra Γ(Spec (.of k), V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Unramified Γ(Spec (.of k), V) Γ(X, U) := hAlgebra
  have hQuasi : (f.appLE V U hUV).hom.QuasiFinite :=
    RingHom.quasiFinite_algebraMap.mpr inferInstance
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : LocallyQuasiFinite (f.resLE V U hUV) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyQuasiFinite)]
    exact (RingHom.QuasiFinite.propertyIsLocal.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f V U hUV)).mpr hQuasi
  have : IsLocallyArtinian V.toScheme := inferInstance
  have : IsLocallyArtinian U.toScheme :=
    IsLocallyArtinian.of_locallyQuasiFinite (f.resLE V U hUV)
  have hdim : topologicalKrullDim U.toScheme ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology U.toScheme
  have heq := topologicalKrullDim_eq_of_isOpen k X f U U.isOpen ⟨x, hxU⟩
  exact (not_le_of_gt hX) (heq ▸ hdim)

/-- Transport along an equality of points is injective on tangent vectors. -/
theorem tangentArrow_transport_injective {X S : Scheme.{u}} (f : X ⟶ S) {x y : X} (h : x = y) :
    Function.Injective (fun v : DottedTangentArrow f x => (h ▸ v : DottedTangentArrow f y)) := by
  subst y
  exact Function.injective_id

/-- An integer is invertible in a residue field of a scheme over `k` exactly when it is
invertible in `k`. -/
theorem isUnit_intCast_residueField_iff (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) (x : X) (d : ℤ) :
    IsUnit (d : X.residueField x) ↔ IsUnit (d : k) := by
  let φ : k →+* X.residueField x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom
  rw [isUnit_iff_ne_zero, isUnit_iff_ne_zero, ← map_intCast φ]
  exact map_ne_zero_iff φ φ.injective

/-- Scalar multiplication by a field element is injective on a nonzero vector space exactly when
the element is a unit. -/
theorem smul_injective_iff_isUnit {k : Type*} [Field k] {M : Type*} [AddCommGroup M]
    [Module k M] [Nontrivial M] (a : k) :
    Function.Injective (fun x : M => a • x) ↔ IsUnit a := by
  refine ⟨fun hinj => isUnit_iff_ne_zero.mpr fun hzero => ?_,
    fun ha => smul_right_injective M ha.ne_zero⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  exact hxy (hinj (by simp [hzero]))

/-- Multiplication by `d` is unramified at the identity exactly when multiplication by `d` is
injective on the tangent space there. -/
private theorem unramifiedAt_zpow_id_identity_iff_smul_injective (k : Type u) [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] (s : Spec (.of k)) (d : ℤ) :
    UnramifiedAt (((𝟙 G : G ⟶ G) ^ d).left) ((η[G]).left s) ↔
      Function.Injective fun v : DottedTangentArrow G.hom ((η[G]).left s) =>
        (d : G.left.residueField ((η[G]).left s)) • v := by
  let e : G.left := (η[G]).left s
  let f : G.left ⟶ G.left := ((𝟙 G : G ⟶ G) ^ d).left
  have := AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left
    (η[G]).w s
  have := zpow_residueFieldMap_isIso_at_identity G s d
  have : LocallyOfFiniteType (f ≫ G.hom) := ((𝟙 G : G ⟶ G) ^ d).w.symm ▸ inferInstance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f G.hom
  have hfix : f e = e := zpow_id_fixes_identity G s d
  have hformula (vector : DottedTangentArrow G.hom e) :
      (hfix ▸ tangentMap f G.hom G.hom ((𝟙 G : G ⟶ G) ^ d).w e vector :
        DottedTangentArrow G.hom e) = (d : G.left.residueField e) • vector := by
    rw [Int.cast_smul_eq_zsmul]
    exact zpow_tangentMap_apply_at_identity G s d vector
  rw [← injective_tangentMap_iff_unramifiedAt f G.hom G.hom e ((𝟙 G : G ⟶ G) ^ d).w]
  refine ⟨fun hinj first second heq => ?_, fun hinj first second hEq => ?_⟩
  · apply hinj
    apply tangentArrow_transport_injective G.hom hfix
    exact (hformula first).trans (heq.trans (hformula second).symm)
  · exact hinj ((hformula first).symm.trans
      ((congrArg (fun vector => (hfix ▸ vector : DottedTangentArrow G.hom e)) hEq).trans
        (hformula second)))

/-- **Multiplication by an invertible integer is unramified at the identity.** The derivative
there is multiplication by `d`, which is injective because `d` is a unit, and Tag 0B2G turns
injectivity of the derivative into unramifiedness.  No hypothesis on the dimension is needed in
this direction. -/
theorem unramifiedAt_zpow_id_identity_of_isUnit (k : Type u) [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] (s : Spec (.of k)) (d : ℤ)
    (hd : IsUnit ((d : ℤ) : k)) :
    UnramifiedAt (((𝟙 G : G ⟶ G) ^ d).left) ((η[G]).left s) := by
  rw [unramifiedAt_zpow_id_identity_iff_smul_injective]
  exact smul_right_injective _
    ((isUnit_intCast_residueField_iff k G.left G.hom _ d).mpr hd).ne_zero

/-- **Multiplication by `d` is unramified at the identity exactly when `d` is invertible.**
Both directions are the computation of the derivative at the identity: it is multiplication by
`d` on a nonzero tangent space, and Tag 0B2G identifies injectivity of the derivative with
unramifiedness. -/
theorem unramifiedAt_zpow_id_identity_iff_isUnit (k : Type u) [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [IrreducibleSpace G.left]
    (hG : 0 < topologicalKrullDim G.left) (s : Spec (.of k)) (d : ℤ) :
    UnramifiedAt (((𝟙 G : G ⟶ G) ^ d).left) ((η[G]).left s) ↔ IsUnit ((d : ℤ) : k) := by
  refine ⟨fun hunram => ?_, unramifiedAt_zpow_id_identity_of_isUnit k G s d⟩
  have := AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left
    (η[G]).w s
  have : Nontrivial (DottedTangentArrow G.hom ((η[G]).left s)) :=
    tangentArrow_nontrivial_of_positiveDimension k G.left G.hom _ hG
  rw [← isUnit_intCast_residueField_iff k G.left G.hom _ d]
  exact (smul_injective_iff_isUnit _).mp
    ((unramifiedAt_zpow_id_identity_iff_smul_injective k G s d).mp hunram)

end Stacks.Groupoids

end
