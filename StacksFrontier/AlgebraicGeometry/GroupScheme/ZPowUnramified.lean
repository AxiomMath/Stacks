module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.TangentIdentity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Unramified
import all StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.TangentIdentity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Multiplication by an invertible integer on a group scheme is unramified

Let `G` be a group scheme locally of finite type over a field `k` and let `d` be an integer.
Multiplication by `d` is the `d`-th power `[d]` of the identity in the group `G ⟶ G` of
morphisms into the group object. Its tangent map at the identity is multiplication by `d` on
the tangent space, and when `G` is commutative and `d` is invertible in `k` the morphism `[d]` is
unramified everywhere. This is the local half of the proof of
[Stacks, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH); it does not use
[Stacks, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG).

## Main results

* `Stacks.Groupoids.tangentMap_zpow_id_left_unit`: the tangent map of `[d]` at the identity is
  multiplication by `d`.
* `Stacks.Groupoids.isUnit_of_unramifiedAt_zpow_id_left_unit`: if `[d]` is unramified at the
  identity of a positive-dimensional irreducible group scheme, then `d` is invertible in `k`.
* `Stacks.Groupoids.unramified_zpow_id_left_of_isUnit`: if `d` is invertible in `k` and `G` is
  commutative, then `[d]` is unramified.

## Implementation notes

The tangent space is `AlgebraicGeometry.DottedTangentArrow`, the set of dual-number points over
the base restricting to the given point, and the tangent map is
`AlgebraicGeometry.tangentMap`. The sum of two tangent vectors at the identity is their product
as points of `G` with values in the dual numbers, which is
[Stacks, Tag 0BF5](https://stacks.math.columbia.edu/tag/0BF5)
(`AlgebraicGeometry.tangentMap_mul_at_identity`); hence `d • v` is the `d`-th power of `v`,
which is `v` composed with `[d]`. The criterion
[Stacks, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G) turns injectivity of the tangent map
into unramifiedness at the identity. Over an algebraically closed field every closed point is
rational, right translation by a rational point intertwines `[d]` with a translation, and the
unramified locus is open, so the ramified locus is a closed set without closed points, hence
empty in the Jacobson space `G`; the general case descends along the base change to an algebraic
closure ([Stacks, Tag 0475](https://stacks.math.columbia.edu/tag/0475)).

## References

* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 0BF5](https://stacks.math.columbia.edu/tag/0BF5)
* [Stacks Project, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

/-- The residue field map of a morphism at the image of a point under a section is an
isomorphism: the section induces a one-sided inverse on residue fields. -/
private alias residueFieldMap_isIso_of_section :=
    AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section

/-- Two morphisms that agree after a common map, and send a point to the same point, induce the
same residue field map up to the canonical identifications. -/
private alias residueFieldMap_congr_after_common_map :=
    AlgebraicGeometry.residueFieldMap_congr_after_common_map

/-- Multiplication by `d` fixes the identity point of a group scheme over a field. -/
theorem zpow_id_left_apply_unit (k : Type u) [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] (s : Spec (.of k)) (d : ℤ) :
    (((𝟙 A : A ⟶ A) ^ d).left) ((η[A]).left s) = (η[A]).left s := by
  have hpow : η[A] ≫ (𝟙 A : A ⟶ A) ^ d = η[A] := by
    rw [GrpObj.comp_zpow, Category.comp_id, MonObj.one_eq_one A]
    simp
  exact congrArg (fun f : Spec (.of k) ⟶ A.left => f s)
    (congrArg Over.Hom.left hpow)

/-- The residue field map of multiplication by `d` at the identity point is an isomorphism. -/
theorem isIso_residueFieldMap_zpow_id_left_unit (k : Type u) [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] (s : Spec (.of k)) (d : ℤ) :
    IsIso (((𝟙 A : A ⟶ A) ^ d).left.residueFieldMap
      ((η[A]).left s)) := by
  have : IsIso (A.hom.residueFieldMap ((η[A]).left s)) :=
    residueFieldMap_isIso_of_section A.hom (η[A]).left (η[A]).w s
  rw [residueFieldMap_eq_residueFieldCongr_of_fixed A.hom _ ((𝟙 A : A ⟶ A) ^ d).w _
    (zpow_id_left_apply_unit k A s d)]
  infer_instance

/-- On a nontrivial vector space, multiplication by a scalar is injective exactly when the
scalar is a unit. -/
private lemma smul_injective_iff_isUnit
    {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M] [Nontrivial M]
    (a : k) : Function.Injective (fun x : M => a • x) ↔ IsUnit a := by
  refine ⟨fun hinj => isUnit_iff_ne_zero.mpr fun hzero => ?_,
    fun ha => smul_right_injective M ha.ne_zero⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  exact hxy (hinj (by simp [hzero]))

/-- Transporting a tangent vector along an equality and back is the identity. -/
private lemma tangentArrow_transport_symm
    {X S : Scheme.{u}} (f : X ⟶ S) {x y : X} (h : x = y)
    (v : DottedTangentArrow f y) :
    (h ▸ h.symm ▸ v : DottedTangentArrow f y) = v := by
  subst y
  rfl

/-- The first projection's tangent map recovers the first component of a pair of tangent vectors
lifted to the fibre product of a morphism with itself. -/
private lemma tangentMap_fst_productEquiv_symm {X S : Scheme.{u}} (f : X ⟶ S)
    (z : ↑(CategoryTheory.Limits.pullback f f)) {e : X}
    (h₁ : CategoryTheory.Limits.pullback.fst f f z = e)
    (h₂ : CategoryTheory.Limits.pullback.snd f f z = e) (v w : DottedTangentArrow f e)
    [IsIso (f.residueFieldMap (CategoryTheory.Limits.pullback.fst f f z))]
    [IsIso (f.residueFieldMap (CategoryTheory.Limits.pullback.snd f f z))] :
    letI := (tangentSpaceProductEquiv f f z).fst_residueField_isIso
    (h₁ ▸ AlgebraicGeometry.tangentMap (CategoryTheory.Limits.pullback.fst f f)
      (CategoryTheory.Limits.pullback.fst f f ≫ f) f rfl z
      ((tangentSpaceProductEquiv f f z).toLinearEquiv.symm (h₁.symm ▸ v, h₂.symm ▸ w)) :
      DottedTangentArrow f e) = v := by
  let product := tangentSpaceProductEquiv f f z
  let θ := product.toLinearEquiv.symm (h₁.symm ▸ v, h₂.symm ▸ w)
  have hraw := (congrArg Prod.fst (product.toLinearEquiv_apply θ)).symm.trans
    (congrArg Prod.fst (product.toLinearEquiv.apply_symm_apply _))
  exact (congrArg (fun vector => h₁ ▸ vector) hraw).trans (tangentArrow_transport_symm f h₁ v)

/-- The second projection's tangent map recovers the second component of a pair of tangent
vectors lifted to the fibre product of a morphism with itself. -/
private lemma tangentMap_snd_productEquiv_symm {X S : Scheme.{u}} (f : X ⟶ S)
    (z : ↑(CategoryTheory.Limits.pullback f f)) {e : X}
    (h₁ : CategoryTheory.Limits.pullback.fst f f z = e)
    (h₂ : CategoryTheory.Limits.pullback.snd f f z = e) (v w : DottedTangentArrow f e)
    [IsIso (f.residueFieldMap (CategoryTheory.Limits.pullback.fst f f z))]
    [IsIso (f.residueFieldMap (CategoryTheory.Limits.pullback.snd f f z))] :
    letI := (tangentSpaceProductEquiv f f z).snd_residueField_isIso
    (h₂ ▸ AlgebraicGeometry.tangentMap (CategoryTheory.Limits.pullback.snd f f)
      (CategoryTheory.Limits.pullback.fst f f ≫ f) f
      CategoryTheory.Limits.pullback.condition.symm z
      ((tangentSpaceProductEquiv f f z).toLinearEquiv.symm (h₁.symm ▸ v, h₂.symm ▸ w)) :
      DottedTangentArrow f e) = w := by
  let product := tangentSpaceProductEquiv f f z
  let θ := product.toLinearEquiv.symm (h₁.symm ▸ v, h₂.symm ▸ w)
  have hraw := (congrArg Prod.snd (product.toLinearEquiv_apply θ)).symm.trans
    (congrArg Prod.snd (product.toLinearEquiv.apply_symm_apply _))
  exact (congrArg (fun vector => h₂ ▸ vector) hraw).trans (tangentArrow_transport_symm f h₂ w)

/-- The sum of two tangent vectors at the identity of a group scheme is their product as points
with values in the dual numbers (Tag 0BF5). -/
private lemma tangentArrow_add_val {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (s : S) (v w : DottedTangentArrow G.hom ((η[G]).left s)) :
    (v + w).val =
      ((Over.homMk v.val v.property.2 :
        Over.mk (dualNumberBasePoint G.hom ((η[G]).left s)) ⟶ G) *
        Over.homMk w.val w.property.2).left := by
  obtain ⟨h₁, h₂, hm, hbase, hfield₁, hfield₂, hfieldm, hadd⟩ :=
    AlgebraicGeometry.tangentMap_mul_at_identity G s
  let e : G.left := (η[G]).left s
  let z : ↑(CategoryTheory.Limits.pullback G.hom G.hom) :=
    ((CartesianMonoidalCategory.lift (η[G]) (η[G])).left s)
  let m : CategoryTheory.Limits.pullback G.hom G.hom ⟶ G.left := (μ[G]).left
  let p := CategoryTheory.Limits.pullback.fst G.hom G.hom
  let q := CategoryTheory.Limits.pullback.snd G.hom G.hom
  change p z = e at h₁
  change q z = e at h₂
  change m z = e at hm
  change m ≫ G.hom = p ≫ G.hom at hbase
  have : IsIso (G.hom.residueFieldMap (p z)) := hfield₁
  have : IsIso (G.hom.residueFieldMap (q z)) := hfield₂
  have : IsIso (m.residueFieldMap z) := hfieldm
  have : IsIso (G.hom.residueFieldMap e) :=
    residueFieldMap_isIso_of_section G.hom (η[G]).left (η[G]).w s
  let product := AlgebraicGeometry.tangentSpaceProductEquiv G.hom G.hom z
  have := product.fst_residueField_isIso
  have := product.snd_residueField_isIso
  let θ := product.toLinearEquiv.symm (h₁.symm ▸ v, h₂.symm ▸ w)
  have hp := tangentMap_fst_productEquiv_symm G.hom z h₁ h₂ v w
  have hq := tangentMap_snd_productEquiv_symm G.hom z h₁ h₂ v w
  let c := Spec.map (CommRingCat.ofHom
    (dualNumberCongr
      (asIso ((G.left.residueFieldCongr hm).inv ≫
        m.residueFieldMap z)).commRingCatIsoToRingEquiv.symm).toRingHom) ≫ θ.val
  have hpval : c ≫ p = v.val :=
    (tangentMap_transport_apply_eq G.hom (p ≫ G.hom) p m rfl hbase
      z e h₁ hm θ).symm.trans (congrArg Subtype.val hp)
  have hqval : c ≫ q = w.val :=
    (tangentMap_transport_apply_eq G.hom (p ≫ G.hom) q m
      CategoryTheory.Limits.pullback.condition.symm hbase z e h₂ hm θ).symm.trans
        (congrArg Subtype.val hq)
  have hc : c = CategoryTheory.Limits.pullback.lift v.val w.val
      (v.property.2.trans w.property.2.symm) :=
    CategoryTheory.Limits.pullback.hom_ext
      (hpval.trans (CategoryTheory.Limits.pullback.lift_fst _ _ _).symm)
      (hqval.trans (CategoryTheory.Limits.pullback.lift_snd _ _ _).symm)
  have hsum : (hm ▸ AlgebraicGeometry.tangentMap m (p ≫ G.hom) G.hom hbase z θ :
      DottedTangentArrow G.hom e) = v + w := hadd v w
  rw [← hsum, tangentMap_transport_apply m (p ≫ G.hom) G.hom hbase z e hm θ]
  change c ≫ m = _
  rw [hc]
  rfl

/-- An integer multiple `d • v` of a tangent vector at the identity of a group scheme is the
`d`-th power of `v` as a point with values in the dual numbers. -/
private lemma tangentArrow_zsmul_val {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (s : S) (v : DottedTangentArrow G.hom ((η[G]).left s)) (d : ℤ) :
    (d • v).val =
      ((Over.homMk v.val v.property.2 :
        Over.mk (dualNumberBasePoint G.hom ((η[G]).left s)) ⟶ G) ^ d).left := by
  let toPoint : DottedTangentArrow G.hom ((η[G]).left s) →
      Additive (Over.mk (dualNumberBasePoint G.hom ((η[G]).left s)) ⟶ G) :=
    fun vector => Additive.ofMul (Over.homMk vector.val vector.property.2)
  have hAdd : ∀ v w, toPoint (v + w) = toPoint v + toPoint w := fun first second =>
    Over.OverMorphism.ext (tangentArrow_add_val G s first second)
  let hom := AddMonoidHom.mk' toPoint hAdd
  exact congrArg (fun point => (Additive.toMul point).left) (hom.map_zsmul d v)

/-- The tangent map of multiplication by `d` at the identity of a group scheme is
multiplication by `d`. -/
@[sga "3 II 3.9.4" "special case", sga "3 II 4.1.1.2" "b), special case"]
private lemma zpow_tangentMap_apply_at_identity
    (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    (s : Spec (.of k)) (d : ℤ)
    (v : DottedTangentArrow A.hom ((η[A]).left s)) :
    letI := isIso_residueFieldMap_zpow_id_left_unit k A s d
    (zpow_id_left_apply_unit k A s d ▸ AlgebraicGeometry.tangentMap
      (((𝟙 A : A ⟶ A) ^ d).left) A.hom A.hom
      ((𝟙 A : A ⟶ A) ^ d).w ((η[A]).left s) v :
        DottedTangentArrow A.hom ((η[A]).left s)) = d • v := by
  have := isIso_residueFieldMap_zpow_id_left_unit k A s d
  have := residueFieldMap_isIso_of_section A.hom (η[A]).left (η[A]).w s
  apply Subtype.ext
  rw [tangentMap_fixed_apply A.hom _ ((𝟙 A : A ⟶ A) ^ d).w
    ((η[A]).left s) (zpow_id_left_apply_unit k A s d) v, tangentArrow_zsmul_val]
  let point : Over.mk (dualNumberBasePoint A.hom ((η[A]).left s)) ⟶ A :=
    Over.homMk v.val v.property.2
  exact congrArg Over.Hom.left
    ((GrpObj.comp_zpow point (𝟙 A) d).trans (by simp [point]))


/-- The tangent space at a rational point of a positive-dimensional irreducible scheme locally
of finite type over a field is nonzero. -/
private lemma tangentArrow_nontrivial_of_positiveDimension
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X]
    (x : X) [IsIso (f.residueFieldMap x)] (hX : 0 < topologicalKrullDim X) :
    Nontrivial (DottedTangentArrow f x) := by
  classical
  by_contra hnontrivial
  have : Subsingleton (DottedTangentArrow f x) :=
    not_nontrivial_iff_subsingleton.mp hnontrivial
  have hinj : Function.Injective
      (AlgebraicGeometry.tangentMap f f (𝟙 _) (by simp) x) :=
    fun _ _ _ => Subsingleton.elim _ _
  have hunram := (injective_tangentMap_iff_unramifiedAt
    f f (𝟙 _) x (by simp)).mp hinj
  obtain ⟨U, hU, hxU, V, hV, hUV, hAlgebra⟩ := hunram
  let : Algebra Γ(Spec (.of k), V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra.Unramified Γ(Spec (.of k), V) Γ(X, U) := hAlgebra
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
  have heq := AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen
    k X f U U.isOpen ⟨x, hxU⟩
  exact (not_le_of_gt hX) (heq ▸ hdim)

/-- Transport of tangent vectors along an equality of points is injective. -/
private lemma tangentArrow_transport_injective
    {X S : Scheme.{u}} (f : X ⟶ S) {x y : X} (h : x = y) :
    Function.Injective (fun v : DottedTangentArrow f x =>
      (h ▸ v : DottedTangentArrow f y)) := by
  subst y
  exact Function.injective_id

/-- An integer is a unit in a residue field of a scheme over `k` exactly when it is a unit in
`k`. -/
private lemma isUnit_intCast_residueField_iff
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (x : X) (d : ℤ) : IsUnit (d : X.residueField x) ↔ IsUnit (d : k) := by
  let φ : k →+* X.residueField x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom
  rw [isUnit_iff_ne_zero, isUnit_iff_ne_zero, ← map_intCast φ]
  exact map_ne_zero_iff φ φ.injective

/-- A composite of unramified ring maps is unramified. -/
private lemma ringHom_unramified_comp
    {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
    (f : R →+* B) (g : B →+* C)
    (hf : letI := f.toAlgebra; Algebra.Unramified R B)
    (hg : letI := g.toAlgebra; Algebra.Unramified B C) :
    letI := (g.comp f).toAlgebra; Algebra.Unramified R C := by
  let := f.toAlgebra
  let := g.toAlgebra
  let := (g.comp f).toAlgebra
  have hform : (g.comp f).FormallyUnramified :=
    (RingHom.formallyUnramified_algebraMap.mpr hf.formallyUnramified).comp
      (RingHom.formallyUnramified_algebraMap.mpr hg.formallyUnramified)
  have hfinite : (g.comp f).FiniteType :=
    (RingHom.finiteType_algebraMap.mpr hg.finiteType).comp
      (RingHom.finiteType_algebraMap.mpr hf.finiteType)
  exact ⟨RingHom.formallyUnramified_algebraMap.mp hform,
    RingHom.finiteType_algebraMap.mp hfinite⟩

/-- An isomorphism of commutative rings is unramified. -/
private lemma ringHom_unramified_of_isIso {R B : CommRingCat.{u}}
    (f : R ⟶ B) [IsIso f] : letI := f.hom.toAlgebra; Algebra.Unramified R B := by
  let := f.hom.toAlgebra
  exact Algebra.Unramified.of_equiv
    (AlgEquiv.ofBijective (Algebra.ofId R B) (ConcreteCategory.bijective_of_isIso f))

/-- Unramifiedness at a point ascends along an isomorphism of the source. -/
private lemma unramifiedAt_precomp_iso
    {X X' Y : Scheme.{u}} (a : X' ⟶ X) [IsIso a] (f : X ⟶ Y) (x : X')
    (h : UnramifiedAt f (a x)) :
    UnramifiedAt (a ≫ f) x := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hAlg⟩ := h
  let U' := a ⁻¹ᵁ U
  have hU' : IsAffineOpen U' := hU.preimage a
  have hcontain : U' ≤ (a ≫ f) ⁻¹ᵁ V := fun _ hpoint => hUV hpoint
  have : IsIso (a.appLE U U' le_rfl) := by
    have : IsIso (a.app U) := a.isIso_app U (by
      rw [Scheme.Hom.opensRange_of_isIso]
      exact le_top)
    dsimp [Scheme.Hom.appLE]
    infer_instance
  refine ⟨U', hU', hxU, V, hV, hcontain, ?_⟩
  have hcomp : f.appLE V U hUV ≫ a.appLE U U' le_rfl =
      (a ≫ f).appLE V U' hcontain :=
    Scheme.Hom.appLE_comp_appLE a f V U U' hUV le_rfl
  rw [← hcomp, CommRingCat.hom_comp]
  exact ringHom_unramified_comp _ _ hAlg (ringHom_unramified_of_isIso _)

/-- Unramifiedness at a point ascends along an isomorphism of the target. -/
private lemma unramifiedAt_postcomp_iso
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (b : Y ⟶ Y') [IsIso b] (x : X)
    (h : UnramifiedAt f x) :
    UnramifiedAt (f ≫ b) x := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hAlg⟩ := h
  let V' := b ''ᵁ V
  have hV' : IsAffineOpen V' := hV.image_of_isOpenImmersion b
  have hVV' : V ≤ b ⁻¹ᵁ V' := (b.preimage_image_eq V).ge
  have hcontain : U ≤ (f ≫ b) ⁻¹ᵁ V' := fun _ hpoint => hVV' (hUV hpoint)
  have : IsIso (b.appLE V' V hVV') := by
    rw [← Scheme.Hom.appIso_hom' b V]
    infer_instance
  refine ⟨U, hU, hxU, V', hV', hcontain, ?_⟩
  have hcomp : b.appLE V' V hVV' ≫ f.appLE V U hUV =
      (f ≫ b).appLE V' U hcontain :=
    Scheme.Hom.appLE_comp_appLE f b V' V U hVV' hUV
  rw [← hcomp, CommRingCat.hom_comp]
  exact ringHom_unramified_comp _ _ (ringHom_unramified_of_isIso _) hAlg

/-- Unramifiedness at a point is unchanged by precomposition with an isomorphism. -/
private lemma unramifiedAt_precomp_iso_iff
    {X X' Y : Scheme.{u}} (a : X' ⟶ X) [IsIso a] (f : X ⟶ Y) (x : X') :
    UnramifiedAt (a ≫ f) x ↔ UnramifiedAt f (a x) := by
  refine ⟨fun h => ?_, unramifiedAt_precomp_iso a f x⟩
  have hpoint : (inv a) (a x) = x :=
    congrArg (fun morphism : X' ⟶ X' => morphism x) (IsIso.hom_inv_id a)
  simpa using unramifiedAt_precomp_iso (inv a) (a ≫ f) (a x) (hpoint.symm ▸ h)

/-- Unramifiedness at a point is unchanged by postcomposition with an isomorphism. -/
private lemma unramifiedAt_postcomp_iso_iff
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (b : Y ⟶ Y') [IsIso b] (x : X) :
    UnramifiedAt (f ≫ b) x ↔ UnramifiedAt f x :=
  ⟨fun h => by simpa using unramifiedAt_postcomp_iso (f ≫ b) (inv b) x h,
    unramifiedAt_postcomp_iso f b x⟩

/-- On a commutative group scheme, multiplication by `d` intertwines right translation by a point
with right translation by its `d`-th power. -/
lemma zpow_translation_commutes {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsCommMonObj G] (point : 𝟙_ (Over S) ⟶ G) (d : ℤ) :
    (GrpObj.mulRight point).hom ≫ (𝟙 G : G ⟶ G) ^ d =
      ((𝟙 G : G ⟶ G) ^ d) ≫ (GrpObj.mulRight (point ^ d)).hom := by
  have : IsMulCommutative (G ⟶ G) :=
    (isCommMonObj_iff_isMulCommutative G).mp inferInstance G
  calc
    (GrpObj.mulRight point).hom ≫ (𝟙 G : G ⟶ G) ^ d =
        ((𝟙 G : G ⟶ G) * (CartesianMonoidalCategory.toUnit G ≫ point)) ^ d := by
      rw [GrpObj.comp_zpow, Category.comp_id]
      rfl
    _ = (𝟙 G : G ⟶ G) ^ d * (CartesianMonoidalCategory.toUnit G ≫ point) ^ d :=
      mul_zpow _ _ _
    _ = ((𝟙 G : G ⟶ G) ^ d) ≫ (GrpObj.mulRight (point ^ d)).hom := by
      change _ = ((𝟙 G : G ⟶ G) ^ d) ≫
        ((𝟙 G : G ⟶ G) * (CartesianMonoidalCategory.toUnit G ≫ point ^ d))
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        CartesianMonoidalCategory.comp_toUnit, GrpObj.comp_zpow]

/-- On a commutative group scheme, multiplication by `d` is unramified at a translate of a point
exactly when it is unramified at the point. -/
private lemma zpow_unramifiedAt_translation {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsCommMonObj G] (point : 𝟙_ (Over S) ⟶ G) (d : ℤ) (x : G.left) :
    UnramifiedAt (((𝟙 G : G ⟶ G) ^ d).left)
      ((GrpObj.mulRight point).hom.left x) ↔
    UnramifiedAt (((𝟙 G : G ⟶ G) ^ d).left) x := by
  have : IsIso (GrpObj.mulRight point).hom.left :=
    ((Over.forget S).mapIso (GrpObj.mulRight point)).isIso_hom
  have : IsIso (GrpObj.mulRight (point ^ d)).hom.left :=
    ((Over.forget S).mapIso (GrpObj.mulRight (point ^ d))).isIso_hom
  rw [← unramifiedAt_precomp_iso_iff (GrpObj.mulRight point).hom.left]
  have hcomm := congrArg Over.Hom.left (zpow_translation_commutes G point d)
  simp only [Over.comp_left] at hcomm
  rw [hcomm]
  exact unramifiedAt_postcomp_iso_iff _ (GrpObj.mulRight (point ^ d)).hom.left x

/-- Right translation by a point sends the identity point to that point. -/
private lemma mulRight_identity_point {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (point : 𝟙_ (Over S) ⟶ G) (s : S) :
    (GrpObj.mulRight point).hom.left ((η[G]).left s) = point.left s := by
  have h : η[G] ≫ (GrpObj.mulRight point).hom = point := by
    change η[G] ≫ ((𝟙 G : G ⟶ G) * (CartesianMonoidalCategory.toUnit G ≫ point)) = point
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      CartesianMonoidalCategory.comp_toUnit, MonObj.one_eq_one]
    have hunit : CartesianMonoidalCategory.toUnit (𝟙_ (Over S)) = 𝟙 _ :=
      CartesianMonoidalCategory.toUnit_unique _ _
    rw [hunit, Category.id_comp, one_mul]
  exact congrArg (fun morphism : S ⟶ G.left => morphism s)
    (congrArg Over.Hom.left h)

/-- Multiplication by `d` on a group scheme locally of finite type is locally of finite type. -/
private lemma locallyOfFiniteType_zpow_id_left {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [LocallyOfFiniteType G.hom] (d : ℤ) : LocallyOfFiniteType ((𝟙 G : G ⟶ G) ^ d).left := by
  have : LocallyOfFiniteType (((𝟙 G : G ⟶ G) ^ d).left ≫ G.hom) :=
    ((𝟙 G : G ⟶ G) ^ d).w.symm ▸ inferInstance
  exact locallyOfFiniteType_of_comp _ G.hom

/-- For `d` invertible in `k`, multiplication by `d` on a group scheme locally of finite type
over `k` is unramified at the identity: its tangent map there is multiplication by `d`. -/
private lemma unramifiedAt_zpow_identity_of_isUnit
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] (s : Spec (.of k)) (d : ℤ) (hd : IsUnit (d : k)) :
    UnramifiedAt (((𝟙 G : G ⟶ G) ^ d).left) ((η[G]).left s) := by
  let f : G.left ⟶ G.left := ((𝟙 G : G ⟶ G) ^ d).left
  let e : G.left := (η[G]).left s
  have := isIso_residueFieldMap_zpow_id_left_unit k G s d
  have : LocallyOfFiniteType f := locallyOfFiniteType_zpow_id_left G d
  apply (injective_tangentMap_iff_unramifiedAt f G.hom G.hom e
    ((𝟙 G : G ⟶ G) ^ d).w).mp
  intro first second hEq
  have hfix : f e = e := zpow_id_left_apply_unit k G s d
  have htransport := congrArg
    (fun vector => (hfix ▸ vector :
      DottedTangentArrow G.hom e)) hEq
  have hsmul : d • first = d • second :=
    (zpow_tangentMap_apply_at_identity k G s d first).symm.trans
      (htransport.trans (zpow_tangentMap_apply_at_identity k G s d second))
  have hunit := (isUnit_intCast_residueField_iff k G.left G.hom e d).mpr hd
  exact smul_right_injective _ hunit.ne_zero
    (by simpa only [Int.cast_smul_eq_zsmul] using hsmul)

/-- Over an algebraically closed field, multiplication by an invertible `d` on a commutative
group scheme locally of finite type is unramified: the ramified locus is closed and would
contain a rational point, which translation moves to the identity. -/
private lemma unramified_zpow_of_isAlgClosed_of_isUnit
    (k : Type u) [Field k] [IsAlgClosed k] (G : Over (Spec (.of k))) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] (d : ℤ) (hd : IsUnit (d : k)) :
    Unramified (((𝟙 G : G ⟶ G) ^ d).left) := by
  let f : G.left ⟶ G.left := ((𝟙 G : G ⟶ G) ^ d).left
  have : LocallyOfFiniteType f := locallyOfFiniteType_zpow_id_left G d
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  refine ⟨fun x => ?_⟩
  by_contra hx
  let U : Set G.left := {point | UnramifiedAt f point}
  have hopen : IsOpen U := AlgebraicGeometry.isOpen_setOf_unramifiedAt f
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (show Uᶜ.Nonempty from ⟨x, hx⟩) hopen.isClosed_compl.isLocallyClosed
  let point : 𝟙_ (Over (Spec (.of k))) ⟶ G := Over.homMk
    ((pointEquivClosedPoint G.hom).symm ⟨y, hyclosed⟩).1
    ((pointEquivClosedPoint G.hom).symm ⟨y, hyclosed⟩).2
  have hpoint : point.left (IsLocalRing.closedPoint k) = y :=
    congrArg Subtype.val ((pointEquivClosedPoint G.hom).apply_symm_apply ⟨y, hyclosed⟩)
  have hidentity := unramifiedAt_zpow_identity_of_isUnit k G
    (IsLocalRing.closedPoint k) d hd
  have htranslation := (zpow_unramifiedAt_translation G point d
    ((η[G]).left (IsLocalRing.closedPoint k))).mpr hidentity
  have htranslatePoint := (mulRight_identity_point G point (IsLocalRing.closedPoint k)).trans
    hpoint
  exact hy (htranslatePoint ▸ htranslation)

/-- **Multiplication by an invertible integer on a commutative group scheme locally of finite
type over a field is unramified.** Over an algebraic closure the ramified locus is closed, and
translation by a rational point, which commutes with `[d]` up to a translation, would move a
closed ramified point to the identity, where the tangent map of `[d]` is multiplication by `d`;
unramifiedness descends from the base change to the algebraic closure. -/
theorem unramified_zpow_id_left_of_isUnit
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] (d : ℤ) (hd : IsUnit (d : k)) :
    Unramified (((𝟙 G : G ⟶ G) ^ d).left) := by
  let Ω := AlgebraicClosure k
  let base : Spec (.of Ω) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let F := Over.pullback base
  let G' := F.obj G
  let : GrpObj G' := Functor.grpObjObj
  let : IsCommMonObj G' :=
    (F.mapCommMon.obj (CommMon.mk G)).comm
  have : LocallyOfFiniteType G'.hom := by
    dsimp [G', F]
    infer_instance
  let original : G.left ⟶ G.left := ((𝟙 G : G ⟶ G) ^ d).left
  let shifted : G'.left ⟶ G'.left := ((𝟙 G' : G' ⟶ G') ^ d).left
  let projection : G'.left ⟶ G.left := CategoryTheory.Limits.pullback.fst G.hom base
  have hmap : F.map ((𝟙 G : G ⟶ G) ^ d) = (𝟙 G' : G' ⟶ G') ^ d := by
    simpa using (F.homMonoidHom (X := G) (M := G)).map_zpow (𝟙 G) d
  have hmapLeft : shifted = (F.map ((𝟙 G : G ⟶ G) ^ d)).left :=
    (congrArg Over.Hom.left hmap).symm
  have hcomm : shifted ≫ projection = projection ≫ original := by
    rw [hmapLeft]
    dsimp [F, Over.pullback, projection, original]
    exact CategoryTheory.Limits.pullback.lift_fst _ _ _
  have hcommBase : shifted ≫ G'.hom = G'.hom := ((𝟙 G' : G' ⟶ G') ^ d).w
  have hpull : IsPullback shifted projection projection original := by
    apply IsPullback.of_right (t := (IsPullback.of_hasPullback G.hom base).flip)
    · have horiginal : original ≫ G.hom = G.hom := ((𝟙 G : G ⟶ G) ^ d).w
      change IsPullback (shifted ≫ G'.hom) projection base (original ≫ G.hom)
      rw [hcommBase, horiginal]
      exact (IsPullback.of_hasPullback G.hom base).flip
    · exact hcomm
  have hunit : IsUnit (d : Ω) := by
    simpa only [map_intCast] using hd.map (algebraMap k Ω)
  have hunram := unramified_zpow_of_isAlgClosed_of_isUnit Ω G' d hunit
  have : LocallyOfFiniteType original := locallyOfFiniteType_zpow_id_left G d
  have : Surjective projection := by
    dsimp [projection, base]
    infer_instance
  refine ⟨fun x => ?_⟩
  obtain ⟨x', rfl⟩ := projection.surjective x
  exact (unramifiedAt_iff_of_isPullback hpull.flip x').mpr (hunram.unramifiedAt x')

/-- **The tangent map of multiplication by `d` at the identity of a group scheme over a field is
multiplication by `d`**, after transporting along the equality `[d] e = e`. -/
@[sga "3 II 3.9.4" "special case", sga "3 II 4.1.1.2" "b), special case"]
alias tangentMap_zpow_id_left_unit := zpow_tangentMap_apply_at_identity

/-- **If multiplication by `d` is unramified at the identity of an irreducible group scheme of
positive dimension, locally of finite type over a field `k`, then `d` is invertible in `k`.**
The tangent space at the identity is nonzero, and the tangent map of `[d]` there is
multiplication by `d`, which is injective by Tag 0B2G. -/
theorem isUnit_of_unramifiedAt_zpow_id_left_unit
    (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [LocallyOfFiniteType A.hom] [IrreducibleSpace A.left]
    (hA : 0 < topologicalKrullDim A.left) (s : Spec (.of k)) (d : ℤ)
    (h : UnramifiedAt (((𝟙 A : A ⟶ A) ^ d).left) ((η[A]).left s)) :
    IsUnit (d : k) := by
  let e : A.left := (η[A]).left s
  let f : A.left ⟶ A.left := ((𝟙 A : A ⟶ A) ^ d).left
  have := residueFieldMap_isIso_of_section A.hom (η[A]).left (η[A]).w s
  have := isIso_residueFieldMap_zpow_id_left_unit k A s d
  have : Nontrivial (DottedTangentArrow A.hom e) :=
    tangentArrow_nontrivial_of_positiveDimension k A.left A.hom e hA
  have : LocallyOfFiniteType f := locallyOfFiniteType_zpow_id_left A d
  have hfix : f e = e := zpow_id_left_apply_unit k A s d
  have hsmul : Function.Injective (fun v : DottedTangentArrow A.hom e => d • v) ↔
      IsUnit (d : k) := by
    rw [← isUnit_intCast_residueField_iff k A.left A.hom e d]
    simpa only [Int.cast_smul_eq_zsmul] using
      (smul_injective_iff_isUnit (M := DottedTangentArrow A.hom e)
        (d : A.left.residueField e))
  have hinj := (injective_tangentMap_iff_unramifiedAt f A.hom A.hom e
    ((𝟙 A : A ⟶ A) ^ d).w).mpr h
  refine hsmul.mp fun first second heq => hinj (tangentArrow_transport_injective A.hom hfix ?_)
  exact (zpow_tangentMap_apply_at_identity k A s d first).trans
    (heq.trans (zpow_tangentMap_apply_at_identity k A s d second).symm)

end Stacks.Groupoids

end
