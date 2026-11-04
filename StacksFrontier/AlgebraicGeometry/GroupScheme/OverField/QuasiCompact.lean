module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.JacobsonSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Varieties.ClosedPointResidue
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.IdentityComponentGeometric
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Jacobson
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Multiplication
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction

/-!
# Quasi-compactness of irreducible group schemes over fields

An irreducible group scheme over a field is quasi-compact.  After base change to a large
algebraically closed field the scheme stays irreducible and becomes Jacobson with rational
closed points, so an affine open neighbourhood of the identity and its translates cover it:
the quotient map from the square of that open is open with closed image complement, and a
closed point in the complement would be a product of two points of the open.

## Main definitions

* `AlgebraicGeometry.largeAlgebraicallyClosedField` is an algebraically closed extension of a
  prescribed cardinality.
* `AlgebraicGeometry.rationalPointOfClosedPoint` is the rational point at a closed point with
  algebraic residue field over an algebraically closed base.
* `AlgebraicGeometry.leftTranslation` is translation of a group object by a global point.

## Main results

* `AlgebraicGeometry.compactSpace_of_irreducibleSpace_grpObj` states that the underlying space
  of an irreducible group scheme over a field is compact.

## Implementation notes

A group scheme over `k` is represented as a group object in the category of schemes over
`Spec k`.  Quasi-compactness of a scheme is expressed by `CompactSpace` on its underlying
topological space.

## References

* [Stacks Project, Tag 0B7P](https://stacks.math.columbia.edu/tag/0B7P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open Stacks.AlgebraicGeometry.ClosedPointResidue
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory CategoryTheory.Obj

namespace AlgebraicGeometry

universe u

/-- An irreducible group scheme over a field is geometrically irreducible after passing to its
reduction. -/
@[sga "3 VIA 2.6.5" "more general"]
private theorem groupScheme_geometricallyIrreducible
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [IrreducibleSpace G.left] :
    GeometricallyIrreducible (G.left.nilradical.subschemeι ≫ G.hom) := by
  have hG : G = Over.mk G.hom := by
    cases G
    rfl
  let _ : GrpObj (Over.mk G.hom) := hG ▸ (inferInstance : GrpObj G)
  let Z : irreducibleComponents G.left := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]
    simp⟩
  have he : Set.range (η[Over.mk G.hom].left) ⊆ Z.1 := fun x _ => Set.mem_univ x
  have h := geometricallyIrreducible_irreducibleComponent_of_identity k G.left G.hom Z he
  have hZtop :
      (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
        TopologicalSpace.Closeds G.left) = ⊤ := by
    ext x
    simp [Z]
  rwa [hZtop, Scheme.IdealSheafData.vanishingIdeal_top] at h

/-- Geometric irreducibility of the reduction makes every base change irreducible, because the
reduction is a universal homeomorphism. -/
theorem irreducibleSpace_pullback_of_geometricallyIrreducible_reduction
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hgeom : GeometricallyIrreducible (X.nilradical.subschemeι ≫ f))
    (K : Type u) [Field K] (g : Spec (.of K) ⟶ S) :
    IrreducibleSpace ↥(pullback f g) := by
  let r := X.nilradical.subschemeι
  have hred : IrreducibleSpace ↥(pullback (r ≫ f) g) :=
    pullback_of_geometrically hgeom.geometrically_irreducibleSpace K g
  let _ : UniversalHomeomorphism r :=
    AlgebraicGeometry.universalHomeomorphism_nilradical_subschemeι X
  have hbase : IrreducibleSpace ↥(pullback r (pullback.fst f g)) :=
    (pullbackRightPullbackFstIso f g r).hom.homeomorph.irreducibleSpace_iff.mpr hred
  have hbase' : IrreducibleSpace ↥(pullback (pullback.fst f g) r) :=
    (pullbackSymmetry r (pullback.fst f g)).hom.homeomorph.irreducibleSpace_iff.mp hbase
  exact (UniversalHomeomorphism.universally_isHomeomorph _ _ _
    (IsPullback.of_hasPullback (pullback.fst f g) r)).homeomorph.irreducibleSpace_iff.mp hbase'

/-- An algebraically closed extension field of cardinality at least `κ`, obtained as the
algebraic closure of a rational function field in `κ` variables. -/
@[ega "IV 10.10.5"]
noncomputable def largeAlgebraicallyClosedField
    (k : Type u) [Field k] (κ : Cardinal.{u}) : Type u :=
  AlgebraicClosure (FractionRing (MvPolynomial κ.out k))

/-- The prescribed cardinal bounds the cardinality of `largeAlgebraicallyClosedField`. -/
theorem cardinal_le_largeAlgebraicallyClosedField
    (k : Type u) [Field k] (κ : Cardinal.{u}) :
    κ ≤ Cardinal.mk (largeAlgebraicallyClosedField k κ) := by
  let F := MvPolynomial κ.out k
  let L := FractionRing F
  let K := AlgebraicClosure L
  have hinj : Function.Injective (fun a : κ.out => algebraMap F K (MvPolynomial.X a)) := by
    intro a b h
    change algebraMap L K (algebraMap F L (MvPolynomial.X a)) =
      algebraMap L K (algebraMap F L (MvPolynomial.X b)) at h
    exact MvPolynomial.X_injective
      (IsFractionRing.injective F L (FaithfulSMul.algebraMap_injective L K h))
  exact (Cardinal.mk_out κ).symm.le.trans (Cardinal.mk_le_of_injective hinj)

/-- Over an algebraically closed field, an algebraic residue field is the field itself. -/
noncomputable def closedPointAlgebraEquiv
    (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u}) (x : X)
    [Algebra K (X.residueField x)]
    (hAlg : Algebra.IsAlgebraic K (X.residueField x)) : K ≃+* X.residueField x := by
  let E := X.residueField x
  let _ : Algebra.IsIntegral K E := Algebra.isAlgebraic_iff_isIntegral.mp hAlg
  exact RingEquiv.ofBijective (algebraMap K E)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := E))

/-- The `K`-rational point at a closed point whose residue field is algebraic over an
algebraically closed field `K`. -/
noncomputable def rationalPointOfClosedPoint
    (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u}) (x : X)
    [Algebra K (X.residueField x)]
    (hAlg : Algebra.IsAlgebraic K (X.residueField x)) : Spec (.of K) ⟶ X :=
  Spec.map (CommRingCat.ofHom (closedPointAlgebraEquiv K X x hAlg).symm.toRingHom) ≫
    X.fromSpecResidueField x

/-- The rational point at a closed point hits that point. -/
theorem rationalPointOfClosedPoint_apply
    (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u}) (x : X)
    [Algebra K (X.residueField x)]
    (hAlg : Algebra.IsAlgebraic K (X.residueField x)) :
    (rationalPointOfClosedPoint K X x hAlg).base
      (PrimeSpectrum.mk (⊥ : Ideal K) inferInstance) = x := by
  simp only [rationalPointOfClosedPoint]
  exact Scheme.fromSpecResidueField_apply x _

/-- The rational point at a closed point of a `K`-scheme is a section of its structure
morphism. -/
theorem rationalPointOfClosedPoint_comp
    (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) (x : X) [(f x).asIdeal.IsPrime]
    [Algebra K (X.residueField x)]
    (hAlg : Algebra.IsAlgebraic K (X.residueField x))
    (hcanonical : CommRingCat.ofHom (algebraMap K (f x).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of K) (f x)).inv ≫ f.residueFieldMap x =
        CommRingCat.ofHom (algebraMap K (X.residueField x))) :
    rationalPointOfClosedPoint K X x hAlg ≫ f = 𝟙 _ := by
  let e := closedPointAlgebraEquiv K X x hAlg
  dsimp [rationalPointOfClosedPoint]
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := f) x,
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
  show CommRingCat.ofHom (algebraMap K (f x).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (.of K) (f x)).inv ≫ f.residueFieldMap x ≫
        CommRingCat.ofHom e.symm.toRingHom = 𝟙 (CommRingCat.of K)
  calc
    _ = CommRingCat.ofHom (algebraMap K (X.residueField x)) ≫
          CommRingCat.ofHom e.symm.toRingHom :=
      congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of (X.residueField x) =>
        h ≫ CommRingCat.ofHom e.symm.toRingHom) hcanonical
    _ = 𝟙 _ := by
      ext a
      exact e.symm_apply_apply a

/-- An affine scheme is quasi-compact. -/
private theorem compactSpace_of_isAffine (X : Scheme.{u}) [IsAffine X] : CompactSpace X :=
  Homeomorph.compactSpace (Scheme.homeoOfIso X.isoSpec).symm

/-- The quotient map `U ⊗ U ⟶ G` of an object mapping to a group object, sending `(u, v)` to
`u v⁻¹`. -/
private noncomputable def quotientFromOpen
    {B : Scheme.{u}} (G U : Over B) [GrpObj G] (i : U ⟶ G) : U ⊗ U ⟶ G :=
  (fst U U ≫ i) / (snd U U ≫ i)

/-- Left translation of a group object by a global point. -/
@[ega "IV 17.12.7"]
noncomputable def leftTranslation
    {B : Scheme.{u}} (G : Over B) [GrpObj G]
    (p : (𝟙_ (Over B)) ⟶ G) : G ⟶ G :=
  (toUnit G ≫ p) * 𝟙 G

/-- Left translations compose. -/
theorem leftTranslation_comp
    {B : Scheme.{u}} (G : Over B) [GrpObj G]
    (p q : (𝟙_ (Over B)) ⟶ G) :
    leftTranslation G p ≫ leftTranslation G q = leftTranslation G (q * p) := by
  calc
    leftTranslation G p ≫ leftTranslation G q =
        leftTranslation G p ≫ ((toUnit G ≫ q) * 𝟙 G) := rfl
    _ = (leftTranslation G p ≫ (toUnit G ≫ q)) *
          (leftTranslation G p ≫ 𝟙 G) := MonObj.comp_mul _ _ _
    _ = (toUnit G ≫ q) * leftTranslation G p := by simp
    _ = (toUnit G ≫ q) * ((toUnit G ≫ p) * 𝟙 G) := rfl
    _ = ((toUnit G ≫ q) * (toUnit G ≫ p)) * 𝟙 G := by simp [mul_assoc]
    _ = (toUnit G ≫ (q * p)) * 𝟙 G := by rw [← MonObj.comp_mul (toUnit G) q p]
    _ = leftTranslation G (q * p) := rfl

/-- Left translation by a global point is an automorphism. -/
@[ega "IV 17.12.7"]
private noncomputable def leftTranslationIso
    {B : Scheme.{u}} (G : Over B) [GrpObj G]
    (p : (𝟙_ (Over B)) ⟶ G) : G ≅ G where
  hom := leftTranslation G p
  inv := leftTranslation G p⁻¹
  hom_inv_id := by
    rw [leftTranslation_comp, inv_mul_cancel]
    simp [leftTranslation]
  inv_hom_id := by
    rw [leftTranslation_comp, mul_inv_cancel]
    simp [leftTranslation]

/-- Inversion of a group object is an involution. -/
private theorem grpObj_inv_involutive {C : Type u} [Category C]
    [CartesianMonoidalCategory C] (G : C) [GrpObj G] :
    ι[G] ≫ ι[G] = 𝟙 G := by
  rw [← Hom.inv_def, GrpObj.inv_eq_inv, inv_inv]

/-- The quotient map factors as the product of the inclusion with inversion on the second
factor, followed by multiplication. -/
private theorem quotientFromOpen_eq_tensor
    {B : Scheme.{u}} (G U : Over B) [GrpObj G] (i : U ⟶ G) :
    quotientFromOpen G U i =
      (i ⊗ₘ i) ≫ (𝟙 G ⊗ₘ ι[G]) ≫ μ[G] := by
  show lift (fst U U ≫ i) (snd U U ≫ i ≫ ι[G]) ≫ μ[G] =
    (i ⊗ₘ i) ≫ (𝟙 G ⊗ₘ ι[G]) ≫ μ[G]
  have hp : lift (fst U U ≫ i) (snd U U ≫ i ≫ ι[G]) =
      (i ⊗ₘ i) ≫ (𝟙 G ⊗ₘ ι[G]) := by
    apply hom_ext <;> simp
  rw [hp, Category.assoc]

/-- The quotient map out of the square of an open subscheme of a group scheme over a field is
an open map. -/
private theorem isOpenMap_quotientFromOpen
    (K : Type u) [Field K] (G U : Over (Spec (.of K))) [GrpObj G]
    (i : U ⟶ G) [IsOpenImmersion i.left] :
    IsOpenMap (quotientFromOpen G U i).left := by
  let _ : IsIso ι[G] := ⟨⟨ι[G], grpObj_inv_involutive G, grpObj_inv_involutive G⟩⟩
  let _ : IsIso (𝟙 G ⊗ₘ ι[G]) := inferInstance
  have hiProd : IsOpenImmersion (i ⊗ₘ i).left := by
    rw [Over.tensorHom_left]
    infer_instance
  have hi : IsOpenMap (i ⊗ₘ i).left := Scheme.Hom.isOpenMap _
  have ht : IsOpenMap (𝟙 G ⊗ₘ ι[G]).left :=
    ((Over.forget (Spec (.of K))).mapIso (asIso (𝟙 G ⊗ₘ ι[G]))).hom.homeomorph.isOpenMap
  have hm : IsOpenMap μ[G].left := isOpenMap_mul G
  rw [quotientFromOpen_eq_tensor]
  show IsOpenMap ((i ⊗ₘ i).left ≫ (𝟙 G ⊗ₘ ι[G]).left ≫ μ[G].left)
  simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_assoc] using
    IsOpenMap.comp hm (IsOpenMap.comp ht hi)

/-- The quotient map evaluated on a pair of global points of the open subscheme. -/
private theorem quotientFromOpen_lift
    {B : Scheme.{u}} (G U : Over B) [GrpObj G] (i : U ⟶ G)
    (u v : (𝟙_ (Over B)) ⟶ U) :
    lift u v ≫ quotientFromOpen G U i = (u ≫ i) / (v ≫ i) := by
  simp [quotientFromOpen, GrpObj.comp_div]

/-- **Stacks Project, Tag 0B7P.** An irreducible group scheme over a field is quasi-compact. -/
@[stacks 0B7P, sga "3 VIA 0.5.1", sga "3 VIA 2.6.5" "more general"]
instance compactSpace_of_irreducibleSpace_grpObj
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [IrreducibleSpace G.left] : CompactSpace G.left := by
  obtain ⟨κJ, hJ⟩ := jacobsonSpace_pullback_of_large_cardinality k G.left G.hom
  obtain ⟨κR, hR⟩ :=
    exists_cardinal_isAlgebraic_residueField_of_mem_closedPoints_baseChange
      k G.left G.hom
  let κ := max κJ κR
  let K := largeAlgebraicallyClosedField k κ
  let _ : Field K := by dsimp [K, largeAlgebraicallyClosedField]; infer_instance
  let _ : IsAlgClosed K := by dsimp [K, largeAlgebraicallyClosedField]; infer_instance
  let _ : Algebra k K := by dsimp [K, largeAlgebraicallyClosedField]; infer_instance
  have hKlarge := cardinal_le_largeAlgebraicallyClosedField k κ
  have hKJ : κJ ≤ Cardinal.mk K := by
    simpa [K, κ] using (le_max_left κJ κR).trans hKlarge
  have hKR : κR ≤ Cardinal.mk K := by
    simpa [K, κ] using (le_max_right κJ κR).trans hKlarge
  let g : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let H := pullback G.hom g
  have hG : G = Over.mk G.hom := by cases G; rfl
  let _ : GrpObj (Over.mk G.hom) := hG ▸ (inferInstance : GrpObj G)
  let Hgrp : Over (Spec (.of K)) := Over.mk (pullback.snd G.hom g)
  let _ : GrpObj Hgrp := Over.grpObjMkPullbackSnd
  have : IrreducibleSpace Hgrp.left :=
    irreducibleSpace_pullback_of_geometricallyIrreducible_reduction G.hom
      (groupScheme_geometricallyIrreducible k G) K g
  have : JacobsonSpace Hgrp.left := hJ K hKJ
  let ptK : Spec (.of K) := PrimeSpectrum.mk ⊥ inferInstance
  let x₀ : H := (η[Hgrp].left.base) ptK
  obtain ⟨V, hV⟩ := H.isBasis_affineOpens.isOpenCover.exists_mem x₀
  let U : Over (Spec (.of K)) :=
    Over.mk (Scheme.Opens.ι V.1 ≫ pullback.snd G.hom g)
  let i : U ⟶ Hgrp := Over.homMk (Scheme.Opens.ι V.1) (by simp [U, Hgrp])
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι V.1))
  have : Nonempty U.left := ⟨⟨x₀, hV⟩⟩
  have : IsAffine U.left := V.property
  have : IsAffine (U ⊗ U).left := inferInstanceAs (IsAffine (pullback U.hom U.hom))
  have : CompactSpace (U ⊗ U).left := compactSpace_of_isAffine _
  have hqrange : Set.range (quotientFromOpen Hgrp U i).left.base = Set.univ := by
    have hpt : ∀ x ∈ closedPoints Hgrp.left, ∃ p : Spec (.of K) ⟶ Hgrp.left,
        p ≫ Hgrp.hom = 𝟙 _ ∧ p.base ptK = x := by
      intro y hyclosed
      let pProj := pullback.snd G.hom g
      let _ : (pProj y).asIdeal.IsPrime := (pProj y).isPrime
      let _ : Algebra K (H.residueField y) :=
        ((CommRingCat.ofHom (algebraMap K (pProj y).asIdeal.ResidueField)) ≫
          (Scheme.Spec.residueFieldIso (.of K) (pProj y)).inv ≫
          pProj.residueFieldMap y).hom.toAlgebra
      have hyAlg : Algebra.IsAlgebraic K (H.residueField y) := by
        dsimp [H] at hyclosed ⊢
        exact hR K hKR y hyclosed
      exact ⟨rationalPointOfClosedPoint K H y hyAlg,
        rationalPointOfClosedPoint_comp K H pProj y hyAlg rfl,
        by simpa [ptK] using rationalPointOfClosedPoint_apply K H y hyAlg⟩
    have hfac (j : U ⟶ Hgrp) [IsOpenImmersion j.left] (p : 𝟙_ (Over (Spec (.of K))) ⟶ Hgrp)
        (h : Set.range p.left.base ⊆ Set.range j.left.base) :
        ∃ l : 𝟙_ (Over (Spec (.of K))) ⟶ U, l ≫ j = p :=
      ⟨Over.homMk (IsOpenImmersion.lift j.left p.left h)
        (by rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w p]),
        by ext; simp [IsOpenImmersion.lift_fac]⟩
    rw [Set.range_eq_univ]
    intro x
    by_contra hx
    have hqopen : IsOpen (Set.range (quotientFromOpen Hgrp U i).left.base) := by
      simpa using isOpenMap_quotientFromOpen K Hgrp U i Set.univ isOpen_univ
    obtain ⟨y, hycomp, hyclosed⟩ := nonempty_inter_closedPoints
      (show (Set.range (quotientFromOpen Hgrp U i).left.base)ᶜ.Nonempty from
        ⟨x, by simpa using hx⟩) hqopen.isClosed_compl.isLocallyClosed
    obtain ⟨qy, hqy, hqyapply⟩ := hpt y hyclosed
    let px : 𝟙_ (Over (Spec (.of K))) ⟶ Hgrp := Over.homMk qy hqy
    let tr := leftTranslationIso Hgrp px
    have : IsIso tr.hom.left := by
      change IsIso ((Over.forget (Spec (.of K))).map tr.hom)
      infer_instance
    have : IsOpenImmersion (i ≫ tr.hom).left :=
      inferInstanceAs (IsOpenImmersion (i.left ≫ tr.hom.left))
    have hUopen : IsOpen (Set.range i.left.base) := by
      simpa using Scheme.Hom.isOpenMap i.left Set.univ isOpen_univ
    have htrOpen : IsOpen (Set.range (i.left ≫ tr.hom.left).base) := by
      simpa using Scheme.Hom.isOpenMap (i.left ≫ tr.hom.left) Set.univ isOpen_univ
    obtain ⟨z, ⟨hzU, hztr⟩, hzclosed⟩ := nonempty_inter_closedPoints
      (nonempty_preirreducible_inter hUopen htrOpen (Set.range_nonempty _) (Set.range_nonempty _))
      (hUopen.inter htrOpen).isLocallyClosed
    obtain ⟨qz, hqz, hqzapply⟩ := hpt z hzclosed
    let pz : 𝟙_ (Over (Spec (.of K))) ⟶ Hgrp := Over.homMk qz hqz
    have : Subsingleton (Spec (.of K)) :=
      (show Subsingleton (PrimeSpectrum K) from
        PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (Field.toIsField K))
    have hsub (s : Set Hgrp.left) (hz : z ∈ s) : Set.range qz.base ⊆ s := by
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a ptK, hqzapply]
    obtain ⟨b, hb⟩ := hfac i pz (hsub _ hzU)
    obtain ⟨a, ha⟩ := hfac (i ≫ tr.hom) pz (hsub _ hztr)
    have htranslate : a ≫ i ≫ tr.hom = px * (a ≫ i) := by
      change (a ≫ i) ≫ ((toUnit Hgrp ≫ px) * 𝟙 Hgrp) = _
      rw [MonObj.comp_mul]
      simp
    have hquot : (b ≫ i) / (a ≫ i) = px := by
      rw [hb.trans ha.symm, htranslate]
      simp [div_eq_mul_inv, mul_assoc]
    have hqpoint : (quotientFromOpen Hgrp U i).left.base ((lift b a).left.base ptK) = y := by
      have hp : (lift b a).left ≫ (quotientFromOpen Hgrp U i).left = (b ≫ i / a ≫ i).left := by
        simpa using congrArg Over.Hom.left (quotientFromOpen_lift Hgrp U i b a)
      rw [← Scheme.Hom.comp_apply, hp, hquot]
      exact hqyapply
    exact hycomp (by simpa using ⟨(lift b a).left.base ptK, hqpoint⟩)
  have : CompactSpace H := by
    rw [← isCompact_univ_iff, ← hqrange]
    exact isCompact_range (Scheme.Hom.continuous (quotientFromOpen Hgrp U i).left)
  have : Subsingleton (Spec (.of k)) :=
    (show Subsingleton (PrimeSpectrum k) from
      PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (Field.toIsField k))
  have : Nonempty (Spec (.of K)) := ⟨ptK⟩
  have : Surjective g := ⟨fun x => ⟨ptK, Subsingleton.elim _ _⟩⟩
  exact (pullback.fst G.hom g).surjective.compactSpace (pullback.fst G.hom g).continuous

end AlgebraicGeometry

end
