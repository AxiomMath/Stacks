/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StalkIdentityComponent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StalkIdentityLocalCartier
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StalkTranslation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ReductionFinitePresentationLifting
public import StacksFrontier.AlgebraicGeometry.Properties.NilradicalStalkFG
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reducing the reducedness of group schemes in characteristic zero to the unit of a nice group

Let `G` be a group scheme over a field `k` of characteristic zero. This file reduces the
statement "`G` is reduced" to the local ring at the unit of a group scheme `H` over an
algebraically closed field `Ω` of characteristic zero which is irreducible, Jacobson, and whose
closed points are `Ω`-rational:

* every local ring of `G` maps by a flat local homomorphism to the local ring at the unit of a
  group scheme over a field extension of `k`
  (`AlgebraicGeometry.exists_flat_localHom_stalk_identity`), and reducedness descends along flat
  local homomorphisms (they are faithfully flat, hence injective);
* the local ring at the unit of a group scheme `H` over `K` maps by a flat local homomorphism to
  that of its base change to a large algebraically closed field `Ω`, which is Jacobson with
  rational closed points ([Stacks, Tag 0479]);
* the local ring at the unit is that of the identity component ([Stacks, Tag 0B7R]), which is
  connected, hence irreducible ([Stacks, Tag 0B7Q]); closed points of the identity component are
  closed points of the ambient group, and rational points lift along the closed immersion since
  `Spec Ω` is reduced.

## Main results

* `AlgebraicGeometry.isReduced_of_forall_isReduced_stalk_unit`: a group scheme over `k` is reduced
  as soon as every group scheme over every field extension of `k` has a reduced local ring at its
  unit.
* `AlgebraicGeometry.isReduced_of_forall_isReduced_stalk_unit_of_irreducible`: in characteristic
  zero it suffices to consider irreducible Jacobson group schemes over algebraically closed fields
  whose closed points are rational.
* `AlgebraicGeometry.isReduced_stalk_identity_of_lifting`: the local ring at the unit is reduced
  as soon as the lifting lemma `AlgebraicGeometry.exists_isAffineOpen_locallyOfFinitePresentation`
  applies to a reduced closed subgroup scheme with the same points (the reduction).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- Reducedness descends along a flat local homomorphism of local rings. -/
@[ega "IV 11.3.13" "clause (i), special case", ega "IV 2.1.13" "more general"]
lemma isReduced_of_flat_of_isLocalHom {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ] (hφ : φ.Flat) [_root_.IsReduced B] :
    _root_.IsReduced A := by
  have hff : φ.FaithfullyFlat := by
    algebraize [φ]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact isReduced_of_injective φ hff.injective

/-- A group scheme over a field `k` is reduced as soon as, for every field extension `K` of `k`
of the same characteristic, every group scheme over `K` has a reduced local ring at its unit. -/
theorem isReduced_of_forall_isReduced_stalk_unit {k : Type u} [Field k]
    (G : Grp (Over (Spec (CommRingCat.of k))))
    (h : ∀ (K : Type u) [Field K] [Algebra k K] (H : Over (Spec (CommRingCat.of K)))
      [GrpObj H], _root_.IsReduced (H.left.presheaf.stalk
        ((η[H]).left (IsLocalRing.closedPoint K)))) :
    IsReduced G.X.left := by
  have (g : G.X.left) : _root_.IsReduced (G.X.left.presheaf.stalk g) := by
    obtain ⟨K, _, _, H, _, φ, hloc, hflat⟩ := exists_flat_localHom_stalk_identity k G g
    have := h K H
    exact isReduced_of_flat_of_isLocalHom φ.hom hflat
  exact isReduced_of_isReduced_stalk _

attribute [local instance] Over.grpObjMkPullbackSnd in
/-- The unit of the base change of a group scheme lies over the unit. -/
lemma unit_left_pullbackFst {k K : Type u} [Field k] [Field K]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj (Over.mk G.hom)]
    (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    (η[Over.mk (pullback.snd G.hom g)]).left ≫ pullback.fst G.hom g =
      g ≫ (η[Over.mk G.hom]).left := by
  simp only [Over.grpObjMkPullbackSnd_one]
  simp

/-- A morphism from a reduced scheme whose image lies in the image of a closed immersion factors
through it. -/
lemma exists_lift_of_isClosedImmersion {X Y T : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    [IsReduced T] (f : T ⟶ Y) (hf : Set.range f ⊆ Set.range i) : ∃ g : T ⟶ X, g ≫ i = f := by
  obtain ⟨g, hg⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    i.ker f).2 (by
      rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
      exact hf)
  refine ⟨g ≫ inv i.toImage, ?_⟩
  calc (g ≫ inv i.toImage) ≫ i = (g ≫ inv i.toImage) ≫ (i.toImage ≫ i.imageι) :=
        congrArg ((g ≫ inv i.toImage) ≫ ·) i.toImage_imageι.symm
    _ = g ≫ i.imageι := by simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    _ = f := hg

attribute [local instance] Over.grpObjMkPullbackSnd in
open Stacks.AlgebraicGeometry.ClosedPointResidue in
/-- **Reduction to irreducible group schemes with rational closed points.** A group scheme over
a field `k` of characteristic zero is reduced as soon as every irreducible Jacobson group scheme,
over an algebraically closed field of characteristic zero, whose closed points are rational, has a
reduced local ring at its unit. -/
theorem isReduced_of_forall_isReduced_stalk_unit_of_irreducible {k : Type u} [Field k]
    [CharZero k] (G : Grp (Over (Spec (CommRingCat.of k))))
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
      (H : Grp (Over (Spec (CommRingCat.of Ω)))), IrreducibleSpace H.X.left →
      JacobsonSpace H.X.left →
      (∀ x ∈ closedPoints H.X.left, ∃ p : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ H.X,
        p.left (basePoint Ω) = x) →
      _root_.IsReduced (H.X.left.presheaf.stalk (identityPoint Ω H))) :
    IsReduced G.X.left := by
  refine isReduced_of_forall_isReduced_stalk_unit G fun K _ _ H _ ↦ ?_
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain ⟨κJ, hJ⟩ := jacobsonSpace_pullback_of_large_cardinality K H.left H.hom
  obtain ⟨κR, hR⟩ :=
    exists_cardinal_isAlgebraic_residueField_of_mem_closedPoints_baseChange K H.left H.hom
  let κ := max κJ κR
  let Ω := largeAlgebraicallyClosedField K κ
  let : Field Ω := by dsimp [Ω, largeAlgebraicallyClosedField]; infer_instance
  let : IsAlgClosed Ω := by dsimp [Ω, largeAlgebraicallyClosedField]; infer_instance
  let : Algebra K Ω := by dsimp [Ω, largeAlgebraicallyClosedField]; infer_instance
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hκ := cardinal_le_largeAlgebraicallyClosedField K κ
  let b : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let : GrpObj (Over.mk H.hom) := ‹GrpObj H›
  let H' : Over (Spec (.of Ω)) := Over.mk (pullback.snd H.hom b)
  let HG : Grp (Over (Spec (.of Ω))) := Grp.mk H'
  have : Subsingleton (Spec (.of K)) := show Subsingleton (PrimeSpectrum K) from inferInstance
  have : Subsingleton (Spec (.of Ω)) := show Subsingleton (PrimeSpectrum Ω) from inferInstance
  have hpt : pullback.fst H.hom b (identityPoint Ω HG) =
      (η[H]).left (IsLocalRing.closedPoint K) := by
    change ((η[H']).left ≫ pullback.fst H.hom b) _ = _
    rw [unit_left_pullbackFst H b, Scheme.Hom.comp_apply]
    exact congrArg _ (Subsingleton.elim _ _)
  suffices hred : _root_.IsReduced (H'.left.presheaf.stalk (identityPoint Ω HG)) by
    let φ := (H.left.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫
      (pullback.fst H.hom b).stalkMap (identityPoint Ω HG)
    have : IsLocalHom φ.hom := by
      dsimp only [φ]
      simp only [CommRingCat.hom_comp]
      infer_instance
    refine @isReduced_of_flat_of_isLocalHom _ _ _ _ _ _ φ.hom _ ?_ hred
    dsimp only [φ]
    simp only [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (Flat.stalkMap _ _)
  have hrat : ∀ x ∈ closedPoints H'.left, ∃ q : Spec (.of Ω) ⟶ H'.left,
      q ≫ H'.hom = 𝟙 _ ∧ Set.range q = {x} := by
    intro x hx
    let p := pullback.snd H.hom b
    let _ : (p x).asIdeal.IsPrime := (p x).isPrime
    let _ : Algebra Ω (H'.left.residueField x) :=
      ((CommRingCat.ofHom (algebraMap Ω (p x).asIdeal.ResidueField)) ≫
        (Scheme.Spec.residueFieldIso (.of Ω) (p x)).inv ≫ p.residueFieldMap x).hom.toAlgebra
    have hAlg : Algebra.IsAlgebraic Ω (H'.left.residueField x) :=
      hR Ω ((le_max_right κJ κR).trans hκ) x hx
    refine ⟨rationalPointOfClosedPoint Ω H'.left x hAlg,
      rationalPointOfClosedPoint_comp Ω H'.left p x hAlg rfl, ?_⟩
    have hq := rationalPointOfClosedPoint_apply Ω H'.left x hAlg
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨_, hq⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    obtain rfl : a = PrimeSpectrum.mk (⊥ : Ideal Ω) inferInstance := Subsingleton.elim _ _
    exact hq
  let C := identityComponent Ω HG
  let i := C.ι.hom.hom.left
  have : IsClosedImmersion i := C.isClosedImmersion
  have hie : Topology.IsClosedEmbedding i := i.isClosedEmbedding
  have hiw : i ≫ H'.hom = C.carrier.X.hom := Over.w C.ι.hom.hom
  suffices hC : _root_.IsReduced
      (C.carrier.X.left.presheaf.stalk (identityPoint Ω C.carrier)) from
    isReduced_of_injective (stalkIdentityComponentIso Ω HG).hom.hom
      (ConcreteCategory.bijective_of_isIso (stalkIdentityComponentIso Ω HG).hom).1
  have : ConnectedSpace C.carrier.X.left := by
    have hrange := identityComponent_range Ω HG
    have hpre : _root_.IsPreconnected (Set.univ : Set C.carrier.X.left) := by
      apply hie.isInducing.isPreconnected_image.mp
      rw [Set.image_univ]
      exact hrange ▸ isPreconnected_connectedComponent
    exact @ConnectedSpace.mk _ _ ⟨hpre⟩ ⟨identityPoint Ω C.carrier⟩
  have : JacobsonSpace H'.left := hJ Ω ((le_max_left κJ κR).trans hκ)
  refine h Ω C.carrier (irreducibleSpace_of_connectedSpace C.carrier.X)
    (JacobsonSpace.of_isClosedEmbedding hie) fun x hx ↦ ?_
  have hix : i x ∈ closedPoints H'.left := by
    rw [mem_closedPoints_iff, ← Set.image_singleton]
    exact hie.isClosedMap _ hx
  obtain ⟨q, hq, hqr⟩ := hrat _ hix
  obtain ⟨g, hg⟩ := exists_lift_of_isClosedImmersion i q
    (by rw [hqr]; exact Set.singleton_subset_iff.mpr ⟨x, rfl⟩)
  refine ⟨Over.homMk g ?_, hie.injective ?_⟩
  · change g ≫ C.carrier.X.hom = 𝟙 _
    rw [← hiw, ← Category.assoc, hg, hq]
  · change (g ≫ i) _ = i x
    rw [hg]
    exact hqr.subset ⟨_, rfl⟩

/-- Let `G` be a group scheme over a field of characteristic zero and `L` a reduced closed
subgroup scheme with the same points (the reduction of `G`). If the data of the lifting lemma
`AlgebraicGeometry.exists_isAffineOpen_locallyOfFinitePresentation` exist around the unit, then
the local ring of `G` at the unit is reduced. -/
theorem isReduced_stalk_identity_of_lifting (k : Type u) [Field k] [CharZero k]
    (G : Grp (Over (Spec (.of k)))) (L : ClosedSubgroupScheme G) [Surjective L.ι.hom.hom.left]
    [IsReduced L.carrier.X.left] {Z : Scheme.{u}} (iZ : Z ⟶ L.carrier.X.left)
    [LocallyOfFinitePresentation (iZ ≫ L.ι.hom.hom.left)]
    (V : L.carrier.X.left.Opens) (X : Over (Spec (.of k)))
    (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ L.carrier.X.hom) [QuasiCompact π] [Flat π]
    (U : G.X.left.Opens) (hUV : L.ι.hom.hom.left ⁻¹ᵁ U ≤ V) (π' : U.toScheme ⟶ X.left)
    (hπ'k : π' ≫ X.hom = U.ι ≫ G.X.hom)
    (hπ' : (L.ι.hom.hom.left ∣_ U) ≫ π' = L.carrier.X.left.homOfLE hUV ≫ π)
    (h : ∀ (T : Over (Spec (.of k))) (x y : T ⟶ L.carrier.X) (x' y' : T.left ⟶ V.toScheme),
      x' ≫ V.ι = x.left → y' ≫ V.ι = y.left → x' ≫ π = y' ≫ π →
      letI := Hom.group (X := T) (G := L.carrier.X)
      ∃ z : T.left ⟶ Z, z ≫ iZ = (x⁻¹ * y).left)
    (he : identityPoint k G ∈ U) :
    _root_.IsReduced (G.X.left.presheaf.stalk (identityPoint k G)) := by
  obtain ⟨U', heU', -, hU', hfp⟩ := exists_isAffineOpen_locallyOfFinitePresentation k G L iZ V X
    π hπ U hUV π' hπ'k hπ' h (identityPoint k G) he
  have : IsClosedImmersion L.ι.hom.hom.left := L.isClosedImmersion
  exact isReduced_stalk_identity_of_fg_nilradical k G
    (fg_nilradical_stalk_of_locallyOfFinitePresentation L.ι.hom.hom.left hU' heU')

end AlgebraicGeometry

end
