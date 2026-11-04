module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationFunctorial.Basic
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationCharacterization.Basic
public import StacksFrontier.AlgebraicGeometry.AffineLocal.Basic

/-!
# Absolute weak normalization and restriction to an affine open

Let `A → B` be a ring map for which `Spec B ⟶ Spec A` is an open immersion. Then the absolute
weak normalization of `A` tensored up to `B` is the absolute weak normalization of `B`: there is
a unique ring isomorphism `B ⊗[A] A^awn ≃+* B^awn` compatible with the maps from `B` and from
`A^awn`.

## Main results

* `AlgebraicGeometry.seminormalRing_of_ringEquiv` and
  `AlgebraicGeometry.absolutelyWeaklyNormalRing_of_ringEquiv`: seminormality and absolute weak
  normality transport along a ring isomorphism.
* `AlgebraicGeometry.exists_absoluteWeakNormalization_tensorProduct_equiv`: the unique
  isomorphism `B ⊗[A] A^awn ≃+* B^awn` above.

## Implementation notes

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

## References

* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open scoped TensorProduct

universe u

namespace AlgebraicGeometry


open Algebra

/-- Seminormality transports along a ring isomorphism. -/
public theorem seminormalRing_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (hR : IsSeminormalRing R) :
    IsSeminormalRing S := by
  rw [isSeminormalRing_iff] at hR ⊢
  intro x y hxy
  have hxy' : e.symm x ^ 3 = e.symm y ^ 2 := e.injective (by simpa using hxy)
  obtain ⟨a, ha, huniq⟩ := hR (e.symm x) (e.symm y) hxy'
  refine ⟨e a, ⟨by simpa using congrArg e ha.1, by simpa using congrArg e ha.2⟩, fun b hb => ?_⟩
  simpa using congrArg e (huniq (e.symm b)
    ⟨by simpa using congrArg e.symm hb.1, by simpa using congrArg e.symm hb.2⟩)

/-- Absolute weak normality transports along a ring isomorphism. -/
public theorem absolutelyWeaklyNormalRing_of_ringEquiv {R S : Type u}
    [CommRing R] [CommRing S] (e : R ≃+* S)
    (hR : IsAbsolutelyWeaklyNormalRing R) :
    IsAbsolutelyWeaklyNormalRing S := by
  rw [isAbsolutelyWeaklyNormalRing_iff] at hR ⊢
  refine ⟨seminormalRing_of_ringEquiv e hR.1, ?_⟩
  intro p hp x y hxy
  have hxy' : (p : R) ^ p * e.symm x = e.symm y ^ p := e.injective (by simpa using hxy)
  obtain ⟨a, ha, huniq⟩ := hR.2 p hp (e.symm x) (e.symm y) hxy'
  refine ⟨e a, ⟨by simpa using congrArg e ha.1, by simpa using congrArg e ha.2⟩, fun b hb => ?_⟩
  simpa using congrArg e (huniq (e.symm b)
    ⟨by simpa using congrArg e.symm hb.1, by simpa using congrArg e.symm hb.2⟩)

/-- The global sections of an affine scheme isomorphic to `Spec R` are isomorphic to `R`. -/
private theorem nonempty_globalSections_ringEquiv {R : Type u} [CommRing R]
    (Y : Scheme) (e : Spec (.of R) ≅ Y) : Nonempty (Γ(Y, ⊤) ≃+* R) := by
  have himg : e.hom ''ᵁ (⊤ : (Spec (.of R)).Opens) = (⊤ : Y.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  exact ⟨((eqToIso (congrArg (fun V : Y.Opens => CommRingCat.of Γ(Y, V)) himg.symm) ≪≫
      e.hom.appIso ⊤) ≪≫ Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv⟩

private theorem seminormalRing_of_affineSpecIso {R : Type u} [CommRing R]
    (Y : Scheme) [IsAffine Y] (e : Spec (.of R) ≅ Y)
    (hY : IsSeminormal Y) : IsSeminormalRing R := by
  have hiff : IsSeminormal Y ↔
      (∀ V : Y.affineOpens, IsSeminormalRing Γ(Y, V)) :=
    (isSeminormal_tfae Y).out 1 2
  have hSections : IsSeminormalRing Γ(Y, ⊤) :=
    hiff.mp hY ⟨⊤, isAffineOpen_top Y⟩
  exact seminormalRing_of_ringEquiv (nonempty_globalSections_ringEquiv Y e).some hSections

private theorem absolutelyWeaklyNormalRing_of_affineSpecIso {R : Type u} [CommRing R]
    (Y : Scheme) [IsAffine Y] (e : Spec (.of R) ≅ Y)
    (hY : IsAbsolutelyWeaklyNormal Y) :
    IsAbsolutelyWeaklyNormalRing R := by
  have hiff : IsAbsolutelyWeaklyNormal Y ↔
      (∀ V : Y.affineOpens, IsAbsolutelyWeaklyNormalRing Γ(Y, V)) :=
    (isAbsolutelyWeaklyNormal_tfae Y).out 1 2
  have hSections : IsAbsolutelyWeaklyNormalRing Γ(Y, ⊤) :=
    hiff.mp hY ⟨⊤, isAffineOpen_top Y⟩
  exact absolutelyWeaklyNormalRing_of_ringEquiv (nonempty_globalSections_ringEquiv Y e).some
    hSections

private theorem seminormal_spec_of_ring {R : Type u} [CommRing R]
    (hR : IsSeminormalRing R) :
    IsSeminormal (Spec (.of R)) := by
  intro x
  refine ⟨⟨⊤, isAffineOpen_top (Spec (.of R))⟩, Set.mem_univ _, ?_⟩
  change IsSeminormalRing Γ(Spec (.of R), ⊤)
  exact seminormalRing_of_ringEquiv
    ((Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv) hR

private theorem absolutelyWeaklyNormal_spec_of_ring {R : Type u} [CommRing R]
    (hR : IsAbsolutelyWeaklyNormalRing R) :
    IsAbsolutelyWeaklyNormal (Spec (.of R)) := by
  intro x
  refine ⟨⟨⊤, isAffineOpen_top (Spec (.of R))⟩, Set.mem_univ _, ?_⟩
  change IsAbsolutelyWeaklyNormalRing Γ(Spec (.of R), ⊤)
  exact absolutelyWeaklyNormalRing_of_ringEquiv
    ((Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv) hR

/-- Absolute weak normalization commutes with restriction to an affine open, with the
identification fixed by the two canonical maps into the tensor product. -/
public theorem exists_absoluteWeakNormalization_tensorProduct_equiv
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsOpenImmersion (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)] :
    ∃! e : (B ⊗[A] AbsoluteWeakNormalization A) ≃+* AbsoluteWeakNormalization B,
      (e.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := A)
        (A := B) (B := AbsoluteWeakNormalization A)) =
          algebraMap B (AbsoluteWeakNormalization B)) ∧
      (e.toRingHom.comp ((Algebra.TensorProduct.includeRight (R := A)
        (A := B) (B := AbsoluteWeakNormalization A)).toRingHom) =
          Classical.choose (existsUnique_absoluteWeakNormalizationMap
            (algebraMap A B))) := by
  let N := AbsoluteWeakNormalization A
  let C := B ⊗[A] N
  let fN : Spec (.of N) ⟶ Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op
  let fB : Spec (.of B) ⟶ Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  let iso := pullbackSpecIso A B N
  let q : Spec (.of C) ⟶ pullback fB fN := iso.inv
  let jB : Spec (.of C) ⟶ Spec (.of B) := q ≫ pullback.fst fB fN
  let jN : Spec (.of C) ⟶ Spec (.of N) := q ≫ pullback.snd fB fN
  have hN : UniversalHomeomorphism fN :=
    absoluteWeakNormalization_universalHomeomorphism A
  have hJ : UniversalHomeomorphism jB :=
    ⟨(topologically @IsHomeomorph).universally.cancel_left_of_respectsIso iso.inv
      (pullback.fst fB fN) |>.mpr ((topologically @IsHomeomorph).universally.pullback_fst fB fN
        hN.universally_isHomeomorph)⟩
  have hSpecB :
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap B C)).op = jB := by
    change Scheme.Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := N))).op = _
    exact (pullbackSpecIso_inv_fst A B N).symm
  have hJ' : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap B C)).op) := hSpecB ▸ hJ
  let U : (Spec (.of N)).Opens := jN.opensRange
  let e : Spec (.of C) ≅ U.toScheme :=
    IsOpenImmersion.isoOfRangeEq jN U.ι (by
      rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange])
  let : IsAffine U.toScheme := IsAffine.of_isIso e.inv
  have hNobj : absoluteWeakNormalizationCategoryObject A =
      (⟨CommAlgCat.of A N, hN⟩ : AbsoluteWeakNormalizationCategory A) := by
    ext
    rfl
  have hNself : IsIso ((absoluteWeakNormalizationCategoryObject_isTerminal A).from
      (⟨CommAlgCat.of A N, hN⟩ : AbsoluteWeakNormalizationCategory A)) := by
    rw [← hNobj, IsTerminal.from_self]
    infer_instance
  have hNring : IsAbsolutelyWeaklyNormalRing N :=
    (isIso_lift_to_absoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing
      A N hN).mp hNself
  have hC : IsAbsolutelyWeaklyNormalRing C :=
    absolutelyWeaklyNormalRing_of_affineSpecIso U.toScheme e
      (isAbsolutelyWeaklyNormal_open (absolutelyWeaklyNormal_spec_of_ring hNring) U)
  let Robj : AbsoluteWeakNormalizationCategory B :=
    ⟨CommAlgCat.of B C, hJ'⟩
  let hterm := absoluteWeakNormalizationCategoryObject_isTerminal B
  have : IsIso (hterm.from Robj) :=
    (isIso_lift_to_absoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing
      B C hJ').2 hC
  let eAlg : C ≃ₐ[B] AbsoluteWeakNormalization B := CommAlgCat.isoEquivAlgEquiv
    ((ObjectProperty.ι (IsAbsoluteWeakNormalizationCandidate B)).mapIso (asIso (hterm.from Robj)))
  let e : C ≃+* AbsoluteWeakNormalization B := eAlg.toRingEquiv
  have hLeft : e.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom
      (R := A) (A := B) (B := N)) = algebraMap B (AbsoluteWeakNormalization B) := by
    ext b
    exact eAlg.commutes b
  have hRightBase :
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := N)).toRingHom.comp
          (algebraMap A N) =
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := N)).comp
          (algebraMap A B) := by
    ext a
    exact ((Algebra.TensorProduct.includeRight (R := A) (A := B) (B := N)).commutes a).trans
      (IsScalarTower.algebraMap_apply A B C a)
  have hRight :
      (e.toRingHom.comp ((Algebra.TensorProduct.includeRight
        (R := A) (A := B) (B := N)).toRingHom)).comp (algebraMap A N) =
      (algebraMap B (AbsoluteWeakNormalization B)).comp (algebraMap A B) := by
    rw [RingHom.comp_assoc, hRightBase, ← RingHom.comp_assoc, hLeft]
  have hRightEq : e.toRingHom.comp ((Algebra.TensorProduct.includeRight
      (R := A) (A := B) (B := N)).toRingHom) =
        Classical.choose (existsUnique_absoluteWeakNormalizationMap (algebraMap A B)) :=
    (Classical.choose_spec (existsUnique_absoluteWeakNormalizationMap (algebraMap A B))).2 _ hRight
  exact ⟨e, ⟨hLeft, hRightEq⟩, fun e' he' => RingEquiv.ext <| RingHom.congr_fun
    (Algebra.TensorProduct.ringHom_ext (he'.1.trans hLeft.symm) (he'.2.trans hRightEq.symm))⟩

end AlgebraicGeometry

end
