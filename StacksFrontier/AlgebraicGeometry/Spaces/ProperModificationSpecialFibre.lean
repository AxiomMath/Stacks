module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModifications

/-!
# Closed immersions of proper modifications, detected on the special fibre

Let `(A, 𝔪, κ)` be a Noetherian local ring. A morphism `g : X ⟶ Y` of proper modifications of
`Spec A` outside its punctured spectrum is a closed immersion as soon as the induced morphism
`X_κ ⟶ Y_κ` of special fibres is one.

## Main definitions

* `AlgebraicGeometry.Space.residueSpecOver` is `Spec κ` as an object of the big fppf site over
  `Spec A`, and `AlgebraicGeometry.Space.residueSpecToBase` is its structure morphism, the
  closed point `Spec κ → Spec A`. The special fibre of an algebraic space over `Spec A` is its
  base change along this morphism.
* `AlgebraicGeometry.Space.residueSpecPoint` is `Spec κ` regarded as a field-valued point of
  itself.

## Main results

* `AlgebraicGeometry.Space.subfunctor_eq_top_of_factorsThrough_closedPoint`: an open subspace of
  `Spec A`, for `A` local, through which the closed point factors is the whole of `Spec A`.
* `AlgebraicGeometry.Space.isClosedImmersion_of_isClosedImmersion_specialFibre` is
  **Stacks 0AGM**.

## Implementation notes

The structure morphisms of two proper modifications `X` and `Y` of `Spec A` and the morphism
`g : X ⟶ Y` between them form a commutative triangle over `Z = Spec A` in which the morphism
from `X` is locally of finite type and universally closed and the morphism from `Y` is
separated, all three being part of properness. So Stacks 05XA applies and produces an open
subspace `W ⊂ Spec A` through which a morphism factors exactly when the base change of `g`
along it is a closed immersion.

The special fibre hypothesis says that the closed point `Spec κ → Spec A` is such a morphism,
hence factors through `W`. Since `A` is local, every point of `Spec A` specialises to the closed
point, so an open subset of `Spec A` containing the closed point is the whole of `Spec A`;
transported along the order isomorphism of Stacks 03BZ between open subspaces and open sets of
points, this gives `W = ⊤`. The identity of `Spec A` therefore factors through `W`, so the base
change of `g` along the identity is a closed immersion, and that base change is isomorphic to
`g` as an arrow.

## References

* [Stacks Project, Tag 0AGM](https://stacks.math.columbia.edu/tag/0AGM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The spectrum of the residue field of a local ring `A` lies in every big fppf site which
contains `Spec A`. -/
theorem contains_residueSpec (A : Type u) [CommRing A] [IsLocalRing A] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of A))) :
    B.Contains (Spec (.of (A ⧸ IsLocalRing.maximalIdeal A))) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hS
    ((Cardinal.mk_le_of_surjective
      (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal A))).trans
      (le_max_right _ _))

variable (A : Type u) [CommRing A] [IsLocalRing A] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of A)))

/-- The closed point `Spec κ → Spec A` of a local ring `A`, as a morphism of the big fppf
site. -/
def residueSpecHom :
    B.obj (contains_residueSpec A B hS) ⟶ B.obj hS :=
  B.inclusion.preimage
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))

/-- The spectrum of the residue field of `A`, as an object of the big fppf site over `Spec A`. -/
def residueSpecOver : BigFppfOver B (Spec (.of A)) hS :=
  Over.mk (residueSpecHom A B hS)

/-- The structure morphism of `AlgebraicGeometry.Space.residueSpecOver`: the closed point of
`Spec A`, as a morphism of the big fppf site over `Spec A`. -/
def residueSpecToBase :
    residueSpecOver A B hS ⟶ baseTerminal B (Spec (.of A)) hS :=
  Over.homMk (residueSpecHom A B hS) rfl

/-- The spectrum of the residue field of `A`, as a field-valued point of itself: the field is
the residue field and the section is the identity. -/
def residueSpecPoint :
    FieldValuedPoint B (Spec (.of A)) hS (yoneda.obj (residueSpecOver A B hS)) where
  carrier := A ⧸ IsLocalRing.maximalIdeal A
  field := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  contained := contains_residueSpec A B hS
  toBase := B.inclusion.map (residueSpecHom A B hS)
  value := 𝟙 (residueSpecOver A B hS)

/-- The point of `Spec A` underlying the image of `AlgebraicGeometry.Space.residueSpecPoint`
along the closed point is the closed point of `Spec A`. -/
theorem schemePoint_residueSpecPoint :
    schemePoint B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS)
        (FieldValuedPoint.map B (Spec (.of A)) hS (yoneda.obj (residueSpecOver A B hS))
          (yoneda.map (residueSpecToBase A B hS)) (residueSpecPoint A B hS)) =
      IsLocalRing.closedPoint A := by
  have hvalue : (BigFppfOver.toScheme B (Spec (.of A)) hS).map
      (FieldValuedPoint.map B (Spec (.of A)) hS (yoneda.obj (residueSpecOver A B hS))
        (yoneda.map (residueSpecToBase A B hS)) (residueSpecPoint A B hS)).value =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) := by
    change (BigFppfOver.toScheme B (Spec (.of A)) hS).map
      (𝟙 (residueSpecOver A B hS) ≫ residueSpecToBase A B hS) = _
    rw [Category.id_comp]
    exact B.inclusion.map_preimage _
  let _ : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  change ((BigFppfOver.toScheme B (Spec (.of A)) hS).map _) _ = _
  rw [hvalue]
  have : IsLocalHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  exact IsLocalRing.comap_closedPoint _

/-- An open subspace of `Spec A`, for `A` local, through which the closed point of `Spec A`
factors is the whole of `Spec A`.

Its set of points is open by the order isomorphism of Tag 03BZ and contains the closed point,
so it is all of `Spec A` because every point of the spectrum of a local ring specialises to the
closed point; the identity then factors through the subspace by Tag 03IE. -/
theorem subfunctor_eq_top_of_factorsThrough_closedPoint
    (W : Subfunctor (yoneda.obj (baseTerminal B (Spec (.of A)) hS)))
    (hWopen : IsOpenSubspace B (Spec (.of A)) hS W)
    {Z : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (.of A)) hS Z)
    (z : Z ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hS))
    (p : FieldValuedPoint B (Spec (.of A)) hS Z)
    (hp : schemePoint B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS)
      (FieldValuedPoint.map B (Spec (.of A)) hS Z z p) = IsLocalRing.closedPoint A)
    (hfac : ∃ k : Z ⟶ W.toFunctor, k ≫ W.ι = z) :
    W = ⊤ := by
  have hT := isAlgebraicSpace_yoneda B (Spec (CommRingCat.of A)) hS
    (baseTerminal B (Spec (CommRingCat.of A)) hS)
  have hpoints :=
    (factorsThrough_openSubspace_iff_points B (Spec (CommRingCat.of A)) hS hT hZ
      W hWopen z).mp hfac
  let _ : TopologicalSpace (points B (Spec (CommRingCat.of A)) hS
    (yoneda.obj (baseTerminal B (Spec (CommRingCat.of A)) hS))) :=
      pointTopology B (Spec (CommRingCat.of A)) hS
        (yoneda.obj (baseTerminal B (Spec (CommRingCat.of A)) hS))
  have hpW : (FieldValuedPoint.map B (Spec (CommRingCat.of A)) hS Z z p).class
      B (Spec (CommRingCat.of A)) hS
      (yoneda.obj (baseTerminal B (Spec (CommRingCat.of A)) hS)) ∈
      Set.range (pointsMap B (Spec (CommRingCat.of A)) hS W.toFunctor W.ι) :=
    hpoints ⟨p.class B (Spec (CommRingCat.of A)) hS Z, by simp⟩
  have hWopenPoints : IsOpen
      (Set.range (pointsMap B (Spec (CommRingCat.of A)) hS W.toFunctor W.ι)) := by
    simpa only [openSubspacesOrderIso_apply] using
      ((openSubspacesOrderIso B (Spec (CommRingCat.of A)) hS
        (yoneda.obj (baseTerminal B (Spec (CommRingCat.of A)) hS)) hT) ⟨W, hWopen⟩).2
  obtain ⟨V, hVopen, hV⟩ :=
    ((pointTopologyFamily B (Spec (CommRingCat.of A)) hS).scheme
      (baseTerminal B (Spec (CommRingCat.of A)) hS)
      (Set.range (pointsMap B (Spec (CommRingCat.of A)) hS W.toFunctor W.ι))).mp hWopenPoints
  have hclosedV : IsLocalRing.closedPoint A ∈ V := by
    rw [← hp]
    exact (hV _).mp hpW
  have hpts : Set.range (pointsMap B (Spec (CommRingCat.of A)) hS W.toFunctor W.ι)
      = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Quot.inductionOn x fun q ↦
      (hV q).mpr ((IsLocalRing.specializes_closedPoint _).mem_open hVopen hclosedV)
  obtain ⟨k, hk⟩ :=
    (factorsThrough_openSubspace_iff_points B (Spec (CommRingCat.of A)) hS hT hT
      W hWopen (𝟙 _)).mpr (by simp [hpts])
  apply top_unique
  intro U f _
  have heq := congrArg (fun m => m.app U f) hk
  change (k.app U f).val = f at heq
  exact heq ▸ (k.app U f).property

variable [IsNoetherianRing A]

/-- **Stacks 0AGM.** Let `(A, 𝔪, κ)` be a Noetherian local ring and let `g : X ⟶ Y` be a
morphism of proper modifications of `Spec A` outside its punctured spectrum. If the induced
morphism `X_κ ⟶ Y_κ` of special fibres — the base change of `g` along the closed point
`Spec κ → Spec A` — is a closed immersion, then `g` is a closed immersion.

This is the case `Z = Spec A` of Stacks 05XA: the open subspace of `Spec A` that lemma produces
contains the closed point, hence is the whole of `Spec A`. -/
@[stacks 0AGM]
theorem isClosedImmersion_of_isClosedImmersion_specialFibre
    {X Y : ProperModification A B hS} (g : X ⟶ Y)
    (hg : IsClosedImmersion B (Spec (.of A)) hS
      (baseChangeOverBase B (Spec (.of A)) hS g.hom.left X.1.hom Y.1.hom g.hom.w
        (yoneda.map (residueSpecToBase A B hS)))) :
    IsClosedImmersion B (Spec (.of A)) hS g.hom.left := by
  have hZ := isAlgebraicSpace_yoneda B (Spec (CommRingCat.of A)) hS
    (baseTerminal B (Spec (CommRingCat.of A)) hS)
  have hR := isAlgebraicSpace_yoneda B (Spec (CommRingCat.of A)) hS (residueSpecOver A B hS)
  obtain ⟨W, hWopen, hW⟩ :=
    exists_isOpenSubspace_iff_isClosedImmersion_baseChange B (Spec (CommRingCat.of A)) hS
      X.2.1.1 Y.2.1.1 hZ g.hom.left X.1.hom Y.1.hom g.hom.w X.2.2.2.1.1 X.2.2.2.2 Y.2.2.1
  obtain ⟨lift, hlift⟩ :=
    (hW (yoneda.obj (residueSpecOver A B hS)) hR
      (yoneda.map (residueSpecToBase A B hS))).mpr hg
  obtain rfl : W = ⊤ :=
    subfunctor_eq_top_of_factorsThrough_closedPoint A B hS W hWopen hR
      (yoneda.map (residueSpecToBase A B hS)) (residueSpecPoint A B hS)
      (schemePoint_residueSpecPoint A B hS) ⟨lift, hlift⟩
  have hci := (hW (yoneda.obj (baseTerminal B (Spec (CommRingCat.of A)) hS)) hZ (𝟙 _)).mp
    ⟨Subfunctor.lift (𝟙 _) fun U x _ ↦ by simp, by ext U x; rfl⟩
  exact ((MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (Spec (CommRingCat.of A)) hS))).arrow_mk_iso_iff
      (Arrow.isoMk (asIso (pullback.fst X.1.hom (𝟙 _))) (asIso (pullback.fst Y.1.hom (𝟙 _)))
        (by exact (pullback.lift_fst _ _ _).symm))).mp hci

end AlgebraicGeometry.Space

end
