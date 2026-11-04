module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.RingTheory.Valuation.ArcAgreement

/-!
# The locus where two closed subspaces coincide

Let `C` and `E` be closed subspaces of an algebraic space `X`. Their *coincidence locus* is the
set of points `x ∈ |X|` having an étale neighbourhood on which `C` and `E` agree: an étale
scheme chart `φ : U ⟶ X`, an affine open `A ⊆ U` meeting the fibre over `x`, such that the chart
ideals of `C` and `E` agree on `A`. It is open, and it meets `|C|` only inside `|E|`.

When `E ⊆ C` and `E` is cut out on an affine chart by a nonzerodivisor `t`, there is an *arc
criterion*: if `ψ : Γ(U) ⟶ A'` is a homomorphism to a local ring with `ψ t` regular and
`ψ t ∈ I_C A'`, then the point of `U` under the closed point of `Spec A'` lies in the coincidence
locus. Geometrically: if `C` and `E` agree along an arc whose generic point avoids `E`, then they
agree near the special point of the arc.

## Main definitions

* `AlgebraicGeometry.Space.coincidenceLocus`: the coincidence locus of two closed subspaces.

## Main results

* `AlgebraicGeometry.Space.mem_subspacePointSet_iff_mem_support_chartKer`: a point of a scheme
  chart lies over `|Z|` exactly when it lies in the support of the chart ideal of `Z`.
* `AlgebraicGeometry.Space.isOpen_coincidenceLocus`: the coincidence locus is open.
* `AlgebraicGeometry.Space.mem_subspacePointSet_of_mem_coincidenceLocus`: a point of `|C|` in the
  coincidence locus of `C` and `E` lies in `|E|`.
* `AlgebraicGeometry.Space.mem_coincidenceLocus_of_mem_map`: the arc criterion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **A point of a scheme chart lies over a closed subspace exactly when it lies in the support
of the chart ideal.** For any scheme point `φ : U ⟶ X` and any closed subspace `Z ⊆ X`, the
image of a point `w` of `U` lies in `|Z|` if and only if `w` lies in the support of the ideal
sheaf of `Z ×_X U ⊆ U`. -/
theorem mem_subspacePointSet_iff_mem_support_chartKer (Z : ClosedSubspaces B S hS X.1)
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X.1) (w : points B S hS (yoneda.obj U)) :
    pointsMap B S hS (yoneda.obj U) φ w ∈ subspacePointSet B S hS X.1 Z.1 ↔
      pointsToScheme B S hS U w ∈ (chartKer B S hS X Z φ).support := by
  rw [subspacePointSet, mem_range_pointsMap_ι_iff, range_rep_snd_eq_support_chartKer]
  rfl

/-- The **coincidence locus** of two closed subspaces `C` and `E` of `X`: the points of `X` which
are the image of a point `w` of an étale scheme chart `φ : U ⟶ X` lying in an affine open `A` of
`U` on which the chart ideals of `C` and `E` agree. -/
def coincidenceLocus (C E : ClosedSubspaces B S hS X.1) : Set (points B S hS X.1) :=
  {x | ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X.1)
      (_ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf φ)
      (A : ((BigFppfOver.toScheme B S hS).obj U).affineOpens),
      (chartKer B S hS X C φ).ideal A = (chartKer B S hS X E φ).ideal A ∧
      ∃ w : points B S hS (yoneda.obj U), pointsToScheme B S hS U w ∈ A.1 ∧
        pointsMap B S hS (yoneda.obj U) φ w = x}

section PointTopology

attribute [local instance] pointTopology

/-- **The coincidence locus of two closed subspaces is open.** It is a union of images of opens
of étale scheme charts, and étale morphisms are open on points. -/
theorem isOpen_coincidenceLocus (C E : ClosedSubspaces B S hS X.1) :
    IsOpen (coincidenceLocus B S hS X C E) := by
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro x ⟨U, φ, hφ, A, hA, w, hwA, rfl⟩
  refine ⟨pointsMap B S hS (yoneda.obj U) φ '' (pointsToScheme B S hS U ⁻¹' A.1), ?_, ?_,
    ⟨w, hwA, rfl⟩⟩
  · rintro _ ⟨w', hw', rfl⟩
    exact ⟨U, φ, hφ, A, hA, w', hw', rfl⟩
  · refine isOpenMap_pointsMap_of_presheafEtale B S hS φ hφ _ ?_
    exact (schemePointsHomeomorph B S hS U).continuous.isOpen_preimage _ A.1.2

end PointTopology

/-- **A point of `|C|` in the coincidence locus of `C` and `E` lies in `|E|`.** On the affine
open of the chart where the two chart ideals agree, the supports agree. -/
theorem mem_subspacePointSet_of_mem_coincidenceLocus {C E : ClosedSubspaces B S hS X.1}
    {x : points B S hS X.1} (hx : x ∈ coincidenceLocus B S hS X C E)
    (hC : x ∈ subspacePointSet B S hS X.1 C.1) : x ∈ subspacePointSet B S hS X.1 E.1 := by
  obtain ⟨U, φ, -, A, hA, w, hwA, rfl⟩ := hx
  rw [mem_subspacePointSet_iff_mem_support_chartKer] at hC ⊢
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hwA] at hC ⊢
  rwa [← hA]

/-- The coincidence locus of `C` and `E` avoids the points of `C` outside `E`. -/
theorem subspacePointSet_diff_subset_compl_coincidenceLocus (C E : ClosedSubspaces B S hS X.1) :
    subspacePointSet B S hS X.1 C.1 \ subspacePointSet B S hS X.1 E.1 ⊆
      (coincidenceLocus B S hS X C E)ᶜ :=
  fun _ hx hmem => hx.2 (mem_subspacePointSet_of_mem_coincidenceLocus B S hS X hmem hx.1)

/-- **The arc criterion for the coincidence locus.** Let `φ : U ⟶ X` be an étale chart with `U`
affine, on which the chart ideal of `E` is generated by `t` and contains the chart ideal of `C`.
Let `ψ : Γ(U) ⟶ A'` be a homomorphism to a local ring with `ψ t` a nonzerodivisor and
`ψ t ∈ I_C A'`, and let `w` be a point of `U` lying in every basic open `D(r)` with `ψ r` a unit
(the image of the closed point of `Spec A'`). Then the image of `w` lies in the coincidence locus
of `C` and `E`. -/
theorem mem_coincidenceLocus_of_mem_map (C E : ClosedSubspaces B S hS X.1)
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X.1)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf φ)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    {t : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (hE : (chartKer B S hS X E φ).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {t})
    (hle : (chartKer B S hS X C φ).ideal ⟨⊤, isAffineOpen_top _⟩ ≤
      (chartKer B S hS X E φ).ideal ⟨⊤, isAffineOpen_top _⟩)
    {A' : Type*} [CommRing A'] [IsLocalRing A']
    (ψ : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →+* A')
    (ht : IsLeftRegular (ψ t))
    (hmem : ψ t ∈ ((chartKer B S hS X C φ).ideal ⟨⊤, isAffineOpen_top _⟩).map ψ)
    (w : points B S hS (yoneda.obj U))
    (hw : ∀ r, IsUnit (ψ r) →
      pointsToScheme B S hS U w ∈ ((BigFppfOver.toScheme B S hS).obj U).basicOpen r) :
    pointsMap B S hS (yoneda.obj U) φ w ∈ coincidenceLocus B S hS X C E := by
  obtain ⟨r, hr, htr⟩ := Ideal.exists_isUnit_map_mul_mem_of_mem_map ψ (hle.trans hE.le) ht hmem
  refine ⟨U, φ, hφ, ((BigFppfOver.toScheme B S hS).obj U).affineBasicOpen
    (U := ⟨⊤, isAffineOpen_top _⟩) r, ?_, w, hw r hr, rfl⟩
  have hC := (chartKer B S hS X C φ).map_ideal_basicOpen ⟨⊤, isAffineOpen_top _⟩ r
  have hE' := (chartKer B S hS X E φ).map_ideal_basicOpen ⟨⊤, isAffineOpen_top _⟩ r
  rw [← hC, ← hE']
  refine le_antisymm (Ideal.map_mono hle) ?_
  rw [hE, Ideal.map_span, Set.image_singleton]
  refine (Ideal.span_singleton_le_iff_mem _).2 ?_
  have hunit := IsLocalization.Away.algebraMap_isUnit (S := Γ((BigFppfOver.toScheme B S hS).obj U,
    ((BigFppfOver.toScheme B S hS).obj U).basicOpen r)) r
  obtain ⟨v, hv⟩ := hunit.exists_left_inv
  have hmul : algebraMap _ _ t = v * algebraMap Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ((BigFppfOver.toScheme B S hS).obj U).basicOpen r)
      (t * r) := by
    rw [map_mul, mul_left_comm, hv, mul_one]
  have key : algebraMap Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ((BigFppfOver.toScheme B S hS).obj U).basicOpen r) t ∈
        ((chartKer B S hS X C φ).ideal ⟨⊤, isAffineOpen_top _⟩).map (algebraMap _ _) := by
    rw [hmul]
    exact Ideal.mul_mem_left _ v (Ideal.mem_map_of_mem _ htr)
  exact key

end AlgebraicGeometry.Space

end
