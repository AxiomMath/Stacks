module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.AffineCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.KoszulLocus

/-!
# Open subspaces of a scheme and their scheme-theoretic closures

For an object `Q` of the big fppf site over `S` and an open `O` of its underlying scheme, the
open subspace of the algebraic space represented by `Q` cut out by the points over `O` is the
range of the open subscheme `O`; it is compatible with inverse images along morphisms of the
site; and its scheme-theoretic closure is the closed subspace cut out by the kernel of
`𝒪_Q ⟶ ι_*𝒪_O`, which is the scheme-theoretic closure of `O` in the scheme `Q`.

## Main results

* `AlgebraicGeometry.Space.openSubspaceOfPoints_preimage_yoneda_map`: inverse image, along a
  morphism of the site, of the open subspace cut out by the points over an open.
* `AlgebraicGeometry.Space.openSubspaceOfPoints_preimage_pointsToScheme`: the open subspace cut
  out by the points over `O` is the range of `O`.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_yoneda_openSubHom`: the
  scheme-theoretic closure of `O` in the space represented by `Q` is cut out by `ker(O ⟶ Q)`.
* `AlgebraicGeometry.Space.subspacePointSet_closedSubspaceOfIdeal`: the points of `Z_K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The points of the algebraic space represented by `Q` in the range of a morphism of the site
are those over the range of the underlying morphism of schemes. -/
theorem range_pointsMap_yoneda_map_eq_preimage {Q Q' : BigFppfOver B S hS} (h : Q' ⟶ Q) :
    Set.range (pointsMap B S hS (yoneda.obj Q') (yoneda.map h)) =
      pointsToScheme B S hS Q ⁻¹' Set.range ((BigFppfOver.toScheme B S hS).map h) :=
  Set.ext fun w => mem_range_pointsMap_yoneda_map_iff B S hS h w

/-- **The open subspace cut out by the points over an open `O` of the scheme is the range of
`O`.** -/
theorem openSubspaceOfPoints_preimage_pointsToScheme (Q : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj Q).Opens) :
    openSubspaceOfPoints B S hS (yoneda.obj Q) (pointsToScheme B S hS Q ⁻¹' (O : Set _)) =
      Subfunctor.range (yoneda.map (openSubHom Q O)) := by
  have h := range_eq_openSubspaceOfPoints_of_isOpenImmersion B S hS (yoneda.map (openSubHom Q O))
    (isOpenImmersion_yoneda_map B S hS _ (by
      rw [toScheme_map_openSubHom B S hS]
      exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion O.ι)))
  have hr : Set.range ((BigFppfOver.toScheme B S hS).map (openSubHom Q O)) = (O : Set _) := by
    rw [← Scheme.Opens.range_ι O]
    exact congrArg (fun k : (BigFppfOver.toScheme B S hS).obj (openSub Q O) ⟶
      (BigFppfOver.toScheme B S hS).obj Q => Set.range k) (toScheme_map_openSubHom B S hS Q O)
  rw [h, range_pointsMap_yoneda_map_eq_preimage, hr]

/-- The points over an open of the scheme form an open subspace. -/
theorem isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme (Q : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj Q).Opens) :
    IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS (yoneda.obj Q) (pointsToScheme B S hS Q ⁻¹' (O : Set _))) :=
  isOpenSubspace_openSubspaceOfPoints B S hS (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Q) _
    ((isOpen_yoneda_iff_isSchemeOpen B S hS Q _).2 ⟨O, O.isOpen, fun _ => Iff.rfl⟩)

/-- The inverse image, along a morphism of the site, of the open subspace cut out by the points
over an open `O` is the open subspace cut out by the points over the inverse image of `O`. -/
theorem openSubspaceOfPoints_preimage_yoneda_map {Q Q' : BigFppfOver B S hS} (m : Q' ⟶ Q)
    (O : ((BigFppfOver.toScheme B S hS).obj Q).Opens) :
    (openSubspaceOfPoints B S hS (yoneda.obj Q) (pointsToScheme B S hS Q ⁻¹' (O : Set _))).preimage
        (yoneda.map m) =
      openSubspaceOfPoints B S hS (yoneda.obj Q')
        (pointsToScheme B S hS Q' ⁻¹' ((BigFppfOver.toScheme B S hS).map m ⁻¹ᵁ O : Set _)) := by
  rw [openSubspaceOfPoints_preimage]
  congr 1
  ext w
  simp only [Set.mem_preimage, pointsToScheme_pointsMap, SetLike.mem_coe,
    Scheme.Hom.mem_preimage]

/-- **The scheme-theoretic closure of an open subscheme `O` of `Q`, in the algebraic space
represented by `Q`, is the closed subspace cut out by the kernel of `𝒪_Q ⟶ ι_*𝒪_O`.** -/
theorem schemeTheoreticImageSubfunctor_yoneda_openSubHom (Q : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj Q).Opens) :
    schemeTheoreticImageSubfunctor B S hS (yoneda.map (openSubHom Q O)) =
      (closedSubspaceOfIdeal Q O.ι.ker).1 := by
  have hO : ((BigFppfOver.toScheme B S hS).map (openSubHom Q O)).ker = O.ι.ker :=
    congrArg Scheme.Hom.ker (toScheme_map_openSubHom B S hS Q O)
  have hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (closedSubschemeOverι B S hS Q O.ι.ker)) :=
    inferInstanceAs (AlgebraicGeometry.IsClosedImmersion O.ι.ker.subschemeι)
  refine le_antisymm ?_ ?_
  · -- `O` lies in the closed subscheme `V(ker)`
    refine schemeTheoreticImageSubfunctor_le B S hS _ (closedSubspaceOfIdeal Q O.ι.ker).2 ?_
    exact (range_yoneda_map_le_iff_ker_le B S hS (closedSubschemeOverι B S hS Q O.ι.ker)
      (openSubHom Q O) hj).2 (hO ▸ (Scheme.IdealSheafData.ker_subschemeι O.ι.ker).le)
  · -- the closure is cut out by a closed immersion through which `O` factors
    obtain ⟨R, j, hjR, heq⟩ := exists_closedImmersion_range B S hS
      (schemeTheoreticImageSubfunctor B S hS (yoneda.map (openSubHom Q O)))
      (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS _
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Q))
    obtain ⟨l, hl⟩ : ∃ l : openSub Q O ⟶ R, l ≫ j = openSubHom Q O := by
      have hmem : Subfunctor.range (yoneda.map (openSubHom Q O)) ≤
          Subfunctor.range (yoneda.map j) := by
        rw [← heq]
        exact range_le_schemeTheoreticImageSubfunctor B S hS _
      have hx : (openSubHom Q O : (yoneda.obj Q).obj (Opposite.op (openSub Q O))) ∈
          (Subfunctor.range (yoneda.map (openSubHom Q O))).obj (Opposite.op (openSub Q O)) :=
        ⟨𝟙 _, by simp⟩
      obtain ⟨l, hl⟩ := hmem _ hx
      exact ⟨l, hl⟩
    rw [heq]
    refine (range_yoneda_map_le_iff_ker_le B S hS j _ hjR).2 ?_
    have h1 : ((BigFppfOver.toScheme B S hS).map j).ker ≤
        ((BigFppfOver.toScheme B S hS).map (openSubHom Q O)).ker := by
      rw [← hl, Functor.map_comp]
      exact Scheme.Hom.le_ker_comp _ _
    exact (Scheme.IdealSheafData.ker_subschemeι O.ι.ker).symm ▸ hO ▸ h1

/-- **The points of `Z_K` are the points over the support of `K`.** -/
theorem subspacePointSet_closedSubspaceOfIdeal (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) :
    subspacePointSet B S hS (yoneda.obj T) (closedSubspaceOfIdeal T K).1 =
      pointsToScheme B S hS T ⁻¹' (K.support : Set _) := by
  ext w
  have h := mem_range_pointsMap_ι_iff B S hS (schemeSpace T) (closedSubspaceOfIdeal T K)
    (𝟙 (yoneda.obj T)) w
  have h' : pointsMap B S hS (yoneda.obj T) (𝟙 (yoneda.obj T)) w = w :=
    congrFun (pointsMap_id B S hS (yoneda.obj T)) w
  refine ((congrArg (fun z => z ∈ Set.range (pointsMap B S hS _ (closedSubspaceOfIdeal T K).1.ι))
    h').symm.to_iff.trans h).trans ?_
  have h4 := range_rep_snd_eq_support_chartKer (schemeSpace T) (closedSubspaceOfIdeal T K)
    (𝟙 (yoneda.obj T))
  have h5 : chartKer B S hS (schemeSpace T) (closedSubspaceOfIdeal T K) (𝟙 (yoneda.obj T)) = K :=
    ker_rep_snd_closedSubspaceOfIdeal T K
  rw [h5] at h4
  exact Iff.of_eq (congrArg (fun A => pointsToScheme B S hS T w ∈ A) h4)

end AlgebraicGeometry.Space

end
