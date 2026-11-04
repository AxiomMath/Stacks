module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Centred
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.AffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.DominatingNormalizedBlowupsAssembly

/-!
# The local step of Stacks 0BHM over an elementary étale neighbourhood

Let `X` be a normal Nagata algebraic space of dimension at most two with locally Noetherian étale
charts, with chosen closed points `x₁, …, xₙ` and elementary étale neighbourhoods
`(Uᵢ, uᵢ) ⟶ (X, xᵢ)` (Stacks 0BH9), and let `l : Y ⟶ X` be proper and an isomorphism over
`X ∖ {x₁, …, xₙ}`. The second half of the proof of Stacks 0BHM finds, for each `i`, a sequence

`X_{i, mᵢ} ⟶ … ⟶ X_{i, 1} ⟶ X_{i, 0} = Uᵢ`

of normalized blowups at closed points over `uᵢ` such that `X_{i, mᵢ}` dominates
`Yᵢ = Y ×_X Uᵢ`, by Stacks 0BBT for the scheme `Uᵢ`. The source first makes `Y ⟶ X`
representable with Stacks 087G, so that `Yᵢ` is a scheme; here instead `Yᵢ`, an algebraic space
proper over the affine Noetherian scheme `Uᵢ` and an isomorphism over `Uᵢ ∖ {uᵢ}`, is dominated
by a `(Uᵢ ∖ {uᵢ})`-admissible blowup `Pᵢ ⟶ Uᵢ` of the scheme `Uᵢ` (087G over an affine
Noetherian scheme base,
`AlgebraicGeometry.Space.exists_isProper_isIso_morphismRestrict_dominating`), and the centred
form of Stacks 0BBT
(`Stacks.ResolutionOfSurfaces.exists_reflTransGen_isProperNormalizedBlowUpOutside_dominating`)
is applied to the proper birational morphism `Pᵢ ⟶ Uᵢ` of schemes.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_local_dominating`: the local step.

## References

* [Stacks Project, Tag 0BHM](https://stacks.math.columbia.edu/tag/0BHM)
* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
* [Stacks Project, Tag 087G](https://stacks.math.columbia.edu/tag/087G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The distinguished point of the `i`th neighbourhood is not isolated when its local ring has
dimension at least two. -/
private theorem dense_compl_singleton_neighborhood_point (i : Fin n)
    (hpt : 1 < localRingDimension B S hS (D.point i)) :
    Dense (({(D.neighborhood i).point}ᶜ : Set (D.neighborhoodScheme i))) := by
  refine dense_compl_singleton_iff_not_open.mpr fun hopen => ?_
  have hgen : (D.neighborhood i).point ∈ genericPoints (D.neighborhoodScheme i) := by
    rw [mem_genericPoints_iff_isMax]
    exact fun b hb => ((specializes_iff_forall_open.mp (Scheme.le_iff_specializes.mp hb)) _
      hopen rfl).le
  have hc := chartPoint_pointsToScheme B S hS (D.neighborhood i).scheme (D.neighborhood i).toSpace
    (presheafPoint B S hS (D.neighborhood i).scheme (D.neighborhood i).point
      (D.neighborhood i).residueField_contained)
  rw [pointsToScheme_presheafPoint, (D.neighborhood i).map_point] at hc
  have h1 := localRingDimension_eq_of_chartPoint B S hS D.space.property
    (D.neighborhood i).scheme _
    (presheaf_etale_of_isEtale B S hS (D.neighborhood i).etale_toSpace)
    (D.neighborhood i).point _ hc
  have h2 : localRingDimension B S hS (D.point i) = 0 := by
    exact_mod_cast h1.trans ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints _ _).mpr hgen)
  rw [h2] at hpt
  exact absurd hpt (by decide)

/-- The open subspace of the `i`th neighbourhood cut out by the complement of its distinguished
point is `D.openAwayFromPoint i`. -/
private theorem openSubspaceOfPoints_preimage_compl_neighborhood_point (i : Fin n) :
    openSubspaceOfPoints B S hS (yoneda.obj (D.neighborhood i).scheme)
      (pointsToScheme B S hS (D.neighborhood i).scheme ⁻¹'
        ({(D.neighborhood i).point}ᶜ : Set (D.neighborhoodScheme i))) =
      D.openAwayFromPoint i := by
  rw [openAwayFromPoint]
  congr 1
  ext y
  have hpt' : pointsToScheme B S hS (D.neighborhood i).scheme (D.neighborhoodPoint i) =
      (D.neighborhood i).point :=
    pointsToScheme_presheafPoint B S hS _ _ _
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  change pointsToScheme B S hS (D.neighborhood i).scheme y ∉
    ({(D.neighborhood i).point} : Set _) ↔ _
  rw [Set.mem_singleton_iff]
  exact ⟨fun h h' => h (h' ▸ hpt'),
    fun h h' => h (injective_pointsToScheme B S hS _ (h'.trans hpt'.symm))⟩

/-- **The local step of Stacks 0BHM.** Over the `i`th neighbourhood `Uᵢ`, a scheme which is
affine, Noetherian, normal, Nagata and of dimension at most two, the base change
`Yᵢ = Y ×_X Uᵢ` of a proper `l : Y ⟶ X` which is an isomorphism over `X ∖ {x₁, …, xₙ}` is
dominated over `Uᵢ` by a scheme `Pᵢ` of the site, which is in turn dominated by the top of a
sequence of proper normalized blowups of `Uᵢ` at closed points over `uᵢ`. -/
theorem exists_local_dominating (i : Fin n) {Y : AlgebraicSpaces B S hS} (l : Y ⟶ D.space)
    (hlp : IsProper B S hS l.hom) (hl : IsIso (pullback.snd l.hom D.openAwayFromPoints.ι))
    (hXn : HasEtaleLocalProperty B S hS D.space.obj
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal T))
    (hXln : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hXnag : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsNagataScheme T))
    (hXdim : dimension B S hS D.space.obj D.space.property ≤ 2)
    (hpt : 1 < localRingDimension B S hS (D.point i)) :
    ∃ (U : (D.neighborhoodScheme i).Opens) (Z : Over (D.neighborhoodScheme i)),
      (∀ y, y ∉ U → y = (D.neighborhood i).point) ∧
        Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U) (Over.mk (𝟙 _)) Z ∧
          ∃ (P : BigFppfOver B S hS) (qP : P ⟶ (D.neighborhood i).scheme)
            (hP : yoneda.obj P ⟶ pullback l.hom (D.toSpaceHom i).hom)
            (k : Z.left ⟶ (BigFppfOver.toScheme B S hS).obj P),
            hP ≫ pullback.snd l.hom (D.toSpaceHom i).hom = yoneda.map qP ∧
              k ≫ (BigFppfOver.toScheme B S hS).map qP = Z.hom := by
  classical
  set V := (D.neighborhood i).scheme
  set u := (D.neighborhood i).point
  have hae := presheaf_etale_of_isEtale B S hS (D.neighborhood i).etale_toSpace
  have : IsAffine (D.neighborhoodScheme i) := D.isAffine_neighborhood i
  have : IsLocallyNoetherian (D.neighborhoodScheme i) :=
    (exists_atlas_iff_forall_etale B S hS _ _ D.space.property).mp hXln V _ hae
  have : _root_.AlgebraicGeometry.IsNormal (D.neighborhoodScheme i) :=
    (exists_atlas_iff_forall_etale B S hS _ _ D.space.property).mp hXn V _ hae
  have hNag : IsNagataScheme (D.neighborhoodScheme i) :=
    (exists_atlas_iff_forall_etale B S hS _ _ D.space.property).mp hXnag V _ hae
  have : AlgebraicGeometry.IsNoetherian (D.neighborhoodScheme i) := {}
  have hdim : topologicalKrullDim (D.neighborhoodScheme i) ≤ 2 :=
    (topologicalKrullDim_le_dimension_of_etale B S hS D.space.property V _ hae).trans hXdim
  have hu : IsClosed ({u} : Set (D.neighborhoodScheme i)) := by
    have h0 := D.isClosed_neighborhoodPoint i
    rw [D.neighborhoodPoint_eq_schemeSpacePoint] at h0
    exact isClosed_singleton_of_isClosed_schemeSpacePoint _ h0
  let W : (D.neighborhoodScheme i).Opens := ⟨{u}ᶜ, hu.isOpen_compl⟩
  let Yi : AlgebraicSpaces B S hS := ⟨pullback l.hom (D.toSpaceHom i).hom,
    isAlgebraicSpace_pullback B S hS _ _ Y.property (D.neighborhoodSpace i).property
      D.space.property⟩
  let fi : Yi ⟶ schemeSpace V := ObjectProperty.homMk (pullback.snd l.hom (D.toSpaceHom i).hom)
  have hfi : IsProper B S hS fi.hom :=
    isProper_pullback_snd B S hS Y.property D.space.property (D.neighborhoodSpace i).property
      l.hom (D.toSpaceHom i).hom hlp
  have hisoi : IsIso (pullback.snd fi.hom (openSubspaceOfPoints B S hS (yoneda.obj V)
      (pointsToScheme B S hS V ⁻¹' (W : Set (D.neighborhoodScheme i)))).ι) := by
    rw [show (W : Set (D.neighborhoodScheme i)) = {u}ᶜ from rfl,
      D.openSubspaceOfPoints_preimage_compl_neighborhood_point i]
    exact ((D.restrictionComponent i).obj ⟨Over.mk l.hom, Y.property, hl⟩).property.2
  obtain ⟨P, q, hP, hPf, hqp, hqiso, -, -, hbir⟩ :=
    exists_isProper_isIso_morphismRestrict_dominating V W fi hfi hisoi
  obtain ⟨Z, hchain, k, hk⟩ :=
    Stacks.ResolutionOfSurfaces.exists_reflTransGen_isProperNormalizedBlowUpOutside_dominating
      hNag hdim _ (hbir (D.dense_compl_singleton_neighborhood_point i hpt)) W hqiso
  exact ⟨W, Z, fun y hy => by simpa [W] using hy, hchain, P, q, hP.hom, k,
    congrArg (fun m => m.hom) hPf, hk⟩

/-- **Stacks 0BHM for given neighbourhoods.** Let `ν : X ⟶ X₀` be the proper normalization of
`X₀`, with `X` normal, Nagata, of dimension at most two and with locally Noetherian étale charts,
and let `l : Y ⟶ X` be proper and an isomorphism over `X ∖ {x₁, …, xₙ}`, where the chosen points
have local rings of dimension at least two. Then `X₀` has a sequence of normalized blowups in the
sense of Stacks 0BHX, starting with `ν`, whose top dominates `Y` over `X`. -/
theorem exists_normalizedBlowUpChain_dominating_of_isProper {X₀ Y : AlgebraicSpaces B S hS}
    (ν : D.space ⟶ X₀) (hν : IsProper B S hS ν.hom)
    (hνnorm : ∃ (Dn : NormalizationData B S hS X₀.obj) (e : D.space.obj ≅ Dn.space),
      ν.hom = e.hom ≫ Dn.hom)
    (hXn : Space.IsNormal B S hS D.space.obj)
    (hXln : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hXnag : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsNagataScheme T))
    (hXdim : dimension B S hS D.space.obj D.space.property ≤ 2)
    (hpt : ∀ i, 1 < localRingDimension B S hS (D.point i))
    (l : Y ⟶ D.space) (hlp : IsProper B S hS l.hom)
    (hl : IsIso (pullback.snd l.hom D.openAwayFromPoints.ι)) :
    ∃ (A : AlgebraicSpaces B S hS) (g : A ⟶ D.space) (h : A ⟶ Y),
      NormalizedBlowUpChain B S hS X₀ A (g ≫ ν) ∧ h ≫ l = g :=
  let := hasSheafify_bigFppfOver B S hS
  D.exists_normalizedBlowUpChain_dominating ν hν hνnorm hXn hXln l hl fun i =>
    D.exists_local_dominating i l hlp hl hXn hXln hXnag hXdim (hpt i)

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
