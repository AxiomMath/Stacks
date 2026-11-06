module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.BoundedElementaryEtaleNeighborhoodModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingUniverseComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RepresentableElementaryEtaleNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationColimitOfLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsSingleClosedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# Modifications of a decent algebraic space at a closed point and its henselian local ring

Let `X` be a decent algebraic space over a scheme `S` and let `x ∈ |X|` be a closed point such
that `U = X ∖ {x} ⟶ X` is quasi-compact. With `V = Spec(𝒪^h_{X, x}) ∖ {𝔪^h_x}` Stacks 0BH0
asserts that base change along `Spec(𝒪^h_{X, x}) ⟶ X` is an equivalence from the algebraic
spaces of finite presentation over `X` which are isomorphisms over `U` onto the algebraic spaces
of finite presentation over `Spec(𝒪^h_{X, x})` which are isomorphisms over `V`. This file proves
it for the functor `AlgebraicGeometry.Space.ClosedPointNeighborhood.henselianBaseChangeFunctor`.

## The proof

Fix the affine elementary étale neighbourhood `(W, w) → (X, x)` with `w` the only point above
`x` (Stacks 0BBP), and the henselization `R` of `𝒪_{W, w}`; by Stacks 0EMY it is the henselian
local ring `𝒪^h_{X, x}`.

*Reduction to `W`.* Base change along `W ⟶ X` is an equivalence from the modifications of `X`
away from `x` onto those of `W` away from `w`, and preserves and reflects finite presentation:
this is the single-point case of Stacks 0BHB together with Stacks 0BGZ
(`AlgebraicGeometry.Space.exists_pullback_obj_iso_single` and its companions).

*The limit.* The affine elementary étale neighbourhoods of the point `w` of the affine space `W`
admit a small initial model with a uniform bound on the sizes of its stages
(`ElementaryEtaleNeighborhood.exists_bounded_cofiltered_initial_affine_model_of_iso`), and
`Spec R` is the limit of its stages (`AlgebraicGeometry.Space.isLimitHenselianSchemeCone`), as an
object of the site and as a presheaf. By Stacks 07SK in its cofinality-free form
(`AlgebraicGeometry.FinitePresentationSpacesOver.isFinitePresentationColimit_of_isLimit`) the
algebraic spaces of finite presentation over `Spec R` are the filtered `2`-colimit of those over
the stages.

*The stages.* A stage `(U, u)` need not have `u` as its only point above `w`, but it is refined
by a neighbourhood which has
(`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_hom_of_unique_point`), over which
base change from `W` is again an equivalence by the single-point case of Stacks 0BHB.
An object over `Spec R` comes from an object over a stage; that it is an isomorphism over `V`
descends to a later stage, over the preimage of `W ∖ {w}`; refining to a neighbourhood with a
single point above `w`, it comes from `W`. Morphisms are treated the same way, the comparisons of
the iterated base changes being the pinned ones of `CategoryTheory.Over.pullbackFactorObjIso`.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space.ClosedPointNeighborhood`.

* `isEquivalence_henselianBaseChangeFunctor`: the base change functor of Stacks 0BH0 is an
  equivalence, for any containment of `Spec R` in the site.
* `contains_spec_of_isHenselization`: the spectrum of a henselization of `𝒪_{W, w}` belongs to
  the site.
* `isEquivalence_henselianBaseChangeFunctor_of_isHenselization`: **Stacks 0BH0**.

## References

* [Stacks Project, Tag 0BH0](https://stacks.math.columbia.edu/tag/0BH0)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 0BGZ](https://stacks.math.columbia.edu/tag/0BGZ)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace ElementaryEtaleNeighborhood

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X} {x : points B S hS X}

/-- The scheme of an elementary étale neighbourhood, as an object of the site, functorially. -/
@[simps]
def siteScheme : ElementaryEtaleNeighborhood B S hS X hX x ⥤ BigFppfOver B S hS where
  obj E := E.scheme
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

end ElementaryEtaleNeighborhood

section Helpers

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inclusion of a subfunctor is quasi-separated: it is a monomorphism, so its diagonal is an
isomorphism. -/
theorem isQuasiSeparated_subfunctor_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor F) :
    IsQuasiSeparated B S hS U.ι := by
  intro Z _ hZqc g
  have : IsIso (pullback.diagonal U.ι) := (pullback.isIso_diagonal_iff U.ι).2 inferInstance
  exact isQuasiCompactSpace_of_iso B S hS (asIso (pullback.fst g (pullback.diagonal U.ι))).symm
    hZqc

/-- Being an isomorphism over a subfunctor is invariant under isomorphism of the object. -/
theorem isIso_pullback_snd_of_overIso {P V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ι : V ⟶ P}
    {Z₁ Z₂ : Over P} (e : Z₁ ≅ Z₂) (h : IsIso (pullback.snd Z₂.hom ι)) :
    IsIso (pullback.snd Z₁.hom ι) := by
  have h₁ : IsPullback (pullback.fst Z₁.hom ι ≫ e.hom.left) (pullback.snd Z₁.hom ι) Z₂.hom ι :=
    (IsPullback.of_hasPullback Z₁.hom ι).of_iso (Iso.refl _) ((Over.forget P).mapIso e)
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  rw [← IsPullback.isoIsPullback_hom_snd _ _ h₁ (IsPullback.of_hasPullback Z₂.hom ι)]
  infer_instance

/-- Finite presentation of the structure morphism is invariant under isomorphism of the object. -/
theorem isFinitePresentation_of_overIso {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) {Z₁ Z₂ : Over P} (e : Z₁ ≅ Z₂)
    (h₂ : IsAlgebraicSpace B S hS Z₂.left) (hfp : IsFinitePresentation B S hS Z₂.hom) :
    IsFinitePresentation B S hS Z₁.hom := by
  have h₁ : IsAlgebraicSpace B S hS Z₁.left := h₂.of_iso ((Over.forget P).mapIso e).symm
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget P).map e.hom))
  exact isFinitePresentation_of_isPullback B S hS h₁ h₂ hP hP
    (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e.hom.left Z₁.hom Z₂.hom (𝟙 P)) hfp

/-- The ring of global sections of an affine object of the site is bounded by any bound on its
size. -/
private theorem mk_sections_le_of_size_le {T : BigFppfOver B S hS} (hT : IsAffine T.left.1)
    {μ : Cardinal.{u}} (h : ((BigFppfOver.toScheme B S hS).obj T).size ≤ μ) :
    Cardinal.mk Γ(T.left.1, ⊤) ≤ μ := by
  refine le_trans ?_ h
  rw [show ((BigFppfOver.toScheme B S hS).obj T) = T.left.1 from rfl, Scheme.size_of_isAffine]
  exact le_max_right _ _

/-- If `μ` is below the cutoff, so is `2 ^ (μ * μ)`. -/
private theorem two_pow_mul_lt_cutoff {μ : Cardinal.{u}} (hμ : μ < B.cutoff) :
    (2 : Cardinal.{u}) ^ (μ * μ) < B.cutoff :=
  B.cutoff_isStrongPrelimit (Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le hμ hμ)

end Helpers

namespace ClosedPointNeighborhood

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : ClosedPointNeighborhood B S hS)

/-! ### The neighbourhood as an algebraic space -/

/-- The scheme `W` of the chosen neighbourhood, as an algebraic space. -/
abbrev nbhdSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj D.neighborhood.scheme, isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme⟩

/-- The point `w` of the chosen neighbourhood, as a point of the algebraic space it represents. -/
abbrev nbhdPoint : points B S hS (yoneda.obj D.neighborhood.scheme) :=
  presheafPoint B S hS D.neighborhood.scheme D.neighborhood.point
    D.neighborhood.residueField_contained

/-- The scheme `W` pointed at `w`, as an elementary étale neighbourhood of its own point. -/
abbrev nbhdSelf :
    ElementaryEtaleNeighborhood B S hS (yoneda.obj D.neighborhood.scheme)
      (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint :=
  ElementaryEtaleNeighborhood.self B S hS D.neighborhood.scheme D.neighborhood.point
    D.neighborhood.residueField_contained

/-- A point of `W` lies above `x` exactly when it is `w`. -/
theorem pointsMap_toSpace_eq_point_iff (y : points B S hS (yoneda.obj D.neighborhood.scheme)) :
    pointsMap B S hS (yoneda.obj D.neighborhood.scheme) D.neighborhood.toSpace y = D.point ↔
      y = D.nbhdPoint :=
  ⟨fun hy ↦ D.eq_of_map_eq_point y hy, fun hy ↦ hy ▸ D.neighborhood.map_point⟩

/-- The point `w` is a closed point of `W`: it is the whole preimage of the closed point `x`. -/
theorem isClosed_nbhdPoint :
    IsClosed ({D.nbhdPoint} : Set (points B S hS (yoneda.obj D.neighborhood.scheme))) := by
  have hpre : ({D.nbhdPoint} : Set (points B S hS (yoneda.obj D.neighborhood.scheme))) =
      pointsMap B S hS (yoneda.obj D.neighborhood.scheme) D.neighborhood.toSpace ⁻¹' {D.point} :=
    Set.ext fun y ↦ (D.pointsMap_toSpace_eq_point_iff y).symm
  rw [hpre]
  exact D.isClosed_point.preimage (continuous_pointsMap B S hS _)

/-- The open subspace `W ∖ {w}`. -/
abbrev nbhdAway : Subfunctor (yoneda.obj D.neighborhood.scheme) :=
  openSubspaceOfPoints B S hS (yoneda.obj D.neighborhood.scheme) {D.nbhdPoint}ᶜ

/-- `W ∖ {w}` is the preimage of `X ∖ {x}`. -/
theorem nbhdAway_eq_preimage :
    D.nbhdAway = D.openAwayFromPoint.preimage D.neighborhood.toSpace := by
  rw [openAwayFromPoint, preimage_openSubspaceOfPoints]
  exact congrArg (openSubspaceOfPoints B S hS _)
    (Set.ext fun y ↦ not_congr (D.pointsMap_toSpace_eq_point_iff y).symm)

/-- The inclusion of `W ∖ {w}` is quasi-compact, as a base change of that of `X ∖ {x}`. -/
theorem isQuasiCompact_nbhdAway : IsQuasiCompact B S hS D.nbhdAway.ι := by
  rw [nbhdAway_eq_preimage]
  exact isQuasiCompact_of_isPullback B S hS
    (Subfunctor.isPullback_fromPreimage D.openAwayFromPoint D.neighborhood.toSpace)
    D.quasiCompact_complement

/-- `W ∖ {w}` is an open subspace of `W`. -/
theorem isOpenSubspace_nbhdAway : IsOpenSubspace B S hS D.nbhdAway :=
  isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_yoneda B S hS _) _
    D.isClosed_nbhdPoint.isOpen_compl

/-- The inclusion of `W ∖ {w}` is of finite presentation. -/
theorem isFinitePresentation_nbhdAway_ι : IsFinitePresentation B S hS D.nbhdAway.ι :=
  ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS D.isOpenSubspace_nbhdAway.2,
    D.isQuasiCompact_nbhdAway, isQuasiSeparated_subfunctor_ι _⟩

/-- The preimage of `W ∖ {w}` in a scheme over `W` is an open subspace. -/
theorem isOpenSubspace_preimage_nbhdAway {U : BigFppfOver B S hS}
    (τ : yoneda.obj U ⟶ yoneda.obj D.neighborhood.scheme) :
    IsOpenSubspace B S hS (D.nbhdAway.preimage τ) := by
  rw [preimage_openSubspaceOfPoints]
  exact isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_yoneda B S hS _) _
    (D.isClosed_nbhdPoint.isOpen_compl.preimage (continuous_pointsMap B S hS _))

/-- The inclusion of the preimage of `W ∖ {w}` in a scheme over `W` is of finite presentation, as
a base change of the inclusion of `W ∖ {w}`. -/
theorem isFinitePresentation_preimage_nbhdAway_ι {U : BigFppfOver B S hS}
    (τ : yoneda.obj U ⟶ yoneda.obj D.neighborhood.scheme) :
    IsFinitePresentation B S hS (D.nbhdAway.preimage τ).ι :=
  isFinitePresentation_of_isPullback B S hS (D.isOpenSubspace_preimage_nbhdAway τ).1
    D.isOpenSubspace_nbhdAway.1 (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _) (Subfunctor.isPullback_fromPreimage D.nbhdAway τ)
    D.isFinitePresentation_nbhdAway_ι

/-- A modification of `X` away from `x`, base changed to a scheme over `X`, as an algebraic space
of finite presentation over that scheme. -/
def stageObj {U : BigFppfOver B S hS} (τ : yoneda.obj U ⟶ D.space.obj)
    (A : D.modificationsAwayFromPoint) : FinitePresentationSpacesOver B S hS U :=
  ⟨(Over.pullback τ).obj A.obj,
    isAlgebraicSpace_pullback B S hS A.obj.hom τ A.property.1.1 (isAlgebraicSpace_yoneda B S hS U)
      D.space.property,
    isFinitePresentation_pullback_snd B S hS A.obj.hom τ A.property.1.1 D.space.property
      (isAlgebraicSpace_yoneda B S hS U) A.property.2⟩

/-- The restriction to the preimage of `W ∖ {w}` of an algebraic space of finite presentation over
a scheme over `W`. -/
def restrictObj {U : BigFppfOver B S hS} (τ : yoneda.obj U ⟶ yoneda.obj D.neighborhood.scheme)
    (Y : FinitePresentationSpacesOver B S hS U) : FinitePresentationSpacesOver B S hS U :=
  ⟨Over.mk (pullback.snd Y.obj.hom (D.nbhdAway.preimage τ).ι ≫ (D.nbhdAway.preimage τ).ι),
    isAlgebraicSpace_pullback B S hS Y.obj.hom (D.nbhdAway.preimage τ).ι Y.property.1
      (D.isOpenSubspace_preimage_nbhdAway τ).1 (isAlgebraicSpace_yoneda B S hS U),
    isFinitePresentation_comp B S hS
      (isAlgebraicSpace_pullback B S hS Y.obj.hom (D.nbhdAway.preimage τ).ι Y.property.1
        (D.isOpenSubspace_preimage_nbhdAway τ).1 (isAlgebraicSpace_yoneda B S hS U))
      (D.isOpenSubspace_preimage_nbhdAway τ).1 (isAlgebraicSpace_yoneda B S hS U) _ _
      (isFinitePresentation_pullback_snd B S hS Y.obj.hom (D.nbhdAway.preimage τ).ι Y.property.1
        (isAlgebraicSpace_yoneda B S hS U) (D.isOpenSubspace_preimage_nbhdAway τ).1 Y.property.2)
      (D.isFinitePresentation_preimage_nbhdAway_ι τ)⟩

/-- The preimage of `W ∖ {w}` in a scheme over `W`, as an algebraic space of finite presentation
over that scheme. -/
def awayObj {U : BigFppfOver B S hS} (τ : yoneda.obj U ⟶ yoneda.obj D.neighborhood.scheme) :
    FinitePresentationSpacesOver B S hS U :=
  ⟨Over.mk (D.nbhdAway.preimage τ).ι, (D.isOpenSubspace_preimage_nbhdAway τ).1,
    D.isFinitePresentation_preimage_nbhdAway_ι τ⟩

/-- The projection of the restriction to the preimage of `W ∖ {w}` onto that preimage. -/
def restrictHom {U : BigFppfOver B S hS} (τ : yoneda.obj U ⟶ yoneda.obj D.neighborhood.scheme)
    (Y : FinitePresentationSpacesOver B S hS U) : D.restrictObj τ Y ⟶ D.awayObj τ :=
  ObjectProperty.homMk (Over.homMk (pullback.snd Y.obj.hom (D.nbhdAway.preimage τ).ι) rfl)

/-- The transition maps between the stages are affine. -/
private theorem isAffineHom_yoneda_map_stage {I : Type u} [SmallCategory I]
    {G : I ⥤ ElementaryEtaleNeighborhood B S hS (yoneda.obj D.neighborhood.scheme)
      (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint}
    (hGaff : ∀ i, IsAffine (G.obj i).scheme.left.1) {i j : I} (f : i ⟶ j) :
    IsAffineHom B S hS (yoneda.map ((G ⋙ ElementaryEtaleNeighborhood.siteScheme).map f)) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((G ⋙ ElementaryEtaleNeighborhood.siteScheme).obj i)) := hGaff i
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((G ⋙ ElementaryEtaleNeighborhood.siteScheme).obj j)) := hGaff j
  exact isAffineHom_yoneda_map B S hS ((G ⋙ ElementaryEtaleNeighborhood.siteScheme).map f)

/-- The representable stages have bounded base change sizes. -/
private theorem baseChangeSizeBounded_stage {I : Type u} [SmallCategory I]
    {G : I ⥤ ElementaryEtaleNeighborhood B S hS (yoneda.obj D.neighborhood.scheme)
      (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint}
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hGμ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ) :
    BaseChangeSizeBounded B S hS ((G ⋙ ElementaryEtaleNeighborhood.siteScheme) ⋙ yoneda) :=
  baseChangeSizeBounded_of_isPullback B S hS
    ((G ⋙ ElementaryEtaleNeighborhood.siteScheme) ⋙ yoneda)
    (G ⋙ ElementaryEtaleNeighborhood.siteScheme) (fun _ ↦ 𝟙 _)
    (fun f ↦ IsPullback.of_vert_isIso ⟨by simp⟩) hμ hGμ

/-- Every stage is refined by a stage mapping to an affine neighbourhood of `w` with a single point
above `w`, which itself maps to the given stage. -/
private theorem exists_refinement {I : Type u} [SmallCategory I]
    (G : I ⥤ ElementaryEtaleNeighborhood B S hS (yoneda.obj D.neighborhood.scheme)
      (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint)
    [G.Initial] [G.Faithful] [G.Full] (hGaff : ∀ i, IsAffine (G.obj i).scheme.left.1) (j : I) :
    ∃ (E' : ElementaryEtaleNeighborhood B S hS (yoneda.obj D.neighborhood.scheme)
      (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint)
      (_ : IsAffine E'.scheme.left.1)
      (_ : ∀ y : points B S hS (yoneda.obj E'.scheme),
        pointsMap B S hS (yoneda.obj E'.scheme) E'.toSpace y = D.nbhdPoint →
          y = presheafPoint B S hS E'.scheme E'.point E'.residueField_contained)
      (r : E' ⟶ G.obj j) (k : I) (r' : G.obj k ⟶ E') (ε' : k ⟶ j),
      yoneda.map r'.hom ≫ yoneda.map r.hom = yoneda.map (G.map ε').hom := by
  obtain ⟨E', hE'aff, hE'u, ⟨r⟩⟩ := ElementaryEtaleNeighborhood.exists_hom_of_unique_point B S hS
    D.neighborhood.scheme D.neighborhood.point D.neighborhood.residueField_contained (G.obj j)
    (hGaff j)
  obtain ⟨⟨k, ⟨⟨⟩⟩, r₀⟩⟩ : Nonempty (CostructuredArrow G E') := inferInstance
  refine ⟨E', hE'aff, hE'u, r, k, r₀, G.preimage (r₀ ≫ r), ?_⟩
  rw [G.map_preimage, ← yoneda.map_comp]
  rfl

/-! ### The punctured spectrum -/

section Henselian

variable (R : Type u) [CommRing R] [IsLocalRing R] [Algebra (D.neighborhoodStalk) R]
    [IsLocalRing.IsHenselization (D.neighborhoodStalk)
      (IsLocalRing.ResidueField (D.neighborhoodStalk)) R]
    (hR : B.Contains (Spec (.of R)))

/-- The closed point of `Spec R` lies above `w`. -/
theorem pointsMap_henselianClosedPoint :
    pointsMap B S hS (D.henselianSpace R hR).obj (yoneda.map (D.toNeighborhoodHom R hR))
      (D.henselianClosedPoint R hR) = D.nbhdPoint := by
  refine injective_pointsToScheme B S hS D.neighborhood.scheme ?_
  refine (pointsToScheme_pointsMap B S hS (D.toNeighborhoodHom R hR)
    (D.henselianClosedPoint R hR)).trans ?_
  rw [D.pointsToScheme_henselianClosedPoint R hR, pointsToScheme_presheafPoint]
  change D.neighborhood.scheme.left.1.fromSpecStalk D.neighborhood.point
    (Spec.map (CommRingCat.ofHom (algebraMap (D.neighborhoodStalk) R))
      (IsLocalRing.closedPoint R)) = D.neighborhood.point
  have := IsLocalRing.IsHenselization.isLocalHom (R := D.neighborhoodStalk)
    (L := IsLocalRing.ResidueField (D.neighborhoodStalk)) (Rh := R)
  have hcl : Spec.map (CommRingCat.ofHom (algebraMap (D.neighborhoodStalk) R))
      (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint (D.neighborhoodStalk) :=
    IsLocalRing.comap_closedPoint (algebraMap (D.neighborhoodStalk) R)
  rw [hcl]
  exact Scheme.fromSpecStalk_closedPoint

/-- The preimage of `W ∖ {w}` in `Spec R` is contained in the punctured spectrum `V`. -/
theorem preimage_nbhdAway_le :
    D.nbhdAway.preimage (yoneda.map (D.toNeighborhoodHom R hR)) ≤
      D.openAwayFromClosedPoint R hR := by
  rw [preimage_openSubspaceOfPoints, openAwayFromClosedPoint]
  refine openSubspaceOfPoints_mono B S hS ?_
  intro y hy hcon
  exact hy (hcon ▸ D.pointsMap_henselianClosedPoint R hR)

/-! ### The stages of the limit presentation -/

section Model

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
  (G : I ⥤ ElementaryEtaleNeighborhood B S hS (yoneda.obj D.neighborhood.scheme)
    (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint)
  (hGaff : ∀ i, IsAffine (G.obj i).scheme.left.1)
  (e : R ≃+* (henselianLocalRing B S hS (yoneda.obj D.neighborhood.scheme)
    (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme) : Type (u + 1)))

/-- The morphism of a stage to `W`. -/
def stageMap (i : I) : (G.obj i).scheme ⟶ D.neighborhood.scheme :=
  yoneda.preimage (G.obj i).toSpace

/-- The Yoneda image of the morphism of a stage to `W` is the structure morphism of the stage. -/
theorem yoneda_map_stageMap (i : I) : yoneda.map (D.stageMap G i) = (G.obj i).toSpace :=
  Functor.map_preimage _ _

/-- The morphism of a stage to `W` carries the distinguished point to `w`. -/
theorem stageMap_point (i : I) :
    (D.stageMap G i).left.1 (G.obj i).point = D.neighborhood.point := by
  have h := congrArg (pointsToScheme B S hS D.neighborhood.scheme) (G.obj i).map_point
  rwa [← D.yoneda_map_stageMap G i, pointsToScheme_pointsMap, pointsToScheme_presheafPoint,
    pointsToScheme_presheafPoint] at h

/-- The morphism of a stage to `W`, as a morphism of elementary étale neighbourhoods. -/
def stageToSelf (i : I) : G.obj i ⟶ D.nbhdSelf :=
  ⟨D.stageMap G i, by rw [D.yoneda_map_stageMap G i]; exact Category.comp_id _,
    D.stageMap_point G i⟩

/-- The projection of `Spec R` to a stage. -/
def stageLeg (i : I) : Spec (.of R) ⟶ (G.obj i).scheme.left.1 :=
  (henselianSchemeCone B S hS (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme) G e hGaff).π.app i

variable (he : ∀ a : D.neighborhoodStalk, e (algebraMap _ R a) =
  stalkToHenselianLocalRing B S hS (yoneda.obj D.neighborhood.scheme)
    (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdSelf a)

include he in
/-- **The projections are compatible with the canonical morphism `Spec R ⟶ W`.** On global
sections of the affine scheme `W` both are the restriction to the stalk at `w` followed by the
structure map of the henselization. -/
theorem stageLeg_comp_stageMap (i : I) :
    D.stageLeg R G hGaff e i ≫ (D.stageMap G i).left.1 = D.specToNeighborhoodScheme R := by
  have : IsAffine D.neighborhood.scheme.left.1 := D.isAffine_neighborhood
  have := hGaff i
  let g := (D.stageMap G i).left.1
  let φ := henselianLeg B S hS (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme)
    D.nbhdPoint (isDecentSpace_yoneda B S hS D.neighborhood.scheme) G e i
  let germ := D.neighborhood.scheme.left.1.presheaf.germ ⊤ D.neighborhood.point trivial
  have h4 : g.appTop ≫ CommRingCat.ofHom φ =
      germ ≫ CommRingCat.ofHom (algebraMap (D.neighborhoodStalk) R) := by
    ext t
    change φ (g.appTop t) = algebraMap (D.neighborhoodStalk) R (germ t)
    have hnat := sectionHom_naturality B S hS (yoneda.obj D.neighborhood.scheme)
      (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
      (isDecentSpace_yoneda B S hS D.neighborhood.scheme) (D.stageToSelf G i).op t
    have htop := stalkToHenselianLocalRing_openGerm B S hS (yoneda.obj D.neighborhood.scheme)
      (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
      (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdSelf ⊤ trivial t
    rw [openRestrictionSectionHom_top] at htop
    apply e.injective
    rw [he]
    exact (e.apply_symm_apply _).trans (hnat.trans htop.symm)
  have hfrom : D.neighborhood.scheme.left.1.fromSpecStalk D.neighborhood.point =
      Spec.map germ ≫ D.neighborhood.scheme.left.1.isoSpec.inv :=
    (Iso.eq_comp_inv _).mpr (Scheme.fromSpecStalk_toSpecΓ _ _)
  calc D.stageLeg R G hGaff e i ≫ g
      = Spec.map (CommRingCat.ofHom φ) ≫ ((G.obj i).scheme.left.1.isoSpec.inv ≫ g) :=
        Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom φ) ≫
        (Spec.map g.appTop ≫ D.neighborhood.scheme.left.1.isoSpec.inv) :=
        congrArg (fun k ↦ Spec.map (CommRingCat.ofHom φ) ≫ k)
          (Scheme.isoSpec_inv_naturality g).symm
    _ = (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map g.appTop) ≫
        D.neighborhood.scheme.left.1.isoSpec.inv := (Category.assoc _ _ _).symm
    _ = Spec.map (g.appTop ≫ CommRingCat.ofHom φ) ≫
        D.neighborhood.scheme.left.1.isoSpec.inv :=
        congrArg (fun k ↦ k ≫ D.neighborhood.scheme.left.1.isoSpec.inv)
          (Spec.map_comp _ _).symm
    _ = Spec.map (germ ≫ CommRingCat.ofHom (algebraMap (D.neighborhoodStalk) R)) ≫
        D.neighborhood.scheme.left.1.isoSpec.inv :=
        congrArg (fun k ↦ Spec.map k ≫ D.neighborhood.scheme.left.1.isoSpec.inv) h4
    _ = (Spec.map (CommRingCat.ofHom (algebraMap (D.neighborhoodStalk) R)) ≫ Spec.map germ) ≫
        D.neighborhood.scheme.left.1.isoSpec.inv :=
        congrArg (fun k ↦ k ≫ D.neighborhood.scheme.left.1.isoSpec.inv) (Spec.map_comp _ _)
    _ = Spec.map (CommRingCat.ofHom (algebraMap (D.neighborhoodStalk) R)) ≫
        (Spec.map germ ≫ D.neighborhood.scheme.left.1.isoSpec.inv) := Category.assoc _ _ _
    _ = D.specToNeighborhoodScheme R :=
        congrArg (fun k ↦ Spec.map (CommRingCat.ofHom (algebraMap (D.neighborhoodStalk) R)) ≫ k)
          hfrom.symm

/-- The projection of `Spec R` to a stage, as a morphism of the site. -/
def stageLegSite (i : I) : D.henselianObj R hR ⟶ (G.obj i).scheme :=
  Over.homMk (⟨D.stageLeg R G hGaff e i⟩ : B.obj hR ⟶ (G.obj i).scheme.left) (by
    apply ObjectProperty.hom_ext
    have hw := congrArg InducedCategory.Hom.hom (Over.w (D.stageMap G i))
    change D.stageLeg R G hGaff e i ≫ ((G.obj i).scheme.hom).hom =
      D.specToNeighborhoodScheme R ≫ D.neighborhood.scheme.hom.hom
    rw [← hw, InducedCategory.comp_hom]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ D.neighborhood.scheme.hom.hom) (D.stageLeg_comp_stageMap R G hGaff e he i)))

/-- The projections of `Spec R` to the stages are compatible with the transitions. -/
theorem stageLegSite_comp {i j : I} (f : j ⟶ i) :
    D.stageLegSite R hR G hGaff e he j ≫ (G ⋙ ElementaryEtaleNeighborhood.siteScheme).map f =
      D.stageLegSite R hR G hGaff e he i := by
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
  exact (henselianSchemeCone B S hS (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme)
    D.nbhdPoint (isDecentSpace_yoneda B S hS D.neighborhood.scheme) G e hGaff).w f

/-- The cone of the site over the stages with vertex `Spec R`. -/
def stageCone : Cone (G ⋙ ElementaryEtaleNeighborhood.siteScheme) where
  pt := D.henselianObj R hR
  π :=
    { app := fun i ↦ D.stageLegSite R hR G hGaff e he i
      naturality := fun _ _ f ↦
        (Category.id_comp _).trans (D.stageLegSite_comp R hR G hGaff e he f).symm }

/-- **`Spec R` is the limit of the stages in the site.** The limit of the stages exists in the
site and is preserved by the underlying scheme functor, which reflects isomorphisms; the image of
the cone is the limit cone of schemes. -/
def isLimitStageCone [G.Initial] (hIs : Cardinal.mk I < B.cutoff) {μ : Cardinal.{u}}
    (hμ : μ < B.cutoff)
    (hGμ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ) :
    IsLimit (D.stageCone R hR G hGaff e he) := by
  have hWaff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((G ⋙ ElementaryEtaleNeighborhood.siteScheme).obj i)) := hGaff
  have := BigFppfOver.hasLimit_of_isAffine_of_size_le
    (G ⋙ ElementaryEtaleNeighborhood.siteScheme) hWaff hIs hμ hGμ
  have := BigFppfOver.preservesLimit_toScheme_of_size_le
    (G ⋙ ElementaryEtaleNeighborhood.siteScheme) hWaff hIs hμ hGμ
  have : ReflectsLimit (G ⋙ ElementaryEtaleNeighborhood.siteScheme)
      (BigFppfOver.toScheme B S hS) := reflectsLimit_of_reflectsIsomorphisms _ _
  let α : G ⋙ neighborhoodScheme B S hS (yoneda.obj D.neighborhood.scheme)
      (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint ≅
      (G ⋙ ElementaryEtaleNeighborhood.siteScheme) ⋙ BigFppfOver.toScheme B S hS :=
    NatIso.ofComponents (fun i ↦ Iso.refl _) (fun f ↦
      (Category.comp_id _).trans (Category.id_comp _).symm)
  have h₁ := (IsLimit.postcomposeHomEquiv α _).symm
    (isLimitHenselianSchemeCone B S hS (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme)
      D.nbhdPoint (isDecentSpace_yoneda B S hS D.neighborhood.scheme) G e hGaff)
  refine isLimitOfReflects (BigFppfOver.toScheme B S hS) (h₁.ofIsoLimit ?_)
  exact Cone.ext (Iso.refl _) (fun i ↦ (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **`Spec R` is the limit of the stages as a presheaf.** -/
def isLimitYonedaStageCone [G.Initial] (hIs : Cardinal.mk I < B.cutoff) {μ : Cardinal.{u}}
    (hμ : μ < B.cutoff)
    (hGμ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ) :
    IsLimit (FinitePresentationSpacesOver.yonedaCone B S hS
      (G ⋙ ElementaryEtaleNeighborhood.siteScheme) (D.henselianObj R hR)
      (D.stageLegSite R hR G hGaff e he) (D.stageLegSite_comp R hR G hGaff e he)) :=
  isLimitOfPreserves yoneda (D.isLimitStageCone R hR G hGaff e he hIs hμ hGμ)

omit [IsCofiltered I] in
include hGaff in
/-- The morphisms between two stages are bounded by one cardinal below the cutoff: they are
determined by their maps on global sections of the affine target. -/
theorem mk_stage_hom_le [G.Faithful] {μ : Cardinal.{u}}
    (hGμ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ) (i j : I) :
    Cardinal.mk (i ⟶ j) ≤ 2 ^ (μ * μ) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (G.obj j).scheme) := hGaff j
  let F : (i ⟶ j) → (Γ((G.obj j).scheme.left.1, ⊤) → Γ((G.obj i).scheme.left.1, ⊤)) :=
    fun f ↦ ⇑(G.map f).hom.left.1.appTop.hom
  have hF : Function.Injective F := by
    intro f₁ f₂ h
    apply G.map_injective
    apply ElementaryEtaleNeighborhood.Hom.ext
    apply (BigFppfOver.toScheme B S hS).map_injective
    apply ext_of_isAffine
    exact CommRingCat.hom_ext (RingHom.ext (congrFun h))
  have hΓ : ∀ k, Cardinal.mk Γ((G.obj k).scheme.left.1, ⊤) ≤ μ := fun k ↦
    mk_sections_le_of_size_le (hGaff k) (hGμ k)
  calc Cardinal.mk (i ⟶ j) ≤ Cardinal.mk (Γ((G.obj j).scheme.left.1, ⊤) →
        Γ((G.obj i).scheme.left.1, ⊤)) := Cardinal.mk_le_of_injective hF
    _ = Cardinal.mk Γ((G.obj i).scheme.left.1, ⊤) ^ Cardinal.mk Γ((G.obj j).scheme.left.1, ⊤) :=
        (Cardinal.power_def _ _).symm
    _ ≤ (2 ^ μ) ^ Cardinal.mk Γ((G.obj j).scheme.left.1, ⊤) :=
        Cardinal.power_le_power_right ((hΓ i).trans (Cardinal.cantor μ).le)
    _ ≤ (2 ^ μ) ^ μ := Cardinal.power_le_power_left (Cardinal.power_ne_zero _ two_ne_zero) (hΓ j)
    _ = 2 ^ (μ * μ) := by rw [← Cardinal.power_mul]

/-- **Stacks 07SK at the stages.** The algebraic spaces of finite presentation over `Spec R` are
the filtered `2`-colimit of those over the stages. -/
theorem isFinitePresentationColimit_stage [G.Initial] [G.Faithful]
    (hIs : Cardinal.mk I < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hGμ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ) :
    FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS
      (G ⋙ ElementaryEtaleNeighborhood.siteScheme) (D.henselianObj R hR)
      (D.stageLegSite R hR G hGaff e he) (D.stageLegSite_comp R hR G hGaff e he) := by
  have hZ := BigFppfSite.contains_terminal B
  have hν := two_pow_mul_lt_cutoff (B := B) hμ
  refine FinitePresentationSpacesOver.isFinitePresentationColimit_of_isLimit
    (D.isLimitYonedaStageCone R hR G hGaff e he hIs hμ hGμ) hZ ?_ ?_ ?_ hIs hν
    (D.mk_stage_hom_le G hGaff hGμ) ?_
  · exact fun f ↦ D.isAffineHom_yoneda_map_stage hGaff f
  · exact fun i ↦ isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (hGaff i)
  · exact fun i ↦ isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
      (isAffineSpace_yoneda B S hS _ (hGaff i))
  · exact D.baseChangeSizeBounded_stage hμ hGμ

/-- **Isomorphisms descend to the stages.** A morphism of algebraic spaces of finite presentation
over a stage whose base change to `Spec R` is an isomorphism becomes an isomorphism after base
change to a later stage. -/
theorem exists_isIso_stage [G.Initial] [G.Faithful]
    (hIs : Cardinal.mk I < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hGμ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ) (i : I)
    {X Y : FinitePresentationSpacesOver B S hS (G.obj i).scheme} (f : X ⟶ Y)
    (hf : IsIso ((FinitePresentationSpacesOver.baseChange B S hS
      (D.stageLegSite R hR G hGaff e he i)).map f)) :
    ∃ (j : I) (ε : j ⟶ i), IsIso ((FinitePresentationSpacesOver.baseChange B S hS
      ((G ⋙ ElementaryEtaleNeighborhood.siteScheme).map ε)).map f) := by
  have hZ := BigFppfSite.contains_terminal B
  have hν := two_pow_mul_lt_cutoff (B := B) hμ
  refine FinitePresentationSpacesOver.exists_isIso_baseChange_map_of_isLimit
    (D.isLimitYonedaStageCone R hR G hGaff e he hIs hμ hGμ) hZ ?_ ?_ ?_ hIs hν
    (D.mk_stage_hom_le G hGaff hGμ) ?_ i f hf
  · exact fun f ↦ D.isAffineHom_yoneda_map_stage hGaff f
  · exact fun i ↦ isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (hGaff i)
  · exact fun i ↦ isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
      (isAffineSpace_yoneda B S hS _ (hGaff i))
  · exact D.baseChangeSizeBounded_stage hμ hGμ

/-- The projection of `Spec R` to a stage followed by the stage's morphism to `W` is the
canonical morphism `Spec R ⟶ W`. -/
theorem stageLegSite_comp_stageMap (i : I) :
    D.stageLegSite R hR G hGaff e he i ≫ D.stageMap G i = D.toNeighborhoodHom R hR :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (D.stageLeg_comp_stageMap R G hGaff e he i))

/-- The canonical morphism `Spec R ⟶ X` factors through every stage. -/
theorem yoneda_stageLegSite_comp_toSpace (i : I) :
    yoneda.map (D.stageLegSite R hR G hGaff e he i) ≫
        ((G.obj i).toSpace ≫ D.neighborhood.toSpace) = (D.toSpaceHom R hR).hom := by
  rw [← D.yoneda_map_stageMap G i, ← Category.assoc, ← Functor.map_comp,
    D.stageLegSite_comp_stageMap R hR G hGaff e he i]
  rfl

/-- The Yoneda images of the projections of `Spec R` to the stages are compatible with the
transitions. -/
private theorem yoneda_stageLegSite_comp_map {i j : I} (f : j ⟶ i) :
    yoneda.map (D.stageLegSite R hR G hGaff e he j) ≫ yoneda.map (G.map f).hom =
      yoneda.map (D.stageLegSite R hR G hGaff e he i) :=
  (yoneda.map_comp _ _).symm.trans
    (congrArg (fun m ↦ yoneda.map m) (D.stageLegSite_comp R hR G hGaff e he f))

section Equivalence

variable [G.Initial] [G.Faithful] [G.Full] (hIs : Cardinal.mk I < B.cutoff) {μ : Cardinal.{u}}
  (hμ : μ < B.cutoff)
  (hGμ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ)

/-- The base change along `W ⟶ X` of a modification of `X` away from `x` is a modification of
`W` away from `w`. -/
theorem isModification_pullback_nbhd {M : Over D.space.obj}
    (hM : IsModification B S hS D.openAwayFromPoint M) :
    IsModification B S hS D.nbhdAway ((Over.pullback D.neighborhood.toSpace).obj M) :=
  isModification_pullback_single B S hS D.space D.decent D.point D.isClosed_point D.neighborhood
    D.isAffine_neighborhood D.eq_of_map_eq_point hM

omit [G.Full] in
include hGaff he hIs hμ hGμ in
/-- **Faithfulness.** The base change functor of Stacks 0BH0 is faithful. -/
theorem faithful_henselianBaseChangeFunctor : (D.henselianBaseChangeFunctor R hR).Faithful := by
  refine ⟨fun {A A'} f g hfg ↦ ?_⟩
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have hcol := D.isFinitePresentationColimit_stage R hR G hGaff e he hIs hμ hGμ
  let τ₀ := (G.obj i₀).toSpace ≫ D.neighborhood.toSpace
  have hτ₀ := D.yoneda_stageLegSite_comp_toSpace R hR G hGaff e he i₀
  have h1 : (Over.pullback (D.toSpaceHom R hR).hom).map f.hom =
      (Over.pullback (D.toSpaceHom R hR).hom).map g.hom :=
    (congrArg InducedCategory.Hom.hom hfg :)
  have h2 := FinitePresentationSpacesOver.map_eq_of_natIso (Over.pullbackFactorIso hτ₀) h1
  obtain ⟨j, ε, hj⟩ := hcol.faithful i₀ (D.stageObj τ₀ A) (D.stageObj τ₀ A')
    (ObjectProperty.homMk ((Over.pullback τ₀).map f.hom))
    (ObjectProperty.homMk ((Over.pullback τ₀).map g.hom)) (ObjectProperty.hom_ext _ h2)
  have h3 := congrArg InducedCategory.Hom.hom hj
  have hτj : yoneda.map (G.map ε).hom ≫ ((G.obj i₀).toSpace ≫ D.neighborhood.toSpace) =
      (G.obj j).toSpace ≫ D.neighborhood.toSpace := by
    rw [← Category.assoc, (G.map ε).over]
  have h4 := FinitePresentationSpacesOver.map_eq_of_natIso (Over.pullbackFactorIso hτj).symm h3
  obtain ⟨E', hE'aff, hE'u, ⟨r⟩⟩ := ElementaryEtaleNeighborhood.exists_hom_of_unique_point B S hS
    D.neighborhood.scheme D.neighborhood.point D.neighborhood.residueField_contained (G.obj j)
    (hGaff j)
  have hτE : yoneda.map r.hom ≫ ((G.obj j).toSpace ≫ D.neighborhood.toSpace) =
      E'.toSpace ≫ D.neighborhood.toSpace := by
    rw [← Category.assoc, r.over]
  have h5 := FinitePresentationSpacesOver.map_eq_of_natIso (Over.pullbackFactorIso hτE).symm
    (congrArg (Over.pullback (yoneda.map r.hom)).map h4)
  have h6 := FinitePresentationSpacesOver.map_eq_of_natIso
    (Over.pullbackFactorIso (rfl : E'.toSpace ≫ D.neighborhood.toSpace = _)) h5
  have h7 := eq_of_pullback_map_eq_single B S hS D.nbhdSpace
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint D.isClosed_nbhdPoint E'
    hE'aff hE'u (D.isModification_pullback_nbhd A.property.1)
    (D.isModification_pullback_nbhd A'.property.1) _ _ h6
  have h8 := eq_of_pullback_map_eq_single B S hS D.space D.decent D.point D.isClosed_point
    D.neighborhood D.isAffine_neighborhood D.eq_of_map_eq_point A.property.1 A'.property.1 _ _ h7
  exact ObjectProperty.hom_ext _ h8

include hGaff he hIs hμ hGμ in
/-- **Essential surjectivity.** An algebraic space of finite presentation over `Spec R` which is an
isomorphism over `V` comes from a stage; that it is an isomorphism over `V` descends to a later
stage over the preimage of `W ∖ {w}`; over a refinement of that stage with a single point above
`w` it comes from `W`, and so from `X`. -/
theorem essSurj_henselianBaseChangeFunctor : (D.henselianBaseChangeFunctor R hR).EssSurj := by
  refine ⟨fun Yobj ↦ ?_⟩
  have hcol := D.isFinitePresentationColimit_stage R hR G hGaff e he hIs hμ hGμ
  let p := D.stageLegSite R hR G hGaff e he
  let Yfp : FinitePresentationSpacesOver B S hS (D.henselianObj R hR) :=
    ⟨Yobj.obj, Yobj.property.1.1, Yobj.property.2⟩
  obtain ⟨i, Yi, ⟨ψ⟩⟩ := hcol.essSurj Yfp
  let ψ' : (Over.pullback (yoneda.map (p i))).obj Yi.obj ≅ Yobj.obj :=
    (ObjectProperty.ι _).mapIso ψ
  -- the isomorphism over the preimage of `W ∖ {w}` in `Spec R`
  have hle : (D.nbhdAway.preimage (G.obj i).toSpace).preimage (yoneda.map (p i)) ≤
      D.openAwayFromClosedPoint R hR := by
    rw [← Subfunctor.preimage_comp, ← D.yoneda_map_stageMap G i, ← Functor.map_comp,
      D.stageLegSite_comp_stageMap R hR G hGaff e he i]
    exact D.preimage_nbhdAway_le R hR
  have hYV : IsIso (pullback.snd Yobj.obj.hom (D.openAwayFromClosedPoint R hR).ι) :=
    Yobj.property.1.2
  have hYi : IsIso (pullback.snd ((Over.pullback (yoneda.map (p i))).obj Yi.obj).hom
      ((D.nbhdAway.preimage (G.obj i).toSpace).preimage (yoneda.map (p i))).ι) :=
    isIso_pullback_snd_of_factor _ (Subfunctor.homOfLe hle) (Subfunctor.homOfLe_ι hle)
      (isIso_pullback_snd_of_overIso ψ' hYV)
  -- the restriction morphism at the stage `i` becomes an isomorphism over `Spec R`
  have hπ : IsIso ((FinitePresentationSpacesOver.baseChange B S hS (p i)).map
      (D.restrictHom (G.obj i).toSpace Yi)) := by
    have h := (isIso_pullback_map_toSubfunctor_iff (yoneda.map (p i))
      (D.nbhdAway.preimage (G.obj i).toSpace) Yi.obj).mpr hYi
    have : IsIso ((ObjectProperty.ι _).map ((FinitePresentationSpacesOver.baseChange B S hS
        (p i)).map (D.restrictHom (G.obj i).toSpace Yi))) := h
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  obtain ⟨j, ε, hπj⟩ := D.exists_isIso_stage R hR G hGaff e he hIs hμ hGμ i _ hπ
  let c : yoneda.obj (G.obj j).scheme ⟶ yoneda.obj (G.obj i).scheme := yoneda.map (G.map ε).hom
  have hYj : IsIso (pullback.snd ((Over.pullback c).obj Yi.obj).hom
      ((D.nbhdAway.preimage (G.obj i).toSpace).preimage c).ι) := by
    exact (isIso_pullback_map_toSubfunctor_iff c (D.nbhdAway.preimage (G.obj i).toSpace)
      Yi.obj).mp <| (ObjectProperty.ι _).map_isIso ((FinitePresentationSpacesOver.baseChange B S hS
      ((G ⋙ ElementaryEtaleNeighborhood.siteScheme).map ε)).map
        (D.restrictHom (G.obj i).toSpace Yi))
  have hUj : (D.nbhdAway.preimage (G.obj i).toSpace).preimage c =
      D.nbhdAway.preimage (G.obj j).toSpace :=
    (Subfunctor.preimage_comp D.nbhdAway c (G.obj i).toSpace).symm.trans
      (congrArg D.nbhdAway.preimage (G.map ε).over)
  -- refine to a neighbourhood with a single point above `w`
  obtain ⟨E', hE'aff, hE'u, r, k, r', ε', hrr⟩ := D.exists_refinement G hGaff j
  let Yj := (Over.pullback c).obj Yi.obj
  let Z := (Over.pullback (yoneda.map r.hom)).obj Yj
  have hYjalg : IsAlgebraicSpace B S hS Yj.left :=
    isAlgebraicSpace_pullback B S hS Yi.obj.hom c Yi.property.1 (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _)
  have hYjfp : IsFinitePresentation B S hS Yj.hom :=
    isFinitePresentation_pullback_snd B S hS Yi.obj.hom c Yi.property.1
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) Yi.property.2
  have hZalg : IsAlgebraicSpace B S hS Z.left :=
    isAlgebraicSpace_pullback B S hS Yj.hom (yoneda.map r.hom) hYjalg
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
  have hZfp : IsFinitePresentation B S hS Z.hom :=
    isFinitePresentation_pullback_snd B S hS Yj.hom (yoneda.map r.hom) hYjalg
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) hYjfp
  have hZiso : IsIso (pullback.snd Z.hom
      ((D.nbhdAway.preimage (G.obj j).toSpace).preimage (yoneda.map r.hom)).ι) := by
    have h := hUj ▸ hYj
    exact isIso_pullback_snd_preimage B S hS Yj.hom (yoneda.map r.hom) _ h
  have hE'le : openSubspaceOfPoints B S hS (yoneda.obj E'.scheme)
      {presheafPoint B S hS E'.scheme E'.point E'.residueField_contained}ᶜ ≤
      (D.nbhdAway.preimage (G.obj j).toSpace).preimage (yoneda.map r.hom) := by
    rw [← Subfunctor.preimage_comp, r.over, preimage_openSubspaceOfPoints]
    exact openSubspaceOfPoints_mono B S hS (fun y hy hcon ↦ hy (hE'u y hcon))
  have hZmod : IsModification B S hS (openSubspaceOfPoints B S hS (yoneda.obj E'.scheme)
      {presheafPoint B S hS E'.scheme E'.point E'.residueField_contained}ᶜ) Z :=
    ⟨hZalg, isIso_pullback_snd_of_factor _ (Subfunctor.homOfLe hE'le)
      (Subfunctor.homOfLe_ι hE'le) hZiso⟩
  -- descend to `W`, then to `X`
  obtain ⟨A₁, hA₁, ⟨eA₁⟩⟩ := exists_pullback_obj_iso_single B S hS D.nbhdSpace
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint D.isClosed_nbhdPoint E'
    hE'aff hE'u hZmod
  have hA₁fp : IsFinitePresentation B S hS A₁.hom :=
    (isFinitePresentation_iff_pullback_single B S hS D.nbhdSpace
      (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint D.isClosed_nbhdPoint E'
      hE'aff hE'u hA₁).mpr
      (isFinitePresentation_of_overIso (isAlgebraicSpace_yoneda B S hS _) eA₁ hZalg hZfp)
  obtain ⟨A, hA, ⟨eA⟩⟩ := exists_pullback_obj_iso_single B S hS D.space D.decent D.point
    D.isClosed_point D.neighborhood D.isAffine_neighborhood D.eq_of_map_eq_point hA₁
  have hAfp : IsFinitePresentation B S hS A.hom :=
    (isFinitePresentation_iff_pullback_single B S hS D.space D.decent D.point
      D.isClosed_point D.neighborhood D.isAffine_neighborhood D.eq_of_map_eq_point hA).mpr
      (isFinitePresentation_of_overIso (isAlgebraicSpace_yoneda B S hS _) eA hA₁.1 hA₁fp)
  let A' : D.modificationsAwayFromPoint := ⟨A, ⟨hA, hAfp⟩⟩
  -- the chain of comparisons
  have ht : yoneda.map (p k) ≫ (yoneda.map r'.hom ≫ (E'.toSpace ≫ D.neighborhood.toSpace)) =
      (D.toSpaceHom R hR).hom :=
    (congrArg (yoneda.map (p k) ≫ ·) ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ D.neighborhood.toSpace) r'.over))).trans
      (D.yoneda_stageLegSite_comp_toSpace R hR G hGaff e he k)
  have hpk := D.yoneda_stageLegSite_comp_map R hR G hGaff e he ε'
  have hpj := D.yoneda_stageLegSite_comp_map R hR G hGaff e he ε
  refine ⟨A', ⟨(ObjectProperty.fullyFaithfulι _).preimageIso ?_⟩⟩
  exact (Over.pullbackFactorIso ht).app A ≪≫
    (Over.pullback (yoneda.map (p k))).mapIso
      ((Over.pullbackFactorIso (rfl : yoneda.map r'.hom ≫
          (E'.toSpace ≫ D.neighborhood.toSpace) = _)).app A ≪≫
        (Over.pullback (yoneda.map r'.hom)).mapIso
          ((Over.pullbackFactorIso (rfl : E'.toSpace ≫ D.neighborhood.toSpace = _)).app A ≪≫
            (Over.pullback E'.toSpace).mapIso eA ≪≫ eA₁) ≪≫
        (Over.pullbackFactorIso hrr).symm.app Yj) ≪≫
    (Over.pullbackFactorIso hpk).symm.app Yj ≪≫
    (Over.pullbackFactorIso hpj).symm.app Yi.obj ≪≫ ψ'

include hGaff he hIs hμ hGμ in
/-- **Fullness.** A morphism over `Spec R` comes from a morphism over a stage; transported to a
refinement of that stage with a single point above `w`, it comes from `W`, and so from `X`; the
comparisons of the iterated base changes along the factorisations of `Spec R ⟶ X` are the pinned
ones, so the morphism found over `X` base changes back to the given one. -/
theorem full_henselianBaseChangeFunctor : (D.henselianBaseChangeFunctor R hR).Full := by
  refine ⟨fun {A A'} φ ↦ ?_⟩
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have hcol := D.isFinitePresentationColimit_stage R hR G hGaff e he hIs hμ hGμ
  let p := D.stageLegSite R hR G hGaff e he
  let t : yoneda.obj (D.henselianObj R hR) ⟶ D.space.obj := (D.toSpaceHom R hR).hom
  let a := D.neighborhood.toSpace
  let τ₀ := (G.obj i₀).toSpace ≫ a
  have h₀ : yoneda.map (p i₀) ≫ τ₀ = t := D.yoneda_stageLegSite_comp_toSpace R hR G hGaff e he i₀
  let φO : (Over.pullback t).obj A.obj ⟶ (Over.pullback t).obj A'.obj := φ.hom
  let φ₀ := (Over.pullbackFactorObjIso h₀ A.obj).inv ≫ φO ≫
    (Over.pullbackFactorObjIso h₀ A'.obj).hom
  obtain ⟨j, ε, h', hh'⟩ := hcol.full i₀ (D.stageObj τ₀ A) (D.stageObj τ₀ A')
    (ObjectProperty.homMk φ₀)
  have hpe := D.yoneda_stageLegSite_comp_map R hR G hGaff e he ε
  have hk : (Over.pullbackFactorObjIso hpe ((Over.pullback τ₀).obj A.obj)).hom ≫
      (Over.pullback (yoneda.map (p j))).map h'.hom =
      φ₀ ≫ (Over.pullbackFactorObjIso hpe ((Over.pullback τ₀).obj A'.obj)).hom := by
    have hX := FinitePresentationSpacesOver.baseChangeFactorIso_hom_app_left B S hS
      (D.stageLegSite_comp R hR G hGaff e he ε) (D.stageObj τ₀ A)
    have hY := FinitePresentationSpacesOver.baseChangeFactorIso_hom_app_left B S hS
      (D.stageLegSite_comp R hR G hGaff e he ε) (D.stageObj τ₀ A')
    simp only [ObjectProperty.ι_map] at hX hY
    have h2 := congrArg InducedCategory.Hom.hom hh'
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom] at h2
    exact ((congrArg (· ≫ ((FinitePresentationSpacesOver.baseChange B S hS (p j)).map h').hom)
      hX).symm.trans h2).trans (congrArg (fun x ↦ φ₀ ≫ x) hY)
  have hτj : yoneda.map (G.map ε).hom ≫ τ₀ = (G.obj j).toSpace ≫ a :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ a) (G.map ε).over)
  have h₂ : yoneda.map (p j) ≫ ((G.obj j).toSpace ≫ a) = t :=
    D.yoneda_stageLegSite_comp_toSpace R hR G hGaff e he j
  have hφj := Over.eq_pullbackFactor_of_compat h₀ hpe hτj h₂ φO h'.hom hk
  -- refine to a neighbourhood with a single point above `w`
  obtain ⟨E', hE'aff, hE'u, r, k, r', ε', hrr⟩ := D.exists_refinement G hGaff j
  have hpk := D.yoneda_stageLegSite_comp_map R hR G hGaff e he ε'
  let hj := (Over.pullbackFactorObjIso hτj A.obj).hom ≫ h'.hom ≫
    (Over.pullbackFactorObjIso hτj A'.obj).inv
  have hg' : (yoneda.map (p k) ≫ yoneda.map r'.hom) ≫ yoneda.map r.hom = yoneda.map (p j) :=
    (Category.assoc _ _ _).trans ((congrArg (yoneda.map (p k) ≫ ·) hrr).trans hpk)
  have hτ' : yoneda.map r.hom ≫ ((G.obj j).toSpace ≫ a) = E'.toSpace ≫ a :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ a) r.over)
  have h₂' : (yoneda.map (p k) ≫ yoneda.map r'.hom) ≫ (E'.toSpace ≫ a) = t := by
    rwa [← hτ', ← Category.assoc, hg']
  have hk2 : (Over.pullbackFactorObjIso hg' ((Over.pullback ((G.obj j).toSpace ≫ a)).obj
      A.obj)).hom ≫ (Over.pullback (yoneda.map (p k) ≫ yoneda.map r'.hom)).map
        ((Over.pullback (yoneda.map r.hom)).map hj) =
      ((Over.pullbackFactorObjIso h₂ A.obj).inv ≫ φO ≫
        (Over.pullbackFactorObjIso h₂ A'.obj).hom) ≫
        (Over.pullbackFactorObjIso hg' ((Over.pullback ((G.obj j).toSpace ≫ a)).obj
          A'.obj)).hom := by
    have hc : (Over.pullbackFactorObjIso h₂ A.obj).inv ≫ φO ≫
        (Over.pullbackFactorObjIso h₂ A'.obj).hom =
        (Over.pullback (yoneda.map (p j))).map hj := by
      rw [hφj]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      rfl
    rw [hc]
    exact ((Over.pullbackFactorIso hg').hom.naturality hj).symm
  have hφE := Over.eq_pullbackFactor_of_compat h₂ hg' hτ' h₂' φO
    ((Over.pullback (yoneda.map r.hom)).map hj) hk2
  -- lift through the two single-point equivalences
  let hE := (Over.pullbackFactorObjIso hτ' A.obj).hom ≫ (Over.pullback (yoneda.map r.hom)).map hj ≫
    (Over.pullbackFactorObjIso hτ' A'.obj).inv
  let β := Over.pullbackFactorIso (rfl : E'.toSpace ≫ a = E'.toSpace ≫ a)
  let h₁ := (β.app A.obj).inv ≫ hE ≫ (β.app A'.obj).hom
  obtain ⟨ψ₁, hψ₁⟩ := exists_eq_pullback_map_single B S hS D.nbhdSpace
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint D.isClosed_nbhdPoint E'
    hE'aff hE'u (D.isModification_pullback_nbhd A.property.1)
    (D.isModification_pullback_nbhd A'.property.1) h₁
  obtain ⟨ψ₀, hψ₀⟩ := exists_eq_pullback_map_single B S hS D.space D.decent D.point
    D.isClosed_point D.neighborhood D.isAffine_neighborhood D.eq_of_map_eq_point A.property.1
    A'.property.1 ψ₁
  have hE_eq : (Over.pullback (E'.toSpace ≫ a)).map ψ₀ = hE := by
    have hn := β.hom.naturality ψ₀
    rw [← Iso.cancel_iso_hom_right _ _ (β.app A'.obj), Iso.app_hom, hn]
    change β.hom.app A.obj ≫ (Over.pullback E'.toSpace).map ((Over.pullback a).map ψ₀) = _
    rw [hψ₀, hψ₁]
    simp only [h₁, Iso.app_inv, Iso.app_hom, Iso.hom_inv_id_app_assoc]
  refine ⟨ObjectProperty.homMk ψ₀, ?_⟩
  apply ObjectProperty.hom_ext
  change (Over.pullback t).map ψ₀ = φO
  have hφE' : φO = (Over.pullbackFactorObjIso h₂' A.obj).hom ≫
      (Over.pullback (yoneda.map (p k) ≫ yoneda.map r'.hom)).map hE ≫
        (Over.pullbackFactorObjIso h₂' A'.obj).inv := hφE
  rw [hφE', ← hE_eq]
  exact (Iso.eq_comp_inv _).mpr ((Over.pullbackFactorIso h₂').hom.naturality ψ₀)

end Equivalence

end Model

/-! ### Stacks 0BH0 -/

/-- **The base change functor of Stacks 0BH0 is an equivalence**, for any containment of
`Spec R` in the site. Since that containment is a proposition, this is the same statement as
`ClosedPointNeighborhood.isEquivalence_henselianBaseChangeFunctor_of_isHenselization`, where it is
supplied by `ClosedPointNeighborhood.contains_spec_of_isHenselization`. -/
theorem isEquivalence_henselianBaseChangeFunctor :
    (D.henselianBaseChangeFunctor R hR).IsEquivalence := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj D.neighborhood.scheme) :=
    D.isAffine_neighborhood
  obtain ⟨I, _, _, G, hGi, hIs, ⟨μ, hμ, hGμ⟩, hGaff, hGfull, hGfaith⟩ :=
    ElementaryEtaleNeighborhood.exists_bounded_cofiltered_initial_affine_model_of_iso B S hS
      (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme)
      (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.neighborhood.scheme (Iso.refl _)
      D.nbhdPoint
  have := hGi
  have := hGfull
  have := hGfaith
  let := henselianLocalRing_isLocalRing B S hS (yoneda.obj D.neighborhood.scheme)
    (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme)
  let := stalkAlgebra B S hS (yoneda.obj D.neighborhood.scheme)
    (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdSelf
  obtain ⟨e⟩ := exists_algEquiv_henselianLocalRing B S hS (yoneda.obj D.neighborhood.scheme)
    (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdSelf R
  have he : ∀ a : D.neighborhoodStalk, e.toRingEquiv (algebraMap _ R a) =
      stalkToHenselianLocalRing B S hS (yoneda.obj D.neighborhood.scheme)
        (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
        (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdSelf a :=
    fun a ↦ e.commutes a
  exact
    { faithful := D.faithful_henselianBaseChangeFunctor R hR G hGaff e.toRingEquiv he hIs hμ hGμ
      full := D.full_henselianBaseChangeFunctor R hR G hGaff e.toRingEquiv he hIs hμ hGμ
      essSurj := D.essSurj_henselianBaseChangeFunctor R hR G hGaff e.toRingEquiv he hIs hμ hGμ }

include D in
/-- **The spectrum of a henselization of `𝒪_{W, w}` belongs to the site.** The henselization is the
colimit of the rings of global sections of a small cofiltered family of étale neighbourhoods of
`w`, fewer than the cutoff in number and each of size at most one cardinal below the cutoff. -/
theorem contains_spec_of_isHenselization : B.Contains (Spec (.of R)) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj D.neighborhood.scheme) :=
    D.isAffine_neighborhood
  obtain ⟨I, _, _, G, hGi, hIs, ⟨μ, hμ, hGμ⟩, hGaff, -, -⟩ :=
    ElementaryEtaleNeighborhood.exists_bounded_cofiltered_initial_affine_model_of_iso B S hS
      (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme)
      (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.neighborhood.scheme (Iso.refl _)
      D.nbhdPoint
  have := hGi
  let := henselianLocalRing_isLocalRing B S hS (yoneda.obj D.neighborhood.scheme)
    (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme)
  let := stalkAlgebra B S hS (yoneda.obj D.neighborhood.scheme)
    (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdSelf
  obtain ⟨e⟩ := exists_algEquiv_henselianLocalRing B S hS (yoneda.obj D.neighborhood.scheme)
    (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
    (isDecentSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdSelf R
  have hc := isColimitHenselianCocone B S hS (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme)
    D.nbhdPoint (isDecentSpace_yoneda B S hS D.neighborhood.scheme) G e.toRingEquiv
  have hcf := isColimitOfPreserves (forget CommRingCat.{u}) hc
  have hsurj : Function.Surjective (fun z : Σ i : Iᵒᵖ, Γ((G.obj i.unop).scheme.left.1, ⊤) ↦
      henselianLeg B S hS (isAlgebraicSpace_yoneda B S hS D.neighborhood.scheme) D.nbhdPoint
        (isDecentSpace_yoneda B S hS D.neighborhood.scheme) G e.toRingEquiv z.1.unop z.2) := by
    intro r
    obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit hcf r
    exact ⟨⟨i, y⟩, hy⟩
  have hΓ : ∀ k, Cardinal.mk Γ((G.obj k).scheme.left.1, ⊤) ≤ μ := fun k ↦
    mk_sections_le_of_size_le (hGaff k) (hGμ k)
  have hR' : Cardinal.mk R < B.cutoff := by
    refine lt_of_le_of_lt (Cardinal.mk_le_of_surjective hsurj) ?_
    rw [Cardinal.mk_sigma]
    refine lt_of_le_of_lt (Cardinal.sum_le_sum _ (fun _ ↦ μ) (fun i ↦ hΓ i.unop)) ?_
    rw [Cardinal.sum_const', ← Cardinal.mk_congr (Opposite.equivToOpposite (α := I))]
    exact Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le hIs hμ
  change (Spec (CommRingCat.of R)).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff hR'

/-- **Stacks 0BH0.** Let `X` be a decent algebraic space over `S` and `x ∈ |X|` a closed point
such that `U = X ∖ {x} ⟶ X` is quasi-compact; let `(W, w) → (X, x)` be an affine elementary étale
neighbourhood with `w` the only point above `x` (Stacks 0BBP) and let `R` be a henselization of
`𝒪_{W, w}`, so that `R = 𝒪^h_{X, x}` (Stacks 0EMY). With `V = Spec(𝒪^h_{X, x}) ∖ {𝔪^h_x}`, the base
change functor from the morphisms `f : Y ⟶ X` of finite presentation with `f⁻¹(U) ⟶ U` an
isomorphism to the morphisms `g : Y ⟶ Spec(𝒪^h_{X, x})` of finite presentation with
`g⁻¹(V) ⟶ V` an isomorphism is an equivalence of categories. -/
@[stacks 0BH0]
theorem isEquivalence_henselianBaseChangeFunctor_of_isHenselization :
    (D.henselianBaseChangeFunctor R (D.contains_spec_of_isHenselization R)).IsEquivalence :=
  D.isEquivalence_henselianBaseChangeFunctor R _

end Henselian

end ClosedPointNeighborhood

end AlgebraicGeometry.Space

end
