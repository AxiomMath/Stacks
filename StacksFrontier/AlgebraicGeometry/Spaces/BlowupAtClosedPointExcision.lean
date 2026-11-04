module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizedBlowupFactorizationRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryEtaleNeighborhoodSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction

/-!
# Blowing up at a closed point, glued from an étale neighbourhood

Let `X` be a decent algebraic space over a scheme `S` with pairwise distinct closed points
`x₁, …, xₙ` and chosen elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` (Stacks 0BH9), and
let `a : G ⟶ X` be an algebraic space over `X` which is unchanged over `X ∖ {x₁, …, xₙ}`. Write
`P = G ×_X Uᵢ`, with projections `ψ : P ⟶ G` and `π : P ⟶ Uᵢ`. If `t` is a closed point of `P`
over `uᵢ` and `P' ⟶ P` is a blowing up of `P` at `t`, then `G` has a blowing up `W ⟶ G` at the
closed point `ψ(t)` whose base change along `ψ` is `P' ⟶ P`.

This is how a blowing up of a neighbourhood is lifted to the whole space in the proof of
Stacks 0BHL ("we construct the sequence of blowing ups of `X` in exactly the same manner"): the
blowing up of `G` is not constructed, but glued, by the excision of Stacks 0BGY, from `P' ⟶ P` and
the identity over `G ∖ {ψ(t)}`; the universal property of Stacks 085U is then checked on the
covering of `X` by `X ∖ {x₁, …, xₙ}` and the neighbourhoods, where the lifts are unique away from
`Uᵢ` and are given by the universal property of `P' ⟶ P` over `Uᵢ`.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isBlowupAlong_of_isBlowupAlong_restriction`:
  the lift of a blowing up at a closed point from `P` to `G`.

## References

* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A smaller subfunctor is carried isomorphically onto its preimage as soon as a larger one
is.** On sections, `T.fromPreimage f` is the restriction of the bijection `Q.fromPreimage f` to
the sections lying over `T`. -/
theorem isIso_fromPreimage_of_le {V X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ X)
    {T Q : Subfunctor X} (hTQ : T ≤ Q) (hQ : IsIso (Q.fromPreimage f)) :
    IsIso (T.fromPreimage f) := by
  have hbij : ∀ U, Function.Bijective ((Q.fromPreimage f).app U) := fun U =>
    (isIso_iff_bijective _).mp (inferInstanceAs (IsIso ((Q.fromPreimage f).app U)))
  refine (NatTrans.isIso_iff_isIso_app _).mpr fun U => ?_
  refine (isIso_iff_bijective _).mpr ⟨fun y₁ y₂ hy => ?_, fun z => ?_⟩
  · have hval : f.app U y₁.1 = f.app U y₂.1 := congrArg Subtype.val hy
    have h : (Q.fromPreimage f).app U ⟨y₁.1, hTQ _ y₁.2⟩ =
        (Q.fromPreimage f).app U ⟨y₂.1, hTQ _ y₂.2⟩ :=
      Subtype.ext hval
    have h' := congrArg Subtype.val ((hbij U).1 h)
    exact Subtype.ext h'
  · obtain ⟨w, hw⟩ := (hbij U).2 ⟨z.1, hTQ _ z.2⟩
    have hw' : f.app U w.1 = z.1 := congrArg Subtype.val hw
    refine ⟨⟨w.1, ?_⟩, Subtype.ext hw'⟩
    show f.app U w.1 ∈ T.obj U
    rw [hw']
    exact z.2

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

section Lift

variable (i : Fin n) {G : AlgebraicSpaces B S hS} (a : G ⟶ D.space)

/-- A point of `G ×_X Uᵢ` over `uᵢ` lies over `xᵢ` in `G`. -/
theorem pointsMap_restrictionFst_eq_point {t : points B S hS
      (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj}
    (htu : pointsMap B S hS _ (D.restrictionHom i a).hom t = D.neighborhoodPoint i) :
    pointsMap B S hS G.obj a.hom (pointsMap B S hS _ (D.restrictionFst i a).hom t) =
      D.point i := by
  have h1 := congrArg (fun m => pointsMap B S hS _ m.hom t)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS a (D.toSpaceHom i)).w
  simp only [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp_apply] at h1
  refine h1.trans ?_
  show pointsMap B S hS _ (D.toSpaceHom i).hom
    (pointsMap B S hS _ (D.restrictionHom i a).hom t) = _
  rw [htu]
  exact D.pointsMap_toSpaceHom_neighborhoodPoint i

/-- **The only point of `G ×_X Uᵢ` over the image in `G` of a point over `uᵢ` is that point.** -/
theorem preimage_pointsMap_restrictionFst {t : points B S hS
      (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj}
    (htu : pointsMap B S hS _ (D.restrictionHom i a).hom t = D.neighborhoodPoint i) :
    pointsMap B S hS _ (D.restrictionFst i a).hom ⁻¹'
      {pointsMap B S hS _ (D.restrictionFst i a).hom t} = {t} := by
  ext t'
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun ht' => ?_, fun ht' => ht' ▸ rfl⟩
  refine pointsMap_fst_injOn_of_isIso_fromPreimage (D.toSpaceHom i).hom a.hom
    (D.pointSubspace i) (D.isIso_fromPreimage_pointSubspace i)
    (D.range_pointsMap_ι_pointSubspace i) (t := t') (t' := t) ?_ ht'
  show pointsMap B S hS G.obj a.hom (pointsMap B S hS _ (D.restrictionFst i a).hom t') = _
  rw [ht']
  exact D.pointsMap_restrictionFst_eq_point i a htu

/-- The image in `G` of a closed point of `G ×_X Uᵢ` over `uᵢ` is a closed point. -/
theorem isClosed_singleton_pointsMap_restrictionFst {t : points B S hS
      (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj}
    (ht : IsClosed ({t} : Set (points B S hS
      (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj)))
    (htu : pointsMap B S hS _ (D.restrictionHom i a).hom t = D.neighborhoodPoint i) :
    IsClosed ({pointsMap B S hS _ (D.restrictionFst i a).hom t} :
      Set (points B S hS G.obj)) :=
  isClosed_singleton_pointsMap_fst_of_isIso_fromPreimage (D.neighborhoodSpace i).property
    D.space.property G.property (D.toSpaceHom i).hom (D.neighborhood i).etale_toSpace a.hom
    (D.pointSubspace i) (D.isIso_fromPreimage_pointSubspace i)
    (D.range_pointsMap_ι_pointSubspace i) (D.isClosed_point i) ht
    (D.pointsMap_restrictionFst_eq_point i a htu)

/-- **The reduced point `z` of `G` over `xᵢ` is carried isomorphically onto its preimage in
`G ×_X Uᵢ`.** It is contained in the inverse image in `G` of the subspace `{xᵢ}` of `X`, which is
carried isomorphically onto its preimage because `{xᵢ}` is, by the choice of the neighbourhood. -/
theorem isIso_fromPreimage_closedPointSubspace {z : points B S hS G.obj}
    (hz : IsClosed ({z} : Set (points B S hS G.obj)))
    (hzx : pointsMap B S hS G.obj a.hom z = D.point i) :
    IsIso ((closedPointSubspace B S hS z hz).1.fromPreimage (D.restrictionFst i a).hom) := by
  set Q := (D.pointSubspace i).preimage a.hom
  have hQ : IsClosedSubspace B S hS Q :=
    isClosedSubspace_preimage B S hS a.hom _ D.space.property G.property
      (D.isClosedSubspace_pointSubspace i)
  have hle : (closedPointSubspace B S hS z hz).1 ≤ Q := by
    refine le_trans (reducedClosedSubspace_mono B S hS G.property {z} _ hz
      (isClosed_range_pointsMap_of_isClosedImmersion B S hS G.property Q.ι hQ.2) ?_)
      (reducedClosedSubspace_le_of_isClosedSubspace B S hS G.property Q hQ)
    rintro _ rfl
    have h := subspacePointSet_preimage B S hS a.hom (D.pointSubspace i)
    simp only [subspacePointSet] at h
    rw [h, Set.mem_preimage, D.range_pointsMap_ι_pointSubspace i, hzx]
    rfl
  exact isIso_fromPreimage_of_le _ hle
    (isIso_fromPreimage_fst_of_isIso_fromPreimage (D.toSpaceHom i).hom a.hom (D.pointSubspace i)
      (D.isIso_fromPreimage_pointSubspace i))

/-- A morphism whose restriction over an open subspace `U` is an isomorphism has an
isomorphism as base change along the inclusion of `U`. -/
theorem isIso_pullback_snd_of_isIso_fromPreimage {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) (U : Subfunctor X) (h : IsIso (U.fromPreimage f)) :
    IsIso (pullback.snd f U.ι) := by
  have sq := (Subfunctor.isPullback_preimage f U).flip
  rw [← sq.isoPullback_inv_snd]
  infer_instance

/-- The projection `G ×_X Uᵢ ⟶ G` is étale. -/
private theorem isEtale_restrictionFst :
    IsEtale B S hS (D.restrictionFst i a).hom :=
  isEtale_pullback_fst B S hS G.property D.space.property (D.neighborhoodSpace i).property
    _ _ (D.neighborhood i).etale_toSpace

/-- The inverse image in `G ×_X Uᵢ` of the point `ψ(t)` of `G` is the point `t`. -/
private theorem preimage_closedPointSubspace_restrictionFst
    {t : points B S hS (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj}
    (ht : IsClosed ({t} : Set (points B S hS
      (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj)))
    (htu : pointsMap B S hS _ (D.restrictionHom i a).hom t = D.neighborhoodPoint i) :
    (closedPointSubspace B S hS (pointsMap B S hS _ (D.restrictionFst i a).hom t)
        (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)).1.preimage
          (D.restrictionFst i a).hom = (closedPointSubspace B S hS t ht).1 :=
  congrArg (fun Z : ClosedSubspaces B S hS _ => Z.1)
    (preimageClosedSubspace_closedPointSubspace (D.restrictionFst i a)
      (D.isEtale_restrictionFst i a)
      (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu) ht
      (D.preimage_pointsMap_restrictionFst i a htu))

/-- **The blowing up at `t` glued, by excision, to an algebraic space over `G`.** For a closed
point `t` of `P = G ×_X Uᵢ` over `uᵢ` and a blowing up `P' ⟶ P` at `t`, there is an algebraic
space `W ⟶ G`, unchanged over `G ∖ {ψ(t)}`, whose base change along `ψ : P ⟶ G` is
`P' ⟶ P`. -/
theorem exists_excision_of_isBlowupAlong {t : points B S hS
      (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj}
    (ht : IsClosed ({t} : Set (points B S hS
      (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj)))
    (htu : pointsMap B S hS _ (D.restrictionHom i a).hom t = D.neighborhoodPoint i)
    {X' : AlgebraicSpaces B S hS}
    {bl : X' ⟶ AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)}
    (hbl : IsBlowupAlong B S hS (closedPointSubspace B S hS t ht) bl) :
    ∃ (W : AlgebraicSpaces B S hS) (w : W ⟶ G)
      (e : AlgebraicSpaces.fiberProduct B S hS w (D.restrictionFst i a) ≅ X'),
      e.hom ≫ bl = ObjectProperty.homMk (pullback.snd w.hom (D.restrictionFst i a).hom) ∧
        IsIso (pullback.snd w.hom (openComplement B S hS (closedPointSubspace B S hS
          (pointsMap B S hS _ (D.restrictionFst i a).hom t)
          (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)).1).ι) := by
  have hz := D.isClosed_singleton_pointsMap_restrictionFst i a ht htu
  let T := closedPointSubspace B S hS (pointsMap B S hS _ (D.restrictionFst i a).hom t) hz
  have hsep : IsSeparated B S hS (D.restrictionFst i a).hom :=
    isSeparated_pullbackFst B S hS a.hom (D.isSeparated_toSpaceHom i)
  have hfT : IsIso (T.1.fromPreimage (D.restrictionFst i a).hom) :=
    D.isIso_fromPreimage_closedPointSubspace i a hz (D.pointsMap_restrictionFst_eq_point i a htu)
  -- the blowing up is an isomorphism over the preimage of `G ∖ {z}`
  let U := openComplementOfClosedSubspace B S hS
    (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)) (closedPointSubspace B S hS t ht)
  have hU : IsIso (pullback.snd bl.hom U.1.ι) :=
    isIso_pullback_snd_of_isIso_fromPreimage _ _ (isIso_fromPreimage_openComplement hbl)
  have hle : (openComplement B S hS T.1).preimage (D.restrictionFst i a).hom ≤ U.1 := by
    refine le_of_range_pointsMap_ι_subset B S hS U.2 ?_
    have h1 := subspacePointSet_preimage B S hS (D.restrictionFst i a).hom
      (openComplement B S hS T.1)
    have h2 := subspacePointSet_openComplement B S hS
      (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)) (closedPointSubspace B S hS t ht)
    simp only [subspacePointSet] at h1 h2
    rw [h1, h2, range_pointsMap_ι_openComplement, range_pointsMap_ι_closedPointSubspace,
      range_pointsMap_ι_closedPointSubspace]
    intro y hy
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    rintro rfl
    exact hy rfl
  have hY₀ : IsIso (pullback.snd bl.hom
      ((openComplement B S hS T.1).preimage (D.restrictionFst i a).hom).ι) :=
    isIso_pullback_snd_of_factor bl.hom (Subfunctor.homOfLe hle) (Subfunctor.homOfLe_ι hle) hU
  obtain ⟨M, hM, ⟨E⟩⟩ := exists_isModification_pullback_iso B S hS
    (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).property X'.property
    G.property (D.restrictionFst i a).hom (D.isEtale_restrictionFst i a) hsep T.1 T.2 hfT bl.hom
    hY₀
  refine ⟨⟨M.left, hM.1⟩, ObjectProperty.homMk M.hom,
    ObjectProperty.isoMk _ ((Over.forget _).mapIso E), ObjectProperty.hom_ext _ (Over.w E.hom),
    hM.2⟩

/-- A morphism `w : W ⟶ G` which is an isomorphism over `G ∖ {z}`, for a point `z` over `xᵢ`, is
an isomorphism over the inverse image of `X ∖ {xᵢ}`. -/
theorem isIso_pullback_snd_preimage_openAwayFromSinglePoint {W : AlgebraicSpaces B S hS}
    (w : W ⟶ G) {z : points B S hS G.obj} (hz : IsClosed ({z} : Set (points B S hS G.obj)))
    (hzx : pointsMap B S hS G.obj a.hom z = D.point i)
    (hw : IsIso (pullback.snd w.hom
      (openComplement B S hS (closedPointSubspace B S hS z hz).1).ι)) :
    IsIso (pullback.snd w.hom ((D.openAwayFromSinglePoint i).preimage a.hom).ι) := by
  have hle : (D.openAwayFromSinglePoint i).preimage a.hom ≤
      openComplement B S hS (closedPointSubspace B S hS z hz).1 := by
    refine le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_openComplement B S hS G.property _ (closedPointSubspace B S hS z hz).2) ?_
    have h1 := subspacePointSet_preimage B S hS a.hom (D.openAwayFromSinglePoint i)
    simp only [subspacePointSet] at h1
    rw [h1, range_pointsMap_ι_openComplement, range_pointsMap_ι_closedPointSubspace,
      D.range_pointsMap_ι_openAwayFromSinglePoint i]
    intro y hy
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    rintro rfl
    exact hy hzx
  exact isIso_pullback_snd_of_factor w.hom (Subfunctor.homOfLe hle) (Subfunctor.homOfLe_ι hle) hw

/-- The section of `G` underlying a section of the base change of `G` to `X ∖ {x₁, …, xₙ}` lies
over `X ∖ {xᵢ}`. -/
theorem range_pullback_fst_openAwayFromPoints_le :
    Subfunctor.range (pullback.fst a.hom D.openAwayFromPoints.ι) ≤
      (D.openAwayFromSinglePoint i).preimage a.hom := by
  rintro A _ ⟨p, rfl⟩
  have h₁ : (pullback.fst a.hom D.openAwayFromPoints.ι ≫ a.hom).app A p =
      (pullback.snd a.hom D.openAwayFromPoints.ι ≫ D.openAwayFromPoints.ι).app A p := by
    rw [pullback.condition]
  simp only [NatTrans.comp_app_apply] at h₁
  show a.hom.app A _ ∈ (D.openAwayFromSinglePoint i).obj A
  rw [h₁]
  exact D.openAwayFromPoints_le_openAwayFromSinglePoint i A
    ((pullback.snd a.hom D.openAwayFromPoints.ι).app A p).2

/-- **The composite of a modification of `G` over `X ∖ {xᵢ}` with `a` is a modification of `X`
away from the chosen points.** -/
theorem isIso_pullback_snd_comp_openAwayFromPoints {W : AlgebraicSpaces B S hS} (w : W ⟶ G)
    (hV : IsIso (pullback.snd w.hom ((D.openAwayFromSinglePoint i).preimage a.hom).ι))
    (ha : IsIso (pullback.snd a.hom D.openAwayFromPoints.ι)) :
    IsIso (pullback.snd (w.hom ≫ a.hom) D.openAwayFromPoints.ι) := by
  have hk : IsIso (pullback.snd w.hom (pullback.fst a.hom D.openAwayFromPoints.ι)) :=
    isIso_pullback_snd_of_factor w.hom
      (Subfunctor.lift _ (D.range_pullback_fst_openAwayFromPoints_le i a))
      (Subfunctor.lift_ι _ _) hV
  have heq : pullback.snd (w.hom ≫ a.hom) D.openAwayFromPoints.ι =
      (pullbackRightPullbackFstIso a.hom D.openAwayFromPoints.ι w.hom).inv ≫
        pullback.snd _ _ ≫ pullback.snd _ _ :=
    (pullbackRightPullbackFstIso_inv_snd_snd _ _ _).symm
  rw [heq]
  infer_instance

section Universal

variable {t : points B S hS (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj}
  (ht : IsClosed ({t} : Set (points B S hS
    (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj)))
  (htu : pointsMap B S hS _ (D.restrictionHom i a).hom t = D.neighborhoodPoint i)
  {X' : AlgebraicSpaces B S hS}
  {bl : X' ⟶ AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)}
  {W : AlgebraicSpaces B S hS} {w : W ⟶ G}
  (e : AlgebraicSpaces.fiberProduct B S hS w (D.restrictionFst i a) ≅ X')
  (he : e.hom ≫ bl = ObjectProperty.homMk (pullback.snd w.hom (D.restrictionFst i a).hom))

/-- The projection `W ×_G P ⟶ W`, as a morphism of algebraic spaces. -/
abbrev gluedFst {W : AlgebraicSpaces B S hS} (w : W ⟶ G) :
    AlgebraicSpaces.fiberProduct B S hS w (D.restrictionFst i a) ⟶ W :=
  ObjectProperty.homMk (pullback.fst w.hom (D.restrictionFst i a).hom)

/-- The projection `W ×_G P ⟶ P`, as a morphism of algebraic spaces. -/
abbrev gluedSnd {W : AlgebraicSpaces B S hS} (w : W ⟶ G) :
    AlgebraicSpaces.fiberProduct B S hS w (D.restrictionFst i a) ⟶
      AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i) :=
  ObjectProperty.homMk (pullback.snd w.hom (D.restrictionFst i a).hom)

include he in
/-- Through the identification `W ×_G P = P'`, the morphism `P' ⟶ W ⟶ G` is `P' ⟶ P ⟶ G`. -/
theorem inv_gluedFst_comp :
    e.inv ≫ D.gluedFst i a w ≫ w = bl ≫ D.restrictionFst i a := by
  rw [(AlgebraicSpaces.isPullback_fiberProduct B S hS w (D.restrictionFst i a)).w,
    ← Category.assoc]
  congr 1
  rw [← he, Iso.inv_hom_id_assoc]

include he in
/-- The inverse image in `P'` of the point `ψ(t)` of `G`, along `P' ⟶ W ⟶ G`, is the inverse
image of the blowing-up centre `t` of `P`. -/
theorem preimage_closedPointSubspace_comp_eq :
    (closedPointSubspace B S hS (pointsMap B S hS _ (D.restrictionFst i a).hom t)
        (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)).1.preimage
          (e.inv ≫ D.gluedFst i a w ≫ w).hom =
      (closedPointSubspace B S hS t ht).1.preimage bl.hom := by
  rw [D.inv_gluedFst_comp i a e he, ObjectProperty.FullSubcategory.comp_hom,
    Subfunctor.preimage_comp,
    D.preimage_closedPointSubspace_restrictionFst i a ht htu]

include he in
/-- **The inverse image of `ψ(t)` in the glued space `W` is an effective Cartier divisor.** Its
points lie over `ψ(t)`, so they lift to `W ×_G P = P'`, where the inverse image is the exceptional
divisor of the blowing up `P' ⟶ P`; the affine étale neighbourhoods of Stacks 083C (4) on which
that divisor is cut out by a nonzerodivisor are, composed with `P' ⟶ W`, neighbourhoods of the
same kind in `W`. -/
theorem isPullbackDefined_of_isBlowupAlong_restriction
    (hbl : IsBlowupAlong B S hS (closedPointSubspace B S hS t ht) bl) :
    IsPullbackDefined B S hS w (closedPointSubspace B S hS
      (pointsMap B S hS _ (D.restrictionFst i a).hom t)
      (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)) := by
  have hz := D.isClosed_singleton_pointsMap_restrictionFst i a ht htu
  have hfst : IsEtale B S hS (D.gluedFst i a w).hom :=
    isEtale_pullback_fst B S hS W.property G.property
      (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).property _ _
      (D.isEtale_restrictionFst i a)
  have hbl' := hasAffinePrincipalEtaleNeighborhoods_of_isEffectiveCartier B S hS X' _
    hbl.isPullbackDefined
  refine isEffectiveCartierDivisor_of_hasAffinePrincipalEtaleNeighborhoods B S hS W _ ?_
  intro x
  -- the image of `x` in `W` lies over `ψ(t)`
  have hxW : pointsMap B S hS W.obj w.hom
      (pointsMap B S hS _ ((closedPointSubspace B S hS _ hz).1.preimage w.hom).ι x) =
        pointsMap B S hS _ (D.restrictionFst i a).hom t := by
    have hmem : pointsMap B S hS _ ((closedPointSubspace B S hS _ hz).1.preimage w.hom).ι x ∈
        subspacePointSet B S hS W.obj
        ((closedPointSubspace B S hS _ hz).1.preimage w.hom) := ⟨x, rfl⟩
    rw [subspacePointSet_preimage] at hmem
    have h := range_pointsMap_ι_closedPointSubspace _ hz
    simp only [subspacePointSet] at hmem
    rw [h] at hmem
    exact hmem
  -- it lifts to `W ×_G P`, over `t`
  obtain ⟨y, hy₁, hy₂⟩ := exists_point_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS w (D.restrictionFst i a)) _ t hxW
  -- the corresponding point of the exceptional divisor of `P'`
  have hy'mem : pointsMap B S hS _ e.hom.hom y ∈ subspacePointSet B S hS X'.obj
      ((closedPointSubspace B S hS t ht).1.preimage bl.hom) := by
    rw [subspacePointSet_preimage]
    have h := range_pointsMap_ι_closedPointSubspace t ht
    simp only [subspacePointSet]
    rw [h, Set.mem_preimage, Set.mem_singleton_iff, ← pointsMap_comp_apply,
      ← ObjectProperty.FullSubcategory.comp_hom, he]
    exact hy₂
  obtain ⟨x', hx'⟩ := hy'mem
  obtain ⟨U, g, v, hUaff, hg, hgv, f, R, j, eR, hreg, hj, hpre⟩ := hbl' x'
  refine ⟨U, g ≫ (e.inv ≫ D.gluedFst i a w).hom, v, hUaff,
    isEtale_comp B S hS hg (isEtale_comp B S hS
      (isEtale_of_iso B S hS ((ObjectProperty.ι _).mapIso e.symm)) hfst), ?_,
    f, R, j, eR, hreg, hj, ?_⟩
  · rw [pointsMap_comp_apply, hgv, hx', ObjectProperty.FullSubcategory.comp_hom,
      pointsMap_comp_apply, ← pointsMap_comp_apply (α := e.hom.hom),
      ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id,
      ObjectProperty.FullSubcategory.id_hom, pointsMap_id]
    exact hy₁
  · rw [← Subfunctor.preimage_comp, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      Subfunctor.preimage_comp, Category.assoc,
      D.preimage_closedPointSubspace_comp_eq i a ht htu e he]
    exact hpre

/-- A section of a member of the covering of `X` other than the `i`th neighbourhood lies, in
`G`, over `X ∖ {xᵢ}`. -/
theorem range_coverPullbackHom_comp_le {Y : AlgebraicSpaces B S hS} (y : Y ⟶ G)
    (k : Option (Fin n)) (hk : k ≠ some i) :
    Subfunctor.range (D.coverPullbackHom (Over.mk (y.hom ≫ a.hom)) k ≫ y.hom) ≤
      (D.openAwayFromSinglePoint i).preimage a.hom := by
  rintro A _ ⟨c, rfl⟩
  have h₁ := congrArg (fun m => m.app A c)
    (D.coverPullbackHom_comp_hom (Over.mk (y.hom ≫ a.hom)) k)
  simp only [Over.mk_hom, NatTrans.comp_app_apply] at h₁
  refine (congrArg (· ∈ (D.openAwayFromSinglePoint i).obj A) h₁).mpr ?_
  cases k with
  | none =>
    exact D.openAwayFromPoints_le_openAwayFromSinglePoint i A
      ((pullback.snd (y.hom ≫ a.hom) D.openAwayFromPoints.ι).app A c).2
  | some k =>
    have hik : i ≠ k := fun h => hk (by rw [h])
    exact D.mem_openAwayFromSinglePoint_toSpaceHom_app hik _

/-- **Lifts through `w` on the members of the covering of `X` glue.** If `w ≫ a` is an
isomorphism over `X ∖ {x₁, …, xₙ}`, then lifts of `y : Y ⟶ G` through `w` on the members of the
covering, unique on each member, glue to a unique lift of `y` through `w`. -/
theorem existsUnique_lift_of_coverPullbackObj
    (hwa : IsIso (pullback.snd (w.hom ≫ a.hom) D.openAwayFromPoints.ι))
    {Y : AlgebraicSpaces B S hS} (y : Y ⟶ G)
    (γ : ∀ k, D.coverPullbackObj (Over.mk (y.hom ≫ a.hom)) k ⟶ W.obj)
    (hγ : ∀ k, γ k ≫ w.hom = D.coverPullbackHom (Over.mk (y.hom ≫ a.hom)) k ≫ y.hom)
    (huniq : ∀ k (β₁ β₂ : D.coverPullbackObj (Over.mk (y.hom ≫ a.hom)) k ⟶ W.obj),
      β₁ ≫ w.hom = D.coverPullbackHom (Over.mk (y.hom ≫ a.hom)) k ≫ y.hom →
        β₂ ≫ w.hom = D.coverPullbackHom (Over.mk (y.hom ≫ a.hom)) k ≫ y.hom → β₁ = β₂) :
    ∃! l : Y ⟶ W, l ≫ w = y := by
  let M : Over D.space.obj := Over.mk (y.hom ≫ a.hom)
  have hWsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) W.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 W.property.isSheaf
  have hγ' : ∀ k, γ k ≫ (Over.mk (w.hom ≫ a.hom)).hom = D.coverPullbackToSpace M k := by
    intro k
    show γ k ≫ (w.hom ≫ a.hom) = _
    rw [← Category.assoc, hγ k, Category.assoc, ← D.coverPullbackHom_comp_hom M k]
    rfl
  obtain ⟨φ, hφ, -⟩ := Presheaf.existsUnique_hom_of_sheafify_iSup_range_eq_top _
    (D.coverPullbackHom M) (D.sheafify_iSup_range_coverPullbackHom_eq_top M) hWsheaf γ
    (fun A k k' c d h => app_eq_of_coverPullbackHom_app_eq (M' := Over.mk (w.hom ≫ a.hom)) hwa
      hWsheaf D.exists_diagonalComplement_openAwayFromSinglePoint γ hγ' A k k' c d h)
  refine ⟨ObjectProperty.homMk φ, ?_, fun m hm => ?_⟩
  · apply ObjectProperty.hom_ext
    refine Presheaf.hom_ext_of_sheafify_iSup_range_eq_top _ (D.coverPullbackHom M)
      (D.sheafify_iSup_range_coverPullbackHom_eq_top M)
      ((isSheaf_iff_isSheaf_of_type _ _).1 G.property.isSheaf) fun k => ?_
    show D.coverPullbackHom M k ≫ φ ≫ w.hom = D.coverPullbackHom M k ≫ y.hom
    rw [← Category.assoc, hφ k, hγ k]
  · apply ObjectProperty.hom_ext
    have hm' : m.hom ≫ w.hom = y.hom := congrArg (fun m => m.hom) hm
    refine Presheaf.hom_ext_of_sheafify_iSup_range_eq_top _ (D.coverPullbackHom M)
      (D.sheafify_iSup_range_coverPullbackHom_eq_top M) hWsheaf fun k => ?_
    show D.coverPullbackHom M k ≫ m.hom = D.coverPullbackHom M k ≫ φ
    rw [hφ k]
    exact huniq k _ _ (by rw [Category.assoc, hm']) (hγ k)

/-- If `c ≫ ψ = f ≫ y` with `f` flat and `y` pulling `ψ(t)` back to an effective Cartier divisor,
then `c` pulls `t` back to an effective Cartier divisor. -/
theorem isPullbackDefined_of_comp_restrictionFst_eq {Y Y' : AlgebraicSpaces B S hS} {y : Y ⟶ G}
    (hy : IsPullbackDefined B S hS y (closedPointSubspace B S hS
      (pointsMap B S hS _ (D.restrictionFst i a).hom t)
      (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)))
    {c : Y' ⟶ AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)} {f : Y' ⟶ Y}
    (hf : IsFlat B S hS f.hom) (hcf : c ≫ D.restrictionFst i a = f ≫ y) :
    IsPullbackDefined B S hS c (closedPointSubspace B S hS t ht) := by
  have hz := D.isClosed_singleton_pointsMap_restrictionFst i a ht htu
  refine isEffectiveCartierDivisor_congr ?_ (isPullbackDefined_of_isFlat B S hS f
    ⟨(closedPointSubspace B S hS _ hz).1.preimage y.hom,
      isClosedSubspace_preimage B S hS y.hom _ G.2 Y.2 (closedPointSubspace B S hS _ hz).2⟩ hy hf)
  show ((closedPointSubspace B S hS _ hz).1.preimage y.hom).preimage f.hom =
    (closedPointSubspace B S hS t ht).1.preimage c.hom
  rw [← D.preimage_closedPointSubspace_restrictionFst i a ht htu, ← Subfunctor.preimage_comp,
    ← Subfunctor.preimage_comp,
    ← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom, hcf]

include he in
/-- For a morphism `c` to `P` pulling `t` back to an effective Cartier divisor, the composite
`c ≫ ψ` factors through `w : W ⟶ G`. -/
theorem exists_comp_eq_comp_restrictionFst
    (hbl : IsBlowupAlong B S hS (closedPointSubspace B S hS t ht) bl)
    {Y' : AlgebraicSpaces B S hS} {c : Y' ⟶ AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)}
    (hc : IsPullbackDefined B S hS c (closedPointSubspace B S hS t ht)) :
    ∃ γ : Y' ⟶ W, γ ≫ w = c ≫ D.restrictionFst i a := by
  obtain ⟨l, hl, -⟩ := hbl.existsUnique_lift c hc
  exact ⟨l ≫ e.inv ≫ D.gluedFst i a w, by
    rw [Category.assoc, Category.assoc, D.inv_gluedFst_comp i a e he, ← Category.assoc, hl]⟩

include he in
/-- Two morphisms to `W` which agree over `G` with `c ≫ ψ`, for a morphism `c` to `P` pulling `t`
back to an effective Cartier divisor, are equal. -/
theorem eq_of_comp_eq_comp_restrictionFst
    (hbl : IsBlowupAlong B S hS (closedPointSubspace B S hS t ht) bl)
    {Y' : AlgebraicSpaces B S hS} {c : Y' ⟶ AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)}
    (hc : IsPullbackDefined B S hS c (closedPointSubspace B S hS t ht)) {β₁ β₂ : Y'.obj ⟶ W.obj}
    (h₁ : β₁ ≫ w.hom = c.hom ≫ (D.restrictionFst i a).hom)
    (h₂ : β₂ ≫ w.hom = c.hom ≫ (D.restrictionFst i a).hom) : β₁ = β₂ := by
  let lam₁ : Y' ⟶ AlgebraicSpaces.fiberProduct B S hS w (D.restrictionFst i a) :=
    ObjectProperty.homMk (pullback.lift β₁ c.hom h₁)
  let lam₂ : Y' ⟶ AlgebraicSpaces.fiberProduct B S hS w (D.restrictionFst i a) :=
    ObjectProperty.homMk (pullback.lift β₂ c.hom h₂)
  have hlam : ∀ lam : Y' ⟶ AlgebraicSpaces.fiberProduct B S hS w (D.restrictionFst i a),
      lam.hom ≫ pullback.snd w.hom (D.restrictionFst i a).hom = c.hom → (lam ≫ e.hom) ≫ bl = c := by
    intro lam h'
    rw [Category.assoc, he]
    exact ObjectProperty.hom_ext _ h'
  obtain ⟨l, -, hl⟩ := hbl.existsUnique_lift c hc
  have hlameq : lam₁ = lam₂ := (cancel_mono e.hom).1
    ((hl _ (hlam lam₁ (pullback.lift_snd _ _ _))).trans
      (hl _ (hlam lam₂ (pullback.lift_snd _ _ _))).symm)
  have h₁' : β₁ = lam₁.hom ≫ pullback.fst w.hom (D.restrictionFst i a).hom :=
    (pullback.lift_fst _ _ _).symm
  have h₂' : β₂ = lam₂.hom ≫ pullback.fst w.hom (D.restrictionFst i a).hom :=
    (pullback.lift_fst _ _ _).symm
  rw [h₁', h₂', hlameq]

include he in
/-- **The glued space is the blowing up of `G` at `ψ(t)`.** The inverse image of the point is an
effective Cartier divisor, and a morphism `y : Y ⟶ G` along which it pulls back to an effective
Cartier divisor lifts uniquely through `W ⟶ G`: on the members of the covering of `X` other than
`Uᵢ` the lift is the unique one through the isomorphism `W ⟶ G` over `X ∖ {xᵢ}`, on `Uᵢ` it is the
lift through the blowing up `P' ⟶ P` given by its universal property, and the pieces glue by the
descent along the covering used for Stacks 0BHB. -/
theorem isBlowupAlong_of_isBlowupAlong_restriction
    (ha : IsIso (pullback.snd a.hom D.openAwayFromPoints.ι))
    (hbl : IsBlowupAlong B S hS (closedPointSubspace B S hS t ht) bl)
    (hw : IsIso (pullback.snd w.hom (openComplement B S hS (closedPointSubspace B S hS
      (pointsMap B S hS _ (D.restrictionFst i a).hom t)
      (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)).1).ι)) :
    IsBlowupAlong B S hS (closedPointSubspace B S hS
      (pointsMap B S hS _ (D.restrictionFst i a).hom t)
      (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)) w := by
  have hV := D.isIso_pullback_snd_preimage_openAwayFromSinglePoint i a w
    (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)
    (D.pointsMap_restrictionFst_eq_point i a htu) hw
  refine isBlowupAlong_of_existsUnique_lift
    (D.isPullbackDefined_of_isBlowupAlong_restriction i a ht htu e he hbl) fun Y y hy => ?_
  let fstC : AlgebraicSpaces.fiberProduct B S hS (y ≫ a) (D.toSpaceHom i) ⟶ Y :=
    ObjectProperty.homMk (pullback.fst (y.hom ≫ a.hom) (D.toSpaceHom i).hom)
  let cP : AlgebraicSpaces.fiberProduct B S hS (y ≫ a) (D.toSpaceHom i) ⟶
      AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i) :=
    ObjectProperty.homMk (pullback.lift (pullback.fst (y.hom ≫ a.hom) (D.toSpaceHom i).hom ≫ y.hom)
      (pullback.snd (y.hom ≫ a.hom) (D.toSpaceHom i).hom)
      ((Category.assoc _ _ _).trans pullback.condition))
  have hcP : cP ≫ D.restrictionFst i a = fstC ≫ y :=
    ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)
  have hfstC : IsEtale B S hS fstC.hom :=
    isEtale_pullback_fst B S hS Y.property D.space.property (D.neighborhoodSpace i).property
      _ _ (D.neighborhood i).etale_toSpace
  have hcart := D.isPullbackDefined_of_comp_restrictionFst_eq i a ht htu hy
    (isFlat_of_isEtale B S hS hfstC) hcP
  have hex : ∀ k, ∃ γ : D.coverPullbackObj (Over.mk (y.hom ≫ a.hom)) k ⟶ W.obj,
      γ ≫ w.hom = D.coverPullbackHom (Over.mk (y.hom ≫ a.hom)) k ≫ y.hom := by
    intro k
    by_cases hk : k = some i
    · subst hk
      obtain ⟨γ, hγ⟩ := D.exists_comp_eq_comp_restrictionFst i a ht e he hbl hcart
      exact ⟨γ.hom, congrArg (fun m => m.hom) (hγ.trans hcP)⟩
    · exact exists_lift_of_isIso_pullback_snd B S hS w.hom hV _
        (Subfunctor.lift _ (D.range_coverPullbackHom_comp_le i a y k hk)) (Subfunctor.lift_ι _ _)
  choose γ hγ using hex
  refine D.existsUnique_lift_of_coverPullbackObj a
    (D.isIso_pullback_snd_comp_openAwayFromPoints i a w hV ha) y γ hγ fun k β₁ β₂ h₁ h₂ => ?_
  by_cases hk : k = some i
  · subst hk
    have hc : ∀ β : D.coverPullbackObj (Over.mk (y.hom ≫ a.hom)) (some i) ⟶ W.obj,
        β ≫ w.hom = D.coverPullbackHom (Over.mk (y.hom ≫ a.hom)) (some i) ≫ y.hom →
          β ≫ w.hom = cP.hom ≫ (D.restrictionFst i a).hom :=
      fun _ hβ => hβ.trans (congrArg (fun m => m.hom) hcP).symm
    exact D.eq_of_comp_eq_comp_restrictionFst i a ht e he hbl hcart (hc β₁ h₁) (hc β₂ h₂)
  · exact lift_eq_of_isIso_pullback_snd B S hS w.hom hV
      (Subfunctor.lift _ (D.range_coverPullbackHom_comp_le i a y k hk)) β₁ β₂
      (h₁.trans (Subfunctor.lift_ι _ _).symm) (h₂.trans (Subfunctor.lift_ι _ _).symm)

end Universal

end Lift

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
