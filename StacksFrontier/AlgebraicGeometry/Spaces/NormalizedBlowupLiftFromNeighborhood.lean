module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAtClosedPointExcision
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyFiniteComponentsPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationGenericStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupLocallyFiniteIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.NormalizedBlowupLiftStep

/-!
# Lifting a normalized blowing up from an étale neighbourhood to the whole space

Let `X` be a decent algebraic space over a scheme `S` with pairwise distinct closed points
`x₁, …, xₙ` and chosen elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` (Stacks 0BH9), and
let `a : G ⟶ X` be a normal algebraic space over `X`, unchanged over `X ∖ {x₁, …, xₙ}`, which is
decent and satisfies the conditions of Stacks 0BB1. A normalized blowing up of `P = G ×_X Uᵢ` at a
closed point `t` over `uᵢ` is the base change of a normalized blowing up `G' ⟶ G` at the closed
point `ψ(t)` of `G`; the new space `G'` is again normal, decent, satisfies the conditions of
Stacks 0BB1 and is unchanged over `X ∖ {x₁, …, xₙ}`, and its base changes to the other
neighbourhoods are those of `G`.

This is the step by which the "if" direction of Stacks 0BHL, for normal `X`, lifts a sequence of
normalized blowings up of a neighbourhood to `X` ("we construct the sequence of blowing ups of `X`
in exactly the same manner").

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_isNormalizedBlowupAtClosedPoint_lift`:
  the lifting step.

## Implementation notes

The blowing up of `G` is the one glued by excision in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupAtClosedPointExcision.lean`. It satisfies the
conditions of Stacks 0BB1 because those are étale local and hold on `G ∖ {ψ(t)}` and on the blowing
up of `P`, which carries normalization data; it is decent because its points of codimension `0`
lie over the dense open `G ∖ {ψ(t)}` (Stacks 0ENA). Its normalization exists by Stacks 07U4, and
normalization commutes with the étale base changes in question.

## References

* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The two descriptions of the open complement of a closed subspace agree: both are open
subspaces with the same points. -/
theorem openComplementOfClosedSubspace_eq_openComplement {G : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS G.obj) :
    (openComplementOfClosedSubspace B S hS G Z).1 = openComplement B S hS Z.1 := by
  have hpts : Set.range (pointsMap B S hS _ (openComplementOfClosedSubspace B S hS G Z).1.ι) =
      Set.range (pointsMap B S hS _ (openComplement B S hS Z.1).ι) := by
    have h := subspacePointSet_openComplement B S hS G Z
    simp only [subspacePointSet] at h
    rw [h, range_pointsMap_ι_openComplement]
  exact le_antisymm
    (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_openComplement B S hS G.property Z.1 Z.2) hpts.le)
    (le_of_range_pointsMap_ι_subset B S hS (openComplementOfClosedSubspace B S hS G Z).2 hpts.ge)

/-- A morphism which is an isomorphism over an open subspace `O` identifies the preimage of `O`
with `O`. -/
theorem isIso_fromPreimage_of_isIso_pullback_snd {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) (O : Subfunctor X) (h : IsIso (pullback.snd f O.ι)) :
    IsIso (O.fromPreimage f) := by
  rw [← (Subfunctor.isPullback_preimage f O).flip.isoPullback_hom_snd]
  infer_instance

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The projection `G ×_X Uᵢ ⟶ G` is étale. -/
theorem isEtale_restrictionFst (i : Fin n) {G : AlgebraicSpaces B S hS} (a : G ⟶ D.space) :
    IsEtale B S hS (D.restrictionFst i a).hom :=
  isEtale_pullback_fst B S hS G.property D.space.property (D.neighborhoodSpace i).property
    _ _ (D.neighborhood i).etale_toSpace

/-- The projection `W ×_G (G ×_X Uᵢ) ⟶ W` is étale. -/
theorem isEtale_gluedFst (i : Fin n) {G W : AlgebraicSpaces B S hS} (a : G ⟶ D.space)
    (w : W ⟶ G) : IsEtale B S hS (D.gluedFst i a w).hom :=
  isEtale_pullback_fst B S hS W.property G.property
    (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).property _ _
    (D.isEtale_restrictionFst i a)

section Lift

variable (i : Fin n) {G : AlgebraicSpaces B S hS} (a : G ⟶ D.space)
  {t : points B S hS (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj}
  (ht : IsClosed ({t} : Set (points B S hS
    (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj)))
  (htu : pointsMap B S hS _ (D.restrictionHom i a).hom t = D.neighborhoodPoint i)
  {X' : AlgebraicSpaces B S hS}
  {bl : X' ⟶ AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)}
  {W : AlgebraicSpaces B S hS} {w : W ⟶ G}
  (e : AlgebraicSpaces.fiberProduct B S hS w (D.restrictionFst i a) ≅ X')
  (he : e.hom ≫ bl = ObjectProperty.homMk (pullback.snd w.hom (D.restrictionFst i a).hom))

include e in
/-- **The glued blowing up satisfies the conditions of Stacks 0BB1 and is decent.** -/
theorem hasLocallyFiniteIrreducibleComponents_and_isDecentSpace_of_restriction
    (hGdec : IsDecentSpace B S hS G.obj)
    (hGfin : HasLocallyFiniteIrreducibleComponents B S hS G.obj)
    (hX'fin : HasLocallyFiniteIrreducibleComponents B S hS X'.obj)
    (hw : IsIso (pullback.snd w.hom (openComplement B S hS (closedPointSubspace B S hS
      (pointsMap B S hS _ (D.restrictionFst i a).hom t)
      (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)).1).ι))
    (hwbl : IsBlowupAlong B S hS (closedPointSubspace B S hS
      (pointsMap B S hS _ (D.restrictionFst i a).hom t)
      (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)) w) :
    HasLocallyFiniteIrreducibleComponents B S hS W.obj ∧ IsDecentSpace B S hS W.obj := by
  set T := closedPointSubspace B S hS (pointsMap B S hS _ (D.restrictionFst i a).hom t)
    (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu)
  have hoc : IsOpenSubspace B S hS (openComplement B S hS T.1) :=
    isOpenSubspace_openComplement B S hS G.property T.1 T.2
  have hO : IsOpenSubspace B S hS ((openComplement B S hS T.1).preimage w.hom) :=
    isOpenSubspace_preimage B S hS w.hom _ G.property W.property hoc
  have hiso : IsIso ((openComplement B S hS T.1).fromPreimage w.hom) :=
    isIso_fromPreimage_of_isIso_pullback_snd _ _ hw
  have hfin : HasLocallyFiniteIrreducibleComponents B S hS W.obj := by
    refine hasLocallyFiniteIrreducibleComponents_of_isEtale_cover_two B S hS W.property hO.1
      (AlgebraicSpaces.fiberProduct B S hS w (D.restrictionFst i a)).property _
      (D.gluedFst i a w).hom (isEtale_ι_of_isOpenSubspace hO)
      (D.isEtale_gluedFst i a w)
      (hasLocallyFiniteIrreducibleComponents_of_iso B S hS
        (asIso ((openComplement B S hS T.1).fromPreimage w.hom)).symm
        (hasLocallyFiniteIrreducibleComponents_of_isEtale B S hS hGfin
          (isEtale_ι_of_isOpenSubspace hoc)))
      (hasLocallyFiniteIrreducibleComponents_of_iso B S hS ((ObjectProperty.ι _).mapIso e.symm)
        hX'fin) fun x => ?_
    by_cases hx : pointsMap B S hS W.obj w.hom x = pointsMap B S hS _ (D.restrictionFst i a).hom t
    · obtain ⟨y, hy, -⟩ := exists_point_of_isPullback B S hS
        (AlgebraicSpaces.isPullback_fiberProduct B S hS w (D.restrictionFst i a)) x t hx
      exact Or.inr ⟨y, hy⟩
    · left
      have h := subspacePointSet_preimage B S hS w.hom (openComplement B S hS T.1)
      simp only [subspacePointSet] at h
      rw [h, Set.mem_preimage, range_pointsMap_ι_openComplement,
        range_pointsMap_ι_closedPointSubspace]
      exact hx
  refine ⟨hfin, isDecentSpace_of_dense_isOpenSubspace B S hS W.property hfin hO ?_ ?_⟩
  · have hd := dense_subspacePointSet_preimage_of_isBlowupAlong
      (openComplementOfClosedSubspace B S hS G T) T hwbl (by
        rw [subspacePointSet_openComplement, compl_compl])
    rwa [openComplementOfClosedSubspace_eq_openComplement] at hd
  · exact isDecentSpace_of_iso B S hS (asIso ((openComplement B S hS T.1).fromPreimage w.hom)).symm
      (isDecentSpace_of_isOpenSubspace B S hS G.property hGdec hoc)

include he in
/-- **Normalization commutes with the base change to `Uᵢ`.** If `Q ⟶ P` is the normalization of
the blowing up `X' ⟶ P = G ×_X Uᵢ`, which is the base change of `w : W ⟶ G`, then the base change
of the normalization of `W` to `Uᵢ` is `Q`, compatibly with the maps to `Uᵢ`. -/
theorem exists_iso_fiberProduct_normalizationHom_comp
    (hX'fin : HasLocallyFiniteIrreducibleComponents B S hS X'.obj)
    (NW : NormalizationData B S hS W.obj) {Q : AlgebraicSpaces B S hS}
    {q : Q ⟶ AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)}
    (N : NormalizationData B S hS X'.obj) (eQ : Q.obj ≅ N.space)
    (hqeq : q.hom = eQ.hom ≫ N.hom ≫ bl.hom) :
    ∃ e' : AlgebraicSpaces.fiberProduct B S hS ((normalizationHom NW ≫ w) ≫ a)
        (D.toSpaceHom i) ≅ Q,
      e'.hom ≫ q ≫ D.restrictionHom i a = D.restrictionHom i ((normalizationHom NW ≫ w) ≫ a) := by
  have hP := (AlgebraicSpaces.fiberProduct B S hS w (D.restrictionFst i a)).property
  obtain ⟨N'⟩ := nonempty_normalizationData B S hS hP
    (hasLocallyFiniteIrreducibleComponents_of_iso B S hS ((ObjectProperty.ι _).mapIso e.symm)
      hX'fin)
  obtain ⟨m, hm⟩ := NW.isPullback_hom_of_isEtale N' W.property hP _ (D.isEtale_gluedFst i a w)
  obtain ⟨m', hm'⟩ := N.isPullback_hom_of_isEtale N' X'.property hP e.hom.hom
    (isEtale_of_iso B S hS ((ObjectProperty.ι _).mapIso e))
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).mapIso e).hom)
  have hm'iso : IsIso m' := hm'.isIso_fst_of_isIso
  have P0 : IsPullback (D.restrictionFst i a).hom (D.restrictionHom i a).hom a.hom
      (D.toSpaceHom i).hom := IsPullback.of_hasPullback a.hom (D.toSpaceHom i).hom
  have P1 : IsPullback (D.gluedFst i a w).hom (D.gluedSnd i a w).hom w.hom
      (D.restrictionFst i a).hom := IsPullback.of_hasPullback w.hom (D.restrictionFst i a).hom
  have big : IsPullback m (N'.hom ≫ (D.gluedSnd i a w).hom ≫ (D.restrictionHom i a).hom)
      (NW.hom ≫ w.hom ≫ a.hom) (D.toSpaceHom i).hom := hm.paste_vert (P1.paste_vert P0)
  have P := IsPullback.of_hasPullback (NW.hom ≫ w.hom ≫ a.hom) (D.toSpaceHom i).hom
  let iso1 := P.isoIsPullback _ _ big
  refine ⟨ObjectProperty.isoMk _ (iso1 ≪≫ asIso m' ≪≫ eQ.symm), ?_⟩
  apply ObjectProperty.hom_ext
  have hsnd : e.hom.hom ≫ bl.hom = (D.gluedSnd i a w).hom := congrArg (fun k => k.hom) he
  change (iso1.hom ≫ m' ≫ eQ.inv) ≫ q.hom ≫ (D.restrictionHom i a).hom =
    pullback.snd (NW.hom ≫ w.hom ≫ a.hom) (D.toSpaceHom i).hom
  rw [hqeq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hm'.w, reassoc_of% hsnd]
  exact P.isoIsPullback_hom_snd _ _ big

end Lift

section LiftStep

variable (i : Fin n) {G : AlgebraicSpaces B S hS} (a : G ⟶ D.space)
  {t : points B S hS (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj}
  (ht : IsClosed ({t} : Set (points B S hS
    (AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)).obj)))
  (htu : pointsMap B S hS _ (D.restrictionHom i a).hom t = D.neighborhoodPoint i)

/-- **A normalized blowing up of a normal `G` at a point over `xᵢ` does not change the base change
of `G` to an étale `c : P' ⟶ X` none of whose points lies over `xᵢ`.** -/
theorem exists_iso_pullback_comp_of_ne_point (hGn : Space.IsNormal B S hS G.obj)
    {z : points B S hS G.obj} {hz : IsClosed ({z} : Set (points B S hS G.obj))}
    (hzx : pointsMap B S hS G.obj a.hom z = D.point i) {G' : AlgebraicSpaces B S hS}
    {b : G' ⟶ G} (hb : IsNormalizationOfBlowupAtClosedPoint B S hS z hz b)
    {P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP' : IsAlgebraicSpace B S hS P')
    (c : P' ⟶ D.space.obj) (hc : IsEtale B S hS c)
    (hcx : ∀ p, pointsMap B S hS P' c p ≠ D.point i) :
    ∃ e : pullback (b.hom ≫ a.hom) c ≅ pullback a.hom c,
      e.hom ≫ pullback.snd a.hom c = pullback.snd (b.hom ≫ a.hom) c := by
  refine exists_iso_pullback_comp_of_isNormalizationOfBlowupAtClosedPoint a hb hP' c hc
    (hasEtaleLocalProperty_of_isEtale B S hS
      (isAlgebraicSpace_pullback B S hS a.hom c G.property hP' D.space.property) G.property
      (isEtale_pullback_fst B S hS G.property D.space.property hP' _ _ hc) hGn) fun p hp => ?_
  refine hcx (pointsMap B S hS _ (pullback.snd a.hom c) p) ?_
  have h1 : pointsMap B S hS _ (pullback.snd a.hom c ≫ c) p =
      pointsMap B S hS _ (pullback.fst a.hom c ≫ a.hom) p := by rw [pullback.condition]
  rwa [pointsMap_comp_apply, pointsMap_comp_apply, hp, hzx] at h1

/-- **The lifting step.** A normalized blowing up `Q ⟶ P` of `P = G ×_X Uᵢ` at a closed point
`t` over `uᵢ` is the base change of a normalized blowing up `G' ⟶ G` at the closed point `ψ(t)`:
`G'` is normal, decent and satisfies the conditions of Stacks 0BB1, `G' ⟶ X` is unchanged over
`X ∖ {x₁, …, xₙ}`, its base change to `Uᵢ` is `Q ⟶ P ⟶ Uᵢ` and its base changes to the other
neighbourhoods are those of `G`. -/
theorem exists_isNormalizedBlowupAtClosedPoint_lift
    (ha : IsIso (pullback.snd a.hom D.openAwayFromPoints.ι)) (hGn : Space.IsNormal B S hS G.obj)
    (hGdec : IsDecentSpace B S hS G.obj)
    (hGfin : HasLocallyFiniteIrreducibleComponents B S hS G.obj)
    {Q : AlgebraicSpaces B S hS} {q : Q ⟶ AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom i)}
    (hq : IsNormalizationOfBlowupAtClosedPoint B S hS t ht q) :
    ∃ (G' : AlgebraicSpaces B S hS) (b : G' ⟶ G),
      IsNormalizedBlowupAtClosedPoint B S hS hGdec hGfin
        (pointsMap B S hS _ (D.restrictionFst i a).hom t)
        (D.isClosed_singleton_pointsMap_restrictionFst i a ht htu) b ∧
      Space.IsNormal B S hS G'.obj ∧ IsDecentSpace B S hS G'.obj ∧
      HasLocallyFiniteIrreducibleComponents B S hS G'.obj ∧
      IsIso (pullback.snd (b ≫ a).hom D.openAwayFromPoints.ι) ∧
      (∃ e : AlgebraicSpaces.fiberProduct B S hS (b ≫ a) (D.toSpaceHom i) ≅ Q,
        e.hom ≫ q ≫ D.restrictionHom i a = D.restrictionHom i (b ≫ a)) ∧
      ∀ k, k ≠ i → ∃ e : AlgebraicSpaces.fiberProduct B S hS (b ≫ a) (D.toSpaceHom k) ≅
          AlgebraicSpaces.fiberProduct B S hS a (D.toSpaceHom k),
        e.hom ≫ D.restrictionHom k a = D.restrictionHom k (b ≫ a) := by
  have hz := D.isClosed_singleton_pointsMap_restrictionFst i a ht htu
  have hzx := D.pointsMap_restrictionFst_eq_point i a htu
  obtain ⟨X', bl, hbl, N, eQ, hqeq⟩ := hq
  have hbl' := hbl.isBlowupAlong
  obtain ⟨W, w, e, he, hw⟩ := D.exists_excision_of_isBlowupAlong i a ht htu hbl'
  have hwbl := D.isBlowupAlong_of_isBlowupAlong_restriction i a ht htu e he ha hbl' hw
  have hX'fin := N.hasLocallyFiniteIrreducibleComponents X'.property
  obtain ⟨hWfin, hWdec⟩ := D.hasLocallyFiniteIrreducibleComponents_and_isDecentSpace_of_restriction
    i a ht htu e hGdec hGfin hX'fin hw hwbl
  obtain ⟨NW⟩ := nonempty_normalizationData B S hS W.property hWfin
  have hb := isNormalizedBlowupAtClosedPoint_comp hGdec hGfin
    (isBlowupAtClosedPoint_of_isBlowupAlong hwbl) NW
  have hbN := hb.isNormalizationOfBlowupAtClosedPoint
  refine ⟨normalizationSpace NW, normalizationHom NW ≫ w, hb, NW.isNormal W.property,
    NW.isDecentSpace W.property hWdec,
    NW.hasLocallyFiniteIrreducibleComponents_space B S hS W.property, ?_, ?_, ?_⟩
  · have hO := D.isOpenSubspace_openAwayFromPoints
    obtain ⟨e₀, he₀⟩ := D.exists_iso_pullback_comp_of_ne_point i a hGn hzx hbN hO.1
      D.openAwayFromPoints.ι (isEtale_ι_of_isOpenSubspace hO) fun p hp => by
        have hmem : D.point i ∈ Set.range (pointsMap B S hS _ D.openAwayFromPoints.ι) :=
          ⟨p, hp⟩
        rw [D.range_pointsMap_ι_openAwayFromPoints] at hmem
        exact hmem ⟨i, rfl⟩
    change IsIso (pullback.snd ((normalizationHom NW ≫ w).hom ≫ a.hom) _)
    rw [← he₀]
    infer_instance
  · exact D.exists_iso_fiberProduct_normalizationHom_comp i a e he hX'fin NW N eQ hqeq
  · intro k hk
    obtain ⟨e₁, he₁⟩ := D.exists_iso_pullback_comp_of_ne_point i a hGn hzx hbN
      (D.neighborhoodSpace k).property (D.toSpaceHom k).hom (D.neighborhood k).etale_toSpace
      fun p => D.map_ne_point k i hk p
    exact ⟨ObjectProperty.isoMk _ e₁, ObjectProperty.hom_ext _ he₁⟩

end LiftStep

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
