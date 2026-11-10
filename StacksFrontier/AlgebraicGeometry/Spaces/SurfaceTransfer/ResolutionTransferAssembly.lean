module

public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularCompletionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.LocalSchemeSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.LocalToGlobalInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.SingularPointNeighborhoods

/-!
# Resolving an algebraic space from resolutions of étale neighbourhoods of its singular points

Let `X` be a normal, locally Noetherian algebraic space over a scheme `S` whose singular points
are the chosen closed points `x₁, …, xₙ` of elementary étale neighbourhoods `(Uᵢ, uᵢ)`
(Stacks 0BH9), and let `ν : X ⟶ Y` be the start of a sequence of normalized blowups over `Y`
(Stacks 0BHX). If each `Uᵢ` has a resolution by proper normalized blowups centred over `uᵢ`, then
these lift, one neighbourhood at a time, to a sequence of normalized blowups of `X` whose top is
regular: over `X ∖ {x₁, …, xₙ}` nothing changes and the top is regular there because `X` is, and
over each `Uᵢ` the top is the regular top of the given sequence. This is the last paragraph of the
proof of (4) `⇒` (3) of Stacks 0BHY.

## Main results

* `AlgebraicGeometry.Space.isRegularAt_of_isEtale` and
  `AlgebraicGeometry.Space.isRegularAt_of_isEtale_of_isRegularAt_image`: regularity at a point
  ascends and descends along étale morphisms.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_normalizedBlowUpChain_isRegular`: the
  statement above.

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0AH9](https://stacks.math.columbia.edu/tag/0AH9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Regularity at a point along étale morphisms -/

/-- **Regularity at a point ascends along an étale morphism**: an étale chart of the source at
the point, followed by the morphism, is an étale chart of the target at the image point. -/
theorem isRegularAt_of_isEtale {P F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hF : IsAlgebraicSpace B S hS F) {h : P ⟶ F}
    (hh : IsEtale B S hS h) {p : points B S hS P} (hp : IsRegularAt B S hS P p) :
    IsRegularAt B S hS F (pointsMap B S hS P h p) := by
  obtain ⟨U, a, ha, q, hq⟩ := exists_etale_chart_at_point B S hS P hP p
  refine (isRegularAt_iff_exists_etale_chart B S hS F hF _).mpr
    ⟨U, a ≫ h, presheaf_etale_of_isEtale B S hS
      (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS ha) hh), q, ?_, hp U a ha q hq⟩
  rw [pointsMap_comp_apply, hq]

/-- **Regularity at a point descends along an étale morphism**: an étale chart of the source,
followed by the morphism, is an étale chart of the target. -/
theorem isRegularAt_of_isEtale_of_isRegularAt_image {P F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {h : P ⟶ F} (hh : IsEtale B S hS h) {p : points B S hS P}
    (hp : IsRegularAt B S hS F (pointsMap B S hS P h p)) : IsRegularAt B S hS P p := by
  intro U a ha q hq
  refine hp U (a ≫ h) (presheaf_etale_of_isEtale B S hS
    (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS ha) hh)) q ?_
  rw [pointsMap_comp_apply, hq]

/-- An algebraic space represented by a regular scheme is regular at every point. -/
theorem isRegularAt_yoneda_of_isRegular (W : BigFppfOver B S hS)
    (hW : IsRegular ((BigFppfOver.toScheme B S hS).obj W)) (w : points B S hS (yoneda.obj W)) :
    IsRegularAt B S hS (yoneda.obj W) w := by
  have h := (isRegularLocalRing_stalk_iff_isRegularAt B S hS (isAlgebraicSpace_yoneda B S hS W) W
    (𝟙 _) (presheaf_etale_of_isEtale B S hS (isEtale_id B S hS _)) w).mp
    (((AlgebraicGeometry.isRegular_iff_regular_stalks _).mp hW).2 _)
  rwa [pointsMap_id] at h

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- A representation of the base change transports along an isomorphism of base changes over the
neighbourhood. -/
theorem stageRep_of_iso (i : Fin n) {A A₀ : AlgebraicSpaces B S hS} {g : A ⟶ D.space}
    {g₀ : A₀ ⟶ D.space} {Z : Over (D.neighborhoodScheme i)}
    (e : pullback g.hom (D.toSpaceHom i).hom ≅ pullback g₀.hom (D.toSpaceHom i).hom)
    (he : e.hom ≫ pullback.snd g₀.hom (D.toSpaceHom i).hom =
      pullback.snd g.hom (D.toSpaceHom i).hom)
    (h : D.StageRep i g₀ Z) : D.StageRep i g Z := by
  obtain ⟨W, q, Φ, θ, hΦ, hθ⟩ := h
  exact ⟨W, q, e ≪≫ Φ, θ, (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hΦ).trans he), hθ⟩

/-- **Resolving `X` from centred resolutions of the neighbourhoods of its singular points.** Let
`ν : X ⟶ Y` be the normalization of `Y`, proper, with `X` normal and locally Noetherian and
regular away from the chosen points. If each chosen neighbourhood has a resolution by proper
normalized blowups centred over its distinguished point, then `Y` has a sequence of normalized
blowups in the sense of Stacks 0BHX, starting with `ν`, whose top is regular. -/
theorem exists_normalizedBlowUpChain_isRegular
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] {Y : AlgebraicSpaces B S hS}
    (ν : D.space ⟶ Y) (hν : IsProper B S hS ν.hom)
    (hνnorm : ∃ (Dn : NormalizationData B S hS Y.obj) (e : D.space.obj ≅ Dn.space),
      ν.hom = e.hom ≫ Dn.hom)
    (hXn : Space.IsNormal B S hS D.space.obj)
    (hXln : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hreg : ∀ x, x ∉ Set.range D.point → IsRegularAt B S hS D.space.obj x)
    (hloc : ∀ i, ∃ (U : (D.neighborhoodScheme i).Opens) (Z : Over (D.neighborhoodScheme i)),
      (∀ y, y ∉ U → y = (D.neighborhood i).point) ∧
        Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U) (Over.mk (𝟙 _)) Z ∧
          AlgebraicGeometry.IsProper Z.hom ∧ IsRegular Z.left) :
    ∃ (A : AlgebraicSpaces B S hS) (f : A ⟶ Y), NormalizedBlowUpChain B S hS Y A f ∧
      HasEtaleLocalProperty B S hS A.obj (fun T : Scheme.{u} => IsRegular T) := by
  classical
  choose U Z hU hZ hZp hZr using hloc
  have hid : IsIso (𝟙 D.space : D.space ⟶ D.space).hom := inferInstanceAs (IsIso (𝟙 D.space.obj))
  have hidp : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : P ⟶ D.space.obj),
      IsIso (pullback.snd (𝟙 D.space : D.space ⟶ D.space).hom c) :=
    fun c => (IsPullback.of_hasPullback _ c).isIso_snd_of_isIso
  have hgood₀ : D.IsGoodStage ν (𝟙 D.space) := by
    refine ⟨?_, hXn, hXln, hidp _⟩
    rw [Category.id_comp]
    exact NormalizedBlowUpChain.normalization ν hνnorm hν
  have hrest₀ : ∀ k,
      IsProper B S hS (pullback.snd (𝟙 D.space : D.space ⟶ D.space).hom (D.toSpaceHom k).hom) :=
    fun k => have := hidp (D.toSpaceHom k).hom; isProper_of_isIso B S hS _
  have hrep₀ : ∀ k, D.StageRep k (𝟙 D.space) (Over.mk (𝟙 _)) := fun k =>
    ⟨(D.neighborhood k).scheme, 𝟙 _, @asIso _ _ _ _
      (pullback.snd (𝟙 D.space : D.space ⟶ D.space).hom (D.toSpaceHom k).hom) (hidp _),
      Iso.refl _, by simp only [CategoryTheory.Functor.map_id, Category.comp_id]; rfl, by simp⟩
  have claim : ∀ s : Finset (Fin n), ∃ (A : AlgebraicSpaces B S hS) (g : A ⟶ D.space),
      D.IsGoodStage ν g ∧ (∀ k, IsProper B S hS (pullback.snd g.hom (D.toSpaceHom k).hom)) ∧
        ∀ k, D.StageRep k g (if k ∈ s then Z k else Over.mk (𝟙 _)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨_, 𝟙 D.space, hgood₀, hrest₀, fun k => by simpa using hrep₀ k⟩
    | @insert i s hi ih =>
      obtain ⟨A₀, g₀, hgood, hrest, hrep⟩ := ih
      have hrepi : D.StageRep i g₀ (Over.mk (𝟙 _)) := by simpa [hi] using hrep i
      obtain ⟨A, g, hgood', hrest', hrepi', hpres⟩ :=
        D.exists_lift_reflTransGen ν hν hXln i (hU i) hgood hrest hrepi (hZ i)
      refine ⟨A, g, hgood', hrest', fun k => ?_⟩
      by_cases hk : k = i
      · subst hk
        simpa using hrepi'
      · obtain ⟨e, he⟩ := hpres (D.neighborhoodSpace k).property (D.toSpaceHom k).hom
          (D.neighborhood k).etale_toSpace (fun p hp => D.map_ne_point k i hk p hp)
        have h := D.stageRep_of_iso k e he (hrep k)
        simpa [Finset.mem_insert, hk] using h
  obtain ⟨A, g, hgood, -, hrep⟩ := claim Finset.univ
  simp only [Finset.mem_univ, ite_true] at hrep
  refine ⟨A, g ≫ ν, hgood.1, ?_⟩
  refine (hasEtaleLocalProperty_isRegular_iff_forall_isRegularAt B S hS A.property hgood.2.2.1).mpr
    fun a => ?_
  by_cases ha : pointsMap B S hS A.obj g.hom a ∈ Set.range D.point
  · obtain ⟨k, hk⟩ := ha
    obtain ⟨W, q, Φ, θ, hΦ, hθ⟩ := hrep k
    obtain ⟨t, ht, -⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback g.hom (D.toSpaceHom k).hom) a (D.neighborhoodPoint k)
      (by rw [← hk, D.pointsMap_toSpaceHom_neighborhoodPoint])
    have hP := isAlgebraicSpace_pullback B S hS g.hom (D.toSpaceHom k).hom A.property
      (D.neighborhoodSpace k).property D.space.property
    have : IsLocallyNoetherian (Z k).left :=
      ((AlgebraicGeometry.isRegular_iff_regular_stalks _).mp (hZr k)).1
    have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) :=
      isLocallyNoetherian_of_isOpenImmersion θ.hom
    have hWreg : IsRegular ((BigFppfOver.toScheme B S hS).obj W) := isRegular_of_iso θ (hZr k)
    have htreg : IsRegularAt B S hS _ t :=
      isRegularAt_of_isEtale_of_isRegularAt_image (isEtale_of_iso B S hS Φ)
        (isRegularAt_yoneda_of_isRegular W hWreg _)
    rw [← ht]
    exact isRegularAt_of_isEtale hP A.property
      (isEtale_pullback_fst B S hS A.property D.space.property (D.neighborhoodSpace k).property
        _ _ (D.neighborhood k).etale_toSpace) htreg
  · have hNo := D.isOpenSubspace_openAwayFromPoints
    obtain ⟨u, hu⟩ : pointsMap B S hS A.obj g.hom a ∈
        Set.range (pointsMap B S hS _ D.openAwayFromPoints.ι) := by
      rw [D.range_pointsMap_ι_openAwayFromPoints]; exact ha
    obtain ⟨t, ht, ht'⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback g.hom D.openAwayFromPoints.ι) a u hu.symm
    have hP := isAlgebraicSpace_pullback B S hS g.hom D.openAwayFromPoints.ι A.property hNo.1
      D.space.property
    have hureg : IsRegularAt B S hS _ u :=
      isRegularAt_of_isEtale_of_isRegularAt_image (isEtale_ι_of_isOpenSubspace hNo)
        (by rw [hu]; exact hreg _ ha)
    have hiso := hgood.2.2.2
    have htreg : IsRegularAt B S hS _ t :=
      isRegularAt_of_isEtale_of_isRegularAt_image
        (isEtale_of_isIso B S hS (pullback.snd g.hom D.openAwayFromPoints.ι))
        (by rw [ht']; exact hureg)
    rw [← ht]
    exact isRegularAt_of_isEtale hP A.property
      (isEtale_pullback_fst B S hS A.property D.space.property hNo.1 _ _
        (isEtale_ι_of_isOpenSubspace hNo)) htreg

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space
