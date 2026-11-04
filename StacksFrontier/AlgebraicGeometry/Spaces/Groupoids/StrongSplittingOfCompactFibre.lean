module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.IteratedRestrictionSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SplittingSituations
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingAffineLocalization

/-!
# The strong splitting step of Stacks 0DU5

The proof of **Stacks 0DU5** works with a groupoid scheme `(U, R, s, t, c)` whose object scheme
`U` is affine and whose source and target are flat, locally of finite presentation, locally
quasi-finite and separated — the groupoid `R = U ×_𝒳 U` of a chart of a quasi-DM stack with
separated diagonal — together with a point `u ∈ U` for which the fibre
`F = Spec κ(u) ×_U R` of one of the structure morphisms is quasi-compact. It concludes that the
set `{r ∈ R : s(r) = u, t(r) = u}` is finite, so that **Stacks 04RZ** applies and, after an
elementary étale neighbourhood, `R` acquires a strong splitting over `u` in the sense of
**Stacks 04RK**, part (1). This file proves those two steps, and that the strong splitting is a
groupoid scheme of the shape of clause (3) of Stacks 0DU5: both structure schemes affine and
source and target finite, flat and locally of finite presentation.

## Main results

* `AlgebraicGeometry.Scheme.Hom.finite_preimage_of_compactSpace_pullback`: a locally
  quasi-finite morphism whose fibre over the spectrum of a field is quasi-compact has finitely
  many points over the image point. This is the special case of Stacks 06S0 that the source's
  proof uses — a quasi-compact scheme locally quasi-finite over a field has finitely many points —
  and it is Mathlib's `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton` applied to the
  projection of the fibre to the spectrum of the field.
* `AlgebraicGeometry.Space.StrongSplittingSituation.ofCompactSpaceTargetFibre` and
  `AlgebraicGeometry.Space.StrongSplittingSituation.ofCompactSpaceSourceFibre`: Situation 04RL
  from a quasi-compact fibre of the target, respectively of the source.
* `Stacks.Groupoids.GroupoidScheme.StrongSplitting.isAffine_isFinite_flat`: a strong splitting
  of a groupoid scheme with affine object scheme and flat, locally finitely presented source and
  target is a groupoid scheme of the shape of clause (3) of Stacks 0DU5.
* `Stacks.Groupoids.GroupoidScheme.exists_comp_mapArrows_eq_of_forall_eq` and
  `Stacks.Groupoids.GroupoidScheme.StrongSplitting.exists_comp_inclusion_eq`: a generalized arrow
  whose source and target take only the value `u` factors through an open subgroupoid containing
  every arrow with source and target `u`, in particular through a strong splitting over `u`.
  This is the step "`P ⊂ R` is open and contains `{r ∈ R : s(r) = u, t(r) = u}`" of the source,
  from which `u ×_{[U/P]} u ⟶ u ×_{[U/R]} u` is an isomorphism.
* `Stacks.Groupoids.GroupoidScheme.StrongSplitting.transport` and
  `AlgebraicGeometry.GroupoidScheme.isStronglySplitAt_of_iteratedRestriction'`: a strong splitting
  transports along an isomorphism of arrow schemes over an equality of object schemes, in
  particular from the two-step restriction `(R|_{U'})|_{U''}` to the restriction along the
  composite `U'' ⟶ U' ⟶ U` (Stacks 04MW).
* `AlgebraicGeometry.Space.restriction_flat_locallyOfFinitePresentation`: a restriction along a
  flat, locally finitely presented morphism inherits flat, locally finitely presented source and
  target.
* `AlgebraicGeometry.Space.exists_isAffine_strongSplitting_of_compactSpace_targetFibre`: the
  strong splitting step of Stacks 0DU5, from Stacks 04RZ.

## References

* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04MW](https://stacks.math.columbia.edu/tag/04MW)
* [Stacks Project, Tag 04RZ](https://stacks.math.columbia.edu/tag/04RZ)
* [Stacks Project, Tag 06S0](https://stacks.math.columbia.edu/tag/06S0)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **A locally quasi-finite morphism with a quasi-compact fibre over a one-point quasi-separated
scheme has finitely many points over the image point.** The projection of the fibre to `Z` is
locally quasi-finite (base change) and quasi-compact (its source is quasi-compact and its target
quasi-separated), so it has finitely many points over the unique point of `Z`, which are all the
points of the fibre; and every point of `X` over the image point lifts to the fibre. The case of
interest is `Z` the spectrum of a field. -/
theorem finite_preimage_of_compactSpace_pullback {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [QuasiSeparatedSpace Z] [Subsingleton Z] (y : Z ⟶ Y)
    [CompactSpace ↑(pullback y f)] (p : Z) :
    (f ⁻¹' {y p}).Finite := by
  have : QuasiCompact (pullback.fst y f) := quasiCompact_of_compactSpace _
  have huniv : (Set.univ : Set ↑(pullback y f)) = pullback.fst y f ⁻¹' {p} := by
    ext z
    simp [Subsingleton.elim (pullback.fst y f z) p]
  have : Finite ↑(pullback y f) :=
    Set.finite_univ_iff.1 (huniv ▸ (pullback.fst y f).finite_preimage_singleton p)
  refine (Set.finite_range (pullback.snd y f)).subset fun x hx => ?_
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := f) p x hx.symm
  exact ⟨z, hz⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Space.StrongSplittingSituation

open Stacks.Groupoids

/-- **Situation 04RL from a quasi-compact fibre of the target.** For a groupoid scheme whose
source and target are separated, locally of finite type and locally quasi-finite, and a point `u`
of the object scheme over which the fibre `Spec κ(u) ×_{U, t} R` of the target is quasi-compact,
the set of arrows with source and target `u` is finite — it lies in `t⁻¹(u)`, which is finite by
`AlgebraicGeometry.Scheme.Hom.finite_preimage_of_compactSpace_pullback` — and the source is
quasi-finite at every point. -/
noncomputable def ofCompactSpaceTargetFibre {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) [AlgebraicGeometry.IsSeparated G.source.left]
    [AlgebraicGeometry.IsSeparated G.target.left]
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    [LocallyQuasiFinite G.source.left] [LocallyQuasiFinite G.target.left]
    [CompactSpace ↑(pullback (G.objects.left.fromSpecResidueField u) G.target.left)] :
    StrongSplittingSituation.{u} where
  S := S
  groupoid := G
  u := u
  stabilizer_finite := by
    refine (G.target.left.finite_preimage_of_compactSpace_pullback
      (G.objects.left.fromSpecResidueField u) (IsLocalRing.closedPoint _)).subset ?_
    rintro r ⟨-, hr⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, hr]
    exact (Scheme.fromSpecResidueField_apply _ _).symm
  source_quasiFiniteAt r _ :=
    (forall_quasiFiniteAt_iff G.source.left).2 ⟨inferInstance, inferInstance⟩ r

/-- **Situation 04RL from a quasi-compact fibre of the source.** As
`AlgebraicGeometry.Space.StrongSplittingSituation.ofCompactSpaceTargetFibre`, with the fibre
`Spec κ(u) ×_{U, s} R` of the source quasi-compact instead. -/
noncomputable def ofCompactSpaceSourceFibre {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) [AlgebraicGeometry.IsSeparated G.source.left]
    [AlgebraicGeometry.IsSeparated G.target.left]
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    [LocallyQuasiFinite G.source.left]
    [CompactSpace ↑(pullback (G.objects.left.fromSpecResidueField u) G.source.left)] :
    StrongSplittingSituation.{u} where
  S := S
  groupoid := G
  u := u
  stabilizer_finite := by
    refine (G.source.left.finite_preimage_of_compactSpace_pullback
      (G.objects.left.fromSpecResidueField u) (IsLocalRing.closedPoint _)).subset ?_
    rintro r ⟨hr, -⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, hr]
    exact (Scheme.fromSpecResidueField_apply _ _).symm
  source_quasiFiniteAt r _ :=
    (forall_quasiFiniteAt_iff G.source.left).2 ⟨inferInstance, inferInstance⟩ r

end AlgebraicGeometry.Space.StrongSplittingSituation

namespace Stacks.Groupoids.GroupoidScheme

open _root_.AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **A strong splitting is a groupoid scheme of the shape of clause (3) of Stacks 0DU5.** For a
groupoid scheme with affine object scheme and with flat, locally finitely presented source and
target, the subgroupoid of a strong splitting has both structure schemes affine and finite, flat,
locally finitely presented source and target.

Its object scheme is the ambient one. Its source and target are the ambient ones restricted along
the open immersion of arrow schemes, transported along the equality of object schemes, so they
are flat and locally of finite presentation; they are finite by definition of a splitting; and
the arrow scheme is affine because the source is finite, hence affine, over the affine object
scheme. -/
theorem StrongSplitting.isAffine_isFinite_flat {G : GroupoidScheme S} {u : G.objects.left}
    (P : StrongSplitting G u) [IsAffine G.objects.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left] :
    IsAffine P.subgroupoid.objects.left ∧ IsAffine P.subgroupoid.arrows.left ∧
      IsFinite P.subgroupoid.source.left ∧ Flat P.subgroupoid.source.left ∧
      LocallyOfFinitePresentation P.subgroupoid.source.left ∧
      IsFinite P.subgroupoid.target.left ∧ Flat P.subgroupoid.target.left ∧
      LocallyOfFinitePresentation P.subgroupoid.target.left := by
  have key : ∀ (f : P.subgroupoid.arrows ⟶ P.subgroupoid.objects) (g : G.arrows ⟶ G.objects),
      P.inclusion.mapArrows ≫ g = f ≫ P.inclusion.mapObjects →
      f.left = P.inclusion.mapArrows.left ≫ g.left ≫ (eqToHom P.objects_eq.symm).left := by
    intro f g h
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, h, P.mapObjects_eq,
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have : IsIso (eqToHom P.objects_eq.symm).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom P.objects_eq.symm)))
  have := P.arrows_open
  have := P.source_finite
  have := P.target_finite
  have hobj : IsAffine P.subgroupoid.objects.left := by
    rw [P.objects_eq]
    infer_instance
  refine ⟨hobj, isAffine_of_isAffineHom P.subgroupoid.source.left, P.source_finite, ?_, ?_,
    P.target_finite, ?_, ?_⟩ <;>
    first | (rw [key _ _ P.inclusion.map_source]; infer_instance) |
      (rw [key _ _ P.inclusion.map_target]; infer_instance)

/-- **Arrows over a strongly split point lift to the open subgroupoid.** Let `φ : H ⟶ K` be a
morphism of groupoid schemes which is an open immersion on arrow schemes, and let `u` be a point
of the object scheme of `K` such that every arrow of `K` with source and target `u` lies in the
image of `φ` — as for the inclusion of a strong splitting over `u`. Then every generalized arrow
`r : T ⟶ R` of `K` whose source and target take only the value `u` factors through `φ`: its image
lies in the set of arrows with source and target `u`, hence in the open image of `φ`. -/
theorem exists_comp_mapArrows_eq_of_forall_eq {H K : GroupoidScheme S} (φ : Hom H K)
    [IsOpenImmersion φ.mapArrows.left] (u : K.objects.left)
    (hstab : ∀ r : K.arrows.left, K.source.left r = u → K.target.left r = u →
      ∃ p : H.arrows.left, φ.mapArrows.left p = r)
    {T : Over S} (r : T ⟶ K.arrows) (hs : ∀ τ : T.left, K.source.left (r.left τ) = u)
    (ht : ∀ τ : T.left, K.target.left (r.left τ) = u) :
    ∃ a : T ⟶ H.arrows, a ≫ φ.mapArrows = r := by
  have hrange : Set.range r.left ⊆ Set.range φ.mapArrows.left := by
    rintro _ ⟨τ, rfl⟩
    exact hstab _ (hs τ) (ht τ)
  let a : T.left ⟶ H.arrows.left := IsOpenImmersion.lift φ.mapArrows.left r.left hrange
  have ha : a ≫ φ.mapArrows.left = r.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
  rw [← Over.w φ.mapArrows, ← Category.assoc, ha]
  exact Over.w r

/-- **Arrows over the point of a strong splitting lift to the splitting.** Every generalized
arrow of `G` whose source and target take only the value `u` factors through the inclusion of a
strong splitting of `G` over `u`. -/
theorem StrongSplitting.exists_comp_inclusion_eq {G : GroupoidScheme S} {u : G.objects.left}
    (P : StrongSplitting G u) {T : Over S} (r : T ⟶ G.arrows)
    (hs : ∀ τ : T.left, G.source.left (r.left τ) = u)
    (ht : ∀ τ : T.left, G.target.left (r.left τ) = u) :
    ∃ a : T ⟶ P.subgroupoid.arrows, a ≫ P.inclusion.mapArrows = r := by
  have := P.arrows_open
  exact exists_comp_mapArrows_eq_of_forall_eq P.inclusion u P.contains_stabilizer r hs ht

/-- **Transport of a strong splitting** along a morphism of groupoid schemes which is an
isomorphism on arrow schemes and is given on objects by an equality of object schemes. The
transported subgroupoid is the original one, with its inclusion composed with the morphism; an
arrow of the target with source and target the transported point is the image of an arrow of the
source with source and target the original point, because the morphism is compatible with source
and target and is the equality on objects. -/
def StrongSplitting.transport {K L : GroupoidScheme S} {u : K.objects.left}
    (P : StrongSplitting K u) (Φ : Hom K L) (e : K.objects = L.objects)
    (hΦ : Φ.mapObjects = eqToHom e) [IsIso Φ.mapArrows] :
    StrongSplitting L ((eqToHom e).left.base u) where
  toOpenFiniteSubgroupoid := P.toOpenFiniteSubgroupoid.transport Φ e hΦ
  contains_stabilizer := by
    intro r hs ht
    let r₀ := (inv Φ.mapArrows).left.base r
    have hr₀ : Φ.mapArrows.left.base r₀ = r := by
      have h := congrArg (fun k : L.arrows ⟶ L.arrows => k.left.base r)
        (IsIso.inv_hom_id Φ.mapArrows)
      simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.id_left] at h
      exact h
    have hcancel : ∀ a : K.objects.left,
        (eqToHom e.symm).left.base ((eqToHom e).left.base a) = a :=
      over_eqToHom_apply_symm e.symm
    have hsrc : (eqToHom e).left.base (K.source.left.base r₀) = (eqToHom e).left.base u := by
      have h := congrArg (fun k : K.arrows.left ⟶ L.objects.left => k.base r₀)
        Φ.map_source_left
      simp only [Scheme.Hom.comp_apply, hr₀, hs, hΦ] at h
      exact h.symm
    have htgt : (eqToHom e).left.base (K.target.left.base r₀) = (eqToHom e).left.base u := by
      have h := congrArg (fun k : K.arrows.left ⟶ L.objects.left => k.base r₀)
        Φ.map_target_left
      simp only [Scheme.Hom.comp_apply, hr₀, ht, hΦ] at h
      exact h.symm
    have hs₀ : K.source.left.base r₀ = u := by
      rw [← hcancel (K.source.left.base r₀), hsrc, hcancel]
    have ht₀ : K.target.left.base r₀ = u := by
      rw [← hcancel (K.target.left.base r₀), htgt, hcancel]
    obtain ⟨p, hp⟩ := P.contains_stabilizer r₀ hs₀ ht₀
    refine ⟨p, ?_⟩
    change (P.inclusion.mapArrows ≫ Φ.mapArrows).left.base p = r
    rw [Over.comp_left, Scheme.Hom.comp_apply, hp, hr₀]

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {H : Stacks.Groupoids.GroupoidScheme S} {U' U'' : Over S}
  {g : U' ⟶ H.objects} (R' : Restriction H g) {j : U'' ⟶ R'.groupoid.objects}
  (R'' : Restriction R'.groupoid j) (R''' : Restriction H (j ≫ R'.hom.mapObjects))

/-- A realization of `G|_{U''}` along the composite `U'' ⟶ U' ⟶ U` is strongly split over a
point of `U''` whenever a realization of the two-step restriction `(G|_{U'})|_{U''}` is: the
comparison of the two restrictions is an isomorphism on arrows and the equality on objects
(Stacks 04MW), and a strong splitting transports along it. -/
theorem isStronglySplitAt_of_iteratedRestriction' (u'' : U''.left)
    (h : Stacks.Groupoids.GroupoidScheme.IsStronglySplitAt R''.groupoid
      ((eqToHom R''.objects_eq.symm).left.base u'')) :
    Stacks.Groupoids.GroupoidScheme.IsStronglySplitAt R'''.groupoid
      ((eqToHom R'''.objects_eq.symm).left.base u'') := by
  have key : (eqToHom (iteratedRestriction_objects_eq R' R'' R''')).left.base
      ((eqToHom R''.objects_eq.symm).left.base u'') =
      (eqToHom R'''.objects_eq.symm).left.base u'' := by
    simpa only [Over.comp_left, Scheme.Hom.comp_apply] using
      congrArg (fun k : U'' ⟶ R'''.groupoid.objects => k.left.base u'')
        (eqToHom_trans R''.objects_eq.symm (iteratedRestriction_objects_eq R' R'' R'''))
  rw [← key]
  exact h.elim fun P =>
    ⟨P.transport (iteratedRestrictionHom R' R'' R''')
      (iteratedRestriction_objects_eq R' R'' R''') rfl⟩

end AlgebraicGeometry.GroupoidScheme

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

/-- The source and target of a restriction of a groupoid scheme along a flat, locally finitely
presented morphism are flat and locally of finite presentation when those of the groupoid
are. -/
theorem restriction_flat_locallyOfFinitePresentation {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (R : AlgebraicGeometry.GroupoidScheme.Restriction G g)
    [Flat g.left] [LocallyOfFinitePresentation g.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left] :
    Flat R.groupoid.source.left ∧ LocallyOfFinitePresentation R.groupoid.source.left ∧
      Flat R.groupoid.target.left ∧ LocallyOfFinitePresentation R.groupoid.target.left := by
  have h : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      [P.IsStableUnderComposition], P G.source.left → P g.left →
      P R.groupoid.source.left ∧ P R.groupoid.target.left := by
    intro P _ _ hs hg
    have hc := AlgebraicGeometry.overFibreProduct_comp (pullback.snd g G.target) G.source
      (AlgebraicGeometry.overFibreProduct_snd _ G.target hg) hs
    exact ⟨AlgebraicGeometry.restriction_source_mem G _ R P hc,
      AlgebraicGeometry.restriction_target_mem G _ R P hc⟩
  obtain ⟨h1, h2⟩ := h @Flat inferInstance inferInstance
  obtain ⟨h3, h4⟩ := h @LocallyOfFinitePresentation inferInstance inferInstance
  exact ⟨h1, h3, h2, h4⟩

/-- **The strong splitting step of Stacks 0DU5.** Let `(U, R, s, t, c)` be a groupoid scheme with
`U` affine and with `s` and `t` flat, locally of finite presentation, locally quasi-finite and
separated, and let `u ∈ U` be a point over which the fibre `Spec κ(u) ×_{U, t} R` of the target is
quasi-compact. Then there are an affine `U''`, an étale `g : U'' ⟶ U` and a point `u''` over `u`
with `κ(u) = κ(u'')` — an elementary étale neighbourhood — such that every groupoid scheme
realizing the restriction `R|_{U''}` along `g` has flat, locally finitely presented source and
target and carries a strong splitting `P` over `u''`, and `P` is a groupoid scheme with both
structure schemes affine and with source and target finite, flat and locally of finite
presentation.

The quasi-compact fibre makes the stabilizer of `u` finite
(`AlgebraicGeometry.Space.StrongSplittingSituation.ofCompactSpaceTargetFibre`), so Situation 04RL
holds and Stacks 04RZ applies. Stacks 04RZ delivers the splitting on the two-step restriction
`(R|_{U'})|_{U''}`; it is transported to the restriction along the composite by
`AlgebraicGeometry.GroupoidScheme.isStronglySplitAt_of_iteratedRestriction'`. The shape of `P` is
`Stacks.Groupoids.GroupoidScheme.StrongSplitting.isAffine_isFinite_flat`. -/
theorem exists_isAffine_strongSplitting_of_compactSpace_targetFibre {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains S)
    (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    [IsAffine G.objects.left]
    [AlgebraicGeometry.IsSeparated G.source.left] [AlgebraicGeometry.IsSeparated G.target.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    [LocallyQuasiFinite G.source.left] [LocallyQuasiFinite G.target.left]
    [CompactSpace ↑(pullback (G.objects.left.fromSpecResidueField u) G.target.left)] :
    ∃ (U'' : Over S) (g : U'' ⟶ G.objects) (u'' : U''.left),
      IsAffine U''.left ∧ Etale g.left ∧ g.left.base u'' = u ∧
      IsIso (g.left.residueFieldMap u'') ∧
      ∀ R : AlgebraicGeometry.GroupoidScheme.Restriction G g,
        (Flat R.groupoid.source.left ∧ LocallyOfFinitePresentation R.groupoid.source.left ∧
          Flat R.groupoid.target.left ∧ LocallyOfFinitePresentation R.groupoid.target.left) ∧
        ∃ P : GroupoidScheme.StrongSplitting R.groupoid
            ((eqToHom R.objects_eq.symm).left.base u''),
          IsAffine P.subgroupoid.objects.left ∧ IsAffine P.subgroupoid.arrows.left ∧
          AlgebraicGeometry.IsFinite P.subgroupoid.source.left ∧ Flat P.subgroupoid.source.left ∧
          LocallyOfFinitePresentation P.subgroupoid.source.left ∧
          AlgebraicGeometry.IsFinite P.subgroupoid.target.left ∧ Flat P.subgroupoid.target.left ∧
          LocallyOfFinitePresentation P.subgroupoid.target.left := by
  let D := StrongSplittingSituation.ofCompactSpaceTargetFibre G u
  have : IsAffine D.groupoid.objects.left := inferInstanceAs (IsAffine G.objects.left)
  have : Flat D.groupoid.source.left := inferInstanceAs (Flat G.source.left)
  have : LocallyOfFinitePresentation D.groupoid.source.left :=
    inferInstanceAs (LocallyOfFinitePresentation G.source.left)
  have : Flat D.groupoid.target.left := inferInstanceAs (Flat G.target.left)
  have : LocallyOfFinitePresentation D.groupoid.target.left :=
    inferInstanceAs (LocallyOfFinitePresentation G.target.left)
  obtain ⟨E⟩ := GroupoidScheme.nonempty_etaleStrongSplitting_scheme D C hS hU hR hP hK
    inferInstance inferInstance
  obtain ⟨U'', j, u'', haff, hj, het, hbase, hres, hsplit⟩ :=
    GroupoidScheme.exists_isAffine_isStronglySplitAt_of_etaleStrongSplitting E
  refine ⟨U'', j ≫ E.restriction.hom.mapObjects, u'', haff, het, hbase, hres, fun R => ?_⟩
  have : Etale (j ≫ E.restriction.hom.mapObjects).left := het
  have : Flat (j ≫ E.restriction.hom.mapObjects).left :=
    (Etale.iff_flat_and_formallyUnramified.1 het).1
  obtain ⟨k1, k2, k3, k4⟩ := restriction_flat_locallyOfFinitePresentation D.groupoid
    (j ≫ E.restriction.hom.mapObjects) R
  have : IsAffine R.groupoid.objects.left := by
    rw [R.objects_eq]
    exact haff
  obtain ⟨P⟩ := AlgebraicGeometry.GroupoidScheme.isStronglySplitAt_of_iteratedRestriction'
    E.restriction (AlgebraicGeometry.GroupoidScheme.restrict E.restriction.groupoid j) R u''
    (hsplit (AlgebraicGeometry.GroupoidScheme.restrict E.restriction.groupoid j))
  exact ⟨⟨k1, k2, k3, k4⟩, P, P.isAffine_isFinite_flat⟩

end AlgebraicGeometry.Space

end
